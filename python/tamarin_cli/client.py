"""Synchronous JSON-lines client; all proof operations belong to Tamarin.

Example::

    with TamarinClient() as client:
        client.load("example.spthy")
        client.lemma("secrecy")
        listing = client.methods()
        print(listing["methods"])
        client.apply(0, revision=listing["revision"])  # Explicit method choice.
        client.save("example-partial.spthy")

Every command returns a dictionary including ``status`` and ``revision``.
Backend command errors raise BackendError without ending the session. Instances
are synchronous and should not be shared between concurrent callers.
"""

from __future__ import annotations

import json
import os
from pathlib import Path
import shlex
import signal
import shutil
import subprocess
import threading
from typing import Any, Dict, Optional, Sequence, TextIO, Union


class TamarinError(Exception):
    """Base class for backend startup, transport, and command errors."""


class BackendError(TamarinError):
    """A structured rejected command.

    ``response`` retains the entire error object for API callers.
    ``recoverable`` indicates whether the session remains available.
    """

    def __init__(self, response: Dict[str, Any]) -> None:
        self.response = response
        error = response["error"]
        self.code: str = error["code"]
        self.recoverable: bool = error["recoverable"]
        self.suggested_action: str = error["suggested_action"]
        super().__init__(str(error["message"]))


class BackendUnavailableError(TamarinError):
    """The configured backend could not be started."""


class ProtocolError(TamarinError):
    """The backend exited or returned something other than a protocol response."""


class ResponseLimitError(ProtocolError):
    """The backend exceeded the configured wire response byte limit."""


class ClientClosedError(TamarinError):
    """A command was attempted after the session ended."""


def _repository_root() -> Optional[Path]:
    # Source installations can use Stack even when invoked outside the checkout.
    candidates = list(Path(__file__).resolve().parents) + [Path.cwd(), *Path.cwd().parents]
    for candidate in candidates:
        if (candidate / "stack.yaml").is_file() and (candidate / "tamarin-prover.cabal").is_file():
            return candidate
    return None


def backend_command(backend: Optional[Union[str, Sequence[str]]] = None) -> list[str]:
    """Resolve a command prefix and append the ``proof-api`` mode.

    Explicit commands and TAMARIN_BACKEND are shell-quoted command strings, not
    shell scripts: quoting is supported, but pipes and shell expansion are not.
    A sequence of arguments can be supplied directly by programmatic callers.
    """
    configured = backend if backend is not None else os.environ.get("TAMARIN_BACKEND")
    if configured is not None:
        try:
            command = shlex.split(configured) if isinstance(configured, str) else list(configured)
        except ValueError as exc:
            raise BackendUnavailableError(f"Invalid backend command: {exc}") from exc
        if not command:
            raise BackendUnavailableError("Backend command must not be empty")
    else:
        root = _repository_root()
        if root is not None and shutil.which("stack") is not None:
            # A checkout must use its own build, not an older installed prover.
            command = [
                "stack", "--stack-yaml", str(root / "stack.yaml"),
                "exec", "--no-install-ghc", "--", "tamarin-prover",
            ]
        elif installed := shutil.which("tamarin-prover"):
            command = [installed]
        else:
            raise BackendUnavailableError(
                "Cannot find tamarin-prover. Use --backend, set TAMARIN_BACKEND, "
                "or build this checkout with Stack."
            )
    return command + ["proof-api"]


class TamarinClient:
    """Own one backend process and its selected theory, lemma, and proof path.

    Use as a context manager for reliable shutdown, or call ``close()`` yourself.
    ``start()`` and context entry start the backend; the first request also starts
    it when necessary. Backend stderr is inherited by default, never parsed as
    JSON. Pass a file object as ``stderr`` to redirect diagnostics explicitly.

    Safety-layer callers may disable SIGINT handling for worker-thread use and
    cap the wire response before decoding. ``process_prefix`` supports an exec
    launcher, ``cwd`` selects its working directory, and ``kill_process_group``
    makes shutdown release descendants too. ``abort_event`` prevents a startup
    racing with external termination from leaving an unowned process.
    """

    def __init__(
        self,
        backend: Optional[Union[str, Sequence[str]]] = None,
        *,
        stderr: Optional[TextIO] = None,
        handle_sigint: bool = True,
        max_response_bytes: Optional[int] = None,
        process_prefix: Sequence[str] = (),
        cwd: Optional[Union[str, os.PathLike[str]]] = None,
        kill_process_group: bool = False,
        abort_event: Optional[threading.Event] = None,
    ) -> None:
        self._backend = backend
        self._stderr = stderr
        if max_response_bytes is not None and (
            type(max_response_bytes) is not int or max_response_bytes <= 0
        ):
            raise ValueError("max_response_bytes must be a positive integer or None")
        self._handle_sigint = handle_sigint
        self._max_response_bytes = max_response_bytes
        self._process_prefix = list(process_prefix)
        self._cwd = cwd
        self._kill_group = kill_process_group
        self._abort_event = abort_event
        self._process: Optional[subprocess.Popen[str]] = None
        self._closed = False
        self._revision: Optional[int] = None
        self._group_killed = False
        self._group_kill_lock = threading.Lock()

    @property
    def revision(self) -> Optional[int]:
        """Latest observed backend revision, or None before the first reply.

        Apply using the revision attached to the method list you selected from,
        not a later value of this property.
        """
        return self._revision

    def check_alive(self) -> None:
        """Check an existing child without starting or restarting a session."""
        if self._closed:
            raise ClientClosedError("The backend session is closed")
        if self._process is not None:
            returncode = self._process.poll()
            if returncode is not None:
                self._shutdown(send_quit=False)
                raise ProtocolError(
                    f"Backend exited (exit status {returncode}); see stderr for diagnostics"
                )

    def __enter__(self) -> TamarinClient:
        return self.start()

    def __exit__(self, exc_type: Any, exc: Any, traceback: Any) -> None:
        self.close()

    def start(self) -> TamarinClient:
        """Start the backend once; return this client."""
        if self._closed:
            raise ClientClosedError("The backend session is closed")
        if self._process is None:
            if self._abort_event is not None and self._abort_event.is_set():
                raise ClientClosedError("The backend session was terminated")
            command = self._process_prefix + backend_command(self._backend)
            try:
                self._process = subprocess.Popen(
                    command,
                    stdin=subprocess.PIPE,
                    stdout=subprocess.PIPE,
                    stderr=self._stderr,
                    text=True,
                    encoding="utf-8",
                    bufsize=1,
                    # Terminal Ctrl-C belongs to the frontend. Forward it as
                    # protocol cancellation, not a process-killing signal.
                    start_new_session=True,
                    cwd=self._cwd,
                )
            except OSError as exc:
                raise BackendUnavailableError(f"Cannot start backend {command[0]!r}: {exc}") from exc
            if self._abort_event is not None and self._abort_event.is_set():
                self._kill_process_group()
                self._shutdown(send_quit=False)
                raise ClientClosedError("The backend session was terminated")
        return self

    def request(self, command: str, **parameters: Any) -> Dict[str, Any]:
        """Issue exactly one command and read exactly one response.

        Commands are never retried: retrying a mutation could apply it twice.
        A protocol failure closes the client instead of silently losing or
        replacing the backend's proof session. By default apply, step, and auto
        handle Ctrl-C as cancellation and must be called on the main thread;
        ``handle_sigint=False`` disables that terminal-only behavior.
        """
        return self._request(
            command, parameters,
            interruptible=self._handle_sigint and command in ("apply", "step", "auto"),
        )

    def _request(
        self, command: str, parameters: Dict[str, Any], *, interruptible: bool = False
    ) -> Dict[str, Any]:
        payload = json.dumps({"command": command, **parameters}, ensure_ascii=False)
        self.start()
        process = self._process
        assert process is not None and process.stdin is not None and process.stdout is not None
        try:
            line = self._exchange(process, payload, interruptible=interruptible)
        except (OSError, UnicodeError) as exc:
            self._shutdown(send_quit=False)
            raise ProtocolError(f"Backend communication failed: {exc}") from exc
        if not line:
            returncode = process.poll()
            self._shutdown(send_quit=False)
            detail = f" (exit status {returncode})" if returncode is not None else ""
            raise ProtocolError(f"Backend closed its output{detail}; see stderr for diagnostics")
        try:
            response = json.loads(line)
        except ValueError as exc:
            self._shutdown(send_quit=False)
            raise ProtocolError(f"Backend returned invalid JSON: {line.rstrip()!r}") from exc
        if not isinstance(response, dict) or response.get("status") not in ("success", "error"):
            self._shutdown(send_quit=False)
            raise ProtocolError(f"Backend returned an invalid response: {response!r}")
        revision = response.get("revision")
        if type(revision) is not int or revision < 0:
            self._shutdown(send_quit=False)
            raise ProtocolError("Backend response has no valid session revision")
        self._revision = revision
        if response["status"] == "error":
            raise BackendError(response)
        return response

    def _exchange(
        self, process: subprocess.Popen[str], payload: str, *, interruptible: bool
    ) -> str:
        assert process.stdin is not None and process.stdout is not None
        sent = False
        cancel_requested = False
        cancel_sent = False

        def send_cancel() -> None:
            nonlocal cancel_sent
            if not cancel_sent:
                cancel_sent = True
                process.stdin.write('{"command":"cancel"}\n')
                process.stdin.flush()

        def interrupt(signum: int, frame: Any) -> None:
            nonlocal cancel_requested
            cancel_requested = True
            if sent:
                send_cancel()

        previous = signal.signal(signal.SIGINT, interrupt) if interruptible else None
        try:
            process.stdin.write(payload + "\n")
            process.stdin.flush()
            sent = True
            if cancel_requested:
                send_cancel()
            # Drain the original response even after cancellation, keeping the
            # JSON-lines stream aligned for the next interactive command.
            if self._max_response_bytes is None:
                return process.stdout.readline()
            # Bound bytes before decoding/JSON parsing, including a response
            # that never terminates its line. Do not mix text and binary reads.
            data = process.stdout.buffer.readline(self._max_response_bytes + 1)
            if len(data) > self._max_response_bytes:
                self._kill_process_group()
                self._shutdown(send_quit=False)
                raise ResponseLimitError("Backend response exceeds max_response_bytes")
            return data.decode("utf-8")
        finally:
            if interruptible:
                signal.signal(signal.SIGINT, previous)

    def load(self, file: Union[str, os.PathLike[str]]) -> Dict[str, Any]:
        """Load a native .spthy theory, including existing proof steps."""
        return self.request("load", file=os.fspath(file))

    def lemmas(self) -> Dict[str, Any]:
        """List lemmas and their backend-reported proof statuses."""
        return self.request("lemmas")

    def lemma(self, name: str) -> Dict[str, Any]:
        """Select or resume a named lemma, without applying a method."""
        return self.request("lemma", name=name)

    def add(self, source: str, *, revision: int) -> Dict[str, Any]:
        """Append one full native lemma declaration and select its fresh proof.

        Pass the latest observed session revision. Changes remain in memory
        until save; an optional proof skeleton is ignored and starts as sorry.
        """
        return self.request("add", source=source, expected_revision=revision)

    def edit(self, name: str, source: str, *, revision: int) -> Dict[str, Any]:
        """Replace a lemma in place, optionally renaming it, with a fresh proof.

        Source is a full native declaration, not a filename. Pass the latest
        observed session revision; save explicitly to persist the replacement.
        """
        return self.request(
            "edit", name=name, source=source, expected_revision=revision
        )

    def delete(self, name: str, *, revision: int) -> Dict[str, Any]:
        """Delete a lemma at the latest observed revision; save to persist it."""
        return self.request("delete", name=name, expected_revision=revision)

    def observe(self, detail: str = "compact") -> Dict[str, Any]:
        """Inspect the selected node with compact, goals, or full detail."""
        return self.request("observe", detail=detail)

    def graph(self) -> Dict[str, Any]:
        """Inspect the selected proof node's expanded GUI constraint graph."""
        return self.request("graph")

    def state(self, detail: str = "compact") -> Dict[str, Any]:
        """Inspect the selected node; request full detail for native state text."""
        return self.request("state", detail=detail)

    def goals(self) -> Dict[str, Any]:
        """List open goals at the selected node."""
        return self.request("goals")

    def methods(self) -> Dict[str, Any]:
        """List applicable methods; IDs are local to the selected node."""
        return self.request("methods")

    def apply(
        self, method_id: int, *, revision: int, timeout_ms: Optional[int] = None
    ) -> Dict[str, Any]:
        """Apply one method; enter its sole child, or stay for a branch choice.

        ``generated_branches`` describes the applied node's children; ordinary
        state fields describe the resulting cursor. No further methods run.
        Pass the revision from the response containing the selected method.
        Stale or missing revisions are rejected without changing the proof.
        An optional positive timeout is in milliseconds. Ctrl-C cancels the
        operation; call on the main thread so SIGINT can be handled.
        """
        parameters = {"method_id": method_id, "expected_revision": revision}
        if timeout_ms is not None:
            if type(timeout_ms) is not int or timeout_ms <= 0:
                raise ValueError("timeout_ms must be a positive integer or None")
            parameters["timeout_ms"] = timeout_ms
        return self.request("apply", **parameters)

    def auto(self, steps: Optional[int] = None) -> Dict[str, Any]:
        """Search the selected subtree; None means no method-application limit.

        Ctrl-C cancels the entire operation and retains the pre-auto session,
        like the GUI's Cancel action. A completed run is one undo entry.
        Called on the main thread so SIGINT can be handled synchronously.
        """
        if steps is not None and (type(steps) is not int or steps < 0):
            raise ValueError("steps must be a non-negative integer or None")
        parameters = {} if steps is None else {"steps": steps}
        return self.request("auto", **parameters)

    def branches(self) -> Dict[str, Any]:
        """List the selected node's immediate child branches."""
        return self.request("branches")

    def branch(self, branch_id: int) -> Dict[str, Any]:
        """Select one immediate child branch (a local zero-based ID)."""
        return self.request("branch", branch_id=branch_id)

    def back(self) -> Dict[str, Any]:
        """Select the parent proof node."""
        return self.request("back")

    def undo(self) -> Dict[str, Any]:
        """Reverse the last proof or lemma mutation, restoring theory and cursor."""
        return self.request("undo")

    def redo(self) -> Dict[str, Any]:
        """Restore the last undone mutation without re-executing its method."""
        return self.request("redo")

    def reset(self) -> Dict[str, Any]:
        """Replace the selected step and its descendants with native sorry."""
        return self.request("reset")

    def tree(self) -> Dict[str, Any]:
        """Return the complete backend-owned proof tree for the selected lemma."""
        return self.request("tree")

    def frontier(self) -> Dict[str, Any]:
        """List unfinished leaf nodes in the selected lemma without navigating."""
        return self.request("frontier")

    def goto(self, node_id: str, *, revision: int) -> Dict[str, Any]:
        """Select a node using the revision of its displayed node listing."""
        return self.request("goto", node_id=node_id, expected_revision=revision)

    def save(self, file: Union[str, os.PathLike[str]]) -> Dict[str, Any]:
        """Serialize the current theory and proofs to native .spthy format."""
        return self.request("save", file=os.fspath(file))

    def check(self) -> Dict[str, Any]:
        """Inspect the current proof, without automatically completing it."""
        return self.request("check")

    def quit(self) -> Dict[str, Any]:
        """Request a normal backend exit and release the subprocess."""
        response = self.request("quit")
        self._shutdown(send_quit=False)
        return response

    def close(self) -> None:
        """End the session, including on REPL EOF; safe to call repeatedly."""
        self._shutdown(send_quit=True)

    def _kill_process_group(self) -> None:
        """Terminate the owned group once, even when deadline and close race."""
        with self._group_kill_lock:
            if self._group_killed:
                return
            process = self._process
            if process is not None:
                try:
                    os.killpg(process.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                self._group_killed = True

    def _shutdown(self, *, send_quit: bool) -> None:
        if self._closed:
            return
        self._closed = True
        process = self._process
        if process is None:
            return
        if self._kill_group:
            # A proof session can own oracle children even after its leader
            # exits. Closing a safety-layer client always releases that group.
            self._kill_process_group()
            send_quit = False
        if process.stdin is not None:
            try:
                if send_quit and process.poll() is None:
                    process.stdin.write('{"command":"quit"}\n')
                    process.stdin.flush()
            except (OSError, UnicodeError):
                pass
            try:
                process.stdin.close()
            except OSError:
                pass
        try:
            process.wait(timeout=5)
        except subprocess.TimeoutExpired:
            try:
                process.terminate()
            except ProcessLookupError:
                pass
            try:
                process.wait(timeout=2)
            except subprocess.TimeoutExpired:
                try:
                    process.kill()
                except ProcessLookupError:
                    pass
                process.wait()
        if process.stdout is not None:
            process.stdout.close()
