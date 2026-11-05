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
import shutil
import subprocess
from typing import Any, Dict, Optional, Sequence, TextIO, Union


class TamarinError(Exception):
    """Base class for backend startup, transport, and command errors."""


class BackendError(TamarinError):
    """A rejected command; the backend session remains available.

    ``response`` retains the entire backend error object for API callers.
    """

    def __init__(self, response: Dict[str, Any]) -> None:
        self.response = response
        super().__init__(str(response.get("message", "Backend rejected command")))


class BackendUnavailableError(TamarinError):
    """The configured backend could not be started."""


class ProtocolError(TamarinError):
    """The backend exited or returned something other than a protocol response."""


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
    """

    def __init__(
        self,
        backend: Optional[Union[str, Sequence[str]]] = None,
        *,
        stderr: Optional[TextIO] = None,
    ) -> None:
        self._backend = backend
        self._stderr = stderr
        self._process: Optional[subprocess.Popen[str]] = None
        self._closed = False
        self._revision: Optional[int] = None

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
            command = backend_command(self._backend)
            try:
                self._process = subprocess.Popen(
                    command,
                    stdin=subprocess.PIPE,
                    stdout=subprocess.PIPE,
                    stderr=self._stderr,
                    text=True,
                    encoding="utf-8",
                    bufsize=1,
                )
            except OSError as exc:
                raise BackendUnavailableError(f"Cannot start backend {command[0]!r}: {exc}") from exc
        return self

    def request(self, command: str, **parameters: Any) -> Dict[str, Any]:
        """Issue exactly one command and read exactly one response.

        Commands are never retried: retrying a mutation could apply it twice.
        A protocol failure closes the client instead of silently losing or
        replacing the backend's proof session.
        """
        payload = json.dumps({"command": command, **parameters}, ensure_ascii=False)
        self.start()
        process = self._process
        assert process is not None and process.stdin is not None and process.stdout is not None
        try:
            process.stdin.write(payload + "\n")
            process.stdin.flush()
            line = process.stdout.readline()
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

    def load(self, file: Union[str, os.PathLike[str]]) -> Dict[str, Any]:
        """Load a native .spthy theory, including existing proof steps."""
        return self.request("load", file=os.fspath(file))

    def lemmas(self) -> Dict[str, Any]:
        """List lemmas and their backend-reported proof statuses."""
        return self.request("lemmas")

    def lemma(self, name: str) -> Dict[str, Any]:
        """Select or resume a named lemma, without applying a method."""
        return self.request("lemma", name=name)

    def state(self) -> Dict[str, Any]:
        """Return the selected node's constraints, goals, methods, and branches."""
        return self.request("state")

    def goals(self) -> Dict[str, Any]:
        """List open goals at the selected node."""
        return self.request("goals")

    def methods(self) -> Dict[str, Any]:
        """List applicable methods; IDs are local to the selected node."""
        return self.request("methods")

    def apply(self, method_id: int, *, revision: int) -> Dict[str, Any]:
        """Apply one method; enter its sole child, or stay for a branch choice.

        ``generated_branches`` describes the applied node's children; ordinary
        state fields describe the resulting cursor. No further methods run.
        Pass the revision from the response containing the selected method.
        Stale or missing revisions are rejected without changing the proof.
        """
        return self.request("apply", method_id=method_id, expected_revision=revision)

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
        """Reverse the last proof mutation, restoring its theory and cursor."""
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

    def _shutdown(self, *, send_quit: bool) -> None:
        if self._closed:
            return
        self._closed = True
        process = self._process
        if process is None:
            return
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
