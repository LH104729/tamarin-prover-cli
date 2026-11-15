"""Workspace-confined, resource-bounded access to a persistent proof session.

This is a POSIX safety layer, not an OS sandbox. Theories, their executable
oracles, and concurrent filesystem writers must be trusted. Paths are checked
at dispatch, not protected against hostile concurrent symlink replacement.
Native saves overwrite existing files just as the backend does; a failed save
can leave a partial output. CPU limits cover the backend's cumulative lifetime
CPU (children inherit their own limits), not aggregate descendant CPU usage.
"""

from __future__ import annotations

import os
from pathlib import Path
import shutil
import signal
import stat
import sys
import threading
from typing import Any, Callable, Dict, Optional, Sequence, Union

from .client import (
    BackendError,
    BackendUnavailableError,
    ClientClosedError,
    ProtocolError,
    ResponseLimitError,
    TamarinClient,
    backend_command,
)


def _error(
    code: str, message: str, revision: int = 0, *, recoverable: bool = True
) -> BackendError:
    return BackendError({
        "status": "error",
        "revision": revision,
        "error": {
            "code": code,
            "message": message,
            "recoverable": recoverable,
            "suggested_action": "observe" if recoverable else "create_session",
        },
    })


def _positive_integer(name: str, value: Any, maximum: int) -> int:
    if type(value) is not int or not 0 < value <= maximum:
        raise _error("INVALID_REQUEST", f"{name} must be a positive integer <= {maximum}")
    return value


def _command(backend: Optional[Union[str, Sequence[str]]]) -> list[str]:
    """Prefer the checkout's built executable without running its compiler."""
    command = backend_command(backend)
    if backend is None and "TAMARIN_BACKEND" not in os.environ and "--stack-yaml" in command:
        root = Path(command[command.index("--stack-yaml") + 1]).parent
        candidates = [
            path for path in (root / ".stack-work" / "install").glob("**/bin/tamarin-prover")
            if path.is_file() and os.access(path, os.X_OK)
        ]
        if candidates:
            executable = max(candidates, key=lambda path: path.stat().st_mtime_ns)
            command = [str(executable), "proof-api"]
    if not all(isinstance(part, str) and part and "\x00" not in part for part in command):
        raise BackendUnavailableError("Backend command must contain nonempty string arguments")
    executable = shutil.which(command[0])
    if executable is None:
        raise BackendUnavailableError(f"Cannot find backend executable {command[0]!r}")
    command[0] = str(Path(executable).resolve())
    return command[:-1]  # TamarinClient owns the protocol mode argument.


class AgentSession:
    """One serialized backend session, usable from non-main worker threads.

    Every dispatched operation has a hard wall deadline. Apply passes its budget
    to the backend and permits at most one extra second for cooperative timeout
    rollback. A hard timeout or broken transport kills the whole process group
    and permanently invalidates this session; requests are never replayed.
    Waiting for another caller's lock is itself bounded by ``timeout_ms``.
    """

    def __init__(
        self,
        workspace: Union[str, os.PathLike[str]],
        *,
        backend: Optional[Union[str, Sequence[str]]] = None,
        timeout_ms: int = 30000,
        cpu_seconds: int = 300,
        max_file_bytes: int = 8388608,
        max_response_bytes: int = 8388608,
    ) -> None:
        self._timeout_ms = _positive_integer(
            "timeout_ms", timeout_ms,
            min(sys.maxsize // 1000, int(threading.TIMEOUT_MAX * 1000) - 1000),
        )
        self._cpu_seconds = _positive_integer("cpu_seconds", cpu_seconds, sys.maxsize - 1)
        self._max_file_bytes = _positive_integer("max_file_bytes", max_file_bytes, sys.maxsize - 1)
        _positive_integer("max_response_bytes", max_response_bytes, sys.maxsize - 1)
        if os.name != "posix":
            raise _error("UNSUPPORTED_PLATFORM", "AgentSession requires POSIX resource limits", recoverable=False)
        try:
            import resource
            resource.getrlimit(resource.RLIMIT_CPU)
            resource.getrlimit(resource.RLIMIT_FSIZE)
        except (ImportError, AttributeError, OSError, ValueError) as exc:
            raise _error("UNSUPPORTED_PLATFORM", f"Required POSIX limits unavailable: {exc}", recoverable=False) from exc
        try:
            self._workspace = Path(workspace).resolve(strict=True)
            if not self._workspace.is_dir():
                raise ValueError("workspace must be an existing directory")
        except (OSError, RuntimeError, TypeError, ValueError) as exc:
            raise _error("POLICY_VIOLATION", f"Invalid workspace: {exc}") from exc
        try:
            command = _command(backend)
        except (BackendUnavailableError, OSError, RuntimeError, TypeError, ValueError) as exc:
            raise _error("BACKEND_UNAVAILABLE", str(exc), recoverable=False) from exc
        self._lock = threading.Lock()
        self._closed = False
        self._abort = threading.Event()
        self._client = TamarinClient(
            command,
            handle_sigint=False,
            max_response_bytes=max_response_bytes,
            cwd=self._workspace,
            process_prefix=[
                sys.executable, str(Path(__file__).with_name("_resource_launcher.py").resolve()),
                str(cpu_seconds), str(max_file_bytes),
            ],
            kill_process_group=True,
            abort_event=self._abort,
        )

    @property
    def revision(self) -> int:
        """Last observed revision; zero until the first protocol response."""
        return self._client.revision if self._client.revision is not None else 0

    def __enter__(self) -> AgentSession:
        # Start lazily on the first bounded request, not outside its wall timer.
        if self._closed:
            raise self._failure("SESSION_CLOSED", "The backend session is closed", recoverable=False)
        return self

    def __exit__(self, exc_type: Any, exc: Any, traceback: Any) -> None:
        self.close()

    def _failure(self, code: str, message: str, *, recoverable: bool = True) -> BackendError:
        return _error(code, message, self.revision, recoverable=recoverable)

    def _invalidate(self) -> None:
        self._closed = True
        self._abort.set()
        self._client._kill_process_group()
        self._client.close()

    def close(self) -> None:
        """Kill the owned process group and release its pipes; idempotent."""
        # Wake a blocked request immediately; its owner performs serialized
        # transport cleanup. No quit write can block behind an unresponsive child.
        self._abort.set()
        self._client._kill_process_group()
        with self._lock:
            self._invalidate()

    def _invoke(
        self, operation: Callable[[], Dict[str, Any]], *, wall_ms: Optional[int] = None
    ) -> Dict[str, Any]:
        if not self._lock.acquire(timeout=self._timeout_ms / 1000):
            raise self._failure("TIMEOUT", "Timed out waiting for another session operation")
        try:
            if self._closed or self._abort.is_set():
                raise self._failure("SESSION_CLOSED", "The backend session is closed", recoverable=False)
            expired = threading.Event()

            def expire() -> None:
                expired.set()
                self._abort.set()
                self._client._kill_process_group()

            timer = threading.Timer((wall_ms or self._timeout_ms) / 1000, expire)
            timer.daemon = True
            timer.start()
            result = None
            failure = None
            try:
                result = operation()
            except BackendError as exc:
                failure = exc
            except ResponseLimitError as exc:
                failure = self._failure("RESOURCE_LIMIT", str(exc), recoverable=False)
            except BackendUnavailableError as exc:
                failure = self._failure("BACKEND_UNAVAILABLE", str(exc), recoverable=False)
            except (ProtocolError, ClientClosedError, OSError, UnicodeError) as exc:
                process = self._client._process
                status = process.poll() if process is not None else None
                resource_signals = (-signal.SIGXCPU, -signal.SIGXFSZ, -signal.SIGKILL)
                code = "RESOURCE_LIMIT" if status in resource_signals else "PROTOCOL_ERROR"
                failure = self._failure(code, str(exc), recoverable=False)
            except Exception as exc:
                failure = self._failure("INTERNAL_ERROR", str(exc), recoverable=False)
            finally:
                # Joining, not just cancelling, excludes a callback racing with
                # completion and killing a later request's process group.
                timer.cancel()
                timer.join()
            if expired.is_set():
                self._invalidate()
                raise self._failure("TIMEOUT", "Hard wall deadline exceeded; session terminated", recoverable=False)
            if self._abort.is_set():
                self._invalidate()
                raise self._failure("SESSION_CLOSED", "The backend session was closed", recoverable=False)
            if failure is not None:
                if not failure.recoverable:
                    self._invalidate()
                raise failure
            assert result is not None
            return result
        finally:
            self._lock.release()

    def _path(self, file: Union[str, os.PathLike[str]], *, saving: bool) -> Path:
        try:
            path = Path(file)
            if ".." in path.parts:
                raise ValueError("parent traversal is not permitted")
            if path.suffix != ".spthy":
                raise ValueError("only native .spthy files are permitted")
            if not path.is_absolute():
                path = self._workspace / path
            path = path.resolve(strict=not saving)
            if not path.is_relative_to(self._workspace):
                raise ValueError("path escapes the workspace")
            if path.suffix != ".spthy":
                raise ValueError("the resolved file must have a .spthy suffix")
            if not path.parent.is_dir():
                raise ValueError("the destination parent must already exist")
            try:
                metadata = path.stat()
            except FileNotFoundError:
                if not saving:
                    raise
            else:
                if not stat.S_ISREG(metadata.st_mode):
                    raise ValueError("the native file must be regular")
                if metadata.st_size > self._max_file_bytes:
                    raise self._failure("RESOURCE_LIMIT", "Native file exceeds max_file_bytes")
            return path
        except BackendError:
            raise
        except (OSError, RuntimeError, TypeError, ValueError) as exc:
            raise self._failure("POLICY_VIOLATION", f"Rejected native file path: {exc}") from exc

    def _integer(self, name: str, value: Any) -> None:
        if type(value) is not int or not 0 <= value <= sys.maxsize:
            raise self._failure("INVALID_REQUEST", f"{name} must be a non-negative integer")

    def load(self, file: Union[str, os.PathLike[str]]) -> Dict[str, Any]:
        return self._invoke(lambda: self._client.load(self._path(file, saving=False)))

    def lemma(self, name: str) -> Dict[str, Any]:
        def operation() -> Dict[str, Any]:
            if not isinstance(name, str):
                raise self._failure("INVALID_REQUEST", "name must be a string")
            return self._client.lemma(name)
        return self._invoke(operation)

    def observe(self, detail: str = "compact") -> Dict[str, Any]:
        def operation() -> Dict[str, Any]:
            if not isinstance(detail, str) or detail not in ("compact", "goals", "full"):
                raise self._failure("INVALID_REQUEST", "detail must be compact, goals, or full")
            return self._client.observe(detail)
        return self._invoke(operation)

    def graph(self) -> Dict[str, Any]:
        """Inspect the constraint graph within the session's resource bounds."""
        return self._invoke(self._client.graph)

    def apply(
        self, method_id: int, *, revision: int, timeout_ms: Optional[int] = None
    ) -> Dict[str, Any]:
        budget = self._timeout_ms if timeout_ms is None else timeout_ms

        def operation() -> Dict[str, Any]:
            self._integer("method_id", method_id)
            self._integer("revision", revision)
            if type(budget) is not int or not 0 < budget <= self._timeout_ms:
                raise self._failure("INVALID_REQUEST", "timeout_ms must be positive and cannot exceed the session budget")
            return self._client.apply(method_id, revision=revision, timeout_ms=budget)

        # Validate before timer arithmetic without leaking non-structured errors.
        wall = budget + 1000 if type(budget) is int and 0 < budget <= self._timeout_ms else self._timeout_ms
        return self._invoke(operation, wall_ms=wall)

    def frontier(self) -> Dict[str, Any]:
        return self._invoke(self._client.frontier)

    def goto(self, node_id: str, *, revision: int) -> Dict[str, Any]:
        def operation() -> Dict[str, Any]:
            self._integer("revision", revision)
            if not isinstance(node_id, str):
                raise self._failure("INVALID_REQUEST", "node_id must be a string")
            return self._client.goto(node_id, revision=revision)
        return self._invoke(operation)

    def save(self, file: Union[str, os.PathLike[str]]) -> Dict[str, Any]:
        def operation() -> Dict[str, Any]:
            path = self._path(file, saving=True)
            try:
                result = self._client.save(path)
            except BackendError as exc:
                if path.exists() and path.stat().st_size >= self._max_file_bytes:
                    raise self._failure("RESOURCE_LIMIT", "Native output reached max_file_bytes") from exc
                raise
            if path.stat().st_size > self._max_file_bytes:
                raise self._failure("RESOURCE_LIMIT", "Native output exceeds max_file_bytes", recoverable=False)
            return result
        return self._invoke(operation)

    def check(self) -> Dict[str, Any]:
        return self._invoke(self._client.check)
