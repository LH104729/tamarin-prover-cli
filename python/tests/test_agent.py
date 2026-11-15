"""Real-engine agent safety and session regressions (no optional MCP dependency)."""

from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import shlex
import socket
import sys
import tempfile
import unittest

from tamarin_cli import AgentSession, BackendError
from test_integration import THEORY


class AgentSessionTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory(prefix="tamarin agent ")
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        self.workspace = self.root / "workspace"
        self.workspace.mkdir()
        (self.workspace / "input.spthy").write_text(THEORY)

    def session(self, **limits):
        session = AgentSession(self.workspace, **limits)
        self.addCleanup(session.close)
        return session

    def test_limits_cannot_be_disabled_or_expanded_per_operation(self):
        for field in ("timeout_ms", "cpu_seconds", "max_file_bytes", "max_response_bytes"):
            for value in (0, -1, True, 1.5, float("inf")):
                with self.subTest(field=field, value=value):
                    with self.assertRaises((ValueError, BackendError)):
                        AgentSession(self.workspace, **{field: value})
        session = self.session(timeout_ms=5000)
        session.load("input.spthy")
        before = session.lemma("witness")
        with self.assertRaises(BackendError):
            session.apply(0, revision=before["revision"], timeout_ms=5001)
        self.assertEqual(session.observe(), before)

    def test_persistent_workflow_and_stale_selection(self):
        session = self.session()
        session.load("input.spthy")
        initial = session.lemma("witness")
        simplified = session.apply(0, revision=initial["revision"])
        before = session.observe()
        with self.assertRaises(BackendError) as stale:
            session.apply(0, revision=initial["revision"])
        self.assertEqual(stale.exception.code, "STALE_REVISION")
        self.assertEqual(session.observe(), before)
        self.assertEqual(simplified["revision"], before["revision"])
        listing = session.frontier()
        target = listing["frontier"][0]["node_id"]
        selected = session.goto(target, revision=listing["revision"])
        method = next(m for m in selected["methods"] if m["name"] == "solve")
        session.apply(method["id"], revision=selected["revision"])
        self.assertEqual(session.check()["result"], "verified")
        session.save("saved.spthy")
        session.load("saved.spthy")
        session.lemma("witness")
        self.assertEqual(session.check()["result"], "verified")

    def test_workspace_paths_reject_escape_and_special_files_without_mutation(self):
        session = self.session()
        session.load("input.spthy")
        session.lemma("witness")
        before = session.observe()
        outside = self.root / "outside.spthy"
        outside.write_text(THEORY)
        (self.workspace / "escape.spthy").symlink_to(outside)
        (self.workspace / "external").symlink_to(self.root, target_is_directory=True)
        (self.workspace / "directory.spthy").mkdir()
        for file in ("../outside.spthy", str(outside), "escape.spthy", "external/new.spthy", "directory.spthy", "input.txt"):
            for operation in (session.load, session.save):
                with self.subTest(file=file, operation=operation.__name__):
                    with self.assertRaises(BackendError):
                        operation(file)
                    self.assertEqual(session.observe(), before)
        self.assertEqual(outside.read_text(), THEORY)
        self.assertFalse((self.root / "new.spthy").exists())

    def test_input_and_response_resource_caps(self):
        small = self.session(max_file_bytes=32)
        with self.assertRaises(BackendError) as oversized:
            small.load("input.spthy")
        self.assertEqual(oversized.exception.code, "RESOURCE_LIMIT")
        bounded = self.session(max_response_bytes=128)
        with self.assertRaises(BackendError) as response:
            bounded.load("input.spthy")
        self.assertEqual(response.exception.code, "RESOURCE_LIMIT")
        self.assertFalse(response.exception.recoverable)
        with self.assertRaises(BackendError):
            bounded.observe()

    def test_hard_timeout_closes_blocked_native_session_without_restart(self):
        listener = socket.socket()
        self.addCleanup(listener.close)
        listener.bind(("127.0.0.1", 0))
        listener.listen(1)
        listener.settimeout(15)
        host, port = listener.getsockname()
        oracle = self.workspace / "blocking-oracle"
        program = (
            "import socket, sys\n"
            "sys.stdin.read()\n"
            f"s = socket.create_connection(({host!r}, {port}))\n"
            "s.sendall(b'R')\n"
            "s.recv(1)\n"
        )
        oracle.write_text(f"#!/bin/sh\nexec {shlex.quote(sys.executable)} -c {shlex.quote(program)}\n")
        oracle.chmod(0o700)
        (self.workspace / "blocked.spthy").write_text(
            THEORY.replace("begin\n", 'begin\nheuristic: o "blocking-oracle"\n', 1)
        )
        session = self.session(timeout_ms=3000)
        session.load("blocked.spthy")
        with ThreadPoolExecutor(max_workers=1) as pool:
            future = pool.submit(session.lemma, "witness")
            gate, _ = listener.accept()
            self.addCleanup(gate.close)
            gate.settimeout(15)
            self.assertEqual(gate.recv(1), b"R")
            with self.assertRaises(BackendError) as timed_out:
                future.result(timeout=15)
        self.assertEqual(timed_out.exception.code, "TIMEOUT")
        self.assertFalse(timed_out.exception.recoverable)
        self.assertEqual(gate.recv(1), b"")  # Oracle descendant was terminated too.
        self.assertTrue(session._client._process.stdin.closed)
        self.assertTrue(session._client._process.stdout.closed)
        with self.assertRaises(BackendError) as closed:
            session.observe()
        self.assertFalse(closed.exception.recoverable)


if __name__ == "__main__":
    unittest.main()
