"""Real-engine regressions; run from the checkout after `stack build`.

    PYTHONPATH=python python3 -m unittest discover -s python/tests -v

TAMARIN_BACKEND can select another built executable. No mocked proof engine.
"""

import io
import json
import os
import select
import shlex
import socket
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from tamarin_cli import BackendError, ClientClosedError, ProtocolError, TamarinClient
from tamarin_cli.client import backend_command
from tamarin_cli.repl import TamarinShell


THEORY = """theory CLI_Regression
begin
functions: tag/1
rule Left: [] --[ Pick(tag('left')) ]-> []
rule Right: [] --[ Pick(tag('right')) ]-> []
lemma witness: exists-trace "Ex x #i. Pick(x) @ i" by sorry
lemma safety: all-traces "All x #i. Pick(x) @ i ==> x = tag('left')" by sorry
lemma reflexive: all-traces "All x #i. Pick(x) @ i ==> x = x" by sorry
end
"""

SOURCE_THEORY = """theory CLI_Source
begin
macros: identity(x) = x
rule Emit: [] --[ Seen(identity('value')) ]-> []
restriction Once: "All #i #j. Seen(identity('value')) @ i & Seen(identity('value')) @ j ==> #i = #j"
lemma event: exists-trace "Ex #i. Seen(identity('value')) @ i" by sorry
lemma unique: all-traces "All #i #j. Seen(identity('value')) @ i & Seen(identity('value')) @ j ==> #i = #j" by sorry
end
"""


class ProofIntegrationTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory(prefix="tamarin cli tests ")
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        self.file = self.root / "input theory.spthy"
        self.file.write_text(THEORY, encoding="utf-8")
        self.client = TamarinClient()
        self.addCleanup(self.client.close)
        self.client.load(self.file)

    def step(self, prefix):
        listing = self.client.methods()
        chosen = next(method for method in listing["methods"] if method["text"].startswith(prefix))
        return self.client.apply(chosen["id"], revision=listing["revision"])

    def proof_view(self):
        response = self.client.tree()
        response.pop("revision")
        return response

    def split(self, lemma):
        self.client.lemma(lemma)
        self.step("simplify")
        return self.step("solve(")

    def assert_error_response(self, response, *, code=None, revision=None):
        self.assertEqual(response["status"], "error")
        error = response["error"]
        self.assertIsInstance(error, dict)
        if code is not None:
            self.assertEqual(error["code"], code)
        self.assertIsInstance(error["code"], str)
        self.assertTrue(error["code"])
        self.assertIsInstance(error["message"], str)
        self.assertTrue(error["message"])
        self.assertIs(type(error["recoverable"]), bool)
        self.assertIsInstance(error["suggested_action"], str)
        self.assertTrue(error["suggested_action"])
        self.assertIs(type(response["revision"]), int)
        if revision is not None:
            self.assertEqual(response["revision"], revision)

    def assert_compact(self, response):
        for key in (
            "lemma", "node_id", "branch_status", "goal_count",
            "children_count", "methods", "branches",
        ):
            self.assertIn(key, response)
        self.assertNotIn("goals", response)
        self.assertNotIn("constraints", response)
        self.assertNotIn("state", response)
        self.assertIs(type(response["goal_count"]), int)
        self.assertGreaterEqual(response["goal_count"], 0)
        self.assertEqual(response["children_count"], len(response["branches"]))

    def ranking_oracle_gate(self):
        listener = socket.socket()
        self.addCleanup(listener.close)
        listener.bind(("127.0.0.1", 0))
        listener.listen(1)
        listener.settimeout(15)
        host, port = listener.getsockname()
        armed = self.root / "oracle-armed"
        self.addCleanup(armed.unlink, missing_ok=True)
        oracle = self.root / "ranking-oracle"
        program = (
            "import pathlib, socket, sys\n"
            "goals = sys.stdin.read().splitlines()\n"
            f"if pathlib.Path({str(armed)!r}).exists():\n"
            f"    with socket.create_connection(({host!r}, {port}), timeout=15) as gate:\n"
            "        gate.settimeout(None)\n"
            "        gate.sendall(b'R')\n"
            "        gate.recv(1)\n"
            "for goal in goals:\n"
            "    print(goal.split(':', 1)[0])\n"
        )
        oracle.write_text(
            f"#!/bin/sh\nexec {shlex.quote(sys.executable)} -c {shlex.quote(program)}\n",
            encoding="utf-8",
        )
        oracle.chmod(0o700)
        theory = self.root / "oracle.spthy"
        theory.write_text(
            THEORY.replace("begin\n", 'begin\nheuristic: o "ranking-oracle"\n', 1),
            encoding="utf-8",
        )
        self.client.load(theory)
        return listener, armed

    @staticmethod
    def release_oracle_gate(gate):
        try:
            gate.sendall(b'R')
        except OSError:
            pass  # Cancellation may already have closed the oracle connection.
        finally:
            gate.close()

    def accept_oracle_gate(self, listener):
        gate, _ = listener.accept()
        self.addCleanup(self.release_oracle_gate, gate)
        gate.settimeout(15)
        self.assertEqual(gate.recv(1), b"R")
        return gate

    def test_observation_projection_counts_and_method_goal_links(self):
        selected = self.client.lemma("witness")
        self.assert_compact(selected)
        initial = self.client.observe()
        self.assert_compact(initial)
        self.assertEqual(self.client.state(), initial)
        simplified = self.step("simplify")
        self.assert_compact(simplified)
        compact = self.client.observe()
        goals = self.client.observe(detail="goals")
        full = self.client.observe(detail="full")
        for response in (goals, full):
            self.assertEqual(
                {key: response[key] for key in compact}, compact
            )
            self.assertEqual(response["goal_count"], len(response["goals"]))
            self.assertIsInstance(response["constraints"], dict)
            self.assertTrue(response["constraints"])
        self.assertNotIn("state", goals)
        self.assertIsInstance(full["state"], str)
        self.assertTrue(full["state"])
        self.assertEqual(
            {key: full[key] for key in goals}, goals
        )
        self.assertEqual(self.client.state(detail="goals"), goals)
        self.assertEqual(self.client.state(detail="full"), full)
        self.assertEqual(self.client.goals()["goals"], goals["goals"])
        self.assertEqual(self.client.methods()["methods"], compact["methods"])
        goal_ids = set()
        for goal in goals["goals"]:
            self.assertIs(type(goal["id"]), int)
            self.assertEqual(goal["goal_id"], f"g{goal['id']}")
            goal_ids.add(goal["goal_id"])
        linked = []
        for method in compact["methods"]:
            self.assertIs(type(method["id"]), int)
            for key in ("text", "name", "kind"):
                self.assertIsInstance(method[key], str)
                self.assertTrue(method[key])
            if "goal_id" in method:
                self.assertIn(method["goal_id"], goal_ids)
                linked.append(method)
        self.assertTrue(linked)
        split = self.step("solve(")
        self.assert_compact(split)
        self.assertEqual(split["children_count"], 2)
        self.assertEqual(self.client.observe()["revision"], split["revision"])
        self.assert_compact(self.client.undo())
        self.assert_compact(self.client.redo())

    def test_goto_requires_current_revision_and_canonical_existing_node(self):
        split = self.split("witness")
        listing = self.client.frontier()
        self.assertEqual(listing["revision"], split["revision"])
        target = split["branches"][0]["node_id"]
        selected = self.client.goto(target, revision=listing["revision"])
        self.assertEqual(selected["node_id"], target)
        self.assertGreater(selected["revision"], listing["revision"])
        self.assert_compact(selected)
        before = self.client.tree()
        state = self.client.state(detail="full")
        invalid_requests = [
            ({"node_id": "0", "expected_revision": listing["revision"]}, "STALE_REVISION"),
            ({"node_id": "0"}, "INVALID_REQUEST"),
        ]
        invalid_requests.extend(
            ({"node_id": path, "expected_revision": selected["revision"]}, "INVALID_NODE")
            for path in (
                "", "1", "00", "0.", ".0", "0..0", "0.01",
                "0.-1", "0.+1", "0.1x", "0.999999",
            )
        )
        invalid_requests.extend(
            ({"node_id": path, "expected_revision": selected["revision"]}, "INVALID_REQUEST")
            for path in (0, None, [], {})
        )
        for parameters, code in invalid_requests:
            with self.subTest(parameters=parameters):
                with self.assertRaises(BackendError) as rejected:
                    self.client.request("goto", **parameters)
                self.assert_error_response(
                    rejected.exception.response, code=code, revision=selected["revision"]
                )
                self.assertEqual(self.client.tree(), before)
                self.assertEqual(self.client.state(detail="full"), state)
        root = self.client.goto("0", revision=selected["revision"])
        self.assertEqual(root["node_id"], "0")
        self.assertGreater(root["revision"], selected["revision"])
        old_nodes = self.client.frontier()
        safety = self.client.lemma("safety")
        with self.assertRaises(BackendError) as stale:
            self.client.goto(target, revision=old_nodes["revision"])
        self.assert_error_response(
            stale.exception.response, code="STALE_REVISION", revision=safety["revision"]
        )
        with self.assertRaises(BackendError) as absent:
            self.client.goto(target, revision=safety["revision"])
        self.assert_error_response(
            absent.exception.response, code="INVALID_NODE", revision=safety["revision"]
        )
        self.assertEqual(self.client.state(), safety)

    def test_frontier_lists_only_unfinished_leaves_across_selected_lemma(self):
        self.client.lemma("safety")
        self.step("induction")
        tree = self.client.tree()
        expected = {}

        def collect(node):
            if not node["children"] and node["method"] == "sorry":
                expected[node["node_id"]] = node["status"]
            for child in node["children"]:
                collect(child)

        collect(tree["tree"])
        self.assertTrue(expected)
        complete = next(
            branch for branch in self.client.branches()["branches"]
            if branch["status"] == "contradictory"
        )
        self.client.branch(complete["id"])
        state = self.client.state()
        listing = self.client.frontier()
        self.assertEqual(listing["lemma"], "safety")
        self.assertEqual(listing["revision"], state["revision"])
        self.assertEqual(
            {node["node_id"]: node["branch_status"] for node in listing["frontier"]},
            expected,
        )
        self.assertEqual(len(listing["frontier"]), len(expected))
        for node in listing["frontier"]:
            self.assertNotEqual(node["node_id"], state["node_id"])
            self.assertIs(type(node["goal_count"]), int)
            self.assertGreaterEqual(node["goal_count"], 0)
        self.assertEqual(self.client.state(), state)
        for node in listing["frontier"]:
            revision = self.client.frontier()["revision"]
            selected = self.client.goto(node["node_id"], revision=revision)
            self.assertEqual(selected["goal_count"], node["goal_count"])
            self.assertEqual(selected["branch_status"], node["branch_status"])
            self.client.auto()
        self.assertEqual(self.client.frontier()["frontier"], [])
        self.client.lemma("witness")
        witness = self.client.frontier()
        self.assertEqual(witness["lemma"], "witness")
        self.assertEqual([node["node_id"] for node in witness["frontier"]], ["0"])

    def test_invalid_observation_and_step_requests_are_structured_and_transactional(self):
        self.client.lemma("witness")
        self.step("simplify")
        self.client.undo()
        state = self.client.state()
        tree = self.client.tree()
        method = state["methods"][0]["id"]
        requests = [
            ("observe", {"detail": "invalid"}),
            ("state", {"detail": 1}),
            ("apply", {"method_id": method}),
            ("step", {"method_id": method}),
        ]
        for command in ("apply", "step"):
            requests.extend(
                (command, {
                    "method_id": method, "expected_revision": state["revision"],
                    "timeout_ms": invalid,
                })
                for invalid in (0, -1, 1.5, "1", True, None, [], {})
            )
        for command, parameters in requests:
            with self.subTest(command=command, parameters=parameters):
                with self.assertRaises(BackendError) as rejected:
                    self.client.request(command, **parameters)
                self.assert_error_response(
                    rejected.exception.response, code="INVALID_REQUEST", revision=state["revision"]
                )
                self.assertEqual(self.client.state(), state)
                self.assertEqual(self.client.tree(), tree)
        self.client.redo()  # Invalid requests must not discard the pending redo.

    def test_manual_navigation_undo_and_native_round_trip(self):
        self.client.lemma("witness")
        initial = self.proof_view()["tree"]
        self.client.state()
        self.client.goals()
        self.client.methods()
        self.assertEqual(self.client.check()["result"], "incomplete")
        self.assertEqual(self.proof_view()["tree"], initial)

        self.step("simplify")
        # Simplify must not silently select and solve the remaining goal.
        self.assertEqual(self.proof_view()["tree"]["children"][0]["method"], "sorry")
        self.assertTrue(any("Pick" in goal["text"] for goal in self.client.goals()["goals"]))
        self.step("solve(")
        branches = self.client.branches()["branches"]
        self.assertEqual({branch["name"] for branch in branches}, {"Left", "Right"})
        left = next(branch for branch in branches if branch["name"] == "Left")
        right = next(branch for branch in branches if branch["name"] == "Right")
        self.client.branch(left["id"])
        left_state = self.client.state()
        self.client.lemma("safety")
        self.assertEqual(self.client.lemma("witness")["node_id"], left_state["node_id"])
        self.client.back()
        self.client.branch(right["id"])
        self.assertIn("right", self.client.state(detail="full")["state"])
        self.client.reset()
        partial = self.proof_view()
        shell = TamarinShell(self.client, stdout=io.StringIO())
        shell.onecmd("undo")
        self.assertEqual(self.client.check()["result"], "verified")
        undone = self.proof_view()
        shell.onecmd("")
        self.assertEqual(self.proof_view(), undone)
        self.client.redo()
        self.assertEqual(self.proof_view(), partial)
        self.assertEqual(self.client.check()["result"], "incomplete")
        retained = self.proof_view()["tree"]
        self.assertEqual(retained["status"], "open")
        self.assertEqual(retained["children"][0]["status"], "open")
        self.assertEqual(retained["children"][0]["children"][left["id"]]["status"], "solved")
        self.assertEqual(retained["children"][0]["children"][right["id"]]["method"], "sorry")

        saved = self.root / "partial proof.spthy"
        self.client.save(saved)
        self.client.load(saved)
        self.client.lemma("witness")
        self.assertEqual(self.proof_view()["tree"], retained)
        self.assertEqual(self.client.check()["result"], "incomplete")
        # Original CLI replays the saved native proof rather than rejecting it.
        original = subprocess.run(
            backend_command()[:-1] + [str(saved)], capture_output=True, text=True, timeout=60
        )
        self.assertEqual(original.returncode, 0, original.stderr)
        self.assertIn("safety (all-traces): analysis incomplete", original.stdout)

    def test_quantifiers_terminal_branches_and_completed_reload(self):
        self.split("witness")
        self.assertEqual(self.client.check()["result"], "verified")
        result = self.split("safety")
        self.assertEqual({branch["status"] for branch in result["branches"]}, {"solved", "contradictory"})
        self.assertEqual(self.client.check()["result"], "falsified")
        self.client.lemma("reflexive")
        self.step("simplify")
        self.assertEqual(self.client.check()["result"], "verified")
        saved = self.root / "completed.spthy"
        self.client.save(saved)
        self.client.load(saved)
        for name, expected in [("witness", "verified"), ("safety", "falsified"), ("reflexive", "verified")]:
            self.client.lemma(name)
            self.assertEqual(self.client.check()["result"], expected)

    def test_induction_partial_proof_round_trip(self):
        self.client.lemma("safety")
        self.step("induction")
        branches = self.client.branches()["branches"]
        self.assertEqual({branch["status"] for branch in branches}, {"contradictory", "open"})
        self.assertEqual(self.client.check()["result"], "incomplete")
        saved = self.root / "induction.spthy"
        self.client.save(saved)
        self.client.load(saved)
        state = self.client.lemma("safety")
        self.assertEqual(state["branches"], branches)
        self.assertEqual(self.client.check()["result"], "incomplete")
        open_branch = next(branch for branch in branches if branch["status"] == "open")
        self.client.branch(open_branch["id"])
        self.assertTrue(any("Pick" in method["text"] for method in self.client.methods()["methods"]))

    def test_errors_are_transactional(self):
        self.client.lemma("witness")
        self.step("simplify")
        before = self.proof_view()
        state = self.client.state()
        operations = [
            (lambda: self.client.apply(-1, revision=state["revision"]), "INVALID_METHOD"),
            (lambda: self.client.apply(999, revision=state["revision"]), "INVALID_METHOD"),
            (lambda: self.client.branch(999), "INVALID_NODE"),
            (lambda: self.client.lemma("missing"), None),
            (lambda: self.client.load(self.root / "missing.spthy"), "IO_ERROR"),
            (lambda: self.client.request("unknown"), "INVALID_REQUEST"),
        ]
        for operation, code in operations:
            with self.assertRaises(BackendError) as rejected:
                operation()
            self.assert_error_response(
                rejected.exception.response, code=code, revision=state["revision"]
            )
            self.assertEqual(self.proof_view(), before)
            self.assertEqual(self.client.state(), state)

    def test_source_macros_and_restrictions(self):
        source = self.root / "source.spthy"
        source.write_text(SOURCE_THEORY, encoding="utf-8")
        self.client.load(source)
        self.client.lemma("event")
        self.step("simplify")
        before = self.proof_view()
        saved = self.root / "saved source.spthy"
        self.client.lemma("unique")
        self.step("simplify")
        # The restriction makes the counterexample impossible immediately.
        self.assertEqual(self.client.check()["result"], "verified")
        self.client.save(saved)
        self.client.load(saved)
        self.client.lemma("event")
        self.assertEqual(self.proof_view(), before)
        self.client.lemma("unique")
        self.assertEqual(self.client.check()["result"], "verified")

    def test_history_restores_mutations_across_navigation_and_lemmas(self):
        self.client.lemma("witness")
        first = self.step("simplify")
        self.assertEqual(first["applied_at"], "0")
        self.assertEqual(first["node_id"], first["generated_branches"][0]["node_id"])
        self.assertTrue(first["methods"])  # No follow-up solve was executed.
        simplified = self.proof_view()
        split = self.step("solve(")
        self.assertEqual(split["node_id"], split["applied_at"])
        completed = self.proof_view()
        self.client.lemma("safety")
        self.step("induction")
        induction = self.proof_view()
        self.client.lemma("witness")
        self.client.back()
        self.client.check()
        self.client.save(self.root / "history.spthy")

        restored = self.client.undo()
        self.assertEqual(restored["lemma"], "safety")
        self.assertEqual(restored["node_id"], "0")
        self.assertFalse(self.proof_view()["tree"]["children"])
        restored = self.client.undo()
        self.assertEqual(restored["lemma"], "witness")
        self.assertEqual(restored["node_id"], first["node_id"])
        self.assertEqual(self.proof_view(), simplified)
        self.client.redo()
        self.assertEqual(self.proof_view(), completed)
        self.client.redo()
        self.assertEqual(self.proof_view(), induction)

        self.client.reset()
        cleared = self.proof_view()
        self.assertFalse(cleared["tree"]["children"])
        self.client.undo()
        self.assertEqual(self.proof_view(), induction)
        with self.assertRaises(BackendError):
            self.client.apply(999, revision=self.client.state()["revision"])
        self.client.redo()  # A failed mutation must not discard redo.
        self.assertEqual(self.proof_view(), cleared)
        self.client.undo()
        self.client.reset()  # A successful alternative mutation discards redo.
        with self.assertRaises(BackendError):
            self.client.redo()
        with self.assertRaises(BackendError):
            self.client.reset()  # Empty sorry has no subtree to discard.
        self.client.load(self.file)
        for operation in (self.client.undo, self.client.redo):
            with self.assertRaises(BackendError):
                operation()

    def test_stale_method_selection_cannot_mutate_another_state(self):
        self.client.lemma("witness")
        listing = self.client.methods()
        chosen = listing["methods"][0]["id"]
        # Both lemma roots offer method 0: an index alone is not safe.
        current = self.client.lemma("safety")
        before = self.proof_view()
        with self.assertRaises(BackendError) as stale:
            self.client.apply(chosen, revision=listing["revision"])
        self.assertEqual(stale.exception.response["revision"], current["revision"])
        self.assertEqual(self.proof_view(), before)
        self.assertEqual(self.client.state(), current)
        with self.assertRaises(BackendError):
            self.client.request("apply", method_id=chosen)
        with self.assertRaises(BackendError):
            self.client.request("step", method_id=chosen, expected_revision=listing["revision"])
        # Read-only inspection and saving do not invalidate the selection.
        fresh = self.client.methods()
        self.client.goals()
        self.client.save(self.root / "revision.spthy")
        applied = self.client.apply(fresh["methods"][0]["id"], revision=fresh["revision"])
        self.assertGreater(applied["revision"], fresh["revision"])
        undone = self.client.undo()
        self.assertGreater(undone["revision"], applied["revision"])
        with self.assertRaises(BackendError):
            self.client.apply(chosen, revision=fresh["revision"])
        redone = self.client.redo()
        self.assertGreater(redone["revision"], undone["revision"])
        reloaded = self.client.load(self.file)
        self.assertGreater(reloaded["revision"], redone["revision"])
        self.client.lemma("witness")
        with self.assertRaises(BackendError):
            self.client.apply(chosen, revision=listing["revision"])

    def test_auto_bounds_count_native_applications_exactly(self):
        for limit in (1, 2):
            with self.subTest(steps=limit):
                self.client.load(self.file)
                self.client.lemma("witness")
                for _ in range(limit):
                    listing = self.client.methods()
                    self.client.apply(listing["methods"][0]["id"], revision=listing["revision"])
                # Manual apply enters sole children; auto keeps its original
                # subtree selected so the next call can resume that scope.
                while self.client.state()["node_id"] != "0":
                    self.client.back()
                expected = self.proof_view()
                expected_state = self.client.state()
                expected_state.pop("revision")

                self.client.load(self.file)
                self.client.lemma("witness")
                result = self.client.auto(limit)
                self.assertEqual(result["auto_steps"], limit)
                self.assertEqual(result["auto_reason"], "step_limit")
                self.assertEqual(self.proof_view(), expected)
                self.assertEqual(
                    {key: result[key] for key in expected_state}, expected_state
                )

    def test_auto_unbounded_completes_and_finished_auto_is_unchanged(self):
        for lemma, expected in (
            ("witness", "verified"), ("safety", "falsified"), ("reflexive", "verified")
        ):
            with self.subTest(lemma=lemma):
                self.client.lemma(lemma)
                result = self.client.auto()
                self.assertIs(type(result["auto_steps"]), int)
                self.assertGreater(result["auto_steps"], 0)
                self.assertEqual(result["auto_reason"], "finished")
                state = self.client.state()
                for key, value in state.items():
                    self.assertEqual(result[key], value)
                self.assertEqual(self.client.check()["result"], expected)
                state = self.client.state()
                before = self.client.tree()
                finished = self.client.auto()
                self.assertEqual(finished["auto_steps"], 0)
                self.assertEqual(finished["auto_reason"], "finished")
                self.assertEqual(self.client.state(), state)
                self.assertEqual(self.client.tree(), before)

    def test_auto_retains_split_and_stays_in_selected_subtree(self):
        split = self.split("witness")
        branches = split["branches"]
        self.assertEqual(len(branches), 2)
        # Reopen both native terminal cases, retaining their parent split.
        for branch in branches:
            self.client.branch(branch["id"])
            self.client.reset()
            self.client.back()
        before = self.proof_view()["tree"]
        parent = before["children"][0]
        self.assertEqual({child["status"] for child in parent["children"]}, {"open"})
        left, right = branches

        self.client.branch(left["id"])
        selected = self.client.state()["node_id"]
        result = self.client.auto()
        self.assertGreater(result["auto_steps"], 0)
        self.assertEqual(result["auto_reason"], "finished")
        self.assertEqual(result["node_id"], selected)
        after = self.proof_view()["tree"]
        retained = after["children"][0]
        self.assertEqual(after["method"], before["method"])
        self.assertEqual(retained["method"], parent["method"])
        self.assertEqual(retained["children"][left["id"]]["status"], "solved")
        self.assertEqual(retained["children"][right["id"]], parent["children"][right["id"]])
        self.assertEqual(self.client.check()["result"], "incomplete")

        # Starting at the retained split must traverse, not reapply it or
        # charge navigation/its already-finished child against the limit.
        self.assertEqual(self.client.back()["node_id"], split["node_id"])
        result = self.client.auto(1)
        self.assertEqual(result["auto_steps"], 1)
        self.assertEqual(result["auto_reason"], "step_limit")
        completed = self.proof_view()["tree"]
        self.assertEqual(
            completed["children"][0]["children"][left["id"]],
            retained["children"][left["id"]],
        )
        self.assertEqual(self.client.check()["result"], "verified")

    def test_auto_bounded_calls_resume_siblings_without_changing_scope(self):
        split = self.split("witness")
        branches = split["branches"]
        self.assertEqual(len(branches), 2)
        for branch in branches:
            self.client.branch(branch["id"])
            self.client.reset()
            self.client.back()
        initial = self.proof_view()
        left, right = branches

        first = self.client.auto(1)
        self.assertEqual(first["auto_steps"], 1)
        self.assertEqual(first["auto_reason"], "step_limit")
        self.assertEqual(first["node_id"], split["node_id"])
        partial = self.proof_view()
        children = partial["tree"]["children"][0]["children"]
        self.assertEqual(children[left["id"]]["status"], "solved")
        self.assertEqual(children[right["id"]]["status"], "open")

        second = self.client.auto(1)
        self.assertEqual(second["auto_steps"], 1)
        self.assertEqual(second["auto_reason"], "step_limit")
        self.assertEqual(second["node_id"], split["node_id"])
        completed = self.proof_view()
        self.assertEqual(
            completed["tree"]["children"][0]["children"][left["id"]],
            children[left["id"]],
        )
        self.assertEqual(self.client.check()["result"], "verified")
        self.client.undo()
        self.assertEqual(self.proof_view(), partial)
        self.client.undo()
        self.assertEqual(self.proof_view(), initial)
        resumed = self.client.auto()
        self.assertEqual(resumed["node_id"], split["node_id"])
        self.assertEqual(resumed["auto_steps"], 2)
        self.assertEqual(resumed["auto_reason"], "finished")
        self.assertEqual(self.proof_view(), completed)

    def test_auto_is_one_undo_entry_and_preserves_prior_history(self):
        self.client.lemma("safety")
        safety_root = self.proof_view()
        self.step("induction")
        induction = self.proof_view()
        self.client.lemma("witness")
        before = self.proof_view()
        cursor = self.client.state()["node_id"]
        result = self.client.auto()
        self.assertGreaterEqual(result["auto_steps"], 2)
        completed = self.proof_view()
        completed_cursor = result["node_id"]

        undone = self.client.undo()
        self.assertEqual(undone["lemma"], "witness")
        self.assertEqual(undone["node_id"], cursor)
        self.assertEqual(self.proof_view(), before)
        self.assertGreater(undone["revision"], result["revision"])
        self.assertEqual(self.client.undo()["lemma"], "safety")
        self.assertEqual(self.proof_view(), safety_root)
        self.client.redo()
        self.assertEqual(self.proof_view(), induction)
        redone = self.client.redo()
        self.assertEqual(redone["lemma"], "witness")
        self.assertEqual(redone["node_id"], completed_cursor)
        self.assertEqual(self.proof_view(), completed)

    def test_auto_zero_and_invalid_counts_preserve_state_and_redo(self):
        self.client.lemma("witness")
        self.step("simplify")
        simplified = self.proof_view()
        self.client.undo()
        state = self.client.state()
        before = self.client.tree()
        result = self.client.auto(0)
        self.assertEqual(result["auto_steps"], 0)
        self.assertEqual(result["auto_reason"], "step_limit")
        self.assertEqual(self.client.state(), state)
        self.assertEqual(self.client.tree(), before)

        with self.assertRaises((ValueError, BackendError)):
            self.client.auto(-1)
        for invalid in (-1, 1.5, "1", True, [], {}):
            with self.subTest(steps=invalid):
                with self.assertRaises(BackendError):
                    self.client.request("auto", steps=invalid)
                self.assertEqual(self.client.state(), state)
                self.assertEqual(self.client.tree(), before)
        self.client.redo()
        self.assertEqual(self.proof_view(), simplified)

    def test_shell_auto_bounds_validation_completion_and_history(self):
        self.client.lemma("witness")
        initial = self.proof_view()
        shell = TamarinShell(self.client, stdout=io.StringIO())
        self.assertFalse(shell.onecmd("auto 1"))
        partial = self.proof_view()
        self.assertNotEqual(partial, initial)
        self.assertEqual(partial["tree"]["children"][0]["method"], "sorry")
        state = self.client.state()
        self.assertEqual(shell.current_node_id, state["node_id"])
        self.assertEqual(shell.displayed_revision, state["revision"])
        self.assertEqual(self.client.check()["result"], "incomplete")
        state = self.client.state()
        for command in ("auto 0", "auto -1", "auto nope", "auto 1.5", "auto 1 2"):
            with self.subTest(command=command):
                self.assertFalse(shell.onecmd(command))
                self.assertEqual(self.client.state(), state)
                self.assertEqual(self.proof_view(), partial)
        self.assertFalse(shell.onecmd("auto"))
        completed = self.proof_view()
        self.assertEqual(self.client.check()["result"], "verified")
        shell.onecmd("undo")
        self.assertEqual(self.proof_view(), partial)
        shell.onecmd("undo")
        self.assertEqual(self.proof_view(), initial)
        shell.onecmd("redo")
        shell.onecmd("redo")
        self.assertEqual(self.proof_view(), completed)

    def test_apply_cancel_rolls_back_refresh_and_preserves_native_proof_and_history(self):
        self.assert_step_rollback("apply", cancelled=True)

    def test_step_timeout_rolls_back_refresh_and_preserves_native_proof_and_history(self):
        self.assert_step_rollback("step", cancelled=False)

    def assert_step_rollback(self, command, *, cancelled):
        listener, armed = self.ranking_oracle_gate()
        # Keep both older undo history and a pending redo, so a failed step
        # cannot pass merely by returning an equivalent current proof.
        self.client.lemma("safety")
        safety_root = self.proof_view()
        self.step("induction")
        induction = self.proof_view()
        self.client.lemma("witness")
        self.step("simplify")
        simplified = self.proof_view()
        self.client.undo()
        state = self.client.state(detail="full")
        before = self.client.tree()
        listing = self.client.methods()
        chosen = next(
            method for method in listing["methods"] if method["name"] == "simplify"
        )
        saved_before = self.root / "before failed step.spthy"
        saved_after = self.root / "after failed step.spthy"
        self.client.save(saved_before)
        timeout_ms = int(os.environ.get("TAMARIN_TEST_APPLY_TIMEOUT_MS", "15000"))
        self.assertGreater(timeout_ms, 0)
        listener.settimeout(timeout_ms / 1000 + 15)
        process = self.client._process
        assert process is not None and process.stdin is not None and process.stdout is not None
        # An idle cancellation must not enqueue a response of its own.
        process.stdin.write('{"command":"cancel"}\n')
        process.stdin.flush()
        self.assertEqual(self.client.state(detail="full"), state)
        parameters = {
            "command": command,
            "method_id": chosen["id"],
            "expected_revision": listing["revision"],
        }
        if not cancelled:
            parameters["timeout_ms"] = timeout_ms
        armed.touch()
        process.stdin.write(json.dumps(parameters) + "\n")
        process.stdin.flush()
        gate = self.accept_oracle_gate(listener)
        try:
            # The cached simplify has already run. Its response refresh invokes
            # the real ranking oracle: cancellation/timeouts must cover that
            # refresh, not just the native proof-method application.
            if cancelled:
                process.stdin.write('{"command":"cancel"}\n')
                process.stdin.flush()
            self.assertTrue(
                select.select([process.stdout], [], [], timeout_ms / 1000 + 15)[0],
                "Backend did not finish the interrupted active proof step",
            )
            result = json.loads(process.stdout.readline())
        finally:
            armed.unlink(missing_ok=True)
            self.release_oracle_gate(gate)
        self.assert_error_response(
            result, code="CANCELLED" if cancelled else "TIMEOUT", revision=state["revision"]
        )
        self.assertTrue(result["error"]["recoverable"])
        # These synchronous requests also prove that no cancel acknowledgement
        # or abandoned worker response has desynchronized the JSON-lines stream.
        self.assertEqual(self.client.state(detail="full"), state)
        self.assertEqual(self.client.tree(), before)
        self.client.save(saved_after)
        self.assertEqual(saved_after.read_bytes(), saved_before.read_bytes())
        self.client.redo()
        self.assertEqual(self.proof_view(), simplified)
        self.client.undo()
        self.assertEqual(self.client.tree()["tree"], before["tree"])
        self.assertEqual(self.client.undo()["lemma"], "safety")
        self.assertEqual(self.proof_view(), safety_root)
        self.client.redo()
        self.assertEqual(self.proof_view(), induction)
        self.client.redo()
        self.assertEqual(self.proof_view(), simplified)
        self.client.undo()
        fresh = self.client.methods()
        successful = self.client.apply(
            next(method["id"] for method in fresh["methods"] if method["name"] == "simplify"),
            revision=fresh["revision"], timeout_ms=timeout_ms,
        )
        self.assert_compact(successful)
        self.assertEqual(self.proof_view(), simplified)

    def test_auto_cancel_rolls_back_candidate_and_keeps_protocol_and_history(self):
        # A genuine external ranking oracle blocks only after auto has applied
        # its cached first method. Its socket handshake, not a delay, proves
        # that native search is underway before the cancellation is sent.
        listener, armed = self.ranking_oracle_gate()
        self.client.lemma("witness")
        self.step("simplify")
        simplified = self.proof_view()
        self.client.undo()
        state = self.client.state()
        before = self.client.tree()
        process = self.client._process
        self.assertIsNotNone(process)
        assert process is not None and process.stdin is not None and process.stdout is not None

        # Idle cancel is fire-and-forget too: the following state request must
        # receive its own response, rather than an acknowledgement of cancel.
        process.stdin.write('{"command":"cancel"}\n')
        process.stdin.flush()
        self.assertEqual(self.client.state(), state)
        armed.touch()
        process.stdin.write('{"command":"auto"}\n')
        process.stdin.flush()
        gate = self.accept_oracle_gate(listener)
        process.stdin.write('{"command":"cancel"}\n')
        process.stdin.flush()
        self.assertTrue(
            select.select([process.stdout], [], [], 15)[0],
            "Backend did not respond to cancellation of active native search",
        )
        result = json.loads(process.stdout.readline())
        armed.unlink()
        self.release_oracle_gate(gate)
        self.assertEqual(result["status"], "success")
        self.assertEqual(result["auto_reason"], "cancelled")
        self.assertEqual(result["auto_steps"], 0)
        for key, value in state.items():
            self.assertEqual(result[key], value)
        self.assertEqual(self.client.state(), state)
        self.assertEqual(self.client.tree(), before)
        # Cancellation must leave both the proof and the existing redo intact.
        self.client.redo()
        self.assertEqual(self.proof_view(), simplified)
        self.client.undo()
        self.assertEqual(self.proof_view()["tree"], before["tree"])
        with self.assertRaises(BackendError):
            self.client.undo()
        self.assertEqual(self.client.auto()["auto_reason"], "finished")
        self.assertEqual(self.client.check()["result"], "verified")

    def test_backend_exit_ends_shell_instead_of_reprompting(self):
        self.client.lemma("witness")
        output = io.StringIO()
        shell = TamarinShell(self.client, stdout=output)
        # Ordinary command errors remain recoverable.
        self.assertFalse(shell.onecmd("lemma missing"))
        self.client._process.terminate()
        self.client._process.wait(timeout=5)
        # Even a local command must not keep a dead session looking usable.
        with self.assertRaises(ProtocolError):
            shell.onecmd("help")
        with self.assertRaises(ClientClosedError):
            self.client.methods()


if __name__ == "__main__":
    unittest.main()
