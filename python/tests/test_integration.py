"""Real-engine regressions; run from the checkout after `stack build`.

    PYTHONPATH=python python3 -m unittest discover -s python/tests -v

TAMARIN_BACKEND can select another built executable. No mocked proof engine.
"""

import io
from pathlib import Path
import subprocess
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
        self.assertIn("right", self.client.state()["state"])
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
        for operation in [
            lambda: self.client.apply(-1, revision=state["revision"]),
            lambda: self.client.apply(999, revision=state["revision"]),
            lambda: self.client.branch(999),
            lambda: self.client.lemma("missing"),
            lambda: self.client.load(self.root / "missing.spthy"),
            lambda: self.client.request("unknown"),
        ]:
            with self.assertRaises(BackendError):
                operation()
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
