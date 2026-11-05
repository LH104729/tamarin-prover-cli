"""Real-engine regressions; run from the checkout after `stack build`.

    PYTHONPATH=python python3 -m unittest discover -s python/tests -v

TAMARIN_BACKEND can select another built executable. No mocked proof engine.
"""

import io
from pathlib import Path
import subprocess
import tempfile
import unittest

from tamarin_cli import BackendError, TamarinClient
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
        methods = self.client.methods()["methods"]
        chosen = next(method for method in methods if method["text"].startswith(prefix))
        return self.client.apply(chosen["id"])

    def split(self, lemma):
        self.client.lemma(lemma)
        self.step("simplify")
        self.client.branch(0)
        return self.step("solve(")

    def test_manual_navigation_undo_and_native_round_trip(self):
        self.client.lemma("witness")
        initial = self.client.tree()["tree"]
        self.client.state()
        self.client.goals()
        self.client.methods()
        self.assertEqual(self.client.check()["result"], "incomplete")
        self.assertEqual(self.client.tree()["tree"], initial)

        self.step("simplify")
        self.client.branch(0)
        # Simplify must not silently select and solve the remaining goal.
        self.assertEqual(self.client.tree()["tree"]["children"][0]["method"], "sorry")
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
        shell = TamarinShell(self.client, stdout=io.StringIO())
        shell.onecmd("undo")
        undone = self.client.tree()
        shell.onecmd("")
        self.assertEqual(self.client.tree(), undone)
        self.assertEqual(self.client.check()["result"], "incomplete")
        retained = self.client.tree()["tree"]
        self.assertEqual(retained["status"], "open")
        self.assertEqual(retained["children"][0]["status"], "open")
        self.assertEqual(retained["children"][0]["children"][left["id"]]["status"], "solved")
        self.assertEqual(retained["children"][0]["children"][right["id"]]["method"], "sorry")

        saved = self.root / "partial proof.spthy"
        self.client.save(saved)
        self.client.load(saved)
        self.client.lemma("witness")
        self.assertEqual(self.client.tree()["tree"], retained)
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
        self.client.branch(0)
        before = self.client.tree()
        state = self.client.state()
        for operation in [
            lambda: self.client.apply(-1),
            lambda: self.client.apply(999),
            lambda: self.client.branch(999),
            lambda: self.client.lemma("missing"),
            lambda: self.client.load(self.root / "missing.spthy"),
            lambda: self.client.request("unknown"),
        ]:
            with self.assertRaises(BackendError):
                operation()
            self.assertEqual(self.client.tree(), before)
            self.assertEqual(self.client.state(), state)

    def test_source_macros_and_restrictions(self):
        source = self.root / "source.spthy"
        source.write_text(SOURCE_THEORY, encoding="utf-8")
        self.client.load(source)
        self.client.lemma("event")
        self.step("simplify")
        before = self.client.tree()
        saved = self.root / "saved source.spthy"
        self.client.lemma("unique")
        self.step("simplify")
        # The restriction makes the counterexample impossible immediately.
        self.assertEqual(self.client.check()["result"], "verified")
        self.client.save(saved)
        self.client.load(saved)
        self.client.lemma("event")
        self.assertEqual(self.client.tree(), before)
        self.client.lemma("unique")
        self.assertEqual(self.client.check()["result"], "verified")


if __name__ == "__main__":
    unittest.main()
