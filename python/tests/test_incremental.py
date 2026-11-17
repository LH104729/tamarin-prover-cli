"""Incremental proof mutation regressions against the real proof-api engine."""

from pathlib import Path
import tempfile
import unittest

from tamarin_cli import TamarinClient

try:
    from .test_integration import THEORY
except ImportError:
    from test_integration import THEORY


DEPENDENCY_THEORY = """theory CLI_Incremental_Dependencies
begin
rule Emit: [] --[ Seen('value') ]-> []
lemma earlier: all-traces "All x #i. Seen(x) @ i ==> x = x" by sorry
lemma prerequisite [{attribute}]: all-traces
  "All x #i. Seen(x) @ i ==> x = 'value'" by sorry
lemma dependent [reuse]: all-traces
  "All x #i. Seen(x) @ i ==> x = 'value'" by sorry
lemma consumer: all-traces
  "All x #i. Seen(x) @ i ==> x = 'value'" by sorry
lemma hidden [hide_lemma=ALL]: all-traces
  "All x #i. Seen(x) @ i ==> x = 'value'" by sorry
lemma invalid: exists-trace "Ex x #i. Seen(x) @ i" by contradiction
end
"""


class IncrementalProofIntegrationTests(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory(prefix="tamarin incremental proofs ")
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        self.client = TamarinClient()
        self.addCleanup(self.client.close)

    def load(self, source):
        file = self.root / "input.spthy"
        file.write_text(source, encoding="utf-8")
        return self.client.load(file)

    def step(self, prefix):
        listing = self.client.methods()
        method = next(item for item in listing["methods"] if item["text"].startswith(prefix))
        return self.client.apply(method["id"], revision=listing["revision"])

    def tree(self, name=None):
        if name is not None:
            self.client.lemma(name)
        return self.client.tree()["tree"]

    def observation(self):
        response = self.client.observe(detail="full")
        response.pop("revision")
        return response

    def statuses(self):
        return {lemma["name"]: lemma["status"] for lemma in self.client.lemmas()["lemmas"]}

    def snapshot(self, names):
        result = {}
        for name in names:
            result[name] = (self.tree(name), self.observation())
        return result

    def assert_preserved(self, proofs):
        for name, (tree, observation) in proofs.items():
            with self.subTest(preserved_lemma=name):
                self.assertEqual(self.tree(name), tree)
                self.assertEqual(self.observation(), observation)

    def assert_finished(self, tree):
        self.assertNotEqual(tree["method"], "sorry")
        self.assertNotEqual(tree["status"], "invalid")
        for child in tree["children"]:
            self.assert_finished(child)

    def assert_same_topology(self, actual, expected):
        for key in ("node_id", "name", "status"):
            self.assertEqual(actual[key], expected[key])
        self.assertEqual(len(actual["children"]), len(expected["children"]))
        for actual_child, expected_child in zip(actual["children"], expected["children"]):
            self.assert_same_topology(actual_child, expected_child)

    def test_apply_reset_and_auto_preserve_other_proofs_annotations_and_history(self):
        self.load(THEORY)
        self.client.lemma("safety")
        self.step("induction")
        open_branch = next(
            branch for branch in self.client.branches()["branches"] if branch["status"] == "open"
        )
        self.client.branch(open_branch["id"])
        self.client.lemma("reflexive")
        self.step("simplify")
        unrelated = self.snapshot(("safety", "reflexive"))

        self.client.lemma("witness")
        self.step("simplify")
        simplified = self.tree()
        self.assertEqual(simplified["children"][0]["method"], "sorry")
        self.assert_preserved(unrelated)

        self.client.lemma("witness")
        split = self.step("solve(")
        complete = self.tree()
        self.assertEqual(self.statuses()["witness"], "verified")
        self.assert_preserved(unrelated)

        self.client.lemma("witness")
        right = next(branch for branch in split["branches"] if branch["name"] == "Right")
        self.client.branch(right["id"])
        self.client.reset()
        partial = self.tree()
        self.assertEqual(self.statuses()["witness"], "incomplete")
        split_children = partial["children"][0]["children"]
        self.assertEqual(split_children[right["id"]]["method"], "sorry")
        for index, child in enumerate(split_children):
            if index != right["id"]:
                self.assertEqual(child, complete["children"][0]["children"][index])
        self.assert_preserved(unrelated)

        self.client.lemma("witness")
        result = self.client.auto(1)
        self.assertEqual(result["auto_steps"], 1)
        self.assertEqual(self.tree(), complete)
        self.assertEqual(self.statuses()["witness"], "verified")
        self.assert_preserved(unrelated)

        # Navigation and observation must not add history entries. Auto is one
        # entry, followed by the preceding reset and manual applications.
        self.client.undo()
        self.assertEqual(self.tree(), partial)
        self.assert_preserved(unrelated)
        self.client.undo()
        self.assertEqual(self.tree(), complete)
        self.client.undo()
        self.assertEqual(self.tree(), simplified)
        self.client.redo()
        self.assertEqual(self.tree(), complete)
        self.client.redo()
        self.assertEqual(self.tree(), partial)
        self.client.redo()
        self.assertEqual(self.tree(), complete)
        self.assert_preserved(unrelated)

        saved = self.root / "incremental.spthy"
        self.client.save(saved)
        self.client.load(saved)
        self.assert_same_topology(self.tree("witness"), complete)
        for name, (tree, _) in unrelated.items():
            self.assert_same_topology(self.tree(name), tree)
        self.assertEqual(
            self.statuses(),
            {"witness": "verified", "safety": "incomplete", "reflexive": "verified"},
        )
        self.client.lemma("witness")
        self.assertEqual(self.client.check()["result"], "verified")
        self.assert_same_topology(self.tree(), complete)

    def test_reuse_and_source_proof_changes_gate_retained_complete_dependents(self):
        for attribute in ("reuse", "sources"):
            with self.subTest(attribute=attribute):
                self.load(DEPENDENCY_THEORY.format(attribute=attribute))
                self.client.lemma("earlier")
                self.step("simplify")
                earlier = self.snapshot(("earlier",))
                self.assert_finished(earlier["earlier"][0])
                # Refined sources are global: even a preceding ordinary lemma
                # is conditional on a later source declaration being proved.
                earlier_unproved = "verified" if attribute == "reuse" else "incomplete"
                self.assertEqual(self.statuses()["earlier"], earlier_unproved)
                for name in ("dependent", "consumer", "hidden"):
                    self.client.lemma(name)
                    self.assertEqual(self.client.auto(12)["auto_reason"], "finished")
                    self.assert_finished(self.tree())
                retained = self.snapshot(("dependent", "consumer", "hidden", "invalid"))
                hidden_unproved = "verified" if attribute == "reuse" else "incomplete"
                self.assertEqual(self.statuses(), {
                    "earlier": earlier_unproved, "prerequisite": "incomplete",
                    "dependent": "incomplete", "consumer": "incomplete",
                    "hidden": hidden_unproved, "invalid": "invalid",
                })

                self.client.lemma("prerequisite")
                initial = self.tree()
                result = self.client.auto(12)
                self.assertEqual(result["auto_reason"], "finished")
                self.assertGreater(result["auto_steps"], 0)
                proved = self.tree()
                self.assertEqual(self.statuses(), {
                    "earlier": "verified", "prerequisite": "verified",
                    "dependent": "verified", "consumer": "verified",
                    "hidden": "verified", "invalid": "invalid",
                })
                self.assert_preserved(earlier)
                self.assert_preserved(retained)

                # Status propagation must work before explicit check (which
                # replays the theory), without discarding dependent proof trees.
                self.client.lemma("prerequisite")
                self.client.reset()
                self.assertEqual(self.tree(), initial)
                self.assertEqual(self.statuses(), {
                    "earlier": earlier_unproved, "prerequisite": "incomplete",
                    "dependent": "incomplete", "consumer": "incomplete",
                    "hidden": hidden_unproved, "invalid": "invalid",
                })
                self.assert_preserved(earlier)
                self.assert_preserved(retained)
                self.client.undo()
                self.assertEqual(self.tree(), proved)
                self.assertEqual(self.statuses()["consumer"], "verified")
                self.assertEqual(self.statuses()["earlier"], "verified")
                self.client.redo()
                self.assertEqual(self.tree(), initial)
                self.assertEqual(self.statuses()["consumer"], "incomplete")
                self.assertEqual(self.statuses()["earlier"], earlier_unproved)
                self.assert_preserved(retained)

                saved = self.root / f"{attribute} reset.spthy"
                self.client.save(saved)
                self.client.load(saved)
                for name in ("dependent", "consumer", "hidden"):
                    self.assert_same_topology(self.tree(name), retained[name][0])
                self.assertEqual(self.statuses()["consumer"], "incomplete")
                self.assertEqual(self.statuses()["earlier"], earlier_unproved)
                self.client.lemma("prerequisite")
                self.assertEqual(self.client.auto(12)["auto_reason"], "finished")
                self.assertEqual(self.statuses()["consumer"], "verified")
                self.assertEqual(self.statuses()["earlier"], "verified")
                self.client.undo()
                self.assertEqual(self.statuses()["consumer"], "incomplete")
                self.assertEqual(self.statuses()["earlier"], earlier_unproved)
                self.client.redo()
                self.assertEqual(self.statuses()["consumer"], "verified")
                self.assertEqual(self.statuses()["earlier"], "verified")
                self.client.lemma("consumer")
                self.assertEqual(self.client.check()["result"], "verified")
                self.assert_same_topology(self.tree(), retained["consumer"][0])
                self.assertEqual(self.statuses()["invalid"], "invalid")

    def test_ordinary_steps_preserve_unreachable_native_proof_annotations(self):
        self.load(DEPENDENCY_THEORY.format(attribute="reuse"))
        invalid = self.tree("invalid")
        self.assertEqual(self.statuses()["invalid"], "invalid")
        self.assertTrue(invalid["children"])
        child = invalid["children"][0]
        self.assertEqual(child["status"], "invalid")
        self.client.goto(child["node_id"], revision=self.client.revision)
        self.assertIsNone(self.client.observe(detail="goals")["constraints"])
        retained = self.snapshot(("invalid",))

        self.client.lemma("prerequisite")
        self.step("simplify")
        self.assert_preserved(retained)
        self.client.lemma("prerequisite")
        self.client.auto(12)
        self.assert_preserved(retained)
        self.client.lemma("prerequisite")
        self.client.goto("0", revision=self.client.revision)
        self.client.reset()
        self.assert_preserved(retained)
        self.assertEqual(self.statuses()["invalid"], "invalid")


if __name__ == "__main__":
    unittest.main()
