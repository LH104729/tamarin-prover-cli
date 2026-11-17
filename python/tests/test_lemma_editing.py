"""Native lemma mutation regressions against the real proof-api engine."""

from pathlib import Path
import tempfile
import unittest

from tamarin_cli import BackendError, TamarinClient

try:
    from .test_integration import SOURCE_THEORY, THEORY
except ImportError:
    from test_integration import SOURCE_THEORY, THEORY


PREDICATE_THEORY = SOURCE_THEORY.replace(
    "macros:", "predicates: Same(x,y) <=> x = y\nmacros:", 1
)
SOURCE_DECLARATION = (
    'lemma origin [sources]: all-traces '
    '"All x #i. Seen(x) @ i ==> x = identity(\'value\')" by sorry'
)
REUSE_THEORY = THEORY.replace(
    'lemma witness: exists-trace "Ex x #i. Pick(x) @ i" by sorry\n'
    'lemma safety: all-traces "All x #i. Pick(x) @ i ==> x = tag(\'left\')" by sorry\n'
    'lemma reflexive: all-traces "All x #i. Pick(x) @ i ==> x = x" by sorry',
    'lemma earlier: all-traces "All x #i. Pick(x) @ i ==> x = x" by sorry\n'
    'lemma reusable [reuse]: all-traces "All x #i. Pick(x) @ i ==> x = x" by sorry\n'
    'lemma dependent: all-traces "All x #i. Pick(x) @ i ==> x = x" by sorry',
)


class LemmaEditingIntegrationTests(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory(prefix="tamarin lemma editing ")
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        self.client = TamarinClient()
        self.addCleanup(self.client.close)
        self.load(THEORY)

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

    def names(self, response=None):
        if response is None:
            response = self.client.lemmas()
        return [lemma["name"] for lemma in response["lemmas"]]

    def native(self, filename="saved.spthy"):
        file = self.root / filename
        self.client.save(file)
        return file.read_text(encoding="utf-8")

    def assert_fresh(self):
        tree = self.tree()
        self.assertEqual(tree["method"], "sorry")
        self.assertEqual(tree["children"], [])
        self.assertEqual(self.client.check()["result"], "incomplete")

    def assert_mutation(self, response, operation, name, selected, previous_name=None):
        self.assertEqual(response["status"], "success")
        self.assertEqual(response["operation"], operation)
        self.assertEqual(response["name"], name)
        self.assertEqual(response["selected_lemma"], selected)
        self.assertIsInstance(response["theory"], str)
        self.assertEqual(response["lemmas"], self.client.lemmas()["lemmas"])
        self.assertEqual(response["revision"], self.client.revision)
        if previous_name is not None:
            self.assertEqual(response["previous_name"], previous_name)
        if selected is not None:
            self.assertEqual(response["lemma"], selected)
            for key in ("node_id", "branch_status", "goal_count", "methods", "branches"):
                self.assertIn(key, response)
            self.assertEqual(response["methods"], self.client.methods()["methods"])

    def test_add_edit_rename_delete_round_trip_preserves_native_definitions(self):
        self.load(PREDICATE_THEORY)
        self.client.lemma("event")
        self.step("simplify")
        event_tree = self.tree()
        self.client.lemma("unique")
        self.step("simplify")
        self.assertEqual(self.client.check()["result"], "verified")

        added = self.client.add(
            'lemma extra:\n exists-trace "Ex #i. Seen(identity(\'value\')) @ i" by simplify',
            revision=self.client.revision,
        )
        self.assert_mutation(added, "add", "extra", "extra")
        self.assertEqual(added["node_id"], "0")
        self.assertEqual(self.names(added), ["event", "unique", "extra"])
        # A parsed, attached native proof must not execute or survive insertion.
        self.assert_fresh()
        self.client.auto(8)
        self.assertEqual(self.client.check()["result"], "verified")

        edited = self.client.edit(
            "unique",
            'lemma renamed [reuse]: all-traces\n'
            ' "All #i. Seen(identity(\'value\')) @ i ==> '
            'Same(identity(\'value\'), identity(\'value\'))" by simplify',
            revision=self.client.revision,
        )
        self.assert_mutation(edited, "edit", "renamed", "renamed", "unique")
        self.assertEqual(edited["node_id"], "0")
        self.assertEqual(self.names(edited), ["event", "renamed", "extra"])
        self.assert_fresh()
        self.step("simplify")
        self.assertEqual(self.client.check()["result"], "verified")
        self.assertEqual(self.tree("event"), event_tree)
        event_cursor = self.client.state()["node_id"]
        deleted = self.client.delete("extra", revision=self.client.revision)
        self.assert_mutation(deleted, "delete", "extra", "event")
        self.assertEqual(deleted["node_id"], event_cursor)
        self.assertEqual(self.tree(), event_tree)
        self.assertEqual(self.names(deleted), ["event", "renamed"])

        native = self.native("round trip.spthy")
        self.assertRegex(native, r"lemma\s+renamed\s*\[reuse\]")
        self.assertNotRegex(native, r"lemma\s+(?:unique|extra)\s*[:\[]")
        self.client.load(self.root / "round trip.spthy")
        self.assertEqual(self.names(), ["event", "renamed"])
        self.assertEqual(self.tree("event"), event_tree)
        self.client.lemma("renamed")
        self.assertEqual(self.client.check()["result"], "verified")
        # The retained macro/predicate declarations remain usable after reload.
        self.client.add(
            'lemma after_reload: all-traces '
            '"All #i. Seen(identity(\'value\')) @ i ==> '
            'Same(identity(\'value\'), identity(\'value\'))"',
            revision=self.client.revision,
        )
        self.step("simplify")
        self.assertEqual(self.client.check()["result"], "verified")

    def test_history_restores_declarations_and_proofs_in_one_entry(self):
        self.client.lemma("reflexive")
        self.step("simplify")
        original_tree = self.tree()
        original_native = self.native()
        original_cursor = self.client.state()["node_id"]
        edited = self.client.edit(
            "reflexive",
            'lemma renamed: exists-trace "Ex x #i. Pick(x) @ i" by simplify',
            revision=self.client.revision,
        )
        self.assert_fresh()
        edited_native = self.native()
        self.assertNotEqual(original_native, edited_native)
        undone = self.client.undo()
        self.assertEqual(undone["selected_lemma"], "reflexive")
        self.assertEqual(undone["node_id"], original_cursor)
        self.assertGreater(undone["revision"], edited["revision"])
        self.assertEqual(self.names(undone), ["witness", "safety", "reflexive"])
        self.assertEqual(self.tree(), original_tree)
        self.assertEqual(self.native(), original_native)
        redone = self.client.redo()
        self.assertEqual(redone["selected_lemma"], "renamed")
        self.assertEqual(redone["node_id"], "0")
        self.assertEqual(self.names(redone), ["witness", "safety", "renamed"])
        self.assert_fresh()
        self.assertEqual(self.native(), edited_native)
        self.client.undo()
        self.client.undo()  # Edit contributes only one entry, then simplify is undone.
        self.assertEqual(self.names(), ["witness", "safety", "reflexive"])
        self.assert_fresh()
        self.client.redo()
        self.assertEqual(self.tree(), original_tree)
        self.client.redo()
        self.assertEqual(self.native(), edited_native)

    def test_selected_delete_and_history_work_without_selected_lemma(self):
        original_native = self.native()
        added = self.client.add(
            'lemma extra: exists-trace "Ex x #i. Pick(x) @ i"',
            revision=self.client.revision,
        )
        self.assert_mutation(added, "add", "extra", "extra")
        undone = self.client.undo()
        self.assertIsNone(undone["selected_lemma"])
        self.assertEqual(self.names(undone), ["witness", "safety", "reflexive"])
        self.assertEqual(self.native(), original_native)
        self.assertGreater(undone["revision"], added["revision"])
        redone = self.client.redo()
        self.assertEqual(redone["selected_lemma"], "extra")
        self.assertEqual(redone["node_id"], "0")
        self.assert_fresh()
        self.step("simplify")
        extra_tree = self.tree()
        extra_cursor = self.client.state()["node_id"]
        extra_native = self.native()
        deleted = self.client.delete("extra", revision=self.client.revision)
        self.assert_mutation(deleted, "delete", "extra", None)
        self.assertEqual(self.native(), original_native)
        restored = self.client.undo()
        self.assertEqual(restored["selected_lemma"], "extra")
        self.assertEqual(self.names(restored), ["witness", "safety", "reflexive", "extra"])
        self.assertEqual(self.native(), extra_native)
        self.assertEqual(restored["node_id"], extra_cursor)
        self.assertEqual(self.tree(), extra_tree)
        self.assertEqual(self.client.check()["result"], "incomplete")
        removed = self.client.redo()
        self.assertIsNone(removed["selected_lemma"])
        self.assertEqual(self.native(), original_native)
        # Another mutation and its history must work from the cleared selection.
        deleted = self.client.delete("safety", revision=self.client.revision)
        self.assert_mutation(deleted, "delete", "safety", None)
        restored = self.client.undo()
        self.assertIsNone(restored["selected_lemma"])
        self.assertEqual(self.names(restored), ["witness", "safety", "reflexive"])
        removed = self.client.redo()
        self.assertIsNone(removed["selected_lemma"])
        self.assertEqual(self.names(removed), ["witness", "reflexive"])

    def test_rejected_mutations_preserve_revision_source_proof_selection_and_redo(self):
        self.client.lemma("safety")
        self.step("induction")
        induction_tree = self.tree()
        induction_native = self.native()
        self.client.undo()
        state = self.client.state(detail="full")
        tree = self.client.tree()
        listing = self.client.lemmas()
        native = self.native()
        revision = self.client.revision
        source = 'lemma extra: exists-trace "Ex x #i. Pick(x) @ i"'
        valid = {
            "add": {"source": source},
            "edit": {"name": "safety", "source": source},
            "delete": {"name": "safety"},
        }
        rejected = []
        for command, parameters in valid.items():
            rejected.append((command, parameters, "INVALID_REQUEST"))
            rejected.append((command, {**parameters, "expected_revision": revision - 1}, "STALE_REVISION"))
            for invalid_revision in (None, True, "1", 1.5, []):
                rejected.append((command, {**parameters, "expected_revision": invalid_revision}, "INVALID_REQUEST"))
        for command in ("add", "edit"):
            parameters = {**valid[command], "expected_revision": revision}
            for invalid_source in (None, True, 12, [], {}):
                rejected.append((command, {**parameters, "source": invalid_source}, "INVALID_REQUEST"))
            for invalid_source in (
                "", 'lemma broken: "not a formula"',
                'lemma unguarded: all-traces "All x. x = \'left\'"',
                source + " trailing_garbage", source + "\n" + source.replace("extra", "another"),
                "rule Extra: [] --[ Pick('extra') ]-> []",
            ):
                rejected.append((command, {**parameters, "source": invalid_source}, "INVALID_LEMMA"))
        for command in ("edit", "delete"):
            parameters = {**valid[command], "expected_revision": revision}
            for invalid_name in (None, True, 12, [], {}):
                rejected.append((command, {**parameters, "name": invalid_name}, "INVALID_REQUEST"))
            rejected.append((command, {**parameters, "name": "missing"}, "INVALID_LEMMA"))
        duplicate = 'lemma witness: exists-trace "Ex x #i. Pick(x) @ i"'
        rejected.extend([
            ("add", {"source": duplicate, "expected_revision": revision}, "LEMMA_EXISTS"),
            ("edit", {"name": "safety", "source": duplicate, "expected_revision": revision}, "LEMMA_EXISTS"),
        ])
        for command, parameters, code in rejected:
            with self.subTest(command=command, parameters=parameters):
                with self.assertRaises(BackendError) as error:
                    self.client.request(command, **parameters)
                self.assertEqual(error.exception.code, code)
                self.assertEqual(error.exception.response["revision"], revision)
                self.assertEqual(self.client.revision, revision)
                self.assertEqual(self.client.state(detail="full"), state)
                self.assertEqual(self.client.tree(), tree)
                self.assertEqual(self.client.lemmas(), listing)
        self.assertEqual(self.native(), native)
        self.client.redo()
        self.assertEqual(self.tree(), induction_tree)
        self.assertEqual(self.native(), induction_native)

    def test_reusable_edit_and_delete_reset_later_proofs_and_history_restores_them(self):
        for operation in ("edit", "delete"):
            with self.subTest(operation=operation):
                self.load(REUSE_THEORY)
                proofs = {}
                for name in ("earlier", "reusable", "dependent"):
                    self.client.lemma(name)
                    self.step("simplify")
                    self.assertEqual(self.client.check()["result"], "verified")
                    proofs[name] = self.tree()
                native = self.native()
                if operation == "edit":
                    response = self.client.edit(
                        "reusable",
                        'lemma reusable [reuse]: all-traces '
                        '"All x #i. Pick(x) @ i ==> x = tag(\'left\')"',
                        revision=self.client.revision,
                    )
                    self.assert_fresh()
                else:
                    response = self.client.delete("reusable", revision=self.client.revision)
                self.assertIn("dependent", response["invalidated_lemmas"])
                self.assertEqual(self.tree("earlier"), proofs["earlier"])
                self.client.lemma("dependent")
                self.assert_fresh()
                changed_native = self.native("invalidated.spthy")
                self.client.undo()
                self.assertEqual(self.native(), native)
                for name, proof in proofs.items():
                    self.assertEqual(self.tree(name), proof)
                    self.assertEqual(self.client.check()["result"], "verified")
                self.client.redo()
                self.assertEqual(self.native(), changed_native)
                self.client.load(self.root / "invalidated.spthy")
                self.client.lemma("dependent")
                self.assert_fresh()
                self.client.lemma("earlier")
                self.assertEqual(self.client.check()["result"], "verified")

    def test_source_add_recloses_and_resets_existing_proofs(self):
        self.load(PREDICATE_THEORY)
        self.client.lemma("event")
        self.step("simplify")
        event_tree = self.tree()
        self.client.lemma("unique")
        self.step("simplify")
        unique_tree = self.tree()
        native = self.native()
        added = self.client.add(SOURCE_DECLARATION, revision=self.client.revision)
        self.assert_mutation(added, "add", "origin", "origin")
        self.assert_fresh()
        self.assertEqual(set(added["invalidated_lemmas"]), {"event", "unique"})
        for name in ("event", "unique"):
            self.client.lemma(name)
            self.assert_fresh()
        changed_native = self.native("added source.spthy")
        self.client.undo()
        self.assertEqual(self.native(), native)
        self.assertEqual(self.tree("event"), event_tree)
        self.assertEqual(self.tree("unique"), unique_tree)
        self.client.redo()
        self.assertEqual(self.native(), changed_native)
        self.client.load(self.root / "added source.spthy")
        self.assertEqual(self.names(), ["event", "unique", "origin"])
        self.client.lemma("origin")
        self.client.auto(8)
        self.assertEqual(self.client.check()["result"], "verified")
        self.client.lemma("unique")
        self.step("simplify")
        self.assertEqual(self.client.check()["result"], "verified")

    def test_source_edit_and_delete_reclose_preserve_source_metadata_and_history(self):
        source = PREDICATE_THEORY.replace("lemma unique:", SOURCE_DECLARATION + "\nlemma unique:", 1)
        for operation in ("edit", "delete"):
            with self.subTest(operation=operation):
                self.load(source)
                proofs = {}
                for name in ("event", "unique"):
                    self.client.lemma(name)
                    self.step("simplify")
                    proofs[name] = self.tree()
                native = self.native()
                if operation == "edit":
                    response = self.client.edit(
                        "origin",
                        'lemma renamed_origin [sources]: all-traces '
                        '"All x #i. Seen(x) @ i ==> Same(x, identity(\'value\'))" by simplify',
                        revision=self.client.revision,
                    )
                    self.assert_mutation(response, "edit", "renamed_origin", "renamed_origin", "origin")
                    self.assert_fresh()
                    expected_names = ["event", "renamed_origin", "unique"]
                else:
                    response = self.client.delete("origin", revision=self.client.revision)
                    self.assert_mutation(response, "delete", "origin", "unique")
                    expected_names = ["event", "unique"]
                self.assertEqual(set(response["invalidated_lemmas"]), {"event", "unique"})
                for name in ("event", "unique"):
                    self.client.lemma(name)
                    self.assert_fresh()
                changed_native = self.native("changed source.spthy")
                self.client.undo()
                self.assertEqual(self.native(), native)
                self.assertEqual(self.names(), ["event", "origin", "unique"])
                for name, proof in proofs.items():
                    self.assertEqual(self.tree(name), proof)
                self.client.redo()
                self.assertEqual(self.native(), changed_native)
                self.client.load(self.root / "changed source.spthy")
                self.assertEqual(self.names(), expected_names)
                if operation == "edit":
                    self.client.lemma("renamed_origin")
                    self.client.auto(8)
                    self.assertEqual(self.client.check()["result"], "verified")
                self.client.lemma("unique")
                self.step("simplify")
                self.assertEqual(self.client.check()["result"], "verified")
                self.client.add(
                    'lemma macros_survive: all-traces '
                    '"All #i. Seen(identity(\'value\')) @ i ==> Same(identity(\'value\'), identity(\'value\'))"',
                    revision=self.client.revision,
                )
                self.step("simplify")
                self.assertEqual(self.client.check()["result"], "verified")


if __name__ == "__main__":
    unittest.main()
