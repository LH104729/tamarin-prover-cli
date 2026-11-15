"""Constraint-graph regressions against the real proof-api engine, never mocks."""

import io
import json
from pathlib import Path
import tempfile
import unittest

from tamarin_cli import BackendError, TamarinClient
from tamarin_cli.repl import TamarinShell


THEORY = """theory CLI_Graph
begin
rule Produce: [] --> [Token('x')]
rule Consume: [Token(x)] --[Seen(x)]-> []
rule ProducePersistent: [] --> [!Permit('x')]
rule ConsumePersistent: [!Permit(x)] --[Used(x)]-> []
rule Start: [] --[Started()]-> []
rule End: [] --[Ended()]-> []
lemma flow: exists-trace "Ex #i. Seen('x') @ i" by sorry
lemma persistent: exists-trace "Ex #i. Used('x') @ i" by sorry
lemma ordered: exists-trace "Ex #i #j. Started() @ i & Ended() @ j & i < j" by sorry
end
"""


class GraphIntegrationTests(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory(prefix="tamarin graph ")
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        self.file = self.root / "graph.spthy"
        self.file.write_text(THEORY, encoding="utf-8")
        self.client = TamarinClient()
        self.addCleanup(self.client.close)

    def load(self):
        return self.client.load(self.file)

    def build_graph(self, lemma, labels, edge_type):
        """Follow only simplify/solve choices; stop at a real populated system.

        Each action and premise in this theory has a unique producer, so there
        are no search alternatives. Inspect each resulting child rather than
        assuming a fixed number of native simplification steps or using auto's
        deliberately retained subtree-root cursor.
        """
        self.client.lemma(lemma)
        for _ in range(12):
            response = self.client.graph()
            graph = response["graph"]
            if labels <= {node["label"] for node in graph["nodes"]} and any(
                edge["type"] == edge_type for edge in graph["edges"]
            ):
                return response
            listing = self.client.methods()
            choices = [
                method for method in listing["methods"]
                if method["name"] in ("simplify", "solve")
            ]
            self.assertTrue(choices, f"No simplify/solve choice before graph appeared: {response!r}")
            method = next(
                (choice for choice in choices if choice["name"] == "simplify"),
                choices[0],
            )
            applied = self.client.apply(method["id"], revision=listing["revision"])
            self.assertLessEqual(
                len(applied["generated_branches"]), 1,
                "The tiny graph fixture unexpectedly needs branch search",
            )
        self.fail(f"No {edge_type} graph after twelve bounded native steps")

    def assert_graph_schema(self, response):
        self.assertEqual(response["status"], "success")
        self.assertIs(type(response["revision"]), int)
        self.assertIsInstance(response["lemma"], str)
        self.assertRegex(response["node_id"], r"^0(?:\.[0-9]+)*$")
        graph = response["graph"]
        self.assertEqual(set(graph), {"nodes", "edges"})
        node_ids = set()
        for node in graph["nodes"]:
            self.assertEqual(
                set(node), {"id", "type", "label", "premises", "actions", "conclusions"}
            )
            self.assertIsInstance(node["id"], str)
            self.assertNotIn(node["id"], node_ids)
            node_ids.add(node["id"])
            for field in ("type", "label"):
                self.assertIsInstance(node[field], str)
            for field, port in (("premises", "p"), ("actions", None), ("conclusions", "c")):
                self.assertIsInstance(node[field], list)
                for index, fact in enumerate(node[field]):
                    self.assertEqual(set(fact), {"id", "text", "name", "multiplicity"})
                    for key in fact:
                        self.assertIsInstance(fact[key], str)
                    self.assertIn(fact["multiplicity"], ("", "!"))
                    if port is not None:
                        self.assertEqual(fact["id"], f"{node['id']}:{port}{index}")
        for edge in graph["edges"]:
            self.assertEqual(set(edge), {"source", "target", "type"})
            self.assertIn(edge["type"], {
                "ProtoFact", "PersistentFact", "KFact", "default", "LessAtoms", "unsolvedChain",
            })
            if edge["type"] == "LessAtoms":
                self.assertIn(edge["source"], node_ids)
                self.assertIn(edge["target"], node_ids)
            else:
                self.assertRegex(edge["source"], r":c[0-9]+$")
                self.assertRegex(edge["target"], r":p[0-9]+$")

    def assert_fact(self, fact, *, name, text, multiplicity=""):
        self.assertEqual(fact["name"], name)
        self.assertEqual("".join(fact["text"].split()), text)
        self.assertEqual(fact["multiplicity"], multiplicity)

    def test_graph_requires_loaded_theory_and_selected_lemma_without_mutation(self):
        with self.assertRaises(BackendError) as missing:
            self.client.graph()
        self.assertEqual(missing.exception.code, "INVALID_STATE")
        self.assertEqual(missing.exception.response["revision"], 0)
        loaded = self.load()
        before = self.client.lemmas()
        with self.assertRaises(BackendError) as unselected:
            self.client.graph()
        self.assertEqual(unselected.exception.code, "INVALID_STATE")
        self.assertEqual(unselected.exception.response["revision"], loaded["revision"])
        self.assertEqual(self.client.lemmas(), before)
        self.assertEqual(self.client.lemma("flow")["node_id"], "0")

    def test_empty_graph_is_valid_and_keeps_displayed_method_revision_usable(self):
        self.load()
        selected = self.client.lemma("flow")
        before = self.client.state(detail="full")
        tree = self.client.tree()
        listing = self.client.methods()
        response = self.client.graph()
        self.assert_graph_schema(response)
        self.assertEqual(response["graph"], {"nodes": [], "edges": []})
        self.assertEqual(response["node_id"], selected["node_id"])
        self.assertEqual(response["revision"], listing["revision"])
        self.assertEqual(self.client.state(detail="full"), before)
        self.assertEqual(self.client.tree(), tree)
        self.assertEqual(self.client.methods(), listing)
        simplify = next(method for method in listing["methods"] if method["name"] == "simplify")
        applied = self.client.apply(simplify["id"], revision=listing["revision"])
        self.assertGreater(applied["revision"], response["revision"])

    def test_linear_and_persistent_fact_flow_preserves_native_ports_and_types(self):
        self.load()
        for lemma, producer, consumer, fact_name, action, multiplicity, edge_type in (
            ("flow", "Produce", "Consume", "Token", "Seen", "", "ProtoFact"),
            ("persistent", "ProducePersistent", "ConsumePersistent", "Permit", "Used", "!", "PersistentFact"),
        ):
            with self.subTest(lemma=lemma):
                response = self.build_graph(lemma, {producer, consumer}, edge_type)
                self.assert_graph_schema(response)
                graph = response["graph"]
                rules = {node["label"]: node for node in graph["nodes"]}
                self.assertEqual(set(rules), {producer, consumer})
                source, target = rules[producer], rules[consumer]
                for node in (source, target):
                    self.assertEqual(node["type"], "isProtocolRule")
                    self.assertNotEqual(node["id"], response["node_id"])
                self.assertEqual(source["premises"], [])
                self.assertEqual(source["actions"], [])
                self.assertEqual(target["conclusions"], [])
                self.assertEqual(len(source["conclusions"]), 1)
                self.assertEqual(len(target["premises"]), 1)
                self.assertEqual(len(target["actions"]), 1)
                for fact in (source["conclusions"][0], target["premises"][0]):
                    self.assert_fact(
                        fact, name=f"{multiplicity}{fact_name}",
                        text=f"{multiplicity}{fact_name}('x')", multiplicity=multiplicity,
                    )
                self.assert_fact(target["actions"][0], name=action, text=f"{action}('x')")
                self.assertIn({
                    "source": source["conclusions"][0]["id"],
                    "target": target["premises"][0]["id"],
                    "type": edge_type,
                }, graph["edges"])
                before = self.client.state(detail="full")
                tree = self.client.tree()
                methods = self.client.methods()
                native_before = self.root / f"{lemma}-before.spthy"
                native_after = self.root / f"{lemma}-after.spthy"
                self.client.save(native_before)
                self.assertEqual(self.client.graph(), response)
                self.client.save(native_after)
                self.assertEqual(native_after.read_bytes(), native_before.read_bytes())
                self.assertEqual(self.client.state(detail="full"), before)
                self.assertEqual(self.client.tree(), tree)
                self.assertEqual(self.client.methods(), methods)

    def test_explicit_node_ordering_uses_node_ids_not_fact_ports(self):
        self.load()
        response = self.build_graph("ordered", {"Start", "End"}, "LessAtoms")
        self.assert_graph_schema(response)
        nodes = {node["label"]: node for node in response["graph"]["nodes"]}
        self.assertIn({
            "source": nodes["Start"]["id"],
            "target": nodes["End"]["id"],
            "type": "LessAtoms",
        }, response["graph"]["edges"])

    def test_shell_displays_native_graph_without_confusing_proof_navigation(self):
        self.load()
        response = self.build_graph("flow", {"Produce", "Consume"}, "ProtoFact")
        before = self.client.state(detail="full")
        output = io.StringIO()
        shell = TamarinShell(self.client, stdout=output)
        shell.onecmd("state")
        output.seek(0)
        output.truncate()
        shell.onecmd("graph")
        displayed = output.getvalue()
        for title in ("Nodes:", "Premises:", "Actions:", "Conclusions:", "Edges:"):
            self.assertIn(title, displayed)
        self.assertLess(displayed.index("Nodes:"), displayed.index("Edges:"))
        for node in response["graph"]["nodes"]:
            self.assertIn(node["id"], displayed)
            self.assertIn(node["label"], displayed)
            self.assertIn(node["type"], displayed)
            for field in ("premises", "actions", "conclusions"):
                for fact in node[field]:
                    self.assertIn(fact["text"], displayed)
        for edge in response["graph"]["edges"]:
            self.assertIn(f"{edge['source']} --[{edge['type']}]--> {edge['target']}", displayed)
        self.assertEqual(shell.current_node_id, response["node_id"])
        self.assertEqual(shell.displayed_revision, response["revision"])
        self.assertEqual(shell.displayed_node_revision, before["revision"])
        output.seek(0)
        output.truncate()
        shell.onecmd("graph --json")
        self.assertEqual(json.loads(output.getvalue()), response)
        self.assertEqual(shell.current_node_id, response["node_id"])
        output.seek(0)
        output.truncate()
        shell.onecmd(f"goto {response['graph']['nodes'][0]['id']}")
        self.assertIn("INVALID_NODE", output.getvalue())
        self.assertEqual(self.client.state(detail="full"), before)


if __name__ == "__main__":
    unittest.main()
