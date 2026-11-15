"""Optional real stdio MCP regression; install the package's [mcp] extra."""

import asyncio
from importlib.util import find_spec
import os
from pathlib import Path
import sys
import tempfile
import unittest

from test_integration import THEORY


@unittest.skipUnless(find_spec("mcp"), "optional MCP SDK is not installed")
class MCPIntegrationTests(unittest.TestCase):
    def test_stdio_session_revisions_errors_and_native_save(self):
        from mcp import Client
        from mcp.client.stdio import StdioServerParameters

        async def exercise(workspace):
            parameters = StdioServerParameters(
                command=sys.executable,
                args=["-m", "tamarin_cli.mcp_server", "--workspace", str(workspace)],
                env={**os.environ, "PYTHONPATH": str(Path(__file__).resolve().parents[1])},
            )
            async with Client(parameters, read_timeout_seconds=60) as client:
                tools = await client.list_tools()
                names = {tool.name for tool in tools.tools}
                self.assertTrue({
                    "tamarin_load", "tamarin_lemma", "tamarin_observe", "tamarin_apply",
                    "tamarin_frontier", "tamarin_goto", "tamarin_save", "tamarin_check",
                } <= names)

                async def call(tool_name, **arguments):
                    result = await client.call_tool(tool_name, arguments)
                    self.assertFalse(result.is_error, result)
                    return result.structured_content

                await call("tamarin_load", file="input.spthy")
                selected = await call("tamarin_lemma", name="witness")
                initial_revision = selected["revision"]
                method = next(m for m in selected["methods"] if m["name"] == "simplify")
                selected = await call("tamarin_apply", method_id=method["id"], revision=initial_revision)
                before = await call("tamarin_observe")
                stale = await client.call_tool("tamarin_apply", {
                    "method_id": method["id"], "revision": initial_revision,
                })
                self.assertTrue(stale.is_error)
                self.assertEqual(stale.structured_content["error"]["code"], "STALE_REVISION")
                self.assertEqual(await call("tamarin_observe"), before)
                rejected = await client.call_tool("tamarin_save", {"file": "../escape.spthy"})
                self.assertTrue(rejected.is_error)
                self.assertEqual(rejected.structured_content["status"], "error")
                self.assertFalse((workspace.parent / "escape.spthy").exists())
                frontier = await call("tamarin_frontier")
                selected = await call("tamarin_goto", node_id=frontier["frontier"][0]["node_id"], revision=frontier["revision"])
                method = next(m for m in selected["methods"] if m["name"] == "solve")
                await call("tamarin_apply", method_id=method["id"], revision=selected["revision"])
                self.assertEqual((await call("tamarin_check"))["result"], "verified")
                await call("tamarin_save", file="saved.spthy")
                self.assertIn("theory CLI_Regression", (workspace / "saved.spthy").read_text())
                await call("tamarin_load", file="saved.spthy")
                await call("tamarin_lemma", name="witness")
                self.assertEqual((await call("tamarin_check"))["result"], "verified")

        with tempfile.TemporaryDirectory(prefix="tamarin MCP ") as directory:
            workspace = Path(directory) / "workspace"
            workspace.mkdir()
            (workspace / "input.spthy").write_text(THEORY)
            asyncio.run(exercise(workspace))


if __name__ == "__main__":
    unittest.main()
