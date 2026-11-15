"""Optional, stdio-only MCP adapter for one confined proof session.

Install ``tamarin-cli[mcp]`` with Python 3.10 or newer. Run with
``python -m tamarin_cli.mcp_server --workspace /path/to/theories``.
The workspace policy is not an OS sandbox: theories, oracles, and concurrent
filesystem writers must be trusted. Saving may overwrite a native .spthy file.
"""

import argparse
import asyncio
from contextlib import asynccontextmanager
import json
import os
import sys
from typing import Any, Callable, Optional, Sequence, Union

from .client import BackendError


def create_server(
    workspace: Union[str, os.PathLike],
    *,
    backend: Optional[Union[str, Sequence[str]]] = None,
    timeout_ms: int = 30000,
    cpu_seconds: int = 300,
    max_file_bytes: int = 8388608,
    max_response_bytes: int = 8388608,
) -> Any:
    """Create an official MCPServer without starting a backend or a listener.

    One AgentSession is owned by the server lifespan. All nine tools share it;
    cancellation waits for an in-flight operation before releasing serialization.
    A hard resource violation permanently invalidates that session, without retry
    or automatic restart. Configuration cannot be changed through tools.
    """
    if sys.version_info < (3, 10):
        raise RuntimeError("The MCP adapter requires Python 3.10 or newer")
    try:
        import anyio
        from mcp.server import MCPServer
        from mcp.types import CallToolResult, TextContent
    except ImportError as exc:
        raise RuntimeError(
            "The MCP adapter requires the optional official MCP SDK v2.3: "
            "install with python -m pip install 'tamarin-cli[mcp]'"
        ) from exc

    from .agent import AgentSession

    session = None
    lock = asyncio.Lock()

    async def complete_in_thread(function: Callable[..., Any], *args: Any, **kwargs: Any) -> Any:
        # Shield the worker itself: cancelling asyncio.to_thread does not stop
        # its thread, and abandoning a mutation would lose response alignment.
        worker = asyncio.create_task(asyncio.to_thread(function, *args, **kwargs))
        try:
            return await asyncio.shield(worker)
        except asyncio.CancelledError:
            # MCP uses AnyIO cancellation scopes (level cancellation); shielding
            # those as well avoids a busy loop while the bounded worker drains.
            with anyio.CancelScope(shield=True):
                while not worker.done():
                    try:
                        await asyncio.shield(worker)
                    except asyncio.CancelledError:
                        continue
                    except Exception:
                        break
                if not worker.cancelled():
                    # Retrieve a worker failure, but keep cancellation as the
                    # caller's outcome. AgentSession owns backend invalidation.
                    try:
                        worker.result()
                    except Exception:
                        pass
            raise

    def open_session() -> None:
        nonlocal session
        session = AgentSession(
            workspace,
            backend=backend,
            timeout_ms=timeout_ms,
            cpu_seconds=cpu_seconds,
            max_file_bytes=max_file_bytes,
            max_response_bytes=max_response_bytes,
        )

    @asynccontextmanager
    async def lifespan(server: Any):
        nonlocal session
        try:
            await complete_in_thread(open_session)
            yield session
        finally:
            # This also covers cancellation during construction. The worker has
            # finished before close, even if no request result was delivered.
            with anyio.CancelScope(shield=True):
                async with lock:
                    if session is not None:
                        await complete_in_thread(session.close)
                        session = None

    server = MCPServer(
        "Tamarin Prover",
        instructions=(
            "Explore one persistent native proof session. Load a theory, select "
            "a lemma, then observe methods before applying one with its displayed "
            "revision. Use frontier and goto to navigate. Use graph to inspect "
            "constraint rule nodes and typed edges; graph node IDs are not "
            "proof-tree IDs for goto. Never guess method IDs or revisions. "
            "A cancelled call may have completed: observe before continuing. "
            "A non-recoverable error requires a new server session. "
            "Files are confined to the configured workspace; saving overwrites "
            "an existing .spthy file. This is not an OS sandbox: theories, oracles, "
            "and concurrent filesystem writers must be trusted."
        ),
        lifespan=lifespan,
    )

    async def invoke(operation: str, *args: Any, **kwargs: Any) -> CallToolResult:
        async with lock:
            if session is None:
                raise RuntimeError("The proof session is not running")
            try:
                response = await complete_in_thread(getattr(session, operation), *args, **kwargs)
            except BackendError as exc:
                response = exc.response
            return CallToolResult(
                content=[TextContent(type="text", text=json.dumps(response, ensure_ascii=False))],
                structured_content=response,
                is_error=response["status"] == "error",
            )

    # CallToolResult is intentionally passed through unchanged, preserving both
    # structured backend errors and MCP's isError flag instead of raising ToolError.
    @server.tool(structured_output=False)
    async def tamarin_load(file: str) -> CallToolResult:
        """Load a regular native .spthy theory from the configured workspace."""
        return await invoke("load", file)

    @server.tool(structured_output=False)
    async def tamarin_lemma(name: str) -> CallToolResult:
        """Select or resume a named lemma without applying a proof method."""
        return await invoke("lemma", name)

    @server.tool(structured_output=False)
    async def tamarin_observe(detail: str = "compact") -> CallToolResult:
        """Inspect state and available methods; detail is compact, goals, or full."""
        return await invoke("observe", detail)

    @server.tool(structured_output=False)
    async def tamarin_graph() -> CallToolResult:
        """Inspect expanded constraint nodes and typed edges without changing proof state.

        Rule-node IDs are not proof-tree IDs for goto. Edge ports cN and pN
        index conclusions and premises respectively, starting at zero.
        """
        return await invoke("graph")

    @server.tool(structured_output=False)
    async def tamarin_apply(
        method_id: int, revision: int, timeout_ms: Optional[int] = None
    ) -> CallToolResult:
        """Apply a displayed method at its revision, within the configured timeout budget."""
        return await invoke("apply", method_id, revision=revision, timeout_ms=timeout_ms)

    @server.tool(structured_output=False)
    async def tamarin_frontier() -> CallToolResult:
        """List unfinished leaf nodes of the selected lemma without navigating."""
        return await invoke("frontier")

    @server.tool(structured_output=False)
    async def tamarin_goto(node_id: str, revision: int) -> CallToolResult:
        """Select a node using the revision of the listing that displayed its ID."""
        return await invoke("goto", node_id, revision=revision)

    @server.tool(structured_output=False)
    async def tamarin_save(file: str) -> CallToolResult:
        """Save native proof state inside the workspace; an existing file is overwritten."""
        return await invoke("save", file)

    @server.tool(structured_output=False)
    async def tamarin_check() -> CallToolResult:
        """Inspect proof status without automatically completing the proof."""
        return await invoke("check")

    return server


def main(argv: Optional[Sequence[str]] = None) -> int:
    """Run the stdio adapter; argument help does not import the optional SDK."""
    parser = argparse.ArgumentParser(
        description="Expose one workspace-confined Tamarin proof session over MCP stdio.",
        epilog=(
            "Requires Python 3.10+ and tamarin-cli[mcp]. POSIX safety limits are "
            "not an OS sandbox: trust theories, oracles, and filesystem writers."
        ),
    )
    parser.add_argument("--workspace", required=True, help="Existing directory containing permitted .spthy files")
    parser.add_argument("--backend", help="Shell-quoted backend command prefix (not a shell script)")
    parser.add_argument("--timeout-ms", type=int, default=30000, help="Per-operation wall-time budget in milliseconds")
    parser.add_argument("--cpu-seconds", type=int, default=300, help="Cumulative backend CPU budget in seconds")
    parser.add_argument("--max-file-bytes", type=int, default=8388608, help="Maximum native input/output file size")
    parser.add_argument("--max-response-bytes", type=int, default=8388608, help="Maximum backend protocol response size")
    options = parser.parse_args(argv)
    try:
        server = create_server(**vars(options))
    except RuntimeError as exc:
        parser.error(str(exc))
    server.run(transport="stdio")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
