"""Human-readable Explore-mode terminal interface with opt-in proof search."""

from __future__ import annotations

import argparse
import cmd
import json
import shlex
import sys
from typing import Any, Dict, Optional, Sequence, TextIO

from .client import (
    BackendError,
    BackendUnavailableError,
    ClientClosedError,
    ProtocolError,
    TamarinClient,
    TamarinError,
)


class TamarinShell(cmd.Cmd):
    """Explore native proofs manually or with explicitly requested automation."""

    intro = "Tamarin Interactive CLI — proof exploration. Type help for commands."
    prompt = "tamarin> "

    def __init__(
        self,
        client: TamarinClient,
        *,
        stdin: Optional[TextIO] = None,
        stdout: Optional[TextIO] = None,
    ) -> None:
        super().__init__(stdin=stdin, stdout=stdout)
        self.client = client
        self.current_node_id: Optional[str] = None
        self.displayed_revision: Optional[int] = None
        self.displayed_node_revision: Optional[int] = None
        if stdin is not None:
            self.use_rawinput = False

    def emptyline(self) -> None:
        """Never repeat a previous command, especially a proof mutation."""

    def preloop(self) -> None:
        # Preserve readline's normal blocking input. An idle backend death is
        # detected on the next command, not by interrupting the input prompt.
        self.client.check_alive()

    def onecmd(self, line: str) -> bool:
        self.client.check_alive()
        try:
            return bool(super().onecmd(line))
        except BackendError as exc:
            self._show_error(exc)
            return False
        except (ValueError, OSError) as exc:
            self._print(f"Error: {exc}")
            return False

    def default(self, line: str) -> None:
        self._print(f"Unknown command: {line!r}. Type help for commands.")

    def _print(self, text: str = "") -> None:
        print(text, file=self.stdout)

    def _show_error(self, error: BackendError) -> None:
        self._print(f"Error [{error.code}]: {error}")
        if error.suggested_action:
            self._print(f"Suggested action: {error.suggested_action}")

    @staticmethod
    def _arguments(argument: str, count: int, usage: str) -> list[str]:
        values = shlex.split(argument)
        if len(values) != count:
            raise ValueError(f"Usage: {usage}; quote paths or names containing spaces")
        return values

    @classmethod
    def _id(cls, argument: str, usage: str) -> int:
        value = cls._arguments(argument, 1, usage)[0]
        try:
            result = int(value)
        except ValueError as exc:
            raise ValueError("ID must be a zero-based integer from the displayed list") from exc
        if result < 0:
            raise ValueError("ID must be non-negative (IDs are zero-based)")
        return result

    def _show_lemmas(self, response: Dict[str, Any]) -> None:
        lemmas = response.get("lemmas", [])
        self._print("Lemmas:")
        for lemma in lemmas:
            self._print(f"  {lemma['name']} [{lemma['status']}]")
        if not lemmas:
            self._print("  (none)")

    def _show_items(self, title: str, items: Sequence[Dict[str, Any]]) -> None:
        self._print(f"{title}:")
        for item in items:
            text = str(item["text"]).replace("\n", "\n      ")
            self._print(f"  [{item['id']}] {text}")
        if not items:
            self._print("  (none)")

    def _show_branches(
        self, response: Dict[str, Any], *, title: str = "Branches"
    ) -> None:
        branches = response.get("branches", [])
        self._print(f"{title}:")
        for branch in branches:
            self._print(
                f"  [{branch['id']}] {branch['name'] or '(continuation)'} "
                f"[{branch['status']}] (node {branch['node_id']})"
            )
        if not branches:
            self._print("  (none)")

    def _remember_state(self, response: Dict[str, Any]) -> None:
        self.current_node_id = response["node_id"]
        self.displayed_revision = response["revision"]
        self.displayed_node_revision = response["revision"]

    def _show_state(
        self,
        response: Dict[str, Any],
        *,
        full: bool = False,
        show_branches: bool = True,
    ) -> None:
        self._remember_state(response)
        self._print(
            f"Lemma: {response['lemma']} | Node: {response['node_id']} "
            f"| Status: {response['branch_status']}"
        )
        if full:
            state = response.get("state", "")
            self._print(str(state) if state else "(No further proof-state details.)")
        self._print(f"Goals: {response.get('goal_count', len(response.get('goals', [])))}")
        if response.get("methods"):
            self._show_items("Methods", response["methods"])
        if show_branches and response.get("branches"):
            self._show_branches(response)

    def load_file(self, file: str) -> None:
        """Load one file, also used by the optional initial command-line file."""
        response = self.client.load(file)
        self.current_node_id = None
        self.displayed_revision = None
        self.displayed_node_revision = None
        self._print(f"Loaded theory: {response['theory']} ({response['file']})")
        self._show_lemmas(response)

    def do_load(self, argument: str) -> None:
        """load <file.spthy>: Load a native theory and its existing proofs.

        Quote paths containing spaces, e.g. load "my theories/example.spthy".
        Loading replaces the current theory; save first to retain changes.
        """
        self.load_file(self._arguments(argument, 1, "load <file.spthy>")[0])

    def do_lemmas(self, argument: str) -> None:
        """lemmas: List the theory's lemma names and proof statuses."""
        self._arguments(argument, 0, "lemmas")
        self._show_lemmas(self.client.lemmas())

    def do_lemma(self, argument: str) -> None:
        """lemma <name>: Select or resume a lemma; do not run any proof method."""
        name = self._arguments(argument, 1, "lemma <name>")[0]
        self._show_state(self.client.lemma(name))

    def do_state(self, argument: str) -> None:
        """state [full]: Show a compact summary, or the full native proof state.

        Use goals or methods to list those items, or observe for JSON and details.
        """
        arguments = shlex.split(argument)
        if arguments not in ([], ["full"]):
            raise ValueError(
                "Usage: state [full]; quote paths or names containing spaces"
            )
        detail = "full" if arguments else "compact"
        self._show_state(self.client.state(detail=detail), full=bool(arguments))

    def do_observe(self, argument: str) -> None:
        """observe [--detail compact|goals|full] [--json]: Inspect the current node.

        Compact detail shows counts, methods, and branches. Goals detail adds
        goals and structured constraints; full also includes native state text.
        JSON prints only the exact backend response, without a summary.
        """
        arguments = shlex.split(argument)
        usage = "Usage: observe [--detail compact|goals|full] [--json]"
        detail = "compact"
        as_json = False
        while arguments:
            option = arguments.pop(0)
            if option == "--json" and not as_json:
                as_json = True
            elif option == "--detail" and arguments:
                detail = arguments.pop(0)
                if detail not in ("compact", "goals", "full"):
                    raise ValueError(usage)
            else:
                raise ValueError(usage)
        response = self.client.observe(detail=detail)
        if as_json:
            self._remember_state(response)
            self._print(json.dumps(response, ensure_ascii=False))
            return
        self._show_state(response, full=detail == "full")
        if detail in ("goals", "full"):
            self._show_items("Goals", response["goals"])
            self._print("Constraints:")
            self._print(json.dumps(response["constraints"], ensure_ascii=False, indent=2))

    def do_goals(self, argument: str) -> None:
        """goals: List open goals at the current proof node."""
        self._arguments(argument, 0, "goals")
        self._show_items("Goals", self.client.goals()["goals"])

    def do_methods(self, argument: str) -> None:
        """methods: List applicable proof methods and their zero-based IDs.

        Listing methods never executes them. Use apply <id> to choose one.
        """
        self._arguments(argument, 0, "methods")
        response = self.client.methods()
        self.displayed_revision = response["revision"]
        self._show_items("Methods", response["methods"])

    def do_apply(self, argument: str) -> None:
        """apply <id> [--timeout-ms N]: Apply one explicitly selected proof method.

        IDs refer to the displayed methods list and its backend revision.
        A sole generated child is entered automatically without applying more
        methods. For multiple children, choose one with branch <id>.
        Ctrl-C cancels the operation; a timeout is a positive millisecond limit.
        """
        arguments = shlex.split(argument)
        usage = "apply <id> [--timeout-ms N]"
        if len(arguments) not in (1, 3):
            raise ValueError(f"Usage: {usage}")
        method_id = self._id(shlex.join(arguments[:1]), usage)
        timeout_ms = None
        if len(arguments) == 3:
            if arguments[1] != "--timeout-ms":
                raise ValueError(f"Usage: {usage}")
            try:
                timeout_ms = int(arguments[2])
            except ValueError as exc:
                raise ValueError("timeout-ms must be a positive integer") from exc
            if timeout_ms <= 0:
                raise ValueError("timeout-ms must be a positive integer")
        if self.displayed_revision is None:
            raise ValueError(
                "No methods revision displayed; select a lemma or run methods "
                "before applying a method"
            )
        parameters = {"revision": self.displayed_revision}
        if timeout_ms is not None:
            parameters["timeout_ms"] = timeout_ms
        response = self.client.apply(method_id, **parameters)
        self._print(f"Applied: {response['applied']} (node {response['applied_at']})")
        generated = response["generated_branches"]
        self._show_branches({"branches": generated}, title="Generated branches")
        if len(generated) == 1:
            self._print(f"Auto-entered sole child: node {response['node_id']}")
        elif len(generated) > 1:
            self._print("Choose a branch with b <id>.")
        self._show_state(response, show_branches=len(generated) <= 1)

    def do_auto(self, argument: str) -> None:
        """auto [k]: Apply up to k ranked methods, or run without a step limit.

        Search unfinished branches depth-first within the selected subtree.
        Existing steps are retained; a completed run is one undo entry.
        Navigation and engine-recognized terminal cases do not consume steps.
        Zero steps only displays the current state. Unbounded search may loop;
        Ctrl-C cancels it, restoring the pre-auto proof and returning to the prompt.
        """
        arguments = shlex.split(argument)
        usage = "Usage: auto [k]; k must be a non-negative integer"
        if len(arguments) > 1:
            raise ValueError(usage)
        limit = None
        if arguments:
            try:
                limit = int(arguments[0])
            except ValueError as exc:
                raise ValueError(usage) from exc
            if limit < 0:
                raise ValueError(usage)

        self._print("Running auto; press Ctrl-C to cancel.")
        self.stdout.flush()
        response = self.client.auto(limit)
        if response["auto_reason"] == "cancelled":
            self._print("Auto cancelled; proof unchanged.")
        else:
            reason = (
                "step limit reached" if response["auto_reason"] == "step_limit"
                else "no further applicable steps in selected subtree"
            )
            self._print(f"Auto: {response['auto_steps']} step(s); {reason}.")
        self._show_state(response)

    def do_branches(self, argument: str) -> None:
        """branches: List immediate child branches, their IDs, and statuses."""
        self._arguments(argument, 0, "branches")
        response = self.client.branches()
        self.displayed_node_revision = response["revision"]
        self._show_branches(response)

    def do_branch(self, argument: str) -> None:
        """branch <id>: Select a child using its local zero-based branch ID.

        To switch siblings, use back followed by branch <id>.
        """
        self._show_state(self.client.branch(self._id(argument, "branch <id>")))

    def do_back(self, argument: str) -> None:
        """back: Navigate to the parent node without changing proof steps."""
        self._arguments(argument, 0, "back")
        self._show_state(self.client.back())

    def do_undo(self, argument: str) -> None:
        """undo: Undo the last apply/auto/reset, restoring its prior selection.

        History spans the session; navigation alone is not a mutation.
        """
        self._arguments(argument, 0, "undo")
        self._show_state(self.client.undo())

    def do_redo(self, argument: str) -> None:
        """redo: Restore the last undone mutation and its resulting selection.

        A new successful proof mutation clears redo history.
        """
        self._arguments(argument, 0, "redo")
        self._show_state(self.client.redo())

    def do_reset(self, argument: str) -> None:
        """reset: Replace the selected proof subtree with an unfinished step.

        Resets this node and its descendants, never an ancestor. Use undo to
        restore the subtree; resetting an already-empty unfinished node fails.
        """
        self._arguments(argument, 0, "reset")
        self._show_state(self.client.reset())

    def do_goto(self, argument: str) -> None:
        """goto <node_id>: Select a node from the latest state, tree, or frontier.

        Node IDs are canonical paths such as 0 or 0.1.2 in the selected lemma.
        Outdated node listings are rejected without changing the selection.
        """
        node_id = self._arguments(argument, 1, "goto <node_id>")[0]
        if self.displayed_node_revision is None:
            raise ValueError(
                "No node revision displayed; select a lemma or run tree or "
                "frontier before navigating"
            )
        self._show_state(
            self.client.goto(node_id, revision=self.displayed_node_revision)
        )

    def do_frontier(self, argument: str) -> None:
        """frontier: List unfinished leaf nodes across the selected lemma.

        Use goto <node_id> to select a listed node without applying a method.
        """
        self._arguments(argument, 0, "frontier")
        response = self.client.frontier()
        self.displayed_node_revision = response["revision"]
        self._print(f"Frontier: {response['lemma']}")
        for node in response["frontier"]:
            self._print(
                f"  {node['node_id']} [{node['branch_status']}] "
                f"(goals: {node['goal_count']})"
            )
        if not response["frontier"]:
            self._print("  (none)")

    def do_tree(self, argument: str) -> None:
        """tree: Display the complete hierarchical proof tree for this lemma."""
        self._arguments(argument, 0, "tree")
        response = self.client.tree()
        self.displayed_node_revision = response["revision"]
        root = response["tree"]
        # An explicit stack also handles proof trees deeper than Python's
        # recursion limit. This is presentation, not construction of proof nodes.
        pending = [(root, "", "", "")]
        while pending:
            node, prefix, connector, child_prefix = pending.pop()
            marker = " *" if node["node_id"] == self.current_node_id else ""
            method = f" — {node['method']}" if node.get("method") else ""
            self._print(
                f"{prefix}{connector}{node['node_id']} "
                f"{node['name'] or '(continuation)'}{method} "
                f"[{node['status']}]{marker}"
            )
            children = node.get("children", [])
            for index in range(len(children) - 1, -1, -1):
                last = index == len(children) - 1
                pending.append((
                    children[index], child_prefix,
                    "`-- " if last else "|-- ",
                    child_prefix + ("    " if last else "|   "),
                ))
        self._print("* current node")

    def do_save(self, argument: str) -> None:
        """save <file.spthy>: Save the native theory and recorded proofs.

        Unfinished branches remain unfinished; saving does not prove them.
        """
        file = self._arguments(argument, 1, "save <file.spthy>")[0]
        response = self.client.save(file)
        self._print(f"Saved theory and proofs: {response['file']}")

    def do_check(self, argument: str) -> None:
        """check: Inspect proof completeness without applying any methods.

        An incomplete proof is never reported as verified.
        """
        self._arguments(argument, 0, "check")
        response = self.client.check()
        self.displayed_revision = None
        self.displayed_node_revision = None
        self._print(f"{response['lemma']}: {response['result']}")
        if response.get("message"):
            self._print(str(response["message"]))

    def do_quit(self, argument: str) -> bool:
        """quit: Exit without saving automatically. Use save first if needed."""
        self._arguments(argument, 0, "quit")
        self.client.quit()
        return True

    def do_EOF(self, argument: str) -> bool:
        """End-of-file (Ctrl-D): Close the backend and exit without auto-saving."""
        self._print()
        self.client.close()
        return True

    def do_help(self, argument: str) -> None:
        """help [command]: Show commands, shortcuts, or help for one command."""
        super().do_help(argument)
        if not argument.strip():
            self._print(
                "Shortcuts: ld=load, ls=lemmas, l=lemma, s=state, g=goals,\n"
                "           m=methods, a=apply, bs=branches, b=branch, p=back,\n"
                "           u=undo, r=redo, t=tree, w=save, c=check, h=help, q=quit\n"
                "           reset has no single-letter shortcut"
            )

    # cmd.Cmd discovers these aliases for dispatch, help, and tab completion.
    do_ld = do_load
    do_ls = do_lemmas
    do_l = do_lemma
    do_s = do_state
    do_g = do_goals
    do_m = do_methods
    do_a = do_apply
    do_bs = do_branches
    do_b = do_branch
    do_p = do_back
    do_u = do_undo
    do_r = do_redo
    do_t = do_tree
    do_w = do_save
    do_c = do_check
    do_h = do_help
    do_q = do_quit


def main(argv: Optional[Sequence[str]] = None) -> int:
    """Run the proof terminal; return a conventional process exit code."""
    parser = argparse.ArgumentParser(
        prog="tamarin-cli",
        description="Explore Tamarin proofs manually or with the auto command.",
        epilog="Quote REPL paths containing spaces. Use help inside the REPL for commands.",
    )
    parser.add_argument("file", nargs="?", help="native .spthy theory to load initially")
    parser.add_argument(
        "--backend", metavar="COMMAND",
        help=(
            "shell-quoted backend command prefix (proof-api is appended); "
            "defaults to TAMARIN_BACKEND, repository Stack build, or installed tamarin-prover"
        ),
    )
    arguments = parser.parse_args(argv)
    try:
        import readline
    except ImportError:
        pass
    else:
        readline.set_history_length(1000)
    try:
        with TamarinClient(arguments.backend) as client:
            shell = TamarinShell(client)
            if arguments.file:
                try:
                    shell.load_file(arguments.file)
                except BackendError as exc:
                    shell._show_error(exc)
                except (ValueError, OSError) as exc:
                    shell._print(f"Error: {exc}")
            shell.cmdloop()
        return 0
    except (ProtocolError, ClientClosedError, BackendUnavailableError) as exc:
        print(
            f"Backend session unavailable or ended: {exc}\n"
            "Unsaved work may have been lost. Exiting without automatically "
            "restarting the backend.",
            file=sys.stderr,
        )
        return 1
    except TamarinError as exc:
        print(f"Error: {exc}", file=sys.stderr)
        return 1
    except KeyboardInterrupt:
        print("\nInterrupted; exiting without automatically saving.", file=sys.stderr)
        return 130
