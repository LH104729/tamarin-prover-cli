"""Human-readable, manually controlled Explore-mode terminal interface."""

from __future__ import annotations

import argparse
import cmd
import shlex
import sys
from typing import Any, Dict, Optional, Sequence, TextIO

from .client import TamarinClient, TamarinError


class TamarinShell(cmd.Cmd):
    """Present backend responses without choosing or applying proof methods."""

    intro = "Tamarin Interactive CLI — manual proof exploration. Type help for commands."
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
        if stdin is not None:
            self.use_rawinput = False

    def emptyline(self) -> None:
        """Never repeat a previous command, especially a proof mutation."""

    def onecmd(self, line: str) -> bool:
        try:
            return bool(super().onecmd(line))
        except (TamarinError, ValueError, OSError) as exc:
            self._print(f"Error: {exc}")
            return False

    def default(self, line: str) -> None:
        self._print(f"Unknown command: {line!r}. Type help for commands.")

    def _print(self, text: str = "") -> None:
        print(text, file=self.stdout)

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

    def _show_state(
        self,
        response: Dict[str, Any],
        *,
        full: bool = False,
        show_branches: bool = True,
    ) -> None:
        self.current_node_id = response["node_id"]
        self._print(
            f"Lemma: {response['lemma']} | Node: {response['node_id']} "
            f"| Status: {response['branch_status']}"
        )
        if full:
            state = response.get("state", "")
            self._print(str(state) if state else "(No further proof-state details.)")
        self._print(f"Goals: {len(response.get('goals', []))}")
        if response.get("methods"):
            self._show_items("Methods", response["methods"])
        if show_branches and response.get("branches"):
            self._show_branches(response)

    def load_file(self, file: str) -> None:
        """Load one file, also used by the optional initial command-line file."""
        response = self.client.load(file)
        self.current_node_id = None
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

        Use goals or methods to list those items individually.
        """
        arguments = shlex.split(argument)
        if arguments not in ([], ["full"]):
            raise ValueError(
                "Usage: state [full]; quote paths or names containing spaces"
            )
        self._show_state(self.client.state(), full=bool(arguments))

    def do_goals(self, argument: str) -> None:
        """goals: List open goals at the current proof node."""
        self._arguments(argument, 0, "goals")
        self._show_items("Goals", self.client.goals()["goals"])

    def do_methods(self, argument: str) -> None:
        """methods: List applicable proof methods and their zero-based IDs.

        Listing methods never executes them. Use apply <id> to choose one.
        """
        self._arguments(argument, 0, "methods")
        self._show_items("Methods", self.client.methods()["methods"])

    def do_apply(self, argument: str) -> None:
        """apply <id>: Apply exactly one explicitly selected proof method.

        IDs refer to the current node's methods list and may change after a step.
        A sole generated child is entered automatically without applying more
        methods. For multiple children, choose one with branch <id>.
        """
        response = self.client.apply(self._id(argument, "apply <id>"))
        self._print(f"Applied: {response['applied']} (node {response['applied_at']})")
        generated = response["generated_branches"]
        self._show_branches({"branches": generated}, title="Generated branches")
        if len(generated) == 1:
            self._print(f"Auto-entered sole child: node {response['node_id']}")
        elif len(generated) > 1:
            self._print("Choose a branch with b <id>.")
        self._show_state(response, show_branches=len(generated) <= 1)

    def do_branches(self, argument: str) -> None:
        """branches: List immediate child branches, their IDs, and statuses."""
        self._arguments(argument, 0, "branches")
        self._show_branches(self.client.branches())

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
        """undo: Undo the last apply/reset mutation, restoring its prior selection.

        History spans the session; navigation alone is not a mutation.
        """
        self._arguments(argument, 0, "undo")
        self._show_state(self.client.undo())

    def do_redo(self, argument: str) -> None:
        """redo: Restore the last undone mutation and its resulting selection.

        A new successful apply or reset clears redo history.
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

    def do_tree(self, argument: str) -> None:
        """tree: Display the complete hierarchical proof tree for this lemma."""
        self._arguments(argument, 0, "tree")
        root = self.client.tree()["tree"]
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
        """save <file.spthy>: Save the native theory and manually built proofs.

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
    """Run the manual proof terminal; return a conventional process exit code."""
    parser = argparse.ArgumentParser(
        prog="tamarin-step",
        description="Manually explore Tamarin proofs; no proof methods run automatically.",
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
                except (TamarinError, ValueError, OSError) as exc:
                    shell._print(f"Error: {exc}")
            shell.cmdloop()
        return 0
    except TamarinError as exc:
        print(f"Error: {exc}", file=sys.stderr)
        return 1
    except KeyboardInterrupt:
        print("\nInterrupted; exiting without automatically saving.", file=sys.stderr)
        return 130
