The Tamarin prover repository
=============================
[![master branch build-status](https://travis-ci.org/tamarin-prover/tamarin-prover.svg?branch=develop)](https://travis-ci.org/tamarin-prover/tamarin-prover)

This README describes the organization of the repository of the Tamarin prover
for security protocol verification. Its intended audience are interested
users and future developers of the Tamarin prover. For installation
and usage instructions of the Tamarin prover see chapter 2 of the manual:
https://tamarin-prover.github.io/manual/master/book/002_installation.html


Developing and contributing
---------------------------

See [contributing instructions](CONTRIBUTING.md) for instructions on how to develop,
test and release changes to the Tamarin prover source code.

Proof exploration in the terminal
---------------------------------

Build and run from this checkout without installing Tamarin:

```sh
stack build --no-install-ghc
./tamarin-cli examples/Tutorial.spthy
```

Requires Python 3.9 or newer and a working Maude installation. The Python
frontend uses only the standard library. In a checkout it uses the local Stack
build rather than an older `tamarin-prover` on `PATH`. Outside a checkout it
uses `tamarin-prover` from `PATH`; override either with `--backend 'COMMAND'`
or `TAMARIN_BACKEND`. The command is an executable prefix, not a shell script;
the client appends the `proof-api` mode. The Python package can also be installed
separately with `python3 -m pip install ./python`, providing `tamarin-cli`.

The REPL supports:

| Commands (shortcuts) | Operation |
| --- | --- |
| `load` (`ld`), `lemmas` (`ls`), `lemma` (`l`) | Load a native theory; list, select, or resume lemmas |
| `state [full]` (`s [full]`), `goals` (`g`), `methods` (`m`) | Show a compact summary or full native state; list goals or methods |
| `observe [--detail compact\|goals\|full] [--json]` | Request structured observations at the chosen detail level |
| `apply <id> [--timeout-ms N]` (`a <id> [--timeout-ms N]`) | Execute one selected method, optionally bounded by a positive millisecond timeout |
| `auto [k]` | Search the selected subtree with up to `k` method applications, or without a limit |
| `branches` (`bs`), `branch <id>` (`b <id>`), `back` (`p`) | Inspect children, select one, or return to its parent |
| `frontier`, `goto <node_id>` | List unfinished leaves across the selected lemma; navigate directly to a revision-local node |
| `undo` (`u`), `redo` (`r`) | Reverse the last proof mutation or restore it |
| `reset` | Replace the selected step and descendants with `sorry` |
| `tree` (`t`) | Display the selected lemma's complete proof tree |
| `graph [--json]` | List the selected constraint graph's rule nodes, facts, and typed edges |
| `save` (`w`), `check` (`c`) | Save native `.spthy`; replay recorded steps and report proof completeness |
| `help` (`h`), `quit` (`q`) | Command help; exit without automatically saving |

Shortcuts accept the same arguments as their full commands, for example
`ld "my theory.spthy"`, `l secrecy`, `a 0`, or `w "partial proof.spthy"`.
`help` lists shortcuts; `help a` (or `h a`) shows help for `apply`.

State responses are compact by default at the backend, not merely shortened by
the terminal: lemma, node, status, goal count, methods, child count, and branches.
`observe --detail goals` adds detailed goals and relevant formulas, equations,
subterms, ordering constraints, and the last-node constraint. `state full` or
`observe --detail full` additionally renders the complete native constraint
system. Compact and goals observations never render the full system.
`observe --detail compact --json` prints the backend response as JSON within the
existing REPL session. `goals` and `methods` list those items separately.

Methods include `id`, `text`, `name`, and `kind`. A goal-solving method also has
`goal_id`, matching the `goal_id` of its detailed goal (`g0`, `g1`, ...).
Goal and method IDs are local to the current node and revision.

Method and branch IDs are local, zero-based indices. `apply` reports generated
branches and enters a sole child automatically, without executing another proof
method. For multiple children it stays at the parent; use `b <id>` to choose.
Unnamed children are displayed as `(continuation)`. Switch siblings with `back`,
then `branch <id>`. Lemma switches retain each lemma's tree and cursor.

`graph` prints the current constraint graph as a node list (rule name/type,
premises, action facts, and conclusions), followed by an edge list. It reuses
the GUI graph model, fully expanded without display simplification, compression,
clustering, or abbreviations. No Graphviz executable is required.
`graph --json` prints the same observation as structured JSON:
`{status, revision, lemma, node_id, graph: {nodes, edges}}`.
Each edge has `source`, `target`, and `type`. Native edge types are:

| Type | Meaning |
| --- | --- |
| `ProtoFact` | Linear protocol-fact dependency |
| `PersistentFact` | Persistent-fact dependency |
| `KFact` | Intruder-knowledge fact dependency |
| `default` | Other fact dependency |
| `LessAtoms` | Temporal ordering constraint |
| `unsolvedChain` | Unresolved destruction-chain dependency |

Fact-flow endpoints such as `#vr:c0` and `#i:p0` identify a rule instance's
zero-based conclusion or premise. Ordering edges connect rule-node IDs directly.
These IDs are **not** proof-tree node IDs accepted by `goto`; the outer `node_id`
identifies the selected proof-tree node. Graph inspection is read-only and does
not invalidate method or navigation revisions. At an initial proof node there
may be no instantiated rules yet; inspect a child state to see its constraints.
Both `TamarinClient.graph()` and `AgentSession.graph()` return this observation.


`frontier` lists unfinished `sorry` leaves in the entire selected lemma,
excluding completed branches and internal nodes. `goto 0.1.0` selects a node
directly without applying a method. Node IDs use canonical zero-based decimal
paths rooted at `0`; `goto` requires the revision of the node listing. The REPL
tracks it from observations, branches, tree, and frontier output. Refresh a
listing after a state change; stale node references are rejected.

`undo` reverses the last successful `apply`, `auto`, or `reset`, even after
navigating or switching lemmas. A completed `auto` run is one undo entry.
`redo` restores the exact resulting proof and selection without re-executing
methods. Navigation, selection, checking, and saving do not create history
entries. A new successful mutation clears redo; failed commands do not.
`reset` explicitly discards only the selected subtree, never an ancestor.
An already-empty `sorry` cannot be reset. Undo can restore a reset subtree.
History is session-only and is cleared by a successful `load`, not persisted in
`.spthy`. Empty lines never repeat proof commands.

`auto 10` applies at most ten methods in total, not ten levels per branch.
`auto` has no step limit; `auto 0` only displays the current state. Search uses
Tamarin's ranked methods depth-first within the selected subtree, preserving
existing steps and visiting unfinished children. The selected subtree root stays
selected, so another `auto` resumes the same scope. Navigation and terminal cases
recognized by the engine do not consume additional steps. Unbounded search
may not terminate. Press **Ctrl-C during auto** to cancel it and return to the
prompt: like the GUI's Cancel action, the entire running operation is discarded,
preserving the pre-auto proof, selection, and undo/redo history.

Individual `apply` steps are also cancellable with **Ctrl-C**.
`apply 0 --timeout-ms 5000` bounds the entire operation, including proof replay,
method ranking, and response preparation. Timeout and cancellation discard the
candidate completely: proof, cursor, revision, and undo/redo history remain
unchanged. They report structured `TIMEOUT` or `CANCELLED` errors and leave the
session usable. No timeout is imposed when omitted.

Loading another theory explicitly replaces the session; save first to retain
edits. Quote paths containing spaces. `quit`, EOF, and Ctrl-C outside `auto` or
`apply` do not save automatically; Ctrl-C outside those operations exits.
Readline command history is available within the session.

Proof construction reuses Tamarin's native methods, including simplification,
induction, and constraint solving. The engine may immediately recognize terminal
cases, as in Explore mode. Subsequent methods run only when explicitly selected
with `apply` or requested with `auto`. `check` replays recorded proof steps
without proof search and returns `verified`, `falsified`, `incomplete`, or `invalid`.
A remaining `sorry` always makes the CLI's result incomplete, even if another
branch already contains a witness; the original prover retains its own
quantifier-specific reporting.

Saving preserves source theory declarations and native proof scripts, not
original whitespace. Partial proofs retain explicit `sorry` branches. Saved
files can be reloaded here, opened in the original GUI, or checked by the
standard prover, for example `stack exec -- tamarin-prover saved.spthy`.
Passing `--prove` to the standard prover explicitly requests automatic search.
The terminal currently explores trace lemmas; diff/equivalence theories still
require the original GUI.

For Python programs, add `python/` to `PYTHONPATH` or install the package:

```python
from tamarin_cli import TamarinClient

with TamarinClient() as client:
    client.load("theory.spthy")
    client.lemma("secrecy")
    listing = client.methods()
    print(listing["methods"])
    # After choosing a method ID, apply using this listing's revision:
    # client.apply(method_id, revision=listing["revision"])
    # Compact by default; request client.observe("goals") or ("full") on demand.
    # client.apply(method_id, revision=listing["revision"], timeout_ms=5000)
    # Or explicitly request search: client.auto(10), or client.auto() unbounded.
    client.save("partial.spthy")
```

Every client operation returns a response dictionary. Backend command errors
raise `BackendError` without replacing the session. `request(command, **fields)`
exposes the underlying protocol for scripting. The synchronous client owns one
backend process; use a context manager or `close()` to release it.
`client.auto(steps=None)` runs cancellable search on the main thread; a
non-negative integer limits method applications. Its response includes
`auto_steps` and `auto_reason` (`step_limit`, `finished`, or `cancelled`).
`apply`, its raw `step` alias, and `auto` must run on the main thread for Ctrl-C
handling. The existing client exposes `observe(detail="compact")`,
`state(detail="compact")`, `frontier()`, and `goto(node_id, revision=...)`.
Use the revision from `frontier` or `tree` when selecting one of its node IDs.

Method application requires an explicit revision:
`client.apply(method_id, revision=listing["revision"])`. Use the revision from
the response containing the methods you selected from, not a later revision.
`client.revision` reports the latest observed revision for inspection; it is
`None` before the first reply. Raw `apply` and `step` requests require
`expected_revision`. Missing or stale tokens raise `BackendError` without
changing the proof, cursor, history, or revision. Refresh `state` or `methods`
and reconsider the choice rather than automatically retrying an old index.

Every response includes a monotonic integer `revision`. Successful load,
lemma selection, branch navigation, goto, apply, reset, undo, redo, and check advance
it, as does an auto run that applies methods; cancelled or zero-step auto runs
do not. Errors (including timed-out/cancelled apply) and read-only observation,
frontier, inspection, and save do not advance it. Undo/redo never
restore old revision numbers, and reload does not reset the counter. Tokens
are local to one backend process and are not proof-storage data.

The REPL supplies the revision belonging to the methods it displays.
After `check`, refresh with `methods` or `state` before applying another step,
or `tree`/`frontier` before navigating with `goto`.
Backend startup, transport, and protocol failures end the REPL with a nonzero
exit status and a warning about unsaved work; ordinary command errors remain
recoverable. The backend is never restarted automatically. To preserve readline
history and completion, an idle backend exit is detected on the next command,
not by interrupting an input prompt. In-flight requests detect a closed stream
immediately. Python callers receive `ProtocolError` or `ClientClosedError`
and must explicitly open a new client session to continue.

The backend can be used directly with
`stack exec --no-install-ghc -- tamarin-prover proof-api`. It accepts one JSON
object per input line and emits one response per ordinary request; engine diagnostics go
to stderr. Requests use `command` and, where needed, `file`, `name`,
`method_id`, `branch_id`, `node_id`, `detail`, `timeout_ms`, or `steps`.
`apply`/`step` and `goto` require `expected_revision`; `timeout_ms`, when present,
must be a positive integer (not `null`). `observe` and `state` accept `compact`
(default), `goals`, or `full` detail. Command names match the REPL. While `auto`
or `apply` is running, send `{"command":"cancel"}` to cancel it. This out-of-band
message never has its own reply (including when idle); the original operation
reports cancellation. Auto retains its successful `auto_reason: "cancelled"`
response; apply returns a `CANCELLED` error.

Responses have `status: "success"` or `status: "error"` and the current
`revision`; current-node status is `branch_status`. Error responses contain
`error: {code, message, recoverable, suggested_action}`. Codes include
`STALE_REVISION`, `INVALID_METHOD`, `INVALID_NODE`, `TIMEOUT`, `CANCELLED`,
`RESOURCE_LIMIT`, `UNSUPPORTED_THEORY`, `INVALID_REQUEST`, `INVALID_STATE`,
`IO_ERROR`, and `ENGINE_ERROR`. Python `BackendError` exposes `code`,
`recoverable`, `suggested_action`, and the complete `response`.
Trees, branches, and frontier entries expose numeric-path `node_id` values.
On `apply`, `applied_at` identifies the node where the method ran and
`generated_branches` lists its resulting children. The ordinary state fields
describe the resulting cursor, including automatic single-child navigation.
Persistent proof files are exclusively native `.spthy`, never JSON.

Run the real-engine integration regressions after building:

```sh
PYTHONPATH=python python3 -m unittest discover -s python/tests -v
```

### Agent sessions and optional MCP server

`AgentSession` adds workspace-confined file operations and bounded execution to
the existing Python client. It owns one persistent proof session and serializes
calls, including calls from worker threads; no terminal or SIGINT handler is
needed. It never chooses a method or retries a mutation on an agent's behalf.

```python
from tamarin_cli import AgentSession

with AgentSession("/absolute/path/to/theories") as agent:
    agent.load("example.spthy")
    observation = agent.lemma("secrecy")
    # Inspect observation["methods"] before choosing a method_id.
    # agent.apply(method_id, revision=observation["revision"], timeout_ms=5000)
    pending = agent.frontier()
    # agent.goto(node_id, revision=pending["revision"])
    agent.save("partial.spthy")
```

Install the optional [official MCP SDK](https://py.sdk.modelcontextprotocol.io/)
extra with Python 3.10 or newer (the base CLI still needs only Python 3.9):

```sh
python3 -m pip install './python[mcp]'
tamarin-mcp --workspace /absolute/path/to/theories
# From a checkout with the extra installed:
PYTHONPATH=python python3 -m tamarin_cli.mcp_server --workspace /absolute/path/to/theories
```

The server uses **stdio only**; its stdout is reserved for MCP messages and
backend diagnostics go to stderr. Configure an MCP host with an absolute
executable and workspace path, for example:

```json
{
  "mcpServers": {
    "tamarin": {
      "command": "/absolute/path/to/venv/bin/tamarin-mcp",
      "args": ["--workspace", "/absolute/path/to/theories"]
    }
  }
}
```

Tools are `tamarin_load`, `tamarin_lemma`, `tamarin_observe`, `tamarin_apply`,
`tamarin_graph`, `tamarin_frontier`, `tamarin_goto`, `tamarin_save`, and `tamarin_check`.
`tamarin_lemma(name)` selects a lemma after loading; `observe` defaults to
compact detail. Apply and goto require the revision of the selected method or
node listing. Tool results expose the backend dictionary as structured content;
errors retain their structured codes and set MCP `isError`. One backend persists
across tool calls and is closed when the server exits.

Safety configuration (also constructor keywords on `AgentSession`):

| CLI option | Python keyword | Default | Scope |
| --- | --- | --- | --- |
| `--timeout-ms` | `timeout_ms` | 30000 | Per-operation wall-time budget; apply gets a native rollback-capable timeout |
| `--cpu-seconds` | `cpu_seconds` | 300 | POSIX cumulative CPU limit per backend/descendant process |
| `--max-file-bytes` | `max_file_bytes` | 8388608 | Maximum theory input and native output file size |
| `--max-response-bytes` | `max_response_bytes` | 8388608 | Maximum backend response size |

`--backend` selects a trusted executable prefix, as with the terminal CLI.
These settings belong to the server operator, not individual tool calls.
An apply timeout may be shortened but cannot exceed the configured budget.
Apply permits one additional second for native timeout rollback before forcing
termination.
A native apply timeout leaves the proof session intact. A hard transport
deadline or response-size violation terminates the backend process group and
invalidates the session; unsaved work is lost and there is no automatic restart.

The safety layer requires POSIX. Paths resolve beneath the required workspace;
escaping traversal/symlinks, non-regular inputs, and non-`.spthy` files are
rejected. Save requires an existing parent and can replace an existing proof
file. These are API restrictions, **not an OS sandbox**: theories can invoke
external ranking oracles, filesystem checks do not defend against hostile
concurrent filesystem changes, and CPU limits are per process, not aggregate
process-tree accounting. Use trusted theories/oracles and a container or
separate OS account for untrusted workloads. Memory is not capped by this layer.

Run the integration command above in an environment with the MCP extra to
include the real stdio MCP regression. Without the extra, only that regression
is skipped; agent-session and native proof integration checks still run.




Version Numbering Policy
-----------------------

We use version numbers with four components.

 - The first component is the major version number. It indicates complete
   rewrites of the codebase.
 - The second component is the minor version number. We use odd minor version
   numbers to denote development releases intended for early adopters. We use
   even minor version numbers to denote public releases, which are also
   published.
 - The third component indicates bugfix releases.
 - The fourth component indicates documentation and meta-data changes.

We ensure that the external interface of a version of the Tamarin prover is backwards
compatible with the external interface of all versions that agree on the major
and minor version number.

We announce all releases of the Tamarin prover on:
http://tamarin-prover.github.io


Manual
------

The manual is available as PDF or HTML at https://tamarin-prover.github.io/manual/index.html

Experimental improved graph output
----------------------------------

You can use our experimental improved graph output which may be
helpful for very large graphs that can be created for complicated
protocols. To enable this feature read the instructions about
[improved graphs](/misc/cleandot/README.md).

Spthy code editors
------------------

The project contains support for spthy syntax highlighting and support
in the [etc](/etc/) directory. This includes support for [Sublime Text](/etc/SUBLIME_TEXT.md), [VIM](/etc/spthy.vim) and [Notepad++](/etc/notepad_plus_plus_spthy.xml).

External tools
------------------

External tools may use the [Tree-sitter](https://tree-sitter.github.io/tree-sitter/) grammar
in the [tree-sitter/](/tree-sitter/) directory.


Example Protocol Models
-----------------------

All example protocol models are found in the directory

    ./examples/

All models that we consider stable
are part of every installation of the Tamarin prover. See
`tamarin-prover.cabal` for the list of installed protocols. We use the
following sub-directories to organize the models.

~~~~
accountability/ case studies using the accountability implementation presented in
                the "Verifying Accountability for Unbounded Sets of Participants" paper
csf12/          the AKE case studies from our CSF'12 paper.
classic/        classic security protocols like the ones from
                [SPORE](http://www.lsv.ens-cachan.fr/Software/spore/table.html)
loops/          experiments for testing loop-invariants and protocols with
                non-monotonic state
related_work/   examples from related work on protocols with loops or
                non-monotonic state
experiments/    all other experiments
ake/            more AKE examples including ID-based and tripartite group KE
                protocols based on bilinear pairing
features/       (small) models that demonstrate a given feature
ccs15/	        the observational equivalence case studies from our CCS'15 paper
csf-18/         the XOR case studies from the CSF'18 paper
~~~~

Feel free to add more sub-directories and describe them here.

In general, we try use descriptive names for files containing the models. We
also document all our findings as comments in the protocol model.  Moreover,
we use the following header in all files to make their context more explicit.

~~~~
/*
   Protocol:    Example
   Modeler:     Simon Meier, Benedikt Schmidt
   Date:        January 2012

   Status:      working

   Description of protocol.

*/
~~~~
