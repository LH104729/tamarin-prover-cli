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

Manual proof exploration in the terminal
----------------------------------------

Build and run from this checkout without installing Tamarin:

```sh
stack build --no-install-ghc
./tamarin-step examples/Tutorial.spthy
```

Requires Python 3.9 or newer and a working Maude installation. The Python
frontend uses only the standard library. In a checkout it uses the local Stack
build rather than an older `tamarin-prover` on `PATH`. Outside a checkout it
uses `tamarin-prover` from `PATH`; override either with `--backend 'COMMAND'`
or `TAMARIN_BACKEND`. The command is an executable prefix, not a shell script;
the client appends the `proof-api` mode. The Python package can also be installed
separately with `python3 -m pip install ./python`, providing `tamarin-step`.

The REPL supports:

| Commands (shortcuts) | Operation |
| --- | --- |
| `load` (`ld`), `lemmas` (`ls`), `lemma` (`l`) | Load a native theory; list, select, or resume lemmas |
| `state` (`s`), `goals` (`g`), `methods` (`m`) | Inspect constraints, facts, open goals, and applicable methods |
| `apply <id>` (`a <id>`) | Execute exactly one explicitly selected engine proof method |
| `branches` (`bs`), `branch <id>` (`b <id>`), `back` (`p`) | Inspect children, select one, or return to its parent |
| `undo` (`u`) | Replace the selected step and descendants with `sorry` |
| `tree` (`t`) | Display the selected lemma's complete proof tree |
| `save` (`w`), `check` (`c`) | Save native `.spthy`; replay recorded steps and report proof completeness |
| `help` (`h`), `quit` (`q`) | Command help; exit without automatically saving |

Shortcuts accept the same arguments as their full commands, for example
`ld "my theory.spthy"`, `l secrecy`, `a 0`, or `w "partial proof.spthy"`.
`help` lists shortcuts; `help a` (or `h a`) shows help for `apply`.

Method and branch IDs are local, zero-based indices. Applying a method leaves
the cursor at its node; use `branches` and `branch <id>` to inspect resulting
states. Switch siblings with `back`, then `branch <id>`. Lemma switches retain
each lemma's tree and cursor. `undo` at an unfinished leaf resets the nearest
applied ancestor; it discards that step's subtree. Undo before replacing an
existing step. Empty lines never repeat proof commands.

Loading another theory explicitly replaces the session; save first to retain
edits. Quote paths containing spaces. `quit`, EOF, and Ctrl-C do not save
automatically. Readline command history is available within the session.

Proof construction reuses Tamarin's native methods, including simplification,
induction, and constraint solving. The engine may immediately recognize terminal
cases, as in Explore mode, but the CLI does not automatically choose subsequent
methods. `check` replays recorded proof steps without proof search and returns
`verified`, `falsified`, `incomplete`, or `invalid`. A remaining `sorry` always
makes the CLI's result incomplete, even if another branch already contains a
witness; the original prover retains its own quantifier-specific reporting.

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
    methods = client.methods()["methods"]
    # Inspect methods before explicitly calling client.apply(method_id).
    print(methods)
    client.save("partial.spthy")
```

Every client operation returns a response dictionary. Backend command errors
raise `BackendError` without replacing the session. `request(command, **fields)`
exposes the underlying protocol for scripting. The synchronous client owns one
backend process; use a context manager or `close()` to release it.

The backend can be used directly with
`stack exec --no-install-ghc -- tamarin-prover proof-api`. It accepts one JSON
object per input line and emits one response per line; engine diagnostics go
to stderr. Requests use `command` and, where needed, `file`, `name`,
`method_id`, or `branch_id`. Command names match the REPL. Responses have
`status: "success"` or `status: "error"` with a `message`; current-node status
is `branch_status`. Trees and branches expose numeric-path `node_id` values.
Persistent proof files are exclusively native `.spthy`, never JSON.

Run the real-engine integration regressions after building:

```sh
PYTHONPATH=python python3 -m unittest discover -s python/tests -v
```



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
