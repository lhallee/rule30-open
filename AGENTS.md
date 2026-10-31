# Agents working on rule30-open

This repository works on the three Rule 30 Prize problems in the open. Read [README.md](README.md) for the layout and
[CONTRIBUTING.md](CONTRIBUTING.md) for the entry format. These rules apply to every agent:

- **Start from the open work.** [ROADMAP.md](ROADMAP.md) says where each route stands and what is next, and
  [CATALOG.md](CATALOG.md#open-work) lists conjectures to settle and findings that want a Lean proof. When an entry
  changes a route's status, update the roadmap. Before working in a category, read its negative results, so you do not retry an approach that stopped,
  and the [literature](literature/README.md) on its theme, so you do not redo published work.
- **A claim of proof needs a Lean proof that builds.** Run `lake build` and `python scripts/catalog.py audit` before
  saying a theorem is proved. Never use `sorry`, `native_decide`, `decide +native`, `bv_decide`, `skipKernelTC` or a
  new axiom; `catalog.py check` refuses them. Prize submissions go through the kit's own checker, `Check.lean`.
- **Every Lean module has its argument.** A new `Rule30Open/<Category>/<Name>.lean` gets `<Name>.md` beside it, with
  the front matter `catalog.py` checks, and an import in `Rule30Open.lean`.
- **Check the kit before claiming novelty.** Search both parts of the pinned kit, its core Lean
  (`.lake/packages/rule30prize/lean/Ruliology/CellularAutomata/`) and its Mathlib-based equivalent forms and analogues
  (`.lake/packages/rule30prize/equivalents/Rule30Equivalents/`), and set `kit:` to `new` only when the result is in
  neither. Read the kit's module docstrings: they summarize its results.
- **Record what failed.** An approach that did not work is a negative result in `negative-results/<category>/`, with the
  step where it stopped. Do not delete one because a later idea superseded it; link the two.
- **Keep claims inside their evidence.** A computation states its range. A heuristic is labeled as one. Numbers in an
  entry come from code in `computations/` or from a named source.
- **State results, not history.** An entry says what is true and how it is known. Leave out who found it, when, and in
  what order; git history records that.
- **Python follows the existing modules.** Type every function, give every array a shape comment, show progress on a
  loop that runs for more than a few seconds, and test each computation in `tests/` against an independent check.
- **Tests are fast and comprehensive.** `python -m pytest` runs on the machine, on a CPU, not in continuous
  integration, and the whole suite must take under a minute: test each computation on small cases, and leave the large
  runs to the reproduce commands of its entry. The suite takes about 20 minutes now; [tests/README.md](tests/README.md)
  lists the slow tests and how to cut them.
- **Regenerate the catalog.** After editing any entry run `python scripts/catalog.py write`, then `check`.
- **Write plainly.** No em dashes, American English, one term per concept.
