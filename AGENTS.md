# Agents working on rule30-open

This repository works on the three Rule 30 Prize problems in the open. Read [README.md](README.md) for the layout and
[CONTRIBUTING.md](CONTRIBUTING.md) for the entry format. These rules apply to every agent:

- **Start from the open work.** [CATALOG.md](CATALOG.md#open-work) lists conjectures to settle and findings that want a
  Lean proof. Before working in a category, read its negative results, so you do not retry an approach that stopped.
- **A claim of proof needs a Lean proof that builds.** Run `lake build` and `python scripts/catalog.py audit` before
  saying a theorem is proved. Never use `sorry`, `native_decide`, `decide +native`, `bv_decide`, `skipKernelTC` or a
  new axiom; `catalog.py check` refuses them. Prize submissions go through the kit's own checker, `Check.lean`.
- **Every Lean module has its argument.** A new `Rule30Open/<Category>/<Name>.lean` gets `<Name>.md` beside it, with
  the front matter `catalog.py` checks, and an import in `Rule30Open.lean`.
- **Check the kit before claiming novelty.** Search the pinned kit
  (`.lake/packages/rule30prize/lean/Ruliology/CellularAutomata/`) for the result, and set `kit:` to `new` only when it is
  not there. Read the kit's module docstrings: they summarize its results.
- **Record what failed.** An approach that did not work is a negative result in `negative-results/<category>/`, with the
  step where it stopped. Do not delete one because a later idea superseded it; link the two.
- **Keep claims inside their evidence.** A computation states its range. A heuristic is labeled as one. Numbers in an
  entry come from code in `computations/` or from a named source.
- **State results, not history.** An entry says what is true and how it is known. Leave out who found it, when, and in
  what order; git history records that.
- **Python follows the existing modules.** Type every function, give every array a shape comment, show progress on a
  loop that runs for more than a few seconds, and test each computation in `tests/` against an independent check.
- **Regenerate the catalog.** After editing any entry run `python scripts/catalog.py write`, then `check`.
- **Write plainly.** No em dashes, American English, one term per concept.
