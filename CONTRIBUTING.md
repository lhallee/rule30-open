# Contributing

Everything here is an entry: a Lean module with its argument, a finding, or a negative result. Each is a Markdown file
with YAML front matter that `scripts/catalog.py` checks and turns into [CATALOG.md](CATALOG.md). Pick the category from
[categories.yaml](categories.yaml); add a category there if none fits.

## A Lean result

1. Write `Rule30Open/<Category>/<Name>.lean` as a module: `module`, then `public import`s, then a `/-! ... -/` docstring
   that states the results and ends with "The natural-language argument is `<Name>.md`, beside this file.", then
   `@[expose] public section` and `namespace Rule30Open`.
2. Import it from [Rule30Open.lean](Rule30Open.lean).
3. State the headline results for every starting row where the argument allows (`evolve init t x`), and give an
   official form with `Rule30Prize.center` through `evolve_single_center` when the result is about the center column.
4. Write `<Name>.md` beside it:

```yaml
---
title: A short claim, as the catalog will show it
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.Name
headline: [main_theorem, second_theorem]
kit: new            # new, independent, refines or bridge
kit_modules: [Rule30Jen]
---

# A short claim, as the catalog will show it
```

The body states the theorems in mathematical notation, gives the argument a reader can follow without Lean, says where
each step lives in the module, and says what the kit has. [AdjacentColumns.md](Rule30Open/Columns/AdjacentColumns.md)
is a model. `catalog.py` refuses a front matter field it does not know.

**Not allowed in Lean files:** `sorry`, `native_decide`, `decide +native`, `bv_decide`, `skipKernelTC` and new axioms.
`decide +kernel` is fine: the kernel itself evaluates it. `python scripts/catalog.py audit` must report only `propext`,
`Classical.choice` and `Quot.sound`.

## A finding

A file in `findings/<category>/` with `status: paper`, `computed` or `conjecture` and `formalization: wanted`,
`partial` or `not-applicable`. Give the result first, then the method or proof, then how to reproduce it. A computation
belongs in [computations/](computations/README.md), runnable as `python -m computations.<module>`, with a test
in `tests/` that checks it against something independent; list it under `evidence`.

## A negative result

A file in `negative-results/<category>/` with `status: negative` and `kind`:

- `no-signal`: a search or test that found nothing, with its controls, so the reader knows what it could have found.
- `refuted`: a conjecture or picture that is false, with the counterexample.
- `dead-end`: an approach that reduces to something as hard as the problem, with the step where it stops.
- `barrier`: a reason a whole class of approaches cannot work.

State the question, what was done, the outcome with its numbers, and what it means. Say plainly when the code is not
in this repository.

## Checks

```bash
lake build
python scripts/catalog.py write   # regenerate CATALOG.md after editing any entry
python scripts/catalog.py check   # front matter, placement, links, pairing of modules and arguments
python scripts/catalog.py audit   # axioms of every headline theorem
python -m pytest
```

Continuous integration runs the same commands. Write without em dashes, in American English, and keep claims inside
their evidence: a computation to $2^{20}$ cells is a statement about $2^{20}$ cells.

## Credit

Git history records who wrote what, and when; an entry states only the result and how it is known. A result that
builds on another, inside or outside this repository, cites it in the body.
