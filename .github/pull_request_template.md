## What this adds

<The entries this pull request adds or changes, and the result of each in one line.>

## Checks

Each item is a rule of [CONTRIBUTING.md](https://github.com/lhallee/rule30-open/blob/main/CONTRIBUTING.md). Tick each item that applies to this pull request.

- [ ] `python scripts/catalog.py write` regenerated CATALOG.md, and `python scripts/catalog.py check` passes.
- [ ] For Lean changes, `lake build` passes and `python scripts/catalog.py audit` reports only `propext`,
      `Classical.choice`, and `Quot.sound`.
- [ ] Each new Lean module has its argument beside it and an import in `Rule30Open.lean`.
- [ ] For a `kit` value of `new`, I searched both the kit's core Lean and its equivalent forms.
- [ ] For Python changes, `python -m pytest` passes on my machine, and the whole suite takes under a minute.
- [ ] Each new computation has a test in `tests/test_<module>.py` against an independent check.
- [ ] Each claim states its range or evidence, and each number comes from code in `computations/` or a named source.
- [ ] ROADMAP.md is updated if a route's status changed.
