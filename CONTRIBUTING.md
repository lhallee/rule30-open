# Contributing

This page holds every rule and every how-to for contributing to this repository, for people and for AI agents alike.
Everything here is an entry: a Lean module with its argument, a finding, or a negative result. Each entry is a Markdown
file with YAML front matter that `scripts/catalog.py` checks and turns into [CATALOG.md](CATALOG.md). Proofs, findings,
and negative results are all welcome, because a well-documented dead end saves the next person weeks.

## First contribution

### Prerequisites

- **Git**, to clone the repository and the prize kit.
- **Lean 4 through elan.** Install [elan](https://github.com/leanprover/elan), Lean's toolchain manager, by its own
  instructions. The repository pins the Lean version in [`lean-toolchain`](lean-toolchain), and elan installs that
  version, with its `lake`, the first time you run `lake` here.
- **Python 3.12 or later**, as [`pyproject.toml`](pyproject.toml) requires. `pip install -e ".[test]"` installs NumPy,
  SciPy, PyYAML, tqdm, and pytest. The extras `topology` and `sat` serve only the modules that `pyproject.toml` names
  beside them. `scripts/catalog.py` on its own needs only PyYAML. On Windows, set `PYTHONUTF8=1` before redirecting a
  generator's output to a file, because the Lean text it prints holds characters such as `→` that Python cannot
  encode in the Windows code page and stops on.
- **A C compiler named `cc` or `gcc`** on the `PATH`. The modules with a C program compile it on first use and stop with
  "a C compiler is needed" when neither name is found, so their tests fail without one. Some programs compile with
  `-fopenmp` and `-march=native`, so the compiler must accept those flags.
- **The prize kit** at `.lake/packages/rule30prize/`. `lake build` fetches it there at the commit pinned in
  [`lake-manifest.json`](lake-manifest.json). Several tests and computations read the kit's Lean source from that path,
  so to run them without building, clone the kit there yourself at the `rev` of `rule30prize` in `lake-manifest.json`:

  ```bash
  git clone https://github.com/WolframInstitute/Rule30PrizeKit .lake/packages/rule30prize
  git -C .lake/packages/rule30prize checkout <rev from lake-manifest.json>
  ```

### Build, test, and check

Clone the repository and run the rest from its root:

```bash
git clone https://github.com/lhallee/rule30-open.git
cd rule30-open
lake build                          # fetch the prize kit and check every proof
python scripts/catalog.py audit     # print the axioms of every headline theorem
pip install -e ".[test]"
python -m pytest                    # the tests, on your machine
python scripts/catalog.py check     # the entries, the links, and CATALOG.md
```

The first `lake build` checks about 98 MB of Lean source, most of it in modules whose data a computation
prints (see [generated certificate modules](#generated-certificate-modules)), and takes far longer than a rebuild, which checks
only what changed. `audit` runs Lean on the built library, so it needs `lake build` first.

### Pick open work

Open work is listed in two places. [CATALOG.md](CATALOG.md#open-work), generated from the findings, lists conjectures to
prove or refute and findings that want a Lean proof. [ROADMAP.md](ROADMAP.md#next-steps) lists the next step of each
route toward the three problems. A finding marked `formalization: wanted` is an open task: turn it into a Lean module
with its argument. Before you work in a category, read its negative results, so you do not retry an approach that
stopped, and the [literature](literature/README.md) on its theme, so you do not redo published work.
[GLOSSARY.md](GLOSSARY.md) defines the project's terms.

### Add the entry, check it, and open a pull request

1. Add the entry by the section below for its kind, starting from its file in [templates/](templates/).
2. If the entry changes a route's status, update [ROADMAP.md](ROADMAP.md).
3. Run `python scripts/catalog.py write` to regenerate CATALOG.md, then `python scripts/catalog.py check`. CI runs
   `check`, not `write`, so a catalog left stale fails CI.
4. Run `lake build` and `python scripts/catalog.py audit` if you changed Lean, and `python -m pytest` if you changed
   Python.
5. Open a pull request against `main`. [The pull request template](.github/pull_request_template.md) lists what you
   confirm, and every item is a rule on this page.

## Front matter

Every entry starts with a line `---`, its fields, and a line `---`, and its body starts with the heading `# <title>`.
`catalog.py check` refuses a field it does not know. Put a value that holds `: ` or starts with a character such as
`*`, `&`, `[`, or `{` in quotes, as in `title: "A: B"`, and write a list in brackets even when it holds one name.

| Field | Entries | Value |
|---|---|---|
| `title` | all, required | The claim in one line, as the catalog shows it. |
| `category` | all, required | An `id` from [categories.yaml](categories.yaml). Add a category there if none fits. |
| `problems` | all, required | The prize problems the entry bears on, a list drawn from 1, 2, and 3, as in `[1, 3]`. |
| `status` | all, required | `proved` for a Lean module, `paper`, `computed`, or `conjecture` for a finding, and `negative` for a negative result. |
| `lean` | Lean, required | The module's name, `Rule30Open.<Directory>.<Name>`, which is its path. |
| `headline` | Lean, required | The module's main theorems, each as it is declared in the module (see [headline names](#headline-names)). `audit` checks the axioms of exactly these. |
| `kit` | Lean, required | How the result relates to the prize kit, one of four values (below). |
| `kit_modules` | Lean, optional | The kit modules the result builds on or compares with. A core module goes by its file name, as `Rule30Jen` for `lean/Ruliology/CellularAutomata/Rule30Jen.lean`, and a module of the equivalent forms as `Rule30Equivalents.<Name>`. |
| `formalization` | finding, required | `wanted` (no Lean proof yet), `partial` (a Lean proof of part of it), `kit` (the kit proves it in Lean, and the entry names the theorems), or `not-applicable`. |
| `kind` | negative result, required | `no-signal`, `refuted`, `dead-end`, or `barrier` (see [a negative result](#a-negative-result)). |
| `evidence` | all, optional | The code or data the entry rests on, as paths from the repository root, such as `computations/game.py`. Most Lean arguments use it for the computation that produced the module's data. |

The four values of `kit`, with the label CATALOG.md prints for each:

| `kit` | Catalog label | Use it when |
|---|---|---|
| `new` | not in the kit | Neither part of the kit has the result (see [checking the kit](#check-the-kit-before-claiming-novelty)). |
| `independent` | independent proof of a kit result | The kit proves the same statement and this module proves it another way. |
| `refines` | extends a kit result | The module strengthens or generalizes a kit result. |
| `bridge` | connects to the kit | The module connects this library's definitions or statements to the kit's. |

## A Lean result

### Where it goes and what it is called

A module lives one directory deep, at `Rule30Open/<Directory>/<Name>.lean`, where `<Directory>` is the `lean` value of
its category in [categories.yaml](categories.yaml). A category with no `lean` value has no Lean modules yet, and adding
one starts with giving it a `lean` directory there. Every module name in the tree is UpperCamelCase, letters and digits,
and names what the module proves or builds (`AdjacentColumns`, `StripeClassCount`, `ClassBlocks16`). The module's name
is its path, `Rule30Open.<Directory>.<Name>`.

### The module

1. Write `Rule30Open/<Directory>/<Name>.lean` in this shape:

   ```lean
   module

   public import Rule30Open.Foundations.Evolve

   /-!
   # The claim

   What the module proves, with the name of each headline theorem.

   The natural-language argument is `<Name>.md`, beside this file.
   -/

   @[expose] public section

   namespace Rule30Open

   -- the definitions and theorems

   end Rule30Open
   ```

2. Add the line `public import Rule30Open.<Directory>.<Name>` to [Rule30Open.lean](Rule30Open.lean).
3. State the headline results for every starting row where the argument allows (`evolve init t x`), and give an official
   form with `Rule30Prize.center` through `evolve_single_center` when the result is about the center column.
4. Write `<Name>.md` beside it from [the template](templates/lean-argument.md). The body states the theorems in
   mathematical notation, gives the argument a reader can follow without Lean, says where each step lives in the
   module, and says what the kit has. [AdjacentColumns.md](Rule30Open/Columns/AdjacentColumns.md) is a model.

### Headline names

`check` matches each headline name literally against the name after `theorem`, `def`, `structure`, or `abbrev` at the
start of a line of the module, and `audit` looks up `Rule30Open.<name>`. A headline must therefore be declared with the
name it is listed by, directly inside `namespace Rule30Open`. For a dotted name, declare it with the dotted name in full:
[StripeClasses.lean](Rule30Open/Frames/StripeClasses.lean) declares `theorem StripeClasses.box_columns ...`, and its
argument lists `StripeClasses.box_columns`. A theorem declared as `box_columns` inside a nested
`namespace StripeClasses` would pass `check` under the name `box_columns` and fail `audit`, which would look for
`Rule30Open.box_columns`.

### What a Lean file may not contain

`sorry`, `native_decide`, `decide +native`, `bv_decide`, `skipKernelTC`, and new axioms are not allowed. `check` looks
for these strings anywhere in the source, comments and docstrings included, so do not write them there either.
`decide +kernel` is allowed, because the kernel itself evaluates it. `python scripts/catalog.py audit` must report only
`propext`, `Classical.choice`, and `Quot.sound`. Prize submissions go through the kit's own checker, `Check.lean`.

### Generated certificate modules

A module whose bulk is data, a certificate or a table that the kernel checks, is printed by a computation rather than
written by hand. The module's docstring names the computation, its argument lists it under `evidence`, and the
argument's `## Reproduce` section gives the command. The generators differ in their interface, and each generator's
module docstring lists its commands, as in these three:

```bash
python -m computations.class_blocks --lean ClassBlocks16 > Rule30Open/Columns/ClassBlocks16.lean
python -m computations.forced_basin lean --width 18 --size 16 > Rule30Open/Columns/ForcedBasin18.lean
python -m computations.long_window --lean    # the literals of LongWindow.lean, pasted into the module
```

A certificate too large for one Lean process is split over several modules, each with its own argument, such as
`ClassBlocks17Split` and its parts `ClassBlocks17SplitA1` to `ClassBlocks17SplitB3`, and many generated modules set
`set_option Elab.async false` so that their kernel checks run one after another rather than in parallel, where their
memory would add up. A test does not regenerate a whole module. It runs the generator on a small case and checks that
the text it writes appears in the module's file, as [tests/README.md](tests/README.md) describes.

### Check the kit before claiming novelty

Search both parts of the pinned kit, its core Lean (`.lake/packages/rule30prize/lean/Ruliology/CellularAutomata/`) and
its Mathlib-based equivalent forms and analogues (`.lake/packages/rule30prize/equivalents/Rule30Equivalents/`), and set
`kit: new` only when the result is in neither. The kit's module docstrings summarize its results.

## A finding

A file in `findings/<category>/`, started from [the template](templates/finding.md), with `status: paper`, `computed`,
or `conjecture` and a `formalization` value. Give the result first, then the method or proof, then how to reproduce it.
A computation belongs in [computations/](computations/README.md) with a test (see [a computation](#a-computation-and-its-test)),
listed under `evidence`.

## A negative result

A file in `negative-results/<category>/`, started from [the template](templates/negative-result.md), with
`status: negative` and a `kind`:

- `no-signal`: a search or test that found nothing, with its controls, so the reader knows what it could have found.
- `refuted`: a conjecture or picture that is false, with the counterexample.
- `dead-end`: an approach that reduces to something as hard as the problem, with the step where it stops.
- `barrier`: a reason a whole class of approaches cannot work.

State the question, what was done, the outcome with its numbers, and what it means. Say plainly when the code is not in
this repository. Do not delete a negative result because a later idea superseded it, and link the two instead.

## A source

An entry in the theme file of [literature/](literature/README.md) that fits it, in the format that page gives. Add a
source only after checking it against a bibliographic record (a publisher or DOI page, an arXiv abstract, or the source
itself), summarize it in your own words, and say where it bears on the entries here. Report an unrefereed claim as a
claim.

## A computation and its test

A computation is a module `computations/<module>.py`, started from [the template](templates/computation.py), that
reproduces the numbers its entries quote and runs as `python -m computations.<module>` from the repository root. Its
docstring says what it computes and lists its commands. Type every function, give every array a shape comment, and show
progress with tqdm on a loop that runs for more than a few seconds. Numbers in an entry come from code in
`computations/` or from a named source.

A search too slow for NumPy can be a C program `computations/<name>.c` beside its module. The module compiles it on first
use with `compiled(name, flags)` from `computations/c_programs.py`, which keeps the binary for later runs, and runs it
with `subprocess`. Test the C program against a Python implementation on small cases, as
`test_c_against_python` in `tests/test_wedge_hypotheses.py` does.

Every computation has a test file `tests/test_<module>.py`, started from [the template](templates/test_computation.py),
that checks it against something independent: a second implementation, a known sequence, a direct run with `step`, or a
number its entry quotes. `python -m pytest` runs on your machine, on a CPU, not in CI, and the whole suite must take
under a minute, serially. Test each computation on small cases and leave the large runs to the reproduce commands of its
entries. [tests/README.md](tests/README.md) gives the layout of the suite and how it stays fast.

## Writing

Write in plain sentences and American English, without em dashes, with one term per concept. Keep claims inside their
evidence: a computation to $2^{20}$ cells is a statement about $2^{20}$ cells, a computation states its range, and a
heuristic is labeled as one. State results, not history. An entry says what is true and how it is known, and leaves out
who found it, when, and in what order, because git history records that. A result that builds on another, inside or
outside this repository, cites it in the body.

## What is checked

The tools enforce the rules in the first table. CI runs `python scripts/catalog.py check` on every push and pull
request, and runs `lake build` and `python scripts/catalog.py audit` in a second job.

| Rule | Checked by |
|---|---|
| Each `.lean` module has its `.md` argument, and each argument its module | `check` |
| A module lives at `Rule30Open/<category directory>/<Name>.lean`, one directory deep | `check` |
| Every module is imported in `Rule30Open.lean`, and every import there exists | `check` |
| No forbidden string and no `axiom` declaration in Lean source | `check` |
| Front matter is valid YAML with every required field and no unknown field | `check` |
| `category`, `status`, `kit`, `formalization`, and `kind` take allowed values | `check` |
| `problems` is a nonempty list from 1, 2, and 3 without repeats, and list fields are lists | `check` |
| The body starts with `# <title>` | `check` |
| `lean` equals the module's path, and the category keeps its modules in that directory | `check` |
| A finding or negative result sits in the directory of its category | `check` |
| `headline` is nonempty and each name is declared in the module | `check` |
| Each `evidence` path exists | `check` |
| Relative links resolve in the entries, the top-level pages, and the pages of `tests/`, `findings/`, `negative-results/`, `computations/`, and `literature/` | `check` |
| CATALOG.md is what `catalog.py write` produces | `check` |
| Every proof checks | `lake build`, in CI |
| Each headline theorem uses only `propext`, `Classical.choice`, and `Quot.sound` | `audit`, in CI |

A reviewer checks the rest, which no tool does:

| Rule | Who checks |
|---|---|
| The tests pass and the suite takes under a minute | the author, by `python -m pytest`, and the reviewer |
| Every computation has a test against an independent check | reviewer |
| The `kit` value is right, after a search of both parts of the kit | reviewer |
| `kit_modules` names modules of the pinned kit | reviewer |
| The module docstring ends with the sentence that names its argument | reviewer |
| The argument matches the proof, and headline results are stated for every starting row where the argument allows | reviewer |
| Claims stay inside their evidence, and the writing follows [Writing](#writing) | reviewer |
| ROADMAP.md reflects a changed route status | reviewer |
| The counts in README.md match the first paragraph of CATALOG.md | reviewer |
