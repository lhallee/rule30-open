# Literature

The published work around the three Rule 30 Prize problems, by theme. Every source here was checked against a
bibliographic record: a publisher or DOI page, an arXiv abstract, Crossref, Semantic Scholar, or the source itself.
Each summary says only what that record or the source supports, an unrefereed claim is reported as a claim, and each
entry says where the source bears on this repository. The search covers sources available in October 2026.

| File | Problems | What it covers |
|---|---|---|
| [rule-30.md](rule-30.md) | 1, 2, 3 | The prize and its formal statements, Wolfram's papers, the data, the structure of the pattern, and the claims made since 2019 |
| [columns.md](columns.md) | 1 | Jen's theorems, permutive and expansive automata, traces and single columns, directional dynamics, 2-adic views |
| [measure-and-analogs.md](measure-and-analogs.md) | 2, 1 | Invariant measures, randomization, entropy, the statistics of the center column, and sibling rules |
| [complexity.md](complexity.md) | 3 | The cost of computing Rule 30, prediction hardness, the lower-bound landscape, and Rule 30 as a cipher |
| [certified-computation.md](certified-computation.md) | all | Precedents for proofs by kernel-checked computation, the method of many Lean entries here |

## Where the problems stand

**Problem 1.** No two columns of the single cell's pattern are both eventually periodic (Jen 1986, proved in the kit),
and no column is eventually constant, for the single cell (the kit) and for every row with a leftmost black cell (here;
claimed for finite rows in a 2026 preprint). Specific eventual periods are excluded by certificates: between the kit
and this repository, 75 of the 2,538 primitive blocks of period at most 14 are excluded in Lean and 2 more by
computation, and the kit also excludes families of padded words and shows that an eventual period $P$ after a
transient $T$ needs $T + P \ge 16{,}359$. The general theory of single columns reaches pairs of columns and special
classes of automata, not one column of one orbit: Kopra (2023) puts Rule 30 in a class whose traces two cells wide are
never eventually periodic and states the one-cell center column as open, and Rule 90, in the same class, has an
eventually periodic center column, so a proof has to use more than the properties that define the class. One preprint
claims a solution; none is refereed, and the prize is unclaimed.

**Problem 2.** For a uniformly random initial row each center cell is black with probability exactly 1/2, because
Rule 30 is onto; the single cell has measure zero, so this says nothing about it. Theorems that drive measures to the
uniform one exist only for linear rules, whose single-cell center columns are periodic. The evidence for density 1/2 is
statistical: the first million cells counted in *A New Kind of Science*, a billion published, and test batteries that
find no deviation.

**Problem 3.** Only upper bounds are known: about $n^2$ cell updates by direct simulation, $O(n^2/\log n)$ for whole
rows, and $O(n)$ operations on a random-access machine with bitwise operations. No lower bound is known for Rule 30 or
for any comparable explicit function. Predicting Rule 110 is P-complete; natural proofs bar many circuit techniques if
Rule 30 behaves as a pseudorandom generator; and Rule 30's orbits compute every Boolean function of up to five
variables, short of the universality a reduction would need.

## Leads not yet checked

The search found these but could not confirm the record or read the text. Check each before citing it.

- Wen (2019), *Analysis of black and white cells in the center column of Rule 30*, Wolfram Notebook Archive; listed in
  the prize bibliography; too large to open.
- Wiles (2023), *Conditional patterns in Rule 30 and their implications on computational reducibility*, an informal web
  page that claims cheaper computation of some cells.
- Koc and Apohan (about 1997), an inversion algorithm for Rule 30 that later surveys describe; the original was not
  found.
- Shereshevsky (1992), *Ergodic properties of certain surjective cellular automata*, *Monatshefte für Mathematik*,
  reported to prove Bernoulli properties for automata permutive with one-sided windows; the record was not reached.
- Jen (1990), Los Alamos report LA-UR-90-761, the report version of her Physica D paper; the scan did not open, and
  the statement of her Proposition 3 should be read there or in the journal.
- Kůrka (2003), *Topological and Symbolic Dynamics*, Société Mathématique de France, and Anashin and Khrennikov (2009),
  *Applied Algebraic Dynamics*, De Gruyter; the standard books on the two frameworks, whose records were not reached.
- Guillon and Richard (2010), *Revisiting the Rice theorem of cellular automata*, STACS 2010; the record's metadata
  conflict.
- Jose and RoyChowdhury (2015), IACR ePrint 2015/700, reported to break Rule 30 keystreams and propose a replacement.
- Moore (1990), *Unpredictability and undecidability in dynamical systems*, *Physical Review Letters* 64(20); the record
  is confirmed, the text was not read.
- Ollinger (2012), *Universalities in cellular automata*, Handbook of Natural Computing; the record is confirmed, the
  text was not read.
- Boespflug, Dénès and Grégoire (2011), *Full reduction at full throttle*, Certified Programs and Proofs; the record is
  confirmed, the text was not read.
- Fukś, *Orbits of Bernoulli measures in cellular automata*, [arXiv:2002.09079](https://arxiv.org/abs/2002.09079), and
  *Sequences of preimages in elementary cellular automata*; reported to list Rule 30 among the surjective rules and to
  estimate densities from preimage counts.
- Bobenko, Bordemann, Gunn and Pinkall (1993), *On two integrable cellular automata*, *Communications in Mathematical
  Physics* 158(1), 127 to 134; the record is in the authors' publication list, the text was not read.

Kumar (2024), arXiv:2411.03468, which claimed to settle Mahler's 3/2 problem, was withdrawn; do not cite it.

## Format

An entry gives the authors and year, the title linked to a DOI or a stable page, the venue, what the source establishes
in one to three sentences, and, after *Here:*, the entries of this repository it bears on. [CONTRIBUTING.md](../CONTRIBUTING.md#a-source)
says how to add one.
