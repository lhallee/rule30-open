# Proofs by checked computation

Many Lean results here are finite certificates that the kernel evaluates by `decide +kernel`: the game certificates of
[FiniteGame](../Rule30Open/Columns/FiniteGame.md) and [GameBlocks](../Rule30Open/Columns/GameBlocks.md), the entry
tables of [EmptyRight](../Rule30Open/Columns/EmptyRight.md), and many of the kit's modules. The sources below are the
precedents for this method and for its trade-off between the size of a certificate and the cost of checking it.

## Large finite checks

- **The bbchallenge Collaboration (2025).** [Determination of the fifth Busy Beaver value](https://doi.org/10.48550/arXiv.2509.12337).
  arXiv:2509.12337.
  Proves that the fifth Busy Beaver value is 47,176,870 with a Coq proof that decides halting for all 181,385,789
  five-state machines it enumerates: a finite enumeration at scale, checked by a proof assistant's kernel.
- **Antihydra (bbchallenge wiki, 2024 to 2026).** [Antihydra](https://wiki.bbchallenge.org/wiki/Antihydra), a stable
  wiki page, and [OEIS A386792](https://oeis.org/A386792); both were seen through a search (the wiki is outside this
  session's network), not read. A Turing machine of six states and two symbols, found in June 2024, whose halting the
  wiki rewrites as a question on one orbit of a map of the shape of Collatz's: from $(8, 0)$, iterate
  $(a, b) \mapsto (3a/2, b + 2)$ for even $a$ and $((3a - 1)/2, b - 1)$ for odd $a$, and ask whether $b$ ever reaches
  $-1$, that is whether the odd values ever outnumber twice the even ones. It is open; the wiki gives a probabilistic
  heuristic, not a proof, that it never halts. So the enumeration that settled five states, entry above, meets at six
  states a problem of the kind of the Collatz conjecture. *Here:* period two reduces to the held map
  $H(U) = (U \gg 1) \oplus (U \lor (U \ll 1))$, with period two needing some $U > 0$ whose orbit keeps one parity
  condition at every odd time ([HeldColumn](../Rule30Open/PeriodTwo/HeldColumn.md)); every integer below $2^{52}$ breaks
  it ([the left half alone](../findings/period-two/left-half-alone.md)) and no finite certificate of the forms tried
  closes it ([no certificate](../negative-results/period-two/no-finite-certificate.md)). Antihydra is the same obstacle
  for a kernel-checked enumeration, met by an independent project: one counting condition along an orbit of a map,
  which no finite search has settled. The maps differ: Antihydra's is arithmetic, with the carries of $3a/2$, and $H$ is
  bitwise, with none; and Antihydra's question is about one start, the held map's about every positive integer.
- **Heule, Kullmann and Marek (2016).**
  [Solving and verifying the Boolean Pythagorean triples problem via cube-and-conquer](https://doi.org/10.1007/978-3-319-40970-2_15).
  SAT 2016, *Lecture Notes in Computer Science* 9710, 228 to 245; [arXiv:1605.00723](https://arxiv.org/abs/1605.00723).
  The positive integers cannot be split into two classes that both avoid Pythagorean triples. The nearly 200 TB proof
  was compressed to a 68 GB certificate that others can regenerate and check.
  *Here:* the same trade-off, at a much smaller scale, leaves two certificates out of the build in
  [GameBlocks](../Rule30Open/Columns/GameBlocks.md).
- **Brakensiek, Heule, Mackey and Narváez (2022).** [The resolution of Keller's conjecture](https://doi.org/10.1007/s10817-022-09623-5).
  *Journal of Automated Reasoning* 66(3), 277 to 300; IJCAR 2020; [arXiv:1910.03740](https://arxiv.org/abs/1910.03740).
  Settles Keller's conjecture in dimension 7 by a SAT search made tractable by symmetry breaking.
- **Hales et al. (2017).** [A formal proof of the Kepler conjecture](https://doi.org/10.1017/fmp.2017.1).
  *Forum of Mathematics, Pi* 5, e2.
  The Flyspeck project: a computer-assisted proof checked in HOL Light and Isabelle.

## Computation inside the kernel

- **Grégoire and Mahboubi (2005).** [Proving equalities in a commutative ring done right in Coq](https://doi.org/10.1007/11541868_7).
  TPHOLs 2005, *Lecture Notes in Computer Science*, 98 to 113.
  A decision procedure proved correct once and then run by the kernel on each goal, which is proof by reflection: the
  pattern of a certificate with a checked `check` function and a soundness theorem, as in `GameMask.check` and
  `mask_column`.
- **de Moura and Ullrich (2021).** [The Lean 4 theorem prover and programming language](https://doi.org/10.1007/978-3-030-79876-5_37).
  CADE-28, *Lecture Notes in Computer Science*, 625 to 635.
  The system this repository is written in.

The repository allows `decide +kernel`, in which the kernel itself evaluates the computation, and refuses
`native_decide`, which trusts compiled code (see [CONTRIBUTING.md](../CONTRIBUTING.md)).

- **Szeider (2026).** *LRAT-Catcher: importing SAT solver certificates into Lean 4 by reflection*; the PDF at
  [arXiv:2607.00815](https://arxiv.org/abs/2607.00815) is titled *Streaming LRAT certificates into Lean theorems*. The
  record and fragments of the abstract were seen through a search (arxiv.org is outside this session's network), the
  text was not read. By the abstract, it turns a DIMACS formula and an LRAT certificate into a Lean 4 theorem by running
  the formally verified LRAT checker of Lean's core as compiled native code, through reflection; it handles instances on
  which importing an explicit proof term with Mathlib runs out of memory, and joins the refutations of the cubes of a
  cube-and-conquer run, with an LRAT certificate that the cubes cover every case, into one theorem. *Here:* a proof
  that runs compiled code rests on the axiom `Lean.ofReduceBool`, the one `native_decide` adds, and the checks of this
  repository and the kit's `Check.lean` refuse it; so a SAT encoding of the finite game or of a trap's closure could
  enter only through the kernel's own evaluation, as the 78 checks by `decide +kernel` of
  [BitBlocks18](../Rule30Open/Columns/BitBlocks18.md) do, at the cost in memory that the tool was built to avoid.

- **Lean kernel issue #14576 (2026).** [Checked-kernel soundness: projections of a mismatched
  structure](https://github.com/leanprover/lean4/issues/14576), fixed by [pull request
  #14577](https://github.com/leanprover/lean4/pull/14577), merged into `master` on July 28, 2026. The report shows a
  metaprogram that adds a nested inductive declaration whose parameters escape type checking, after which ordinary code
  proves `False` with no axioms; `#print axioms` shows nothing. A follow-up, pull request #14582, checks the uniformity
  of nested occurrences. Press coverage, seen only through a search, reports that a claimed AI-assisted disproof of the
  Collatz conjecture used this bug. *Here:* the repository builds with Lean 4.35.0 (commit `eb6cafb`, released October
  12, 2026, eleven weeks after the fix's merge commit `a39eab6`), and no module here adds declarations by metaprogram,
  which the exploit needs. The episode is a reason to keep the audit of axioms in `scripts/catalog.py` and to build
  only from source.
