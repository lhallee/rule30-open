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
