module

public import Rule30Open.Columns.ClassGame

/-!
# A certificate of the game with cyclic classes, checked over several modules

The kernel check of a `ClassCert` reads, at width `j + 1`, only the block and the heights of widths `j` and `j + 1`
(`ClassCert.levelOk`). So the widths of a large certificate can be checked in several modules, each on a certificate
whose `levels` is a prefix of the full one, and carried to the full certificate here.

* `ClassCert.tri_append`: when `d.levels = c.levels ++ t`, the heights of `c` and `d` agree up to the length of
  `c.levels`.
* `ClassCert.levelOk_append`: the check of width `j + 1` is then the same for `c` and `d` when the blocks agree and
  `j < c.levels.length`.

The natural-language argument is `ClassSplit.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

/-- The heights of two certificates agree up to the length of the shorter list of widths when one extends the other. -/
theorem ClassCert.tri_append (c d : ClassCert) (t : List (List KeyTrie)) (hl : d.levels = c.levels ++ t) {i : Nat}
    (hi : i ≤ c.levels.length) (φ : Nat) : d.tri i φ = c.tri i φ := by
  cases i with
  | zero => rfl
  | succ i =>
    have hi' : i < c.levels.length := by omega
    simp only [tri, hl, List.getD_eq_getElem?_getD, List.getElem?_append_left hi']

/-- **The checks of a width carry over.** When `d` has the block of `c` and extends its widths, the check of width
`j + 1` is the same for both, for `j` below the number of widths of `c`. -/
theorem ClassCert.levelOk_append (c d : ClassCert) (t : List (List KeyTrie)) (hb : d.block = c.block)
    (hl : d.levels = c.levels ++ t) {j : Nat} (hj : j < c.levels.length) (φ : Nat) :
    d.levelOk j φ = c.levelOk j φ := by
  have h1 : ∀ ψ, d.tri j ψ = c.tri j ψ := tri_append c d t hl (by omega)
  have h2 : ∀ ψ, d.tri (j + 1) ψ = c.tri (j + 1) ψ := tri_append c d t hl (by omega)
  simp only [levelOk, center, next, hb, h1, h2]

end Rule30Open
