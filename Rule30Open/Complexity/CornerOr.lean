module

public import Rule30Open.Complexity.RightCorner
public import Rule30Open.Complexity.QueryDepth

/-!
# The center sees the two rightmost cells of its cone only through their OR

Write `c_t(x) = evo x t 0` for the center after `t` steps from a row `x`, a Boolean function of the `2t + 1` cells
`-t .. t`.

* `center_flip_beside_black`: if cell `t` is black, flipping cell `t - 1` does not change the center, for every `t`.
* `center_flip_corner_of_black`: if cell `t - 1` is black, flipping cell `t` does not change the center, for
  `t ≥ 1` (from `corner_white` of `RightCorner`).
* `center_corner_or`: so for `t ≥ 1` the center depends on the cells `t - 1` and `t` only through
  `x (t - 1) || x t`: it equals the center of the row with cell `t - 1` white and cell `t` set to that OR.
* `corner_tree_lift`: a decision tree for the center with cell `t - 1` held white gives a tree for the center one
  query deeper: read cell `t - 1`, and on black run the tree with cell `t` fixed to black.

The proof of the first statement follows the diagonals at the right edge of the cone (`rdiag`, with `a = t`). A flip
of `R 1` at time 0 beside a black `R 0` stays on `R 1` while `R 2` is white, and `R 0` stays black meanwhile; the first
black `R 2` absorbs it. In every case the two rows keep the same `R 0` (`CornerKeep`, `corner_keep_succ`), and `R 0` at
time `t` is the center.

This is a statement about an arbitrary input row. Its consequences bound the restriction certificates for the
decision-tree depth of `c_t` (`CornerOr.md`), a query model for an arbitrary row, and say nothing about the single
black cell's column, where a tree reads nothing.

The natural-language argument is `CornerOr.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

open QTree

/-- The invariant of a flip beside a black corner: the rows agree on the diagonals `k ≥ 2` and on `R 0`, and they
agree on `R 1` too unless `R 0` is black. -/
def CornerKeep (z x : Int → Bool) (a : Int) (s : Nat) : Prop :=
  DiagAgree z x a 2 s ∧ rdiag z a 0 s = rdiag x a 0 s ∧ (rdiag z a 1 s = rdiag x a 1 s ∨ rdiag x a 0 s = true)

theorem corner_keep_succ {z x : Int → Bool} {a : Int} {s : Nat} (h : CornerKeep z x a s) :
    CornerKeep z x a (s + 1) := by
  obtain ⟨hag, h0, h1⟩ := h
  refine ⟨agree_succ hag, ?_, ?_⟩
  · rw [rd0 z, rd0 x, hag 2 (by omega), h0]
    rcases h1 with h1 | h1
    · rw [h1]
    · rw [h1]
      generalize rdiag z a 1 s = p
      generalize rdiag x a 1 s = q
      cases p <;> cases q <;> rfl
  · rw [rd1 z, rd1 x, rd0 x, hag 2 (by omega), hag 3 (by omega)]
    rcases h1 with h1 | h1
    · left; rw [h1]
    · rw [h1]
      generalize rdiag x a 3 s = p
      generalize rdiag x a 2 s = q
      generalize rdiag z a 1 s = r
      generalize rdiag x a 1 s = u
      cases p <;> cases q <;> cases r <;> cases u <;> simp

theorem corner_keep_all {z x : Int → Bool} {a : Int} (h : CornerKeep z x a 0) : ∀ n : Nat, CornerKeep z x a n
  | 0 => h
  | n + 1 => corner_keep_succ (corner_keep_all h n)

/-- **A black corner shields the cell beside it.** If cell `t` is black, flipping cell `t - 1` does not change the
center after `t` steps. -/
theorem center_flip_beside_black (x : Int → Bool) (t : Nat) (h : x t = true) :
    evo (flipAt x ((t : Int) - 1)) t 0 = evo x t 0 := by
  have h0 : CornerKeep (flipAt x ((t : Int) - 1)) x t 0 := by
    refine ⟨?_, ?_, Or.inr ?_⟩
    · have hf := agree_flip x t 1
      intro k hk
      exact hf k (by omega)
    · rw [rdiag_zero, rdiag_zero]
      have hne : (t : Int) - 0 = (t : Int) ∧ (t : Int) ≠ (t : Int) - 1 := ⟨by omega, by omega⟩
      rw [hne.1]
      simp [flipAt, hne.2]
    · rw [rdiag_zero]
      simpa using h
  rw [← rdiag_center, ← rdiag_center]
  exact (corner_keep_all h0 t).2.1

/-- **A black cell beside the corner shields the corner.** If cell `t - 1` is black and `t ≥ 1`, flipping cell `t`
does not change the center after `t` steps. -/
theorem center_flip_corner_of_black (x : Int → Bool) (t : Nat) (ht : 1 ≤ t) (h : x ((t : Int) - 1) = true) :
    evo (flipAt x t) t 0 = evo x t 0 := by
  apply Classical.byContradiction
  intro hne
  have hw := corner_white x t hne 0 (by omega)
  rw [rdiag_zero] at hw
  rw [h] at hw
  cases hw

theorem setAt_self (x : Int → Bool) (u : Int) : setAt x u (x u) = x := by
  funext j
  by_cases hj : j = u
  · subst hj; simp [setAt]
  · simp [setAt, hj]

/-- **The OR of the two rightmost cells.** For `t ≥ 1` the center after `t` steps equals the center of the row with
cell `t - 1` white and cell `t` set to `x (t - 1) || x t`. -/
theorem center_corner_or (x : Int → Bool) (t : Nat) (ht : 1 ≤ t) :
    evo x t 0 = evo (setAt (setAt x ((t : Int) - 1) false) t (x ((t : Int) - 1) || x t)) t 0 := by
  have hne : ((t : Int) - 1) ≠ (t : Int) := by omega
  cases ha : x ((t : Int) - 1) with
  | false =>
    have e : setAt (setAt x ((t : Int) - 1) false) t (false || x t) = x := by
      funext j
      by_cases hj : j = (t : Int)
      · subst hj; simp [setAt]
      · by_cases hj' : j = (t : Int) - 1
        · subst hj'; simp [setAt, hne, ha]
        · simp [setAt, hj, hj']
    rw [e]
  | true =>
    -- Flip cell t - 1 (beside the black corner) after setting cell t black: the center does not move.
    have e1 : evo (setAt x t true) t 0 = evo x t 0 := by
      cases hb : x t with
      | true => rw [← hb, setAt_self]
      | false =>
        have e : setAt x t true = flipAt x t := by
          funext j
          by_cases hj : j = (t : Int)
          · subst hj; simp [setAt, flipAt, hb]
          · simp [setAt, flipAt, hj]
        rw [e]
        exact center_flip_corner_of_black x t ht ha
    have e2 : setAt (setAt x ((t : Int) - 1) false) t (true || x t) =
        flipAt (setAt x t true) ((t : Int) - 1) := by
      funext j
      by_cases hj : j = (t : Int)
      · subst hj; simp [setAt, flipAt, hne.symm]
      · by_cases hj' : j = (t : Int) - 1
        · subst hj'; simp [setAt, flipAt, hne, ha]
        · simp [setAt, flipAt, hj, hj']
    rw [e2, center_flip_beside_black (setAt x t true) t (by simp [setAt]), e1]

/-- The restriction that fixes only the cell `u`, to black. -/
def blackAt (u : Int) : Int → Option Bool := fun j => if j = u then some true else none

theorem fillRow_blackAt (u : Int) (x : Int → Bool) : fillRow (blackAt u) x = setAt x u true := by
  funext j
  by_cases hj : j = u <;> simp [fillRow, blackAt, setAt, hj]

/-- **One query for the corner pair.** A tree that computes the center with cell `t - 1` held white gives a tree for
the center one query deeper: read cell `t - 1`; on white run the tree, on black run it with cell `t` fixed to black. -/
theorem corner_tree_lift (t : Nat) (ht : 1 ≤ t) (T' : QTree)
    (hT' : ∀ x, T'.eval x = evo (setAt x ((t : Int) - 1) false) t 0) :
    ∃ T : QTree, (∀ x, T.eval x = evo x t 0) ∧ T.depth ≤ T'.depth + 1 := by
  have hne : ((t : Int) - 1) ≠ (t : Int) := by omega
  refine ⟨.query ((t : Int) - 1) T' (T'.restrict (blackAt t)), fun x => ?_, ?_⟩
  · rw [center_corner_or x t ht]
    simp only [eval]
    cases ha : x ((t : Int) - 1) with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, hT', Bool.false_or]
      congr 1
      funext j
      by_cases hj : j = (t : Int)
      · subst hj; simp [setAt, hne.symm]
      · simp [setAt, hj]
    | true =>
      simp only [↓reduceIte, eval_restrict, fillRow_blackAt, hT', Bool.true_or]
      congr 1
      funext j
      by_cases hj : j = (t : Int)
      · subst hj; simp [setAt, hne.symm]
      · by_cases hj' : j = (t : Int) - 1
        · subst hj'; simp [setAt, hne]
        · simp [setAt, hj, hj']
  · simp only [depth]
    have := depth_restrict_le T' (blackAt t)
    omega

end Rule30Open
