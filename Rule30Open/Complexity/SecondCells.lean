module

public import Rule30Open.Complexity.CornerOr

/-!
# The second cell of each side of the cone

Write `c_t(x) = evo x t 0` for the center after `t` steps from a row `x`, a Boolean function of the `2t + 1` cells
`-t .. t`. [CornerOr](CornerOr.md) reduces the question whether every decision tree for `c_t` reads all `2t + 1` cells
to the same question for `G_t`, the center with the cells `-t` and `t - 1` white. This module proves two facts about
the next cell on each side.

* Left: `center_flip_second`. Flipping cell `-t + 1` changes the center by `diagPar x (-t + 1) t`, the xor over
  `s < t` of the negated cells `(s, -t + 2 + s)`: the diagonal two cells inside the left edge of the cone. The general
  form `flip_second_cell` follows the two cells of the difference at the left edge of the cone; the kit proves its
  one-step form (`AlgebraicDegree.deriv_evol_diag_succ`, in the Mathlib-based equivalents). Every cell of that diagonal
  flips with cell `-t + 2` (`front_xor`), so the derivative flips with cell `-t + 2` on every row for odd `t` and does
  not depend on it for even `t` (`diagPar_flip`, `second_derivative_flip`).
* Right: `center_step_corner`. After one step the center is the center of the next row, which sees its own corner
  pair through an OR (`center_corner_or` at `t - 1`). With cell `t - 1` white, that OR is
  `(x (t - 3) xor x (t - 2)) || (x (t - 2) xor x t)`. So `center_second_shield`: cell `t` does not matter when
  `x (t - 3) ≠ x (t - 2)`, and `center_second_and`: with cell `t - 3` black the center sees the cells `t - 2` and `t`
  only through their AND. The theorems are stated for `t = n + 2`.

These are statements about an arbitrary input row, for the query model of `CornerOr.md`. They say nothing about the
single black cell's column, where a tree reads nothing.

The natural-language argument is `SecondCells.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

/-- One step first: `s + 1` steps from `x` are `s` steps from the next row. -/
theorem evo_succ_left (x : Int → Bool) : ∀ s : Nat, evo x (s + 1) = evo (coneStep x) s
  | 0 => rfl
  | s + 1 => by
    show coneStep (evo x (s + 1)) = coneStep (evo (coneStep x) s)
    rw [evo_succ_left x s]

theorem coneStep_apply (x : Int → Bool) (i : Int) : coneStep x i = xor (x (i - 1)) (x i || x (i + 1)) := rfl

theorem flipAt_of_ne (x : Int → Bool) {a i : Int} (h : i ≠ a) : flipAt x a i = x i := by
  simp [flipAt, h]

theorem setAt_of_ne (x : Int → Bool) (v : Bool) {a i : Int} (h : i ≠ a) : setAt x a v i = x i := by
  simp [setAt, h]

theorem setAt_same (x : Int → Bool) (a : Int) (v : Bool) : setAt x a v a = v := by
  simp [setAt]

/-- The xor over `r < s` of the negated cells `(r, a + 1 + r)`, the diagonal two cells right of the left edge of the
difference that a flip of cell `a` starts. -/
def diagPar (x : Int → Bool) (a : Int) : Nat → Bool
  | 0 => false
  | s + 1 => xor (diagPar x a s) (!evo x s (a + 1 + s))

/-- **A flip of cell `a`, one cell left of its front.** After `s` steps the cell `a - 1 + s` of the flipped row
differs from that of `x` by `diagPar x a s`. -/
theorem flip_second_cell (x : Int → Bool) (a : Int) : ∀ s : Nat,
    evo (flipAt x a) s (a - 1 + s) = xor (evo x s (a - 1 + s)) (diagPar x a s)
  | 0 => by
    have e : a - 1 + ((0 : Nat) : Int) = a - 1 := by omega
    show flipAt x a (a - 1 + ((0 : Nat) : Int)) = xor (x (a - 1 + ((0 : Nat) : Int))) false
    rw [e, flipAt_of_ne x (by omega), Bool.xor_false]
  | s + 1 => by
    have ih := flip_second_cell x a s
    have hf := front_xor x (flipAt x a) a (fun i hi => (flipAt_of_ne x (by omega)).symm) s
    have hr : evo (flipAt x a) s (a + s + 1) = evo x s (a + s + 1) :=
      evo_local _ _ s _ (fun i h1 _ => flipAt_of_ne x (by omega))
    have e1 : a - 1 + ((s + 1 : Nat) : Int) - 1 = a - 1 + s := by push_cast; omega
    have e2 : a - 1 + ((s + 1 : Nat) : Int) = a + s := by push_cast; omega
    have e3 : a + s + 1 = a + 1 + (s : Int) := by omega
    have hfa : flipAt x a a = !x a := by simp [flipAt]
    show coneStep (evo (flipAt x a) s) (a - 1 + ((s + 1 : Nat) : Int)) =
      xor (coneStep (evo x s) (a - 1 + ((s + 1 : Nat) : Int))) (xor (diagPar x a s) (!evo x s (a + 1 + s)))
    rw [coneStep_apply, coneStep_apply, e1, e2, ih, hf, hr, hfa, e3]
    generalize evo x s (a - 1 + s) = p
    generalize diagPar x a s = d
    generalize evo x s (a + s) = b
    generalize evo x s (a + 1 + s) = e
    generalize x a = c
    revert p d b e c
    decide

/-- **The derivative along the second cell.** Flipping cell `-t + 1` changes the center after `t` steps by
`diagPar x (-t + 1) t`, the xor over `s < t` of the negated cells `(s, -t + 2 + s)`. -/
theorem center_flip_second (x : Int → Bool) (t : Nat) :
    evo (flipAt x (-(t : Int) + 1)) t 0 = xor (evo x t 0) (diagPar x (-(t : Int) + 1) t) := by
  have h := flip_second_cell x (-(t : Int) + 1) t
  have e : -(t : Int) + 1 - 1 + (t : Int) = 0 := by omega
  rw [e] at h
  exact h

theorem odd_succ (s : Nat) : decide ((s + 1) % 2 = 1) = !decide (s % 2 = 1) := by
  rcases Nat.mod_two_eq_zero_or_one s with h | h
  · have h' : (s + 1) % 2 = 1 := by omega
    simp [h, h']
  · have h' : (s + 1) % 2 = 0 := by omega
    simp [h, h']

/-- Every cell of the diagonal flips with cell `a + 1`, so the parity of `s` of them flips when `s` is odd. -/
theorem diagPar_flip (x : Int → Bool) (a : Int) : ∀ s : Nat,
    diagPar (flipAt x (a + 1)) a s = xor (diagPar x a s) (decide (s % 2 = 1))
  | 0 => by simp [diagPar]
  | s + 1 => by
    have ih := diagPar_flip x a s
    have hf := front_xor x (flipAt x (a + 1)) (a + 1) (fun i hi => (flipAt_of_ne x (by omega)).symm) s
    have hfa : flipAt x (a + 1) (a + 1) = !x (a + 1) := by simp [flipAt]
    show xor (diagPar (flipAt x (a + 1)) a s) (!evo (flipAt x (a + 1)) s (a + 1 + s)) =
      xor (xor (diagPar x a s) (!evo x s (a + 1 + s))) (decide ((s + 1) % 2 = 1))
    rw [ih, hf, hfa, odd_succ]
    generalize diagPar x a s = d
    generalize evo x s (a + 1 + s) = b
    generalize x (a + 1) = c
    generalize decide (s % 2 = 1) = o
    revert d b c o
    decide

/-- **The derivative along the second cell flips with the third exactly for odd `t`.** Write
`D x = c_t (x flipped at -t + 1) xor c_t x`. Flipping cell `-t + 2` changes `D` by `t mod 2`. -/
theorem second_derivative_flip (x : Int → Bool) (t : Nat) :
    xor (evo (flipAt (flipAt x (-(t : Int) + 2)) (-(t : Int) + 1)) t 0) (evo (flipAt x (-(t : Int) + 2)) t 0) =
      xor (xor (evo (flipAt x (-(t : Int) + 1)) t 0) (evo x t 0)) (decide (t % 2 = 1)) := by
  rw [center_flip_second, center_flip_second]
  have e : -(t : Int) + 2 = -(t : Int) + 1 + 1 := by omega
  rw [e, diagPar_flip]
  generalize evo (flipAt x (-(t : Int) + 1 + 1)) t 0 = p
  generalize evo x t 0 = q
  generalize diagPar x (-(t : Int) + 1) t = d
  generalize decide (t % 2 = 1) = o
  revert p q d o
  decide

/-- Rows that agree on the cells up to `m + 1` have the same next row on the cells up to `m`. -/
theorem coneStep_agree {x y : Int → Bool} {m : Int} (h : ∀ j : Int, j ≤ m + 1 → y j = x j) :
    ∀ i : Int, i ≤ m → coneStep y i = coneStep x i := by
  intro i hi
  rw [coneStep_apply, coneStep_apply, h (i - 1) (by omega), h i (by omega), h (i + 1) (by omega)]

/-- **One step, then the next corner.** For `t = n + 2` the center equals the center after `n + 1` steps of the next
row with its cell `n` white and its cell `n + 1` set to the OR of the two. -/
theorem center_step_corner (x : Int → Bool) (n : Nat) :
    evo x (n + 2) 0 = evo (setAt (setAt (coneStep x) (n : Int) false) ((n : Int) + 1)
      (coneStep x (n : Int) || coneStep x ((n : Int) + 1))) (n + 1) 0 := by
  show evo x (n + 1 + 1) 0 = _
  rw [evo_succ_left x (n + 1), center_corner_or (coneStep x) (n + 1) (by omega)]
  have e1 : ((n + 1 : Nat) : Int) - 1 = (n : Int) := by push_cast; omega
  have e2 : ((n + 1 : Nat) : Int) = (n : Int) + 1 := by push_cast; rfl
  rw [e1, e2]

/-- Two rows with the same OR at the next corner and the same next row left of it have the same center. -/
theorem center_of_step_agree (x y : Int → Bool) (n : Nat)
    (hor : (coneStep x (n : Int) || coneStep x ((n : Int) + 1)) = (coneStep y (n : Int) || coneStep y ((n : Int) + 1)))
    (hl : ∀ i : Int, i < (n : Int) → coneStep x i = coneStep y i) :
    evo x (n + 2) 0 = evo y (n + 2) 0 := by
  rw [center_step_corner, center_step_corner]
  apply evo_local
  intro i _ hi
  by_cases hi1 : i = (n : Int) + 1
  · rw [hi1, setAt_same, setAt_same, hor]
  · by_cases hi0 : i = (n : Int)
    · have hne : (n : Int) ≠ (n : Int) + 1 := by omega
      rw [hi0, setAt_of_ne _ _ hne, setAt_of_ne _ _ hne, setAt_same, setAt_same]
    · rw [setAt_of_ne _ _ hi1, setAt_of_ne _ _ hi1, setAt_of_ne _ _ hi0, setAt_of_ne _ _ hi0]
      exact hl i (by push_cast at hi; omega)

/-- **The second shield.** For `t = n + 2`, if cell `t - 1` is white and the cells `t - 3`, `t - 2` differ, flipping
cell `t` does not change the center. -/
theorem center_second_shield (x : Int → Bool) (n : Nat) (h1 : x ((n : Int) + 1) = false)
    (h3 : x ((n : Int) - 1) ≠ x (n : Int)) :
    evo (flipAt x ((n : Int) + 2)) (n + 2) 0 = evo x (n + 2) 0 := by
  have hy : ∀ j : Int, j ≤ (n : Int) + 1 → flipAt x ((n : Int) + 2) j = x j :=
    fun j hj => flipAt_of_ne x (by omega)
  have hagree := coneStep_agree (m := (n : Int)) hy
  have hb : coneStep x (n : Int) = true := by
    rw [coneStep_apply, h1]
    revert h3
    cases x ((n : Int) - 1) <;> cases x (n : Int) <;> decide
  apply center_of_step_agree
  · rw [hagree (n : Int) (Int.le_refl _), hb, Bool.true_or, Bool.true_or]
  · intro i hi
    exact hagree i (by omega)

/-- **The second corner is an AND.** For `t = n + 2`, if cell `t - 1` is white and cell `t - 3` is black, the center
sees the cells `t - 2` and `t` only through their AND: it equals the center of the row with cell `t - 2` set to that
AND and cell `t` black. -/
theorem center_second_and (x : Int → Bool) (n : Nat) (h1 : x ((n : Int) + 1) = false)
    (h3 : x ((n : Int) - 1) = true) :
    evo x (n + 2) 0 =
      evo (setAt (setAt x (n : Int) (x (n : Int) && x ((n : Int) + 2))) ((n : Int) + 2) true) (n + 2) 0 := by
  generalize hv : (x (n : Int) && x ((n : Int) + 2)) = v
  have hY : ∀ j : Int, j ≠ (n : Int) → j ≠ (n : Int) + 2 →
      setAt (setAt x (n : Int) v) ((n : Int) + 2) true j = x j :=
    fun j h0 h2 => by rw [setAt_of_ne _ _ h2, setAt_of_ne _ _ h0]
  have hYn : setAt (setAt x (n : Int) v) ((n : Int) + 2) true (n : Int) = v := by
    rw [setAt_of_ne _ _ (by omega), setAt_same]
  have hY2 : setAt (setAt x (n : Int) v) ((n : Int) + 2) true ((n : Int) + 2) = true := setAt_same _ _ _
  apply center_of_step_agree
  · have e1 : (n : Int) + 1 - 1 = (n : Int) := by omega
    have e2 : (n : Int) + 1 + 1 = (n : Int) + 2 := by omega
    rw [coneStep_apply, coneStep_apply, coneStep_apply (setAt _ _ _), coneStep_apply (setAt _ _ _), e1, e2,
      hY ((n : Int) - 1) (by omega) (by omega), hY ((n : Int) + 1) (by omega) (by omega), hYn, hY2, h1, h3, ← hv]
    generalize x (n : Int) = p
    generalize x ((n : Int) + 2) = q
    revert p q
    decide
  · intro i hi
    by_cases hi1 : i = (n : Int) - 1
    · rw [hi1, coneStep_apply, coneStep_apply, show (n : Int) - 1 + 1 = (n : Int) by omega,
        hY ((n : Int) - 1) (by omega) (by omega), hY ((n : Int) - 1 - 1) (by omega) (by omega), h3,
        Bool.true_or, Bool.true_or]
    · exact (coneStep_agree (m := (n : Int) - 2)
        (fun j hj => hY j (by omega) (by omega)) i (by omega)).symm

end Rule30Open
