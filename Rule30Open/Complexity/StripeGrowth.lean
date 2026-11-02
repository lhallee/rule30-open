module

public import Rule30Open.Complexity.MinCertificate

/-!
# The stripe grows by two cells every nine steps, so `t - 2k` cells fix the center for `t ≥ 9(k + 1)`

ConeScreening's `screening_odd`: if `x (-j) = (j odd)` for `1 ≤ j ≤ t` (the odd stripe, black wall at `-1`) and
`t ≥ 9`, the cell `0` after `t` steps is white, whatever the cells `0, 1, ...` are. This module iterates it.

* `stripe_grow`: if the odd stripe covers `-1 .. -L` with `L ≥ 10`, then after nine steps it covers
  `-(L - 9) .. 1`: the old stripe has lost nine cells on the left, and the cells `0, 1` have become white and black,
  whatever lies right of the wall. Translated by two cells, the row after nine steps carries the odd stripe again,
  with `L - 7` cells (`stripe_grow_shift`).
* `stripe_far`: if the odd stripe covers `-1 .. -(t - 2k)` and `t ≥ 9(k + 1)`, the cell `2k` after `t` steps is
  white, for every row. Induction on `k`, one growth step at a time.
* `far_stripe_center`, `farStripe_constOn`: for the center, the stripe `x (-i) = (i odd)` on the `t - 2k` cells
  `-t .. -(2k + 1)`, every other cell free, makes the center after `t` steps constant whenever `t ≥ 9(k + 1)`: it is
  white when `x (-t) = (t odd)` and black otherwise (MinCertificate's partial rows, `farStripeRow_isSome`).

So the least number of fixed cells of a subcube on which the center is constant satisfies `m(t) ≤ t - 2k` for
`t ≥ 9(k + 1)`, that is `m(t) ≤ t - 2⌊t/9⌋ + 2` for `t ≥ 9`. In particular `m(t) ≤ t - 2` for `t ≥ 18`, which refutes
`m(t) = t - 1` for every `t ≥ 18`, and `m(t) / t ≤ 7/9 + o(1)`.

The natural-language argument is `StripeGrowth.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

/-- `s` steps after `a` steps are `a + s` steps. -/
theorem evo_add (x : Int → Bool) (a : Nat) : ∀ s : Nat, evo (evo x a) s = evo x (a + s)
  | 0 => rfl
  | s + 1 => by
    show coneStep (evo (evo x a) s) = coneStep (evo x (a + s))
    rw [evo_add x a s]

/-- Evolution commutes with translation by `d` cells. -/
theorem evo_translate (x : Int → Bool) (d : Int) : ∀ (s : Nat) (j : Int),
    evo (fun i => x (i + d)) s j = evo x s (j + d)
  | 0, _ => rfl
  | s + 1, j => by
    show coneStep (evo (fun i => x (i + d)) s) j = coneStep (evo x s) (j + d)
    simp only [coneStep]
    rw [evo_translate x d s (j - 1), evo_translate x d s j, evo_translate x d s (j + 1),
      show j - 1 + d = j + d - 1 by omega, show j + 1 + d = j + d + 1 by omega]

theorem odd_sub_two (j : Int) : odd (j - 2) = odd j := by
  simp only [odd]
  have : (j - 2) % 2 = j % 2 := by omega
  rw [this]

/-- **The stripe grows.** If the odd stripe covers `-1 .. -L` with `L ≥ 10`, then nine steps later the cells
`-1 .. -(L - 9)` still alternate, cell `0` is white and cell `1` is black, whatever the cells `0, 1, ...` were. -/
theorem stripe_grow (y : Int → Bool) (L : Nat) (hL : 10 ≤ L)
    (h : ∀ j : Int, 1 ≤ j → j ≤ L → y (-j) = odd j) :
    (∀ j : Int, 1 ≤ j → j ≤ (L - 9 : Nat) → evo y 9 (-j) = odd j) ∧ evo y 9 0 = false ∧ evo y 9 1 = true := by
  have hs : ∀ j : Int, 1 ≤ j → j ≤ (L - 9 : Nat) → evo y 9 (-j) = odd j := stripe y L h 9 (by omega)
  have a9 : evo y 9 0 = false := screening_odd y 9 (by omega) (fun j h1 h2 => h j h1 (by omega))
  have a10 : evo y 10 0 = false := screening_odd y 10 (by omega) (fun j h1 h2 => h j h1 (by omega))
  have w : evo y 9 (-1) = true := by simpa [odd] using hs 1 (by omega) (by omega)
  refine ⟨hs, a9, ?_⟩
  have e : evo y 10 0 = xor (evo y 9 (0 - 1)) (evo y 9 0 || evo y 9 (0 + 1)) := rfl
  rw [show (0 : Int) - 1 = -1 by rfl, show (0 : Int) + 1 = 1 by rfl, w, a9, a10] at e
  revert e
  cases evo y 9 1 <;> simp

/-- The row nine steps later, translated by two cells, carries the odd stripe with `L - 7` cells. -/
theorem stripe_grow_shift (y : Int → Bool) (L : Nat) (hL : 10 ≤ L)
    (h : ∀ j : Int, 1 ≤ j → j ≤ L → y (-j) = odd j) :
    ∀ j : Int, 1 ≤ j → j ≤ (L - 7 : Nat) → evo y 9 (-j + 2) = odd j := by
  obtain ⟨hs, a0, a1⟩ := stripe_grow y L hL h
  intro j h1 h2
  by_cases j1 : j = 1
  · subst j1; simpa [odd] using a1
  by_cases j2 : j = 2
  · subst j2; simpa [odd] using a0
  have e : -j + 2 = -(j - 2) := by omega
  rw [e, hs (j - 2) (by omega) (by omega), odd_sub_two]

/-- **The far cell.** If the odd stripe covers `-1 .. -(t - 2k)` and `t ≥ 9(k + 1)`, then the cell `2k` after `t`
steps is white, whatever the cells `0, 1, ...` are. -/
theorem stripe_far : ∀ (k : Nat) (y : Int → Bool) (t : Nat), 9 * (k + 1) ≤ t →
    (∀ j : Int, 1 ≤ j → j ≤ (t - 2 * k : Nat) → y (-j) = odd j) → evo y t (2 * (k : Int)) = false
  | 0, y, t, ht, h => by
    simpa using screening_odd y t (by omega) (fun j h1 h2 => h j h1 (by omega))
  | k + 1, y, t, ht, h => by
    have hz := stripe_grow_shift y (t - 2 * (k + 1)) (by omega) h
    have ih := stripe_far k (fun i => evo y 9 (i + 2)) (t - 9) (by omega)
      (fun j h1 h2 => by
        show evo y 9 (-j + 2) = odd j
        exact hz j h1 (by omega))
    rw [evo_translate (evo y 9) 2 (t - 9) (2 * (k : Int)), evo_add] at ih
    have e1 : 9 + (t - 9) = t := by omega
    have e2 : 2 * (k : Int) + 2 = 2 * ((k + 1 : Nat) : Int) := by push_cast; omega
    rw [e1, e2] at ih
    exact ih

/-- **The center, with the stripe ending `2k + 1` cells left of it.** If `x (-i) = (i odd)` for
`2k + 1 ≤ i ≤ t - 1` and `t ≥ 9(k + 1)`, the center after `t` steps is black exactly when `x (-t) ≠ (t odd)`,
whatever the cells `-2k .. t` are. -/
theorem far_stripe_center (x : Int → Bool) (k t : Nat) (ht : 9 * (k + 1) ≤ t)
    (h : ∀ i : Int, 2 * (k : Int) + 1 ≤ i → i ≤ (t : Int) - 1 → x (-i) = odd i) :
    evo x t 0 = xor (x (-t)) (odd t) := by
  let x' := setAt x (-t) (odd t)
  have h' : ∀ j : Int, 1 ≤ j → j ≤ (t - 2 * k : Nat) → (fun i => x' (i + -(2 * (k : Int)))) (-j) = odd j := by
    intro j h1 h2
    show x' (-j + -(2 * (k : Int))) = odd j
    have e : -j + -(2 * (k : Int)) = -(j + 2 * (k : Int)) := by omega
    have hp : odd (j + 2 * (k : Int)) = odd j := by
      simp only [odd]
      have : (j + 2 * (k : Int)) % 2 = j % 2 := by omega
      rw [this]
    rw [e, ← hp]
    by_cases hj : j + 2 * (k : Int) = t
    · rw [hj]
      simp [x', setAt]
    · have hne : -(j + 2 * (k : Int)) ≠ -(t : Int) := by omega
      simp only [x', setAt, hne, ite_false]
      exact h (j + 2 * (k : Int)) (by omega) (by omega)
  have c' := stripe_far k (fun i => x' (i + -(2 * (k : Int)))) t ht h'
  have e0 : 2 * (k : Int) + -(2 * (k : Int)) = 0 := by omega
  rw [evo_translate x' (-(2 * (k : Int))) t (2 * (k : Int)), e0] at c'
  rw [center_decomp x' t] at c'
  rw [center_decomp x t]
  have e : setAt x' (-t) false = setAt x (-t) false := setAt_setAt x (-t) (odd t) false
  have hx' : x' (-t) = odd t := by simp [x', setAt]
  rw [e, hx'] at c'
  revert c'
  cases x (-t) <;> cases odd t <;> cases evo (setAt x (-t) false) t 0 <;> simp

/-- The far stripe: cell `-t` fixed to `v`, cells `-(t - 1) .. -(2k + 1)` fixed to the odd pattern, the rest free. -/
def farStripeRow (t k : Nat) (v : Bool) : Int → Option Bool := fun i =>
  if i = -(t : Int) then some v else if -(t : Int) < i ∧ i ≤ -(2 * (k : Int) + 1) then some (odd (-i)) else none

/-- The far stripe fixes exactly the `t - 2k` cells `-t .. -(2k + 1)` (for `2k + 1 ≤ t`). -/
theorem farStripeRow_isSome (t k : Nat) (ht : 2 * k + 1 ≤ t) (v : Bool) (i : Int) :
    (farStripeRow t k v i).isSome = true ↔ -(t : Int) ≤ i ∧ i ≤ -(2 * (k : Int) + 1) := by
  simp only [farStripeRow]
  by_cases h1 : i = -(t : Int)
  · simp [h1]; omega
  · by_cases h2 : -(t : Int) < i ∧ i ≤ -(2 * (k : Int) + 1)
    · simp [h1, h2]; omega
    · simp [h1, h2]; omega

/-- **`t - 2k` fixed cells make the center constant, for every `t ≥ 9(k + 1)`.** -/
theorem farStripe_constOn (t k : Nat) (ht : 9 * (k + 1) ≤ t) (v : Bool) : CenterConstOn (farStripeRow t k v) t := by
  have key : ∀ x : Int → Bool, evo (fillRow (farStripeRow t k v) x) t 0 = xor v (odd t) := by
    intro x
    have hfill : ∀ i : Int, 2 * (k : Int) + 1 ≤ i → i ≤ (t : Int) - 1 →
        fillRow (farStripeRow t k v) x (-i) = odd i := by
      intro i a b
      have n1 : -i ≠ -(t : Int) := by omega
      have n2 : -(t : Int) < -i ∧ -i ≤ -(2 * (k : Int) + 1) := by omega
      simp [fillRow, farStripeRow, n1, n2]
    rw [far_stripe_center _ k t ht hfill]
    simp [fillRow, farStripeRow]
  intro x y
  rw [key x, key y]

end Rule30Open
