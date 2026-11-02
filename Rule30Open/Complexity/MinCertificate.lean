module

public import Rule30Open.Complexity.QueryDepth

/-!
# The fewest cells that fix the center: every such set holds `x_{-t}`, and `t - 1` cells suffice for `t ≥ 9`

A subcube of rows is a partial row `ρ : Int → Option Bool` (QueryDepth's restrictions): the rows `fillRow ρ x`, which
agree with `ρ` on the cells it fixes. The center after `t` steps is constant on it (`CenterConstOn ρ t`) when every
two such rows give the same center.

* `constOn_fixes_left`: every subcube on which the center after `t` steps is constant fixes the cell `-t`, since the
  center flips with that cell on every row (`center_flip_setAt`).
* `screening_even_free`: if `x (-j) = (j even)` for `2 ≤ j ≤ t` and `t ≥ 9`, the center after `t` steps is black,
  whatever `x (-1)` and the right half are. ConeScreening's `screening_even` has this with `x (-1)` white too; the
  case `x (-1)` black runs the same pair argument from the base times 9 and 10, checked over every right half by
  `decide` on rows encoded as natural numbers.
* `stripe_center` and `stripe_constOn`: for `t ≥ 9`, the `t - 1` cells `-t .. -2`, with `x (-j) = (j even)` for
  `2 ≤ j ≤ t - 1` and `x (-t)` either color, fix the center: it is black exactly when `x (-t) = (t even)`. The partial
  row `stripeRow t v` fixes exactly the cells `-t .. -2` (`stripeRow_isSome`).

So the least number of fixed cells of a subcube on which the center is constant is at most `t - 1` for `t ≥ 9`; it
is exactly `t - 1` for `9 ≤ t ≤ 15` by computation (`computations/min_certificate.py`), which is not proved here.

The natural-language argument is `MinCertificate.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

/-- The center after `t` steps is constant on the subcube of the rows that agree with `ρ` on its fixed cells. -/
def CenterConstOn (ρ : Int → Option Bool) (t : Nat) : Prop :=
  ∀ x y : Int → Bool, evo (fillRow ρ x) t 0 = evo (fillRow ρ y) t 0

/-- Setting a free cell commutes with filling in the fixed cells. -/
theorem fillRow_setAt_none (ρ : Int → Option Bool) (u : Int) (hu : ρ u = none) (x : Int → Bool) (v : Bool) :
    fillRow ρ (setAt x u v) = setAt (fillRow ρ x) u v := by
  funext j
  by_cases hj : j = u
  · subst hj; simp [fillRow, setAt, hu]
  · simp only [fillRow, setAt, hj, ite_false]

/-- **Every constant subcube fixes the leftmost cone cell.** -/
theorem constOn_fixes_left (ρ : Int → Option Bool) (t : Nat) (h : CenterConstOn ρ t) : ρ (-t) ≠ none := by
  intro hnone
  let x : Int → Bool := fun _ => false
  have e := h (setAt x (-t) true) (setAt x (-t) false)
  rw [fillRow_setAt_none ρ _ hnone, fillRow_setAt_none ρ _ hnone] at e
  exact center_flip_setAt (fillRow ρ x) t e

/-! ## The even pattern with `x (-1)` black -/

/-- The even pattern with cell `-1` black as well. -/
def evenOne (j : Int) : Bool := even j || decide (j = 1)

def oneCheck9 (r : Nat) : Bool := (nevo (426 + 512 * r) 9).testBit 0
def oneCheck10 (r : Nat) : Bool := (nevo (853 + 1024 * r) 10).testBit 0

theorem ebase9_one_all : allIn oneCheck9 0 10 = true := by decide
theorem ebase10_one_all : allIn oneCheck10 0 11 = true := by decide

theorem ebase9_one (x : Int → Bool) (h : ∀ j : Int, 1 ≤ j → j ≤ 9 → x (-j) = evenOne j) : evo x 9 0 = true :=
  base_of_check evenOne true 9 426 (by decide)
    (fun r hr => allIn_spec oneCheck9 10 0 ebase9_one_all r (by omega) (by simpa using hr)) x (by simpa using h)

theorem ebase10_one (x : Int → Bool) (h : ∀ j : Int, 1 ≤ j → j ≤ 10 → x (-j) = evenOne j) : evo x 10 0 = true :=
  base_of_check evenOne true 10 853 (by decide)
    (fun r hr => allIn_spec oneCheck10 11 0 ebase10_one_all r (by omega) (by simpa using hr)) x (by simpa using h)

theorem evenOne_of_black (x : Int → Bool) (t : Nat) (h : ∀ j : Int, 2 ≤ j → j ≤ t → x (-j) = even j)
    (h1 : x (-1) = true) : ∀ j : Int, 1 ≤ j → j ≤ t → x (-j) = evenOne j := by
  intro j a b
  by_cases hj : j = 1
  · subst hj; simp [evenOne, h1]
  · simp only [evenOne, hj, decide_false, Bool.or_false]; exact h j (by omega) b

theorem even_of_white (x : Int → Bool) (t : Nat) (h : ∀ j : Int, 2 ≤ j → j ≤ t → x (-j) = even j)
    (h1 : x (-1) = false) : ∀ j : Int, 1 ≤ j → j ≤ t → x (-j) = even j := by
  intro j a b
  by_cases hj : j = 1
  · subst hj; simp [even, h1]
  · exact h j (by omega) b

/-- The base times 9 and 10, for either color of `x (-1)`. -/
theorem stripe_base_free (x : Int → Bool) (t : Nat) (ht : t = 9 ∨ t = 10)
    (h : ∀ j : Int, 2 ≤ j → j ≤ t → x (-j) = even j) : evo x t 0 = true := by
  cases h1 : x (-1)
  · exact screening_even x t (by omega) (even_of_white x t h h1)
  · rcases ht with rfl | rfl
    · exact ebase9_one x (evenOne_of_black x 9 h h1)
    · exact ebase10_one x (evenOne_of_black x 10 h h1)

/-- **Screening with `x (-1)` free.** If `x (-j) = (j even)` for `2 ≤ j ≤ t` and `t ≥ 9`, the center after `t`
steps is black, whatever the cells `-1 .. t` are. -/
theorem screening_even_free (x : Int → Bool) (t : Nat) (ht : 9 ≤ t)
    (h : ∀ j : Int, 2 ≤ j → j ≤ t → x (-j) = even j) : evo x t 0 = true := by
  by_cases h9 : t = 9
  · exact stripe_base_free x t (Or.inl h9) h
  by_cases h10 : t = 10
  · exact stripe_base_free x t (Or.inr h10) h
  have c9 := stripe_base_free x 9 (Or.inl rfl) (fun j h1 h2 => h j h1 (by omega))
  have c10 := stripe_base_free x 10 (Or.inr rfl) (fun j h1 h2 => h j h1 (by omega))
  -- The translated row has the odd pattern on `-1 .. -(t - 1)`.
  let y : Int → Bool := fun i => x (i - 1)
  have hy : ∀ j : Int, 1 ≤ j → j ≤ (t - 1 : Nat) → y (-j) = odd j := by
    intro j h1 h2
    simp only [y]
    rw [show -j - 1 = -(j + 1) by omega, h (j + 1) (by omega) (by omega)]
    simp only [even, odd]
    rcases (show j % 2 = 0 ∨ j % 2 = 1 by omega) with hm | hm
    · have : (j + 1) % 2 = 1 := by omega
      simp [hm, this]
    · have : (j + 1) % 2 = 0 := by omega
      simp [hm, this]
  have hb : ∀ s : Nat, evo x s 0 = evo y s 1 := by
    intro s; rw [evo_shift]; rfl
  have b9 : evo y 9 1 = true := by rw [← hb]; exact c9
  have b10 : evo y 10 1 = true := by rw [← hb]; exact c10
  have W := wall_black y (t - 1) hy
  have key : ∀ s : Nat, 8 ≤ s → s ≤ t - 1 → ¬ (evo y s 0 = false ∧ evo y s 1 = false) := by
    intro s
    induction s using Nat.strongRecOn with
    | _ s ih =>
      intro hs1 hs2 hp
      by_cases e8 : s = 8
      · subst e8
        have a9 := pair_a y 8 (W 8 (by omega))
        have bb9 := pair_b y 8
        have bb10 := pair_b y 9
        rw [hp.1, hp.2] at a9 bb9
        rw [b9] at bb9 bb10
        rw [b10] at bb10
        revert a9 bb9 bb10
        cases evo y 9 0 <;> cases evo y 8 2 <;> cases evo y 9 2 <;> simp
      by_cases e9 : s = 9
      · subst e9; rw [b9] at hp; simp at hp
      by_cases e10 : s = 10
      · subst e10; rw [b10] at hp; simp at hp
      obtain ⟨u, rfl⟩ : ∃ u, s = u + 2 := ⟨s - 2, by omega⟩
      have := pair_back y u (W u (by omega)) (W (u + 1) (by omega)) hp.1 hp.2
      exact ih u (by omega) (by omega) (by omega) this
  obtain ⟨u, rfl⟩ : ∃ u, t = u + 2 := ⟨t - 2, by omega⟩
  rw [hb, pair_b y (u + 1), pair_a y u (W u (by omega))]
  have k0 := key u (by omega) (by omega)
  have k1 := key (u + 1) (by omega) (by omega)
  rw [pair_a y u (W u (by omega))] at k1
  revert k0 k1
  cases evo y u 0 <;> cases evo y u 1 <;> cases evo y (u + 1) 1 <;> cases evo y (u + 1) 2 <;> simp

/-! ## The stripe subcube -/

/-- **The stripe fixes the center.** For `t ≥ 9`, if `x (-j) = (j even)` for `2 ≤ j ≤ t - 1`, the center after `t`
steps is black exactly when `x (-t) = (t even)`, whatever the cells `-1 .. t` are. -/
theorem stripe_center (x : Int → Bool) (t : Nat) (ht : 9 ≤ t)
    (h : ∀ j : Int, 2 ≤ j → j ≤ (t : Int) - 1 → x (-j) = even j) :
    evo x t 0 = !(xor (x (-t)) (even t)) := by
  let x' := setAt x (-t) (even t)
  have h' : ∀ j : Int, 2 ≤ j → j ≤ t → x' (-j) = even j := by
    intro j a b
    by_cases hj : j = t
    · subst hj; simp [x', setAt]
    · have : -j ≠ -(t : Int) := by omega
      simp only [x', setAt, this, ite_false]
      exact h j a (by omega)
  have c' := screening_even_free x' t ht h'
  rw [center_decomp x' t] at c'
  rw [center_decomp x t]
  have e : setAt x' (-t) false = setAt x (-t) false := setAt_setAt x (-t) (even t) false
  rw [e] at c'
  have hx' : x' (-t) = even t := by simp [x', setAt]
  rw [hx'] at c'
  revert c'
  cases x (-t) <;> cases even t <;> cases evo (setAt x (-t) false) t 0 <;> simp

/-- The stripe subcube: cell `-t` fixed to `v`, cells `-(t - 1) .. -2` fixed to the even pattern, the rest free. -/
def stripeRow (t : Nat) (v : Bool) : Int → Option Bool := fun i =>
  if i = -(t : Int) then some v else if -(t : Int) < i ∧ i ≤ -2 then some (even (-i)) else none

/-- The stripe subcube fixes exactly the `t - 1` cells `-t .. -2` (for `t ≥ 2`). -/
theorem stripeRow_isSome (t : Nat) (ht : 2 ≤ t) (v : Bool) (i : Int) :
    (stripeRow t v i).isSome = true ↔ -(t : Int) ≤ i ∧ i ≤ -2 := by
  simp only [stripeRow]
  by_cases h1 : i = -(t : Int)
  · simp [h1]; omega
  · by_cases h2 : -(t : Int) < i ∧ i ≤ -2
    · simp [h1, h2]; omega
    · simp [h1, h2]; omega

/-- **`t - 1` fixed cells make the center constant, for every `t ≥ 9`.** -/
theorem stripe_constOn (t : Nat) (ht : 9 ≤ t) (v : Bool) : CenterConstOn (stripeRow t v) t := by
  have key : ∀ x : Int → Bool, evo (fillRow (stripeRow t v) x) t 0 = !(xor v (even t)) := by
    intro x
    have hfill : ∀ j : Int, 2 ≤ j → j ≤ (t : Int) - 1 → fillRow (stripeRow t v) x (-j) = even j := by
      intro j a b
      have n1 : -j ≠ -(t : Int) := by omega
      have n2 : -(t : Int) < -j ∧ -j ≤ -2 := by omega
      simp [fillRow, stripeRow, n1, n2]
    rw [stripe_center _ t ht hfill]
    simp [fillRow, stripeRow]
  intro x y
  rw [key x, key y]

end Rule30Open
