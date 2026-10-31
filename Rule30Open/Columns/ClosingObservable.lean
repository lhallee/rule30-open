module

public import Ruliology.CellularAutomata.Rule30Jen

/-!
# A periodic column and a closing observable on its right

Let column `j` of the single-cell orbit be eventually periodic. Take the strip of cells
`j + 1, ..., j + w` and any observable `h` that, together with the strip, determines the one
quantity the strip's right edge reads from outside, `cell t (j + w) || cell t (j + w + 1)`. Then
`h` is not eventually periodic (`closing_observable`). The strip runs as a finite-state system
driven by the periodic column `j` and the periodic `h`, so pigeonhole makes it eventually periodic,
and then two adjacent columns are, against Jen's theorem.

Special cases:
* `h = column j + w + 1`: Jen's theorem for the pair `(j, j + w + 1)`;
* `w = 0`, `h = cell j || cell (j + 1)`: the kit's `orCol` form;
* `affine_observable`: `cell t k` plus any function of the cells strictly between `j` and `k`;
* `center_xor`: the center column and `column 1 xor column 2`;
* `center_masked_two`: the center column and `column 2` on the white times of column 1, as the
  sequence `!cell t 1 && cell t 2`;
* `center_parity`: the center column and the parity of columns `1, ..., k`, for every `k ≥ 1`.

The natural-language argument is `ClosingObservable.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

open Ruliology.CellularAutomata Rule30Jen

theorem strip_get {j k p : Int} (t : Nat) (h1 : j < p) (h2 : p < k) :
    (strip j k t).getD (p - j - 1).toNat false = cell t p := by
  simp only [strip, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range (show (p - j - 1).toNat < (k - j - 1).toNat by omega),
    Option.map_some, Option.getD_some]
  rw [show j + 1 + (((p - j - 1).toNat : Nat) : Int) = p by omega]

theorem strip_ext {j k : Int} {t₁ t₂ : Nat}
    (h : ∀ p, j < p → p < k → cell t₁ p = cell t₂ p) : strip j k t₁ = strip j k t₂ := by
  unfold strip
  apply List.map_congr_left
  intro r hr
  rw [List.mem_range] at hr
  exact h _ (by omega) (by omega)

/-- The strip `j + 1, ..., j + w` evolves from its state, column `j` and the observable `h`. -/
theorem closed_agree {j : Int} {w : Nat} {F : List Bool → Bool → Bool} {h : Nat → Bool}
    (hF : ∀ t, (cell t (j + w) || cell t (j + w + 1)) = F (strip j (j + w + 1) t) (h t))
    {t₁ t₂ : Nat} (hs : strip j (j + w + 1) t₁ = strip j (j + w + 1) t₂)
    (hb : ∀ r, cell (t₁ + r) j = cell (t₂ + r) j ∧ h (t₁ + r) = h (t₂ + r)) :
    ∀ r, ∀ p, j ≤ p → p ≤ j + w → cell (t₁ + r) p = cell (t₂ + r) p := by
  intro r
  induction r with
  | zero =>
    intro p hp1 hp2
    by_cases e : p = j
    · subst e; exact (hb 0).1
    · have := congrArg (fun l => l.getD (p - j - 1).toNat false) hs
      rw [strip_get t₁ (by omega) (by omega), strip_get t₂ (by omega) (by omega)] at this
      exact this
  | succ r ih =>
    intro p hp1 hp2
    by_cases e : p = j
    · subst e; exact (hb (r + 1)).1
    rw [show t₁ + (r + 1) = (t₁ + r) + 1 by omega, show t₂ + (r + 1) = (t₂ + r) + 1 by omega]
    show rule (cell (t₁ + r) (p - 1)) (cell (t₁ + r) p) (cell (t₁ + r) (p + 1)) =
      rule (cell (t₂ + r) (p - 1)) (cell (t₂ + r) p) (cell (t₂ + r) (p + 1))
    by_cases e2 : p = j + w
    · subst e2
      have hs' : strip j (j + w + 1) (t₁ + r) = strip j (j + w + 1) (t₂ + r) :=
        strip_ext fun q hq1 hq2 => ih q (by omega) (by omega)
      unfold rule
      rw [hF (t₁ + r), hF (t₂ + r), ih (j + w - 1) (by omega) (by omega), hs', (hb r).2]
    · rw [ih (p - 1) (by omega) (by omega), ih p (by omega) (by omega),
        ih (p + 1) (by omega) (by omega)]

/-- **Closing observable.** If column `j` is eventually periodic, no observable `h` that determines
`cell t (j + w) || cell t (j + w + 1)` from the strip `j + 1, ..., j + w` is eventually periodic. -/
theorem closing_observable (j : Int) (w : Nat) (F : List Bool → Bool → Bool) (h : Nat → Bool)
    (hF : ∀ t, (cell t (j + w) || cell t (j + w + 1)) = F (strip j (j + w + 1) t) (h t))
    (hj : EventuallyPeriodic fun t => cell t j) (hh : EventuallyPeriodic h) : False := by
  obtain ⟨T, P, hP, hpj, hph⟩ := common_period hj hh
  obtain ⟨m, n, hmn, -, he⟩ := pigeonhole (j + w + 1 - j - 1).toNat
    (fun m => strip j (j + w + 1) (T + m * P))
    (fun m => by simp only [strip, List.length_map, List.length_range])
  have hmP : m * P ≤ n * P := Nat.mul_le_mul_right _ (by omega)
  have hQ : 0 < (n - m) * P := Nat.mul_pos (by omega) hP
  have hshift : ∀ r, T + n * P + r = (T + m * P + r) + (n - m) * P := fun r => by
    rw [Nat.sub_mul]; omega
  have hb : ∀ r, cell (T + m * P + r) j = cell (T + n * P + r) j ∧
      h (T + m * P + r) = h (T + n * P + r) := fun r => by
    rw [hshift r]
    exact ⟨(periodic_mul (f := fun t => cell t j) hpj (n - m) _ (by omega)).symm,
      (periodic_mul (f := h) hph (n - m) _ (by omega)).symm⟩
  have key := closed_agree hF he hb
  -- every cell `j, ..., j + w` repeats with period `(n - m) * P` from `T + m * P`
  have hcol : ∀ p, j ≤ p → p ≤ j + w → ∀ t, T + m * P ≤ t →
      cell (t + (n - m) * P) p = cell t p := by
    intro p hp1 hp2 t ht
    have := key (t - (T + m * P)) p hp1 hp2
    rw [hshift, show T + m * P + (t - (T + m * P)) = t by omega] at this
    exact this.symm
  rcases Nat.eq_zero_or_pos w with hw | hw
  · -- `w = 0`: `h` determines `cell j || cell (j + 1)`, which then repeats; so does column `j - 1`
    have hs0 : ∀ t₁ t₂, strip j (j + w + 1) t₁ = strip j (j + w + 1) t₂ :=
      fun t₁ t₂ => strip_ext fun q hq1 hq2 => by omega
    have hw' : j + (w : Int) = j := by omega
    have hor : ∀ t, T + m * P ≤ t → (cell (t + (n - m) * P) j || cell (t + (n - m) * P) (j + 1)) =
        (cell t j || cell t (j + 1)) := by
      intro t ht
      have e := hF (t + (n - m) * P)
      rw [hs0 (t + (n - m) * P) t, periodic_mul (f := h) hph (n - m) t (by omega), ← hF t, hw'] at e
      exact e
    have hleft : ∀ t, T + m * P ≤ t → cell (t + (n - m) * P) (j - 1) = cell t (j - 1) := by
      intro t ht
      rw [cell_left, cell_left t, show t + (n - m) * P + 1 = (t + 1) + (n - m) * P by omega,
        hcol j (by omega) (by omega) (t + 1) (by omega), hor t ht]
    exact not_adjacent (j - 1) ⟨T + m * P, (n - m) * P, hQ, hleft⟩
      ⟨T + m * P, (n - m) * P, hQ, by
        rw [show j - 1 + 1 = j by omega]; exact hcol j (by omega) (by omega)⟩
  · -- `w ≥ 1`: columns `j` and `j + 1` both repeat
    exact not_adjacent j ⟨T + m * P, (n - m) * P, hQ, hcol j (by omega) (by omega)⟩
      ⟨T + m * P, (n - m) * P, hQ, hcol (j + 1) (by omega) (by omega)⟩

/-- **Affine form.** If column `j` is eventually periodic and `j < k`, then `cell t k` plus any
function `G` of the cells strictly between `j` and `k` is not eventually periodic. `G` constant is
Jen's theorem for the pair `(j, k)`. -/
theorem affine_observable (j k : Int) (hjk : j < k) (G : List Bool → Bool) :
    ¬ ((EventuallyPeriodic fun t => cell t j) ∧
      EventuallyPeriodic fun t => xor (cell t k) (G (strip j k t))) := by
  rintro ⟨hj, hh⟩
  obtain ⟨w, rfl⟩ : ∃ w : Nat, k = j + w + 1 := ⟨(k - j - 1).toNat, by omega⟩
  rcases Nat.eq_zero_or_pos w with hw | hw
  · -- the strip is empty, so column `j + 1` is `h` plus a constant
    have hs0 : ∀ t, strip j (j + w + 1) t = strip j (j + w + 1) 0 :=
      fun t => strip_ext fun q hq1 hq2 => by omega
    have hw' : j + (w : Int) = j := by omega
    obtain ⟨T, P, hP, hp⟩ := hh
    refine not_adjacent j hj ⟨T, P, hP, fun t ht => ?_⟩
    have := hp t ht
    simp only [hs0 (t + P), hs0 t] at this
    generalize G (strip j (j + w + 1) 0) = g at this
    rw [hw'] at this
    have e : xor (cell (t + P) (j + 1)) g = xor (cell t (j + 1)) g := this
    show cell (t + P) (j + 1) = cell t (j + 1)
    revert e
    cases cell (t + P) (j + 1) <;> cases cell t (j + 1) <;> cases g <;> decide
  · refine closing_observable j w
      (fun s y => s.getD (w - 1) false || xor y (G s))
      (fun t => xor (cell t (j + w + 1)) (G (strip j (j + w + 1) t))) (fun t => ?_) hj hh
    have hg : (strip j (j + w + 1) t).getD (w - 1) false = cell t (j + w) := by
      have := strip_get (j := j) (k := j + w + 1) (p := j + w) t (by omega) (by omega)
      rwa [show (j + (w : Int) - j - 1).toNat = w - 1 by omega] at this
    simp only [hg]
    cases cell t (j + w) <;> cases cell t (j + w + 1) <;>
      cases G (strip j (j + w + 1) t) <;> rfl

/-- The center column and `column 1 xor column 2` are not both eventually periodic. -/
theorem center_xor :
    ¬ ((EventuallyPeriodic fun t => cell t 0) ∧
      EventuallyPeriodic fun t => xor (cell t 1) (cell t 2)) := by
  rintro ⟨hc, hh⟩
  refine closing_observable 0 1 (fun s y => s.getD 0 false || xor (s.getD 0 false) y)
    (fun t => xor (cell t 1) (cell t 2)) (fun t => ?_) hc hh
  have hg : (strip 0 (0 + ((1 : Nat) : Int) + 1) t).getD 0 false = cell t 1 :=
    strip_get (j := 0) (p := 1) t (by omega) (by omega)
  simp only [hg]
  show (cell t 1 || cell t 2) = (cell t 1 || xor (cell t 1) (xor (cell t 1) (cell t 2)))
  cases cell t 1 <;> cases cell t 2 <;> rfl

/-- The center column, and column 2 read on the white times of column 1, are not both eventually
periodic. -/
theorem center_masked_two :
    ¬ ((EventuallyPeriodic fun t => cell t 0) ∧
      EventuallyPeriodic fun t => (!cell t 1 && cell t 2)) := by
  rintro ⟨hc, hh⟩
  refine closing_observable 0 1 (fun s y => s.getD 0 false || y)
    (fun t => !cell t 1 && cell t 2) (fun t => ?_) hc hh
  have hg : (strip 0 (0 + ((1 : Nat) : Int) + 1) t).getD 0 false = cell t 1 :=
    strip_get (j := 0) (p := 1) t (by omega) (by omega)
  simp only [hg]
  show (cell t 1 || cell t 2) = (cell t 1 || (!cell t 1 && cell t 2))
  cases cell t 1 <;> cases cell t 2 <;> rfl

/-- Parity of a list of colors. -/
def lpar : List Bool → Bool
  | [] => false
  | b :: l => xor b (lpar l)

theorem lpar_append : ∀ (l₁ l₂ : List Bool), lpar (l₁ ++ l₂) = xor (lpar l₁) (lpar l₂)
  | [], l₂ => by simp [lpar]
  | b :: l₁, l₂ => by
    simp only [List.cons_append, lpar, lpar_append l₁ l₂, Bool.xor_assoc]

theorem strip_succ (j : Int) (w : Nat) (t : Nat) :
    strip j (j + w + 2) t = strip j (j + w + 1) t ++ [cell t (j + w + 1)] := by
  unfold strip
  rw [show (j + (w : Int) + 2 - j - 1).toNat = w + 1 by omega,
    show (j + (w : Int) + 1 - j - 1).toNat = w by omega, List.range_succ, List.map_append]
  simp only [List.map_cons, List.map_nil]
  rw [show j + 1 + (w : Int) = j + w + 1 by omega]

/-- **Parity form.** For every `k ≥ 1`, the center column and the parity of columns `1, ..., k`
are not both eventually periodic. -/
theorem center_parity (k : Nat) (hk : 1 ≤ k) :
    ¬ ((EventuallyPeriodic fun t => cell t 0) ∧
      EventuallyPeriodic fun t => lpar (strip 0 (k + 1) t)) := by
  rintro ⟨hc, hh⟩
  obtain ⟨w, rfl⟩ : ∃ w : Nat, k = w + 1 := ⟨k - 1, by omega⟩
  refine affine_observable 0 (w + 1) (by omega) lpar ⟨hc, ?_⟩
  have e : ∀ t, lpar (strip 0 (((w + 1 : Nat) : Int) + 1) t) =
      xor (cell t ((w + 1 : Nat) : Int)) (lpar (strip 0 ((w + 1 : Nat) : Int) t)) := by
    intro t
    have := strip_succ 0 w t
    rw [show (0 : Int) + w + 2 = ((w + 1 : Nat) : Int) + 1 by omega,
      show (0 : Int) + w + 1 = ((w + 1 : Nat) : Int) by omega] at this
    rw [this, lpar_append]
    simp only [lpar, Bool.xor_false]
    rw [Bool.xor_comm]
  simp only [e] at hh
  exact hh

end Rule30Open
