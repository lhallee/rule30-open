module

public import Rule30Open.Diagonals.SettledRuns

/-!
# Linear settling of the left diagonals, with periods that grow, bounds black center runs with a slope below 3/5

Read the single seed's pattern along the left diagonals, `D j t = cell t (j - t)`. `SettledRuns` proves that two
adjacent diagonals never alternate in antiphase from some time on (`no_alt_pair`), and that a black run of the center
column of length `L` from time `a` makes two adjacent diagonals alternate in antiphase over a window of times
(`black_diag`). This module replaces the fixed period 16 of `SettledRuns` by a bound `A` on the antiphase alternations
of each settled pair, so the periods may grow with the depth.

* `AltBound j T A`: no antiphase alternation of `D j`, `D (j + 1)` that starts at a time `≥ T` lasts `A + 1` times.
  If the pair repeats from `T` with a period `P > 0`, a bound that holds from some time on holds from `T`
  (`altBound_of_repeats`), and `A = P` always works (`altBound_of_period_le`), so the longest antiphase
  alternation of a settled pair lasts at most `P` times.
* `black_run_window`: the window argument. If the trapezoid of a black run covers diagonals `j` and `j + 1` at the
  `A + 1` times `a - s0 - A .. a - s0`, the pair alternates in antiphase there, so `AltBound j T A` fails for
  every `T ≤ a - s0 - A`.
* `black_run_le_of_settling`: if every diagonal `j ≤ J + 1` repeats, with any period, from time `⌈3j/2⌉ + δ`, and
  every pair `j ≤ J` has its antiphase alternations bounded by `A` from some time on, then a black run from time
  `a ≥ 1` with `⌊8a/13⌋ ≤ J` has `13 L ≤ 3a + 130 A + 130 δ + 260`. The slope is `3/13`. At the settling time
  `⌈27j/20⌉ + δ`, `black_run_le_of_fast_settling` gives the slope `21/115`.
* `pair_repeats_of_white_runs`: the reset bound. If every diagonal `1 ≤ i ≤ J` is eventually white, or eventually
  has a black cell in every `c i` consecutive times, then the pair `(D j, D (j + 1))` repeats from time
  `1 + c 1 + ... + c j` for every `j ≤ J`. Behind a black cell the next diagonal forgets its past
  (`D_periodic_of_black`); behind a white diagonal it repeats with twice the period, at once.
* `black_run_le_of_white_runs`: so if `c 1 + ... + c j ≤ 6 j + δ` for `j ≤ J` and the alternations are bounded by
  `A`, a black run from `a ≥ 1` with `⌊4a/29⌋ ≤ J` has `29 L ≤ 15 a + 90 A + 90 δ + 180`. The slope is `15/29`;
  the hypothesis is about the white runs and the alternations of the settled diagonals only.

None of the hypotheses is proved. They are checked on a finite table (`computations/settled_slope.py`), and the
theorems apply only up to the depth `J` the check reaches; see `SettledSlope.md`.

The natural-language argument is `SettledSlope.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

open Ruliology.CellularAutomata
open Ruliology.CellularAutomata.Rule30Diagonals
open Ruliology.CellularAutomata.Rule30CenterRuns
open Rule30Jen Rule30Prize

/-! ### Periodic sequences -/

/-- `f` repeats with period `P` from time `T` on. -/
def RepeatsFrom (f : Nat → Bool) (T P : Nat) : Prop :=
  ∀ t, T ≤ t → f (t + P) = f t

theorem RepeatsFrom.mono {f : Nat → Bool} {T U P : Nat} (h : RepeatsFrom f T P) (hTU : T ≤ U) :
    RepeatsFrom f U P :=
  fun t ht => h t (Nat.le_trans hTU ht)

theorem RepeatsFrom.iter {f : Nat → Bool} {T P : Nat} (h : RepeatsFrom f T P) :
    ∀ n t, T ≤ t → f (t + n * P) = f t
  | 0, t, _ => by rw [Nat.zero_mul, Nat.add_zero]
  | n + 1, t, ht => by
    rw [Nat.add_mul, Nat.one_mul, ← Nat.add_assoc, h _ (Nat.le_trans ht (Nat.le_add_right _ _)),
      RepeatsFrom.iter h n t ht]

/-- `f` is white from some time on. -/
def EventuallyWhite (f : Nat → Bool) : Prop :=
  ∃ T, ∀ t, T ≤ t → f t = false

/-- Every `c` consecutive times from `T` on contain a black cell of `f`: its white runs from `T` on are shorter
than `c`. -/
def BlackWithin (f : Nat → Bool) (T c : Nat) : Prop :=
  ∀ t, T ≤ t → ∃ r, t ≤ r ∧ r < t + c ∧ f r = true

/-- A sequence that repeats from `T` and has its white runs shorter than `c` from some time on has them shorter than
`c` from `T` on. -/
theorem blackWithin_of_repeats {f : Nat → Bool} {T P T' c : Nat} (hP : 0 < P) (hf : RepeatsFrom f T P)
    (hb : BlackWithin f T' c) : BlackWithin f T c := by
  intro t ht
  have hm : T' ≤ T' * P := Nat.le_mul_of_pos_right T' hP
  have e := hf.iter T'
  generalize T' * P = m at hm e
  obtain ⟨r, hr1, hr2, hr⟩ := hb (t + m) (by omega)
  refine ⟨r - m, by omega, by omega, ?_⟩
  rw [← e (r - m) (by omega), show r - m + m = r by omega]
  exact hr

/-- A sequence that repeats from `T` and is eventually white is white from `T` on. -/
theorem white_of_repeats {f : Nat → Bool} {T P : Nat} (hP : 0 < P) (hf : RepeatsFrom f T P)
    (hw : EventuallyWhite f) : ∀ t, T ≤ t → f t = false := by
  obtain ⟨T', hT'⟩ := hw
  intro t ht
  have hm : T' ≤ T' * P := Nat.le_mul_of_pos_right T' hP
  have e := hf.iter T' t ht
  generalize T' * P = m at hm e
  rw [← e]
  exact hT' _ (by omega)

/-! ### Antiphase alternations of a settled pair -/

/-- Diagonals `j` and `j + 1` alternate in antiphase at the `A + 1` times `T .. T + A`. -/
def AntiWindow (j T A : Nat) : Prop :=
  (∀ k, k ≤ A → D (j + 1) (T + k) = !D j (T + k)) ∧ (∀ k, k < A → D j (T + k + 1) = !D j (T + k))

/-- No antiphase alternation of diagonals `j` and `j + 1` that starts at a time `≥ T` lasts `A + 1` times. -/
def AltBound (j T A : Nat) : Prop :=
  ∀ T', T ≤ T' → ¬ AntiWindow j T' A

/-- If the pair repeats with period `P > 0` from `T`, a bound on its alternations from some time on holds from `T`. -/
theorem altBound_of_repeats {j T P T₀ A : Nat} (hP : 0 < P) (h0 : RepeatsFrom (D j) T P)
    (h1 : RepeatsFrom (D (j + 1)) T P) (hB : AltBound j T₀ A) : AltBound j T A := by
  intro T' hT' hw
  obtain ⟨ha, hl⟩ := hw
  have hm : T₀ ≤ T₀ * P := Nat.le_mul_of_pos_right T₀ hP
  have e0 := h0.iter T₀
  have e1 := h1.iter T₀
  generalize T₀ * P = m at hm e0 e1
  refine hB (T' + m) (by omega) ⟨fun k hk => ?_, fun k hk => ?_⟩
  · rw [show T' + m + k = (T' + k) + m by omega, e1 _ (by omega), e0 _ (by omega)]
    exact ha k hk
  · rw [show T' + m + k + 1 = (T' + k + 1) + m by omega, show T' + m + k = (T' + k) + m by omega,
      e0 _ (by omega), e0 _ (by omega)]
    exact hl k hk

/-- A settled pair never alternates in antiphase for `P + 1` times: `A = P` bounds its alternations. -/
theorem altBound_of_period_le {j T P A : Nat} (hP : 0 < P) (h0 : RepeatsFrom (D j) T P)
    (h1 : RepeatsFrom (D (j + 1)) T P) (hA : P ≤ A) : AltBound j T A := by
  intro T' hT' hw
  exact settled_alt_pair j T P T' hT' hP h0 h1 (fun k hk => hw.1 k (by omega)) (fun k hk => hw.2 k (by omega))

/-- Diagonals `j` and `j + 1` that repeat, with any periods, from times `T₀, T₁ ≤ T` have a bound on their
alternations from `T` as soon as they have one from some time on. -/
theorem altBound_of_settled {j T₀ T₁ T P₀ P₁ T' A : Nat} (hP₀ : 0 < P₀) (hP₁ : 0 < P₁)
    (h0 : RepeatsFrom (D j) T₀ P₀) (h1 : RepeatsFrom (D (j + 1)) T₁ P₁) (hT₀ : T₀ ≤ T) (hT₁ : T₁ ≤ T)
    (hB : AltBound j T' A) : AltBound j T A := by
  refine altBound_of_repeats (P := P₁ * P₀) (Nat.mul_pos hP₁ hP₀) (fun t ht => h0.iter P₁ t (by omega))
    (fun t ht => ?_) hB
  rw [Nat.mul_comm]
  exact h1.iter P₀ t (by omega)

/-! ### The window argument -/

/-- **The window argument.** If the trapezoid of a black run of length `L` from time `a` covers diagonals `j` and
`j + 1` at the `A + 1` times `a - s0 - A .. a - s0`, their alternations are not bounded by `A` from any time
`T ≤ a - s0 - A`. -/
theorem black_run_window (a L j s0 A T : Nat) (h : ∀ i, i < L → center (a + i) = true)
    (r1 : a + 1 ≤ 2 * s0 + j + L) (r2 : 5 * (s0 + A) + j + 1 ≤ a) (r3 : T ≤ a - s0 - A)
    (hB : AltBound j T A) : False := by
  have h2 : ∀ i, i < L → cell (a + i) 0 = true := h
  have key : ∀ s, s0 ≤ s → s ≤ s0 + A →
      D j (a - s) = altPat ((j : Int) - ((a - s : Nat) : Int)) ∧
      D (j + 1) (a - s) = altPat (((j + 1 : Nat) : Int) - ((a - s : Nat) : Int)) := by
    intro s hs1 hs2
    exact ⟨black_diag a L h2 j s (by omega) (by omega) (by omega),
      black_diag a L h2 (j + 1) s (by omega) (by omega) (by omega)⟩
  refine hB (a - s0 - A) r3 ⟨fun k hk => ?_, fun k hk => ?_⟩
  · have e := key (s0 + A - k) (by omega) (by omega)
    rw [show a - s0 - A + k = a - (s0 + A - k) by omega, e.1, e.2]
    rw [show ((j + 1 : Nat) : Int) = (j : Int) + 1 by omega]
    have := altPat_succ ((j : Int) - ((a - (s0 + A - k) : Nat) : Int))
    rw [show (j : Int) + 1 - ((a - (s0 + A - k) : Nat) : Int) =
      (j : Int) - ((a - (s0 + A - k) : Nat) : Int) + 1 by omega]
    exact this
  · have e := key (s0 + A - k) (by omega) (by omega)
    have e2 := key (s0 + A - k - 1) (by omega) (by omega)
    rw [show a - s0 - A + k + 1 = a - (s0 + A - k - 1) by omega,
      show a - s0 - A + k = a - (s0 + A - k) by omega, e.1, e2.1]
    rw [show ((a - (s0 + A - k - 1) : Nat) : Int) = ((a - (s0 + A - k) : Nat) : Int) + 1 by omega,
      show (j : Int) - (((a - (s0 + A - k) : Nat) : Int) + 1) =
        ((j : Int) - ((a - (s0 + A - k) : Nat) : Int)) - 1 by omega, altPat_pred]

/-- **Black runs under linear settling, with any periods.** If every diagonal `j ≤ J + 1` repeats, with a period
that may depend on `j`, from time `⌈3j/2⌉ + δ` on, and the antiphase alternations of every pair `j ≤ J` are
eventually bounded by `A`, then a black run of the center column from time `a ≥ 1` with `⌊8a/13⌋ ≤ J` has
`13 L ≤ 3a + 130 A + 130 δ + 260`. -/
theorem black_run_le_of_settling (J δ A : Nat)
    (hP : ∀ j, j ≤ J + 1 → ∃ P, 0 < P ∧ RepeatsFrom (D j) ((3 * j + 1) / 2 + δ) P)
    (hA : ∀ j, j ≤ J → ∃ T, AltBound j T A)
    (a L : Nat) (ha : 1 ≤ a) (hJ : 8 * a / 13 ≤ J) (h : ∀ i, i < L → center (a + i) = true) :
    13 * L ≤ 3 * a + 130 * A + 130 * δ + 260 := by
  refine Classical.byContradiction fun hcon => ?_
  have hLa : L ≤ a := black_run_le a L ha h
  obtain ⟨j, hj⟩ : ∃ j, j = 8 * a / 13 := ⟨_, rfl⟩
  obtain ⟨s0, hs0⟩ : ∃ s0, s0 = (a + 2 - j - L) / 2 := ⟨_, rfl⟩
  obtain ⟨P₀, hP₀, h0⟩ := hP j (by omega)
  obtain ⟨P₁, hP₁, h1⟩ := hP (j + 1) (by omega)
  obtain ⟨T', hB⟩ := hA j (by omega)
  exact black_run_window a L j s0 A ((3 * (j + 1) + 1) / 2 + δ) h (by omega) (by omega) (by omega)
    (altBound_of_settled hP₀ hP₁ h0 h1 (by omega) (Nat.le_refl _) hB)

/-- The same at the settling time `⌈27j/20⌉ + δ`: `115 L ≤ 21 a + 1600 A + 1600 δ + 4000` for `⌊16a/23⌋ ≤ J`. The
slope is `21/115`. -/
theorem black_run_le_of_fast_settling (J δ A : Nat)
    (hP : ∀ j, j ≤ J + 1 → ∃ P, 0 < P ∧ RepeatsFrom (D j) ((27 * j + 19) / 20 + δ) P)
    (hA : ∀ j, j ≤ J → ∃ T, AltBound j T A)
    (a L : Nat) (ha : 1 ≤ a) (hJ : 16 * a / 23 ≤ J) (h : ∀ i, i < L → center (a + i) = true) :
    115 * L ≤ 21 * a + 1600 * A + 1600 * δ + 4000 := by
  refine Classical.byContradiction fun hcon => ?_
  have hLa : L ≤ a := black_run_le a L ha h
  obtain ⟨j, hj⟩ : ∃ j, j = 16 * a / 23 := ⟨_, rfl⟩
  obtain ⟨s0, hs0⟩ : ∃ s0, s0 = (a + 2 - j - L) / 2 := ⟨_, rfl⟩
  obtain ⟨P₀, hP₀, h0⟩ := hP j (by omega)
  obtain ⟨P₁, hP₁, h1⟩ := hP (j + 1) (by omega)
  obtain ⟨T', hB⟩ := hA j (by omega)
  exact black_run_window a L j s0 A ((27 * (j + 1) + 19) / 20 + δ) h (by omega) (by omega) (by omega)
    (altBound_of_settled hP₀ hP₁ h0 h1 (by omega) (Nat.le_refl _) hB)

/-! ### The reset bound -/

/-- Behind a black cell of diagonal `j + 1` within `c` times of `Q`, diagonal `j + 2` repeats from `Q + c`. -/
theorem pair_step_black {j Q P c : Nat} (h0 : RepeatsFrom (D j) Q P) (h1 : RepeatsFrom (D (j + 1)) Q P)
    (hb : BlackWithin (D (j + 1)) Q c) : RepeatsFrom (D (j + 1)) (Q + c) P ∧ RepeatsFrom (D (j + 2)) (Q + c) P := by
  obtain ⟨r, hr1, hr2, hr⟩ := hb Q (Nat.le_refl Q)
  exact ⟨h1.mono (by omega), fun t ht => D_periodic_of_black j Q P r h0 h1 hr1 hr t (by omega)⟩

/-- Behind a white diagonal `j + 1`, diagonal `j + 2` repeats with twice the period, from the same time. -/
theorem pair_step_white {j Q P : Nat} (h0 : RepeatsFrom (D j) Q P) (hw : ∀ t, Q ≤ t → D (j + 1) t = false) :
    RepeatsFrom (D (j + 1)) Q (2 * P) ∧ RepeatsFrom (D (j + 2)) Q (2 * P) := by
  have shift : ∀ t, Q ≤ t → D (j + 2) (t + P) = xor (D (j + 2) t) (windowParity (D j) Q P) := fun t ht => by
    rw [D_shift_of_white j Q hw t ht P, windowParity_periodic (D j) Q P h0 t ht]
  refine ⟨fun t ht => by rw [hw t ht, hw _ (by omega)], fun t ht => ?_⟩
  rw [show t + 2 * P = t + P + P by omega, shift (t + P) (by omega), shift t ht]
  generalize D (j + 2) t = x
  generalize windowParity (D j) Q P = p
  cases x <;> cases p <;> rfl

/-- The sum `c 1 + ... + c j`. -/
def costSum (c : Nat → Nat) : Nat → Nat
  | 0 => 0
  | j + 1 => costSum c j + c (j + 1)

/-- **The reset bound.** If every diagonal `1 ≤ i ≤ J` is eventually white, or eventually has a black cell in every
`c i` consecutive times, then for every `j ≤ J` the pair `(D j, D (j + 1))` repeats with a common period from time
`1 + c 1 + ... + c j` on. -/
theorem pair_repeats_of_white_runs (c : Nat → Nat) (J : Nat)
    (hc : ∀ i, 1 ≤ i → i ≤ J → EventuallyWhite (D i) ∨ ∃ T, BlackWithin (D i) T (c i)) :
    ∀ j, j ≤ J → ∃ P, 0 < P ∧ RepeatsFrom (D j) (1 + costSum c j) P ∧
      RepeatsFrom (D (j + 1)) (1 + costSum c j) P
  | 0, _ => ⟨1, Nat.one_pos, fun t _ => by rw [D_zero, D_zero], fun t ht => by
      obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by simp [costSum] at ht; omega⟩
      rw [D_one, D_one]⟩
  | j + 1, hj => by
    obtain ⟨P, hP, h0, h1⟩ := pair_repeats_of_white_runs c J hc j (by omega)
    have hQ : 1 + costSum c (j + 1) = 1 + costSum c j + c (j + 1) := by
      show 1 + (costSum c j + c (j + 1)) = 1 + costSum c j + c (j + 1)
      omega
    rw [hQ]
    rcases hc (j + 1) (by omega) (by omega) with hw | ⟨T, hb⟩
    · have hw' := white_of_repeats hP h1 hw
      obtain ⟨s1, s2⟩ := pair_step_white h0 hw'
      exact ⟨2 * P, by omega, s1.mono (by omega), s2.mono (by omega)⟩
    · obtain ⟨s1, s2⟩ := pair_step_black h0 h1 (blackWithin_of_repeats hP h1 hb)
      exact ⟨P, hP, s1, s2⟩

/-- **Black runs from the white runs of the settled diagonals.** If every diagonal `1 ≤ i ≤ J` is eventually white
or eventually has its white runs shorter than `c i`, with `c 1 + ... + c j ≤ 6 j + δ` for `j ≤ J`, and the antiphase
alternations of every pair `j ≤ J` are eventually bounded by `A`, then a black run of the center column from time
`a ≥ 1` with `⌊4a/29⌋ ≤ J` has `29 L ≤ 15 a + 90 A + 90 δ + 180`. -/
theorem black_run_le_of_white_runs (c : Nat → Nat) (J δ A : Nat)
    (hc : ∀ i, 1 ≤ i → i ≤ J → EventuallyWhite (D i) ∨ ∃ T, BlackWithin (D i) T (c i))
    (hS : ∀ j, j ≤ J → costSum c j ≤ 6 * j + δ)
    (hA : ∀ j, j ≤ J → ∃ T, AltBound j T A)
    (a L : Nat) (ha : 1 ≤ a) (hJ : 4 * a / 29 ≤ J) (h : ∀ i, i < L → center (a + i) = true) :
    29 * L ≤ 15 * a + 90 * A + 90 * δ + 180 := by
  refine Classical.byContradiction fun hcon => ?_
  have hLa : L ≤ a := black_run_le a L ha h
  obtain ⟨j, hj⟩ : ∃ j, j = 4 * a / 29 := ⟨_, rfl⟩
  obtain ⟨s0, hs0⟩ : ∃ s0, s0 = (a + 2 - j - L) / 2 := ⟨_, rfl⟩
  obtain ⟨P, hP, h0, h1⟩ := pair_repeats_of_white_runs c J hc j (by omega)
  obtain ⟨T', hB⟩ := hA j (by omega)
  have hSj := hS j (by omega)
  exact black_run_window a L j s0 A (1 + costSum c j) h (by omega) (by omega) (by omega)
    (altBound_of_repeats hP h0 h1 hB)

end Rule30Open
