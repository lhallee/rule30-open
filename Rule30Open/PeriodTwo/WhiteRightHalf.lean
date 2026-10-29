module

public import Ruliology.CellularAutomata.Rule30PeriodTwoSideways
public import Ruliology.CellularAutomata.Rule30EtherThreeReach

/-!
# Against a white right half, no left half within depth 32,755 keeps the center alternating

The kit's open milestone for period two, `Rule30PeriodTwoSideways.CQ01Empty`, asks that no finite configuration whose
cells right of the center are white keeps its center alternating `1, 0, 1, …` from time `0`. Exactly one left half,
`Psi empty`, does so forever, and a left half that first differs from it at depth `d` keeps the center alternating
through time `d - 1` and not at time `d` (the kit's `exact_death_center`). So a left half of width `W` loses the
alternation by the first black depth of `Psi empty` beyond `W`. This module computes `Psi empty` in the kernel and
checks that its black cells are never `G` or more apart.

* `yLoop`, `yLoop_spec`: the right half driven by the alternating center (the kit's `rowN`), and column `-1` of the
  row that keeps the center alternating, as the bits of one number.
* `colN`, `colN_testBit`, `psiLoop`, `psiLoop_spec`: the sideways reconstruction of `Psi empty`, one column per step.
* `runsAnd`, `gaps_of_check`: every window of `G` depths beyond `W < W0` holds a black cell of `Psi empty`.
* `psi_empty_gaps`: with `N = 32768` and `G = 13`, for every `W < 32755`.
* `white_right_leaves`: no configuration whose right half is white and whose left half lies within depth `W < 32755`
  keeps the center alternating through time `W + 13`.

The natural-language argument is `WhiteRightHalf.md`, beside this file.
-/

@[expose] public section

-- Sequential elaboration: the kernel checks would otherwise run in parallel and stack their memory.
set_option Elab.async false

namespace Rule30Open

open Ruliology.CellularAutomata
open Rule30ZeroBoundary Rule30PeriodTwoSideways Rule30PeriodTwoCoupled Rule30Ether Rule30EtherThree
  Rule30Realization

/-! ### Column `-1` -/

/-- Column `-1` of the row that keeps the center alternating against the white right half. -/
def yAt (t : Nat) : Bool := alt (fun s => !u empty s) t

theorem rowN_empty_bit (t : Nat) : (rowN altCol 0 t).testBit 0 = drv altCol empty t 1 := by
  have h := rowN_eq_drv altCol 0 t 0
  have he : (fun p : Nat => (0 : Nat).testBit (p - 1)) = empty := by
    funext p; exact Nat.zero_testBit _
  rw [he] at h
  exact h

theorem yAt_eq (t : Nat) : yAt t = ((t % 2 == 0) || !(rowN altCol 0 t).testBit 0) := by
  unfold yAt alt
  by_cases h : t % 2 = 0
  · rw [ite_eq_left h]; simp [h]
  · rw [ite_eq_right h, rowN_empty_bit]
    have h1 : (t % 2 == 0) = false := by simpa using h
    rw [h1, Bool.false_or]
    show (!drv altCol empty (2 * (t / 2) + 1) 1) = !drv altCol empty t 1
    rw [show 2 * (t / 2) + 1 = t by omega]

/-- The right half driven by the alternating center, collecting column `-1` at times `t, t + 1, …`. -/
def yLoop : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, acc => acc
  | n + 1, t, r, acc =>
    if (Nat.ble 0 (if ((t % 2 == 0) || !r.testBit 0) = true then acc ||| (1 <<< t) else acc) &&
        Nat.ble 0 (stepN (altCol t) r)) = true
    then yLoop n (t + 1) (stepN (altCol t) r)
      (if ((t % 2 == 0) || !r.testBit 0) = true then acc ||| (1 <<< t) else acc)
    else 0

theorem yLoop_succ (n t r acc : Nat) :
    yLoop (n + 1) t r acc = yLoop n (t + 1) (stepN (altCol t) r)
      (if ((t % 2 == 0) || !r.testBit 0) = true then acc ||| (1 <<< t) else acc) := by
  rw [yLoop, Nat.ble_eq_true_of_le (Nat.zero_le _), Nat.ble_eq_true_of_le (Nat.zero_le _)]
  rfl

theorem yLoop_spec : ∀ n t acc, (∀ i, t ≤ i → acc.testBit i = false) → ∀ i,
    (yLoop n t (rowN altCol 0 t) acc).testBit i =
      if i < t then acc.testBit i else if i < t + n then yAt i else false := by
  intro n
  induction n with
  | zero =>
    intro t acc hacc i
    simp only [yLoop, Nat.add_zero]
    by_cases h : i < t
    · rw [ite_eq_left h]
    · rw [ite_eq_right h, ite_eq_right h, hacc i (by omega)]
  | succ n ih =>
    intro t acc hacc i
    have hbit : ∀ j,
        (if ((t % 2 == 0) || !(rowN altCol 0 t).testBit 0) = true then acc ||| (1 <<< t) else acc).testBit j =
          (acc.testBit j || (decide (t = j) && yAt t)) := by
      intro j
      rw [yAt_eq]
      cases ((t % 2 == 0) || !(rowN altCol 0 t).testBit 0)
      · simp
      · simp [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow]
    rw [yLoop_succ, show stepN (altCol t) (rowN altCol 0 t) = rowN altCol 0 (t + 1) from rfl,
      ih (t + 1) _ (by
        intro j hj
        rw [hbit j, hacc j (by omega), decide_eq_false (show ¬ t = j by omega)]
        rfl),
      hbit i]
    by_cases h1 : i < t
    · rw [ite_eq_left (show i < t + 1 by omega), ite_eq_left h1, decide_eq_false (show ¬ t = i by omega),
        Bool.false_and, Bool.or_false]
    · by_cases h2 : i = t
      · rw [ite_eq_left (show i < t + 1 by omega), ite_eq_right h1, ite_eq_left (show i < t + (n + 1) by omega),
          hacc i (by omega), decide_eq_true h2.symm, Bool.true_and, Bool.false_or, h2]
      · rw [ite_eq_right (show ¬ i < t + 1 by omega), ite_eq_right h1, show t + 1 + n = t + (n + 1) by omega]

/-! ### The sideways reconstruction -/

/-- The columns of the reconstruction from column `-1` given as the bits of `Y`: depth `0` is the white wall. -/
def colN (Y : Nat) : Nat → Nat
  | 0 => 0
  | 1 => Y
  | k + 2 => (colN Y (k + 1) >>> 1) ^^^ (colN Y (k + 1) ||| colN Y k)

/-- **The columns are the reconstruction** while the bits of `Y` they read are those of `y`. -/
theorem colN_testBit (Y : Nat) (y : Nat → Bool) (N : Nat) (hY : ∀ t, t < N → Y.testBit t = y t) :
    ∀ k t, t + k ≤ N → (colN Y k).testBit t = recon y k t := by
  have key : ∀ k, (∀ t, t + k ≤ N → (colN Y k).testBit t = recon y k t) ∧
      (∀ t, t + (k + 1) ≤ N → (colN Y (k + 1)).testBit t = recon y (k + 1) t) := by
    intro k
    induction k with
    | zero =>
      refine ⟨fun t _ => ?_, fun t ht => ?_⟩
      · show (0 : Nat).testBit t = recon y 0 t
        rw [recon]; exact Nat.zero_testBit t
      · show Y.testBit t = recon y 1 t
        rw [recon]; exact hY t (by omega)
    | succ k ih =>
      refine ⟨ih.2, fun t ht => ?_⟩
      show ((colN Y (k + 1) >>> 1) ^^^ (colN Y (k + 1) ||| colN Y k)).testBit t = _
      rw [Nat.testBit_xor, Nat.testBit_or, Nat.testBit_shiftRight, show 1 + t = t + 1 by omega,
        ih.2 (t + 1) (by omega), ih.2 t (by omega), ih.1 t (by omega), recon_two]
  exact fun k t ht => (key k).1 t ht

/-- The reconstruction, collecting bit `0` of columns `k, k + 1, …` (the start at those depths). -/
def psiLoop : Nat → Nat → Nat → Nat → Nat → Nat
  | 0, _, _, _, acc => acc
  | n + 1, k, prev, cur, acc =>
    if (Nat.ble 0 (if cur.testBit 0 = true then acc ||| (1 <<< k) else acc) &&
        Nat.ble 0 ((cur >>> 1) ^^^ (cur ||| prev))) = true
    then psiLoop n (k + 1) cur ((cur >>> 1) ^^^ (cur ||| prev))
      (if cur.testBit 0 = true then acc ||| (1 <<< k) else acc)
    else 0

theorem psiLoop_succ (n k prev cur acc : Nat) :
    psiLoop (n + 1) k prev cur acc = psiLoop n (k + 1) cur ((cur >>> 1) ^^^ (cur ||| prev))
      (if cur.testBit 0 = true then acc ||| (1 <<< k) else acc) := by
  rw [psiLoop, Nat.ble_eq_true_of_le (Nat.zero_le _), Nat.ble_eq_true_of_le (Nat.zero_le _)]
  rfl

theorem psiLoop_spec (Y : Nat) : ∀ n k acc, 1 ≤ k → (∀ i, k ≤ i → acc.testBit i = false) → ∀ i,
    (psiLoop n k (colN Y (k - 1)) (colN Y k) acc).testBit i =
      if i < k then acc.testBit i else if i < k + n then (colN Y i).testBit 0 else false := by
  intro n
  induction n with
  | zero =>
    intro k acc _ hacc i
    simp only [psiLoop, Nat.add_zero]
    by_cases h : i < k
    · rw [ite_eq_left h]
    · rw [ite_eq_right h, ite_eq_right h, hacc i (by omega)]
  | succ n ih =>
    intro k acc hk hacc i
    have hbit : ∀ j, (if (colN Y k).testBit 0 = true then acc ||| (1 <<< k) else acc).testBit j =
        (acc.testBit j || (decide (k = j) && (colN Y k).testBit 0)) := by
      intro j
      cases (colN Y k).testBit 0
      · simp
      · simp [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow]
    have hnext : (colN Y k >>> 1) ^^^ (colN Y k ||| colN Y (k - 1)) = colN Y (k + 1) := by
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      rfl
    rw [psiLoop_succ, hnext, show colN Y k = colN Y (k + 1 - 1) by rw [Nat.add_sub_cancel],
      ih (k + 1) _ (by omega) (by
        intro j hj
        rw [show k + 1 - 1 = k by omega, hbit j, hacc j (by omega), decide_eq_false (show ¬ k = j by omega)]
        rfl),
      show k + 1 - 1 = k by omega, hbit i]
    by_cases h1 : i < k
    · rw [ite_eq_left (show i < k + 1 by omega), ite_eq_left h1, decide_eq_false (show ¬ k = i by omega),
        Bool.false_and, Bool.or_false]
    · by_cases h2 : i = k
      · rw [ite_eq_left (show i < k + 1 by omega), ite_eq_right h1, ite_eq_left (show i < k + (n + 1) by omega),
          hacc i (by omega), decide_eq_true h2.symm, Bool.true_and, Bool.false_or, h2]
      · rw [ite_eq_right (show ¬ i < k + 1 by omega), ite_eq_right h1, show k + 1 + n = k + (n + 1) by omega]

/-- The bits of `Psi empty` at depths `1, …, N`. -/
def psiBits (N : Nat) : Nat := psiLoop N 1 0 (yLoop N 0 0 0) 0

/-- **The computed bits are `Psi empty`.** -/
theorem psiBits_spec (N d : Nat) (h1 : 1 ≤ d) (hd : d ≤ N) : (psiBits N).testBit d = Psi empty d := by
  have hY : ∀ t, t < N → (yLoop N 0 0 0).testBit t = yAt t := by
    intro t ht
    have := yLoop_spec N 0 0 (fun i _ => Nat.zero_testBit i) t
    rw [show rowN altCol 0 0 = 0 from rfl] at this
    rw [this, ite_eq_right (by omega), ite_eq_left (by omega)]
  have h := psiLoop_spec (yLoop N 0 0 0) N 1 0 (Nat.le_refl 1) (fun i _ => Nat.zero_testBit i) d
  rw [show colN (yLoop N 0 0 0) (1 - 1) = 0 from rfl, show colN (yLoop N 0 0 0) 1 = yLoop N 0 0 0 from rfl] at h
  unfold psiBits
  rw [h, ite_eq_right (by omega), ite_eq_left (by omega), colN_testBit _ yAt N hY d 0 (by omega)]
  rfl

/-! ### Gaps -/

/-- Bit `j` is set when bits `j, …, j + g` of `Z` all are. -/
def runsAnd (Z : Nat) : Nat → Nat
  | 0 => Z
  | g + 1 => runsAnd Z g &&& (Z >>> (g + 1))

theorem testBit_runsAnd (Z : Nat) :
    ∀ g j, (∀ i, i ≤ g → Z.testBit (j + i) = true) → (runsAnd Z g).testBit j = true := by
  intro g
  induction g with
  | zero => intro j h; show Z.testBit j = true; simpa using h 0 (by omega)
  | succ g ih =>
    intro j h
    show (runsAnd Z g &&& (Z >>> (g + 1))).testBit j = true
    rw [Nat.testBit_and, ih j (fun i hi => h i (by omega)), Nat.testBit_shiftRight,
      show g + 1 + j = j + (g + 1) by omega, h (g + 1) (Nat.le_refl _)]
    rfl

/-- The check: no `G` depths in a row, starting at a depth in `1, …, W0`, without a black cell of `P` among
depths `1, …, N`. -/
def gapsCheck (P N G W0 : Nat) : Bool :=
  (runsAnd ((2 ^ (N + 1) - 1) ^^^ P) (G - 1) &&& ((2 ^ (W0 + 1) - 1) ^^^ 1)) == 0

theorem gaps_of_check (P N G W0 : Nat) (hG : 1 ≤ G) (hN : W0 + G ≤ N) (h : gapsCheck P N G W0 = true) :
    ∀ W, W < W0 → ∃ d, W < d ∧ d ≤ W + G ∧ P.testBit d = true := by
  intro W hW
  refine Classical.byContradiction fun hne => ?_
  have hz : ∀ i, i ≤ G - 1 → ((2 ^ (N + 1) - 1) ^^^ P).testBit (W + 1 + i) = true := by
    intro i hi
    rw [Nat.testBit_xor, Nat.testBit_two_pow_sub_one, decide_eq_true (by omega)]
    cases hp : P.testBit (W + 1 + i)
    · rfl
    · exact absurd ⟨W + 1 + i, by omega, by omega, hp⟩ hne
  have hr := testBit_runsAnd _ (G - 1) (W + 1) hz
  have hm : ((2 ^ (W0 + 1) - 1) ^^^ 1).testBit (W + 1) = true := by
    rw [Nat.testBit_xor, Nat.testBit_two_pow_sub_one, decide_eq_true (by omega),
      show (1 : Nat) = 2 ^ 0 by rfl, Nat.testBit_two_pow, decide_eq_false (by omega)]
    rfl
  have hand : (runsAnd ((2 ^ (N + 1) - 1) ^^^ P) (G - 1) &&& ((2 ^ (W0 + 1) - 1) ^^^ 1)).testBit (W + 1) = true := by
    rw [Nat.testBit_and, hr, hm]; rfl
  unfold gapsCheck at h
  rw [beq_iff_eq] at h
  rw [h, Nat.zero_testBit] at hand
  exact absurd hand (by decide)

/-! ### The left halves -/

/-- The first depth at which `L` differs from `Psi empty`, below a known difference. -/
theorem first_difference (L : Nat → Bool) : ∀ n, (∃ d, 1 ≤ d ∧ d ≤ n ∧ L d ≠ Psi empty d) →
    ∃ d, 1 ≤ d ∧ d ≤ n ∧ L d ≠ Psi empty d ∧ ∀ i, 1 ≤ i → i < d → L i = Psi empty i := by
  intro n
  induction n with
  | zero => rintro ⟨d, h1, h2, _⟩; omega
  | succ n ih =>
    intro h
    by_cases hb : ∃ d, 1 ≤ d ∧ d ≤ n ∧ L d ≠ Psi empty d
    · obtain ⟨d, h1, h2, h3, h4⟩ := ih hb
      exact ⟨d, h1, by omega, h3, h4⟩
    · obtain ⟨d, h1, h2, h3⟩ := h
      have hd : d = n + 1 := by
        refine Classical.byContradiction fun hne => hb ⟨d, h1, by omega, h3⟩
      refine ⟨d, h1, h2, h3, fun i hi1 hi2 => Classical.byContradiction fun hne => hb ⟨i, hi1, by omega, hne⟩⟩

/-- **A left half that lies within depth `W` loses the alternation** by the first black depth of `Psi empty` beyond
`W`, against the white right half. -/
theorem leaves_by_gap (x : Int → Bool) (W G : Nat) (hR : ∀ p : Int, 0 < p → x p = false)
    (hL : ∀ p : Int, p < -(W : Int) → x p = false) (hgap : ∃ d, W < d ∧ d ≤ W + G ∧ Psi empty d = true) :
    ∃ t, t ≤ W + G ∧ evol x t 0 ≠ altCol t := by
  cases h0 : x 0 with
  | false =>
    refine ⟨0, by omega, ?_⟩
    show x 0 ≠ altCol 0
    rw [h0]; decide
  | true =>
    have hx : x = glue (fun k => x (-(k : Int))) empty := by
      funext p
      unfold glue
      by_cases hp : p < 0
      · rw [ite_eq_left hp]
        show x p = x (-(((-p).toNat : Nat) : Int))
        rw [show (-(((-p).toNat : Nat) : Int)) = p by omega]
      · rw [ite_eq_right hp]
        by_cases hp0 : p = 0
        · rw [ite_eq_left hp0, hp0, h0]
        · rw [ite_eq_right hp0, hR p (by omega)]; rfl
    obtain ⟨d0, hd0, hd0', hpsi⟩ := hgap
    obtain ⟨d, h1, h2, h3, h4⟩ := first_difference (fun k => x (-(k : Int))) d0
      ⟨d0, by omega, Nat.le_refl _, by rw [hpsi, hL _ (by omega)]; decide⟩
    refine ⟨d, by omega, ?_⟩
    rw [hx]
    exact (exact_death_center h1 h4 h3).2

/-! ### The computation

Column `-1` at times below `32768` and `Psi empty` at depths `1, …, 32768`, as numbers that the kernel checks in two
steps; then the gaps. -/

/-- Column `-1` at times `0, …, 32767`, bit `t` being time `t`. -/
def yBits : Nat :=
  0xf7fdff7fdff7fdf7fdff7fdff7fdff7fdff7fdff7dff7fdff7dff7fdff7dff7fdff7fdff7fdff7fdff7dff7fdff7fdff7fdff7fdff7fdff7fdff7fdff7fdff7fdff7fdff7fdff7fdff7fdff7fdff7fdff7fdff7dff7fdff7fdff7fdf7fdff7fdf7fdff7fdff7fdff7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdff7fdf7fdff7fdff7fdff7fdff7dff7fdff7fdff7dff7fdff7dff7fdff7fdff7dff7fdff7dff7fdff7fdff7dff7fdff7dff7fdff7dff7fdff7dff7fdff7fdff7fdff7dff7fdff7dff7fdff7dff7fdff7dff7fdff7fdff7dff7fdff7dff7fdff7dff7fdff7fdff7fdff7fdff7fdff7fdff7fdff7dff7fdff7dff7fdff7fdff7fdff7dff7fdff7dff7fdff7dff7fdff7fdff7dff7fdff7dff7fdff7fdff7dff7fdff7dff7fdff7dff7fdff7dff7fdff7fdff7dff7fdff7dff7fdff7dff7fdff7fdff7dff7fdff7fdff7fdff7fdff7dff7fdff7dff7dff7fdff7dff7fdff7fdff7fdff7fdff7dff7fdff7dff7fdff7dff7fdff7fdff7fdff7fdff7fdff7fdff7fdff7fdff7fdff7dff7fdff7dff7fdff7dff7fdff7dff7fdff7fdff7fdff7fdff7fdff7dff7fdff7fdff7dff7fdff7fdff7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdff7fdff7fdf7fdff7fdff7fdff7fdff7fdff7dff7fdff7dff7fdff7dff7fdff7fdff7dff7fdff7fdff7fdff7fdff7dff7fdff7dff7fdff7fdff7fdff7fdff7dff7fdff7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdff7fdff7fdff7fdff7fdff7fdf7fdff7fdff7fdff7fdff7fdf7fdff7fdff7fdff7fdf7fdff7fdff7fdff7fdff7fdff7dff7fdff7fdff7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdff7fdff7fdff7fdff7fdf7fdff7fdff7fdff7fdff7fdff7dff7fdff7dff7fdff7dff7fdff7dff7fdff7dff7fdff7dff7fdff7dff7fdff7dff7fdff7fdff7dff7fdff7dff7fdff7fdff7fdff7dff7fdff7dff7fdff7fdff7fdff7fdff7dff7fdff7fdff7fdff7fdff7fdff7fdff7dff7fdff7dff7fdff7fdff7dff7fdff7dff7fdff7dff7fdff7dff7fdff7dff7fdff7fdff7fdff7fdff7fdff7fdff7dff7fdff7fdff7fdff7fdff7fdff7fdff7fdff7fdff7dff7fdff7fdff7dff7fdff7fdff7fdff7fdff7fdf7fdf7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdff7dff7fdff7dff7fdff7fdff7fdff7fdff7fdff7dff7fdff7fdff7fdff7dff7fdff7dff7fdff7fdff7fdff7dff7fdff7dff7fdff7fdf7fdff7fdf7fdff7fdff7fdff7fdff7dff7fdff7dff7fdff7dff7fdff7fdff7fdff7fdff7fdff7fdff7fdff7fdff7dff7fdff7dff7fdff7fdff7dff7fdff7dff7fdff7fdff7fdff7fdff7fdf7fdff7fdf7fdff7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdff7fdff7fdff7fdf7fdff7fdff7fdff7fdff7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdff7fdff7fdff7dff7fdff7dff7fdff7fdff7fdff7fdff7fdff7fdff7fdff7fdff7fdff7fdff7fdff7dff7fdff7fdff7dff7fdff7dff7fdff7fdf7fdff7fdf7fdff7fdff7fdf7fdff7fdff7fdf7fdff7fdff7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdff7fdf7fdff7fdf7fdff7fdff7dff7fdff7fdff7dff7fdff7dff7fdff7dff7fdff7fdff7fdff7fdff7dff7fdff7dff7fdff7fdff7fdff7fdff7fdff7fdff7fdff7dff7fdff7dff7fdff7fdff7dff7fdff7dff7fdff7dff7fdff7fdff7fdff7fdff7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdff7fdff7fdf7fdff7fdff7fdf7fdff7fdf7fdff7fdff7fdff7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdff7fdff7fdf7fdff7fdff7fdff7fdff7fdff7dff7fdff7dff7fdff7dff7fdff7fdff7fdff7fdff7fdf7fdff7fdff7fdff7fdff7fdff7fdff7dff7fdff7dff7fdff7dff7fdff7dff7fdff7fdff7fdff7fdff7dff7fdff7fdff7fdff7fdff7fdf7fdff7fdff7fdff7fdff7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdff7fdf7fdff7fdf7fdff7fdff7fdff7fdff7fdf7fdff7fdff7fdff7fdff7fdff7dff7fdff7dff7fdff7fdff7dff7fdff7fdff7fdff7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdff7fdff7fdff7fdff7fdff7fdff7fdf7fdff7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdff7fdf7fdff7fdf7fdff7fdff7fdff7dff7fdff7dff7fdff7fdff7fdff7dff7fdff7fdff7dff7fdff7fdff7dff7fdff7dff7fdff7dff7fdff7dff7fdff7dff7fdff7dff7fdff7fdff7fdff7fdff7fdff7fdff7fdff7dff7fdff7dff7fdff7dff7fdff7dff7fdff7dff7fdff7dff7fdff7fdff7dff7fdff7dff7fdff7dff7fdff7fdff7dff7fdff7dff7fdff7dff7fdff7fdff7fdff7dff7fdff7fdff7fdff7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdff7fdff7fdff7fdff7fdff7fdf7fdff7fdff7fdff7fdff7fdff7dff7fdff7dff7fdff7fdff7fdff7fdff7dff7fdff7fdff7fdff7fdf7fdff7fdf7fdff7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdff7fdff7fdff7fdf7fdff7fdff7fdff7fdf7fdff7fdf7fdff7fdff7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdff7fdff7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdff7fdff7fdff7fdf7fdff7fdff7fdff7fdff7fdff7dff7fdff7fdff7fdff7fdff7fdf7fdff7fdff7fdff7dff7fdff7dff7fdff7fdff7fdff7fdff7fdff7dff7fdff7fdff7dff7fdff7dff7fdff7dff7fdff7dff7fdff7fdff7dff7fdff7dff7fdff7dff7fdff7dff7fdff7fdff7fdff7fdff7dff7fdff7dff7fdff7fdff7fdff7dff7fdff7fdff7fdff7fdff7fdff7fdff7fdff7fdf7fdff7fdff7fdff7fdf7fdff7fdf7fdff7fdff7dff7fdff7dff7fdff7fdff7dff7fdff7fdff7dff7fdff7dff7fdff7fdff7fdff7fdff7fdff7dff7fdff7fdff7fdff7fdff7fdff7fdff7fdff7dff7fdff7dff7fdff7dff7fdff7dff7fdff7fdff7dff7fdff7dff7fdff7dff7fdff7dff7dff7fdff7dff7fdff7dff7fdff7fdff7fdff7fdff7dff7fdff7dff7fdff7fdff7fdff7fdff7dff7fdff7dff7fdff7dff7fdff7fdff7fdff7fdff7fdff7dff7fdff7dff7fdff7fdff7fdff7fdff7dff7fdff7fdff7fdff7fdff7fdff7dff7fdff7dff7fdff7dff7fdff7dff7fdff7fdff7fdff7fdff7dff7fdff7fdff7fdff7fdff7dff7fdff7fdff7dff7fdff7dff7fdff7dff7fdff7fdff7fdff7dff7fdff7fdff7fdff7fdf7fdff7fdff7fdff7fdff7fdff7fdff7fdf7fdff7fdff7fdff7fdff7fdff7dff7fdff7dff7fdff7dff7fdff7fdff7fdff7fdff7fdf7fdff7fdf7fdff7fdff7fdf7fdff7fdff7fdff7fdf7fdff7fdf7fdff7fdff7fdff7fdff7fdff7fdff7fdff7fdff7fdff7fdff7fdff7fdff7fdff7fdff7fdf7fdff7fdf7fdff7fdff7fdff7fdff7fdff7fdff7fdff7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdff7fdf7fdff7fdff7fdff7fdff7fdff7dff7fdff7dff7fdff7fdff7fdff7fdf7fdff7fdff7fdff7fdff7fdff7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdff7fdff7fdff7fdff7fdff7fdff7dff7fdff7dff7fdff7dff7fdff7fdff7fdff7fdff7fdff7fdff7dff7fdff7fdff7dff7fdff7dff7fdff7dff7fdff7dff7fdff7fdff7fdff7fdff7fdff7fdff7dff7fdff7dff7fdff7fdff7fdff7fdff7fdff7fdff7fdff7dff7fdff7fdff7dff7fdff7dff7fdff7dff7fdff7fdff7dff7fdff7fdff7fdff7fdff7dff7fdff7dff7fdff7dff7fdff7dff7fdff7dff7fdff7dff7fdff7dff7fdff7dff7fdff7fdff7fdff7fdff7dff7fdff7dff7fdff7fdff7fdff7dff7fdff7fdff7fdff7fdff7fdff7fdf7fdff7fdf7fdff7fdff7fdff7fdff7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdff7fdff7fdff7fdff7fdff7fdff7fdf7fdff7fdf7fdff7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdff7fdf7fdff7fdf7fdff7fdff7fdff7fdf7fdff7fdf7fdff7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdff7fdff7fdff7fdff7fdff7fdf7fdff7fdff7fdf7fdff7fdf7fdff7fdff7fdff7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdff7fdff7fdff7dff7fdff7fdff7fdff7dff7fdff7dff7fdff7dff7fdff7fdff7fdff7fdff7dff7fdff7dff7fdff7dff7fdff7fdff7fdff7fdff7fdff7fdff7fdff7fdff7fdff7dff7fdff7dff7fdff7fdff7fdff7fdff7dff7fdff7dff7fdff7fdff7dff7fdff7dff7fdff7dff7fdff7fdff7fdff7fdff7fdff7fdff7fdff7fdff7fdff7fdf7fdff7fdf7fdff7fdff7fdff7fdf7fdff7fdff7fdff7fdf7fdff7fdff7fdff7fdff7fdff7dff7fdff7fdff7fdff7fdff7dff7fdff7dff7fdff7dff7fdff7dff7fdff7fdff7fdff7fdff7fdff7fdff7fdff7fdff7fdff7fdff7fdff7fdff7dff7fdff7dff7fdff7dff7fdff7dff7fdff7dff7fdff7fdff7dff7fdff7fdff7dff7fdff7dff7fdff7fdff7fdff7dff7fdff7dff7fdff7fdff7fdff7fdff7fdff7fdff7dff7fdff7dff7fdff7dff7fdff7dff7fdff7fdff7fdff7fdff7fdff7fdf7fdff7fdff7fdff7fdff7dff7fdff7dff7fdff7dff7fdff7fdff7fdff7fdff7fdff7fdff7fdff7fdff7fdff7fdff7fdff7fdff7fdff7fdff7fdff7dff7fdff7fdff7fdff7fdff7fdff7dff7fdff7fdff7fdff7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdff7dff7fdff7dff7fdff7fdff7dff7fdff7dff7fdff7fdff7fdff7fdff7fdff7fdf7fdff7fdff7fdff7fdff7fdff7dff7fdff7dff7fdff7dff7fdff7fdff7fdff7dff7fdff7fdff7dff7fdff7dff7fdff7dff7fdff7dff7fdff7fdff7fdff7fdff7fdff7fdf7fdf7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdf7fdf7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdff7fdf7fdff7fdff7fdff7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdff7fdff7fdff7fdf7fdff7fdff7fdff7fdff7fdff7dff7fdff7dff7fdff7fdff7dff7fdff7dff7fdff7fdff7dff7fdff7dff7fdff7dff7fdff7dff7fdff7dff7fdff7fdff7fdff7fdff7dff7fdff7dff7fdff7fdff7fdff7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdff7fdff7fdff7fdff7fdff7dff7fdff7dff7fdff7fdff7fdff7dff7fdff7dff7fdff7fdf7fdff7fdff7fdff7fdff7dff7fdff7dff7fdff7dff7fdff7fdff7fdff7fdff7fdff7fdf7fdff7fdff7fdff7fdff7fdf7fdff7fdff7fdff7fdf7fdff7fdf7fdff7fdf7fdff7fdff7fdff7fdff7fdff7dff7fdff7fdff7dff7fdff7dff7fdff7dff7fdff7dff7fdff7df7fddff77fddff77fddff77fddff77fddff77fddff77fddff77fddff77fddff77fddff77fddfd

/-- `Psi empty` at depths `1, …, 32768`, bit `d` being depth `d`. -/
def psiBitsLit : Nat :=
  0x1d5486d39a7c4aaffd0b53b8668b97b63ce03fb56cdb3a158ebf8f1520da3329e26904933daa7e00787cc2930c712271da8522a1ca0ec362479bfbde7f8b922587cad1a6d6055174c1e3cf16d8d35e2bda22f0e27addb6fbefc198caa520cc2cd63852f3b569870662c04f83ced568addb5b1144f41d3449620040629528c9995f7ec73a41e13fa8f95bf2e0b3acfe14a706e6d15ecd43e32e09bcd6c16d90561c7afc50448beb11e4fedcda2a1effc608670838eff739425fe5e8ed81950c8c44725902978dbb7dc34a64d749c8fa87e002227f42772182e6ae0724e5f4186b156f5d148bb62a0dc5ebffef29bba7804561a719d62a99846655da0818de286602816b90b1693e81ce2a3670cabaa52314cb1097fbc1d5cbaa833eba139e10d3c54bfa92606cec370a2ae91db895bb6904fa0c7d9b63df2307fdfc90d82b540e182dac9c84bde01fc3006b3b290538a6c4bb464d75fea82cf39865b9b472967d94d74ac515af77bc065d78439f37f534f3333bd55a634f0f9302f21baa0f0a70b364848a5a83de4d9fe3bdc3d5fbb385f45af467d080f770615b558f56c09ca583572b62a6df0b436bcaaadeb745a777c3184b979326d0d8d3106964cbecc3879194108318533f973a80cb468913b2ae3ed6917ccb71bf1237981d9f59515857d5e0a45c5ad4bf6012b0f519d13fda18c71655ac77fc750d448406a6243af61198a33c9938ef2ef325548c8fd9cfc267c4bfdc9c17c5674f50503711d9990f27aad1d6aee81761ff9891907a0f460e598807b2afce7a32541da8d1da918ea69702b4dbb49fffdb3b76e4f3c061601f02a26a66ddc9419d0f54425c180ccd21076db1479edd87853bacc877cce3de1f4c8f12c078bacb65375ec1761d4a0d0b310bc056688790d7bbadd6b00e122fe7857b042ae3d1d9d054180428ca6dbf22ce6bace6b9ad0eef1ddf6ef206fb1502c521d71e7c297f927ca6a6e7d9ee9cad29d99ebcf832094625071632d36bba923498221f670458f88b35970ad2be1d869f1fb7ec8d5ce90ceb23199b31ed32381a39933bb30724aece5bb91652b7b3ad5b8f77124738831c53a5fb47a0170bb5fc8a8b5484b0c9349c9414169779472f43800c1326ad1361aea72f8456f01d58e6807acf6ef817f308f02a2410e6b7bcd490b7b12a8004301ba5eca4e8e6bbb26d1c2a0159e75b605259729dd18390ee669d1ea75064828f2d49526c86f18bdfacf97968bfb6322b67ce45b5a0e38bd5fbda160164409af774830c4da3cb7ae360d0eb1a7533d12573c7af7ca018d8332f26918db433b6a0bce79324526a343ec6103571350b68fe7e9f5a6011d78479aab34f8ca2e464a45747ddac8612332c5a43f1058c18b5806f564ecc9ab1e67870109e91f62bb78cd1e9c5e8bc0abc57020ed8554670648eee77ad01581dda75942cc4148023d11988a8317d473b676c9637f12414497690bca82a7c900fda0aaea62623e1d4326ba399edfe01f0e8aa4de1dbc64db3b0a36aaac6f7cac51746d9eb1dabf1faa736067748f988cedf4acb02f52d23735bde6d6ac229580b8bc6c68c7ce186801b19736cc32e822ccbe8211baa14f67d7397326c250473fc247d9e951af467b2cded1769f1e3eb169dd9e141c75a244d0b1ed8751998ffc1c9df8e8912e2d5b9a90d5667a3343cf02426d2f260ff149500a7807de1ff8fffb4b675bce417f7cf6455b7fcc3f431f047e3c9bf348afa98e421be5e509511e1da5bc179e2ace6df9eaac01fe1e1f355e64f5a1401af4d822641ef30d8a3e2f2671157accc8cb6fe687e085ada513965b40fc479aa3cb2503fb0ef775652d4b3ca7987357a3e57e83dc8b7face69aaf3ba518e742e7068cd46c04f35999f880f21fc82208bc17e0639ac5219be7646fbcfbaa0a0b091d4df98dbee1090ef0cc6f2b5481a0f1666bb38a56d44278c529b7c1107127e49443ec1f15d3a652b6d0ec998db6523012df401e2cebfa0e257af8e0c4c3596d0557555e13e1460ce5dd1b25879c46afc3c93430582f7d26af975a814f6679d1e67463624e2692ecae4eee3e05a4ccb5386645f978ceef4bc776f5101298e0bd83b1df944197b06c3ede32b7767ca214c6608dd560347ff1fe5a9adcf85b7b64c2c82a6c5ba02ff0b688eeb29adf6a1cfab77679c5d6f130ab11dae0b6ed040558bf7f4286dbd4a89d156bf4498d13615a1d93a98d225e9bad966b2a89d2868c44560e86593ece02765f6140f8f423f7bc61a8b88b90e5c8e2eb6e747023eabdd37b9054c9ce275369e934dcb359260aa2ab4b7507297444d7f2d666765ddb8fbfb892c509638b081eae3cd07f95397a17ce4dd5f3fd72788c9c085bad2ce60f3524651133e0d06860f14dfc179526e05bcbcc01380d7d40d3e4082e42b0929f2f6d2532c02c58d96767addf2cfcb885b1cd2867a176941a4e7ade3fe9523c8b7cacfbda673360594ce6d544a4a12d5baf9618f65669645f96b45a1e238994e168072101a481af734dbe6be91702ee0333b1c706b194bf5cbde1cf051a8b21acb0ebc49b57188d8a7ed3f58049826ec45306e857fca16a68986218d941b99fb47eaaedef79e7c1e302ae0338bc4aa7636b868aa2aea2069e586df756b61994674530e2a41685cefaceef55f4e5d5be10a0a4ca064be88ffaf4e863543aae8717c744d5ef572a5d708bc098208ed876ec1f5a414a0692d923e0a9142c3dcbfb855844cb003d9c85df8277026b49db35e78f8dc3eb2658170ac7d65e772c7716cbd68a9b8f6f70d3c4d1ba1a20cb65b491dcffb04f2fd21884f0c32fa41dee319eadb8aecb4e8cc026e6dfe07cf3927dc0a5c4aaf640c78c76adac6001144e244de65702d2a5d0e028d18483f1b13ae1a38f61ca5c7202d76395cd8042e2df449e2126e4e204a1d5695158acaf9d0cdbc133891f13f4d9cc373a87b6d77633aedab603097185bb3e8732568f22714e8e4681739e217bf59f91ab23943e0db37aa19464b24bdaa846605da2be319b531d4e679227fa36424c1b68334c25d0f6e8d0ecdbaaf7fe312eedcaf60d8378db48762d9d5158f479691280afa5ddaba4cbbe5d839157e1bfcacf6fc9bc54a1211d4c384f0f59033327bdefc5f9463c3f3371a29372bbaac9cef531031fe03e0d9aa65b356b04d2fd7a4e4e4b3e91c54239b4bf7be099667544a0b95a156f91314a934f9a7393e9bd0a1f4dfae2446137bf37ad4d00a0ceff7c2eb30e46745beb0e7f873db5ca3468626ef05876e4b528cddc69afc972a596d877683b68806c4dddbbdf0f1d4ad5820912bdaa54daf95f073189f519bdd48951381200484d2ee91d4e5b8a381475cc9b12c6e3e9c5d892f5de298e21ee7c8e4e3a1f5d794bacd57fcc8c8fcdb14944ace531ebca01926fdff14bb30eafd6b1a8da0ee66acda56662b005ff6710c89b66fd44080d924c18c635e193b44209550e3ba27d21aacfdb032d680b3042bca60d4a35b7e900a1705be5458a375e1b592ed00b0771c9dbca100b6bc244489305cb9d3c9bc0f6b134ad79fa661fc10bd43cc44d6e7540dffa476151341618a0f3429d578b95615664b79199f3631609b6cdd3de6a9e1cc869ace62018a341096d8017201d6a59bbeab0063bfd1dc298e4454bf36a4c105ca47af5ab6acfb21e48478f0404b4396f3676b6a4ff1abc1de9579fa1b004b7f7f7a1aa5a6f08906f1f1248350bf3c57a5e30bb969a3da8268351413d41241cb0d206a56f1221beee07b1abf2a29d011124518e83478bd141c02ea26ebbd6f7f8b21a9ad4c18bfe5fafabbc5bce69c868cfc21367d755ff387622bf2912dc93cebdbbf2871e60ae6ae90bfa85aaab470ea4cfe1a249c3156fc26eed13ea820be9511daa410740e7beafd24811c09fd4fc2f0a839f7ccfdec59bcb99c539925cfe7a3cce357adaa19c2fa3c1283882527f47281487f5b81132fadd632cd39cbe436230f869827a5b4b7be77acea6f5e3eeaeeada5b00c38ab050cf7120b7d4cfb71f943fb7ea6a228648ff4f57fe3c845448b22a00637e1604e6f73afc89e2652aa8a8d81f6217dd315efc73a8f6977c41ea0c38b5a13e98c81065034d1877b5137ea8d1782dad43b54b39a275c797b9db5fac250f17430fa565f8642a0373a2af0954891fa6f42b952f41e6a449575cc0e2d66637b4a5660d1a8ee2587900ca32ece585fd3a68de639e44a0ec96b919cb188b92ce381760924d7d3e99424b322f3b5eec2b4c42dc4bea5e2408d615da4daf7c19455198828f4605e4c8275d4d15e86ed0026027f3b34adf6b1d9446b45a8cad8c5007f9b23bfe5b2017abc0159bff2e6c68bb58ee94c8945f744a1c1a03d9348633e506c8b3df9e0700b80391f28178d829bf4b0988979580269adca18d3a0c5447f6bbdd51185e8e499e80cea31a3007259ae594958319023bdd9666df20a82e769dbc7932149784738560a323e54b40e9fabbb783d4343f2fa0c4a2be9528e41f4047a380706ba8fc23cf1eee5ffe3c20c9bccddfaed3f64e79bf36ec5e2d416981327dfdf2a046cb5e694ca0eba2ce4fcd98f9d628ece28ea748e68cd5102408dbc56cd3230ec263b61c126b9f0a646aa942799631a1055b8de61bbdb9448e9c36db188e2d2351cf6bcdff22ce7af3a4583b1bc7e5775baebe2e3f9b97de90461f5ef54ff8058bc9d0e451d65750a90b61485635a1fa3129890b590a03ea5847960e5fc03d2327ff15c05800ff84d22e9db6af87685b57bd1d253ad3278a465650da5ba39151a732dd4a25093ef1f02740d0792643b12c38a498408305a5200af6f5a18d54ba38a1159c659a9bf7fbe515e066d489f22713ddeb0f1dae589513ee92b3d546c1b6d75327c6418b1e68b54370ca759afdb9c1f090e1178a5c5cce6b1838061f34f065f62099d710e52b94f5a047efe7f9ad714eaf8dfbafc03817ca2a1bf8570e6ac2b30d8eca50614312c903b7cf823f8d04201eb0e9d9b181ad90965ecae2211bd6b471850f55a212404cbb9462e541a5c26d87fcb86cff136fe82947c1448855c409d495e18777b90506dbea5944584114acb08dcad3b384f127fbeac2f9d0da160b54d3436e6e005e4f15b2bfd64e287b28bd6798396006f6a68a34b482c5838770eb4524f380754b931d741c6eb6f20e4da8110212ff11fa157280d5342e5d7a45402deb1c34269e692531d4edceb298716103403e150454ee3499d85d3c19ee83c80588e436e99fa442e07423c7666b48d1c49fb6ed6f3097ca31e205350c84b7ae971a303625ba3b0ef71aa16abc7f160e7964303d9aebc95ef5d05ebafed8bc1e808a090523b28376ef0a0aeee37b4c3903d17202984eaaa8bfdb23d3c0431b10e7d6bfd450cef3e531aaab823c5a560befe31624a9d9ff00d1bc40480a6c9b68513ebe645e9923b7b0faf4e6ba1581add8d28f4727f35097996bc33fea063c187835195688f5240fb3c497c0d68fe4b850b3c2e1410ae3e2367ad2a7db9d230f6748bbe464f8f2df6f3346dc344d057b703bfa678a8bcb5b3dae95d99eccc9a78d44969e8905f3a01dc9f14f8ead59d62856bf2fc3a15e2a9bea6a1432b6b6f48f3edc751a7e2d4c60b2b620bb3e4d4a1bcde6c3573201b69c2beb98d6776839220e136567c47741d1aa2ae7693e372569b457146be89ed9810a6dd08077b29ce2ea0f9665f4bbb6d0af49b893ac8cdc4b6799513c4cf6d7da0bacedd77266b9f6e5713415e4eb4dfbface6176141a66eb51ed9f6afbdba3ab3fb17fe13f3088c146c6

theorem yLoop_eq : yLoop 32768 0 0 0 = yBits := by decide +kernel

theorem psiLoop_eq : psiLoop 32768 1 0 yBits 0 = psiBitsLit := by decide +kernel

theorem gaps_eq : gapsCheck psiBitsLit 32768 13 32755 = true := by decide +kernel

/-- **The black cells of `Psi empty` are never 13 or more apart** up to depth 32768: every window of 13 depths beyond
`W < 32755` holds one. -/
theorem psi_empty_gaps (W : Nat) (hW : W < 32755) : ∃ d, W < d ∧ d ≤ W + 13 ∧ Psi empty d = true := by
  obtain ⟨d, h1, h2, h3⟩ := gaps_of_check psiBitsLit 32768 13 32755 (by decide) (by decide) gaps_eq W hW
  refine ⟨d, h1, h2, ?_⟩
  have hp : psiBits 32768 = psiBitsLit := by
    unfold psiBits
    rw [yLoop_eq, psiLoop_eq]
  rw [← psiBits_spec 32768 d (by omega) (by omega), hp]
  exact h3

/-- **No left half within depth `W < 32755` keeps the center alternating against the white right half**: the center
of every configuration whose cells right of it are white and whose cells left of `-W` are white leaves
`1, 0, 1, …` by time `W + 13`. -/
theorem white_right_leaves (x : Int → Bool) (W : Nat) (hW : W < 32755) (hR : ∀ p : Int, 0 < p → x p = false)
    (hL : ∀ p : Int, p < -(W : Int) → x p = false) : ∃ t, t ≤ W + 13 ∧ evol x t 0 ≠ altCol t :=
  leaves_by_gap x W 13 hR hL (psi_empty_gaps W hW)

end Rule30Open
