module

public import Rule30Open.Foundations.Official
public import Ruliology.CellularAutomata.Rule30StripeMeeting

/-!
# A right half of `B` cells gives at most `2^(B-1) + 1` center columns to each left part

Frame: the kit's `Rule30StripeMeeting` with center index `B`. A row white right of cell `B` is the number whose bit
`k` is cell `B - k`: bits `0 .. B - 1` are its right half (cells `B .. 1`), and `x / 2^B` is its left part (cells
`<= 0`; bit 0 of it is cell 0). `column B x t` is the center cell at time `t`, and `evolve_eq_phiRows` identifies the
frame with `evolve`.

Every row is related to a row whose cell `B` is black by one application of the kit's stripe relation, at time 0
(`time_zero_move`) or at time 1 (`time_one_move`), unless its right half is empty and its left part does not end in
`0 1`; the kit's `stripe_related_same_trace` gives equal center columns (`exists_odd_rep`). Hence:

* `right_half_columns`, `right_half_center_columns`: for every finite left part, the `2^B` rows with a right half
  inside `[1, B]` have at most `2^(B-1) + 1` center columns, and at most `2^(B-1)` when the left part ends in `0 1`
  (cell `-1` white, cell `0` black).
* `box_columns`, `box_center_columns`: the Rule 30 rows supported in `[-A, B]` (`A, B >= 1`) have at most
  `2^(A+B) + 3 * 2^(A-1)` center columns, each that of one of the explicit rows `boxRep A B i`.
* `center_eq_right_extension`: the official form for the single black cell.

`StripeClassCount` proves that the stripe relation itself gives exactly this many classes.

The natural-language argument is `StripeClasses.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

open Ruliology.CellularAutomata
open Ruliology.CellularAutomata.Rule30StripeMeeting

namespace StripeClasses

/-- The center column of the row `x` in the kit's frame with center index `c`. -/
def column (c x t : Nat) : Bool := (phiRows x t).testBit (c + t)

theorem phiRows_succ' (x t : Nat) : phiRows x (t + 1) = phiRows (Phi x) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      show Phi (phiRows x (t + 1)) = Phi (phiRows (Phi x) t)
      rw [ih]

/-- Time-zero soundness: the kit's theorem. -/
theorem column_eq_of_stripe {x y c : Nat} (h : StripeRelated x y c) (t : Nat) :
    column c x t = column c y t :=
  stripe_related_same_trace x y c h t

/-- Time-one soundness: equal cell 0 and a stripe relation after one step give equal center columns. -/
theorem column_eq_of_stripe_one {x y c : Nat} (h0 : x.testBit c = y.testBit c)
    (h1 : StripeRelated (Phi x) (Phi y) (c + 1)) (t : Nat) : column c x t = column c y t := by
  cases t with
  | zero => simpa [column, phiRows] using h0
  | succ s =>
      have h := stripe_related_same_trace (Phi x) (Phi y) (c + 1) h1 s
      unfold column
      rw [phiRows_succ', phiRows_succ', show c + (s + 1) = c + 1 + s by omega]
      exact h

/-! ## Bits of `2^k * H + low` -/

theorem testBit_hi {H k low i : Nat} (hl : low < 2 ^ k) (hi : k ≤ i) :
    (2 ^ k * H + low).testBit i = H.testBit (i - k) := by
  rw [Nat.testBit_two_pow_mul_add H hl i]
  simp [Nat.not_lt.mpr hi]

theorem testBit_lo {H k low i : Nat} (hl : low < 2 ^ k) (hi : i < k) :
    (2 ^ k * H + low).testBit i = low.testBit i := by
  rw [Nat.testBit_two_pow_mul_add H hl i]
  simp [hi]

theorem testBit_pow (m i : Nat) : (2 ^ m).testBit i = decide (i = m) := by
  rw [Nat.testBit_two_pow]
  by_cases h : i = m
  · subst h; simp
  · have h' : ¬ m = i := fun e => h e.symm
    simp [h, h']

/-! ## The stripe word ending with a black cell -/

/-- `stripeLow n`: the kit's stripe word of length `n` whose bit 0 is black, `1 (01)^k` or `1 1 (01)^k` read from
bit 0, as a number: bit `i < n` is black iff `i = 0` or `i + n` is odd. -/
def stripeLow : Nat → Nat
  | 0 => 0
  | 1 => 1
  | 2 => 3
  | n + 3 => stripeLow (n + 1) + 2 ^ (n + 2)

theorem stripeLow_lt : ∀ n, stripeLow n < 2 ^ n
  | 0 => by decide
  | 1 => by decide
  | 2 => by decide
  | n + 3 => by
      have ih := stripeLow_lt (n + 1)
      have e1 : 2 ^ (n + 2) = 2 * 2 ^ (n + 1) := by rw [Nat.pow_succ]; omega
      have e2 : 2 ^ (n + 3) = 2 * 2 ^ (n + 2) := by rw [Nat.pow_succ]; omega
      show stripeLow (n + 1) + 2 ^ (n + 2) < 2 ^ (n + 3)
      omega

theorem stripeLow_testBit : ∀ n i, (stripeLow n).testBit i = decide (i < n ∧ (i = 0 ∨ (i + n) % 2 = 1))
  | 0, i => by simp [stripeLow]
  | 1, i => by
      show (2 ^ 0).testBit i = _
      rw [testBit_pow]
      simp only [decide_eq_decide]
      omega
  | 2, i => by
      show (2 ^ 1 * 1 + 1).testBit i = _
      rw [Nat.testBit_two_pow_mul_add 1 (by decide) i]
      by_cases h : i < 1
      · simp only [h, ↓reduceIte]
        have : i = 0 := by omega
        subst this
        decide
      · simp only [h, ↓reduceIte]
        rw [show (1 : Nat) = 2 ^ 0 from rfl, testBit_pow]
        simp only [decide_eq_decide]
        omega
  | n + 3, i => by
      have ih := stripeLow_testBit (n + 1)
      show (stripeLow (n + 1) + 2 ^ (n + 2)).testBit i = _
      rw [Nat.add_comm, show 2 ^ (n + 2) + stripeLow (n + 1) = 2 ^ (n + 2) * 1 + stripeLow (n + 1) by omega,
        Nat.testBit_two_pow_mul_add 1 (Nat.lt_trans (stripeLow_lt (n + 1)) (Nat.pow_lt_pow_right (by decide)
          (by omega))) i]
      by_cases h : i < n + 2
      · simp only [h, ↓reduceIte, ih i, decide_eq_decide]
        omega
      · simp only [h, ↓reduceIte]
        rw [show (1 : Nat) = 2 ^ 0 from rfl, testBit_pow]
        simp only [decide_eq_decide]
        omega

/-! ## Stripe words as lists -/

theorem rowBits_congr {a b n : Nat} (h : ∀ i, i < n → a.testBit i = b.testBit i) :
    rowBits a n = rowBits b n := by
  unfold rowBits
  exact List.map_congr_left (fun i hi => h i (List.mem_range.mp hi))

theorem rowBits_zeros {a m : Nat} (hz : ∀ i, i < m → a.testBit i = false) :
    rowBits a m = List.replicate m false := by
  unfold rowBits
  rw [List.map_congr_left (g := fun _ => false) (fun i hi => hz i (List.mem_range.mp hi)), List.map_const',
    List.length_range]

theorem stripeWord_single_bit {a m : Nat} (hz : ∀ i, i < m → a.testBit i = false) (hm : a.testBit m = true) :
    StripeWord (rowBits a (m + 1)) := by
  rw [rowBits_succ, rowBits_zeros hz, hm]
  exact StripeWord.single _ (fun b hb => List.eq_of_mem_replicate hb)

theorem stripeWord_stripeLow : ∀ n, 1 ≤ n → StripeWord (rowBits (stripeLow n) n)
  | 0, h => absurd h (by decide)
  | 1, _ => by
      have e : rowBits (stripeLow 1) 1 = [] ++ [true] := by decide
      rw [e]
      exact StripeWord.single [] (fun b hb => by simp at hb)
  | 2, _ => by
      have e : rowBits (stripeLow 2) 2 = [] ++ [true, true] := by decide
      rw [e]
      exact StripeWord.double [] (fun b hb => by simp at hb)
  | n + 3, _ => by
      have ih := stripeWord_stripeLow (n + 1) (by omega)
      have e : rowBits (stripeLow (n + 3)) (n + 3) = rowBits (stripeLow (n + 1)) (n + 1) ++ [false, true] := by
        rw [rowBits_succ, rowBits_succ, stripeLow_testBit (n + 3) (n + 1), stripeLow_testBit (n + 3) (n + 2)]
        have h1 : decide (n + 1 < n + 3 ∧ (n + 1 = 0 ∨ (n + 1 + (n + 3)) % 2 = 1)) = false := by
          simp only [decide_eq_false_iff_not]; omega
        have h2 : decide (n + 2 < n + 3 ∧ (n + 2 = 0 ∨ (n + 2 + (n + 3)) % 2 = 1)) = true := by
          simp only [decide_eq_true_eq]; omega
        rw [h1, h2, List.append_assoc]
        congr 1
        apply rowBits_congr
        intro i hi
        rw [stripeLow_testBit, stripeLow_testBit]
        simp only [decide_eq_decide]
        omega
      rw [e]
      exact StripeWord.extend ih

/-! ## One step in bits -/

theorem Phi_bit (a i : Nat) : (Phi a).testBit i =
    xor (a.testBit i) ((decide (0 < i) && a.testBit (i - 1)) || (decide (1 < i) && a.testBit (i - 2))) := by
  rw [Phi_testBit]
  rfl

/-! ## The two moves -/

/-- Time zero: when the lowest black bit `m` of a row is followed by a white bit `m + 1`, the stripe word `0^m 1`
(read from bit 0) can be replaced by the stripe word of the same length ending with bit 0 black. -/
theorem time_zero_move (H m c : Nat) (hH : H % 2 = 0) (hm : m ≤ c) :
    StripeRelated (2 ^ (m + 1) * H + 2 ^ m) (2 ^ (m + 1) * H + stripeLow (m + 1)) c := by
  have hlx : 2 ^ m < 2 ^ (m + 1) := Nat.pow_lt_pow_right (by decide) (by omega)
  have hly : stripeLow (m + 1) < 2 ^ (m + 1) := stripeLow_lt (m + 1)
  refine Or.inr ⟨m, hm, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply stripeWord_single_bit
    · intro i hi
      rw [testBit_lo hlx (by omega), testBit_pow]
      simp only [decide_eq_false_iff_not]; omega
    · rw [testBit_lo hlx (by omega), testBit_pow]; simp
  · rw [rowBits_congr (b := stripeLow (m + 1)) (fun i hi => testBit_lo hly hi)]
    exact stripeWord_stripeLow (m + 1) (by omega)
  · rw [testBit_lo hlx (by omega), testBit_pow]; simp
  · rw [testBit_lo hly (by omega), stripeLow_testBit]
    simp only [decide_eq_true_eq]; omega
  · rw [testBit_hi hlx (by omega), Nat.sub_self, Nat.testBit_zero]
    simp only [decide_eq_false_iff_not]; omega
  · rw [testBit_hi hly (by omega), Nat.sub_self, Nat.testBit_zero]
    simp only [decide_eq_false_iff_not]; omega
  · intro i hi
    rw [testBit_hi hlx (by omega), testBit_hi hly (by omega)]

/-- Time one: when the lowest black bit `m >= 1` of a row is followed by a black bit `m + 1`, replacing bits
`0 .. m` (`0^m 1` read from bit 0) by `stripeLow m` (bit `m` white) gives a row with the same cell 0 that is
stripe-related to it after one step: both images carry stripe words on bits `0 .. m`. -/
theorem time_one_move (H m c : Nat) (hH : H % 2 = 1) (hm1 : 1 ≤ m) (hmc : m + 1 ≤ c) :
    (2 ^ (m + 1) * H + 2 ^ m).testBit c = (2 ^ (m + 1) * H + stripeLow m).testBit c ∧
    StripeRelated (Phi (2 ^ (m + 1) * H + 2 ^ m)) (Phi (2 ^ (m + 1) * H + stripeLow m)) (c + 1) := by
  have hlx : 2 ^ m < 2 ^ (m + 1) := Nat.pow_lt_pow_right (by decide) (by omega)
  have hly : stripeLow m < 2 ^ (m + 1) :=
    Nat.lt_trans (stripeLow_lt m) (Nat.pow_lt_pow_right (by decide) (by omega))
  -- the bits of the two rows
  have bx : ∀ i, (2 ^ (m + 1) * H + 2 ^ m).testBit i =
      if i < m + 1 then decide (i = m) else H.testBit (i - (m + 1)) := by
    intro i
    by_cases h : i < m + 1
    · rw [testBit_lo hlx h, testBit_pow]; simp [h]
    · rw [testBit_hi hlx (by omega)]; simp [h]
  have byy : ∀ i, (2 ^ (m + 1) * H + stripeLow m).testBit i =
      if i < m + 1 then decide (i < m ∧ (i = 0 ∨ (i + m) % 2 = 1)) else H.testBit (i - (m + 1)) := by
    intro i
    by_cases h : i < m + 1
    · rw [testBit_lo hly h, stripeLow_testBit]; simp [h]
    · rw [testBit_hi hly (by omega)]; simp [h]
  have hH0 : H.testBit 0 = true := by rw [Nat.testBit_zero]; simp [hH]
  refine ⟨?_, Or.inr ⟨m, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [bx, byy]
    have h : ¬ c < m + 1 := by omega
    simp [h]
  · -- the image of the first row: 0^m 1 on bits 0 .. m
    apply stripeWord_single_bit
    · intro i hi
      rw [Phi_bit, bx, bx, bx]
      have h0 : i < m + 1 := by omega
      have h1 : i - 1 < m + 1 := by omega
      have h2 : i - 2 < m + 1 := by omega
      simp only [h0, h1, h2, ↓reduceIte]
      have e0 : decide (i = m) = false := by simp only [decide_eq_false_iff_not]; omega
      have e1 : decide (i - 1 = m) = false := by simp only [decide_eq_false_iff_not]; omega
      have e2 : decide (i - 2 = m) = false := by simp only [decide_eq_false_iff_not]; omega
      rw [e0, e1, e2]
      simp
    · rw [Phi_bit, bx, bx, bx]
      have h0 : m < m + 1 := by omega
      have h1 : m - 1 < m + 1 := by omega
      have h2 : m - 2 < m + 1 := by omega
      simp only [h0, h1, h2, ↓reduceIte]
      have e1 : decide (m - 1 = m) = false := by simp only [decide_eq_false_iff_not]; omega
      have e2 : decide (m - 2 = m) = false := by simp only [decide_eq_false_iff_not]; omega
      rw [e1, e2]
      simp
  · -- the image of the second row: stripeLow (m + 1) on bits 0 .. m
    have e : rowBits (Phi (2 ^ (m + 1) * H + stripeLow m)) (m + 1) = rowBits (stripeLow (m + 1)) (m + 1) := by
      apply rowBits_congr
      intro i hi
      rw [Phi_bit, byy, byy, byy, stripeLow_testBit, ite_eq_left (show i < m + 1 by omega),
        ite_eq_left (show i - 1 < m + 1 by omega), ite_eq_left (show i - 2 < m + 1 by omega)]
      -- a Boolean identity: each decision is fixed by i = 0, i = 1, i = m and the parity of i + m
      by_cases i0 : i = 0
      · subst i0
        rw [decide_eq_true (show 0 < m ∧ (0 = 0 ∨ (0 + m) % 2 = 1) by omega),
          decide_eq_true (show 0 < m + 1 ∧ (0 = 0 ∨ (0 + (m + 1)) % 2 = 1) by omega)]
        rfl
      · by_cases him : i = m
        · subst him
          rw [decide_eq_false (show ¬ (i < i ∧ (i = 0 ∨ (i + i) % 2 = 1)) by omega),
            decide_eq_true (show 0 < i by omega),
            decide_eq_true (show i - 1 < i ∧ (i - 1 = 0 ∨ (i - 1 + i) % 2 = 1) by omega),
            decide_eq_true (show i < i + 1 ∧ (i = 0 ∨ (i + (i + 1)) % 2 = 1) by omega)]
          simp
        · by_cases p : (i + m) % 2 = 1
          · by_cases i1 : i = 1
            · -- bits 1 and 0 of stripeLow m are black
              subst i1
              rw [decide_eq_true (show 1 < m ∧ (1 = 0 ∨ (1 + m) % 2 = 1) by omega),
                decide_eq_true (show 1 - 1 < m ∧ (1 - 1 = 0 ∨ (1 - 1 + m) % 2 = 1) by omega),
                decide_eq_false (show ¬ (1 < m + 1 ∧ (1 = 0 ∨ (1 + (m + 1)) % 2 = 1)) by omega)]
              simp
            · -- bit i of stripeLow m is black, bit i - 2 too, bit i - 1 is white
              rw [decide_eq_true (show i < m ∧ (i = 0 ∨ (i + m) % 2 = 1) by omega),
                decide_eq_false (show ¬ (i - 1 < m ∧ (i - 1 = 0 ∨ (i - 1 + m) % 2 = 1)) by omega),
                decide_eq_true (show 1 < i by omega),
                decide_eq_true (show i - 2 < m ∧ (i - 2 = 0 ∨ (i - 2 + m) % 2 = 1) by omega),
                decide_eq_false (show ¬ (i < m + 1 ∧ (i = 0 ∨ (i + (m + 1)) % 2 = 1)) by omega)]
              simp
          · -- bit i of stripeLow m is white and bit i - 1 is black
            rw [decide_eq_false (show ¬ (i < m ∧ (i = 0 ∨ (i + m) % 2 = 1)) by omega),
              decide_eq_true (show 0 < i by omega),
              decide_eq_true (show i - 1 < m ∧ (i - 1 = 0 ∨ (i - 1 + m) % 2 = 1) by omega),
              decide_eq_true (show i < m + 1 ∧ (i = 0 ∨ (i + (m + 1)) % 2 = 1) by omega)]
            simp
    rw [e]
    exact stripeWord_stripeLow (m + 1) (by omega)
  · -- bit m of the first image is black
    rw [Phi_bit, bx, bx, bx]
    have h0 : m < m + 1 := by omega
    have h1 : m - 1 < m + 1 := by omega
    have h2 : m - 2 < m + 1 := by omega
    simp only [h0, h1, h2, ↓reduceIte]
    have e1 : decide (m - 1 = m) = false := by simp only [decide_eq_false_iff_not]; omega
    have e2 : decide (m - 2 = m) = false := by simp only [decide_eq_false_iff_not]; omega
    rw [e1, e2]
    simp
  · -- bit m of the second image is black
    rw [Phi_bit, byy, byy, byy]
    have h0 : m < m + 1 := by omega
    have h1 : m - 1 < m + 1 := by omega
    have h2 : m - 2 < m + 1 := by omega
    simp only [h0, h1, h2, ↓reduceIte]
    have e0 : decide (m < m ∧ (m = 0 ∨ (m + m) % 2 = 1)) = false := by
      simp only [decide_eq_false_iff_not]; omega
    have e1 : decide (m - 1 < m ∧ (m - 1 = 0 ∨ (m - 1 + m) % 2 = 1)) = true := by
      simp only [decide_eq_true_eq]; omega
    have e3 : decide (0 < m) = true := by simp only [decide_eq_true_eq]; omega
    rw [e0, e1, e3]
    simp
  · -- bit m + 1 of the first image is white
    rw [Phi_bit, bx, bx, bx]
    have h0 : ¬ m + 1 < m + 1 := by omega
    have h1 : m + 1 - 1 < m + 1 := by omega
    have h2 : m + 1 - 2 < m + 1 := by omega
    simp only [h0, h1, h2, ↓reduceIte, Nat.sub_self, hH0]
    have e1 : decide (m + 1 - 1 = m) = true := by simp only [decide_eq_true_eq]; omega
    rw [e1]
    simp
  · -- bit m + 1 of the second image is white
    rw [Phi_bit, byy, byy, byy]
    have h0 : ¬ m + 1 < m + 1 := by omega
    have h1 : m + 1 - 1 < m + 1 := by omega
    have h2 : m + 1 - 2 < m + 1 := by omega
    simp only [h0, h1, h2, ↓reduceIte, Nat.sub_self, hH0]
    have e2 : decide (m + 1 - 2 < m ∧ (m + 1 - 2 = 0 ∨ (m + 1 - 2 + m) % 2 = 1)) = true := by
      simp only [decide_eq_true_eq]; omega
    have e3 : decide (1 < m + 1) = true := by simp only [decide_eq_true_eq]; omega
    rw [e2, e3]
    simp
  · -- above bit m + 1 the images agree
    intro i hi
    rw [Phi_bit, Phi_bit, bx, bx, bx, byy, byy, byy]
    have h0 : ¬ i < m + 1 := by omega
    have h1 : ¬ i - 1 < m + 1 := by omega
    simp only [h0, h1, ↓reduceIte]
    by_cases h2 : i - 2 < m + 1
    · -- i = m + 2: bit m + 1 = bit 0 of H is black, so both ORs are true
      have hi2 : i - 1 - (m + 1) = 0 := by omega
      simp only [h2, ↓reduceIte, hi2, hH0]
      have q : decide (0 < i) = true := by simp only [decide_eq_true_eq]; omega
      rw [q]
      simp
    · simp only [h2, ↓reduceIte]

/-! ## Every row has the column of a row with cell `B` black, or of a row with an empty right half -/

/-- Every nonzero number is `2^(m+1) * H + 2^m`: `m` is its lowest black bit. -/
theorem exists_lowbit : ∀ x, x ≠ 0 → ∃ m H, x = 2 ^ (m + 1) * H + 2 ^ m := by
  intro x
  induction x using Nat.strongRecOn with
  | ind x ih =>
      intro hx
      rcases Nat.mod_two_eq_zero_or_one x with h | h
      · have hlt : x / 2 < x := by omega
        obtain ⟨m, H, e⟩ := ih (x / 2) hlt (by omega)
        refine ⟨m + 1, H, ?_⟩
        have e1 : 2 ^ (m + 1 + 1) = 2 * 2 ^ (m + 1) := by rw [Nat.pow_succ]; omega
        have e2 : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [Nat.pow_succ]; omega
        rw [e1, e2, Nat.mul_assoc, ← Nat.mul_add, ← e2, ← e]
        omega
      · exact ⟨0, x / 2, by rw [show 2 ^ (0 + 1) = 2 from rfl, show 2 ^ 0 = 1 from rfl]; omega⟩

theorem div_eq_of_testBit {x y B : Nat} (h : ∀ i, B ≤ i → x.testBit i = y.testBit i) :
    x / 2 ^ B = y / 2 ^ B := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_div_two_pow, Nat.testBit_div_two_pow]
  exact h (i + B) (by omega)

/-- Every row whose right half (bits `0 .. B - 1`) is nonempty, or whose right half is empty and whose left part
ends in `0 1` (bit `B` black, bit `B + 1` white), has the center column of a row with the same left part whose
cell `B` (bit 0) is black. One application of the stripe relation, at time 0 or at time 1, does it. -/
theorem exists_odd_rep (B x : Nat) (hB : 1 ≤ B)
    (hx : x % 2 ^ B ≠ 0 ∨ (x / 2 ^ B) % 4 = 1) :
    ∃ y, y % 2 = 1 ∧ y / 2 ^ B = x / 2 ^ B ∧ ∀ t, column B x t = column B y t := by
  rcases Nat.mod_two_eq_zero_or_one x with hx2 | hx2
  · have hx0 : x ≠ 0 := by
      intro h0
      subst h0
      rcases hx with h | h
      · exact h (Nat.zero_mod _)
      · simp at h
    obtain ⟨m, H, e⟩ := exists_lowbit x hx0
    have hm1 : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · subst h
        rw [e, show 2 ^ (0 + 1) = 2 from rfl, show 2 ^ 0 = 1 from rfl] at hx2
        omega
      · omega
    have hlx : 2 ^ m < 2 ^ (m + 1) := Nat.pow_lt_pow_right (by decide) (by omega)
    -- the lowest black bit is at most B
    have hmB : m ≤ B := by
      apply Nat.le_of_not_lt
      intro hBm
      have hz : x % 2 ^ B = 0 := by
        apply Nat.eq_of_testBit_eq
        intro i
        rw [Nat.testBit_mod_two_pow, Nat.zero_testBit, e]
        by_cases hi : i < B
        · rw [testBit_lo hlx (by omega), testBit_pow]
          simp only [hi, decide_true, Bool.true_and, decide_eq_false_iff_not]
          omega
        · simp [hi]
      have hq : (x / 2 ^ B) % 2 = 0 := by
        have : (x / 2 ^ B).testBit 0 = false := by
          rw [Nat.testBit_div_two_pow, Nat.zero_add, e, testBit_lo hlx (by omega), testBit_pow]
          simp only [decide_eq_false_iff_not]
          omega
        rw [Nat.testBit_zero] at this
        simpa using this
      rcases hx with h | h
      · exact h hz
      · omega
    rcases Nat.mod_two_eq_zero_or_one H with hH | hH
    · -- bit m + 1 white: the stripe relation at time 0
      have hly : stripeLow (m + 1) < 2 ^ (m + 1) := stripeLow_lt (m + 1)
      refine ⟨2 ^ (m + 1) * H + stripeLow (m + 1), ?_, ?_, ?_⟩
      · have h0 := testBit_lo (H := H) hly (show 0 < m + 1 by omega)
        rw [stripeLow_testBit, Nat.testBit_zero] at h0
        have : decide (0 < m + 1 ∧ (0 = 0 ∨ (0 + (m + 1)) % 2 = 1)) = true := decide_eq_true (by omega)
        rw [this] at h0
        simpa using h0
      · symm
        apply div_eq_of_testBit
        intro i hi
        rw [e]
        by_cases him : i = m
        · subst him
          rw [testBit_lo hlx (by omega), testBit_lo hly (by omega), testBit_pow, stripeLow_testBit]
          simp only [decide_true]
          exact (decide_eq_true (by omega)).symm
        · rw [testBit_hi hlx (by omega), testBit_hi hly (by omega)]
      · intro t
        rw [e]
        exact column_eq_of_stripe (time_zero_move H m B hH hmB) t
    · -- bit m + 1 black: then m < B, and the stripe relation holds at time 1
      have hmB' : m + 1 ≤ B := by
        apply Nat.lt_of_le_of_ne hmB
        intro hmeq
        subst hmeq
        have hz : x % 2 ^ m = 0 := by
          apply Nat.eq_of_testBit_eq
          intro i
          rw [Nat.testBit_mod_two_pow, Nat.zero_testBit, e]
          by_cases hi : i < m
          · rw [testBit_lo hlx (by omega), testBit_pow]
            simp only [hi, decide_true, Bool.true_and, decide_eq_false_iff_not]
            omega
          · simp [hi]
        have hq : (x / 2 ^ m) % 4 = 3 := by
          have hd : x / 2 ^ m = 2 * H + 1 := by
            rw [e, show 2 ^ (m + 1) * H + 2 ^ m = 2 ^ m * (2 * H + 1) by
              rw [Nat.pow_succ]; rw [Nat.mul_add, Nat.mul_one, Nat.mul_assoc, Nat.mul_comm 2 H]]
            exact Nat.mul_div_cancel_left _ (Nat.two_pow_pos m)
          omega
        rcases hx with h | h
        · exact h hz
        · omega
      have hly : stripeLow m < 2 ^ (m + 1) :=
        Nat.lt_trans (stripeLow_lt m) (Nat.pow_lt_pow_right (by decide) (by omega))
      obtain ⟨h0, h1⟩ := time_one_move H m B hH hm1 hmB'
      refine ⟨2 ^ (m + 1) * H + stripeLow m, ?_, ?_, ?_⟩
      · have h0' := testBit_lo (H := H) hly (show 0 < m + 1 by omega)
        rw [stripeLow_testBit, Nat.testBit_zero] at h0'
        have : decide (0 < m ∧ (0 = 0 ∨ (0 + m) % 2 = 1)) = true := decide_eq_true (by omega)
        rw [this] at h0'
        simpa using h0'
      · symm
        apply div_eq_of_testBit
        intro i hi
        rw [e, testBit_hi hlx (by omega), testBit_hi hly (by omega)]
      · intro t
        rw [e]
        exact column_eq_of_stripe_one h0 h1 t
  · exact ⟨x, hx2, rfl, fun _ => rfl⟩

end StripeClasses

/-- **A right half of `B` cells gives at most `2^(B-1) + 1` center columns to each left part.** Fix the left part
`lam` (cells `<= 0`; bit 0 of `lam` is cell 0). Every nonempty right half `rho` (cells `1 .. B`) gives the center column
of one of the `2^(B-1)` rows `lam` followed by a right half whose cell `B` is black, and so does the empty right half
when `lam` ends in `0 1` (`lam % 4 = 1`). So the `2^B` rows with left part `lam` have at most `2^(B-1) + 1` center
columns, and at most `2^(B-1)` when `lam % 4 = 1`. -/
theorem StripeClasses.right_half_columns (lam B rho : Nat) (hB : 1 ≤ B) (hrho : rho < 2 ^ B)
    (hne : rho ≠ 0 ∨ lam % 4 = 1) :
    ∃ i, i < 2 ^ (B - 1) ∧ ∀ t, column B (2 ^ B * lam + rho) t = column B (2 ^ B * lam + (2 * i + 1)) t := by
  have hpos : 0 < 2 ^ B := Nat.two_pow_pos B
  have hmod : (2 ^ B * lam + rho) % 2 ^ B = rho := by rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hrho]
  have hdiv : (2 ^ B * lam + rho) / 2 ^ B = lam := by
    rw [Nat.mul_add_div hpos, Nat.div_eq_of_lt hrho, Nat.add_zero]
  obtain ⟨y, hy1, hyd, hcol⟩ := exists_odd_rep B (2 ^ B * lam + rho) hB (by rw [hmod, hdiv]; exact hne)
  rw [hdiv] at hyd
  have hB2 : 2 ^ (B - 1) * 2 = 2 ^ B := Nat.two_pow_pred_mul_two (by omega)
  have hr : y % 2 ^ B < 2 ^ B := Nat.mod_lt _ hpos
  have hdvd : 2 ∣ 2 ^ B := ⟨2 ^ (B - 1), by rw [← hB2, Nat.mul_comm]⟩
  have hr2 : (y % 2 ^ B) % 2 = 1 := by rw [Nat.mod_mod_of_dvd y hdvd]; exact hy1
  refine ⟨(y % 2 ^ B) / 2, by omega, ?_⟩
  intro t
  rw [hcol t]
  congr 1
  have hy := Nat.div_add_mod y (2 ^ B)
  rw [hyd] at hy
  omega

namespace StripeClasses

/-- The left parts `lam % 4` that do not end in `0 1`, listed: 0, 2, 3. -/
def leftResidue (r : Nat) : Nat := if r = 0 then 0 else if r = 1 then 2 else 3

/-- The rows used as representatives of a box: the odd rows `2 i + 1` for `i < 2^(A+B)`, then the rows with an empty
right half whose left part `lam < 2^(A+1)` does not end in `0 1`, `lam = 4 q + r` with `r` in `0, 2, 3`. -/
def boxRep (A B i : Nat) : Nat :=
  if i < 2 ^ (A + B) then 2 * i + 1
  else 2 ^ B * (4 * ((i - 2 ^ (A + B)) / 3) + leftResidue ((i - 2 ^ (A + B)) % 3))

end StripeClasses

/-- **The rows supported in `[-A, B]` have at most `2^(A+B) + 3 * 2^(A-1)` distinct center columns** (`A, B >= 1`):
each has the center column of one of the rows `boxRep A B i`, `i < 2^(A+B) + 3 * 2^(A-1)`. -/
theorem StripeClasses.box_columns (A B x : Nat) (hA : 1 ≤ A) (hB : 1 ≤ B) (hx : x < 2 ^ (A + B + 1)) :
    ∃ i, i < 2 ^ (A + B) + 3 * 2 ^ (A - 1) ∧ ∀ t, column B x t = column B (boxRep A B i) t := by
  have hpos : 0 < 2 ^ B := Nat.two_pow_pos B
  have hlam : x / 2 ^ B < 2 ^ (A + 1) := by
    rw [Nat.div_lt_iff_lt_mul hpos, ← Nat.pow_add, show A + 1 + B = A + B + 1 by omega]; exact hx
  have hrho : x % 2 ^ B < 2 ^ B := Nat.mod_lt _ hpos
  have hxe : x = 2 ^ B * (x / 2 ^ B) + x % 2 ^ B := (Nat.div_add_mod x (2 ^ B)).symm
  generalize x / 2 ^ B = lam at hlam hxe
  generalize x % 2 ^ B = rho at hrho hxe
  subst hxe
  have hA4 : 2 ^ (A + 1) = 4 * 2 ^ (A - 1) := by
    rw [show A + 1 = (A - 1) + 2 by omega, Nat.pow_add]; omega
  have hB2 : 2 ^ (B - 1) * 2 = 2 ^ B := Nat.two_pow_pred_mul_two (by omega)
  by_cases hne : rho ≠ 0 ∨ lam % 4 = 1
  · obtain ⟨i, hi, hcol⟩ := right_half_columns lam B rho hB hrho hne
    -- the representative 2^B * lam + 2 i + 1 is the odd row with index 2^(B-1) * lam + i
    have hidx : 2 ^ (B - 1) * lam + i < 2 ^ (A + B) :=
      calc 2 ^ (B - 1) * lam + i < 2 ^ (B - 1) * lam + 2 ^ (B - 1) := Nat.add_lt_add_left hi _
        _ = 2 ^ (B - 1) * (lam + 1) := by rw [Nat.mul_add, Nat.mul_one]
        _ ≤ 2 ^ (B - 1) * 2 ^ (A + 1) := Nat.mul_le_mul_left _ hlam
        _ = 2 ^ (A + B) := by rw [← Nat.pow_add]; congr 1; omega
    refine ⟨2 ^ (B - 1) * lam + i, by omega, ?_⟩
    intro t
    have hrep : boxRep A B (2 ^ (B - 1) * lam + i) = 2 ^ B * lam + (2 * i + 1) := by
      unfold boxRep
      rw [ite_eq_left hidx, Nat.mul_add, ← Nat.mul_assoc, show 2 * 2 ^ (B - 1) = 2 ^ B by omega, Nat.add_assoc]
    rw [hrep]
    exact hcol t
  · -- an empty right half whose left part does not end in 0 1: the row is its own representative
    have h0 : rho = 0 := by omega
    have h1 : lam % 4 ≠ 1 := by omega
    subst h0
    obtain ⟨r, hr3, hlr⟩ : ∃ r, r < 3 ∧ 4 * (lam / 4) + leftResidue r = lam := by
      by_cases c0 : lam % 4 = 0
      · exact ⟨0, by decide, by show 4 * (lam / 4) + 0 = lam; omega⟩
      · by_cases c2 : lam % 4 = 2
        · exact ⟨1, by decide, by show 4 * (lam / 4) + 2 = lam; omega⟩
        · exact ⟨2, by decide, by show 4 * (lam / 4) + 3 = lam; omega⟩
    have hq : lam / 4 < 2 ^ (A - 1) := by omega
    refine ⟨2 ^ (A + B) + (3 * (lam / 4) + r), by omega, ?_⟩
    intro t
    have hrep : boxRep A B (2 ^ (A + B) + (3 * (lam / 4) + r)) = 2 ^ B * lam + 0 := by
      unfold boxRep
      rw [ite_eq_right (by omega), Nat.add_sub_cancel_left, show (3 * (lam / 4) + r) / 3 = lam / 4 by omega,
        show (3 * (lam / 4) + r) % 3 = r by omega, hlr, Nat.add_zero]
    rw [hrep]

namespace StripeClasses

/-! ## The frame is Rule 30: the statements for `evolve` -/

/-- A row white right of cell `m` stays white right of cell `m + t` at time `t`. -/
theorem white_right (init : Int → Bool) (m : Int) (hm : ∀ x : Int, m < x → init x = false) :
    ∀ t : Nat, ∀ x : Int, m + t < x → evolve init t x = false
  | 0, x, hx => hm x (by omega)
  | t + 1, x, hx => by
    show rule30 (evolve init t (x - 1)) (evolve init t x) (evolve init t (x + 1)) = false
    rw [white_right init m hm t (x - 1) (by omega), white_right init m hm t x (by omega),
      white_right init m hm t (x + 1) (by omega)]
    rfl

/-- **The kit's frame is Rule 30.** If the row `init` is white right of cell `c` and cell `c - j` is bit `j` of `a`,
then cell `c + t - j` at time `t` is bit `j` of the `t`-th image `phiRows a t`. -/
theorem evolve_eq_phiRows (init : Int → Bool) (c : Int) (a : Nat) (hw : ∀ x : Int, c < x → init x = false)
    (hb : ∀ j : Nat, init (c - j) = a.testBit j) :
    ∀ t : Nat, ∀ j : Nat, evolve init t (c + t - j) = (phiRows a t).testBit j
  | 0, j => by
    show init (c + ((0 : Nat) : Int) - j) = a.testBit j
    rw [show c + ((0 : Nat) : Int) - j = c - j by omega]
    exact hb j
  | t + 1, j => by
    have ih := evolve_eq_phiRows init c a hw hb t
    have hwt := white_right init c hw t
    show rule30 (evolve init t (c + ((t + 1 : Nat) : Int) - j - 1)) (evolve init t (c + ((t + 1 : Nat) : Int) - j))
      (evolve init t (c + ((t + 1 : Nat) : Int) - j + 1)) = (Phi (phiRows a t)).testBit j
    rw [Phi_testBit]
    match j with
    | 0 =>
      rw [show c + ((t + 1 : Nat) : Int) - ((0 : Nat) : Int) - 1 = c + t - ((0 : Nat) : Int) by omega, ih 0,
        hwt _ (by omega), hwt _ (by omega)]
      simp [rule30, before]
    | 1 =>
      rw [show c + ((t + 1 : Nat) : Int) - ((1 : Nat) : Int) - 1 = c + t - ((1 : Nat) : Int) by omega, ih 1,
        show c + ((t + 1 : Nat) : Int) - ((1 : Nat) : Int) = c + t - ((0 : Nat) : Int) by omega, ih 0,
        hwt _ (by omega)]
      simp [rule30, before]
    | j + 2 =>
      rw [show c + ((t + 1 : Nat) : Int) - ((j + 2 : Nat) : Int) + 1 = c + t - ((j : Nat) : Int) by omega, ih j,
        show c + ((t + 1 : Nat) : Int) - ((j + 2 : Nat) : Int) - 1 = c + t - ((j + 2 : Nat) : Int) by omega,
        ih (j + 2),
        show c + ((t + 1 : Nat) : Int) - ((j + 2 : Nat) : Int) = c + t - ((j + 1 : Nat) : Int) by omega, ih (j + 1)]
      simp [rule30, before]

/-- The center column of Rule 30 from `init` is the kit-frame column of `a`. -/
theorem evolve_center (init : Int → Bool) (c a : Nat) (hw : ∀ x : Int, (c : Int) < x → init x = false)
    (hb : ∀ j : Nat, init ((c : Int) - j) = a.testBit j) (t : Nat) : evolve init t 0 = column c a t := by
  have h := evolve_eq_phiRows init c a hw hb t (c + t)
  rw [show (c : Int) + (t : Int) - ((c + t : Nat) : Int) = 0 by omega] at h
  exact h

/-- The row whose cell `c - j` is bit `j` of `a`, white right of `c`. -/
def rowOf (c a : Nat) (x : Int) : Bool := decide (x ≤ (c : Int)) && a.testBit ((c : Int) - x).toNat

theorem rowOf_white (c a : Nat) (x : Int) (hx : (c : Int) < x) : rowOf c a x = false := by
  unfold rowOf
  rw [decide_eq_false (by omega)]
  rfl

theorem rowOf_bit (c a j : Nat) : rowOf c a ((c : Int) - j) = a.testBit j := by
  unfold rowOf
  rw [decide_eq_true (by omega), show ((c : Int) - ((c : Int) - (j : Int))).toNat = j by omega]
  rfl

theorem evolve_rowOf (c a t : Nat) : evolve (rowOf c a) t 0 = column c a t :=
  evolve_center (rowOf c a) c a (rowOf_white c a) (rowOf_bit c a) t

/-- The number whose bit `j < n` is cell `c - j` of `init`. -/
def rowNat (init : Int → Bool) (c : Int) : Nat → Nat
  | 0 => 0
  | n + 1 => 2 ^ n * (init (c - n)).toNat + rowNat init c n

theorem rowNat_lt (init : Int → Bool) (c : Int) : ∀ n, rowNat init c n < 2 ^ n
  | 0 => by show (0 : Nat) < 2 ^ 0; decide
  | n + 1 => by
    have ih := rowNat_lt init c n
    show 2 ^ n * (init (c - n)).toNat + rowNat init c n < 2 ^ (n + 1)
    rw [Nat.pow_succ]
    cases init (c - n) <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one] <;> omega

theorem rowNat_testBit (init : Int → Bool) (c : Int) :
    ∀ n j, (rowNat init c n).testBit j = (decide (j < n) && init (c - j))
  | 0, j => by simp [rowNat]
  | n + 1, j => by
    show (2 ^ n * (init (c - n)).toNat + rowNat init c n).testBit j = _
    rw [Nat.testBit_two_pow_mul_add _ (rowNat_lt init c n) j]
    by_cases h : j < n
    · rw [ite_eq_left h, rowNat_testBit init c n j, decide_eq_true h, decide_eq_true (by omega)]
    · rw [ite_eq_right h]
      by_cases hj : j = n
      · subst hj
        rw [Nat.sub_self, decide_eq_true (by omega)]
        cases init (c - j) <;> rfl
      · rw [decide_eq_false (by omega)]
        have hk : (init (c - n)).toNat < 2 ^ (j - n) :=
          Nat.lt_of_le_of_lt (by cases init (c - n) <;> simp)
            (Nat.one_lt_two_pow (by omega))
        rw [Nat.testBit_lt_two_pow hk]
        rfl

end StripeClasses

/-- **Every Rule 30 row supported in `[-A, B]` has the center column of one of `2^(A+B) + 3 * 2^(A-1)` explicit
rows** (`A, B >= 1`): the odd rows of the box (cell `B` black) and the rows with an empty right half whose left part
does not end in `0 1`. -/
theorem StripeClasses.box_center_columns (A B : Nat) (hA : 1 ≤ A) (hB : 1 ≤ B) (init : Int → Bool)
    (hsupp : ∀ x : Int, init x = true → -(A : Int) ≤ x ∧ x ≤ (B : Int)) :
    ∃ i, i < 2 ^ (A + B) + 3 * 2 ^ (A - 1) ∧
      ∀ t, evolve init t 0 = evolve (rowOf B (boxRep A B i)) t 0 := by
  have hw : ∀ x : Int, (B : Int) < x → init x = false := by
    intro x hx
    cases h : init x
    · rfl
    · have := hsupp x h; omega
  have hb : ∀ j : Nat, init ((B : Int) - j) = (rowNat init B (A + B + 1)).testBit j := by
    intro j
    rw [rowNat_testBit]
    by_cases hj : j < A + B + 1
    · rw [decide_eq_true hj]; rfl
    · rw [decide_eq_false hj]
      cases h : init ((B : Int) - j)
      · rfl
      · have := hsupp _ h; omega
  obtain ⟨i, hi, hcol⟩ := box_columns A B (rowNat init B (A + B + 1)) hA hB (rowNat_lt init B (A + B + 1))
  refine ⟨i, hi, fun t => ?_⟩
  rw [evolve_center init B _ hw hb t, hcol t, evolve_rowOf]

/-- **Per left part, in Rule 30 terms.** Rows with left part `lam` (cell `-k` is bit `k` of `lam`) and a right half
`rho` inside `[1, B]`: every nonempty `rho`, and the empty one when `lam % 4 = 1`, gives the center column of one of
the `2^(B-1)` rows whose right half has cell `B` black. -/
theorem StripeClasses.right_half_center_columns (lam B rho : Nat) (hB : 1 ≤ B) (hrho : rho < 2 ^ B)
    (hne : rho ≠ 0 ∨ lam % 4 = 1) :
    ∃ i, i < 2 ^ (B - 1) ∧
      ∀ t, evolve (rowOf B (2 ^ B * lam + rho)) t 0 = evolve (rowOf B (2 ^ B * lam + (2 * i + 1))) t 0 := by
  obtain ⟨i, hi, hcol⟩ := right_half_columns lam B rho hB hrho hne
  exact ⟨i, hi, fun t => by rw [evolve_rowOf, evolve_rowOf, hcol t]⟩

namespace StripeClasses

/-! ## The single black cell -/

/-- The single black cell is the row `2^B` in the frame with center index `B`. -/
theorem rowOf_single (B : Nat) : rowOf B (2 ^ B) = single := by
  funext x
  unfold rowOf single
  by_cases hx : x ≤ (B : Int)
  · rw [decide_eq_true hx, Bool.true_and, testBit_pow]
    simp only [decide_eq_decide]
    omega
  · rw [decide_eq_false hx, Bool.false_and]
    exact (decide_eq_false (by omega)).symm

end StripeClasses

/-- **Official form.** For every `B >= 1`, the prize's center column is the center column of a row made of the single
black cell and a right half inside `[1, B]` whose cell `B` is black; together with the `2^B - 1` other nonempty right
halves of the single cell, these rows have at most `2^(B-1)` center columns (`right_half_center_columns` with
`lam = 1`). -/
theorem StripeClasses.center_eq_right_extension (B : Nat) (hB : 1 ≤ B) :
    ∃ i, i < 2 ^ (B - 1) ∧ ∀ t, Rule30Prize.center t = evolve (rowOf B (2 ^ B + (2 * i + 1))) t 0 := by
  obtain ⟨i, hi, h⟩ := right_half_center_columns 1 B 0 hB (Nat.two_pow_pos B) (Or.inr rfl)
  refine ⟨i, hi, fun t => ?_⟩
  have e := h t
  rw [Nat.mul_one, Nat.add_zero, rowOf_single] at e
  rw [← evolve_single_center, e]

end Rule30Open
