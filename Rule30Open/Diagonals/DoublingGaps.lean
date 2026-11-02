module

public import Ruliology.CellularAutomata.Rule30Diagonals
public import Rule30Open.Diagonals.LeftMemory

/-!
# The white-step identity and the first gaps after a period doubling

Read the single cell's left diagonals `D j t = cell t (j - t)` (the kit's `Rule30Diagonals.D`), fed by
`D (j + 2) (t + 1) = D j t xor (D (j + 1) t || D (j + 2) t)` (`Rule30Diagonals.D_step`).

* `D_no_two_white`: two consecutive diagonals are never both white from some time on (the backward step would make
  every diagonal below them white, down to the black `D 0`).
* `D_white_iff_and` (the white-step identity): diagonal `j + 4` is white from some time on exactly when, from some
  time on, `D j t = (D (j + 1) t && D (j + 2) t)`. The forward direction is the kit main branch's
  `Rule30LeftAntiPeriod.D_white_prev_three`, reproved here because the pinned kit does not have it; the converse is
  new: behind `D j = D (j + 1) && D (j + 2)`, diagonal `j + 3` copies `j + 2` after a black cell of `j + 2`, and then
  diagonal `j + 4` is wiped by the next one.
* `D_doubling_odd_weight` (descent): if `D j` has period `P` from `T`, `D (j + 1)` is white from `T`, and the period
  of `D (j + 2)` is not eventually `P`, then `D j` has odd weight over a period (`LeftMemory.D_period_dichotomy`), and
  for `P = 2 Q` it does not have period `Q` from any time on: a doubling white diagonal is preceded by a diagonal of
  full period.
* `doublingGap_one`, `doublingGap_two`, `doublingGap_three`, `doublingGap_four`: on aligned words of period `2p`
  (bit `t` of a natural number is the cell at time `t mod 2p`), the pair map `F (A, B) = (B, C)` of the settled words
  run from `(0, Y)`, `Y` anti-periodic (`Y (t + p) = !Y t`) of least period `2p`, keeps its second word non-white for
  the first `m - 1` steps, with `m = 5, 21, 56, 88` for `p = 1, 2, 3, 4`, and some `Y` reaches the white word at step
  `m` (`doublingGap_exact`). Each is one `decide` over the words of at most 8 bits, checking at every step that the
  computed word solves the step relation.
* `D_doubling_gap`: the census is a statement about the single cell. If `D w` is white from `T` and `D (w + 1)` is
  anti-periodic with half-period `p = 1, 2` or `4` from `T`, then no diagonal `w + k` with `1 ≤ k < m(p)` is white
  from any time on, `m(p) = 5, 21, 88`. The words of the diagonals, read from time `T`, follow the checked orbit:
  each next diagonal agrees with the computed word from one period after a black cell of the diagonal before it.

The natural-language argument, and the census of `m(p)` to `p = 16` by computation, is `DoublingGaps.md`, beside
this file.
-/

@[expose] public section

namespace Rule30Open

open Ruliology.CellularAutomata.Rule30Diagonals

namespace DoublingGaps

/-! ## The backward step and two consecutive white diagonals -/

/-- The step read backward: `D j t = D (j + 2) (t + 1) xor (D (j + 1) t || D (j + 2) t)`. -/
theorem back (j t : Nat) : D j t = xor (D (j + 2) (t + 1)) (D (j + 1) t || D (j + 2) t) := by
  rw [D_step j t]
  cases D j t <;> cases (D (j + 1) t || D (j + 2) t) <;> rfl

/-- Two white diagonals `i + 1`, `i + 2` make diagonal `i` white. -/
theorem white_down (i T : Nat) (h1 : ∀ t, T ≤ t → D (i + 1) t = false)
    (h2 : ∀ t, T ≤ t → D (i + 2) t = false) : ∀ t, T ≤ t → D i t = false := by
  intro t ht
  rw [back i t, h1 t ht, h2 t ht, h2 (t + 1) (by omega)]
  rfl

theorem no_two_white : ∀ i T, (∀ t, T ≤ t → D i t = false) → (∀ t, T ≤ t → D (i + 1) t = false) → False
  | 0, T, h0, _ => by
    have h := h0 T (Nat.le_refl T)
    rw [D_zero] at h
    exact Bool.noConfusion h
  | i + 1, T, h1, h2 => no_two_white i T (white_down i T h1 h2) h1

/-- If diagonal `j + 2` is white from `s` on, then `D j t = D (j + 1) t` there. -/
theorem eq_of_white_two {j s : Nat} (hw : ∀ t, s ≤ t → D (j + 2) t = false) :
    ∀ t, s ≤ t → D j t = D (j + 1) t := by
  intro t ht
  have h := D_step j t
  rw [hw (t + 1) (by omega), hw t ht] at h
  revert h
  cases D j t <;> cases D (j + 1) t <;> decide

end DoublingGaps

open DoublingGaps

/-- **No two consecutive white diagonals.** -/
theorem D_no_two_white (i : Nat) :
    ¬ ((∃ T, ∀ t, T ≤ t → D i t = false) ∧ ∃ T, ∀ t, T ≤ t → D (i + 1) t = false) := by
  rintro ⟨⟨T1, h1⟩, ⟨T2, h2⟩⟩
  exact no_two_white i (max T1 T2) (fun t ht => h1 t (by omega)) (fun t ht => h2 t (by omega))

namespace DoublingGaps

/-- The forward direction of the white-step identity (the kit main branch's `D_white_prev_three`). -/
theorem and_of_white {j s : Nat} (hw : ∀ t, s ≤ t → D (j + 4) t = false) :
    ∀ t, s ≤ t → D j t = (D (j + 1) t && D (j + 2) t) := by
  have h23 : ∀ u, s ≤ u → D (j + 2) u = D (j + 3) u :=
    eq_of_white_two (j := j + 2) (fun t ht => hw t ht)
  have h1 : ∀ u, s ≤ u → D (j + 1) u = xor (D (j + 3) u) (D (j + 3) (u + 1)) := by
    intro u hu
    have h := D_step (j + 1) u
    rw [show j + 1 + 2 = j + 3 by omega, show j + 1 + 1 = j + 2 by omega, h23 u hu] at h
    rw [h]
    generalize D (j + 1) u = a
    generalize D (j + 3) u = x
    cases a <;> cases x <;> rfl
  intro t ht
  have h := D_step j t
  rw [h23 (t + 1) (by omega), h23 t ht, h1 t ht] at h
  rw [h1 t ht, h23 t ht]
  revert h
  generalize D j t = a
  generalize D (j + 3) t = x
  generalize D (j + 3) (t + 1) = y
  cases a <;> cases x <;> cases y <;> decide

/-- Behind `D j = D (j + 1) && D (j + 2)`, diagonal `j + 1` is the change of diagonal `j + 2`. -/
theorem change_of_and {j s : Nat} (hand : ∀ t, s ≤ t → D j t = (D (j + 1) t && D (j + 2) t)) :
    ∀ u, s ≤ u → D (j + 1) u = xor (D (j + 2) u) (D (j + 2) (u + 1)) := by
  intro u hu
  have h := D_step j u
  rw [hand u hu] at h
  rw [h]
  generalize D (j + 1) u = a
  generalize D (j + 2) u = b
  cases a <;> cases b <;> rfl

/-- One step of the copy: if `D (j + 2) u` is black or diagonal `j + 3` already agrees with `j + 2` at `u`, it
agrees at `u + 1`. -/
theorem copy_step {j s : Nat} (hand : ∀ t, s ≤ t → D j t = (D (j + 1) t && D (j + 2) t)) (u : Nat) (hu : s ≤ u)
    (h : D (j + 2) u = true ∨ D (j + 3) u = D (j + 2) u) : D (j + 3) (u + 1) = D (j + 2) (u + 1) := by
  have hs := D_step (j + 1) u
  rw [show j + 1 + 2 = j + 3 by omega, show j + 1 + 1 = j + 2 by omega, change_of_and hand u hu] at hs
  rw [hs]
  rcases h with h | h
  · rw [h]
    generalize D (j + 2) (u + 1) = b'
    generalize D (j + 3) u = y
    cases b' <;> cases y <;> rfl
  · rw [h]
    generalize D (j + 2) (u + 1) = b'
    generalize D (j + 2) u = b
    cases b <;> cases b' <;> rfl

/-- The converse direction, with two black cells of diagonal `j + 2` named. -/
theorem white_of_and {j s : Nat} (hand : ∀ t, s ≤ t → D j t = (D (j + 1) t && D (j + 2) t))
    (r₁ : Nat) (hr₁ : s ≤ r₁) (hb₁ : D (j + 2) r₁ = true)
    (r₂ : Nat) (hr₂ : r₁ + 1 ≤ r₂) (hb₂ : D (j + 2) r₂ = true) :
    ∀ t, r₂ + 1 ≤ t → D (j + 4) t = false := by
  have copy : ∀ d, D (j + 3) (r₁ + 1 + d) = D (j + 2) (r₁ + 1 + d) := by
    intro d
    induction d with
    | zero => exact copy_step hand r₁ hr₁ (Or.inl hb₁)
    | succ d ih =>
      rw [show r₁ + 1 + (d + 1) = r₁ + 1 + d + 1 by omega]
      exact copy_step hand (r₁ + 1 + d) (by omega) (Or.inr ih)
  have wipe : ∀ u, r₁ + 1 ≤ u → D (j + 4) (u + 1) = (!D (j + 2) u && D (j + 4) u) := by
    intro u hu
    have h := D_step (j + 2) u
    rw [show j + 2 + 2 = j + 4 by omega, show j + 2 + 1 = j + 3 by omega] at h
    have hc := copy (u - (r₁ + 1))
    rw [show r₁ + 1 + (u - (r₁ + 1)) = u by omega] at hc
    rw [h, hc]
    generalize D (j + 2) u = b
    generalize D (j + 4) u = f
    cases b <;> cases f <;> rfl
  have stay : ∀ d, D (j + 4) (r₂ + 1 + d) = false := by
    intro d
    induction d with
    | zero => rw [Nat.add_zero, wipe r₂ (by omega), hb₂]; rfl
    | succ d ih =>
      rw [show r₂ + 1 + (d + 1) = r₂ + 1 + d + 1 by omega, wipe (r₂ + 1 + d) (by omega), ih]
      generalize D (j + 2) (r₂ + 1 + d) = b
      cases b <;> rfl
  intro t ht
  have := stay (t - (r₂ + 1))
  rwa [show r₂ + 1 + (t - (r₂ + 1)) = t by omega] at this

end DoublingGaps

/-- **The white-step identity.** Diagonal `j + 4` is eventually white exactly when, eventually,
`D j t = (D (j + 1) t && D (j + 2) t)`. -/
theorem D_white_iff_and (j : Nat) :
    (∃ s, ∀ t, s ≤ t → D (j + 4) t = false) ↔ ∃ s, ∀ t, s ≤ t → D j t = (D (j + 1) t && D (j + 2) t) := by
  constructor
  · rintro ⟨s, hw⟩
    exact ⟨s, and_of_white hw⟩
  · rintro ⟨s, hand⟩
    have black : ∀ T, ∃ r, T ≤ r ∧ D (j + 2) r = true := by
      intro T
      by_cases h : ∃ r, T ≤ r ∧ D (j + 2) r = true
      · exact h
      · exfalso
        have hw2 : ∀ r, max s T ≤ r → D (j + 2) r = false := fun r hr => by
          cases hc : D (j + 2) r with
          | false => rfl
          | true => exact absurd ⟨r, by omega, hc⟩ h
        have hw1 : ∀ r, max s T ≤ r → D (j + 1) r = false := fun r hr => by
          rw [change_of_and hand r (by omega), hw2 r hr, hw2 (r + 1) (by omega)]
          rfl
        exact no_two_white (j + 1) (max s T) hw1 hw2
    obtain ⟨r₁, hr₁, hb₁⟩ := black s
    obtain ⟨r₂, hr₂, hb₂⟩ := black (r₁ + 1)
    exact ⟨r₂ + 1, white_of_and hand r₁ hr₁ hb₁ r₂ hr₂ hb₂⟩

namespace DoublingGaps

/-! ## Descent: a doubling needs a diagonal of odd weight and full period -/

theorem windowParity_add (f : Nat → Bool) (t m : Nat) :
    ∀ n, windowParity f t (m + n) = xor (windowParity f t m) (windowParity f (t + m) n)
  | 0 => by
    show windowParity f t m = xor (windowParity f t m) false
    generalize windowParity f t m = a
    cases a <;> rfl
  | n + 1 => by
    show xor (windowParity f t (m + n)) (f (t + (m + n))) =
      xor (windowParity f t m) (xor (windowParity f (t + m) n) (f (t + m + n)))
    rw [windowParity_add f t m n, show t + (m + n) = t + m + n by omega]
    generalize windowParity f t m = a
    generalize windowParity f (t + m) n = b
    generalize f (t + m + n) = c
    cases a <;> cases b <;> cases c <;> rfl

/-- A sequence of period `Q` has even weight over `2 Q` consecutive times. -/
theorem windowParity_double (f : Nat → Bool) (T Q : Nat) (hf : ∀ t, T ≤ t → f (t + Q) = f t) :
    windowParity f T (2 * Q) = false := by
  rw [show 2 * Q = Q + Q by omega, windowParity_add, windowParity_periodic f T Q hf (T + Q) (by omega)]
  generalize windowParity f T Q = a
  cases a <;> rfl

end DoublingGaps

/-- **Descent.** If `D j` has period `P` from `T`, `D (j + 1)` is white from `T`, and `D (j + 2)` does not have
period `P` from any time on, then `D j` has odd weight over a period, and for `P = 2 Q` it does not have period `Q`
from any time on. -/
theorem D_doubling_odd_weight (j T P : Nat) (hj : ∀ t, T ≤ t → D j (t + P) = D j t)
    (hw : ∀ t, T ≤ t → D (j + 1) t = false)
    (hnot : ¬ ∃ T', ∀ t, T' ≤ t → D (j + 2) (t + P) = D (j + 2) t) :
    windowParity (D j) T P = true ∧ ∀ Q, P = 2 * Q → ¬ ∃ T', ∀ t, T' ≤ t → D j (t + Q) = D j t := by
  have hj1 : ∀ t, T ≤ t → D (j + 1) (t + P) = D (j + 1) t := fun t ht => by
    rw [hw (t + P) (by omega), hw t ht]
  have odd : windowParity (D j) T P = true := by
    rcases D_period_dichotomy j T P hj hj1 with h | ⟨_, hp, _⟩
    · exact absurd h hnot
    · exact hp
  refine ⟨odd, fun Q hQ => ?_⟩
  rintro ⟨T', hT'⟩
  have h1 := windowParity_double (D j) (max T T') Q (fun t ht => hT' t (by omega))
  rw [← hQ, windowParity_periodic (D j) T P hj (max T T') (by omega), odd] at h1
  exact Bool.noConfusion h1

namespace DoublingGaps

/-! ## Words of period `P` as natural numbers, and the pair map -/

/-- Bit `t` of a natural number: the cell at time `t` of a word. -/
def bit (w t : Nat) : Bool := w / 2 ^ t % 2 == 1

/-- The cells at times `0 .. P - 1` as a word, least time in the lowest bit. -/
def word (f : Nat → Bool) : Nat → Nat → Nat
  | _, 0 => 0
  | T, n + 1 => (f T).toNat + 2 * word f (T + 1) n

/-- The first time `t < P` with a black cell of `b` (0 if none). -/
def low (P b : Nat) : Nat := ((List.range P).find? (fun t => bit b t)).getD 0

/-- `n` more cells of the next word from time `t`, whose cell there is `cur`, onto the bits `c` already set. -/
def fill (P a b : Nat) : Nat → Nat → Bool → Nat → Nat
  | 0, _, _, c => c
  | n + 1, t, cur, c =>
    fill P a b n (t + 1) (xor (bit a (t % P)) (bit b (t % P) || cur)) (if cur then c + 2 ^ (t % P) else c)

/-- The pair map's next word: reset to `!a r` after the first black cell `r` of `b`, then one turn of the step. -/
def next (P a b : Nat) : Nat := fill P a b P (low P b + 1) (!bit a (low P b)) 0

/-- Whether `c` solves the step relation `c (t + 1) = a t xor (b t || c t)` around the cycle of length `P`. -/
def stepOK (P a b c : Nat) : Bool :=
  (List.range P).all fun t => bit c ((t + 1) % P) == xor (bit a t) (bit b t || bit c t)

/-- Whether the next `n` second words from `(a, b)` are not white, each next word solving the step relation. -/
def regimeOK (P : Nat) : Nat → Nat → Nat → Bool
  | 0, _, _ => true
  | n + 1, a, b => (List.range P).any (bit b) && stepOK P a b (next P a b) && regimeOK P n b (next P a b)

/-- The gap of the regime from `(a, b)` at step `k`: the first `k' + 1` with a white word (`k + fuel` if none). -/
def firstWhite (P : Nat) : Nat → Nat → Nat → Nat → Nat
  | 0, k, _, _ => k
  | n + 1, k, a, b => if next P a b = 0 then k + 1 else firstWhite P n (k + 1) b (next P a b)

/-- `y` of period `2 p` is anti-periodic: `y (t + p) = !y t`. -/
def anti (p y : Nat) : Bool := (List.range p).all fun t => bit y (t + p) == !bit y t

end DoublingGaps

/-! ## The census for `p ≤ 4` -/

theorem doublingGap_one : ∀ y, y < 2 ^ 2 → anti 1 y = true → regimeOK 2 4 0 y = true := by
  decide +kernel

theorem doublingGap_two : ∀ y, y < 2 ^ 4 → anti 2 y = true → regimeOK 4 20 0 y = true := by
  decide +kernel

/-- At `p = 3` the words `010101` and `101010` are anti-periodic of least period 2 and are left out. -/
theorem doublingGap_three :
    ∀ y, y < 2 ^ 6 → anti 3 y = true → y ≠ 21 → y ≠ 42 → regimeOK 6 55 0 y = true := by
  decide +kernel

theorem doublingGap_four : ∀ y, y < 2 ^ 8 → anti 4 y = true → regimeOK 8 87 0 y = true := by
  decide +kernel

/-- The bounds are attained, by `Y = 1^p 0^p`. -/
theorem doublingGap_exact :
    firstWhite 2 10 1 0 1 = 5 ∧ firstWhite 4 30 1 0 3 = 21 ∧ firstWhite 6 60 1 0 7 = 56 ∧
      firstWhite 8 100 1 0 15 = 88 := by
  decide +kernel

namespace DoublingGaps

/-! ## From the words to the diagonals -/

theorem bit_zero (t : Nat) : bit 0 t = false := by
  simp [bit]

theorem bit_add_two_mul (b m : Nat) (hb : b ≤ 1) : ∀ t, bit (b + 2 * m) (t + 1) = bit m t := by
  intro t
  unfold bit
  rw [Nat.pow_succ', ← Nat.div_div_eq_div_mul, show (b + 2 * m) / 2 = m by omega]

theorem toNat_le (b : Bool) : b.toNat ≤ 1 := by
  cases b <;> decide

theorem bit_toNat_add (b : Bool) (m : Nat) : bit (b.toNat + 2 * m) 0 = b := by
  cases b
  · show ((0 + 2 * m) / 2 ^ 0 % 2 == 1) = false
    rw [Nat.pow_zero, Nat.div_one, show (0 + 2 * m) % 2 = 0 by omega]
    rfl
  · show ((1 + 2 * m) / 2 ^ 0 % 2 == 1) = true
    rw [Nat.pow_zero, Nat.div_one, show (1 + 2 * m) % 2 = 1 by omega]
    rfl

theorem bit_word (f : Nat → Bool) : ∀ n T t, t < n → bit (word f T n) t = f (T + t)
  | 0, _, _, ht => absurd ht (Nat.not_lt_zero _)
  | n + 1, T, 0, _ => by
    show bit ((f T).toNat + 2 * word f (T + 1) n) 0 = f (T + 0)
    rw [bit_toNat_add, Nat.add_zero]
  | n + 1, T, t + 1, ht => by
    show bit ((f T).toNat + 2 * word f (T + 1) n) (t + 1) = f (T + (t + 1))
    rw [bit_add_two_mul _ _ (toNat_le _), bit_word f n (T + 1) t (by omega),
      show T + 1 + t = T + (t + 1) by omega]

theorem word_lt (f : Nat → Bool) : ∀ n T, word f T n < 2 ^ n
  | 0, _ => by show 0 < 2 ^ 0; decide
  | n + 1, T => by
    show (f T).toNat + 2 * word f (T + 1) n < 2 ^ (n + 1)
    have := word_lt f n (T + 1)
    have := toNat_le (f T)
    rw [Nat.pow_succ]
    omega

/-- A sequence of period `P` from `T`, read through its word at `T`. -/
theorem eq_bit_word {f : Nat → Bool} {T P : Nat} (hP : 0 < P) (hf : ∀ t, T ≤ t → f (t + P) = f t) (t : Nat) :
    f (T + t) = bit (word f T P) (t % P) := by
  rw [bit_word f P T (t % P) (Nat.mod_lt t hP)]
  have key : ∀ k, f (T + t % P + P * k) = f (T + t % P) := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [show T + t % P + P * (k + 1) = T + t % P + P * k + P by rw [Nat.mul_succ]; omega,
        hf (T + t % P + P * k) (by omega), ih]
  have := key (t / P)
  rwa [Nat.add_assoc, Nat.mod_add_div] at this

theorem mod_succ (t P : Nat) : (t % P + 1) % P = (t + 1) % P := by
  rw [Nat.add_mod t 1 P, Nat.add_mod (t % P) 1 P, Nat.mod_mod]

theorem step_of_stepOK {P a b c : Nat} (hP : 0 < P) (h : stepOK P a b c = true) (t : Nat) :
    bit c ((t + 1) % P) = xor (bit a (t % P)) (bit b (t % P) || bit c (t % P)) := by
  simp only [stepOK, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  have := h (t % P) (Nat.mod_lt t hP)
  rw [mod_succ] at this
  exact this

/-- Each next diagonal follows the computed word, from one turn after a black cell of the diagonal before it. -/
theorem follow {P a b c j T s : Nat} (hP : 0 < P) (hstep : stepOK P a b c = true)
    (r : Nat) (hr : r < P) (hbr : bit b r = true)
    (ha : ∀ t, s ≤ t → D j (T + t) = bit a (t % P)) (hb : ∀ t, s ≤ t → D (j + 1) (T + t) = bit b (t % P)) :
    ∀ t, r + P * s + 1 ≤ t → D (j + 2) (T + t) = bit c (t % P) := by
  have hs : s ≤ r + P * s := by
    have : s ≤ P * s := Nat.le_mul_of_pos_left s hP
    omega
  have hmod : (r + P * s) % P = r := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
  have key : ∀ d, D (j + 2) (T + (r + P * s + 1 + d)) = bit c ((r + P * s + 1 + d) % P) := by
    intro d
    induction d with
    | zero =>
      have h := D_step j (T + (r + P * s))
      rw [ha _ hs, hb _ hs, hmod, hbr] at h
      have hc := step_of_stepOK hP hstep (r + P * s)
      rw [hmod, hbr] at hc
      rw [Nat.add_zero, show T + (r + P * s + 1) = T + (r + P * s) + 1 by omega, h, hc]
      rfl
    | succ d ih =>
      have h := D_step j (T + (r + P * s + 1 + d))
      rw [ha (r + P * s + 1 + d) (by omega), hb (r + P * s + 1 + d) (by omega), ih] at h
      rw [show T + (r + P * s + 1 + (d + 1)) = T + (r + P * s + 1 + d) + 1 by omega, h,
        show r + P * s + 1 + (d + 1) = r + P * s + 1 + d + 1 by omega, step_of_stepOK hP hstep]
  intro t ht
  have := key (t - (r + P * s + 1))
  rwa [show r + P * s + 1 + (t - (r + P * s + 1)) = t by omega] at this

/-- A diagonal that follows a word with a black cell is black at arbitrarily late times. -/
theorem black_late {P b j T s : Nat} (hP : 0 < P) (r : Nat) (hr : r < P) (hbr : bit b r = true)
    (hb : ∀ t, s ≤ t → D j (T + t) = bit b (t % P)) (S : Nat) : ∃ t, S ≤ t ∧ D j t = true := by
  have hle : s + S ≤ P * (s + S) := Nat.le_mul_of_pos_left _ hP
  refine ⟨T + (r + P * (s + S)), by omega, ?_⟩
  rw [hb (r + P * (s + S)) (by omega), Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr, hbr]

/-- Along a checked orbit, every diagonal whose word is checked not white is black at arbitrarily late times. -/
theorem track {P T : Nat} (hP : 0 < P) : ∀ n j a b, regimeOK P n a b = true →
    (∃ s, ∀ t, s ≤ t → D j (T + t) = bit a (t % P)) → (∃ s, ∀ t, s ≤ t → D (j + 1) (T + t) = bit b (t % P)) →
    ∀ k, 1 ≤ k → k ≤ n → ∀ S, ∃ t, S ≤ t ∧ D (j + k) t = true
  | 0, _, _, _, _, _, _, k, hk1, hkn, _ => absurd hkn (by omega)
  | n + 1, j, a, b, h, ⟨sa, ha⟩, ⟨sb, hb⟩, k, hk1, hkn, S => by
    simp only [regimeOK, Bool.and_eq_true] at h
    obtain ⟨⟨hany, hstep⟩, hrest⟩ := h
    obtain ⟨r, hr, hbr⟩ := List.any_eq_true.mp hany
    have hr' := List.mem_range.mp hr
    have ha' : ∀ t, max sa sb ≤ t → D j (T + t) = bit a (t % P) := fun t ht => ha t (by omega)
    have hb' : ∀ t, max sa sb ≤ t → D (j + 1) (T + t) = bit b (t % P) := fun t ht => hb t (by omega)
    rcases (show k = 1 ∨ 2 ≤ k by omega) with rfl | hk2
    · exact black_late hP r hr' hbr hb' S
    · have hc := follow hP hstep r hr' hbr ha' hb'
      obtain ⟨t, ht, hD⟩ := track hP n (j + 1) b (next P a b) hrest ⟨sb, hb⟩ ⟨_, hc⟩ (k - 1) (by omega)
        (by omega) S
      exact ⟨t, ht, by rwa [show j + 1 + (k - 1) = j + k by omega] at hD⟩

theorem anti_word {f : Nat → Bool} {T p : Nat} (hanti : ∀ t, T ≤ t → f (t + p) = !f t) :
    anti p (word f T (2 * p)) = true := by
  simp only [anti, List.all_eq_true, List.mem_range]
  intro t ht
  rw [bit_word f (2 * p) T (t + p) (by omega), bit_word f (2 * p) T t (by omega),
    show T + (t + p) = T + t + p by omega, hanti (T + t) (by omega)]
  simp

end DoublingGaps

/-- **The first gaps after a doubling, for the single cell.** If diagonal `w` is white from `T` and diagonal `w + 1`
is anti-periodic with half-period `p` from `T` (`D (w + 1) (t + p) = !D (w + 1) t`), with `p = 1, 2` or `4`, then
every diagonal `w + k` with `1 ≤ k < m`, `m = 5, 21, 88`, is black at arbitrarily late times: the next white
diagonal is at least `w + m`. -/
theorem D_doubling_gap (w T p m : Nat) (hpm : (p = 1 ∧ m = 5) ∨ (p = 2 ∧ m = 21) ∨ (p = 4 ∧ m = 88))
    (hw : ∀ t, T ≤ t → D w t = false) (hanti : ∀ t, T ≤ t → D (w + 1) (t + p) = !D (w + 1) t) :
    ∀ k, 1 ≤ k → k < m → ∀ S, ∃ t, S ≤ t ∧ D (w + k) t = true := by
  have hp : 0 < 2 * p := by omega
  have hper : ∀ t, T ≤ t → D (w + 1) (t + 2 * p) = D (w + 1) t := fun t ht => by
    rw [show t + 2 * p = t + p + p by omega, hanti _ (by omega), hanti t ht]
    generalize D (w + 1) t = a
    cases a <;> rfl
  have hy := word_lt (D (w + 1)) (2 * p) T
  have hya := anti_word hanti
  have hreg : regimeOK (2 * p) (m - 1) 0 (word (D (w + 1)) T (2 * p)) = true := by
    rcases hpm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact doublingGap_one _ hy hya
    · exact doublingGap_two _ hy hya
    · exact doublingGap_four _ hy hya
  intro k hk1 hkm S
  exact track (T := T) hp (m - 1) w 0 _ hreg ⟨0, fun t _ => by rw [hw (T + t) (by omega), bit_zero]⟩
    ⟨0, fun t _ => eq_bit_word hp hper t⟩ k hk1 (by omega) S

end Rule30Open
