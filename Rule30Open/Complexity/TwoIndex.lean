module

public import Ruliology.CellularAutomata.Rule30RightPeriods
public import Ruliology.CellularAutomata.Rule30Realization

/-!
# Two-index automaticity: rows of a recognizable array have linear periods

An array `b : ℕ → ℕ → Bool` is *2-recognizable* (2-automatic in two indices, after Salon) when its
2-kernel, the arrays `(v, w) ↦ b (2^e v + r) (2^e w + s)` with `r, s < 2^e`, is finite; here
`TwoIndex.Recognizable b` says that one list contains every element of the kernel, which needs no
finite-set library. `TwoIndex.Automatic f` is the same for a sequence.

* `twoIndex_row_period_le` (**the kernel lemma**): if `b` is recognizable and every row
  `t ↦ b j t` is eventually periodic, there is `C` such that row `j` has an eventual period at most
  `C (j + 1)`. Row `j`, read on the residues of `t` modulo `2^e` with `j < 2^e ≤ 2 (j + 1)`, is
  row `0` of an element of the kernel, and the finitely many kernel elements share one eventual
  period `P` of their row `0`; so row `j` has the eventual period `2^e P`.
  `twoIndex_row_period_le_of_periodic`: when every row is periodic from time `0`, so is the bound.
* `twoIndex_diag_automatic`: the diagonal `n ↦ b n n` of a recognizable array is automatic.
* `rule90_twoIndex_recognizable`: rule 90 from one black cell, as the array
  `(j, t) ↦ cell (t, t - j)` of its right diagonals (`rule90_diag_eq`: row `2m` is
  `binom(t, m) mod 2`, row `2m + 1` is white), is recognizable; its kernel has at most four
  elements. `rule90_spacetime_recognizable`: the same in the coordinates `(t, x)`, `x ≥ 0`, of
  time and column (the left half is the mirror image, `Rule30Realization.run_symm`), with at most
  six kernel elements. Binomial coefficients modulo 2 are `bsub m t`, true when the binary digits
  of `m` are digits of `t` (Lucas), defined by the digits and characterized by Pascal's rule
  (`bsub_pascal`) and the digit splitting (`bsub_split`).
* `rule30_twoIndex_not_recognizable` (**conditional**): if for every `C` some right diagonal
  `R j` of rule 30 (`Rule30Diagonals.R j t = cell t (t - j)`) has no period at most `C (j + 1)`,
  then rule 30's array `R` is not recognizable. Every row of `R` is periodic from time `0`
  (`Rule30Diagonals.R_periodic`), so this is the kernel lemma. The least period of `R j` is
  `2 ^ e_j` (`two_pow_leastExp_le`, with the kit's `Rule30RightPeriods.leastExp`), which is
  `L_(j+1)`, the cycle length of `1` under `Φ(x) = x ⊕ (2x ∨ 4x)` modulo `2^(j+1)` (the kit's
  `TFunctionCycles.seed_rows_return_iff`), so the hypothesis says that `L_n / n` is unbounded.
  - `rule30_twoIndex_not_recognizable_of_leastExp`: the same from `2 ^ e_j / (j + 1)` unbounded.
  - `rule30_twoIndex_not_recognizable_of_white_runs`: the same if for every `C` the white run
    beside the right edge at some time `2^k` is shorter than `2^k / C` (a black cell on diagonal
    `j + 1` at time `2^k` with `C (j + 1) < 2^k`; the kit's `Rule30RightPeriods.per_iff_gap`).
  The hypothesis is open: the kit's lower bounds on the periods are linear
  (`Rule30RightPeriods.period_gt`, `per_bound`), and `L_61 = 2^25` by computation.
* `rule30_twoIndex_center_automatic`: if `R` is recognizable, the center column is 2-automatic
  (it is the diagonal `R t t`). So a proof that the center column is not 2-automatic, which the kit
  shows implies Problem 1, would also show that `R` is not recognizable; nothing here gives the
  other direction.

The natural-language argument is `TwoIndex.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

namespace TwoIndex

open Ruliology.CellularAutomata

/-! ### Kernels of arrays and sequences -/

/-- The `(e, r, s)` section of an array: `(v, w) ↦ b (2^e v + r) (2^e w + s)`. -/
def sect (b : Nat → Nat → Bool) (e r s : Nat) : Nat → Nat → Bool :=
  fun v w => b (2 ^ e * v + r) (2 ^ e * w + s)

/-- An array is 2-recognizable: one list contains every section with `r, s < 2^e`, so its
2-kernel is finite. -/
def Recognizable (b : Nat → Nat → Bool) : Prop :=
  ∃ K : List (Nat → Nat → Bool), ∀ e r s, r < 2 ^ e → s < 2 ^ e → sect b e r s ∈ K

/-- A sequence is 2-automatic: one list contains every `n ↦ f (2^e n + r)` with `r < 2^e`. -/
def Automatic (f : Nat → Bool) : Prop :=
  ∃ K : List (Nat → Bool), ∀ e r, r < 2 ^ e → (fun n => f (2 ^ e * n + r)) ∈ K

theorem two_pow_pos' (e : Nat) : 0 < 2 ^ e := Nat.pos_of_ne_zero (Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos e))

/-- A period from `T` on is a period of every multiple. -/
theorem per_mul_from {f : Nat → Bool} {T p : Nat} (h : ∀ t, T ≤ t → f (t + p) = f t) :
    ∀ n t, T ≤ t → f (t + n * p) = f t
  | 0, t, _ => by rw [Nat.zero_mul, Nat.add_zero]
  | n + 1, t, ht => by
    rw [Nat.succ_mul, ← Nat.add_assoc, h (t + n * p) (by omega), per_mul_from h n t ht]

/-- Finitely many eventually periodic sequences share one eventual period. -/
theorem common_period {α : Type} (F : α → Nat → Bool) (good : α → Prop)
    (hg : ∀ a, good a → ∃ T p, 0 < p ∧ ∀ t, T ≤ t → F a (t + p) = F a t) :
    ∀ K : List α, ∃ T P, 0 < P ∧ ∀ a ∈ K, good a → ∀ t, T ≤ t → F a (t + P) = F a t
  | [] => ⟨0, 1, by omega, fun a ha => absurd ha (List.not_mem_nil)⟩
  | a :: K => by
    obtain ⟨T, P, hP, hK⟩ := common_period F good hg K
    by_cases ha : good a
    · obtain ⟨T', p, hp, hper⟩ := hg a ha
      refine ⟨max T T', P * p, Nat.mul_pos hP hp, fun x hx hgx t ht => ?_⟩
      rcases List.mem_cons.1 hx with rfl | hx'
      · exact per_mul_from hper P t (by omega)
      · rw [Nat.mul_comm]
        exact per_mul_from (hK x hx' hgx) p t (by omega)
    · refine ⟨T, P, hP, fun x hx hgx => ?_⟩
      rcases List.mem_cons.1 hx with rfl | hx'
      · exact absurd hgx ha
      · exact hK x hx' hgx

/-- A sequence periodic from `0` with period `q` and eventually periodic with period `p` is
periodic from `0` with period `p`. -/
theorem per_of_eventual {f : Nat → Bool} {q p T : Nat} (hq : 0 < q)
    (hpure : ∀ t, f (t + q) = f t) (hev : ∀ t, T ≤ t → f (t + p) = f t) :
    ∀ t, f (t + p) = f t := by
  have hm : ∀ n t, f (t + n * q) = f t :=
    fun n t => per_mul_from (T := 0) (fun t _ => hpure t) n t (Nat.zero_le t)
  intro t
  have hTq : T ≤ T * q := Nat.le_mul_of_pos_right T hq
  rw [← hm T (t + p), show t + p + T * q = (t + T * q) + p by omega, hev _ (by omega), hm]

/-- The exponent `e = log₂ j + 1`: `j < 2^e ≤ 2 (j + 1)`. -/
theorem exists_exp (j : Nat) : ∃ e, j < 2 ^ e ∧ 2 ^ e ≤ 2 * (j + 1) := by
  refine ⟨j.log2 + 1, Nat.lt_log2_self, ?_⟩
  rw [Nat.pow_succ]
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · decide
  · have := Nat.log2_self_le (Nat.pos_iff_ne_zero.mp hj)
    omega

end TwoIndex

open TwoIndex Ruliology.CellularAutomata

/-- **The kernel lemma.** If an array is recognizable and each of its rows is eventually periodic,
then for some `C` every row `j` has an eventual period at most `C (j + 1)`. -/
theorem twoIndex_row_period_le {b : Nat → Nat → Bool} (hb : Recognizable b)
    (hrow : ∀ j, ∃ T p, 0 < p ∧ ∀ t, T ≤ t → b j (t + p) = b j t) :
    ∃ C, ∀ j, ∃ p, 0 < p ∧ p ≤ C * (j + 1) ∧ ∃ T, ∀ t, T ≤ t → b j (t + p) = b j t := by
  obtain ⟨K, hK⟩ := hb
  -- a section's row `0` is a row of `b` read on a residue class, so it is eventually periodic
  have hg : ∀ g : Nat → Nat → Bool,
      (∃ e r s, r < 2 ^ e ∧ s < 2 ^ e ∧ g = sect b e r s) →
        ∃ T p, 0 < p ∧ ∀ t, T ≤ t → g 0 (t + p) = g 0 t := by
    rintro g ⟨e, r, s, -, -, rfl⟩
    obtain ⟨T, p, hp, hper⟩ := hrow r
    refine ⟨T, p, hp, fun t ht => ?_⟩
    show b (2 ^ e * 0 + r) (2 ^ e * (t + p) + s) = b (2 ^ e * 0 + r) (2 ^ e * t + s)
    have h1 : t ≤ 2 ^ e * t := Nat.le_mul_of_pos_left t (two_pow_pos' e)
    rw [Nat.mul_zero, Nat.zero_add, Nat.mul_add,
      show 2 ^ e * t + 2 ^ e * p + s = (2 ^ e * t + s) + 2 ^ e * p by omega]
    exact per_mul_from hper (2 ^ e) _ (by omega)
  obtain ⟨T, P, hP, hcom⟩ := common_period (fun g t => g 0 t) _ hg K
  refine ⟨2 * P, fun j => ?_⟩
  obtain ⟨e, hje, hle⟩ := exists_exp j
  have he := two_pow_pos' e
  refine ⟨2 ^ e * P, Nat.mul_pos he hP, ?_, 2 ^ e * T, fun t ht => ?_⟩
  · calc 2 ^ e * P ≤ 2 * (j + 1) * P := Nat.mul_le_mul_right P hle
      _ = 2 * P * (j + 1) := by rw [Nat.mul_assoc, Nat.mul_comm (j + 1) P, ← Nat.mul_assoc]
  · have hs : t % 2 ^ e < 2 ^ e := Nat.mod_lt _ he
    have hq : T ≤ t / 2 ^ e := (Nat.le_div_iff_mul_le he).2 (by rw [Nat.mul_comm]; exact ht)
    have key := hcom (sect b e j (t % 2 ^ e)) (hK e j _ hje hs) ⟨e, j, _, hje, hs, rfl⟩ _ hq
    simp only [sect, Nat.mul_zero, Nat.zero_add] at key
    have ht1 : t = 2 ^ e * (t / 2 ^ e) + t % 2 ^ e := (Nat.div_add_mod t (2 ^ e)).symm
    have ht2 : t + 2 ^ e * P = 2 ^ e * (t / 2 ^ e + P) + t % 2 ^ e := by
      rw [Nat.mul_add]; omega
    rw [ht2, key, ← ht1]

/-- **The kernel lemma for rows periodic from time `0`.** -/
theorem twoIndex_row_period_le_of_periodic {b : Nat → Nat → Bool} (hb : Recognizable b)
    (hrow : ∀ j, ∃ q, 0 < q ∧ ∀ t, b j (t + q) = b j t) :
    ∃ C, ∀ j, ∃ p, 0 < p ∧ p ≤ C * (j + 1) ∧ ∀ t, b j (t + p) = b j t := by
  obtain ⟨C, hC⟩ := twoIndex_row_period_le hb fun j => by
    obtain ⟨q, hq, hper⟩ := hrow j
    exact ⟨0, q, hq, fun t _ => hper t⟩
  refine ⟨C, fun j => ?_⟩
  obtain ⟨p, hp, hpC, T, hT⟩ := hC j
  obtain ⟨q, hq, hper⟩ := hrow j
  exact ⟨p, hp, hpC, per_of_eventual hq hper hT⟩

/-- The diagonal of a recognizable array is automatic. -/
theorem twoIndex_diag_automatic {b : Nat → Nat → Bool} (hb : Recognizable b) :
    Automatic fun n => b n n := by
  obtain ⟨K, hK⟩ := hb
  exact ⟨K.map fun g n => g n n, fun e r hr => List.mem_map.2 ⟨_, hK e r r hr hr, rfl⟩⟩

/-! ### Rule 30 -/

/-- **Rule 30's array of right diagonals is not recognizable if the right-edge cycles grow faster
than linearly**: if for every `C` some diagonal `R j` has no period `p ≤ C (j + 1)`, then
`(j, t) ↦ cell t (t - j)` is not 2-recognizable. -/
theorem rule30_twoIndex_not_recognizable
    (h : ∀ C, ∃ j, ∀ p, 0 < p → (∀ t, Rule30Diagonals.R j (t + p) = Rule30Diagonals.R j t) →
      C * (j + 1) < p) :
    ¬ Recognizable Rule30Diagonals.R := by
  intro hR
  obtain ⟨C, hC⟩ := twoIndex_row_period_le_of_periodic hR fun j =>
    ⟨2 ^ j, two_pow_pos' j, Rule30Diagonals.R_periodic j⟩
  obtain ⟨j, hj⟩ := h C
  obtain ⟨p, hp, hpC, hper⟩ := hC j
  exact absurd (hj p hp hper) (Nat.not_lt.2 hpC)

/-- If rule 30's array of right diagonals is recognizable, its center column is 2-automatic. -/
theorem rule30_twoIndex_center_automatic (hR : Recognizable Rule30Diagonals.R) :
    Automatic fun t => Rule30Jen.cell t 0 := by
  have e : (fun n => Rule30Diagonals.R n n) = fun t => Rule30Jen.cell t 0 := by
    funext n
    show Rule30Jen.cell n ((n : Int) - n) = Rule30Jen.cell n 0
    rw [Int.sub_self]
  rw [← e]
  exact twoIndex_diag_automatic hR

namespace TwoIndex

open Rule30RightPeriods

/-- A divisor of a power of two is a power of two. -/
theorem dvd_two_pow_eq : ∀ j d, d ∣ 2 ^ j → ∃ k, d = 2 ^ k
  | 0, d, h => ⟨0, by rw [Nat.pow_zero] at h ⊢; exact Nat.dvd_one.1 h⟩
  | j + 1, d, h => by
    rcases dvd_two_pow_succ h with h1 | h1
    · exact ⟨j + 1, h1⟩
    · exact dvd_two_pow_eq j d h1

/-- Every period of `R j` is at least `2 ^ e_j`, the least period (the kit's `leastExp`). -/
theorem two_pow_leastExp_le {j p : Nat} (hp : 0 < p) (h : Per j p) : 2 ^ leastExp j ≤ p := by
  have hg := PerF.gcd (f := Rule30Diagonals.R j) p (2 ^ j) h (per_R_periodic j)
  obtain ⟨k, hk⟩ := dvd_two_pow_eq j _ (Nat.gcd_dvd_right p (2 ^ j))
  rw [hk] at hg
  have he := (leastExp_spec j).le hg
  calc 2 ^ leastExp j ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) he
    _ = Nat.gcd p (2 ^ j) := hk.symm
    _ ≤ p := Nat.le_of_dvd hp (Nat.gcd_dvd_left p _)

end TwoIndex

open Rule30RightPeriods in
/-- **The conditional theorem with the kit's exponents**: if `2 ^ e_j / (j + 1)` is unbounded
(`e_j = Rule30RightPeriods.leastExp j`, so `2 ^ e_j = L_(j+1)`), rule 30's array of right
diagonals is not recognizable. -/
theorem rule30_twoIndex_not_recognizable_of_leastExp (h : ∀ C, ∃ j, C * (j + 1) < 2 ^ leastExp j) :
    ¬ Recognizable Rule30Diagonals.R :=
  rule30_twoIndex_not_recognizable fun C => by
    obtain ⟨j, hj⟩ := h C
    exact ⟨j, fun p hp hper => Nat.lt_of_lt_of_le hj (two_pow_leastExp_le hp hper)⟩

open Rule30RightPeriods in
/-- **The conditional theorem in the form of white runs**: if for every `C` some row `2^k` has a
black cell on the diagonal `j + 1` with `C (j + 1) < 2^k`, that is the white run beside the right
edge at time `2^k` is shorter than `2^k / C`, rule 30's array of right diagonals is not
recognizable. -/
theorem rule30_twoIndex_not_recognizable_of_white_runs
    (h : ∀ C, ∃ k j, Rule30Diagonals.R (j + 1) (2 ^ k) = true ∧ C * (j + 1) < 2 ^ k) :
    ¬ Recognizable Rule30Diagonals.R := by
  apply rule30_twoIndex_not_recognizable
  intro C
  obtain ⟨k, j, hb, hlt⟩ := h C
  refine ⟨j + 1, fun p hp hper => ?_⟩
  have hnot : ¬ Per (j + 1) (2 ^ k) := fun hk => by
    have := hk.at_mul 1
    rw [Nat.mul_one, R_init (by omega)] at this
    rw [this] at hb
    exact absurd hb (by decide)
  have hek : k < leastExp (j + 1) :=
    Nat.lt_of_not_le fun hle => hnot ((leastExp_spec (j + 1)).1.pow_mono hle)
  have h1 := two_pow_leastExp_le hp hper
  have h2 : 2 ^ (k + 1) ≤ 2 ^ leastExp (j + 1) := Nat.pow_le_pow_right (by decide) hek
  have h3 : C * 1 ≤ C * (j + 1) := Nat.mul_le_mul_left C (by omega)
  rw [Nat.pow_succ] at h2
  rw [Nat.mul_add]
  omega

/-! ### Binomial coefficients modulo 2 -/

namespace TwoIndex

/-- `bsub m t`: every binary digit of `m` is a digit of `t`, that is `binom(t, m)` is odd (Lucas).
Defined digit by digit. -/
def bsub (m t : Nat) : Bool :=
  if h : t = 0 then m == 0 else (decide (m % 2 ≤ t % 2) && bsub (m / 2) (t / 2))
termination_by t
decreasing_by omega

theorem bsub_zero_right (m : Nat) : bsub m 0 = (m == 0) := by
  rw [bsub]; simp

theorem bsub_pos {m t : Nat} (h : t ≠ 0) :
    bsub m t = (decide (m % 2 ≤ t % 2) && bsub (m / 2) (t / 2)) := by
  rw [bsub]; simp [h]

/-- One digit: `bsub (2x + a) (2y + b) = (a ≤ b) ∧ bsub x y`. -/
theorem bsub_digit (x y a b : Nat) (ha : a < 2) (hb : b < 2) :
    bsub (2 * x + a) (2 * y + b) = (decide (a ≤ b) && bsub x y) := by
  by_cases h : 2 * y + b = 0
  · have hy : y = 0 := by omega
    have hb0 : b = 0 := by omega
    subst hy hb0
    rw [show 2 * 0 + 0 = 0 from rfl, bsub_zero_right, bsub_zero_right]
    rcases (by omega : a = 0 ∨ a = 1) with rfl | rfl
    · cases x <;> simp
    · simp
  · rw [bsub_pos h, show (2 * x + a) % 2 = a by omega, show (2 * y + b) % 2 = b by omega,
      show (2 * x + a) / 2 = x by omega, show (2 * y + b) / 2 = y by omega]

theorem bsub_zero_left (t : Nat) : bsub 0 t = true := by
  by_cases h : t = 0
  · subst h; rw [bsub_zero_right]; rfl
  · rw [bsub_pos h, bsub_zero_left (t / 2)]; simp
termination_by t
decreasing_by omega

/-- **Pascal's rule modulo 2.** -/
theorem bsub_pascal (m t : Nat) : bsub (m + 1) (t + 1) = xor (bsub (m + 1) t) (bsub m t) := by
  obtain ⟨m', a, ha, rfl⟩ : ∃ m' a, a < 2 ∧ m = 2 * m' + a :=
    ⟨m / 2, m % 2, Nat.mod_lt _ (by decide), (Nat.div_add_mod m 2).symm⟩
  obtain ⟨t', b, hb, rfl⟩ : ∃ t' b, b < 2 ∧ t = 2 * t' + b :=
    ⟨t / 2, t % 2, Nat.mod_lt _ (by decide), (Nat.div_add_mod t 2).symm⟩
  rcases (by omega : a = 0 ∨ a = 1) with rfl | rfl <;>
    rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl
  · rw [show 2 * m' + 0 + 1 = 2 * m' + 1 by omega, show 2 * t' + 0 + 1 = 2 * t' + 1 by omega,
      bsub_digit m' t' 1 1 (by decide) (by decide), bsub_digit m' t' 1 0 (by decide) (by decide),
      bsub_digit m' t' 0 0 (by decide) (by decide)]
    cases bsub m' t' <;> rfl
  · rw [show 2 * m' + 0 + 1 = 2 * m' + 1 by omega, show 2 * t' + 1 + 1 = 2 * (t' + 1) + 0 by omega,
      bsub_digit m' (t' + 1) 1 0 (by decide) (by decide), bsub_digit m' t' 1 1 (by decide) (by decide),
      bsub_digit m' t' 0 1 (by decide) (by decide)]
    cases bsub m' t' <;> rfl
  · rw [show 2 * m' + 1 + 1 = 2 * (m' + 1) + 0 by omega, show 2 * t' + 0 + 1 = 2 * t' + 1 by omega,
      bsub_digit (m' + 1) t' 0 1 (by decide) (by decide),
      bsub_digit (m' + 1) t' 0 0 (by decide) (by decide), bsub_digit m' t' 1 0 (by decide) (by decide)]
    cases bsub (m' + 1) t' <;> rfl
  · rw [show 2 * m' + 1 + 1 = 2 * (m' + 1) + 0 by omega, show 2 * t' + 1 + 1 = 2 * (t' + 1) + 0 by omega,
      bsub_digit (m' + 1) (t' + 1) 0 0 (by decide) (by decide),
      bsub_digit (m' + 1) t' 0 1 (by decide) (by decide), bsub_digit m' t' 1 1 (by decide) (by decide),
      bsub_pascal m' t']
    cases bsub (m' + 1) t' <;> cases bsub m' t' <;> rfl
termination_by t
decreasing_by omega

theorem two_pow_succ_mul (e v : Nat) : 2 ^ (e + 1) * v = 2 * (2 ^ e * v) := by
  rw [Nat.pow_succ, Nat.mul_comm (2 ^ e) 2, Nat.mul_assoc]

/-- **Digit splitting.** For `r, s < 2^e`, `bsub (2^e v + r) (2^e w + s) = bsub r s ∧ bsub v w`. -/
theorem bsub_split : ∀ (e v w r s : Nat), r < 2 ^ e → s < 2 ^ e →
    bsub (2 ^ e * v + r) (2 ^ e * w + s) = (bsub r s && bsub v w)
  | 0, v, w, r, s, hr, hs => by
    have hr0 : r = 0 := by simp at hr; omega
    have hs0 : s = 0 := by simp at hs; omega
    subst hr0 hs0
    rw [bsub_zero_left]
    simp
  | e + 1, v, w, r, s, hr, hs => by
    have hP := two_pow_pos' e
    rw [Nat.pow_succ] at hr hs
    have h1 : 2 ^ (e + 1) * v + r = 2 * (2 ^ e * v + r / 2) + r % 2 := by
      rw [two_pow_succ_mul]; omega
    have h2 : 2 ^ (e + 1) * w + s = 2 * (2 ^ e * w + s / 2) + s % 2 := by
      rw [two_pow_succ_mul]; omega
    have h3 : bsub r s = (decide (r % 2 ≤ s % 2) && bsub (r / 2) (s / 2)) := by
      have := bsub_digit (r / 2) (s / 2) (r % 2) (s % 2) (Nat.mod_lt _ (by decide))
        (Nat.mod_lt _ (by decide))
      rwa [Nat.div_add_mod, Nat.div_add_mod] at this
    rw [h1, h2, bsub_digit _ _ _ _ (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)),
      bsub_split e v w (r / 2) (s / 2) (by omega) (by omega), h3, Bool.and_assoc]

theorem lt_two_cases {q : Nat} (h : q < 2) : q = 0 ∨ q = 1 := by omega

/-- Decomposition of a residue modulo `2^(e+1)` at its top digit. -/
theorem split_top (e v r : Nat) (hr : r < 2 ^ (e + 1)) :
    2 ^ (e + 1) * v + r = 2 ^ e * (2 * v + r / 2 ^ e) + r % 2 ^ e ∧ r / 2 ^ e < 2 ∧
      r % 2 ^ e < 2 ^ e := by
  have hP := two_pow_pos' e
  refine ⟨?_, (Nat.div_lt_iff_lt_mul hP).2 (by rw [Nat.pow_succ] at hr; omega), Nat.mod_lt _ hP⟩
  have := Nat.div_add_mod r (2 ^ e)
  rw [Nat.pow_succ, Nat.mul_comm (2 ^ e) 2, Nat.mul_assoc, Nat.mul_add, Nat.mul_left_comm]
  omega

end TwoIndex

/-! ### Rule 90 -/

namespace TwoIndex

open Rule30Realization

/-- Rule 90 from one black cell, as the array of its right diagonals: `cell t (t - j)`. -/
def rd90 (j t : Nat) : Bool := run g90 t ((t : Int) - j)

theorem run90_succ (t : Nat) (p : Int) :
    run g90 (t + 1) p = xor (run g90 t (p - 1)) (run g90 t (p + 1)) := rfl

theorem run90_left (t : Nat) (p : Int) (h : p < -(t : Int)) : run g90 t p = false :=
  run_eq_false_of_lt g90 rfl t p h

theorem run90_symm (t : Nat) (p : Int) : run g90 t (-p) = run g90 t p :=
  run_symm g90 (by intro a b c; cases a <;> cases c <;> rfl) t p

theorem run90_right (t : Nat) (p : Int) (h : (t : Int) < p) : run g90 t p = false := by
  rw [← run90_symm]; exact run90_left t (-p) (by omega)

/-- **Rule 90 is Pascal's triangle modulo 2**: row `j` of its array of right diagonals is white
for odd `j`, and `binom(t, j / 2) mod 2` for even `j`. -/
theorem rule90_diag_eq : ∀ t j, rd90 j t = (decide (j % 2 = 0) && bsub (j / 2) t)
  | 0, j => by
    show run g90 0 (((0 : Nat) : Int) - j) = _
    simp only [run]
    rw [bsub_zero_right]
    rcases Nat.lt_or_ge j 2 with hj | hj
    · rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;> decide
    · have : ((((0 : Nat) : Int) - j) = 0) = False := by simp; omega
      simp only [this, decide_false]
      have : (j / 2 == 0) = false := by simp; omega
      rw [this]; simp
  | t + 1, j => by
    have ih := rule90_diag_eq t
    show run g90 (t + 1) (((t + 1 : Nat) : Int) - j) = _
    rw [run90_succ, show ((t + 1 : Nat) : Int) - j - 1 = (t : Int) - j by omega]
    have e1 : run g90 t ((t : Int) - j) = rd90 j t := rfl
    rw [e1, ih j]
    rcases Nat.lt_or_ge j 2 with hj | hj
    · rw [run90_right t _ (by omega)]
      rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
      · simp [bsub_zero_left]
      · simp
    · obtain ⟨i, rfl⟩ : ∃ i, j = i + 2 := ⟨j - 2, by omega⟩
      have e2 : run g90 t (((t + 1 : Nat) : Int) - (i + 2 : Nat) + 1) = rd90 i t := by
        show _ = run g90 t ((t : Int) - i)
        congr 1; omega
      rw [e2, ih i, show (i + 2) % 2 = i % 2 by omega, show (i + 2) / 2 = i / 2 + 1 by omega,
        bsub_pascal]
      cases decide (i % 2 = 0) <;> simp

/-- The sections of rule 90's array of right diagonals beyond level `0`. -/
def rd90Sect (a : Nat) : Nat → Nat → Bool := fun v w => bsub v (2 * w + a)

theorem rd90_sect_succ (e r s : Nat) (hr : r < 2 ^ (e + 1)) (hs : s < 2 ^ (e + 1)) :
    sect rd90 (e + 1) r s =
      fun v w => (decide (r % 2 = 0) && bsub (r / 2) (s % 2 ^ e)) && rd90Sect (s / 2 ^ e) v w := by
  funext v w
  obtain ⟨hst, hs2, hs3⟩ := split_top e w s hs
  have hP := two_pow_pos' e
  have hr2 : r / 2 < 2 ^ e := by rw [Nat.pow_succ] at hr; omega
  show rd90 (2 ^ (e + 1) * v + r) (2 ^ (e + 1) * w + s) = _
  rw [rule90_diag_eq, two_pow_succ_mul, show (2 * (2 ^ e * v) + r) % 2 = r % 2 by omega,
    show (2 * (2 ^ e * v) + r) / 2 = 2 ^ e * v + r / 2 by omega, hst, bsub_split e _ _ _ _ hr2 hs3,
    rd90Sect, Bool.and_assoc]

end TwoIndex

open TwoIndex Rule30Realization

/-- **Rule 90's array of right diagonals is 2-recognizable**, with at most four kernel elements. -/
theorem rule90_twoIndex_recognizable : Recognizable rd90 := by
  refine ⟨[rd90, fun _ _ => false, rd90Sect 0, rd90Sect 1], fun e r s hr hs => ?_⟩
  cases e with
  | zero =>
    have hr0 : r = 0 := by simp at hr; omega
    have hs0 : s = 0 := by simp at hs; omega
    subst hr0 hs0
    have : sect rd90 0 0 0 = rd90 := by funext v w; simp [sect]
    rw [this]; simp
  | succ e =>
    rw [rd90_sect_succ e r s hr hs]
    obtain ⟨-, hs2, -⟩ := split_top e 0 s hs
    cases decide (r % 2 = 0) && bsub (r / 2) (s % 2 ^ e)
    · simp
    · rcases lt_two_cases hs2 with h | h <;> rw [h] <;> simp

namespace TwoIndex

/-- Rule 90 from one black cell in the coordinates of time and column, right half: `cell t x`,
`x ≥ 0`. The left half is its mirror image (`Rule30Realization.run_symm`). -/
def st90 (t x : Nat) : Bool := run g90 t (x : Int)

theorem st90_eq (t x : Nat) :
    st90 t x = (decide (x ≤ t) && (decide ((t - x) % 2 = 0) && bsub ((t - x) / 2) t)) := by
  by_cases hx : x ≤ t
  · have : st90 t x = rd90 (t - x) t := by
      show run g90 t (x : Int) = run g90 t ((t : Int) - ((t - x : Nat) : Int))
      congr 1; omega
    rw [this, rule90_diag_eq]; simp [hx]
  · show run g90 t (x : Int) = _
    rw [run90_right t _ (by omega)]; simp [hx]

/-- The sections of `st90` beyond level `0`: a borrow `β` and the top digit `τ` of the time. -/
def st90Sect (β τ : Nat) : Nat → Nat → Bool :=
  fun v w => decide (w + β ≤ v) && bsub (v - w - β) (2 * v + τ)

theorem st90_sect_succ (e r s : Nat) (hr : r < 2 ^ (e + 1)) (hs : s < 2 ^ (e + 1)) :
    ∃ c : Bool, sect st90 (e + 1) r s =
      fun v w => c && st90Sect (if r < s then 1 else 0) (r / 2 ^ e) v w := by
  have hP := two_pow_pos' e
  -- the borrow of the low digits, and their difference
  obtain ⟨β, hβ⟩ : ∃ β, β = if r < s then 1 else 0 := ⟨_, rfl⟩
  rw [← hβ]
  have hβ1 : (r < s ∧ β = 1) ∨ (s ≤ r ∧ β = 0) := by
    by_cases h : r < s
    · left; simp [hβ, h]
    · right; simp [hβ, h]; omega
  obtain ⟨P, hPdef⟩ : ∃ P, P = 2 ^ (e + 1) := ⟨_, rfl⟩
  have hP2 : P = 2 * 2 ^ e := by rw [hPdef, Nat.pow_succ, Nat.mul_comm]
  obtain ⟨d, hd⟩ : ∃ d, d = r + P * β - s := ⟨_, rfl⟩
  have hdlt : d < P := by
    rcases hβ1 with ⟨h1, rfl⟩ | ⟨h1, rfl⟩
    · rw [Nat.mul_one] at hd; omega
    · rw [Nat.mul_zero] at hd; omega
  have hd2 : d / 2 < 2 ^ e := by omega
  refine ⟨decide (d % 2 = 0) && bsub (d / 2) (r % 2 ^ e), ?_⟩
  funext v w
  show st90 (2 ^ (e + 1) * v + r) (2 ^ (e + 1) * w + s) = _
  have htop := (split_top e v r hr).1
  rw [← hPdef] at htop hr hs
  rw [← hPdef, st90_eq]
  simp only [st90Sect]
  -- compare `x ≤ t` with `w + β ≤ v`
  have hmono : ∀ a b : Nat, a ≤ b → P * a ≤ P * b := fun a b h => Nat.mul_le_mul_left _ h
  have hcmp : (P * w + s ≤ P * v + r) ↔ w + β ≤ v := by
    rcases hβ1 with ⟨h1, rfl⟩ | ⟨h1, rfl⟩
    · constructor
      · intro h
        refine Nat.not_lt.1 fun hlt => ?_
        have := hmono v w (by omega)
        omega
      · intro h
        have := hmono (w + 1) v h
        rw [Nat.mul_add, Nat.mul_one] at this
        omega
    · constructor
      · intro h
        refine Nat.not_lt.1 fun hlt => ?_
        have := hmono (v + 1) w (by omega)
        rw [Nat.mul_add, Nat.mul_one] at this
        omega
      · intro h
        have := hmono w v (by omega)
        omega
  by_cases hle : w + β ≤ v
  · have hxt := hcmp.2 hle
    -- `t - x = 2^(e+1) (v - w - β) + d`
    have hdiff : P * v + r - (P * w + s) = 2 * (2 ^ e * (v - w - β)) + d := by
      have h2 : P * (v - w - β) + P * w + P * β = P * v := by
        rw [← Nat.mul_add, ← Nat.mul_add, show v - w - β + w + β = v by omega]
      have h3 : P * (v - w - β) = 2 * (2 ^ e * (v - w - β)) := by rw [hP2, Nat.mul_assoc]
      rcases hβ1 with ⟨h1, rfl⟩ | ⟨h1, rfl⟩
      · rw [Nat.mul_one] at h2 hd; omega
      · rw [Nat.mul_zero] at h2 hd; omega
    rw [decide_eq_true hxt, decide_eq_true hle, hdiff,
      show (2 * (2 ^ e * (v - w - β)) + d) % 2 = d % 2 by omega,
      show (2 * (2 ^ e * (v - w - β)) + d) / 2 = 2 ^ e * (v - w - β) + d / 2 by omega,
      htop, bsub_split e _ _ _ _ hd2 (Nat.mod_lt _ hP)]
    cases decide (d % 2 = 0) <;> cases bsub (d / 2) (r % 2 ^ e) <;> simp
  · have hxt : ¬ (P * w + s ≤ P * v + r) := fun h => hle (hcmp.1 h)
    rw [decide_eq_false hxt, decide_eq_false hle]
    simp

end TwoIndex

/-- **Rule 90 in time and column is 2-recognizable**: `(t, x) ↦ cell t x` on the right half
`x ≥ 0`, with at most six kernel elements. -/
theorem rule90_spacetime_recognizable : Recognizable st90 := by
  refine ⟨[st90, fun _ _ => false, st90Sect 0 0, st90Sect 0 1, st90Sect 1 0, st90Sect 1 1],
    fun e r s hr hs => ?_⟩
  cases e with
  | zero =>
    have hr0 : r = 0 := by simp at hr; omega
    have hs0 : s = 0 := by simp at hs; omega
    subst hr0 hs0
    have : sect st90 0 0 0 = st90 := by funext v w; simp [sect]
    rw [this]; simp
  | succ e =>
    obtain ⟨c, hc⟩ := st90_sect_succ e r s hr hs
    rw [hc]
    obtain ⟨-, hr2, -⟩ := split_top e 0 r hr
    cases c
    · simp
    · have hβ : (if r < s then 1 else 0) = 0 ∨ (if r < s then 1 else 0) = 1 := by split <;> omega
      rcases hβ with h1 | h1 <;>
        rcases lt_two_cases hr2 with h2 | h2 <;>
        rw [h1, h2] <;> simp

end Rule30Open
