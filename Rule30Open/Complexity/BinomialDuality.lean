module

public import Ruliology.CellularAutomata.Rule30DifferenceOrder
public import Ruliology.CellularAutomata.Rule30Prize
public import Rule30Open.Complexity.TwoIndex
public import Rule30Open.Columns.WideWindow

/-!
# The binomial transform over GF(2) exchanges transients and power-of-two periods

For `f : ℕ → Bool` let `zeta f n` be the XOR of `f t` over the `t ≤ n` whose binary digits are
digits of `n`, that is `t &&& n = t` (`BinomialDuality.zeta`). Read as a function of the digits
of `n` it is the algebraic normal form of `f` (the Moebius transform over the subset order of the
digits), and by Lucas's theorem `zeta f n = ∑_t C(n, t) f(t) mod 2`, the binomial transform.

* `binomial_eq_difs`: `zeta f n = difs n f 0`, the `n`-th difference at `0` of the kit's
  `Rule30DifferenceOrder` (the Mahler coefficient over GF(2)). Both sides split the same way on the
  lowest digit of `n` (`zeta_two_mul`, `zeta_two_mul_add_one`, `difs_two_mul`,
  `difs_two_mul_add_one`): Lucas's theorem modulo 2 in transform form. `bsub_eq_land`: the subset
  relation is `TwoIndex.bsub`, which satisfies Pascal's rule (`TwoIndex.bsub_pascal`).
* `binomial_involutive`: `zeta (zeta f) = f`. The transform turns shifts into differences and back:
  `zeta (f (· + k)) = difs k (zeta f)` (`binomial_shift`), `zeta (difs k f) n = zeta f (n + k)`
  (`binomial_difs`), so the transform of `j ↦ difs r f (j + s)` is `i ↦ difs s (zeta f) (i + r)`
  (`binomial_tail_difs`).
* `binomial_prefix_iff`, `binomial_firstOne_iff`: `g` vanishes on `[0, N)` iff `zeta g` does, so the
  two have their first `1` at the same index.
* **The duality** (`binomial_window_iff`, `binomial_tail_iff`): `difs r f` vanishes on `[s, s + N)`
  iff `difs s (zeta f)` vanishes on `[r, r + N)`, and on `[s, ∞)` iff on `[r, ∞)`.
* **Powers of two**, through the kit's `difs_two_pow`: `f` has period `2^a` on `[2^m, ∞)` iff
  `zeta f` has period `2^m` on `[2^a, ∞)` (`binomial_period_iff`; on windows,
  `binomial_period_window_iff`), and the least `j` with `f (2^m + j + 2^a) ≠ f (2^m + j)` is the least
  `j` with `zeta f (2^a + j + 2^m) ≠ zeta f (2^a + j)` (`binomial_firstMismatch_iff`). The extreme
  cases: `f` vanishes on `[2^m, ∞)` iff `zeta f` has period `2^m` (`binomial_support_iff`), and `f`
  has period `2^a` iff `zeta f` vanishes on `[2^a, ∞)` (`binomial_periodic_iff`).
  `binomial_twoPow_iff`: `zeta f` has an eventual period that is a power of two iff `f` has one.
* **Any period** (`binomial_eventuallyPeriodic_iff`): `zeta f` is eventually periodic iff `f` is. If
  `f` has period `P` from `T`, so does every `difs k f` (`difs_period`), which is then fixed by its
  window on `[0, T + P)` (`eq_of_agree_window`), and the kit's `Rule30Jen.pigeonhole` finds two equal
  windows.
* **The center column**, with `gamma = zeta Rule30Prize.center`: `center_binomial_period_iff`;
  `center_binomial_rung_iff` (`c` is not `2^(k+1)`-periodic from `2^k` iff `gamma` is not
  `2^k`-periodic from `2^(k+1)`) with the same least witness (`center_binomial_firstMismatch_iff`);
  `center_binomial_twoPow_iff`; `problem1_iff_gamma` (**Problem 1 holds iff `gamma` is not eventually
  periodic**); `gamma_not_period_from_one` (from the kit's `center_not_eventually_period_one`: `gamma`
  has no period `2^m` on `[1, ∞)`); `gamma_not_twoPow_of_problem1`; `gamma_period_ge_262125` (a period
  `2^m` of `gamma` from `2^a` needs `2^a + 2^m ≥ 262125`, from `transient_add_period_ge_262125`); and
  the rung at every level up to `17` on both sides (`center_rung_le_seventeen`,
  `gamma_rung_le_seventeen`).

The natural-language argument is `BinomialDuality.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

namespace BinomialDuality

open Ruliology.CellularAutomata Rule30DifferenceOrder

/-! ### Sums over GF(2) -/

/-- The XOR of `g t` over `t < k`. -/
def xorSum (g : Nat → Bool) : Nat → Bool
  | 0 => false
  | k + 1 => xor (xorSum g k) (g k)

theorem xorSum_congr {g g' : Nat → Bool} : ∀ {k : Nat}, (∀ t, t < k → g t = g' t) →
    xorSum g k = xorSum g' k
  | 0, _ => rfl
  | k + 1, h => by
    show xor (xorSum g k) (g k) = xor (xorSum g' k) (g' k)
    rw [xorSum_congr (fun t ht => h t (by omega)), h k (by omega)]

theorem xorSum_false : ∀ k, xorSum (fun _ => false) k = false
  | 0 => rfl
  | k + 1 => by
    show xor (xorSum (fun _ => false) k) false = false
    rw [xorSum_false k]
    rfl

/-- A sum over `t < 2k` splits into the even and the odd `t`. -/
theorem xorSum_two_mul (g : Nat → Bool) : ∀ k, xorSum g (2 * k) =
    xor (xorSum (fun s => g (2 * s)) k) (xorSum (fun s => g (2 * s + 1)) k)
  | 0 => rfl
  | k + 1 => by
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by omega]
    show xor (xor (xorSum g (2 * k)) (g (2 * k))) (g (2 * k + 1)) =
      xor (xor (xorSum (fun s => g (2 * s)) k) (g (2 * k)))
        (xor (xorSum (fun s => g (2 * s + 1)) k) (g (2 * k + 1)))
    rw [xorSum_two_mul g k]
    cases xorSum (fun s => g (2 * s)) k <;> cases xorSum (fun s => g (2 * s + 1)) k <;>
      cases g (2 * k) <;> cases g (2 * k + 1) <;> rfl

/-! ### The subset order of the binary digits -/

/-- `t &&& n = t` says that every binary digit of `t` is a digit of `n`. -/
theorem land_eq_self_iff {t n : Nat} :
    t &&& n = t ↔ ∀ i, t.testBit i = true → n.testBit i = true := by
  constructor
  · intro h i hi
    have h' := congrArg (fun x => x.testBit i) h
    simp only [Nat.testBit_and, hi, Bool.true_and] at h'
    exact h'
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and]
    cases hti : t.testBit i
    · rfl
    · rw [h i hti]
      rfl

theorem testBit_two_mul_add_zero {s a : Nat} (ha : a < 2) :
    (2 * s + a).testBit 0 = decide (a = 1) := by
  rw [Nat.testBit_zero]
  rcases (by omega : a = 0 ∨ a = 1) with rfl | rfl
  · rw [show (2 * s + 0) % 2 = 0 by omega]
  · rw [show (2 * s + 1) % 2 = 1 by omega]

theorem testBit_two_mul_add_succ {s a : Nat} (ha : a < 2) (i : Nat) :
    (2 * s + a).testBit (i + 1) = s.testBit i := by
  rw [Nat.testBit_add_one, show (2 * s + a) / 2 = s by omega]

/-- **One digit**: `2s + a` is a subset of `2n + b` iff `a ≤ b` and `s` is a subset of `n`. -/
theorem sub_digit (s n a b : Nat) (ha : a < 2) (hb : b < 2) :
    (2 * s + a) &&& (2 * n + b) = 2 * s + a ↔ a ≤ b ∧ s &&& n = s := by
  rw [land_eq_self_iff, land_eq_self_iff]
  constructor
  · intro h
    refine ⟨?_, fun i hi => ?_⟩
    · have h0 := h 0
      rw [testBit_two_mul_add_zero ha, testBit_two_mul_add_zero hb] at h0
      rcases (by omega : a = 0 ∨ a = 1) with rfl | rfl
      · omega
      · have h1 := h0 rfl
        rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl
        · exact absurd h1 (by decide)
        · omega
    · have h' := h (i + 1)
      rw [testBit_two_mul_add_succ ha, testBit_two_mul_add_succ hb] at h'
      exact h' hi
  · rintro ⟨hab, hsn⟩ i hi
    cases i with
    | zero =>
      rw [testBit_two_mul_add_zero ha] at hi
      rw [testBit_two_mul_add_zero hb]
      rcases (by omega : a = 0 ∨ a = 1) with rfl | rfl
      · exact absurd hi (by decide)
      · rw [show b = 1 by omega]
        rfl
    | succ i =>
      rw [testBit_two_mul_add_succ ha] at hi
      rw [testBit_two_mul_add_succ hb]
      exact hsn i hi

theorem sub_even_even (s n : Nat) : (2 * s &&& 2 * n = 2 * s) ↔ s &&& n = s := by
  have h := sub_digit s n 0 0 (by omega) (by omega)
  simp only [Nat.add_zero] at h
  rw [h]
  omega

theorem sub_odd_even (s n : Nat) : ¬ (2 * s + 1 &&& 2 * n = 2 * s + 1) := by
  have h := sub_digit s n 1 0 (by omega) (by omega)
  simp only [Nat.add_zero] at h
  rw [h]
  omega

theorem sub_even_odd (s n : Nat) : (2 * s &&& 2 * n + 1 = 2 * s) ↔ s &&& n = s := by
  have h := sub_digit s n 0 1 (by omega) (by omega)
  simp only [Nat.add_zero] at h
  rw [h]
  omega

theorem sub_odd_odd (s n : Nat) : (2 * s + 1 &&& 2 * n + 1 = 2 * s + 1) ↔ s &&& n = s := by
  rw [sub_digit s n 1 1 (by omega) (by omega)]
  omega

/-! ### The transform -/

/-- **The binomial transform over GF(2).** `zeta f n` is the XOR of `f t` over the `t ≤ n` whose
binary digits are digits of `n`. -/
def zeta (f : Nat → Bool) (n : Nat) : Bool :=
  xorSum (fun t => decide (t &&& n = t) && f t) (n + 1)

theorem zeta_zero (f : Nat → Bool) : zeta f 0 = f 0 := by
  show xor false (decide (0 &&& 0 = 0) && f 0) = f 0
  rw [Nat.zero_and]
  cases f 0 <;> rfl

theorem zeta_two_mul (f : Nat → Bool) (n : Nat) :
    zeta f (2 * n) = zeta (fun s => f (2 * s)) n := by
  unfold zeta
  -- the term `t = 2n + 1` does not count, so the range extends to `2 (n + 1)`
  have hext : xorSum (fun t => decide (t &&& 2 * n = t) && f t) (2 * n + 1) =
      xorSum (fun t => decide (t &&& 2 * n = t) && f t) (2 * (n + 1)) := by
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega]
    show _ = xor _ (decide (2 * n + 1 &&& 2 * n = 2 * n + 1) && f (2 * n + 1))
    rw [decide_eq_false (sub_odd_even n n)]
    cases xorSum (fun t => decide (t &&& 2 * n = t) && f t) (2 * n + 1) <;> rfl
  rw [hext, xorSum_two_mul]
  have h0 : xorSum (fun s => decide (2 * s &&& 2 * n = 2 * s) && f (2 * s)) (n + 1) =
      xorSum (fun s => decide (s &&& n = s) && f (2 * s)) (n + 1) :=
    xorSum_congr fun s _ => by rw [decide_eq_decide.mpr (sub_even_even s n)]
  have h1 : xorSum (fun s => decide (2 * s + 1 &&& 2 * n = 2 * s + 1) && f (2 * s + 1)) (n + 1) =
      false := by
    rw [← xorSum_false (n + 1)]
    exact xorSum_congr fun s _ => by rw [decide_eq_false (sub_odd_even s n)]; rfl
  rw [h0, h1]
  cases xorSum (fun s => decide (s &&& n = s) && f (2 * s)) (n + 1) <;> rfl

theorem zeta_two_mul_add_one (f : Nat → Bool) (n : Nat) :
    zeta f (2 * n + 1) = xor (zeta (fun s => f (2 * s)) n) (zeta (fun s => f (2 * s + 1)) n) := by
  unfold zeta
  rw [show 2 * n + 1 + 1 = 2 * (n + 1) by omega, xorSum_two_mul]
  have h0 : xorSum (fun s => decide (2 * s &&& 2 * n + 1 = 2 * s) && f (2 * s)) (n + 1) =
      xorSum (fun s => decide (s &&& n = s) && f (2 * s)) (n + 1) :=
    xorSum_congr fun s _ => by rw [decide_eq_decide.mpr (sub_even_odd s n)]
  have h1 : xorSum (fun s => decide (2 * s + 1 &&& 2 * n + 1 = 2 * s + 1) && f (2 * s + 1))
      (n + 1) = xorSum (fun s => decide (s &&& n = s) && f (2 * s + 1)) (n + 1) :=
    xorSum_congr fun s _ => by rw [decide_eq_decide.mpr (sub_odd_odd s n)]
  rw [h0, h1]

/-! ### Differences split the same way -/

/-- The `2n`-th difference read at even places is the `n`-th difference of the even part. -/
theorem difs_two_mul (f : Nat → Bool) : ∀ n s, difs (2 * n) f (2 * s) = difs n (fun u => f (2 * u)) s
  | 0, _ => rfl
  | n + 1, s => by
    rw [show 2 * (n + 1) = 2 * n + 2 ^ 1 by omega, difs_add, difs_two_pow, difs_xor, difs_shift]
    show xor (difs (2 * n) f (2 * s + 2 ^ 1)) (difs (2 * n) f (2 * s)) =
      xor (difs n (fun u => f (2 * u)) (s + 1)) (difs n (fun u => f (2 * u)) s)
    rw [show 2 * s + 2 ^ 1 = 2 * (s + 1) by omega, difs_two_mul f n (s + 1), difs_two_mul f n s]

theorem difs_two_mul_add_one (f : Nat → Bool) (n : Nat) :
    difs (2 * n + 1) f 0 =
      xor (difs n (fun u => f (2 * u)) 0) (difs n (fun u => f (2 * u + 1)) 0) := by
  rw [difs_succ', show (0 : Nat) = 2 * 0 from rfl, difs_two_mul]
  have h : (fun u => dif f (2 * u)) = fun u => xor (f (2 * u + 1)) (f (2 * u)) := rfl
  rw [h, difs_xor]
  show xor (difs n (fun u => f (2 * u + 1)) 0) (difs n (fun u => f (2 * u)) 0) = _
  cases difs n (fun u => f (2 * u + 1)) 0 <;> cases difs n (fun u => f (2 * u)) 0 <;> rfl

end BinomialDuality

open Ruliology.CellularAutomata Rule30DifferenceOrder BinomialDuality

/-- **The transform is the iterated difference** (Lucas's theorem modulo 2, in transform form):
`zeta f n = difs n f 0`, the `n`-th forward difference of `f` at `0`. -/
theorem binomial_eq_difs (n : Nat) : ∀ f : Nat → Bool, zeta f n = difs n f 0 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro f
    obtain ⟨m, hm | hm⟩ : ∃ m, n = 2 * m ∨ n = 2 * m + 1 := ⟨n / 2, by omega⟩
    · subst hm
      rcases Nat.eq_zero_or_pos m with rfl | hpos
      · exact zeta_zero f
      · rw [zeta_two_mul, ih m (by omega), ← difs_two_mul f m 0]
    · subst hm
      rw [zeta_two_mul_add_one, ih m (by omega), ih m (by omega), difs_two_mul_add_one]

/-- The subset relation is the repository's `TwoIndex.bsub`, which is `C(n, t) mod 2` by Pascal's
rule (`TwoIndex.bsub_pascal`). -/
theorem bsub_eq_land (n : Nat) : ∀ t : Nat, TwoIndex.bsub t n = decide (t &&& n = t) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro t
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · rw [TwoIndex.bsub_zero_right, Nat.and_zero]
      cases t with
      | zero => rfl
      | succ t => rfl
    · rw [TwoIndex.bsub_pos (by omega), ih (n / 2) (by omega) (t / 2)]
      have hd := sub_digit (t / 2) (n / 2) (t % 2) (n % 2) (Nat.mod_lt _ (by omega))
        (Nat.mod_lt _ (by omega))
      rw [show 2 * (t / 2) + t % 2 = t by omega, show 2 * (n / 2) + n % 2 = n by omega] at hd
      rw [decide_eq_decide.mpr hd, Bool.decide_and]

/-! ### Shifts and differences trade places -/

/-- The transform of the shift by one is the difference of the transform. -/
theorem binomial_shift_one (f : Nat → Bool) (n : Nat) :
    zeta (fun t => f (t + 1)) n = xor (zeta f (n + 1)) (zeta f n) := by
  rw [binomial_eq_difs, binomial_eq_difs, binomial_eq_difs, difs_shift]
  show difs n f (0 + 1) = xor (xor (difs n f (0 + 1)) (difs n f 0)) (difs n f 0)
  cases difs n f (0 + 1) <;> cases difs n f 0 <;> rfl

/-- The transform of the difference is the shift of the transform. -/
theorem binomial_dif (f : Nat → Bool) (n : Nat) : zeta (dif f) n = zeta f (n + 1) := by
  rw [binomial_eq_difs, binomial_eq_difs, difs_succ']

theorem binomial_involutive_apply : ∀ (t : Nat) (f : Nat → Bool), zeta (zeta f) t = f t
  | 0, f => by rw [zeta_zero, zeta_zero]
  | t + 1, f => by
    have h : dif (zeta f) = zeta (fun s => f (s + 1)) := by
      funext n
      rw [binomial_shift_one]
      rfl
    rw [← binomial_dif (zeta f) t, h, binomial_involutive_apply t (fun s => f (s + 1))]

/-- **The transform is an involution**: `zeta (zeta f) = f`. -/
theorem binomial_involutive (f : Nat → Bool) : zeta (zeta f) = f :=
  funext fun t => binomial_involutive_apply t f

theorem binomial_injective {f g : Nat → Bool} (h : zeta f = zeta g) : f = g := by
  rw [← binomial_involutive f, h, binomial_involutive]

/-- **Shifts become differences**: `zeta (f (· + k)) = difs k (zeta f)`. -/
theorem binomial_shift (f : Nat → Bool) : ∀ k, zeta (fun t => f (t + k)) = difs k (zeta f)
  | 0 => rfl
  | k + 1 => by
    funext n
    have h := binomial_shift_one (fun t => f (t + k)) n
    rw [binomial_shift f k] at h
    have e : (fun t => f (t + (k + 1))) = fun t => f (t + 1 + k) :=
      funext fun t => congrArg f (by omega)
    rw [e, h]
    rfl

/-- **Differences become shifts**: `zeta (difs k f) n = zeta f (n + k)`. -/
theorem binomial_difs : ∀ (k : Nat) (f : Nat → Bool) (n : Nat), zeta (difs k f) n = zeta f (n + k)
  | 0, _, _ => rfl
  | k + 1, f, n => by
    rw [difs_succ', binomial_difs k (dif f) n, binomial_dif]
    exact congrArg (zeta f) (by omega)

/-- **The duality, operator form**: the transform of `j ↦ difs r f (j + s)` is
`i ↦ difs s (zeta f) (i + r)`. -/
theorem binomial_tail_difs (f : Nat → Bool) (r s : Nat) :
    zeta (fun j => difs r f (j + s)) = fun i => difs s (zeta f) (i + r) := by
  rw [binomial_shift (difs r f) s]
  have h : zeta (difs r f) = fun n => zeta f (n + r) := funext (binomial_difs r f)
  rw [h, difs_shift]

/-! ### The first `1` -/

theorem difs_eq_false_of_prefix {g : Nat → Bool} {N : Nat} (h : ∀ j, j < N → g j = false) :
    ∀ k t, t + k < N → difs k g t = false
  | 0, t, ht => h t (by omega)
  | k + 1, t, ht => by
    show xor (difs k g (t + 1)) (difs k g t) = false
    rw [difs_eq_false_of_prefix h k (t + 1) (by omega), difs_eq_false_of_prefix h k t (by omega)]
    rfl

theorem binomial_eq_false_of_prefix {g : Nat → Bool} {N : Nat} (h : ∀ j, j < N → g j = false) :
    ∀ i, i < N → zeta g i = false := fun i hi => by
  rw [binomial_eq_difs]
  exact difs_eq_false_of_prefix h i 0 (by omega)

/-- **The transform keeps the zero prefix**: `g` vanishes on `[0, N)` iff `zeta g` does. -/
theorem binomial_prefix_iff (g : Nat → Bool) (N : Nat) :
    (∀ j, j < N → g j = false) ↔ ∀ i, i < N → zeta g i = false :=
  ⟨binomial_eq_false_of_prefix, fun h j hj => by
    rw [← binomial_involutive_apply j g]
    exact binomial_eq_false_of_prefix h j hj⟩

namespace BinomialDuality

/-- `j` is the first index at which `g` is `true`. -/
def FirstOne (g : Nat → Bool) (j : Nat) : Prop := g j = true ∧ ∀ i, i < j → g i = false

theorem firstOne_iff_prefix (g : Nat → Bool) (j : Nat) :
    FirstOne g j ↔ (∀ i, i < j → g i = false) ∧ ¬ ∀ i, i < j + 1 → g i = false := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h2, fun hall => ?_⟩
    rw [hall j (by omega)] at h1
    exact Bool.noConfusion h1
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h1⟩
    cases hj : g j
    · exfalso
      apply h2
      intro i hi
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi | rfl
      · exact h1 i hi
      · exact hj
    · rfl

end BinomialDuality

/-- **The transform keeps the first `1`**: `g` and `zeta g` have their first `1` at the same
index. -/
theorem binomial_firstOne_iff (g : Nat → Bool) (j : Nat) : FirstOne g j ↔ FirstOne (zeta g) j := by
  rw [firstOne_iff_prefix, firstOne_iff_prefix, binomial_prefix_iff g j, binomial_prefix_iff g (j + 1)]

/-! ### The duality -/

/-- **The duality, finite form**: the `r`-th difference of `f` vanishes on `[s, s + N)` iff the
`s`-th difference of `zeta f` vanishes on `[r, r + N)`. -/
theorem binomial_window_iff (f : Nat → Bool) (r s N : Nat) :
    (∀ j, j < N → difs r f (j + s) = false) ↔ ∀ i, i < N → difs s (zeta f) (i + r) = false := by
  rw [binomial_prefix_iff (fun j => difs r f (j + s)) N, binomial_tail_difs]

/-- **The duality**: the `r`-th difference of `f` vanishes on `[s, ∞)` iff the `s`-th difference
of `zeta f` vanishes on `[r, ∞)`. -/
theorem binomial_tail_iff (f : Nat → Bool) (r s : Nat) :
    (∀ t, s ≤ t → difs r f t = false) ↔ ∀ n, r ≤ n → difs s (zeta f) n = false := by
  constructor
  · intro h n hn
    have h' := (binomial_window_iff f r s (n - r + 1)).1 (fun j _ => h (j + s) (by omega))
      (n - r) (by omega)
    rwa [show n - r + r = n by omega] at h'
  · intro h t ht
    have h' := (binomial_window_iff f r s (t - s + 1)).2 (fun i _ => h (i + r) (by omega))
      (t - s) (by omega)
    rwa [show t - s + s = t by omega] at h'

namespace BinomialDuality

theorem xor_eq_false_iff {x y : Bool} : xor x y = false ↔ x = y := by
  cases x <;> cases y <;> decide

theorem xor_eq_true_iff {x y : Bool} : xor x y = true ↔ x ≠ y := by
  cases x <;> cases y <;> decide

/-- `t = s + j` is the least `t ≥ s` with `f (t + P) ≠ f t`. -/
def FirstMismatch (f : Nat → Bool) (s P j : Nat) : Prop :=
  f (s + j + P) ≠ f (s + j) ∧ ∀ i, i < j → f (s + i + P) = f (s + i)

/-- `f` has an eventual period that is a power of two. -/
def TwoPowPeriodic (f : Nat → Bool) : Prop := ∃ T a, ∀ t, T ≤ t → f (t + 2 ^ a) = f t

end BinomialDuality

/-- **The duality for powers of two, finite form**: `f` agrees with its shift by `2^a` on
`[2^m, 2^m + N)` iff `zeta f` agrees with its shift by `2^m` on `[2^a, 2^a + N)`. -/
theorem binomial_period_window_iff (f : Nat → Bool) (a m N : Nat) :
    (∀ j, j < N → f (2 ^ m + j + 2 ^ a) = f (2 ^ m + j)) ↔
      ∀ i, i < N → zeta f (2 ^ a + i + 2 ^ m) = zeta f (2 ^ a + i) := by
  have h := binomial_window_iff f (2 ^ a) (2 ^ m) N
  simp only [difs_two_pow, xor_eq_false_iff] at h
  constructor
  · intro hf i hi
    rw [Nat.add_comm (2 ^ a) i]
    exact (h.1 fun j hj => by rw [Nat.add_comm j]; exact hf j hj) i hi
  · intro hg j hj
    rw [Nat.add_comm (2 ^ m) j]
    exact (h.2 fun i hi => by rw [Nat.add_comm i]; exact hg i hi) j hj

/-- **The duality for powers of two**: `f` has period `2^a` on `[2^m, ∞)` iff `zeta f` has period
`2^m` on `[2^a, ∞)`. -/
theorem binomial_period_iff (f : Nat → Bool) (a m : Nat) :
    (∀ t, 2 ^ m ≤ t → f (t + 2 ^ a) = f t) ↔ ∀ n, 2 ^ a ≤ n → zeta f (n + 2 ^ m) = zeta f n := by
  have h := binomial_tail_iff f (2 ^ a) (2 ^ m)
  simp only [difs_two_pow, xor_eq_false_iff] at h
  exact h

/-- **The least witnesses agree**: the least `t ≥ 2^m` with `f (t + 2^a) ≠ f t` and the least
`n ≥ 2^a` with `zeta f (n + 2^m) ≠ zeta f n` have the same offset `j`. -/
theorem binomial_firstMismatch_iff (f : Nat → Bool) (a m j : Nat) :
    FirstMismatch f (2 ^ m) (2 ^ a) j ↔ FirstMismatch (zeta f) (2 ^ a) (2 ^ m) j := by
  have h := binomial_firstOne_iff (fun j => difs (2 ^ a) f (j + 2 ^ m)) j
  rw [binomial_tail_difs] at h
  simp only [FirstOne, difs_two_pow, xor_eq_false_iff, xor_eq_true_iff] at h
  unfold FirstMismatch
  simp only [Nat.add_comm (2 ^ m), Nat.add_comm (2 ^ a)]
  exact h

/-- `f` vanishes on `[2^m, ∞)` iff `zeta f` has period `2^m`. -/
theorem binomial_support_iff (f : Nat → Bool) (m : Nat) :
    (∀ t, 2 ^ m ≤ t → f t = false) ↔ ∀ n, zeta f (n + 2 ^ m) = zeta f n := by
  have h := binomial_tail_iff f 0 (2 ^ m)
  simp only [difs_two_pow, xor_eq_false_iff, Nat.zero_le, true_implies] at h
  exact h

/-- `f` has period `2^a` iff `zeta f` vanishes on `[2^a, ∞)`. -/
theorem binomial_periodic_iff (f : Nat → Bool) (a : Nat) :
    (∀ t, f (t + 2 ^ a) = f t) ↔ ∀ n, 2 ^ a ≤ n → zeta f n = false := by
  have h := binomial_tail_iff f (2 ^ a) 0
  simp only [difs_two_pow, xor_eq_false_iff, Nat.zero_le, true_implies] at h
  exact h

/-- **An eventual period that is a power of two is self-dual**: `zeta f` has one iff `f` has
one. A period `2^a` of `f` from `2^m` is a period `2^m` of `zeta f` from `2^a`. -/
theorem binomial_twoPow_iff (f : Nat → Bool) : TwoPowPeriodic (zeta f) ↔ TwoPowPeriodic f := by
  have hdir : ∀ g : Nat → Bool, TwoPowPeriodic g → TwoPowPeriodic (zeta g) := by
    rintro g ⟨T, a, h⟩
    refine ⟨2 ^ a, T, (binomial_period_iff g a T).1 fun t ht => h t ?_⟩
    exact Nat.le_trans (Nat.le_of_lt Nat.lt_two_pow_self) ht
  constructor
  · intro h
    have := hdir (zeta f) h
    rwa [binomial_involutive] at this
  · exact hdir f

/-! ### Eventual periodicity of any period -/

namespace BinomialDuality

/-- Two sequences with period `P` from `T` that agree on `[0, T + P)` agree everywhere. -/
theorem eq_of_agree_window {g h : Nat → Bool} {T P : Nat} (hP : 0 < P)
    (hg : ∀ t, T ≤ t → g (t + P) = g t) (hh : ∀ t, T ≤ t → h (t + P) = h t)
    (hw : ∀ t, t < T + P → g t = h t) (t : Nat) : g t = h t := by
  induction t using Nat.strongRecOn with
  | ind t ih =>
    by_cases ht : t < T + P
    · exact hw t ht
    · have e : t = (t - P) + P := by omega
      rw [e, hg (t - P) (by omega), hh (t - P) (by omega), ih (t - P) (by omega)]

/-- Differences keep a period from `T`. -/
theorem difs_period {f : Nat → Bool} {T P : Nat} (h : ∀ t, T ≤ t → f (t + P) = f t) :
    ∀ k t, T ≤ t → difs k f (t + P) = difs k f t
  | 0, t, ht => h t ht
  | k + 1, t, ht => by
    show xor (difs k f (t + P + 1)) (difs k f (t + P)) = xor (difs k f (t + 1)) (difs k f t)
    rw [show t + P + 1 = t + 1 + P by omega, difs_period h k (t + 1) (by omega),
      difs_period h k t ht]

end BinomialDuality

/-- The transform of an eventually periodic sequence is eventually periodic: every difference
`difs k f` has the period of `f`, so it is fixed by its values on `[0, T + P)`, and among
`2^(T + P) + 1` such windows two are equal (the kit's `Rule30Jen.pigeonhole`). -/
theorem binomial_eventuallyPeriodic {f : Nat → Bool} (hf : Rule30Jen.EventuallyPeriodic f) :
    Rule30Jen.EventuallyPeriodic (zeta f) := by
  obtain ⟨T, P, hP, hper⟩ := hf
  obtain ⟨m, n, hmn, -, he⟩ := Rule30Jen.pigeonhole (T + P)
    (fun k => (List.range (T + P)).map (difs k f)) (fun k => by simp)
  have hw : ∀ t, t < T + P → difs m f t = difs n f t :=
    fun t ht => (List.map_inj_left.1 he) t (List.mem_range.2 ht)
  have hall : difs n f = difs m f :=
    funext fun t => (eq_of_agree_window hP (difs_period hper m) (difs_period hper n) hw t).symm
  refine ⟨m, n - m, by omega, fun t ht => ?_⟩
  rw [binomial_eq_difs, binomial_eq_difs]
  have e1 : difs (t + (n - m)) f 0 = difs (t - m) (difs n f) 0 := by
    rw [← difs_add, show t - m + n = t + (n - m) by omega]
  have e2 : difs t f 0 = difs (t - m) (difs m f) 0 := by
    rw [← difs_add, show t - m + m = t by omega]
  rw [e1, e2, hall]

/-- **Eventual periodicity is self-dual**: `zeta f` is eventually periodic iff `f` is. Only the
powers of two in the period keep their exact form (`binomial_period_iff`). -/
theorem binomial_eventuallyPeriodic_iff (f : Nat → Bool) :
    Rule30Jen.EventuallyPeriodic (zeta f) ↔ Rule30Jen.EventuallyPeriodic f := by
  constructor
  · intro h
    have := binomial_eventuallyPeriodic h
    rwa [binomial_involutive] at this
  · exact binomial_eventuallyPeriodic

/-! ### The center column -/

namespace BinomialDuality

/-- The binomial transform of the center column: `gamma n` is the XOR of `c(t)` over the `t` whose
binary digits are digits of `n`. -/
def gamma : Nat → Bool := zeta Rule30Prize.center

end BinomialDuality

/-- The transform of `gamma` is the center column. -/
theorem center_binomial_involutive : zeta gamma = Rule30Prize.center :=
  binomial_involutive Rule30Prize.center

/-- **The center column**: `c` has period `2^a` on `[2^m, ∞)` iff `gamma` has period `2^m` on
`[2^a, ∞)`. -/
theorem center_binomial_period_iff (a m : Nat) :
    (∀ t, 2 ^ m ≤ t → Rule30Prize.center (t + 2 ^ a) = Rule30Prize.center t) ↔
      ∀ n, 2 ^ a ≤ n → gamma (n + 2 ^ m) = gamma n :=
  binomial_period_iff Rule30Prize.center a m

/-- **The first rung, at `k + 1`**: `c` is not `2^(k+1)`-periodic from `2^k` iff `gamma` is not
`2^k`-periodic from `2^(k+1)`. -/
theorem center_binomial_rung_iff (k : Nat) :
    (∃ t, 2 ^ k ≤ t ∧ Rule30Prize.center (t + 2 ^ (k + 1)) ≠ Rule30Prize.center t) ↔
      ∃ n, 2 ^ (k + 1) ≤ n ∧ gamma (n + 2 ^ k) ≠ gamma n := by
  have h := center_binomial_period_iff (k + 1) k
  constructor
  · rintro ⟨t, ht, hne⟩
    apply Classical.byContradiction
    intro hno
    apply hne
    refine h.2 (fun n hn => ?_) t ht
    apply Classical.byContradiction
    exact fun hn' => hno ⟨n, hn, hn'⟩
  · rintro ⟨n, hn, hne⟩
    apply Classical.byContradiction
    intro hno
    apply hne
    refine h.1 (fun t ht => ?_) n hn
    apply Classical.byContradiction
    exact fun ht' => hno ⟨t, ht, ht'⟩

/-- **The least witnesses of the rung agree**: the least `t ≥ 2^k` with `c(t + 2^(k+1)) ≠ c(t)` and
the least `n ≥ 2^(k+1)` with `gamma (n + 2^k) ≠ gamma n` have the same offset. -/
theorem center_binomial_firstMismatch_iff (k j : Nat) :
    FirstMismatch Rule30Prize.center (2 ^ k) (2 ^ (k + 1)) j ↔
      FirstMismatch gamma (2 ^ (k + 1)) (2 ^ k) j :=
  binomial_firstMismatch_iff Rule30Prize.center (k + 1) k j

/-- `c` has an eventual period that is a power of two iff `gamma` has one. -/
theorem center_binomial_twoPow_iff : TwoPowPeriodic gamma ↔ TwoPowPeriodic Rule30Prize.center :=
  binomial_twoPow_iff Rule30Prize.center

/-- **Problem 1 is self-dual**: it holds iff `gamma` is not eventually periodic. -/
theorem problem1_iff_gamma : Rule30Prize.Problem1 ↔ ¬ Rule30Jen.EventuallyPeriodic gamma := by
  unfold Rule30Prize.Problem1
  rw [show gamma = zeta Rule30Prize.center from rfl, binomial_eventuallyPeriodic_iff]

/-- **From the kit's period-one case**: for no `m` does `gamma` have period `2^m` on `[1, ∞)`. -/
theorem gamma_not_period_from_one (m : Nat) : ¬ ∀ n, 1 ≤ n → gamma (n + 2 ^ m) = gamma n := by
  intro h
  have hc := (center_binomial_period_iff 0 m).2 h
  exact Rule30Prize.center_not_eventually_period_one ⟨2 ^ m, hc⟩

/-- Problem 1 implies that `gamma` has no eventual period that is a power of two. -/
theorem gamma_not_twoPow_of_problem1 (h : Rule30Prize.Problem1) : ¬ TwoPowPeriodic gamma := by
  rw [center_binomial_twoPow_iff]
  rintro ⟨T, a, hT⟩
  exact h ⟨T, 2 ^ a, Nat.two_pow_pos a, hT⟩

/-- **Window bounds transfer**: if `gamma` has period `2^m` on `[2^a, ∞)`, then
`2^a + 2^m ≥ 262125`, the bound `transient_add_period_ge_262125` on the center column. -/
theorem gamma_period_ge_262125 (a m : Nat) (h : ∀ n, 2 ^ a ≤ n → gamma (n + 2 ^ m) = gamma n) :
    262125 ≤ 2 ^ m + 2 ^ a :=
  transient_add_period_ge_262125 (2 ^ m) (2 ^ a) (Nat.two_pow_pos a)
    ((center_binomial_period_iff a m).2 h)

/-- **The first rung up to level 17**: for `k ≤ 16`, `c` is not `2^(k+1)`-periodic from `2^k`,
since `2^k + 2^(k+1) ≤ 3 · 2^16 < 262125`. -/
theorem center_rung_le_seventeen (k : Nat) (hk : k ≤ 16) :
    ∃ t, 2 ^ k ≤ t ∧ Rule30Prize.center (t + 2 ^ (k + 1)) ≠ Rule30Prize.center t := by
  apply Classical.byContradiction
  intro hno
  have hper : ∀ t, 2 ^ k ≤ t → Rule30Prize.center (t + 2 ^ (k + 1)) = Rule30Prize.center t :=
    fun t ht => Classical.byContradiction fun hne => hno ⟨t, ht, hne⟩
  have hb := transient_add_period_ge_262125 (2 ^ k) (2 ^ (k + 1)) (Nat.two_pow_pos (k + 1)) hper
  have hle : 2 ^ k ≤ 2 ^ 16 := Nat.pow_le_pow_right (by omega) hk
  rw [Nat.pow_succ] at hb
  omega

/-- **The dual rung up to level 17**: for `k ≤ 16`, `gamma` is not `2^k`-periodic from
`2^(k+1)`. -/
theorem gamma_rung_le_seventeen (k : Nat) (hk : k ≤ 16) :
    ∃ n, 2 ^ (k + 1) ≤ n ∧ gamma (n + 2 ^ k) ≠ gamma n :=
  (center_binomial_rung_iff k).1 (center_rung_le_seventeen k hk)

end Rule30Open
