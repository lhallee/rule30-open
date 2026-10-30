module

public import Rule30Open.Frames.SeedPast

/-!
# The periods of the single cell's past grow without bound

`rho k`, the row `k` steps before the single cell in the moving frame, is eventually periodic (`SeedPast`). Here:

* `rho_not_evZero`: for `k ≥ 1`, `rho k` has infinitely many black cells. A row with a top black cell keeps one, two
  cells higher at each step (`phiF_topAt`), so no such row, and no white one, reaches the single cell.
* `rho_period_bound`: if `rho k` repeats with period `p` from some cell on, then `k ≤ 2 ^ p`. The tails of
  `rho k, rho (k - 1), ..., rho 1`, read on one window of `p` cells far out, are pairwise distinct: if two agreed, the
  same number of steps that takes the later one to the single cell would take the earlier one to a row white far out,
  some `rho j` with `j ≥ 1` (`agree_iter`, `rho_iter`). There are `2 ^ p` windows (`pigeonhole`).
* `rho_no_short_period`: so once `k > 2 ^ p`, `rho k` has no period of `p` cells or fewer.

On a ring of `p` cells the tail of `rho k` therefore takes exactly `k` steps to die out, and the periods of the single
cell's past are unbounded.

The natural-language argument is `SeedPastPeriods.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

/-! ### Rows with a top black cell -/

/-- `y` is black at bit `n` and white above it. -/
def TopAt (y : Nat → Bool) (n : Nat) : Prop := y n = true ∧ ∀ i, n < i → y i = false

/-- One step moves the top black cell up by two. -/
theorem phiF_topAt {y : Nat → Bool} {n : Nat} (h : TopAt y n) : TopAt (phiF y) (n + 2) := by
  obtain ⟨h1, h0⟩ := h
  refine ⟨?_, fun i hi => ?_⟩
  · show xor (y (n + 2)) (y (n + 1) || y n) = true
    rw [h0 (n + 2) (by omega), h0 (n + 1) (by omega), h1]
    rfl
  · match i, hi with
    | 0, hi => exact absurd hi (by omega)
    | 1, hi => exact absurd hi (by omega)
    | i + 2, hi =>
      show xor (y (i + 2)) (y (i + 1) || y i) = false
      rw [h0 (i + 2) (by omega), h0 (i + 1) (by omega), h0 i (by omega)]
      rfl

theorem phiIter_topAt : ∀ k {y : Nat → Bool} {n : Nat}, TopAt y n → TopAt (phiIter k y) (n + 2 * k)
  | 0, _, _, h => h
  | k + 1, y, n, h => by
    have e := phiIter_topAt k (phiF_topAt h)
    rw [show n + 2 + 2 * k = n + 2 * (k + 1) by omega] at e
    exact e

theorem phiIter_white : ∀ k {y : Nat → Bool}, (∀ i, y i = false) → ∀ i, phiIter k y i = false
  | 0, _, h => h
  | k + 1, y, h => by
    refine phiIter_white k (y := phiF y) fun i => ?_
    match i with
    | 0 => exact h 0
    | 1 => show xor (y 1) (y 0) = false; rw [h 1, h 0]; rfl
    | i + 2 => show xor (y (i + 2)) (y (i + 1) || y i) = false; rw [h (i + 2), h (i + 1), h i]; rfl

/-- A row white from bit `N` on with a black bit has a top black bit. -/
theorem exists_top {y : Nat → Bool} : ∀ N, (∀ i, N ≤ i → y i = false) → (∃ i, y i = true) → ∃ n, TopAt y n
  | 0, h, ⟨i, hi⟩ => by rw [h i (Nat.zero_le _)] at hi; exact absurd hi Bool.false_ne_true
  | N + 1, h, hex => by
    cases hN : y N with
    | true => exact ⟨N, hN, fun i hi => h i (by omega)⟩
    | false =>
      refine exists_top N (fun i hi => ?_) hex
      rcases Nat.eq_or_lt_of_le hi with e | e
      · rw [← e]; exact hN
      · exact h i (by omega)

/-- `y` is white from some bit on. -/
def EvZero (y : Nat → Bool) : Prop := ∃ N, ∀ i, N ≤ i → y i = false

/-- **One step back or more, the single cell's past has infinitely many black cells.** -/
theorem rho_not_evZero (k : Nat) (hk : 0 < k) : ¬ EvZero (rho k) := by
  rintro ⟨N, hN⟩
  have hs := phiIter_rho k
  by_cases hb : ∃ i, rho k i = true
  · obtain ⟨n, hn⟩ := exists_top N hN hb
    have ht := (phiIter_topAt k hn).1
    rw [hs] at ht
    have e : n + 2 * k = 0 := of_decide_eq_true ht
    omega
  · have hw : ∀ i, rho k i = false := fun i => by
      cases h : rho k i with
      | false => rfl
      | true => exact absurd ⟨i, h⟩ hb
    have h0 := phiIter_white k hw 0
    rw [hs] at h0
    exact absurd h0 (by decide)

/-! ### Periods move out two cells per step -/

/-- `phiF` keeps a period, two bits further out. -/
theorem phiF_period {y : Nat → Bool} {N p : Nat} (h : ∀ j, N ≤ j → y (j + p) = y j) :
    ∀ j, N + 2 ≤ j → phiF y (j + p) = phiF y j := by
  intro j hj
  match j, hj with
  | j + 2, hj =>
    rw [show j + 2 + p = (j + p) + 2 by omega]
    show xor (y (j + p + 2)) (y (j + p + 1) || y (j + p)) = xor (y (j + 2)) (y (j + 1) || y j)
    rw [show j + p + 2 = (j + 2) + p by omega, show j + p + 1 = (j + 1) + p by omega,
      h (j + 2) (by omega), h (j + 1) (by omega), h j (by omega)]

theorem phiF_rho_succ (j : Nat) : phiF (rho (j + 1)) = rho j := phiF_phiInv (rho j)

/-- `d` steps take `rho k` to `rho (k - d)`. -/
theorem rho_iter : ∀ d k, d ≤ k → phiIter d (rho k) = rho (k - d)
  | 0, k, _ => rfl
  | d + 1, k, h => by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    show phiIter d (phiF (rho (j + 1))) = _
    rw [phiF_rho_succ, rho_iter d j (by omega), show j + 1 - (d + 1) = j - d by omega]

/-- If `rho k` repeats with period `p` from bit `N`, then `rho (k - m)` does from bit `N + 2 m`. -/
theorem rho_sub_period {k N p : Nat} (h : ∀ j, N ≤ j → rho k (j + p) = rho k j) :
    ∀ m, m ≤ k → ∀ j, N + 2 * m ≤ j → rho (k - m) (j + p) = rho (k - m) j
  | 0, _, j, hj => h j (by omega)
  | m + 1, hm, j, hj => by
    have e : rho (k - (m + 1)) = phiF (rho (k - m)) := by
      rw [show k - m = (k - (m + 1)) + 1 by omega, phiF_rho_succ]
    rw [e]
    exact phiF_period (rho_sub_period h m (by omega)) j (by omega)

/-! ### Agreement far out -/

/-- Two rows that agree from bit `M` on agree from bit `M + 2` on after one step. -/
theorem phiF_agree {y y' : Nat → Bool} {M : Nat} (h : ∀ j, M ≤ j → y j = y' j) :
    ∀ j, M + 2 ≤ j → phiF y j = phiF y' j := by
  intro j hj
  match j, hj with
  | j + 2, hj =>
    show xor (y (j + 2)) (y (j + 1) || y j) = xor (y' (j + 2)) (y' (j + 1) || y' j)
    rw [h (j + 2) (by omega), h (j + 1) (by omega), h j (by omega)]

theorem agree_iter : ∀ d {y y' : Nat → Bool} {M : Nat}, (∀ j, M ≤ j → y j = y' j) →
    ∀ j, M + 2 * d ≤ j → phiIter d y j = phiIter d y' j
  | 0, _, _, _, h => fun j hj => h j (by omega)
  | d + 1, _, _, _, h => fun j hj =>
    agree_iter d (phiF_agree h) j (by omega)

/-- Two rows with period `p` from bit `M` that agree on bits `M .. M + p - 1` agree from bit `M` on. -/
theorem agree_of_period {y y' : Nat → Bool} {M p : Nat} (hp : 0 < p) (hy : ∀ j, M ≤ j → y (j + p) = y j)
    (hy' : ∀ j, M ≤ j → y' (j + p) = y' j) (h : ∀ r, r < p → y (M + r) = y' (M + r)) :
    ∀ j, M ≤ j → y j = y' j := by
  have key : ∀ q r, r < p → y (M + r + q * p) = y' (M + r + q * p) := by
    intro q r hr
    induction q with
    | zero => rw [Nat.zero_mul, Nat.add_zero]; exact h r hr
    | succ q ih =>
      rw [show M + r + (q + 1) * p = (M + r + q * p) + p by rw [Nat.succ_mul]; omega,
        hy _ (by omega), hy' _ (by omega), ih]
  intro j hj
  have e := key ((j - M) / p) ((j - M) % p) (Nat.mod_lt _ hp)
  rw [show M + (j - M) % p + (j - M) / p * p = j by
    have := Nat.div_add_mod (j - M) p
    rw [Nat.mul_comm] at this
    omega] at e
  exact e

/-! ### Windows as numbers, and the pigeonhole -/

/-- Bits `M .. M + n - 1` of `y` as a number, bit `r` being `y (M + r)`. -/
def window (y : Nat → Bool) (M : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => window y M n + (y (M + n)).toNat * 2 ^ n

theorem window_lt (y : Nat → Bool) (M : Nat) : ∀ n, window y M n < 2 ^ n
  | 0 => by show (0 : Nat) < 2 ^ 0; decide
  | n + 1 => by
    have h := window_lt y M n
    show window y M n + (y (M + n)).toNat * 2 ^ n < 2 ^ (n + 1)
    rw [Nat.pow_succ]
    cases y (M + n) <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.zero_mul, Nat.one_mul] <;> omega

theorem window_split (y : Nat → Bool) (M n : Nat) :
    window y M (n + 1) % 2 ^ n = window y M n ∧ window y M (n + 1) / 2 ^ n = (y (M + n)).toNat := by
  have hlt := window_lt y M n
  have hpos : 0 < 2 ^ n := Nat.two_pow_pos n
  show (window y M n + (y (M + n)).toNat * 2 ^ n) % 2 ^ n = _ ∧
    (window y M n + (y (M + n)).toNat * 2 ^ n) / 2 ^ n = _
  cases y (M + n) with
  | false =>
    simp only [Bool.toNat_false, Nat.zero_mul, Nat.add_zero]
    exact ⟨Nat.mod_eq_of_lt hlt, Nat.div_eq_of_lt hlt⟩
  | true =>
    simp only [Bool.toNat_true, Nat.one_mul]
    exact ⟨by rw [Nat.add_mod_right, Nat.mod_eq_of_lt hlt], by rw [Nat.add_div_right _ hpos, Nat.div_eq_of_lt hlt]⟩

/-- Equal windows have equal bits. -/
theorem window_inj {y y' : Nat → Bool} {M : Nat} :
    ∀ n, window y M n = window y' M n → ∀ r, r < n → y (M + r) = y' (M + r)
  | 0, _, r, h => absurd h (by omega)
  | n + 1, he, r, hr => by
    have s := window_split y M n
    have s' := window_split y' M n
    rw [he] at s
    by_cases h : r < n
    · exact window_inj n (s.1.symm.trans s'.1) r h
    · have e : r = n := by omega
      subst e
      have hb := s.2.symm.trans s'.2
      cases a : y (M + r) <;> cases b : y' (M + r) <;> rw [a, b] at hb <;> first | rfl | exact absurd hb (by decide)

/-- `n` distinct numbers below `B`: `n ≤ B`. -/
theorem pigeonhole : ∀ n B (g : Nat → Nat), (∀ i, i < n → g i < B) →
    (∀ i j, i < j → j < n → g i ≠ g j) → n ≤ B
  | 0, _, _, _, _ => Nat.zero_le _
  | n + 1, B, g, hlt, hne => by
    have hB : g n < B := hlt n (by omega)
    have h1 : ∀ i, i < n → (if g i < g n then g i else g i - 1) < B - 1 := by
      intro i hi
      have := hlt i (by omega)
      have := hne i n hi (by omega)
      split <;> omega
    have h2 : ∀ i j, i < j → j < n →
        (if g i < g n then g i else g i - 1) ≠ (if g j < g n then g j else g j - 1) := by
      intro i j hij hj
      have := hne i j hij (by omega)
      have := hne i n (by omega) (by omega)
      have := hne j n hj (by omega)
      split <;> split <;> omega
    have := pigeonhole n (B - 1) (fun i => if g i < g n then g i else g i - 1) h1 h2
    omega

/-! ### The bound -/

/-- **A period of `rho k` has at least `log2 k` cells**: if `rho k` repeats with period `p` from some bit on, then
`k ≤ 2 ^ p`. The windows of `p` bits at bit `N + 2k` of `rho k, rho (k - 1), ..., rho 1` are pairwise distinct. -/
theorem rho_period_bound (k N p : Nat) (hp : 0 < p) (h : ∀ j, N ≤ j → rho k (j + p) = rho k j) : k ≤ 2 ^ p := by
  have hper : ∀ m, m ≤ k → ∀ j, N + 2 * k ≤ j → rho (k - m) (j + p) = rho (k - m) j :=
    fun m hm j hj => rho_sub_period h m hm j (by omega)
  refine pigeonhole k (2 ^ p) (fun m => window (rho (k - m)) (N + 2 * k) p) (fun i _ => window_lt _ _ p) ?_
  intro a b hab hb he
  have hag := agree_of_period hp (hper a (by omega)) (hper b (by omega)) (window_inj p he)
  have hit := agree_iter (k - b) hag
  rw [rho_iter (k - b) (k - a) (by omega), rho_iter (k - b) (k - b) (Nat.le_refl _), Nat.sub_self] at hit
  apply rho_not_evZero (k - a - (k - b)) (by omega)
  refine ⟨N + 2 * k + 2 * (k - b) + 1, fun i hi => ?_⟩
  rw [hit i (by omega)]
  show decide (i = 0) = false
  exact decide_eq_false (by omega)

/-- **The periods of the single cell's past are unbounded**: once `k > 2 ^ p`, `rho k` has no period of `p` cells or
fewer, from any bit on. -/
theorem rho_no_short_period (p k : Nat) (hk : 2 ^ p < k) (q N : Nat) (hq : 0 < q) (hqp : q ≤ p) :
    ¬ ∀ j, N ≤ j → rho k (j + q) = rho k j := by
  intro h
  have h1 := rho_period_bound k N q hq h
  have h2 : 2 ^ q ≤ 2 ^ p := Nat.pow_le_pow_right (by decide) hqp
  omega

end Rule30Open
