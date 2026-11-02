module

public import Rule30Open.Frames.SeedPastRing

/-!
# The periods and preperiods of the single cell's past, checked in the kernel to depth 3,000

`rho k` is the row `k` steps before the single cell in the moving frame (`SeedPast`). Here the kernel checks the table
of [the finding](../../findings/frames/seed-past.md): the minimal period of `rho k` is 1, 3, 6, 12, 24 and 48 from
`k` = 1, 2, 4, 10, 18 and 66 to `k = 3000` (`rho_min_period`), its preperiod is 0 or 1 for `k ≤ 28` and 4, 188,
1509, 4968 and 15615 at `k` = 30, 66, 300, 1000 and 3000 (`rho_preperiod_small`, `rho_preperiods`), and the tail of
every `rho k` with `66 ≤ k ≤ 3000` is a row of a ring of 48 cells that Rule 30 turns white in exactly `k` steps
(`ring48_dies`).

* **Certificates** (`SeedTable.bits`, `seedCerts`). A certificate `(k, N, P, a, w)` claims that bit `j` of `rho k` is
  bit `j` of `a` below `N` and bit `(j - N) % P` of `w` from `N` on. The list holds one for each `k ≤ 66` and for
  `k` = 300, 1000 and 3000, written by `computations/seed_past_lean.py`.
* **Links** (`SeedTable.linkOk`, `SeedTable.link_sound`). From the certificate of `k + d` to that of `k`: `d` steps
  of `phiF` on the first `B` bits, a number of `B` bits stepped by shifts and masks (`SeedTable.iterW`), give the
  first `B` bits of the lower certificate, with `B` past both preperiods by a full period of the upper one and its
  period a multiple of the lower one's. Two rows with a common period that agree on a full period agree from there on
  (`agree_of_period`), so the `d` steps take the upper row to the lower one exactly. A chain of links from the single
  cell names `rho k` for every certificate (`SeedTable.chain_sound`, `phiIter_eq_rho`).
* **Minimality** (`SeedTable.minPerOk`, `SeedTable.preOk`). No `q < P` is a period of the window of `P` bits at `N`,
  so no `q < P` is a period from any bit on; and bit `N - 1` differs from bit `N - 1 + P`.
* Between the certificates the period passes down (`rho_sub_period`): a period of `rho 3000` is one of every
  `rho k` with `k ≤ 3000`, and a period of `rho k` is one of `rho 66` for `k ≥ 66`.
* For every `k`, the least period of `rho k` divides that of `rho (k + 1)` (`rho_min_period_dvd`): the least period
  divides every period (`minTailPeriod_dvd`), since two periods give their greatest common divisor
  (`tailPeriod_gcd`). For every `k ≥ 66`, beyond the checked range too, every period of `rho k` is a multiple of 48
  (`rho_period_dvd_of_ge`).

The natural-language argument is `SeedPastTable.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

/-- `y` repeats with period `p` from bit `N` on. -/
def TailPeriod (y : Nat → Bool) (N p : Nat) : Prop := ∀ j, N ≤ j → y (j + p) = y j

/-- `p` is the least period with which `y` repeats from some bit on. -/
def MinTailPeriod (y : Nat → Bool) (p : Nat) : Prop :=
  0 < p ∧ (∃ N, TailPeriod y N p) ∧ ∀ q N, 0 < q → q < p → ¬ TailPeriod y N q

/-- `N` is the first bit from which `y` repeats with period `p`. -/
def IsPreperiod (y : Nat → Bool) (N p : Nat) : Prop := TailPeriod y N p ∧ ∀ N', TailPeriod y N' p → N ≤ N'

/-- `phiIter d` keeps a period, `2 d` bits further out. -/
theorem phiIter_period : ∀ d {y : Nat → Bool} {N p : Nat}, TailPeriod y N p → TailPeriod (phiIter d y) (N + 2 * d) p
  | 0, _, _, _, h => h
  | d + 1, y, N, p, h => by
    have e := phiIter_period d (y := phiF y) (phiF_period h)
    intro j hj
    exact e j (by omega)

/-- A row that `d` steps take to `rho k` is `rho (k + d)`. -/
theorem phiIter_eq_rho : ∀ d k {y : Nat → Bool}, phiIter d y = rho k → y = rho (k + d)
  | 0, _, _, h => h
  | d + 1, k, y, h => by
    have e := phiIter_eq_rho d k (y := phiF y) h
    rw [← phiInv_phiF y, e]
    rfl

theorem tailPeriod_mono {y : Nat → Bool} {N N' p : Nat} (h : TailPeriod y N p) (hN : N ≤ N') : TailPeriod y N' p :=
  fun j hj => h j (by omega)

theorem tailPeriod_mul {y : Nat → Bool} {N p : Nat} (h : TailPeriod y N p) (m : Nat) : TailPeriod y N (m * p) :=
  fun j hj => evPer_mul h m j hj

theorem tailPeriod_sub {y : Nat → Bool} {N a b : Nat} (ha : TailPeriod y N a) (hb : TailPeriod y N b) (hab : a ≤ b) :
    TailPeriod y N (b - a) := by
  intro j hj
  have e := ha (j + (b - a)) (by omega)
  rw [show j + (b - a) + a = j + b by omega, hb j hj] at e
  exact e.symm

/-- Two periods from the same bit give their greatest common divisor as a period from there. -/
theorem tailPeriod_gcd {y : Nat → Bool} {N : Nat} (m n : Nat) :
    TailPeriod y N m → TailPeriod y N n → TailPeriod y N (Nat.gcd m n) := by
  induction m, n using Nat.gcd.induction with
  | H0 n => intro _ hn; rwa [Nat.gcd_zero_left]
  | H1 m n hm ih =>
    intro h1 h2
    rw [Nat.gcd_rec]
    refine ih ?_ h1
    have hd := Nat.div_add_mod n m
    have hsub := tailPeriod_sub (tailPeriod_mul h1 (n / m)) h2 (by
      rw [Nat.mul_comm] at hd
      omega)
    rwa [show n - n / m * m = n % m by rw [Nat.mul_comm] at hd; omega] at hsub

/-- **The least period divides every period**, from whatever bit the period starts. -/
theorem minTailPeriod_dvd {y : Nat → Bool} {q N p : Nat} (hq : MinTailPeriod y q) (h : TailPeriod y N p) :
    q ∣ p := by
  obtain ⟨hq0, ⟨N1, h1⟩, hmin⟩ := hq
  have hg := tailPeriod_gcd q p (tailPeriod_mono h1 (Nat.le_max_left N1 N)) (tailPeriod_mono h (Nat.le_max_right N1 N))
  have hpos : 0 < Nat.gcd q p := Nat.gcd_pos_of_pos_left p hq0
  have hle : Nat.gcd q p ≤ q := Nat.le_of_dvd hq0 (Nat.gcd_dvd_left q p)
  have heq : Nat.gcd q p = q := by
    refine Classical.byContradiction fun hne => hmin _ _ hpos (by omega) hg
  rw [← heq]
  exact Nat.gcd_dvd_right q p

/-- **The least period of `rho k` divides that of `rho (k + 1)`**: a period of `rho (k + 1)` is one of `rho k`, two
bits further out. -/
theorem rho_min_period_dvd {k q q' : Nat} (hq : MinTailPeriod (rho k) q) (hq' : MinTailPeriod (rho (k + 1)) q') :
    q ∣ q' := by
  obtain ⟨-, ⟨N, hN⟩, -⟩ := hq'
  have e := phiF_period hN
  rw [phiF_rho_succ] at e
  exact minTailPeriod_dvd hq e

namespace SeedTable

/-- Bit `j` of the certificate `(N, P, a, w)`: bit `j` of `a` below `N`, bit `(j - N) % P` of `w` from `N` on. -/
def bits (N P a w : Nat) (j : Nat) : Bool := if j < N then a.testBit j else w.testBit ((j - N) % P)

theorem bits_period (N P a w : Nat) : TailPeriod (bits N P a w) N P := by
  intro j hj
  unfold bits
  split
  · omega
  split
  · omega
  rw [show j + P - N = (j - N) + P by omega, Nat.add_mod_right]

/-- `n` copies of the `P`-bit word `w`, side by side. -/
def rep (P w : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => Nat.lor (rep P w n) (Nat.shiftLeft w (Nat.mul n P))

theorem rep_testBit (P w : Nat) (hw : w < 2 ^ P) :
    ∀ n g, (rep P w n).testBit g = (decide (g < n * P) && w.testBit (g % P)) := by
  intro n
  induction n with
  | zero => intro g; simp [rep]
  | succ n ih =>
    intro g
    show (rep P w n ||| (w <<< (n * P))).testBit g = _
    rw [Nat.testBit_or, ih, Nat.testBit_shiftLeft]
    by_cases h1 : g < n * P
    · have : ¬ g ≥ n * P := by omega
      simp [h1, this, show g < (n + 1) * P by rw [Nat.succ_mul]; omega]
    · by_cases h2 : g < (n + 1) * P
      · have hm : g % P = g - n * P := by
          have hP : 0 < P := by rw [Nat.succ_mul] at h2; omega
          rw [show g = g - n * P + n * P by omega, Nat.add_mul_mod_self_right,
            Nat.mod_eq_of_lt (by rw [Nat.succ_mul] at h2; omega)]
          omega
        simp [h1, h2, show g ≥ n * P by omega, hm]
      · have hlt : w.testBit (g - n * P) = false :=
          Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hw (Nat.pow_le_pow_right (by decide) (by
            rw [Nat.succ_mul] at h2; omega)))
        simp [h1, h2, hlt]

/-- The first `B` bits of the certificate `(N, P, a, w)`, as a number. -/
def expand (N P a w B : Nat) : Nat :=
  Nat.mod (Nat.lor (Nat.mod a (2 ^ N)) (Nat.shiftLeft (rep P (Nat.mod w (2 ^ P)) (B / P + 1)) N)) (2 ^ B)

theorem expand_testBit (N P a w B : Nat) (hP : 0 < P) (j : Nat) (hj : j < B) :
    (expand N P a w B).testBit j = bits N P a w j := by
  show ((a % 2 ^ N ||| (rep P (w % 2 ^ P) (B / P + 1) <<< N)) % 2 ^ B).testBit j = _
  rw [Nat.testBit_mod_two_pow, decide_eq_true hj, Bool.true_and, Nat.testBit_or, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft,
    rep_testBit P _ (Nat.mod_lt _ (Nat.two_pow_pos P)), Nat.testBit_mod_two_pow]
  unfold bits
  by_cases h : j < N
  · simp [h, show ¬ N ≤ j by omega]
  · have hB : j - N < (B / P + 1) * P := by
      have := Nat.div_add_mod B P
      have := Nat.mod_lt B hP
      rw [Nat.succ_mul, Nat.mul_comm]
      omega
    simp [h, show j ≥ N by omega, hB, Nat.mod_lt _ hP]

/-- One step of `phiF` on the first `B` bits. -/
def stepW (B X : Nat) : Nat := Nat.mod (Nat.xor X (Nat.lor (Nat.shiftLeft X 1) (Nat.shiftLeft X 2))) (2 ^ B)

theorem stepW_testBit (B X : Nat) (y : Nat → Bool) (h : ∀ j, j < B → X.testBit j = y j) :
    ∀ j, j < B → (stepW B X).testBit j = phiF y j := by
  intro j hj
  show ((X ^^^ ((X <<< 1) ||| (X <<< 2))) % 2 ^ B).testBit j = _
  rw [Nat.testBit_mod_two_pow, decide_eq_true hj, Bool.true_and, Nat.testBit_xor, Nat.testBit_or,
    Nat.testBit_shiftLeft, Nat.testBit_shiftLeft]
  match j, hj with
  | 0, hj => rw [h 0 hj]; show (y 0 ^^ (false || false)) = y 0; cases y 0 <;> rfl
  | 1, hj =>
    rw [h 1 hj, show 1 - 1 = 0 from rfl, h 0 (by omega)]
    show (y 1 ^^ (y 0 || false)) = xor (y 1) (y 0)
    cases y 0 <;> cases y 1 <;> rfl
  | j + 2, hj =>
    rw [h (j + 2) hj, show j + 2 - 1 = j + 1 by omega, show j + 2 - 2 = j by omega, h (j + 1) (by omega),
      h j (by omega), decide_eq_true (by omega : j + 2 ≥ 1), decide_eq_true (by omega : j + 2 ≥ 2)]
    rfl

/-- `d` steps of `phiF` on the first `B` bits. -/
def iterW (B : Nat) : Nat → Nat → Nat
  | 0, X => X
  | d + 1, X => iterW B d (stepW B X)

theorem iterW_testBit (B : Nat) : ∀ d (X : Nat) (y : Nat → Bool), (∀ j, j < B → X.testBit j = y j) →
    ∀ j, j < B → (iterW B d X).testBit j = phiIter d y j
  | 0, _, _, h => h
  | d + 1, X, y, h => iterW_testBit B d (stepW B X) (phiF y) (stepW_testBit B X y h)

/-- **A link**: `d` steps take the certificate `(N1, P1, a1, w1)` to `(N0, P0, a0, w0)`, checked on the first
`max (N1 + 2 d) N0 + P1` bits, with `P0` dividing `P1`. -/
def linkOk (d N1 P1 a1 w1 N0 P0 a0 w0 : Nat) : Bool :=
  Nat.blt 0 P1 && Nat.blt 0 P0 && Nat.beq (P1 % P0) 0 &&
    Nat.beq (iterW (max (N1 + 2 * d) N0 + P1) d (expand N1 P1 a1 w1 (max (N1 + 2 * d) N0 + P1)))
      (expand N0 P0 a0 w0 (max (N1 + 2 * d) N0 + P1))

theorem link_sound (d N1 P1 a1 w1 N0 P0 a0 w0 : Nat) (h : linkOk d N1 P1 a1 w1 N0 P0 a0 w0 = true) :
    phiIter d (bits N1 P1 a1 w1) = bits N0 P0 a0 w0 := by
  unfold linkOk at h
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  obtain ⟨⟨⟨hP1, hP0⟩, hdiv⟩, he⟩ := h
  have hwin : ∀ j, j < max (N1 + 2 * d) N0 + P1 → phiIter d (bits N1 P1 a1 w1) j = bits N0 P0 a0 w0 j := by
    intro j hj
    rw [← iterW_testBit _ d _ _ (fun i hi => expand_testBit N1 P1 a1 w1 _ hP1 i hi) j hj, he,
      expand_testBit N0 P0 a0 w0 _ hP0 j hj]
  have hper1 := phiIter_period d (bits_period N1 P1 a1 w1)
  have hper0 : TailPeriod (bits N0 P0 a0 w0) N0 P1 := by
    intro j hj
    have e := evPer_mul (bits_period N0 P0 a0 w0) (P1 / P0) j hj
    rwa [Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hdiv)] at e
  have hag := agree_of_period (M := max (N1 + 2 * d) N0) hP1 (fun j hj => hper1 j (by omega))
    (fun j hj => hper0 j (by omega)) (fun r hr => hwin _ (by omega))
  funext j
  by_cases hj : j < max (N1 + 2 * d) N0
  · exact hwin j (by omega)
  · exact hag j (by omega)

/-- The links along a list of certificates, from the certificate `c` of `k`. -/
def chainOk : Nat → Nat × Nat × Nat × Nat → List (Nat × Nat × Nat × Nat × Nat) → Bool
  | _, _, [] => true
  | k, (N0, P0, a0, w0), (k1, N1, P1, a1, w1) :: rest =>
    Nat.blt k k1 && linkOk (k1 - k) N1 P1 a1 w1 N0 P0 a0 w0 && chainOk k1 (N1, P1, a1, w1) rest

theorem chain_sound : ∀ (l : List (Nat × Nat × Nat × Nat × Nat)) (k N P a w : Nat),
    chainOk k (N, P, a, w) l = true → bits N P a w = rho k →
    ∀ e ∈ l, bits e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2 = rho e.1
  | [], _, _, _, _, _, _, _ => fun e he => absurd he (List.not_mem_nil)
  | (k1, N1, P1, a1, w1) :: rest, k, N, P, a, w, h, hb => by
    unfold chainOk at h
    simp only [Bool.and_eq_true, Nat.blt_eq] at h
    obtain ⟨⟨hk, hl⟩, hr⟩ := h
    have e1 : bits N1 P1 a1 w1 = rho k1 := by
      have := phiIter_eq_rho (k1 - k) k (by rw [link_sound _ _ _ _ _ _ _ _ _ hl, hb])
      rwa [show k + (k1 - k) = k1 by omega] at this
    intro e he
    rcases List.mem_cons.mp he with he | he
    · subst he; exact e1
    · exact chain_sound rest k1 N1 P1 a1 w1 hr e1 e he

/-- The certificate of `k` in a list. -/
def certOf (k : Nat) : List (Nat × Nat × Nat × Nat × Nat) → Option (Nat × Nat × Nat × Nat)
  | [] => none
  | (k', c) :: rest => if Nat.beq k' k then some c else certOf k rest

theorem certOf_mem (k : Nat) : ∀ (l : List (Nat × Nat × Nat × Nat × Nat)) c, certOf k l = some c → (k, c) ∈ l
  | [], _, h => absurd h (by simp [certOf])
  | (k', c') :: rest, c, h => by
    unfold certOf at h
    by_cases hk : Nat.beq k' k = true
    · simp only [hk, ↓reduceIte] at h
      have := Nat.eq_of_beq_eq_true hk
      subst this
      cases h
      exact List.mem_cons_self
    · simp only [Bool.not_eq_true] at hk
      simp only [hk, Bool.false_eq_true, ↓reduceIte] at h
      exact List.mem_cons_of_mem _ (certOf_mem k rest c h)

/-- `f i` holds for every `i < n`. -/
def checkBelow (f : Nat → Bool) : Nat → Bool
  | 0 => true
  | n + 1 => checkBelow f n && f n

theorem checkBelow_spec (f : Nat → Bool) : ∀ n, checkBelow f n = true → ∀ i, i < n → f i = true
  | 0, _, i, hi => absurd hi (by omega)
  | n + 1, h, i, hi => by
    unfold checkBelow at h
    simp only [Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
    · exact checkBelow_spec f n h.1 i hi
    · rw [hi]; exact h.2

/-- **Minimal period**: no `q` with `0 < q < P` is a period of the window of `P` bits at `N`. -/
def minPerOk (N P a w : Nat) : Bool :=
  checkBelow (fun q => Nat.beq q 0 ||
    !Nat.beq (Nat.mod (Nat.xor (Nat.shiftRight (Nat.shiftRight (expand N P a w (N + 2 * P)) N) q)
      (Nat.shiftRight (expand N P a w (N + 2 * P)) N)) (2 ^ P)) 0) P

theorem minPer_sound (N P a w : Nat) (hP : 0 < P) (h : minPerOk N P a w = true) (q : Nat) (hq : 0 < q)
    (hqP : q < P) : ∃ r, r < P ∧ bits N P a w (N + r + q) ≠ bits N P a w (N + r) := by
  have hf := checkBelow_spec _ P h q hqP
  simp only [Bool.or_eq_true, Nat.beq_eq, Bool.not_eq_true'] at hf
  rcases hf with hf | hf
  · omega
  · refine Classical.byContradiction fun hn => Nat.ne_of_beq_eq_false hf ?_
    apply Nat.eq_of_testBit_eq
    intro i
    show ((((expand N P a w (N + 2 * P) >>> N) >>> q) ^^^ (expand N P a w (N + 2 * P) >>> N)) % 2 ^ P).testBit i =
      Nat.testBit 0 i
    rw [Nat.testBit_mod_two_pow, Nat.zero_testBit, Nat.testBit_xor, Nat.testBit_shiftRight, Nat.testBit_shiftRight,
      Nat.testBit_shiftRight]
    by_cases hi : i < P
    · rw [expand_testBit N P a w _ hP _ (by omega), expand_testBit N P a w _ hP _ (by omega)]
      have : bits N P a w (N + i + q) = bits N P a w (N + i) :=
        Classical.byContradiction fun hne => hn ⟨i, hi, hne⟩
      rw [show N + (q + i) = N + i + q by omega, this]
      simp
    · simp [hi]

/-- **Preperiod**: `N = 0`, or bit `N - 1` differs from bit `N - 1 + P`. -/
def preOk (N P a w : Nat) : Bool :=
  Nat.beq N 0 || !(Bool.beq ((expand N P a w (N + P)).testBit (N - 1)) ((expand N P a w (N + P)).testBit (N - 1 + P)))

theorem pre_sound (N P a w : Nat) (hP : 0 < P) (h : preOk N P a w = true) :
    N = 0 ∨ bits N P a w (N - 1 + P) ≠ bits N P a w (N - 1) := by
  unfold preOk at h
  simp only [Bool.or_eq_true, Nat.beq_eq, Bool.not_eq_true'] at h
  by_cases hN : N = 0
  · exact Or.inl hN
  right
  rcases h with h | h
  · exact absurd h hN
  · rw [expand_testBit N P a w _ hP _ (by omega), expand_testBit N P a w _ hP _ (by omega)] at h
    intro e
    rw [e] at h
    revert h
    cases bits N P a w (N - 1) <;> decide

/-- A certificate that passes both checks gives the minimal period and the preperiod. -/
theorem cert_facts (y : Nat → Bool) (N P a w : Nat) (hy : bits N P a w = y) (hP : 0 < P)
    (hm : minPerOk N P a w = true) (hpre : preOk N P a w = true) : MinTailPeriod y P ∧ IsPreperiod y N P := by
  subst hy
  have hper := bits_period N P a w
  refine ⟨⟨hP, ⟨N, hper⟩, fun q N' hq hqP hq' => ?_⟩, hper, fun N' hN' => ?_⟩
  · obtain ⟨r, hr, hne⟩ := minPer_sound N P a w hP hm q hq hqP
    apply hne
    have e1 := evPer_mul hper N' (N + r + q) (by omega)
    have e2 := evPer_mul hper N' (N + r) (by omega)
    have e3 := hq' (N + r + N' * P) (by
      have : N' * P ≥ N' := Nat.le_mul_of_pos_right N' hP
      omega)
    rw [show N + r + N' * P + q = N + r + q + N' * P by omega, e1, e2] at e3
    exact e3
  · refine Classical.byContradiction fun hlt => ?_
    rcases pre_sound N P a w hP hpre with h0 | hne
    · omega
    · exact hne (hN' (N - 1) (by omega))

end SeedTable

open SeedTable

/-- The certificates `(k, N, P, a, w)` of `rho k` for `k = 1 .. 66`, 300, 1000 and 3000, written by
`computations/seed_past_lean.py`. -/
def seedCerts : List (Nat × Nat × Nat × Nat × Nat) := [
  (1, 0, 1, 0x0, 0x1),
  (2, 0, 3, 0x0, 0x1),
  (3, 1, 3, 0x1, 0x3),
  (4, 0, 6, 0x0, 0x11),
  (5, 1, 6, 0x1, 0x17),
  (6, 0, 6, 0x0, 0x19),
  (7, 0, 6, 0x0, 0x7),
  (8, 0, 6, 0x0, 0x1),
  (9, 1, 6, 0x1, 0x1f),
  (10, 0, 12, 0x0, 0x489),
  (11, 1, 12, 0x1, 0x5bb),
  (12, 0, 12, 0x0, 0x511),
  (13, 1, 12, 0x1, 0x577),
  (14, 0, 12, 0x0, 0x599),
  (15, 1, 12, 0x1, 0x543),
  (16, 0, 12, 0x0, 0x581),
  (17, 1, 12, 0x1, 0x63f),
  (18, 0, 24, 0x0, 0x4123c9),
  (19, 1, 24, 0x1, 0x5f6e9b),
  (20, 0, 24, 0x0, 0x5232d1),
  (21, 1, 24, 0x1, 0x570717),
  (22, 0, 24, 0x0, 0x59f9d9),
  (23, 1, 24, 0x1, 0x542423),
  (24, 0, 24, 0x0, 0x57b7c1),
  (25, 1, 24, 0x1, 0x55289f),
  (26, 0, 24, 0x0, 0x55af09),
  (27, 1, 24, 0x1, 0x562a7b),
  (28, 0, 24, 0x0, 0x63ab91),
  (29, 0, 24, 0x0, 0x1e566f),
  (30, 4, 24, 0x9, 0x4e9aa1),
  (31, 10, 24, 0x207, 0x7ae615),
  (32, 8, 24, 0x1, 0x9887aa),
  (33, 7, 24, 0x7f, 0xef4ab),
  (34, 6, 24, 0x9, 0xf296b1),
  (35, 14, 24, 0x23b7, 0x504d71),
  (36, 23, 24, 0x441e51, 0x6757e1),
  (37, 36, 24, 0x8903be9af, 0x64f8e5),
  (38, 39, 24, 0x4770089859, 0x6384f3),
  (39, 41, 24, 0x13ccff787c7, 0x479ed3),
  (40, 46, 24, 0x1cd3424a7a41, 0x85d391),
  (41, 51, 24, 0x3c430bdb5a5bf, 0x83d973),
  (42, 60, 24, 0x8853c0f528c5a89, 0x673f23),
  (43, 62, 24, 0x277ad3f4ad83c577, 0x473937),
  (44, 65, 24, 0x9ca62e4b547d3b11, 0x979ce1),
  (45, 84, 24, 0x4e73d7361d9b8ac1308ef, 0x90840d),
  (46, 95, 24, 0x402b9cd2cd1f286763f0f799, 0x7e8def),
  (47, 104, 24, 0x913fd8842d4304d7a11e4f4c87, 0x4a64c1),
  (48, 115, 24, 0x3406ed2477be2c0fc2a5ee9b4c381, 0x87d6c3),
  (49, 128, 24, 0x51e8bfa22dbcc89e3f93d5a9968c3e7f, 0x8a0409),
  (50, 132, 24, 0x6ae97525dd4643769d26d2c58717409c9, 0x875fbf),
  (51, 147, 24, 0x44891596cadb32c1bd1172da2e3c7cecbf737, 0x64a4f9),
  (52, 158, 24, 0x1a43b76ec6a35450d4052eecd45d9d3a42364cd1, 0x84e36b),
  (53, 160, 24, 0x45be51194160abb02bfad9942bc472e5bdd1b42f, 0x9ee745),
  (54, 163, 24, 0x2ba89af06bf1f588fd526286bd53bcd9c532e8bd9, 0x8d3397),
  (55, 161, 24, 0x1657859018904c7792ae1d8152ae53473b0d97647, 0xc39b2),
  (56, 163, 24, 0x31aa7c70076fc3ca6d62047ead59b0c108f4711c1, 0x80f9a3),
  (57, 169, 24, 0x105055a41001193d35a31dfbc962a8503ef74bcef3f, 0x79fd21),
  (58, 175, 24, 0x40fafac5befff06d30c60f325371d57b0094cb539909, 0x7a9a4b),
  (59, 173, 24, 0x26263a89924fa30f41f90db0cf2ac8ff6c38b086f7, 0x9616e2),
  (60, 173, 24, 0x1fe1e1e5786dc260f4bf26f45034d63824a3e78f8191, 0x71f19d),
  (61, 174, 24, 0x249e9e9aa7a33e1f4b64e14bb00c31e7db609a74806f, 0x674839),
  (62, 186, 24, 0x2021b6969855a60d204b51b9eb88ff40e9a451f85cb8019, 0x7e71cb),
  (63, 190, 24, 0x19fe0517187ac5a02dfb8b066967824bf985baf27b388007, 0x8c9cf3),
  (64, 188, 24, 0x849faf107a63c5fe32678fa171a7db6487c654dc8e78001, 0xdce42),
  (65, 190, 24, 0x17b7254efa61d3a920e1c825f105a451b7a41ac3379a7fff, 0x80ce6f),
  (66, 188, 48, 0xc8cdac2261f2e56df9f37dc4efc5bae8a5c063d0c861249, 0xe689fd0852),
  (300, 1509, 48, 0x177e75c32c43bf2f218efd140015876efb37afd80893cfa1501bb2ef6e27a6703c7a9b866298ae2f0c12df05dc7a6ed4b27d76930fc5f1067ecbfcad1017e0d100b08d86d0793bfd261680485aa52d2d789911d24cf3c887f59150896f500145efdba7869d26b7aaf7bc9be469ec183b399910433ecaff03078bf3b32e5d0d484319df014cc08a4cbc76eeeb7463009bda7ba2fba861016a937f34fa205e19f66eefe5ffdab6e8cdcc4423f3008c15300b761bdc9d327c7176537d3b11, 0xe5035b270c2),
  (1000, 4968, 48, 0x975a9291ea69767538c34b056fe8ccab955af463eeeb8ff347c204ebd9827d4a9868553932e4b230bfa037b3f1c31c818cfea8f609511ca9922b5c847763d3bce62ad741244a43b0f639ebe87e655793530615bdb8906858c38b080e763ca7be858e0d2d8e05c862a7e7f0f8564343f39ff848c121094ef08e399bc51567aeaa8f3afa3385899b66bfbfc966d8ae977f2830d1ee263c95014ccab29b1d5ffa6eb8bac778940fe3e2dcfab6ddc7e157254db08e4661ad8e3a03b34662f86e4494942b7bad536a53d8cc830a566058c25dc1c17ce1071b463d16af4d6346764838bd3613a9ec0eb3944cb91e67d3696f07f9fc84b0559287fe5a78e2e990c6cb8da03bfc68b558f6ca7f97b69b4f94bb12492aebdc7b6802a2fc71fce8be14bfd5c24b38a7b65687bec2e79ef9146998a07ba23694de1d36046c2773fbee6c9c677d728182987b253a6156b2f372f0e3e3f838a2dcadd4ae0a954a6b3bf622289919913d6a12e0724af6297693f8d5590ad919be2e540fb59b10539b6aef3f66506c4cc1724948feb28da6cc05171959c36da07db1914cc46cae03065f38f741d73b6ecb3fabfb7ae68421900dc8f8057e0914b025398e8c4590d079de7111cddcb395f744fd67eedcc6a10a3214f6ec04b6b41aa6254c7166b0371f639109625419a4f6296f63c0861da683d809c0968413872d5495075ac59e138cba342272fc97c990cf38ba31dedec5f18f3c8e2f394373d9e8bd2aecf2c4d3242d767fb14cda2bcf84bfb9ace3a10f542211f19e0d46bf44225038f742fa171c73750c15596853c274703c9a03f1eff01ece26047de7f57581ed9a31ce16e6156be941cd21addc8ae9a9a1ecd51d3e2fa41, 0xc01a4dcded7a),
  (3000, 15615, 48, 0x3a9c2af7f68094b803d932a08f281040b79e01398262184fcd358c67a388da7c3d928bcf861b6d65e719ce27f3c051c935b3bcaccbe068107acf5d242927aeba3ff62a686ac79406464f34c99fe388acd34739bdf503db6bb604ffaefadede218931477854f2d1d18032b4927e07d17cd933f9b66753c673a3ab430e87c6522dff81e8a7e45f4dc465c297538d2957a179d1678b452c951e1eaa2d544c4671ac8fee7198f72f23171383aeacdd94777b131840126eaa9485aed54d2649a03375e348b1d06458b546dd9aecea5822dd763714a3d46750be4f1e818a05c26b732b3db73604557fe3b57cb41f05d6eab137475dafc97f5c90bd1a8439c4c78ed890d532a401ec688aa45244cd7a2226f073830429b4b21635403dc617bfb4e9bc253139da4ab31f78b621a3f75be5556c4b6c3ed8044b9eeb7657ad217d3cfb175d767d438aef60b127c678c243a82a08b4201ad6e785dac6436bcb5febb6f35225c9a791546847a899fdf2df89c9f7b10201f4358e2389a95e82b3998ce0bd9f151bfcad59d1ab35d07f80998586e99d4afbb8c285b72bd894d929647fa1db83d7b5aaa04e3b4a9115628a76ae6e4b61b5696688434e873c47e3923cd96bec7fce5459ca9f289ca3cdee25f37054c081f7802cfd4abbd53b900886031c331cd5b0fb42e334f8104f7f1ecb08eb8b091cb23bc300441d64d8bbfce0c51e487f7ea6137c1a8a7be33ead773a6cdfafaed8ffa96a82707c7be18457be00ad207d13d697b6198ad1d841c70b8f53259ea53b6078ace3b174a609eef40db950b63937f40675ea6187fa294914c3760150c9363973c2be9e551eddfda5df154f3ade697821155732ed40c1319091aafd9ea61c4d430791c9d7cbedf28033bd7d3598ccce3bc79b5e2f298258917662821422e3f51515df050639a46d897714ef7cddc6148148063ffb91e77e4b42dfd16c74d5709d9c73cffa030386a7938fcadf8d4c6658f4b18606e5110543f3900b16a0729a7b1294a708f04174fc8694e073aa6d3e82b35de4189b25ac65b43a1b9df7ee96c9863336e8d0e800ee80741d0c114cfc37e7fd004203fe1ccfd0bd482b332bad43fb3481d0ab3dd2fb637a8369466ccea38177e6bad5bfe01025fc77eb3372983de890919b66b664c328dac9647d26af0b19602c4bff7f6d05fd2005afcd74d3daec75fee8e99116241ab4892a1cdb3f01f64b1a80d659499dbcd81241a3889a6f34c7d0b4720388c09bff186ab4fec22700f266dfd65cedca284723a5702870d8907dff3bea3e268064cba6ca2ed19f9320682f98a3ff4e4944a51924ce1d6240ed539801d9b9db1f611b6166445979e093fb96866a9b6d117c1f95c2b5adb2427185be3106c00d9682dc7b3b4ad5ba3bcf519bee2b9207e2ad26e1e66f91b118d7387fe891fd8deb1ca7279c673c5727d45afce83ee64ce142f5eb1972daed5407f0667f810a6f46d24e332db6e827daab9c8730cc85d120518e828a094645762d2efe36cf7e56af1d61fbcabb1413a80b50d4c7faa167ef78d02ee550280858c3281ee6b2281fc6fb97504b9f10ba2a4f445642826006bae3b20b196ff4740a6e137b40c49e4f9e4674c9b74fec992bbec16bf6c21917511531e9531506d1ccba6e44ddc7d8ed604583f0857c182815558cbd847e24357bbd1f2d7f932572a7d05b26383d05782c7984dc8caa5288eb96c7781f1cced7eca28ad8602c4b20f935548da395751a927b6d8fe73a898b47da2cb2bcc0b3103d6b0b99207e94c2e872deab6e626a2d78d8176a96463a05d559b277ddc662c8fefaa8aa1f5fc268c0800c3ba13aa79667575cb2ad8e41ed44f240e35948500e84795035492dce0d5beb72d12f3e333aca15a8943d1b231e183a6074d820e0cdbbf4682c8c2b55393449887feb91a20a9903b6967774740a8bbc50240af7f022dcb60ec24802fec4d6a6172daefbdef7f1a8705077ef9d2d63b7a11e553acc06704017f72fcdaa9ac0897d996f75f9b5e69c3f60e9180cea929d8cf23964bd926a67ca8e0127bd65aea97a40f937869de3b1fb27534d0c0067f681d00c703cea3e5ec9f1a95ec9d10fcc56ff6cd5fe287da5e8e25285b09b8ed818b661046a0db62c20f205d40f093b16277fcf9659ac519499e85f3caa0771faff0e80ffe15392e1c7488d69a4083e8a5eb873b22fb6b493374ca86abb3390fb59168d1a0bb2568f1b66c30eb432677a6171562de3ea2125f68b20012316f4c3545eac9e26782afea54a1c7bcb82258107aeea96ffc1f023bbb281d53f80358c51850f2a03a1f9a7ae8cf5d467ef548726367d37d102f76522e419ebe22f8c4bf67a9678e74561be7f06f0cb0dd295863440769ce4338535504cc7955a6aa88e596591eff9a8d7669378a7d6572dfd4f8d1cc6829dd2acb93f6074df9d90ad5422a70e33acdce32d91911d27f327fd77062154b7ae7f3b0f0620924826755a8365bb62149fa8c2f16112ca74ca29e4c2022857f2a7af92055f09bd4b3d38322b0f7f4c13ddae50c62d1566542158f756faf17832aefe8413b8727181e79faf249031006985ee71fba11ce12915d14a17338f7c295a3c35553e5ee5e7d82dbcf4ba2ba194d8bc7a8d7c2364c671210ae16218f76fc2e320f6a5775ff1cf9aeee64957c3114c220fe5f7d452bee7b0643665c76db7d9de8c6917bc26a55810640855fa14619803f04e716dbfba2039b25b0c74781774c3622c277bb32e11c1, 0x83ede9bc417b)]

set_option maxHeartbeats 0 in
/-- **The chain of links** from the single cell through every certificate. -/
theorem seedCerts_ok : chainOk 0 (1, 1, 1, 0) seedCerts = true := by decide +kernel

/-- Every certificate of the list is the single cell's past at its depth. -/
theorem seedCerts_rho {k N P a w : Nat} (h : certOf k seedCerts = some (N, P, a, w)) : bits N P a w = rho k := by
  have base : bits 1 1 1 0 = rho 0 := by
    funext j
    show _ = decide (j = 0)
    unfold bits
    match j with
    | 0 => rfl
    | j + 1 =>
      split
      · omega
      · rw [Nat.zero_testBit]
        exact (decide_eq_false (by omega)).symm
  exact chain_sound seedCerts 0 1 1 1 0 seedCerts_ok base (k, N, P, a, w) (certOf_mem k seedCerts _ h)

/-- The minimal period of `rho k` for `1 ≤ k ≤ 3000`: 1, 3, 6, 12, 24 and 48 from `k` = 1, 2, 4, 10, 18 and 66. -/
def seedPeriod (k : Nat) : Nat :=
  if k < 2 then 1 else if k < 4 then 3 else if k < 10 then 6 else if k < 18 then 12 else if k < 66 then 24 else 48

theorem seedPeriod_of_ge (k : Nat) (h : 66 ≤ k) : seedPeriod k = 48 := by
  unfold seedPeriod
  split
  · omega
  split
  · omega
  split
  · omega
  split
  · omega
  split
  · omega
  rfl

/-- The certificate of `k` has preperiod `N` and period `P > 0`, and passes both checks. -/
def factOk (k N P : Nat) : Bool :=
  match certOf k seedCerts with
  | some (N', P', a, w) => Nat.beq N' N && Nat.beq P' P && Nat.blt 0 P && minPerOk N P a w && preOk N P a w
  | none => false

theorem factOk_sound (k N P : Nat) (h : factOk k N P = true) :
    MinTailPeriod (rho k) P ∧ IsPreperiod (rho k) N P := by
  unfold factOk at h
  split at h
  · rename_i N' P' a w hc
    simp only [Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq] at h
    obtain ⟨⟨⟨⟨hN, hP⟩, hP0⟩, hm⟩, hpre⟩ := h
    subst hN
    subst hP
    exact cert_facts _ _ _ _ _ (seedCerts_rho hc) hP0 hm hpre
  · exact absurd h (by simp)

/-- At depth `k ≤ 66`: the certificate's period is `seedPeriod k`, and its preperiod is at most 1 up to `k = 28`. -/
def smallOk (k : Nat) : Bool :=
  match certOf k seedCerts with
  | some (N, _, _, _) => factOk k N (seedPeriod k) && (Nat.blt 28 k || Nat.ble N 1)
  | none => false

set_option maxHeartbeats 0 in
theorem smallOk_all : checkBelow (fun i => smallOk (i + 1)) 66 = true := by decide +kernel

theorem rho_small (k : Nat) (h1 : 1 ≤ k) (h2 : k ≤ 66) :
    ∃ N, MinTailPeriod (rho k) (seedPeriod k) ∧ IsPreperiod (rho k) N (seedPeriod k) ∧ (k ≤ 28 → N ≤ 1) := by
  have h := checkBelow_spec _ 66 smallOk_all (k - 1) (by omega)
  rw [show k - 1 + 1 = k by omega] at h
  unfold smallOk at h
  split at h
  · rename_i N P a w hc
    simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.blt_eq, Nat.ble_eq] at h
    obtain ⟨hf, hN⟩ := h
    obtain ⟨hm, hp⟩ := factOk_sound k N _ hf
    refine ⟨N, hm, hp, fun hk => ?_⟩
    rcases hN with hN | hN
    · omega
    · exact hN
  · exact absurd h (by simp)

theorem fact_30 : factOk 30 4 24 = true := by decide +kernel
theorem fact_66 : factOk 66 188 48 = true := by decide +kernel
theorem fact_300 : factOk 300 1509 48 = true := by decide +kernel
theorem fact_1000 : factOk 1000 4968 48 = true := by decide +kernel
theorem fact_3000 : factOk 3000 15615 48 = true := by decide +kernel

/-- **The minimal periods of the single cell's past**: for `1 ≤ k ≤ 3000`, `rho k` repeats from some bit on with
least period 1, 3, 6, 12, 24 or 48, the last from `k = 66` on. -/
theorem rho_min_period (k : Nat) (h1 : 1 ≤ k) (h2 : k ≤ 3000) : MinTailPeriod (rho k) (seedPeriod k) := by
  by_cases hk : k ≤ 66
  · obtain ⟨N, hm, -⟩ := rho_small k h1 hk
    exact hm
  · rw [seedPeriod_of_ge k (by omega)]
    obtain ⟨⟨_, ⟨N, hN⟩, _⟩, _⟩ := factOk_sound 3000 15615 48 fact_3000
    obtain ⟨⟨_, _, hmin⟩, _⟩ := factOk_sound 66 188 48 fact_66
    refine ⟨by omega, ⟨N + 2 * (3000 - k), fun j hj => ?_⟩, fun q N' hq hq48 hper => ?_⟩
    · have e := rho_sub_period hN (3000 - k) (by omega) j hj
      rwa [show 3000 - (3000 - k) = k by omega] at e
    · apply hmin q (N' + 2 * (k - 66)) hq hq48
      intro j hj
      have e := rho_sub_period hper (k - 66) (by omega) j hj
      rwa [show k - (k - 66) = 66 by omega] at e

/-- **Past depth 66 every period is a multiple of 48**, for every `k ≥ 66`, beyond the checked range too: a period of
`rho k` is one of `rho 66`, whose least period is 48. -/
theorem rho_period_dvd_of_ge (k N p : Nat) (hk : 66 ≤ k) (h : TailPeriod (rho k) N p) : 48 ∣ p := by
  obtain ⟨hmin, _⟩ := factOk_sound 66 188 48 fact_66
  refine minTailPeriod_dvd hmin (N := N + 2 * (k - 66)) fun j hj => ?_
  have e := rho_sub_period h (k - 66) (by omega) j hj
  rwa [show k - (k - 66) = 66 by omega] at e

/-- **Preperiods up to depth 28**: for `1 ≤ k ≤ 28`, `rho k` repeats with its least period from bit 0 or bit 1. -/
theorem rho_preperiod_small (k : Nat) (h1 : 1 ≤ k) (h2 : k ≤ 28) :
    IsPreperiod (rho k) 0 (seedPeriod k) ∨ IsPreperiod (rho k) 1 (seedPeriod k) := by
  obtain ⟨N, -, hp, hN⟩ := rho_small k h1 (by omega)
  have := hN h2
  match N, this, hp with
  | 0, _, hp => exact Or.inl hp
  | 1, _, hp => exact Or.inr hp

/-- **The preperiods of the table**: 4, 188, 1509, 4968 and 15615 at depths 30, 66, 300, 1000 and 3000. -/
theorem rho_preperiods : IsPreperiod (rho 30) 4 24 ∧ IsPreperiod (rho 66) 188 48 ∧ IsPreperiod (rho 300) 1509 48 ∧
    IsPreperiod (rho 1000) 4968 48 ∧ IsPreperiod (rho 3000) 15615 48 :=
  ⟨(factOk_sound _ _ _ fact_30).2, (factOk_sound _ _ _ fact_66).2, (factOk_sound _ _ _ fact_300).2,
    (factOk_sound _ _ _ fact_1000).2, (factOk_sound _ _ _ fact_3000).2⟩

/-- Two steps back, the single cell's past is `(100)` repeated leftward: black exactly at the bits `j ≡ 0 (mod 3)`. -/
theorem rho_two : rho 2 = fun j => decide (j % 3 = 0) := by
  have hc : certOf 2 seedCerts = some (0, 3, 0, 1) := by decide +kernel
  rw [← seedCerts_rho hc]
  funext j
  unfold bits
  split
  · omega
  · rw [Nat.sub_zero]
    have h3 : j % 3 < 3 := Nat.mod_lt _ (by omega)
    generalize j % 3 = r at h3 ⊢
    match r, h3 with
    | 0, _ => rfl
    | 1, _ => rfl
    | 2, _ => rfl

/-- Ten steps back, the single cell's past is the word `100100010010` repeated leftward, bit `0` first: bit `j` is
bit `j % 12` of `0b010010001001`. -/
theorem rho_ten : rho 10 = fun j => Nat.testBit 0b010010001001 (j % 12) := by
  have hc : certOf 10 seedCerts = some (0, 12, 0, 0b010010001001) := by decide +kernel
  rw [← seedCerts_rho hc]
  funext j
  unfold bits
  split
  · omega
  · rw [Nat.sub_zero]

/-- Twenty-eight steps back, the single cell's past is the word `100010011101010111000110` repeated leftward, bit `0`
first, from the frame on. -/
theorem rho_twentyEight : rho 28 = fun j => Nat.testBit 0b011000111010101110010001 (j % 24) := by
  have hc : certOf 28 seedCerts = some (0, 24, 0, 0b011000111010101110010001) := by decide +kernel
  rw [← seedCerts_rho hc]
  funext j
  unfold bits
  split
  · omega
  · rw [Nat.sub_zero]

/-- **Rule 30 on a ring of 48 cells kills a row in exactly `k` steps, for every `k` from 66 to 3000**: the tail of
`rho k` wrapped on the ring. -/
theorem ring48_dies (k : Nat) (h1 : 66 ≤ k) (h2 : k ≤ 3000) : ∃ c : Int → Bool, (∀ x, c (x + 48) = c x) ∧
    (∀ x, evolve c k x = false) ∧ ∀ t, t < k → ∃ x, evolve c t x = true := by
  obtain ⟨_, ⟨N, hN⟩, _⟩ := rho_min_period k (by omega) h2
  rw [seedPeriod_of_ge k h1] at hN
  obtain ⟨hd, ha, -⟩ := rho_tail_dies k N 48 (by omega) hN
  exact ⟨tailRing (rho k) N 48, tailRing_periodic (rho k) N 48, hd, ha⟩

end Rule30Open
