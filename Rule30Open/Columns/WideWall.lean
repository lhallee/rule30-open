module

public import Rule30Open.Columns.LongRuns

/-!
# A long black run shields the next cell for four steps per nine 1s, whatever follows

Nine 1s in a column leave the two cells right of it reading `0 1` (`wall_forms`), and while the column stays black that
wall stays (`wall_stays`); so `9 j` 1s leave the `2 j` cells right of the column reading `(0 1)^j` (`black_shield`, the
kit's Lemma A* for the single seed). The stripe `0 1 0 1 …` is fixed by Rule 30, and each of its 1s hides the cell to
its right, so two rows that both carry the shield and then see the same column agree on the `2 j` cells for `2 j`
steps, and on one cell fewer at each later step: on the cell right of the column for `4 j` steps (`shield_agree`).

* `wide_wall_column`: no column of the orbit of a row with a leftmost 1 is eventually periodic if each of its 0s comes
  less than `4 j` steps after `9 j` 1s.
* `long_run_tail_column`, `center_long_run_tail`: in particular no eventual period of length `P` has a black run of
  length `r ≥ 9` with `P - r ≤ 4 ⌊r / 9⌋`. The kit's Theorem B (`Rule30BlackRuns.no_long_black_run`) asks
  `9 ⌈(P - r + 9) / 2⌉ ≤ r`, which implies this.

The natural-language argument is `WideWall.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

open Ruliology.CellularAutomata

/-! ### The shield -/

theorem evolve_succ (init : Int → Bool) (t : Nat) (x : Int) :
    evolve init (t + 1) x = xor (evolve init t (x - 1)) (evolve init t x || evolve init t (x + 1)) := rfl

/-- **The wall stays while the column is black.** -/
theorem wall_stays (init : Int → Bool) (k : Int) (τ : Nat) (h1 : evolve init τ k = true)
    (hw : evolve init τ (k + 1) = false ∧ evolve init τ (k + 2) = true) :
    evolve init (τ + 1) (k + 1) = false ∧ evolve init (τ + 1) (k + 2) = true := by
  rw [evolve_succ, evolve_succ, show k + 1 - 1 = k by omega, show k + 2 - 1 = k + 1 by omega,
    show k + 1 + 1 = k + 2 by omega, h1, hw.1, hw.2]
  exact ⟨rfl, by cases evolve init τ (k + 2 + 1) <;> rfl⟩

/-- **The black shield.** `9 j` 1s in column `k` from time `s` leave columns `k + 1, …, k + 2 j` reading `(0 1)^j`. -/
theorem black_shield (init : Int → Bool) : ∀ (j : Nat) (k : Int) (s : Nat),
    (∀ i : Nat, i < 9 * j → evolve init (s + i) k = true) →
    ∀ i : Nat, i < j → evolve init (s + 9 * j) (k + 2 * i + 1) = false ∧
      evolve init (s + 9 * j) (k + 2 * i + 2) = true := by
  intro j
  induction j with
  | zero => intro k s _ i hi; omega
  | succ j ih =>
    intro k s h i hi
    -- the wall forms after nine 1s and stays while the column is black
    have w0 := wall_forms init k s (fun i hi => h i (by omega))
    have stays : ∀ n : Nat, n ≤ 9 * j → evolve init (s + 9 + n) (k + 1) = false ∧
        evolve init (s + 9 + n) (k + 2) = true := by
      intro n
      induction n with
      | zero => intro _; exact w0
      | succ n ihn =>
        intro hn
        have hb := h (9 + n) (by omega)
        rw [show s + (9 + n) = s + 9 + n by omega] at hb
        exact wall_stays init k (s + 9 + n) hb (ihn (by omega))
    cases i with
    | zero =>
      have := stays (9 * j) (Nat.le_refl _)
      rw [show s + 9 + 9 * j = s + 9 * (j + 1) by omega] at this
      rw [show k + 2 * ((0 : Nat) : Int) + 1 = k + 1 by omega, show k + 2 * ((0 : Nat) : Int) + 2 = k + 2 by omega]
      exact this
    | succ i =>
      have := ih (k + 2) (s + 9) (fun n hn => (stays n (by omega)).2) i (by omega)
      rw [show s + 9 + 9 * j = s + 9 * (j + 1) by omega,
        show k + 2 + 2 * (i : Int) + 1 = k + 2 * ((i + 1 : Nat) : Int) + 1 by omega,
        show k + 2 + 2 * (i : Int) + 2 = k + 2 * ((i + 1 : Nat) : Int) + 2 by omega] at this
      exact this

/-! ### Two shielded rows agree beside the column -/

/-- The stripe value of cell `k + i`: white at odd `i`, black at even `i`. -/
def stripeAt (i : Nat) : Bool := i % 2 == 0

/-- **Two shielded rows that see the same column agree on the cell right of it for `4 j` steps.** -/
theorem shield_agree (init init' : Int → Bool) (k : Int) (τ τ' j : Nat)
    (hA : ∀ i : Nat, i < j → evolve init τ (k + 2 * i + 1) = false ∧ evolve init τ (k + 2 * i + 2) = true)
    (hB : ∀ i : Nat, i < j → evolve init' τ' (k + 2 * i + 1) = false ∧ evolve init' τ' (k + 2 * i + 2) = true)
    (hcol : ∀ s : Nat, s < 4 * j → evolve init (τ + s) k = evolve init' (τ' + s) k) :
    ∀ s : Nat, s < 4 * j → evolve init (τ + s) (k + 1) = evolve init' (τ' + s) (k + 1) := by
  -- cells `k + i`, `1 ≤ i`, at times `τ + s` and `τ' + s`
  let A : Nat → Nat → Bool := fun s i => evolve init (τ + s) (k + i)
  let B : Nat → Nat → Bool := fun s i => evolve init' (τ' + s) (k + i)
  have stepA : ∀ s i, 1 ≤ i → A (s + 1) i = xor (A s (i - 1)) (A s i || A s (i + 1)) := by
    intro s i hi
    show evolve init (τ + (s + 1)) (k + i) = xor (evolve init (τ + s) (k + ((i - 1 : Nat) : Int)))
      (evolve init (τ + s) (k + i) || evolve init (τ + s) (k + ((i + 1 : Nat) : Int)))
    rw [show τ + (s + 1) = τ + s + 1 by omega, evolve_succ,
      show k + (i : Int) - 1 = k + ((i - 1 : Nat) : Int) by omega,
      show k + (i : Int) + 1 = k + ((i + 1 : Nat) : Int) by omega]
  have stepB : ∀ s i, 1 ≤ i → B (s + 1) i = xor (B s (i - 1)) (B s i || B s (i + 1)) := by
    intro s i hi
    show evolve init' (τ' + (s + 1)) (k + i) = xor (evolve init' (τ' + s) (k + ((i - 1 : Nat) : Int)))
      (evolve init' (τ' + s) (k + i) || evolve init' (τ' + s) (k + ((i + 1 : Nat) : Int)))
    rw [show τ' + (s + 1) = τ' + s + 1 by omega, evolve_succ,
      show k + (i : Int) - 1 = k + ((i - 1 : Nat) : Int) by omega,
      show k + (i : Int) + 1 = k + ((i + 1 : Nat) : Int) by omega]
  have col0 : ∀ s, s < 4 * j → A s 0 = B s 0 := by
    intro s hs
    show evolve init (τ + s) (k + ((0 : Nat) : Int)) = evolve init' (τ' + s) (k + ((0 : Nat) : Int))
    rw [show k + ((0 : Nat) : Int) = k by omega]
    exact hcol s hs
  -- the start: both rows read the stripe on cells `1, …, 2 j`
  have start : ∀ i, 1 ≤ i → i ≤ 2 * j → A 0 i = stripeAt i ∧ B 0 i = stripeAt i := by
    intro i h1 h2
    obtain ⟨q, rfl | rfl⟩ : ∃ q, i = 2 * q + 1 ∨ i = 2 * q + 2 := ⟨(i - 1) / 2, by omega⟩
    · have ha := (hA q (by omega)).1
      have hb := (hB q (by omega)).1
      refine ⟨?_, ?_⟩
      · show evolve init (τ + 0) (k + ((2 * q + 1 : Nat) : Int)) = _
        rw [Nat.add_zero, show k + ((2 * q + 1 : Nat) : Int) = k + 2 * (q : Int) + 1 by omega, ha]
        unfold stripeAt; simp
      · show evolve init' (τ' + 0) (k + ((2 * q + 1 : Nat) : Int)) = _
        rw [Nat.add_zero, show k + ((2 * q + 1 : Nat) : Int) = k + 2 * (q : Int) + 1 by omega, hb]
        unfold stripeAt; simp
    · have ha := (hA q (by omega)).2
      have hb := (hB q (by omega)).2
      refine ⟨?_, ?_⟩
      · show evolve init (τ + 0) (k + ((2 * q + 2 : Nat) : Int)) = _
        rw [Nat.add_zero, show k + ((2 * q + 2 : Nat) : Int) = k + 2 * (q : Int) + 2 by omega, ha]
        unfold stripeAt; simp
      · show evolve init' (τ' + 0) (k + ((2 * q + 2 : Nat) : Int)) = _
        rw [Nat.add_zero, show k + ((2 * q + 2 : Nat) : Int) = k + 2 * (q : Int) + 2 by omega, hb]
        unfold stripeAt; simp
  -- phase one: for `s ≤ 2 j`, the rows agree on cells `1, …, 2 j`, and beyond `s` both are still the stripe
  have phase1 : ∀ s, s ≤ 2 * j → (∀ i, 1 ≤ i → i ≤ 2 * j → A s i = B s i) ∧
      (∀ i, s < i → i ≤ 2 * j → A s i = stripeAt i ∧ B s i = stripeAt i) := by
    intro s
    induction s with
    | zero =>
      intro _
      refine ⟨fun i h1 h2 => ?_, fun i h1 h2 => start i (by omega) h2⟩
      rw [(start i h1 h2).1, (start i h1 h2).2]
    | succ s ih =>
      intro hs
      obtain ⟨hag, hst⟩ := ih (by omega)
      have hsj : s < 4 * j := by omega
      -- the stripe beyond `s + 1`, in both rows
      have stA : ∀ i, s + 1 < i → i ≤ 2 * j → A (s + 1) i = stripeAt i := by
        intro i h1 h2
        rw [stepA s i (by omega), (hst (i - 1) (by omega) (by omega)).1, (hst i (by omega) h2).1]
        by_cases hi2 : i < 2 * j
        · rw [(hst (i + 1) (by omega) (by omega)).1]
          unfold stripeAt
          rcases Nat.mod_two_eq_zero_or_one i with h | h
          · rw [show (i - 1) % 2 = 1 by omega, show (i + 1) % 2 = 1 by omega, h]; rfl
          · rw [show (i - 1) % 2 = 0 by omega, show (i + 1) % 2 = 0 by omega, h]; rfl
        · have hi : i = 2 * j := by omega
          unfold stripeAt
          rw [hi, show (2 * j - 1) % 2 = 1 by omega, show (2 * j) % 2 = 0 by omega]
          rfl
      have stB : ∀ i, s + 1 < i → i ≤ 2 * j → B (s + 1) i = stripeAt i := by
        intro i h1 h2
        rw [stepB s i (by omega), (hst (i - 1) (by omega) (by omega)).2, (hst i (by omega) h2).2]
        by_cases hi2 : i < 2 * j
        · rw [(hst (i + 1) (by omega) (by omega)).2]
          unfold stripeAt
          rcases Nat.mod_two_eq_zero_or_one i with h | h
          · rw [show (i - 1) % 2 = 1 by omega, show (i + 1) % 2 = 1 by omega, h]; rfl
          · rw [show (i - 1) % 2 = 0 by omega, show (i + 1) % 2 = 0 by omega, h]; rfl
        · have hi : i = 2 * j := by omega
          unfold stripeAt
          rw [hi, show (2 * j - 1) % 2 = 1 by omega, show (2 * j) % 2 = 0 by omega]
          rfl
      refine ⟨fun i h1 h2 => ?_, fun i h1 h2 => ⟨stA i h1 h2, stB i h1 h2⟩⟩
      rw [stepA s i h1, stepB s i h1]
      have hl : A s (i - 1) = B s (i - 1) := by
        by_cases hi1 : i = 1
        · rw [hi1]; exact col0 s hsj
        · exact hag (i - 1) (by omega) (by omega)
      by_cases hi2 : i < 2 * j
      · rw [hl, hag i h1 h2, hag (i + 1) (by omega) (by omega)]
      · -- cell `2 j`: still the stripe's 1 at time `s` (since `s < 2 j`), which hides the cell beyond
        have hi : i = 2 * j := by omega
        have h1A := (hst i (by omega) h2).1
        have h1B := (hst i (by omega) h2).2
        have hone : stripeAt i = true := by unfold stripeAt; rw [hi]; simp
        rw [hl, h1A, h1B, hone, Bool.true_or, Bool.true_or]
  -- phase two: from `2 j` on, the agreement loses one cell per step
  have phase2 : ∀ n, n ≤ 2 * j → ∀ i, 1 ≤ i → i + n ≤ 2 * j → A (2 * j + n) i = B (2 * j + n) i := by
    intro n
    induction n with
    | zero => intro _ i h1 h2; exact (phase1 (2 * j) (Nat.le_refl _)).1 i h1 (by omega)
    | succ n ih =>
      intro hn i h1 h2
      rw [show 2 * j + (n + 1) = 2 * j + n + 1 by omega, stepA _ i h1, stepB _ i h1]
      have hl : A (2 * j + n) (i - 1) = B (2 * j + n) (i - 1) := by
        by_cases hi1 : i = 1
        · rw [hi1]; exact col0 _ (by omega)
        · exact ih (by omega) (i - 1) (by omega) (by omega)
      rw [hl, ih (by omega) i h1 (by omega), ih (by omega) (i + 1) (by omega) (by omega)]
  intro s hs
  have e : evolve init (τ + s) (k + 1) = A s 1 := by
    show evolve init (τ + s) (k + 1) = evolve init (τ + s) (k + ((1 : Nat) : Int)); rfl
  have e' : evolve init' (τ' + s) (k + 1) = B s 1 := by
    show evolve init' (τ' + s) (k + 1) = evolve init' (τ' + s) (k + ((1 : Nat) : Int)); rfl
  rw [e, e']
  by_cases h2 : s ≤ 2 * j
  · exact (phase1 s h2).1 1 (Nat.le_refl 1) (by omega)
  · have := phase2 (s - 2 * j) (by omega) 1 (Nat.le_refl 1) (by omega)
    rwa [show 2 * j + (s - 2 * j) = s by omega] at this

/-! ### The left column follows -/

/-- **No column is eventually periodic if each of its 0s comes less than `4 j` steps after `9 j` 1s.** -/
theorem wide_wall_column (init : Int → Bool) (m : Int) (hm : init m = true)
    (hz : ∀ x : Int, x < m → init x = false) (k : Int) (T P j T0 : Nat) (hP : 0 < P) (hT0 : T + 9 * j ≤ T0)
    (hper : ∀ t : Nat, T ≤ t → evolve init (t + P) k = evolve init t k)
    (hcover : ∀ t : Nat, T0 ≤ t → evolve init t k = false →
      ∃ τ, T + 9 * j ≤ τ ∧ τ ≤ t ∧ t < τ + 4 * j ∧
        ∀ i : Nat, i < 9 * j → evolve init (τ - 9 * j + i) k = true) :
    False := by
  have right : ∀ t : Nat, T0 ≤ t → evolve init t k = false →
      evolve init (t + P) (k + 1) = evolve init t (k + 1) := by
    intro t ht h0
    obtain ⟨τ, h1, h2, h3, hrun⟩ := hcover t ht h0
    have sh := black_shield init j k (τ - 9 * j) hrun
    rw [show τ - 9 * j + 9 * j = τ by omega] at sh
    have sh' := black_shield init j k (τ + P - 9 * j) (fun i hi => by
      rw [show τ + P - 9 * j + i = τ - 9 * j + i + P by omega, hper _ (by omega)]
      exact hrun i hi)
    rw [show τ + P - 9 * j + 9 * j = τ + P by omega] at sh'
    have ag := shield_agree init init k τ (τ + P) j sh sh' (fun s hs => by
      rw [show τ + P + s = τ + s + P by omega, hper _ (by omega)]) (t - τ) (by omega)
    rw [show τ + (t - τ) = t by omega, show τ + P + (t - τ) = t + P by omega] at ag
    exact ag.symm
  exact adjacent_columns init m hm hz (k - 1) T0 P hP
    (fun t ht => by
      rw [left_cell init (t + P) k, left_cell init t k, show t + P + 1 = t + 1 + P by omega,
        hper (t + 1) (by omega), hper t (by omega)]
      cases hc : evolve init t k with
      | true => rfl
      | false => rw [right t ht hc])
    (fun t ht => by rw [show k - 1 + 1 = k by omega]; exact hper t (by omega))

/-! ### A long run and any tail -/

/-- **A black run of length `r ≥ 9` and a period `P` with `P - r ≤ 4 ⌊r / 9⌋` cannot go together**, in any column of
the orbit of a row with a leftmost 1. -/
theorem long_run_tail_column (init : Int → Bool) (m : Int) (hm : init m = true)
    (hz : ∀ x : Int, x < m → init x = false) (k : Int) (T P r t1 : Nat)
    (hper : ∀ t : Nat, T ≤ t → evolve init (t + P) k = evolve init t k) (ht1 : T ≤ t1) (hr : 9 ≤ r)
    (hrP : r ≤ P) (hrun : ∀ s : Nat, s < r → evolve init (t1 + s) k = true) (htail : P - r ≤ 4 * (r / 9)) :
    False := by
  have hP : 0 < P := by omega
  have perq : ∀ q n : Nat, evolve init (t1 + (n + q * P)) k = evolve init (t1 + n) k := by
    intro q
    induction q with
    | zero => intro n; rw [Nat.zero_mul, Nat.add_zero]
    | succ q ih =>
      intro n
      rw [Nat.succ_mul, show t1 + (n + (q * P + P)) = t1 + (n + q * P) + P by omega, hper _ (by omega), ih]
  refine wide_wall_column init m hm hz k T P (r / 9) (t1 + r) hP (by omega) hper ?_
  intro t ht h0
  have hq : (t - t1) % P + (t - t1) / P * P = t - t1 := by rw [Nat.mul_comm]; exact Nat.mod_add_div _ _
  have hρ : (t - t1) % P < P := Nat.mod_lt _ hP
  have hcol : evolve init t k = evolve init (t1 + (t - t1) % P) k := by
    rw [← perq ((t - t1) / P) ((t - t1) % P), hq, show t1 + (t - t1) = t by omega]
  have hge : r ≤ (t - t1) % P := by
    refine Classical.byContradiction fun hlt => ?_
    rw [hcol, hrun _ (by omega)] at h0
    exact absurd h0 (by decide)
  refine ⟨t1 + (t - t1) / P * P + r, ?_, ?_, ?_, fun i hi => ?_⟩
  · omega
  · omega
  · omega
  · rw [show t1 + (t - t1) / P * P + r - 9 * (r / 9) + i = t1 + ((r - 9 * (r / 9) + i) + (t - t1) / P * P) by omega,
      perq, hrun _ (by omega)]

/-- **The center column**: no eventual period `P` from any time on has a black run of length `r ≥ 9` with
`P - r ≤ 4 ⌊r / 9⌋`. -/
theorem center_long_run_tail (T P r t1 : Nat)
    (hper : ∀ t : Nat, T ≤ t → Rule30Prize.center (t + P) = Rule30Prize.center t) (ht1 : T ≤ t1) (hr : 9 ≤ r)
    (hrP : r ≤ P) (hrun : ∀ s : Nat, s < r → Rule30Prize.center (t1 + s) = true) (htail : P - r ≤ 4 * (r / 9)) :
    False := by
  simp only [← evolve_single_center] at hper hrun
  exact long_run_tail_column single 0 rfl (fun x hx => decide_eq_false (by omega)) 0 T P r t1 hper ht1 hr hrP hrun
    htail

/-- The kit's Theorem B asks `9 ⌈(P - r + 9) / 2⌉ ≤ r` (as `9 * ((P - r + 10) / 2) ≤ r`); that implies the condition
here. -/
theorem kit_theoremB_condition (P r : Nat) (h : 9 * ((P - r + 10) / 2) ≤ r) : 9 ≤ r ∧ P - r ≤ 4 * (r / 9) := by
  omega

end Rule30Open
