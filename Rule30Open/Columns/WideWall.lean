module

public import Rule30Open.Columns.LongRuns

/-!
# A stripe beside a column keeps the next cell for twice its length, whatever the column reads

Nine 1s in a column leave the two cells right of it reading `0 1` (`wall_forms`), and while the column stays black that
wall stays (`wall_stays`); so `9 j` 1s leave the `2 j` cells right of the column reading `(0 1)^j` (`black_shield`, the
kit's Lemma A* for the single seed). A stripe `… 1 0 1` of `L` cells that ends in a black cell is fixed by Rule 30, and
each of its 1s hides the cell to its right, so two rows that both carry it and then see the same column agree on the
`L` cells for `L` steps, and on one cell fewer at each later step: on the cell right of the column for `2 L` steps
(`stripe_agree`). The shield is the stripe of length `2 j` (`shield_agree`).

* `wide_wall_column`: no column of the orbit of a row with a leftmost 1 is eventually periodic if each of its 0s comes
  less than `4 j` steps after `9 j` 1s.
* `long_run_tail_column`, `center_long_run_tail`: in particular no eventual period of length `P` has a black run of
  length `r ≥ 9` with `P - r ≤ 4 ⌊r / 9⌋`. The kit's Theorem B (`Rule30BlackRuns.no_long_black_run`) asks
  `9 ⌈(P - r + 9) / 2⌉ ≤ r`, which implies this.
* `black_white_tail_column`, `center_black_white_tail`: after nine 1s and then `b` 0s, the cell right of the column is
  black through the white run (`white_latch`) and ends it as the stripe `1 (0 1)^j` with `j = ⌊(b - 1) / 9⌋`, so no
  eventual period is a black run of `s ≥ 9` steps, a white run of `b ≥ 1` steps and a tail of at most
  `4 ⌊(b - 1) / 9⌋ + 2` steps. The kit's Theorem D (`Rule30BlackRuns.no_black_white_run`) asks
  `b ≥ 1 + 9 ⌈(P - s - b + 8) / 2⌉`, which implies this.

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

/-! ### Two rows that end in the same stripe agree beside the column -/

/-- The stripe of length `L` that ends in a black cell: cell `k + i` is black when `L - i` is even. -/
def stripeEnd (L i : Nat) : Bool := (L - i) % 2 == 0

/-- **Two rows that read the same stripe ending in a black cell on cells `k + 1, …, k + L`, and then see the same
column, agree on the cell right of the column for `2 L` steps.** The stripe is fixed by Rule 30 and its black cells
hide the cells beyond from the OR, so the rows agree on all `L` cells for `L` steps; after that the agreement loses one
cell per step. -/
theorem stripe_agree (init init' : Int → Bool) (k : Int) (τ τ' L : Nat)
    (hA : ∀ i : Nat, 1 ≤ i → i ≤ L → evolve init τ (k + i) = stripeEnd L i)
    (hB : ∀ i : Nat, 1 ≤ i → i ≤ L → evolve init' τ' (k + i) = stripeEnd L i)
    (hcol : ∀ s : Nat, s < 2 * L → evolve init (τ + s) k = evolve init' (τ' + s) k) :
    ∀ s : Nat, s < 2 * L → evolve init (τ + s) (k + 1) = evolve init' (τ' + s) (k + 1) := by
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
  have col0 : ∀ s, s < 2 * L → A s 0 = B s 0 := by
    intro s hs
    show evolve init (τ + s) (k + ((0 : Nat) : Int)) = evolve init' (τ' + s) (k + ((0 : Nat) : Int))
    rw [show k + ((0 : Nat) : Int) = k by omega]
    exact hcol s hs
  -- the stripe is fixed: away from its left end, each cell keeps its value, and the last one hides the cell beyond
  have fixedStripe : ∀ (C : Nat → Nat → Bool) (s i : Nat),
      (C (s + 1) i = xor (C s (i - 1)) (C s i || C s (i + 1))) → 2 ≤ i → i ≤ L →
      C s (i - 1) = stripeEnd L (i - 1) → C s i = stripeEnd L i → (i < L → C s (i + 1) = stripeEnd L (i + 1)) →
      C (s + 1) i = stripeEnd L i := by
    intro C s i hstep h1 h2 hl hc hr
    rw [hstep, hl, hc]
    by_cases hiL : i < L
    · rw [hr hiL]
      unfold stripeEnd
      rcases Nat.mod_two_eq_zero_or_one (L - i) with h | h
      · rw [show (L - (i - 1)) % 2 = 1 by omega, show (L - (i + 1)) % 2 = 1 by omega, h]; rfl
      · rw [show (L - (i - 1)) % 2 = 0 by omega, show (L - (i + 1)) % 2 = 0 by omega, h]; rfl
    · have hi : i = L := by omega
      unfold stripeEnd
      rw [hi, show (L - (L - 1)) % 2 = 1 by omega, Nat.sub_self]
      rfl
  -- phase one: for `s ≤ L`, the rows agree on cells `1, …, L`, and beyond `s` both are still the stripe
  have phase1 : ∀ s, s ≤ L → (∀ i, 1 ≤ i → i ≤ L → A s i = B s i) ∧
      (∀ i, s < i → i ≤ L → A s i = stripeEnd L i ∧ B s i = stripeEnd L i) := by
    intro s
    induction s with
    | zero =>
      intro _
      refine ⟨fun i h1 h2 => ?_, fun i h1 h2 => ⟨hA i (by omega) h2, hB i (by omega) h2⟩⟩
      show evolve init (τ + 0) (k + i) = evolve init' (τ' + 0) (k + i)
      rw [Nat.add_zero, Nat.add_zero, hA i h1 h2, hB i h1 h2]
    | succ s ih =>
      intro hs
      obtain ⟨hag, hst⟩ := ih (by omega)
      have hsL : s < 2 * L := by omega
      refine ⟨fun i h1 h2 => ?_, fun i h1 h2 =>
        ⟨fixedStripe A s i (stepA s i (by omega)) (by omega) h2 (hst (i - 1) (by omega) (by omega)).1
          (hst i (by omega) h2).1 (fun hi => (hst (i + 1) (by omega) (by omega)).1),
         fixedStripe B s i (stepB s i (by omega)) (by omega) h2 (hst (i - 1) (by omega) (by omega)).2
          (hst i (by omega) h2).2 (fun hi => (hst (i + 1) (by omega) (by omega)).2)⟩⟩
      rw [stepA s i h1, stepB s i h1]
      have hl : A s (i - 1) = B s (i - 1) := by
        by_cases hi1 : i = 1
        · rw [hi1]; exact col0 s hsL
        · exact hag (i - 1) (by omega) (by omega)
      by_cases hiL : i < L
      · rw [hl, hag i h1 h2, hag (i + 1) (by omega) (by omega)]
      · -- cell `L`: still the stripe's black end at time `s` (since `s < L`), which hides the cell beyond
        have hi : i = L := by omega
        have h1A := (hst i (by omega) h2).1
        have h1B := (hst i (by omega) h2).2
        have hone : stripeEnd L i = true := by unfold stripeEnd; rw [hi, Nat.sub_self]; rfl
        rw [hl, h1A, h1B, hone, Bool.true_or, Bool.true_or]
  -- phase two: from `L` on, the agreement loses one cell per step
  have phase2 : ∀ n, n ≤ L → ∀ i, 1 ≤ i → i + n ≤ L → A (L + n) i = B (L + n) i := by
    intro n
    induction n with
    | zero => intro _ i h1 h2; exact (phase1 L (Nat.le_refl _)).1 i h1 (by omega)
    | succ n ih =>
      intro hn i h1 h2
      rw [show L + (n + 1) = L + n + 1 by omega, stepA _ i h1, stepB _ i h1]
      have hl : A (L + n) (i - 1) = B (L + n) (i - 1) := by
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
  by_cases h2 : s ≤ L
  · exact (phase1 s h2).1 1 (by omega) (by omega)
  · have := phase2 (s - L) (by omega) 1 (Nat.le_refl 1) (by omega)
    rwa [show L + (s - L) = s by omega] at this

/-- The shield `(0 1)^j` is the stripe of length `2 j` that ends in a black cell. -/
theorem shield_stripe (init : Int → Bool) (k : Int) (τ j : Nat)
    (h : ∀ i : Nat, i < j → evolve init τ (k + 2 * i + 1) = false ∧ evolve init τ (k + 2 * i + 2) = true) :
    ∀ i : Nat, 1 ≤ i → i ≤ 2 * j → evolve init τ (k + i) = stripeEnd (2 * j) i := by
  intro i h1 h2
  obtain ⟨q, rfl | rfl⟩ : ∃ q, i = 2 * q + 1 ∨ i = 2 * q + 2 := ⟨(i - 1) / 2, by omega⟩
  · rw [show k + ((2 * q + 1 : Nat) : Int) = k + 2 * (q : Int) + 1 by omega, (h q (by omega)).1]
    unfold stripeEnd; rw [show (2 * j - (2 * q + 1)) % 2 = 1 by omega]; rfl
  · rw [show k + ((2 * q + 2 : Nat) : Int) = k + 2 * (q : Int) + 2 by omega, (h q (by omega)).2]
    unfold stripeEnd; rw [show (2 * j - (2 * q + 2)) % 2 = 0 by omega]; rfl

/-- **Two shielded rows that see the same column agree on the cell right of it for `4 j` steps.** -/
theorem shield_agree (init init' : Int → Bool) (k : Int) (τ τ' j : Nat)
    (hA : ∀ i : Nat, i < j → evolve init τ (k + 2 * i + 1) = false ∧ evolve init τ (k + 2 * i + 2) = true)
    (hB : ∀ i : Nat, i < j → evolve init' τ' (k + 2 * i + 1) = false ∧ evolve init' τ' (k + 2 * i + 2) = true)
    (hcol : ∀ s : Nat, s < 4 * j → evolve init (τ + s) k = evolve init' (τ' + s) k) :
    ∀ s : Nat, s < 4 * j → evolve init (τ + s) (k + 1) = evolve init' (τ' + s) (k + 1) := by
  intro s hs
  exact stripe_agree init init' k τ τ' (2 * j) (shield_stripe init k τ j hA) (shield_stripe init' k τ' j hB)
    (fun s hs => hcol s (by omega)) s (by omega)

/-! ### The left column follows -/

/-- **The left column follows.** If column `k` has period `P` from time `T` on and, from `T0 ≥ T` on, the cell right of
it repeats with period `P` at every 0 of the column, then column `k - 1` has period `P` from `T0` on, and two adjacent
columns of the orbit of a row with a leftmost 1 cannot both be eventually periodic. -/
theorem zeros_repeat_column (init : Int → Bool) (m : Int) (hm : init m = true)
    (hz : ∀ x : Int, x < m → init x = false) (k : Int) (T P T0 : Nat) (hP : 0 < P) (hT0 : T ≤ T0)
    (hper : ∀ t : Nat, T ≤ t → evolve init (t + P) k = evolve init t k)
    (hright : ∀ t : Nat, T0 ≤ t → evolve init t k = false →
      evolve init (t + P) (k + 1) = evolve init t (k + 1)) :
    False :=
  adjacent_columns init m hm hz (k - 1) T0 P hP
    (fun t ht => by
      rw [left_cell init (t + P) k, left_cell init t k, show t + P + 1 = t + 1 + P by omega,
        hper (t + 1) (by omega), hper t (by omega)]
      cases hc : evolve init t k with
      | true => rfl
      | false => rw [hright t ht hc])
    (fun t ht => by rw [show k - 1 + 1 = k by omega]; exact hper t (by omega))

/-- **No column is eventually periodic if each of its 0s comes less than `4 j` steps after `9 j` 1s.** -/
theorem wide_wall_column (init : Int → Bool) (m : Int) (hm : init m = true)
    (hz : ∀ x : Int, x < m → init x = false) (k : Int) (T P j T0 : Nat) (hP : 0 < P) (hT0 : T + 9 * j ≤ T0)
    (hper : ∀ t : Nat, T ≤ t → evolve init (t + P) k = evolve init t k)
    (hcover : ∀ t : Nat, T0 ≤ t → evolve init t k = false →
      ∃ τ, T + 9 * j ≤ τ ∧ τ ≤ t ∧ t < τ + 4 * j ∧
        ∀ i : Nat, i < 9 * j → evolve init (τ - 9 * j + i) k = true) :
    False := by
  refine zeros_repeat_column init m hm hz k T P T0 hP (by omega) hper fun t ht h0 => ?_
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

/-! ### A black run, a white run and a short tail -/

/-- **While the column is white after the wall, the cell right of it is black.** The wall `0 1` makes it black at the
first step, and a black cell beside a white column stays black: `0 ⊕ (1 ∨ ·) = 1`. -/
theorem white_latch (init : Int → Bool) (k : Int) (W n : Nat)
    (hw : evolve init W (k + 1) = false ∧ evolve init W (k + 2) = true)
    (hwht : ∀ i : Nat, i < n → evolve init (W + i) k = false) :
    ∀ i : Nat, 1 ≤ i → i ≤ n → evolve init (W + i) (k + 1) = true := by
  intro i
  induction i with
  | zero => intro h; omega
  | succ i ih =>
    intro _ hi
    rw [show W + (i + 1) = W + i + 1 by omega, evolve_succ, show k + 1 - 1 = k by omega, hwht i (by omega)]
    by_cases h0 : i = 0
    · rw [h0, Nat.add_zero, show k + 1 + 1 = k + 2 by omega, hw.2, Bool.or_true]; rfl
    · rw [ih (by omega) (by omega), Bool.true_or]; rfl

/-- A black cell followed by the shield `(0 1)^j` is the stripe of length `2 j + 1` that ends in a black cell. -/
theorem black_shield_stripe (init : Int → Bool) (k : Int) (τ j : Nat) (h0 : evolve init τ (k + 1) = true)
    (h : ∀ i : Nat, i < j → evolve init τ (k + 1 + 2 * i + 1) = false ∧
      evolve init τ (k + 1 + 2 * i + 2) = true) :
    ∀ i : Nat, 1 ≤ i → i ≤ 2 * j + 1 → evolve init τ (k + i) = stripeEnd (2 * j + 1) i := by
  intro i h1 h2
  by_cases hi : i = 1
  · rw [hi, show k + ((1 : Nat) : Int) = k + 1 by omega, h0]
    unfold stripeEnd
    rw [show (2 * j + 1 - 1) % 2 = 0 by omega]; rfl
  · have := shield_stripe init (k + 1) τ j h (i - 1) (by omega) (by omega)
    rw [show k + 1 + ((i - 1 : Nat) : Int) = k + (i : Int) by omega] at this
    rw [this]
    unfold stripeEnd
    rw [show 2 * j + 1 - i = 2 * j - (i - 1) by omega]

/-- **A black run of `s ≥ 9` steps, then a white run of `b ≥ 1` steps, then a tail of at most `4 ⌊(b - 1) / 9⌋ + 2`
steps cannot make up a period** of any column of the orbit of a row with a leftmost 1. At the first 0 the wall gives
the cell right of the column; during the white run that cell is black; and its own run of 1s leaves the stripe
`1 (0 1)^j` with `j = ⌊(b - 1) / 9⌋`, which keeps it for `4 j + 2` steps of the tail. -/
theorem black_white_tail_column (init : Int → Bool) (m : Int) (hm : init m = true)
    (hz : ∀ x : Int, x < m → init x = false) (k : Int) (T P s b t1 : Nat)
    (hper : ∀ t : Nat, T ≤ t → evolve init (t + P) k = evolve init t k) (ht1 : T ≤ t1) (hs : 9 ≤ s) (hb : 1 ≤ b)
    (hsb : s + b ≤ P) (hblk : ∀ i : Nat, i < s → evolve init (t1 + i) k = true)
    (hwht : ∀ i : Nat, i < b → evolve init (t1 + s + i) k = false)
    (htail : P - s - b ≤ 4 * ((b - 1) / 9) + 2) : False := by
  have hP : 0 < P := by omega
  -- the column at time `t1 + q P + n` reads what it reads at `t1 + n`
  have perq : ∀ q n : Nat, evolve init (t1 + q * P + n) k = evolve init (t1 + n) k := by
    intro q n
    have h : evolve init (t1 + n + q * P) k = evolve init (t1 + n) k :=
      periodic_iterate (fun t => evolve init t k) (t1 + n) P (fun t ht => hper t (by omega)) q
    rw [show t1 + q * P + n = t1 + n + q * P by omega, h]
  -- in every period: the wall after the black run, the latch during the white run, the stripe after it
  have wallq : ∀ q : Nat, evolve init (t1 + q * P + s) (k + 1) = false ∧
      evolve init (t1 + q * P + s) (k + 2) = true := by
    intro q
    have := wall_forms init k (t1 + q * P + (s - 9)) (fun i hi => by
      rw [show t1 + q * P + (s - 9) + i = t1 + q * P + (s - 9 + i) by omega, perq]; exact hblk _ (by omega))
    rwa [show t1 + q * P + (s - 9) + 9 = t1 + q * P + s by omega] at this
  have latchq : ∀ q i : Nat, 1 ≤ i → i ≤ b → evolve init (t1 + q * P + s + i) (k + 1) = true := fun q =>
    white_latch init k (t1 + q * P + s) b (wallq q) (fun i hi => by
      rw [show t1 + q * P + s + i = t1 + q * P + (s + i) by omega, perq, ← Nat.add_assoc]; exact hwht i hi)
  have stripeq : ∀ q : Nat, ∀ i : Nat, 1 ≤ i → i ≤ 2 * ((b - 1) / 9) + 1 →
      evolve init (t1 + q * P + s + b) (k + i) = stripeEnd (2 * ((b - 1) / 9) + 1) i := by
    intro q
    refine black_shield_stripe init k (t1 + q * P + s + b) ((b - 1) / 9) (latchq q b hb (Nat.le_refl b)) ?_
    have := black_shield init ((b - 1) / 9) (k + 1) (t1 + q * P + s + (b - 9 * ((b - 1) / 9))) (fun i hi => by
      rw [show t1 + q * P + s + (b - 9 * ((b - 1) / 9)) + i = t1 + q * P + s + (b - 9 * ((b - 1) / 9) + i) by omega]
      exact latchq q _ (by omega) (by omega))
    rwa [show t1 + q * P + s + (b - 9 * ((b - 1) / 9)) + 9 * ((b - 1) / 9) = t1 + q * P + s + b by omega] at this
  refine zeros_repeat_column init m hm hz k T P t1 hP ht1 hper fun t ht h0 => ?_
  -- place `t` in its period
  obtain ⟨q, ρ, hρ, rfl⟩ : ∃ q ρ, ρ < P ∧ t = t1 + q * P + ρ :=
    ⟨(t - t1) / P, (t - t1) % P, Nat.mod_lt _ hP, by
      have := Nat.div_add_mod (t - t1) P; rw [Nat.mul_comm] at this; omega⟩
  rw [show t1 + q * P + ρ + P = t1 + (q + 1) * P + ρ by rw [Nat.add_mul, Nat.one_mul]; omega]
  rw [perq] at h0
  -- a 0 comes after the black run
  have hsρ : s ≤ ρ := Classical.byContradiction fun hlt => by
    rw [hblk ρ (by omega)] at h0; exact absurd h0 (by decide)
  by_cases hρs : ρ = s
  · -- the first 0: the wall
    rw [hρs, (wallq q).1, (wallq (q + 1)).1]
  by_cases hρb : ρ < s + b
  · -- inside the white run: the latch
    rw [show t1 + q * P + ρ = t1 + q * P + s + (ρ - s) by omega,
      show t1 + (q + 1) * P + ρ = t1 + (q + 1) * P + s + (ρ - s) by omega,
      latchq q _ (by omega) (by omega), latchq (q + 1) _ (by omega) (by omega)]
  -- in the tail: the stripe after the white run
  have ag := stripe_agree init init k (t1 + q * P + s + b) (t1 + (q + 1) * P + s + b) (2 * ((b - 1) / 9) + 1)
    (stripeq q) (stripeq (q + 1)) (fun n _ => by
      rw [show t1 + q * P + s + b + n = t1 + q * P + (s + b + n) by omega,
        show t1 + (q + 1) * P + s + b + n = t1 + (q + 1) * P + (s + b + n) by omega, perq, perq])
    (ρ - s - b) (by omega)
  rw [show t1 + q * P + s + b + (ρ - s - b) = t1 + q * P + ρ by omega,
    show t1 + (q + 1) * P + s + b + (ρ - s - b) = t1 + (q + 1) * P + ρ by omega] at ag
  exact ag.symm

/-- **The center column**: no eventual period has a black run of `s ≥ 9` steps followed by a white run of `b ≥ 1`
steps and a tail of at most `4 ⌊(b - 1) / 9⌋ + 2` steps. -/
theorem center_black_white_tail (T P s b t1 : Nat)
    (hper : ∀ t : Nat, T ≤ t → Rule30Prize.center (t + P) = Rule30Prize.center t) (ht1 : T ≤ t1) (hs : 9 ≤ s)
    (hb : 1 ≤ b) (hsb : s + b ≤ P) (hblk : ∀ i : Nat, i < s → Rule30Prize.center (t1 + i) = true)
    (hwht : ∀ i : Nat, i < b → Rule30Prize.center (t1 + s + i) = false)
    (htail : P - s - b ≤ 4 * ((b - 1) / 9) + 2) : False := by
  simp only [← evolve_single_center] at hper hblk hwht
  exact black_white_tail_column single 0 rfl (fun x hx => decide_eq_false (by omega)) 0 T P s b t1 hper ht1 hs hb
    hsb hblk hwht htail

/-- The kit's Theorem D asks `1 + 9 ⌈(P - s - r + 8) / 2⌉ ≤ r` of its white run `r` (as
`1 + 9 * ((P - s - r + 9) / 2) ≤ r`); that implies the condition here. -/
theorem kit_theoremD_condition (P s r : Nat) (h : 1 + 9 * ((P - s - r + 9) / 2) ≤ r) :
    1 ≤ r ∧ P - s - r ≤ 4 * ((r - 1) / 9) + 2 := by
  omega

end Rule30Open
