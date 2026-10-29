module

public import Rule30Open.Columns.WallSegments

/-!
# After nine 1s: the set of possible windows of three cells, and the periods it excludes

[WallSegments](WallSegments.md) follows the two cells right of a column after the nine-black wall with three values
per cell. Here the state is the set of windows of three cells, right of the column, that the true row may hold, a set
of the eight windows written as the bits of a number (`wmem`); the cell beyond the window is free at every step
(`sstep`, sound by `sstep_sound`). The set keeps correlations that three values lose, so the cell right of the column
is known more often (`sknown`), and after reading 1s it can become known again.

* `wall_sets_column`: no column of the orbit of a row with a leftmost 1 is eventually periodic if, from a time just
  after nine 1s, the set knows the cell right of the column at every 0 of one period.
* `wall_set_block_column`, `center_wall_set_block`: the same for a block `B` with `wallSet B = true`.
* `run_set_column`, `center_run_set`: the block `1^a u` for every `a ≥ 9`, when `u` passes `segSet` from the wall.
* `center_runs_odd_100`, `center_runs_odd_110`, `center_runs_even_1010`: for `a ≥ 9` and `k ≥ 0`, the blocks
  `1^a 0^(2k+3) 1 0 0`, `1^a 0^(2k+3) 1 1 0` and `1^a 0^(2k+2) 1 0 1 0`, which the three values do not reach.

The natural-language argument is `WallSets.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

open Ruliology.CellularAutomata

/-! ### Sets of windows -/

/-- The index of the window `c1 c2 c3` among the eight. -/
def widx (c1 c2 c3 : Bool) : Nat := c1.toNat + 2 * c2.toNat + 4 * c3.toNat

/-- Whether the set `m` holds the window `c1 c2 c3` (bit `widx c1 c2 c3` of `m`). -/
def wmem (m : Nat) (c1 c2 c3 : Bool) : Bool := m.testBit (widx c1 c2 c3)

/-- The two windows one step after window `i` beside a column reading `x`, the cell beyond the window free. -/
def wimg (x : Bool) (i : Nat) : Nat :=
  2 ^ widx (xor x (i.testBit 0 || i.testBit 1)) (xor (i.testBit 0) (i.testBit 1 || i.testBit 2))
      (xor (i.testBit 1) (i.testBit 2 || false)) |||
    2 ^ widx (xor x (i.testBit 0 || i.testBit 1)) (xor (i.testBit 0) (i.testBit 1 || i.testBit 2))
      (xor (i.testBit 1) (i.testBit 2 || true))

/-- One step of the set of windows beside a column reading `x`. -/
def sstep (x : Bool) (m : Nat) : Nat :=
  (List.range 8).foldl (fun acc i => if m.testBit i then acc ||| wimg x i else acc) 0

/-- **The step is sound**: the true window one step later is in the next set, whatever the cell beyond. -/
theorem sstep_sound : ∀ m, m < 256 → ∀ x a1 a2 a3 a4 : Bool, wmem m a1 a2 a3 = true →
    wmem (sstep x m) (xor x (a1 || a2)) (xor a1 (a2 || a3)) (xor a2 (a3 || a4)) = true := by
  decide +kernel

theorem sstep_lt : ∀ m, m < 256 → ∀ x, sstep x m < 256 := by decide +kernel

/-- Whether every window of the set has the same first cell. -/
def sknown (m : Nat) : Bool := (m &&& 85 == 0) || (m &&& 170 == 0)

/-- The first cell, when it is known. -/
def sval (m : Nat) : Bool := m &&& 170 != 0

theorem sknown_val : ∀ m, m < 256 → sknown m = true → ∀ a1 a2 a3 : Bool, wmem m a1 a2 a3 = true →
    a1 = sval m := by
  decide +kernel

/-- The wall: the first two cells read `0 1`, the third is free. -/
def wall3 : Nat := 68

theorem wall3_mem (a3 : Bool) : wmem wall3 false true a3 = true := by cases a3 <;> rfl

/-! ### Along a column -/

/-- The set at time `T1 + n`: the wall at `T1`, back to the wall after every nine 1s, and the set step otherwise. -/
def sstate (col : Nat → Bool) (T1 : Nat) : Nat → Nat
  | 0 => wall3
  | n + 1 => if nine col (T1 + n + 1) = true then wall3 else sstep (col (T1 + n)) (sstate col T1 n)

theorem sstate_succ (col : Nat → Bool) (T1 n : Nat) :
    sstate col T1 (n + 1) =
      if nine col (T1 + n + 1) = true then wall3 else sstep (col (T1 + n)) (sstate col T1 n) := rfl

theorem sstate_lt (col : Nat → Bool) (T1 : Nat) : ∀ n, sstate col T1 n < 256 := by
  intro n
  induction n with
  | zero => show wall3 < 256; decide
  | succ n ih =>
    rw [sstate_succ]
    split
    · show wall3 < 256; decide
    · exact sstep_lt _ ih _

/-- **The set is sound along a real column**: from a time `T1` that follows nine 1s, the true window right of the
column is in the set at every later time. -/
theorem sstate_sound (init : Int → Bool) (k : Int) (T1 : Nat) (h9 : 9 ≤ T1)
    (hwall : ∀ i : Nat, i < 9 → evolve init (T1 - 9 + i) k = true) :
    ∀ n : Nat, wmem (sstate (fun t => evolve init t k) T1 n) (evolve init (T1 + n) (k + 1))
      (evolve init (T1 + n) (k + 2)) (evolve init (T1 + n) (k + 3)) = true := by
  have atWall : ∀ t : Nat, 9 ≤ t → (∀ i : Nat, i < 9 → evolve init (t - 9 + i) k = true) →
      wmem wall3 (evolve init t (k + 1)) (evolve init t (k + 2)) (evolve init t (k + 3)) = true := by
    intro t ht h
    have w := wall_forms init k (t - 9) h
    rw [show t - 9 + 9 = t by omega] at w
    rw [w.1, w.2]
    exact wall3_mem _
  have cellAt : ∀ (t : Nat) (j : Int), evolve init (t + 1) (k + j) =
      xor (evolve init t (k + j - 1)) (evolve init t (k + j) || evolve init t (k + j + 1)) := fun t j => rfl
  intro n
  induction n with
  | zero => rw [Nat.add_zero]; exact atWall T1 h9 hwall
  | succ n ih =>
    rw [sstate_succ]
    by_cases hn : nine (fun t => evolve init t k) (T1 + n + 1) = true
    · rw [ite_eq_left hn, show T1 + (n + 1) = T1 + n + 1 by omega]
      exact atWall (T1 + n + 1) (by omega) ((nine_spec _ _).1 hn)
    · rw [ite_eq_right hn, show T1 + (n + 1) = T1 + n + 1 by omega, cellAt, cellAt, cellAt,
        show k + 1 - 1 = k by omega, show k + 2 - 1 = k + 1 by omega, show k + 3 - 1 = k + 2 by omega,
        show k + 1 + 1 = k + 2 by omega, show k + 2 + 1 = k + 3 by omega, show k + 3 + 1 = k + 4 by omega]
      exact sstep_sound _ (sstate_lt _ _ n) _ _ _ _ _ ih

/-- **The set repeats with the column.** -/
theorem sstate_periodic (col : Nat → Bool) (T P T1 : Nat) (hP : 0 < P) (hT1 : T + 9 ≤ T1)
    (hper : ∀ t : Nat, T ≤ t → col (t + P) = col t) (hwall : nine col T1 = true) :
    ∀ n : Nat, sstate col T1 (n + P) = sstate col T1 n := by
  have nineP : ∀ t : Nat, T + 9 ≤ t → nine col (t + P) = nine col t := by
    intro t ht
    unfold nine
    congr 1
    funext i
    rw [show t + P - 9 + i = t - 9 + i + P by omega, hper (t - 9 + i) (by omega)]
  intro n
  induction n with
  | zero =>
    obtain ⟨q, hq⟩ : ∃ q, P = q + 1 := ⟨P - 1, by omega⟩
    rw [Nat.zero_add, hq, sstate_succ, show T1 + q + 1 = T1 + P by omega, nineP T1 hT1, hwall]
    rfl
  | succ n ih =>
    rw [show n + 1 + P = (n + P) + 1 by omega, sstate_succ, sstate_succ, ih,
      show T1 + (n + P) + 1 = T1 + n + 1 + P by omega, nineP (T1 + n + 1) (by omega),
      show T1 + (n + P) = T1 + n + P by omega, hper (T1 + n) (by omega)]

/-- **The left column follows.** If the column is periodic from `T` and, from a time `T1 ≥ T + 9` just after nine
1s, the set knows the cell right of the column at every 0 of one period, two adjacent columns are eventually
periodic, which `adjacent_columns` rules out. -/
theorem wall_sets_column (init : Int → Bool) (m : Int) (hm : init m = true)
    (hz : ∀ x : Int, x < m → init x = false) (k : Int) (T P : Nat) (hP : 0 < P)
    (hper : ∀ t : Nat, T ≤ t → evolve init (t + P) k = evolve init t k)
    (T1 : Nat) (hT1 : T + 9 ≤ T1) (hwall : ∀ i : Nat, i < 9 → evolve init (T1 - 9 + i) k = true)
    (hgood : ∀ j : Nat, j < P → evolve init (T1 + j) k = false →
      sknown (sstate (fun t => evolve init t k) T1 j) = true) : False := by
  have hsound := sstate_sound init k T1 (by omega) hwall
  have hst := sstate_periodic (fun t => evolve init t k) T P T1 hP hT1 hper ((nine_spec _ _).2 hwall)
  have stq : ∀ q j : Nat, sstate (fun t => evolve init t k) T1 (j + q * P) =
      sstate (fun t => evolve init t k) T1 j := by
    intro q
    induction q with
    | zero => intro j; rw [Nat.zero_mul, Nat.add_zero]
    | succ q ih => intro j; rw [Nat.succ_mul, ← Nat.add_assoc, hst, ih]
  have colq : ∀ q j : Nat, evolve init (T1 + (j + q * P)) k = evolve init (T1 + j) k := by
    intro q
    induction q with
    | zero => intro j; rw [Nat.zero_mul, Nat.add_zero]
    | succ q ih =>
      intro j
      rw [Nat.succ_mul, show T1 + (j + (q * P + P)) = T1 + (j + q * P) + P by omega, hper _ (by omega), ih]
  have known : ∀ n : Nat, evolve init (T1 + n) k = false →
      evolve init (T1 + n) (k + 1) = sval (sstate (fun t => evolve init t k) T1 n) := by
    intro n h0
    have hn : n % P + n / P * P = n := by rw [Nat.mul_comm]; exact Nat.mod_add_div n P
    have hk : sknown (sstate (fun t => evolve init t k) T1 n) = true := by
      rw [← hn, stq]
      exact hgood (n % P) (Nat.mod_lt _ hP) (by rw [← colq (n / P), hn]; exact h0)
    exact sknown_val _ (sstate_lt _ _ n) hk _ _ _ (hsound n)
  have left : ∀ t : Nat, T1 ≤ t → evolve init t (k - 1) =
      xor (evolve init (t + 1) k) (evolve init t k || sval (sstate (fun t => evolve init t k) T1 (t - T1))) := by
    intro t ht
    rw [left_cell init t k]
    cases hc : evolve init t k with
    | true => rfl
    | false =>
      have := known (t - T1) (by rw [show T1 + (t - T1) = t by omega]; exact hc)
      rw [show T1 + (t - T1) = t by omega] at this
      rw [this]
  exact adjacent_columns init m hm hz (k - 1) T1 P hP
    (fun t ht => by
      rw [left (t + P) (by omega), left t ht, show t + P + 1 = t + 1 + P by omega, hper (t + 1) (by omega),
        hper t (by omega), show t + P - T1 = t - T1 + P by omega, hst])
    (fun t ht => by rw [show k - 1 + 1 = k by omega]; exact hper t (by omega))

/-! ### Blocks -/

/-- **The criterion on a block**: some phase `i` follows nine 1s of `B` read cyclically, and from there the set knows
the cell right of the column at every 0 of one period. -/
def wallSet (B : List Bool) : Bool :=
  (List.range B.length).any fun i =>
    nine (cyc B) (9 * B.length + i) &&
      (List.range B.length).all fun j => cyc B (9 * B.length + i + j) || sknown (sstate (cyc B) (9 * B.length + i) j)

/-- The set depends only on the column from nine steps before its start. -/
theorem sstate_congr (col col' : Nat → Bool) (T1 T1' : Nat) (h9 : 9 ≤ T1) (h9' : 9 ≤ T1')
    (h : ∀ x : Nat, col (T1 - 9 + x) = col' (T1' - 9 + x)) : ∀ n, sstate col T1 n = sstate col' T1' n := by
  have hn : ∀ t, nine col (T1 + t) = nine col' (T1' + t) := by
    intro t
    unfold nine
    congr 1
    funext i
    rw [show T1 + t - 9 + i = T1 - 9 + (t + i) by omega, show T1' + t - 9 + i = T1' - 9 + (t + i) by omega, h]
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sstate_succ, sstate_succ, ih, show T1 + n + 1 = T1 + (n + 1) by omega,
      show T1' + n + 1 = T1' + (n + 1) by omega, hn, show T1 + n = T1 - 9 + (n + 9) by omega,
      show T1' + n = T1' - 9 + (n + 9) by omega, h]

/-- **No column is eventually periodic with a block that passes `wallSet`.** -/
theorem wall_set_block_column (init : Int → Bool) (m : Int) (hm : init m = true)
    (hz : ∀ x : Int, x < m → init x = false) (k : Int) (T : Nat) (B : List Bool) (hB : wallSet B = true)
    (hcol : ∀ t : Nat, T ≤ t → evolve init t k = cyc B (t - T)) : False := by
  unfold wallSet at hB
  rw [List.any_eq_true] at hB
  obtain ⟨i, hi, hgood⟩ := hB
  rw [List.mem_range] at hi
  rw [Bool.and_eq_true, List.all_eq_true] at hgood
  obtain ⟨hnine, hall⟩ := hgood
  have hP : 0 < B.length := by omega
  have hper : ∀ t : Nat, T ≤ t → evolve init (t + B.length) k = evolve init t k := by
    intro t ht
    rw [hcol (t + B.length) (by omega), hcol t ht, show t + B.length - T = t - T + B.length by omega, cyc_add]
  have shift : ∀ x : Nat, evolve init (T + 9 * B.length + i - 9 + x) k = cyc B (9 * B.length + i - 9 + x) := by
    intro x
    rw [hcol _ (by omega), show T + 9 * B.length + i - 9 + x - T = 9 * B.length + i - 9 + x by omega]
  have hcongr := sstate_congr (fun t => evolve init t k) (cyc B) (T + 9 * B.length + i) (9 * B.length + i)
    (by omega) (by omega) shift
  refine wall_sets_column init m hm hz k T B.length hP hper (T + 9 * B.length + i) (by omega) ?_ ?_
  · intro x hx
    rw [shift x]
    exact (nine_spec _ _).1 hnine x hx
  · intro j hj h0
    have hj' := hall j (List.mem_range.mpr hj)
    have hc : evolve init (T + 9 * B.length + i + j) k = cyc B (9 * B.length + i + j) := by
      rw [show T + 9 * B.length + i + j = T + 9 * B.length + i - 9 + (j + 9) by omega, shift,
        show 9 * B.length + i - 9 + (j + 9) = 9 * B.length + i + j by omega]
    rw [hc] at h0
    rw [h0, Bool.false_or] at hj'
    rw [hcongr j]
    exact hj'

/-- **The center column is not eventually periodic with a block that passes `wallSet`.** -/
theorem center_wall_set_block (T : Nat) (B : List Bool) (hB : wallSet B = true)
    (hcol : ∀ t : Nat, T ≤ t → Rule30Prize.center t = cyc B (t - T)) : False := by
  simp only [← evolve_single_center] at hcol
  exact wall_set_block_column single 0 rfl (fun x hx => decide_eq_false (by omega)) 0 T B hB hcol

/-! ### One long run and one segment -/

/-- Run the set along a segment from `m`, checking at each 0 that the cell right of the column is known. -/
def segSet : Nat → List Bool → Bool
  | _, [] => true
  | m, c :: u => (c || sknown m) && segSet (sstep c m) u

/-- The set along the column without resets, from `m` at time `t0`. -/
def srun (col : Nat → Bool) (t0 : Nat) (m : Nat) : Nat → Nat
  | 0 => m
  | n + 1 => srun col (t0 + 1) (sstep (col t0) m) n

theorem srun_succ' (col : Nat → Bool) : ∀ (n t0 m : Nat),
    srun col t0 m (n + 1) = sstep (col (t0 + n)) (srun col t0 m n) := by
  intro n
  induction n with
  | zero => intro t0 m; rfl
  | succ n ih =>
    intro t0 m
    show srun col (t0 + 1) (sstep (col t0) m) (n + 1) = _
    rw [ih, show t0 + 1 + n = t0 + (n + 1) by omega]
    rfl

theorem segSet_known (col : Nat → Bool) : ∀ (u : List Bool) (t0 m : Nat), segSet m u = true →
    (∀ x, x < u.length → col (t0 + x) = u.getD x false) →
    ∀ j, j < u.length → col (t0 + j) = false → sknown (srun col t0 m j) = true := by
  intro u
  induction u with
  | nil => intro t0 m _ _ j hj; exact absurd hj (by simp)
  | cons c u ih =>
    intro t0 m hok hcol j hj h0
    simp only [segSet, Bool.and_eq_true] at hok
    have hc : col t0 = c := by have := hcol 0 (by simp); simpa using this
    cases j with
    | zero =>
      rw [Nat.add_zero, hc] at h0
      rw [h0, Bool.false_or] at hok
      exact hok.1
    | succ j =>
      show sknown (srun col (t0 + 1) (sstep (col t0) m) j) = true
      rw [hc]
      refine ih (t0 + 1) (sstep c m) hok.2 (fun x hx => ?_) j (by simp at hj; omega) ?_
      · have := hcol (x + 1) (by simp; omega)
        rw [show t0 + (x + 1) = t0 + 1 + x by omega] at this
        rw [this]
        rfl
      · rw [show t0 + 1 + j = t0 + (j + 1) by omega]; exact h0

theorem sstate_eq_srun (col : Nat → Bool) (T1 L : Nat) (h : ∀ n, n < L → nine col (T1 + n + 1) = false) :
    ∀ n, n ≤ L → sstate col T1 n = srun col T1 wall3 n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hn
    rw [sstate_succ, ite_eq_right (by rw [h n (by omega)]; decide), ih (by omega), srun_succ']

/-- **A long run and one segment.** If a column repeats `1^a u` with `a ≥ 9`, where `u` starts with a 0, passes
`segSet` from the wall, and has a 0 among any nine consecutive places, two adjacent columns are eventually periodic,
which `adjacent_columns` rules out. -/
theorem run_set_column (init : Int → Bool) (m : Int) (hm : init m = true)
    (hz : ∀ x : Int, x < m → init x = false) (k : Int) (T a : Nat) (ha : 9 ≤ a) (u : List Bool)
    (hu0 : u.getD 0 true = false) (hok : segSet wall3 u = true)
    (hgap : ∀ n, 9 ≤ n → n < u.length → ∃ d, d < 9 ∧ u.getD (n - d) false = false)
    (hcol : ∀ t : Nat, T ≤ t → evolve init t k = cyc (List.replicate a true ++ u) (t - T)) : False := by
  have hlen : (List.replicate a true ++ u).length = a + u.length := by simp
  have hpos : 0 < u.length := by
    cases u with
    | nil => simp at hu0
    | cons c u => simp
  have hper : ∀ t : Nat, T ≤ t → evolve init (t + (List.replicate a true ++ u).length) k = evolve init t k := by
    intro t ht
    rw [hcol _ (by omega), hcol t ht, show t + (List.replicate a true ++ u).length - T =
      t - T + (List.replicate a true ++ u).length by omega, cyc_add]
  let P := a + u.length
  have colAt : ∀ x : Nat, x < P → evolve init (T + P + x) k = (List.replicate a true ++ u).getD x false := by
    intro x hx
    rw [hcol _ (by omega), show T + P + x - T = x + (List.replicate a true ++ u).length by simp [P]; omega, cyc_add]
    unfold cyc
    rw [Nat.mod_eq_of_lt (by rw [hlen]; exact hx)]
  have colU : ∀ x : Nat, x < u.length → evolve init (T + P + a + x) k = u.getD x false := by
    intro x hx
    rw [show T + P + a + x = T + P + (a + x) by omega, colAt (a + x) (by omega), getD_rep_add]
  have colRun : ∀ x : Nat, x < a → evolve init (T + P + x) k = true := by
    intro x hx
    rw [colAt x (by omega), getD_rep_lt true u a x hx]
  have hnr : ∀ n, n < u.length → nine (fun t => evolve init t k) (T + P + a + n + 1) = false := by
    intro n hn
    by_cases h8 : n ≤ 8
    · refine nine_false _ _ (T + P + a) (by omega) (by omega) (by omega) ?_
      have := colU 0 hpos
      rw [Nat.add_zero] at this
      rw [this]
      cases u with
      | nil => simp at hpos
      | cons c u => simpa using hu0
    · obtain ⟨d, hd, hz0⟩ := hgap n (by omega) hn
      exact nine_false _ _ (T + P + a + (n - d)) (by omega) (by omega) (by omega)
        (by rw [colU (n - d) (by omega)]; exact hz0)
  have hperP : ∀ t : Nat, T ≤ t → evolve init (t + P) k = evolve init t k := by
    intro t ht
    show evolve init (t + (a + u.length)) k = _
    rw [← hlen]
    exact hper t ht
  refine wall_sets_column init m hm hz k T P (by omega) hperP (T + P + a) (by omega) ?_ ?_
  · intro i hi
    rw [show T + P + a - 9 + i = T + P + (a - 9 + i) by omega]
    exact colRun _ (by omega)
  · intro j hj h0
    by_cases hju : j < u.length
    · rw [sstate_eq_srun _ (T + P + a) u.length hnr j (by omega)]
      exact segSet_known (fun t => evolve init t k) u (T + P + a) wall3 hok (fun x hx => colU x hx) j hju h0
    · have := colAt (a + j - P) (by omega)
      rw [show T + P + (a + j - P) = T + P + a + j - P by omega, getD_rep_lt true u a _ (by omega)] at this
      have hper' := hper (T + P + a + j - P) (by omega)
      rw [show T + P + a + j - P + (List.replicate a true ++ u).length = T + P + a + j by simp [P]; omega,
        this] at hper'
      rw [hper'] at h0
      exact absurd h0 (by decide)

/-- **The center column and one segment.** -/
theorem center_run_set (T a : Nat) (ha : 9 ≤ a) (u : List Bool) (hu0 : u.getD 0 true = false)
    (hok : segSet wall3 u = true)
    (hgap : ∀ n, 9 ≤ n → n < u.length → ∃ d, d < 9 ∧ u.getD (n - d) false = false)
    (hcol : ∀ t : Nat, T ≤ t → Rule30Prize.center t = cyc (List.replicate a true ++ u) (t - T)) : False := by
  simp only [← evolve_single_center] at hcol
  exact run_set_column single 0 rfl (fun x hx => decide_eq_false (by omega)) 0 T a ha u hu0 hok hgap hcol

/-! ### Parity families -/

theorem sstep_wall0 : sstep false wall3 = 136 := by decide
theorem sstep_136 : sstep false 136 = 34 := by decide
theorem sstep_34 : sstep false 34 = 168 := by decide
theorem sstep_168 : sstep false 168 = 34 := by decide
theorem sknown_wall3 : sknown wall3 = true := by decide
theorem sknown_136 : sknown 136 = true := by decide
theorem sknown_34 : sknown 34 = true := by decide
theorem sknown_168 : sknown 168 = true := by decide

/-- Under 0s the set alternates between `34` and `168`, both knowing the cell right of the column. -/
theorem segSet_zeros_168 (tl : List Bool) : ∀ k : Nat,
    segSet 168 (List.replicate (2 * k) false ++ tl) = segSet 168 tl := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by omega, List.replicate_succ, List.replicate_succ, List.cons_append,
      List.cons_append]
    simp only [segSet, sstep_168, sstep_34, sknown_168, sknown_34, Bool.or_true, Bool.true_and, ih]

theorem segSet_zeros_34 (tl : List Bool) : ∀ k : Nat,
    segSet 34 (List.replicate (2 * k) false ++ tl) = segSet 34 tl := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by omega, List.replicate_succ, List.replicate_succ, List.cons_append,
      List.cons_append]
    simp only [segSet, sstep_168, sstep_34, sknown_168, sknown_34, Bool.or_true, Bool.true_and, ih]

/-- A segment of 0s, then a short tail, has a 0 among any nine consecutive places. -/
theorem gap_zeros_tail (b : Nat) (hb : 1 ≤ b) (tl : List Bool) (htl : tl.length ≤ 7) :
    ∀ n, 9 ≤ n → n < (List.replicate b false ++ tl).length →
      ∃ d, d < 9 ∧ (List.replicate b false ++ tl).getD (n - d) false = false := by
  intro n _ hn
  rw [List.length_append, List.length_replicate] at hn
  by_cases hnb : n < b
  · exact ⟨0, by omega, by rw [Nat.sub_zero, getD_rep_lt false tl b n hnb]⟩
  · exact ⟨n - b + 1, by omega, by rw [show n - (n - b + 1) = b - 1 by omega, getD_rep_lt false tl b _ (by omega)]⟩

theorem odd_zeros (k : Nat) (tl : List Bool) :
    List.replicate (2 * k + 3) false ++ tl = false :: false :: false :: (List.replicate (2 * k) false ++ tl) := by
  rw [show 2 * k + 3 = 2 * k + 1 + 1 + 1 by omega, List.replicate_succ, List.replicate_succ, List.replicate_succ]
  rfl

theorem even_zeros (k : Nat) (tl : List Bool) :
    List.replicate (2 * k + 2) false ++ tl = false :: false :: (List.replicate (2 * k) false ++ tl) := by
  rw [show 2 * k + 2 = 2 * k + 1 + 1 by omega, List.replicate_succ, List.replicate_succ]
  rfl

theorem segSet_odd (k : Nat) (tl : List Bool) (h : segSet 168 tl = true) :
    segSet wall3 (List.replicate (2 * k + 3) false ++ tl) = true := by
  rw [odd_zeros]
  simp only [segSet, sstep_wall0, sstep_136, sstep_34, sknown_wall3, sknown_136, sknown_34, Bool.or_true,
    Bool.true_and, segSet_zeros_168, h]

theorem segSet_even (k : Nat) (tl : List Bool) (h : segSet 34 tl = true) :
    segSet wall3 (List.replicate (2 * k + 2) false ++ tl) = true := by
  rw [even_zeros]
  simp only [segSet, sstep_wall0, sstep_136, sknown_wall3, sknown_136, Bool.or_true, Bool.true_and,
    segSet_zeros_34, h]

/-- **`1^a 0^(2k+3) 1 0 0`**, for every `a ≥ 9` and `k ≥ 0`, is not an eventual period of the center column. -/
theorem center_runs_odd_100 (T a k : Nat) (ha : 9 ≤ a)
    (hcol : ∀ t : Nat, T ≤ t → Rule30Prize.center t =
      cyc (List.replicate a true ++ (List.replicate (2 * k + 3) false ++ [true, false, false])) (t - T)) : False :=
  center_run_set T a ha _ (by rw [odd_zeros]; rfl) (segSet_odd k _ (by decide))
    (gap_zeros_tail (2 * k + 3) (by omega) _ (by simp)) hcol

/-- **`1^a 0^(2k+3) 1 1 0`**, for every `a ≥ 9` and `k ≥ 0`, is not an eventual period of the center column. -/
theorem center_runs_odd_110 (T a k : Nat) (ha : 9 ≤ a)
    (hcol : ∀ t : Nat, T ≤ t → Rule30Prize.center t =
      cyc (List.replicate a true ++ (List.replicate (2 * k + 3) false ++ [true, true, false])) (t - T)) : False :=
  center_run_set T a ha _ (by rw [odd_zeros]; rfl) (segSet_odd k _ (by decide))
    (gap_zeros_tail (2 * k + 3) (by omega) _ (by simp)) hcol

/-- **`1^a 0^(2k+2) 1 0 1 0`**, for every `a ≥ 9` and `k ≥ 0`, is not an eventual period of the center column. -/
theorem center_runs_even_1010 (T a k : Nat) (ha : 9 ≤ a)
    (hcol : ∀ t : Nat, T ≤ t → Rule30Prize.center t =
      cyc (List.replicate a true ++ (List.replicate (2 * k + 2) false ++ [true, false, true, false])) (t - T)) :
    False :=
  center_run_set T a ha _ (by rw [even_zeros]; rfl) (segSet_even k _ (by decide))
    (gap_zeros_tail (2 * k + 2) (by omega) _ (by simp)) hcol

/-! ### Spot checks -/

/-- `1^9 0 0 0 1 0 0`, beyond the three-valued run, passes `wallSet`. -/
theorem wallSet_odd_100 : wallSet (List.replicate 9 true ++ [false, false, false, true, false, false]) = true := by
  decide

end Rule30Open
