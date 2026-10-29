module

public import Rule30Open.Columns.LongRuns

/-!
# After nine 1s: segments that keep the next cell known, and the periods they exclude

Nine 1s in a column leave the two cells right of it reading `0 1`, whatever the rest of the row holds (`wall_forms`).
From there, three-valued Rule 30 on those two cells, with the cell beyond them unknown, follows the column for a
while: `tstep` is the step, `tstep_sound` says that the cells it knows are the true ones, and `wstate` runs it along a
column, back to the wall after every nine 1s (`wstate_sound`). Whenever it knows the cell right of the column at a 0 of
the column, the column to the left is a function of the column (`left_cell`); at a 1 it always is. If that holds at
every 0 of an eventually periodic column, two adjacent columns are eventually periodic, which `adjacent_columns` rules
out.

* `wall_segments_column`: no column of the orbit of a row with a leftmost 1 is eventually periodic if, from a time
  just after nine 1s, `wstate` knows the cell right of the column at every 0 of one period.
* `wall_block_column`, `center_wall_block`: the same for an eventual period given as a block `B` with
  `wallGood B = true`, a computation on `B` alone.
* `run_segment_column`, `center_run_segment`: the block `1^a u` for every `a ≥ 9`, when `u` passes `segOK` from the
  wall (and has no long run of 1s).
* `run_family_column`, `center_run_family`: for `a ≥ 9` and `z ≥ 0`, the blocks `1^a h 0^z t` with `h` one of `0`
  and `0 1 1` and `t` one of the empty word and `1 0`: among them `1^a 0^b 1 0`, `1^a 0 1 1 0^c` and
  `1^a 0 1 1 0^c 1 0`.
* `segOK_kit_tails`: the eight tails of the kit's Theorem B′, which it excludes after 18 or 27 1s, pass `segOK`.

The natural-language argument is `WallSegments.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

open Ruliology.CellularAutomata

/-! ### Three-valued Rule 30 beside a column -/

/-- `some b` for a cell known to be `b`, `none` for an unknown cell. -/
abbrev Tri := Option Bool

/-- Three-valued OR: known when either side is known to be 1, or both are known. -/
def tor : Tri → Tri → Tri
  | some true, _ => some true
  | _, some true => some true
  | some false, some false => some false
  | _, _ => none

/-- Three-valued XOR: known when both sides are known. -/
def txor : Tri → Tri → Tri
  | some a, some b => some (xor a b)
  | _, _ => none

/-- One step of the two cells right of a column that reads `c`; the cell beyond them is unknown. -/
def tstep (c : Bool) (s : Tri × Tri) : Tri × Tri :=
  (txor (some c) (tor s.1 s.2), txor s.1 (tor s.2 none))

/-- Whether the true value `a` agrees with the three-valued `x`. -/
def agree : Tri → Bool → Bool
  | none, _ => true
  | some b, a => a == b

theorem agree_eq {x : Tri} {a b : Bool} (h : agree x a = true) (hx : x = some b) : a = b := by
  subst hx; simpa [agree] using h

/-- **The step is sound.** If the true cells right of the column agree with the state, the true cells one step later
agree with the next state, whatever the third cell holds. -/
theorem tstep_sound : ∀ (c a1 a2 a3 : Bool) (s1 s2 : Tri), agree s1 a1 = true → agree s2 a2 = true →
    agree (tstep c (s1, s2)).1 (xor c (a1 || a2)) = true ∧ agree (tstep c (s1, s2)).2 (xor a1 (a2 || a3)) = true := by
  intro c a1 a2 a3 s1 s2
  cases c <;> cases a1 <;> cases a2 <;> cases a3 <;> rcases s1 with _ | ⟨_ | _⟩ <;>
    rcases s2 with _ | ⟨_ | _⟩ <;> decide

/-! ### Along a column -/

/-- The wall `0 1` that nine 1s leave. -/
def wall : Tri × Tri := (some false, some true)

/-- Whether the column reads 1 at the nine times before `t`. -/
def nine (col : Nat → Bool) (t : Nat) : Bool := (List.range 9).all fun i => col (t - 9 + i)

theorem nine_spec (col : Nat → Bool) (t : Nat) : nine col t = true ↔ ∀ i, i < 9 → col (t - 9 + i) = true := by
  unfold nine
  rw [List.all_eq_true]
  constructor
  · intro h i hi; exact h i (List.mem_range.mpr hi)
  · intro h i hi; exact h i (List.mem_range.mp hi)

/-- The state of the two cells right of the column at time `T1 + n`: the wall at `T1`, back to the wall after every
nine 1s, and the three-valued step otherwise. -/
def wstate (col : Nat → Bool) (T1 : Nat) : Nat → Tri × Tri
  | 0 => wall
  | n + 1 => if nine col (T1 + n + 1) = true then wall else tstep (col (T1 + n)) (wstate col T1 n)

theorem wstate_succ (col : Nat → Bool) (T1 n : Nat) :
    wstate col T1 (n + 1) =
      if nine col (T1 + n + 1) = true then wall else tstep (col (T1 + n)) (wstate col T1 n) := rfl

/-- **The state is sound along a real column.** Started at a time `T1` that follows nine 1s, the state agrees with
the two true cells right of the column at every later time. -/
theorem wstate_sound (init : Int → Bool) (k : Int) (T1 : Nat) (h9 : 9 ≤ T1)
    (hwall : ∀ i : Nat, i < 9 → evolve init (T1 - 9 + i) k = true) :
    ∀ n : Nat, agree (wstate (fun t => evolve init t k) T1 n).1 (evolve init (T1 + n) (k + 1)) = true ∧
      agree (wstate (fun t => evolve init t k) T1 n).2 (evolve init (T1 + n) (k + 2)) = true := by
  have atWall : ∀ t : Nat, 9 ≤ t → (∀ i : Nat, i < 9 → evolve init (t - 9 + i) k = true) →
      agree wall.1 (evolve init t (k + 1)) = true ∧ agree wall.2 (evolve init t (k + 2)) = true := by
    intro t ht h
    have w := wall_forms init k (t - 9) h
    rw [show t - 9 + 9 = t by omega] at w
    rw [w.1, w.2]
    exact ⟨rfl, rfl⟩
  intro n
  induction n with
  | zero => rw [Nat.add_zero]; exact atWall T1 h9 hwall
  | succ n ih =>
    rw [wstate_succ]
    by_cases hn : nine (fun t => evolve init t k) (T1 + n + 1) = true
    · rw [ite_eq_left hn, show T1 + (n + 1) = T1 + n + 1 by omega]
      exact atWall (T1 + n + 1) (by omega) ((nine_spec _ _).1 hn)
    · rw [ite_eq_right hn]
      have s := tstep_sound (evolve init (T1 + n) k) (evolve init (T1 + n) (k + 1)) (evolve init (T1 + n) (k + 2))
        (evolve init (T1 + n) (k + 3)) _ _ ih.1 ih.2
      have e1 : evolve init (T1 + (n + 1)) (k + 1) =
          xor (evolve init (T1 + n) k) (evolve init (T1 + n) (k + 1) || evolve init (T1 + n) (k + 2)) := by
        show rule30 (evolve init (T1 + n) (k + 1 - 1)) (evolve init (T1 + n) (k + 1))
          (evolve init (T1 + n) (k + 1 + 1)) = _
        rw [show k + 1 - 1 = k by omega, show k + 1 + 1 = k + 2 by omega]; rfl
      have e2 : evolve init (T1 + (n + 1)) (k + 2) =
          xor (evolve init (T1 + n) (k + 1)) (evolve init (T1 + n) (k + 2) || evolve init (T1 + n) (k + 3)) := by
        show rule30 (evolve init (T1 + n) (k + 2 - 1)) (evolve init (T1 + n) (k + 2))
          (evolve init (T1 + n) (k + 2 + 1)) = _
        rw [show k + 2 - 1 = k + 1 by omega, show k + 2 + 1 = k + 3 by omega]; rfl
      rw [e1, e2]
      exact s

/-- **The state repeats with the column.** If the column has period `P` from `T` and `T1 ≥ T + 9` follows nine 1s,
the state has period `P`. -/
theorem wstate_periodic (col : Nat → Bool) (T P T1 : Nat) (hP : 0 < P) (hT1 : T + 9 ≤ T1)
    (hper : ∀ t : Nat, T ≤ t → col (t + P) = col t) (hwall : nine col T1 = true) :
    ∀ n : Nat, wstate col T1 (n + P) = wstate col T1 n := by
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
    rw [Nat.zero_add, hq, wstate_succ, show T1 + q + 1 = T1 + P by omega, nineP T1 hT1, hwall]
    rfl
  | succ n ih =>
    rw [show n + 1 + P = (n + P) + 1 by omega, wstate_succ, wstate_succ, ih,
      show T1 + (n + P) + 1 = T1 + n + 1 + P by omega, nineP (T1 + n + 1) (by omega),
      show T1 + (n + P) = T1 + n + P by omega, hper (T1 + n) (by omega)]

/-- **The left column follows.** If the column is periodic from `T` and, from a time `T1 ≥ T + 9` just after nine
1s, the state knows the cell right of the column at every 0 of one period, the two columns are eventually periodic,
which `adjacent_columns` rules out. -/
theorem wall_segments_column (init : Int → Bool) (m : Int) (hm : init m = true)
    (hz : ∀ x : Int, x < m → init x = false) (k : Int) (T P : Nat) (hP : 0 < P)
    (hper : ∀ t : Nat, T ≤ t → evolve init (t + P) k = evolve init t k)
    (T1 : Nat) (hT1 : T + 9 ≤ T1) (hwall : ∀ i : Nat, i < 9 → evolve init (T1 - 9 + i) k = true)
    (hgood : ∀ j : Nat, j < P → evolve init (T1 + j) k = false →
      (wstate (fun t => evolve init t k) T1 j).1 ≠ none) : False := by
  have hsound := wstate_sound init k T1 (by omega) hwall
  have hst := wstate_periodic (fun t => evolve init t k) T P T1 hP hT1 hper ((nine_spec _ _).2 hwall)
  -- both repeat with period `P` from `T1`, over any number of periods
  have stq : ∀ q j : Nat, wstate (fun t => evolve init t k) T1 (j + q * P) =
      wstate (fun t => evolve init t k) T1 j := by
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
      evolve init (T1 + n) (k + 1) = ((wstate (fun t => evolve init t k) T1 n).1).getD false := by
    intro n h0
    have hn : n % P + n / P * P = n := by rw [Nat.mul_comm]; exact Nat.mod_add_div n P
    have hne : (wstate (fun t => evolve init t k) T1 n).1 ≠ none := by
      rw [← hn, stq]
      exact hgood (n % P) (Nat.mod_lt _ hP) (by rw [← colq (n / P), hn]; exact h0)
    obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hne
    rw [hb, agree_eq (hsound n).1 hb]
    rfl
  have left : ∀ t : Nat, T1 ≤ t → evolve init t (k - 1) =
      xor (evolve init (t + 1) k)
        (evolve init t k || ((wstate (fun t => evolve init t k) T1 (t - T1)).1).getD false) := by
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

/-- The block `B` read cyclically. -/
def cyc (B : List Bool) (i : Nat) : Bool := B.getD (i % B.length) false

/-- **The criterion on a block**, a computation on `B` alone: some phase `i` follows nine 1s of `B` read cyclically,
and from there the state knows the cell right of the column at every 0 of one period. -/
def wallGood (B : List Bool) : Bool :=
  (List.range B.length).any fun i =>
    nine (cyc B) (9 * B.length + i) &&
      (List.range B.length).all fun j =>
        cyc B (9 * B.length + i + j) || ((wstate (cyc B) (9 * B.length + i) j).1).isSome

theorem cyc_add (B : List Bool) (i : Nat) : cyc B (i + B.length) = cyc B i := by
  unfold cyc; rw [Nat.add_mod_right]

/-- The state depends only on the column from nine steps before its start. -/
theorem wstate_congr (col col' : Nat → Bool) (T1 T1' : Nat) (h9 : 9 ≤ T1) (h9' : 9 ≤ T1')
    (h : ∀ x : Nat, col (T1 - 9 + x) = col' (T1' - 9 + x)) : ∀ n, wstate col T1 n = wstate col' T1' n := by
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
    rw [wstate_succ, wstate_succ, ih, show T1 + n + 1 = T1 + (n + 1) by omega,
      show T1' + n + 1 = T1' + (n + 1) by omega, hn, show T1 + n = T1 - 9 + (n + 9) by omega,
      show T1' + n = T1' - 9 + (n + 9) by omega, h]

/-- **No column is eventually periodic with a block that passes `wallGood`.** -/
theorem wall_block_column (init : Int → Bool) (m : Int) (hm : init m = true)
    (hz : ∀ x : Int, x < m → init x = false) (k : Int) (T : Nat) (B : List Bool) (hB : wallGood B = true)
    (hcol : ∀ t : Nat, T ≤ t → evolve init t k = cyc B (t - T)) : False := by
  unfold wallGood at hB
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
  have hcongr := wstate_congr (fun t => evolve init t k) (cyc B) (T + 9 * B.length + i) (9 * B.length + i)
    (by omega) (by omega) shift
  refine wall_segments_column init m hm hz k T B.length hP hper (T + 9 * B.length + i) (by omega) ?_ ?_
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
    intro hnone
    rw [hnone] at hj'
    exact Bool.noConfusion hj'

/-- **The center column is not eventually periodic with a block that passes `wallGood`.** -/
theorem center_wall_block (T : Nat) (B : List Bool) (hB : wallGood B = true)
    (hcol : ∀ t : Nat, T ≤ t → Rule30Prize.center t = cyc B (t - T)) : False := by
  simp only [← evolve_single_center] at hcol
  exact wall_block_column single 0 rfl (fun x hx => decide_eq_false (by omega)) 0 T B hB hcol

/-! ### Families -/

/-- Run along a segment from the state `s`, checking at each 0 that the cell right of the column is known. -/
def segOK : Tri × Tri → List Bool → Bool
  | _, [] => true
  | s, c :: u => (c || s.1.isSome) && segOK (tstep c s) u

/-- The state after a segment, without resets. -/
def segRun : Tri × Tri → List Bool → Tri × Tri
  | s, [] => s
  | s, c :: u => segRun (tstep c s) u

theorem segOK_append (s : Tri × Tri) :
    ∀ l l' : List Bool, segOK s (l ++ l') = (segOK s l && segOK (segRun s l) l') := by
  intro l
  induction l generalizing s with
  | nil => intro l'; simp [segOK, segRun]
  | cons c l ih => intro l'; simp only [List.cons_append, segOK, segRun, ih, Bool.and_assoc]

/-- The state along the column without resets, from the state `s` at time `t0`. -/
def wrun (col : Nat → Bool) (t0 : Nat) (s : Tri × Tri) : Nat → Tri × Tri
  | 0 => s
  | n + 1 => wrun col (t0 + 1) (tstep (col t0) s) n

theorem wrun_succ' (col : Nat → Bool) : ∀ (n t0 : Nat) (s : Tri × Tri),
    wrun col t0 s (n + 1) = tstep (col (t0 + n)) (wrun col t0 s n) := by
  intro n
  induction n with
  | zero => intro t0 s; rfl
  | succ n ih =>
    intro t0 s
    show wrun col (t0 + 1) (tstep (col t0) s) (n + 1) = _
    rw [ih, show t0 + 1 + n = t0 + (n + 1) by omega]
    rfl

/-- A segment that passes `segOK` keeps the cell right of the column known at each of its 0s, along any column that
reads it. -/
theorem segOK_known (col : Nat → Bool) : ∀ (u : List Bool) (t0 : Nat) (s : Tri × Tri), segOK s u = true →
    (∀ x, x < u.length → col (t0 + x) = u.getD x false) →
    ∀ j, j < u.length → col (t0 + j) = false → ((wrun col t0 s j).1).isSome = true := by
  intro u
  induction u with
  | nil => intro t0 s _ _ j hj; exact absurd hj (by simp)
  | cons c u ih =>
    intro t0 s hok hcol j hj h0
    simp only [segOK, Bool.and_eq_true] at hok
    have hc : col t0 = c := by have := hcol 0 (by simp); simpa using this
    cases j with
    | zero =>
      rw [Nat.add_zero, hc] at h0
      rw [h0, Bool.false_or] at hok
      exact hok.1
    | succ j =>
      show ((wrun col (t0 + 1) (tstep (col t0) s) j).1).isSome = true
      rw [hc]
      refine ih (t0 + 1) (tstep c s) hok.2 (fun x hx => ?_) j (by simp at hj; omega) ?_
      · have := hcol (x + 1) (by simp; omega)
        rw [show t0 + (x + 1) = t0 + 1 + x by omega] at this
        rw [this]
        rfl
      · rw [show t0 + 1 + j = t0 + (j + 1) by omega]; exact h0

/-- Without nine 1s in a row, the state is the run without resets. -/
theorem wstate_eq_wrun (col : Nat → Bool) (T1 L : Nat) (h : ∀ n, n < L → nine col (T1 + n + 1) = false) :
    ∀ n, n ≤ L → wstate col T1 n = wrun col T1 wall n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hn
    rw [wstate_succ, ite_eq_right (by rw [h n (by omega)]; decide), ih (by omega), wrun_succ']

/-- A 0 among the nine times before `t` rules out a reset at `t`. -/
theorem nine_false (col : Nat → Bool) (t x : Nat) (h9 : 9 ≤ t) (hx1 : t - 9 ≤ x) (hx2 : x < t)
    (h : col x = false) : nine col t = false := by
  cases hn : nine col t with
  | false => rfl
  | true =>
    have := (nine_spec col t).1 hn (x - (t - 9)) (by omega)
    rw [show t - 9 + (x - (t - 9)) = x by omega, h] at this
    exact absurd this (by decide)

theorem getD_rep_lt (b : Bool) (u : List Bool) :
    ∀ a i : Nat, i < a → (List.replicate a b ++ u).getD i false = b := by
  intro a
  induction a with
  | zero => intro i hi; omega
  | succ a ih =>
    intro i hi
    cases i with
    | zero => rfl
    | succ i => rw [List.replicate_succ, List.cons_append, List.getD_cons_succ]; exact ih i (by omega)

theorem getD_rep_add (b : Bool) (u : List Bool) : ∀ a x : Nat, (List.replicate a b ++ u).getD (a + x) false =
    u.getD x false := by
  intro a
  induction a with
  | zero => intro x; simp
  | succ a ih =>
    intro x
    rw [List.replicate_succ, List.cons_append, show a + 1 + x = (a + x) + 1 by omega, List.getD_cons_succ]
    exact ih x

theorem getD_app_left (l l' : List Bool) : ∀ n, n < l.length → (l ++ l').getD n false = l.getD n false := by
  induction l with
  | nil => intro n hn; simp at hn
  | cons c l ih =>
    intro n hn
    cases n with
    | zero => rfl
    | succ n => rw [List.cons_append, List.getD_cons_succ, List.getD_cons_succ]; exact ih n (by simp at hn; omega)

theorem getD_app_right (l l' : List Bool) : ∀ n, (l ++ l').getD (l.length + n) false = l'.getD n false := by
  induction l with
  | nil => intro n; simp
  | cons c l ih =>
    intro n
    rw [List.cons_append, List.length_cons, show l.length + 1 + n = (l.length + n) + 1 by omega,
      List.getD_cons_succ]
    exact ih n

/-- **A long run and one segment.** If a column repeats `1^a u` with `a ≥ 9`, where `u` starts with a 0, passes
`segOK` from the wall, and has a 0 at or just before each of its places from the ninth on, two adjacent columns are
eventually periodic, which `adjacent_columns` rules out. -/
theorem run_segment_column (init : Int → Bool) (m : Int) (hm : init m = true)
    (hz : ∀ x : Int, x < m → init x = false) (k : Int) (T a : Nat) (ha : 9 ≤ a) (u : List Bool)
    (hu0 : u.getD 0 true = false) (hok : segOK wall u = true)
    (hgap : ∀ n, 9 ≤ n → n < u.length → u.getD n false = false ∨ u.getD (n - 1) false = false)
    (hcol : ∀ t : Nat, T ≤ t → evolve init t k = cyc (List.replicate a true ++ u) (t - T)) : False := by
  have hlen : (List.replicate a true ++ u).length = a + u.length := by simp
  have hpos : 0 < u.length := by
    cases u with
    | nil => simp at hu0
    | cons c u => simp
  have hP : 0 < (List.replicate a true ++ u).length := by omega
  have hper : ∀ t : Nat, T ≤ t → evolve init (t + (List.replicate a true ++ u).length) k = evolve init t k := by
    intro t ht
    rw [hcol _ (by omega), hcol t ht, show t + (List.replicate a true ++ u).length - T =
      t - T + (List.replicate a true ++ u).length by omega, cyc_add]
  -- the column read from the end of the run in the second period
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
    · rcases hgap n (by omega) hn with h | h
      · exact nine_false _ _ (T + P + a + n) (by omega) (by omega) (by omega) (by rw [colU n hn]; exact h)
      · exact nine_false _ _ (T + P + a + (n - 1)) (by omega) (by omega) (by omega)
          (by rw [colU (n - 1) (by omega)]; exact h)
  have hperP : ∀ t : Nat, T ≤ t → evolve init (t + P) k = evolve init t k := by
    intro t ht
    show evolve init (t + (a + u.length)) k = _
    rw [← hlen]
    exact hper t ht
  refine wall_segments_column init m hm hz k T P (by omega) hperP (T + P + a) (by omega) ?_ ?_
  · intro i hi
    rw [show T + P + a - 9 + i = T + P + (a - 9 + i) by omega]
    exact colRun _ (by omega)
  · intro j hj h0
    by_cases hju : j < u.length
    · rw [wstate_eq_wrun _ (T + P + a) u.length hnr j (by omega)]
      intro hnone
      have := segOK_known (fun t => evolve init t k) u (T + P + a) wall hok (fun x hx => colU x hx) j hju h0
      rw [hnone] at this
      exact absurd this (by decide)
    · -- in the next run
      have := colAt (a + j - P) (by omega)
      rw [show T + P + (a + j - P) = T + P + a + j - P by omega, getD_rep_lt true u a _ (by omega)] at this
      have hper' := hper (T + P + a + j - P) (by omega)
      rw [show T + P + a + j - P + (List.replicate a true ++ u).length = T + P + a + j by simp [P]; omega,
        this] at hper'
      rw [hper'] at h0
      exact absurd h0 (by decide)

/-- From the latch, a 0 keeps the cell right of the column at 1. -/
theorem segOK_zeros (y : Tri) : ∀ z : Nat, ∀ tl : List Bool, (∀ y', segOK (some true, y') tl = true) →
    segOK (some true, y) (List.replicate z false ++ tl) = true := by
  intro z
  induction z generalizing y with
  | zero => intro tl h; exact h y
  | succ z ih =>
    intro tl h
    rw [List.replicate_succ, List.cons_append]
    simp only [segOK, Bool.false_or, Option.isSome_some, Bool.true_and]
    have : tstep false (some true, y) = (some true, (tstep false (some true, y)).2) := by
      cases y with
      | none => rfl
      | some b => cases b <;> rfl
    rw [this]
    exact ih _ tl h

theorem segOK_latch_end (y : Tri) : segOK (some true, y) [] = true ∧ segOK (some true, y) [true, false] = true := by
  constructor
  · rfl
  · cases y with
    | none => rfl
    | some b => cases b <;> rfl

/-- **The families.** For `a ≥ 9` and `z ≥ 0`, no column of a row with a leftmost 1 repeats `1^a h 0^z t` with the
head `h` one of `0` and `0 1 1` and the tail `t` one of the empty word and `1 0`. -/
theorem run_family_column (init : Int → Bool) (m : Int) (hm : init m = true)
    (hz : ∀ x : Int, x < m → init x = false) (k : Int) (T a z : Nat) (ha : 9 ≤ a) (h tl : List Bool)
    (hh : h = [false] ∨ h = [false, true, true]) (htl : tl = [] ∨ tl = [true, false])
    (hcol : ∀ t : Nat, T ≤ t →
      evolve init t k = cyc (List.replicate a true ++ (h ++ (List.replicate z false ++ tl))) (t - T)) : False := by
  refine run_segment_column init m hm hz k T a ha (h ++ (List.replicate z false ++ tl)) ?_ ?_ ?_ hcol
  · rcases hh with rfl | rfl <;> rfl
  · rw [segOK_append]
    have htl' : ∀ y', segOK (some true, y') tl = true := by
      intro y'; rcases htl with rfl | rfl
      · exact (segOK_latch_end y').1
      · exact (segOK_latch_end y').2
    rcases hh with rfl | rfl
    · show (segOK wall [false] && segOK (some true, some true) (List.replicate z false ++ tl)) = true
      rw [segOK_zeros _ z tl htl']; rfl
    · show (segOK wall [false, true, true] && segOK (some true, none) (List.replicate z false ++ tl)) = true
      rw [segOK_zeros _ z tl htl']; rfl
  · intro n hn9 hnl
    have hhl : h.length ≤ 3 := by rcases hh with rfl | rfl <;> simp
    rw [List.length_append, List.length_append, List.length_replicate] at hnl
    have htll : tl.length ≤ 2 := by rcases htl with rfl | rfl <;> simp
    by_cases hm1 : n < h.length + z
    · left
      rw [show n = h.length + (n - h.length) by omega, getD_app_right,
        getD_app_left _ _ _ (by rw [List.length_replicate]; omega)]
      have := getD_rep_lt false [] z (n - h.length) (by omega)
      rwa [List.append_nil] at this
    · by_cases hm2 : n = h.length + z
      · right
        rw [show n - 1 = h.length + (n - 1 - h.length) by omega, getD_app_right,
          getD_app_left _ _ _ (by rw [List.length_replicate]; omega)]
        have : (List.replicate z false).getD (n - 1 - h.length) false = false := by
          have := getD_rep_lt false [] z (n - 1 - h.length) (by omega)
          rwa [List.append_nil] at this
        exact this
      · left
        rcases htl with rfl | rfl
        · simp at hnl; omega
        · rw [show n = h.length + (z + 1) by simp at hnl; omega, getD_app_right,
            show z + 1 = (List.replicate z false).length + 1 by simp, getD_app_right]
          rfl

/-- **The center column**: for `a ≥ 9` and `z ≥ 0`, it does not repeat `1^a h 0^z t` from any time on, with `h` one
of `0` and `0 1 1` and `t` one of the empty word and `1 0`. -/
theorem center_run_family (T a z : Nat) (ha : 9 ≤ a) (h tl : List Bool)
    (hh : h = [false] ∨ h = [false, true, true]) (htl : tl = [] ∨ tl = [true, false])
    (hcol : ∀ t : Nat, T ≤ t →
      Rule30Prize.center t = cyc (List.replicate a true ++ (h ++ (List.replicate z false ++ tl))) (t - T)) :
    False := by
  simp only [← evolve_single_center] at hcol
  exact run_family_column single 0 rfl (fun x hx => decide_eq_false (by omega)) 0 T a z ha h tl hh htl hcol

/-- **The center column and one segment**: for `a ≥ 9`, it does not repeat `1^a u` from any time on, for any `u` that
starts with a 0, passes `segOK` from the wall, and has a 0 at or just before each of its places from the ninth on. -/
theorem center_run_segment (T a : Nat) (ha : 9 ≤ a) (u : List Bool) (hu0 : u.getD 0 true = false)
    (hok : segOK wall u = true)
    (hgap : ∀ n, 9 ≤ n → n < u.length → u.getD n false = false ∨ u.getD (n - 1) false = false)
    (hcol : ∀ t : Nat, T ≤ t → Rule30Prize.center t = cyc (List.replicate a true ++ u) (t - T)) : False := by
  simp only [← evolve_single_center] at hcol
  exact run_segment_column single 0 rfl (fun x hx => decide_eq_false (by omega)) 0 T a ha u hu0 hok hgap hcol

/-! ### Spot checks -/

/-- The eight tails of the kit's Theorem B′ (`Rule30BlackRunBlocks`), which it proves after `18` or `27` 1s, pass
`segOK` from the wall, so `center_run_segment` excludes them after nine. -/
theorem segOK_kit_tails :
    ([[false], [false, false], [false, false, false], [false, false, false, false], [false, true, false, false],
      [false, true, false], [false, false, true, false], [false, true, true, false]] : List (List Bool)).all
      (segOK wall) = true := by
  decide

/-- A block with two long runs and two segments, `1^9 0 1 0 1^9 0 1 1 0 0`, passes `wallGood`. -/
theorem wallGood_two_runs : wallGood ((List.replicate 9 true ++ [false, true, false]) ++
    (List.replicate 9 true ++ [false, true, true, false, false])) = true := by
  decide

end Rule30Open
