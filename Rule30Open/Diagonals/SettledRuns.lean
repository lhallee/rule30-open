module

public import Rule30Open.Diagonals.LeftMemory
public import Ruliology.CellularAutomata.Rule30CenterRuns

/-!
# Settled left diagonals bound the black runs of the center column

Read the single seed's pattern along the left diagonals, `D j t = cell t (j - t)`. Two facts about adjacent diagonals
drive this module.

* Two adjacent diagonals cannot alternate in antiphase from some time on (`no_alt_pair`): the diagonal two before is
  then determined by the rule (`D_step`) and alternates in antiphase with its neighbour, down to the diagonals 0 and 1,
  and `D 0` is always black.
* A periodic sequence that alternates over one period alternates forever (`alt_forever`).

A black run of the center column from time `a`, of length `L`, makes the cells of the row `a - s` read alternately
black and white on a trapezoid (`black_block_back`): the cell `-m` is black exactly for even `m`, from `m = 4 s` out
to `m = L - 1 + s`. It is the kit's erosion by four cells a step, here proved for the alternating pattern directly.
Diagonals meet that trapezoid in windows of times (`black_diag`). If two adjacent diagonals `j` and `j + 1` repeat
with period `16` over the whole window and the window is 17 times long, they alternate in antiphase forever, which
`no_alt_pair` forbids.

The hypothesis that the left diagonals settle linearly to depth `J` (`hS`: every diagonal `8 <= j <= J` repeats with
period 16 from time `3j/2` on) is not proved: the kit proves a settling time `2^j` for diagonal `j`, and computation
for `j < 8000` gives period 16 from time `3j/2` on, with onset at most `1.48 j` to depth 1500
(`findings/diagonals/settled-runs.md`). It is false for `J >= 87867`, where the period becomes 32. Under it, a black run from time `a` has length at most `3a/13 + 185`
(`black_run_le_of_settled`), against the kit's `3a/5` without it, and a white block of the row `a` that extends `m`
cells left of the center has `3 m <= a + 100` (`white_block_le_of_settled`). This module proves those implications
in Lean.

The natural-language argument is `SettledRuns.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

open Ruliology.CellularAutomata
open Ruliology.CellularAutomata.Rule30Diagonals
open Ruliology.CellularAutomata.Rule30CenterRuns
open Rule30Jen Rule30Prize

/-- A sequence that repeats with period `P` from `T` and alternates over `P` steps from `T' >= T` alternates forever. -/
theorem alt_forever (f : Nat → Bool) (T P T' : Nat) (hT : T ≤ T') (hP : 0 < P)
    (hper : ∀ t, T ≤ t → f (t + P) = f t) (hwin : ∀ k, k < P → f (T' + k + 1) = !f (T' + k)) :
    ∀ n, f (T' + n + 1) = !f (T' + n) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases hn : n < P
    · exact hwin n hn
    · have h1 := ih (n - P) (by omega)
      have e1 : f (T' + n + 1) = f (T' + (n - P) + 1) := by
        rw [show T' + n + 1 = T' + (n - P) + 1 + P by omega]
        exact hper _ (by omega)
      have e2 : f (T' + n) = f (T' + (n - P)) := by
        rw [show T' + n = T' + (n - P) + P by omega]
        exact hper _ (by omega)
      rw [e1, e2, h1]

/-- Adjacent diagonals alternating in antiphase from a time on. -/
def AltPair (j T : Nat) : Prop :=
  ∀ t, T ≤ t → D (j + 1) t = !D j t ∧ D j (t + 1) = !D j t

/-- The antiphase alternation of diagonals `j + 1`, `j + 2` passes to diagonals `j`, `j + 1`. -/
theorem altPair_down (j T : Nat) (h : AltPair (j + 1) T) : AltPair j T := by
  have key : ∀ t, T ≤ t → D (j + 1) t = !D j t := by
    intro t ht
    have a1 := h t ht
    have a2 := h (t + 1) (by omega)
    have st := D_step j t
    rw [a2.1, a1.2, a1.1] at st
    revert st
    generalize D j t = x
    generalize D (j + 1) t = y
    cases x <;> cases y <;> simp
  intro t ht
  refine ⟨key t ht, ?_⟩
  have e1 := key (t + 1) (by omega)
  have e2 := (h t ht).2
  have e3 := key t ht
  rw [e2, e3] at e1
  revert e1
  generalize D j (t + 1) = x
  generalize D j t = y
  cases x <;> cases y <;> simp

/-- Adjacent diagonals never alternate in antiphase from a time on: the alternation reaches `D 0`, which is black. -/
theorem no_alt_pair : ∀ j T, ¬ AltPair j T
  | 0, T => fun h => by
    have := (h (T + 1) (by omega)).1
    rw [D_zero, D_one T] at this
    exact Bool.noConfusion this
  | j + 1, T => fun h => no_alt_pair j T (altPair_down j T h)

/-- Periodic diagonals that alternate in antiphase over one period alternate in antiphase forever. -/
theorem settled_alt_pair (j T P T' : Nat) (hT : T ≤ T') (hP : 0 < P)
    (hj : ∀ t, T ≤ t → D j (t + P) = D j t) (hj1 : ∀ t, T ≤ t → D (j + 1) (t + P) = D (j + 1) t)
    (hanti : ∀ k, k ≤ P → D (j + 1) (T' + k) = !D j (T' + k))
    (halt : ∀ k, k < P → D j (T' + k + 1) = !D j (T' + k)) : False := by
  have alt := alt_forever (D j) T P T' hT hP hj halt
  have anti : ∀ n, D (j + 1) (T' + n) = !D j (T' + n) := by
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
      by_cases hn : n < P
      · exact hanti n (by omega)
      · have h1 := ih (n - P) (by omega)
        rw [show T' + n = T' + (n - P) + P by omega, hj1 _ (by omega), hj _ (by omega)]
        exact h1
  refine no_alt_pair j T' (fun t ht => ?_)
  obtain ⟨n, rfl⟩ : ∃ n, t = T' + n := ⟨t - T', by omega⟩
  exact ⟨anti n, alt n⟩

/-- Adjacent diagonals never both stay white from a time on. -/
theorem no_white_pair : ∀ j T, ¬ ((∀ t, T ≤ t → D j t = false) ∧ (∀ t, T ≤ t → D (j + 1) t = false))
  | 0, T => fun h => by
    have := h.1 T (Nat.le_refl T)
    rw [D_zero] at this
    exact Bool.noConfusion this
  | j + 1, T => fun h => no_white_pair j T ⟨fun t ht => by
      have st := D_step j t
      have e2 : D (j + 2) (t + 1) = false := h.2 (t + 1) (by omega)
      have e3 : D (j + 2) t = false := h.2 t ht
      rw [e2, h.1 t ht, e3] at st
      revert st
      cases D j t <;> simp, h.1⟩


/-- Periodic sequences that are white over one period are white forever. -/
theorem white_forever (f : Nat → Bool) (T P T' : Nat) (hT : T ≤ T') (hP : 0 < P)
    (hper : ∀ t, T ≤ t → f (t + P) = f t) (hwin : ∀ k, k < P → f (T' + k) = false) :
    ∀ n, f (T' + n) = false := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases hn : n < P
    · exact hwin n hn
    · have h1 := ih (n - P) (by omega)
      rw [show T' + n = T' + (n - P) + P by omega, hper _ (by omega), h1]

/-! ### The trapezoid behind a black run -/

/-- The alternating pattern: black on even cells. -/
def altPat (i : Int) : Bool := decide (i % 2 = 0)

theorem altPat_pred (i : Int) : altPat (i - 1) = !altPat i := by
  unfold altPat
  by_cases h : i % 2 = 0
  · rw [decide_eq_true h, decide_eq_false (by omega)]; rfl
  · rw [decide_eq_false h, decide_eq_true (by omega)]; rfl

theorem altPat_succ (i : Int) : altPat (i + 1) = !altPat i := by
  have := altPat_pred (i + 1)
  rw [show i + 1 - 1 = i by omega] at this
  rw [this]; cases altPat (i + 1) <;> rfl

theorem altPat_neg (k : Nat) : altPat (-(k : Int)) = ev k := by
  unfold altPat ev
  by_cases h : k % 2 = 0
  · rw [decide_eq_true h, decide_eq_true (by omega)]
  · rw [decide_eq_false h, decide_eq_false (by omega)]

/-- If row `t + 1` reads the alternating pattern on `lo .. hi`, then row `t` does on `lo - 1 .. hi - 4`, whatever
the cells of row `t` to the right are. -/
theorem erode_alt (t : Nat) (lo hi : Int) (h : ∀ i, lo ≤ i → i ≤ hi → cell (t + 1) i = altPat i) :
    ∀ i, lo - 1 ≤ i → i ≤ hi - 4 → cell t i = altPat i := by
  intro i hi1 hi2
  have step : ∀ i, lo ≤ i → i ≤ hi → cell t (i - 1) = xor (altPat i) (cell t i || cell t (i + 1)) := by
    intro i h1 h2
    have := cell_left t i
    rwa [h i h1 h2] at this
  have p1 : altPat (hi - 1) = !altPat hi := altPat_pred hi
  have p2 : altPat (hi - 2) = altPat hi := by
    have := altPat_pred (hi - 1)
    rw [show hi - 1 - 1 = hi - 2 by omega, p1] at this
    rw [this]; cases altPat hi <;> rfl
  have p3 : altPat (hi - 3) = !altPat hi := by
    have := altPat_pred (hi - 2)
    rw [show hi - 2 - 1 = hi - 3 by omega, p2] at this
    exact this
  have p4 : altPat (hi - 4) = altPat hi := by
    have := altPat_pred (hi - 3)
    rw [show hi - 3 - 1 = hi - 4 by omega, p3] at this
    rw [this]; cases altPat hi <;> rfl
  have p5 : altPat (hi - 5) = !altPat hi := by
    have := altPat_pred (hi - 4)
    rw [show hi - 4 - 1 = hi - 5 by omega, p4] at this
    exact this
  have q0 : cell t (hi - 1) = xor (altPat hi) (cell t hi || cell t (hi + 1)) := step hi (by omega) (Int.le_refl _)
  have q1 : cell t (hi - 2) = xor (altPat (hi - 1)) (cell t (hi - 1) || cell t hi) := by
    have := step (hi - 1) (by omega) (by omega)
    rwa [show hi - 1 - 1 = hi - 2 by omega, show hi - 1 + 1 = hi by omega] at this
  have q2 : cell t (hi - 3) = xor (altPat (hi - 2)) (cell t (hi - 2) || cell t (hi - 1)) := by
    have := step (hi - 2) (by omega) (by omega)
    rwa [show hi - 2 - 1 = hi - 3 by omega, show hi - 2 + 1 = hi - 1 by omega] at this
  have q3 : cell t (hi - 4) = xor (altPat (hi - 3)) (cell t (hi - 3) || cell t (hi - 2)) := by
    have := step (hi - 3) (by omega) (by omega)
    rwa [show hi - 3 - 1 = hi - 4 by omega, show hi - 3 + 1 = hi - 2 by omega] at this
  have b4 : cell t (hi - 4) = altPat (hi - 4) := by
    rw [q3, q2, q1, q0, p1, p2, p3, p4]
    generalize altPat hi = A
    generalize cell t hi = u
    generalize cell t (hi + 1) = v
    cases A <;> cases u <;> cases v <;> rfl
  by_cases e4 : i = hi - 4
  · rw [e4]; exact b4
  have q4 : cell t (hi - 5) = xor (altPat (hi - 4)) (cell t (hi - 4) || cell t (hi - 3)) := by
    have := step (hi - 4) (by omega) (by omega)
    rwa [show hi - 4 - 1 = hi - 5 by omega, show hi - 4 + 1 = hi - 3 by omega] at this
  have b5 : cell t (hi - 5) = altPat (hi - 5) := by
    rw [q4, b4, q2, q1, q0, p5, p1, p2, p4]
    generalize altPat hi = A
    generalize cell t hi = u
    generalize cell t (hi + 1) = v
    cases A <;> cases u <;> cases v <;> rfl
  have pair : ∀ n : Nat, hi - 5 - (n : Int) ≥ lo - 1 →
      cell t (hi - 5 - (n : Int)) = altPat (hi - 5 - (n : Int)) ∧
        cell t (hi - 4 - (n : Int)) = altPat (hi - 4 - (n : Int)) := by
    intro n
    induction n with
    | zero =>
      intro _
      rw [show hi - 5 - ((0 : Nat) : Int) = hi - 5 by omega, show hi - 4 - ((0 : Nat) : Int) = hi - 4 by omega]
      exact ⟨b5, b4⟩
    | succ n ih =>
      intro hn
      have ih2 := ih (by omega)
      have st := step (hi - 5 - (n : Int)) (by omega) (by omega)
      rw [ih2.1, show hi - 5 - (n : Int) + 1 = hi - 4 - (n : Int) by omega, ih2.2] at st
      have c1 : hi - 5 - ((n + 1 : Nat) : Int) = hi - 5 - (n : Int) - 1 := by omega
      have c2 : hi - 4 - ((n + 1 : Nat) : Int) = hi - 5 - (n : Int) := by omega
      refine ⟨?_, ?_⟩
      · rw [c1, st, altPat_pred]
        rw [show hi - 4 - (n : Int) = hi - 5 - (n : Int) + 1 by omega, altPat_succ]
        cases altPat (hi - 5 - (n : Int)) <;> rfl
      · rw [c2]; exact ih2.1
  have := (pair (hi - 5 - i).toNat (by omega)).1
  rwa [show hi - 5 - ((hi - 5 - i).toNat : Int) = i by omega] at this

/-- Under a black run of the center from time `a` of length `L`, row `a - s` reads the alternating pattern on the
cells `-(L - 1) - s .. -4 s`. -/
theorem black_block_back (a L : Nat) (h : ∀ i, i < L → cell (a + i) 0 = true) :
    ∀ s, s ≤ a → ∀ i : Int, -((L : Int) - 1) - s ≤ i → i ≤ -4 * (s : Int) → cell (a - s) i = altPat i := by
  intro s
  induction s with
  | zero =>
    intro _ i hi1 hi2
    have := black_triangle a L h (-i).toNat a (Nat.le_refl a) (by omega)
    rw [show (a - 0) = a by omega, show i = -(((-i).toNat : Nat) : Int) by omega, this, altPat_neg]
  | succ s ih =>
    intro hs i hi1 hi2
    have ih2 := ih (by omega)
    exact erode_alt (a - (s + 1)) (-((L : Int) - 1) - s) (-4 * (s : Int))
      (fun j hj1 hj2 => by
        rw [show a - (s + 1) + 1 = a - s by omega]; exact ih2 j hj1 hj2) i (by omega) (by omega)

/-- A diagonal inside the trapezoid reads the alternating pattern. -/
theorem black_diag (a L : Nat) (h : ∀ i, i < L → cell (a + i) 0 = true) (j s : Nat) (hs : s ≤ a)
    (h1 : a + 1 ≤ 2 * s + j + L) (h2 : 5 * s + j ≤ a) :
    D j (a - s) = altPat ((j : Int) - ((a - s : Nat) : Int)) := by
  unfold D
  exact black_block_back a L h s hs _ (by omega) (by omega)

/-- **A black run from time `a` has length at most `3a/13 + 185` if the left diagonals settle linearly.**
Here "settle" means: every diagonal `8 ≤ j ≤ J` repeats with period 16 from time `3j/2` on, and the run starts
at a time `a` with `8a/13 + 1 ≤ J`. -/
theorem black_run_le_of_settled
    (J : Nat) (hS : ∀ j t, 8 ≤ j → j ≤ J → 3 * j ≤ 2 * t → D j (t + 16) = D j t)
    (a L : Nat) (ha : 1 ≤ a) (hJ : 8 * a / 13 + 1 ≤ J) (h : ∀ i, i < L → center (a + i) = true) :
    13 * L ≤ 3 * a + 2400 := by
  refine Classical.byContradiction fun hcon => ?_
  have h2 : ∀ i, i < L → cell (a + i) 0 = true := h
  have hLa : L ≤ a := black_run_le a L ha h
  obtain ⟨j, hj⟩ : ∃ j, j = 8 * a / 13 := ⟨_, rfl⟩
  obtain ⟨s0, hs0⟩ : ∃ s0, s0 = (a + 2 - j - L) / 2 := ⟨_, rfl⟩
  have r1 : a + 1 ≤ 2 * s0 + j + L := by omega
  have r2 : 5 * (s0 + 16) + j + 1 ≤ a := by omega
  have r3 : 3 * (j + 1) ≤ 2 * (a - s0 - 16) := by omega
  have r4 : 8 ≤ j := by omega
  have key : ∀ s, s0 ≤ s → s ≤ s0 + 16 →
      D j (a - s) = altPat ((j : Int) - ((a - s : Nat) : Int)) ∧
      D (j + 1) (a - s) = altPat (((j + 1 : Nat) : Int) - ((a - s : Nat) : Int)) := by
    intro s hs1 hs2
    exact ⟨black_diag a L h2 j s (by omega) (by omega) (by omega),
      black_diag a L h2 (j + 1) s (by omega) (by omega) (by omega)⟩
  refine settled_alt_pair j ((3 * (j + 1) + 1) / 2) 16 (a - s0 - 16) (by omega) (by omega)
    (fun t ht => hS j t r4 (by omega) (by omega)) (fun t ht => hS (j + 1) t (by omega) (by omega) (by omega)) ?_ ?_
  · intro k hk
    have e := key (s0 + 16 - k) (by omega) (by omega)
    rw [show a - s0 - 16 + k = a - (s0 + 16 - k) by omega, e.1, e.2]
    rw [show ((j + 1 : Nat) : Int) = (j : Int) + 1 by omega]
    have := altPat_succ ((j : Int) - ((a - (s0 + 16 - k) : Nat) : Int))
    rw [show (j : Int) + 1 - ((a - (s0 + 16 - k) : Nat) : Int) = (j : Int) - ((a - (s0 + 16 - k) : Nat) : Int) + 1 by omega]
    exact this
  · intro k hk
    have e := key (s0 + 16 - k) (by omega) (by omega)
    have e2 := key (s0 + 16 - k - 1) (by omega) (by omega)
    rw [show a - s0 - 16 + k + 1 = a - (s0 + 16 - k - 1) by omega,
      show a - s0 - 16 + k = a - (s0 + 16 - k) by omega, e.1, e2.1]
    rw [show ((a - (s0 + 16 - k - 1) : Nat) : Int) = ((a - (s0 + 16 - k) : Nat) : Int) + 1 by omega,
      show (j : Int) - (((a - (s0 + 16 - k) : Nat) : Int) + 1) =
        ((j : Int) - ((a - (s0 + 16 - k) : Nat) : Int)) - 1 by omega, altPat_pred]

/-! ### White blocks -/

/-- Under white cells `-m .. l` of row `a`, the triangle below them is white. -/
theorem white_triangle (a m l : Nat) (hw : ∀ x : Int, -(m : Int) ≤ x → x ≤ l → cell a x = false) :
    ∀ i : Nat, ∀ x : Int, -(m : Int) + i ≤ x → x ≤ (l : Int) - i → cell (a + i) x = false
  | 0, x, h1, h2 => by
    have := hw x (by omega) (by omega)
    simpa using this
  | i + 1, x, h1, h2 => by
    show cell (a + i + 1) x = false
    rw [cell_succ' (a + i) x (x - 1) x (x + 1) rfl rfl rfl,
      white_triangle a m l hw i (x - 1) (by omega) (by omega),
      white_triangle a m l hw i x (by omega) (by omega),
      white_triangle a m l hw i (x + 1) (by omega) (by omega)]
    rfl

/-- **A white block of row `a` has left half-width at most `a/3 + 33` if the left diagonals settle linearly.**
Row `a` white on the cells `-m .. l` leaves a white triangle below it, which two adjacent diagonals read as white
for 16 steps; settled, they stay white forever, which `no_white_pair` forbids. -/
theorem white_block_le_of_settled
    (J : Nat) (hS : ∀ j t, 8 ≤ j → j ≤ J → 3 * j ≤ 2 * t → D j (t + 16) = D j t)
    (a m l : Nat) (ha : 14 ≤ a) (hJ : 2 * a / 3 ≤ J) (hw : ∀ x : Int, -(m : Int) ≤ x → x ≤ l → cell a x = false) :
    3 * m ≤ a + 100 := by
  refine Classical.byContradiction fun hcon => ?_
  obtain ⟨j, hj⟩ : ∃ j, j = 2 * a / 3 - 1 := ⟨_, rfl⟩
  have r4 : 8 ≤ j := by omega
  have tri := white_triangle a m l hw
  have win : ∀ k, k < 16 → D j (a + k) = false ∧ D (j + 1) (a + k) = false := by
    intro k hk
    exact ⟨tri k _ (by omega) (by omega), tri k _ (by omega) (by omega)⟩
  have f0 := white_forever (D j) ((3 * (j + 1) + 1) / 2) 16 a (by omega) (by omega)
    (fun t ht => hS j t r4 (by omega) (by omega)) (fun k hk => (win k hk).1)
  have f1 := white_forever (D (j + 1)) ((3 * (j + 1) + 1) / 2) 16 a (by omega) (by omega)
    (fun t ht => hS (j + 1) t (by omega) (by omega) (by omega)) (fun k hk => (win k hk).2)
  refine no_white_pair j a ⟨fun t ht => ?_, fun t ht => ?_⟩
  · have := f0 (t - a); rwa [show a + (t - a) = t by omega] at this
  · have := f1 (t - a); rwa [show a + (t - a) = t by omega] at this

end Rule30Open
