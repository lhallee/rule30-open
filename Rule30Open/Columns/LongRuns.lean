module

public import Rule30Open.Foundations.Evolve
public import Rule30Open.Foundations.Official
public import Rule30Open.Foundations.RightHalf
public import Rule30Open.Columns.AdjacentColumns

/-!
# Long runs of 1s exclude a periodic column

Nine 1s in a column force the two cells just right of it, whatever else the row holds: one step after the
ninth, the next two columns read 0 1 (`wall_forms`, checked over every right half in the light cone by
`wall_check`). So if every run of 1s in an eventually periodic column lasts at least 9 steps, then at the
first 0 after each run the column to its right is 0, with a 1 beside it, and at each later 0 of a run of 0s
it is 1, an OR latch there (`latch_after_runs`). The column to the left is then a function of the column
itself (`left_cell`), so two adjacent columns are eventually periodic, which `adjacent_columns` rules out
(`long_runs_column`). This excludes infinitely many repeating blocks of the center column, among them every block
0 1^k with k ≥ 9 (`center_long_runs`).

The kit's `Rule30BlackRuns` proves the same nine-black shield for the single seed; this proof is
independent and covers every row with a leftmost 1.

The natural-language argument is `LongRuns.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

open Ruliology.CellularAutomata

/-- Every right half of 11 cells, driven by nine 1s, ends with the cells 0 1. -/
theorem wall_check : (allLists 11).all (fun l => drive (List.replicate 9 true) l == [false, true]) = true := by
  decide +kernel

/-- Nine 1s in column `k`, from time `s`, leave columns `k + 1` and `k + 2` reading 0 1 at time `s + 9`. -/
theorem wall_forms (init : Int → Bool) (k : Int) (s : Nat) (h : ∀ i : Nat, i < 9 → evolve init (s + i) k = true) :
    evolve init (s + 9) (k + 1) = false ∧ evolve init (s + 9) (k + 2) = true := by
  have cells := drive_cells init (k + 1) 9 s 2
  rw [show k + 1 - 1 = k by omega, columnFrom_const init k true 9 s h] at cells
  have hall := List.all_eq_true.mp wall_check (cellsFrom init s (k + 1) (2 + 9))
    (by have := mem_allLists (cellsFrom init s (k + 1) (2 + 9)); rwa [length_cellsFrom] at this)
  rw [cells] at hall
  have heq := beq_iff_eq.mp hall
  have h1 : evolve init (s + 9) (k + 1) = false := by
    have := congrArg List.head? heq
    exact Option.some.inj this
  have h2 : evolve init (s + 9) (k + 1 + 1) = true := by
    have := congrArg (fun l => l.tail.head?) heq
    exact Option.some.inj this
  exact ⟨h1, by rw [show k + 2 = k + 1 + 1 by omega]; exact h2⟩

/-- Under long runs of 1s in column `k`, from `T0` on, column `k + 1` at each 0 of column `k` is the negation of
column `k` one step earlier: 0 right after a run of 1s, 1 later in a run of 0s. -/
theorem latch_after_runs (init : Int → Bool) (k : Int) (T0 : Nat) (h9 : 9 ≤ T0)
    (hstart : evolve init (T0 - 1) k = true)
    (hrun : ∀ t : Nat, T0 ≤ t → evolve init t k = false → evolve init (t - 1) k = true →
      ∀ i : Nat, i < 9 → evolve init (t - 9 + i) k = true) :
    ∀ n : Nat, evolve init (T0 + n) k = false →
      evolve init (T0 + n) (k + 1) = !evolve init (T0 + n - 1) k ∧
        (evolve init (T0 + n - 1) k = true → evolve init (T0 + n) (k + 2) = true) := by
  have first : ∀ t : Nat, T0 ≤ t → evolve init t k = false → evolve init (t - 1) k = true →
      evolve init t (k + 1) = false ∧ evolve init t (k + 2) = true := fun t ht h0 h1 => by
    have := wall_forms init k (t - 9) (hrun t ht h0 h1)
    rwa [show t - 9 + 9 = t by omega] at this
  intro n
  induction n with
  | zero =>
    intro h0
    rw [Nat.add_zero] at h0 ⊢
    have w := first T0 (Nat.le_refl _) h0 hstart
    rw [hstart, w.1, w.2]
    exact ⟨rfl, fun _ => rfl⟩
  | succ n ih =>
    intro h0
    rw [show T0 + (n + 1) - 1 = T0 + n by omega]
    cases hprev : evolve init (T0 + n) k with
    | true =>
      have w := first (T0 + (n + 1)) (by omega) h0 (by rw [show T0 + (n + 1) - 1 = T0 + n by omega]; exact hprev)
      rw [w.1, w.2]
      exact ⟨rfl, fun _ => rfl⟩
    | false =>
      refine ⟨?_, fun h => Bool.noConfusion h⟩
      have step : evolve init (T0 + (n + 1)) (k + 1) =
          (evolve init (T0 + n) (k + 1) || evolve init (T0 + n) (k + 2)) := by
        show rule30 (evolve init (T0 + n) (k + 1 - 1)) (evolve init (T0 + n) (k + 1)) (evolve init (T0 + n) (k + 1 + 1))
          = _
        rw [show k + 1 - 1 = k by omega, hprev, show k + 1 + 1 = k + 2 by omega]
        exact Bool.false_xor _
      rw [step]
      have prev := ih hprev
      cases hb : evolve init (T0 + n - 1) k with
      | true => rw [prev.2 hb, Bool.or_true]; rfl
      | false => rw [prev.1, hb]; rfl

/-- No column of the orbit of a row with a leftmost 1 is eventually periodic with every run of 1s that ends, from some
time on, lasting at least 9 steps. Take `T` at least 9: both hypotheses persist under a larger `T`, and below 9 the
time `t - 9` truncates. -/
theorem long_runs_column (init : Int → Bool) (m : Int) (hm : init m = true) (hz : ∀ x : Int, x < m → init x = false)
    (k : Int) (T P : Nat) (hP : 0 < P) (hper : ∀ t : Nat, T ≤ t → evolve init (t + P) k = evolve init t k)
    (hrun : ∀ t : Nat, T ≤ t → evolve init t k = false → evolve init (t - 1) k = true →
      ∀ i : Nat, i < 9 → evolve init (t - 9 + i) k = true) : False := by
  by_cases hone : ∃ T0 : Nat, T + 10 ≤ T0 ∧ evolve init (T0 - 1) k = true
  · obtain ⟨T0, hT0, hstart⟩ := hone
    have latch := latch_after_runs init k T0 (by omega) hstart (fun t ht => hrun t (by omega))
    -- column k - 1 is a function of column k from T0 on
    have left : ∀ t : Nat, T0 ≤ t → evolve init t (k - 1) =
        xor (evolve init (t + 1) k) (evolve init t k || !evolve init (t - 1) k) := by
      intro t ht
      rw [left_cell init t k]
      cases hc : evolve init t k with
      | true => rfl
      | false =>
        have := (latch (t - T0) (by rw [show T0 + (t - T0) = t by omega]; exact hc)).1
        rw [show T0 + (t - T0) = t by omega] at this
        rw [this]
    exact adjacent_columns init m hm hz (k - 1) T0 P hP
      (fun t ht => by
        rw [left (t + P) (by omega), left t ht, show t + P + 1 = t + 1 + P by omega, hper (t + 1) (by omega),
          hper t (by omega), show t + P - 1 = t - 1 + P by omega, hper (t - 1) (by omega)])
      (fun t ht => by rw [show k - 1 + 1 = k by omega]; exact hper t (by omega))
  · -- no 1 after T + 9: the column is eventually 0
    exact no_constant_column init m hm hz k (T + 9) false fun t ht => by
      cases h : evolve init t k with
      | false => rfl
      | true => exact absurd ⟨t + 1, by omega, by rw [show t + 1 - 1 = t by omega]; exact h⟩ hone

/-- No column of the single seed's orbit is eventually periodic with every run of 1s lasting at least 9 steps. -/
theorem single_long_runs (k : Int) (T P : Nat) (hP : 0 < P)
    (hper : ∀ t : Nat, T ≤ t → evolve single (t + P) k = evolve single t k)
    (hrun : ∀ t : Nat, T ≤ t → evolve single t k = false → evolve single (t - 1) k = true →
      ∀ i : Nat, i < 9 → evolve single (t - 9 + i) k = true) : False :=
  long_runs_column single 0 rfl (fun x hx => decide_eq_false (by omega)) k T P hP hper hrun

/-- Official form: the center column is not eventually periodic with every run of 1s lasting at least 9 steps. -/
theorem center_long_runs (T P : Nat) (hP : 0 < P)
    (hper : ∀ t : Nat, T ≤ t → Rule30Prize.center (t + P) = Rule30Prize.center t)
    (hrun : ∀ t : Nat, T ≤ t → Rule30Prize.center t = false → Rule30Prize.center (t - 1) = true →
      ∀ i : Nat, i < 9 → Rule30Prize.center (t - 9 + i) = true) : False := by
  simp only [← evolve_single_center] at hper hrun
  exact single_long_runs 0 T P hP hper hrun

end Rule30Open
