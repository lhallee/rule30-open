module

public import Rule30Open.Foundations.Evolve
public import Rule30Open.Foundations.Official

/-!
# No two adjacent columns are eventually periodic, so no column is eventually constant

Rule 30 is left-permutive: a cell follows from the cell to its right one step later and the two cells
to its right now (`left_cell`). So two adjacent columns that repeat with period `P` from time `T` make
every column to their left repeat too (`periodic_left`). The leftmost 1 of a row that is 0 left of some
cell moves one cell left each step (`left_edge`), so far enough left a column is 0 at time `T` and 1 when
the edge arrives a multiple of `P` later: no two adjacent columns are both eventually periodic
(`adjacent_columns`, the adjacent form of Jen's theorem; Kopra 2023, Theorem 3.5, credits it to Jen
1990, Proposition 3).

A column that is eventually constant always has an eventually constant neighbor, since 1s force 0s in
the column to their left, and 0s make the column to their right an OR latch, which switches on at most
once. So no column is eventually constant (`no_constant_column`); for the center column this excludes
period 1 of Prize Problem 1 (`center_not_eventually_constant`). The kit proves the same for the single
seed (`Rule30Prize.center_not_eventually_constant`); this proof is independent and covers every row
with a leftmost 1.

The natural-language argument is `AdjacentColumns.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

open Ruliology.CellularAutomata

/-- Two adjacent columns periodic from time `T` with period `P` make every column to their left periodic too: the
columns `k - n` and `k - n + 1`, for every `n`. -/
theorem periodic_left (init : Int → Bool) (k : Int) (T P : Nat)
    (h0 : ∀ t : Nat, T ≤ t → evolve init (t + P) k = evolve init t k)
    (h1 : ∀ t : Nat, T ≤ t → evolve init (t + P) (k + 1) = evolve init t (k + 1)) (n : Nat) :
    (∀ t : Nat, T ≤ t → evolve init (t + P) (k - n) = evolve init t (k - n)) ∧
      ∀ t : Nat, T ≤ t → evolve init (t + P) (k - n + 1) = evolve init t (k - n + 1) := by
  induction n with
  | zero =>
    rw [show k - ((0 : Nat) : Int) = k by omega]
    exact ⟨h0, h1⟩
  | succ n ih =>
    refine ⟨fun t ht => ?_, fun t ht => ?_⟩
    · rw [show k - ((n + 1 : Nat) : Int) = k - n - 1 by omega, left_cell init (t + P) (k - n),
        left_cell init t (k - n), show t + P + 1 = t + 1 + P by omega, ih.1 (t + 1) (by omega), ih.1 t ht, ih.2 t ht]
    · rw [show k - ((n + 1 : Nat) : Int) + 1 = k - n by omega]
      exact ih.1 t ht

/-- A column periodic from `T` with period `P` has its value at `T` again after any number of periods. -/
theorem periodic_iterate (f : Nat → Bool) (T P : Nat) (h : ∀ t : Nat, T ≤ t → f (t + P) = f t) (q : Nat) :
    f (T + q * P) = f T := by
  induction q with
  | zero => rw [Nat.zero_mul, Nat.add_zero]
  | succ q ih => rw [show T + (q + 1) * P = T + q * P + P by rw [Nat.add_mul, Nat.one_mul]; omega,
      h (T + q * P) (by omega), ih]

/-- Jen's theorem, adjacent form: in the orbit of a row with a leftmost 1, no two adjacent columns are both eventually
periodic. -/
theorem adjacent_columns (init : Int → Bool) (m : Int) (hm : init m = true) (hz : ∀ x : Int, x < m → init x = false)
    (k : Int) (T P : Nat) (hP : 0 < P)
    (h0 : ∀ t : Nat, T ≤ t → evolve init (t + P) k = evolve init t k)
    (h1 : ∀ t : Nat, T ≤ t → evolve init (t + P) (k + 1) = evolve init t (k + 1)) : False := by
  -- after s = q P steps, with q periods enough, the edge reaches a column at or left of k that was 0 at time T
  have back : ∀ n q : Nat, evolve init (T + q * P) (k - n) = evolve init T (k - n) := fun n q =>
    periodic_iterate (fun t => evolve init t (k - n)) T P (periodic_left init k T P h0 h1 n).1 q
  have key := back (k - m + T + ((((m - T - k).toNat + 1) * P : Nat) : Int)).toNat ((m - T - k).toNat + 1)
  have hs := Nat.le_mul_of_pos_right ((m - T - k).toNat + 1) hP
  generalize ((m - T - k).toNat + 1) * P = s at key hs
  rw [show k - (((k - m + T + s : Int).toNat : Nat) : Int) = m - ((T + s : Nat) : Int) by omega] at key
  have edge := (left_edge init m hm hz (T + s)).1
  rw [key, (left_edge init m hm hz T).2 (m - ((T + s : Nat) : Int)) (by omega)] at edge
  exact Bool.false_ne_true edge

/-- No column of the orbit of a row with a leftmost 1 is eventually constant. From `T` on, 1s at `k` force 0s at
`k - 1`, and 0s at `k` make `k + 1` an OR latch, constant once it switches on; either way two adjacent columns are
eventually constant, which `adjacent_columns` rules out. -/
theorem no_constant_column (init : Int → Bool) (m : Int) (hm : init m = true)
    (hz : ∀ x : Int, x < m → init x = false) (k : Int) (T : Nat) (b : Bool)
    (h : ∀ t : Nat, T ≤ t → evolve init t k = b) : False := by
  cases b with
  | true =>
    have off : ∀ t : Nat, T ≤ t → evolve init t (k - 1) = false := by
      intro t ht
      rw [left_cell init t k, h (t + 1) (by omega), h t ht]
      rfl
    exact adjacent_columns init m hm hz (k - 1) T 1 (by decide)
      (fun t ht => by rw [off (t + 1) (by omega), off t ht])
      (fun t ht => by rw [show k - 1 + 1 = k by omega, h (t + 1) (by omega), h t ht])
  | false =>
    have latch : ∀ t : Nat, T ≤ t → evolve init t (k + 1) = true → evolve init (t + 1) (k + 1) = true := by
      intro t ht hon
      show rule30 (evolve init t (k + 1 - 1)) (evolve init t (k + 1)) (evolve init t (k + 1 + 1)) = true
      rw [show k + 1 - 1 = k by omega, h t ht, hon]
      rfl
    by_cases hon : ∃ t0 : Nat, T ≤ t0 ∧ evolve init t0 (k + 1) = true
    · obtain ⟨t0, ht0, hon⟩ := hon
      have from_t0 : ∀ d : Nat, evolve init (t0 + d) (k + 1) = true := by
        intro d
        induction d with
        | zero => exact hon
        | succ d ih => exact latch (t0 + d) (by omega) ih
      have stays : ∀ t : Nat, t0 ≤ t → evolve init t (k + 1) = true := fun t ht => by
        have := from_t0 (t - t0)
        rwa [show t0 + (t - t0) = t by omega] at this
      exact adjacent_columns init m hm hz k t0 1 (by decide)
        (fun t ht => by rw [h (t + 1) (by omega), h t (by omega)])
        (fun t ht => by rw [stays (t + 1) (by omega), stays t ht])
    · have never : ∀ t : Nat, T ≤ t → evolve init t (k + 1) = false := by
        intro t ht
        cases h' : evolve init t (k + 1) with
        | false => rfl
        | true => exact absurd ⟨t, ht, h'⟩ hon
      exact adjacent_columns init m hm hz k T 1 (by decide)
        (fun t ht => by rw [h (t + 1) (by omega), h t ht])
        (fun t ht => by rw [never (t + 1) (by omega), never t ht])

/-- The single seed's center column is not eventually constant, nor is any other column of its orbit. -/
theorem single_not_constant (k : Int) (T : Nat) (b : Bool) (h : ∀ t : Nat, T ≤ t → evolve single t k = b) : False :=
  no_constant_column single 0 rfl (fun x hx => decide_eq_false (by omega)) k T b h

/-- Official form, period 1 of Prize Problem 1: the center column is not eventually constant. -/
theorem center_not_eventually_constant : ¬ ∃ T b, ∀ t, T ≤ t → Rule30Prize.center t = b :=
  fun ⟨T, b, h⟩ => single_not_constant 0 T b fun t ht => (evolve_single_center t).trans (h t ht)

end Rule30Open
