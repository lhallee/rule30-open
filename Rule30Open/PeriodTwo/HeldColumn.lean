module

public import Rule30Open.Foundations.Evolve
public import Rule30Open.Foundations.Official

/-!
# Period 2 comes down to an integer map

A column that alternates 0 1 0 1 from some time on reads 1 at every other step, and since
`rule30 l true r = !l` while the column reads 0 a step later, the cell left of it reads 1 at each of those
steps (`left_of_alternating`). The OR in that cell's next update is then 1 whether the column reads 1 or
0, so from then on the cells left of the column evolve exactly as Rule 30 with the column held at 0
(`held`), and the cell next to it reads 1 at every other step (`period_two_held`).

Read as the number with bit `j` for the cell `j + 1` places left of the column, `held` is the map
`U ↦ (U >>> 1) ^^^ (U ||| (U <<< 1))` (`heldNat_testBit`, and step by step along an orbit,
`heldNat_repeat`). So a row with a leftmost 1 and an eventually alternating column gives a positive
integer whose orbit under that map is odd at every odd step (`period_two_integer`). Showing that no such
integer exists would rule out period 2 of Prize Problem 1 (`center_period_two_integer`); that question is
open. The kit reaches the same question by another route (`Rule30PeriodTwo`, statement Q01, proved there
for every start of width at most 52).

The natural-language argument is `HeldColumn.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

open Ruliology.CellularAutomata

/-- Rule 30 left of a column held at 0; bit `j` is the cell `j + 1` places left of the column. -/
def held (u : Nat → Bool) : Nat → Bool
  | 0 => xor (u 1) (u 0)
  | j + 1 => xor (u (j + 2)) (u (j + 1) || u j)

/-- The orbit of `u` under `held`. -/
def heldOrbit (u : Nat → Bool) : Nat → Nat → Bool
  | 0 => u
  | n + 1 => held (heldOrbit u n)

/-- `held` on numbers: bit `j` of `U` is the cell `j + 1` places left of the column. -/
def heldNat (U : Nat) : Nat := (U >>> 1) ^^^ (U ||| (U <<< 1))

theorem heldNat_testBit (U j : Nat) : (heldNat U).testBit j = held (fun i => U.testBit i) j := by
  unfold heldNat
  rw [Nat.testBit_xor, Nat.testBit_or, Nat.testBit_shiftRight, Nat.testBit_shiftLeft]
  cases j with
  | zero => simp [held]
  | succ j =>
    rw [show 1 + (j + 1) = j + 2 by omega, show j + 1 - 1 = j by omega]
    simp [held]

/-- The orbit of 1 under the integer map, as a spot check of `heldNat`. -/
theorem heldNat_orbit_one :
    (List.range 8).map (fun n => Nat.repeat heldNat n 1) = [1, 3, 6, 13, 25, 55, 100, 222] := by decide

/-- Period 2 comes down to the held column: if column `k` of the orbit of a row with a leftmost 1 alternates from time
`T` on, then the cells left of it, from a later step on, are the `held` orbit of a nonzero half that is 0 beyond some
cell, and the cell next to the column reads 1 at every odd step of that orbit. -/
theorem period_two_held (init : Int → Bool) (m : Int) (hm : init m = true) (hz : ∀ x : Int, x < m → init x = false)
    (k : Int) (T : Nat) (h : ∀ t : Nat, T ≤ t → evolve init (t + 1) k = !evolve init t k) :
    ∃ u : Nat → Bool, (∃ j, u j = true) ∧ (∃ N, ∀ j, N ≤ j → u j = false) ∧
      ∀ s, heldOrbit u (2 * s + 1) 0 = true := by
  -- a start S ≥ T at which the column reads 0 and the leftmost 1 lies left of column k - 1
  obtain ⟨S, hST, hSm, hS0⟩ : ∃ S : Nat, T ≤ S ∧ m - S ≤ k - 1 ∧ evolve init S k = false := by
    cases hc : evolve init (T + (m - k + 1).toNat) k with
    | false => exact ⟨T + (m - k + 1).toNat, by omega, by omega, hc⟩
    | true => exact ⟨T + (m - k + 1).toNat + 1, by omega, by omega, by rw [h _ (by omega), hc]; rfl⟩
  have col : ∀ n : Nat, evolve init (S + n) k = decide (n % 2 = 1) := by
    intro n
    induction n with
    | zero => simpa using hS0
    | succ n ih =>
      rw [show S + (n + 1) = S + n + 1 by omega, h (S + n) (by omega), ih]
      by_cases hn : n % 2 = 1
      · simp [hn]; omega
      · simp [hn]; omega
  -- the cells left of the column at step S + n, bit j for the cell j + 1 places left of it
  let v : Nat → Nat → Bool := fun n j => evolve init (S + n) (k - 1 - (j : Int))
  have one : ∀ n : Nat, n % 2 = 1 → v n 0 = true := by
    intro n hn
    have h1 : evolve init (S + n) k = true := by rw [col n]; simp [hn]
    have h0 : evolve init (S + n + 1) k = false := by
      rw [show S + n + 1 = S + (n + 1) by omega, col (n + 1)]; simp; omega
    show evolve init (S + n) (k - 1 - ((0 : Nat) : Int)) = true
    rw [show k - 1 - ((0 : Nat) : Int) = k - 1 by omega]
    exact left_of_alternating init k (S + n) h1 h0
  have unfold_v : ∀ n j : Nat,
      v (n + 1) j = rule30 (v n (j + 1)) (v n j) (evolve init (S + n) (k - 1 - (j : Int) + 1)) := by
    intro n j
    show evolve init (S + (n + 1)) (k - 1 - (j : Int)) =
      rule30 (evolve init (S + n) (k - 1 - ((j + 1 : Nat) : Int))) (evolve init (S + n) (k - 1 - (j : Int)))
        (evolve init (S + n) (k - 1 - (j : Int) + 1))
    rw [show S + (n + 1) = S + n + 1 by omega,
      show k - 1 - ((j + 1 : Nat) : Int) = k - 1 - (j : Int) - 1 by omega]
    rfl
  have step : ∀ n : Nat, v (n + 1) = held (v n) := by
    intro n
    funext j
    cases j with
    | zero =>
      rw [unfold_v n 0, show k - 1 - ((0 : Nat) : Int) + 1 = k by omega]
      show xor (v n 1) (v n 0 || evolve init (S + n) k) = xor (v n 1) (v n 0)
      by_cases hn : n % 2 = 1
      · rw [one n hn]; rfl
      · rw [col n]; simp [hn]
    | succ j =>
      rw [unfold_v n (j + 1), show k - 1 - ((j + 1 : Nat) : Int) + 1 = k - 1 - (j : Int) by omega]
      rfl
  have orbit : ∀ n : Nat, heldOrbit (v 0) n = v n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => show held (heldOrbit (v 0) n) = v (n + 1); rw [ih, step n]
  refine ⟨v 0, ⟨(k - 1 - (m - S)).toNat, ?_⟩, ⟨(k - m + S).toNat, fun j hj => ?_⟩, fun s => ?_⟩
  · show evolve init (S + 0) (k - 1 - (((k - 1 - (m - S)).toNat : Nat) : Int)) = true
    rw [Nat.add_zero, show k - 1 - (((k - 1 - (m - S)).toNat : Nat) : Int) = m - S by omega]
    exact (left_edge init m hm hz S).1
  · show evolve init (S + 0) (k - 1 - (j : Int)) = false
    rw [Nat.add_zero]
    exact (left_edge init m hm hz S).2 _ (by omega)
  · rw [orbit]
    exact one (2 * s + 1) (by omega)

/-- If the single seed's center column alternated from `T` on, some nonzero half that is 0 beyond some cell would read 1
next to the held column at every odd step of its `held` orbit. -/
theorem single_period_two_held (T : Nat) (h : ∀ t : Nat, T ≤ t → evolve single (t + 1) 0 = !evolve single t 0) :
    ∃ u : Nat → Bool, (∃ j, u j = true) ∧ (∃ N, ∀ j, N ≤ j → u j = false) ∧
      ∀ s, heldOrbit u (2 * s + 1) 0 = true :=
  period_two_held single 0 rfl (fun x hx => decide_eq_false (by omega)) 0 T h

/-- The number whose bit `j` is `u j` for `j < N` and 0 beyond. -/
def natOf (u : Nat → Bool) : Nat → Nat
  | 0 => 0
  | N + 1 => 2 * natOf (fun j => u (j + 1)) N + if u 0 then 1 else 0

theorem natOf_testBit : ∀ (N : Nat) (u : Nat → Bool) (j : Nat), (natOf u N).testBit j = (decide (j < N) && u j) := by
  intro N
  induction N with
  | zero => intro u j; simp [natOf]
  | succ N ih =>
    intro u j
    cases j with
    | zero =>
      rw [Nat.testBit_zero]
      cases h : u 0 <;> simp [natOf, h] <;> omega
    | succ j =>
      rw [Nat.testBit_succ, show (natOf u (N + 1)) / 2 = natOf (fun j => u (j + 1)) N by
        show (2 * natOf (fun j => u (j + 1)) N + if u 0 then 1 else 0) / 2 = _
        split <;> omega, ih]
      simp

/-- With `u` 0 from bit `N` on, the integer map follows the `held` orbit of `u` bit for bit. -/
theorem heldNat_repeat (u : Nat → Bool) (N : Nat) (hN : ∀ j, N ≤ j → u j = false) :
    ∀ n j, (Nat.repeat heldNat n (natOf u N)).testBit j = heldOrbit u n j := by
  intro n
  induction n with
  | zero =>
    intro j
    show (natOf u N).testBit j = u j
    rw [natOf_testBit]
    by_cases hj : j < N
    · simp [hj]
    · simp [hj, hN j (by omega)]
  | succ n ih =>
    intro j
    show (heldNat (Nat.repeat heldNat n (natOf u N))).testBit j = held (heldOrbit u n) j
    rw [heldNat_testBit]
    exact congrArg (fun v => held v j) (funext ih)

/-- Period 2 as a question about integers: if column `k` of the orbit of a row with a leftmost 1 alternates from time
`T` on, some positive integer is odd at every odd step of its orbit under `heldNat`. -/
theorem period_two_integer (init : Int → Bool) (m : Int) (hm : init m = true) (hz : ∀ x : Int, x < m → init x = false)
    (k : Int) (T : Nat) (h : ∀ t : Nat, T ≤ t → evolve init (t + 1) k = !evolve init t k) :
    ∃ U : Nat, 0 < U ∧ ∀ s, Nat.repeat heldNat (2 * s + 1) U % 2 = 1 := by
  obtain ⟨u, ⟨j0, hj0⟩, ⟨N, hN⟩, hodd⟩ := period_two_held init m hm hz k T h
  refine ⟨natOf u N, ?_, fun s => ?_⟩
  · have hj0N : j0 < N := by
      by_cases hc : j0 < N
      · exact hc
      · rw [hN j0 (by omega)] at hj0; exact absurd hj0 Bool.false_ne_true
    have hbit := natOf_testBit N u j0
    rw [hj0, show decide (j0 < N) = true from decide_eq_true hj0N] at hbit
    exact Nat.pos_of_ne_zero (fun h0 => by rw [h0] at hbit; simp at hbit)
  · have hbit := heldNat_repeat u N hN (2 * s + 1) 0
    rw [hodd s, Nat.testBit_zero] at hbit
    simpa using hbit

/-- The single seed's center column, as a question about integers. -/
theorem single_period_two_integer (T : Nat) (h : ∀ t : Nat, T ≤ t → evolve single (t + 1) 0 = !evolve single t 0) :
    ∃ U : Nat, 0 < U ∧ ∀ s, Nat.repeat heldNat (2 * s + 1) U % 2 = 1 :=
  period_two_integer single 0 rfl (fun x hx => decide_eq_false (by omega)) 0 T h

/-- Official form: if the prize's center column alternated from some time on, some positive integer would be odd at
every odd step of its orbit under `heldNat`. -/
theorem center_period_two_integer (T : Nat)
    (h : ∀ t : Nat, T ≤ t → Rule30Prize.center (t + 1) = !Rule30Prize.center t) :
    ∃ U : Nat, 0 < U ∧ ∀ s, Nat.repeat heldNat (2 * s + 1) U % 2 = 1 :=
  single_period_two_integer T fun t ht => by
    rw [evolve_single_center, evolve_single_center]
    exact h t ht

end Rule30Open
