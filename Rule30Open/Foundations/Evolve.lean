module

/-!
# Rule 30 from an arbitrary row

`evolve init t x` is cell `x` at time `t` of Rule 30 started from the row `init`: cell `x` at `t + 1` is
`rule30` of cells `x - 1`, `x` and `x + 1` at `t`. Every other module of this library is stated for
`evolve`, so its results hold for any initial row and specialize to the single seed.

This module holds the definitions, spot checks against independent data, and the one-step facts the
other modules use: Rule 30 is left-permutive (`left_cell`), a leftmost black cell moves one cell left
per step (`left_edge`), and a black cell's left neighbor is the opposite of its next value
(`left_of_one`, `left_of_alternating`).

The natural-language argument is `Evolve.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

/-- Rule 30 on a cell's left neighbor, the cell itself and its right neighbor. -/
def rule30 (l c r : Bool) : Bool := xor l (c || r)

/-- Cell `x` at time `t` of Rule 30 started from the row `init`. -/
def evolve (init : Int → Bool) : Nat → Int → Bool
  | 0 => init
  | t + 1 => fun x => rule30 (evolve init t (x - 1)) (evolve init t x) (evolve init t (x + 1))

/-- The single seed: 1 at cell 0. -/
def single (x : Int) : Bool := decide (x = 0)

/-- The cells left of column `k` at time `t`: bit `j` is the cell `j + 1` places left of the column. -/
def leftOf (init : Int → Bool) (t : Nat) (k : Int) (j : Nat) : Bool := evolve init t (k - 1 - (j : Int))

/-! Spot checks against independent data, so a slip in a definition that left the theorems provable would
show: `rule30` is Wolfram's code 30 (0 0 0 1 1 1 1 0 on the neighborhoods 111, 110, ..., 000), and the
single seed's center column starts 1 1 0 1 1 1 0 0 1 1, as OEIS A051023 does. -/

example : [rule30 true true true, rule30 true true false, rule30 true false true, rule30 true false false,
    rule30 false true true, rule30 false true false, rule30 false false true, rule30 false false false] =
    [false, false, false, true, true, true, true, false] := by decide

example : (List.range 10).map (fun t => evolve single t 0) =
    [true, true, false, true, true, true, false, false, true, true] := by decide

/-- Rule 30 is left-permutive: cell `x - 1` follows from cell `x` one step later and cells `x` and `x + 1` now. -/
theorem left_cell (init : Int → Bool) (t : Nat) (x : Int) :
    evolve init t (x - 1) = xor (evolve init (t + 1) x) (evolve init t x || evolve init t (x + 1)) := by
  show evolve init t (x - 1) = xor (rule30 (evolve init t (x - 1)) (evolve init t x) (evolve init t (x + 1)))
    (evolve init t x || evolve init t (x + 1))
  generalize evolve init t (x - 1) = a
  generalize evolve init t x = b
  generalize evolve init t (x + 1) = c
  cases a <;> cases b <;> cases c <;> rfl

/-- In a row that is 0 left of cell `m` and 1 at `m`, the leftmost 1 is at `m - t` at time `t`. -/
theorem left_edge (init : Int → Bool) (m : Int) (hm : init m = true) (hz : ∀ x : Int, x < m → init x = false) :
    ∀ t : Nat, evolve init t (m - t) = true ∧ ∀ x : Int, x < m - t → evolve init t x = false := by
  intro t
  induction t with
  | zero =>
    refine ⟨?_, fun x hx => hz x (by omega)⟩
    rw [show m - ((0 : Nat) : Int) = m by omega]
    exact hm
  | succ t ih =>
    refine ⟨?_, fun x hx => ?_⟩
    · rw [show m - ((t + 1 : Nat) : Int) = m - t - 1 by omega]
      show rule30 (evolve init t (m - t - 1 - 1)) (evolve init t (m - t - 1)) (evolve init t (m - t - 1 + 1)) = true
      rw [ih.2 (m - t - 1 - 1) (by omega), ih.2 (m - t - 1) (by omega), show m - (t : Int) - 1 + 1 = m - t by omega,
        ih.1]
      rfl
    · show rule30 (evolve init t (x - 1)) (evolve init t x) (evolve init t (x + 1)) = false
      rw [ih.2 (x - 1) (by omega), ih.2 x (by omega), ih.2 (x + 1) (by omega)]
      rfl

/-- A cell reading 1 has, left of it, the opposite of its next value. -/
theorem left_of_one (init : Int → Bool) (k : Int) (t : Nat) (h1 : evolve init t k = true) :
    evolve init t (k - 1) = !evolve init (t + 1) k := by
  show evolve init t (k - 1) = !rule30 (evolve init t (k - 1)) (evolve init t k) (evolve init t (k + 1))
  rw [h1]
  generalize evolve init t (k - 1) = a
  cases a <;> rfl

/-- A column that reads 1 and then 0 has a 1 left of it at the first of the two steps. -/
theorem left_of_alternating (init : Int → Bool) (k : Int) (t : Nat) (h1 : evolve init t k = true)
    (h0 : evolve init (t + 1) k = false) : evolve init t (k - 1) = true := by
  rw [left_of_one init k t h1, h0]
  rfl

end Rule30Open
