module

public import Rule30Open.Foundations.Evolve
public import Rule30Open.PeriodTwo.HeldColumn

/-!
# Every period in one identity: the kicked form

Whatever a column reads, the cells left of it follow Rule 30 beside a column held at 0 (`held`), except
that the cell next to the column is flipped when the column reads 1 at two steps in a row
(`left_kicked_zero`, `left_kicked_succ`). And at a 1 of the column that cell is the opposite of the
column's next value (`left_kicked_check`). So a column repeating a block gives a half that follows `held`
with periodic kicks and meets one parity condition at each 1 of the block. This holds in the orbit of
every row. For the single seed's center column the kit has the same identity as
`Rule30MaskedJen.effective_step`: the left half sees the center only through `c t && c (t + 1)`.

The cell right of the column adds tests at its 0s: a 1 there is followed by the opposite of the column
(`right_latch`), and at a 0 of the column the column's next value shows it (`right_shown`). So beside an
alternating column the cell left of it never reads 0 at two of the column's 0s in a row
(`period_two_golden`), the kit's `Rule30PeriodTwo.golden` in the orbit of every row.

The natural-language argument is `KickedForm.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

/-- Every period in one identity, the kicked form: in the orbit of any row the cell next to column `k` follows `held`
from step `t` to step `t + 1`, flipped when the column reads 1 at both steps. -/
theorem left_kicked_zero (init : Int → Bool) (k : Int) (t : Nat) :
    leftOf init (t + 1) k 0 = xor (held (leftOf init t k) 0) (evolve init t k && evolve init (t + 1) k) := by
  have e : evolve init (t + 1) k = rule30 (evolve init t (k - 1)) (evolve init t k) (evolve init t (k + 1)) := rfl
  show rule30 (evolve init t (k - 1 - ((0 : Nat) : Int) - 1)) (evolve init t (k - 1 - ((0 : Nat) : Int)))
      (evolve init t (k - 1 - ((0 : Nat) : Int) + 1)) =
    xor (xor (evolve init t (k - 1 - ((1 : Nat) : Int))) (evolve init t (k - 1 - ((0 : Nat) : Int))))
      (evolve init t k && evolve init (t + 1) k)
  rw [show k - 1 - ((0 : Nat) : Int) + 1 = k by omega,
    show k - 1 - ((0 : Nat) : Int) - 1 = k - 1 - ((1 : Nat) : Int) by omega,
    show k - 1 - ((0 : Nat) : Int) = k - 1 by omega, e]
  generalize evolve init t (k - 1 - ((1 : Nat) : Int)) = a
  generalize evolve init t (k - 1) = u
  generalize evolve init t k = c
  generalize evolve init t (k + 1) = r
  cases a <;> cases u <;> cases c <;> cases r <;> rfl

/-- ... and every other cell left of the column follows `held` exactly, whatever the column reads. -/
theorem left_kicked_succ (init : Int → Bool) (k : Int) (t j : Nat) :
    leftOf init (t + 1) k (j + 1) = held (leftOf init t k) (j + 1) := by
  show rule30 (evolve init t (k - 1 - ((j + 1 : Nat) : Int) - 1)) (evolve init t (k - 1 - ((j + 1 : Nat) : Int)))
      (evolve init t (k - 1 - ((j + 1 : Nat) : Int) + 1)) =
    xor (evolve init t (k - 1 - ((j + 2 : Nat) : Int)))
      (evolve init t (k - 1 - ((j + 1 : Nat) : Int)) || evolve init t (k - 1 - (j : Int)))
  rw [show k - 1 - ((j + 1 : Nat) : Int) - 1 = k - 1 - ((j + 2 : Nat) : Int) by omega,
    show k - 1 - ((j + 1 : Nat) : Int) + 1 = k - 1 - (j : Int) by omega]
  rfl

/-- The kicked form read as a check on the cell next to the column: where the column reads 1, that cell is the
opposite of the column's next value, the parity condition a repeating block imposes at each of its 1s. -/
theorem left_kicked_check (init : Int → Bool) (k : Int) (t : Nat) (h1 : evolve init t k = true) :
    leftOf init t k 0 = !evolve init (t + 1) k := by
  show evolve init t (k - 1 - ((0 : Nat) : Int)) = _
  rw [show k - 1 - ((0 : Nat) : Int) = k - 1 by omega]
  exact left_of_one init k t h1

/-- The cell right of a column, as far as the column forces it: a 1 there is followed by the opposite of the column. -/
theorem right_latch (init : Int → Bool) (k : Int) (t : Nat) (h1 : evolve init t (k + 1) = true) :
    evolve init (t + 1) (k + 1) = !evolve init t k := by
  show rule30 (evolve init t (k + 1 - 1)) (evolve init t (k + 1)) (evolve init t (k + 1 + 1)) = _
  rw [show k + 1 - 1 = k by omega, h1]
  generalize evolve init t k = c
  cases c <;> rfl

/-- ... and where the column reads 0, its next value shows the cell right of it, given the cell left of it. -/
theorem right_shown (init : Int → Bool) (k : Int) (t : Nat) (h0 : evolve init t k = false) :
    evolve init t (k + 1) = xor (evolve init (t + 1) k) (evolve init t (k - 1)) := by
  have e : evolve init (t + 1) k = rule30 (evolve init t (k - 1)) (evolve init t k) (evolve init t (k + 1)) := rfl
  rw [e, h0]
  generalize evolve init t (k - 1) = a
  generalize evolve init t (k + 1) = r
  cases a <;> cases r <;> rfl

/-- Beside an alternating column the cell left of it is never 0 at two of the column's 0s in a row: if the column reads
0 1 0 1 from step `t` and the cell left of it reads 0 at `t`, it reads 1 at `t + 2`. The right half shows it: the cell
right of the column reads 1 at `t` and `t + 1`, so 0 at `t + 2`, which the column's update at `t + 2` turns into a 1
on the left. In the orbit of every row. -/
theorem period_two_golden (init : Int → Bool) (k : Int) (t : Nat) (h0 : evolve init t k = false)
    (h1 : evolve init (t + 1) k = true) (h2 : evolve init (t + 2) k = false) (h3 : evolve init (t + 3) k = true)
    (hl : evolve init t (k - 1) = false) : evolve init (t + 2) (k - 1) = true := by
  have r0 : evolve init t (k + 1) = true := by rw [right_shown init k t h0, h1, hl]; rfl
  have r1 : evolve init (t + 1) (k + 1) = true := by rw [right_latch init k t r0, h0]; rfl
  have r2 : evolve init (t + 2) (k + 1) = false := by rw [right_latch init k (t + 1) r1, h1]; rfl
  have e := right_shown init k (t + 2) h2
  rw [r2, h3] at e
  revert e
  generalize evolve init (t + 2) (k - 1) = a
  cases a <;> decide

end Rule30Open
