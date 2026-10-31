module

public import Ruliology.CellularAutomata.Rule30Jen

/-!
# Counts of black cells move left by at most a factor of three

Write `N i n` for the number of black cells of column `i` of the single-cell orbit at the times `0, ..., n - 1`, and
`Wh i n` for the white ones. Rule 30 is left permutive (`Rule30Jen.cell_left`): a cell of column `i - 1` is
`cell (t + 1) i xor (cell t i || cell t (i + 1))`. So a black cell of column `i - 1` at time `t` needs a black cell at
`(t + 1, i)`, `(t, i)` or `(t, i + 1)`, and also a white one there. Summing over time:

* `transfer`: `N (i - 1) n <= N i (n + 1) + N i n + N (i + 1) n`;
* `transfer_white`: `N (i - 1) n <= Wh i (n + 1) + Wh i n + Wh (i + 1) n`;
* `iterate`: `N (-k) n + N (-k + 1) n <= 3 ^ k * (N 0 (n + k) + N 1 (n + k))`.

In densities, the upper density of black cells in column `i - 1` is at most twice that of column `i` plus that of
column `i + 1`, and at most twice the upper white density of column `i` plus that of column `i + 1`.
-/

@[expose] public section

namespace Rule30Open

open Ruliology.CellularAutomata.Rule30Jen

/-- Black cells of column `i` at times `0, …, n - 1`. -/
def N (i : Int) : Nat → Nat
  | 0 => 0
  | n + 1 => N i n + (if cell n i then 1 else 0)

theorem N_mono (i : Int) (m : Nat) : N i m ≤ N i (m + 1) := by
  simp only [N]; omega

theorem point (t : Nat) (i : Int) :
    (if cell t (i - 1) then 1 else 0) ≤
      (if cell (t + 1) i then 1 else 0) + (if cell t i then 1 else 0) +
        (if cell t (i + 1) then 1 else 0) := by
  rw [cell_left t i]
  cases cell (t + 1) i <;> cases cell t i <;> cases cell t (i + 1) <;> simp

/-- **Leftward transfer.** Every black cell of column `i - 1` at time `t` has a black cell at
`(t + 1, i)`, `(t, i)` or `(t, i + 1)`, so the black cells of column `i - 1` before time `n` are
at most those of column `i` (counted twice, one step apart) and column `i + 1`. -/
theorem transfer (i : Int) : ∀ n, N (i - 1) n ≤ N i (n + 1) + N i n + N (i + 1) n
  | 0 => by simp [N]
  | n + 1 => by
    have ih := transfer i n
    have hp := point n i
    simp only [N] at ih ⊢
    omega

/-- **Iterated transfer.** The black cells of columns `-k` and `-k + 1` before time `n` number at
most `3^k` times those of columns `0` and `1` before time `n + k`. -/
theorem iterate (k : Nat) : ∀ n,
    N (-(k : Int)) n + N (-(k : Int) + 1) n ≤ 3 ^ k * (N 0 (n + k) + N 1 (n + k)) := by
  induction k with
  | zero => intro n; simp
  | succ k ih =>
    intro n
    have h := ih (n + 1)
    rw [show n + 1 + k = n + (k + 1) by omega] at h
    have t := transfer (-(k : Int)) n
    rw [show -(k : Int) - 1 = -((k + 1 : Nat) : Int) by omega] at t
    rw [show -((k + 1 : Nat) : Int) + 1 = -(k : Int) by omega]
    have m0 := N_mono (-(k : Int)) n
    have m1 := N_mono (-(k : Int) + 1) n
    have e : 3 ^ (k + 1) * (N 0 (n + (k + 1)) + N 1 (n + (k + 1))) =
        3 * (3 ^ k * (N 0 (n + (k + 1)) + N 1 (n + (k + 1)))) := by
      rw [Nat.pow_succ, Nat.mul_comm (3 ^ k) 3, Nat.mul_assoc]
    rw [e]
    generalize 3 ^ k * (N 0 (n + (k + 1)) + N 1 (n + (k + 1))) = X at h ⊢
    omega

/-- White cells of column `i` at times `0, …, n - 1`. -/
def Wh (i : Int) : Nat → Nat
  | 0 => 0
  | n + 1 => Wh i n + (if cell n i then 0 else 1)

theorem point_white (t : Nat) (i : Int) :
    (if cell t (i - 1) then 1 else 0) ≤
      (if cell (t + 1) i then 0 else 1) + (if cell t i then 0 else 1) +
        (if cell t (i + 1) then 0 else 1) := by
  rw [cell_left t i]
  cases cell (t + 1) i <;> cases cell t i <;> cases cell t (i + 1) <;> simp

/-- **Dual transfer.** A black cell of column `i - 1` at time `t` also needs a white cell at
`(t + 1, i)`, `(t, i)` or `(t, i + 1)`: if columns `i` and `i + 1` are both black at time `t`,
then `cell t (i - 1) = ¬ cell (t + 1) i`. -/
theorem transfer_white (i : Int) : ∀ n, N (i - 1) n ≤ Wh i (n + 1) + Wh i n + Wh (i + 1) n
  | 0 => by simp [N, Wh]
  | n + 1 => by
    have ih := transfer_white i n
    have hp := point_white n i
    simp only [N, Wh] at ih ⊢
    omega

theorem point_right (t : Nat) (i : Int) :
    (if cell t (i + 1) then 1 else 0) ≤
      (if cell t (i - 1) then 1 else 0) + (if cell (t + 1) i then 1 else 0) := by
  rw [cell_left t i]
  cases cell (t + 1) i <;> cases cell t i <;> cases cell t (i + 1) <;> simp

theorem point_right_white (t : Nat) (i : Int) :
    (if cell t (i + 1) then 1 else 0) ≤
      (if cell t (i - 1) then 0 else 1) + (if cell (t + 1) i then 0 else 1) := by
  rw [cell_left t i]
  cases cell (t + 1) i <;> cases cell t i <;> cases cell t (i + 1) <;> simp

/-- **Rightward transfer.** A black cell at `(t, i + 1)` forces exactly one black cell among
`(t, i - 1)` and `(t + 1, i)`. -/
theorem transfer_right (i : Int) : ∀ n, N (i + 1) n ≤ N (i - 1) n + N i (n + 1)
  | 0 => by simp [N]
  | n + 1 => by
    have ih := transfer_right i n
    have hp := point_right n i
    simp only [N] at ih ⊢
    omega

/-- **Dual rightward transfer.** A black cell at `(t, i + 1)` also forces exactly one white cell
among `(t, i - 1)` and `(t + 1, i)`. -/
theorem transfer_right_white (i : Int) : ∀ n, N (i + 1) n ≤ Wh (i - 1) n + Wh i (n + 1)
  | 0 => by simp [N, Wh]
  | n + 1 => by
    have ih := transfer_right_white i n
    have hp := point_right_white n i
    simp only [N, Wh] at ih ⊢
    omega

/-- **Iterated rightward transfer.** The black cells of columns `k` and `k + 1` before time `n`
number at most `2^k` times those of columns `0` and `1` before time `n + k`. -/
theorem iterate_right (k : Nat) : ∀ n,
    N (k : Int) n + N ((k : Int) + 1) n ≤ 2 ^ k * (N 0 (n + k) + N 1 (n + k)) := by
  induction k with
  | zero => intro n; simp
  | succ k ih =>
    intro n
    have h := ih (n + 1)
    rw [show n + 1 + k = n + (k + 1) by omega] at h
    have t := transfer_right ((k : Int) + 1) n
    rw [show (k : Int) + 1 - 1 = (k : Int) by omega] at t
    rw [show ((k + 1 : Nat) : Int) = (k : Int) + 1 by omega]
    have m0 := N_mono (k : Int) n
    have m1 := N_mono ((k : Int) + 1) n
    have e : 2 ^ (k + 1) * (N 0 (n + (k + 1)) + N 1 (n + (k + 1))) =
        2 * (2 ^ k * (N 0 (n + (k + 1)) + N 1 (n + (k + 1)))) := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ k) 2, Nat.mul_assoc]
    rw [e]
    generalize 2 ^ k * (N 0 (n + (k + 1)) + N 1 (n + (k + 1))) = X at h ⊢
    omega

/-- **Center column against columns `-1` and `1`.** `N 1 n ≤ N (-1) n + N 0 (n + 1)`. -/
theorem center_lower (n : Nat) : N 1 n ≤ N (-1) n + N 0 (n + 1) := by
  have := transfer_right 0 n
  simpa using this

end Rule30Open
