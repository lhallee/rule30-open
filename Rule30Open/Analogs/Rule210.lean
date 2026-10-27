module

/-!
# Rule 210 beside an alternating column

A proof that no finite half keeps the held column's condition (`Rule30Open.period_two_held`) must also use
what Rule 30 does at a cell reading 1, where `rule30 l true r = !l` and Rule 210, `xor l (!c && r)`, gives
`l`: the two rules agree everywhere else. Rule 210 is left-permutive and moves a leftmost 1 one cell left a
step as Rule 30 does, and an alternating column forces the cell left of it at each of its 1s as in Rule 30.
Yet finite halves keep the condition forever: a half on one color of the space-time checkerboard stays on
it, since under Rule 210 a cell whose two neighbors read 0 becomes 0 (under Rule 30,
`rule30 false true false` is 1), and at each 1 of the column the cell next to it lies on the other color
(`orbit210_checkerboard`). So a single 1 next to the column, a finite nonzero half, never breaks the
condition (`rule210_finite_half`).

The kit's `Rule30Realization` shows a related barrier from the single seed: under Rules 90, 150 and 210
the center column is eventually constant.

The natural-language argument is `Rule210.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

/-- Rule 210 on a cell's left neighbor, the cell itself and its right neighbor. -/
def rule210 (l c r : Bool) : Bool := xor l (!c && r)

/-- Rule 210 left of a column that reads `c`; bit `j` is the cell `j + 1` places left of the column. -/
def drive210 (c : Bool) (u : Nat → Bool) : Nat → Bool
  | 0 => rule210 (u 1) (u 0) c
  | j + 1 => rule210 (u (j + 2)) (u (j + 1)) (u j)

/-- The cells left of a column reading 0 at even steps and 1 at odd steps, from `u` at step 0. -/
def orbit210 (u : Nat → Bool) : Nat → Nat → Bool
  | 0 => u
  | n + 1 => drive210 (n % 2 == 1) (orbit210 u n)

/-- The first steps from a single 1 next to the column, as a spot check of `orbit210`. -/
theorem orbit210_single :
    (List.range 5).map (fun n => (List.range 6).map (orbit210 (fun j => j == 0) n)) =
      [[true, false, false, false, false, false], [false, true, false, false, false, false],
       [false, false, true, false, false, false], [false, true, false, true, false, false],
       [false, false, false, false, true, false]] := by decide

/-- A half on the even bits at step 0 stays on the bits `j` with `j + n` even, the colors of the checkerboard. -/
theorem orbit210_checkerboard (u : Nat → Bool) (hu : ∀ j, j % 2 = 1 → u j = false) :
    ∀ n j, (j + n) % 2 = 1 → orbit210 u n j = false := by
  intro n
  induction n with
  | zero => intro j hj; exact hu j (by omega)
  | succ n ih =>
    intro j hj
    show drive210 (n % 2 == 1) (orbit210 u n) j = false
    cases j with
    | zero =>
      have h1 : orbit210 u n 1 = false := ih 1 (by omega)
      have hn : (n % 2 == 1) = false := by
        rw [show n % 2 = 0 by omega]; rfl
      simp only [drive210, rule210, h1, hn]
      cases orbit210 u n 0 <;> rfl
    | succ j =>
      have h2 : orbit210 u n (j + 2) = false := ih (j + 2) (by omega)
      have h0 : orbit210 u n j = false := ih j (by omega)
      simp only [drive210, rule210, h2, h0]
      cases orbit210 u n (j + 1) <;> rfl

/-- The analog of `period_two_held`'s conclusion holds for Rule 210: a single 1 next to an alternating column, a
finite nonzero half, keeps the forced 0 next to the column at every 1 of the column. So a proof for Rule 30 must use
its update at a cell reading 1, where the two rules differ. -/
theorem rule210_finite_half :
    ∃ u : Nat → Bool, (∃ j, u j = true) ∧ (∃ N, ∀ j, N ≤ j → u j = false) ∧
      ∀ s, orbit210 u (2 * s + 1) 0 = false := by
  have hu : ∀ j, j % 2 = 1 → (j == 0) = false := by
    intro j hj
    cases j with
    | zero => omega
    | succ j => rfl
  refine ⟨fun j => j == 0, ⟨0, rfl⟩, ⟨1, fun j hj => ?_⟩, fun s => ?_⟩
  · cases j with
    | zero => omega
    | succ j => rfl
  · exact orbit210_checkerboard (fun j => j == 0) hu (2 * s + 1) 0 (by omega)

end Rule30Open
