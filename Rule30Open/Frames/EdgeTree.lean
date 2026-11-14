module

public import Rule30Open.Frames.EdgePeriodFour
public import Ruliology.CellularAutomata.Rule30FrozenRuler

/-!
# Every edge code is rain or passes through a branch state

For an edge code `c` (the kit's `Rule30FrozenRuler.T` and `iter`) write `col c e i = iter i c e`, the column of bit `e`
in time. Call a sequence alternating (`Alt`) when it flips at every step.

* `rain_or_branch`: **for every code with bit 0 black, either `c` is `rainA` or `rainB`, or for some `j ≥ 1` the column
  `j` alternates and column `j + 1` equals it (a branch state).** No periodicity is assumed. From a pair of columns
  that alternate and are complementary, the next column alternates (its input is always black), so it is the
  complement of the one before (rain continues) or equal to it (a branch). Columns 1 and 2 alternate because column 0
  is black.

So the classification of the codes of period `L` reduces to the statement that no periodic walk starts at a branch
state. That is a finite check for each `L`, not made here.

The natural-language argument is `EdgeTree.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open.Frames.EdgeTree

open Ruliology.CellularAutomata.Rule30FrozenRuler (iter iter_zero)

/-- The column of bit `e` in time. -/
def col (c : Nat → Bool) (e : Nat) : Nat → Bool := fun i => iter i c e

/-- A sequence that flips at every step. -/
def Alt (f : Nat → Bool) : Prop := ∀ i, f (i + 1) = !f i

theorem alt_eq {f g : Nat → Bool} (hf : Alt f) (hg : Alt g) (h0 : f 0 = g 0) : f = g := by
  funext i
  induction i with
  | zero => exact h0
  | succ i ih => rw [hf, hg, ih]

theorem alt_not {f : Nat → Bool} (hf : Alt f) : Alt (fun i => !f i) := by
  intro i
  show (!f (i + 1)) = !!f i
  rw [hf]

theorem col_one_succ (c : Nat → Bool) (i : Nat) :
    col c 1 (i + 1) = xor (col c 1 i) (col c 0 i) := rfl

theorem col_succ (c : Nat → Bool) (j i : Nat) :
    col c (j + 2) (i + 1) = xor (col c (j + 2) i) (col c (j + 1) i || col c j i) := rfl

/-- A column whose input is black at every step alternates. -/
theorem alt_of_input {f g : Nat → Bool} (hstep : ∀ i, f (i + 1) = xor (f i) (g i)) (hg : ∀ i, g i = true) :
    Alt f := by
  intro i
  rw [hstep, hg]
  cases f i <;> rfl

/-- Two alternating sequences: the second is the first or its complement. -/
theorem alt_cases {f g : Nat → Bool} (hf : Alt f) (hg : Alt g) : g = f ∨ g = fun i => !f i := by
  by_cases h : g 0 = f 0
  · exact Or.inl (alt_eq hg hf h)
  · refine Or.inr (alt_eq hg (alt_not hf) ?_)
    revert h
    cases g 0 <;> cases f 0 <;> decide

/-- A rain pair at `j`: column `j` alternates and column `j + 1` is its complement. -/
def RainPair (c : Nat → Bool) (j : Nat) : Prop := Alt (col c j) ∧ col c (j + 1) = fun i => !col c j i

/-- A branch state at `j`: column `j` alternates and column `j + 1` equals it. -/
def Branch (c : Nat → Bool) (j : Nat) : Prop := Alt (col c j) ∧ col c (j + 1) = col c j

theorem next_of_rain (c : Nat → Bool) (j : Nat) (h : RainPair c (j + 1)) :
    RainPair c (j + 2) ∨ Branch c (j + 2) := by
  obtain ⟨ha, hn⟩ := h
  have ha2 : Alt (col c (j + 2)) := by rw [hn]; exact alt_not ha
  have ha3 : Alt (col c (j + 3)) := by
    apply alt_of_input (col_succ c (j + 1))
    intro i
    have : col c (j + 2) i = !col c (j + 1) i := congrFun hn i
    rw [this]
    cases col c (j + 1) i <;> rfl
  rcases alt_cases ha2 ha3 with e | e
  · exact Or.inr ⟨ha2, e⟩
  · exact Or.inl ⟨ha2, e⟩

theorem start (c : Nat → Bool) (h0 : c 0 = true) : RainPair c 1 ∨ Branch c 1 := by
  have z : ∀ i, col c 0 i = true := fun i => by
    show iter i c 0 = true
    rw [iter_zero]; exact h0
  have a1 : Alt (col c 1) := alt_of_input (col_one_succ c) z
  have a2 : Alt (col c 2) := by
    apply alt_of_input (col_succ c 0)
    intro i
    rw [z i]
    cases col c 1 i <;> rfl
  rcases alt_cases a1 a2 with e | e
  · exact Or.inr ⟨a1, e⟩
  · exact Or.inl ⟨a1, e⟩

theorem rainA_succ (k : Nat) : Rule30Open.Frames.EdgePeriodFour.rainA (k + 1) =
    !Rule30Open.Frames.EdgePeriodFour.rainA k := by
  simp only [Rule30Open.Frames.EdgePeriodFour.rainA]
  rcases Nat.mod_two_eq_zero_or_one k with h | h
  · have h1 : (k + 1) % 2 = 1 := by omega
    simp [h, h1]
  · have h1 : (k + 1) % 2 = 0 := by omega
    simp [h, h1]

theorem rainB_succ (k : Nat) : Rule30Open.Frames.EdgePeriodFour.rainB (k + 2) =
    !Rule30Open.Frames.EdgePeriodFour.rainB (k + 1) := by
  simp only [Rule30Open.Frames.EdgePeriodFour.rainB]
  rcases Nat.mod_two_eq_zero_or_one k with h | h
  · have h1 : (k + 1) % 2 = 1 := by omega
    have h2 : (k + 2) % 2 = 0 := by omega
    simp [h1, h2]
  · have h1 : (k + 1) % 2 = 0 := by omega
    have h2 : (k + 2) % 2 = 1 := by omega
    simp [h1, h2]

theorem rain_or_branch (c : Nat → Bool) (h0 : c 0 = true) :
    (c = Rule30Open.Frames.EdgePeriodFour.rainA ∨ c = Rule30Open.Frames.EdgePeriodFour.rainB) ∨
      ∃ j, 1 ≤ j ∧ Branch c j := by
  by_cases hb : ∃ j, 1 ≤ j ∧ Branch c j
  · exact Or.inr hb
  · left
    have all : ∀ k, RainPair c (k + 1) := by
      intro k
      induction k with
      | zero =>
        rcases start c h0 with h | h
        · exact h
        · exact absurd ⟨1, Nat.le_refl 1, h⟩ hb
      | succ k ih =>
        rcases next_of_rain c k ih with h | h
        · exact h
        · exact absurd ⟨k + 2, by omega, h⟩ hb
    have flip : ∀ k, c (k + 2) = !c (k + 1) := fun k => by
      have h := congrFun (all k).2 0
      exact h
    cases h1 : c 1
    · refine Or.inl (funext fun k => ?_)
      induction k with
      | zero => rw [h0]; rfl
      | succ k ih =>
        cases k with
        | zero => rw [h1]; rfl
        | succ k => rw [flip, ih]; exact (rainA_succ (k + 1)).symm
    · refine Or.inr (funext fun k => ?_)
      induction k with
      | zero => rw [h0]; rfl
      | succ k ih =>
        cases k with
        | zero => rw [h1]; rfl
        | succ k => rw [flip, ih]; exact (rainB_succ k).symm

end Rule30Open.Frames.EdgeTree
