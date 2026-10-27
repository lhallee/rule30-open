module

public import Rule30Open.Foundations.Evolve

/-!
# Finite windows of a row, and the cells right of a column

The cells `x .. x + n - 1` of a row one step later depend only on the cells `x - 1 .. x + n` now. So
the cells right of a column, driven by the values the column takes, are a finite computation: `drive`
runs it on lists. `drive_cells` says the real rows follow it, which turns statements about all rows
into finite checks over every list of cells (`allLists`, `mem_allLists`).

The natural-language argument is `RightHalf.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

/-- One step of the cells right of a column whose cell is `c` now: the cells `x .. x + n - 1` one step later from the
cells `x .. x + n` now. -/
def driveStep (c : Bool) : List Bool → List Bool
  | a :: b :: rest => rule30 c a b :: driveStep a (b :: rest)
  | _ => []

/-- The cells right of a column, after the column takes the values `cs` in turn. -/
def drive : List Bool → List Bool → List Bool
  | [], cells => cells
  | c :: cs, cells => drive cs (driveStep c cells)

/-- Cells `x .. x + n - 1` of the row at time `t`. -/
def cellsFrom (init : Int → Bool) (t : Nat) (x : Int) : Nat → List Bool
  | 0 => []
  | n + 1 => evolve init t x :: cellsFrom init t (x + 1) n

/-- Column `y` at times `t .. t + n - 1`. -/
def columnFrom (init : Int → Bool) (y : Int) (t : Nat) : Nat → List Bool
  | 0 => []
  | n + 1 => evolve init t y :: columnFrom init y (t + 1) n

/-- Every list of `n` cells. -/
def allLists : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (allLists n).flatMap fun l => [false :: l, true :: l]

theorem driveStep_cells (init : Int → Bool) (t : Nat) : ∀ (n : Nat) (x : Int),
    driveStep (evolve init t (x - 1)) (cellsFrom init t x (n + 1)) = cellsFrom init (t + 1) x n
  | 0, _ => rfl
  | n + 1, x => by
    have ih := driveStep_cells init t n (x + 1)
    rw [show x + 1 - 1 = x by omega] at ih
    show rule30 (evolve init t (x - 1)) (evolve init t x) (evolve init t (x + 1)) ::
      driveStep (evolve init t x) (cellsFrom init t (x + 1) (n + 1)) = cellsFrom init (t + 1) x (n + 1)
    rw [ih]
    rfl

/-- Driving the cells right of column `x - 1` with that column's real values gives the real cells. -/
theorem drive_cells (init : Int → Bool) (x : Int) : ∀ (m t n : Nat),
    drive (columnFrom init (x - 1) t m) (cellsFrom init t x (n + m)) = cellsFrom init (t + m) x n
  | 0, _, _ => rfl
  | m + 1, t, n => by
    show drive (columnFrom init (x - 1) (t + 1) m) (driveStep (evolve init t (x - 1)) (cellsFrom init t x (n + m + 1)))
      = cellsFrom init (t + (m + 1)) x n
    rw [driveStep_cells init t (n + m) x, drive_cells init x m (t + 1) n, show t + 1 + m = t + (m + 1) by omega]

theorem columnFrom_const (init : Int → Bool) (y : Int) (b : Bool) : ∀ (n t : Nat),
    (∀ i : Nat, i < n → evolve init (t + i) y = b) → columnFrom init y t n = List.replicate n b
  | 0, _, _ => rfl
  | n + 1, t, h => by
    show evolve init t y :: columnFrom init y (t + 1) n = b :: List.replicate n b
    rw [show evolve init t y = b from h 0 (by omega),
      columnFrom_const init y b n (t + 1) fun i hi => by rw [show t + 1 + i = t + (i + 1) by omega]; exact h (i + 1) (by omega)]

theorem length_cellsFrom (init : Int → Bool) (t : Nat) : ∀ (n : Nat) (x : Int), (cellsFrom init t x n).length = n
  | 0, _ => rfl
  | n + 1, x => by
    show (cellsFrom init t (x + 1) n).length + 1 = n + 1
    rw [length_cellsFrom init t n (x + 1)]

/-- Every list of cells is among the lists `allLists` enumerates for its length. -/
theorem mem_allLists : ∀ l : List Bool, l ∈ allLists l.length
  | [] => List.mem_singleton.mpr rfl
  | b :: l => by
    show b :: l ∈ (allLists l.length).flatMap fun l => [false :: l, true :: l]
    rw [List.mem_flatMap]
    exact ⟨l, mem_allLists l, by cases b <;> simp⟩

theorem cellsFrom_succ (init : Int → Bool) (t : Nat) : ∀ (n : Nat) (x : Int),
    cellsFrom init t x (n + 1) = cellsFrom init t x n ++ [evolve init t (x + n)]
  | 0, x => by
    show [evolve init t x] = [evolve init t (x + ((0 : Nat) : Int))]
    rw [show x + ((0 : Nat) : Int) = x by omega]
  | n + 1, x => by
    show evolve init t x :: cellsFrom init t (x + 1) (n + 1) =
      evolve init t x :: (cellsFrom init t (x + 1) n ++ [evolve init t (x + ((n + 1 : Nat) : Int))])
    rw [cellsFrom_succ init t n (x + 1), show x + 1 + (n : Int) = x + ((n + 1 : Nat) : Int) by omega]

theorem headD_cellsFrom (init : Int → Bool) (t : Nat) (x : Int) :
    ∀ n : Nat, 0 < n → (cellsFrom init t x n).headD false = evolve init t x
  | 0, h => absurd h (Nat.lt_irrefl 0)
  | _ + 1, _ => rfl

end Rule30Open
