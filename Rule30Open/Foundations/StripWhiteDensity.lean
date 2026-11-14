module

public import Ruliology.CellularAutomata.Rule30Jen

/-!
# Strips of five to nine adjacent columns of every orbit are at least 2/5 white

For `J = 5, 6, 7, 8, 9`, in every orbit of Rule 30 (any initial row), the strip of columns
`a .. a + J - 1` has at least `(2 J n - C_J) / 5` white cells at the times `0 .. n - 1`
(`stripJ_white`). The proof telescopes in time with a potential on the strip's own cells, a table
found by shortest paths: `tabJ(next) + 2 J ≤ tabJ(now) + 5 (white cells of the strip)` for every
value of the strip and of the two cells beside it (`stepJ`, by `decide`). Every width `J ≥ 5` is a sum
of the widths 5 to 9, so every strip of at least five columns has lower white density at least
`2/5`; the orbit of `(11001)^∞` attains `2/5` (`StripWhiteDensity.md`).

The natural-language argument is `StripWhiteDensity.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open
namespace StripWhiteDensity

open Ruliology.CellularAutomata.Rule30Jen

/-- `1` for a white cell. -/
def wh (b : Bool) : Nat := if b then 0 else 1

/-- The bit `1` for a black cell. -/
def bit (b : Bool) : Nat := if b then 1 else 0

/-- One Rule 30 step of a row. -/
def step (x : Int → Bool) : Int → Bool := fun p => rule (x (p - 1)) (x p) (x (p + 1))

/-- An orbit of Rule 30: any sequence of rows, each the image of the one before. -/
def IsOrbit (f : Nat → Int → Bool) : Prop := ∀ t, f (t + 1) = step (f t)

theorem nxt (f : Nat → Int → Bool) (hf : IsOrbit f) (n : Nat) (a : Int) (i : Nat) :
    f (n + 1) (a + (i : Int)) = rule (f n (a + (i : Int) - 1)) (f n (a + (i : Int))) (f n (a + (i : Int) + 1)) := by
  rw [hf n]; rfl

/-! ### Width 5 -/

/-- The potential table for width 5, indexed by the strip read from the left as a binary number. -/
def tab5 : List Nat := [0, 5, 5, 10, 5, 10, 10, 10, 5, 10, 10, 10, 10, 10, 10, 10, 0, 5, 5, 10, 5, 10, 10, 10, 5, 10, 10, 10, 10, 10, 10, 10]

/-- The potential of a strip of width 5. -/
def phi5 (b0 b1 b2 b3 b4 : Bool) : Nat := tab5.getD (16 * bit b0 + 8 * bit b1 + 4 * bit b2 + 2 * bit b3 + 1 * bit b4) 0

theorem phi5_le (b0 b1 b2 b3 b4 : Bool) : phi5 b0 b1 b2 b3 b4 ≤ 10 := by
  revert b0 b1 b2 b3 b4
  decide

/-- **One step for width 5**, whatever the cells `l` and `r` beside the strip. -/
theorem step5 (l b0 b1 b2 b3 b4 r : Bool) :
    phi5 (rule l b0 b1) (rule b0 b1 b2) (rule b1 b2 b3) (rule b2 b3 b4) (rule b3 b4 r) + 10 ≤ phi5 b0 b1 b2 b3 b4 + 5 * (wh b0 + wh b1 + wh b2 + wh b3 + wh b4) := by
  revert l b0 b1 b2 b3 b4 r
  decide

/-- White cells of the columns `a .. a + 4` at the times `0 .. n - 1`. -/
def W5 (f : Nat → Int → Bool) (a : Int) : Nat → Nat
  | 0 => 0
  | n + 1 => W5 f a n + (wh (f n (a + (0 : Nat))) + wh (f n (a + (1 : Nat))) + wh (f n (a + (2 : Nat))) + wh (f n (a + (3 : Nat))) + wh (f n (a + (4 : Nat))))

/-- The potential at time `n`. -/
def pot5 (f : Nat → Int → Bool) (a : Int) (n : Nat) : Nat := phi5 (f n (a + (0 : Nat))) (f n (a + (1 : Nat))) (f n (a + (2 : Nat))) (f n (a + (3 : Nat))) (f n (a + (4 : Nat)))

theorem aux5 (f : Nat → Int → Bool) (hf : IsOrbit f) (a : Int) :
    ∀ n, 10 * n + pot5 f a n ≤ pot5 f a 0 + 5 * W5 f a n
  | 0 => by simp [W5]
  | n + 1 => by
    have ih := aux5 f hf a n
    have h := step5 (f n (a + (0 : Nat) - 1)) (f n (a + (0 : Nat))) (f n (a + (1 : Nat))) (f n (a + (2 : Nat))) (f n (a + (3 : Nat))) (f n (a + (4 : Nat))) (f n (a + (4 : Nat) + 1))
    have hp : pot5 f a (n + 1) = phi5 (rule (f n (a + (0 : Nat) - 1)) (f n (a + (0 : Nat))) (f n (a + (0 : Nat) + 1))) (rule (f n (a + (1 : Nat) - 1)) (f n (a + (1 : Nat))) (f n (a + (1 : Nat) + 1))) (rule (f n (a + (2 : Nat) - 1)) (f n (a + (2 : Nat))) (f n (a + (2 : Nat) + 1))) (rule (f n (a + (3 : Nat) - 1)) (f n (a + (3 : Nat))) (f n (a + (3 : Nat) + 1))) (rule (f n (a + (4 : Nat) - 1)) (f n (a + (4 : Nat))) (f n (a + (4 : Nat) + 1))) := by
      unfold pot5; simp only [nxt f hf n a]
    have e : ∀ i : Nat, f n (a + ((i + 1 : Nat) : Int) - 1) = f n (a + (i : Int)) := fun i => by
      congr 1; omega
    have e' : ∀ i : Nat, f n (a + (i : Int) + 1) = f n (a + ((i + 1 : Nat) : Int)) := fun i => by
      congr 1; omega
    simp only [e, e'] at hp
    unfold pot5 at ih
    simp only [W5]
    unfold pot5 at hp
    omega

/-- **Every strip of 5 adjacent columns of every orbit**: `5 W ≥ 10 n - 10`. -/
theorem strip5_white (f : Nat → Int → Bool) (hf : IsOrbit f) (a : Int) (n : Nat) :
    10 * n ≤ 5 * W5 f a n + 10 := by
  have h := aux5 f hf a n
  have : pot5 f a 0 ≤ 10 := phi5_le _ _ _ _ _
  omega

end StripWhiteDensity
end Rule30Open
