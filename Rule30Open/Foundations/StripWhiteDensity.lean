module

public import Ruliology.CellularAutomata.Rule30Jen

/-!
# Strips of five to nine adjacent columns of every orbit are at least 2/5 white

For `J = 5, 6, 7, 8, 9`, in every orbit of Rule 30 (any initial row), the strip of columns
`a .. a + J - 1` has at least `(2 J n - C_J) / 5` white cells at the times `0 .. n - 1`
(`stripJ_white`). The proof telescopes in time with a potential on the strip's own cells, a table
found by shortest paths: `tabJ(next) + 2 J ≤ tabJ(now) + 5 (white cells of the strip)` for every
value of the strip and of the two cells beside it (`stepJ`, by `decide`). Splitting off strips of
width 5, every strip of `J ≥ 5` columns has `5 W ≥ 2 J (n - 1)` (`strip_white_ge5`), so lower white
density at least `2/5`; the orbit of `(11001)^∞` attains `2/5` (`StripWhiteDensity.md`).

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

set_option maxRecDepth 100000 in
theorem phi5_le (b0 b1 b2 b3 b4 : Bool) : phi5 b0 b1 b2 b3 b4 ≤ 10 := by
  revert b0 b1 b2 b3 b4
  decide

set_option maxRecDepth 100000 in
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
    have hp : pot5 f a (n + 1) = phi5 (rule (f n (a + (0 : Nat) - 1)) (f n (a + (0 : Nat))) (f n (a + (1 : Nat)))) (rule (f n (a + (0 : Nat))) (f n (a + (1 : Nat))) (f n (a + (2 : Nat)))) (rule (f n (a + (1 : Nat))) (f n (a + (2 : Nat))) (f n (a + (3 : Nat)))) (rule (f n (a + (2 : Nat))) (f n (a + (3 : Nat))) (f n (a + (4 : Nat)))) (rule (f n (a + (3 : Nat))) (f n (a + (4 : Nat))) (f n (a + (4 : Nat) + 1))) := by
      unfold pot5
      have c0 : f (n + 1) (a + (0 : Nat)) = rule (f n (a + (0 : Nat) - 1)) (f n (a + (0 : Nat))) (f n (a + (1 : Nat))) := by
        rw [nxt f hf n a 0]
        have v : a + ((0 : Nat) : Int) + 1 = a + ((1 : Nat) : Int) := by omega
        rw [v]
      have c1 : f (n + 1) (a + (1 : Nat)) = rule (f n (a + (0 : Nat))) (f n (a + (1 : Nat))) (f n (a + (2 : Nat))) := by
        rw [nxt f hf n a 1]
        have u : a + ((1 : Nat) : Int) - 1 = a + ((0 : Nat) : Int) := by omega
        have v : a + ((1 : Nat) : Int) + 1 = a + ((2 : Nat) : Int) := by omega
        rw [u, v]
      have c2 : f (n + 1) (a + (2 : Nat)) = rule (f n (a + (1 : Nat))) (f n (a + (2 : Nat))) (f n (a + (3 : Nat))) := by
        rw [nxt f hf n a 2]
        have u : a + ((2 : Nat) : Int) - 1 = a + ((1 : Nat) : Int) := by omega
        have v : a + ((2 : Nat) : Int) + 1 = a + ((3 : Nat) : Int) := by omega
        rw [u, v]
      have c3 : f (n + 1) (a + (3 : Nat)) = rule (f n (a + (2 : Nat))) (f n (a + (3 : Nat))) (f n (a + (4 : Nat))) := by
        rw [nxt f hf n a 3]
        have u : a + ((3 : Nat) : Int) - 1 = a + ((2 : Nat) : Int) := by omega
        have v : a + ((3 : Nat) : Int) + 1 = a + ((4 : Nat) : Int) := by omega
        rw [u, v]
      have c4 : f (n + 1) (a + (4 : Nat)) = rule (f n (a + (3 : Nat))) (f n (a + (4 : Nat))) (f n (a + (4 : Nat) + 1)) := by
        rw [nxt f hf n a 4]
        have u : a + ((4 : Nat) : Int) - 1 = a + ((3 : Nat) : Int) := by omega
        rw [u]
      rw [c0,c1,c2,c3,c4]
    have hq : pot5 f a n = phi5 (f n (a + (0 : Nat))) (f n (a + (1 : Nat))) (f n (a + (2 : Nat))) (f n (a + (3 : Nat))) (f n (a + (4 : Nat))) := rfl
    simp only [W5]
    omega

/-- **Every strip of 5 adjacent columns of every orbit**: `5 W ≥ 10 n - 10`. -/
theorem strip5_white (f : Nat → Int → Bool) (hf : IsOrbit f) (a : Int) (n : Nat) :
    10 * n ≤ 5 * W5 f a n + 10 := by
  have h := aux5 f hf a n
  have : pot5 f a 0 ≤ 10 := phi5_le _ _ _ _ _
  omega

/-! ### Width 6 -/

/-- The potential table for width 6, indexed by the strip read from the left as a binary number. -/
def tab6 : List Nat := [0, 3, 5, 6, 5, 7, 12, 10, 3, 7, 9, 11, 11, 11, 9, 10, 5, 8, 10, 11, 10, 12, 9, 12, 8, 12, 12, 12, 8, 10, 12, 12, 0, 3, 5, 6, 5, 7, 12, 10, 3, 7, 9, 11, 11, 11, 9, 10, 5, 8, 10, 11, 10, 12, 9, 12, 8, 12, 12, 12, 8, 10, 12, 12]

/-- The potential of a strip of width 6. -/
def phi6 (b0 b1 b2 b3 b4 b5 : Bool) : Nat := tab6.getD (32 * bit b0 + 16 * bit b1 + 8 * bit b2 + 4 * bit b3 + 2 * bit b4 + 1 * bit b5) 0

set_option maxRecDepth 100000 in
theorem phi6_le (b0 b1 b2 b3 b4 b5 : Bool) : phi6 b0 b1 b2 b3 b4 b5 ≤ 12 := by
  revert b0 b1 b2 b3 b4 b5
  decide

set_option maxRecDepth 100000 in
/-- **One step for width 6**, whatever the cells `l` and `r` beside the strip. -/
theorem step6 (l b0 b1 b2 b3 b4 b5 r : Bool) :
    phi6 (rule l b0 b1) (rule b0 b1 b2) (rule b1 b2 b3) (rule b2 b3 b4) (rule b3 b4 b5) (rule b4 b5 r) + 12 ≤ phi6 b0 b1 b2 b3 b4 b5 + 5 * (wh b0 + wh b1 + wh b2 + wh b3 + wh b4 + wh b5) := by
  revert l b0 b1 b2 b3 b4 b5 r
  decide

/-- White cells of the columns `a .. a + 5` at the times `0 .. n - 1`. -/
def W6 (f : Nat → Int → Bool) (a : Int) : Nat → Nat
  | 0 => 0
  | n + 1 => W6 f a n + (wh (f n (a + (0 : Nat))) + wh (f n (a + (1 : Nat))) + wh (f n (a + (2 : Nat))) + wh (f n (a + (3 : Nat))) + wh (f n (a + (4 : Nat))) + wh (f n (a + (5 : Nat))))

/-- The potential at time `n`. -/
def pot6 (f : Nat → Int → Bool) (a : Int) (n : Nat) : Nat := phi6 (f n (a + (0 : Nat))) (f n (a + (1 : Nat))) (f n (a + (2 : Nat))) (f n (a + (3 : Nat))) (f n (a + (4 : Nat))) (f n (a + (5 : Nat)))

theorem aux6 (f : Nat → Int → Bool) (hf : IsOrbit f) (a : Int) :
    ∀ n, 12 * n + pot6 f a n ≤ pot6 f a 0 + 5 * W6 f a n
  | 0 => by simp [W6]
  | n + 1 => by
    have ih := aux6 f hf a n
    have h := step6 (f n (a + (0 : Nat) - 1)) (f n (a + (0 : Nat))) (f n (a + (1 : Nat))) (f n (a + (2 : Nat))) (f n (a + (3 : Nat))) (f n (a + (4 : Nat))) (f n (a + (5 : Nat))) (f n (a + (5 : Nat) + 1))
    have hp : pot6 f a (n + 1) = phi6 (rule (f n (a + (0 : Nat) - 1)) (f n (a + (0 : Nat))) (f n (a + (1 : Nat)))) (rule (f n (a + (0 : Nat))) (f n (a + (1 : Nat))) (f n (a + (2 : Nat)))) (rule (f n (a + (1 : Nat))) (f n (a + (2 : Nat))) (f n (a + (3 : Nat)))) (rule (f n (a + (2 : Nat))) (f n (a + (3 : Nat))) (f n (a + (4 : Nat)))) (rule (f n (a + (3 : Nat))) (f n (a + (4 : Nat))) (f n (a + (5 : Nat)))) (rule (f n (a + (4 : Nat))) (f n (a + (5 : Nat))) (f n (a + (5 : Nat) + 1))) := by
      unfold pot6
      have c0 : f (n + 1) (a + (0 : Nat)) = rule (f n (a + (0 : Nat) - 1)) (f n (a + (0 : Nat))) (f n (a + (1 : Nat))) := by
        rw [nxt f hf n a 0]
        have v : a + ((0 : Nat) : Int) + 1 = a + ((1 : Nat) : Int) := by omega
        rw [v]
      have c1 : f (n + 1) (a + (1 : Nat)) = rule (f n (a + (0 : Nat))) (f n (a + (1 : Nat))) (f n (a + (2 : Nat))) := by
        rw [nxt f hf n a 1]
        have u : a + ((1 : Nat) : Int) - 1 = a + ((0 : Nat) : Int) := by omega
        have v : a + ((1 : Nat) : Int) + 1 = a + ((2 : Nat) : Int) := by omega
        rw [u, v]
      have c2 : f (n + 1) (a + (2 : Nat)) = rule (f n (a + (1 : Nat))) (f n (a + (2 : Nat))) (f n (a + (3 : Nat))) := by
        rw [nxt f hf n a 2]
        have u : a + ((2 : Nat) : Int) - 1 = a + ((1 : Nat) : Int) := by omega
        have v : a + ((2 : Nat) : Int) + 1 = a + ((3 : Nat) : Int) := by omega
        rw [u, v]
      have c3 : f (n + 1) (a + (3 : Nat)) = rule (f n (a + (2 : Nat))) (f n (a + (3 : Nat))) (f n (a + (4 : Nat))) := by
        rw [nxt f hf n a 3]
        have u : a + ((3 : Nat) : Int) - 1 = a + ((2 : Nat) : Int) := by omega
        have v : a + ((3 : Nat) : Int) + 1 = a + ((4 : Nat) : Int) := by omega
        rw [u, v]
      have c4 : f (n + 1) (a + (4 : Nat)) = rule (f n (a + (3 : Nat))) (f n (a + (4 : Nat))) (f n (a + (5 : Nat))) := by
        rw [nxt f hf n a 4]
        have u : a + ((4 : Nat) : Int) - 1 = a + ((3 : Nat) : Int) := by omega
        have v : a + ((4 : Nat) : Int) + 1 = a + ((5 : Nat) : Int) := by omega
        rw [u, v]
      have c5 : f (n + 1) (a + (5 : Nat)) = rule (f n (a + (4 : Nat))) (f n (a + (5 : Nat))) (f n (a + (5 : Nat) + 1)) := by
        rw [nxt f hf n a 5]
        have u : a + ((5 : Nat) : Int) - 1 = a + ((4 : Nat) : Int) := by omega
        rw [u]
      rw [c0,c1,c2,c3,c4,c5]
    have hq : pot6 f a n = phi6 (f n (a + (0 : Nat))) (f n (a + (1 : Nat))) (f n (a + (2 : Nat))) (f n (a + (3 : Nat))) (f n (a + (4 : Nat))) (f n (a + (5 : Nat))) := rfl
    simp only [W6]
    omega

/-- **Every strip of 6 adjacent columns of every orbit**: `5 W ≥ 12 n - 12`. -/
theorem strip6_white (f : Nat → Int → Bool) (hf : IsOrbit f) (a : Int) (n : Nat) :
    12 * n ≤ 5 * W6 f a n + 12 := by
  have h := aux6 f hf a n
  have : pot6 f a 0 ≤ 12 := phi6_le _ _ _ _ _ _
  omega

/-! ### Width 7 -/

/-- The potential table for width 7, indexed by the strip read from the left as a binary number. -/
def tab7 : List Nat := [0, 5, 5, 6, 5, 10, 14, 7, 5, 10, 9, 9, 13, 14, 10, 14, 5, 6, 8, 9, 10, 13, 12, 14, 14, 14, 14, 12, 8, 13, 10, 14, 5, 10, 10, 11, 10, 14, 12, 12, 10, 14, 14, 14, 8, 14, 14, 14, 10, 11, 13, 14, 14, 14, 14, 14, 10, 11, 10, 14, 13, 14, 14, 14, 0, 5, 5, 6, 5, 10, 14, 7, 5, 10, 9, 9, 13, 14, 10, 14, 5, 6, 8, 9, 10, 13, 12, 14, 14, 14, 14, 12, 8, 13, 10, 14, 5, 10, 10, 11, 10, 14, 12, 12, 10, 14, 14, 14, 8, 14, 14, 14, 10, 11, 13, 14, 14, 14, 14, 14, 10, 11, 10, 14, 13, 14, 14, 14]

/-- The potential of a strip of width 7. -/
def phi7 (b0 b1 b2 b3 b4 b5 b6 : Bool) : Nat := tab7.getD (64 * bit b0 + 32 * bit b1 + 16 * bit b2 + 8 * bit b3 + 4 * bit b4 + 2 * bit b5 + 1 * bit b6) 0

set_option maxRecDepth 100000 in
theorem phi7_le (b0 b1 b2 b3 b4 b5 b6 : Bool) : phi7 b0 b1 b2 b3 b4 b5 b6 ≤ 14 := by
  revert b0 b1 b2 b3 b4 b5 b6
  decide

set_option maxRecDepth 100000 in
/-- **One step for width 7**, whatever the cells `l` and `r` beside the strip. -/
theorem step7 (l b0 b1 b2 b3 b4 b5 b6 r : Bool) :
    phi7 (rule l b0 b1) (rule b0 b1 b2) (rule b1 b2 b3) (rule b2 b3 b4) (rule b3 b4 b5) (rule b4 b5 b6) (rule b5 b6 r) + 14 ≤ phi7 b0 b1 b2 b3 b4 b5 b6 + 5 * (wh b0 + wh b1 + wh b2 + wh b3 + wh b4 + wh b5 + wh b6) := by
  revert l b0 b1 b2 b3 b4 b5 b6 r
  decide

/-- White cells of the columns `a .. a + 6` at the times `0 .. n - 1`. -/
def W7 (f : Nat → Int → Bool) (a : Int) : Nat → Nat
  | 0 => 0
  | n + 1 => W7 f a n + (wh (f n (a + (0 : Nat))) + wh (f n (a + (1 : Nat))) + wh (f n (a + (2 : Nat))) + wh (f n (a + (3 : Nat))) + wh (f n (a + (4 : Nat))) + wh (f n (a + (5 : Nat))) + wh (f n (a + (6 : Nat))))

/-- The potential at time `n`. -/
def pot7 (f : Nat → Int → Bool) (a : Int) (n : Nat) : Nat := phi7 (f n (a + (0 : Nat))) (f n (a + (1 : Nat))) (f n (a + (2 : Nat))) (f n (a + (3 : Nat))) (f n (a + (4 : Nat))) (f n (a + (5 : Nat))) (f n (a + (6 : Nat)))

theorem aux7 (f : Nat → Int → Bool) (hf : IsOrbit f) (a : Int) :
    ∀ n, 14 * n + pot7 f a n ≤ pot7 f a 0 + 5 * W7 f a n
  | 0 => by simp [W7]
  | n + 1 => by
    have ih := aux7 f hf a n
    have h := step7 (f n (a + (0 : Nat) - 1)) (f n (a + (0 : Nat))) (f n (a + (1 : Nat))) (f n (a + (2 : Nat))) (f n (a + (3 : Nat))) (f n (a + (4 : Nat))) (f n (a + (5 : Nat))) (f n (a + (6 : Nat))) (f n (a + (6 : Nat) + 1))
    have hp : pot7 f a (n + 1) = phi7 (rule (f n (a + (0 : Nat) - 1)) (f n (a + (0 : Nat))) (f n (a + (1 : Nat)))) (rule (f n (a + (0 : Nat))) (f n (a + (1 : Nat))) (f n (a + (2 : Nat)))) (rule (f n (a + (1 : Nat))) (f n (a + (2 : Nat))) (f n (a + (3 : Nat)))) (rule (f n (a + (2 : Nat))) (f n (a + (3 : Nat))) (f n (a + (4 : Nat)))) (rule (f n (a + (3 : Nat))) (f n (a + (4 : Nat))) (f n (a + (5 : Nat)))) (rule (f n (a + (4 : Nat))) (f n (a + (5 : Nat))) (f n (a + (6 : Nat)))) (rule (f n (a + (5 : Nat))) (f n (a + (6 : Nat))) (f n (a + (6 : Nat) + 1))) := by
      unfold pot7
      have c0 : f (n + 1) (a + (0 : Nat)) = rule (f n (a + (0 : Nat) - 1)) (f n (a + (0 : Nat))) (f n (a + (1 : Nat))) := by
        rw [nxt f hf n a 0]
        have v : a + ((0 : Nat) : Int) + 1 = a + ((1 : Nat) : Int) := by omega
        rw [v]
      have c1 : f (n + 1) (a + (1 : Nat)) = rule (f n (a + (0 : Nat))) (f n (a + (1 : Nat))) (f n (a + (2 : Nat))) := by
        rw [nxt f hf n a 1]
        have u : a + ((1 : Nat) : Int) - 1 = a + ((0 : Nat) : Int) := by omega
        have v : a + ((1 : Nat) : Int) + 1 = a + ((2 : Nat) : Int) := by omega
        rw [u, v]
      have c2 : f (n + 1) (a + (2 : Nat)) = rule (f n (a + (1 : Nat))) (f n (a + (2 : Nat))) (f n (a + (3 : Nat))) := by
        rw [nxt f hf n a 2]
        have u : a + ((2 : Nat) : Int) - 1 = a + ((1 : Nat) : Int) := by omega
        have v : a + ((2 : Nat) : Int) + 1 = a + ((3 : Nat) : Int) := by omega
        rw [u, v]
      have c3 : f (n + 1) (a + (3 : Nat)) = rule (f n (a + (2 : Nat))) (f n (a + (3 : Nat))) (f n (a + (4 : Nat))) := by
        rw [nxt f hf n a 3]
        have u : a + ((3 : Nat) : Int) - 1 = a + ((2 : Nat) : Int) := by omega
        have v : a + ((3 : Nat) : Int) + 1 = a + ((4 : Nat) : Int) := by omega
        rw [u, v]
      have c4 : f (n + 1) (a + (4 : Nat)) = rule (f n (a + (3 : Nat))) (f n (a + (4 : Nat))) (f n (a + (5 : Nat))) := by
        rw [nxt f hf n a 4]
        have u : a + ((4 : Nat) : Int) - 1 = a + ((3 : Nat) : Int) := by omega
        have v : a + ((4 : Nat) : Int) + 1 = a + ((5 : Nat) : Int) := by omega
        rw [u, v]
      have c5 : f (n + 1) (a + (5 : Nat)) = rule (f n (a + (4 : Nat))) (f n (a + (5 : Nat))) (f n (a + (6 : Nat))) := by
        rw [nxt f hf n a 5]
        have u : a + ((5 : Nat) : Int) - 1 = a + ((4 : Nat) : Int) := by omega
        have v : a + ((5 : Nat) : Int) + 1 = a + ((6 : Nat) : Int) := by omega
        rw [u, v]
      have c6 : f (n + 1) (a + (6 : Nat)) = rule (f n (a + (5 : Nat))) (f n (a + (6 : Nat))) (f n (a + (6 : Nat) + 1)) := by
        rw [nxt f hf n a 6]
        have u : a + ((6 : Nat) : Int) - 1 = a + ((5 : Nat) : Int) := by omega
        rw [u]
      rw [c0,c1,c2,c3,c4,c5,c6]
    have hq : pot7 f a n = phi7 (f n (a + (0 : Nat))) (f n (a + (1 : Nat))) (f n (a + (2 : Nat))) (f n (a + (3 : Nat))) (f n (a + (4 : Nat))) (f n (a + (5 : Nat))) (f n (a + (6 : Nat))) := rfl
    simp only [W7]
    omega

/-- **Every strip of 7 adjacent columns of every orbit**: `5 W ≥ 14 n - 14`. -/
theorem strip7_white (f : Nat → Int → Bool) (hf : IsOrbit f) (a : Int) (n : Nat) :
    14 * n ≤ 5 * W7 f a n + 14 := by
  have h := aux7 f hf a n
  have : pot7 f a 0 ≤ 14 := phi7_le _ _ _ _ _ _ _
  omega

/-! ### Width 8 -/

/-- The potential table for width 8, indexed by the strip read from the left as a binary number. -/
def tab8 : List Nat := [0, 5, 5, 9, 5, 10, 9, 9, 5, 10, 10, 13, 16, 16, 8, 13, 5, 10, 10, 14, 10, 15, 13, 11, 16, 16, 16, 16, 10, 15, 15, 16, 5, 10, 9, 9, 10, 12, 16, 11, 10, 14, 15, 16, 13, 16, 15, 16, 15, 16, 16, 16, 15, 16, 13, 16, 10, 12, 15, 16, 10, 16, 16, 16, 5, 10, 10, 14, 10, 15, 14, 14, 10, 15, 15, 16, 13, 16, 13, 16, 10, 15, 15, 16, 15, 16, 16, 16, 12, 12, 16, 16, 15, 16, 16, 16, 10, 15, 14, 14, 15, 16, 16, 16, 15, 16, 16, 16, 16, 16, 16, 16, 10, 14, 14, 14, 10, 16, 16, 16, 15, 16, 16, 16, 15, 16, 16, 16, 0, 5, 5, 9, 5, 10, 9, 9, 5, 10, 10, 13, 16, 16, 8, 13, 5, 10, 10, 14, 10, 15, 13, 11, 16, 16, 16, 16, 10, 15, 15, 16, 5, 10, 9, 9, 10, 12, 16, 11, 10, 14, 15, 16, 13, 16, 15, 16, 15, 16, 16, 16, 15, 16, 13, 16, 10, 12, 15, 16, 10, 16, 16, 16, 5, 10, 10, 14, 10, 15, 14, 14, 10, 15, 15, 16, 13, 16, 13, 16, 10, 15, 15, 16, 15, 16, 16, 16, 12, 12, 16, 16, 15, 16, 16, 16, 10, 15, 14, 14, 15, 16, 16, 16, 15, 16, 16, 16, 16, 16, 16, 16, 10, 14, 14, 14, 10, 16, 16, 16, 15, 16, 16, 16, 15, 16, 16, 16]

/-- The potential of a strip of width 8. -/
def phi8 (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) : Nat := tab8.getD (128 * bit b0 + 64 * bit b1 + 32 * bit b2 + 16 * bit b3 + 8 * bit b4 + 4 * bit b5 + 2 * bit b6 + 1 * bit b7) 0

set_option maxRecDepth 100000 in
theorem phi8_le (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) : phi8 b0 b1 b2 b3 b4 b5 b6 b7 ≤ 16 := by
  revert b0 b1 b2 b3 b4 b5 b6 b7
  decide

set_option maxRecDepth 100000 in
/-- **One step for width 8**, whatever the cells `l` and `r` beside the strip. -/
theorem step8 (l b0 b1 b2 b3 b4 b5 b6 b7 r : Bool) :
    phi8 (rule l b0 b1) (rule b0 b1 b2) (rule b1 b2 b3) (rule b2 b3 b4) (rule b3 b4 b5) (rule b4 b5 b6) (rule b5 b6 b7) (rule b6 b7 r) + 16 ≤ phi8 b0 b1 b2 b3 b4 b5 b6 b7 + 5 * (wh b0 + wh b1 + wh b2 + wh b3 + wh b4 + wh b5 + wh b6 + wh b7) := by
  revert l b0 b1 b2 b3 b4 b5 b6 b7 r
  decide

/-- White cells of the columns `a .. a + 7` at the times `0 .. n - 1`. -/
def W8 (f : Nat → Int → Bool) (a : Int) : Nat → Nat
  | 0 => 0
  | n + 1 => W8 f a n + (wh (f n (a + (0 : Nat))) + wh (f n (a + (1 : Nat))) + wh (f n (a + (2 : Nat))) + wh (f n (a + (3 : Nat))) + wh (f n (a + (4 : Nat))) + wh (f n (a + (5 : Nat))) + wh (f n (a + (6 : Nat))) + wh (f n (a + (7 : Nat))))

/-- The potential at time `n`. -/
def pot8 (f : Nat → Int → Bool) (a : Int) (n : Nat) : Nat := phi8 (f n (a + (0 : Nat))) (f n (a + (1 : Nat))) (f n (a + (2 : Nat))) (f n (a + (3 : Nat))) (f n (a + (4 : Nat))) (f n (a + (5 : Nat))) (f n (a + (6 : Nat))) (f n (a + (7 : Nat)))

theorem aux8 (f : Nat → Int → Bool) (hf : IsOrbit f) (a : Int) :
    ∀ n, 16 * n + pot8 f a n ≤ pot8 f a 0 + 5 * W8 f a n
  | 0 => by simp [W8]
  | n + 1 => by
    have ih := aux8 f hf a n
    have h := step8 (f n (a + (0 : Nat) - 1)) (f n (a + (0 : Nat))) (f n (a + (1 : Nat))) (f n (a + (2 : Nat))) (f n (a + (3 : Nat))) (f n (a + (4 : Nat))) (f n (a + (5 : Nat))) (f n (a + (6 : Nat))) (f n (a + (7 : Nat))) (f n (a + (7 : Nat) + 1))
    have hp : pot8 f a (n + 1) = phi8 (rule (f n (a + (0 : Nat) - 1)) (f n (a + (0 : Nat))) (f n (a + (1 : Nat)))) (rule (f n (a + (0 : Nat))) (f n (a + (1 : Nat))) (f n (a + (2 : Nat)))) (rule (f n (a + (1 : Nat))) (f n (a + (2 : Nat))) (f n (a + (3 : Nat)))) (rule (f n (a + (2 : Nat))) (f n (a + (3 : Nat))) (f n (a + (4 : Nat)))) (rule (f n (a + (3 : Nat))) (f n (a + (4 : Nat))) (f n (a + (5 : Nat)))) (rule (f n (a + (4 : Nat))) (f n (a + (5 : Nat))) (f n (a + (6 : Nat)))) (rule (f n (a + (5 : Nat))) (f n (a + (6 : Nat))) (f n (a + (7 : Nat)))) (rule (f n (a + (6 : Nat))) (f n (a + (7 : Nat))) (f n (a + (7 : Nat) + 1))) := by
      unfold pot8
      have c0 : f (n + 1) (a + (0 : Nat)) = rule (f n (a + (0 : Nat) - 1)) (f n (a + (0 : Nat))) (f n (a + (1 : Nat))) := by
        rw [nxt f hf n a 0]
        have v : a + ((0 : Nat) : Int) + 1 = a + ((1 : Nat) : Int) := by omega
        rw [v]
      have c1 : f (n + 1) (a + (1 : Nat)) = rule (f n (a + (0 : Nat))) (f n (a + (1 : Nat))) (f n (a + (2 : Nat))) := by
        rw [nxt f hf n a 1]
        have u : a + ((1 : Nat) : Int) - 1 = a + ((0 : Nat) : Int) := by omega
        have v : a + ((1 : Nat) : Int) + 1 = a + ((2 : Nat) : Int) := by omega
        rw [u, v]
      have c2 : f (n + 1) (a + (2 : Nat)) = rule (f n (a + (1 : Nat))) (f n (a + (2 : Nat))) (f n (a + (3 : Nat))) := by
        rw [nxt f hf n a 2]
        have u : a + ((2 : Nat) : Int) - 1 = a + ((1 : Nat) : Int) := by omega
        have v : a + ((2 : Nat) : Int) + 1 = a + ((3 : Nat) : Int) := by omega
        rw [u, v]
      have c3 : f (n + 1) (a + (3 : Nat)) = rule (f n (a + (2 : Nat))) (f n (a + (3 : Nat))) (f n (a + (4 : Nat))) := by
        rw [nxt f hf n a 3]
        have u : a + ((3 : Nat) : Int) - 1 = a + ((2 : Nat) : Int) := by omega
        have v : a + ((3 : Nat) : Int) + 1 = a + ((4 : Nat) : Int) := by omega
        rw [u, v]
      have c4 : f (n + 1) (a + (4 : Nat)) = rule (f n (a + (3 : Nat))) (f n (a + (4 : Nat))) (f n (a + (5 : Nat))) := by
        rw [nxt f hf n a 4]
        have u : a + ((4 : Nat) : Int) - 1 = a + ((3 : Nat) : Int) := by omega
        have v : a + ((4 : Nat) : Int) + 1 = a + ((5 : Nat) : Int) := by omega
        rw [u, v]
      have c5 : f (n + 1) (a + (5 : Nat)) = rule (f n (a + (4 : Nat))) (f n (a + (5 : Nat))) (f n (a + (6 : Nat))) := by
        rw [nxt f hf n a 5]
        have u : a + ((5 : Nat) : Int) - 1 = a + ((4 : Nat) : Int) := by omega
        have v : a + ((5 : Nat) : Int) + 1 = a + ((6 : Nat) : Int) := by omega
        rw [u, v]
      have c6 : f (n + 1) (a + (6 : Nat)) = rule (f n (a + (5 : Nat))) (f n (a + (6 : Nat))) (f n (a + (7 : Nat))) := by
        rw [nxt f hf n a 6]
        have u : a + ((6 : Nat) : Int) - 1 = a + ((5 : Nat) : Int) := by omega
        have v : a + ((6 : Nat) : Int) + 1 = a + ((7 : Nat) : Int) := by omega
        rw [u, v]
      have c7 : f (n + 1) (a + (7 : Nat)) = rule (f n (a + (6 : Nat))) (f n (a + (7 : Nat))) (f n (a + (7 : Nat) + 1)) := by
        rw [nxt f hf n a 7]
        have u : a + ((7 : Nat) : Int) - 1 = a + ((6 : Nat) : Int) := by omega
        rw [u]
      rw [c0,c1,c2,c3,c4,c5,c6,c7]
    have hq : pot8 f a n = phi8 (f n (a + (0 : Nat))) (f n (a + (1 : Nat))) (f n (a + (2 : Nat))) (f n (a + (3 : Nat))) (f n (a + (4 : Nat))) (f n (a + (5 : Nat))) (f n (a + (6 : Nat))) (f n (a + (7 : Nat))) := rfl
    simp only [W8]
    omega

/-- **Every strip of 8 adjacent columns of every orbit**: `5 W ≥ 16 n - 16`. -/
theorem strip8_white (f : Nat → Int → Bool) (hf : IsOrbit f) (a : Int) (n : Nat) :
    16 * n ≤ 5 * W8 f a n + 16 := by
  have h := aux8 f hf a n
  have : pot8 f a 0 ≤ 16 := phi8_le _ _ _ _ _ _ _ _
  omega

/-! ### Width 9 -/

/-- The potential table for width 9, indexed by the strip read from the left as a binary number. -/
def tab9 : List Nat := [0, 5, 5, 9, 5, 10, 15, 10, 5, 10, 10, 15, 17, 17, 10, 12, 5, 10, 10, 15, 10, 15, 14, 15, 18, 18, 18, 18, 9, 14, 15, 17, 5, 10, 10, 15, 10, 15, 18, 15, 10, 15, 15, 18, 14, 18, 13, 18, 18, 18, 18, 18, 18, 18, 18, 18, 10, 15, 15, 18, 15, 18, 18, 18, 5, 10, 10, 15, 10, 15, 17, 12, 10, 15, 15, 16, 17, 18, 13, 17, 10, 15, 15, 17, 15, 18, 18, 18, 14, 17, 18, 18, 15, 18, 18, 18, 15, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 14, 18, 18, 18, 10, 15, 15, 16, 15, 18, 18, 18, 14, 15, 18, 18, 18, 18, 18, 18, 5, 10, 10, 14, 10, 15, 18, 15, 10, 15, 15, 18, 17, 18, 15, 17, 10, 15, 15, 18, 15, 18, 18, 18, 14, 17, 18, 18, 14, 18, 18, 18, 10, 15, 15, 18, 15, 18, 18, 18, 15, 18, 18, 18, 18, 18, 18, 18, 14, 16, 16, 16, 17, 18, 18, 18, 15, 18, 18, 18, 18, 18, 18, 18, 10, 15, 15, 18, 15, 18, 18, 17, 15, 18, 18, 18, 18, 18, 18, 18, 15, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 10, 15, 15, 17, 15, 17, 18, 17, 15, 15, 18, 18, 18, 18, 18, 18, 15, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 17, 18, 18, 18, 0, 5, 5, 9, 5, 10, 15, 10, 5, 10, 10, 15, 17, 17, 10, 12, 5, 10, 10, 15, 10, 15, 14, 15, 18, 18, 18, 18, 9, 14, 15, 17, 5, 10, 10, 15, 10, 15, 18, 15, 10, 15, 15, 18, 14, 18, 13, 18, 18, 18, 18, 18, 18, 18, 18, 18, 10, 15, 15, 18, 15, 18, 18, 18, 5, 10, 10, 15, 10, 15, 17, 12, 10, 15, 15, 16, 17, 18, 13, 17, 10, 15, 15, 17, 15, 18, 18, 18, 14, 17, 18, 18, 15, 18, 18, 18, 15, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 14, 18, 18, 18, 10, 15, 15, 16, 15, 18, 18, 18, 14, 15, 18, 18, 18, 18, 18, 18, 5, 10, 10, 14, 10, 15, 18, 15, 10, 15, 15, 18, 17, 18, 15, 17, 10, 15, 15, 18, 15, 18, 18, 18, 14, 17, 18, 18, 14, 18, 18, 18, 10, 15, 15, 18, 15, 18, 18, 18, 15, 18, 18, 18, 18, 18, 18, 18, 14, 16, 16, 16, 17, 18, 18, 18, 15, 18, 18, 18, 18, 18, 18, 18, 10, 15, 15, 18, 15, 18, 18, 17, 15, 18, 18, 18, 18, 18, 18, 18, 15, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 10, 15, 15, 17, 15, 17, 18, 17, 15, 15, 18, 18, 18, 18, 18, 18, 15, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 17, 18, 18, 18]

/-- The potential of a strip of width 9. -/
def phi9 (b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool) : Nat := tab9.getD (256 * bit b0 + 128 * bit b1 + 64 * bit b2 + 32 * bit b3 + 16 * bit b4 + 8 * bit b5 + 4 * bit b6 + 2 * bit b7 + 1 * bit b8) 0

set_option maxRecDepth 100000 in
theorem phi9_le (b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool) : phi9 b0 b1 b2 b3 b4 b5 b6 b7 b8 ≤ 18 := by
  revert b0 b1 b2 b3 b4 b5 b6 b7 b8
  decide

set_option maxRecDepth 100000 in
/-- **One step for width 9**, whatever the cells `l` and `r` beside the strip. -/
theorem step9 (l b0 b1 b2 b3 b4 b5 b6 b7 b8 r : Bool) :
    phi9 (rule l b0 b1) (rule b0 b1 b2) (rule b1 b2 b3) (rule b2 b3 b4) (rule b3 b4 b5) (rule b4 b5 b6) (rule b5 b6 b7) (rule b6 b7 b8) (rule b7 b8 r) + 18 ≤ phi9 b0 b1 b2 b3 b4 b5 b6 b7 b8 + 5 * (wh b0 + wh b1 + wh b2 + wh b3 + wh b4 + wh b5 + wh b6 + wh b7 + wh b8) := by
  revert l b0 b1 b2 b3 b4 b5 b6 b7 b8 r
  decide

/-- White cells of the columns `a .. a + 8` at the times `0 .. n - 1`. -/
def W9 (f : Nat → Int → Bool) (a : Int) : Nat → Nat
  | 0 => 0
  | n + 1 => W9 f a n + (wh (f n (a + (0 : Nat))) + wh (f n (a + (1 : Nat))) + wh (f n (a + (2 : Nat))) + wh (f n (a + (3 : Nat))) + wh (f n (a + (4 : Nat))) + wh (f n (a + (5 : Nat))) + wh (f n (a + (6 : Nat))) + wh (f n (a + (7 : Nat))) + wh (f n (a + (8 : Nat))))

/-- The potential at time `n`. -/
def pot9 (f : Nat → Int → Bool) (a : Int) (n : Nat) : Nat := phi9 (f n (a + (0 : Nat))) (f n (a + (1 : Nat))) (f n (a + (2 : Nat))) (f n (a + (3 : Nat))) (f n (a + (4 : Nat))) (f n (a + (5 : Nat))) (f n (a + (6 : Nat))) (f n (a + (7 : Nat))) (f n (a + (8 : Nat)))

theorem aux9 (f : Nat → Int → Bool) (hf : IsOrbit f) (a : Int) :
    ∀ n, 18 * n + pot9 f a n ≤ pot9 f a 0 + 5 * W9 f a n
  | 0 => by simp [W9]
  | n + 1 => by
    have ih := aux9 f hf a n
    have h := step9 (f n (a + (0 : Nat) - 1)) (f n (a + (0 : Nat))) (f n (a + (1 : Nat))) (f n (a + (2 : Nat))) (f n (a + (3 : Nat))) (f n (a + (4 : Nat))) (f n (a + (5 : Nat))) (f n (a + (6 : Nat))) (f n (a + (7 : Nat))) (f n (a + (8 : Nat))) (f n (a + (8 : Nat) + 1))
    have hp : pot9 f a (n + 1) = phi9 (rule (f n (a + (0 : Nat) - 1)) (f n (a + (0 : Nat))) (f n (a + (1 : Nat)))) (rule (f n (a + (0 : Nat))) (f n (a + (1 : Nat))) (f n (a + (2 : Nat)))) (rule (f n (a + (1 : Nat))) (f n (a + (2 : Nat))) (f n (a + (3 : Nat)))) (rule (f n (a + (2 : Nat))) (f n (a + (3 : Nat))) (f n (a + (4 : Nat)))) (rule (f n (a + (3 : Nat))) (f n (a + (4 : Nat))) (f n (a + (5 : Nat)))) (rule (f n (a + (4 : Nat))) (f n (a + (5 : Nat))) (f n (a + (6 : Nat)))) (rule (f n (a + (5 : Nat))) (f n (a + (6 : Nat))) (f n (a + (7 : Nat)))) (rule (f n (a + (6 : Nat))) (f n (a + (7 : Nat))) (f n (a + (8 : Nat)))) (rule (f n (a + (7 : Nat))) (f n (a + (8 : Nat))) (f n (a + (8 : Nat) + 1))) := by
      unfold pot9
      have c0 : f (n + 1) (a + (0 : Nat)) = rule (f n (a + (0 : Nat) - 1)) (f n (a + (0 : Nat))) (f n (a + (1 : Nat))) := by
        rw [nxt f hf n a 0]
        have v : a + ((0 : Nat) : Int) + 1 = a + ((1 : Nat) : Int) := by omega
        rw [v]
      have c1 : f (n + 1) (a + (1 : Nat)) = rule (f n (a + (0 : Nat))) (f n (a + (1 : Nat))) (f n (a + (2 : Nat))) := by
        rw [nxt f hf n a 1]
        have u : a + ((1 : Nat) : Int) - 1 = a + ((0 : Nat) : Int) := by omega
        have v : a + ((1 : Nat) : Int) + 1 = a + ((2 : Nat) : Int) := by omega
        rw [u, v]
      have c2 : f (n + 1) (a + (2 : Nat)) = rule (f n (a + (1 : Nat))) (f n (a + (2 : Nat))) (f n (a + (3 : Nat))) := by
        rw [nxt f hf n a 2]
        have u : a + ((2 : Nat) : Int) - 1 = a + ((1 : Nat) : Int) := by omega
        have v : a + ((2 : Nat) : Int) + 1 = a + ((3 : Nat) : Int) := by omega
        rw [u, v]
      have c3 : f (n + 1) (a + (3 : Nat)) = rule (f n (a + (2 : Nat))) (f n (a + (3 : Nat))) (f n (a + (4 : Nat))) := by
        rw [nxt f hf n a 3]
        have u : a + ((3 : Nat) : Int) - 1 = a + ((2 : Nat) : Int) := by omega
        have v : a + ((3 : Nat) : Int) + 1 = a + ((4 : Nat) : Int) := by omega
        rw [u, v]
      have c4 : f (n + 1) (a + (4 : Nat)) = rule (f n (a + (3 : Nat))) (f n (a + (4 : Nat))) (f n (a + (5 : Nat))) := by
        rw [nxt f hf n a 4]
        have u : a + ((4 : Nat) : Int) - 1 = a + ((3 : Nat) : Int) := by omega
        have v : a + ((4 : Nat) : Int) + 1 = a + ((5 : Nat) : Int) := by omega
        rw [u, v]
      have c5 : f (n + 1) (a + (5 : Nat)) = rule (f n (a + (4 : Nat))) (f n (a + (5 : Nat))) (f n (a + (6 : Nat))) := by
        rw [nxt f hf n a 5]
        have u : a + ((5 : Nat) : Int) - 1 = a + ((4 : Nat) : Int) := by omega
        have v : a + ((5 : Nat) : Int) + 1 = a + ((6 : Nat) : Int) := by omega
        rw [u, v]
      have c6 : f (n + 1) (a + (6 : Nat)) = rule (f n (a + (5 : Nat))) (f n (a + (6 : Nat))) (f n (a + (7 : Nat))) := by
        rw [nxt f hf n a 6]
        have u : a + ((6 : Nat) : Int) - 1 = a + ((5 : Nat) : Int) := by omega
        have v : a + ((6 : Nat) : Int) + 1 = a + ((7 : Nat) : Int) := by omega
        rw [u, v]
      have c7 : f (n + 1) (a + (7 : Nat)) = rule (f n (a + (6 : Nat))) (f n (a + (7 : Nat))) (f n (a + (8 : Nat))) := by
        rw [nxt f hf n a 7]
        have u : a + ((7 : Nat) : Int) - 1 = a + ((6 : Nat) : Int) := by omega
        have v : a + ((7 : Nat) : Int) + 1 = a + ((8 : Nat) : Int) := by omega
        rw [u, v]
      have c8 : f (n + 1) (a + (8 : Nat)) = rule (f n (a + (7 : Nat))) (f n (a + (8 : Nat))) (f n (a + (8 : Nat) + 1)) := by
        rw [nxt f hf n a 8]
        have u : a + ((8 : Nat) : Int) - 1 = a + ((7 : Nat) : Int) := by omega
        rw [u]
      rw [c0,c1,c2,c3,c4,c5,c6,c7,c8]
    have hq : pot9 f a n = phi9 (f n (a + (0 : Nat))) (f n (a + (1 : Nat))) (f n (a + (2 : Nat))) (f n (a + (3 : Nat))) (f n (a + (4 : Nat))) (f n (a + (5 : Nat))) (f n (a + (6 : Nat))) (f n (a + (7 : Nat))) (f n (a + (8 : Nat))) := rfl
    simp only [W9]
    omega

/-- **Every strip of 9 adjacent columns of every orbit**: `5 W ≥ 18 n - 18`. -/
theorem strip9_white (f : Nat → Int → Bool) (hf : IsOrbit f) (a : Int) (n : Nat) :
    18 * n ≤ 5 * W9 f a n + 18 := by
  have h := aux9 f hf a n
  have : pot9 f a 0 ≤ 18 := phi9_le _ _ _ _ _ _ _ _ _
  omega

/-! ### Every width from 5 on -/

/-- White cells of `x` on `a .. a + k - 1`. -/
def rowW (x : Int → Bool) (a : Int) : Nat → Nat
  | 0 => 0
  | k + 1 => rowW x a k + wh (x (a + (k : Int)))

/-- White cells of the columns `a .. a + J - 1` at the times `0 .. n - 1`. -/
def stripW (f : Nat → Int → Bool) (a : Int) (J : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => stripW f a J n + rowW (f n) a J

theorem rowW_add (x : Int → Bool) (a : Int) (J : Nat) :
    ∀ K, rowW x a (J + K) = rowW x a J + rowW x (a + (J : Int)) K
  | 0 => rfl
  | K + 1 => by
    have ih := rowW_add x a J K
    have e : a + ((J + K : Nat) : Int) = a + (J : Int) + (K : Int) := by omega
    show rowW x a (J + K) + wh (x (a + ((J + K : Nat) : Int))) = _
    rw [ih, e]; simp only [rowW]; omega

theorem stripW_add (f : Nat → Int → Bool) (a : Int) (J K : Nat) :
    ∀ n, stripW f a (J + K) n = stripW f a J n + stripW f (a + (J : Int)) K n
  | 0 => rfl
  | n + 1 => by
    have ih := stripW_add f a J K n
    simp only [stripW, ih, rowW_add]; omega

theorem stripW_5 (f : Nat → Int → Bool) (a : Int) : ∀ n, stripW f a 5 n = W5 f a n
  | 0 => rfl
  | n + 1 => by
    have ih := stripW_5 f a n
    simp only [stripW, W5, ih, rowW]
    omega

theorem stripW_6 (f : Nat → Int → Bool) (a : Int) : ∀ n, stripW f a 6 n = W6 f a n
  | 0 => rfl
  | n + 1 => by
    have ih := stripW_6 f a n
    simp only [stripW, W6, ih, rowW]
    omega

theorem stripW_7 (f : Nat → Int → Bool) (a : Int) : ∀ n, stripW f a 7 n = W7 f a n
  | 0 => rfl
  | n + 1 => by
    have ih := stripW_7 f a n
    simp only [stripW, W7, ih, rowW]
    omega

theorem stripW_8 (f : Nat → Int → Bool) (a : Int) : ∀ n, stripW f a 8 n = W8 f a n
  | 0 => rfl
  | n + 1 => by
    have ih := stripW_8 f a n
    simp only [stripW, W8, ih, rowW]
    omega

theorem stripW_9 (f : Nat → Int → Bool) (a : Int) : ∀ n, stripW f a 9 n = W9 f a n
  | 0 => rfl
  | n + 1 => by
    have ih := stripW_9 f a n
    simp only [stripW, W9, ih, rowW]
    omega

/-- **Every strip of `J ≥ 5` adjacent columns of every orbit**: `5 W ≥ 2 J (n - 1)`. -/
theorem strip_white_ge5 (f : Nat → Int → Bool) (hf : IsOrbit f) :
    ∀ J, 5 ≤ J → ∀ (a : Int) (n : Nat), 2 * J * n ≤ 5 * stripW f a J n + 2 * J
  | J, hJ, a, n => by
    by_cases h10 : J < 10
    · have : J = 5 ∨ J = 6 ∨ J = 7 ∨ J = 8 ∨ J = 9 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl
      · rw [stripW_5]; exact strip5_white f hf a n
      · rw [stripW_6]; exact strip6_white f hf a n
      · rw [stripW_7]; exact strip7_white f hf a n
      · rw [stripW_8]; exact strip8_white f hf a n
      · rw [stripW_9]; exact strip9_white f hf a n
    · obtain ⟨k, rfl⟩ : ∃ k, J = 5 + k := ⟨J - 5, by omega⟩
      have h1 := strip_white_ge5 f hf k (by omega) (a + ((5 : Nat) : Int)) n
      have h2 := strip5_white f hf a n
      have hs := stripW_add f a 5 k n
      rw [stripW_5] at hs
      have m : 2 * (5 + k) * n = 10 * n + 2 * k * n := by
        rw [Nat.mul_add, Nat.add_mul]
      omega

end StripWhiteDensity
end Rule30Open
