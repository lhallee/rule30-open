module

public import Ruliology.CellularAutomata.Rule30Jen

/-!
# Three adjacent columns of every orbit are at least one third white, and one third is attained

In every orbit of Rule 30 (any initial row), any three adjacent columns `a, a + 1, a + 2` have at
least `n - 1` white cells among their `3 n` cells at the times `0 .. n - 1` (`triple_white`). The
proof telescopes in time: with the potential `phi(q, r) = 0` if the cells `a + 1, a + 2` are both
white and `1` otherwise, every step satisfies
`phi(next) + 1 ≤ phi(now) + (white cells of the strip now)` (`triple_step`, 32 cases, whatever the
cells outside the strip are). The constant is sharp: the row `(10)^∞` is a fixed point
(`alt_fixed`), and its strip `1 0 1` is white exactly once per step (`alt_triple`).

The natural-language argument is `PairWhiteDensity.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open
namespace PairWhiteDensity

open Ruliology.CellularAutomata.Rule30Jen

/-- `1` for a white cell. -/
def wh (b : Bool) : Nat := if b then 0 else 1

/-- One Rule 30 step of a row. -/
def step (x : Int → Bool) : Int → Bool := fun p => rule (x (p - 1)) (x p) (x (p + 1))

/-- An orbit of Rule 30: any sequence of rows, each the image of the one before. -/
def IsOrbit (f : Nat → Int → Bool) : Prop := ∀ t, f (t + 1) = step (f t)

/-- The potential of the two right cells of the strip. -/
def phi (q r : Bool) : Nat := if q || r then 1 else 0

/-- **One step**, whatever the cells around the strip. -/
theorem triple_step (p q r s : Bool) :
    phi (rule p q r) (rule q r s) + 1 ≤ phi q r + wh p + wh q + wh r := by
  cases p <;> cases q <;> cases r <;> cases s <;> decide

/-- White cells of the columns `a, a + 1, a + 2` at the times `0 .. n - 1`. -/
def tripleW (f : Nat → Int → Bool) (a : Int) : Nat → Nat
  | 0 => 0
  | n + 1 => tripleW f a n + wh (f n a) + wh (f n (a + 1)) + wh (f n (a + 2))

theorem triple_aux (f : Nat → Int → Bool) (hf : IsOrbit f) (a : Int) :
    ∀ n, n + phi (f n (a + 1)) (f n (a + 2)) ≤ phi (f 0 (a + 1)) (f 0 (a + 2)) + tripleW f a n
  | 0 => by simp [tripleW]
  | n + 1 => by
    have ih := triple_aux f hf a n
    have h := triple_step (f n a) (f n (a + 1)) (f n (a + 2)) (f n (a + 3))
    have e1 : f (n + 1) (a + 1) = rule (f n a) (f n (a + 1)) (f n (a + 2)) := by
      rw [hf n]; show rule (f n (a + 1 - 1)) (f n (a + 1)) (f n (a + 1 + 1)) = _
      have u : a + 1 - 1 = a := by omega
      have v : a + 1 + 1 = a + 2 := by omega
      rw [u, v]
    have e2 : f (n + 1) (a + 2) = rule (f n (a + 1)) (f n (a + 2)) (f n (a + 3)) := by
      rw [hf n]; show rule (f n (a + 2 - 1)) (f n (a + 2)) (f n (a + 2 + 1)) = _
      have u : a + 2 - 1 = a + 1 := by omega
      have v : a + 2 + 1 = a + 3 := by omega
      rw [u, v]
    rw [e1, e2]
    simp only [tripleW]
    omega

theorem phi_le (q r : Bool) : phi q r ≤ 1 := by cases q <;> cases r <;> decide

/-- **Every three adjacent columns of every orbit**: at least `n - 1` white cells at the times
`0 .. n - 1`. -/
theorem triple_white (f : Nat → Int → Bool) (hf : IsOrbit f) (a : Int) (n : Nat) :
    n ≤ tripleW f a n + 1 := by
  have h := triple_aux f hf a n
  have := phi_le (f 0 (a + 1)) (f 0 (a + 2))
  omega

/-! ### Sharpness -/

/-- The row `(10)^∞`: black at the even cells. -/
def alt (p : Int) : Bool := decide (p % 2 = 0)

/-- `(10)^∞` is a fixed point of Rule 30. -/
theorem alt_fixed : step alt = alt := by
  funext p
  have h : p % 2 = 0 ∨ p % 2 = 1 := by omega
  have e1 : (p - 1) % 2 = (p % 2 + 1) % 2 := by omega
  have e2 : (p + 1) % 2 = (p % 2 + 1) % 2 := by omega
  simp only [step, alt, e1, e2]
  rcases h with h | h <;> rw [h] <;> decide

/-- The constant orbit of `(10)^∞`. -/
theorem alt_orbit : IsOrbit (fun _ => alt) := fun _ => alt_fixed.symm

/-- Its columns `0, 1, 2` read black, white, black: exactly `n` white cells in `3 n`. -/
theorem alt_triple (n : Nat) : tripleW (fun _ => alt) 0 n = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h0 : wh (alt 0) = 0 := by decide
    have h1 : wh (alt (0 + 1)) = 1 := by decide
    have h2 : wh (alt (0 + 2)) = 0 := by decide
    simp only [tripleW, ih, h0, h1, h2]

end PairWhiteDensity
end Rule30Open
