module

public import Rule30Open.Foundations.RowWhiteDensity
public import Rule30Open.Foundations.StripWhiteDensity

/-!
# The bound 2/5 for strips is attained

The orbit of the row `(11001)^∞` is `f t p = p5 (p + 2 t)`, since Rule 30 maps the row to its shift
by two cells (`RowWhiteDensity.period_five_shift`). Each column of it is white exactly twice in every
five consecutive times, so every strip of `J` columns has exactly `2 J n` white cells in its first
`5 n` rows (`strip_sharp`). This is the case of equality of `StripWhiteDensity.strip_white_ge5`.

The natural-language argument is `StripWhiteSharp.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open
namespace StripWhiteSharp

open Ruliology.CellularAutomata.Rule30Jen
open StripWhiteDensity (wh rowW stripW IsOrbit)

/-- The orbit of `(11001)^∞`. -/
def f (t : Nat) (p : Int) : Bool := RowWhiteDensity.p5 (p + 2 * (t : Int))

theorem f_orbit : IsOrbit f := by
  intro t
  funext p
  have h := RowWhiteDensity.period_five_shift (p + 2 * (t : Int))
  unfold RowWhiteDensity.step at h
  show RowWhiteDensity.p5 (p + 2 * ((t + 1 : Nat) : Int)) =
    rule (f t (p - 1)) (f t p) (f t (p + 1))
  unfold f
  have e1 : p - 1 + 2 * (t : Int) = p + 2 * (t : Int) - 1 := by omega
  have e2 : p + 1 + 2 * (t : Int) = p + 2 * (t : Int) + 1 := by omega
  have e3 : p + 2 * ((t + 1 : Nat) : Int) = p + 2 * (t : Int) + 2 := by omega
  rw [e1, e2, e3, h]

/-- Five consecutive times of one column: exactly two white cells. -/
theorem col_five (c : Int) :
    wh (RowWhiteDensity.p5 c) + wh (RowWhiteDensity.p5 (c + 2)) + wh (RowWhiteDensity.p5 (c + 4)) +
      wh (RowWhiteDensity.p5 (c + 6)) + wh (RowWhiteDensity.p5 (c + 8)) = 2 := by
  have h : c % 5 = 0 ∨ c % 5 = 1 ∨ c % 5 = 2 ∨ c % 5 = 3 ∨ c % 5 = 4 := by omega
  have e : ∀ k : Int, (c + k) % 5 = (c % 5 + k) % 5 := fun k => by omega
  simp only [RowWhiteDensity.p5, e]
  rcases h with h | h | h | h | h <;> rw [h] <;> decide

/-- The white cells of the strip in the five rows `5 m .. 5 m + 4`. -/
def block (a : Int) (J m : Nat) : Nat :=
  rowW (f (5 * m)) a J + rowW (f (5 * m + 1)) a J + rowW (f (5 * m + 2)) a J +
    rowW (f (5 * m + 3)) a J + rowW (f (5 * m + 4)) a J

theorem block_eq (a : Int) (m : Nat) : ∀ J, block a J m = 2 * J
  | 0 => rfl
  | J + 1 => by
    have ih := block_eq a m J
    unfold block at ih ⊢
    simp only [rowW]
    have c := col_five (a + (J : Int) + 2 * ((5 * m : Nat) : Int))
    unfold f
    have e1 : a + (J : Int) + 2 * ((5 * m + 1 : Nat) : Int) =
      a + (J : Int) + 2 * ((5 * m : Nat) : Int) + 2 := by omega
    have e2 : a + (J : Int) + 2 * ((5 * m + 2 : Nat) : Int) =
      a + (J : Int) + 2 * ((5 * m : Nat) : Int) + 4 := by omega
    have e3 : a + (J : Int) + 2 * ((5 * m + 3 : Nat) : Int) =
      a + (J : Int) + 2 * ((5 * m : Nat) : Int) + 6 := by omega
    have e4 : a + (J : Int) + 2 * ((5 * m + 4 : Nat) : Int) =
      a + (J : Int) + 2 * ((5 * m : Nat) : Int) + 8 := by omega
    rw [e1, e2, e3, e4]
    unfold f at ih
    omega

/-- **Sharpness**: in the orbit of `(11001)^∞`, every strip of `J` columns has exactly `2 J n` white
cells in its first `5 n` rows. -/
theorem strip_sharp (a : Int) (J : Nat) : ∀ n, stripW f a J (5 * n) = 2 * J * n
  | 0 => rfl
  | n + 1 => by
    have ih := strip_sharp a J n
    have hb := block_eq a n J
    have e : 5 * (n + 1) = 5 * n + 4 + 1 := by omega
    rw [e]
    simp only [stripW]
    unfold block at hb
    rw [Nat.mul_add, Nat.mul_one]
    omega

end StripWhiteSharp
end Rule30Open
