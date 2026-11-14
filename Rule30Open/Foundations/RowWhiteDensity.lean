module

public import Ruliology.CellularAutomata.Rule30Jen

/-!
# White cells of a row pay for the black cells of the next row

For every row `x` and its image `y` under Rule 30, and every window of `n` cells,
three times the white cells of `x` on `[a - 1, a + n - 2]` plus 2 is at least twice the black cells
of `y` on `[a, a + n - 1]` (`two_black_le`). The proof is a telescoping sum: with the potential
`psi` of a pair of adjacent cells (`0` for `00`, `1` for `01`, `2` for `1?`), every cell satisfies
`2 [y_i black] + psi(x_i, x_(i+1)) ≤ 3 [x_(i-1) white] + psi(x_(i-1), x_i)` (`local_ineq`, eight
cases).

For the single black cell, the window of row `s + 1` is its whole light-cone row, and the boundary
terms are exact: `2 B(s + 1) ≤ 3 W(s) + 6` (`row_pair`), where `B(t)` and `W(t)` count the black and
white cells of row `t` on `-t .. t`. Summed over the rows, the triangle of rows `0 .. n - 1`
(`n^2` cells) has at least `2 (n - 1)(n - 2) / 5` white cells (`triangle_white`).

On a fixed strip of `J` columns the same telescoping gives `2 B ≤ 3 W + 2` for every row
(`strip_ineq`), so every strip of `J` adjacent columns of every orbit has at least `(2 J - 2) n / 5`
white cells at the times `0 .. n` (`strip_white`); for two adjacent columns, two black cells leave the
right one white a step later (`pair_rule`), so `W_a(n) + W_(a+1)(n) + W_(a+1)(n + 1) ≥ n`
(`pair_white`).

The constant `2/5` is the best a local argument can give: the row `(11001)^∞` is mapped by Rule 30
to a shift of itself (`period_five_shift`), so every row of its orbit is exactly `2/5` white.

The natural-language argument is `RowWhiteDensity.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open
namespace RowWhiteDensity

open Ruliology.CellularAutomata.Rule30Jen

/-- `1` for a white cell. -/
def wh (b : Bool) : Nat := if b then 0 else 1

/-- `1` for a black cell. -/
def bl (b : Bool) : Nat := if b then 1 else 0

/-- The potential of a pair of adjacent cells. -/
def psi : Bool → Bool → Nat
  | false, false => 0
  | false, true => 1
  | true, _ => 2

theorem psi_le (a b : Bool) : psi a b ≤ 2 := by cases a <;> cases b <;> decide

/-- The one-cell inequality behind the count. -/
theorem local_ineq (a b c : Bool) : 2 * bl (rule a b c) + psi b c ≤ 3 * wh a + psi a b := by
  cases a <;> cases b <;> cases c <;> decide

/-- White cells of `x` on `a, a + 1, ..., a + n - 1`. -/
def whites (x : Int → Bool) (a : Int) : Nat → Nat
  | 0 => 0
  | n + 1 => whites x a n + wh (x (a + n))

/-- Black cells of `x` on `a, a + 1, ..., a + n - 1`. -/
def blacks (x : Int → Bool) (a : Int) : Nat → Nat
  | 0 => 0
  | n + 1 => blacks x a n + bl (x (a + n))

/-- One Rule 30 step of a row. -/
def step (x : Int → Bool) : Int → Bool := fun p => rule (x (p - 1)) (x p) (x (p + 1))

theorem whites_add_blacks (x : Int → Bool) (a : Int) : ∀ n, whites x a n + blacks x a n = n
  | 0 => rfl
  | n + 1 => by
    have ih := whites_add_blacks x a n
    simp only [whites, blacks]
    cases x (a + n) <;> simp [wh, bl] <;> omega

theorem whites_append (x : Int → Bool) (a : Int) (m : Nat) :
    ∀ n, whites x a (m + n) = whites x a m + whites x (a + m) n
  | 0 => rfl
  | n + 1 => by
    have ih := whites_append x a m n
    have e : a + ((m + n : Nat) : Int) = a + (m : Int) + (n : Int) := by omega
    show whites x a (m + n) + wh (x (a + ((m + n : Nat) : Int))) = _
    rw [ih, e]; simp only [whites]; omega

/-- **The telescoping count**, for every row and every window. -/
theorem telescope (x : Int → Bool) (a : Int) : ∀ n : Nat,
    2 * blacks (step x) a n + psi (x (a + n - 1)) (x (a + n)) ≤
      3 * whites x (a - 1) n + psi (x (a - 1)) (x a)
  | 0 => by
    have e2 : a + ((0 : Nat) : Int) = a := by omega
    simp only [blacks, whites, e2]; omega
  | n + 1 => by
    have ih := telescope x a n
    have l := local_ineq (x (a + n - 1)) (x (a + n)) (x (a + n + 1))
    have e2 : a + ((n + 1 : Nat) : Int) = a + n + 1 := by omega
    have e3 : a - 1 + (n : Int) = a + n - 1 := by omega
    have e4 : a + (n : Int) + 1 - 1 = a + n := by omega
    have hs : step x (a + n) = rule (x (a + n - 1)) (x (a + n)) (x (a + n + 1)) := rfl
    simp only [blacks, whites, e2, e3, e4, hs]
    omega

/-- **Every row**: three times the white cells of `x` on `[a - 1, a + n - 2]`, plus 2, is at least
twice the black cells of its image on `[a, a + n - 1]`. -/
theorem two_black_le (x : Int → Bool) (a : Int) (n : Nat) :
    2 * blacks (step x) a n ≤ 3 * whites x (a - 1) n + 2 := by
  have h := telescope x a n
  have := psi_le (x (a - 1)) (x a)
  omega

/-! ### The single black cell -/

/-- Black cells of row `t` of the single cell on `-t .. t`. -/
def B (t : Nat) : Nat := blacks (cell t) (-(t : Int)) (2 * t + 1)

/-- White cells of row `t` of the single cell on `-t .. t`. -/
def W (t : Nat) : Nat := whites (cell t) (-(t : Int)) (2 * t + 1)

theorem B_add_W (t : Nat) : B t + W t = 2 * t + 1 := by
  have := whites_add_blacks (cell t) (-(t : Int)) (2 * t + 1)
  unfold B W; omega

theorem step_cell (s : Nat) : step (cell s) = cell (s + 1) := by
  funext p; rfl

/-- **Two consecutive rows**: `2 B(s + 1) ≤ 3 W(s) + 6`. -/
theorem row_pair (s : Nat) : 2 * B (s + 1) ≤ 3 * W s + 6 := by
  have h := telescope (cell s) (-((s + 1 : Nat) : Int)) (2 * (s + 1) + 1)
  rw [step_cell] at h
  have e0 : -((s + 1 : Nat) : Int) - 1 = -(s : Int) - 2 := by omega
  have p0 : cell s (-(s : Int) - 2) = false := cell_eq_false_of_lt s _ (by omega)
  have p1 : cell s (-((s + 1 : Nat) : Int)) = false := cell_eq_false_of_lt s _ (by omega)
  have hsplit := whites_append (cell s) (-(s : Int) - 2) 2 (2 * s + 1)
  have e2 : 2 + (2 * s + 1) = 2 * (s + 1) + 1 := by omega
  have e3 : -(s : Int) - 2 + ((2 : Nat) : Int) = -(s : Int) := by omega
  rw [e2, e3] at hsplit
  have htwo : whites (cell s) (-(s : Int) - 2) 2 = 2 := by
    have q1 : cell s (-(s : Int) - 2 + ((0 : Nat) : Int)) = false :=
      cell_eq_false_of_lt s _ (by omega)
    have q2 : cell s (-(s : Int) - 2 + ((1 : Nat) : Int)) = false :=
      cell_eq_false_of_lt s _ (by omega)
    simp only [whites, q1, q2, wh]; rfl
  rw [e0, p0, p1] at h
  have hp : psi false false = 0 := rfl
  unfold B W
  omega

/-- White cells of the rows `0 .. n - 1`. -/
def Wtot : Nat → Nat
  | 0 => 0
  | n + 1 => Wtot n + W n

/-- White cells of the rows `1 .. n`. -/
def Wshift : Nat → Nat
  | 0 => 0
  | n + 1 => Wshift n + W (n + 1)

theorem Wshift_le : ∀ n, Wshift n ≤ Wtot (n + 1)
  | 0 => Nat.zero_le _
  | n + 1 => by
    have := Wshift_le n
    simp only [Wshift, Wtot] at *
    omega

theorem triangle_aux : ∀ m : Nat, 2 * m * (m + 2) ≤ 3 * Wtot m + 2 * Wshift m + 6 * m
  | 0 => by simp [Wtot, Wshift]
  | m + 1 => by
    have ih := triangle_aux m
    have hp := row_pair m
    have hbw := B_add_W (m + 1)
    simp only [Wtot, Wshift]
    have : 2 * (m + 1) * (m + 1 + 2) = 2 * m * (m + 2) + 2 * (2 * m + 3) := by grind
    omega

/-- **The triangle**: rows `0 .. n - 1` of the single cell (`n^2` cells) have at least
`2 (n - 1)(n - 2) / 5` white cells. -/
theorem triangle_white (n : Nat) : 2 * (n - 1) * (n - 2) ≤ 5 * Wtot n := by
  cases n with
  | zero => simp [Wtot]
  | succ m =>
    have h := triangle_aux m
    have hs := Wshift_le m
    have hmono : Wtot m ≤ Wtot (m + 1) := by simp only [Wtot]; omega
    have e : m + 1 - 1 = m := by omega
    rw [e]
    rcases m with _ | k
    · simp
    · have e2 : k + 1 + 1 - 2 = k := by omega
      rw [e2]
      have : 2 * (k + 1) * (k + 1 + 2) = 2 * (k + 1) * k + 6 * (k + 1) := by grind
      omega

/-! ### Vertical strips, for every orbit -/

theorem edge_bounds (p q : Bool) : 2 ≤ 3 * wh p + psi p q ∧ 3 * wh p + psi p q ≤ 4 := by
  cases p <;> cases q <;> decide

/-- **A fixed strip**: twice the black cells of the image on `[a, a + J - 1]` are at most three times
the white cells of the row on the same cells, plus 2. -/
theorem strip_ineq (x : Int → Bool) (a : Int) (J : Nat) :
    2 * blacks (step x) a J ≤ 3 * whites x a J + 2 := by
  have h := telescope x a J
  have h1 := whites_append x (a - 1) 1 J
  have e1 : a - 1 + ((1 : Nat) : Int) = a := by omega
  rw [e1] at h1
  have h2 : whites x (a - 1) (1 + J) = whites x (a - 1) J + wh (x (a - 1 + J)) := by
    rw [Nat.add_comm]; rfl
  have h3 : whites x (a - 1) 1 = wh (x (a - 1)) := by
    have e : a - 1 + ((0 : Nat) : Int) = a - 1 := by omega
    simp only [whites, e]; omega
  have e2 : a - 1 + (J : Int) = a + J - 1 := by omega
  rw [e2] at h2
  have b1 := edge_bounds (x (a - 1)) (x a)
  have b2 := edge_bounds (x (a + J - 1)) (x (a + J))
  omega

/-- **Two adjacent cells**: if cells `a` and `a + 1` are black, cell `a + 1` of the image is white. -/
theorem pair_rule (x : Int → Bool) (a : Int) :
    1 ≤ wh (x a) + wh (x (a + 1)) + wh (step x (a + 1)) := by
  have e : a + 1 - 1 = a := by omega
  simp only [step, e]
  cases x a <;> cases x (a + 1) <;> cases x (a + 1 + 1) <;> decide

/-- An orbit of Rule 30: any sequence of rows, each the image of the one before. -/
def IsOrbit (f : Nat → Int → Bool) : Prop := ∀ t, f (t + 1) = step (f t)

/-- White cells of the strip `[a, a + J - 1]` at the times `0 .. n - 1`. -/
def stripW (f : Nat → Int → Bool) (a : Int) (J : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => stripW f a J n + whites (f n) a J

/-- White cells of the strip at the times `1 .. n`. -/
def stripW1 (f : Nat → Int → Bool) (a : Int) (J : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => stripW1 f a J n + whites (f (n + 1)) a J

theorem stripW1_le (f : Nat → Int → Bool) (a : Int) (J : Nat) :
    ∀ n, stripW1 f a J n ≤ stripW f a J (n + 1)
  | 0 => Nat.zero_le _
  | n + 1 => by
    have := stripW1_le f a J n
    simp only [stripW1, stripW] at *
    omega

theorem strip_aux (f : Nat → Int → Bool) (hf : IsOrbit f) (a : Int) (J : Nat) :
    ∀ n, 2 * J * n ≤ 3 * stripW f a J n + 2 * stripW1 f a J n + 2 * n
  | 0 => by simp [stripW, stripW1]
  | n + 1 => by
    have ih := strip_aux f hf a J n
    have hs := strip_ineq (f n) a J
    rw [← hf n] at hs
    have hb := whites_add_blacks (f (n + 1)) a J
    simp only [stripW, stripW1]
    have : 2 * J * (n + 1) = 2 * J * n + 2 * J := by grind
    omega

/-- **Every vertical strip of every orbit**: the strip of `J` adjacent columns has at least
`(2 J - 2) n / 5` white cells at the times `0 .. n`. -/
theorem strip_white (f : Nat → Int → Bool) (hf : IsOrbit f) (a : Int) (J n : Nat) :
    2 * J * n ≤ 5 * stripW f a J (n + 1) + 2 * n := by
  have h := strip_aux f hf a J n
  have h1 := stripW1_le f a J n
  have h2 : stripW f a J n ≤ stripW f a J (n + 1) := by simp only [stripW]; omega
  omega

/-- White cells of column `i` at the times `0 .. n - 1`. -/
def colW (f : Nat → Int → Bool) (i : Int) : Nat → Nat
  | 0 => 0
  | n + 1 => colW f i n + wh (f n i)

/-- **Two adjacent columns of every orbit**: `W_a(n) + W_(a+1)(n) + W_(a+1)(n + 1) ≥ n`. -/
theorem pair_white (f : Nat → Int → Bool) (hf : IsOrbit f) (a : Int) :
    ∀ n, n ≤ colW f a n + colW f (a + 1) n + colW f (a + 1) (n + 1)
  | 0 => Nat.zero_le _
  | n + 1 => by
    have ih := pair_white f hf a n
    have hp := pair_rule (f n) a
    rw [← hf n] at hp
    simp only [colW] at *
    omega

/-! ### Sharpness -/

/-- The row `(11001)^∞`. -/
def p5 (p : Int) : Bool := [true, true, false, false, true].getD (p % 5).toNat false

/-- Rule 30 maps `(11001)^∞` to its shift by two cells. -/
theorem period_five_shift (p : Int) : step p5 p = p5 (p + 2) := by
  have h : p % 5 = 0 ∨ p % 5 = 1 ∨ p % 5 = 2 ∨ p % 5 = 3 ∨ p % 5 = 4 := by omega
  have e1 : (p - 1) % 5 = (p % 5 + 4) % 5 := by omega
  have e2 : (p + 1) % 5 = (p % 5 + 1) % 5 := by omega
  have e3 : (p + 2) % 5 = (p % 5 + 2) % 5 := by omega
  simp only [step, p5, e1, e2, e3]
  rcases h with h | h | h | h | h <;> rw [h] <;> decide

/-- Each period of `(11001)^∞` has two white cells and three black cells. -/
theorem period_five_count (a : Int) : whites p5 a 5 = 2 := by
  have h : a % 5 = 0 ∨ a % 5 = 1 ∨ a % 5 = 2 ∨ a % 5 = 3 ∨ a % 5 = 4 := by omega
  have e : ∀ k : Nat, (a + (k : Int)) % 5 = (a % 5 + k) % 5 := fun k => by omega
  simp only [whites, p5, e]
  rcases h with h | h | h | h | h <;> rw [h] <;> decide

end RowWhiteDensity
end Rule30Open
