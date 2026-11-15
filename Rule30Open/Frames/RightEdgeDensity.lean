module

/-!
# A white density bound on the right diagonals

In the frame of the right edge a row is a code `y : Nat → Bool`, bit `e` being the cell `e` places left of the edge,
and one step of rule 30 is `codeStep y e = y e xor (y (e - 1) || y (e - 2))` with `y (-1) = y (-2) = false`
(the kit's `Rule30Equivalents.Odometer.G`). Let `whites y J` count the white bits among `0, …, J - 1`.

* `local_ineq`: the potential of `RowWhiteDensity`: `2 [a xor (b || c) black] + ψ(b, c) ≤ 3 [a white] + ψ(a, b)`.
* `two_black_le`: for every code, `2 * blacks (codeStep y) J ≤ 3 * whites y J + 2`. The inequality telescopes
  along the code from bit 0, where the two missing bits are white.
* `white_step`: `2 * J ≤ 3 * whites y J + 2 * whites (codeStep y) J + 2`.
* `orbit_white`: over `P` consecutive steps of any orbit,
  `2 * J * P + 2 * whites (f 0) J ≤ 5 * (whites over the P codes) + 2 * whites (f P) J + 2 * P`.
* `periodic_white`: if the first `J` bits return after `P` steps, `(2 * J - 2) * P ≤ 5 * (whites over the P codes)`:
  over one period of the first `J` right diagonals at least `(2J - 2)/5` of them are white on average.

The natural-language argument, with the black cells forced by the doubling diagonals, is `RightEdgeDensity.md`, beside
this file.
-/

@[expose] public section

namespace Rule30Open

namespace RightEdgeDensity

/-- One step of rule 30 in the frame of the right edge. -/
def codeStep (y : Nat → Bool) : Nat → Bool
  | 0 => y 0
  | 1 => xor (y 1) (y 0)
  | e + 2 => xor (y (e + 2)) (y (e + 1) || y e)

def wh (b : Bool) : Nat := if b then 0 else 1

def bl (b : Bool) : Nat := if b then 1 else 0

def psi : Bool → Bool → Nat
  | false, false => 0
  | false, true => 1
  | true, _ => 2

theorem local_ineq (a b c : Bool) : 2 * bl (xor a (b || c)) + psi b c ≤ 3 * wh a + psi a b := by
  cases a <;> cases b <;> cases c <;> decide

theorem psi_le (a b : Bool) : psi a b ≤ 2 := by cases a <;> cases b <;> decide

def whites (y : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => whites y n + wh (y n)

def blacks (y : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => blacks y n + bl (y n)

theorem whites_add_blacks (y : Nat → Bool) : ∀ n, whites y n + blacks y n = n
  | 0 => rfl
  | n + 1 => by
    have := whites_add_blacks y n
    simp only [whites, blacks]
    cases y n <;> simp [wh, bl] <;> omega

/-- The code with two white bits below bit 0: `pad y (e + 2) = y e`. -/
def pad (y : Nat → Bool) : Nat → Bool
  | 0 => false
  | 1 => false
  | e + 2 => y e

theorem codeStep_pad (y : Nat → Bool) (e : Nat) :
    codeStep y e = xor (pad y (e + 2)) (pad y (e + 1) || pad y e) := by
  match e with
  | 0 => cases h : y 0 <;> simp [codeStep, pad, h]
  | 1 => cases h0 : y 0 <;> cases h1 : y 1 <;> simp [codeStep, pad, h0, h1]
  | j + 2 => simp [codeStep, pad]

theorem telescope (y : Nat → Bool) : ∀ n,
    2 * blacks (codeStep y) n ≤ 3 * whites y n + psi (pad y (n + 1)) (pad y n)
  | 0 => by simp [blacks]
  | n + 1 => by
    have ih := telescope y n
    have h := local_ineq (pad y (n + 2)) (pad y (n + 1)) (pad y n)
    rw [← codeStep_pad] at h
    have e : pad y (n + 2) = y n := rfl
    have e2 : pad y (n + 1 + 1) = y n := rfl
    rw [e] at h
    simp only [blacks, whites]
    rw [e2]
    omega

/-- **For every code, `2 * blacks (codeStep y) J ≤ 3 * whites y J + 2`.** -/
theorem two_black_le (y : Nat → Bool) (J : Nat) : 2 * blacks (codeStep y) J ≤ 3 * whites y J + 2 := by
  have h := telescope y J
  have := psi_le (pad y (J + 1)) (pad y J)
  omega

/-- **One step: `2 J ≤ 3 * whites y J + 2 * whites (codeStep y) J + 2`.** -/
theorem white_step (y : Nat → Bool) (J : Nat) : 2 * J ≤ 3 * whites y J + 2 * whites (codeStep y) J + 2 := by
  have h := two_black_le y J
  have e := whites_add_blacks (codeStep y) J
  omega

def sumW (f : Nat → Nat → Bool) (J : Nat) : Nat → Nat
  | 0 => 0
  | P + 1 => sumW f J P + whites (f P) J

theorem orbit_white (f : Nat → Nat → Bool) (hf : ∀ i, f (i + 1) = codeStep (f i)) (J : Nat) :
    ∀ P, 2 * J * P + 2 * whites (f 0) J ≤ 5 * sumW f J P + 2 * whites (f P) J + 2 * P
  | 0 => by simp [sumW]
  | P + 1 => by
    have ih := orbit_white f hf J P
    have h := white_step (f P) J
    rw [← hf P] at h
    simp only [sumW]
    rw [Nat.mul_succ, Nat.mul_succ]
    omega

theorem whites_congr {y y' : Nat → Bool} : ∀ J, (∀ e, e < J → y e = y' e) → whites y J = whites y' J
  | 0, _ => rfl
  | J + 1, h => by
    simp only [whites]
    rw [whites_congr J (fun e he => h e (by omega)), h J (by omega)]

/-- **Over one period of the first `J` bits, at least `(2J - 2)/5` of them are white on average.** -/
theorem periodic_white (f : Nat → Nat → Bool) (hf : ∀ i, f (i + 1) = codeStep (f i)) (J P : Nat)
    (hP : ∀ e, e < J → f P e = f 0 e) : (2 * J - 2) * P ≤ 5 * sumW f J P := by
  have h := orbit_white f hf J P
  rw [whites_congr J hP] at h
  have : (2 * J - 2) * P ≤ 2 * J * P - 2 * P := Nat.le_of_eq (Nat.sub_mul _ _ _)
  omega

end RightEdgeDensity

end Rule30Open
