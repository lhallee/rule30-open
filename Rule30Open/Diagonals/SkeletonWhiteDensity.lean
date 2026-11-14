module

public import Rule30Open.Diagonals.EternalSkeleton

/-!
# A white density bound on the left diagonals, for every row and every eternal orbit

In the left-edge frame (`EternalSkeleton.leftStep`, coordinate `d` is left diagonal `d`), let `whites R J` count the
white cells among diagonals `0, …, J - 1` of a row `R`.

* `local_ineq`: with `ψ(0,0) = 0`, `ψ(0,1) = 1`, `ψ(1,·) = 2`, every cell `y = a xor (b || c)` satisfies
  `2 [y black] + ψ(b, c) ≤ 3 [a white] + ψ(a, b)` (the potential of `RowWhiteDensity.local_ineq`, re-proved here by
  cases).
* `two_black_le`: for every row `R` and every `J`, `2 * blacks (leftStep R) J ≤ 3 * whites R J + 4`. The inequality
  telescopes along the depth, starting from the two white cells left of the frame.
* `white_step`: so `2 * J ≤ 3 * whites R J + 2 * whites (leftStep R) J + 4`.
* `orbit_white`: over `P` consecutive rows of any forward orbit,
  `2 * J * P ≤ 5 * (whites over the P rows) + 2 * whites (row P) J + 4 * P`, the boundary term being the last row.
* `eternal_white`: on every eternal orbit, over the period `2 ^ J` of its first `J` diagonals,
  `(2 * J - 4) * 2 ^ J ≤ 5 * (white cells of diagonals 0 … J-1 over 2 ^ J consecutive times)`: at least `(2J - 4)/5` of
  the first `J` diagonals are white on average. This holds for the single cell's shadow
  (`EternalSkeleton.shadow_eternal`).

The natural-language argument is `SkeletonWhiteDensity.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

namespace SkeletonWhiteDensity

open EternalSkeleton

def wh (b : Bool) : Nat := if b then 0 else 1

def bl (b : Bool) : Nat := if b then 1 else 0

def psi : Bool → Bool → Nat
  | false, false => 0
  | false, true => 1
  | true, _ => 2

theorem local_ineq (a b c : Bool) : 2 * bl (xor a (b || c)) + psi b c ≤ 3 * wh a + psi a b := by
  cases a <;> cases b <;> cases c <;> decide

/-- White cells among coordinates `0 … n - 1`. -/
def whites (R : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => whites R n + wh (R n)

/-- Black cells among coordinates `0 … n - 1`. -/
def blacks (R : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => blacks R n + bl (R n)

theorem whites_add_blacks (R : Nat → Bool) : ∀ n, whites R n + blacks R n = n
  | 0 => rfl
  | n + 1 => by
    have := whites_add_blacks R n
    simp only [whites, blacks]
    cases R n <;> simp [wh, bl] <;> omega

/-- The row with the two white cells left of the frame put in front. -/
def pad (R : Nat → Bool) : Nat → Bool
  | 0 => false
  | 1 => false
  | d + 2 => R d

theorem leftStep_pad (R : Nat → Bool) (d : Nat) :
    leftStep R d = xor (pad R d) (pad R (d + 1) || pad R (d + 2)) := by
  match d with
  | 0 => cases R 0 <;> rfl
  | 1 => cases R 0 <;> cases R 1 <;> rfl
  | j + 2 => rfl

theorem whites_pad (R : Nat → Bool) : ∀ n, whites (pad R) (n + 2) = 2 + whites R n
  | 0 => rfl
  | n + 1 => by
    show whites (pad R) (n + 2) + wh (R n) = 2 + (whites R n + wh (R n))
    rw [whites_pad R n]; omega

theorem telescope (R : Nat → Bool) : ∀ n,
    2 * blacks (leftStep R) n + psi (pad R n) (pad R (n + 1)) ≤ 3 * whites (pad R) n
  | 0 => by simp [blacks, whites, pad, psi]
  | n + 1 => by
    have ih := telescope R n
    have h := local_ineq (pad R n) (pad R (n + 1)) (pad R (n + 2))
    rw [← leftStep_pad] at h
    simp only [blacks, whites]
    omega

/-- **For every row, `2 * blacks (leftStep R) J ≤ 3 * whites R J + 4`.** -/
theorem two_black_le (R : Nat → Bool) (J : Nat) : 2 * blacks (leftStep R) J ≤ 3 * whites R J + 4 := by
  match J with
  | 0 => simp [blacks]
  | 1 =>
    show 2 * (0 + bl (leftStep R 0)) ≤ 3 * (0 + wh (R 0)) + 4
    show 2 * (0 + bl (R 0)) ≤ 3 * (0 + wh (R 0)) + 4
    cases R 0 <;> decide
  | n + 2 =>
    have h := telescope R (n + 2)
    rw [whites_pad] at h
    show 2 * blacks (leftStep R) (n + 2) ≤ 3 * (whites R n + wh (R n) + wh (R (n + 1))) + 4
    have hp : psi (pad R (n + 2)) (pad R (n + 2 + 1)) = psi (R n) (R (n + 1)) := rfl
    rw [hp] at h
    revert h
    cases R n <;> cases R (n + 1) <;> simp [psi, wh] <;> omega

/-- **One step: `2 J ≤ 3 * whites R J + 2 * whites (leftStep R) J + 4`.** -/
theorem white_step (R : Nat → Bool) (J : Nat) : 2 * J ≤ 3 * whites R J + 2 * whites (leftStep R) J + 4 := by
  have h := two_black_le R J
  have e := whites_add_blacks (leftStep R) J
  omega

/-- Sum of `whites (f i) J` over `i < P`. -/
def sumW (f : Nat → Nat → Bool) (J : Nat) : Nat → Nat
  | 0 => 0
  | P + 1 => sumW f J P + whites (f P) J

/-- **Any forward orbit, any window of `P` rows.** -/
theorem orbit_white (f : Nat → Nat → Bool) (hf : ∀ i, f (i + 1) = leftStep (f i)) (J : Nat) :
    ∀ P, 2 * J * P + 2 * whites (f 0) J ≤ 5 * sumW f J P + 2 * whites (f P) J + 4 * P
  | 0 => by simp [sumW]
  | P + 1 => by
    have ih := orbit_white f hf J P
    have h := white_step (f P) J
    rw [← hf P] at h
    simp only [sumW]
    rw [Nat.mul_succ, Nat.mul_succ]
    omega

theorem whites_congr {R R' : Nat → Bool} : ∀ J, (∀ d, d < J → R d = R' d) → whites R J = whites R' J
  | 0, _ => rfl
  | J + 1, h => by
    simp only [whites]
    rw [whites_congr J (fun d hd => h d (by omega)), h J (by omega)]

/-- **Every eternal orbit: over `2 ^ J` consecutive times, at least `(2J - 4)/5` of the first `J` diagonals are white
on average.** -/
theorem eternal_white {R : Int → Nat → Bool} (hR : Eternal R) (t₀ : Int) (J : Nat) :
    (2 * J - 4) * 2 ^ J ≤ 5 * sumW (fun i => R (t₀ + (i : Int))) J (2 ^ J) := by
  let f : Nat → Nat → Bool := fun i => R (t₀ + (i : Int))
  have hf : ∀ i, f (i + 1) = leftStep (f i) := by
    intro i
    show R (t₀ + ((i + 1 : Nat) : Int)) = leftStep (R (t₀ + (i : Int)))
    rw [show t₀ + ((i + 1 : Nat) : Int) = t₀ + (i : Int) + 1 by omega]
    exact hR _
  have hper : whites (f (2 ^ J)) J = whites (f 0) J := by
    apply whites_congr
    intro d hd
    show R (t₀ + ((2 ^ J : Nat) : Int)) d = R (t₀ + ((0 : Nat) : Int)) d
    have hk : 2 ^ J = 2 ^ d * 2 ^ (J - d) := by
      rw [← Nat.pow_add, show d + (J - d) = J by omega]
    rw [hk, eternal_periodic_mul hR d t₀ (2 ^ (J - d))]
    simp
  have h := orbit_white f hf J (2 ^ J)
  rw [hper] at h
  have : (2 * J - 4) * 2 ^ J ≤ 2 * J * 2 ^ J - 4 * 2 ^ J := by
    rw [Nat.sub_mul]
  show (2 * J - 4) * 2 ^ J ≤ 5 * sumW f J (2 ^ J)
  omega

end SkeletonWhiteDensity

end Rule30Open
