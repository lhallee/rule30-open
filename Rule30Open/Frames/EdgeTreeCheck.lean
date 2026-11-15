module

public import Rule30Open.Frames.EdgeTree
public import Rule30Open.Frames.LightReturnClassified

/-!
# A checker for the branch tree, sound for every period, and the period-32 instance

Columns of an `L`-periodic edge code are read as lists of their first `L` values (`seg`). From two consecutive
columns `v`, `w` the next column `x` satisfies `x (i + 1) = x i xor (w i || v i)`, so its first `L` values are
`integ (x 0) (orW w v)` and it closes up after `L` steps only if `orW w v` has even parity.

* `dead fuel v w`: true when every walk of columns from `(v, w)` stops within `fuel` steps.
* `dead_sound`: **for every `L` and every code with `iter L c = c`, no pair of consecutive columns is dead.**
* `period_32`: **a code with bit 0 black and `iter 32 c = c` is `rainA` or `rainB`**, from `EdgeTree.rain_or_branch`,
  `dead_sound` and a kernel evaluation of `dead` at the two branch states.
* `rain_of_return_64`: **a row white right of a black cell `r` that returns after `L` steps moved `L` cells right,
  with `L % 64 ≠ 0`, has the code `rainA` or `rainB` at `r`.**

The natural-language argument is `EdgeTreeCheck.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open.Frames.EdgeTreeCheck

open Rule30Open.Frames.EdgeTree
open Ruliology.CellularAutomata.Rule30FrozenRuler (iter)

/-- The first `n` values of a sequence. -/
def seg (f : Nat → Bool) : Nat → List Bool
  | 0 => []
  | n + 1 => f 0 :: seg (fun i => f (i + 1)) n

/-- The sequence that starts at `b` and flips where `g` is black, one entry per entry of `g`. -/
def integ : Bool → List Bool → List Bool
  | _, [] => []
  | b, g :: gs => b :: integ (xor b g) gs

/-- The parity of a list. -/
def par : List Bool → Bool
  | [] => false
  | g :: gs => xor g (par gs)

/-- Entrywise OR. -/
def orW : List Bool → List Bool → List Bool
  | a :: as, b :: bs => (a || b) :: orW as bs
  | _, _ => []

/-- `n` values alternating from `b`. -/
def altList (b : Bool) : Nat → List Bool
  | 0 => []
  | n + 1 => b :: altList (!b) n

/-- True when no walk of columns of length `fuel` starts at the pair `(v, w)`. -/
def dead : Nat → List Bool → List Bool → Bool
  | 0, _, _ => false
  | n + 1, v, w =>
    if par (orW w v) then true
    else dead n w (integ false (orW w v)) && dead n w (integ true (orW w v))

theorem seg_orW (f g : Nat → Bool) : ∀ n, orW (seg f n) (seg g n) = seg (fun i => f i || g i) n := by
  intro n
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    show (f 0 || g 0) :: orW (seg (fun i => f (i + 1)) n) (seg (fun i => g (i + 1)) n) = _
    rw [ih]; rfl

theorem integ_seg (x g : Nat → Bool) (h : ∀ i, x (i + 1) = xor (x i) (g i)) :
    ∀ n, integ (x 0) (seg g n) = seg x n := by
  intro n
  induction n generalizing x g with
  | zero => rfl
  | succ n ih =>
    show x 0 :: integ (xor (x 0) (g 0)) (seg (fun i => g (i + 1)) n) = x 0 :: seg (fun i => x (i + 1)) n
    rw [← h 0, ih (fun i => x (i + 1)) (fun i => g (i + 1)) (fun i => h (i + 1))]

theorem par_seg (x g : Nat → Bool) (h : ∀ i, x (i + 1) = xor (x i) (g i)) :
    ∀ n, x n = xor (x 0) (par (seg g n)) := by
  intro n
  induction n generalizing x g with
  | zero => cases x 0 <;> rfl
  | succ n ih =>
    have := ih (fun i => x (i + 1)) (fun i => g (i + 1)) (fun i => h (i + 1))
    show x (n + 1) = xor (x 0) (xor (g 0) (par (seg (fun i => g (i + 1)) n)))
    rw [this, h 0]
    generalize x 0 = a
    generalize g 0 = b
    generalize par (seg (fun i => g (i + 1)) n) = p
    cases a <;> cases b <;> cases p <;> rfl

theorem seg_alt (f : Nat → Bool) (hf : Alt f) : ∀ n, seg f n = altList (f 0) n := by
  intro n
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    show f 0 :: seg (fun i => f (i + 1)) n = f 0 :: altList (!f 0) n
    rw [ih (fun i => f (i + 1)) (fun i => hf (i + 1)), hf 0]

theorem dead_sound (c : Nat → Bool) (L : Nat) (hp : iter L c = c) :
    ∀ n e, dead n (seg (col c e) L) (seg (col c (e + 1)) L) = true → False := by
  intro n
  induction n with
  | zero => intro e h; cases h
  | succ n ih =>
    intro e h
    have hg : orW (seg (col c (e + 1)) L) (seg (col c e) L) =
        seg (fun i => col c (e + 1) i || col c e i) L := seg_orW _ _ L
    have step : ∀ i, col c (e + 2) (i + 1) = xor (col c (e + 2) i) (col c (e + 1) i || col c e i) :=
      fun i => col_succ c e i
    have close : col c (e + 2) L = col c (e + 2) 0 := by
      show iter L c (e + 2) = iter 0 c (e + 2)
      rw [hp]; rfl
    have hpar := par_seg (col c (e + 2)) _ step L
    rw [close] at hpar
    have hpar0 : par (seg (fun i => col c (e + 1) i || col c e i) L) = false := by
      revert hpar
      generalize col c (e + 2) 0 = a
      generalize par (seg (fun i => col c (e + 1) i || col c e i) L) = p
      cases a <;> cases p <;> decide
    have hint := integ_seg (col c (e + 2)) _ step L
    simp only [dead] at h
    rw [hg, hpar0] at h
    simp only [Bool.false_eq_true, ite_false, Bool.and_eq_true] at h
    cases hx : col c (e + 2) 0
    · rw [hx] at hint
      rw [hint] at h
      exact ih (e + 1) h.1
    · rw [hx] at hint
      rw [hint] at h
      exact ih (e + 1) h.2

theorem dead_false : dead 16 (altList false 32) (altList false 32) = true := by decide +kernel

theorem dead_true : dead 16 (altList true 32) (altList true 32) = true := by decide +kernel

theorem period_32 (c : Nat → Bool) (h0 : c 0 = true) (hp : iter 32 c = c) :
    c = Rule30Open.Frames.EdgePeriodFour.rainA ∨ c = Rule30Open.Frames.EdgePeriodFour.rainB := by
  rcases rain_or_branch c h0 with hr | ⟨j, _, ha, he⟩
  · exact hr
  · exfalso
    apply dead_sound c 32 hp 16 j
    rw [he, seg_alt _ ha]
    cases col c j 0
    · exact dead_false
    · exact dead_true

theorem rain_of_return_64 (init : Int → Bool) (r : Int) (hr : ∀ p, r < p → init p = false)
    (h0 : init r = true) (L : Nat) (hL : L % 64 ≠ 0)
    (h : ∀ x, evolve init L (x + (L : Int)) = init x) :
    LightReturnRows.codeAt init r = Rule30Open.Frames.EdgePeriodFour.rainA ∨
      LightReturnRows.codeAt init r = Rule30Open.Frames.EdgePeriodFour.rainB := by
  have fac : ∃ a q : Nat, a ≤ 5 ∧ q % 2 = 1 ∧ L = 2 ^ a * q := by
    by_cases h5 : L % 32 = 0
    · exact ⟨5, L / 32, by omega, by omega, by show L = 32 * (L / 32); omega⟩
    · obtain ⟨a, q, ha, hq, e⟩ := LightReturnClassified.factor_of_mod L h5
      exact ⟨a, q, by omega, hq, e⟩
  obtain ⟨a, q, ha, hq, rfl⟩ := fac
  have hp := LightReturnRows.pow_two_return init r hr a q hq h
  have hi := LightReturnRows.iter_code_of_return init r hr (2 ^ a) hp
  have e32 : 2 ^ a * 2 ^ (5 - a) = 32 := by
    rw [← Nat.pow_add, Nat.add_sub_cancel' ha]
  have h32 := LightReturnClassified.iter_mul_of (LightReturnRows.codeAt init r) (2 ^ a) hi (2 ^ (5 - a))
  rw [e32] at h32
  have hc0 : LightReturnRows.codeAt init r 0 = true := by
    show init (r - ((0 : Nat) : Int)) = true
    simpa using h0
  exact period_32 _ hc0 h32

end Rule30Open.Frames.EdgeTreeCheck
