module

public import Rule30Open.Analogs.Rule150Descent
public import Ruliology.CellularAutomata.Rule30Realization

/-!
# Rules 90 and 150: the eventually periodic columns of a finite row are its mirror axes

Under Rule 90, `x' = x_(-1) xor x_(+1)`, and Rule 150, `x' = x_(-1) xor x xor x_(+1)`, the column `p` of the orbit of
a finite row `y` is eventually periodic exactly when `y` is mirror-symmetric about `p`: `y (p + m) = y (p - m)` for
every `m` (`iter90_column_periodic_iff`, `iter150_column_periodic_iff`). Both rules are `stepLin b`,
`x' = x_(-1) xor (b && x) xor x_(+1)`, and one proof covers both (`linear_column_periodic_iff`).

* **If.** The mirror about `p` commutes with the rule, so a symmetric row stays symmetric, the two neighbors of the
  axis agree, and the axis reads `u (t + 1) = b && u t`: 0 from time 1 under Rule 90, constant under Rule 150
  (`symm_axis_column`).
* **Only if.** Split the row moved to `p = 0` into its symmetric part `symPart`, its left half mirrored onto the right,
  and its skew part `skewPart`, `y m xor y (-m)` on the cells `m ≥ 1` (`symPart_xor_skewPart`). By linearity the
  column of the skew part is eventually periodic too (`skewPart_periodic`), and then the skew part is 0
  (`skew_descent`). Two steps of the rule are one step on each sublattice (`stepLin_twice`, `iterLin_double`, which
  generalize `step150_twice` and `iter150_double`), so the even times of the column are the column of the even
  sublattice, and the odd times the column of a row whose skew part lives on at most half as many cells. The descent
  on the width ends at the single cell next to the axis, whose column `u` has `u (2r) = 0` and
  `u (2r + 1) = u r xor c r`, `c` the axis column of the single cell; a descent on the period shows that no such `u`
  is eventually periodic (`halving_not_periodic`, `single_one_not_periodic`).

Consequences: a nonzero finite row has at most one eventually periodic column (`at_most_one_periodic_column`), and
from the single cell the center is the only eventually periodic column under Rules 90, 150 and 210
(`run90_column_periodic_iff`, `run150_column_periodic_iff`, `run210_column_periodic_iff`), which sharpens the kit's
`Rule30Realization.barrier`. Rule 30 is Rule 150 plus `x && x_(+1)`, and the two-step identity has no counterpart for
it.

The natural-language argument is `SymmetricAxes.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

open Ruliology.CellularAutomata.Rule30Jen (EventuallyPeriodic common_period)

/-! ### The two rules -/

/-- The linear rule `x' = x_(-1) xor (b && x) xor x_(+1)`: Rule 90 for `b = false`, Rule 150 for `b = true`. -/
def stepLin (b : Bool) (y : Int → Bool) : Int → Bool := fun x => xor (xor (y (x - 1)) (b && y x)) (y (x + 1))

/-- The orbit of `y` under `stepLin b`. -/
def iterLin (b : Bool) (y : Int → Bool) : Nat → Int → Bool
  | 0 => y
  | n + 1 => stepLin b (iterLin b y n)

/-- Rule 90 on the whole line. -/
def step90 (y : Int → Bool) : Int → Bool := fun x => xor (y (x - 1)) (y (x + 1))

/-- The orbit of `y` under Rule 90. -/
def iter90 (y : Int → Bool) : Nat → Int → Bool
  | 0 => y
  | n + 1 => step90 (iter90 y n)

theorem iter90_eq (y : Int → Bool) : ∀ n, iter90 y n = iterLin false y n
  | 0 => rfl
  | n + 1 => by
    show step90 (iter90 y n) = stepLin false (iterLin false y n)
    rw [iter90_eq y n]
    funext x
    show xor (iterLin false y n (x - 1)) (iterLin false y n (x + 1)) =
      xor (xor (iterLin false y n (x - 1)) false) (iterLin false y n (x + 1))
    cases iterLin false y n (x - 1) <;> rfl

theorem iter150_eq (y : Int → Bool) : ∀ n, iter150 y n = iterLin true y n
  | 0 => rfl
  | n + 1 => by
    show step150 (iter150 y n) = stepLin true (iterLin true y n)
    rw [iter150_eq y n]
    rfl

/-! ### Linearity, mirror, translation -/

/-- The orbit from `y` is the orbit from one step of `y`, one step on. -/
theorem iterLin_succ (b : Bool) (y : Int → Bool) : ∀ n, iterLin b y (n + 1) = iterLin b (stepLin b y) n
  | 0 => rfl
  | n + 1 => by
    show stepLin b (iterLin b y (n + 1)) = stepLin b (iterLin b (stepLin b y) n)
    rw [iterLin_succ b y n]

theorem iterLin_false (b : Bool) : ∀ (n : Nat) (x : Int), iterLin b (fun _ => false) n x = false
  | 0, _ => rfl
  | n + 1, x => by
    show xor (xor (iterLin b (fun _ => false) n (x - 1)) (b && iterLin b (fun _ => false) n x))
      (iterLin b (fun _ => false) n (x + 1)) = false
    rw [iterLin_false b n (x - 1), iterLin_false b n x, iterLin_false b n (x + 1)]
    cases b <;> rfl

/-- The rule is linear over `𝔽₂`. -/
theorem iterLin_xor (b : Bool) (y z : Int → Bool) : ∀ (n : Nat) (x : Int),
    iterLin b (fun w => xor (y w) (z w)) n x = xor (iterLin b y n x) (iterLin b z n x)
  | 0, _ => rfl
  | n + 1, x => by
    show xor (xor (iterLin b (fun w => xor (y w) (z w)) n (x - 1)) (b && iterLin b (fun w => xor (y w) (z w)) n x))
        (iterLin b (fun w => xor (y w) (z w)) n (x + 1)) =
      xor (xor (xor (iterLin b y n (x - 1)) (b && iterLin b y n x)) (iterLin b y n (x + 1)))
        (xor (xor (iterLin b z n (x - 1)) (b && iterLin b z n x)) (iterLin b z n (x + 1)))
    rw [iterLin_xor b y z n (x - 1), iterLin_xor b y z n x, iterLin_xor b y z n (x + 1)]
    generalize iterLin b y n (x - 1) = a₁
    generalize iterLin b y n x = a₂
    generalize iterLin b y n (x + 1) = a₃
    generalize iterLin b z n (x - 1) = c₁
    generalize iterLin b z n x = c₂
    generalize iterLin b z n (x + 1) = c₃
    revert a₁ a₂ a₃ c₁ c₂ c₃ b
    decide

/-- The rule commutes with the mirror `x ↦ c - x`. -/
theorem iterLin_mirror (b : Bool) (y : Int → Bool) (c : Int) : ∀ (n : Nat) (x : Int),
    iterLin b (fun z => y (c - z)) n x = iterLin b y n (c - x)
  | 0, _ => rfl
  | n + 1, x => by
    show xor (xor (iterLin b (fun z => y (c - z)) n (x - 1)) (b && iterLin b (fun z => y (c - z)) n x))
        (iterLin b (fun z => y (c - z)) n (x + 1)) =
      xor (xor (iterLin b y n (c - x - 1)) (b && iterLin b y n (c - x))) (iterLin b y n (c - x + 1))
    rw [iterLin_mirror b y c n (x - 1), iterLin_mirror b y c n x, iterLin_mirror b y c n (x + 1),
      show c - (x - 1) = c - x + 1 by omega, show c - (x + 1) = c - x - 1 by omega]
    generalize iterLin b y n (c - x + 1) = a
    generalize iterLin b y n (c - x) = m
    generalize iterLin b y n (c - x - 1) = d
    revert a m d b
    decide

/-- The rule commutes with translations. -/
theorem iterLin_shift (b : Bool) (y : Int → Bool) (c : Int) : ∀ (n : Nat) (x : Int),
    iterLin b (fun z => y (z + c)) n x = iterLin b y n (x + c)
  | 0, _ => rfl
  | n + 1, x => by
    show xor (xor (iterLin b (fun z => y (z + c)) n (x - 1)) (b && iterLin b (fun z => y (z + c)) n x))
        (iterLin b (fun z => y (z + c)) n (x + 1)) =
      xor (xor (iterLin b y n (x + c - 1)) (b && iterLin b y n (x + c))) (iterLin b y n (x + c + 1))
    rw [iterLin_shift b y c n (x - 1), iterLin_shift b y c n x, iterLin_shift b y c n (x + 1),
      show x - 1 + c = x + c - 1 by omega, show x + 1 + c = x + c + 1 by omega]

/-! ### Two steps are one step on each sublattice -/

/-- Over `𝔽₂` the cross terms of two steps cancel in pairs: `(z⁻¹ + b + z)² = z⁻² + b + z²`. -/
theorem stepLin_twice (b : Bool) (y : Int → Bool) (x : Int) :
    stepLin b (stepLin b y) x = xor (xor (y (x - 2)) (b && y x)) (y (x + 2)) := by
  show xor (xor (xor (xor (y (x - 1 - 1)) (b && y (x - 1))) (y (x - 1 + 1)))
    (b && xor (xor (y (x - 1)) (b && y x)) (y (x + 1))))
    (xor (xor (y (x + 1 - 1)) (b && y (x + 1))) (y (x + 1 + 1))) = _
  rw [show x - 1 - 1 = x - 2 by omega, show x - 1 + 1 = x by omega, show x + 1 - 1 = x by omega,
    show x + 1 + 1 = x + 2 by omega]
  generalize y (x - 2) = a
  generalize y (x - 1) = d
  generalize y x = m
  generalize y (x + 1) = e
  generalize y (x + 2) = f
  revert a d m e f b
  decide

/-- Steps `2r` of the rule, read on the sublattice `2x + i`, are `r` steps on that sublattice. -/
theorem iterLin_double (b : Bool) (y : Int → Bool) (i : Int) : ∀ (r : Nat) (x : Int),
    iterLin b y (2 * r) (2 * x + i) = iterLin b (fun z => y (2 * z + i)) r x
  | 0, _ => rfl
  | r + 1, x => by
    show stepLin b (stepLin b (iterLin b y (2 * r))) (2 * x + i) =
      stepLin b (iterLin b (fun z => y (2 * z + i)) r) x
    rw [stepLin_twice]
    show xor (xor (iterLin b y (2 * r) (2 * x + i - 2)) (b && iterLin b y (2 * r) (2 * x + i)))
        (iterLin b y (2 * r) (2 * x + i + 2)) =
      xor (xor (iterLin b (fun z => y (2 * z + i)) r (x - 1)) (b && iterLin b (fun z => y (2 * z + i)) r x))
        (iterLin b (fun z => y (2 * z + i)) r (x + 1))
    rw [show 2 * x + i - 2 = 2 * (x - 1) + i by omega, show 2 * x + i + 2 = 2 * (x + 1) + i by omega,
      iterLin_double b y i r (x - 1), iterLin_double b y i r x, iterLin_double b y i r (x + 1)]

/-! ### Eventually periodic sequences -/

theorem periodic_xor {f g : Nat → Bool} (hf : EventuallyPeriodic f) (hg : EventuallyPeriodic g) :
    EventuallyPeriodic fun t => xor (f t) (g t) := by
  obtain ⟨T, P, hP, h₁, h₂⟩ := common_period hf hg
  exact ⟨T, P, hP, fun t ht => by
    show xor (f (t + P)) (g (t + P)) = xor (f t) (g t)
    rw [h₁ t ht, h₂ t ht]⟩

/-- The terms `2r + j` of an eventually periodic sequence form an eventually periodic sequence. -/
theorem periodic_two_mul_add {f : Nat → Bool} (hf : EventuallyPeriodic f) (j : Nat) :
    EventuallyPeriodic fun r => f (2 * r + j) := by
  obtain ⟨T, P, hP, h⟩ := hf
  refine ⟨T, P, hP, fun r hr => ?_⟩
  show f (2 * (r + P) + j) = f (2 * r + j)
  rw [show 2 * (r + P) + j = (2 * r + j + P) + P by omega, h _ (by omega), h _ (by omega)]

theorem eq_of_xor_eq_false {a c : Bool} (h : xor a c = false) : a = c := by
  revert h; cases a <;> cases c <;> decide

/-! ### Even and odd times of a column -/

/-- The even times of the column `0` are the column `0` of the even sublattice. -/
theorem iterLin_column_even (b : Bool) (y : Int → Bool) (r : Nat) :
    iterLin b y (2 * r) 0 = iterLin b (fun z => y (2 * z + 0)) r 0 :=
  iterLin_double b y 0 r 0

/-- The odd times of the column `0` are the column `0` of the even sublattice one step on. -/
theorem iterLin_column_odd (b : Bool) (y : Int → Bool) (r : Nat) :
    iterLin b y (2 * r + 1) 0 = iterLin b (fun z => stepLin b y (2 * z + 0)) r 0 := by
  rw [iterLin_succ]
  exact iterLin_column_even b (stepLin b y) r

theorem periodic_even_times {b : Bool} {y : Int → Bool} (h : EventuallyPeriodic fun t => iterLin b y t 0) :
    EventuallyPeriodic fun r => iterLin b (fun z => y (2 * z + 0)) r 0 := by
  obtain ⟨T, P, hP, h⟩ := periodic_two_mul_add h 0
  exact ⟨T, P, hP, fun r hr => by
    show iterLin b (fun z => y (2 * z + 0)) (r + P) 0 = iterLin b (fun z => y (2 * z + 0)) r 0
    rw [← iterLin_column_even, ← iterLin_column_even]; exact h r hr⟩

theorem periodic_odd_times {b : Bool} {y : Int → Bool} (h : EventuallyPeriodic fun t => iterLin b y t 0) :
    EventuallyPeriodic fun r => iterLin b (fun z => stepLin b y (2 * z + 0)) r 0 := by
  obtain ⟨T, P, hP, h⟩ := periodic_two_mul_add h 1
  exact ⟨T, P, hP, fun r hr => by
    show iterLin b (fun z => stepLin b y (2 * z + 0)) (r + P) 0 = iterLin b (fun z => stepLin b y (2 * z + 0)) r 0
    rw [← iterLin_column_odd, ← iterLin_column_odd]; exact h r hr⟩

/-! ### Symmetric rows: the "if" direction -/

/-- A row symmetric about `0` stays symmetric about `0`. -/
theorem iterLin_symm (b : Bool) (y : Int → Bool) (hy : ∀ m, y (-m) = y m) (n : Nat) (m : Int) :
    iterLin b y n (-m) = iterLin b y n m := by
  have h := iterLin_mirror b y 0 n m
  rw [show (fun z => y (0 - z)) = y from funext fun z => by rw [show (0 : Int) - z = -z by omega, hy],
    show (0 : Int) - m = -m by omega] at h
  exact h.symm

/-- **The axis of a symmetric row** reads `u (t + 1) = b && u t`: its two neighbors agree. -/
theorem symm_axis_column (b : Bool) (y : Int → Bool) (hy : ∀ m, y (-m) = y m) (n : Nat) :
    iterLin b y (n + 1) 0 = (b && iterLin b y n 0) := by
  show xor (xor (iterLin b y n (0 - 1)) (b && iterLin b y n 0)) (iterLin b y n (0 + 1)) = _
  rw [show (0 : Int) - 1 = -1 by rfl, show (0 : Int) + 1 = 1 by rfl, iterLin_symm b y hy n 1]
  generalize iterLin b y n 1 = a
  generalize iterLin b y n 0 = m
  revert a m b
  decide

/-- The axis of a symmetric row is constant from time 1. -/
theorem symm_axis_periodic (b : Bool) (y : Int → Bool) (hy : ∀ m, y (-m) = y m) :
    EventuallyPeriodic fun t => iterLin b y t 0 :=
  ⟨1, 1, Nat.one_pos, fun t ht => by
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    show iterLin b y (s + 1 + 1) 0 = iterLin b y (s + 1) 0
    rw [symm_axis_column b y hy (s + 1), symm_axis_column b y hy s]
    cases b <;> rfl⟩

/-! ### The symmetric part and the skew part -/

/-- The symmetric part of `y` about `0`: its left half, mirrored onto the right. -/
def symPart (y : Int → Bool) (x : Int) : Bool := if 0 < x then y (-x) else y x

/-- The skew part of `y` about `0`: `y x xor y (-x)` on the cells `x ≥ 1`, and 0 elsewhere. -/
def skewPart (y : Int → Bool) (x : Int) : Bool := if 0 < x then xor (y x) (y (-x)) else false

theorem symPart_symm (y : Int → Bool) (m : Int) : symPart y (-m) = symPart y m := by
  unfold symPart
  rcases (show 0 < m ∨ m = 0 ∨ m < 0 by omega) with h | h | h
  · rw [ite_eq_right (show ¬ (0 < -m) by omega), ite_eq_left h]
  · subst h; rfl
  · rw [ite_eq_left (show 0 < -m by omega), ite_eq_right (show ¬ (0 < m) by omega), show -(-m) = m by omega]

/-- A row is its symmetric part xor its skew part. -/
theorem symPart_xor_skewPart (y : Int → Bool) (x : Int) : xor (symPart y x) (skewPart y x) = y x := by
  unfold symPart skewPart
  by_cases h : 0 < x
  · rw [ite_eq_left h, ite_eq_left h]; cases y x <;> cases y (-x) <;> rfl
  · rw [ite_eq_right h, ite_eq_right h]; cases y x <;> rfl

/-- If the column `0` of `y` is eventually periodic, so is the column `0` of its skew part, since the column of the
symmetric part is. -/
theorem skewPart_periodic (b : Bool) (y : Int → Bool) (h : EventuallyPeriodic fun t => iterLin b y t 0) :
    EventuallyPeriodic fun t => iterLin b (skewPart y) t 0 := by
  have e : ∀ t, iterLin b (skewPart y) t 0 = xor (iterLin b y t 0) (iterLin b (symPart y) t 0) := fun t => by
    have hs : skewPart y = fun x => xor (y x) (symPart y x) := funext fun x => by
      rw [← symPart_xor_skewPart y x]; cases symPart y x <;> cases skewPart y x <;> rfl
    rw [hs, iterLin_xor]
  obtain ⟨T, P, hP, h⟩ := periodic_xor h (symm_axis_periodic b (symPart y) (symPart_symm y))
  exact ⟨T, P, hP, fun t ht => by
    show iterLin b (skewPart y) (t + P) 0 = iterLin b (skewPart y) t 0
    rw [e, e]; exact h t ht⟩

/-! ### The single cell next to the axis -/

/-- **No sequence with `u (2r) = 0` and `u (2r + 1) = u r xor c r` is eventually periodic**, when `c` is constant from
time 1 and differs from `u` at arbitrarily late times. By descent on the period: an odd period carries the even times,
where `u` is 0, to the odd times, so `u` agrees with `c` from some time on; an even period `2Q` gives `u` the period
`Q`. -/
theorem halving_not_periodic (u c : Nat → Bool) (hev : ∀ r, u (2 * r) = false)
    (hodd : ∀ r, u (2 * r + 1) = xor (u r) (c r)) (hc : ∀ r, 1 ≤ r → c (r + 1) = c r)
    (hne : ∀ S, ∃ s, S ≤ s ∧ u s ≠ c s) :
    ∀ (n P T : Nat), P ≤ n → 0 < P → ¬ ∀ t, T ≤ t → u (t + P) = u t := by
  have hc' : ∀ k r, 1 ≤ r → c (r + k) = c r := by
    intro k
    induction k with
    | zero => intro r _; rfl
    | succ k ih => intro r hr; rw [show r + (k + 1) = (r + k) + 1 by omega, hc _ (by omega), ih r hr]
  intro n
  induction n with
  | zero => intro P T hPn hP; omega
  | succ n ih =>
    intro P T hPn hP h
    obtain ⟨Q, hQ | hQ⟩ : ∃ Q, P = 2 * Q ∨ P = 2 * Q + 1 := ⟨P / 2, by omega⟩
    · -- an even period `2Q`: `u` has period `Q` from `max T 1`
      subst hQ
      apply ih Q (max T 1) (by omega) (by omega)
      intro r hr
      have h1 := h (2 * r + 1) (by omega)
      rw [show 2 * r + 1 + 2 * Q = 2 * (r + Q) + 1 by omega, hodd, hodd, hc' Q r (by omega)] at h1
      revert h1
      cases u (r + Q) <;> cases u r <;> cases c r <;> decide
    · -- an odd period `2Q + 1`: `u` agrees with `c` from `T + Q` on
      subst hQ
      obtain ⟨s, hs, hne⟩ := hne (T + Q)
      apply hne
      have h1 := h (2 * (s - Q)) (by omega)
      rw [show 2 * (s - Q) + (2 * Q + 1) = 2 * s + 1 by omega, hodd, hev] at h1
      exact eq_of_xor_eq_false h1

/-- The column `0` from the single cell at `0`: `1` at time 0, then `b` and `b && ...`. -/
theorem single_zero_column (b : Bool) (n : Nat) :
    iterLin b (fun x => decide (x = 0)) (n + 1) 0 = (b && iterLin b (fun x => decide (x = 0)) n 0) :=
  symm_axis_column b _ (fun m => by
    by_cases h : m = 0
    · subst h; rfl
    · rw [decide_eq_false h, decide_eq_false (show ¬ (-m = 0) by omega)]) n

/-- The column `0` from the single cell at `1` reads 0 at even times. -/
theorem single_one_even (b : Bool) (r : Nat) : iterLin b (fun x => decide (x = 1)) (2 * r) 0 = false := by
  rw [iterLin_column_even, show (fun z : Int => decide (2 * z + 0 = 1)) = fun _ => false from
    funext fun z => decide_eq_false (by omega)]
  exact iterLin_false b r 0

/-- At odd times it reads `u (2r + 1) = u r xor c r`, `c` the column from the single cell at `0`: one step of the
single cell at `1`, on the even sublattice, is the pair of cells `0` and `1`. -/
theorem single_one_odd (b : Bool) (r : Nat) :
    iterLin b (fun x => decide (x = 1)) (2 * r + 1) 0 =
      xor (iterLin b (fun x => decide (x = 1)) r 0) (iterLin b (fun x => decide (x = 0)) r 0) := by
  rw [iterLin_column_odd]
  have e : (fun z : Int => stepLin b (fun x => decide (x = 1)) (2 * z + 0)) =
      fun z => xor (decide (z = 1)) (decide (z = 0)) := by
    funext z
    show xor (xor (decide (2 * z + 0 - 1 = 1)) (b && decide (2 * z + 0 = 1))) (decide (2 * z + 0 + 1 = 1)) = _
    rcases (show z = 0 ∨ z = 1 ∨ (z ≠ 0 ∧ z ≠ 1) by omega) with h | h | ⟨h0, h1⟩
    · subst h; cases b <;> decide
    · subst h; cases b <;> decide
    · rw [decide_eq_false (show ¬ (2 * z + 0 - 1 = 1) by omega), decide_eq_false (show ¬ (2 * z + 0 = 1) by omega),
        decide_eq_false (show ¬ (2 * z + 0 + 1 = 1) by omega), decide_eq_false h1, decide_eq_false h0]
      cases b <;> rfl
  rw [e, iterLin_xor]

/-- **The single cell next to the axis has an aperiodic axis column**, under Rules 90 and 150. -/
theorem single_one_not_periodic (b : Bool) :
    ¬ EventuallyPeriodic fun t => iterLin b (fun x => decide (x = 1)) t 0 := by
  rintro ⟨T, P, hP, h⟩
  let u : Nat → Bool := fun t => iterLin b (fun x => decide (x = 1)) t 0
  let c : Nat → Bool := fun t => iterLin b (fun x => decide (x = 0)) t 0
  have hcs : ∀ n, c (n + 1) = (b && c n) := single_zero_column b
  have hne : ∀ S, ∃ s, S ≤ s ∧ u s ≠ c s := by
    cases b with
    | true =>
      -- Rule 150: `c` is constantly 1 and `u` is 0 at even times
      have hct : ∀ n, c n = true := by
        intro n; induction n with
        | zero => rfl
        | succ n ih => rw [hcs, ih]; rfl
      intro S
      refine ⟨2 * S, by omega, ?_⟩
      show iterLin true (fun x => decide (x = 1)) (2 * S) 0 ≠ c (2 * S)
      rw [single_one_even, hct]
      decide
    | false =>
      -- Rule 90: `c` is 0 from time 1 and `u` is 1 at times `1, 3, 7, 15, ...`
      have hcf : ∀ n, c (n + 1) = false := fun n => by rw [hcs]; rfl
      have hu : ∀ S, ∃ s, S ≤ s ∧ 1 ≤ s ∧ u s = true := by
        intro S
        induction S with
        | zero =>
          refine ⟨1, by omega, by omega, ?_⟩
          show iterLin false (fun x => decide (x = 1)) (2 * 0 + 1) 0 = true
          rw [single_one_odd]
          rfl
        | succ S ih =>
          obtain ⟨s, hs, hs1, hus⟩ := ih
          refine ⟨2 * s + 1, by omega, by omega, ?_⟩
          show iterLin false (fun x => decide (x = 1)) (2 * s + 1) 0 = true
          rw [single_one_odd]
          obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
          show xor (u (s' + 1)) (c (s' + 1)) = true
          rw [hus, hcf]
          rfl
      intro S
      obtain ⟨s, hs, hs1, hus⟩ := hu S
      obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
      refine ⟨s' + 1, hs, ?_⟩
      rw [hus, hcf]
      decide
  exact halving_not_periodic u c (single_one_even b) (single_one_odd b)
    (fun r hr => by
      obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
      rw [hcs, hcs r']
      cases b <;> rfl)
    hne P P T (Nat.le_refl P) hP h

/-! ### The descent -/

/-- **The descent.** A row on the cells `1 .. N` whose column `0` is eventually periodic is 0. The even times of the
column are the column of the even sublattice, which lives on `1 .. N / 2`; once that is 0, the odd times are the
column of `B z = A (2z - 1) xor A (2z + 1)`, whose skew part lives on `1 .. (N + 1) / 2`. Both are narrower once
`N ≥ 2`, and for `N = 1` the row is the single cell next to the axis (`single_one_not_periodic`). -/
theorem skew_descent (b : Bool) : ∀ (n N : Nat), N ≤ n → ∀ A : Int → Bool,
    (∀ x : Int, x < 1 ∨ (N : Int) < x → A x = false) →
    (EventuallyPeriodic fun t => iterLin b A t 0) → ∀ x, A x = false := by
  intro n
  induction n with
  | zero =>
    intro N hN A hA _ x
    exact hA x (by omega)
  | succ n ih =>
    intro N hN A hA hper
    by_cases hNn : N ≤ n
    · exact ih N hNn A hA hper
    by_cases hN1 : N = 1
    · -- the single cell next to the axis
      subst hN1
      have hA' : ∀ x : Int, x ≠ 1 → A x = false := fun x hx => hA x (by omega)
      cases h1 : A 1 with
      | false =>
        intro x
        by_cases hx : x = 1
        · subst hx; exact h1
        · exact hA' x hx
      | true =>
        exfalso
        have e : A = fun x => decide (x = 1) := funext fun x => by
          by_cases hx : x = 1
          · subst hx; rw [h1]; rfl
          · rw [hA' x hx, decide_eq_false hx]
        rw [e] at hper
        exact single_one_not_periodic b hper
    -- `N ≥ 2`: the even sublattice lives on `1 .. N / 2`
    have heven : ∀ z : Int, A (2 * z + 0) = false :=
      ih (N / 2) (by omega) (fun z => A (2 * z + 0)) (fun x hx => hA _ (by omega)) (periodic_even_times hper)
    -- the even sublattice one step on is `B z = A (2z - 1) xor A (2z + 1)`
    let B : Int → Bool := fun z => stepLin b A (2 * z + 0)
    have hB : ∀ z : Int, B z = xor (A (2 * z - 1)) (A (2 * z + 1)) := fun z => by
      show xor (xor (A (2 * z + 0 - 1)) (b && A (2 * z + 0))) (A (2 * z + 0 + 1)) = _
      rw [heven z, show 2 * z + 0 - 1 = 2 * z - 1 by omega, show 2 * z + 0 + 1 = 2 * z + 1 by omega]
      cases b <;> cases A (2 * z - 1) <;> rfl
    -- its skew part lives on `1 .. (N + 1) / 2`
    have hskew := ih ((N + 1) / 2) (by omega) (skewPart B) (fun x hx => by
      unfold skewPart
      by_cases h0 : 0 < x
      · rw [ite_eq_left h0, hB, hB, hA (2 * x - 1) (by omega), hA (2 * x + 1) (by omega),
          hA (2 * -x - 1) (by omega), hA (2 * -x + 1) (by omega)]
        rfl
      · exact ite_eq_right h0) (skewPart_periodic b B (periodic_odd_times hper))
    -- so `A (2z - 1) = A (2z + 1)` for `z ≥ 1`
    have hstep : ∀ z : Int, 1 ≤ z → A (2 * z - 1) = A (2 * z + 1) := fun z hz => by
      have h := hskew z
      unfold skewPart at h
      rw [ite_eq_left (show 0 < z by omega), hB, hB, hA (2 * -z - 1) (by omega), hA (2 * -z + 1) (by omega)] at h
      revert h
      cases A (2 * z - 1) <;> cases A (2 * z + 1) <;> decide
    -- and the odd cells are 0, from the right end down
    have hodd : ∀ z : Int, 0 ≤ z → A (2 * z + 1) = false := fun z hz => by
      have h : ∀ j : Nat, A (2 * z + 1) = A (2 * (z + j) + 1) := by
        intro j
        induction j with
        | zero => exact congrArg A (by omega)
        | succ j ihj =>
          rw [ihj]
          have e := hstep (z + j + 1) (by omega)
          rw [show 2 * (z + j + 1) - 1 = 2 * (z + j) + 1 by omega] at e
          rw [e]
          exact congrArg A (by omega)
      rw [h N]
      exact hA _ (by omega)
    intro x
    obtain ⟨z, hz | hz⟩ : ∃ z : Int, x = 2 * z + 0 ∨ x = 2 * z + 1 := ⟨x / 2, by omega⟩
    · subst hz; exact heven z
    · subst hz
      by_cases h0 : 0 ≤ z
      · exact hodd z h0
      · exact hA _ (by omega)

/-! ### The theorem -/

/-- **The eventually periodic columns of a finite row are its mirror axes**, under `stepLin b`: the column `p` of the
orbit of a row that is 0 outside `-N .. N` is eventually periodic iff `y (p + m) = y (p - m)` for every `m`. -/
theorem linear_column_periodic_iff (b : Bool) (y : Int → Bool) (N : Nat)
    (hy : ∀ x : Int, N < x.natAbs → y x = false) (p : Int) :
    (EventuallyPeriodic fun t => iterLin b y t p) ↔ ∀ m, y (p + m) = y (p - m) := by
  -- move the column to `0`
  have hcol : ∀ t, iterLin b y t p = iterLin b (fun z => y (z + p)) t 0 := fun t => by
    rw [iterLin_shift b y p t 0, show (0 : Int) + p = p by omega]
  have hiff : (EventuallyPeriodic fun t => iterLin b y t p) ↔
      EventuallyPeriodic fun t => iterLin b (fun z => y (z + p)) t 0 := by
    constructor
    · rintro ⟨T, P, hP, h⟩
      exact ⟨T, P, hP, fun t ht => by
        show iterLin b (fun z => y (z + p)) (t + P) 0 = iterLin b (fun z => y (z + p)) t 0
        rw [← hcol, ← hcol]; exact h t ht⟩
    · rintro ⟨T, P, hP, h⟩
      exact ⟨T, P, hP, fun t ht => by
        show iterLin b y (t + P) p = iterLin b y t p
        rw [hcol, hcol]; exact h t ht⟩
  rw [hiff]
  constructor
  · -- only if: the skew part about `p` is 0
    intro h m
    have h0 := skew_descent b (N + p.natAbs) (N + p.natAbs) (Nat.le_refl _) (skewPart fun z => y (z + p))
      (fun x hx => by
        unfold skewPart
        by_cases hx0 : 0 < x
        · rw [ite_eq_left hx0]
          show xor (y (x + p)) (y (-x + p)) = false
          rw [hy (x + p) (by omega), hy (-x + p) (by omega)]
          rfl
        · exact ite_eq_right hx0)
      (skewPart_periodic b _ h)
    rcases (show 0 < m ∨ m = 0 ∨ m < 0 by omega) with hm | hm | hm
    · have e := h0 m
      unfold skewPart at e
      rw [ite_eq_left hm] at e
      rw [show p + m = m + p by omega, show p - m = -m + p by omega]
      exact eq_of_xor_eq_false e
    · exact congrArg y (by omega)
    · have e := h0 (-m)
      unfold skewPart at e
      rw [ite_eq_left (show 0 < -m by omega)] at e
      rw [show p + m = -(-m) + p by omega, show p - m = -m + p by omega]
      exact (eq_of_xor_eq_false e).symm
  · -- if: the row moved to `0` is symmetric about `0`
    intro hs
    exact symm_axis_periodic b _ fun m => by
      show y (-m + p) = y (m + p)
      rw [show -m + p = p - m by omega, show m + p = p + m by omega, hs m]

/-- **Rule 90**: the column `p` of a finite row is eventually periodic iff the row is symmetric about `p`. -/
theorem iter90_column_periodic_iff (y : Int → Bool) (N : Nat) (hy : ∀ x : Int, N < x.natAbs → y x = false)
    (p : Int) : (EventuallyPeriodic fun t => iter90 y t p) ↔ ∀ m, y (p + m) = y (p - m) := by
  simp only [iter90_eq]
  exact linear_column_periodic_iff false y N hy p

/-- **Rule 150**: the column `p` of a finite row is eventually periodic iff the row is symmetric about `p`. -/
theorem iter150_column_periodic_iff (y : Int → Bool) (N : Nat) (hy : ∀ x : Int, N < x.natAbs → y x = false)
    (p : Int) : (EventuallyPeriodic fun t => iter150 y t p) ↔ ∀ m, y (p + m) = y (p - m) := by
  simp only [iter150_eq]
  exact linear_column_periodic_iff true y N hy p

/-! ### Consequences -/

/-- A finite row symmetric about two cells is 0: it is periodic with period twice their distance. -/
theorem two_axes_zero (y : Int → Bool) (N : Nat) (hy : ∀ x : Int, N < x.natAbs → y x = false) (p q : Int)
    (hpq : p < q) (sp : ∀ m, y (p + m) = y (p - m)) (sq : ∀ m, y (q + m) = y (q - m)) : ∀ x, y x = false := by
  have hshift : ∀ x, y x = y (x + 2 * (q - p)) := fun x => by
    have h1 := sp (x - p)
    have h2 := sq (x - 2 * p + q)
    rw [show p + (x - p) = x by omega, show p - (x - p) = 2 * p - x by omega] at h1
    rw [show q - (x - 2 * p + q) = 2 * p - x by omega, show q + (x - 2 * p + q) = x + 2 * (q - p) by omega] at h2
    rw [h1, h2]
  have hfar : ∀ (k : Nat) (x : Int), ∃ x', x + k ≤ x' ∧ y x' = y x := by
    intro k
    induction k with
    | zero => intro x; exact ⟨x, by omega, rfl⟩
    | succ k ih =>
      intro x
      obtain ⟨x', hx', hy'⟩ := ih x
      exact ⟨x' + 2 * (q - p), by omega, by rw [← hshift, hy']⟩
  intro x
  obtain ⟨x', hx', hyx⟩ := hfar (N + x.natAbs + 1) x
  rw [← hyx]
  exact hy x' (by omega)

/-- **A nonzero finite row has at most one eventually periodic column** under Rules 90 and 150: a row symmetric
about two cells is periodic, and a finite periodic row is 0. -/
theorem at_most_one_periodic_column (b : Bool) (y : Int → Bool) (N : Nat)
    (hy : ∀ x : Int, N < x.natAbs → y x = false) (p q : Int) (hpq : p ≠ q)
    (hp : EventuallyPeriodic fun t => iterLin b y t p) (hq : EventuallyPeriodic fun t => iterLin b y t q) :
    ∀ x, y x = false := by
  have sp := (linear_column_periodic_iff b y N hy p).1 hp
  have sq := (linear_column_periodic_iff b y N hy q).1 hq
  rcases (show p < q ∨ q < p by omega) with h | h
  · exact two_axes_zero y N hy p q h sp sq
  · exact two_axes_zero y N hy q p h sq sp

open Ruliology.CellularAutomata.Rule30Realization (run g90 g150 g210 run210_eq)

/-- The kit's single-seed Rule 90 is `iterLin false` from the single cell. -/
theorem run90_eq (t : Nat) : run g90 t = iterLin false (fun x => decide (x = 0)) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    funext p
    show xor (run g90 t (p - 1)) (g90 (run g90 t p) (run g90 t (p + 1))) =
      xor (xor (iterLin false (fun x => decide (x = 0)) t (p - 1))
        (false && iterLin false (fun x => decide (x = 0)) t p)) (iterLin false (fun x => decide (x = 0)) t (p + 1))
    rw [ih]
    generalize iterLin false (fun x => decide (x = 0)) t (p - 1) = a
    generalize iterLin false (fun x => decide (x = 0)) t p = m
    generalize iterLin false (fun x => decide (x = 0)) t (p + 1) = c
    cases a <;> cases m <;> cases c <;> rfl

/-- The kit's single-seed Rule 150 is `iterLin true` from the single cell. -/
theorem run150_eq (t : Nat) : run g150 t = iterLin true (fun x => decide (x = 0)) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    funext p
    show xor (run g150 t (p - 1)) (g150 (run g150 t p) (run g150 t (p + 1))) =
      xor (xor (iterLin true (fun x => decide (x = 0)) t (p - 1))
        (true && iterLin true (fun x => decide (x = 0)) t p)) (iterLin true (fun x => decide (x = 0)) t (p + 1))
    rw [ih]
    generalize iterLin true (fun x => decide (x = 0)) t (p - 1) = a
    generalize iterLin true (fun x => decide (x = 0)) t p = m
    generalize iterLin true (fun x => decide (x = 0)) t (p + 1) = c
    cases a <;> cases m <;> cases c <;> rfl

/-- The single cell is symmetric about `p` only for `p = 0`. -/
theorem single_symm_iff (p : Int) : (∀ m, decide (p + m = 0) = decide (p - m = 0)) ↔ p = 0 := by
  constructor
  · intro h
    have h1 := h p
    rw [show p - p = 0 by omega] at h1
    have h2 : p + p = 0 := of_decide_eq_true (h1.trans rfl)
    omega
  · intro hp m
    subst hp
    by_cases hm : m = 0
    · subst hm; rfl
    · rw [decide_eq_false (show ¬ (0 + m = 0) by omega), decide_eq_false (show ¬ (0 - m = 0) by omega)]

theorem single_zero_finite (x : Int) (hx : 0 < x.natAbs) : decide (x = 0) = false := decide_eq_false (by omega)

/-- **From the single cell, the center is the only eventually periodic column of Rule 90.** -/
theorem run90_column_periodic_iff (p : Int) : (EventuallyPeriodic fun t => run g90 t p) ↔ p = 0 := by
  simp only [run90_eq]
  rw [linear_column_periodic_iff false _ 0 single_zero_finite p]
  exact single_symm_iff p

/-- **From the single cell, the center is the only eventually periodic column of Rule 150.** -/
theorem run150_column_periodic_iff (p : Int) : (EventuallyPeriodic fun t => run g150 t p) ↔ p = 0 := by
  simp only [run150_eq]
  rw [linear_column_periodic_iff true _ 0 single_zero_finite p]
  exact single_symm_iff p

/-- **And of Rule 210**, which draws Rule 90's pattern from the single cell (the kit's `run210_eq`). -/
theorem run210_column_periodic_iff (p : Int) : (EventuallyPeriodic fun t => run g210 t p) ↔ p = 0 := by
  have e : (fun t => run g210 t p) = fun t => run g90 t p := funext fun t => (run210_eq t p).1
  rw [e]
  exact run90_column_periodic_iff p

end Rule30Open
