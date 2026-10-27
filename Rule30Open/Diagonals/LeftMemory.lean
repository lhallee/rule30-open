module

public import Ruliology.CellularAutomata.Rule30Diagonals

/-!
# The left diagonals remember only behind a white diagonal

Read the single-seed pattern along the diagonals parallel to its left edge, `D j t = cell t (j - t)`
(the kit's `Rule30Diagonals.D`). Each diagonal is fed by the two before it:
`D (j + 2) (t + 1) = D j t xor (D (j + 1) t || D (j + 2) t)` (`Rule30Diagonals.D_step`).

* Where `D (j + 1)` is black, the OR is 1 and `D (j + 2)` is reset: its next value is `!D j t`, whatever
  it was (`D_reset`). Where `D (j + 1)` is white, `D (j + 2)` adds `D j` to itself (`D_accumulate`).
* So if `D j` and `D (j + 1)` repeat with period `P` and `D (j + 1)` is black somewhere after that, then
  `D (j + 2)` repeats with period `P` too, from just after that black cell (`D_periodic_of_black`): it has
  forgotten everything before, the center column included.
* If instead `D (j + 1)` is white from some time on, `D (j + 2)` is a running XOR of `D j`. Over one period
  it changes by the parity of `D j` over a period (`D_shift_of_white`, `windowParity_periodic`), so it
  repeats with period `P` when that parity is even and flips every `P` steps when it is odd
  (`D_period_dichotomy`). In the odd case its least period is exactly doubled (`D_period_doubles`).

Hence an eventual period of a left diagonal can exceed those of the two diagonals before it only right
after an eventually white diagonal, and only when the diagonal two before has odd weight per period; and
only then does a diagonal keep a bit of the pattern's history. `D_two_white` and `D_three_flips` are the
first instance: diagonal 2 is white from time 2 on, and diagonal 3 alternates. Computation locates the
others below depth 100,000 (see `findings/diagonals/left-records.md`).

The kit's `Rule30Diagonals.D_periodic` proves that every left diagonal is eventually periodic with period
dividing `2^j`; this module explains where the periods grow.

The natural-language argument is `LeftMemory.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

open Ruliology.CellularAutomata.Rule30Diagonals

/-- The parity of the black cells of `f` at the times `t .. t + n - 1`. -/
def windowParity (f : Nat → Bool) (t : Nat) : Nat → Bool
  | 0 => false
  | n + 1 => xor (windowParity f t n) (f (t + n))

/-- Behind a black cell of diagonal `j + 1`, diagonal `j + 2` is reset to the opposite of diagonal `j`. -/
theorem D_reset (j t : Nat) (h : D (j + 1) t = true) : D (j + 2) (t + 1) = !D j t := by
  rw [D_step, h]
  generalize D j t = a
  cases a <;> rfl

/-- Behind a white cell of diagonal `j + 1`, diagonal `j + 2` adds diagonal `j` to itself. -/
theorem D_accumulate (j t : Nat) (h : D (j + 1) t = false) : D (j + 2) (t + 1) = xor (D j t) (D (j + 2) t) := by
  rw [D_step, h]
  rfl

/-- No memory behind a black cell: if diagonals `j` and `j + 1` repeat with period `P` from time `T`, and diagonal
`j + 1` is black at some time `r ≥ T`, then diagonal `j + 2` repeats with period `P` from time `r + 1`. -/
theorem D_periodic_of_black (j T P r : Nat)
    (hj : ∀ t, T ≤ t → D j (t + P) = D j t) (hj1 : ∀ t, T ≤ t → D (j + 1) (t + P) = D (j + 1) t)
    (hr : T ≤ r) (hb : D (j + 1) r = true) :
    ∀ t, r + 1 ≤ t → D (j + 2) (t + P) = D (j + 2) t := by
  have key : ∀ d, D (j + 2) (r + 1 + d + P) = D (j + 2) (r + 1 + d) := by
    intro d
    induction d with
    | zero =>
      have hb' : D (j + 1) (r + P) = true := by rw [hj1 r hr]; exact hb
      rw [Nat.add_zero, show r + 1 + P = r + P + 1 by omega, D_reset j (r + P) hb', D_reset j r hb, hj r hr]
    | succ d ih =>
      rw [show r + 1 + (d + 1) + P = r + 1 + d + P + 1 by omega, show r + 1 + (d + 1) = r + 1 + d + 1 by omega,
        D_step, D_step, hj (r + 1 + d) (by omega), hj1 (r + 1 + d) (by omega), ih]
  intro t ht
  have := key (t - (r + 1))
  rwa [show r + 1 + (t - (r + 1)) = t by omega] at this

/-- Moving a window one step drops its first cell and adds the next. -/
theorem windowParity_succ_start (f : Nat → Bool) (t : Nat) : ∀ n,
    windowParity f (t + 1) n = xor (xor (windowParity f t n) (f t)) (f (t + n))
  | 0 => by
    show false = xor (xor false (f t)) (f (t + 0))
    rw [Nat.add_zero]
    generalize f t = a
    cases a <;> rfl
  | n + 1 => by
    show xor (windowParity f (t + 1) n) (f (t + 1 + n)) =
      xor (xor (xor (windowParity f t n) (f (t + n))) (f t)) (f (t + (n + 1)))
    rw [windowParity_succ_start f t n, show t + 1 + n = t + (n + 1) by omega]
    generalize windowParity f t n = a
    generalize f t = b
    generalize f (t + n) = c
    generalize f (t + (n + 1)) = d
    cases a <;> cases b <;> cases c <;> cases d <;> rfl

/-- The parity of a periodic sequence over one period does not depend on where the period starts. -/
theorem windowParity_periodic (f : Nat → Bool) (T P : Nat) (hf : ∀ t, T ≤ t → f (t + P) = f t) :
    ∀ t, T ≤ t → windowParity f t P = windowParity f T P := by
  have key : ∀ d, windowParity f (T + d) P = windowParity f T P := by
    intro d
    induction d with
    | zero => rfl
    | succ d ih =>
      rw [show T + (d + 1) = T + d + 1 by omega, windowParity_succ_start, hf (T + d) (by omega), ih]
      generalize windowParity f T P = a
      generalize f (T + d) = b
      cases a <;> cases b <;> rfl
  intro t ht
  have := key (t - T)
  rwa [show T + (t - T) = t by omega] at this

/-- Behind a white diagonal `j + 1`, diagonal `j + 2` changes over a window by the parity of diagonal `j` there. -/
theorem D_shift_of_white (j T : Nat) (hw : ∀ t, T ≤ t → D (j + 1) t = false) (t : Nat) (ht : T ≤ t) :
    ∀ n, D (j + 2) (t + n) = xor (D (j + 2) t) (windowParity (D j) t n)
  | 0 => by
    show D (j + 2) (t + 0) = xor (D (j + 2) t) false
    rw [Nat.add_zero]
    generalize D (j + 2) t = a
    cases a <;> rfl
  | n + 1 => by
    rw [show t + (n + 1) = t + n + 1 by omega, D_accumulate j (t + n) (hw (t + n) (by omega)),
      D_shift_of_white j T hw t ht n]
    show xor (D j (t + n)) (xor (D (j + 2) t) (windowParity (D j) t n)) =
      xor (D (j + 2) t) (xor (windowParity (D j) t n) (D j (t + n)))
    generalize D j (t + n) = a
    generalize D (j + 2) t = b
    generalize windowParity (D j) t n = c
    cases a <;> cases b <;> cases c <;> rfl

/-- The dichotomy: if diagonals `j` and `j + 1` repeat with period `P` from time `T`, then either diagonal `j + 2`
repeats with period `P` from some time on, or diagonal `j + 1` is white from `T` on, diagonal `j` has odd parity over
a period, and diagonal `j + 2` flips every `P` steps. -/
theorem D_period_dichotomy (j T P : Nat)
    (hj : ∀ t, T ≤ t → D j (t + P) = D j t) (hj1 : ∀ t, T ≤ t → D (j + 1) (t + P) = D (j + 1) t) :
    (∃ T', ∀ t, T' ≤ t → D (j + 2) (t + P) = D (j + 2) t) ∨
      ((∀ t, T ≤ t → D (j + 1) t = false) ∧ windowParity (D j) T P = true ∧
        ∀ t, T ≤ t → D (j + 2) (t + P) = !D (j + 2) t) := by
  by_cases hblack : ∃ r, T ≤ r ∧ D (j + 1) r = true
  · obtain ⟨r, hr, hb⟩ := hblack
    exact Or.inl ⟨r + 1, D_periodic_of_black j T P r hj hj1 hr hb⟩
  · have hw : ∀ t, T ≤ t → D (j + 1) t = false := fun t ht => by
      cases h : D (j + 1) t with
      | false => rfl
      | true => exact absurd ⟨t, ht, h⟩ hblack
    have shift : ∀ t, T ≤ t → D (j + 2) (t + P) = xor (D (j + 2) t) (windowParity (D j) T P) := fun t ht => by
      rw [D_shift_of_white j T hw t ht P, windowParity_periodic (D j) T P hj t ht]
    cases hp : windowParity (D j) T P with
    | false =>
      refine Or.inl ⟨T, fun t ht => ?_⟩
      rw [shift t ht, hp]
      generalize D (j + 2) t = a
      cases a <;> rfl
    | true =>
      refine Or.inr ⟨hw, rfl, fun t ht => ?_⟩
      rw [shift t ht, hp]
      generalize D (j + 2) t = a
      cases a <;> rfl

/-- In the odd case the period doubles: diagonal `j + 2` repeats with period `2P` and never with period `P`. -/
theorem D_period_doubles (j T P : Nat) (hflip : ∀ t, T ≤ t → D (j + 2) (t + P) = !D (j + 2) t) :
    (∀ t, T ≤ t → D (j + 2) (t + 2 * P) = D (j + 2) t) ∧
      ∀ T', ¬ ∀ t, T' ≤ t → D (j + 2) (t + P) = D (j + 2) t := by
  constructor
  · intro t ht
    rw [show t + 2 * P = t + P + P by omega, hflip (t + P) (by omega), hflip t ht]
    generalize D (j + 2) t = a
    cases a <;> rfl
  · intro T' hper
    have h1 := hflip (T + T') (by omega)
    rw [hper (T + T') (by omega)] at h1
    revert h1
    generalize D (j + 2) (T + T') = a
    cases a <;> decide

/-- The first white diagonal: diagonal 2 is white from time 2 on, since diagonal 1 is black from time 1 on. -/
theorem D_two_white (t : Nat) : D 2 (t + 2) = false := by
  rw [show t + 2 = t + 1 + 1 by omega, D_reset 0 (t + 1) (D_one t), D_zero]
  rfl

/-- The first record: behind the white diagonal 2, diagonal 3 is a running XOR of the black diagonal 1, so it flips at
every step from time 2 on, period 2. -/
theorem D_three_flips (t : Nat) : D 3 (t + 3) = !D 3 (t + 2) := by
  rw [show t + 3 = t + 2 + 1 by omega, D_accumulate 1 (t + 2) (D_two_white t),
    show t + 2 = t + 1 + 1 by omega, D_one (t + 1)]
  show xor true (D 3 (t + 1 + 1)) = !D 3 (t + 1 + 1)
  generalize D 3 (t + 1 + 1) = a
  cases a <;> rfl

end Rule30Open
