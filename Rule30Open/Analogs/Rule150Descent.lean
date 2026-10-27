module

/-!
# Rule 150 beside a held column: the linear analog is true

The linear analog of the held map is rule 150 with the column held at 0, `x' = x_(-1) xor x xor x_(+1)`.
For it the analog of the open period-2 statement is true: every finite half reads 0 next to the column at
some even step from 4 on (`held150_even_steps`) and at some odd step from 5 on (`held150_odd_steps`).

The proof mirrors the half about the column to the whole line (`mirror_step`), where two steps of rule 150
are one step on each sublattice (`step150_twice`, `iter150_double`). Those identities split the center of
a line and the cell left of it between the line's two halves, and a line with both reading 1 at every step
`r ≥ 1` would have two halves with the same property, each at most half as wide (`halves150`), which no
finite line survives (`descent150`). Rule 30 has no two-step identity of this kind.

The natural-language argument is `Rule150Descent.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

/-- Rule 150 on the whole line. -/
def step150 (y : Int → Bool) : Int → Bool := fun x => xor (xor (y (x - 1)) (y x)) (y (x + 1))

/-- The orbit of `y` under rule 150. -/
def iter150 (y : Int → Bool) : Nat → Int → Bool
  | 0 => y
  | n + 1 => step150 (iter150 y n)

/-- Two steps of rule 150 are one step on each sublattice. -/
theorem step150_twice (y : Int → Bool) (x : Int) :
    step150 (step150 y) x = xor (xor (y (x - 2)) (y x)) (y (x + 2)) := by
  show xor (xor (xor (xor (y (x - 1 - 1)) (y (x - 1))) (y (x - 1 + 1)))
    (xor (xor (y (x - 1)) (y x)) (y (x + 1)))) (xor (xor (y (x + 1 - 1)) (y (x + 1))) (y (x + 1 + 1))) = _
  rw [show x - 1 - 1 = x - 2 by omega, show x - 1 + 1 = x by omega, show x + 1 - 1 = x by omega,
    show x + 1 + 1 = x + 2 by omega]
  generalize y (x - 2) = a
  generalize y (x - 1) = b
  generalize y x = c
  generalize y (x + 1) = d
  generalize y (x + 2) = e
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> rfl

/-- Steps `2r` of rule 150, read on the sublattice `2x + i`, are `r` steps on that sublattice. -/
theorem iter150_double (y : Int → Bool) (i : Int) : ∀ (r : Nat) (x : Int),
    iter150 y (2 * r) (2 * x + i) = iter150 (fun z => y (2 * z + i)) r x
  | 0, _ => rfl
  | r + 1, x => by
    show step150 (step150 (iter150 y (2 * r))) (2 * x + i) = step150 (iter150 (fun z => y (2 * z + i)) r) x
    rw [step150_twice]
    show xor (xor (iter150 y (2 * r) (2 * x + i - 2)) (iter150 y (2 * r) (2 * x + i)))
        (iter150 y (2 * r) (2 * x + i + 2)) =
      xor (xor (iter150 (fun z => y (2 * z + i)) r (x - 1)) (iter150 (fun z => y (2 * z + i)) r x))
        (iter150 (fun z => y (2 * z + i)) r (x + 1))
    rw [show 2 * x + i - 2 = 2 * (x - 1) + i by omega, show 2 * x + i + 2 = 2 * (x + 1) + i by omega,
      iter150_double y i r (x - 1), iter150_double y i r x, iter150_double y i r (x + 1)]

/-- Rule 150 commutes with the mirror `x ↦ c - x`. -/
theorem iter150_mirror (y : Int → Bool) (c : Int) : ∀ (r : Nat) (x : Int),
    iter150 (fun z => y (c - z)) r x = iter150 y r (c - x)
  | 0, _ => rfl
  | r + 1, x => by
    show xor (xor (iter150 (fun z => y (c - z)) r (x - 1)) (iter150 (fun z => y (c - z)) r x))
        (iter150 (fun z => y (c - z)) r (x + 1)) =
      xor (xor (iter150 y r (c - x - 1)) (iter150 y r (c - x))) (iter150 y r (c - x + 1))
    rw [iter150_mirror y c r (x - 1), iter150_mirror y c r x, iter150_mirror y c r (x + 1),
      show c - (x - 1) = c - x + 1 by omega, show c - (x + 1) = c - x - 1 by omega]
    generalize iter150 y r (c - x + 1) = a
    generalize iter150 y r (c - x) = b
    generalize iter150 y r (c - x - 1) = d
    cases a <;> cases b <;> cases d <;> rfl

theorem iter150_false : ∀ (r : Nat) (x : Int), iter150 (fun _ => false) r x = false
  | 0, _ => rfl
  | r + 1, x => by
    show xor (xor (iter150 (fun _ => false) r (x - 1)) (iter150 (fun _ => false) r x))
      (iter150 (fun _ => false) r (x + 1)) = false
    rw [iter150_false r (x - 1), iter150_false r x, iter150_false r (x + 1)]
    rfl

/-- A line whose center and the cell left of it read 1 at every step `r ≥ 1` passes the property to both halves,
`z ↦ y (2z)` and `z ↦ y (2z + 1)`. -/
theorem halves150 (y : Int → Bool)
    (h : ∀ r : Nat, 0 < r → iter150 y r 0 = true ∧ iter150 y r (-1) = true) :
    (∀ r : Nat, 0 < r → iter150 (fun z => y (2 * z + 0)) r 0 = true ∧
      iter150 (fun z => y (2 * z + 0)) r (-1) = true) ∧
    ∀ r : Nat, 0 < r → iter150 (fun z => y (2 * z + 1)) r 0 = true ∧
      iter150 (fun z => y (2 * z + 1)) r (-1) = true := by
  have even0 : ∀ r : Nat, iter150 (fun z => y (2 * z + 0)) r 0 = iter150 y (2 * r) 0 := fun r =>
    (iter150_double y 0 r 0).symm
  have even1 : ∀ r : Nat, iter150 (fun z => y (2 * z + 0)) r (-1) = iter150 y (2 * r) (-2) := fun r =>
    (iter150_double y 0 r (-1)).symm
  have odd0 : ∀ r : Nat, iter150 (fun z => y (2 * z + 1)) r 0 = iter150 y (2 * r) 1 := fun r =>
    (iter150_double y 1 r 0).symm
  have odd1 : ∀ r : Nat, iter150 (fun z => y (2 * z + 1)) r (-1) = iter150 y (2 * r) (-1) := fun r =>
    (iter150_double y 1 r (-1)).symm
  -- one more step reads the cells -2 .. 1 of step 2r
  have next0 : ∀ r : Nat, iter150 y (2 * r + 1) 0 =
      xor (xor (iter150 y (2 * r) (-1)) (iter150 y (2 * r) 0)) (iter150 y (2 * r) 1) := fun r => rfl
  have next1 : ∀ r : Nat, iter150 y (2 * r + 1) (-1) =
      xor (xor (iter150 y (2 * r) (-2)) (iter150 y (2 * r) (-1))) (iter150 y (2 * r) 0) := fun r => rfl
  refine ⟨fun r hr => ⟨?_, ?_⟩, fun r hr => ⟨?_, ?_⟩⟩
  · rw [even0]; exact (h (2 * r) (by omega)).1
  · have h1 := (h (2 * r + 1) (by omega)).2
    rw [next1, (h (2 * r) (by omega)).1, (h (2 * r) (by omega)).2] at h1
    rw [even1]
    revert h1
    cases iter150 y (2 * r) (-2) <;> simp
  · have h0 := (h (2 * r + 1) (by omega)).1
    rw [next0, (h (2 * r) (by omega)).1, (h (2 * r) (by omega)).2] at h0
    rw [odd0]
    revert h0
    cases iter150 y (2 * r) 1 <;> simp
  · rw [odd1]; exact (h (2 * r) (by omega)).2

/-- No finite line has its center and the cell left of it at 1 at every step `r ≥ 1`. By induction on the width:
both halves of such a line would have the property, the even half is at most half as wide, and a line of width 0
has a half that is 0 everywhere. -/
theorem descent150 : ∀ (n w : Nat), w ≤ n → ∀ (y : Int → Bool) (a : Int),
    (∀ x : Int, x < a ∨ a + w < x → y x = false) →
    ¬ ∀ r : Nat, 0 < r → iter150 y r 0 = true ∧ iter150 y r (-1) = true := by
  intro n
  induction n with
  | zero =>
    intro w hw y a hy h
    obtain ⟨h0, h1⟩ := halves150 y h
    -- the half that misses `a` is 0 everywhere
    rcases (show a % 2 = 0 ∨ a % 2 = 1 by omega) with ha | ha
    · have zero : (fun z => y (2 * z + 1)) = fun _ => false := by
        funext z
        exact hy (2 * z + 1) (by omega)
      have := (h1 1 (by omega)).1
      rw [zero, iter150_false] at this
      exact Bool.false_ne_true this
    · have zero : (fun z => y (2 * z + 0)) = fun _ => false := by
        funext z
        exact hy (2 * z + 0) (by omega)
      have := (h0 1 (by omega)).1
      rw [zero, iter150_false] at this
      exact Bool.false_ne_true this
  | succ n ih =>
    intro w hw y a hy h
    by_cases hwn : w ≤ n
    · exact ih w hwn y a hy h
    · -- the even half lives on `(a + 1) / 2 .. (a + 1) / 2 + w / 2`, and `w / 2 ≤ n`
      exact ih (w / 2) (by omega) (fun z => y (2 * z + 0)) ((a + 1) / 2)
        (fun x hx => hy (2 * x + 0) (by omega)) (halves150 y h).1

/-- Rule 150 beside a column held at 0; bit `j` is the cell `j + 1` places left of the column. -/
def held150 (u : Nat → Bool) : Nat → Bool
  | 0 => xor (u 1) (u 0)
  | j + 1 => xor (xor (u (j + 2)) (u (j + 1))) (u j)

/-- The orbit of `u` under `held150`. -/
def held150Orbit (u : Nat → Bool) : Nat → Nat → Bool
  | 0 => u
  | n + 1 => held150 (held150Orbit u n)

/-- The half mirrored to the whole line about cell `-1`, which reads 0: cell `j ≥ 0` is bit `j`, and cell
`-2 - j` is bit `j` again. -/
def mirror (u : Nat → Bool) (x : Int) : Bool :=
  if 0 ≤ x then u x.toNat else if x = -1 then false else u (-2 - x).toNat

theorem mirror_step (u : Nat → Bool) (x : Int) : step150 (mirror u) x = mirror (held150 u) x := by
  rcases (show x = -2 ∨ x = -1 ∨ x = 0 ∨ 1 ≤ x ∨ x ≤ -3 by omega) with hx | hx | hx | hx | hx
  · subst hx
    show xor (xor (u 1) (u 0)) false = xor (u 1) (u 0)
    cases u 0 <;> cases u 1 <;> rfl
  · subst hx
    show xor (xor (u 0) false) (u 0) = false
    cases u 0 <;> rfl
  · subst hx
    show xor (xor false (u 0)) (u 1) = xor (u 1) (u 0)
    cases u 0 <;> cases u 1 <;> rfl
  · obtain ⟨j, rfl⟩ : ∃ j : Nat, x = (j : Int) + 1 := ⟨(x - 1).toNat, by omega⟩
    have e1 : (((j : Int) + 1 - 1).toNat) = j := by omega
    have e2 : (((j : Int) + 1).toNat) = j + 1 := by omega
    have e3 : (((j : Int) + 1 + 1).toNat) = j + 2 := by omega
    simp only [step150, mirror, show (0 : Int) ≤ (j : Int) + 1 - 1 by omega,
      show (0 : Int) ≤ (j : Int) + 1 by omega, show (0 : Int) ≤ (j : Int) + 1 + 1 by omega, ite_true, e1, e2, e3,
      held150]
    cases u j <;> cases u (j + 1) <;> cases u (j + 2) <;> rfl
  · obtain ⟨j, rfl⟩ : ∃ j : Nat, x = -2 - ((j : Int) + 1) := ⟨(-3 - x).toNat, by omega⟩
    have e1 : ((-2 - (-2 - ((j : Int) + 1) - 1)).toNat) = j + 2 := by omega
    have e2 : ((-2 - (-2 - ((j : Int) + 1))).toNat) = j + 1 := by omega
    have e3 : ((-2 - (-2 - ((j : Int) + 1) + 1)).toNat) = j := by omega
    simp only [step150, mirror, show ¬ (0 : Int) ≤ -2 - ((j : Int) + 1) - 1 by omega,
      show ¬ (0 : Int) ≤ -2 - ((j : Int) + 1) by omega, show ¬ (0 : Int) ≤ -2 - ((j : Int) + 1) + 1 by omega,
      show ¬ (-2 - ((j : Int) + 1) - 1 = -1) by omega, show ¬ (-2 - ((j : Int) + 1) = -1) by omega,
      show ¬ (-2 - ((j : Int) + 1) + 1 = -1) by omega, ite_false, e1, e2, e3, held150]

theorem mirror_orbit (u : Nat → Bool) : ∀ n, iter150 (mirror u) n = mirror (held150Orbit u n)
  | 0 => rfl
  | n + 1 => by
    funext x
    show step150 (iter150 (mirror u) n) x = mirror (held150 (held150Orbit u n)) x
    rw [mirror_orbit u n, mirror_step]

theorem mirror_symm (u : Nat → Bool) (x : Int) : mirror u (-2 - x) = mirror u x := by
  rcases (show 0 ≤ x ∨ x = -1 ∨ x ≤ -2 by omega) with hx | hx | hx
  · simp only [mirror, show ¬ (0 : Int) ≤ -2 - x by omega, show ¬ (-2 - x = -1) by omega, hx, ite_true,
      ite_false, show -2 - (-2 - x) = x by omega]
  · subst hx; rfl
  · simp only [mirror, show (0 : Int) ≤ -2 - x by omega, show ¬ (0 : Int) ≤ x by omega,
      show ¬ (x = -1) by omega, ite_true, ite_false]

/-- Every finite half under rule 150 beside a held 0 reads 0 next to the column at some step `4r` or `4r + 2`
with `r ≥ 1`. -/
theorem held150_even_steps (u : Nat → Bool) (N : Nat) (hN : ∀ j, N ≤ j → u j = false) :
    ¬ ∀ r : Nat, 0 < r → held150Orbit u (4 * r) 0 = true ∧ held150Orbit u (4 * r + 2) 0 = true := by
  intro h
  let y := mirror u
  let P : Int → Bool := fun z => y (2 * z + 0)
  let X : Int → Bool := fun z => P (2 * z + 0)
  have bit : ∀ n, held150Orbit u n 0 = iter150 y n 0 := fun n => by
    rw [mirror_orbit]; rfl
  -- steps 4r: the even half of the even half
  have four : ∀ r : Nat, iter150 y (4 * r) 0 = iter150 X r 0 := fun r => by
    have h1 := iter150_double y 0 (2 * r) 0
    rw [show 2 * (2 * r) = 4 * r by omega] at h1
    exact h1.trans (iter150_double P 0 r 0)
  -- the odd half of `P` is `X` mirrored about `-1/2`, since `y` is symmetric about `-1`
  have odd_half : (fun z => P (2 * z + 1)) = fun z => X (-1 - z) := by
    funext z
    show mirror u (2 * (2 * z + 1) + 0) = mirror u (2 * (2 * (-1 - z) + 0) + 0)
    rw [← mirror_symm u (2 * (2 * z + 1) + 0)]
    exact congrArg (mirror u) (by omega)
  have six : ∀ r : Nat, iter150 y (4 * r + 2) 0 = iter150 X r (-1) := fun r => by
    have h1 := iter150_double y 0 (2 * r + 1) 0
    rw [show 2 * (2 * r + 1) = 4 * r + 2 by omega] at h1
    refine h1.trans ?_
    show xor (xor (iter150 P (2 * r) (-1)) (iter150 P (2 * r) 0)) (iter150 P (2 * r) 1) = iter150 X r (-1)
    have m1 : iter150 P (2 * r) (-1) = iter150 X r 0 := by
      have h2 := iter150_double P 1 r (-1)
      rw [odd_half, iter150_mirror X (-1) r (-1)] at h2
      exact h2
    have p0 : iter150 P (2 * r) 0 = iter150 X r 0 := iter150_double P 0 r 0
    have p1 : iter150 P (2 * r) 1 = iter150 X r (-1) := by
      have h2 := iter150_double P 1 r 0
      rw [odd_half, iter150_mirror X (-1) r 0] at h2
      exact h2
    rw [m1, p0, p1]
    generalize iter150 X r 0 = a
    generalize iter150 X r (-1) = b
    cases a <;> cases b <;> rfl
  apply descent150 (2 * N + 2) (2 * N + 2) (Nat.le_refl _) X (-(N : Int) - 1)
  · intro x hx
    show mirror u (2 * (2 * x + 0) + 0) = false
    simp only [mirror]
    split
    · exact hN _ (by omega)
    · split
      · rfl
      · exact hN _ (by omega)
  · intro r hr
    have := h r hr
    rw [bit, bit, four, six] at this
    exact this

/-- The orbit from `held150 u` is the orbit from `u`, one step on. -/
theorem held150Orbit_succ (u : Nat → Bool) : ∀ n, held150Orbit u (n + 1) = held150Orbit (held150 u) n
  | 0 => rfl
  | n + 1 => by
    show held150 (held150Orbit u (n + 1)) = held150 (held150Orbit (held150 u) n)
    rw [held150Orbit_succ u n]

/-- And at some odd step from 5 on: apply `held150_even_steps` to the half one step on. -/
theorem held150_odd_steps (u : Nat → Bool) (N : Nat) (hN : ∀ j, N ≤ j → u j = false) :
    ¬ ∀ r : Nat, 0 < r → held150Orbit u (4 * r + 1) 0 = true ∧ held150Orbit u (4 * r + 3) 0 = true := by
  intro h
  apply held150_even_steps (held150 u) (N + 1)
  · intro j hj
    cases j with
    | zero => omega
    | succ j =>
      show xor (xor (u (j + 2)) (u (j + 1))) (u j) = false
      rw [hN (j + 2) (by omega), hN (j + 1) (by omega), hN j (by omega)]
      rfl
  · intro r hr
    rw [← held150Orbit_succ, ← held150Orbit_succ]
    exact h r hr

/-- The cell next to the column from a single 1, as a spot check of `held150`: it reads 0 at steps 2, 3, 10 and 11 of
the first twelve. -/
theorem held150_orbit_one :
    (List.range 12).map (fun n => held150Orbit (fun j => j == 0) n 0) =
      [true, true, false, false, true, true, true, true, true, true, false, false] := by decide

end Rule30Open
