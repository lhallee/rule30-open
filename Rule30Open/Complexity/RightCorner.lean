module

public import Rule30Open.Complexity.ConeScreening

/-!
# The center never depends on all three rightmost cells of its cone at once

Write `c_t(x) = evo x t 0` for the center after `t` steps from a row `x`, a Boolean function of the `2t + 1` cells
`-t .. t`. The function is *sensitive* to a cell at a row when flipping that cell flips the center.

* `right_corner`: for `t ≥ 2` and every row, the center is insensitive to at least one of the cells `t - 2`, `t - 1`,
  `t`.
* `right_corner_certificate`: so for every row some `2t` of the cone cells fix the center: every row that agrees with
  `x` on them has the same center. The certificate complexity of `c_t` is at most `2t`, and so is its sensitivity.

The proof follows the diagonals at the right edge of the cone. In the frame that moves left one cell per step, write
`R x a k s` for the cell `a - s - k` after `s` steps; one step is `R k ← R (k + 2) xor (R (k + 1) || R k)`
(`R_succ`), so two rows that agree on the diagonals `k ≥ m` keep agreeing on them (`agree_add`). With `a = t`, the
center is `R 0` at time `t`.

* `corner_white`: if the center is sensitive to cell `t`, the diagonal `R 1` is white at every time before `t`: a
  black cell there absorbs the flip of `R 0`.
* `strip_one`, `strip_two`, `strip_three`: against such a row, a flip that has entered only the diagonals
  `R 0 .. R 2` ends with a difference at the center that a short invariant fixes: unchanged (`strip_one`), equal to
  the complement of `R 0` at the start (`strip_two`), or none (`strip_three`).

Flipping cell `t - 1` and flipping cell `t - 2` then reach the center under opposite conditions on cell `t`, or the
second does not reach it at all.

This is a statement about an arbitrary input row. It bounds the certificate complexity of `c_t`, a lower-bound method
for decision trees, and does not bound the cost of the single black cell's column.

The natural-language argument is `RightCorner.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

/-- The cell `a - s - k` after `s` steps: diagonal `k` counted from the cell `a`, in the frame that moves left one
cell per step. -/
def rdiag (x : Int → Bool) (a k : Int) (s : Nat) : Bool := evo x s (a - s - k)

/-- One step on the diagonals. -/
theorem rdiag_succ (x : Int → Bool) (a k : Int) (s : Nat) :
    rdiag x a k (s + 1) = xor (rdiag x a (k + 2) s) (rdiag x a (k + 1) s || rdiag x a k s) := by
  show coneStep (evo x s) (a - ((s + 1 : Nat) : Int) - k) = _
  simp only [coneStep, rdiag]
  have e1 : a - ((s + 1 : Nat) : Int) - k - 1 = a - s - (k + 2) := by omega
  have e2 : a - ((s + 1 : Nat) : Int) - k = a - s - (k + 1) := by omega
  have e3 : a - ((s + 1 : Nat) : Int) - k + 1 = a - s - k := by omega
  rw [e1, e3, e2]

theorem rd0 (x : Int → Bool) (a : Int) (s : Nat) :
    rdiag x a 0 (s + 1) = xor (rdiag x a 2 s) (rdiag x a 1 s || rdiag x a 0 s) := rdiag_succ x a 0 s

theorem rd1 (x : Int → Bool) (a : Int) (s : Nat) :
    rdiag x a 1 (s + 1) = xor (rdiag x a 3 s) (rdiag x a 2 s || rdiag x a 1 s) := rdiag_succ x a 1 s

theorem rd2 (x : Int → Bool) (a : Int) (s : Nat) :
    rdiag x a 2 (s + 1) = xor (rdiag x a 4 s) (rdiag x a 3 s || rdiag x a 2 s) := rdiag_succ x a 2 s

theorem rdiag_zero (x : Int → Bool) (a k : Int) : rdiag x a k 0 = x (a - k) := by
  show x (a - ((0 : Nat) : Int) - k) = x (a - k)
  congr 1
  omega

theorem rdiag_center (x : Int → Bool) (t : Nat) : rdiag x t 0 t = evo x t 0 := by
  show evo x t ((t : Int) - (t : Int) - 0) = evo x t 0
  congr 1
  omega

/-- Two rows agree on the diagonals `k ≥ m` at time `s`. -/
def DiagAgree (y x : Int → Bool) (a m : Int) (s : Nat) : Prop := ∀ k : Int, m ≤ k → rdiag y a k s = rdiag x a k s

theorem agree_succ {y x : Int → Bool} {a m : Int} {s : Nat} (h : DiagAgree y x a m s) :
    DiagAgree y x a m (s + 1) := by
  intro k hk
  rw [rdiag_succ, rdiag_succ, h k hk, h (k + 1) (by omega), h (k + 2) (by omega)]

theorem agree_add {y x : Int → Bool} {a m : Int} {s : Nat} (h : DiagAgree y x a m s) :
    ∀ n : Nat, DiagAgree y x a m (s + n)
  | 0 => h
  | n + 1 => agree_succ (agree_add h n)

theorem agree_le {y x : Int → Bool} {a m s' : Int} {s : Nat} (h : DiagAgree y x a m s) (hm : m ≤ s') :
    DiagAgree y x a s' s := fun k hk => h k (by omega)

theorem agree_down {y x : Int → Bool} {a m : Int} {s : Nat} (h : DiagAgree y x a (m + 1) s)
    (hm : rdiag y a m s = rdiag x a m s) : DiagAgree y x a m s := by
  intro k hk
  by_cases hkm : k = m
  · subst hkm; exact hm
  · exact h k (by omega)

/-- A row flipped at the cell `a - k` agrees with the row on the diagonals `k + 1` and beyond. -/
theorem agree_flip (x : Int → Bool) (a k : Int) : DiagAgree (flipAt x (a - k)) x a (k + 1) 0 := by
  intro j hj
  rw [rdiag_zero, rdiag_zero]
  have hne : a - j ≠ a - k := by omega
  simp [flipAt, hne]

/-- Rows that agree on every diagonal at time `t`, with `a = t`, have the same center. -/
theorem center_of_agree {y x : Int → Bool} {t s : Nat} (h : DiagAgree y x t 0 s) (hs : s ≤ t) :
    evo y t 0 = evo x t 0 := by
  have h' := agree_add h (t - s)
  have e : s + (t - s) = t := by omega
  rw [e] at h'
  rw [← rdiag_center, ← rdiag_center]
  exact h' 0 (by omega)

theorem rdiag_flip_self (x : Int → Bool) (a k : Int) : rdiag (flipAt x (a - k)) a k 0 = !(x (a - k)) := by
  rw [rdiag_zero]; simp [flipAt]

/-- **A flip of cell `t` reaches the center only through a white second diagonal.** If flipping cell `t` flips the
center after `t` steps, the cells `t - s - 1` after `s` steps are white for every `s < t`. -/
theorem corner_white (x : Int → Bool) (t : Nat) (h : evo (flipAt x t) t 0 ≠ evo x t 0) :
    ∀ s : Nat, s < t → rdiag x t 1 s = false := by
  intro s hs
  cases hb : rdiag x t 1 s
  · rfl
  · exfalso
    apply h
    have e : ((t : Int) - 0) = (t : Int) := by omega
    have h0 := agree_flip x t 0
    rw [e] at h0
    have h1 := agree_add h0 s
    rw [Nat.zero_add] at h1
    have h2 : DiagAgree (flipAt x t) x t 0 (s + 1) := by
      apply agree_down (agree_succ h1)
      rw [rd0, rd0, h1 2 (by omega), h1 1 (by omega), hb]
      simp
    exact center_of_agree h2 (by omega)

/-- **A difference confined to the center diagonal is carried unchanged** while the second diagonal of `x` is
white. -/
theorem strip_one (z x : Int → Bool) (a : Int) (s0 T : Nat) (hag : DiagAgree z x a 1 s0)
    (hw : ∀ s : Nat, s < T → rdiag x a 1 s = false) :
    ∀ n : Nat, s0 + n ≤ T →
      xor (rdiag z a 0 (s0 + n)) (rdiag x a 0 (s0 + n)) = xor (rdiag z a 0 s0) (rdiag x a 0 s0)
  | 0, _ => rfl
  | n + 1, hn => by
    have ih := strip_one z x a s0 T hag hw n (by omega)
    have ag := agree_add hag n
    rw [show s0 + (n + 1) = s0 + n + 1 from rfl, rd0 z, rd0 x, ag 2 (by omega), ag 1 (by omega),
      hw (s0 + n) (by omega), ← ih]
    generalize rdiag x a 2 (s0 + n) = p
    generalize rdiag z a 0 (s0 + n) = q
    generalize rdiag x a 0 (s0 + n) = r
    cases p <;> cases q <;> cases r <;> rfl

/-- The invariant of `strip_two`. -/
theorem strip_two_inv (z x : Int → Bool) (a : Int) (s0 T : Nat) (hag : DiagAgree z x a 2 s0)
    (hz : rdiag z a 1 s0 = true) (hT : s0 < T) (hw : ∀ s : Nat, s < T → rdiag x a 1 s = false) :
    ∀ n : Nat, s0 + 1 + n ≤ T →
      (s0 + 1 + n < T → rdiag z a 1 (s0 + 1 + n) = true → rdiag x a 0 (s0 + 1 + n) = rdiag x a 0 s0) ∧
      xor (rdiag z a 0 (s0 + 1 + n)) (rdiag x a 0 (s0 + 1 + n)) = !(rdiag x a 0 s0)
  | 0, _ => by
    have hx1 := hw s0 hT
    refine ⟨fun hlt h1 => ?_, ?_⟩
    · have h3 : rdiag x a 3 s0 = rdiag x a 2 s0 := by
        have := hw (s0 + 1) hlt
        rw [rd1, hx1] at this
        revert this
        generalize rdiag x a 3 s0 = p
        generalize rdiag x a 2 s0 = q
        cases p <;> cases q <;> simp
      rw [rd1 z, hag 3 (by omega), hag 2 (by omega), hz, h3] at h1
      rw [rd0 x, hx1]
      revert h1
      generalize rdiag x a 2 s0 = p
      generalize rdiag x a 0 s0 = q
      cases p <;> cases q <;> simp
    · rw [rd0 z, rd0 x, hag 2 (by omega), hz, hx1]
      generalize rdiag x a 2 s0 = p
      generalize rdiag x a 0 s0 = q
      cases p <;> cases q <;> rfl
  | n + 1, hn => by
    have ih := strip_two_inv z x a s0 T hag hz hT hw n (by omega)
    have ag := agree_add hag (1 + n)
    rw [show s0 + (1 + n) = s0 + 1 + n by omega] at ag
    have e : s0 + 1 + (n + 1) = s0 + 1 + n + 1 := rfl
    rw [e]
    have hx1 := hw (s0 + 1 + n) (by omega)
    have h3 : s0 + 1 + n + 1 < T → rdiag x a 3 (s0 + 1 + n) = rdiag x a 2 (s0 + 1 + n) := by
      intro hlt
      have := hw (s0 + 1 + n + 1) hlt
      rw [rd1, hx1] at this
      revert this
      generalize rdiag x a 3 (s0 + 1 + n) = p
      generalize rdiag x a 2 (s0 + 1 + n) = q
      cases p <;> cases q <;> simp
    obtain ⟨i1, i2⟩ := ih
    cases hz1 : rdiag z a 1 (s0 + 1 + n)
    · -- the second diagonal of `z` is white: the difference is carried, and it stays white
      refine ⟨fun hlt h1 => ?_, ?_⟩
      · rw [rd1 z, ag 3 (by omega), ag 2 (by omega), hz1, h3 hlt] at h1
        revert h1
        generalize rdiag x a 2 (s0 + 1 + n) = p
        cases p <;> simp
      · rw [rd0 z, rd0 x, ag 2 (by omega), hz1, hx1, ← i2]
        generalize rdiag x a 2 (s0 + 1 + n) = p
        generalize rdiag z a 0 (s0 + 1 + n) = q
        generalize rdiag x a 0 (s0 + 1 + n) = r
        cases p <;> cases q <;> cases r <;> rfl
    · have hx0 := i1 (by omega) hz1
      refine ⟨fun hlt h1 => ?_, ?_⟩
      · rw [rd1 z, ag 3 (by omega), ag 2 (by omega), hz1, h3 hlt] at h1
        rw [rd0 x, hx1, hx0]
        revert h1
        generalize rdiag x a 2 (s0 + 1 + n) = p
        cases p <;> simp
      · rw [rd0 z, rd0 x, ag 2 (by omega), hz1, hx1, hx0]
        generalize rdiag x a 2 (s0 + 1 + n) = p
        generalize rdiag x a 0 s0 = q
        cases p <;> cases q <;> rfl

/-- **A difference that enters the second diagonal reaches the center as the complement of `R 0` at its start.** -/
theorem strip_two (z x : Int → Bool) (a : Int) (s0 T : Nat) (hag : DiagAgree z x a 2 s0)
    (hz : rdiag z a 1 s0 = true) (hT : s0 < T) (hw : ∀ s : Nat, s < T → rdiag x a 1 s = false) :
    xor (rdiag z a 0 T) (rdiag x a 0 T) = !(rdiag x a 0 s0) := by
  have h := (strip_two_inv z x a s0 T hag hz hT hw (T - s0 - 1) (by omega)).2
  rwa [show s0 + 1 + (T - s0 - 1) = T by omega] at h

/-- The invariant of `strip_three`: either the two rows agree on every diagonal, or the third diagonal of `z` is the
complement of that of `x`, the second diagonal of `z` is black, and the center diagonals are white. -/
def ThreeState (z x : Int → Bool) (a : Int) (s : Nat) : Prop :=
  DiagAgree z x a 0 s ∨
    (rdiag z a 2 s = !(rdiag x a 2 s) ∧ rdiag z a 1 s = true ∧ rdiag x a 0 s = false ∧
      (2 ≤ s → rdiag z a 0 s = false))

theorem three_step (z x : Int → Bool) (a : Int) (s T : Nat) (hag : DiagAgree z x a 3 s)
    (hw : ∀ s : Nat, s < T → rdiag x a 1 s = false) (hlt : s + 1 < T) (h : ThreeState z x a s) :
    ThreeState z x a (s + 1) := by
  have hx1 := hw s (by omega)
  have h3 : rdiag x a 3 s = rdiag x a 2 s := by
    have := hw (s + 1) hlt
    rw [rd1, hx1] at this
    revert this
    generalize rdiag x a 3 s = p
    generalize rdiag x a 2 s = q
    cases p <;> cases q <;> simp
  rcases h with hall | ⟨hz2, hz1, hx0, _⟩
  · exact Or.inl (agree_succ hall)
  · cases hx2 : rdiag x a 2 s
    · -- the flip stays in the third diagonal
      rw [hx2] at hz2 h3
      refine Or.inr ⟨?_, ?_, ?_, fun _ => ?_⟩
      · rw [rd2 z, rd2 x, hag 4 (by omega), hag 3 (by omega), hz2, h3, hx2]
        generalize rdiag x a 4 s = p
        cases p <;> rfl
      · rw [rd1 z, hag 3 (by omega), hz2, h3]; rfl
      · rw [rd0 x, hx2, hx1, hx0]; rfl
      · rw [rd0 z, hz2, hz1]; rfl
    · -- the flip leaves the third diagonal, and the rows agree again
      rw [hx2] at hz2 h3
      have ag3 := agree_succ hag
      have g2 : DiagAgree z x a 2 (s + 1) := agree_down ag3 (by
        rw [rd2 z, rd2 x, hag 4 (by omega), hag 3 (by omega), hz2, h3, hx2]
        generalize rdiag x a 4 s = p
        cases p <;> rfl)
      have g1 : DiagAgree z x a 1 (s + 1) := agree_down g2 (by
        rw [rd1 z, rd1 x, hag 3 (by omega), hz2, hz1, h3, hx2, hx1]; rfl)
      exact Or.inl (agree_down g1 (by rw [rd0 z, rd0 x, hz2, hz1, hx2, hx1, hx0]; rfl))

/-- **A difference that enters the third diagonal with a black second diagonal and white centers never reaches the
center.** -/
theorem strip_three (z x : Int → Bool) (a : Int) (T : Nat) (hag : DiagAgree z x a 3 1)
    (hz2 : rdiag z a 2 1 = !(rdiag x a 2 1)) (hz1 : rdiag z a 1 1 = true) (hx0 : rdiag x a 0 1 = false)
    (hT : 2 ≤ T) (hw : ∀ s : Nat, s < T → rdiag x a 1 s = false) :
    rdiag z a 0 T = rdiag x a 0 T := by
  have inv : ∀ n : Nat, 1 + n < T → ThreeState z x a (1 + n) := by
    intro n
    induction n with
    | zero => intro _; exact Or.inr ⟨hz2, hz1, hx0, fun h => by omega⟩
    | succ n ih =>
      intro hn
      have := three_step z x a (1 + n) T (agree_add hag n) hw (by omega) (ih (by omega))
      rwa [show 1 + n + 1 = 1 + (n + 1) by omega] at this
  have last := inv (T - 2) (by omega)
  rw [show 1 + (T - 2) = T - 1 by omega] at last
  have eT : T = T - 1 + 1 := by omega
  rw [eT]
  have ag := agree_add hag (T - 2)
  rw [show 1 + (T - 2) = T - 1 by omega] at ag
  rcases last with hall | ⟨hz2', hz1', hx0', _⟩
  · exact agree_succ hall 0 (by omega)
  · have hx1 := hw (T - 1) (by omega)
    rw [rd0 z, rd0 x, hz2', hz1', hx1, hx0']
    generalize rdiag x a 2 (T - 1) = p
    cases p <;> rfl

/-- The row's own cells on the diagonals at time 1, near the right edge. -/
theorem rdiag_one (x : Int → Bool) (a k : Int) :
    rdiag x a k 1 = xor (x (a - (k + 2))) (x (a - (k + 1)) || x (a - k)) := by
  rw [show (1 : Nat) = 0 + 1 from rfl, rdiag_succ, rdiag_zero, rdiag_zero, rdiag_zero]

/-- **The right corner.** For `t ≥ 2`, no row makes the center after `t` steps sensitive to all three of the cells
`t - 2`, `t - 1` and `t`. -/
theorem right_corner (x : Int → Bool) (t : Nat) (ht : 2 ≤ t) :
    ¬ (evo (flipAt x t) t 0 ≠ evo x t 0 ∧ evo (flipAt x (t - 1)) t 0 ≠ evo x t 0 ∧
      evo (flipAt x (t - 2)) t 0 ≠ evo x t 0) := by
  rintro ⟨h0, h1, h2⟩
  have hw := corner_white x t h0
  -- the cells next to the corner
  have hx1 : x (t - 1) = false := by
    have := hw 0 (by omega); rw [rdiag_zero] at this; exact this
  have hx3 : x (t - 3) = x (t - 2) := by
    have := hw 1 (by omega)
    rw [rdiag_one] at this
    rw [show (t : Int) - (1 + 2) = t - 3 by omega, show (t : Int) - (1 + 1) = t - 2 by omega, hx1] at this
    revert this
    generalize x (t - 3) = p
    generalize x (t - 2) = q
    cases p <;> cases q <;> simp
  have hx0 : rdiag x t 0 1 = xor (x (t - 2)) (x t) := by
    rw [rdiag_one, show (t : Int) - (0 + 2) = t - 2 by omega, show (t : Int) - (0 + 1) = t - 1 by omega,
      show (t : Int) - 0 = t by omega, hx1]
    rfl
  -- the row flipped at `t - 1`
  have a1 := agree_succ (agree_flip x t 1)
  have z1_1 : rdiag (flipAt x (t - 1)) t 1 1 = !(x (t - 2)) := by
    rw [rdiag_one]
    simp only [flipAt, show (t : Int) - (1 + 2) = t - 3 by omega, show (t : Int) - (1 + 1) = t - 2 by omega]
    simp [hx1, hx3]
  have z1_0 : rdiag (flipAt x (t - 1)) t 0 1 = !(x (t - 2)) := by
    rw [rdiag_one]
    simp only [flipAt, show (t : Int) - (0 + 2) = t - 2 by omega, show (t : Int) - (0 + 1) = t - 1 by omega,
      show (t : Int) - 0 = t by omega]
    simp [hx1]
  -- the row flipped at `t - 2`
  have a2 := agree_succ (agree_flip x t 2)
  have z2_1 : rdiag (flipAt x (t - 2)) t 1 1 = true := by
    rw [rdiag_one]
    simp only [flipAt, show (t : Int) - (1 + 2) = t - 3 by omega, show (t : Int) - (1 + 1) = t - 2 by omega]
    simp [hx1, hx3]
  have z2_2 : rdiag (flipAt x (t - 2)) t 2 1 = xor (x (t - 4)) true ∧
      rdiag x t 2 1 = xor (x (t - 4)) (x (t - 2)) := by
    rw [rdiag_one, rdiag_one]
    simp only [flipAt, show (t : Int) - (2 + 2) = t - 4 by omega, show (t : Int) - (2 + 1) = t - 3 by omega]
    simp [hx3]
  have c1 : evo (flipAt x (t - 1)) t 0 = rdiag (flipAt x (t - 1)) t 0 t := (rdiag_center _ t).symm
  have c2 : evo (flipAt x (t - 2)) t 0 = rdiag (flipAt x (t - 2)) t 0 t := (rdiag_center _ t).symm
  have c0 : evo x t 0 = rdiag x t 0 t := (rdiag_center _ t).symm
  rw [c1, c0] at h1
  rw [c2, c0] at h2
  cases hv : x (t - 2)
  · -- `x (t - 2)` white: the flip at `t - 1` reaches the center only if cell `t` is white, and then the flip at
    -- `t - 2` does not reach it
    have d1 := strip_two (flipAt x (t - 1)) x t 1 t a1 (by rw [z1_1, hv]; rfl) (by omega) hw
    rw [hx0, hv] at d1
    cases hxt : x t
    · apply h2
      apply strip_three _ x t t a2 _ (by rw [z2_1]) (by rw [hx0, hv, hxt]; rfl) ht hw
      rw [z2_2.1, z2_2.2, hv]
      generalize x (t - 4) = p
      cases p <;> rfl
    · apply h1
      rw [hxt] at d1
      revert d1
      generalize rdiag (flipAt x (t - 1)) t 0 t = p
      generalize rdiag x t 0 t = q
      cases p <;> cases q <;> simp
  · -- `x (t - 2)` black: the flip at `t - 1` reaches the center only if cell `t` is white, the flip at `t - 2`
    -- only if it is black
    have ag1 : DiagAgree (flipAt x (t - 1)) x t 1 1 := agree_down a1 (by
      rw [z1_1, hv, hw 1 (by omega)]; rfl)
    have d1 := strip_one (flipAt x (t - 1)) x t 1 t ag1 hw (t - 1) (by omega)
    rw [show 1 + (t - 1) = t by omega, z1_0, hx0, hv] at d1
    have ag2 : DiagAgree (flipAt x (t - 2)) x t 2 1 := agree_down a2 (by
      rw [z2_2.1, z2_2.2, hv])
    have d2 := strip_two (flipAt x (t - 2)) x t 1 t ag2 z2_1 (by omega) hw
    rw [hx0, hv] at d2
    cases hxt : x t
    · apply h2
      rw [hxt] at d2
      revert d2
      generalize rdiag (flipAt x (t - 2)) t 0 t = p
      generalize rdiag x t 0 t = q
      cases p <;> cases q <;> simp
    · apply h1
      rw [hxt] at d1
      revert d1
      generalize rdiag (flipAt x (t - 1)) t 0 t = p
      generalize rdiag x t 0 t = q
      cases p <;> cases q <;> simp

/-- **Certificates of `2t` cells.** For `t ≥ 2` and every row `x`, one of the cells `t - 2`, `t - 1`, `t` can be
left out: every row that agrees with `x` on the other `2t` cells of the cone has the center of `x`. -/
theorem right_corner_certificate (x : Int → Bool) (t : Nat) (ht : 2 ≤ t) :
    ∃ i : Int, (i = t ∨ i = t - 1 ∨ i = t - 2) ∧
      ∀ y : Int → Bool, (∀ j : Int, -(t : Int) ≤ j → j ≤ t → j ≠ i → y j = x j) → evo y t 0 = evo x t 0 := by
  have key : ∃ i : Int, (i = t ∨ i = t - 1 ∨ i = t - 2) ∧ evo (flipAt x i) t 0 = evo x t 0 := by
    by_cases a : evo (flipAt x t) t 0 = evo x t 0
    · exact ⟨t, Or.inl rfl, a⟩
    by_cases b : evo (flipAt x (t - 1)) t 0 = evo x t 0
    · exact ⟨t - 1, Or.inr (Or.inl rfl), b⟩
    by_cases c : evo (flipAt x (t - 2)) t 0 = evo x t 0
    · exact ⟨t - 2, Or.inr (Or.inr rfl), c⟩
    exact absurd ⟨a, b, c⟩ (right_corner x t ht)
  obtain ⟨i, hi, hflip⟩ := key
  refine ⟨i, hi, fun y hy => ?_⟩
  have hit : -(t : Int) ≤ i ∧ i ≤ t := by omega
  cases hyi : (y i == x i)
  · -- `y` agrees with `x` flipped at `i` on the cone
    rw [← hflip]
    apply evo_local
    intro j h1 h2
    simp only [flipAt]
    by_cases hj : j = i
    · subst hj
      revert hyi
      generalize y j = p
      generalize x j = q
      cases p <;> cases q <;> simp
    · simp only [hj, ite_false]
      exact hy j (by omega) (by omega) hj
  · apply evo_local
    intro j h1 h2
    by_cases hj : j = i
    · subst hj; simpa using hyi
    · exact hy j (by omega) (by omega) hj

end Rule30Open
