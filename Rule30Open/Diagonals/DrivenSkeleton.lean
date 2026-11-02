module

public import Ruliology.CellularAutomata.Rule30FiniteDiagonals

/-!
# Every configuration with a left edge settles to the same left diagonals, up to a time shift

Read a configuration that is white left of a cell `lo` along its left diagonals,
`Ld x lo j t = cell t (lo - t + j)` (the kit's `Rule30FiniteDiagonals.Ld`). They obey the single cell's
recurrence `b (i + 2) (t + 1) = b i t xor (b (i + 1) t || b (i + 2) t)` (`DiagStep`, from the kit's
`Ld_step`). This module compares two such arrays `b` and `b'` (in the application, any configuration and the
single cell) diagonal by diagonal. The step lemmas need the recurrence for `b` only for the diagonal they treat and
only from the time they start (`DiagStepFrom`), so they also apply to the left half driven by any center column,
whose diagonal `j` obeys the recurrence from time `j + 1` on.

* `shift_of_black`: if diagonals `i` and `i + 1` of `b` equal those of `b'` read `h` steps later, from time
  `T` on, and diagonal `i + 1` of `b` is black at some `r ≥ T`, then diagonal `i + 2` of `b` equals that of
  `b'` read `h` steps later, from `r + 1` on. The diagonal forgets its past at the black cell.
* `shift_or_flip_of_white`: if instead diagonal `i + 1` is white from `T` on, diagonal `i + 2` of `b` is,
  from `T` on, either diagonal `i + 2` of `b'` read `h` steps later or its complement.
* `skeleton_step`: the two cases together: the shift passes from the pair `(i, i + 1)` to the pair
  `(i + 1, i + 2)`, or diagonal `i + 1` is white from `T` on and diagonal `i + 2` is the complement.
* `skeleton_step_of_flip`: when diagonal `i + 2` of `b'` flips every `P` steps and diagonals `i, i + 1` of
  `b'` repeat with period `P` (the case of a doubling period behind a white diagonal, the kit's
  `Rule30Diagonals` and `LeftMemory.D_period_doubles`), the complement is the shift by `h + P`, so the shift
  passes in every case.
* `base_pair`: every configuration white left of `lo` with cell `lo` black has diagonals `0` and `1` black
  from time `1` on, so any two such configurations start with the shift `0`.

So, by induction on the depth, every configuration white left of a black cell has, at each depth, the same
eventually periodic pair of left diagonals as the single cell, read with a time shift, as long as every
eventually white diagonal of the single cell up to that depth is followed by a doubling period. That holds for
the white diagonals 2, 7, 28 and 399 and fails for the next two, 53,207 and 58,286, where the step leaves the
shift or a complement that is not a shift. The induction and that check are in `DrivenSkeleton.md`; this module
proves the step and the base.

The natural-language argument is `DrivenSkeleton.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

/-- The left-diagonal recurrence of Rule 30. -/
def DiagStep (b : Nat → Nat → Bool) : Prop :=
  ∀ i t, b (i + 2) (t + 1) = xor (b i t) (b (i + 1) t || b (i + 2) t)

/-- The recurrence for diagonal `i + 2` of `b` from time `T` on. A driven left half obeys it for diagonal `j` from
time `j + 1` on (the driver sets only `b j j`), so the step lemmas below apply to it with `T ≥ i + 2`. -/
def DiagStepFrom (b : Nat → Nat → Bool) (i T : Nat) : Prop :=
  ∀ t, T ≤ t → b (i + 2) (t + 1) = xor (b i t) (b (i + 1) t || b (i + 2) t)

theorem DiagStep.from {b : Nat → Nat → Bool} (hb : DiagStep b) (i T : Nat) : DiagStepFrom b i T :=
  fun t _ => hb i t

/-- From time `T` on, diagonal `i` of `b` is diagonal `i` of `b'` read `h` steps later. -/
def ShiftFrom (b b' : Nat → Nat → Bool) (i T h : Nat) : Prop :=
  ∀ t, T ≤ t → b i t = b' i (t + h)

theorem ShiftFrom.mono {b b' : Nat → Nat → Bool} {i T U h : Nat} (hs : ShiftFrom b b' i T h) (hTU : T ≤ U) :
    ShiftFrom b b' i U h :=
  fun t ht => hs t (Nat.le_trans hTU ht)

/-- Behind a black cell of diagonal `i + 1`, the shift passes to diagonal `i + 2`. -/
theorem shift_of_black {b b' : Nat → Nat → Bool} {i T h r : Nat} (hb : DiagStepFrom b i T)
    (hb' : DiagStep b') (h0 : ShiftFrom b b' i T h) (h1 : ShiftFrom b b' (i + 1) T h)
    (hr : T ≤ r) (hblack : b (i + 1) r = true) : ShiftFrom b b' (i + 2) (r + 1) h := by
  intro t ht
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ht
  clear ht
  induction k with
  | zero =>
    have e1 : b' (i + 1) (r + h) = true := by rw [← h1 r hr]; exact hblack
    have e0 : b' i (r + h) = b i r := (h0 r hr).symm
    rw [show r + 1 + 0 = r + 1 by omega, hb r hr, show r + 1 + h = (r + h) + 1 by omega, hb' i (r + h), e1, e0,
      hblack]
    simp
  | succ k ih =>
    have e1 : b' (i + 1) (r + 1 + k + h) = b (i + 1) (r + 1 + k) := (h1 _ (by omega)).symm
    have e0 : b' i (r + 1 + k + h) = b i (r + 1 + k) := (h0 _ (by omega)).symm
    rw [show r + 1 + (k + 1) = (r + 1 + k) + 1 by omega, hb (r + 1 + k) (by omega),
      show r + 1 + k + 1 + h = (r + 1 + k + h) + 1 by omega, hb' i (r + 1 + k + h), e1, e0, ← ih]

/-- Behind a white diagonal `i + 1`, diagonal `i + 2` follows the shift or its complement. -/
theorem shift_or_flip_of_white {b b' : Nat → Nat → Bool} {i T h : Nat} (hb : DiagStepFrom b i T)
    (hb' : DiagStep b') (h0 : ShiftFrom b b' i T h) (h1 : ShiftFrom b b' (i + 1) T h)
    (hw : ∀ t, T ≤ t → b (i + 1) t = false) :
    ShiftFrom b b' (i + 2) T h ∨ (∀ t, T ≤ t → b (i + 2) t = !b' (i + 2) (t + h)) := by
  have hd : ∀ k, xor (b (i + 2) (T + k)) (b' (i + 2) (T + k + h)) =
      xor (b (i + 2) T) (b' (i + 2) (T + h)) := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      have e1 : b (i + 1) (T + k) = false := hw _ (by omega)
      have e2 : b' (i + 1) (T + k + h) = false := by rw [← h1 _ (by omega)]; exact e1
      have e0 : b' i (T + k + h) = b i (T + k) := (h0 _ (by omega)).symm
      rw [show T + (k + 1) = (T + k) + 1 by omega, hb (T + k) (by omega),
        show T + k + 1 + h = (T + k + h) + 1 by omega, hb' i (T + k + h), e1, e2, e0, ← ih]
      generalize b i (T + k) = p
      generalize b (i + 2) (T + k) = q
      generalize b' (i + 2) (T + k + h) = u
      cases p <;> cases q <;> cases u <;> rfl
  cases hc : xor (b (i + 2) T) (b' (i + 2) (T + h))
  · left
    intro t ht
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ht
    have := hd k
    rw [hc] at this
    revert this
    generalize b (i + 2) (T + k) = q
    generalize b' (i + 2) (T + k + h) = u
    cases q <;> cases u <;> simp
  · right
    intro t ht
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ht
    have := hd k
    rw [hc] at this
    revert this
    generalize b (i + 2) (T + k) = q
    generalize b' (i + 2) (T + k + h) = u
    cases q <;> cases u <;> simp

/-- The shift passes from the pair `(i, i + 1)` to the pair `(i + 1, i + 2)`, or diagonal `i + 1` is white
and diagonal `i + 2` is the complement of the shift. -/
theorem skeleton_step {b b' : Nat → Nat → Bool} {i T h : Nat} (hb : DiagStepFrom b i T)
    (hb' : DiagStep b') (h0 : ShiftFrom b b' i T h) (h1 : ShiftFrom b b' (i + 1) T h) :
    (∃ T₁, ShiftFrom b b' (i + 1) T₁ h ∧ ShiftFrom b b' (i + 2) T₁ h) ∨
      ((∀ t, T ≤ t → b (i + 1) t = false) ∧ (∀ t, T ≤ t → b (i + 2) t = !b' (i + 2) (t + h))) := by
  by_cases hblack : ∃ r, T ≤ r ∧ b (i + 1) r = true
  · obtain ⟨r, hr, hbr⟩ := hblack
    exact Or.inl ⟨r + 1, h1.mono (by omega), shift_of_black hb hb' h0 h1 hr hbr⟩
  · have hw : ∀ t, T ≤ t → b (i + 1) t = false := by
      intro t ht
      cases e : b (i + 1) t
      · rfl
      · exact (hblack ⟨t, ht, e⟩).elim
    rcases shift_or_flip_of_white hb hb' h0 h1 hw with hs | hf
    · exact Or.inl ⟨T, h1, hs⟩
    · exact Or.inr ⟨hw, hf⟩

/-- When diagonal `i + 2` of `b'` flips every `P` steps and diagonals `i`, `i + 1` of `b'` repeat with period
`P` (from `T' ≤ T + h`), the shift always passes to the pair `(i + 1, i + 2)`, with `h` or `h + P`. -/
theorem skeleton_step_of_flip {b b' : Nat → Nat → Bool} {i T h P T' : Nat} (hb : DiagStepFrom b i T)
    (hb' : DiagStep b') (h0 : ShiftFrom b b' i T h) (h1 : ShiftFrom b b' (i + 1) T h) (hT' : T' ≤ T + h)
    (hp1 : ∀ t, T' ≤ t → b' (i + 1) (t + P) = b' (i + 1) t)
    (hflip : ∀ t, T' ≤ t → b' (i + 2) (t + P) = !b' (i + 2) t) :
    ∃ T₁ h₁, ShiftFrom b b' (i + 1) T₁ h₁ ∧ ShiftFrom b b' (i + 2) T₁ h₁ := by
  rcases skeleton_step hb hb' h0 h1 with ⟨T₁, hs1, hs2⟩ | ⟨_, hf⟩
  · exact ⟨T₁, h, hs1, hs2⟩
  · refine ⟨T, h + P, fun t ht => ?_, fun t ht => ?_⟩
    · rw [h1 t ht, ← Nat.add_assoc, hp1 (t + h) (by omega)]
    · rw [hf t ht, ← Nat.add_assoc, hflip (t + h) (by omega)]

/-- The diagonals of every configuration, read from any cell `lo`, obey the recurrence (the kit's `Ld_step`). -/
theorem Ld_diagStep (x : Int → Bool) (lo : Int) :
    DiagStep (Ruliology.CellularAutomata.Rule30FiniteDiagonals.Ld x lo) :=
  fun i t => Ruliology.CellularAutomata.Rule30FiniteDiagonals.Ld_step (x := x) (lo := lo) i t

/-- Every configuration white left of `lo` whose cell `lo` is black has diagonals `0` and `1` black from time
`1` on. -/
theorem base_pair {x : Int → Bool} {lo : Int} (hleft : ∀ p, p < lo → x p = false)
    (hblack : Ruliology.CellularAutomata.Rule30FiniteDiagonals.Ld x lo 0 0 = true) (t : Nat) (ht : 1 ≤ t) :
    Ruliology.CellularAutomata.Rule30FiniteDiagonals.Ld x lo 0 t = true ∧
      Ruliology.CellularAutomata.Rule30FiniteDiagonals.Ld x lo 1 t = true := by
  have h0 : ∀ s, Ruliology.CellularAutomata.Rule30FiniteDiagonals.Ld x lo 0 s = true := by
    intro s
    induction s with
    | zero => exact hblack
    | succ s ih => rw [Ruliology.CellularAutomata.Rule30FiniteDiagonals.Ld_zero_succ hleft, ih]
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le ht
  refine ⟨h0 _, ?_⟩
  rw [show 1 + s = s + 1 by omega, Ruliology.CellularAutomata.Rule30FiniteDiagonals.Ld_one_succ hleft, h0 s,
    Bool.true_or]

/-- Any two configurations white left of a black cell start with the shift `0` on the pair `(0, 1)`. -/
theorem base_shift {x x' : Int → Bool} {lo lo' : Int} (hleft : ∀ p, p < lo → x p = false)
    (hleft' : ∀ p, p < lo' → x' p = false)
    (hblack : Ruliology.CellularAutomata.Rule30FiniteDiagonals.Ld x lo 0 0 = true)
    (hblack' : Ruliology.CellularAutomata.Rule30FiniteDiagonals.Ld x' lo' 0 0 = true) :
    ShiftFrom (Ruliology.CellularAutomata.Rule30FiniteDiagonals.Ld x lo)
        (Ruliology.CellularAutomata.Rule30FiniteDiagonals.Ld x' lo') 0 1 0 ∧
      ShiftFrom (Ruliology.CellularAutomata.Rule30FiniteDiagonals.Ld x lo)
        (Ruliology.CellularAutomata.Rule30FiniteDiagonals.Ld x' lo') 1 1 0 := by
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩
  · rw [(base_pair hleft hblack t ht).1, Nat.add_zero, (base_pair hleft' hblack' t ht).1]
  · rw [(base_pair hleft hblack t ht).2, Nat.add_zero, (base_pair hleft' hblack' t ht).2]

end Rule30Open
