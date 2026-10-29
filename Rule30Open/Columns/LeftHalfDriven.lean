module

public import Rule30Open.Columns.LeftHalf0001

/-!
# The left half for `0011` and `0111`: no start of depth at most 88 keeps the kit's pattern

For the words `0011` and `0111` of least period four the kit reduces Problem 1 to statements about the left half alone
(`Rule30PeriodFourSkeleton.C3 w0011` and `C3 w0111`, open): no finitely supported left half, run as rule 30 beside the
effective boundary, keeps column `-1` black at the times `4 s + 3` and white at the times `4 s + 1` and `4 s + 2` for
all large times. Unlike that of `0001`, the effective boundary of these words is not white: it is black at phase `2`
for `0011` (`effWord_0011`) and at phases `1` and `2` for `0111` (`effWord_0111`).

Column `-1` and the boundary determine the whole half sideways (`reconB`, `history_eq_reconB`), as the kit's
`history_eq_recon` does for the white boundary. The kit's lane checker (`Rule30ZeroBoundaryLanes`) runs with the
boundary entering every anti-diagonal at depth `0` (`scanN_ADB`, `levelB`); the checker here takes the pattern and
the boundary as bit masks over the phase (`stepG`, `runG`, `checkG`, `runG_sound`), with the free reading at phase `1`
after a shift of the phase.

* `c3G_of_checks`: if every chunk passes `checkG W K φ n ones bnd`, every start supported at depths `≤ W` breaks the
  pattern from phase `φ` at some time `< K`.
* `c3_0011_depth`, `c3_0111_depth`: at depth `88`, from each of the four phases, within `115` steps (`64` chunk checks
  for each word).
* `c3_0011_bounded`, `c3_0111_bounded`: a left half that keeps the kit's pattern from time `K` on has a black cell
  beyond depth `88` at time `K`; this is `C3 w0011` and `C3 w0111` for every half whose row at time `K` lies within
  depth `88`.
* `c3_0011_small`, `c3_0111_small`: no left half supported within depth `M` keeps the pattern from a time `K` with
  `M + K ≤ 88`.
* `sharp20_0011_0` to `sharp20_0111_3`: at depth `20` the least number of levels that passes is one more than the latest
  first failure, for each word and phase.

The natural-language argument is `LeftHalfDriven.md`, beside this file.
-/

@[expose] public section

-- Sequential elaboration: the kernel checks would otherwise run in parallel and stack their memory.
set_option Elab.async false

namespace Rule30Open

open Ruliology.CellularAutomata
open Rule30ZeroBoundaryLanes

/-! ### Reconstruction beside a boundary column -/

/-- The sideways reconstruction beside the boundary column `b` from the column-`-1` sequence `y`: `reconB b y k t` is
the cell at depth `k` and time `t`, and depth `0` is the boundary. -/
def reconB (b y : Nat → Bool) : Nat → Nat → Bool
  | 0, t => b t
  | 1, t => y t
  | k + 2, t => xor (reconB b y (k + 1) (t + 1)) (reconB b y (k + 1) t || reconB b y k t)

theorem reconB_zero (b y : Nat → Bool) (t : Nat) : reconB b y 0 t = b t := by rw [reconB]

theorem reconB_one (b y : Nat → Bool) (t : Nat) : reconB b y 1 t = y t := by rw [reconB]

theorem reconB_two (b y : Nat → Bool) (k t : Nat) :
    reconB b y (k + 2) t = xor (reconB b y (k + 1) (t + 1)) (reconB b y (k + 1) t || reconB b y k t) := by
  rw [reconB]

/-- **The driven half is the reconstruction from its column `-1` and its boundary**, from any time `K` on. -/
theorem history_eq_reconB (c : Nat → Bool) (s : Int → Bool) (K : Nat) :
    ∀ k t : Nat, Rule30DrivenLeft.L c s (K + t) (-(k : Int)) =
      reconB (fun t => c (K + t)) (fun t => Rule30DrivenLeft.L c s (K + t) (-1)) k t := by
  have key : ∀ k : Nat, (∀ t : Nat, Rule30DrivenLeft.L c s (K + t) (-(k : Int)) =
        reconB (fun t => c (K + t)) (fun t => Rule30DrivenLeft.L c s (K + t) (-1)) k t) ∧
      (∀ t : Nat, Rule30DrivenLeft.L c s (K + t) (-((k + 1 : Nat) : Int)) =
        reconB (fun t => c (K + t)) (fun t => Rule30DrivenLeft.L c s (K + t) (-1)) (k + 1) t) := by
    intro k
    induction k with
    | zero =>
      refine ⟨fun t => ?_, fun t => ?_⟩
      · rw [reconB_zero, show -((0 : Nat) : Int) = 0 by omega, Rule30DrivenLeft.L_col0]
      · rw [reconB_one]; rfl
    | succ k ih =>
      refine ⟨ih.2, fun t => ?_⟩
      have e := Rule30DrivenLeft.L_left (c := c) (s := s) (K + t) (p := -((k + 1 : Nat) : Int)) (by omega)
      rw [show -((k + 1 : Nat) : Int) - 1 = -((k + 1 + 1 : Nat) : Int) by omega,
        show -((k + 1 : Nat) : Int) + 1 = -((k : Nat) : Int) by omega,
        show K + t + 1 = K + (t + 1) by omega, ih.2 (t + 1), ih.2 t, ih.1 t] at e
      rw [e, reconB_two]
  exact fun k t => (key k).1 t

/-! ### Anti-diagonals beside a boundary -/

/-- `ADB b y k i n`: the entries `i, …, i + n - 1` of anti-diagonal `k` of the reconstruction beside `b`, listed by
depth; entry `i` is the cell at depth `i + 1` and time `k - 1 - i`. -/
def ADB (b y : Nat → Bool) (k : Nat) : Nat → Nat → List Bool
  | _, 0 => []
  | i, n + 1 => reconB b y (i + 1) (k - 1 - i) :: ADB b y k (i + 1) n

theorem ADB_getD (b y : Nat → Bool) (k : Nat) :
    ∀ n i j, j < n → (ADB b y k i n).getD j false = reconB b y (i + j + 1) (k - 1 - i - j) := by
  intro n
  induction n with
  | zero => intro i j hj; omega
  | succ n ih =>
    intro i j hj
    cases j with
    | zero => simp [ADB]
    | succ j =>
      show (ADB b y k (i + 1) n).getD j false = _
      rw [ih (i + 1) j (by omega), show i + 1 + j + 1 = i + (j + 1) + 1 by omega,
        show k - 1 - (i + 1) - j = k - 1 - i - (j + 1) by omega]

/-- **Lane semantics of the running xor beside a boundary**, as the kit's `scanN_AD`. -/
theorem scanN_ADB (b y : Nat → Bool) (k p : Nat) : ∀ (n i : Nat) (as bs : List Nat) (acc : Nat),
    i + n ≤ k →
    as.map (fun v => v.testBit p) = ADB b y k i n →
    (∀ j, j < n → (bs.getD j 0).testBit p = reconB b y (i + j) (k - 1 - i - j)) →
    acc.testBit p = reconB b y (i + 1) (k - i) →
    (scanN acc as bs).1.map (fun v => v.testBit p) = ADB b y (k + 1) (i + 1) n ∧
      (scanN acc as bs).2.testBit p = reconB b y (i + n + 1) (k - i - n) := by
  intro n
  induction n with
  | zero =>
    intro i as bs acc _ has _ hacc
    cases as with
    | nil => exact ⟨rfl, by rw [scanN_nil]; exact hacc⟩
    | cons a as => simp [ADB] at has
  | succ n ih =>
    intro i as bs acc hk has hbs hacc
    cases as with
    | nil => simp [ADB] at has
    | cons a as =>
      rw [List.map_cons] at has
      simp only [ADB, List.cons.injEq] at has
      obtain ⟨ha, has⟩ := has
      have hb0 := hbs 0 (by omega)
      rw [Nat.add_zero, Nat.sub_zero] at hb0
      have hv : (acc ^^^ (a ||| bs.headD 0)).testBit p = reconB b y (i + 1 + 1) (k - (i + 1)) := by
        rw [show k - (i + 1) = k - 1 - i by omega, show i + 1 + 1 = i + 2 from rfl, reconB_two,
          show k - 1 - i + 1 = k - i by omega, Nat.testBit_xor, Nat.testBit_or, hacc, ha,
          headD_eq, hb0]
      have := ih (i + 1) as bs.tail (acc ^^^ (a ||| bs.headD 0)) (by omega) has
        (fun j hj => by
          rw [getD_tail, hbs (j + 1) (by omega), show i + (j + 1) = i + 1 + j by omega,
            show k - 1 - i - (j + 1) = k - 1 - (i + 1) - j by omega]) hv
      rw [scanN_cons]
      refine ⟨?_, ?_⟩
      · rw [List.map_cons, this.1]
        simp only [ADB]
        rw [hv, show k + 1 - 1 - (i + 1) = k - (i + 1) by omega]
      · rw [this.2, show i + 1 + n + 1 = i + (n + 1) + 1 by omega,
          show k - (i + 1) - n = k - i - (n + 1) by omega]

/-- **One level, one lane, beside a boundary.** The boundary at time `k - 1` enters at depth `0` (`B`). -/
theorem levelB (b y : Nat → Bool) (p k : Nat) (R Rm : List Nat) (Y B : Nat)
    (hR : R.map (fun v => v.testBit p) = ADB b y k 0 k)
    (hRm : Rm.map (fun v => v.testBit p) = ADB b y (k - 1) 0 (k - 1))
    (hY : Y.testBit p = y k) (hB : 0 < k → B.testBit p = b (k - 1)) :
    (Y :: (scanN Y R (B :: Rm)).1).map (fun v => v.testBit p) = ADB b y (k + 1) 0 (k + 1) ∧
      (scanN Y R (B :: Rm)).2.testBit p = reconB b y (k + 1) 0 := by
  have h := scanN_ADB b y k p k 0 R (B :: Rm) Y (by omega) hR
    (fun j hj => by
      cases j with
      | zero =>
        rw [show ((B :: Rm).getD 0 0) = B from rfl, hB (by omega), Nat.zero_add, reconB_zero]
        rfl
      | succ j =>
        show (Rm.getD j 0).testBit p = _
        rw [getD_testBit, hRm, ADB_getD b y (k - 1) (k - 1) 0 j (by omega)]
        rw [show 0 + j + 1 = 0 + (j + 1) by omega,
          show k - 1 - 1 - 0 - j = k - 1 - 0 - (j + 1) by omega])
    (by rw [hY, Nat.zero_add, Nat.sub_zero, reconB_one])
  refine ⟨?_, ?_⟩
  · rw [List.map_cons, h.1, hY]
    simp only [ADB]
    rw [Nat.zero_add, show k + 1 - 1 - 0 = k by omega, reconB_one]
  · rw [h.2, show 0 + k + 1 = k + 1 by omega, show k - 0 - k = 0 by omega]

/-! ### The checker -/

/-- The pattern from phase `φ`, with the free reading at phase `1`: at time `t`, with `r = (t + φ) % 4 ≠ 1`, column
`-1` reads bit `r` of `ones`. -/
def KeepsG (φ ones : Nat) (y : Nat → Bool) (t : Nat) : Prop :=
  (t + φ) % 4 ≠ 1 → y t = ones.testBit ((t + φ) % 4)

/-- One level for the pattern `ones` beside the boundary `bnd` (bit `r` of `bnd`: the boundary at phase `r`), from
phase `φ`. At a fixed phase the reading is the pattern's; at the free phase with `k + 1 ≤ W` a free reading; at the
free phase with `W < k + 1` the reading that makes the start white at depth `k + 1`. -/
noncomputable def stepG (W φ n c ALL ones bnd : Nat) (pats : List Nat) (k : Nat) (R Rm : List Nat) :
    List Nat × Nat :=
  Bool.rec
    (let y := Bool.rec 0 ALL (Nat.testBit ones (Nat.mod (Nat.add k φ) 4))
     let r := scanN y R (Bool.rec 0 ALL (Nat.testBit bnd (Nat.mod (Nat.add (Nat.add k φ) 3) 4)) :: Rm)
     (y :: r.1, r.2))
    (Bool.rec
      (let r := scanN 0 R (Bool.rec 0 ALL (Nat.testBit bnd (Nat.mod (Nat.add (Nat.add k φ) 3) 4)) :: Rm)
       (r.2 :: mapX r.2 r.1, r.2))
      (let y := yFree n c ALL pats (Nat.sub (Nat.div (Nat.add k φ) 4) (Nat.div φ 2))
       let r := scanN y R (Bool.rec 0 ALL (Nat.testBit bnd (Nat.mod (Nat.add (Nat.add k φ) 3) 4)) :: Rm)
       (y :: r.1, r.2))
      (Nat.ble (Nat.add k 1) W))
    (Nat.beq (Nat.mod (Nat.add k φ) 4) 1)

/-- Run `fuel` levels from level `k`; a lane dies when a fixed reading leaves the start black at a depth beyond `W`.
Succeeds when no lane is alive at the end. -/
noncomputable def runG (W φ n c ALL ones bnd : Nat) (pats : List Nat) (fuel : Nat) :
    Nat → List Nat → List Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → List Nat → List Nat → Nat → Bool)
    (fun _ _ _ alive => Nat.beq alive 0)
    (fun _ ih k R Rm alive =>
      let st := stepG W φ n c ALL ones bnd pats k R Rm
      ih (Nat.add k 1) st.1 R
        (Bool.rec alive (Nat.land alive (Nat.xor ALL st.2))
          (band (Bool.rec true false (Nat.beq (Nat.mod (Nat.add k φ) 4) 1)) (Nat.blt W (Nat.add k 1)))))
    fuel

/-- The check for chunk `c` from phase `φ`: `2 ^ n` lanes, `K` levels, starts supported at depths `≤ W`. -/
noncomputable def checkG (W K φ n ones bnd c : Nat) : Bool :=
  runG W φ n c (2 ^ 2 ^ n - 1) ones bnd ((List.range n).map (pat n)) K 0 [] [] (2 ^ 2 ^ n - 1)

/-- The boundary's lane value at level `k`: the boundary at time `k - 1`. -/
noncomputable def laneB (φ ALL bnd k : Nat) : Nat := Bool.rec 0 ALL (Nat.testBit bnd ((k + φ + 3) % 4))

theorem runG_zero (W φ n c ALL ones bnd : Nat) (pats : List Nat) (k : Nat) (R Rm : List Nat) (alive : Nat) :
    runG W φ n c ALL ones bnd pats 0 k R Rm alive = Nat.beq alive 0 := rfl

theorem runG_succ (W φ n c ALL ones bnd : Nat) (pats : List Nat) (f k : Nat) (R Rm : List Nat) (alive : Nat) :
    runG W φ n c ALL ones bnd pats (f + 1) k R Rm alive =
      runG W φ n c ALL ones bnd pats f (k + 1) (stepG W φ n c ALL ones bnd pats k R Rm).1 R
        (Bool.rec alive (alive &&& (ALL ^^^ (stepG W φ n c ALL ones bnd pats k R Rm).2))
          (band (Bool.rec true false (Nat.beq ((k + φ) % 4) 1)) (Nat.blt W (k + 1)))) := rfl

theorem stepG_fixed (W φ n c ALL ones bnd : Nat) (pats : List Nat) (k : Nat) (R Rm : List Nat)
    (h : (k + φ) % 4 ≠ 1) :
    stepG W φ n c ALL ones bnd pats k R Rm =
      (Bool.rec 0 ALL (ones.testBit ((k + φ) % 4)) ::
          (scanN (Bool.rec 0 ALL (ones.testBit ((k + φ) % 4))) R (laneB φ ALL bnd k :: Rm)).1,
        (scanN (Bool.rec 0 ALL (ones.testBit ((k + φ) % 4))) R (laneB φ ALL bnd k :: Rm)).2) := by
  have hb : Nat.beq (Nat.mod (Nat.add k φ) 4) 1 = false := by
    cases hq : Nat.beq (Nat.mod (Nat.add k φ) 4) 1
    · rfl
    · rw [Nat.beq_eq] at hq; exact absurd hq h
  unfold stepG; rw [hb]; rfl

theorem stepG_free (W φ n c ALL ones bnd : Nat) (pats : List Nat) (k : Nat) (R Rm : List Nat)
    (h : (k + φ) % 4 = 1) (hW : k + 1 ≤ W) :
    stepG W φ n c ALL ones bnd pats k R Rm =
      (yFree n c ALL pats (freeIdx φ k) :: (scanN (yFree n c ALL pats (freeIdx φ k)) R (laneB φ ALL bnd k :: Rm)).1,
        (scanN (yFree n c ALL pats (freeIdx φ k)) R (laneB φ ALL bnd k :: Rm)).2) := by
  have hb : Nat.beq (Nat.mod (Nat.add k φ) 4) 1 = true := by rw [Nat.beq_eq]; exact h
  have hb2 : Nat.ble (Nat.add k 1) W = true := by rw [Nat.ble_eq]; exact hW
  unfold stepG; rw [hb, hb2]; rfl

theorem stepG_forced (W φ n c ALL ones bnd : Nat) (pats : List Nat) (k : Nat) (R Rm : List Nat)
    (h : (k + φ) % 4 = 1) (hW : W < k + 1) :
    stepG W φ n c ALL ones bnd pats k R Rm =
      ((scanN 0 R (laneB φ ALL bnd k :: Rm)).2 ::
          mapX (scanN 0 R (laneB φ ALL bnd k :: Rm)).2 (scanN 0 R (laneB φ ALL bnd k :: Rm)).1,
        (scanN 0 R (laneB φ ALL bnd k :: Rm)).2) := by
  have hb : Nat.beq (Nat.mod (Nat.add k φ) 4) 1 = true := by rw [Nat.beq_eq]; exact h
  have hb2 : Nat.ble (Nat.add k 1) W = false := by
    cases hq : Nat.ble (Nat.add k 1) W
    · rfl
    · rw [Nat.ble_eq] at hq; exact absurd hq (by show ¬ k + 1 ≤ W; omega)
  unfold stepG; rw [hb, hb2]; rfl

theorem testBit_laneB (φ ALL bnd k p : Nat) (hALL : ALL.testBit p = true) :
    (laneB φ ALL bnd k).testBit p = bnd.testBit ((k + φ + 3) % 4) := by
  unfold laneB
  cases bnd.testBit ((k + φ + 3) % 4)
  · exact Nat.zero_testBit p
  · exact hALL

theorem testBit_rec (ALL p : Nat) (v : Bool) (hALL : ALL.testBit p = true) :
    (Bool.rec 0 ALL v : Nat).testBit p = v := by
  cases v
  · exact Nat.zero_testBit p
  · exact hALL

/-- **Soundness of `runG` for one lane.** Lane `p` follows a column `y` that keeps the pattern beside the boundary
`b`, matches the free readings of the lane, and comes from a start that is white beyond depth `W`. Then the lane never
dies, so `runG` cannot succeed. -/
theorem runG_sound (W φ n c ALL ones bnd : Nat) (pats : List Nat) (b y : Nat → Bool) (p : Nat)
    (hALL : ALL.testBit p = true)
    (hb : ∀ t, b t = bnd.testBit ((t + φ) % 4))
    (hfree : ∀ t, (t + φ) % 4 = 1 → t + 1 ≤ W → (yFree n c ALL pats (freeIdx φ t)).testBit p = y t)
    (hwid : ∀ d, W < d → reconB b y d 0 = false) :
    ∀ fuel k R Rm alive,
      runG W φ n c ALL ones bnd pats fuel k R Rm alive = true →
      (∀ t, k ≤ t → t < k + fuel → KeepsG φ ones y t) →
      R.map (fun v => v.testBit p) = ADB b y k 0 k →
      Rm.map (fun v => v.testBit p) = ADB b y (k - 1) 0 (k - 1) →
      alive.testBit p = true → False := by
  intro fuel
  induction fuel with
  | zero =>
    intro k R Rm alive hrun _ _ _ halive
    rw [runG_zero, Nat.beq_eq] at hrun
    rw [hrun, Nat.zero_testBit] at halive
    exact absurd halive (by decide)
  | succ fuel ih =>
    intro k R Rm alive hrun hkeep hR hRm halive
    rw [runG_succ] at hrun
    have hkeep' : ∀ t, k + 1 ≤ t → t < k + 1 + fuel → KeepsG φ ones y t :=
      fun t h1 h2 => hkeep t (by omega) (by omega)
    have hRm' : R.map (fun v => v.testBit p) = ADB b y (k + 1 - 1) 0 (k + 1 - 1) := by
      rw [show k + 1 - 1 = k by omega]; exact hR
    have hk := hkeep k (by omega) (by omega)
    have hB : 0 < k → (laneB φ ALL bnd k).testBit p = b (k - 1) := by
      intro hk0
      rw [testBit_laneB φ ALL bnd k p hALL, hb (k - 1), show (k - 1 + φ) % 4 = (k + φ + 3) % 4 by omega]
    by_cases h1 : (k + φ) % 4 = 1
    · have hb1 : Nat.beq ((k + φ) % 4) 1 = true := by rw [Nat.beq_eq]; exact h1
      by_cases hW : k + 1 ≤ W
      · -- a free reading
        rw [stepG_free W φ n c ALL ones bnd pats k R Rm h1 hW] at hrun
        have hl := levelB b y p k R Rm _ _ hR hRm (hfree k h1 hW) hB
        refine ih (k + 1) _ R _ hrun hkeep' hl.1 hRm' ?_
        rw [hb1]
        exact halive
      · -- a forced reading: the white cell at depth `k + 1` fixes it, and it is the true one
        rw [stepG_forced W φ n c ALL ones bnd pats k R Rm h1 (by omega)] at hrun
        let Y' : Nat := if y k then 2 ^ p else 0
        have hY' : Y'.testBit p = y k := by
          show (if y k then 2 ^ p else 0).testBit p = y k
          cases y k
          · simp
          · simp
        have hl' := levelB b y p k R Rm Y' _ hR hRm hY' hB
        rw [hwid (k + 1) (by omega), scanN_lin, Nat.testBit_xor, hY'] at hl'
        have hT : (scanN 0 R (laneB φ ALL bnd k :: Rm)).2.testBit p = y k := by
          have h2 := hl'.2
          revert h2
          cases y k <;> cases (scanN 0 R (laneB φ ALL bnd k :: Rm)).2.testBit p <;> simp
        have hl := levelB b y p k R Rm (scanN 0 R (laneB φ ALL bnd k :: Rm)).2 _ hR hRm hT hB
        rw [scanN_lin R (laneB φ ALL bnd k :: Rm) (scanN 0 R (laneB φ ALL bnd k :: Rm)).2] at hl
        refine ih (k + 1) _ R _ hrun hkeep' hl.1 hRm' ?_
        rw [hb1]
        exact halive
    · -- a fixed reading
      have hb1 : Nat.beq ((k + φ) % 4) 1 = false := by
        cases hq : Nat.beq ((k + φ) % 4) 1
        · rfl
        · rw [Nat.beq_eq] at hq; exact absurd hq h1
      rw [stepG_fixed W φ n c ALL ones bnd pats k R Rm h1] at hrun
      have hY : (Bool.rec 0 ALL (ones.testBit ((k + φ) % 4)) : Nat).testBit p = y k := by
        rw [testBit_rec ALL p _ hALL, hk h1]
      have hl := levelB b y p k R Rm _ _ hR hRm hY hB
      refine ih (k + 1) _ R _ hrun hkeep' hl.1 hRm' ?_
      rw [hb1]
      by_cases hW : W < k + 1
      · have hb2 : Nat.blt W (k + 1) = true := by rw [Nat.blt_eq]; exact hW
        rw [hb2]
        show (alive &&& (ALL ^^^
          (scanN (Bool.rec 0 ALL (ones.testBit ((k + φ) % 4))) R (laneB φ ALL bnd k :: Rm)).2)).testBit p = true
        rw [Nat.testBit_and, Nat.testBit_xor, hl.2, hwid (k + 1) hW, hALL, halive]
        rfl
      · have hb2 : Nat.blt W (k + 1) = false := by
          cases hq : Nat.blt W (k + 1)
          · rfl
          · rw [Nat.blt_eq] at hq; exact absurd hq hW
        rw [hb2]
        exact halive

/-- **Soundness of the chunked check.** If every chunk passes from phase `φ`, then every column `-1` beside the
boundary `bnd` whose start is white beyond depth `W` breaks the pattern `ones` from phase `φ` at some time `< K`. -/
theorem c3G_of_checks (W K φ n ones bnd : Nat) (hφ : φ < 4) (hn : n ≤ freeCount W φ)
    (hc : ∀ c, c < 2 ^ (freeCount W φ - n) → checkG W K φ n ones bnd c = true)
    (b y : Nat → Bool) (hb : ∀ t, b t = bnd.testBit ((t + φ) % 4))
    (hx : ∀ d, W < d → reconB b y d 0 = false) :
    ∃ t, t < K ∧ ¬ KeepsG φ ones y t := by
  refine Classical.byContradiction fun hne => ?_
  have hall : ∀ t, t < K → KeepsG φ ones y t := by
    intro t ht
    exact Classical.byContradiction fun hk => hne ⟨t, ht, hk⟩
  let p := pack (fun s => y (freeTime φ s)) n
  let c := pack (fun s => y (freeTime φ (n + s))) (freeCount W φ - n)
  have hcheck := hc c (pack_lt _ _)
  have hp : p < 2 ^ n := pack_lt _ _
  have hALL : (2 ^ 2 ^ n - 1).testBit p = true := by
    rw [Nat.testBit_two_pow_sub_one]; simpa using hp
  refine runG_sound W φ n c (2 ^ 2 ^ n - 1) ones bnd ((List.range n).map (pat n)) b y p hALL hb ?_ hx K 0 [] []
    (2 ^ 2 ^ n - 1) hcheck (fun t _ ht => hall t (by omega)) rfl rfl hALL
  intro t ht htW
  have hlt := freeIdx_lt W φ t hφ ht htW
  have hy : y (freeTime φ (freeIdx φ t)) = y t := by rw [freeTime_freeIdx φ t hφ ht]
  generalize freeIdx φ t = s at hlt hy
  unfold yFree
  by_cases hs : s < n
  · rw [ite_eq_left hs, pats_getD n s hs, pat_spec n s p hs hp, testBit_pack]
    simp [hs, hy]
  · rw [ite_eq_right hs, testBit_pack]
    have hsn : s - n < freeCount W φ - n := by omega
    have hyy : y (freeTime φ (n + (s - n))) = y t := by
      rw [show n + (s - n) = s by omega]; exact hy
    simp only [hsn, decide_true, Bool.true_and, hyy]
    cases y t
    · simp
    · simpa using hALL

/-- The chunks `lo, …, lo + cnt - 1` pass from phase `φ`. -/
def ChunksG (W K φ n ones bnd lo cnt : Nat) : Prop :=
  ∀ c, lo ≤ c → c < lo + cnt → checkG W K φ n ones bnd c = true

theorem chunksG_one {W K φ n ones bnd c : Nat} (h : checkG W K φ n ones bnd c = true) :
    ChunksG W K φ n ones bnd c 1 :=
  fun c' h1 h2 => by rw [show c' = c by omega]; exact h

theorem chunksG_append {W K φ n ones bnd lo a b : Nat} (h1 : ChunksG W K φ n ones bnd lo a)
    (h2 : ChunksG W K φ n ones bnd (lo + a) b) : ChunksG W K φ n ones bnd lo (a + b) := fun c hc1 hc2 => by
  rcases Nat.lt_or_ge c (lo + a) with h | h
  · exact h1 c hc1 h
  · exact h2 c h (by omega)

/-! ### The checks at depth 88

The pattern of both words, with the free reading moved to phase `1`, reads `1` at phase `0` and `0` at phases `2`
and `3` (`ones = 1`); the boundary is black at phase `3` for `0011` (`bnd = 8`) and at phases `2` and `3` for `0111`
(`bnd = 12`). For each word and phase, `16` chunks of `2 ^ 18` lanes cover the `2 ^ 22` choices of the free
readings; each check runs `115` levels. -/

theorem chunk0011_0_0 : checkG 88 115 0 18 1 8 0 = true := by decide +kernel
theorem chunk0011_0_1 : checkG 88 115 0 18 1 8 1 = true := by decide +kernel
theorem chunk0011_0_2 : checkG 88 115 0 18 1 8 2 = true := by decide +kernel
theorem chunk0011_0_3 : checkG 88 115 0 18 1 8 3 = true := by decide +kernel
theorem chunk0011_0_4 : checkG 88 115 0 18 1 8 4 = true := by decide +kernel
theorem chunk0011_0_5 : checkG 88 115 0 18 1 8 5 = true := by decide +kernel
theorem chunk0011_0_6 : checkG 88 115 0 18 1 8 6 = true := by decide +kernel
theorem chunk0011_0_7 : checkG 88 115 0 18 1 8 7 = true := by decide +kernel
theorem chunk0011_0_8 : checkG 88 115 0 18 1 8 8 = true := by decide +kernel
theorem chunk0011_0_9 : checkG 88 115 0 18 1 8 9 = true := by decide +kernel
theorem chunk0011_0_10 : checkG 88 115 0 18 1 8 10 = true := by decide +kernel
theorem chunk0011_0_11 : checkG 88 115 0 18 1 8 11 = true := by decide +kernel
theorem chunk0011_0_12 : checkG 88 115 0 18 1 8 12 = true := by decide +kernel
theorem chunk0011_0_13 : checkG 88 115 0 18 1 8 13 = true := by decide +kernel
theorem chunk0011_0_14 : checkG 88 115 0 18 1 8 14 = true := by decide +kernel
theorem chunk0011_0_15 : checkG 88 115 0 18 1 8 15 = true := by decide +kernel

theorem chunks0011_0 : ChunksG 88 115 0 18 1 8 0 16 := by
  have h := chunksG_one chunk0011_0_0
  have h := chunksG_append h (chunksG_one chunk0011_0_1)
  have h := chunksG_append h (chunksG_one chunk0011_0_2)
  have h := chunksG_append h (chunksG_one chunk0011_0_3)
  have h := chunksG_append h (chunksG_one chunk0011_0_4)
  have h := chunksG_append h (chunksG_one chunk0011_0_5)
  have h := chunksG_append h (chunksG_one chunk0011_0_6)
  have h := chunksG_append h (chunksG_one chunk0011_0_7)
  have h := chunksG_append h (chunksG_one chunk0011_0_8)
  have h := chunksG_append h (chunksG_one chunk0011_0_9)
  have h := chunksG_append h (chunksG_one chunk0011_0_10)
  have h := chunksG_append h (chunksG_one chunk0011_0_11)
  have h := chunksG_append h (chunksG_one chunk0011_0_12)
  have h := chunksG_append h (chunksG_one chunk0011_0_13)
  have h := chunksG_append h (chunksG_one chunk0011_0_14)
  have h := chunksG_append h (chunksG_one chunk0011_0_15)
  exact h

theorem chunk0011_1_0 : checkG 88 115 1 18 1 8 0 = true := by decide +kernel
theorem chunk0011_1_1 : checkG 88 115 1 18 1 8 1 = true := by decide +kernel
theorem chunk0011_1_2 : checkG 88 115 1 18 1 8 2 = true := by decide +kernel
theorem chunk0011_1_3 : checkG 88 115 1 18 1 8 3 = true := by decide +kernel
theorem chunk0011_1_4 : checkG 88 115 1 18 1 8 4 = true := by decide +kernel
theorem chunk0011_1_5 : checkG 88 115 1 18 1 8 5 = true := by decide +kernel
theorem chunk0011_1_6 : checkG 88 115 1 18 1 8 6 = true := by decide +kernel
theorem chunk0011_1_7 : checkG 88 115 1 18 1 8 7 = true := by decide +kernel
theorem chunk0011_1_8 : checkG 88 115 1 18 1 8 8 = true := by decide +kernel
theorem chunk0011_1_9 : checkG 88 115 1 18 1 8 9 = true := by decide +kernel
theorem chunk0011_1_10 : checkG 88 115 1 18 1 8 10 = true := by decide +kernel
theorem chunk0011_1_11 : checkG 88 115 1 18 1 8 11 = true := by decide +kernel
theorem chunk0011_1_12 : checkG 88 115 1 18 1 8 12 = true := by decide +kernel
theorem chunk0011_1_13 : checkG 88 115 1 18 1 8 13 = true := by decide +kernel
theorem chunk0011_1_14 : checkG 88 115 1 18 1 8 14 = true := by decide +kernel
theorem chunk0011_1_15 : checkG 88 115 1 18 1 8 15 = true := by decide +kernel

theorem chunks0011_1 : ChunksG 88 115 1 18 1 8 0 16 := by
  have h := chunksG_one chunk0011_1_0
  have h := chunksG_append h (chunksG_one chunk0011_1_1)
  have h := chunksG_append h (chunksG_one chunk0011_1_2)
  have h := chunksG_append h (chunksG_one chunk0011_1_3)
  have h := chunksG_append h (chunksG_one chunk0011_1_4)
  have h := chunksG_append h (chunksG_one chunk0011_1_5)
  have h := chunksG_append h (chunksG_one chunk0011_1_6)
  have h := chunksG_append h (chunksG_one chunk0011_1_7)
  have h := chunksG_append h (chunksG_one chunk0011_1_8)
  have h := chunksG_append h (chunksG_one chunk0011_1_9)
  have h := chunksG_append h (chunksG_one chunk0011_1_10)
  have h := chunksG_append h (chunksG_one chunk0011_1_11)
  have h := chunksG_append h (chunksG_one chunk0011_1_12)
  have h := chunksG_append h (chunksG_one chunk0011_1_13)
  have h := chunksG_append h (chunksG_one chunk0011_1_14)
  have h := chunksG_append h (chunksG_one chunk0011_1_15)
  exact h

theorem chunk0011_2_0 : checkG 88 115 2 18 1 8 0 = true := by decide +kernel
theorem chunk0011_2_1 : checkG 88 115 2 18 1 8 1 = true := by decide +kernel
theorem chunk0011_2_2 : checkG 88 115 2 18 1 8 2 = true := by decide +kernel
theorem chunk0011_2_3 : checkG 88 115 2 18 1 8 3 = true := by decide +kernel
theorem chunk0011_2_4 : checkG 88 115 2 18 1 8 4 = true := by decide +kernel
theorem chunk0011_2_5 : checkG 88 115 2 18 1 8 5 = true := by decide +kernel
theorem chunk0011_2_6 : checkG 88 115 2 18 1 8 6 = true := by decide +kernel
theorem chunk0011_2_7 : checkG 88 115 2 18 1 8 7 = true := by decide +kernel
theorem chunk0011_2_8 : checkG 88 115 2 18 1 8 8 = true := by decide +kernel
theorem chunk0011_2_9 : checkG 88 115 2 18 1 8 9 = true := by decide +kernel
theorem chunk0011_2_10 : checkG 88 115 2 18 1 8 10 = true := by decide +kernel
theorem chunk0011_2_11 : checkG 88 115 2 18 1 8 11 = true := by decide +kernel
theorem chunk0011_2_12 : checkG 88 115 2 18 1 8 12 = true := by decide +kernel
theorem chunk0011_2_13 : checkG 88 115 2 18 1 8 13 = true := by decide +kernel
theorem chunk0011_2_14 : checkG 88 115 2 18 1 8 14 = true := by decide +kernel
theorem chunk0011_2_15 : checkG 88 115 2 18 1 8 15 = true := by decide +kernel

theorem chunks0011_2 : ChunksG 88 115 2 18 1 8 0 16 := by
  have h := chunksG_one chunk0011_2_0
  have h := chunksG_append h (chunksG_one chunk0011_2_1)
  have h := chunksG_append h (chunksG_one chunk0011_2_2)
  have h := chunksG_append h (chunksG_one chunk0011_2_3)
  have h := chunksG_append h (chunksG_one chunk0011_2_4)
  have h := chunksG_append h (chunksG_one chunk0011_2_5)
  have h := chunksG_append h (chunksG_one chunk0011_2_6)
  have h := chunksG_append h (chunksG_one chunk0011_2_7)
  have h := chunksG_append h (chunksG_one chunk0011_2_8)
  have h := chunksG_append h (chunksG_one chunk0011_2_9)
  have h := chunksG_append h (chunksG_one chunk0011_2_10)
  have h := chunksG_append h (chunksG_one chunk0011_2_11)
  have h := chunksG_append h (chunksG_one chunk0011_2_12)
  have h := chunksG_append h (chunksG_one chunk0011_2_13)
  have h := chunksG_append h (chunksG_one chunk0011_2_14)
  have h := chunksG_append h (chunksG_one chunk0011_2_15)
  exact h

theorem chunk0011_3_0 : checkG 88 115 3 18 1 8 0 = true := by decide +kernel
theorem chunk0011_3_1 : checkG 88 115 3 18 1 8 1 = true := by decide +kernel
theorem chunk0011_3_2 : checkG 88 115 3 18 1 8 2 = true := by decide +kernel
theorem chunk0011_3_3 : checkG 88 115 3 18 1 8 3 = true := by decide +kernel
theorem chunk0011_3_4 : checkG 88 115 3 18 1 8 4 = true := by decide +kernel
theorem chunk0011_3_5 : checkG 88 115 3 18 1 8 5 = true := by decide +kernel
theorem chunk0011_3_6 : checkG 88 115 3 18 1 8 6 = true := by decide +kernel
theorem chunk0011_3_7 : checkG 88 115 3 18 1 8 7 = true := by decide +kernel
theorem chunk0011_3_8 : checkG 88 115 3 18 1 8 8 = true := by decide +kernel
theorem chunk0011_3_9 : checkG 88 115 3 18 1 8 9 = true := by decide +kernel
theorem chunk0011_3_10 : checkG 88 115 3 18 1 8 10 = true := by decide +kernel
theorem chunk0011_3_11 : checkG 88 115 3 18 1 8 11 = true := by decide +kernel
theorem chunk0011_3_12 : checkG 88 115 3 18 1 8 12 = true := by decide +kernel
theorem chunk0011_3_13 : checkG 88 115 3 18 1 8 13 = true := by decide +kernel
theorem chunk0011_3_14 : checkG 88 115 3 18 1 8 14 = true := by decide +kernel
theorem chunk0011_3_15 : checkG 88 115 3 18 1 8 15 = true := by decide +kernel

theorem chunks0011_3 : ChunksG 88 115 3 18 1 8 0 16 := by
  have h := chunksG_one chunk0011_3_0
  have h := chunksG_append h (chunksG_one chunk0011_3_1)
  have h := chunksG_append h (chunksG_one chunk0011_3_2)
  have h := chunksG_append h (chunksG_one chunk0011_3_3)
  have h := chunksG_append h (chunksG_one chunk0011_3_4)
  have h := chunksG_append h (chunksG_one chunk0011_3_5)
  have h := chunksG_append h (chunksG_one chunk0011_3_6)
  have h := chunksG_append h (chunksG_one chunk0011_3_7)
  have h := chunksG_append h (chunksG_one chunk0011_3_8)
  have h := chunksG_append h (chunksG_one chunk0011_3_9)
  have h := chunksG_append h (chunksG_one chunk0011_3_10)
  have h := chunksG_append h (chunksG_one chunk0011_3_11)
  have h := chunksG_append h (chunksG_one chunk0011_3_12)
  have h := chunksG_append h (chunksG_one chunk0011_3_13)
  have h := chunksG_append h (chunksG_one chunk0011_3_14)
  have h := chunksG_append h (chunksG_one chunk0011_3_15)
  exact h

/-- **Every start of depth at most 88 breaks the pattern of `0011`**, from every phase, within 115
steps. -/
theorem c3_0011_depth (φ : Nat) (hφ : φ < 4) (b y : Nat → Bool)
    (hb : ∀ t, b t = (8 : Nat).testBit ((t + φ) % 4)) (hx : ∀ d, 88 < d → reconB b y d 0 = false) :
    ∃ t, t < 115 ∧ ¬ KeepsG φ 1 y t := by
  have hcount : freeCount 88 φ = 22 := by
    rcases (show φ = 0 ∨ φ = 1 ∨ φ = 2 ∨ φ = 3 by omega) with rfl | rfl | rfl | rfl <;> rfl
  refine c3G_of_checks 88 115 φ 18 1 8 hφ (by rw [hcount]; decide) ?_ b y hb hx
  rw [hcount]
  intro c hc
  have hc' : c < 0 + 16 := by
    have : 2 ^ (22 - 18) = 16 := rfl
    omega
  rcases (show φ = 0 ∨ φ = 1 ∨ φ = 2 ∨ φ = 3 by omega) with rfl | rfl | rfl | rfl
  · exact chunks0011_0 c (Nat.zero_le c) hc'
  · exact chunks0011_1 c (Nat.zero_le c) hc'
  · exact chunks0011_2 c (Nat.zero_le c) hc'
  · exact chunks0011_3 c (Nat.zero_le c) hc'

theorem chunk0111_0_0 : checkG 88 115 0 18 1 12 0 = true := by decide +kernel
theorem chunk0111_0_1 : checkG 88 115 0 18 1 12 1 = true := by decide +kernel
theorem chunk0111_0_2 : checkG 88 115 0 18 1 12 2 = true := by decide +kernel
theorem chunk0111_0_3 : checkG 88 115 0 18 1 12 3 = true := by decide +kernel
theorem chunk0111_0_4 : checkG 88 115 0 18 1 12 4 = true := by decide +kernel
theorem chunk0111_0_5 : checkG 88 115 0 18 1 12 5 = true := by decide +kernel
theorem chunk0111_0_6 : checkG 88 115 0 18 1 12 6 = true := by decide +kernel
theorem chunk0111_0_7 : checkG 88 115 0 18 1 12 7 = true := by decide +kernel
theorem chunk0111_0_8 : checkG 88 115 0 18 1 12 8 = true := by decide +kernel
theorem chunk0111_0_9 : checkG 88 115 0 18 1 12 9 = true := by decide +kernel
theorem chunk0111_0_10 : checkG 88 115 0 18 1 12 10 = true := by decide +kernel
theorem chunk0111_0_11 : checkG 88 115 0 18 1 12 11 = true := by decide +kernel
theorem chunk0111_0_12 : checkG 88 115 0 18 1 12 12 = true := by decide +kernel
theorem chunk0111_0_13 : checkG 88 115 0 18 1 12 13 = true := by decide +kernel
theorem chunk0111_0_14 : checkG 88 115 0 18 1 12 14 = true := by decide +kernel
theorem chunk0111_0_15 : checkG 88 115 0 18 1 12 15 = true := by decide +kernel

theorem chunks0111_0 : ChunksG 88 115 0 18 1 12 0 16 := by
  have h := chunksG_one chunk0111_0_0
  have h := chunksG_append h (chunksG_one chunk0111_0_1)
  have h := chunksG_append h (chunksG_one chunk0111_0_2)
  have h := chunksG_append h (chunksG_one chunk0111_0_3)
  have h := chunksG_append h (chunksG_one chunk0111_0_4)
  have h := chunksG_append h (chunksG_one chunk0111_0_5)
  have h := chunksG_append h (chunksG_one chunk0111_0_6)
  have h := chunksG_append h (chunksG_one chunk0111_0_7)
  have h := chunksG_append h (chunksG_one chunk0111_0_8)
  have h := chunksG_append h (chunksG_one chunk0111_0_9)
  have h := chunksG_append h (chunksG_one chunk0111_0_10)
  have h := chunksG_append h (chunksG_one chunk0111_0_11)
  have h := chunksG_append h (chunksG_one chunk0111_0_12)
  have h := chunksG_append h (chunksG_one chunk0111_0_13)
  have h := chunksG_append h (chunksG_one chunk0111_0_14)
  have h := chunksG_append h (chunksG_one chunk0111_0_15)
  exact h

theorem chunk0111_1_0 : checkG 88 115 1 18 1 12 0 = true := by decide +kernel
theorem chunk0111_1_1 : checkG 88 115 1 18 1 12 1 = true := by decide +kernel
theorem chunk0111_1_2 : checkG 88 115 1 18 1 12 2 = true := by decide +kernel
theorem chunk0111_1_3 : checkG 88 115 1 18 1 12 3 = true := by decide +kernel
theorem chunk0111_1_4 : checkG 88 115 1 18 1 12 4 = true := by decide +kernel
theorem chunk0111_1_5 : checkG 88 115 1 18 1 12 5 = true := by decide +kernel
theorem chunk0111_1_6 : checkG 88 115 1 18 1 12 6 = true := by decide +kernel
theorem chunk0111_1_7 : checkG 88 115 1 18 1 12 7 = true := by decide +kernel
theorem chunk0111_1_8 : checkG 88 115 1 18 1 12 8 = true := by decide +kernel
theorem chunk0111_1_9 : checkG 88 115 1 18 1 12 9 = true := by decide +kernel
theorem chunk0111_1_10 : checkG 88 115 1 18 1 12 10 = true := by decide +kernel
theorem chunk0111_1_11 : checkG 88 115 1 18 1 12 11 = true := by decide +kernel
theorem chunk0111_1_12 : checkG 88 115 1 18 1 12 12 = true := by decide +kernel
theorem chunk0111_1_13 : checkG 88 115 1 18 1 12 13 = true := by decide +kernel
theorem chunk0111_1_14 : checkG 88 115 1 18 1 12 14 = true := by decide +kernel
theorem chunk0111_1_15 : checkG 88 115 1 18 1 12 15 = true := by decide +kernel

theorem chunks0111_1 : ChunksG 88 115 1 18 1 12 0 16 := by
  have h := chunksG_one chunk0111_1_0
  have h := chunksG_append h (chunksG_one chunk0111_1_1)
  have h := chunksG_append h (chunksG_one chunk0111_1_2)
  have h := chunksG_append h (chunksG_one chunk0111_1_3)
  have h := chunksG_append h (chunksG_one chunk0111_1_4)
  have h := chunksG_append h (chunksG_one chunk0111_1_5)
  have h := chunksG_append h (chunksG_one chunk0111_1_6)
  have h := chunksG_append h (chunksG_one chunk0111_1_7)
  have h := chunksG_append h (chunksG_one chunk0111_1_8)
  have h := chunksG_append h (chunksG_one chunk0111_1_9)
  have h := chunksG_append h (chunksG_one chunk0111_1_10)
  have h := chunksG_append h (chunksG_one chunk0111_1_11)
  have h := chunksG_append h (chunksG_one chunk0111_1_12)
  have h := chunksG_append h (chunksG_one chunk0111_1_13)
  have h := chunksG_append h (chunksG_one chunk0111_1_14)
  have h := chunksG_append h (chunksG_one chunk0111_1_15)
  exact h

theorem chunk0111_2_0 : checkG 88 115 2 18 1 12 0 = true := by decide +kernel
theorem chunk0111_2_1 : checkG 88 115 2 18 1 12 1 = true := by decide +kernel
theorem chunk0111_2_2 : checkG 88 115 2 18 1 12 2 = true := by decide +kernel
theorem chunk0111_2_3 : checkG 88 115 2 18 1 12 3 = true := by decide +kernel
theorem chunk0111_2_4 : checkG 88 115 2 18 1 12 4 = true := by decide +kernel
theorem chunk0111_2_5 : checkG 88 115 2 18 1 12 5 = true := by decide +kernel
theorem chunk0111_2_6 : checkG 88 115 2 18 1 12 6 = true := by decide +kernel
theorem chunk0111_2_7 : checkG 88 115 2 18 1 12 7 = true := by decide +kernel
theorem chunk0111_2_8 : checkG 88 115 2 18 1 12 8 = true := by decide +kernel
theorem chunk0111_2_9 : checkG 88 115 2 18 1 12 9 = true := by decide +kernel
theorem chunk0111_2_10 : checkG 88 115 2 18 1 12 10 = true := by decide +kernel
theorem chunk0111_2_11 : checkG 88 115 2 18 1 12 11 = true := by decide +kernel
theorem chunk0111_2_12 : checkG 88 115 2 18 1 12 12 = true := by decide +kernel
theorem chunk0111_2_13 : checkG 88 115 2 18 1 12 13 = true := by decide +kernel
theorem chunk0111_2_14 : checkG 88 115 2 18 1 12 14 = true := by decide +kernel
theorem chunk0111_2_15 : checkG 88 115 2 18 1 12 15 = true := by decide +kernel

theorem chunks0111_2 : ChunksG 88 115 2 18 1 12 0 16 := by
  have h := chunksG_one chunk0111_2_0
  have h := chunksG_append h (chunksG_one chunk0111_2_1)
  have h := chunksG_append h (chunksG_one chunk0111_2_2)
  have h := chunksG_append h (chunksG_one chunk0111_2_3)
  have h := chunksG_append h (chunksG_one chunk0111_2_4)
  have h := chunksG_append h (chunksG_one chunk0111_2_5)
  have h := chunksG_append h (chunksG_one chunk0111_2_6)
  have h := chunksG_append h (chunksG_one chunk0111_2_7)
  have h := chunksG_append h (chunksG_one chunk0111_2_8)
  have h := chunksG_append h (chunksG_one chunk0111_2_9)
  have h := chunksG_append h (chunksG_one chunk0111_2_10)
  have h := chunksG_append h (chunksG_one chunk0111_2_11)
  have h := chunksG_append h (chunksG_one chunk0111_2_12)
  have h := chunksG_append h (chunksG_one chunk0111_2_13)
  have h := chunksG_append h (chunksG_one chunk0111_2_14)
  have h := chunksG_append h (chunksG_one chunk0111_2_15)
  exact h

theorem chunk0111_3_0 : checkG 88 115 3 18 1 12 0 = true := by decide +kernel
theorem chunk0111_3_1 : checkG 88 115 3 18 1 12 1 = true := by decide +kernel
theorem chunk0111_3_2 : checkG 88 115 3 18 1 12 2 = true := by decide +kernel
theorem chunk0111_3_3 : checkG 88 115 3 18 1 12 3 = true := by decide +kernel
theorem chunk0111_3_4 : checkG 88 115 3 18 1 12 4 = true := by decide +kernel
theorem chunk0111_3_5 : checkG 88 115 3 18 1 12 5 = true := by decide +kernel
theorem chunk0111_3_6 : checkG 88 115 3 18 1 12 6 = true := by decide +kernel
theorem chunk0111_3_7 : checkG 88 115 3 18 1 12 7 = true := by decide +kernel
theorem chunk0111_3_8 : checkG 88 115 3 18 1 12 8 = true := by decide +kernel
theorem chunk0111_3_9 : checkG 88 115 3 18 1 12 9 = true := by decide +kernel
theorem chunk0111_3_10 : checkG 88 115 3 18 1 12 10 = true := by decide +kernel
theorem chunk0111_3_11 : checkG 88 115 3 18 1 12 11 = true := by decide +kernel
theorem chunk0111_3_12 : checkG 88 115 3 18 1 12 12 = true := by decide +kernel
theorem chunk0111_3_13 : checkG 88 115 3 18 1 12 13 = true := by decide +kernel
theorem chunk0111_3_14 : checkG 88 115 3 18 1 12 14 = true := by decide +kernel
theorem chunk0111_3_15 : checkG 88 115 3 18 1 12 15 = true := by decide +kernel

theorem chunks0111_3 : ChunksG 88 115 3 18 1 12 0 16 := by
  have h := chunksG_one chunk0111_3_0
  have h := chunksG_append h (chunksG_one chunk0111_3_1)
  have h := chunksG_append h (chunksG_one chunk0111_3_2)
  have h := chunksG_append h (chunksG_one chunk0111_3_3)
  have h := chunksG_append h (chunksG_one chunk0111_3_4)
  have h := chunksG_append h (chunksG_one chunk0111_3_5)
  have h := chunksG_append h (chunksG_one chunk0111_3_6)
  have h := chunksG_append h (chunksG_one chunk0111_3_7)
  have h := chunksG_append h (chunksG_one chunk0111_3_8)
  have h := chunksG_append h (chunksG_one chunk0111_3_9)
  have h := chunksG_append h (chunksG_one chunk0111_3_10)
  have h := chunksG_append h (chunksG_one chunk0111_3_11)
  have h := chunksG_append h (chunksG_one chunk0111_3_12)
  have h := chunksG_append h (chunksG_one chunk0111_3_13)
  have h := chunksG_append h (chunksG_one chunk0111_3_14)
  have h := chunksG_append h (chunksG_one chunk0111_3_15)
  exact h

/-- **Every start of depth at most 88 breaks the pattern of `0111`**, from every phase, within 115
steps. -/
theorem c3_0111_depth (φ : Nat) (hφ : φ < 4) (b y : Nat → Bool)
    (hb : ∀ t, b t = (12 : Nat).testBit ((t + φ) % 4)) (hx : ∀ d, 88 < d → reconB b y d 0 = false) :
    ∃ t, t < 115 ∧ ¬ KeepsG φ 1 y t := by
  have hcount : freeCount 88 φ = 22 := by
    rcases (show φ = 0 ∨ φ = 1 ∨ φ = 2 ∨ φ = 3 by omega) with rfl | rfl | rfl | rfl <;> rfl
  refine c3G_of_checks 88 115 φ 18 1 12 hφ (by rw [hcount]; decide) ?_ b y hb hx
  rw [hcount]
  intro c hc
  have hc' : c < 0 + 16 := by
    have : 2 ^ (22 - 18) = 16 := rfl
    omega
  rcases (show φ = 0 ∨ φ = 1 ∨ φ = 2 ∨ φ = 3 by omega) with rfl | rfl | rfl | rfl
  · exact chunks0111_0 c (Nat.zero_le c) hc'
  · exact chunks0111_1 c (Nat.zero_le c) hc'
  · exact chunks0111_2 c (Nat.zero_le c) hc'
  · exact chunks0111_3 c (Nat.zero_le c) hc'

/-! ### Sharpness at depth 20

At depth `20` one chunk of `2 ^ 5` lanes covers every start, and the least number of levels that passes is one more
than the latest first failure over the starts of at most `20` cells. -/

theorem sharp20_0011_0 : checkG 20 29 0 5 1 8 0 = true ∧ checkG 20 28 0 5 1 8 0 = false := by
  decide +kernel
theorem sharp20_0011_1 : checkG 20 42 1 5 1 8 0 = true ∧ checkG 20 41 1 5 1 8 0 = false := by
  decide +kernel
theorem sharp20_0011_2 : checkG 20 41 2 5 1 8 0 = true ∧ checkG 20 40 2 5 1 8 0 = false := by
  decide +kernel
theorem sharp20_0011_3 : checkG 20 40 3 5 1 8 0 = true ∧ checkG 20 39 3 5 1 8 0 = false := by
  decide +kernel
theorem sharp20_0111_0 : checkG 20 27 0 5 1 12 0 = true ∧ checkG 20 26 0 5 1 12 0 = false := by
  decide +kernel
theorem sharp20_0111_1 : checkG 20 27 1 5 1 12 0 = true ∧ checkG 20 26 1 5 1 12 0 = false := by
  decide +kernel
theorem sharp20_0111_2 : checkG 20 29 2 5 1 12 0 = true ∧ checkG 20 28 2 5 1 12 0 = false := by
  decide +kernel
theorem sharp20_0111_3 : checkG 20 28 3 5 1 12 0 = true ∧ checkG 20 27 3 5 1 12 0 = false := by
  decide +kernel

/-! ### The kit's statements -/

open Rule30PeriodFourSkeleton (fits colPattern effWord effWord_0011 effWord_0111)
open Rule30Ether (wordAt w0011 w0111)

/-- The kit's effective boundary for `0011`, black at phase `2`, from time `K` with the phase moved by one. -/
theorem drive_0011 (K t : Nat) :
    wordAt (effWord w0011) (K + t) = (8 : Nat).testBit ((t + (K + 1) % 4) % 4) := by
  rw [effWord_0011]
  unfold wordAt
  rcases (show (K + t) % 4 = 0 ∨ (K + t) % 4 = 1 ∨ (K + t) % 4 = 2 ∨ (K + t) % 4 = 3 by omega) with h | h | h | h
  · rw [h, show (t + (K + 1) % 4) % 4 = 1 by omega]; rfl
  · rw [h, show (t + (K + 1) % 4) % 4 = 2 by omega]; rfl
  · rw [h, show (t + (K + 1) % 4) % 4 = 3 by omega]; rfl
  · rw [h, show (t + (K + 1) % 4) % 4 = 0 by omega]; rfl

/-- The kit's effective boundary for `0111`, black at phases `1` and `2`, from time `K` with the phase moved by one. -/
theorem drive_0111 (K t : Nat) :
    wordAt (effWord w0111) (K + t) = (12 : Nat).testBit ((t + (K + 1) % 4) % 4) := by
  rw [effWord_0111]
  unfold wordAt
  rcases (show (K + t) % 4 = 0 ∨ (K + t) % 4 = 1 ∨ (K + t) % 4 = 2 ∨ (K + t) % 4 = 3 by omega) with h | h | h | h
  · rw [h, show (t + (K + 1) % 4) % 4 = 1 by omega]; rfl
  · rw [h, show (t + (K + 1) % 4) % 4 = 2 by omega]; rfl
  · rw [h, show (t + (K + 1) % 4) % 4 = 3 by omega]; rfl
  · rw [h, show (t + (K + 1) % 4) % 4 = 0 by omega]; rfl

/-- The kit's pattern for `0011` and `0111` at time `k`, with the phase moved by one: black at phase `3`, white at
phases `1` and `2`. -/
theorem fits_x011 (w : List Bool) (hw : colPattern w = [none, some false, some false, some true]) (k : Nat) (v : Bool)
    (h : fits (colPattern w) (k % 4) v = true) : (k + 1) % 4 ≠ 1 → v = (1 : Nat).testBit ((k + 1) % 4) := by
  intro hne
  rw [hw] at h
  rcases (show k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 by omega) with h4 | h4 | h4 | h4
  · exact absurd (by omega) hne
  · rw [h4] at h; rw [show (k + 1) % 4 = 2 by omega]; revert h; cases v <;> decide
  · rw [h4] at h; rw [show (k + 1) % 4 = 3 by omega]; revert h; cases v <;> decide
  · rw [h4] at h; rw [show (k + 1) % 4 = 0 by omega]; revert h; cases v <;> decide

/-- The support of the driven half grows by at most one cell per step, whatever the boundary. -/
theorem L_fin (c : Nat → Bool) (s : Int → Bool) (M : Nat) (hs : ∀ p : Int, p < -(M : Int) → s p = false) :
    ∀ t : Nat, ∀ p : Int, p < -((M + t : Nat) : Int) → Rule30DrivenLeft.L c s t p = false := by
  intro t
  induction t with
  | zero => intro p hp; rw [Rule30DrivenLeft.L_zero (by omega)]; exact hs p (by omega)
  | succ t ih =>
    intro p hp
    rw [Rule30DrivenLeft.L_succ (by omega), ih (p - 1) (by omega), ih p (by omega), ih (p + 1) (by omega)]
    rfl

/-- **A bounded case of the kit's `C3 w0011`.** A left half that keeps the kit's pattern for `0011` from time `K` on,
beside the effective boundary, has a black cell at a depth beyond `88` at time `K`. -/
theorem c3_0011_bounded (s : Int → Bool) (K : Nat)
    (hK : ∀ k, K ≤ k → fits (colPattern w0011) (k % 4)
      (Rule30DrivenLeft.L (fun k => wordAt (effWord w0011) k) s k (-1)) = true) :
    ∃ d : Nat, 88 < d ∧ Rule30DrivenLeft.L (fun k => wordAt (effWord w0011) k) s K (-(d : Int)) = true := by
  refine Classical.byContradiction fun hne => ?_
  have hx : ∀ d, 88 < d → reconB (fun t => wordAt (effWord w0011) (K + t))
      (fun t => Rule30DrivenLeft.L (fun k => wordAt (effWord w0011) k) s (K + t) (-1)) d 0 = false := by
    intro d hd
    rw [← history_eq_reconB _ s K d 0, Nat.add_zero]
    cases h : Rule30DrivenLeft.L (fun k => wordAt (effWord w0011) k) s K (-(d : Int))
    · rfl
    · exact absurd ⟨d, hd, h⟩ hne
  obtain ⟨t, -, hbad⟩ := c3_0011_depth ((K + 1) % 4) (Nat.mod_lt _ (by decide)) _ _ (drive_0011 K) hx
  apply hbad
  intro hr
  have hf := fits_x011 w0011 rfl (K + t) _ (hK (K + t) (by omega))
  rw [show (K + t + 1) % 4 = (t + (K + 1) % 4) % 4 by omega] at hf
  exact hf hr

/-- **Small starts.** No left half supported within depth `M` keeps the kit's pattern for `0011` from a time `K` with
`M + K ≤ 88`; in particular none of at most 88 cells keeps it from time `0`. -/
theorem c3_0011_small (s : Int → Bool) (M K : Nat) (hs : ∀ p : Int, p < -(M : Int) → s p = false)
    (hMK : M + K ≤ 88) :
    ¬ ∀ k, K ≤ k → fits (colPattern w0011) (k % 4)
      (Rule30DrivenLeft.L (fun k => wordAt (effWord w0011) k) s k (-1)) = true := by
  intro hK
  obtain ⟨d, hd, hb⟩ := c3_0011_bounded s K hK
  rw [L_fin _ s M hs K (-(d : Int)) (by omega)] at hb
  exact absurd hb (by decide)

/-- **A bounded case of the kit's `C3 w0111`.** A left half that keeps the kit's pattern for `0111` from time `K` on,
beside the effective boundary, has a black cell at a depth beyond `88` at time `K`. -/
theorem c3_0111_bounded (s : Int → Bool) (K : Nat)
    (hK : ∀ k, K ≤ k → fits (colPattern w0111) (k % 4)
      (Rule30DrivenLeft.L (fun k => wordAt (effWord w0111) k) s k (-1)) = true) :
    ∃ d : Nat, 88 < d ∧ Rule30DrivenLeft.L (fun k => wordAt (effWord w0111) k) s K (-(d : Int)) = true := by
  refine Classical.byContradiction fun hne => ?_
  have hx : ∀ d, 88 < d → reconB (fun t => wordAt (effWord w0111) (K + t))
      (fun t => Rule30DrivenLeft.L (fun k => wordAt (effWord w0111) k) s (K + t) (-1)) d 0 = false := by
    intro d hd
    rw [← history_eq_reconB _ s K d 0, Nat.add_zero]
    cases h : Rule30DrivenLeft.L (fun k => wordAt (effWord w0111) k) s K (-(d : Int))
    · rfl
    · exact absurd ⟨d, hd, h⟩ hne
  obtain ⟨t, -, hbad⟩ := c3_0111_depth ((K + 1) % 4) (Nat.mod_lt _ (by decide)) _ _ (drive_0111 K) hx
  apply hbad
  intro hr
  have hf := fits_x011 w0111 rfl (K + t) _ (hK (K + t) (by omega))
  rw [show (K + t + 1) % 4 = (t + (K + 1) % 4) % 4 by omega] at hf
  exact hf hr

/-- **Small starts.** No left half supported within depth `M` keeps the kit's pattern for `0111` from a time `K` with
`M + K ≤ 88`; in particular none of at most 88 cells keeps it from time `0`. -/
theorem c3_0111_small (s : Int → Bool) (M K : Nat) (hs : ∀ p : Int, p < -(M : Int) → s p = false)
    (hMK : M + K ≤ 88) :
    ¬ ∀ k, K ≤ k → fits (colPattern w0111) (k % 4)
      (Rule30DrivenLeft.L (fun k => wordAt (effWord w0111) k) s k (-1)) = true := by
  intro hK
  obtain ⟨d, hd, hb⟩ := c3_0111_bounded s K hK
  rw [L_fin _ s M hs K (-(d : Int)) (by omega)] at hb
  exact absurd hb (by decide)

end Rule30Open
