module

public import Ruliology.CellularAutomata.Rule30ZeroBoundaryLanes
public import Ruliology.CellularAutomata.Rule30PeriodFourSkeleton

/-!
# The left half for `0001`: no start of depth at most 88 keeps the kit's pattern

For the word `0001` of least period four the kit reduces Problem 1 to a statement about the left half alone
(`Rule30PeriodFourSkeleton.C3 w0001`, open): no finitely supported left half, run as rule 30 beside the effective
boundary, keeps column `-1` white at the times `4 s` and `4 s + 2` and black at the times `4 s + 3` for all large
times. The effective boundary of `0001` is white (`effWord_0001`), so this half is the kit's zero-boundary left half
(`zrow`).

Column `-1` determines the whole half sideways (the kit's `history_eq_recon`), and the pattern fixes three readings in
four. The kit's lane checker for its period-two statement `Q01` (`Rule30ZeroBoundaryLanes`) runs every choice of the
free readings at once, one choice per bit of a number; here the same checker runs the pattern of `0001` from a phase
`φ`, with one free reading in four (`stepC`, `runC`, `checkC`, `runC_sound`). A start supported at depths `≤ W` has
`freeCount W φ` free readings before its support ends, and every later free reading is forced by the white cells
beyond `W`.

* `c3_0001_of_checks`: if every chunk passes `checkC W K φ n`, every start supported at depths `≤ W` breaks the
  pattern from phase `φ` at some time `< K`.
* `c3_0001_depth`: at depth `88`, from each of the four phases, within `114` steps (`64` chunk checks).
* `c3_0001_bounded`: a left half that keeps the kit's pattern from time `K` on has a black cell beyond depth `88` at
  time `K`; this is `C3 w0001` for every half whose row at time `K` lies within depth `88`.
* `c3_0001_small`: no left half supported within depth `M` keeps the pattern from a time `K` with `M + K ≤ 88`.
* `sharp20_0` to `sharp20_3`: at depth `20` the least number of levels that passes is one more than the latest first
  failure, from each phase.

The natural-language argument is `LeftHalf0001.md`, beside this file.
-/

@[expose] public section

-- Sequential elaboration: the kernel checks would otherwise run in parallel and stack their memory.
set_option Elab.async false

namespace Rule30Open

open Ruliology.CellularAutomata
open Rule30ZeroBoundary Rule30ZeroBoundaryLanes

/-- The pattern of `0001` on column `-1` from phase `φ`: the phase at time `t` is `(t + φ) % 4`, and the reading is
white at the phases `0` and `2`, black at `3`, free at `1`. -/
def KeepsC3 (φ : Nat) (y : Nat → Bool) (t : Nat) : Prop :=
  ((t + φ) % 4 = 0 → y t = false) ∧ ((t + φ) % 4 = 2 → y t = false) ∧ ((t + φ) % 4 = 3 → y t = true)

/-- The index of the free reading at time `t`, counting from the first free time at or after time `0`. -/
def freeIdx (φ t : Nat) : Nat := (t + φ) / 4 - φ / 2

/-- The time of the free reading of index `s`. -/
def freeTime (φ s : Nat) : Nat := 4 * (s + φ / 2) + 1 - φ

/-- The number of free readings at the times `t` with `t + 1 ≤ W`. -/
def freeCount (W φ : Nat) : Nat := (W + 2 + φ) / 4 - φ / 2

/-- One level for the pattern of `0001` from phase `φ`: the new anti-diagonal `k + 1` and its last entry, in every
lane. Phases `0`, `2`: the reading is white. Phase `3`: black. Phase `1` with `k + 1 ≤ W`: a free reading. Phase `1`
with `W < k + 1`: the reading that makes the start white at depth `k + 1`. -/
noncomputable def stepC (W φ n c ALL : Nat) (pats : List Nat) (k : Nat) (R Rm : List Nat) : List Nat × Nat :=
  Bool.rec
    (let y := Bool.rec 0 ALL (Nat.beq (Nat.mod (Nat.add k φ) 4) 3)
     let r := scanN y R (0 :: Rm); (y :: r.1, r.2))
    (Bool.rec
      (let r := scanN 0 R (0 :: Rm); (r.2 :: mapX r.2 r.1, r.2))
      (let y := yFree n c ALL pats (Nat.sub (Nat.div (Nat.add k φ) 4) (Nat.div φ 2))
       let r := scanN y R (0 :: Rm); (y :: r.1, r.2))
      (Nat.ble (Nat.add k 1) W))
    (Nat.beq (Nat.mod (Nat.add k φ) 4) 1)

/-- Run `fuel` levels from level `k`; a lane dies when a fixed reading leaves the start black at a depth beyond `W`.
Succeeds when no lane is alive at the end. -/
noncomputable def runC (W φ n c ALL : Nat) (pats : List Nat) (fuel : Nat) :
    Nat → List Nat → List Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → List Nat → List Nat → Nat → Bool)
    (fun _ _ _ alive => Nat.beq alive 0)
    (fun _ ih k R Rm alive =>
      let st := stepC W φ n c ALL pats k R Rm
      ih (Nat.add k 1) st.1 R
        (Bool.rec alive (Nat.land alive (Nat.xor ALL st.2))
          (band (Bool.rec true false (Nat.beq (Nat.mod (Nat.add k φ) 4) 1)) (Nat.blt W (Nat.add k 1)))))
    fuel

/-- The check for chunk `c` from phase `φ`: `2 ^ n` lanes, `K` levels, starts supported at depths `≤ W`. -/
noncomputable def checkC (W K φ n c : Nat) : Bool :=
  runC W φ n c (2 ^ 2 ^ n - 1) ((List.range n).map (pat n)) K 0 [] [] (2 ^ 2 ^ n - 1)

theorem runC_zero (W φ n c ALL : Nat) (pats : List Nat) (k : Nat) (R Rm : List Nat) (alive : Nat) :
    runC W φ n c ALL pats 0 k R Rm alive = Nat.beq alive 0 := rfl

theorem runC_succ (W φ n c ALL : Nat) (pats : List Nat) (f k : Nat) (R Rm : List Nat) (alive : Nat) :
    runC W φ n c ALL pats (f + 1) k R Rm alive =
      runC W φ n c ALL pats f (k + 1) (stepC W φ n c ALL pats k R Rm).1 R
        (Bool.rec alive (alive &&& (ALL ^^^ (stepC W φ n c ALL pats k R Rm).2))
          (band (Bool.rec true false (Nat.beq ((k + φ) % 4) 1)) (Nat.blt W (k + 1)))) := rfl

theorem stepC_fixed (W φ n c ALL : Nat) (pats : List Nat) (k : Nat) (R Rm : List Nat) (h : (k + φ) % 4 ≠ 1) :
    stepC W φ n c ALL pats k R Rm =
      (Bool.rec 0 ALL (Nat.beq ((k + φ) % 4) 3) :: (scanN (Bool.rec 0 ALL (Nat.beq ((k + φ) % 4) 3)) R (0 :: Rm)).1,
        (scanN (Bool.rec 0 ALL (Nat.beq ((k + φ) % 4) 3)) R (0 :: Rm)).2) := by
  have hb : Nat.beq (Nat.mod (Nat.add k φ) 4) 1 = false := by
    cases hq : Nat.beq (Nat.mod (Nat.add k φ) 4) 1
    · rfl
    · rw [Nat.beq_eq] at hq; exact absurd hq h
  unfold stepC; rw [hb]; rfl

theorem stepC_free (W φ n c ALL : Nat) (pats : List Nat) (k : Nat) (R Rm : List Nat) (h : (k + φ) % 4 = 1)
    (hW : k + 1 ≤ W) :
    stepC W φ n c ALL pats k R Rm =
      (yFree n c ALL pats (freeIdx φ k) :: (scanN (yFree n c ALL pats (freeIdx φ k)) R (0 :: Rm)).1,
        (scanN (yFree n c ALL pats (freeIdx φ k)) R (0 :: Rm)).2) := by
  have hb : Nat.beq (Nat.mod (Nat.add k φ) 4) 1 = true := by rw [Nat.beq_eq]; exact h
  have hb2 : Nat.ble (Nat.add k 1) W = true := by rw [Nat.ble_eq]; exact hW
  unfold stepC; rw [hb, hb2]; rfl

theorem stepC_forced (W φ n c ALL : Nat) (pats : List Nat) (k : Nat) (R Rm : List Nat) (h : (k + φ) % 4 = 1)
    (hW : W < k + 1) :
    stepC W φ n c ALL pats k R Rm =
      ((scanN 0 R (0 :: Rm)).2 :: mapX (scanN 0 R (0 :: Rm)).2 (scanN 0 R (0 :: Rm)).1,
        (scanN 0 R (0 :: Rm)).2) := by
  have hb : Nat.beq (Nat.mod (Nat.add k φ) 4) 1 = true := by rw [Nat.beq_eq]; exact h
  have hb2 : Nat.ble (Nat.add k 1) W = false := by
    cases hq : Nat.ble (Nat.add k 1) W
    · rfl
    · rw [Nat.ble_eq] at hq; exact absurd hq (by show ¬ k + 1 ≤ W; omega)
  unfold stepC; rw [hb, hb2]

/-- **Soundness of `runC` for one lane.** Lane `p` follows a column `y` that keeps the pattern, matches the free
readings of the lane, and comes from a start that is white beyond depth `W`. Then the lane never dies, so `runC`
cannot succeed. -/
theorem runC_sound (W φ n c ALL : Nat) (pats : List Nat) (y : Nat → Bool) (p : Nat)
    (hALL : ALL.testBit p = true)
    (hfree : ∀ t, (t + φ) % 4 = 1 → t + 1 ≤ W → (yFree n c ALL pats (freeIdx φ t)).testBit p = y t)
    (hwid : ∀ d, W < d → recon y d 0 = false) :
    ∀ fuel k R Rm alive,
      runC W φ n c ALL pats fuel k R Rm alive = true →
      (∀ t, k ≤ t → t < k + fuel → KeepsC3 φ y t) →
      R.map (fun v => v.testBit p) = AD y k 0 k →
      Rm.map (fun v => v.testBit p) = AD y (k - 1) 0 (k - 1) →
      alive.testBit p = true → False := by
  intro fuel
  induction fuel with
  | zero =>
    intro k R Rm alive hrun _ _ _ halive
    rw [runC_zero, Nat.beq_eq] at hrun
    rw [hrun, Nat.zero_testBit] at halive
    exact absurd halive (by decide)
  | succ fuel ih =>
    intro k R Rm alive hrun hkeep hR hRm halive
    rw [runC_succ] at hrun
    have hkeep' : ∀ t, k + 1 ≤ t → t < k + 1 + fuel → KeepsC3 φ y t :=
      fun t h1 h2 => hkeep t (by omega) (by omega)
    have hRm' : R.map (fun v => v.testBit p) = AD y (k + 1 - 1) 0 (k + 1 - 1) := by
      rw [show k + 1 - 1 = k by omega]; exact hR
    have hk := hkeep k (by omega) (by omega)
    by_cases h1 : (k + φ) % 4 = 1
    · have hb : Nat.beq ((k + φ) % 4) 1 = true := by rw [Nat.beq_eq]; exact h1
      by_cases hW : k + 1 ≤ W
      · -- a free reading
        rw [stepC_free W φ n c ALL pats k R Rm h1 hW] at hrun
        have hl := level y p k R Rm _ hR hRm (hfree k h1 hW)
        refine ih (k + 1) _ R _ hrun hkeep' hl.1 hRm' ?_
        rw [hb]
        exact halive
      · -- a forced reading: the white cell at depth `k + 1` fixes it, and it is the true one
        rw [stepC_forced W φ n c ALL pats k R Rm h1 (by omega)] at hrun
        let Y' : Nat := if y k then 2 ^ p else 0
        have hY' : Y'.testBit p = y k := by
          show (if y k then 2 ^ p else 0).testBit p = y k
          cases y k
          · simp
          · simp
        have hl' := level y p k R Rm Y' hR hRm hY'
        rw [hwid (k + 1) (by omega), scanN_lin, Nat.testBit_xor, hY'] at hl'
        have hT : (scanN 0 R (0 :: Rm)).2.testBit p = y k := by
          have h2 := hl'.2
          revert h2
          cases y k <;> cases (scanN 0 R (0 :: Rm)).2.testBit p <;> simp
        have hl := level y p k R Rm (scanN 0 R (0 :: Rm)).2 hR hRm hT
        rw [scanN_lin R (0 :: Rm) (scanN 0 R (0 :: Rm)).2] at hl
        refine ih (k + 1) _ R _ hrun hkeep' hl.1 hRm' ?_
        rw [hb]
        exact halive
    · -- a fixed reading
      have hb : Nat.beq ((k + φ) % 4) 1 = false := by
        cases hq : Nat.beq ((k + φ) % 4) 1
        · rfl
        · rw [Nat.beq_eq] at hq; exact absurd hq h1
      rw [stepC_fixed W φ n c ALL pats k R Rm h1] at hrun
      have hY : (Bool.rec 0 ALL (Nat.beq ((k + φ) % 4) 3) : Nat).testBit p = y k := by
        by_cases h3 : (k + φ) % 4 = 3
        · have hb3 : Nat.beq ((k + φ) % 4) 3 = true := by rw [Nat.beq_eq]; exact h3
          rw [hb3]
          show ALL.testBit p = y k
          rw [hALL, hk.2.2 h3]
        · have hb3 : Nat.beq ((k + φ) % 4) 3 = false := by
            cases hq : Nat.beq ((k + φ) % 4) 3
            · rfl
            · rw [Nat.beq_eq] at hq; exact absurd hq h3
          rw [hb3]
          show (0 : Nat).testBit p = y k
          rw [Nat.zero_testBit]
          rcases (show (k + φ) % 4 = 0 ∨ (k + φ) % 4 = 2 by omega) with h0 | h2
          · exact (hk.1 h0).symm
          · exact (hk.2.1 h2).symm
      have hl := level y p k R Rm _ hR hRm hY
      refine ih (k + 1) _ R _ hrun hkeep' hl.1 hRm' ?_
      rw [hb]
      by_cases hW : W < k + 1
      · have hb2 : Nat.blt W (k + 1) = true := by rw [Nat.blt_eq]; exact hW
        rw [hb2]
        show (alive &&& (ALL ^^^ (scanN (Bool.rec 0 ALL (Nat.beq ((k + φ) % 4) 3)) R (0 :: Rm)).2)).testBit p = true
        rw [Nat.testBit_and, Nat.testBit_xor, hl.2, hwid (k + 1) hW, hALL, halive]
        rfl
      · have hb2 : Nat.blt W (k + 1) = false := by
          cases hq : Nat.blt W (k + 1)
          · rfl
          · rw [Nat.blt_eq] at hq; exact absurd hq hW
        rw [hb2]
        exact halive

theorem freeIdx_freeTime (φ s : Nat) (hφ : φ < 4) : freeIdx φ (freeTime φ s) = s := by
  unfold freeIdx freeTime; omega

theorem freeTime_freeIdx (φ t : Nat) (hφ : φ < 4) (h : (t + φ) % 4 = 1) : freeTime φ (freeIdx φ t) = t := by
  unfold freeIdx freeTime; omega

theorem freeTime_phase (φ s : Nat) (hφ : φ < 4) : (freeTime φ s + φ) % 4 = 1 := by
  unfold freeTime; omega

theorem freeIdx_lt (W φ t : Nat) (hφ : φ < 4) (h : (t + φ) % 4 = 1) (hW : t + 1 ≤ W) :
    freeIdx φ t < freeCount W φ := by
  unfold freeIdx freeCount; omega

/-- **Soundness of the chunked check.** If every chunk passes from phase `φ`, then every start supported at depths
`≤ W` breaks the pattern of `0001` from phase `φ` at some time `< K`. -/
theorem c3_0001_of_checks (W K φ n : Nat) (hφ : φ < 4) (hn : n ≤ freeCount W φ)
    (hc : ∀ c, c < 2 ^ (freeCount W φ - n) → checkC W K φ n c = true)
    (x : Nat → Bool) (hx : ∀ k, W < k → x k = false) :
    ∃ t, t < K ∧ ¬ KeepsC3 φ (fun t => zrow x t 1) t := by
  refine Classical.byContradiction fun hne => ?_
  have hall : ∀ t, t < K → KeepsC3 φ (fun t => zrow x t 1) t := by
    intro t ht
    exact Classical.byContradiction fun hk => hne ⟨t, ht, hk⟩
  let y : Nat → Bool := fun t => zrow x t 1
  let p := pack (fun s => y (freeTime φ s)) n
  let c := pack (fun s => y (freeTime φ (n + s))) (freeCount W φ - n)
  have hcheck := hc c (pack_lt _ _)
  have hp : p < 2 ^ n := pack_lt _ _
  have hALL : (2 ^ 2 ^ n - 1).testBit p = true := by
    rw [Nat.testBit_two_pow_sub_one]; simpa using hp
  refine runC_sound W φ n c (2 ^ 2 ^ n - 1) ((List.range n).map (pat n)) y p hALL ?_ ?_ K 0 [] []
    (2 ^ 2 ^ n - 1) hcheck (fun t _ ht => hall t (by omega)) rfl rfl hALL
  · intro t ht htW
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
  · intro d hd
    have e := history_eq_recon x d 0
    rw [zrow_zero_of_pos x (by omega), hx d hd] at e
    exact e.symm

/-- The chunks `lo, …, lo + cnt - 1` pass from phase `φ`. -/
def ChunksC (W K φ n lo cnt : Nat) : Prop := ∀ c, lo ≤ c → c < lo + cnt → checkC W K φ n c = true

theorem chunksC_one {W K φ n c : Nat} (h : checkC W K φ n c = true) : ChunksC W K φ n c 1 :=
  fun c' h1 h2 => by rw [show c' = c by omega]; exact h

theorem chunksC_append {W K φ n lo a b : Nat} (h1 : ChunksC W K φ n lo a) (h2 : ChunksC W K φ n (lo + a) b) :
    ChunksC W K φ n lo (a + b) := fun c hc1 hc2 => by
  rcases Nat.lt_or_ge c (lo + a) with h | h
  · exact h1 c hc1 h
  · exact h2 c h (by omega)

/-! ### The checks at depth 88

For each phase, `16` chunks of `2 ^ 18` lanes cover the `2 ^ 22` choices of the free readings; each check runs
`114` levels. -/

theorem chunk0_0 : checkC 88 114 0 18 0 = true := by decide +kernel
theorem chunk0_1 : checkC 88 114 0 18 1 = true := by decide +kernel
theorem chunk0_2 : checkC 88 114 0 18 2 = true := by decide +kernel
theorem chunk0_3 : checkC 88 114 0 18 3 = true := by decide +kernel
theorem chunk0_4 : checkC 88 114 0 18 4 = true := by decide +kernel
theorem chunk0_5 : checkC 88 114 0 18 5 = true := by decide +kernel
theorem chunk0_6 : checkC 88 114 0 18 6 = true := by decide +kernel
theorem chunk0_7 : checkC 88 114 0 18 7 = true := by decide +kernel
theorem chunk0_8 : checkC 88 114 0 18 8 = true := by decide +kernel
theorem chunk0_9 : checkC 88 114 0 18 9 = true := by decide +kernel
theorem chunk0_10 : checkC 88 114 0 18 10 = true := by decide +kernel
theorem chunk0_11 : checkC 88 114 0 18 11 = true := by decide +kernel
theorem chunk0_12 : checkC 88 114 0 18 12 = true := by decide +kernel
theorem chunk0_13 : checkC 88 114 0 18 13 = true := by decide +kernel
theorem chunk0_14 : checkC 88 114 0 18 14 = true := by decide +kernel
theorem chunk0_15 : checkC 88 114 0 18 15 = true := by decide +kernel

theorem chunks0 : ChunksC 88 114 0 18 0 16 := by
  have h := chunksC_one chunk0_0
  have h := chunksC_append h (chunksC_one chunk0_1)
  have h := chunksC_append h (chunksC_one chunk0_2)
  have h := chunksC_append h (chunksC_one chunk0_3)
  have h := chunksC_append h (chunksC_one chunk0_4)
  have h := chunksC_append h (chunksC_one chunk0_5)
  have h := chunksC_append h (chunksC_one chunk0_6)
  have h := chunksC_append h (chunksC_one chunk0_7)
  have h := chunksC_append h (chunksC_one chunk0_8)
  have h := chunksC_append h (chunksC_one chunk0_9)
  have h := chunksC_append h (chunksC_one chunk0_10)
  have h := chunksC_append h (chunksC_one chunk0_11)
  have h := chunksC_append h (chunksC_one chunk0_12)
  have h := chunksC_append h (chunksC_one chunk0_13)
  have h := chunksC_append h (chunksC_one chunk0_14)
  have h := chunksC_append h (chunksC_one chunk0_15)
  exact h

theorem chunk1_0 : checkC 88 114 1 18 0 = true := by decide +kernel
theorem chunk1_1 : checkC 88 114 1 18 1 = true := by decide +kernel
theorem chunk1_2 : checkC 88 114 1 18 2 = true := by decide +kernel
theorem chunk1_3 : checkC 88 114 1 18 3 = true := by decide +kernel
theorem chunk1_4 : checkC 88 114 1 18 4 = true := by decide +kernel
theorem chunk1_5 : checkC 88 114 1 18 5 = true := by decide +kernel
theorem chunk1_6 : checkC 88 114 1 18 6 = true := by decide +kernel
theorem chunk1_7 : checkC 88 114 1 18 7 = true := by decide +kernel
theorem chunk1_8 : checkC 88 114 1 18 8 = true := by decide +kernel
theorem chunk1_9 : checkC 88 114 1 18 9 = true := by decide +kernel
theorem chunk1_10 : checkC 88 114 1 18 10 = true := by decide +kernel
theorem chunk1_11 : checkC 88 114 1 18 11 = true := by decide +kernel
theorem chunk1_12 : checkC 88 114 1 18 12 = true := by decide +kernel
theorem chunk1_13 : checkC 88 114 1 18 13 = true := by decide +kernel
theorem chunk1_14 : checkC 88 114 1 18 14 = true := by decide +kernel
theorem chunk1_15 : checkC 88 114 1 18 15 = true := by decide +kernel

theorem chunks1 : ChunksC 88 114 1 18 0 16 := by
  have h := chunksC_one chunk1_0
  have h := chunksC_append h (chunksC_one chunk1_1)
  have h := chunksC_append h (chunksC_one chunk1_2)
  have h := chunksC_append h (chunksC_one chunk1_3)
  have h := chunksC_append h (chunksC_one chunk1_4)
  have h := chunksC_append h (chunksC_one chunk1_5)
  have h := chunksC_append h (chunksC_one chunk1_6)
  have h := chunksC_append h (chunksC_one chunk1_7)
  have h := chunksC_append h (chunksC_one chunk1_8)
  have h := chunksC_append h (chunksC_one chunk1_9)
  have h := chunksC_append h (chunksC_one chunk1_10)
  have h := chunksC_append h (chunksC_one chunk1_11)
  have h := chunksC_append h (chunksC_one chunk1_12)
  have h := chunksC_append h (chunksC_one chunk1_13)
  have h := chunksC_append h (chunksC_one chunk1_14)
  have h := chunksC_append h (chunksC_one chunk1_15)
  exact h

theorem chunk2_0 : checkC 88 114 2 18 0 = true := by decide +kernel
theorem chunk2_1 : checkC 88 114 2 18 1 = true := by decide +kernel
theorem chunk2_2 : checkC 88 114 2 18 2 = true := by decide +kernel
theorem chunk2_3 : checkC 88 114 2 18 3 = true := by decide +kernel
theorem chunk2_4 : checkC 88 114 2 18 4 = true := by decide +kernel
theorem chunk2_5 : checkC 88 114 2 18 5 = true := by decide +kernel
theorem chunk2_6 : checkC 88 114 2 18 6 = true := by decide +kernel
theorem chunk2_7 : checkC 88 114 2 18 7 = true := by decide +kernel
theorem chunk2_8 : checkC 88 114 2 18 8 = true := by decide +kernel
theorem chunk2_9 : checkC 88 114 2 18 9 = true := by decide +kernel
theorem chunk2_10 : checkC 88 114 2 18 10 = true := by decide +kernel
theorem chunk2_11 : checkC 88 114 2 18 11 = true := by decide +kernel
theorem chunk2_12 : checkC 88 114 2 18 12 = true := by decide +kernel
theorem chunk2_13 : checkC 88 114 2 18 13 = true := by decide +kernel
theorem chunk2_14 : checkC 88 114 2 18 14 = true := by decide +kernel
theorem chunk2_15 : checkC 88 114 2 18 15 = true := by decide +kernel

theorem chunks2 : ChunksC 88 114 2 18 0 16 := by
  have h := chunksC_one chunk2_0
  have h := chunksC_append h (chunksC_one chunk2_1)
  have h := chunksC_append h (chunksC_one chunk2_2)
  have h := chunksC_append h (chunksC_one chunk2_3)
  have h := chunksC_append h (chunksC_one chunk2_4)
  have h := chunksC_append h (chunksC_one chunk2_5)
  have h := chunksC_append h (chunksC_one chunk2_6)
  have h := chunksC_append h (chunksC_one chunk2_7)
  have h := chunksC_append h (chunksC_one chunk2_8)
  have h := chunksC_append h (chunksC_one chunk2_9)
  have h := chunksC_append h (chunksC_one chunk2_10)
  have h := chunksC_append h (chunksC_one chunk2_11)
  have h := chunksC_append h (chunksC_one chunk2_12)
  have h := chunksC_append h (chunksC_one chunk2_13)
  have h := chunksC_append h (chunksC_one chunk2_14)
  have h := chunksC_append h (chunksC_one chunk2_15)
  exact h

theorem chunk3_0 : checkC 88 114 3 18 0 = true := by decide +kernel
theorem chunk3_1 : checkC 88 114 3 18 1 = true := by decide +kernel
theorem chunk3_2 : checkC 88 114 3 18 2 = true := by decide +kernel
theorem chunk3_3 : checkC 88 114 3 18 3 = true := by decide +kernel
theorem chunk3_4 : checkC 88 114 3 18 4 = true := by decide +kernel
theorem chunk3_5 : checkC 88 114 3 18 5 = true := by decide +kernel
theorem chunk3_6 : checkC 88 114 3 18 6 = true := by decide +kernel
theorem chunk3_7 : checkC 88 114 3 18 7 = true := by decide +kernel
theorem chunk3_8 : checkC 88 114 3 18 8 = true := by decide +kernel
theorem chunk3_9 : checkC 88 114 3 18 9 = true := by decide +kernel
theorem chunk3_10 : checkC 88 114 3 18 10 = true := by decide +kernel
theorem chunk3_11 : checkC 88 114 3 18 11 = true := by decide +kernel
theorem chunk3_12 : checkC 88 114 3 18 12 = true := by decide +kernel
theorem chunk3_13 : checkC 88 114 3 18 13 = true := by decide +kernel
theorem chunk3_14 : checkC 88 114 3 18 14 = true := by decide +kernel
theorem chunk3_15 : checkC 88 114 3 18 15 = true := by decide +kernel

theorem chunks3 : ChunksC 88 114 3 18 0 16 := by
  have h := chunksC_one chunk3_0
  have h := chunksC_append h (chunksC_one chunk3_1)
  have h := chunksC_append h (chunksC_one chunk3_2)
  have h := chunksC_append h (chunksC_one chunk3_3)
  have h := chunksC_append h (chunksC_one chunk3_4)
  have h := chunksC_append h (chunksC_one chunk3_5)
  have h := chunksC_append h (chunksC_one chunk3_6)
  have h := chunksC_append h (chunksC_one chunk3_7)
  have h := chunksC_append h (chunksC_one chunk3_8)
  have h := chunksC_append h (chunksC_one chunk3_9)
  have h := chunksC_append h (chunksC_one chunk3_10)
  have h := chunksC_append h (chunksC_one chunk3_11)
  have h := chunksC_append h (chunksC_one chunk3_12)
  have h := chunksC_append h (chunksC_one chunk3_13)
  have h := chunksC_append h (chunksC_one chunk3_14)
  have h := chunksC_append h (chunksC_one chunk3_15)
  exact h

/-- **Every start of depth at most 88 breaks the pattern**, from every phase, within 114 steps. -/
theorem c3_0001_depth (φ : Nat) (hφ : φ < 4) (x : Nat → Bool) (hx : ∀ d, 88 < d → x d = false) :
    ∃ t, t < 114 ∧ ¬ KeepsC3 φ (fun t => zrow x t 1) t := by
  have hcount : freeCount 88 φ = 22 := by
    rcases (show φ = 0 ∨ φ = 1 ∨ φ = 2 ∨ φ = 3 by omega) with rfl | rfl | rfl | rfl <;> rfl
  refine c3_0001_of_checks 88 114 φ 18 hφ (by rw [hcount]; decide) ?_ x hx
  rw [hcount]
  intro c hc
  have hc' : c < 0 + 16 := by
    have : 2 ^ (22 - 18) = 16 := rfl
    omega
  rcases (show φ = 0 ∨ φ = 1 ∨ φ = 2 ∨ φ = 3 by omega) with rfl | rfl | rfl | rfl
  · exact chunks0 c (Nat.zero_le c) hc'
  · exact chunks1 c (Nat.zero_le c) hc'
  · exact chunks2 c (Nat.zero_le c) hc'
  · exact chunks3 c (Nat.zero_le c) hc'

/-! ### Sharpness at depth 20

At depth `20` one chunk of `2 ^ 5` lanes covers every start, and the least number of levels that passes is one more
than the latest first failure over the starts of at most `20` cells: the check is not vacuous, and it decides exactly
the time by which every start has failed. -/

theorem sharp20_0 : checkC 20 28 0 5 0 = true ∧ checkC 20 27 0 5 0 = false := by decide +kernel
theorem sharp20_1 : checkC 20 27 1 5 0 = true ∧ checkC 20 26 1 5 0 = false := by decide +kernel
theorem sharp20_2 : checkC 20 29 2 5 0 = true ∧ checkC 20 28 2 5 0 = false := by decide +kernel
theorem sharp20_3 : checkC 20 28 3 5 0 = true ∧ checkC 20 27 3 5 0 = false := by decide +kernel

/-! ### The kit's statement -/

open Rule30PeriodFourSkeleton (fits colPattern effWord effWord_0001)
open Rule30Ether (wordAt w0001)

/-- The kit's effective boundary for `0001` is the white column. -/
theorem drive_0001 : (fun k => wordAt (effWord w0001) k) = fun _ => false := by
  funext k
  rw [effWord_0001]
  unfold wordAt
  rcases (show k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 by omega) with h | h | h | h <;> rw [h] <;> rfl

/-- The kit's pattern `P_0001` at time `k`: white at the phases `0` and `2`, black at `3`. -/
theorem fits_0001 (k : Nat) (b : Bool) :
    fits (colPattern w0001) (k % 4) b = true ↔
      ((k % 4 = 0 → b = false) ∧ (k % 4 = 2 → b = false) ∧ (k % 4 = 3 → b = true)) := by
  rcases (show k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 by omega) with h | h | h | h <;> rw [h] <;>
    cases b <;> decide

/-- **A bounded case of the kit's `C3 w0001`.** A left half that keeps the kit's pattern for `0001` from time `K` on,
beside the effective boundary, has a black cell at a depth beyond `88` at time `K`. -/
theorem c3_0001_bounded (s : Int → Bool) (K : Nat)
    (hK : ∀ k, K ≤ k → fits (colPattern w0001) (k % 4)
      (Rule30DrivenLeft.L (fun k => wordAt (effWord w0001) k) s k (-1)) = true) :
    ∃ d : Nat, 88 < d ∧ Rule30DrivenLeft.L (fun k => wordAt (effWord w0001) k) s K (-(d : Int)) = true := by
  rw [drive_0001] at hK ⊢
  refine Classical.byContradiction fun hne => ?_
  let x : Nat → Bool := zrow (fun k => s (-(k : Int))) K
  have hx : ∀ d, 88 < d → x d = false := by
    intro d hd
    show zrow _ K d = false
    rw [← L_eq_zrow s K d (by omega)]
    cases h : Rule30DrivenLeft.L (fun _ => false) s K (-(d : Int))
    · rfl
    · exact absurd ⟨d, hd, h⟩ hne
  obtain ⟨t, -, hbad⟩ := c3_0001_depth (K % 4) (Nat.mod_lt _ (by decide)) x hx
  apply hbad
  have hcol : zrow x t 1 = Rule30DrivenLeft.L (fun _ => false) s (K + t) (-1) := by
    have e := L_eq_zrow s (K + t) 1 (Nat.le_refl 1)
    rw [zrow_shift] at e
    exact e.symm
  have hf := (fits_0001 (K + t) _).1 (hK (K + t) (by omega))
  rw [← hcol] at hf
  have hph : (K + t) % 4 = (t + K % 4) % 4 := by omega
  rw [hph] at hf
  exact hf

/-- **Small starts.** No left half supported within depth `M` keeps the kit's pattern for `0001` from a time `K` with
`M + K ≤ 88`; in particular none of at most 88 cells keeps it from time `0`. -/
theorem c3_0001_small (s : Int → Bool) (M K : Nat) (hs : ∀ p : Int, p < -(M : Int) → s p = false)
    (hMK : M + K ≤ 88) :
    ¬ ∀ k, K ≤ k → fits (colPattern w0001) (k % 4)
      (Rule30DrivenLeft.L (fun k => wordAt (effWord w0001) k) s k (-1)) = true := by
  intro hK
  obtain ⟨d, hd, hb⟩ := c3_0001_bounded s K hK
  rw [drive_0001, L_eq_zrow s K d (by omega),
    zrow_fin (W := M) (fun k hk => hs _ (by omega)) K d (by omega)] at hb
  exact absurd hb (by decide)

end Rule30Open
