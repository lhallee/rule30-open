module

public import Ruliology.CellularAutomata.Rule30PeriodTwoSideways
public import Ruliology.CellularAutomata.Rule30EtherThreeReach

/-!
# A lock of period seven beside an alternating center excludes period two

Drive a right half with an alternating center, black at the even steps (the kit's `altCol`). Column `1` at the white
steps, the kit's `u R`, is what the left half has to absorb: the kit's `Psi R` is the one left half that keeps the
center alternating against `R`, and it has infinitely many black cells whenever `u R` is eventually periodic
(`Rule30PeriodTwoSideways.not_finSupp_Psi_of_eventuallyPeriodic`). This module gives a set of windows of the columns
`1..32` that a right half never leaves and inside which column `1` repeats `0101000` at the white steps. A finite
configuration whose center alternates therefore never has its columns `1..32` in the set.

* `lockCls k`, `lockWord`: the `195` windows, as `32`-bit codes in seven classes, and the word of column `1`.
* `lock_ok`: every window of class `k` reads `lockWord k` in column `1`, and two steps later, whatever columns `33`
  holds at the two steps, it is in class `k + 1` (modulo `7`). Checked by the kernel.
* `win_lock_forever`: a window in class `k` at an odd time is in class `k + n` two `n` steps later.
* `u_periodic_of_lock`: so `u R` is eventually periodic, with period `7`.
* `not_finSupp_Psi_of_lock`: so `Psi R` has infinitely many black cells.
* `no_alternating_of_lock`: no finite configuration whose center alternates `1, 0, 1, …` from time `0` has its columns
  `1..32` in the lock at an odd time, whatever its left half.
* `no_alternating_lock_example`: in particular no finite configuration whose cells `1..9` read `1 0 0 1 0 1 1 1 1`,
  with only white cells beyond, keeps its center alternating from time `0`, whatever its left half: its columns enter
  the lock at time `29`.

The natural-language argument is `SevenLock.md`, beside this file.
-/

@[expose] public section

-- Sequential elaboration: the kernel checks would otherwise run in parallel and stack their memory.
set_option Elab.async false

namespace Rule30Open

open Ruliology.CellularAutomata
open Rule30ZeroBoundary Rule30PeriodTwoSideways Rule30PeriodTwoCoupled Rule30Ether Rule30StripCertificates
  Rule30Realization Rule30Jen Rule30EtherThree

namespace SevenLock

/-! ### Windows and the double step -/

/-- The window of `R`: columns `1..32` of the right half `R` driven by the alternating column, at time `t`. -/
def win (R : Nat → Bool) (t : Nat) : List Bool := rowOf (drv altCol R) t 0 32

/-- The double step from an odd time: column `0` is white, then black, and `x1`, `x2` are the two values of column
`33`. -/
def step2 (s : List Bool) (x1 x2 : Bool) : List Bool :=
  lin3 (true :: (lin3 (false :: (s ++ [x1])) ++ [x2]))

/-- `P` holds after the double step from `s`, for all four values of column `33`. -/
def allSucc (P : List Bool → Bool) (s : List Bool) : Bool :=
  P (step2 s false false) && P (step2 s false true) && P (step2 s true false) && P (step2 s true true)

theorem win_length (R : Nat → Bool) (t : Nat) : (win R t).length = 32 := length_seg _ _

theorem win_step2 (R : Nat → Bool) (t : Nat) (ht : t % 2 = 1) :
    ∃ x1 x2, win R (t + 2) = step2 (win R t) x1 x2 := by
  have h1 := rowOf_succ (drv_isR30 altCol R) t 0 32
  have h2 := rowOf_succ (drv_isR30 altCol R) (t + 1) 0 32
  rw [drv_col0] at h1 h2
  have a1 : altCol t = false := by unfold altCol; simp [ht]
  have a2 : altCol (t + 1) = true := by unfold altCol; simp; omega
  rw [a1] at h1
  rw [a2] at h2
  refine ⟨drv altCol R t 33, drv altCol R (t + 1) 33, ?_⟩
  unfold win step2
  rw [show t + 2 = t + 1 + 1 by omega, h2, h1]

theorem allSucc_spec {P : List Bool → Bool} {s : List Bool} (h : allSucc P s = true) (x1 x2 : Bool) :
    P (step2 s x1 x2) = true := by
  unfold allSucc at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  cases x1 <;> cases x2 <;> assumption

/-! ### Codes -/

/-- The window coded by `n`: bit `i` of `n` is column `i + 1`. -/
def decode (n : Nat) : List Bool := seg (fun i => n.testBit i) 32

theorem testBit_encList_zero (x : Bool) (l : List Bool) : (encList (x :: l)).testBit 0 = x := by
  cases x <;> simp [encList, Nat.testBit_zero] <;> omega

theorem testBit_encList_succ (x : Bool) (l : List Bool) (i : Nat) :
    (encList (x :: l)).testBit (i + 1) = (encList l).testBit i := by
  rw [Nat.testBit_succ]
  congr 1
  cases x <;> simp [encList] <;> omega

theorem seg_encList : ∀ w : List Bool, seg (fun i => (encList w).testBit i) w.length = w
  | [] => rfl
  | x :: l => by
    show (encList (x :: l)).testBit 0 :: seg (fun i => (encList (x :: l)).testBit (i + 1)) l.length = x :: l
    rw [testBit_encList_zero]
    simp only [testBit_encList_succ]
    rw [seg_encList l]

theorem decode_encList {w : List Bool} (hw : w.length = 32) : decode (encList w) = w := by
  have := seg_encList w
  rw [hw] at this
  exact this

/-! ### The lock -/

/-- Column `1` of the windows of class `k`, at the white steps. -/
def lockWord (k : Nat) : Bool := [false, true, false, true, false, false, false].getD k false

/-- The windows of class `k` of the lock, as codes. -/
def lockCls : Nat → List Nat
  | 0 => [
    46898496, 181116224, 315333952, 583769408, 852204864, 1120640320, 1389075776, 1791728960,
    1925946688, 2060164416, 2194382144, 2328599872, 2462817600, 2731253056, 2999688512, 3133906240,
    3268123968, 3402341696, 3536559424, 3939212608, 4073430336, 4207648064]
  | 1 => [
    59587889, 193805617, 328023345, 462241073, 596458801, 730676529, 999111985, 1133329713,
    1267547441, 1804418353, 2207071537, 2341289265, 2475506993, 2609724721, 2743942449, 2878160177,
    3146595633, 3280813361, 3415031089, 3683466545, 3817684273, 3951902001]
  | 2 => [
    122973256, 223636552, 257190984, 391408712, 760507464, 1062497352, 1196715080, 1297378376,
    1465150536, 1834249288, 1867803720, 2102684744, 2270456904, 2371120200, 2404674632, 2538892360,
    2907991112, 3209981000, 3344198728, 3478416456, 3612634184, 3713297480, 3981732936, 4250168392]
  | 3 => [
    223525383, 357743111, 458406407, 525515271, 793950727, 894614023, 995277319, 1028831751,
    1431484935, 1532148231, 1666365959, 1834138119, 1934801415, 2102573575, 2136128007, 2371009031,
    2505226759, 2605890055, 2672998919, 2941434375, 3008543239, 3042097671, 3142760967, 3176315399,
    3276978695, 3444750855, 3679631879, 3746740743, 3813849607, 3981621767, 4082285063, 4115839495,
    4216502791, 4250057223]
  | 4 => [
    54712734, 222484894, 356702622, 524474782, 625138078, 792910238, 860019102, 893573534,
    1027791262, 1430444446, 1665325470, 1833097630, 1866652062, 1933760926, 2101533086, 2135087518,
    2202196382, 2369968542, 2504186270, 2671958430, 2772621726, 2940393886, 3007502750, 3041057182,
    3175274910, 3275938206, 3443710366, 3577928094, 3745700254, 3812809118, 3846363550, 3980581278,
    4014135710, 4081244574, 4114799006, 4249016734, 4282571166]
  | 5 => [
    54260276, 87814708, 222032436, 356250164, 624685620, 859566644, 893121076, 1027338804,
    1161556532, 1429991988, 1664873012, 1832645172, 1933308468, 2101080628, 2201743924, 2235298356,
    2369516084, 2503733812, 2772169268, 3007050292, 3040604724, 3174822452, 3275485748, 3309040180,
    3443257908, 3577475636, 3812356660, 3845911092, 3980128820, 4080792116, 4114346548, 4248564276]
  | 6 => [
    75243858, 209461586, 343679314, 612114770, 880550226, 1014767954, 1148985682, 1417421138,
    1820074322, 1954292050, 2088509778, 2222727506, 2356945234, 2491162962, 2759598418, 3028033874,
    3162251602, 3296469330, 3430687058, 3564904786, 3833340242, 3967557970, 4101775698, 4235993426]
  | _ => []

/-- Membership of a window in class `k`. -/
def inCls (k : Nat) (w : List Bool) : Bool := (lockCls k).contains (encList w)

/-- **The check.** Every window of class `k` reads `lockWord k` in column `1`, and every double step from it, whatever
column `33` holds, lands in class `k + 1` modulo `7`. -/
def lockCheck : Bool :=
  (List.range 7).all fun k => (lockCls k).all fun n =>
    ((decode n).headD false == lockWord k) && allSucc (inCls ((k + 1) % 7)) (decode n)

theorem lock_ok : lockCheck = true := by decide +kernel

theorem lock_spec {k : Nat} (hk : k < 7) {n : Nat} (hn : n ∈ lockCls k) :
    (decode n).headD false = lockWord k ∧ allSucc (inCls ((k + 1) % 7)) (decode n) = true := by
  have h := lock_ok
  unfold lockCheck at h
  have h1 := List.all_eq_true.1 h k (List.mem_range.2 hk)
  have h2 := List.all_eq_true.1 h1 n hn
  simp only [Bool.and_eq_true, beq_iff_eq] at h2
  exact h2

theorem lockCls_empty {k : Nat} (hk : 7 ≤ k) : lockCls k = [] := by
  match k, hk with
  | k + 7, _ => rfl

theorem inCls_spec {k : Nat} {w : List Bool} (hw : w.length = 32) (h : inCls k w = true) :
    k < 7 ∧ encList w ∈ lockCls k ∧ decode (encList w) = w := by
  unfold inCls at h
  have hm : encList w ∈ lockCls k := by simpa using h
  refine ⟨?_, hm, decode_encList hw⟩
  rcases Nat.lt_or_ge k 7 with hk | hk
  · exact hk
  · rw [lockCls_empty hk] at hm
    simp at hm

/-! ### The orbit of a window in the lock -/

theorem win_lock_forever (R : Nat → Bool) {t0 k : Nat} (h0 : t0 % 2 = 1) (hw : inCls k (win R t0) = true) :
    ∀ n, inCls ((k + n) % 7) (win R (t0 + 2 * n)) = true
  | 0 => by
    have := (inCls_spec (win_length R t0) hw).1
    rw [Nat.add_zero, Nat.mod_eq_of_lt this]
    exact hw
  | n + 1 => by
    have ih := win_lock_forever R h0 hw n
    obtain ⟨hk, hm, hd⟩ := inCls_spec (win_length R _) ih
    obtain ⟨x1, x2, e⟩ := win_step2 R (t0 + 2 * n) (by omega)
    have hs := (lock_spec hk hm).2
    rw [hd] at hs
    have := allSucc_spec hs x1 x2
    rw [← e, show t0 + 2 * n + 2 = t0 + 2 * (n + 1) by omega, Nat.mod_add_mod,
      show k + n + 1 = k + (n + 1) by omega] at this
    exact this

theorem win_head (R : Nat → Bool) (t : Nat) : (win R t).headD false = drv altCol R t 1 := rfl

theorem u_of_lock (R : Nat → Bool) {s0 k : Nat} (hw : inCls k (win R (2 * s0 + 1)) = true) (n : Nat) :
    u R (s0 + n) = lockWord ((k + n) % 7) := by
  have h := win_lock_forever R (t0 := 2 * s0 + 1) (by omega) hw n
  obtain ⟨hk, hm, hd⟩ := inCls_spec (win_length R _) h
  have := (lock_spec hk hm).1
  rw [hd, win_head] at this
  unfold u
  rw [show 2 * (s0 + n) + 1 = 2 * s0 + 1 + 2 * n by omega]
  exact this

/-- **The lock makes column `1` periodic.** -/
theorem u_periodic_of_lock (R : Nat → Bool) {s0 k : Nat} (hw : inCls k (win R (2 * s0 + 1)) = true) :
    EventuallyPeriodic (u R) := by
  refine ⟨s0, 7, by omega, fun s hs => ?_⟩
  obtain ⟨n, rfl⟩ : ∃ n, s = s0 + n := ⟨s - s0, by omega⟩
  rw [show s0 + n + 7 = s0 + (n + 7) by omega, u_of_lock R hw, u_of_lock R hw,
    show k + (n + 7) = k + n + 7 by omega, Nat.add_mod_right]

/-- **The lock excludes period two against `R`**: the one left half that keeps the center alternating against `R`
has infinitely many black cells. -/
theorem not_finSupp_Psi_of_lock (R : Nat → Bool) {s0 k : Nat} (hw : inCls k (win R (2 * s0 + 1)) = true) :
    ¬ FinSupp (Psi R) :=
  not_finSupp_Psi_of_eventuallyPeriodic R (u_periodic_of_lock R hw)

/-! ### Finite configurations -/

/-- **No finite configuration with an alternating center enters the lock.** If the center of a finite
configuration reads `1, 0, 1, 0, …` from time `0`, then at no odd time are its columns `1..32` a window of the lock. -/
theorem no_alternating_of_lock (x : Int → Bool) (hfin : FinConfig x) (hx : ∀ t, evol x t 0 = altCol t)
    (s0 k : Nat) : inCls k (seg (fun i => evol x (2 * s0 + 1) ((i : Int) + 1)) 32) = false := by
  cases hin : inCls k (seg (fun i => evol x (2 * s0 + 1) ((i : Int) + 1)) 32)
  · rfl
  exfalso
  have hw : inCls k (win (fun p => x (p : Int)) (2 * s0 + 1)) = true := by
    have e : win (fun p => x (p : Int)) (2 * s0 + 1) = seg (fun i => evol x (2 * s0 + 1) ((i : Int) + 1)) 32 := by
      unfold win rowOf
      apply seg_congr
      intro i _
      rw [right_is_drv x hx]
      congr 1
      push_cast
      omega
    rw [e]
    exact hin
  obtain ⟨W, hW⟩ := hfin
  apply not_finSupp_Psi_of_lock _ hw
  refine ⟨W, fun j hj => ?_⟩
  rw [← Psi_unique (left_inX x hx) (left_coupled x hx), zrow_zero_of_pos _ (by omega)]
  exact hW _ (by omega)

/-! ### An example -/

/-- The right half whose cells `1..9` read `1 0 0 1 0 1 1 1 1` (the number `489`, bit `i` the cell `i + 1`). -/
def exampleHalf : Nat → Bool := fun p => (489 : Nat).testBit (p - 1)

/-- The window of the example at time `29`, computed from its row as a number. -/
def exampleWindow : List Bool := seg (fun i => (rowN altCol 489 29).testBit i) 32

theorem exampleWindow_inCls : inCls 4 exampleWindow = true := by decide +kernel

theorem example_enters : inCls 4 (win exampleHalf 29) = true := by
  have e : win exampleHalf 29 = exampleWindow := by
    unfold win rowOf exampleWindow
    apply seg_congr
    intro i _
    rw [rowN_eq_drv, Nat.zero_add]
    rfl
  rw [e]
  exact exampleWindow_inCls

/-- **An unconditional exclusion.** No finite configuration whose center alternates `1, 0, 1, …` from time `0` has
the cells `1, 2, …` reading `1 0 0 1 0 1 1 1 1` and then white at time `0`, whatever its left half. -/
theorem no_alternating_lock_example (x : Int → Bool) (hfin : FinConfig x) (hx : ∀ t, evol x t 0 = altCol t) :
    ¬ ∀ p : Nat, 1 ≤ p → x (p : Int) = exampleHalf p := by
  intro hR
  obtain ⟨W, hW⟩ := hfin
  have hw : inCls 4 (win (fun p => x (p : Int)) (2 * 14 + 1)) = true := by
    have e : win (fun p => x (p : Int)) 29 = win exampleHalf 29 := by
      unfold win rowOf
      apply seg_congr
      intro i _
      exact drv_congr (fun p hp => hR p hp) 29 (0 + i + 1)
    rw [show 2 * 14 + 1 = 29 by rfl, e]
    exact example_enters
  apply not_finSupp_Psi_of_lock _ hw
  refine ⟨W, fun j hj => ?_⟩
  rw [← Psi_unique (left_inX x hx) (left_coupled x hx), zrow_zero_of_pos _ (by omega)]
  exact hW _ (by omega)

end SevenLock

end Rule30Open
