module

public import Rule30Open.Columns.BitGame
public import Rule30Open.Columns.LockWord
public import Rule30Open.Columns.EmptyRight

/-!
# The forced basin of the period-four family: windows from which entry does not depend on the cells beyond

Drive a right half with the center repeating `0001`, `0011` or `0111` from phase `φ`. Watch its first `K` cells, the
window, and leave cell `K + 1` free at every step: the game of `BitGame` with the center as the repeating column. A
window certifies entry into the kit's ether-and-wall family (`Rule30Ether.InFamily`) when, for an alignment `(j0, s)`
of the word and a depth `k` with column `j0 + k` a `B3` column and `k + 13 ≤ K`, its first `k` cells are the ether and
the next 13 one of the kit's wall states (`target`). The forced basin is the least set of nodes that holds these and
every node whose two moves lie in it; `basinFrom` computes its layers in the kernel on bit tables, with no stored set.

* **The all-successor test** (`allPre`, `allPre_sound`). The complement of `BitGame.pre` of the complement: a node
  set there has both its moves in the set. Generic in the block and the width.
* **Layers** (`basinFrom`, `basinFrom_sound`). After `n` rounds from a set whose nodes enter a target within `m`
  steps of every play, every node of the result enters it within `m + n` steps (`Enters`, `run`).
* **The family** (`target`, `target_sound`, `inFamily_of_window`, `enters_of_basin`). Every driven right half, finite
  or infinite, whose window at time 0 lies in the basin after `R` rounds is in the family by step `R`.
* **Counting** (`popc`, `popcR`, `count_halves`). For `n ≥ K`, the right halves of `n` cells whose window lies in the
  basin number `c · 2 ^ (n - K)`, `c` the basin's size at that phase.
* **Exclusion** (`excludes_of_basin`): no finite configuration whose cells `1, …, K` at time 0 form a window of the
  basin has a center that repeats the word from time 0, whatever its left half (`EmptyRight.no_finite_of_family`).
* `covers_of_counts` bundles the four for one word and width (`Covers`); `forcedBasin_0011_14`, `forcedBasin_0111_14`,
  `forcedBasin_0001_16`, `forcedBasin_0011_16` and `forcedBasin_0111_16` are the instances here. `ForcedBasin18` has
  width 18, where the kernel's rounds are cut at stored sets (`spread`, `basinFrom_add`) to bound each check's memory.

The natural-language argument is `ForcedBasin.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

open Ruliology.CellularAutomata
open Rule30Ether Rule30Realization Rule30PeriodTwoSideways
open Rule30StripCertificates (seg)

namespace ForcedBasin

/-! ### The all-successor test -/

/-- The nodes whose moves, for both free cells, all lie in `Y`. -/
def allPre (b : List Bool) (K Y : Nat) : Nat :=
  Nat.xor (BitGame.full b.length K) (BitGame.pre b K (Nat.xor (BitGame.full b.length K) Y))

/-- **The all-successor test is sound**: each move of a node of `allPre b K Y` lies in `Y`. -/
theorem allPre_sound (b : List Bool) (K : Nat) (hK : 1 ≤ K) (Y φ r : Nat) (u : Bool) (hφ : φ < b.length)
    (hr : r < 2 ^ K) (h : (allPre b K Y).testBit (φ * 2 ^ (K + 2) + r) = true) :
    Y.testBit ((φ + 1) % b.length * 2 ^ (K + 2) + GameMask.move K (BitGame.col b φ) u r) = true := by
  have hKB : 2 ^ K ≤ 2 ^ (K + 2) := Nat.pow_le_pow_right (by decide) (by omega)
  have hP : 0 < b.length := by omega
  have hy := BitGame.move_lt K (BitGame.col b φ) u r
  have hnode : (φ + 1) % b.length * 2 ^ (K + 2) + GameMask.move K (BitGame.col b φ) u r <
      b.length * 2 ^ (K + 2) := BitGame.blk_lt (Nat.mod_lt _ hP) (by omega)
  have hsrc : φ * 2 ^ (K + 2) + r < b.length * 2 ^ (K + 2) := BitGame.blk_lt hφ (by omega)
  cases hY : Y.testBit ((φ + 1) % b.length * 2 ^ (K + 2) + GameMask.move K (BitGame.col b φ) u r)
  · exfalso
    have hc : (BitGame.full b.length K ^^^ Y).testBit
        ((φ + 1) % b.length * 2 ^ (K + 2) + GameMask.move K (BitGame.col b φ) u r) = true := by
      rw [Nat.testBit_xor, BitGame.full_testBit, hY, decide_eq_true hnode]; rfl
    have hp := BitGame.pre_sound b K hK _ φ r u hφ hr hc
    have h' : (BitGame.full b.length K ^^^ BitGame.pre b K (BitGame.full b.length K ^^^ Y)).testBit
        (φ * 2 ^ (K + 2) + r) = true := h
    rw [Nat.testBit_xor, BitGame.full_testBit, hp, decide_eq_true hsrc] at h'
    exact absurd h' (by decide)
  · rfl

/-! ### Layers -/

/-- The real nodes of `P` phases: in each block of `2 ^ (K + 2)` bits, the first `2 ^ K`. -/
def realMask (P K : Nat) : Nat := BitGame.rep (Nat.pow 2 (K + 2)) (Nat.sub (Nat.pow 2 (Nat.pow 2 K)) 1) P

/-- `n` rounds of the forced basin of `T`, from `S`: each round keeps `T` and adds the real nodes whose moves all lie
in the last set. -/
def basinFrom (b : List Bool) (K T S : Nat) : Nat → Nat
  | 0 => S
  | n + 1 => Nat.lor T (Nat.land (allPre b K (basinFrom b K T S n)) (realMask b.length K))

theorem basinFrom_add (b : List Bool) (K T S a : Nat) :
    ∀ c, basinFrom b K T S (a + c) = basinFrom b K T (basinFrom b K T S a) c
  | 0 => rfl
  | c + 1 => by
    show Nat.lor T (Nat.land (allPre b K (basinFrom b K T S (a + c))) (realMask b.length K)) =
      Nat.lor T (Nat.land (allPre b K (basinFrom b K T (basinFrom b K T S a) c)) (realMask b.length K))
    rw [basinFrom_add b K T S a c]

/-- The window after `t` steps of a play from window `r` at phase `φ`, with free cells `u`. -/
def run (b : List Bool) (K φ : Nat) (u : Nat → Bool) (r : Nat) : Nat → Nat
  | 0 => r
  | t + 1 => GameMask.move K (BitGame.col b (φ + t)) (u t) (run b K φ u r t)

theorem run_shift (b : List Bool) (K φ : Nat) (u : Nat → Bool) (r : Nat) : ∀ t,
    run b K φ u r (t + 1) = run b K (φ + 1) (fun i => u (i + 1)) (GameMask.move K (BitGame.col b φ) (u 0) r) t
  | 0 => rfl
  | t + 1 => by
    show GameMask.move K (BitGame.col b (φ + (t + 1))) (u (t + 1)) (run b K φ u r (t + 1)) =
      GameMask.move K (BitGame.col b (φ + 1 + t)) (u (t + 1)) (run b K (φ + 1) (fun i => u (i + 1))
        (GameMask.move K (BitGame.col b φ) (u 0) r) t)
    rw [run_shift b K φ u r t, show φ + (t + 1) = φ + 1 + t by omega]

theorem run_mod (b : List Bool) (K : Nat) {φ φ' : Nat} (h : φ % b.length = φ' % b.length) (u : Nat → Bool)
    (r : Nat) : ∀ t, run b K φ u r t = run b K φ' u r t
  | 0 => rfl
  | t + 1 => by
    show GameMask.move K (BitGame.col b (φ + t)) (u t) (run b K φ u r t) =
      GameMask.move K (BitGame.col b (φ' + t)) (u t) (run b K φ' u r t)
    have hc : BitGame.col b (φ + t) = BitGame.col b (φ' + t) := by
      unfold BitGame.col; rw [Nat.add_mod, h, ← Nat.add_mod]
    rw [run_mod b K h u r t, hc]

/-- Every play from window `r` at phase `φ` is in `T` within `m` steps. -/
def Enters (b : List Bool) (K T m φ r : Nat) : Prop :=
  ∀ u : Nat → Bool, ∃ t, t ≤ m ∧ T.testBit ((φ + t) % b.length * 2 ^ (K + 2) + run b K φ u r t) = true

/-- **The layers are sound.** If every real node of `S` enters `T` within `m` steps, every real node after `n` rounds
enters it within `m + n` steps. -/
theorem basinFrom_sound (b : List Bool) (K : Nat) (hK : 1 ≤ K) (T S m : Nat)
    (hS : ∀ φ r, φ < b.length → r < 2 ^ K → S.testBit (φ * 2 ^ (K + 2) + r) = true → Enters b K T m φ r) :
    ∀ n φ r, φ < b.length → r < 2 ^ K → (basinFrom b K T S n).testBit (φ * 2 ^ (K + 2) + r) = true →
      Enters b K T (m + n) φ r
  | 0, φ, r, hφ, hr, h => hS φ r hφ hr h
  | n + 1, φ, r, hφ, hr, h => by
    intro u
    have hP : 0 < b.length := by omega
    have h' : (T ||| (allPre b K (basinFrom b K T S n) &&& realMask b.length K)).testBit
        (φ * 2 ^ (K + 2) + r) = true := h
    rw [Nat.testBit_or, Nat.testBit_and, Bool.or_eq_true, Bool.and_eq_true] at h'
    rcases h' with hT | ⟨hA, _⟩
    · refine ⟨0, by omega, ?_⟩
      rw [Nat.add_zero, Nat.mod_eq_of_lt hφ]
      exact hT
    · have hnext := allPre_sound b K hK _ φ r (u 0) hφ hr hA
      obtain ⟨t, ht, hTt⟩ := basinFrom_sound b K hK T S m hS n ((φ + 1) % b.length) _ (Nat.mod_lt _ hP)
        (BitGame.move_lt _ _ _ _) hnext (fun i => u (i + 1))
      refine ⟨t + 1, by omega, ?_⟩
      rw [run_shift, run_mod b K (Nat.mod_mod (φ + 1) b.length).symm (fun i => u (i + 1)) _ t,
        show φ + (t + 1) = φ + 1 + t by omega]
      rw [Nat.mod_add_mod] at hTt
      exact hTt

/-! ### The family as a target -/

/-- The depths `k ≤ K - 13` at which column `j0 + k` is a `B3` column. -/
def depths (j0 K : Nat) : List Nat :=
  (List.range (K + 1)).filter fun k => Nat.beq ((j0 + k) % 7) 2 && Nat.ble (k + 13) K

/-- The family windows of the wall entries at ether phase `ψ`, cut to `k + 13` cells: bit `code j0 k e` for each. -/
def wallCodes (j0 k ψ : Nat) : List (Nat × List Bool) → Nat
  | [] => 0
  | e :: es => Nat.lor (cond (Nat.beq e.1 ψ) (Nat.pow 2 (LockWord.code j0 k e)) 0) (wallCodes j0 k ψ es)

theorem wallCodes_sound (j0 k ψ g : Nat) : ∀ es : List (Nat × List Bool), (wallCodes j0 k ψ es).testBit g = true →
    ∃ e ∈ es, e.1 = ψ ∧ g = LockWord.code j0 k e
  | [], h => by simp [wallCodes] at h
  | e :: es, h => by
    have h' : (cond (Nat.beq e.1 ψ) (2 ^ LockWord.code j0 k e) 0 ||| wallCodes j0 k ψ es).testBit g = true := h
    rw [Nat.testBit_or, Bool.or_eq_true] at h'
    rcases h' with h1 | h1
    · cases hb : Nat.beq e.1 ψ
      · rw [hb] at h1; simp at h1
      · rw [hb, Bool.cond_true, Nat.testBit_two_pow] at h1
        exact ⟨e, List.mem_cons_self, Nat.eq_of_beq_eq_true hb, (of_decide_eq_true h1).symm⟩
    · obtain ⟨e', he', h2⟩ := wallCodes_sound j0 k ψ g es h1
      exact ⟨e', List.mem_cons_of_mem e he', h2⟩

/-- The windows of `K` cells whose first `k + 13` cells are a family window at depth `k`. -/
def depthBlock (K j0 ψ : Nat) : List Nat → Nat
  | [] => 0
  | k :: ks => Nat.lor (BitGame.rep (Nat.pow 2 (k + 13))
      (Nat.land (wallCodes j0 k ψ wallStates) (Nat.sub (Nat.pow 2 (Nat.pow 2 (k + 13))) 1)) (Nat.pow 2 (K - (k + 13))))
      (depthBlock K j0 ψ ks)

/-- The family windows of `K` cells at drive phase `p`, over the alignments `A`. -/
def alignBlock (K p : Nat) : List (Nat × Nat) → Nat
  | [] => 0
  | a :: as => Nat.lor (depthBlock K a.1 ((p + a.2) % 4) (depths a.1 K)) (alignBlock K p as)

/-- Tables of one block each, `f 0, …, f (n - 1)`, cut to `2 ^ (K + 2)` bits and laid side by side. -/
def stack (K : Nat) (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => Nat.lor (stack K f n)
      (Nat.shiftLeft (Nat.land (f n) (Nat.sub (Nat.pow 2 (Nat.pow 2 (K + 2))) 1)) (Nat.mul n (Nat.pow 2 (K + 2))))

theorem stack_sound (K : Nat) (f : Nat → Nat) (p r : Nat) (hr : r < 2 ^ (K + 2)) :
    ∀ n, (stack K f n).testBit (p * 2 ^ (K + 2) + r) = true → (f p).testBit r = true
  | 0, h => by simp [stack] at h
  | n + 1, h => by
    have h' : (stack K f n ||| ((f n &&& (2 ^ 2 ^ (K + 2) - 1)) <<< (n * 2 ^ (K + 2)))).testBit
        (p * 2 ^ (K + 2) + r) = true := h
    rw [Nat.testBit_or, Bool.or_eq_true] at h'
    rcases h' with h1 | h1
    · exact stack_sound K f p r hr n h1
    · rw [Nat.testBit_shiftLeft, Bool.and_eq_true, Nat.testBit_and, Bool.and_eq_true,
        Nat.testBit_two_pow_sub_one] at h1
      obtain ⟨hge, hf, hlt⟩ := h1
      have hB := Nat.two_pow_pos (K + 2)
      have hge' := of_decide_eq_true hge
      have hlt' := of_decide_eq_true hlt
      have hpn : p = n := by
        rcases Nat.lt_trichotomy p n with hpn | hpn | hpn
        · have : (p + 1) * 2 ^ (K + 2) ≤ n * 2 ^ (K + 2) := Nat.mul_le_mul_right _ hpn
          rw [Nat.succ_mul] at this; omega
        · exact hpn
        · have : (n + 1) * 2 ^ (K + 2) ≤ p * 2 ^ (K + 2) := Nat.mul_le_mul_right _ hpn
          rw [Nat.succ_mul] at this; omega
      subst hpn
      rwa [show p * 2 ^ (K + 2) + r - p * 2 ^ (K + 2) = r by omega] at hf

/-- **The target**: at each of the four drive phases, the windows that certify entry into the family. -/
def target (A : List (Nat × Nat)) (K : Nat) : Nat := stack K (fun p => alignBlock K p A) 4

theorem target_sound (A : List (Nat × Nat)) (K p r : Nat) (hr : r < 2 ^ (K + 2))
    (h : (target A K).testBit (p * 2 ^ (K + 2) + r) = true) :
    ∃ a ∈ A, ∃ k, ∃ e ∈ wallStates, (a.1 + k) % 7 = 2 ∧ k + 13 ≤ K ∧ e.1 = (p + a.2) % 4 ∧
      r % 2 ^ (k + 13) = LockWord.code a.1 k e := by
  have hA := stack_sound K _ p r hr 4 h
  clear h
  induction A with
  | nil => simp [alignBlock] at hA
  | cons a as ih =>
    have hA' : (depthBlock K a.1 ((p + a.2) % 4) (depths a.1 K) ||| alignBlock K p as).testBit r = true := hA
    rw [Nat.testBit_or, Bool.or_eq_true] at hA'
    rcases hA' with h1 | h1
    · suffices hd : ∀ ks : List Nat, (∀ k ∈ ks, (a.1 + k) % 7 = 2 ∧ k + 13 ≤ K) →
          (depthBlock K a.1 ((p + a.2) % 4) ks).testBit r = true →
          ∃ k, ∃ e ∈ wallStates, (a.1 + k) % 7 = 2 ∧ k + 13 ≤ K ∧ e.1 = (p + a.2) % 4 ∧
            r % 2 ^ (k + 13) = LockWord.code a.1 k e by
        obtain ⟨k, e, he, h2⟩ := hd (depths a.1 K) (fun k hk => by
          unfold depths at hk
          rw [List.mem_filter, Bool.and_eq_true] at hk
          exact ⟨Nat.eq_of_beq_eq_true hk.2.1, Nat.le_of_ble_eq_true hk.2.2⟩) h1
        exact ⟨a, List.mem_cons_self, k, e, he, h2⟩
      intro ks
      induction ks with
      | nil => intro _ h; simp [depthBlock] at h
      | cons k ks ihk =>
        intro hks h
        have h' : (BitGame.rep (2 ^ (k + 13)) (wallCodes a.1 k ((p + a.2) % 4) wallStates &&&
            (2 ^ 2 ^ (k + 13) - 1)) (2 ^ (K - (k + 13))) ||| depthBlock K a.1 ((p + a.2) % 4) ks).testBit r =
            true := h
        rw [Nat.testBit_or, Bool.or_eq_true] at h'
        rcases h' with h2 | h2
        · obtain ⟨hk7, hkK⟩ := hks k List.mem_cons_self
          have hX : (wallCodes a.1 k ((p + a.2) % 4) wallStates &&& (2 ^ 2 ^ (k + 13) - 1)) < 2 ^ 2 ^ (k + 13) :=
            Nat.and_lt_two_pow _ (by have := Nat.two_pow_pos (2 ^ (k + 13)); omega)
          rw [BitGame.rep_testBit _ _ hX, Bool.and_eq_true, Nat.testBit_and, Bool.and_eq_true] at h2
          obtain ⟨_, hw, _⟩ := h2
          obtain ⟨e, he, hψ, hcode⟩ := wallCodes_sound a.1 k ((p + a.2) % 4) _ wallStates hw
          exact ⟨k, e, he, hk7, hkK, hψ, hcode⟩
        · exact ihk (fun k' hk' => hks k' (List.mem_cons_of_mem k hk')) h2
    · obtain ⟨a', ha', rest⟩ := ih h1
      exact ⟨a', List.mem_cons_of_mem a ha', rest⟩

/-! ### Windows of the driven half -/

/-- Cells `1, …, n` of `F` at time `t`, cell `i + 1` at bit `i`. -/
def win (F : Nat → Nat → Bool) (t : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => Nat.lor (win F t n) (cond (F t (n + 1)) (Nat.pow 2 n) 0)

theorem win_testBit (F : Nat → Nat → Bool) (t : Nat) :
    ∀ n i, (win F t n).testBit i = (decide (i < n) && F t (i + 1))
  | 0, i => by simp [win]
  | n + 1, i => by
    show (win F t n ||| cond (F t (n + 1)) (2 ^ n) 0).testBit i = _
    rw [Nat.testBit_or, win_testBit F t n i]
    have hb : (cond (F t (n + 1)) (2 ^ n) 0).testBit i = (decide (i = n) && F t (n + 1)) := by
      cases F t (n + 1)
      · simp
      · rw [Bool.cond_true, Nat.testBit_two_pow]
        by_cases h : i = n
        · simp [h]
        · simp [h, Ne.symm h]
    rw [hb]
    by_cases h1 : i < n
    · simp [h1, show i ≠ n by omega, show i < n + 1 by omega]
    · by_cases h2 : i = n
      · subst h2; simp
      · simp [h1, h2, show ¬ i < n + 1 by omega]

theorem win_lt (F : Nat → Nat → Bool) (t n : Nat) : win F t n < 2 ^ n :=
  Nat.lt_pow_two_of_testBit _ fun i hi => by rw [win_testBit]; simp [show ¬ i < n by omega]

/-- **One step of the window is a move**, with the column and the cell beyond as the game's. -/
theorem win_succ {F : Nat → Nat → Bool} (hF : IsR30 F) (t K : Nat) :
    win F (t + 1) K = GameMask.move K (F t 0) (F t (K + 1)) (win F t K) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [win_testBit]
  by_cases hi : i < K
  · rw [BitGame.move_testBit K _ _ _ (win_lt F t K) i hi, decide_eq_true hi, Bool.true_and, hF t i]
    unfold BitGame.nextCell Rule30Jen.rule
    have e1 : (if i = 0 then F t 0 else (win F t K).testBit (i - 1)) = F t i := by
      by_cases h0 : i = 0
      · subst h0; rfl
      · rw [ite_eq_right h0, win_testBit, decide_eq_true (by omega), Bool.true_and, show i - 1 + 1 = i by omega]
    have e2 : (if i + 1 = K then F t (K + 1) else (win F t K).testBit (i + 1)) = F t (i + 2) := by
      by_cases h1 : i + 1 = K
      · rw [ite_eq_left h1, show K + 1 = i + 2 by omega]
      · rw [ite_eq_right h1, win_testBit, decide_eq_true (by omega), Bool.true_and]
    rw [e1, e2, win_testBit, decide_eq_true hi, Bool.true_and]
  · rw [decide_eq_false hi, Bool.false_and]
    exact (Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (BitGame.move_lt _ _ _ _)
      (Nat.pow_le_pow_right (by decide) (by omega)))).symm

/-- The window of a right half at time 0 is its first cells. -/
theorem win_drv_zero (c x : Nat → Bool) (K : Nat) : win (drv c x) 0 K = win (fun _ p => x p) 0 K := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [win_testBit, win_testBit, drv_init c x (i + 1) (by omega)]

/-- The window of the half `r` of `n ≥ K` cells is `r mod 2 ^ K`. -/
theorem win_half (r K : Nat) : win (fun _ p => r.testBit (p - 1)) 0 K = r % 2 ^ K := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [win_testBit, Nat.testBit_mod_two_pow, show i + 1 - 1 = i by omega]

/-- **A family window in the right half is entry.** -/
theorem inFamily_of_window {F : Nat → Nat → Bool} {t j0 k s : Nat} {e : Nat × List Bool} (he : e ∈ wallStates)
    (hk : (j0 + k) % 7 = 2) (hph : e.1 = (t + s) % 4)
    (hbits : ∀ i, i < k + 13 → F t (i + 1) = (LockWord.code j0 k e).testBit i) : InFamily F j0 s t := by
  refine ⟨k, hk, fun q hq1 hqk => ?_, ?_⟩
  · obtain ⟨i, rfl⟩ : ∃ i, q = i + 1 := ⟨q - 1, by omega⟩
    rw [hbits i (by omega), LockWord.code_low j0 k e i (by omega)]
    exact ether_congr (by omega) (by rw [hph, Nat.mod_mod])
  · have hrow : rowOf F t k 13 = e.2 := by
      unfold rowOf
      conv => rhs; rw [← LockWord.seg_getD e.2 13 (LockWord.wallStates_length e he)]
      refine Rule30Ether.seg_congr 13 _ _ fun i hi => ?_
      rw [show k + i + 1 = (k + i) + 1 by omega, hbits (k + i) (by omega), LockWord.code_high]
    rw [hrow, ← hph]
    exact he

/-! ### Entry, counting and exclusion -/

/-- The window `r` of the true half follows the play of its cells beyond. -/
theorem run_eq_win {w : List Bool} (hw4 : w.length = 4) (K φ : Nat) (x : Nat → Bool) :
    ∀ t, run w K (φ % 4) (fun t => drv (fun t => wordAt w (t + φ)) x t (K + 1))
      (win (drv (fun t => wordAt w (t + φ)) x) 0 K) t = win (drv (fun t => wordAt w (t + φ)) x) t K
  | 0 => rfl
  | t + 1 => by
    show GameMask.move K (BitGame.col w (φ % 4 + t)) _ (run w K (φ % 4) _ _ t) = _
    rw [run_eq_win hw4 K φ x t, win_succ (drv_isR30 _ _) t K, drv_col0]
    congr 1
    unfold BitGame.col wordAt
    rw [bit_eq_getD, hw4, show (φ % 4 + t) % 4 = (t + φ) % 4 by omega]

/-- **Entry from the basin.** Every driven right half, finite or infinite, whose window at time 0 lies in the basin
after `R` rounds is in the family by step `R`. -/
theorem enters_of_basin {w : List Bool} (hw4 : w.length = 4) (A : List (Nat × Nat)) {K : Nat} (hK : 1 ≤ K)
    (R φ : Nat) (x : Nat → Bool)
    (h : (basinFrom w K (target A K) (target A K) R).testBit
      (φ % 4 * 2 ^ (K + 2) + win (drv (fun t => wordAt w (t + φ)) x) 0 K) = true) :
    ∃ a ∈ A, ∃ t, t ≤ R ∧ InFamily (drv (fun t => wordAt w (t + φ)) x) a.1 (a.2 + φ) t := by
  have hKB : 2 ^ K ≤ 2 ^ (K + 2) := Nat.pow_le_pow_right (by decide) (by omega)
  have h0 : ∀ φ' r, φ' < w.length → r < 2 ^ K → (target A K).testBit (φ' * 2 ^ (K + 2) + r) = true →
      Enters w K (target A K) 0 φ' r := fun φ' r hφ' _ hT u =>
    ⟨0, Nat.le_refl 0, by rw [Nat.add_zero, Nat.mod_eq_of_lt hφ']; exact hT⟩
  have hφ : φ % 4 < w.length := by rw [hw4]; exact Nat.mod_lt _ (by decide)
  obtain ⟨t, ht, hT⟩ := basinFrom_sound w K hK _ _ 0 h0 R (φ % 4) _ hφ (win_lt _ 0 K) h
    (fun t => drv (fun t => wordAt w (t + φ)) x t (K + 1))
  rw [run_eq_win hw4 K φ x t, hw4] at hT
  obtain ⟨a, ha, k, e, he, hk, hkK, hph, hcode⟩ :=
    target_sound A K _ _ (Nat.lt_of_lt_of_le (win_lt _ t K) hKB) hT
  refine ⟨a, ha, t, by omega, inFamily_of_window he hk (by rw [hph]; omega) fun i hi => ?_⟩
  have e1 := win_testBit (drv (fun t => wordAt w (t + φ)) x) t K i
  rw [decide_eq_true (by omega), Bool.true_and] at e1
  rw [← e1, ← hcode, Nat.testBit_mod_two_pow, decide_eq_true hi, Bool.true_and]

/-- Bits set among the first `2 ^ m` of `x`. -/
def popc : Nat → Nat → Nat
  | 0, x => Nat.mod x 2
  | m + 1, x => popc m (Nat.mod x (Nat.pow 2 (Nat.pow 2 m))) + popc m (Nat.shiftRight x (Nat.pow 2 m))

theorem popc_spec : ∀ m x, popc m x = (List.range (2 ^ m)).countP fun i => x.testBit i
  | 0, x => by
    show x % 2 = _
    rw [Nat.pow_zero, show List.range 1 = [0] from rfl, List.countP_cons, List.countP_nil, Nat.testBit_zero]
    rcases Nat.mod_two_eq_zero_or_one x with h | h <;> simp [h]
  | m + 1, x => by
    show popc m (x % 2 ^ 2 ^ m) + popc m (x >>> 2 ^ m) = _
    rw [popc_spec m, popc_spec m, show 2 ^ (m + 1) = 2 ^ m + 2 ^ m by rw [Nat.pow_succ]; omega, List.range_add,
      List.countP_append, List.countP_map]
    congr 1
    · refine List.countP_congr fun i hi => ?_
      rw [Nat.testBit_mod_two_pow, decide_eq_true (List.mem_range.1 hi), Bool.true_and]
    · refine List.countP_congr fun i _ => ?_
      rw [Function.comp_apply, Nat.testBit_shiftRight]

/-- The bit counts of the 256 bytes, four bits each. -/
def byteTable : Nat := (List.range 256).foldr (fun v acc => Nat.lor acc (Nat.shiftLeft (popc 3 v) (4 * v))) 0

theorem byteTable_ok : ∀ v, v < 256 → Nat.mod (Nat.shiftRight byteTable (4 * v)) 16 = popc 3 v := by
  decide +kernel

/-- Bits set among the first 16 of `x`, by two lookups in the table. -/
def leaf16 (x : Nat) : Nat :=
  Nat.mod (Nat.shiftRight byteTable (4 * Nat.mod x 256)) 16 +
    Nat.mod (Nat.shiftRight byteTable (4 * Nat.mod (Nat.shiftRight x 8) 256)) 16

/-- `popc (m + 4)` as a plain recursor with leaves of 16 bits, which the kernel evaluates with less memory than the
equations of `popc`. -/
def popcR (m : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) leaf16
    (fun k ih x => ih (Nat.mod x (Nat.pow 2 (Nat.pow 2 (k + 4)))) + ih (Nat.shiftRight x (Nat.pow 2 (k + 4)))) m

theorem popc_byte (x : Nat) : popc 3 x = Nat.mod (Nat.shiftRight byteTable (4 * Nat.mod x 256)) 16 := by
  rw [byteTable_ok (Nat.mod x 256) (Nat.mod_lt _ (by decide)), show Nat.mod x 256 = x % 2 ^ 8 from rfl,
    popc_spec, popc_spec]
  refine List.countP_congr fun i hi => ?_
  have hi' := List.mem_range.1 hi
  rw [Nat.testBit_mod_two_pow, decide_eq_true (show i < 8 by
    have : (2 : Nat) ^ 3 = 8 := rfl; omega), Bool.true_and]

theorem popcR_eq : ∀ m x, popcR m x = popc (m + 4) x
  | 0, x => by
    show leaf16 x = popc 3 (x % 2 ^ 2 ^ 3) + popc 3 (x >>> 2 ^ 3)
    rw [popc_byte, popc_byte]
    show (byteTable >>> (4 * (x % 256))) % 16 + (byteTable >>> (4 * ((x >>> 8) % 256))) % 16 =
      (byteTable >>> (4 * (x % 2 ^ 2 ^ 3 % 256))) % 16 + (byteTable >>> (4 * ((x >>> 2 ^ 3) % 256))) % 16
    rw [Nat.mod_mod_of_dvd x (by decide : 256 ∣ 2 ^ 2 ^ 3)]
  | m + 1, x => by
    show popcR m (Nat.mod x (Nat.pow 2 (Nat.pow 2 (m + 4)))) + popcR m (Nat.shiftRight x (Nat.pow 2 (m + 4))) =
      popc (m + 4) (x % 2 ^ 2 ^ (m + 4)) + popc (m + 4) (x >>> 2 ^ (m + 4))
    rw [popcR_eq m, popcR_eq m]
    rfl

/-- The basin's windows at phase `p`. -/
def countPhase (K X p : Nat) : Nat :=
  popcR (K - 4) (Nat.mod (Nat.shiftRight X (Nat.mul p (Nat.pow 2 (K + 2)))) (Nat.pow 2 (Nat.pow 2 K)))

/-- Counting the halves of `n` cells by their first `K`. -/
theorem countP_mod (f : Nat → Bool) (B : Nat) : ∀ m, (List.range (B * m)).countP (fun r => f (r % B)) =
    m * (List.range B).countP f
  | 0 => by simp
  | m + 1 => by
    rw [Nat.mul_succ, List.range_add, List.countP_append, countP_mod f B m, List.countP_map, Nat.succ_mul]
    congr 1
    refine List.countP_congr fun i hi => ?_
    have hi' := List.mem_range.1 hi
    rw [Function.comp_apply, Nat.add_mod, Nat.mul_mod_right, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hi']

/-- **The count.** For `n ≥ K`, the halves of `n` cells whose window at phase `p` lies in `X` number
`countPhase K X p · 2 ^ (n - K)`. -/
theorem count_halves (X K p n : Nat) (hK : 4 ≤ K) (hn : K ≤ n) :
    (List.range (2 ^ n)).countP (fun r => X.testBit (p * 2 ^ (K + 2) + r % 2 ^ K)) =
      countPhase K X p * 2 ^ (n - K) := by
  rw [show 2 ^ n = 2 ^ K * 2 ^ (n - K) by rw [← Nat.pow_add]; congr 1; omega,
    countP_mod (fun v => X.testBit (p * 2 ^ (K + 2) + v)) (2 ^ K), Nat.mul_comm]
  congr 1
  unfold countPhase
  rw [popcR_eq, show K - 4 + 4 = K by omega, popc_spec]
  refine List.countP_congr fun i hi => ?_
  show _ ↔ ((X >>> (p * 2 ^ (K + 2))) % 2 ^ 2 ^ K).testBit i = true
  rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, decide_eq_true (List.mem_range.1 hi), Bool.true_and]

/-- **Exclusion from the basin.** No finite configuration whose cells `1, …, K` at time 0 form a window of the basin
at phase `φ` has a center that repeats `w` from time 0 in that phase, whatever its left half. -/
theorem excludes_of_basin {w : List Bool} (hw4 : w.length = 4) {A : List (Nat × Nat)}
    (hA : ∀ a ∈ A, aligned w a.1 a.2 = true) (hw : ∃ ψ, wordAt w ψ = true) {K : Nat} (hK : 1 ≤ K) (R φ : Nat) :
    ¬ ∃ y : Int → Bool, FinConfig y ∧
      (basinFrom w K (target A K) (target A K) R).testBit (φ % 4 * 2 ^ (K + 2) + win (fun _ p => y (p : Int)) 0 K) =
        true ∧ ∀ t, evol y t 0 = wordAt w (t + φ) := by
  rintro ⟨y, hfin, hB, hc⟩
  rw [← win_drv_zero (fun t => wordAt w (t + φ))] at hB
  obtain ⟨a, ha, t, _, hfam⟩ := enters_of_basin hw4 A hK R φ _ hB
  exact no_finite_of_family (hA a ha) φ hfin hc hw t hfam

/-- **What the basin of one word and width gives**, at each phase `φ < 4`: entry by step `R` from its windows,
the count of the halves of `n ≥ K` cells that start with one, which `counts` lists by phase, and the exclusion of the
word for every finite configuration that starts with one. -/
def Covers (w : List Bool) (A : List (Nat × Nat)) (K R B : Nat) (counts : List Nat) : Prop :=
  ∀ φ, φ < 4 →
    (∀ x : Nat → Bool, B.testBit (φ * 2 ^ (K + 2) + win (fun _ p => x p) 0 K) = true →
      ∃ a ∈ A, ∃ t, t ≤ R ∧ InFamily (drv (fun t => wordAt w (t + φ)) x) a.1 (a.2 + φ) t) ∧
    (∀ r, B.testBit (φ * 2 ^ (K + 2) + r % 2 ^ K) = true →
      ∃ a ∈ A, ∃ t, t ≤ R ∧ InFamily (drv (fun t => wordAt w (t + φ)) fun p => r.testBit (p - 1)) a.1 (a.2 + φ) t) ∧
    (∀ n, K ≤ n → (List.range (2 ^ n)).countP (fun r => B.testBit (φ * 2 ^ (K + 2) + r % 2 ^ K)) =
      counts.getD φ 0 * 2 ^ (n - K)) ∧
    ¬ ∃ y : Int → Bool, FinConfig y ∧ B.testBit (φ * 2 ^ (K + 2) + win (fun _ p => y (p : Int)) 0 K) = true ∧
      ∀ t, evol y t 0 = wordAt w (t + φ)

/-- The basin after `R` rounds. -/
def basin (w : List Bool) (A : List (Nat × Nat)) (K R : Nat) : Nat := basinFrom w K (target A K) (target A K) R

theorem covers_of_counts {w : List Bool} (hw4 : w.length = 4) {A : List (Nat × Nat)}
    (hA : ∀ a ∈ A, aligned w a.1 a.2 = true) (hw : ∃ ψ, wordAt w ψ = true) {K : Nat} (hK : 4 ≤ K) (R : Nat)
    (counts : List Nat) (hc : (List.range 4).map (countPhase K (basin w A K R)) = counts) :
    Covers w A K R (basin w A K R) counts := by
  intro φ hφ
  have hm : φ % 4 = φ := Nat.mod_eq_of_lt hφ
  refine ⟨fun x hx => ?_, fun r hr => ?_, fun n hn => ?_, ?_⟩
  · rw [← win_drv_zero (fun t => wordAt w (t + φ))] at hx
    exact enters_of_basin hw4 A (Nat.le_trans (by decide : 1 ≤ 4) hK) R φ x (by rw [hm]; exact hx)
  · rw [← win_half r K, ← win_drv_zero (fun t => wordAt w (t + φ))] at hr
    exact enters_of_basin hw4 A (Nat.le_trans (by decide : 1 ≤ 4) hK) R φ _ (by rw [hm]; exact hr)
  · rw [count_halves _ K φ n hK hn, ← hc, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range hφ]
    rfl
  · have h := excludes_of_basin hw4 hA hw (Nat.le_trans (by decide : 1 ≤ 4) hK) R φ
    rwa [hm] at h

/-- The width-`K` tables of the four phases, packed `2 ^ K` bits each, spread into the game's blocks. -/
def spread (K L : Nat) : Nat :=
  stack K (fun p => Nat.mod (Nat.shiftRight L (Nat.mul p (Nat.pow 2 K))) (Nat.pow 2 (Nat.pow 2 K))) 4

end ForcedBasin

open ForcedBasin

/-! ### Widths 14 and 16

Each count is one kernel computation of all the rounds; one at a time, each peaks below 3 GB. -/

set_option Elab.async false


/-- At width 14 the family fits only for `0011` and `0111`; the basin of `0001` is empty below width 16. -/
theorem forcedBasin_0011_14 :
    Covers w0011 A0011 14 26 (basin w0011 A0011 14 26) [885, 837, 665, 685] :=
  covers_of_counts rfl A0011_ok ⟨2, rfl⟩ (by decide) 26 _ (by decide +kernel)

theorem forcedBasin_0111_14 :
    Covers w0111 A0111 14 37 (basin w0111 A0111 14 37) [2243, 2376, 2129, 2322] :=
  covers_of_counts rfl A0111_ok ⟨1, rfl⟩ (by decide) 37 _ (by decide +kernel)

theorem forcedBasin_0001_16 :
    Covers w0001 A0001 16 32 (basin w0001 A0001 16 32) [2212, 2066, 1730, 1647] :=
  covers_of_counts rfl A0001_ok ⟨3, rfl⟩ (by decide) 32 _ (by decide +kernel)

theorem forcedBasin_0011_16 :
    Covers w0011 A0011 16 44 (basin w0011 A0011 16 44) [9957, 9693, 9428, 9093] :=
  covers_of_counts rfl A0011_ok ⟨2, rfl⟩ (by decide) 44 _ (by decide +kernel)

theorem forcedBasin_0111_16 :
    Covers w0111 A0111 16 51 (basin w0111 A0111 16 51) [15332, 15418, 14478, 15204] :=
  covers_of_counts rfl A0111_ok ⟨1, rfl⟩ (by decide) 51 _ (by decide +kernel)

end Rule30Open
