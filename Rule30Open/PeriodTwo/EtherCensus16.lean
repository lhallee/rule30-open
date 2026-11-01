module

public import Rule30Open.PeriodTwo.EtherCensus

/-!
# Every head of up to 16 cells on the ether settles

`EtherCensus` runs a checker over every head of 12 cells on the ether and proves (R) for the 2-adic integers whose tail
from cell 12 on is the ether. This module extends the census to the heads of 16 cells, with one more way for a head to
settle: **descent**.

* **Descent.** If the defect of `u` at alignment `(a, o)` is a number `n` at some step `T`, then the half `H^T(u)` has
  the defect `n` at step 0 at the alignment `(a + T, o)`, and its later defect is the defect of `u` from step `T` on
  (`defect_shift`). So if every head below a bound `lo` is bounded at every phase (`HeadsBelow`) and the defect falls
  below `lo`, the head is bounded (`descend`). `runDesc` is the checker `runHead` of `EtherCensus` with this test after
  each of the four steps of a round, and it is sound given the heads below its bound (`runDesc_sound`).
* **Blocks.** The heads are checked in blocks of 256, each with descent below its first head: a block that passes at
  the four phases of an offset extends `HeadsBelow` by the block (`headsBelow_block`), and `descChunk` runs 16 blocks
  as one kernel computation (`headsBelow_chunk`). The heads below `2^12` are bounded by `EtherCensus.census` with the
  bound 61 (`headsBelow_12`).
* **The census.** The kernel runs `descChunk` on the heads from `2^12` to `2^16` at each of the 28 alignments, in 420
  chunks of 4,096 heads, with the bound 79 and 110 rounds; for each offset the chunks are chained from `headsBelow_12`
  (`descUpTo_o_k`, `descCensus`).
* **The theorems.** If the cells of `u` from `p ≤ 16` on are the ether at an alignment, every cell from 79 on is the
  ether at every step (`ether_tail_clear_16`); the orbit of `u` is then eventually periodic
  (`ether_tail_eventually_periodic_16`, through `eventually_periodic_of_clear` of `EtherCensus`), and so is its
  itinerary (`ether_tail_itinerary_16`).

The natural-language argument is `EtherCensus16.md`, beside this file.
-/

@[expose] public section

-- Sequential elaboration: the 420 kernel checks would otherwise run in parallel and stack their memory.
set_option Elab.async false

namespace Rule30Open

/-! ### Descent to a smaller head -/

/-- The defect of `u` is clear from cell `L` on at every step. -/
def DefectClear (u : Nat → Bool) (a o L : Nat) : Prop := ∀ k j, L ≤ j → defect u a o k j = false

/-- **The defect of `H^T(u)` is the defect of `u` from step `T` on**, at the phase moved by `T`. -/
theorem defect_shift (u : Nat → Bool) (a o T s j : Nat) :
    defect (heldOrbit u T) (a + T) o s j = defect u a o (T + s) j := by
  unfold defect
  rw [heldOrbit_add, show a + T + s = a + (T + s) by omega]

theorem defect_phase {u : Nat → Bool} {a a' : Nat} (o t j : Nat) (h : a % 4 = a' % 4) :
    defect u a o t j = defect u a' o t j := by
  unfold defect
  rw [eth_congr (a := a + t) (a' := a' + t) (j := j + o) (j' := j + o) (by omega) rfl]

theorem enc_phase {u : Nat → Bool} {a a' o t n : Nat} (h : a % 4 = a' % 4) (he : Enc u a o t n) : Enc u a' o t n :=
  fun j => by rw [← defect_phase o t j h]; exact he j

theorem defectClear_phase {u : Nat → Bool} {a a' o L : Nat} (h : a % 4 = a' % 4) (hc : DefectClear u a o L) :
    DefectClear u a' o L :=
  fun k j hj => by rw [← defect_phase o k j h]; exact hc k j hj

/-- Every head below `h` is bounded at offset `o`, at every phase: a half with that head as its defect at step 0 has its
defect clear from cell `L` on at every step. -/
def HeadsBelow (o L h : Nat) : Prop := ∀ m, m < h → ∀ a (v : Nat → Bool), Enc v a o 0 m → DefectClear v a o L

/-- **Descent**: a defect that is a smaller head at some step `T` stays clear from cell `L` on, if it is up to `T`. -/
theorem descend {u : Nat → Bool} {a o L h T n : Nat} (IH : HeadsBelow o L h) (he : Enc u a o T n) (hlt : n < h)
    (hb : ∀ k j, k ≤ T → L ≤ j → defect u a o k j = false) : DefectClear u a o L := by
  have he' : Enc (heldOrbit u T) (a + T) o 0 n := fun j => by rw [defect_shift, Nat.add_zero]; exact he j
  have hc := IH n hlt (a + T) (heldOrbit u T) he'
  intro k j hj
  by_cases hk : k ≤ T
  · exact hb k j hk hj
  · have := hc (k - T) j hj
    rwa [defect_shift, show T + (k - T) = k by omega] at this

theorem bound_succ {u : Nat → Bool} {a o L T m : Nat} (hb : ∀ k j, k ≤ T → L ≤ j → defect u a o k j = false)
    (he : Enc u a o (T + 1) m) (hm : m < 2 ^ L) : ∀ k j, k ≤ T + 1 → L ≤ j → defect u a o k j = false := by
  intro k j hk hj
  by_cases hkT : k ≤ T
  · exact hb k j hkT hj
  · rw [show k = T + 1 by omega]; exact clear_of_enc he hm j hj

/-! ### The checker with descent -/

/-- The checker `runHead` of `EtherCensus` for the head `h`, with descent: after each step, a defect below `h` settles
the head. -/
def runDesc (o L h b0 b1 b2 b3 cl : Nat) (fuel : Nat) : Nat → Nat → Nat → Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat → Nat → Bool)
    (fun _ _ _ _ _ => false)
    (fun _ ih t n snap snapT nxt =>
      closedAt cl o L n || (Nat.blt snapT t && Nat.beq n snap) ||
      letN (dstep b0 b1 n) fun n1 => Nat.beq (Nat.shiftRight n1 L) 0 && (Nat.blt n1 h ||
      letN (dstep b1 b2 n1) fun n2 => Nat.beq (Nat.shiftRight n2 L) 0 && (Nat.blt n2 h ||
      letN (dstep b2 b3 n2) fun n3 => Nat.beq (Nat.shiftRight n3 L) 0 && (Nat.blt n3 h ||
      letN (dstep b3 b0 n3) fun n4 => Nat.beq (Nat.shiftRight n4 L) 0 && (Nat.blt n4 h ||
      cond (Nat.beq t nxt) (ih (Nat.add t 4) n4 n t (Nat.mul 2 t)) (ih (Nat.add t 4) n4 snap snapT nxt))))))
    fuel

/-- **The checker with descent is sound**: a head that `runDesc` settles has its defect clear from cell `L` on at every
step, when every smaller head is bounded. -/
theorem runDesc_sound (u : Nat → Bool) (a o L h : Nat) (hL : L ≤ 126) (IH : HeadsBelow o L h) :
    ∀ fuel t n snap snapT nxt,
      runDesc o L h (bgL a o) (bgL (a + 1) o) (bgL (a + 2) o) (bgL (a + 3) o) (closedSet a) fuel t n snap snapT nxt
        = true →
      t % 4 = 0 → snapT % 4 = 0 → snapT ≤ t → Enc u a o t n → Enc u a o snapT snap →
      (∀ k j, k ≤ t → L ≤ j → defect u a o k j = false) → DefectClear u a o L := by
  intro fuel
  induction fuel with
  | zero => intro t n snap snapT nxt h; exact absurd h Bool.false_ne_true
  | succ fuel ih =>
    intro t n snap snapT nxt h' ht hs hst he hse hb
    have hn : n < 2 ^ L :=
      Nat.lt_pow_two_of_testBit _ fun j hj => by rw [← he j]; exact hb t j (Nat.le_refl t) hj
    have h126 : ∀ m, m < 2 ^ L → m < 2 ^ 126 :=
      fun m hm => Nat.lt_of_lt_of_le hm (Nat.pow_le_pow_right (by decide) hL)
    simp only [runDesc] at h'
    rw [letN_eq, letN_eq, letN_eq, letN_eq] at h'
    rw [Bool.or_eq_true, Bool.or_eq_true] at h'
    rcases h' with (hc | hrep) | hsteps
    · -- a closed strip
      obtain ⟨c, hcand⟩ := closedAt_sound hc
      obtain ⟨hinv, hcL, hc12⟩ := stripInv_of_cand he ht hcand
      intro k j hj
      by_cases hk : k ≤ t
      · exact hb k j hk hj
      · have := (stripInv_forever hc12 hinv (k - t)).1 j (by omega)
        rwa [show t + (k - t) = k by omega] at this
    · -- a repeat of the snapshot
      rw [Bool.and_eq_true] at hrep
      have hlt' : snapT < t := Nat.le_of_ble_eq_true hrep.1
      have hnn : n = snap := Nat.eq_of_beq_eq_true hrep.2
      subst hnn
      have hrow := heldOrbit_eq_of_enc he hse (by omega)
      refine clear_of_repeat (i := snapT) (P := t - snapT) (by omega) (by omega) ?_ ?_
      · rw [show snapT + (t - snapT) = t by omega]; exact hrow
      · intro k j hk hj; exact hb k j (by omega) hj
    · -- four steps, each a descent or on to the next
      simp only [Bool.and_eq_true, Bool.or_eq_true] at hsteps
      have e1 : Enc u a o (t + 1) (dstep (bgL a o) (bgL (a + 1) o) n) := by
        have := enc_step he (h126 n hn)
        rwa [bgL_phase o (show (a + t) % 4 = a % 4 by omega),
          bgL_phase o (show (a + t + 1) % 4 = (a + 1) % 4 by omega)] at this
      generalize dstep (bgL a o) (bgL (a + 1) o) n = n1 at e1 hsteps
      obtain ⟨h1, hsteps⟩ := hsteps
      have l1 : n1 < 2 ^ L := lt_of_shiftRight_eq_zero (Nat.eq_of_beq_eq_true h1)
      have hb1 := bound_succ hb e1 l1
      rcases hsteps with hd | hsteps
      · exact descend IH e1 (Nat.le_of_ble_eq_true hd) hb1
      have e2 : Enc u a o (t + 2) (dstep (bgL (a + 1) o) (bgL (a + 2) o) n1) := by
        have := enc_step e1 (h126 n1 l1)
        rwa [bgL_phase o (show (a + (t + 1)) % 4 = (a + 1) % 4 by omega),
          bgL_phase o (show (a + (t + 1) + 1) % 4 = (a + 2) % 4 by omega)] at this
      generalize dstep (bgL (a + 1) o) (bgL (a + 2) o) n1 = n2 at e2 hsteps
      obtain ⟨h2, hsteps⟩ := hsteps
      have l2 : n2 < 2 ^ L := lt_of_shiftRight_eq_zero (Nat.eq_of_beq_eq_true h2)
      have hb2 := bound_succ hb1 e2 l2
      rcases hsteps with hd | hsteps
      · exact descend IH e2 (Nat.le_of_ble_eq_true hd) hb2
      have e3 : Enc u a o (t + 3) (dstep (bgL (a + 2) o) (bgL (a + 3) o) n2) := by
        have := enc_step e2 (h126 n2 l2)
        rwa [bgL_phase o (show (a + (t + 2)) % 4 = (a + 2) % 4 by omega),
          bgL_phase o (show (a + (t + 2) + 1) % 4 = (a + 3) % 4 by omega)] at this
      generalize dstep (bgL (a + 2) o) (bgL (a + 3) o) n2 = n3 at e3 hsteps
      obtain ⟨h3, hsteps⟩ := hsteps
      have l3 : n3 < 2 ^ L := lt_of_shiftRight_eq_zero (Nat.eq_of_beq_eq_true h3)
      have hb3 := bound_succ hb2 e3 l3
      rcases hsteps with hd | hsteps
      · exact descend IH e3 (Nat.le_of_ble_eq_true hd) hb3
      have e4 : Enc u a o (t + 4) (dstep (bgL (a + 3) o) (bgL a o) n3) := by
        have := enc_step e3 (h126 n3 l3)
        rwa [bgL_phase o (show (a + (t + 3)) % 4 = (a + 3) % 4 by omega),
          bgL_phase o (show (a + (t + 3) + 1) % 4 = a % 4 by omega)] at this
      generalize dstep (bgL (a + 3) o) (bgL a o) n3 = n4 at e4 hsteps
      obtain ⟨h4, hsteps⟩ := hsteps
      have l4 : n4 < 2 ^ L := lt_of_shiftRight_eq_zero (Nat.eq_of_beq_eq_true h4)
      have hb4 := bound_succ hb3 e4 l4
      rcases hsteps with hd | hrest
      · exact descend IH e4 (Nat.le_of_ble_eq_true hd) hb4
      cases hnx : Nat.beq t nxt
      · rw [hnx] at hrest
        exact ih (t + 4) n4 snap snapT nxt hrest (by omega) hs (by omega) e4 hse hb4
      · rw [hnx] at hrest
        exact ih (t + 4) n4 n t (2 * t) hrest (by omega) ht (by omega) e4 he hb4

/-! ### The census with descent in blocks -/

/-- Every head `h` with `lo ≤ h < lo + cnt` at the alignment `(a, o)` passes the checker with descent below `lo`, with the
bound `L` and `fuel` rounds. -/
def BlockOK (a o L fuel lo cnt : Nat) : Prop :=
  ∀ h, lo ≤ h → h < lo + cnt →
    runDesc o L lo (bgL a o) (bgL (a + 1) o) (bgL (a + 2) o) (bgL (a + 3) o) (closedSet a) fuel 0 h h 0 4 = true

/-- The `nb` blocks of `B` heads from `lo` on at the alignment `(a, o)`, each with descent below its first head, as one
kernel computation. -/
def descChunk (a o L fuel lo B nb : Nat) : Bool :=
  allBelow (fun b => allBelow (fun k => runDesc o L (lo + B * b) (bgL a o) (bgL (a + 1) o) (bgL (a + 2) o)
    (bgL (a + 3) o) (closedSet a) fuel 0 (lo + B * b + k) (lo + B * b + k) 0 4) B) nb

theorem blockOK_of_chunk {a o L fuel lo B nb : Nat} (h : descChunk a o L fuel lo B nb = true) (b : Nat) (hb : b < nb) :
    BlockOK a o L fuel (lo + B * b) B := by
  intro x hlo hhi
  have := allBelow_spec _ B (allBelow_spec _ nb h b hb) (x - (lo + B * b)) (by omega)
  rwa [show lo + B * b + (x - (lo + B * b)) = x by omega] at this

/-- **One block**: if every head below `lo` is bounded and the block of `cnt` heads from `lo` passes the checker with
descent below `lo` at the four phases, every head below `lo + cnt` is bounded. -/
theorem headsBelow_block {o L fuel lo cnt : Nat} (hL : L ≤ 126) (hhi : lo + cnt ≤ 2 ^ L) (hlo : HeadsBelow o L lo)
    (hc : ∀ a, a < 4 → BlockOK a o L fuel lo cnt) : HeadsBelow o L (lo + cnt) := by
  intro h hh a v he
  by_cases hl : h < lo
  · exact hlo h hl a v he
  have he' : Enc v (a % 4) o 0 h := enc_phase (by omega) he
  have hn : h < 2 ^ L := by omega
  refine defectClear_phase (a := a % 4) (by omega) ?_
  refine runDesc_sound v (a % 4) o L lo hL hlo fuel 0 h h 0 4
    (hc (a % 4) (Nat.mod_lt _ (by decide)) h (by omega) hh) rfl rfl (Nat.le_refl 0) he' he' ?_
  intro k j hk hj
  rw [show k = 0 by omega]
  exact clear_of_enc he' hn j hj

/-- **One chunk**: the blocks of a chunk, one after another. -/
theorem headsBelow_chunk {o L fuel lo B nb hi : Nat} (hL : L ≤ 126) (hhi : lo + B * nb = hi) (hhiL : hi ≤ 2 ^ L)
    (hlo : HeadsBelow o L lo) (hc : ∀ a, a < 4 → descChunk a o L fuel lo B nb = true) : HeadsBelow o L hi := by
  subst hhi
  have key : ∀ i, i ≤ nb → HeadsBelow o L (lo + B * i) := by
    intro i
    induction i with
    | zero => intro _; rw [Nat.mul_zero, Nat.add_zero]; exact hlo
    | succ i ih =>
      intro hi
      have hle : B * (i + 1) ≤ B * nb := Nat.mul_le_mul_left B hi
      rw [Nat.mul_succ] at hle
      have := headsBelow_block hL (by omega) (ih (by omega)) (fun a ha => blockOK_of_chunk (hc a ha) i (by omega))
      rwa [show lo + B * i + B = lo + B * (i + 1) by rw [Nat.mul_succ]; omega] at this
  exact key nb (Nat.le_refl _)

theorem descChunk_phases {o L fuel lo B nb : Nat} (h0 : descChunk 0 o L fuel lo B nb = true)
    (h1 : descChunk 1 o L fuel lo B nb = true) (h2 : descChunk 2 o L fuel lo B nb = true)
    (h3 : descChunk 3 o L fuel lo B nb = true) : ∀ a, a < 4 → descChunk a o L fuel lo B nb = true := by
  intro a ha
  rcases (show a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 by omega) with rfl | rfl | rfl | rfl <;> assumption

/-- **The heads below `2^12` are bounded** by the census of `EtherCensus`, with the bound 61 and so with any bound
`L ≥ 61`. -/
theorem headsBelow_12 (o L : Nat) (ho : o < 7) (hL : 61 ≤ L) : HeadsBelow o L (2 ^ 12) := by
  intro m hm a v he
  have he' : Enc v (a % 4) o 0 m := enc_phase (by omega) he
  have hm61 : m < 2 ^ 61 := Nat.lt_of_lt_of_le hm (Nat.pow_le_pow_right (by decide) (by decide))
  have hc := runHead_sound v (a % 4) o 61 (by decide) 80 0 m m 0 4
    (census (a % 4) o (Nat.mod_lt _ (by decide)) ho m (Nat.zero_le _) hm) rfl rfl (Nat.le_refl 0) he' he'
    (fun k j hk hj => by rw [show k = 0 by omega]; exact clear_of_enc he' hm61 j hj)
  refine defectClear_phase (a := a % 4) (by omega) ?_
  intro k j hj
  exact hc k j (by omega)

/-! ### The census -/

theorem desc_0_0_0 : descChunk 0 0 79 110 4096 256 16 = true := by
  decide +kernel

theorem desc_1_0_0 : descChunk 1 0 79 110 4096 256 16 = true := by
  decide +kernel

theorem desc_2_0_0 : descChunk 2 0 79 110 4096 256 16 = true := by
  decide +kernel

theorem desc_3_0_0 : descChunk 3 0 79 110 4096 256 16 = true := by
  decide +kernel

theorem descUpTo_0_0 : HeadsBelow 0 79 8192 :=
  headsBelow_chunk (by decide) rfl (by decide) (headsBelow_12 0 79 (by decide) (by decide))
    (descChunk_phases desc_0_0_0 desc_1_0_0 desc_2_0_0 desc_3_0_0)

theorem desc_0_0_1 : descChunk 0 0 79 110 8192 256 16 = true := by
  decide +kernel

theorem desc_1_0_1 : descChunk 1 0 79 110 8192 256 16 = true := by
  decide +kernel

theorem desc_2_0_1 : descChunk 2 0 79 110 8192 256 16 = true := by
  decide +kernel

theorem desc_3_0_1 : descChunk 3 0 79 110 8192 256 16 = true := by
  decide +kernel

theorem descUpTo_0_1 : HeadsBelow 0 79 12288 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_0_0)
    (descChunk_phases desc_0_0_1 desc_1_0_1 desc_2_0_1 desc_3_0_1)

theorem desc_0_0_2 : descChunk 0 0 79 110 12288 256 16 = true := by
  decide +kernel

theorem desc_1_0_2 : descChunk 1 0 79 110 12288 256 16 = true := by
  decide +kernel

theorem desc_2_0_2 : descChunk 2 0 79 110 12288 256 16 = true := by
  decide +kernel

theorem desc_3_0_2 : descChunk 3 0 79 110 12288 256 16 = true := by
  decide +kernel

theorem descUpTo_0_2 : HeadsBelow 0 79 16384 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_0_1)
    (descChunk_phases desc_0_0_2 desc_1_0_2 desc_2_0_2 desc_3_0_2)

theorem desc_0_0_3 : descChunk 0 0 79 110 16384 256 16 = true := by
  decide +kernel

theorem desc_1_0_3 : descChunk 1 0 79 110 16384 256 16 = true := by
  decide +kernel

theorem desc_2_0_3 : descChunk 2 0 79 110 16384 256 16 = true := by
  decide +kernel

theorem desc_3_0_3 : descChunk 3 0 79 110 16384 256 16 = true := by
  decide +kernel

theorem descUpTo_0_3 : HeadsBelow 0 79 20480 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_0_2)
    (descChunk_phases desc_0_0_3 desc_1_0_3 desc_2_0_3 desc_3_0_3)

theorem desc_0_0_4 : descChunk 0 0 79 110 20480 256 16 = true := by
  decide +kernel

theorem desc_1_0_4 : descChunk 1 0 79 110 20480 256 16 = true := by
  decide +kernel

theorem desc_2_0_4 : descChunk 2 0 79 110 20480 256 16 = true := by
  decide +kernel

theorem desc_3_0_4 : descChunk 3 0 79 110 20480 256 16 = true := by
  decide +kernel

theorem descUpTo_0_4 : HeadsBelow 0 79 24576 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_0_3)
    (descChunk_phases desc_0_0_4 desc_1_0_4 desc_2_0_4 desc_3_0_4)

theorem desc_0_0_5 : descChunk 0 0 79 110 24576 256 16 = true := by
  decide +kernel

theorem desc_1_0_5 : descChunk 1 0 79 110 24576 256 16 = true := by
  decide +kernel

theorem desc_2_0_5 : descChunk 2 0 79 110 24576 256 16 = true := by
  decide +kernel

theorem desc_3_0_5 : descChunk 3 0 79 110 24576 256 16 = true := by
  decide +kernel

theorem descUpTo_0_5 : HeadsBelow 0 79 28672 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_0_4)
    (descChunk_phases desc_0_0_5 desc_1_0_5 desc_2_0_5 desc_3_0_5)

theorem desc_0_0_6 : descChunk 0 0 79 110 28672 256 16 = true := by
  decide +kernel

theorem desc_1_0_6 : descChunk 1 0 79 110 28672 256 16 = true := by
  decide +kernel

theorem desc_2_0_6 : descChunk 2 0 79 110 28672 256 16 = true := by
  decide +kernel

theorem desc_3_0_6 : descChunk 3 0 79 110 28672 256 16 = true := by
  decide +kernel

theorem descUpTo_0_6 : HeadsBelow 0 79 32768 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_0_5)
    (descChunk_phases desc_0_0_6 desc_1_0_6 desc_2_0_6 desc_3_0_6)

theorem desc_0_0_7 : descChunk 0 0 79 110 32768 256 16 = true := by
  decide +kernel

theorem desc_1_0_7 : descChunk 1 0 79 110 32768 256 16 = true := by
  decide +kernel

theorem desc_2_0_7 : descChunk 2 0 79 110 32768 256 16 = true := by
  decide +kernel

theorem desc_3_0_7 : descChunk 3 0 79 110 32768 256 16 = true := by
  decide +kernel

theorem descUpTo_0_7 : HeadsBelow 0 79 36864 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_0_6)
    (descChunk_phases desc_0_0_7 desc_1_0_7 desc_2_0_7 desc_3_0_7)

theorem desc_0_0_8 : descChunk 0 0 79 110 36864 256 16 = true := by
  decide +kernel

theorem desc_1_0_8 : descChunk 1 0 79 110 36864 256 16 = true := by
  decide +kernel

theorem desc_2_0_8 : descChunk 2 0 79 110 36864 256 16 = true := by
  decide +kernel

theorem desc_3_0_8 : descChunk 3 0 79 110 36864 256 16 = true := by
  decide +kernel

theorem descUpTo_0_8 : HeadsBelow 0 79 40960 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_0_7)
    (descChunk_phases desc_0_0_8 desc_1_0_8 desc_2_0_8 desc_3_0_8)

theorem desc_0_0_9 : descChunk 0 0 79 110 40960 256 16 = true := by
  decide +kernel

theorem desc_1_0_9 : descChunk 1 0 79 110 40960 256 16 = true := by
  decide +kernel

theorem desc_2_0_9 : descChunk 2 0 79 110 40960 256 16 = true := by
  decide +kernel

theorem desc_3_0_9 : descChunk 3 0 79 110 40960 256 16 = true := by
  decide +kernel

theorem descUpTo_0_9 : HeadsBelow 0 79 45056 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_0_8)
    (descChunk_phases desc_0_0_9 desc_1_0_9 desc_2_0_9 desc_3_0_9)

theorem desc_0_0_10 : descChunk 0 0 79 110 45056 256 16 = true := by
  decide +kernel

theorem desc_1_0_10 : descChunk 1 0 79 110 45056 256 16 = true := by
  decide +kernel

theorem desc_2_0_10 : descChunk 2 0 79 110 45056 256 16 = true := by
  decide +kernel

theorem desc_3_0_10 : descChunk 3 0 79 110 45056 256 16 = true := by
  decide +kernel

theorem descUpTo_0_10 : HeadsBelow 0 79 49152 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_0_9)
    (descChunk_phases desc_0_0_10 desc_1_0_10 desc_2_0_10 desc_3_0_10)

theorem desc_0_0_11 : descChunk 0 0 79 110 49152 256 16 = true := by
  decide +kernel

theorem desc_1_0_11 : descChunk 1 0 79 110 49152 256 16 = true := by
  decide +kernel

theorem desc_2_0_11 : descChunk 2 0 79 110 49152 256 16 = true := by
  decide +kernel

theorem desc_3_0_11 : descChunk 3 0 79 110 49152 256 16 = true := by
  decide +kernel

theorem descUpTo_0_11 : HeadsBelow 0 79 53248 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_0_10)
    (descChunk_phases desc_0_0_11 desc_1_0_11 desc_2_0_11 desc_3_0_11)

theorem desc_0_0_12 : descChunk 0 0 79 110 53248 256 16 = true := by
  decide +kernel

theorem desc_1_0_12 : descChunk 1 0 79 110 53248 256 16 = true := by
  decide +kernel

theorem desc_2_0_12 : descChunk 2 0 79 110 53248 256 16 = true := by
  decide +kernel

theorem desc_3_0_12 : descChunk 3 0 79 110 53248 256 16 = true := by
  decide +kernel

theorem descUpTo_0_12 : HeadsBelow 0 79 57344 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_0_11)
    (descChunk_phases desc_0_0_12 desc_1_0_12 desc_2_0_12 desc_3_0_12)

theorem desc_0_0_13 : descChunk 0 0 79 110 57344 256 16 = true := by
  decide +kernel

theorem desc_1_0_13 : descChunk 1 0 79 110 57344 256 16 = true := by
  decide +kernel

theorem desc_2_0_13 : descChunk 2 0 79 110 57344 256 16 = true := by
  decide +kernel

theorem desc_3_0_13 : descChunk 3 0 79 110 57344 256 16 = true := by
  decide +kernel

theorem descUpTo_0_13 : HeadsBelow 0 79 61440 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_0_12)
    (descChunk_phases desc_0_0_13 desc_1_0_13 desc_2_0_13 desc_3_0_13)

theorem desc_0_0_14 : descChunk 0 0 79 110 61440 256 16 = true := by
  decide +kernel

theorem desc_1_0_14 : descChunk 1 0 79 110 61440 256 16 = true := by
  decide +kernel

theorem desc_2_0_14 : descChunk 2 0 79 110 61440 256 16 = true := by
  decide +kernel

theorem desc_3_0_14 : descChunk 3 0 79 110 61440 256 16 = true := by
  decide +kernel

theorem descUpTo_0_14 : HeadsBelow 0 79 65536 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_0_13)
    (descChunk_phases desc_0_0_14 desc_1_0_14 desc_2_0_14 desc_3_0_14)

theorem desc_0_1_0 : descChunk 0 1 79 110 4096 256 16 = true := by
  decide +kernel

theorem desc_1_1_0 : descChunk 1 1 79 110 4096 256 16 = true := by
  decide +kernel

theorem desc_2_1_0 : descChunk 2 1 79 110 4096 256 16 = true := by
  decide +kernel

theorem desc_3_1_0 : descChunk 3 1 79 110 4096 256 16 = true := by
  decide +kernel

theorem descUpTo_1_0 : HeadsBelow 1 79 8192 :=
  headsBelow_chunk (by decide) rfl (by decide) (headsBelow_12 1 79 (by decide) (by decide))
    (descChunk_phases desc_0_1_0 desc_1_1_0 desc_2_1_0 desc_3_1_0)

theorem desc_0_1_1 : descChunk 0 1 79 110 8192 256 16 = true := by
  decide +kernel

theorem desc_1_1_1 : descChunk 1 1 79 110 8192 256 16 = true := by
  decide +kernel

theorem desc_2_1_1 : descChunk 2 1 79 110 8192 256 16 = true := by
  decide +kernel

theorem desc_3_1_1 : descChunk 3 1 79 110 8192 256 16 = true := by
  decide +kernel

theorem descUpTo_1_1 : HeadsBelow 1 79 12288 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_1_0)
    (descChunk_phases desc_0_1_1 desc_1_1_1 desc_2_1_1 desc_3_1_1)

theorem desc_0_1_2 : descChunk 0 1 79 110 12288 256 16 = true := by
  decide +kernel

theorem desc_1_1_2 : descChunk 1 1 79 110 12288 256 16 = true := by
  decide +kernel

theorem desc_2_1_2 : descChunk 2 1 79 110 12288 256 16 = true := by
  decide +kernel

theorem desc_3_1_2 : descChunk 3 1 79 110 12288 256 16 = true := by
  decide +kernel

theorem descUpTo_1_2 : HeadsBelow 1 79 16384 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_1_1)
    (descChunk_phases desc_0_1_2 desc_1_1_2 desc_2_1_2 desc_3_1_2)

theorem desc_0_1_3 : descChunk 0 1 79 110 16384 256 16 = true := by
  decide +kernel

theorem desc_1_1_3 : descChunk 1 1 79 110 16384 256 16 = true := by
  decide +kernel

theorem desc_2_1_3 : descChunk 2 1 79 110 16384 256 16 = true := by
  decide +kernel

theorem desc_3_1_3 : descChunk 3 1 79 110 16384 256 16 = true := by
  decide +kernel

theorem descUpTo_1_3 : HeadsBelow 1 79 20480 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_1_2)
    (descChunk_phases desc_0_1_3 desc_1_1_3 desc_2_1_3 desc_3_1_3)

theorem desc_0_1_4 : descChunk 0 1 79 110 20480 256 16 = true := by
  decide +kernel

theorem desc_1_1_4 : descChunk 1 1 79 110 20480 256 16 = true := by
  decide +kernel

theorem desc_2_1_4 : descChunk 2 1 79 110 20480 256 16 = true := by
  decide +kernel

theorem desc_3_1_4 : descChunk 3 1 79 110 20480 256 16 = true := by
  decide +kernel

theorem descUpTo_1_4 : HeadsBelow 1 79 24576 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_1_3)
    (descChunk_phases desc_0_1_4 desc_1_1_4 desc_2_1_4 desc_3_1_4)

theorem desc_0_1_5 : descChunk 0 1 79 110 24576 256 16 = true := by
  decide +kernel

theorem desc_1_1_5 : descChunk 1 1 79 110 24576 256 16 = true := by
  decide +kernel

theorem desc_2_1_5 : descChunk 2 1 79 110 24576 256 16 = true := by
  decide +kernel

theorem desc_3_1_5 : descChunk 3 1 79 110 24576 256 16 = true := by
  decide +kernel

theorem descUpTo_1_5 : HeadsBelow 1 79 28672 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_1_4)
    (descChunk_phases desc_0_1_5 desc_1_1_5 desc_2_1_5 desc_3_1_5)

theorem desc_0_1_6 : descChunk 0 1 79 110 28672 256 16 = true := by
  decide +kernel

theorem desc_1_1_6 : descChunk 1 1 79 110 28672 256 16 = true := by
  decide +kernel

theorem desc_2_1_6 : descChunk 2 1 79 110 28672 256 16 = true := by
  decide +kernel

theorem desc_3_1_6 : descChunk 3 1 79 110 28672 256 16 = true := by
  decide +kernel

theorem descUpTo_1_6 : HeadsBelow 1 79 32768 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_1_5)
    (descChunk_phases desc_0_1_6 desc_1_1_6 desc_2_1_6 desc_3_1_6)

theorem desc_0_1_7 : descChunk 0 1 79 110 32768 256 16 = true := by
  decide +kernel

theorem desc_1_1_7 : descChunk 1 1 79 110 32768 256 16 = true := by
  decide +kernel

theorem desc_2_1_7 : descChunk 2 1 79 110 32768 256 16 = true := by
  decide +kernel

theorem desc_3_1_7 : descChunk 3 1 79 110 32768 256 16 = true := by
  decide +kernel

theorem descUpTo_1_7 : HeadsBelow 1 79 36864 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_1_6)
    (descChunk_phases desc_0_1_7 desc_1_1_7 desc_2_1_7 desc_3_1_7)

theorem desc_0_1_8 : descChunk 0 1 79 110 36864 256 16 = true := by
  decide +kernel

theorem desc_1_1_8 : descChunk 1 1 79 110 36864 256 16 = true := by
  decide +kernel

theorem desc_2_1_8 : descChunk 2 1 79 110 36864 256 16 = true := by
  decide +kernel

theorem desc_3_1_8 : descChunk 3 1 79 110 36864 256 16 = true := by
  decide +kernel

theorem descUpTo_1_8 : HeadsBelow 1 79 40960 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_1_7)
    (descChunk_phases desc_0_1_8 desc_1_1_8 desc_2_1_8 desc_3_1_8)

theorem desc_0_1_9 : descChunk 0 1 79 110 40960 256 16 = true := by
  decide +kernel

theorem desc_1_1_9 : descChunk 1 1 79 110 40960 256 16 = true := by
  decide +kernel

theorem desc_2_1_9 : descChunk 2 1 79 110 40960 256 16 = true := by
  decide +kernel

theorem desc_3_1_9 : descChunk 3 1 79 110 40960 256 16 = true := by
  decide +kernel

theorem descUpTo_1_9 : HeadsBelow 1 79 45056 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_1_8)
    (descChunk_phases desc_0_1_9 desc_1_1_9 desc_2_1_9 desc_3_1_9)

theorem desc_0_1_10 : descChunk 0 1 79 110 45056 256 16 = true := by
  decide +kernel

theorem desc_1_1_10 : descChunk 1 1 79 110 45056 256 16 = true := by
  decide +kernel

theorem desc_2_1_10 : descChunk 2 1 79 110 45056 256 16 = true := by
  decide +kernel

theorem desc_3_1_10 : descChunk 3 1 79 110 45056 256 16 = true := by
  decide +kernel

theorem descUpTo_1_10 : HeadsBelow 1 79 49152 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_1_9)
    (descChunk_phases desc_0_1_10 desc_1_1_10 desc_2_1_10 desc_3_1_10)

theorem desc_0_1_11 : descChunk 0 1 79 110 49152 256 16 = true := by
  decide +kernel

theorem desc_1_1_11 : descChunk 1 1 79 110 49152 256 16 = true := by
  decide +kernel

theorem desc_2_1_11 : descChunk 2 1 79 110 49152 256 16 = true := by
  decide +kernel

theorem desc_3_1_11 : descChunk 3 1 79 110 49152 256 16 = true := by
  decide +kernel

theorem descUpTo_1_11 : HeadsBelow 1 79 53248 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_1_10)
    (descChunk_phases desc_0_1_11 desc_1_1_11 desc_2_1_11 desc_3_1_11)

theorem desc_0_1_12 : descChunk 0 1 79 110 53248 256 16 = true := by
  decide +kernel

theorem desc_1_1_12 : descChunk 1 1 79 110 53248 256 16 = true := by
  decide +kernel

theorem desc_2_1_12 : descChunk 2 1 79 110 53248 256 16 = true := by
  decide +kernel

theorem desc_3_1_12 : descChunk 3 1 79 110 53248 256 16 = true := by
  decide +kernel

theorem descUpTo_1_12 : HeadsBelow 1 79 57344 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_1_11)
    (descChunk_phases desc_0_1_12 desc_1_1_12 desc_2_1_12 desc_3_1_12)

theorem desc_0_1_13 : descChunk 0 1 79 110 57344 256 16 = true := by
  decide +kernel

theorem desc_1_1_13 : descChunk 1 1 79 110 57344 256 16 = true := by
  decide +kernel

theorem desc_2_1_13 : descChunk 2 1 79 110 57344 256 16 = true := by
  decide +kernel

theorem desc_3_1_13 : descChunk 3 1 79 110 57344 256 16 = true := by
  decide +kernel

theorem descUpTo_1_13 : HeadsBelow 1 79 61440 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_1_12)
    (descChunk_phases desc_0_1_13 desc_1_1_13 desc_2_1_13 desc_3_1_13)

theorem desc_0_1_14 : descChunk 0 1 79 110 61440 256 16 = true := by
  decide +kernel

theorem desc_1_1_14 : descChunk 1 1 79 110 61440 256 16 = true := by
  decide +kernel

theorem desc_2_1_14 : descChunk 2 1 79 110 61440 256 16 = true := by
  decide +kernel

theorem desc_3_1_14 : descChunk 3 1 79 110 61440 256 16 = true := by
  decide +kernel

theorem descUpTo_1_14 : HeadsBelow 1 79 65536 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_1_13)
    (descChunk_phases desc_0_1_14 desc_1_1_14 desc_2_1_14 desc_3_1_14)

theorem desc_0_2_0 : descChunk 0 2 79 110 4096 256 16 = true := by
  decide +kernel

theorem desc_1_2_0 : descChunk 1 2 79 110 4096 256 16 = true := by
  decide +kernel

theorem desc_2_2_0 : descChunk 2 2 79 110 4096 256 16 = true := by
  decide +kernel

theorem desc_3_2_0 : descChunk 3 2 79 110 4096 256 16 = true := by
  decide +kernel

theorem descUpTo_2_0 : HeadsBelow 2 79 8192 :=
  headsBelow_chunk (by decide) rfl (by decide) (headsBelow_12 2 79 (by decide) (by decide))
    (descChunk_phases desc_0_2_0 desc_1_2_0 desc_2_2_0 desc_3_2_0)

theorem desc_0_2_1 : descChunk 0 2 79 110 8192 256 16 = true := by
  decide +kernel

theorem desc_1_2_1 : descChunk 1 2 79 110 8192 256 16 = true := by
  decide +kernel

theorem desc_2_2_1 : descChunk 2 2 79 110 8192 256 16 = true := by
  decide +kernel

theorem desc_3_2_1 : descChunk 3 2 79 110 8192 256 16 = true := by
  decide +kernel

theorem descUpTo_2_1 : HeadsBelow 2 79 12288 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_2_0)
    (descChunk_phases desc_0_2_1 desc_1_2_1 desc_2_2_1 desc_3_2_1)

theorem desc_0_2_2 : descChunk 0 2 79 110 12288 256 16 = true := by
  decide +kernel

theorem desc_1_2_2 : descChunk 1 2 79 110 12288 256 16 = true := by
  decide +kernel

theorem desc_2_2_2 : descChunk 2 2 79 110 12288 256 16 = true := by
  decide +kernel

theorem desc_3_2_2 : descChunk 3 2 79 110 12288 256 16 = true := by
  decide +kernel

theorem descUpTo_2_2 : HeadsBelow 2 79 16384 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_2_1)
    (descChunk_phases desc_0_2_2 desc_1_2_2 desc_2_2_2 desc_3_2_2)

theorem desc_0_2_3 : descChunk 0 2 79 110 16384 256 16 = true := by
  decide +kernel

theorem desc_1_2_3 : descChunk 1 2 79 110 16384 256 16 = true := by
  decide +kernel

theorem desc_2_2_3 : descChunk 2 2 79 110 16384 256 16 = true := by
  decide +kernel

theorem desc_3_2_3 : descChunk 3 2 79 110 16384 256 16 = true := by
  decide +kernel

theorem descUpTo_2_3 : HeadsBelow 2 79 20480 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_2_2)
    (descChunk_phases desc_0_2_3 desc_1_2_3 desc_2_2_3 desc_3_2_3)

theorem desc_0_2_4 : descChunk 0 2 79 110 20480 256 16 = true := by
  decide +kernel

theorem desc_1_2_4 : descChunk 1 2 79 110 20480 256 16 = true := by
  decide +kernel

theorem desc_2_2_4 : descChunk 2 2 79 110 20480 256 16 = true := by
  decide +kernel

theorem desc_3_2_4 : descChunk 3 2 79 110 20480 256 16 = true := by
  decide +kernel

theorem descUpTo_2_4 : HeadsBelow 2 79 24576 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_2_3)
    (descChunk_phases desc_0_2_4 desc_1_2_4 desc_2_2_4 desc_3_2_4)

theorem desc_0_2_5 : descChunk 0 2 79 110 24576 256 16 = true := by
  decide +kernel

theorem desc_1_2_5 : descChunk 1 2 79 110 24576 256 16 = true := by
  decide +kernel

theorem desc_2_2_5 : descChunk 2 2 79 110 24576 256 16 = true := by
  decide +kernel

theorem desc_3_2_5 : descChunk 3 2 79 110 24576 256 16 = true := by
  decide +kernel

theorem descUpTo_2_5 : HeadsBelow 2 79 28672 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_2_4)
    (descChunk_phases desc_0_2_5 desc_1_2_5 desc_2_2_5 desc_3_2_5)

theorem desc_0_2_6 : descChunk 0 2 79 110 28672 256 16 = true := by
  decide +kernel

theorem desc_1_2_6 : descChunk 1 2 79 110 28672 256 16 = true := by
  decide +kernel

theorem desc_2_2_6 : descChunk 2 2 79 110 28672 256 16 = true := by
  decide +kernel

theorem desc_3_2_6 : descChunk 3 2 79 110 28672 256 16 = true := by
  decide +kernel

theorem descUpTo_2_6 : HeadsBelow 2 79 32768 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_2_5)
    (descChunk_phases desc_0_2_6 desc_1_2_6 desc_2_2_6 desc_3_2_6)

theorem desc_0_2_7 : descChunk 0 2 79 110 32768 256 16 = true := by
  decide +kernel

theorem desc_1_2_7 : descChunk 1 2 79 110 32768 256 16 = true := by
  decide +kernel

theorem desc_2_2_7 : descChunk 2 2 79 110 32768 256 16 = true := by
  decide +kernel

theorem desc_3_2_7 : descChunk 3 2 79 110 32768 256 16 = true := by
  decide +kernel

theorem descUpTo_2_7 : HeadsBelow 2 79 36864 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_2_6)
    (descChunk_phases desc_0_2_7 desc_1_2_7 desc_2_2_7 desc_3_2_7)

theorem desc_0_2_8 : descChunk 0 2 79 110 36864 256 16 = true := by
  decide +kernel

theorem desc_1_2_8 : descChunk 1 2 79 110 36864 256 16 = true := by
  decide +kernel

theorem desc_2_2_8 : descChunk 2 2 79 110 36864 256 16 = true := by
  decide +kernel

theorem desc_3_2_8 : descChunk 3 2 79 110 36864 256 16 = true := by
  decide +kernel

theorem descUpTo_2_8 : HeadsBelow 2 79 40960 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_2_7)
    (descChunk_phases desc_0_2_8 desc_1_2_8 desc_2_2_8 desc_3_2_8)

theorem desc_0_2_9 : descChunk 0 2 79 110 40960 256 16 = true := by
  decide +kernel

theorem desc_1_2_9 : descChunk 1 2 79 110 40960 256 16 = true := by
  decide +kernel

theorem desc_2_2_9 : descChunk 2 2 79 110 40960 256 16 = true := by
  decide +kernel

theorem desc_3_2_9 : descChunk 3 2 79 110 40960 256 16 = true := by
  decide +kernel

theorem descUpTo_2_9 : HeadsBelow 2 79 45056 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_2_8)
    (descChunk_phases desc_0_2_9 desc_1_2_9 desc_2_2_9 desc_3_2_9)

theorem desc_0_2_10 : descChunk 0 2 79 110 45056 256 16 = true := by
  decide +kernel

theorem desc_1_2_10 : descChunk 1 2 79 110 45056 256 16 = true := by
  decide +kernel

theorem desc_2_2_10 : descChunk 2 2 79 110 45056 256 16 = true := by
  decide +kernel

theorem desc_3_2_10 : descChunk 3 2 79 110 45056 256 16 = true := by
  decide +kernel

theorem descUpTo_2_10 : HeadsBelow 2 79 49152 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_2_9)
    (descChunk_phases desc_0_2_10 desc_1_2_10 desc_2_2_10 desc_3_2_10)

theorem desc_0_2_11 : descChunk 0 2 79 110 49152 256 16 = true := by
  decide +kernel

theorem desc_1_2_11 : descChunk 1 2 79 110 49152 256 16 = true := by
  decide +kernel

theorem desc_2_2_11 : descChunk 2 2 79 110 49152 256 16 = true := by
  decide +kernel

theorem desc_3_2_11 : descChunk 3 2 79 110 49152 256 16 = true := by
  decide +kernel

theorem descUpTo_2_11 : HeadsBelow 2 79 53248 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_2_10)
    (descChunk_phases desc_0_2_11 desc_1_2_11 desc_2_2_11 desc_3_2_11)

theorem desc_0_2_12 : descChunk 0 2 79 110 53248 256 16 = true := by
  decide +kernel

theorem desc_1_2_12 : descChunk 1 2 79 110 53248 256 16 = true := by
  decide +kernel

theorem desc_2_2_12 : descChunk 2 2 79 110 53248 256 16 = true := by
  decide +kernel

theorem desc_3_2_12 : descChunk 3 2 79 110 53248 256 16 = true := by
  decide +kernel

theorem descUpTo_2_12 : HeadsBelow 2 79 57344 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_2_11)
    (descChunk_phases desc_0_2_12 desc_1_2_12 desc_2_2_12 desc_3_2_12)

theorem desc_0_2_13 : descChunk 0 2 79 110 57344 256 16 = true := by
  decide +kernel

theorem desc_1_2_13 : descChunk 1 2 79 110 57344 256 16 = true := by
  decide +kernel

theorem desc_2_2_13 : descChunk 2 2 79 110 57344 256 16 = true := by
  decide +kernel

theorem desc_3_2_13 : descChunk 3 2 79 110 57344 256 16 = true := by
  decide +kernel

theorem descUpTo_2_13 : HeadsBelow 2 79 61440 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_2_12)
    (descChunk_phases desc_0_2_13 desc_1_2_13 desc_2_2_13 desc_3_2_13)

theorem desc_0_2_14 : descChunk 0 2 79 110 61440 256 16 = true := by
  decide +kernel

theorem desc_1_2_14 : descChunk 1 2 79 110 61440 256 16 = true := by
  decide +kernel

theorem desc_2_2_14 : descChunk 2 2 79 110 61440 256 16 = true := by
  decide +kernel

theorem desc_3_2_14 : descChunk 3 2 79 110 61440 256 16 = true := by
  decide +kernel

theorem descUpTo_2_14 : HeadsBelow 2 79 65536 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_2_13)
    (descChunk_phases desc_0_2_14 desc_1_2_14 desc_2_2_14 desc_3_2_14)

theorem desc_0_3_0 : descChunk 0 3 79 110 4096 256 16 = true := by
  decide +kernel

theorem desc_1_3_0 : descChunk 1 3 79 110 4096 256 16 = true := by
  decide +kernel

theorem desc_2_3_0 : descChunk 2 3 79 110 4096 256 16 = true := by
  decide +kernel

theorem desc_3_3_0 : descChunk 3 3 79 110 4096 256 16 = true := by
  decide +kernel

theorem descUpTo_3_0 : HeadsBelow 3 79 8192 :=
  headsBelow_chunk (by decide) rfl (by decide) (headsBelow_12 3 79 (by decide) (by decide))
    (descChunk_phases desc_0_3_0 desc_1_3_0 desc_2_3_0 desc_3_3_0)

theorem desc_0_3_1 : descChunk 0 3 79 110 8192 256 16 = true := by
  decide +kernel

theorem desc_1_3_1 : descChunk 1 3 79 110 8192 256 16 = true := by
  decide +kernel

theorem desc_2_3_1 : descChunk 2 3 79 110 8192 256 16 = true := by
  decide +kernel

theorem desc_3_3_1 : descChunk 3 3 79 110 8192 256 16 = true := by
  decide +kernel

theorem descUpTo_3_1 : HeadsBelow 3 79 12288 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_3_0)
    (descChunk_phases desc_0_3_1 desc_1_3_1 desc_2_3_1 desc_3_3_1)

theorem desc_0_3_2 : descChunk 0 3 79 110 12288 256 16 = true := by
  decide +kernel

theorem desc_1_3_2 : descChunk 1 3 79 110 12288 256 16 = true := by
  decide +kernel

theorem desc_2_3_2 : descChunk 2 3 79 110 12288 256 16 = true := by
  decide +kernel

theorem desc_3_3_2 : descChunk 3 3 79 110 12288 256 16 = true := by
  decide +kernel

theorem descUpTo_3_2 : HeadsBelow 3 79 16384 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_3_1)
    (descChunk_phases desc_0_3_2 desc_1_3_2 desc_2_3_2 desc_3_3_2)

theorem desc_0_3_3 : descChunk 0 3 79 110 16384 256 16 = true := by
  decide +kernel

theorem desc_1_3_3 : descChunk 1 3 79 110 16384 256 16 = true := by
  decide +kernel

theorem desc_2_3_3 : descChunk 2 3 79 110 16384 256 16 = true := by
  decide +kernel

theorem desc_3_3_3 : descChunk 3 3 79 110 16384 256 16 = true := by
  decide +kernel

theorem descUpTo_3_3 : HeadsBelow 3 79 20480 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_3_2)
    (descChunk_phases desc_0_3_3 desc_1_3_3 desc_2_3_3 desc_3_3_3)

theorem desc_0_3_4 : descChunk 0 3 79 110 20480 256 16 = true := by
  decide +kernel

theorem desc_1_3_4 : descChunk 1 3 79 110 20480 256 16 = true := by
  decide +kernel

theorem desc_2_3_4 : descChunk 2 3 79 110 20480 256 16 = true := by
  decide +kernel

theorem desc_3_3_4 : descChunk 3 3 79 110 20480 256 16 = true := by
  decide +kernel

theorem descUpTo_3_4 : HeadsBelow 3 79 24576 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_3_3)
    (descChunk_phases desc_0_3_4 desc_1_3_4 desc_2_3_4 desc_3_3_4)

theorem desc_0_3_5 : descChunk 0 3 79 110 24576 256 16 = true := by
  decide +kernel

theorem desc_1_3_5 : descChunk 1 3 79 110 24576 256 16 = true := by
  decide +kernel

theorem desc_2_3_5 : descChunk 2 3 79 110 24576 256 16 = true := by
  decide +kernel

theorem desc_3_3_5 : descChunk 3 3 79 110 24576 256 16 = true := by
  decide +kernel

theorem descUpTo_3_5 : HeadsBelow 3 79 28672 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_3_4)
    (descChunk_phases desc_0_3_5 desc_1_3_5 desc_2_3_5 desc_3_3_5)

theorem desc_0_3_6 : descChunk 0 3 79 110 28672 256 16 = true := by
  decide +kernel

theorem desc_1_3_6 : descChunk 1 3 79 110 28672 256 16 = true := by
  decide +kernel

theorem desc_2_3_6 : descChunk 2 3 79 110 28672 256 16 = true := by
  decide +kernel

theorem desc_3_3_6 : descChunk 3 3 79 110 28672 256 16 = true := by
  decide +kernel

theorem descUpTo_3_6 : HeadsBelow 3 79 32768 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_3_5)
    (descChunk_phases desc_0_3_6 desc_1_3_6 desc_2_3_6 desc_3_3_6)

theorem desc_0_3_7 : descChunk 0 3 79 110 32768 256 16 = true := by
  decide +kernel

theorem desc_1_3_7 : descChunk 1 3 79 110 32768 256 16 = true := by
  decide +kernel

theorem desc_2_3_7 : descChunk 2 3 79 110 32768 256 16 = true := by
  decide +kernel

theorem desc_3_3_7 : descChunk 3 3 79 110 32768 256 16 = true := by
  decide +kernel

theorem descUpTo_3_7 : HeadsBelow 3 79 36864 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_3_6)
    (descChunk_phases desc_0_3_7 desc_1_3_7 desc_2_3_7 desc_3_3_7)

theorem desc_0_3_8 : descChunk 0 3 79 110 36864 256 16 = true := by
  decide +kernel

theorem desc_1_3_8 : descChunk 1 3 79 110 36864 256 16 = true := by
  decide +kernel

theorem desc_2_3_8 : descChunk 2 3 79 110 36864 256 16 = true := by
  decide +kernel

theorem desc_3_3_8 : descChunk 3 3 79 110 36864 256 16 = true := by
  decide +kernel

theorem descUpTo_3_8 : HeadsBelow 3 79 40960 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_3_7)
    (descChunk_phases desc_0_3_8 desc_1_3_8 desc_2_3_8 desc_3_3_8)

theorem desc_0_3_9 : descChunk 0 3 79 110 40960 256 16 = true := by
  decide +kernel

theorem desc_1_3_9 : descChunk 1 3 79 110 40960 256 16 = true := by
  decide +kernel

theorem desc_2_3_9 : descChunk 2 3 79 110 40960 256 16 = true := by
  decide +kernel

theorem desc_3_3_9 : descChunk 3 3 79 110 40960 256 16 = true := by
  decide +kernel

theorem descUpTo_3_9 : HeadsBelow 3 79 45056 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_3_8)
    (descChunk_phases desc_0_3_9 desc_1_3_9 desc_2_3_9 desc_3_3_9)

theorem desc_0_3_10 : descChunk 0 3 79 110 45056 256 16 = true := by
  decide +kernel

theorem desc_1_3_10 : descChunk 1 3 79 110 45056 256 16 = true := by
  decide +kernel

theorem desc_2_3_10 : descChunk 2 3 79 110 45056 256 16 = true := by
  decide +kernel

theorem desc_3_3_10 : descChunk 3 3 79 110 45056 256 16 = true := by
  decide +kernel

theorem descUpTo_3_10 : HeadsBelow 3 79 49152 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_3_9)
    (descChunk_phases desc_0_3_10 desc_1_3_10 desc_2_3_10 desc_3_3_10)

theorem desc_0_3_11 : descChunk 0 3 79 110 49152 256 16 = true := by
  decide +kernel

theorem desc_1_3_11 : descChunk 1 3 79 110 49152 256 16 = true := by
  decide +kernel

theorem desc_2_3_11 : descChunk 2 3 79 110 49152 256 16 = true := by
  decide +kernel

theorem desc_3_3_11 : descChunk 3 3 79 110 49152 256 16 = true := by
  decide +kernel

theorem descUpTo_3_11 : HeadsBelow 3 79 53248 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_3_10)
    (descChunk_phases desc_0_3_11 desc_1_3_11 desc_2_3_11 desc_3_3_11)

theorem desc_0_3_12 : descChunk 0 3 79 110 53248 256 16 = true := by
  decide +kernel

theorem desc_1_3_12 : descChunk 1 3 79 110 53248 256 16 = true := by
  decide +kernel

theorem desc_2_3_12 : descChunk 2 3 79 110 53248 256 16 = true := by
  decide +kernel

theorem desc_3_3_12 : descChunk 3 3 79 110 53248 256 16 = true := by
  decide +kernel

theorem descUpTo_3_12 : HeadsBelow 3 79 57344 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_3_11)
    (descChunk_phases desc_0_3_12 desc_1_3_12 desc_2_3_12 desc_3_3_12)

theorem desc_0_3_13 : descChunk 0 3 79 110 57344 256 16 = true := by
  decide +kernel

theorem desc_1_3_13 : descChunk 1 3 79 110 57344 256 16 = true := by
  decide +kernel

theorem desc_2_3_13 : descChunk 2 3 79 110 57344 256 16 = true := by
  decide +kernel

theorem desc_3_3_13 : descChunk 3 3 79 110 57344 256 16 = true := by
  decide +kernel

theorem descUpTo_3_13 : HeadsBelow 3 79 61440 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_3_12)
    (descChunk_phases desc_0_3_13 desc_1_3_13 desc_2_3_13 desc_3_3_13)

theorem desc_0_3_14 : descChunk 0 3 79 110 61440 256 16 = true := by
  decide +kernel

theorem desc_1_3_14 : descChunk 1 3 79 110 61440 256 16 = true := by
  decide +kernel

theorem desc_2_3_14 : descChunk 2 3 79 110 61440 256 16 = true := by
  decide +kernel

theorem desc_3_3_14 : descChunk 3 3 79 110 61440 256 16 = true := by
  decide +kernel

theorem descUpTo_3_14 : HeadsBelow 3 79 65536 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_3_13)
    (descChunk_phases desc_0_3_14 desc_1_3_14 desc_2_3_14 desc_3_3_14)

theorem desc_0_4_0 : descChunk 0 4 79 110 4096 256 16 = true := by
  decide +kernel

theorem desc_1_4_0 : descChunk 1 4 79 110 4096 256 16 = true := by
  decide +kernel

theorem desc_2_4_0 : descChunk 2 4 79 110 4096 256 16 = true := by
  decide +kernel

theorem desc_3_4_0 : descChunk 3 4 79 110 4096 256 16 = true := by
  decide +kernel

theorem descUpTo_4_0 : HeadsBelow 4 79 8192 :=
  headsBelow_chunk (by decide) rfl (by decide) (headsBelow_12 4 79 (by decide) (by decide))
    (descChunk_phases desc_0_4_0 desc_1_4_0 desc_2_4_0 desc_3_4_0)

theorem desc_0_4_1 : descChunk 0 4 79 110 8192 256 16 = true := by
  decide +kernel

theorem desc_1_4_1 : descChunk 1 4 79 110 8192 256 16 = true := by
  decide +kernel

theorem desc_2_4_1 : descChunk 2 4 79 110 8192 256 16 = true := by
  decide +kernel

theorem desc_3_4_1 : descChunk 3 4 79 110 8192 256 16 = true := by
  decide +kernel

theorem descUpTo_4_1 : HeadsBelow 4 79 12288 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_4_0)
    (descChunk_phases desc_0_4_1 desc_1_4_1 desc_2_4_1 desc_3_4_1)

theorem desc_0_4_2 : descChunk 0 4 79 110 12288 256 16 = true := by
  decide +kernel

theorem desc_1_4_2 : descChunk 1 4 79 110 12288 256 16 = true := by
  decide +kernel

theorem desc_2_4_2 : descChunk 2 4 79 110 12288 256 16 = true := by
  decide +kernel

theorem desc_3_4_2 : descChunk 3 4 79 110 12288 256 16 = true := by
  decide +kernel

theorem descUpTo_4_2 : HeadsBelow 4 79 16384 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_4_1)
    (descChunk_phases desc_0_4_2 desc_1_4_2 desc_2_4_2 desc_3_4_2)

theorem desc_0_4_3 : descChunk 0 4 79 110 16384 256 16 = true := by
  decide +kernel

theorem desc_1_4_3 : descChunk 1 4 79 110 16384 256 16 = true := by
  decide +kernel

theorem desc_2_4_3 : descChunk 2 4 79 110 16384 256 16 = true := by
  decide +kernel

theorem desc_3_4_3 : descChunk 3 4 79 110 16384 256 16 = true := by
  decide +kernel

theorem descUpTo_4_3 : HeadsBelow 4 79 20480 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_4_2)
    (descChunk_phases desc_0_4_3 desc_1_4_3 desc_2_4_3 desc_3_4_3)

theorem desc_0_4_4 : descChunk 0 4 79 110 20480 256 16 = true := by
  decide +kernel

theorem desc_1_4_4 : descChunk 1 4 79 110 20480 256 16 = true := by
  decide +kernel

theorem desc_2_4_4 : descChunk 2 4 79 110 20480 256 16 = true := by
  decide +kernel

theorem desc_3_4_4 : descChunk 3 4 79 110 20480 256 16 = true := by
  decide +kernel

theorem descUpTo_4_4 : HeadsBelow 4 79 24576 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_4_3)
    (descChunk_phases desc_0_4_4 desc_1_4_4 desc_2_4_4 desc_3_4_4)

theorem desc_0_4_5 : descChunk 0 4 79 110 24576 256 16 = true := by
  decide +kernel

theorem desc_1_4_5 : descChunk 1 4 79 110 24576 256 16 = true := by
  decide +kernel

theorem desc_2_4_5 : descChunk 2 4 79 110 24576 256 16 = true := by
  decide +kernel

theorem desc_3_4_5 : descChunk 3 4 79 110 24576 256 16 = true := by
  decide +kernel

theorem descUpTo_4_5 : HeadsBelow 4 79 28672 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_4_4)
    (descChunk_phases desc_0_4_5 desc_1_4_5 desc_2_4_5 desc_3_4_5)

theorem desc_0_4_6 : descChunk 0 4 79 110 28672 256 16 = true := by
  decide +kernel

theorem desc_1_4_6 : descChunk 1 4 79 110 28672 256 16 = true := by
  decide +kernel

theorem desc_2_4_6 : descChunk 2 4 79 110 28672 256 16 = true := by
  decide +kernel

theorem desc_3_4_6 : descChunk 3 4 79 110 28672 256 16 = true := by
  decide +kernel

theorem descUpTo_4_6 : HeadsBelow 4 79 32768 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_4_5)
    (descChunk_phases desc_0_4_6 desc_1_4_6 desc_2_4_6 desc_3_4_6)

theorem desc_0_4_7 : descChunk 0 4 79 110 32768 256 16 = true := by
  decide +kernel

theorem desc_1_4_7 : descChunk 1 4 79 110 32768 256 16 = true := by
  decide +kernel

theorem desc_2_4_7 : descChunk 2 4 79 110 32768 256 16 = true := by
  decide +kernel

theorem desc_3_4_7 : descChunk 3 4 79 110 32768 256 16 = true := by
  decide +kernel

theorem descUpTo_4_7 : HeadsBelow 4 79 36864 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_4_6)
    (descChunk_phases desc_0_4_7 desc_1_4_7 desc_2_4_7 desc_3_4_7)

theorem desc_0_4_8 : descChunk 0 4 79 110 36864 256 16 = true := by
  decide +kernel

theorem desc_1_4_8 : descChunk 1 4 79 110 36864 256 16 = true := by
  decide +kernel

theorem desc_2_4_8 : descChunk 2 4 79 110 36864 256 16 = true := by
  decide +kernel

theorem desc_3_4_8 : descChunk 3 4 79 110 36864 256 16 = true := by
  decide +kernel

theorem descUpTo_4_8 : HeadsBelow 4 79 40960 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_4_7)
    (descChunk_phases desc_0_4_8 desc_1_4_8 desc_2_4_8 desc_3_4_8)

theorem desc_0_4_9 : descChunk 0 4 79 110 40960 256 16 = true := by
  decide +kernel

theorem desc_1_4_9 : descChunk 1 4 79 110 40960 256 16 = true := by
  decide +kernel

theorem desc_2_4_9 : descChunk 2 4 79 110 40960 256 16 = true := by
  decide +kernel

theorem desc_3_4_9 : descChunk 3 4 79 110 40960 256 16 = true := by
  decide +kernel

theorem descUpTo_4_9 : HeadsBelow 4 79 45056 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_4_8)
    (descChunk_phases desc_0_4_9 desc_1_4_9 desc_2_4_9 desc_3_4_9)

theorem desc_0_4_10 : descChunk 0 4 79 110 45056 256 16 = true := by
  decide +kernel

theorem desc_1_4_10 : descChunk 1 4 79 110 45056 256 16 = true := by
  decide +kernel

theorem desc_2_4_10 : descChunk 2 4 79 110 45056 256 16 = true := by
  decide +kernel

theorem desc_3_4_10 : descChunk 3 4 79 110 45056 256 16 = true := by
  decide +kernel

theorem descUpTo_4_10 : HeadsBelow 4 79 49152 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_4_9)
    (descChunk_phases desc_0_4_10 desc_1_4_10 desc_2_4_10 desc_3_4_10)

theorem desc_0_4_11 : descChunk 0 4 79 110 49152 256 16 = true := by
  decide +kernel

theorem desc_1_4_11 : descChunk 1 4 79 110 49152 256 16 = true := by
  decide +kernel

theorem desc_2_4_11 : descChunk 2 4 79 110 49152 256 16 = true := by
  decide +kernel

theorem desc_3_4_11 : descChunk 3 4 79 110 49152 256 16 = true := by
  decide +kernel

theorem descUpTo_4_11 : HeadsBelow 4 79 53248 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_4_10)
    (descChunk_phases desc_0_4_11 desc_1_4_11 desc_2_4_11 desc_3_4_11)

theorem desc_0_4_12 : descChunk 0 4 79 110 53248 256 16 = true := by
  decide +kernel

theorem desc_1_4_12 : descChunk 1 4 79 110 53248 256 16 = true := by
  decide +kernel

theorem desc_2_4_12 : descChunk 2 4 79 110 53248 256 16 = true := by
  decide +kernel

theorem desc_3_4_12 : descChunk 3 4 79 110 53248 256 16 = true := by
  decide +kernel

theorem descUpTo_4_12 : HeadsBelow 4 79 57344 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_4_11)
    (descChunk_phases desc_0_4_12 desc_1_4_12 desc_2_4_12 desc_3_4_12)

theorem desc_0_4_13 : descChunk 0 4 79 110 57344 256 16 = true := by
  decide +kernel

theorem desc_1_4_13 : descChunk 1 4 79 110 57344 256 16 = true := by
  decide +kernel

theorem desc_2_4_13 : descChunk 2 4 79 110 57344 256 16 = true := by
  decide +kernel

theorem desc_3_4_13 : descChunk 3 4 79 110 57344 256 16 = true := by
  decide +kernel

theorem descUpTo_4_13 : HeadsBelow 4 79 61440 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_4_12)
    (descChunk_phases desc_0_4_13 desc_1_4_13 desc_2_4_13 desc_3_4_13)

theorem desc_0_4_14 : descChunk 0 4 79 110 61440 256 16 = true := by
  decide +kernel

theorem desc_1_4_14 : descChunk 1 4 79 110 61440 256 16 = true := by
  decide +kernel

theorem desc_2_4_14 : descChunk 2 4 79 110 61440 256 16 = true := by
  decide +kernel

theorem desc_3_4_14 : descChunk 3 4 79 110 61440 256 16 = true := by
  decide +kernel

theorem descUpTo_4_14 : HeadsBelow 4 79 65536 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_4_13)
    (descChunk_phases desc_0_4_14 desc_1_4_14 desc_2_4_14 desc_3_4_14)

theorem desc_0_5_0 : descChunk 0 5 79 110 4096 256 16 = true := by
  decide +kernel

theorem desc_1_5_0 : descChunk 1 5 79 110 4096 256 16 = true := by
  decide +kernel

theorem desc_2_5_0 : descChunk 2 5 79 110 4096 256 16 = true := by
  decide +kernel

theorem desc_3_5_0 : descChunk 3 5 79 110 4096 256 16 = true := by
  decide +kernel

theorem descUpTo_5_0 : HeadsBelow 5 79 8192 :=
  headsBelow_chunk (by decide) rfl (by decide) (headsBelow_12 5 79 (by decide) (by decide))
    (descChunk_phases desc_0_5_0 desc_1_5_0 desc_2_5_0 desc_3_5_0)

theorem desc_0_5_1 : descChunk 0 5 79 110 8192 256 16 = true := by
  decide +kernel

theorem desc_1_5_1 : descChunk 1 5 79 110 8192 256 16 = true := by
  decide +kernel

theorem desc_2_5_1 : descChunk 2 5 79 110 8192 256 16 = true := by
  decide +kernel

theorem desc_3_5_1 : descChunk 3 5 79 110 8192 256 16 = true := by
  decide +kernel

theorem descUpTo_5_1 : HeadsBelow 5 79 12288 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_5_0)
    (descChunk_phases desc_0_5_1 desc_1_5_1 desc_2_5_1 desc_3_5_1)

theorem desc_0_5_2 : descChunk 0 5 79 110 12288 256 16 = true := by
  decide +kernel

theorem desc_1_5_2 : descChunk 1 5 79 110 12288 256 16 = true := by
  decide +kernel

theorem desc_2_5_2 : descChunk 2 5 79 110 12288 256 16 = true := by
  decide +kernel

theorem desc_3_5_2 : descChunk 3 5 79 110 12288 256 16 = true := by
  decide +kernel

theorem descUpTo_5_2 : HeadsBelow 5 79 16384 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_5_1)
    (descChunk_phases desc_0_5_2 desc_1_5_2 desc_2_5_2 desc_3_5_2)

theorem desc_0_5_3 : descChunk 0 5 79 110 16384 256 16 = true := by
  decide +kernel

theorem desc_1_5_3 : descChunk 1 5 79 110 16384 256 16 = true := by
  decide +kernel

theorem desc_2_5_3 : descChunk 2 5 79 110 16384 256 16 = true := by
  decide +kernel

theorem desc_3_5_3 : descChunk 3 5 79 110 16384 256 16 = true := by
  decide +kernel

theorem descUpTo_5_3 : HeadsBelow 5 79 20480 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_5_2)
    (descChunk_phases desc_0_5_3 desc_1_5_3 desc_2_5_3 desc_3_5_3)

theorem desc_0_5_4 : descChunk 0 5 79 110 20480 256 16 = true := by
  decide +kernel

theorem desc_1_5_4 : descChunk 1 5 79 110 20480 256 16 = true := by
  decide +kernel

theorem desc_2_5_4 : descChunk 2 5 79 110 20480 256 16 = true := by
  decide +kernel

theorem desc_3_5_4 : descChunk 3 5 79 110 20480 256 16 = true := by
  decide +kernel

theorem descUpTo_5_4 : HeadsBelow 5 79 24576 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_5_3)
    (descChunk_phases desc_0_5_4 desc_1_5_4 desc_2_5_4 desc_3_5_4)

theorem desc_0_5_5 : descChunk 0 5 79 110 24576 256 16 = true := by
  decide +kernel

theorem desc_1_5_5 : descChunk 1 5 79 110 24576 256 16 = true := by
  decide +kernel

theorem desc_2_5_5 : descChunk 2 5 79 110 24576 256 16 = true := by
  decide +kernel

theorem desc_3_5_5 : descChunk 3 5 79 110 24576 256 16 = true := by
  decide +kernel

theorem descUpTo_5_5 : HeadsBelow 5 79 28672 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_5_4)
    (descChunk_phases desc_0_5_5 desc_1_5_5 desc_2_5_5 desc_3_5_5)

theorem desc_0_5_6 : descChunk 0 5 79 110 28672 256 16 = true := by
  decide +kernel

theorem desc_1_5_6 : descChunk 1 5 79 110 28672 256 16 = true := by
  decide +kernel

theorem desc_2_5_6 : descChunk 2 5 79 110 28672 256 16 = true := by
  decide +kernel

theorem desc_3_5_6 : descChunk 3 5 79 110 28672 256 16 = true := by
  decide +kernel

theorem descUpTo_5_6 : HeadsBelow 5 79 32768 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_5_5)
    (descChunk_phases desc_0_5_6 desc_1_5_6 desc_2_5_6 desc_3_5_6)

theorem desc_0_5_7 : descChunk 0 5 79 110 32768 256 16 = true := by
  decide +kernel

theorem desc_1_5_7 : descChunk 1 5 79 110 32768 256 16 = true := by
  decide +kernel

theorem desc_2_5_7 : descChunk 2 5 79 110 32768 256 16 = true := by
  decide +kernel

theorem desc_3_5_7 : descChunk 3 5 79 110 32768 256 16 = true := by
  decide +kernel

theorem descUpTo_5_7 : HeadsBelow 5 79 36864 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_5_6)
    (descChunk_phases desc_0_5_7 desc_1_5_7 desc_2_5_7 desc_3_5_7)

theorem desc_0_5_8 : descChunk 0 5 79 110 36864 256 16 = true := by
  decide +kernel

theorem desc_1_5_8 : descChunk 1 5 79 110 36864 256 16 = true := by
  decide +kernel

theorem desc_2_5_8 : descChunk 2 5 79 110 36864 256 16 = true := by
  decide +kernel

theorem desc_3_5_8 : descChunk 3 5 79 110 36864 256 16 = true := by
  decide +kernel

theorem descUpTo_5_8 : HeadsBelow 5 79 40960 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_5_7)
    (descChunk_phases desc_0_5_8 desc_1_5_8 desc_2_5_8 desc_3_5_8)

theorem desc_0_5_9 : descChunk 0 5 79 110 40960 256 16 = true := by
  decide +kernel

theorem desc_1_5_9 : descChunk 1 5 79 110 40960 256 16 = true := by
  decide +kernel

theorem desc_2_5_9 : descChunk 2 5 79 110 40960 256 16 = true := by
  decide +kernel

theorem desc_3_5_9 : descChunk 3 5 79 110 40960 256 16 = true := by
  decide +kernel

theorem descUpTo_5_9 : HeadsBelow 5 79 45056 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_5_8)
    (descChunk_phases desc_0_5_9 desc_1_5_9 desc_2_5_9 desc_3_5_9)

theorem desc_0_5_10 : descChunk 0 5 79 110 45056 256 16 = true := by
  decide +kernel

theorem desc_1_5_10 : descChunk 1 5 79 110 45056 256 16 = true := by
  decide +kernel

theorem desc_2_5_10 : descChunk 2 5 79 110 45056 256 16 = true := by
  decide +kernel

theorem desc_3_5_10 : descChunk 3 5 79 110 45056 256 16 = true := by
  decide +kernel

theorem descUpTo_5_10 : HeadsBelow 5 79 49152 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_5_9)
    (descChunk_phases desc_0_5_10 desc_1_5_10 desc_2_5_10 desc_3_5_10)

theorem desc_0_5_11 : descChunk 0 5 79 110 49152 256 16 = true := by
  decide +kernel

theorem desc_1_5_11 : descChunk 1 5 79 110 49152 256 16 = true := by
  decide +kernel

theorem desc_2_5_11 : descChunk 2 5 79 110 49152 256 16 = true := by
  decide +kernel

theorem desc_3_5_11 : descChunk 3 5 79 110 49152 256 16 = true := by
  decide +kernel

theorem descUpTo_5_11 : HeadsBelow 5 79 53248 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_5_10)
    (descChunk_phases desc_0_5_11 desc_1_5_11 desc_2_5_11 desc_3_5_11)

theorem desc_0_5_12 : descChunk 0 5 79 110 53248 256 16 = true := by
  decide +kernel

theorem desc_1_5_12 : descChunk 1 5 79 110 53248 256 16 = true := by
  decide +kernel

theorem desc_2_5_12 : descChunk 2 5 79 110 53248 256 16 = true := by
  decide +kernel

theorem desc_3_5_12 : descChunk 3 5 79 110 53248 256 16 = true := by
  decide +kernel

theorem descUpTo_5_12 : HeadsBelow 5 79 57344 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_5_11)
    (descChunk_phases desc_0_5_12 desc_1_5_12 desc_2_5_12 desc_3_5_12)

theorem desc_0_5_13 : descChunk 0 5 79 110 57344 256 16 = true := by
  decide +kernel

theorem desc_1_5_13 : descChunk 1 5 79 110 57344 256 16 = true := by
  decide +kernel

theorem desc_2_5_13 : descChunk 2 5 79 110 57344 256 16 = true := by
  decide +kernel

theorem desc_3_5_13 : descChunk 3 5 79 110 57344 256 16 = true := by
  decide +kernel

theorem descUpTo_5_13 : HeadsBelow 5 79 61440 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_5_12)
    (descChunk_phases desc_0_5_13 desc_1_5_13 desc_2_5_13 desc_3_5_13)

theorem desc_0_5_14 : descChunk 0 5 79 110 61440 256 16 = true := by
  decide +kernel

theorem desc_1_5_14 : descChunk 1 5 79 110 61440 256 16 = true := by
  decide +kernel

theorem desc_2_5_14 : descChunk 2 5 79 110 61440 256 16 = true := by
  decide +kernel

theorem desc_3_5_14 : descChunk 3 5 79 110 61440 256 16 = true := by
  decide +kernel

theorem descUpTo_5_14 : HeadsBelow 5 79 65536 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_5_13)
    (descChunk_phases desc_0_5_14 desc_1_5_14 desc_2_5_14 desc_3_5_14)

theorem desc_0_6_0 : descChunk 0 6 79 110 4096 256 16 = true := by
  decide +kernel

theorem desc_1_6_0 : descChunk 1 6 79 110 4096 256 16 = true := by
  decide +kernel

theorem desc_2_6_0 : descChunk 2 6 79 110 4096 256 16 = true := by
  decide +kernel

theorem desc_3_6_0 : descChunk 3 6 79 110 4096 256 16 = true := by
  decide +kernel

theorem descUpTo_6_0 : HeadsBelow 6 79 8192 :=
  headsBelow_chunk (by decide) rfl (by decide) (headsBelow_12 6 79 (by decide) (by decide))
    (descChunk_phases desc_0_6_0 desc_1_6_0 desc_2_6_0 desc_3_6_0)

theorem desc_0_6_1 : descChunk 0 6 79 110 8192 256 16 = true := by
  decide +kernel

theorem desc_1_6_1 : descChunk 1 6 79 110 8192 256 16 = true := by
  decide +kernel

theorem desc_2_6_1 : descChunk 2 6 79 110 8192 256 16 = true := by
  decide +kernel

theorem desc_3_6_1 : descChunk 3 6 79 110 8192 256 16 = true := by
  decide +kernel

theorem descUpTo_6_1 : HeadsBelow 6 79 12288 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_6_0)
    (descChunk_phases desc_0_6_1 desc_1_6_1 desc_2_6_1 desc_3_6_1)

theorem desc_0_6_2 : descChunk 0 6 79 110 12288 256 16 = true := by
  decide +kernel

theorem desc_1_6_2 : descChunk 1 6 79 110 12288 256 16 = true := by
  decide +kernel

theorem desc_2_6_2 : descChunk 2 6 79 110 12288 256 16 = true := by
  decide +kernel

theorem desc_3_6_2 : descChunk 3 6 79 110 12288 256 16 = true := by
  decide +kernel

theorem descUpTo_6_2 : HeadsBelow 6 79 16384 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_6_1)
    (descChunk_phases desc_0_6_2 desc_1_6_2 desc_2_6_2 desc_3_6_2)

theorem desc_0_6_3 : descChunk 0 6 79 110 16384 256 16 = true := by
  decide +kernel

theorem desc_1_6_3 : descChunk 1 6 79 110 16384 256 16 = true := by
  decide +kernel

theorem desc_2_6_3 : descChunk 2 6 79 110 16384 256 16 = true := by
  decide +kernel

theorem desc_3_6_3 : descChunk 3 6 79 110 16384 256 16 = true := by
  decide +kernel

theorem descUpTo_6_3 : HeadsBelow 6 79 20480 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_6_2)
    (descChunk_phases desc_0_6_3 desc_1_6_3 desc_2_6_3 desc_3_6_3)

theorem desc_0_6_4 : descChunk 0 6 79 110 20480 256 16 = true := by
  decide +kernel

theorem desc_1_6_4 : descChunk 1 6 79 110 20480 256 16 = true := by
  decide +kernel

theorem desc_2_6_4 : descChunk 2 6 79 110 20480 256 16 = true := by
  decide +kernel

theorem desc_3_6_4 : descChunk 3 6 79 110 20480 256 16 = true := by
  decide +kernel

theorem descUpTo_6_4 : HeadsBelow 6 79 24576 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_6_3)
    (descChunk_phases desc_0_6_4 desc_1_6_4 desc_2_6_4 desc_3_6_4)

theorem desc_0_6_5 : descChunk 0 6 79 110 24576 256 16 = true := by
  decide +kernel

theorem desc_1_6_5 : descChunk 1 6 79 110 24576 256 16 = true := by
  decide +kernel

theorem desc_2_6_5 : descChunk 2 6 79 110 24576 256 16 = true := by
  decide +kernel

theorem desc_3_6_5 : descChunk 3 6 79 110 24576 256 16 = true := by
  decide +kernel

theorem descUpTo_6_5 : HeadsBelow 6 79 28672 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_6_4)
    (descChunk_phases desc_0_6_5 desc_1_6_5 desc_2_6_5 desc_3_6_5)

theorem desc_0_6_6 : descChunk 0 6 79 110 28672 256 16 = true := by
  decide +kernel

theorem desc_1_6_6 : descChunk 1 6 79 110 28672 256 16 = true := by
  decide +kernel

theorem desc_2_6_6 : descChunk 2 6 79 110 28672 256 16 = true := by
  decide +kernel

theorem desc_3_6_6 : descChunk 3 6 79 110 28672 256 16 = true := by
  decide +kernel

theorem descUpTo_6_6 : HeadsBelow 6 79 32768 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_6_5)
    (descChunk_phases desc_0_6_6 desc_1_6_6 desc_2_6_6 desc_3_6_6)

theorem desc_0_6_7 : descChunk 0 6 79 110 32768 256 16 = true := by
  decide +kernel

theorem desc_1_6_7 : descChunk 1 6 79 110 32768 256 16 = true := by
  decide +kernel

theorem desc_2_6_7 : descChunk 2 6 79 110 32768 256 16 = true := by
  decide +kernel

theorem desc_3_6_7 : descChunk 3 6 79 110 32768 256 16 = true := by
  decide +kernel

theorem descUpTo_6_7 : HeadsBelow 6 79 36864 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_6_6)
    (descChunk_phases desc_0_6_7 desc_1_6_7 desc_2_6_7 desc_3_6_7)

theorem desc_0_6_8 : descChunk 0 6 79 110 36864 256 16 = true := by
  decide +kernel

theorem desc_1_6_8 : descChunk 1 6 79 110 36864 256 16 = true := by
  decide +kernel

theorem desc_2_6_8 : descChunk 2 6 79 110 36864 256 16 = true := by
  decide +kernel

theorem desc_3_6_8 : descChunk 3 6 79 110 36864 256 16 = true := by
  decide +kernel

theorem descUpTo_6_8 : HeadsBelow 6 79 40960 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_6_7)
    (descChunk_phases desc_0_6_8 desc_1_6_8 desc_2_6_8 desc_3_6_8)

theorem desc_0_6_9 : descChunk 0 6 79 110 40960 256 16 = true := by
  decide +kernel

theorem desc_1_6_9 : descChunk 1 6 79 110 40960 256 16 = true := by
  decide +kernel

theorem desc_2_6_9 : descChunk 2 6 79 110 40960 256 16 = true := by
  decide +kernel

theorem desc_3_6_9 : descChunk 3 6 79 110 40960 256 16 = true := by
  decide +kernel

theorem descUpTo_6_9 : HeadsBelow 6 79 45056 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_6_8)
    (descChunk_phases desc_0_6_9 desc_1_6_9 desc_2_6_9 desc_3_6_9)

theorem desc_0_6_10 : descChunk 0 6 79 110 45056 256 16 = true := by
  decide +kernel

theorem desc_1_6_10 : descChunk 1 6 79 110 45056 256 16 = true := by
  decide +kernel

theorem desc_2_6_10 : descChunk 2 6 79 110 45056 256 16 = true := by
  decide +kernel

theorem desc_3_6_10 : descChunk 3 6 79 110 45056 256 16 = true := by
  decide +kernel

theorem descUpTo_6_10 : HeadsBelow 6 79 49152 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_6_9)
    (descChunk_phases desc_0_6_10 desc_1_6_10 desc_2_6_10 desc_3_6_10)

theorem desc_0_6_11 : descChunk 0 6 79 110 49152 256 16 = true := by
  decide +kernel

theorem desc_1_6_11 : descChunk 1 6 79 110 49152 256 16 = true := by
  decide +kernel

theorem desc_2_6_11 : descChunk 2 6 79 110 49152 256 16 = true := by
  decide +kernel

theorem desc_3_6_11 : descChunk 3 6 79 110 49152 256 16 = true := by
  decide +kernel

theorem descUpTo_6_11 : HeadsBelow 6 79 53248 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_6_10)
    (descChunk_phases desc_0_6_11 desc_1_6_11 desc_2_6_11 desc_3_6_11)

theorem desc_0_6_12 : descChunk 0 6 79 110 53248 256 16 = true := by
  decide +kernel

theorem desc_1_6_12 : descChunk 1 6 79 110 53248 256 16 = true := by
  decide +kernel

theorem desc_2_6_12 : descChunk 2 6 79 110 53248 256 16 = true := by
  decide +kernel

theorem desc_3_6_12 : descChunk 3 6 79 110 53248 256 16 = true := by
  decide +kernel

theorem descUpTo_6_12 : HeadsBelow 6 79 57344 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_6_11)
    (descChunk_phases desc_0_6_12 desc_1_6_12 desc_2_6_12 desc_3_6_12)

theorem desc_0_6_13 : descChunk 0 6 79 110 57344 256 16 = true := by
  decide +kernel

theorem desc_1_6_13 : descChunk 1 6 79 110 57344 256 16 = true := by
  decide +kernel

theorem desc_2_6_13 : descChunk 2 6 79 110 57344 256 16 = true := by
  decide +kernel

theorem desc_3_6_13 : descChunk 3 6 79 110 57344 256 16 = true := by
  decide +kernel

theorem descUpTo_6_13 : HeadsBelow 6 79 61440 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_6_12)
    (descChunk_phases desc_0_6_13 desc_1_6_13 desc_2_6_13 desc_3_6_13)

theorem desc_0_6_14 : descChunk 0 6 79 110 61440 256 16 = true := by
  decide +kernel

theorem desc_1_6_14 : descChunk 1 6 79 110 61440 256 16 = true := by
  decide +kernel

theorem desc_2_6_14 : descChunk 2 6 79 110 61440 256 16 = true := by
  decide +kernel

theorem desc_3_6_14 : descChunk 3 6 79 110 61440 256 16 = true := by
  decide +kernel

theorem descUpTo_6_14 : HeadsBelow 6 79 65536 :=
  headsBelow_chunk (by decide) rfl (by decide) (descUpTo_6_13)
    (descChunk_phases desc_0_6_14 desc_1_6_14 desc_2_6_14 desc_3_6_14)

/-- **The census with descent**: at each offset and every phase, every head below `2 ^ 16` is bounded with the
bound 79. -/
theorem descCensus (o : Nat) (ho : o < 7) : HeadsBelow o 79 (2 ^ 16) :=
  match o, ho with
  | 0, _ => descUpTo_0_14
  | 1, _ => descUpTo_1_14
  | 2, _ => descUpTo_2_14
  | 3, _ => descUpTo_3_14
  | 4, _ => descUpTo_4_14
  | 5, _ => descUpTo_5_14
  | 6, _ => descUpTo_6_14
  | o + 7, ho => absurd ho (by omega)

/-! ### Every head of up to 16 cells on the ether settles -/

/-- **The defect of every head of up to 16 cells on the ether stays below cell 79.** If the cells of `u` from
`p ≤ 16` on are the ether at the alignment `(a, o)`, then at every step `t` the cells from 79 on are the ether at phase
`a + t`. -/
theorem ether_tail_clear_16 (u : Nat → Bool) (a o p : Nat) (hp : p ≤ 16)
    (hu : ∀ j, p ≤ j → u j = eth a (j + o)) :
    ∀ t j, 79 ≤ j → heldOrbit u t j = eth (a + t) (j + o) := by
  have hd : ∀ j, 16 ≤ j → defect u a (o % 7) 0 j = false := by
    intro j hj
    unfold defect
    rw [show heldOrbit u 0 j = u j from rfl, hu j (by omega), Nat.add_zero,
      eth_congr (a := a) (a' := a) (j := j + o) (j' := j + o % 7) rfl (by omega)]
    exact Bool.xor_self _
  have he : Enc u a (o % 7) 0 (natOf (defect u a (o % 7) 0) 16) := by
    intro j
    rw [natOf_testBit]
    by_cases hj : j < 16
    · rw [decide_eq_true hj, Bool.true_and]
    · rw [decide_eq_false hj, Bool.false_and, hd j (by omega)]
  have hc := descCensus (o % 7) (Nat.mod_lt _ (by decide)) _ (natOf_lt _ 16) a u he
  intro t j hj
  rw [heldOrbit_eq_defect u a (o % 7) t j, hc t j hj, Bool.false_xor]
  exact eth_congr rfl (by omega)

/-- **Every head of up to 16 cells on the ether has an eventually periodic orbit.** -/
theorem ether_tail_eventually_periodic_16 (u : Nat → Bool) (a o p : Nat) (hp : p ≤ 16)
    (hu : ∀ j, p ≤ j → u j = eth a (j + o)) :
    ∃ T P, 0 < P ∧ ∀ t, T ≤ t → heldOrbit u (t + P) = heldOrbit u t := by
  refine eventually_periodic_of_clear (a := a) (o := o) (L := 79) fun t j hj => ?_
  unfold defect
  rw [ether_tail_clear_16 u a o p hp hu t j hj]
  exact Bool.xor_self _

/-- **Conjecture (R) for the ether tails of up to 16 cells**: every 2-adic integer whose bits from `p ≤ 16` on are the
ether at one of its alignments, in `InK` or not, has an eventually periodic itinerary. -/
theorem ether_tail_itinerary_16 (u : Nat → Bool) (a o p : Nat) (hp : p ≤ 16)
    (hu : ∀ j, p ≤ j → u j = eth a (j + o)) :
    ∃ pre n, 0 < n ∧ ∀ s, pre ≤ s → itinerary u (s + n) = itinerary u s := by
  obtain ⟨T, P, hP, h⟩ := ether_tail_eventually_periodic_16 u a o p hp hu
  exact itinerary_of_eventually_periodic hP h

end Rule30Open
