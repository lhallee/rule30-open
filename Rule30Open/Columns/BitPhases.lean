module

public import Rule30Open.Columns.BitGame

/-!
# The game decided phase by phase in the kernel excludes the 14 blocks of period 17 and 18 that need 13 or 14 cells

[BitGame](BitGame.md) decides the finite game in the kernel with one check per block, `gameCheck`, and at 13 or 14
cells the kernel's tables for one block take up to 12 GB, or more. That check is a conjunction over the phases of the
block, and the argument of `bitGame_column` uses one phase at a time. Here each phase gets its own check, `phaseCheck`,
with its own number of images, rounds and fuel, in its own declaration, so the kernel holds the tables of one phase at
a time.

* `phaseCheck`: the refinement of `gameCheck` at one phase.
* `phases_column`, `center_not_phases`, `phases_not_eventuallyWord`: `bitGame_column` and its corollaries for a block
  each of whose phases passes `phaseCheck` with some parameters.
* `center_not_phases_list`, `phases_list_not_eventually`: the same for every entry of a list of blocks.
* `blocksPhases18`, `center_not_blocksPhases18`, `not_eventually_blocksPhases18`: the 14 blocks of period 17 and 18
  that the game excludes at width 13 or 14 and that neither the kit nor [WallSets](WallSets.md) excludes, with one
  kernel check per phase.

The natural-language argument is `BitPhases.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

open Ruliology.CellularAutomata

namespace BitGame

/-- The check of `gameCheck` at the phase `φ` alone, with its own number of images `D`, rounds and fuel. -/
def phaseCheck (b : List Bool) (K D rounds fuel φ : Nat) : Bool :=
  let m := Nat.land (reach b K D) (blockSel K (fun ψ => Nat.beq ψ φ) b.length)
  refine b K fuel φ rounds (Nat.land m (Nat.xor (full b.length K) (valMask b K))) (Nat.land m (valMask b K))

end BitGame

open BitGame

/-- **`bitGame_column` with one check per phase.** No column of the orbit of a row with a leftmost 1 repeats a block,
from any time on and in any rotation, if at each phase some number of images, rounds and fuel make `phaseCheck`
succeed. -/
theorem phases_column (init : Int → Bool) (m : Int) (hm : init m = true) (hz : ∀ x : Int, x < m → init x = false)
    (b : List Bool) (K : Nat) (hK : 1 ≤ K) (hP : 1 ≤ b.length)
    (hall : ∀ φ, φ < b.length → ∃ D rounds fuel, phaseCheck b K D rounds fuel φ = true) (k : Int) (T shift : Nat)
    (h : ∀ t : Nat, T ≤ t → evolve init t k = col b (t + shift)) : False := by
  have hB := Nat.two_pow_pos (K + 2)
  have hKB : 2 ^ K < 2 ^ (K + 2) := Nat.pow_lt_pow_right (by decide) (by omega)
  let phase : Nat → Nat := fun t => (t + shift) % b.length
  let code : Nat → Nat := fun t => codeFrom init t (k + 1) K
  have hcode : ∀ t, code t < 2 ^ K := fun t => codeFrom_lt init t K (k + 1)
  have hpos : ∀ t, pos init b K k shift t = phase t * 2 ^ (K + 2) + code t := fun t => rfl
  -- the column left of `k` is the value of the node
  have hleft : ∀ t, T ≤ t → evolve init t (k - 1) = value b (phase t) (code t) := fun t ht => by
    rw [left_cell init t k, h (t + 1) (by omega), h t ht]
    unfold value col
    have e1 : (t + 1 + shift) % b.length = (phase t + 1) % b.length := by
      show _ = ((t + shift) % b.length + 1) % b.length
      rw [mod_succ_mod, show t + 1 + shift = t + shift + 1 by omega]
    have e2 : (t + shift) % b.length = phase t % b.length := by
      show _ = (t + shift) % b.length % b.length; rw [Nat.mod_mod]
    rw [e1, e2, testBit_codeFrom, decide_eq_true (by omega), Bool.true_and, show k + 1 + ((0 : Nat) : Int) = k + 1 by
      omega]
  -- at each phase the value is eventually constant
  have hconst : ∀ φ, φ < b.length → ∃ N, ∀ t1 t2, N ≤ t1 → N ≤ t2 → phase t1 = φ → phase t2 = φ →
      value b φ (code t1) = value b φ (code t2) := by
    intro φ hφ
    obtain ⟨D, rounds, fuel, hφc⟩ := hall φ hφ
    refine Classical.byContradiction fun hno => ?_
    -- otherwise both values recur at phase `φ`
    have hrec : ∀ v : Bool, ∀ N, ∃ t, N ≤ t ∧ phase t = φ ∧ value b φ (code t) = v := by
      intro v N
      refine Classical.byContradiction fun hn => hno ⟨N + T + D + 1, fun t1 t2 h1 h2 e1 e2 => ?_⟩
      have a1 : value b φ (code t1) = !v := by
        cases hv : value b φ (code t1)
        · cases v
          · exact absurd ⟨t1, by omega, e1, hv⟩ hn
          · rfl
        · cases v
          · rfl
          · exact absurd ⟨t1, by omega, e1, hv⟩ hn
      have a2 : value b φ (code t2) = !v := by
        cases hv : value b φ (code t2)
        · cases v
          · exact absurd ⟨t2, by omega, e2, hv⟩ hn
          · rfl
        · cases v
          · rfl
          · exact absurd ⟨t2, by omega, e2, hv⟩ hn
      rw [a1, a2]
    -- a node of each value is visited again and again
    have hvisit : ∀ v : Bool, ∃ r, r < 2 ^ K ∧ value b φ r = v ∧ ∀ N, ∃ t, N ≤ t ∧ phase t = φ ∧ code t = r := by
      intro v
      obtain ⟨r, hr, hr'⟩ := pigeonhole (fun t => phase t = φ ∧ value b φ (code t) = v) code (2 ^ K)
        (fun N => by obtain ⟨t, ht, e, ev⟩ := hrec v N; exact ⟨t, ht, ⟨e, ev⟩, hcode t⟩)
      refine ⟨r, hr, ?_, fun N => ?_⟩
      · obtain ⟨t, -, ⟨-, ev⟩, ec⟩ := hr' 0
        rw [← ec]; exact ev
      · obtain ⟨t, ht, ⟨e, -⟩, ec⟩ := hr' N
        exact ⟨t, ht, e, ec⟩
    obtain ⟨ra, hra, va, visA⟩ := hvisit false
    obtain ⟨rb, hrb, vb, visB⟩ := hvisit true
    have hraB : ra < 2 ^ (K + 2) := by omega
    have hrbB : rb < 2 ^ (K + 2) := by omega
    -- visits as positions, in either order
    have order : ∀ r r', (∀ N, ∃ t, N ≤ t ∧ phase t = φ ∧ code t = r) → (∀ N, ∃ t, N ≤ t ∧ phase t = φ ∧ code t = r') →
        ∀ N, ∃ t1 t2, N ≤ t1 ∧ t1 < t2 ∧ pos init b K k shift t1 = φ * 2 ^ (K + 2) + r ∧
          pos init b K k shift t2 = φ * 2 ^ (K + 2) + r' := fun r r' hr hr' N => by
      obtain ⟨t1, ht1, e1, c1⟩ := hr N
      obtain ⟨t2, ht2, e2, c2⟩ := hr' (t1 + 1)
      exact ⟨t1, t2, ht1, by omega, by rw [hpos, e1, c1], by rw [hpos, e2, c2]⟩
    have hrefine := refine_sound init b K hK k T shift hP h fuel φ _ _ (order ra rb visA visB)
      (order rb ra visB visA) rounds
    -- the two nodes start in their sides
    obtain ⟨tA, htA, eA, cA⟩ := visA (T + D)
    obtain ⟨tB, htB, eB, cB⟩ := visB (T + D)
    have hJA := play_reach init b K hK k T shift hP h D tA htA
    have hJB := play_reach init b K hK k T shift hP h D tB htB
    rw [hpos, eA, cA] at hJA
    rw [hpos, eB, cB] at hJB
    have hgA := blk_lt hφ hraB
    have hgB := blk_lt hφ hrbB
    have hdivA : (φ * 2 ^ (K + 2) + ra) / 2 ^ (K + 2) = φ := by
      rw [Nat.mul_comm, Nat.mul_add_div hB, Nat.div_eq_of_lt hraB, Nat.add_zero]
    have hdivB : (φ * 2 ^ (K + 2) + rb) / 2 ^ (K + 2) = φ := by
      rw [Nat.mul_comm, Nat.mul_add_div hB, Nat.div_eq_of_lt hrbB, Nat.add_zero]
    have hvalA : value b φ (φ * 2 ^ (K + 2) + ra) = value b φ ra := by
      unfold value; rw [testBit_zero_blk]
    have hvalB : value b φ (φ * 2 ^ (K + 2) + rb) = value b φ rb := by
      unfold value; rw [testBit_zero_blk]
    have hfalse := hrefine
      (Nat.land (Nat.land (reach b K D) (blockSel K (fun ψ => Nat.beq ψ φ) b.length))
        (Nat.xor (full b.length K) (valMask b K)))
      (Nat.land (Nat.land (reach b K D) (blockSel K (fun ψ => Nat.beq ψ φ) b.length)) (valMask b K))
      (by
        show ((reach b K D &&& blockSel K (fun ψ => Nat.beq ψ φ) b.length) &&& (full b.length K ^^^ valMask b K)).testBit
          _ = true
        rw [Nat.testBit_and, Nat.testBit_and, Nat.testBit_xor, hJA, blockSel_testBit, full_testBit,
          valMask_testBit _ _ _ hgA, hdivA, hvalA, va, decide_eq_true hgA]
        simp)
      (by
        show ((reach b K D &&& blockSel K (fun ψ => Nat.beq ψ φ) b.length) &&& valMask b K).testBit _ = true
        rw [Nat.testBit_and, Nat.testBit_and, hJB, blockSel_testBit, valMask_testBit _ _ _ hgB, hdivB, hvalB, vb,
          decide_eq_true hgB]
        simp)
    have hφf : phaseCheck b K D rounds fuel φ = false := hfalse
    rw [hφc] at hφf
    exact Bool.noConfusion hφf
  -- one bound for every phase
  obtain ⟨N, hN⟩ := common_bound (fun φ N => ∀ t1 t2, N ≤ t1 → N ≤ t2 → phase t1 = φ → phase t2 = φ →
      value b φ (code t1) = value b φ (code t2))
    (fun φ N N' hle hR t1 t2 h1 h2 => hR t1 t2 (by omega) (by omega)) b.length hconst
  have hphase : ∀ t, phase (t + b.length) = phase t := fun t => by
    show (t + b.length + shift) % b.length = (t + shift) % b.length
    rw [show t + b.length + shift = t + shift + b.length by omega, Nat.add_mod_right]
  exact adjacent_columns init m hm hz (k - 1) (N + T) b.length hP
    (fun t ht => by
      rw [hleft (t + b.length) (by omega), hleft t (by omega), hphase t]
      exact hN (phase t) (Nat.mod_lt _ hP) _ _ (by omega) (by omega) (hphase t) rfl)
    (fun t ht => by
      rw [show k - 1 + 1 = k by omega, h (t + b.length) (by omega), h t (by omega)]
      unfold col
      rw [show t + b.length + shift = t + shift + b.length by omega, Nat.add_mod_right])

/-- **The center column does not repeat a block whose phases all pass `phaseCheck`**, from any time on and in any
phase. -/
theorem center_not_phases (b : List Bool) (K : Nat) (hK : 1 ≤ K) (hP : 1 ≤ b.length)
    (hall : ∀ φ, φ < b.length → ∃ D rounds fuel, phaseCheck b K D rounds fuel φ = true)
    (T shift : Nat) (h : ∀ t : Nat, T ≤ t → Rule30Prize.center t = b.getD ((t + shift) % b.length) false) : False :=
  phases_column single 0 rfl (fun x hx => decide_eq_false (by omega)) b K hK hP hall 0 T shift fun t ht => by
    rw [evolve_single_center, h t ht]
    unfold col
    rw [bit_eq_getD]

/-- The same in the kit's form `Rule30StripCertificates.EventuallyWord`. -/
theorem phases_not_eventuallyWord (b : List Bool) (K : Nat) (hK : 1 ≤ K) (hP : 1 ≤ b.length)
    (hall : ∀ φ, φ < b.length → ∃ D rounds fuel, phaseCheck b K D rounds fuel φ = true) :
    ¬ Rule30StripCertificates.EventuallyWord b := by
  rintro ⟨T, hT⟩
  refine center_not_phases b K hK hP hall T (b.length * T - T) fun t ht => ?_
  rw [← evolve_single_center, evolve_single_eq_cell]
  show Rule30Jen.cell t 0 = _
  have hLT : T ≤ b.length * T := Nat.le_mul_of_pos_left T hP
  rw [hT t ht, show t + (b.length * T - T) = t - T + b.length * T by omega, Nat.add_mul_mod_self_left]

/-- Every entry of a list of blocks with widths whose phases all pass excludes its block. -/
theorem center_not_phases_list (L : List ((Nat × Nat) × Nat))
    (hpos : ∀ e ∈ L, 1 ≤ e.2 ∧ 1 ≤ e.1.1)
    (hL : ∀ e ∈ L, ∀ φ, φ < e.1.1 → ∃ D rounds fuel,
      phaseCheck (Rule30StripCertificateTable.wordOf e.1.1 e.1.2) e.2 D rounds fuel φ = true)
    (e : (Nat × Nat) × Nat) (he : e ∈ L) (T shift : Nat)
    (h : ∀ t : Nat, T ≤ t → Rule30Prize.center t =
      (Rule30StripCertificateTable.wordOf e.1.1 e.1.2).getD ((t + shift) % e.1.1) false) : False := by
  have hlen := Rule30StripCertificateTable.wordOf_length e.1.1 e.1.2
  refine center_not_phases _ e.2 (hpos e he).1 (by rw [hlen]; exact (hpos e he).2)
    (fun φ hφ => hL e he φ (by rw [hlen] at hφ; exact hφ)) T shift fun t ht => ?_
  rw [h t ht, hlen]

/-- The same in the kit's form. -/
theorem phases_list_not_eventually (L : List ((Nat × Nat) × Nat))
    (hpos : ∀ e ∈ L, 1 ≤ e.2 ∧ 1 ≤ e.1.1)
    (hL : ∀ e ∈ L, ∀ φ, φ < e.1.1 → ∃ D rounds fuel,
      phaseCheck (Rule30StripCertificateTable.wordOf e.1.1 e.1.2) e.2 D rounds fuel φ = true)
    (e : (Nat × Nat) × Nat) (he : e ∈ L) :
    ¬ Rule30StripCertificates.EventuallyWord (Rule30StripCertificateTable.wordOf e.1.1 e.1.2) := by
  have hlen := Rule30StripCertificateTable.wordOf_length e.1.1 e.1.2
  exact phases_not_eventuallyWord _ e.2 (hpos e he).1 (by rw [hlen]; exact (hpos e he).2)
    (fun φ hφ => hL e he φ (by rw [hlen] at hφ; exact hφ))

open Rule30StripCertificateTable (wordOf)

set_option Elab.async false

set_option maxHeartbeats 0 in
theorem w00000000000101101_0 : phaseCheck (wordOf 17 0b00000000000101101) 13 0 1 300 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000101101_1 : phaseCheck (wordOf 17 0b00000000000101101) 13 0 1 300 1 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000101101_2 : phaseCheck (wordOf 17 0b00000000000101101) 13 0 4 300 2 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000101101_3 : phaseCheck (wordOf 17 0b00000000000101101) 13 0 1 300 3 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000101101_4 : phaseCheck (wordOf 17 0b00000000000101101) 13 0 1 300 4 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000101101_5 : phaseCheck (wordOf 17 0b00000000000101101) 13 0 1 300 5 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000101101_6 : phaseCheck (wordOf 17 0b00000000000101101) 13 0 1 300 6 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000101101_7 : phaseCheck (wordOf 17 0b00000000000101101) 13 0 1 300 7 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000101101_8 : phaseCheck (wordOf 17 0b00000000000101101) 13 0 1 300 8 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000101101_9 : phaseCheck (wordOf 17 0b00000000000101101) 13 0 1 300 9 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000101101_10 : phaseCheck (wordOf 17 0b00000000000101101) 13 0 1 300 10 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000101101_11 : phaseCheck (wordOf 17 0b00000000000101101) 13 0 0 300 11 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000101101_12 : phaseCheck (wordOf 17 0b00000000000101101) 13 0 1 300 12 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000101101_13 : phaseCheck (wordOf 17 0b00000000000101101) 13 0 0 300 13 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000101101_14 : phaseCheck (wordOf 17 0b00000000000101101) 13 0 0 300 14 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000101101_15 : phaseCheck (wordOf 17 0b00000000000101101) 13 0 2 300 15 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000101101_16 : phaseCheck (wordOf 17 0b00000000000101101) 13 0 0 300 16 = true := by
  decide +kernel

/-- Every phase of `00000000000101101` at width 13. -/
theorem w00000000000101101 : ∀ φ, φ < 17 → ∃ D rounds fuel,
    phaseCheck (wordOf 17 0b00000000000101101) 13 D rounds fuel φ = true
  | 0, _ => ⟨0, 1, 300, w00000000000101101_0⟩
  | 1, _ => ⟨0, 1, 300, w00000000000101101_1⟩
  | 2, _ => ⟨0, 4, 300, w00000000000101101_2⟩
  | 3, _ => ⟨0, 1, 300, w00000000000101101_3⟩
  | 4, _ => ⟨0, 1, 300, w00000000000101101_4⟩
  | 5, _ => ⟨0, 1, 300, w00000000000101101_5⟩
  | 6, _ => ⟨0, 1, 300, w00000000000101101_6⟩
  | 7, _ => ⟨0, 1, 300, w00000000000101101_7⟩
  | 8, _ => ⟨0, 1, 300, w00000000000101101_8⟩
  | 9, _ => ⟨0, 1, 300, w00000000000101101_9⟩
  | 10, _ => ⟨0, 1, 300, w00000000000101101_10⟩
  | 11, _ => ⟨0, 0, 300, w00000000000101101_11⟩
  | 12, _ => ⟨0, 1, 300, w00000000000101101_12⟩
  | 13, _ => ⟨0, 0, 300, w00000000000101101_13⟩
  | 14, _ => ⟨0, 0, 300, w00000000000101101_14⟩
  | 15, _ => ⟨0, 2, 300, w00000000000101101_15⟩
  | 16, _ => ⟨0, 0, 300, w00000000000101101_16⟩
  | _ + 17, h => absurd h (by omega)

set_option maxHeartbeats 0 in
theorem w00000000000111011_0 : phaseCheck (wordOf 17 0b00000000000111011) 14 0 1 300 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000111011_1 : phaseCheck (wordOf 17 0b00000000000111011) 14 0 2 300 1 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000111011_2 : phaseCheck (wordOf 17 0b00000000000111011) 14 0 3 300 2 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000111011_3 : phaseCheck (wordOf 17 0b00000000000111011) 14 0 3 300 3 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000111011_4 : phaseCheck (wordOf 17 0b00000000000111011) 14 0 1 300 4 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000111011_5 : phaseCheck (wordOf 17 0b00000000000111011) 14 0 1 300 5 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000111011_6 : phaseCheck (wordOf 17 0b00000000000111011) 14 0 1 300 6 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000111011_7 : phaseCheck (wordOf 17 0b00000000000111011) 14 0 1 300 7 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000111011_8 : phaseCheck (wordOf 17 0b00000000000111011) 14 0 1 300 8 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000111011_9 : phaseCheck (wordOf 17 0b00000000000111011) 14 0 1 300 9 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000111011_10 : phaseCheck (wordOf 17 0b00000000000111011) 14 0 1 300 10 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000111011_11 : phaseCheck (wordOf 17 0b00000000000111011) 14 0 0 300 11 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000111011_12 : phaseCheck (wordOf 17 0b00000000000111011) 14 0 0 300 12 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000111011_13 : phaseCheck (wordOf 17 0b00000000000111011) 14 0 0 300 13 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000111011_14 : phaseCheck (wordOf 17 0b00000000000111011) 14 0 1 300 14 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000111011_15 : phaseCheck (wordOf 17 0b00000000000111011) 14 0 0 300 15 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000111011_16 : phaseCheck (wordOf 17 0b00000000000111011) 14 0 0 300 16 = true := by
  decide +kernel

/-- Every phase of `00000000000111011` at width 14. -/
theorem w00000000000111011 : ∀ φ, φ < 17 → ∃ D rounds fuel,
    phaseCheck (wordOf 17 0b00000000000111011) 14 D rounds fuel φ = true
  | 0, _ => ⟨0, 1, 300, w00000000000111011_0⟩
  | 1, _ => ⟨0, 2, 300, w00000000000111011_1⟩
  | 2, _ => ⟨0, 3, 300, w00000000000111011_2⟩
  | 3, _ => ⟨0, 3, 300, w00000000000111011_3⟩
  | 4, _ => ⟨0, 1, 300, w00000000000111011_4⟩
  | 5, _ => ⟨0, 1, 300, w00000000000111011_5⟩
  | 6, _ => ⟨0, 1, 300, w00000000000111011_6⟩
  | 7, _ => ⟨0, 1, 300, w00000000000111011_7⟩
  | 8, _ => ⟨0, 1, 300, w00000000000111011_8⟩
  | 9, _ => ⟨0, 1, 300, w00000000000111011_9⟩
  | 10, _ => ⟨0, 1, 300, w00000000000111011_10⟩
  | 11, _ => ⟨0, 0, 300, w00000000000111011_11⟩
  | 12, _ => ⟨0, 0, 300, w00000000000111011_12⟩
  | 13, _ => ⟨0, 0, 300, w00000000000111011_13⟩
  | 14, _ => ⟨0, 1, 300, w00000000000111011_14⟩
  | 15, _ => ⟨0, 0, 300, w00000000000111011_15⟩
  | 16, _ => ⟨0, 0, 300, w00000000000111011_16⟩
  | _ + 17, h => absurd h (by omega)

set_option maxHeartbeats 0 in
theorem w00000000011011111_0 : phaseCheck (wordOf 17 0b00000000011011111) 13 0 1 300 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000011011111_1 : phaseCheck (wordOf 17 0b00000000011011111) 13 0 1 300 1 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000011011111_2 : phaseCheck (wordOf 17 0b00000000011011111) 13 0 1 300 2 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000011011111_3 : phaseCheck (wordOf 17 0b00000000011011111) 13 0 1 300 3 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000011011111_4 : phaseCheck (wordOf 17 0b00000000011011111) 13 0 1 300 4 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000011011111_5 : phaseCheck (wordOf 17 0b00000000011011111) 13 0 1 300 5 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000011011111_6 : phaseCheck (wordOf 17 0b00000000011011111) 13 0 1 300 6 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000011011111_7 : phaseCheck (wordOf 17 0b00000000011011111) 13 0 2 300 7 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000011011111_8 : phaseCheck (wordOf 17 0b00000000011011111) 13 0 2 300 8 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000011011111_9 : phaseCheck (wordOf 17 0b00000000011011111) 13 0 0 300 9 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000011011111_10 : phaseCheck (wordOf 17 0b00000000011011111) 13 0 0 300 10 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000011011111_11 : phaseCheck (wordOf 17 0b00000000011011111) 13 0 2 300 11 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000011011111_12 : phaseCheck (wordOf 17 0b00000000011011111) 13 0 0 300 12 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000011011111_13 : phaseCheck (wordOf 17 0b00000000011011111) 13 0 0 300 13 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000011011111_14 : phaseCheck (wordOf 17 0b00000000011011111) 13 0 0 300 14 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000011011111_15 : phaseCheck (wordOf 17 0b00000000011011111) 13 0 0 300 15 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000011011111_16 : phaseCheck (wordOf 17 0b00000000011011111) 13 0 0 300 16 = true := by
  decide +kernel

/-- Every phase of `00000000011011111` at width 13. -/
theorem w00000000011011111 : ∀ φ, φ < 17 → ∃ D rounds fuel,
    phaseCheck (wordOf 17 0b00000000011011111) 13 D rounds fuel φ = true
  | 0, _ => ⟨0, 1, 300, w00000000011011111_0⟩
  | 1, _ => ⟨0, 1, 300, w00000000011011111_1⟩
  | 2, _ => ⟨0, 1, 300, w00000000011011111_2⟩
  | 3, _ => ⟨0, 1, 300, w00000000011011111_3⟩
  | 4, _ => ⟨0, 1, 300, w00000000011011111_4⟩
  | 5, _ => ⟨0, 1, 300, w00000000011011111_5⟩
  | 6, _ => ⟨0, 1, 300, w00000000011011111_6⟩
  | 7, _ => ⟨0, 2, 300, w00000000011011111_7⟩
  | 8, _ => ⟨0, 2, 300, w00000000011011111_8⟩
  | 9, _ => ⟨0, 0, 300, w00000000011011111_9⟩
  | 10, _ => ⟨0, 0, 300, w00000000011011111_10⟩
  | 11, _ => ⟨0, 2, 300, w00000000011011111_11⟩
  | 12, _ => ⟨0, 0, 300, w00000000011011111_12⟩
  | 13, _ => ⟨0, 0, 300, w00000000011011111_13⟩
  | 14, _ => ⟨0, 0, 300, w00000000011011111_14⟩
  | 15, _ => ⟨0, 0, 300, w00000000011011111_15⟩
  | 16, _ => ⟨0, 0, 300, w00000000011011111_16⟩
  | _ + 17, h => absurd h (by omega)

set_option maxHeartbeats 0 in
theorem w00000000101110101_0 : phaseCheck (wordOf 17 0b00000000101110101) 13 0 1 300 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000101110101_1 : phaseCheck (wordOf 17 0b00000000101110101) 13 0 2 300 1 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000101110101_2 : phaseCheck (wordOf 17 0b00000000101110101) 13 0 2 300 2 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000101110101_3 : phaseCheck (wordOf 17 0b00000000101110101) 13 0 2 300 3 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000101110101_4 : phaseCheck (wordOf 17 0b00000000101110101) 13 0 2 300 4 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000101110101_5 : phaseCheck (wordOf 17 0b00000000101110101) 13 0 2 300 5 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000101110101_6 : phaseCheck (wordOf 17 0b00000000101110101) 13 0 1 300 6 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000101110101_7 : phaseCheck (wordOf 17 0b00000000101110101) 13 0 1 300 7 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000101110101_8 : phaseCheck (wordOf 17 0b00000000101110101) 13 0 0 300 8 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000101110101_9 : phaseCheck (wordOf 17 0b00000000101110101) 13 0 1 300 9 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000101110101_10 : phaseCheck (wordOf 17 0b00000000101110101) 13 0 0 300 10 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000101110101_11 : phaseCheck (wordOf 17 0b00000000101110101) 13 0 0 300 11 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000101110101_12 : phaseCheck (wordOf 17 0b00000000101110101) 13 0 0 300 12 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000101110101_13 : phaseCheck (wordOf 17 0b00000000101110101) 13 0 1 300 13 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000101110101_14 : phaseCheck (wordOf 17 0b00000000101110101) 13 0 0 300 14 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000101110101_15 : phaseCheck (wordOf 17 0b00000000101110101) 13 0 1 300 15 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000101110101_16 : phaseCheck (wordOf 17 0b00000000101110101) 13 0 0 300 16 = true := by
  decide +kernel

/-- Every phase of `00000000101110101` at width 13. -/
theorem w00000000101110101 : ∀ φ, φ < 17 → ∃ D rounds fuel,
    phaseCheck (wordOf 17 0b00000000101110101) 13 D rounds fuel φ = true
  | 0, _ => ⟨0, 1, 300, w00000000101110101_0⟩
  | 1, _ => ⟨0, 2, 300, w00000000101110101_1⟩
  | 2, _ => ⟨0, 2, 300, w00000000101110101_2⟩
  | 3, _ => ⟨0, 2, 300, w00000000101110101_3⟩
  | 4, _ => ⟨0, 2, 300, w00000000101110101_4⟩
  | 5, _ => ⟨0, 2, 300, w00000000101110101_5⟩
  | 6, _ => ⟨0, 1, 300, w00000000101110101_6⟩
  | 7, _ => ⟨0, 1, 300, w00000000101110101_7⟩
  | 8, _ => ⟨0, 0, 300, w00000000101110101_8⟩
  | 9, _ => ⟨0, 1, 300, w00000000101110101_9⟩
  | 10, _ => ⟨0, 0, 300, w00000000101110101_10⟩
  | 11, _ => ⟨0, 0, 300, w00000000101110101_11⟩
  | 12, _ => ⟨0, 0, 300, w00000000101110101_12⟩
  | 13, _ => ⟨0, 1, 300, w00000000101110101_13⟩
  | 14, _ => ⟨0, 0, 300, w00000000101110101_14⟩
  | 15, _ => ⟨0, 1, 300, w00000000101110101_15⟩
  | 16, _ => ⟨0, 0, 300, w00000000101110101_16⟩
  | _ + 17, h => absurd h (by omega)

set_option maxHeartbeats 0 in
theorem w00000000110110111_0 : phaseCheck (wordOf 17 0b00000000110110111) 13 0 1 300 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000110110111_1 : phaseCheck (wordOf 17 0b00000000110110111) 13 0 3 300 1 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000110110111_2 : phaseCheck (wordOf 17 0b00000000110110111) 13 0 3 300 2 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000110110111_3 : phaseCheck (wordOf 17 0b00000000110110111) 13 0 3 300 3 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000110110111_4 : phaseCheck (wordOf 17 0b00000000110110111) 13 0 1 300 4 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000110110111_5 : phaseCheck (wordOf 17 0b00000000110110111) 13 0 1 300 5 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000110110111_6 : phaseCheck (wordOf 17 0b00000000110110111) 13 0 1 300 6 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000110110111_7 : phaseCheck (wordOf 17 0b00000000110110111) 13 0 1 300 7 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000110110111_8 : phaseCheck (wordOf 17 0b00000000110110111) 13 0 0 300 8 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000110110111_9 : phaseCheck (wordOf 17 0b00000000110110111) 13 0 0 300 9 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000110110111_10 : phaseCheck (wordOf 17 0b00000000110110111) 13 0 3 300 10 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000110110111_11 : phaseCheck (wordOf 17 0b00000000110110111) 13 0 0 300 11 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000110110111_12 : phaseCheck (wordOf 17 0b00000000110110111) 13 0 0 300 12 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000110110111_13 : phaseCheck (wordOf 17 0b00000000110110111) 13 0 3 300 13 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000110110111_14 : phaseCheck (wordOf 17 0b00000000110110111) 13 0 0 300 14 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000110110111_15 : phaseCheck (wordOf 17 0b00000000110110111) 13 0 0 300 15 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000110110111_16 : phaseCheck (wordOf 17 0b00000000110110111) 13 0 0 300 16 = true := by
  decide +kernel

/-- Every phase of `00000000110110111` at width 13. -/
theorem w00000000110110111 : ∀ φ, φ < 17 → ∃ D rounds fuel,
    phaseCheck (wordOf 17 0b00000000110110111) 13 D rounds fuel φ = true
  | 0, _ => ⟨0, 1, 300, w00000000110110111_0⟩
  | 1, _ => ⟨0, 3, 300, w00000000110110111_1⟩
  | 2, _ => ⟨0, 3, 300, w00000000110110111_2⟩
  | 3, _ => ⟨0, 3, 300, w00000000110110111_3⟩
  | 4, _ => ⟨0, 1, 300, w00000000110110111_4⟩
  | 5, _ => ⟨0, 1, 300, w00000000110110111_5⟩
  | 6, _ => ⟨0, 1, 300, w00000000110110111_6⟩
  | 7, _ => ⟨0, 1, 300, w00000000110110111_7⟩
  | 8, _ => ⟨0, 0, 300, w00000000110110111_8⟩
  | 9, _ => ⟨0, 0, 300, w00000000110110111_9⟩
  | 10, _ => ⟨0, 3, 300, w00000000110110111_10⟩
  | 11, _ => ⟨0, 0, 300, w00000000110110111_11⟩
  | 12, _ => ⟨0, 0, 300, w00000000110110111_12⟩
  | 13, _ => ⟨0, 3, 300, w00000000110110111_13⟩
  | 14, _ => ⟨0, 0, 300, w00000000110110111_14⟩
  | 15, _ => ⟨0, 0, 300, w00000000110110111_15⟩
  | 16, _ => ⟨0, 0, 300, w00000000110110111_16⟩
  | _ + 17, h => absurd h (by omega)

set_option maxHeartbeats 0 in
theorem w00000001011111001_0 : phaseCheck (wordOf 17 0b00000001011111001) 14 0 1 300 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000001011111001_1 : phaseCheck (wordOf 17 0b00000001011111001) 14 0 2 300 1 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000001011111001_2 : phaseCheck (wordOf 17 0b00000001011111001) 14 0 1 300 2 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000001011111001_3 : phaseCheck (wordOf 17 0b00000001011111001) 14 0 1 300 3 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000001011111001_4 : phaseCheck (wordOf 17 0b00000001011111001) 14 0 1 300 4 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000001011111001_5 : phaseCheck (wordOf 17 0b00000001011111001) 14 0 1 300 5 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000001011111001_6 : phaseCheck (wordOf 17 0b00000001011111001) 14 0 1 300 6 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000001011111001_7 : phaseCheck (wordOf 17 0b00000001011111001) 14 0 0 300 7 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000001011111001_8 : phaseCheck (wordOf 17 0b00000001011111001) 14 0 1 300 8 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000001011111001_9 : phaseCheck (wordOf 17 0b00000001011111001) 14 0 0 300 9 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000001011111001_10 : phaseCheck (wordOf 17 0b00000001011111001) 14 0 0 300 10 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000001011111001_11 : phaseCheck (wordOf 17 0b00000001011111001) 14 0 0 300 11 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000001011111001_12 : phaseCheck (wordOf 17 0b00000001011111001) 14 0 0 300 12 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000001011111001_13 : phaseCheck (wordOf 17 0b00000001011111001) 14 0 0 300 13 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000001011111001_14 : phaseCheck (wordOf 17 0b00000001011111001) 14 0 1 300 14 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000001011111001_15 : phaseCheck (wordOf 17 0b00000001011111001) 14 0 1 300 15 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000001011111001_16 : phaseCheck (wordOf 17 0b00000001011111001) 14 0 0 300 16 = true := by
  decide +kernel

/-- Every phase of `00000001011111001` at width 14. -/
theorem w00000001011111001 : ∀ φ, φ < 17 → ∃ D rounds fuel,
    phaseCheck (wordOf 17 0b00000001011111001) 14 D rounds fuel φ = true
  | 0, _ => ⟨0, 1, 300, w00000001011111001_0⟩
  | 1, _ => ⟨0, 2, 300, w00000001011111001_1⟩
  | 2, _ => ⟨0, 1, 300, w00000001011111001_2⟩
  | 3, _ => ⟨0, 1, 300, w00000001011111001_3⟩
  | 4, _ => ⟨0, 1, 300, w00000001011111001_4⟩
  | 5, _ => ⟨0, 1, 300, w00000001011111001_5⟩
  | 6, _ => ⟨0, 1, 300, w00000001011111001_6⟩
  | 7, _ => ⟨0, 0, 300, w00000001011111001_7⟩
  | 8, _ => ⟨0, 1, 300, w00000001011111001_8⟩
  | 9, _ => ⟨0, 0, 300, w00000001011111001_9⟩
  | 10, _ => ⟨0, 0, 300, w00000001011111001_10⟩
  | 11, _ => ⟨0, 0, 300, w00000001011111001_11⟩
  | 12, _ => ⟨0, 0, 300, w00000001011111001_12⟩
  | 13, _ => ⟨0, 0, 300, w00000001011111001_13⟩
  | 14, _ => ⟨0, 1, 300, w00000001011111001_14⟩
  | 15, _ => ⟨0, 1, 300, w00000001011111001_15⟩
  | 16, _ => ⟨0, 0, 300, w00000001011111001_16⟩
  | _ + 17, h => absurd h (by omega)

set_option maxHeartbeats 0 in
theorem w00000010111101111_0 : phaseCheck (wordOf 17 0b00000010111101111) 13 0 3 300 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000010111101111_1 : phaseCheck (wordOf 17 0b00000010111101111) 13 0 1 300 1 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000010111101111_2 : phaseCheck (wordOf 17 0b00000010111101111) 13 0 1 300 2 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000010111101111_3 : phaseCheck (wordOf 17 0b00000010111101111) 13 0 1 300 3 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000010111101111_4 : phaseCheck (wordOf 17 0b00000010111101111) 13 0 1 300 4 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000010111101111_5 : phaseCheck (wordOf 17 0b00000010111101111) 13 0 1 300 5 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000010111101111_6 : phaseCheck (wordOf 17 0b00000010111101111) 13 0 0 300 6 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000010111101111_7 : phaseCheck (wordOf 17 0b00000010111101111) 13 0 1 300 7 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000010111101111_8 : phaseCheck (wordOf 17 0b00000010111101111) 13 0 0 300 8 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000010111101111_9 : phaseCheck (wordOf 17 0b00000010111101111) 13 0 0 300 9 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000010111101111_10 : phaseCheck (wordOf 17 0b00000010111101111) 13 0 0 300 10 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000010111101111_11 : phaseCheck (wordOf 17 0b00000010111101111) 13 0 0 300 11 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000010111101111_12 : phaseCheck (wordOf 17 0b00000010111101111) 13 0 2 300 12 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000010111101111_13 : phaseCheck (wordOf 17 0b00000010111101111) 13 0 0 300 13 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000010111101111_14 : phaseCheck (wordOf 17 0b00000010111101111) 13 0 0 300 14 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000010111101111_15 : phaseCheck (wordOf 17 0b00000010111101111) 13 0 0 300 15 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000010111101111_16 : phaseCheck (wordOf 17 0b00000010111101111) 13 0 0 300 16 = true := by
  decide +kernel

/-- Every phase of `00000010111101111` at width 13. -/
theorem w00000010111101111 : ∀ φ, φ < 17 → ∃ D rounds fuel,
    phaseCheck (wordOf 17 0b00000010111101111) 13 D rounds fuel φ = true
  | 0, _ => ⟨0, 3, 300, w00000010111101111_0⟩
  | 1, _ => ⟨0, 1, 300, w00000010111101111_1⟩
  | 2, _ => ⟨0, 1, 300, w00000010111101111_2⟩
  | 3, _ => ⟨0, 1, 300, w00000010111101111_3⟩
  | 4, _ => ⟨0, 1, 300, w00000010111101111_4⟩
  | 5, _ => ⟨0, 1, 300, w00000010111101111_5⟩
  | 6, _ => ⟨0, 0, 300, w00000010111101111_6⟩
  | 7, _ => ⟨0, 1, 300, w00000010111101111_7⟩
  | 8, _ => ⟨0, 0, 300, w00000010111101111_8⟩
  | 9, _ => ⟨0, 0, 300, w00000010111101111_9⟩
  | 10, _ => ⟨0, 0, 300, w00000010111101111_10⟩
  | 11, _ => ⟨0, 0, 300, w00000010111101111_11⟩
  | 12, _ => ⟨0, 2, 300, w00000010111101111_12⟩
  | 13, _ => ⟨0, 0, 300, w00000010111101111_13⟩
  | 14, _ => ⟨0, 0, 300, w00000010111101111_14⟩
  | 15, _ => ⟨0, 0, 300, w00000010111101111_15⟩
  | 16, _ => ⟨0, 0, 300, w00000010111101111_16⟩
  | _ + 17, h => absurd h (by omega)

set_option maxHeartbeats 0 in
theorem w00111001111111101_0 : phaseCheck (wordOf 17 0b00111001111111101) 13 0 1 300 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00111001111111101_1 : phaseCheck (wordOf 17 0b00111001111111101) 13 0 1 300 1 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00111001111111101_2 : phaseCheck (wordOf 17 0b00111001111111101) 13 0 0 300 2 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00111001111111101_3 : phaseCheck (wordOf 17 0b00111001111111101) 13 0 0 300 3 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00111001111111101_4 : phaseCheck (wordOf 17 0b00111001111111101) 13 0 0 300 4 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00111001111111101_5 : phaseCheck (wordOf 17 0b00111001111111101) 13 0 4 300 5 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00111001111111101_6 : phaseCheck (wordOf 17 0b00111001111111101) 13 0 4 300 6 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00111001111111101_7 : phaseCheck (wordOf 17 0b00111001111111101) 13 0 0 300 7 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00111001111111101_8 : phaseCheck (wordOf 17 0b00111001111111101) 13 0 0 300 8 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00111001111111101_9 : phaseCheck (wordOf 17 0b00111001111111101) 13 0 0 300 9 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00111001111111101_10 : phaseCheck (wordOf 17 0b00111001111111101) 13 0 0 300 10 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00111001111111101_11 : phaseCheck (wordOf 17 0b00111001111111101) 13 0 0 300 11 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00111001111111101_12 : phaseCheck (wordOf 17 0b00111001111111101) 13 0 0 300 12 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00111001111111101_13 : phaseCheck (wordOf 17 0b00111001111111101) 13 0 0 300 13 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00111001111111101_14 : phaseCheck (wordOf 17 0b00111001111111101) 13 0 0 300 14 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00111001111111101_15 : phaseCheck (wordOf 17 0b00111001111111101) 13 0 4 300 15 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00111001111111101_16 : phaseCheck (wordOf 17 0b00111001111111101) 13 0 0 300 16 = true := by
  decide +kernel

/-- Every phase of `00111001111111101` at width 13. -/
theorem w00111001111111101 : ∀ φ, φ < 17 → ∃ D rounds fuel,
    phaseCheck (wordOf 17 0b00111001111111101) 13 D rounds fuel φ = true
  | 0, _ => ⟨0, 1, 300, w00111001111111101_0⟩
  | 1, _ => ⟨0, 1, 300, w00111001111111101_1⟩
  | 2, _ => ⟨0, 0, 300, w00111001111111101_2⟩
  | 3, _ => ⟨0, 0, 300, w00111001111111101_3⟩
  | 4, _ => ⟨0, 0, 300, w00111001111111101_4⟩
  | 5, _ => ⟨0, 4, 300, w00111001111111101_5⟩
  | 6, _ => ⟨0, 4, 300, w00111001111111101_6⟩
  | 7, _ => ⟨0, 0, 300, w00111001111111101_7⟩
  | 8, _ => ⟨0, 0, 300, w00111001111111101_8⟩
  | 9, _ => ⟨0, 0, 300, w00111001111111101_9⟩
  | 10, _ => ⟨0, 0, 300, w00111001111111101_10⟩
  | 11, _ => ⟨0, 0, 300, w00111001111111101_11⟩
  | 12, _ => ⟨0, 0, 300, w00111001111111101_12⟩
  | 13, _ => ⟨0, 0, 300, w00111001111111101_13⟩
  | 14, _ => ⟨0, 0, 300, w00111001111111101_14⟩
  | 15, _ => ⟨0, 4, 300, w00111001111111101_15⟩
  | 16, _ => ⟨0, 0, 300, w00111001111111101_16⟩
  | _ + 17, h => absurd h (by omega)

set_option maxHeartbeats 0 in
theorem w000000000000000111_0 : phaseCheck (wordOf 18 0b000000000000000111) 14 0 1 300 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000000111_1 : phaseCheck (wordOf 18 0b000000000000000111) 14 0 1 300 1 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000000111_2 : phaseCheck (wordOf 18 0b000000000000000111) 14 0 2 300 2 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000000111_3 : phaseCheck (wordOf 18 0b000000000000000111) 14 0 2 300 3 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000000111_4 : phaseCheck (wordOf 18 0b000000000000000111) 14 0 2 300 4 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000000111_5 : phaseCheck (wordOf 18 0b000000000000000111) 14 0 2 300 5 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000000111_6 : phaseCheck (wordOf 18 0b000000000000000111) 14 0 3 300 6 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000000111_7 : phaseCheck (wordOf 18 0b000000000000000111) 14 0 2 300 7 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000000111_8 : phaseCheck (wordOf 18 0b000000000000000111) 14 0 2 300 8 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000000111_9 : phaseCheck (wordOf 18 0b000000000000000111) 14 0 2 300 9 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000000111_10 : phaseCheck (wordOf 18 0b000000000000000111) 14 0 1 300 10 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000000111_11 : phaseCheck (wordOf 18 0b000000000000000111) 14 0 1 300 11 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000000111_12 : phaseCheck (wordOf 18 0b000000000000000111) 14 0 1 300 12 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000000111_13 : phaseCheck (wordOf 18 0b000000000000000111) 14 0 1 300 13 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000000111_14 : phaseCheck (wordOf 18 0b000000000000000111) 14 0 1 300 14 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000000111_15 : phaseCheck (wordOf 18 0b000000000000000111) 14 0 0 300 15 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000000111_16 : phaseCheck (wordOf 18 0b000000000000000111) 14 0 0 300 16 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000000111_17 : phaseCheck (wordOf 18 0b000000000000000111) 14 0 0 300 17 = true := by
  decide +kernel

/-- Every phase of `000000000000000111` at width 14. -/
theorem w000000000000000111 : ∀ φ, φ < 18 → ∃ D rounds fuel,
    phaseCheck (wordOf 18 0b000000000000000111) 14 D rounds fuel φ = true
  | 0, _ => ⟨0, 1, 300, w000000000000000111_0⟩
  | 1, _ => ⟨0, 1, 300, w000000000000000111_1⟩
  | 2, _ => ⟨0, 2, 300, w000000000000000111_2⟩
  | 3, _ => ⟨0, 2, 300, w000000000000000111_3⟩
  | 4, _ => ⟨0, 2, 300, w000000000000000111_4⟩
  | 5, _ => ⟨0, 2, 300, w000000000000000111_5⟩
  | 6, _ => ⟨0, 3, 300, w000000000000000111_6⟩
  | 7, _ => ⟨0, 2, 300, w000000000000000111_7⟩
  | 8, _ => ⟨0, 2, 300, w000000000000000111_8⟩
  | 9, _ => ⟨0, 2, 300, w000000000000000111_9⟩
  | 10, _ => ⟨0, 1, 300, w000000000000000111_10⟩
  | 11, _ => ⟨0, 1, 300, w000000000000000111_11⟩
  | 12, _ => ⟨0, 1, 300, w000000000000000111_12⟩
  | 13, _ => ⟨0, 1, 300, w000000000000000111_13⟩
  | 14, _ => ⟨0, 1, 300, w000000000000000111_14⟩
  | 15, _ => ⟨0, 0, 300, w000000000000000111_15⟩
  | 16, _ => ⟨0, 0, 300, w000000000000000111_16⟩
  | 17, _ => ⟨0, 0, 300, w000000000000000111_17⟩
  | _ + 18, h => absurd h (by omega)

set_option maxHeartbeats 0 in
theorem w000000000010000101_0 : phaseCheck (wordOf 18 0b000000000010000101) 13 0 1 300 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000010000101_1 : phaseCheck (wordOf 18 0b000000000010000101) 13 0 1 300 1 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000010000101_2 : phaseCheck (wordOf 18 0b000000000010000101) 13 0 1 300 2 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000010000101_3 : phaseCheck (wordOf 18 0b000000000010000101) 13 0 1 300 3 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000010000101_4 : phaseCheck (wordOf 18 0b000000000010000101) 13 0 1 300 4 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000010000101_5 : phaseCheck (wordOf 18 0b000000000010000101) 13 0 1 300 5 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000010000101_6 : phaseCheck (wordOf 18 0b000000000010000101) 13 0 1 300 6 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000010000101_7 : phaseCheck (wordOf 18 0b000000000010000101) 13 0 1 300 7 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000010000101_8 : phaseCheck (wordOf 18 0b000000000010000101) 13 0 1 300 8 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000010000101_9 : phaseCheck (wordOf 18 0b000000000010000101) 13 0 1 300 9 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000010000101_10 : phaseCheck (wordOf 18 0b000000000010000101) 13 0 0 300 10 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000010000101_11 : phaseCheck (wordOf 18 0b000000000010000101) 13 0 1 300 11 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000010000101_12 : phaseCheck (wordOf 18 0b000000000010000101) 13 0 1 300 12 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000010000101_13 : phaseCheck (wordOf 18 0b000000000010000101) 13 0 1 300 13 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000010000101_14 : phaseCheck (wordOf 18 0b000000000010000101) 13 0 1 300 14 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000010000101_15 : phaseCheck (wordOf 18 0b000000000010000101) 13 0 0 300 15 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000010000101_16 : phaseCheck (wordOf 18 0b000000000010000101) 13 0 1 300 16 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000010000101_17 : phaseCheck (wordOf 18 0b000000000010000101) 13 0 0 300 17 = true := by
  decide +kernel

/-- Every phase of `000000000010000101` at width 13. -/
theorem w000000000010000101 : ∀ φ, φ < 18 → ∃ D rounds fuel,
    phaseCheck (wordOf 18 0b000000000010000101) 13 D rounds fuel φ = true
  | 0, _ => ⟨0, 1, 300, w000000000010000101_0⟩
  | 1, _ => ⟨0, 1, 300, w000000000010000101_1⟩
  | 2, _ => ⟨0, 1, 300, w000000000010000101_2⟩
  | 3, _ => ⟨0, 1, 300, w000000000010000101_3⟩
  | 4, _ => ⟨0, 1, 300, w000000000010000101_4⟩
  | 5, _ => ⟨0, 1, 300, w000000000010000101_5⟩
  | 6, _ => ⟨0, 1, 300, w000000000010000101_6⟩
  | 7, _ => ⟨0, 1, 300, w000000000010000101_7⟩
  | 8, _ => ⟨0, 1, 300, w000000000010000101_8⟩
  | 9, _ => ⟨0, 1, 300, w000000000010000101_9⟩
  | 10, _ => ⟨0, 0, 300, w000000000010000101_10⟩
  | 11, _ => ⟨0, 1, 300, w000000000010000101_11⟩
  | 12, _ => ⟨0, 1, 300, w000000000010000101_12⟩
  | 13, _ => ⟨0, 1, 300, w000000000010000101_13⟩
  | 14, _ => ⟨0, 1, 300, w000000000010000101_14⟩
  | 15, _ => ⟨0, 0, 300, w000000000010000101_15⟩
  | 16, _ => ⟨0, 1, 300, w000000000010000101_16⟩
  | 17, _ => ⟨0, 0, 300, w000000000010000101_17⟩
  | _ + 18, h => absurd h (by omega)

set_option maxHeartbeats 0 in
theorem w000000000010010001_0 : phaseCheck (wordOf 18 0b000000000010010001) 14 0 1 300 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000010010001_1 : phaseCheck (wordOf 18 0b000000000010010001) 14 0 1 300 1 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000010010001_2 : phaseCheck (wordOf 18 0b000000000010010001) 14 0 2 300 2 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000010010001_3 : phaseCheck (wordOf 18 0b000000000010010001) 14 0 1 300 3 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000010010001_4 : phaseCheck (wordOf 18 0b000000000010010001) 14 0 1 300 4 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000010010001_5 : phaseCheck (wordOf 18 0b000000000010010001) 14 0 1 300 5 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000010010001_6 : phaseCheck (wordOf 18 0b000000000010010001) 14 0 1 300 6 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000010010001_7 : phaseCheck (wordOf 18 0b000000000010010001) 14 0 1 300 7 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000010010001_8 : phaseCheck (wordOf 18 0b000000000010010001) 14 0 1 300 8 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000010010001_9 : phaseCheck (wordOf 18 0b000000000010010001) 14 0 1 300 9 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000010010001_10 : phaseCheck (wordOf 18 0b000000000010010001) 14 0 0 300 10 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000010010001_11 : phaseCheck (wordOf 18 0b000000000010010001) 14 0 1 300 11 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000010010001_12 : phaseCheck (wordOf 18 0b000000000010010001) 14 0 3 300 12 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000010010001_13 : phaseCheck (wordOf 18 0b000000000010010001) 14 0 0 300 13 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000010010001_14 : phaseCheck (wordOf 18 0b000000000010010001) 14 0 1 300 14 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000010010001_15 : phaseCheck (wordOf 18 0b000000000010010001) 14 0 3 300 15 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000010010001_16 : phaseCheck (wordOf 18 0b000000000010010001) 14 0 2 300 16 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000010010001_17 : phaseCheck (wordOf 18 0b000000000010010001) 14 0 0 300 17 = true := by
  decide +kernel

/-- Every phase of `000000000010010001` at width 14. -/
theorem w000000000010010001 : ∀ φ, φ < 18 → ∃ D rounds fuel,
    phaseCheck (wordOf 18 0b000000000010010001) 14 D rounds fuel φ = true
  | 0, _ => ⟨0, 1, 300, w000000000010010001_0⟩
  | 1, _ => ⟨0, 1, 300, w000000000010010001_1⟩
  | 2, _ => ⟨0, 2, 300, w000000000010010001_2⟩
  | 3, _ => ⟨0, 1, 300, w000000000010010001_3⟩
  | 4, _ => ⟨0, 1, 300, w000000000010010001_4⟩
  | 5, _ => ⟨0, 1, 300, w000000000010010001_5⟩
  | 6, _ => ⟨0, 1, 300, w000000000010010001_6⟩
  | 7, _ => ⟨0, 1, 300, w000000000010010001_7⟩
  | 8, _ => ⟨0, 1, 300, w000000000010010001_8⟩
  | 9, _ => ⟨0, 1, 300, w000000000010010001_9⟩
  | 10, _ => ⟨0, 0, 300, w000000000010010001_10⟩
  | 11, _ => ⟨0, 1, 300, w000000000010010001_11⟩
  | 12, _ => ⟨0, 3, 300, w000000000010010001_12⟩
  | 13, _ => ⟨0, 0, 300, w000000000010010001_13⟩
  | 14, _ => ⟨0, 1, 300, w000000000010010001_14⟩
  | 15, _ => ⟨0, 3, 300, w000000000010010001_15⟩
  | 16, _ => ⟨0, 2, 300, w000000000010010001_16⟩
  | 17, _ => ⟨0, 0, 300, w000000000010010001_17⟩
  | _ + 18, h => absurd h (by omega)

set_option maxHeartbeats 0 in
theorem w000001011111111001_0 : phaseCheck (wordOf 18 0b000001011111111001) 14 0 1 300 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000001011111111001_1 : phaseCheck (wordOf 18 0b000001011111111001) 14 0 2 300 1 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000001011111111001_2 : phaseCheck (wordOf 18 0b000001011111111001) 14 0 1 300 2 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000001011111111001_3 : phaseCheck (wordOf 18 0b000001011111111001) 14 0 1 300 3 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000001011111111001_4 : phaseCheck (wordOf 18 0b000001011111111001) 14 0 1 300 4 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000001011111111001_5 : phaseCheck (wordOf 18 0b000001011111111001) 14 0 0 300 5 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000001011111111001_6 : phaseCheck (wordOf 18 0b000001011111111001) 14 0 1 300 6 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000001011111111001_7 : phaseCheck (wordOf 18 0b000001011111111001) 14 0 0 300 7 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000001011111111001_8 : phaseCheck (wordOf 18 0b000001011111111001) 14 0 0 300 8 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000001011111111001_9 : phaseCheck (wordOf 18 0b000001011111111001) 14 0 0 300 9 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000001011111111001_10 : phaseCheck (wordOf 18 0b000001011111111001) 14 0 0 300 10 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000001011111111001_11 : phaseCheck (wordOf 18 0b000001011111111001) 14 0 0 300 11 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000001011111111001_12 : phaseCheck (wordOf 18 0b000001011111111001) 14 0 0 300 12 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000001011111111001_13 : phaseCheck (wordOf 18 0b000001011111111001) 14 0 0 300 13 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000001011111111001_14 : phaseCheck (wordOf 18 0b000001011111111001) 14 0 0 300 14 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000001011111111001_15 : phaseCheck (wordOf 18 0b000001011111111001) 14 0 1 300 15 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000001011111111001_16 : phaseCheck (wordOf 18 0b000001011111111001) 14 0 1 300 16 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000001011111111001_17 : phaseCheck (wordOf 18 0b000001011111111001) 14 0 0 300 17 = true := by
  decide +kernel

/-- Every phase of `000001011111111001` at width 14. -/
theorem w000001011111111001 : ∀ φ, φ < 18 → ∃ D rounds fuel,
    phaseCheck (wordOf 18 0b000001011111111001) 14 D rounds fuel φ = true
  | 0, _ => ⟨0, 1, 300, w000001011111111001_0⟩
  | 1, _ => ⟨0, 2, 300, w000001011111111001_1⟩
  | 2, _ => ⟨0, 1, 300, w000001011111111001_2⟩
  | 3, _ => ⟨0, 1, 300, w000001011111111001_3⟩
  | 4, _ => ⟨0, 1, 300, w000001011111111001_4⟩
  | 5, _ => ⟨0, 0, 300, w000001011111111001_5⟩
  | 6, _ => ⟨0, 1, 300, w000001011111111001_6⟩
  | 7, _ => ⟨0, 0, 300, w000001011111111001_7⟩
  | 8, _ => ⟨0, 0, 300, w000001011111111001_8⟩
  | 9, _ => ⟨0, 0, 300, w000001011111111001_9⟩
  | 10, _ => ⟨0, 0, 300, w000001011111111001_10⟩
  | 11, _ => ⟨0, 0, 300, w000001011111111001_11⟩
  | 12, _ => ⟨0, 0, 300, w000001011111111001_12⟩
  | 13, _ => ⟨0, 0, 300, w000001011111111001_13⟩
  | 14, _ => ⟨0, 0, 300, w000001011111111001_14⟩
  | 15, _ => ⟨0, 1, 300, w000001011111111001_15⟩
  | 16, _ => ⟨0, 1, 300, w000001011111111001_16⟩
  | 17, _ => ⟨0, 0, 300, w000001011111111001_17⟩
  | _ + 18, h => absurd h (by omega)

set_option maxHeartbeats 0 in
theorem w000010111111110111_0 : phaseCheck (wordOf 18 0b000010111111110111) 14 0 1 300 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000010111111110111_1 : phaseCheck (wordOf 18 0b000010111111110111) 14 0 4 300 1 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000010111111110111_2 : phaseCheck (wordOf 18 0b000010111111110111) 14 0 3 300 2 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000010111111110111_3 : phaseCheck (wordOf 18 0b000010111111110111) 14 0 2 300 3 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000010111111110111_4 : phaseCheck (wordOf 18 0b000010111111110111) 14 0 0 300 4 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000010111111110111_5 : phaseCheck (wordOf 18 0b000010111111110111) 14 0 2 300 5 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000010111111110111_6 : phaseCheck (wordOf 18 0b000010111111110111) 14 0 0 300 6 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000010111111110111_7 : phaseCheck (wordOf 18 0b000010111111110111) 14 0 0 300 7 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000010111111110111_8 : phaseCheck (wordOf 18 0b000010111111110111) 14 0 0 300 8 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000010111111110111_9 : phaseCheck (wordOf 18 0b000010111111110111) 14 0 0 300 9 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000010111111110111_10 : phaseCheck (wordOf 18 0b000010111111110111) 14 0 0 300 10 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000010111111110111_11 : phaseCheck (wordOf 18 0b000010111111110111) 14 0 0 300 11 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000010111111110111_12 : phaseCheck (wordOf 18 0b000010111111110111) 14 0 0 300 12 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000010111111110111_13 : phaseCheck (wordOf 18 0b000010111111110111) 14 0 0 300 13 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000010111111110111_14 : phaseCheck (wordOf 18 0b000010111111110111) 14 0 2 300 14 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000010111111110111_15 : phaseCheck (wordOf 18 0b000010111111110111) 14 0 0 300 15 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000010111111110111_16 : phaseCheck (wordOf 18 0b000010111111110111) 14 0 0 300 16 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000010111111110111_17 : phaseCheck (wordOf 18 0b000010111111110111) 14 0 0 300 17 = true := by
  decide +kernel

/-- Every phase of `000010111111110111` at width 14. -/
theorem w000010111111110111 : ∀ φ, φ < 18 → ∃ D rounds fuel,
    phaseCheck (wordOf 18 0b000010111111110111) 14 D rounds fuel φ = true
  | 0, _ => ⟨0, 1, 300, w000010111111110111_0⟩
  | 1, _ => ⟨0, 4, 300, w000010111111110111_1⟩
  | 2, _ => ⟨0, 3, 300, w000010111111110111_2⟩
  | 3, _ => ⟨0, 2, 300, w000010111111110111_3⟩
  | 4, _ => ⟨0, 0, 300, w000010111111110111_4⟩
  | 5, _ => ⟨0, 2, 300, w000010111111110111_5⟩
  | 6, _ => ⟨0, 0, 300, w000010111111110111_6⟩
  | 7, _ => ⟨0, 0, 300, w000010111111110111_7⟩
  | 8, _ => ⟨0, 0, 300, w000010111111110111_8⟩
  | 9, _ => ⟨0, 0, 300, w000010111111110111_9⟩
  | 10, _ => ⟨0, 0, 300, w000010111111110111_10⟩
  | 11, _ => ⟨0, 0, 300, w000010111111110111_11⟩
  | 12, _ => ⟨0, 0, 300, w000010111111110111_12⟩
  | 13, _ => ⟨0, 0, 300, w000010111111110111_13⟩
  | 14, _ => ⟨0, 2, 300, w000010111111110111_14⟩
  | 15, _ => ⟨0, 0, 300, w000010111111110111_15⟩
  | 16, _ => ⟨0, 0, 300, w000010111111110111_16⟩
  | 17, _ => ⟨0, 0, 300, w000010111111110111_17⟩
  | _ + 18, h => absurd h (by omega)

set_option maxHeartbeats 0 in
theorem w000101111111111001_0 : phaseCheck (wordOf 18 0b000101111111111001) 13 0 1 300 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000101111111111001_1 : phaseCheck (wordOf 18 0b000101111111111001) 13 0 3 300 1 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000101111111111001_2 : phaseCheck (wordOf 18 0b000101111111111001) 13 0 1 300 2 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000101111111111001_3 : phaseCheck (wordOf 18 0b000101111111111001) 13 0 0 300 3 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000101111111111001_4 : phaseCheck (wordOf 18 0b000101111111111001) 13 0 1 300 4 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000101111111111001_5 : phaseCheck (wordOf 18 0b000101111111111001) 13 0 0 300 5 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000101111111111001_6 : phaseCheck (wordOf 18 0b000101111111111001) 13 0 0 300 6 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000101111111111001_7 : phaseCheck (wordOf 18 0b000101111111111001) 13 0 0 300 7 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000101111111111001_8 : phaseCheck (wordOf 18 0b000101111111111001) 13 0 0 300 8 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000101111111111001_9 : phaseCheck (wordOf 18 0b000101111111111001) 13 0 0 300 9 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000101111111111001_10 : phaseCheck (wordOf 18 0b000101111111111001) 13 0 0 300 10 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000101111111111001_11 : phaseCheck (wordOf 18 0b000101111111111001) 13 0 0 300 11 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000101111111111001_12 : phaseCheck (wordOf 18 0b000101111111111001) 13 0 0 300 12 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000101111111111001_13 : phaseCheck (wordOf 18 0b000101111111111001) 13 0 0 300 13 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000101111111111001_14 : phaseCheck (wordOf 18 0b000101111111111001) 13 0 0 300 14 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000101111111111001_15 : phaseCheck (wordOf 18 0b000101111111111001) 13 0 1 300 15 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000101111111111001_16 : phaseCheck (wordOf 18 0b000101111111111001) 13 0 1 300 16 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000101111111111001_17 : phaseCheck (wordOf 18 0b000101111111111001) 13 0 0 300 17 = true := by
  decide +kernel

/-- Every phase of `000101111111111001` at width 13. -/
theorem w000101111111111001 : ∀ φ, φ < 18 → ∃ D rounds fuel,
    phaseCheck (wordOf 18 0b000101111111111001) 13 D rounds fuel φ = true
  | 0, _ => ⟨0, 1, 300, w000101111111111001_0⟩
  | 1, _ => ⟨0, 3, 300, w000101111111111001_1⟩
  | 2, _ => ⟨0, 1, 300, w000101111111111001_2⟩
  | 3, _ => ⟨0, 0, 300, w000101111111111001_3⟩
  | 4, _ => ⟨0, 1, 300, w000101111111111001_4⟩
  | 5, _ => ⟨0, 0, 300, w000101111111111001_5⟩
  | 6, _ => ⟨0, 0, 300, w000101111111111001_6⟩
  | 7, _ => ⟨0, 0, 300, w000101111111111001_7⟩
  | 8, _ => ⟨0, 0, 300, w000101111111111001_8⟩
  | 9, _ => ⟨0, 0, 300, w000101111111111001_9⟩
  | 10, _ => ⟨0, 0, 300, w000101111111111001_10⟩
  | 11, _ => ⟨0, 0, 300, w000101111111111001_11⟩
  | 12, _ => ⟨0, 0, 300, w000101111111111001_12⟩
  | 13, _ => ⟨0, 0, 300, w000101111111111001_13⟩
  | 14, _ => ⟨0, 0, 300, w000101111111111001_14⟩
  | 15, _ => ⟨0, 1, 300, w000101111111111001_15⟩
  | 16, _ => ⟨0, 1, 300, w000101111111111001_16⟩
  | 17, _ => ⟨0, 0, 300, w000101111111111001_17⟩
  | _ + 18, h => absurd h (by omega)

/-- The blocks of this module, each as its least rotation `wordOf n bits`, with the width of its checks. -/
def blocksPhases18 : List ((Nat × Nat) × Nat) := [
    ((17, 0b00000000000101101), 13), ((17, 0b00000000000111011), 14), ((17, 0b00000000011011111), 13),
    ((17, 0b00000000101110101), 13), ((17, 0b00000000110110111), 13), ((17, 0b00000001011111001), 14),
    ((17, 0b00000010111101111), 13), ((17, 0b00111001111111101), 13), ((18, 0b000000000000000111), 14),
    ((18, 0b000000000010000101), 13), ((18, 0b000000000010010001), 14), ((18, 0b000001011111111001), 14),
    ((18, 0b000010111111110111), 14), ((18, 0b000101111111111001), 13)]

theorem blocksPhases18_phases : ∀ e ∈ blocksPhases18, ∀ φ, φ < e.1.1 → ∃ D rounds fuel,
    phaseCheck (wordOf e.1.1 e.1.2) e.2 D rounds fuel φ = true := by
  intro e he
  simp only [blocksPhases18, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact w00000000000101101
  · exact w00000000000111011
  · exact w00000000011011111
  · exact w00000000101110101
  · exact w00000000110110111
  · exact w00000001011111001
  · exact w00000010111101111
  · exact w00111001111111101
  · exact w000000000000000111
  · exact w000000000010000101
  · exact w000000000010010001
  · exact w000001011111111001
  · exact w000010111111110111
  · exact w000101111111111001

theorem blocksPhases18_pos : ∀ e ∈ blocksPhases18, 1 ≤ e.2 ∧ 1 ≤ e.1.1 := by decide

/-- **The center column does not eventually repeat any of the 14 blocks of `blocksPhases18`**, from any time on
and in any rotation. -/
theorem center_not_blocksPhases18 (e : (Nat × Nat) × Nat) (he : e ∈ blocksPhases18) (T shift : Nat)
    (h : ∀ t : Nat, T ≤ t → Rule30Prize.center t = (wordOf e.1.1 e.1.2).getD ((t + shift) % e.1.1) false) :
    False :=
  center_not_phases_list blocksPhases18 blocksPhases18_pos blocksPhases18_phases e he T shift h

/-- The same in the kit's form `Rule30StripCertificates.EventuallyWord`. -/
theorem not_eventually_blocksPhases18 (e : (Nat × Nat) × Nat) (he : e ∈ blocksPhases18) :
    ¬ Rule30StripCertificates.EventuallyWord (wordOf e.1.1 e.1.2) :=
  phases_list_not_eventually blocksPhases18 blocksPhases18_pos blocksPhases18_phases e he

end Rule30Open
