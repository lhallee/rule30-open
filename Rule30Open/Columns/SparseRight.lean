module

public import Rule30Open.Columns.WhiteGap

/-!
# Sparse right halves: absorption for every right half with at most two black cells among its first cells

The kit proves that one black cell, anywhere, enters the ether-and-wall family under `0001`
(`Rule30EtherSingleCell.singleCell_absorption`). Here the same holds for every right half that has at most two black
cells among the cells `1 .. G`, whatever lies beyond `G`, for each of the three words of least period four, with
`G = 778` for `0001`, `1359` for `0011` and `623` for `0111` (`sparse_0001`, `sparse_0011`, `sparse_0111`). So no
finite configuration whose right half has at most two black cells among those cells has a center column that repeats
the word, whatever its left half (`sparseRight_0001`, `sparseRight_0011`, `sparseRight_0111`). In particular one black
cell, anywhere, enters under each word (`oneCell_0011`, `oneCell_0111`).

A half white on cells `1 .. 30` enters (`WhiteGap.high_*`). Otherwise its first black cell `p1` is at most 30, and the
half `{p1}` enters at a step `t` and depth `k` that a kernel computation lists; by the light cone so does every half
whose second black cell lies beyond `t + k + 13`. Otherwise the second black cell `p2` is at most `t + k + 13`, and
the half `{p1, p2}` enters at its own listed step `t'` and depth `k'` with `t' + k' + 13 ≤ G`, so every half that agrees
with it on the cells `1 .. G` enters too (`two_absorption`). The kernel replays the 360 halves of one cell and the
23,509 halves of two cells (`cells0001_0_ok` and the eleven others). It steps the packed half four steps at a time
(`quads`, `stateAt_eq`) and reads the family off bit masks (`fastFamily`, `inFamily_of_fast`).

The natural-language argument is `SparseRight.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

open Ruliology.CellularAutomata
open Rule30Realization Rule30Ether Rule30StripCertificates Rule30PeriodTwoSideways

/-! ### The driven half, four steps at a time -/

/-- One step of the packed right half `r` (bit `i` is column `i + 1`) beside the center bit `c`: the kit's
`Rule30EtherThree.stepN`, written with the operations that the kernel computes on numerals. -/
def stepK (c r : Nat) : Nat :=
  Nat.xor (Nat.lor c (Nat.shiftLeft r 1))
    (Nat.lor (Nat.shiftRight (Nat.lor c (Nat.shiftLeft r 1)) 1) (Nat.shiftRight (Nat.lor c (Nat.shiftLeft r 1)) 2))

theorem stepK_toNat (b : Bool) (r : Nat) : stepK b.toNat r = Rule30EtherThree.stepN b r := rfl

/-- `n` blocks of four steps beside the centers `c0, c1, c2, c3`. -/
def quads (c0 c1 c2 c3 : Nat) : Nat → Nat → Nat
  | 0, r => r
  | n + 1, r => stepK c3 (stepK c2 (stepK c1 (stepK c0 (quads c0 c1 c2 c3 n r))))

/-- The packed half at step `t`: `t / 4` blocks of four steps, then the rest one at a time. -/
def stateAt (c0 c1 c2 c3 t r : Nat) : Nat :=
  if t % 4 = 0 then quads c0 c1 c2 c3 (t / 4) r
  else if t % 4 = 1 then stepK c0 (quads c0 c1 c2 c3 (t / 4) r)
  else if t % 4 = 2 then stepK c1 (stepK c0 (quads c0 c1 c2 c3 (t / 4) r))
  else stepK c2 (stepK c1 (stepK c0 (quads c0 c1 c2 c3 (t / 4) r)))

theorem rowN_succ (c : Nat → Bool) (x0 t : Nat) :
    Rule30EtherThree.rowN c x0 (t + 1) = Rule30EtherThree.stepN (c t) (Rule30EtherThree.rowN c x0 t) := rfl

theorem period_four {c : Nat → Bool} (hc : ∀ t, c (t + 4) = c t) : ∀ n i, c (4 * n + i) = c i
  | 0, i => by rw [Nat.mul_zero, Nat.zero_add]
  | n + 1, i => by rw [show 4 * (n + 1) + i = (4 * n + i) + 4 by omega, hc, period_four hc n i]

theorem rowN_quads {c : Nat → Bool} (hc : ∀ t, c (t + 4) = c t) (r : Nat) :
    ∀ n, Rule30EtherThree.rowN c r (4 * n) = quads (c 0).toNat (c 1).toNat (c 2).toNat (c 3).toNat n r
  | 0 => rfl
  | n + 1 => by
    rw [show 4 * (n + 1) = 4 * n + 3 + 1 by omega, rowN_succ, rowN_succ, rowN_succ, rowN_succ, rowN_quads hc r n,
      period_four hc n 3, period_four hc n 2, period_four hc n 1,
      show 4 * n = 4 * n + 0 by omega, period_four hc n 0]
    rfl

/-- **The blocks of four steps are the driven half**, for a center of period four. -/
theorem stateAt_eq {c : Nat → Bool} (hc : ∀ t, c (t + 4) = c t) (t r : Nat) :
    stateAt (c 0).toNat (c 1).toNat (c 2).toNat (c 3).toNat t r = Rule30EtherThree.rowN c r t := by
  have ht := (Nat.div_add_mod t 4).symm
  have hq := rowN_quads hc r (t / 4)
  have p0 := period_four hc (t / 4) 0
  have p1 := period_four hc (t / 4) 1
  have p2 := period_four hc (t / 4) 2
  rw [Nat.add_zero] at p0
  unfold stateAt
  by_cases h0 : t % 4 = 0
  · rw [ite_eq_left h0, ← hq]; conv => rhs; rw [ht, h0, Nat.add_zero]
  by_cases h1 : t % 4 = 1
  · rw [ite_eq_right h0, ite_eq_left h1, ← hq]; conv => rhs; rw [ht, h1]
    rw [rowN_succ, p0]; rfl
  by_cases h2 : t % 4 = 2
  · rw [ite_eq_right h0, ite_eq_right h1, ite_eq_left h2, ← hq]; conv => rhs; rw [ht, h2]
    rw [show 4 * (t / 4) + 2 = 4 * (t / 4) + 1 + 1 by omega, rowN_succ, rowN_succ, p1, p0]; rfl
  · have h3 : t % 4 = 3 := by omega
    rw [ite_eq_right h0, ite_eq_right h1, ite_eq_right h2, ← hq]; conv => rhs; rw [ht, h3]
    rw [show 4 * (t / 4) + 3 = 4 * (t / 4) + 1 + 1 + 1 by omega, rowN_succ, rowN_succ, rowN_succ,
      show 4 * (t / 4) + 1 + 1 = 4 * (t / 4) + 2 by omega, p2, p1, p0]; rfl

/-! ### The family, read off bit masks -/

/-- The ether columns `j0 + 1 .. j0 + 64` at phase `ψ`, packed, the first at bit `0`: row `j0 < 7`, entry `ψ < 4`. -/
def etherWords : List (List Nat) := [
  [0x0204081020408102, 0x870e1c3870e1c387, 0xc993264c993264c9, 0x7efdfbf7efdfbf7e],
  [0x8102040810204081, 0xc3870e1c3870e1c3, 0x64c993264c993264, 0xbf7efdfbf7efdfbf],
  [0x4081020408102040, 0xe1c3870e1c3870e1, 0x3264c993264c9932, 0xdfbf7efdfbf7efdf],
  [0x2040810204081020, 0x70e1c3870e1c3870, 0x993264c993264c99, 0xefdfbf7efdfbf7ef],
  [0x1020408102040810, 0x3870e1c3870e1c38, 0x4c993264c993264c, 0xf7efdfbf7efdfbf7],
  [0x0810204081020408, 0x1c3870e1c3870e1c, 0x264c993264c99326, 0xfbf7efdfbf7efdfb],
  [0x0408102040810204, 0x0e1c3870e1c3870e, 0x93264c993264c993, 0xfdfbf7efdfbf7efd]]

theorem etherWords_spec : ∀ j0, j0 < 7 → ∀ ψ, ψ < 4 → ∀ i, i < 64 →
    ((etherWords.getD j0 []).getD ψ 0).testBit i = ether (j0 + (i + 1)) ψ := by decide +kernel

/-- The kit's wall states at each phase `ψ < 4`, packed, the first cell at bit `0`. -/
def wallTable : List (List Nat) := [
  [130, 168, 386, 424, 642, 1154, 1192, 1666, 2216, 2690, 3496, 3714, 4226, 4264, 4482, 4520, 4738, 5250, 5288,
   5762, 6312, 6530, 6568, 6786, 7336, 7810],
  [429, 454, 685, 710, 1197, 1734, 1965, 2758, 3501, 3757, 3782, 4013, 4038, 4525, 4550, 4781, 4806, 5293, 5830,
   6061, 6086, 6573, 6598, 6829, 6854, 7597, 7878, 8109, 8134],
  [106, 164, 618, 676, 1188, 1642, 1700, 2212, 2666, 2724, 3690, 3748, 4004, 4202, 4260, 4714, 4772, 5284, 5738,
   5796, 6052, 6308, 6762, 6820, 7786, 7844, 8100],
  [171, 190, 446, 702, 939, 1726, 1963, 2750, 2987, 3518, 4030, 4267, 4286, 4542, 4798, 5035, 5822, 6059, 6078,
   6315, 6590, 6846, 7083, 7614, 7870, 8107, 8126]]

theorem wallTable_spec : ∀ ψ, ψ < 4 → ∀ n ∈ wallTable.getD ψ [], (ψ, seg (fun i => n.testBit i) 13) ∈ wallStates := by
  decide +kernel

/-- The family at step `t1` and depth `k ≤ 64`, read off the packed half `r` with masks: column `k` is a B3, the half
agrees with the ether on its first `k` bits, and its next 13 bits are a wall state. -/
def fastFamily (r j0 s t1 k : Nat) : Bool :=
  Nat.beq ((j0 + k) % 7) 2 && Nat.ble k 64 &&
    Nat.beq ((Nat.xor r ((etherWords.getD (j0 % 7) []).getD ((t1 + s) % 4) 0)) % 2 ^ k) 0 &&
    (wallTable.getD ((t1 + s) % 4) []).any fun n => Nat.beq n ((r >>> k) % 2 ^ 13)

/-- **The mask check gives the family**, for every right half that agrees with the packed half `x0` on the cells
`1 .. t1 + k + 13`. -/
theorem inFamily_of_fast {c x : Nat → Bool} {x0 j0 s t1 k : Nat}
    (h : fastFamily (Rule30EtherThree.rowN c x0 t1) j0 s t1 k = true)
    (hx : ∀ q, 1 ≤ q → q ≤ t1 + k + 13 → x q = x0.testBit (q - 1)) : InFamily (drv c x) j0 s t1 := by
  have hcone : ∀ p, p ≤ k + 13 → drv c x t1 p = drv c (fun p => x0.testBit (p - 1)) t1 p := fun p hp =>
    drv_cone t1 p fun q h1 h2 => hx q h1 (by omega)
  unfold fastFamily at h
  simp only [Bool.and_eq_true, List.any_eq_true] at h
  obtain ⟨⟨⟨hk, h64⟩, hE⟩, n, hn, hW⟩ := h
  have hk' : (j0 + k) % 7 = 2 := Nat.eq_of_beq_eq_true hk
  have h64' : k ≤ 64 := Nat.le_of_ble_eq_true h64
  have hE' := Nat.eq_of_beq_eq_true hE
  have hW' := Nat.eq_of_beq_eq_true hW
  refine ⟨k, hk', fun p hp1 hpk => ?_, ?_⟩
  · obtain ⟨i, rfl⟩ : ∃ i, p = i + 1 := ⟨p - 1, by omega⟩
    rw [hcone (i + 1) (by omega), ← Rule30EtherThree.rowN_eq_drv]
    have hb := congrArg (fun m => m.testBit i) hE'
    simp only [Nat.testBit_mod_two_pow, Nat.zero_testBit] at hb
    rw [decide_eq_true (by omega : i < k), Bool.true_and] at hb
    have hx' : (Nat.xor (Rule30EtherThree.rowN c x0 t1) ((etherWords.getD (j0 % 7) []).getD ((t1 + s) % 4) 0)).testBit i =
        ((Rule30EtherThree.rowN c x0 t1).testBit i ^^ ((etherWords.getD (j0 % 7) []).getD ((t1 + s) % 4) 0).testBit i) :=
      Nat.testBit_xor _ _ i
    rw [hx', etherWords_spec (j0 % 7) (Nat.mod_lt _ (by omega)) ((t1 + s) % 4) (Nat.mod_lt _ (by omega)) i (by omega)] at hb
    rw [ether_congr (j := j0 + (i + 1)) (j' := j0 % 7 + (i + 1)) (φ := t1 + s) (φ' := (t1 + s) % 4) (by omega)
      (by omega)]
    revert hb
    cases (Rule30EtherThree.rowN c x0 t1).testBit i <;> cases ether (j0 % 7 + (i + 1)) ((t1 + s) % 4) <;> simp
  · have hrow : rowOf (drv c x) t1 k 13 = seg (fun i => n.testBit i) 13 := by
      unfold rowOf
      apply seg_congr
      intro i hi
      rw [hcone (k + i + 1) (by omega), ← Rule30EtherThree.rowN_eq_drv, hW', Nat.testBit_mod_two_pow,
        decide_eq_true hi, Bool.true_and, Nat.testBit_shiftRight]
    rw [hrow]
    exact wallTable_spec _ (Nat.mod_lt _ (by omega)) n hn

/-! ### Certificates for halves of one and two black cells -/

/-- The packed half `h` is in the family at step `t` and depth `k` for one of the alignments `A`, with
`t + k + 13 ≤ G`. -/
def entryOK (w : List Bool) (A : List (Nat × Nat)) (φ G h t k : Nat) : Bool :=
  Nat.ble (t + k + 13) G && A.any fun a =>
    fastFamily (stateAt (wordAt w (0 + φ)).toNat (wordAt w (1 + φ)).toNat (wordAt w (2 + φ)).toNat
      (wordAt w (3 + φ)).toNat t h) a.1 (a.2 + φ) t k

theorem wordAt_period (w : List Bool) (φ t : Nat) : wordAt w (t + 4 + φ) = wordAt w (t + φ) := by
  unfold wordAt
  rw [show (t + 4 + φ) % 4 = (t + φ) % 4 by omega]

theorem entryOK_spec {w : List Bool} {A : List (Nat × Nat)} {φ G h t k : Nat} (hok : entryOK w A φ G h t k = true) :
    t + k + 13 ≤ G ∧ ∃ a ∈ A,
      fastFamily (Rule30EtherThree.rowN (fun t => wordAt w (t + φ)) h t) a.1 (a.2 + φ) t k = true := by
  unfold entryOK at hok
  simp only [Bool.and_eq_true, List.any_eq_true] at hok
  obtain ⟨hG, a, ha, hf⟩ := hok
  refine ⟨Nat.le_of_ble_eq_true hG, a, ha, ?_⟩
  rw [← stateAt_eq (c := fun t => wordAt w (t + φ)) (fun t => wordAt_period w φ t)]
  exact hf

/-- Entry `j` of a packed list: 17 bits, the step times 64 plus the depth. -/
def entryAt (D : Nat) : Nat := D % 2 ^ 17

/-- The halves `{p1, p}`, `{p1, p + 1}`, ..., `n` of them, enter at the steps and depths packed in `D`. -/
def pairsOK (w : List Bool) (A : List (Nat × Nat)) (φ G p1 : Nat) : Nat → Nat → Nat → Bool
  | 0, _, _ => true
  | n + 1, p, D => entryOK w A φ G (2 ^ (p1 - 1) ||| 2 ^ (p - 1)) (entryAt D / 64) (entryAt D % 64) &&
      pairsOK w A φ G p1 n (p + 1) (D >>> 17)

/-- The half `{p1}` enters at the step `t` and depth `k` in the first entry of `D`, and each half `{p1, p2}`,
`p1 < p2 ≤ t + k + 13`, at the step and depth in the entries that follow. -/
def cellOK (w : List Bool) (A : List (Nat × Nat)) (φ G p1 D : Nat) : Bool :=
  entryOK w A φ G (2 ^ (p1 - 1)) (entryAt D / 64) (entryAt D % 64) &&
    pairsOK w A φ G p1 (entryAt D / 64 + entryAt D % 64 + 13 - p1) (p1 + 1) (D >>> 17)

theorem pairsOK_spec {w : List Bool} {A : List (Nat × Nat)} {φ G p1 : Nat} :
    ∀ n p D, pairsOK w A φ G p1 n p D = true →
      ∀ p2, p ≤ p2 → p2 < p + n → ∃ t k, entryOK w A φ G (2 ^ (p1 - 1) ||| 2 ^ (p2 - 1)) t k = true
  | 0, p, D, _, p2, h1, h2 => absurd h2 (by omega)
  | n + 1, p, D, h, p2, h1, h2 => by
    unfold pairsOK at h
    rw [Bool.and_eq_true] at h
    by_cases hp : p2 = p
    · subst hp; exact ⟨_, _, h.1⟩
    · exact pairsOK_spec n (p + 1) (D >>> 17) h.2 p2 (by omega) (by omega)

theorem cellOK_spec {w : List Bool} {A : List (Nat × Nat)} {φ G p1 D : Nat} (h : cellOK w A φ G p1 D = true) :
    ∃ t k, entryOK w A φ G (2 ^ (p1 - 1)) t k = true ∧
      ∀ p2, p1 < p2 → p2 ≤ t + k + 13 → ∃ t' k', entryOK w A φ G (2 ^ (p1 - 1) ||| 2 ^ (p2 - 1)) t' k' = true := by
  unfold cellOK at h
  rw [Bool.and_eq_true] at h
  exact ⟨_, _, h.1, fun p2 h1 h2 => pairsOK_spec _ _ _ h.2 p2 (by omega) (by omega)⟩

/-! ### At most two black cells -/

/-- At most two black cells among the cells `1 .. G`. -/
def AtMostTwo (G : Nat) (x : Nat → Bool) : Prop :=
  ∀ p q r, 1 ≤ p → p < q → q < r → r ≤ G → x p = true → x q = true → x r = true → False

/-- Either the cells `lo .. n` are white, or there is a first black one among them. -/
theorem first_black (x : Nat → Bool) (lo : Nat) : ∀ n,
    (∀ p, lo ≤ p → p ≤ n → x p = false) ∨ ∃ p, lo ≤ p ∧ p ≤ n ∧ x p = true ∧ ∀ q, lo ≤ q → q < p → x q = false
  | 0 => by
    by_cases h : lo = 0 ∧ x 0 = true
    · exact Or.inr ⟨0, by omega, Nat.le_refl 0, h.2, fun q h1 h2 => absurd h2 (by omega)⟩
    · refine Or.inl fun p h1 h2 => ?_
      have hp : p = 0 := by omega
      subst hp
      cases hx : x 0
      · rfl
      · exact absurd ⟨by omega, hx⟩ h
  | n + 1 => by
    rcases first_black x lo n with hw | ⟨p, h1, h2, h3, h4⟩
    · by_cases hb : lo ≤ n + 1 ∧ x (n + 1) = true
      · exact Or.inr ⟨n + 1, hb.1, Nat.le_refl _, hb.2, fun q h1 h2 => hw q h1 (by omega)⟩
      · refine Or.inl fun p h1 h2 => ?_
        by_cases hp : p = n + 1
        · subst hp
          cases hx : x (n + 1)
          · rfl
          · exact absurd ⟨h1, hx⟩ hb
        · exact hw p h1 (by omega)
    · exact Or.inr ⟨p, h1, by omega, h3, h4⟩

theorem testBit_one {p1 q : Nat} (h1 : 1 ≤ p1) (hq : 1 ≤ q) : (2 ^ (p1 - 1)).testBit (q - 1) = decide (q = p1) := by
  rw [Nat.testBit_two_pow]
  by_cases h : q = p1
  · subst h; simp
  · rw [decide_eq_false (by omega), decide_eq_false h]

theorem testBit_two {p1 p2 q : Nat} (h1 : 1 ≤ p1) (h2 : 1 ≤ p2) (hq : 1 ≤ q) :
    (2 ^ (p1 - 1) ||| 2 ^ (p2 - 1)).testBit (q - 1) = (decide (q = p1) || decide (q = p2)) := by
  rw [Nat.testBit_or, testBit_one h1 hq, testBit_one h2 hq]

/-- Thirty cases. -/ theorem all30 {P : Nat → Prop} (h1 : P 1) (h2 : P 2) (h3 : P 3) (h4 : P 4) (h5 : P 5) (h6 : P 6)
    (h7 : P 7) (h8 : P 8) (h9 : P 9) (h10 : P 10) (h11 : P 11) (h12 : P 12) (h13 : P 13) (h14 : P 14) (h15 : P 15)
    (h16 : P 16) (h17 : P 17) (h18 : P 18) (h19 : P 19) (h20 : P 20) (h21 : P 21) (h22 : P 22) (h23 : P 23) (h24 : P
    24) (h25 : P 25) (h26 : P 26) (h27 : P 27) (h28 : P 28) (h29 : P 29) (h30 : P 30) :
    ∀ p, 1 ≤ p → p ≤ 30 → P p
  | 1, _, _ => h1
  | 2, _, _ => h2
  | 3, _, _ => h3
  | 4, _, _ => h4
  | 5, _, _ => h5
  | 6, _, _ => h6
  | 7, _, _ => h7
  | 8, _, _ => h8
  | 9, _, _ => h9
  | 10, _, _ => h10
  | 11, _, _ => h11
  | 12, _, _ => h12
  | 13, _, _ => h13
  | 14, _, _ => h14
  | 15, _, _ => h15
  | 16, _, _ => h16
  | 17, _, _ => h17
  | 18, _, _ => h18
  | 19, _, _ => h19
  | 20, _, _ => h20
  | 21, _, _ => h21
  | 22, _, _ => h22
  | 23, _, _ => h23
  | 24, _, _ => h24
  | 25, _, _ => h25
  | 26, _, _ => h26
  | 27, _, _ => h27
  | 28, _, _ => h28
  | 29, _, _ => h29
  | 30, _, _ => h30
  | 0, h, _ => absurd h (by decide)
  | _ + 31, _, h => absurd h (by omega)

/-- **Absorption for every right half with at most two black cells among the cells `1 .. G`**, given the kernel
check `cellOK` of each first black cell `1 .. 30` and absorption for every half white on cells `1 .. 30`. -/
theorem two_absorption {w : List Bool} {A : List (Nat × Nat)} {φ G : Nat} {L : List Nat}
    (hcheck : ∀ p1, 1 ≤ p1 → p1 ≤ 30 → cellOK w A φ G p1 (L.getD (p1 - 1) 0) = true)
    (hhigh : ∀ x : Nat → Bool, (∀ p, 1 ≤ p → p ≤ 30 → x p = false) →
      ∃ a ∈ A, ∃ t1, InFamily (drv (fun t => wordAt w (t + φ)) x) a.1 (a.2 + φ) t1)
    (x : Nat → Bool) (hx : AtMostTwo G x) :
    ∃ a ∈ A, ∃ t1, InFamily (drv (fun t => wordAt w (t + φ)) x) a.1 (a.2 + φ) t1 := by
  rcases first_black x 1 30 with hw | ⟨p1, h11, h12, hb1, hmin1⟩
  · exact hhigh x hw
  obtain ⟨t, k, hone, hpairs⟩ := cellOK_spec (hcheck p1 h11 h12)
  obtain ⟨hG, a, ha, hf⟩ := entryOK_spec hone
  rcases first_black x (p1 + 1) (t + k + 13) with hw2 | ⟨p2, h21, h22, hb2, hmin2⟩
  · -- no second black cell before `t + k + 13`: the half agrees with `{p1}` there
    refine ⟨a, ha, t, inFamily_of_fast hf fun q hq1 hq2 => ?_⟩
    rw [testBit_one (by omega) hq1]
    by_cases hq : q = p1
    · subst hq; rw [hb1]; simp
    · rw [decide_eq_false hq]
      by_cases hlt : q < p1
      · exact hmin1 q hq1 hlt
      · exact hw2 q (by omega) hq2
  · -- the second black cell `p2`: the half agrees with `{p1, p2}` on the cells `1 .. G`
    obtain ⟨t', k', htwo⟩ := hpairs p2 (by omega) h22
    obtain ⟨hG', a', ha', hf'⟩ := entryOK_spec htwo
    refine ⟨a', ha', t', inFamily_of_fast hf' fun q hq1 hq2 => ?_⟩
    rw [testBit_two (by omega) (by omega) hq1]
    by_cases hq : q = p1
    · subst hq; rw [hb1]; simp
    by_cases hq' : q = p2
    · subst hq'; rw [hb2]; simp
    rw [decide_eq_false hq, decide_eq_false hq', Bool.false_or]
    by_cases hlt : q < p1
    · exact hmin1 q hq1 hlt
    by_cases hlt2 : q < p2
    · exact hmin2 q (by omega) hlt2
    cases hxq : x q
    · rfl
    · exact (hx p1 p2 q (by omega) (by omega) (by omega) (by omega) hb1 hb2 hxq).elim

/-! ### The certificates

Generated by `python -m computations.sparse_halves --lean`. For each word and phase, `cells<word>_<phase>` holds one
number per first black cell `p1 = 1 .. 30`, 17 bits an entry, each entry the step times 64 plus the depth: the half
`{p1}` first, then `{p1, p2}` for `p2 = p1 + 1 .. t + k + 13`. Each `cell<word>_<phase>_<p1>` is one kernel computation,
so that no single check holds the kernel's cache of every half. -/

def cells0001_0 : List Nat := [
  0x5060283016180a0c0e0610c30c6180a0c3c060d030ee18050c6086260319618090c200610830a418710c108636430ea18080c05860283,
  0x138309c184e0c2706138309c184e0c2706138309c184e0c2706138309c184e0c2706138309c184e0c2706138309c184e0c2706138309c184e0c2706308315a184e0c2706304309c184e0c2706394309c18b00c270615c315a18ad0c2b8620030b0184e0c4086138318a184e0c2706128309219130c57061c0309418810c2506350319618490c6c861dc309c19550c340624830f818420c1e8622030aa18490c188618c304c19180c4f061d8a06418880c120604830a818490c37861e830d4184e0c27061383,
  0x406038301218080c07861f8308018070c3f061d030e418050c2a861c8301050ad0c0f0601030ba18060c03860203,
  0x408038401220081007881b430a4180710cc0611831841805105686198301058760c1686010403a18061003880204,
  0x13018980c4c06260313018980c4c06260313018980c4c06260313018980c4c06260313018980c4c06260313018980c4c06260313018980c4c06260313018980c4c06260313018980c4c06260313018980c4c06260313018980c4c06260313018980c4c06260313018980c4c06260313018980c4c06260313018980c4c06260313018980c4c06260313018980c4c06260313018980c4c06260313018980c4c06260313018980c4c06260313018980c4c06260313018980c4c06260313018980c4c06238329618980ce906258311c18980c4c061e83130188e0c73061e4316018960c57861e83160188e0c81062bc323a18b00c7d0629c31bc18990c548617430c018970c2e061e8313218e00c3c86500a09a18790c970613030ba187a0c2d861343046185e0c11860a83200185b0c4f0615c31a8185b0c48065d0303c18590c63060e0305450790c20060c8308018760c1686254314218980c4c062603,
  0x1283094184a0c25061283094184a0c25061283094184a0c25061283094184a0c25061283094184a0c25061283094184a0c25061283094184a0c250648c31a4184a0c25062a43094184a0c25063a0309418b70c250614c315218a70c29861ec30a8184a0c3e861283118184a0c2506118308a18da0c3c061b4308c18d60c230639430a418460c9d062a83094184a0c370613c321418510c6c0620830a018990c16860ac304218860c3b86120311a184a0c25061283,
  0xd0c0686038301c180d0c068611c3050180d0c8306620a06e180d0c19061d4305e183f0c0b061543022180d0c06860343,
  0x10e18870c438621c310e18870c438621c310e18870c438621c310e18870c438621c310e18870c438621c310e18870c438621c310e18870c438621c310e18870c438621c310e18870c438621c310e18870c438621c310e18870c438621c310e18870c438621c310e18870c438621c310e18870c438621c310e18870c438621c310e18870c438621c310e18870c438621c310e18870c4386218310c18870c3f061f8310e18870c3f061f8310e18860c438621c310e18860c438619c30fc18870c33861f8310c18870c71061f8316618e10c33861cca25a187e0c3e8627c30e450c90c258612c3152189c0c258624c310818a00c96061e03104194c0c210627830a618420c870614c30a818890c25860b8311a18530c470613c30b0184a0c0d861dc3034191e0c25061c4308e18870c438621c3,
  0x35431aa18d50c6a8635431aa18d50c6a8635431aa18d50c6a8635431aa18d50c6a8635431aa18d50c6a8635431aa18d50c6a8635431aa18d50c6a8635431aa18d50c6a8635431aa18d50c6a8635431aa18d50c6a8635431aa18d50c6a8635431aa18d50c6a8635431aa18d50c6a8635431aa18d50c6a8635431aa18d50c6a8635431aa18d50c6a8635431aa18d50c6a8635431aa18d50c6a8635431aa18d50c6a8635431aa18d50c6a8635431aa18d50c6a8635431aa18d50c6a8635431aa18d50c6a8635431aa18d50c6a8635431aa18d50c95864ac33d818d50c958635431aa192b0c95863b4325618d50c6a863b4325e18d50c9786398322c192b0c9a064cc3222192b0c9e8639ca28418d50c730678431da19530c8b0623c311e18e60c768623c327a19330c6f8623c311e188f0c948623c312218e60ca5862443122188f0c4786244311e188f0c5d8623c311e188f0c9086430317a188f0c5e8618ca0c6508f0c618618ca122186a281d221c8a064886d282322630308c88632818a22091074c032441922364308c8867443d9411831d4187d281f060c8a05e887b288186108307e18452829061943214189b0c2b8616830ee183f0c2a0620430dc18ea0c1f860b831f4187f0c4b06140309218d50c6a863543,
  0x17830bc185e0c2f0617830bc185e0c2f0617830bc185e0c2f0617830bc185e0c2f0617830bc185e0c2f0617830bc185e0c2f0617830bc185e0c2f0617830bc185e0c2f0617830bc185e0c2f0617830bc185e0c2f0619830bc185e0c2f061783100185e0c3f8619830bc185e0c40062d830bc185e0c5b8637c30a2505e0c4206400a0cc187f0c2f06320a0bc18820c49061d8315c18800c2486178312a185e0c2814140a100194e0c25062dc310218660ca206128306219020c248613c312a18a90c4206294a0d4185e0c5b861283108185e0c2f061783,
  0xe418720c39061c830e418720c39061c830e418720c39061c830e418720c39061c830e418720c39061c830e418720c39061c830e418720c39061c830e418720c39061c830e418720c39061c830e418720c39061c830e418720c39061c830e418720c39061c430e218720c39061c430e418720c39061c830e418710c6e861c830e418720c390637430f450720c4914318a0e218ae0c65061c831ec18720c330623831a0188e0ca30647030cc18bb0c710629c317250d60c5f064ac30de18c80c5486208307e18be0c38860fc307e18a80c3a14108307e186d0c20860fc30fc183f0c1d06100326e186c0c2006238307218760c280603c301c18720c39061c83,
  0x905048282414120a0905048282414120a0905048282414120a0905048282414120a0905048282414120a0905048282414120a0905048282414120a0905048282414120a0905048282414120a0905048282414124a0a6504828299412ca092504828241429c315e1849285686124a1621848283d062c830f0184a283d0617c313218b20c4a0617c311418ae0c5d06104308418bf282b061043084187b0c5186098324418420c550612c30461848282414120a,
  0x514328a19450ca286514328a19450ca286514328a19450ca286514328a19450ca286514328a19450ca286514328a19450ca286514328a19450ca286514328a19450ca286514328a19450ca286514328a19450ca286514328a19450ca286514328a19450ca286514328a19450ca286514328a19450ca286514328a19450ca286514328a19450ca286514328a19450ca286514328a19450ca286514328a19450ca286514328a19450ca286514328a19450ca286514328a19450ca286514328a19450ca286514328a19450ca286514328a19450ca286514328a19450ca286514328a19450ca286514328a19450ca286514328a19450ca286514328a19450ca286514328a19450ca286514328a19450ca286514328a19450ca286514328a19450ca286514328a19450ca286514328a19450ca286514328a19450ca286514328a19450ca286514328a19450ca286514328a19450ca286514328a19450ca286514328a19450ca286514328a19450ca286514328a19450ca286514328a19450ca286514328a19450ca286514328a19450ca286514328a19450cd78651432f619450ca28651432f619b10d0f0650c3514197b0cd886514336419e80ca286514330019ea0ca286568328a1a850ca1865f03364197c0cd88650c32f619b10cbd86450322019b20ca30643c31c451430c7c06514321e18f80c7b86440321e195a0ca2862b4325a190f0c7c062b4328c18f80c87862b4328619910c7c062b4322018f80c748620c310619100c418620c321e190f0c41861e830f418830c568620c30f418830c3d061e430f4187a0c3d0620c3106187a0c41061e830f6187a0c6d062cca0f4187a0c3d8620c309a18b5282686134309a187f282686198318a184d0c26861e830cc184d0c330618c31a4184d0c3d061b0a140184d0c5e8618c30b418b90c5d862d430c618660c27061e8308c1a090c2b94134318c19450ca2865143,
  0x138309c184e0c2706138309c184e0c2706138309c184e0c2706138309c184e0c2706138309c184e0c2706138309c184e0c2706138309c184e0c2706138309c184e0c2706138309c184e0c2706138309c184e0c2706138309c184e0c2686134309c184e0c280623c3098184e0c26861383098184e0c2706138309a184e0c28061343096184d0c59062243272184d0c258628ca12c184e0c5c863e431e8189a0c68861d83038184e0c27061383,
  0xc06060303018180c0c06060303018180c0c0605c302e18180c0c0605c302e18180c0b8608030c018170c068605c302c18180c0c060603,
  0xd6186b0c35861ac30d6186b0c35861ac30d6186b0c35861ac30d6186b0c35861ac30d6186b0c35861ac30d6186b0c35861ac30d6186b0c35861ac30d6186b0c35861ac30d6186b0c35861ac30d6186b0c35861ac30d6186b0c35861ac30d6186b0c35861ac30d6186b0c35861b030d6186b0c35861ac30d6186b0c36061b030d8186b0c35861b03174186c0c5d062e83174186b0c4206210310c186b0c35861b031f818830c360621830dc18860c4306134309a18880c31061343180506c0c4986158a10a184e0c2686404309a18d80c26860c8321618960c61860c43064186b0c35861ac3,
  0x4106208310418820c4106208310418820c4106208310418820c4106208310418820c4106208310418820c4106208310418820c4106208310418820c4106208310418820c4106208310418820c4106208310418820c4106208310418820c4106208310418820c4106208310418820c4106208310418820c4106208310418820c4106208310418820c4106208310418820c4106208310418820c4106208319a18820c75063b0310418820c41063a0310418820c990627c311050820c6186258311250820c4f863bc31da18ba0c41062e8310418d90c459423c320c18c30c400621c31121888285e0621c327e189e0c51061e43088194b0c410631430cc5089284b060f0307c18440c25861c0a0f018820c41062083,
  0x8c0c46062303118188c0c46062303118188c0c46062303118188c0c46062303118188c0c46062303118188c0c46062303118188c0c46062303118188c0c46062303118188c0c46062303118188c0c46062303118188c0c46062303118188c0c46062303118188c0c46062303118188c0c46062303118188c0c46062303118188c0c46062303118188c0c46062303118188c0c46062303118188c0c46062303118188c0c46062303118188c0c46062303118188c0c46062303118188c0c4606238311c188c0c470630830d4188c0c350623830d4188c0c6b0666c30d4188c0c350630830e6188b0c3a0619ca0d4186a0c3986480a21418730c3506170a29e188c0c35060e0307018df0c67860e03072188c0c1c860dc30ec18380c3286294306e188c0c46062303,
  0x90c0486024301218090c04860243,
  0x7e0c3f061f830fc187e0c3f061f830fc187e0c3f061f830fc187e0c3f061f830fc187e0c3f061f830fc187e0c3f061f830fc187e0c3f061f830fc187e0c3f061f830fc187e0c3f061f830fc187e0c3f061f830fc187e0c3f061f830fc187e0c3f061f830fc187e0c3f061f830fc187e0c3f061f830fc187e0c3f061f830fc187e0c3f061f830fc187e0c3f061f830fc187e0c3f061f830fc187e0c3f061f830fc187e0c3f061f830fa187e0c3f061f430fc187e0c3e861f430fc187e0c3f061f830f8187d0c490624830fa187e0c3e061203090187e0c3f0626831fc189a0c250611c309018480c328611c309218650c23860dc306e18490c29060dc3074187e0c3f061f83,
  0x1d060e83074183a0c1d060e83074183a0c1d060e83074183a0c1d060e83074183a0c1d060e83074183a0c1d060e43072183a0c1d060e43074183a0c1c860e4307218390c1c860e43072183a0c1c060e8307218390c1c060e831b4183a0c37061ac30aa183a0c1d061003080183a0c1d060e83,
  0x7c0c3e061f030f8187c0c3e061f030f8187c0c3e061f030f8187c0c3e061f030f8187c0c3e061f030f8187c0c3e061f030f8187c0c3e061f030f8187c0c3e061f030f8187c0c3e061f030f8187c0c3e061f030f8187c0c3e061f030f8187c0c3e061f030f8187c0c3e061f030f8187c0c3e061f030f8187c0c3e061f030f8187c0c3e061f030f8187c0c3e061f030f8187c0c3e061f030f8187c0c3e061f030f8187c0c3e061f030f8187c0c3e061f030f8187c0c5f861f830f8187c0c598644c3226187c0c3f0621ca1d6187d0cb386210a108508428421414830a4189b0c4d86144330c18bf0c5e862c4308218520c42941cc3088187c0c3e061f03,
  0x1c180e0c0706038301c180e0c07060383,
  0x136189b0c4d8626c3136189b0c4d8626c3136189b0c4d8626c3136189b0c4d8626c3136189b0c4d8626c3136189b0c4d8626c3136189b0c4d8626c3136189b0c4d8626c3136189b0c4d8626c3136189b0c4d8626c3136189b0c4d8626c3136189b0c4d8626c3136189b0c4d8626c3136189b0c4d8626c3136189b0c4d8626c3136189b0c4d8626c3136189b0c4d8626c3136189b0c4d8626c3136189b0c4d8626c3136189b0c4e862743136189b0c4e8626c3136189b0c4e862743136189d0c4d86388a22219140c4e8626c3136189b0c6d063ec31b4189b0c470640434fc18f70c768659c321618f70cb3863b4326c18ae0c4706238a18018ed0c5b86288315819580c7986324319218c90c4a863d83404187d0c4714230a10618c90c4d062ec31b218b90c4d8605c302e18c90c4f0605c302e189b0c4d8626c3,
  0x25061283094184a0c25061283094184a0c25061283094184a0c25061283094184a0c25061283094184a0c25061283094184a0c25061283094184a0c25061283094184a0c25061283094184a0c25061283094184a0c25061283094184a0c25061283094184a0c25061243092184a0c25061243094184a0c26060a0305018490c24060803050184a0c25061283,
  0x200c1006080304018200c1006080304018200c1006080304018200c1006080304018200c1006080304018200c10060803,
  0x1c180e0c07060383,
  0x1e180f0c078603c3,
  0x7060383,
  0x383]

theorem cell0001_0_1 : cellOK w0001 A0001 0 778 1 (cells0001_0.getD 0 0) = true := by decide +kernel
theorem cell0001_0_2 : cellOK w0001 A0001 0 778 2 (cells0001_0.getD 1 0) = true := by decide +kernel
theorem cell0001_0_3 : cellOK w0001 A0001 0 778 3 (cells0001_0.getD 2 0) = true := by decide +kernel
theorem cell0001_0_4 : cellOK w0001 A0001 0 778 4 (cells0001_0.getD 3 0) = true := by decide +kernel
theorem cell0001_0_5 : cellOK w0001 A0001 0 778 5 (cells0001_0.getD 4 0) = true := by decide +kernel
theorem cell0001_0_6 : cellOK w0001 A0001 0 778 6 (cells0001_0.getD 5 0) = true := by decide +kernel
theorem cell0001_0_7 : cellOK w0001 A0001 0 778 7 (cells0001_0.getD 6 0) = true := by decide +kernel
theorem cell0001_0_8 : cellOK w0001 A0001 0 778 8 (cells0001_0.getD 7 0) = true := by decide +kernel
theorem cell0001_0_9 : cellOK w0001 A0001 0 778 9 (cells0001_0.getD 8 0) = true := by decide +kernel
theorem cell0001_0_10 : cellOK w0001 A0001 0 778 10 (cells0001_0.getD 9 0) = true := by decide +kernel
theorem cell0001_0_11 : cellOK w0001 A0001 0 778 11 (cells0001_0.getD 10 0) = true := by decide +kernel
theorem cell0001_0_12 : cellOK w0001 A0001 0 778 12 (cells0001_0.getD 11 0) = true := by decide +kernel
theorem cell0001_0_13 : cellOK w0001 A0001 0 778 13 (cells0001_0.getD 12 0) = true := by decide +kernel
theorem cell0001_0_14 : cellOK w0001 A0001 0 778 14 (cells0001_0.getD 13 0) = true := by decide +kernel
theorem cell0001_0_15 : cellOK w0001 A0001 0 778 15 (cells0001_0.getD 14 0) = true := by decide +kernel
theorem cell0001_0_16 : cellOK w0001 A0001 0 778 16 (cells0001_0.getD 15 0) = true := by decide +kernel
theorem cell0001_0_17 : cellOK w0001 A0001 0 778 17 (cells0001_0.getD 16 0) = true := by decide +kernel
theorem cell0001_0_18 : cellOK w0001 A0001 0 778 18 (cells0001_0.getD 17 0) = true := by decide +kernel
theorem cell0001_0_19 : cellOK w0001 A0001 0 778 19 (cells0001_0.getD 18 0) = true := by decide +kernel
theorem cell0001_0_20 : cellOK w0001 A0001 0 778 20 (cells0001_0.getD 19 0) = true := by decide +kernel
theorem cell0001_0_21 : cellOK w0001 A0001 0 778 21 (cells0001_0.getD 20 0) = true := by decide +kernel
theorem cell0001_0_22 : cellOK w0001 A0001 0 778 22 (cells0001_0.getD 21 0) = true := by decide +kernel
theorem cell0001_0_23 : cellOK w0001 A0001 0 778 23 (cells0001_0.getD 22 0) = true := by decide +kernel
theorem cell0001_0_24 : cellOK w0001 A0001 0 778 24 (cells0001_0.getD 23 0) = true := by decide +kernel
theorem cell0001_0_25 : cellOK w0001 A0001 0 778 25 (cells0001_0.getD 24 0) = true := by decide +kernel
theorem cell0001_0_26 : cellOK w0001 A0001 0 778 26 (cells0001_0.getD 25 0) = true := by decide +kernel
theorem cell0001_0_27 : cellOK w0001 A0001 0 778 27 (cells0001_0.getD 26 0) = true := by decide +kernel
theorem cell0001_0_28 : cellOK w0001 A0001 0 778 28 (cells0001_0.getD 27 0) = true := by decide +kernel
theorem cell0001_0_29 : cellOK w0001 A0001 0 778 29 (cells0001_0.getD 28 0) = true := by decide +kernel
theorem cell0001_0_30 : cellOK w0001 A0001 0 778 30 (cells0001_0.getD 29 0) = true := by decide +kernel

theorem cells0001_0_ok : ∀ p1, 1 ≤ p1 → p1 ≤ 30 → cellOK w0001 A0001 0 778 p1
    (cells0001_0.getD (p1 - 1) 0) = true :=
  all30
    cell0001_0_1 cell0001_0_2 cell0001_0_3 cell0001_0_4 cell0001_0_5 cell0001_0_6 cell0001_0_7 cell0001_0_8
    cell0001_0_9 cell0001_0_10 cell0001_0_11 cell0001_0_12 cell0001_0_13 cell0001_0_14 cell0001_0_15 cell0001_0_16
    cell0001_0_17 cell0001_0_18 cell0001_0_19 cell0001_0_20 cell0001_0_21 cell0001_0_22 cell0001_0_23 cell0001_0_24
    cell0001_0_25 cell0001_0_26 cell0001_0_27 cell0001_0_28 cell0001_0_29 cell0001_0_30

def cells0001_1 : List Nat := [
  0x50604c307a180a0c29862a830f018090c11061b8303418cc0c2486130302618090c1c06384302c18660c268617430b2180a0c04860283,
  0x300c18060c0306018300c18060c0306018300c18060c0306018300c18060c0306018300c18060c0306018300c18060c4306018300c18060c0306218300c23060b8308a18300c228618030ce18300c4e062b031b018b10c5d060d8323218740c548602c30e818a80c2086358317a18830c0b061dc310c18f60c2c064b0311018300c18060c03,
  0x11c188e0c4706238311c188e0c4706238311c188e0c4706238311c188e0c4706238311c188e0c4706238311c188e0c4706238311c188e0c4706238311c188e0c4706238311c188e0c4706238311c188e0c4706238311c188e0c4706238311c188e0c4706238311c188e0c4706238311c188e0c4706238311c188e0c4706238311c188e0c4706238311c188e0c4706238311c188e0c470623c311c188e0c47062383290188e0c4706430311c188e0c4706238311e195f0c4706288a144508e0c47061f4314a188f0c5594238311c19172875062d43122188e0c5206318313e187d0c91062c43162187d0c25944e030f41899283e86234313819010c3186164317618620c5e8611030fa18620c5886184308a192e0c210651c319218b10c22861dc30e818690c6f941b4301e18990c3c8604830de18450c700644830ee18a80c28862203052188e0c47062383,
  0x1c4a0e250712838941c4a0e250712838941c4a0e250712838941c4a0e250712838941c4a0e250712838941c4a0e250712838941c4a0e250712838941c4a0e250712838941c4a0e250712838941c4a0e250712838941c4a0e250712838941c4a0e250712838941c4a0e250712838941c4a0e25071283d941c4a0e250712838941c4a0e250712838941c4a0e2507128389435831701871286486304a18018712838941c4a1b018d90c3894248a0ca18b80c32863203178186d0c7194140312a187128322224c313618760c4586318322418d20c4a8614030ae50940c460619ca16e19510c8106184305818d00c2c060b030bc18650c1e061bc308a182d0c4c9409030e818850c228635831a250880c49861d0313e50712838941c4a,
  0x1d430ea18750c3a861d430ea18750c3a861d430ea18750c3a861d430ea18750c3a861d430ea18750c3a861d430ea18750c3a861d430ea18750c3a861d430ea18750c3a861d430ea18750c3a861d430ea18750c3a861d430ea18750c3a861d430ea18750c3a861d430ea18750c3a861d430ea18750c3a861d430ea18750c3a861d430ea18750c3a861d430ea18750c3a861d430ea18750c3a861d430ea18750c3a861d430ea18750c3a8628c314e50750c3a86704313218750c4c8629430aa18990c3d94208314418720c1b0626832b218540c1b860d830a418830c60862b4316c1a4b0c1b8618830f4186d0c91061ac325418810c188603830a8187f282e06404306218890c0806164308a18750c3a861d43,
  0xc218610c308618430c218610c308618430c218610c308618430c218610c308618430c218610c308618430c218610c308618430c218610c308618430c218610c308618430c218610c308618430c218610c308618430c218610c308618430c018610c308618c30c218610c318618030c218610c4a0618430c218610c318617c30c218610c318618430be18610c2f8657430c2185f0c2f861783126185f0c4606178303e185e0c0f8605c302e188a0c0b860783114181f0c0f86078303a181f0c07860743018190a0c6e0603c3312181f0c0a861e83124180b0c3806050305218610c30861843,
  0x2c0616030b018580c2c0616030b018580c2c0616030b018580c2c0616030b018580c2c0616030b018580c2c0616030b018580c2c0616030b018580c2c0616030b018580c2c0616030b018580c2c0616030b018580c2c0616030b018580c2c0616030b018580c2c0624c30b018580c680626c31ac18580c2c064f431e218580c8a0616430b018580c3c061b431c0187e0c3686268313a18580c3b0615c313418d00c19063b431ca18780c351413430fa886d0c1c864403072182d0c3706078401820cc28080822c30a218580c2c061603,
  0x2a0c15060a83054182a0c15060a83054182a0c15060a83054182a0c15860a83056182a0c16064cca054182a0c16860b43058182b0c528623430cc182a0c1c86284305a182c0c168617830be18710c1d86164309a182d0c1c86234303c18290c78060b43072182a0c15060a83,
  0x2d4316a18b50c5a862d4316a18b50c5a862d4316a18b50c5a862d4316a18b50c5a862d4316a18b50c5a862d4316a18b50c5a862d4316a18b50c5a862d4316a18b50c5a862d4316a18b50c5a862d4316a18b50c5a862d4316a18b50c5a862d4316a18b50c5a862d4316a18b50c5a862d4316a18b50c5a862d4316a18b50c5a862d4316a18b50c5a862d4316a18b50c5a862d4316a18b50c5a862d4316a18b50c5a862d4316a18b50c5a862d4316a18b50c5a862d433c218b50c5a862d4316a18b50c5a862d4316a18b50c5a862d4316a18b50c5a862d4316a19780c5a862d4316a18b50c5a862d4316a18b50c94862d431ec18b50c5a86384327c18b50c54142d4316a18b50c5a86434316818b50c4f86288321a18d1285a86394313c18a00c5106558330218a20c51062d431d8194d0c5a8628831e618b50c4f8623830c41a1d0c48863d8314450a10c868627ca13a18640c1c86168314418890c2d860e0315050ce0c23060e431a450390c4686228309218a00c1806250318e518b0c6c86158318018490c140610430e218b50c5a862d43,
  0x1e218f10c78863c431e218f10c78863c431e218f10c78863c431e218f10c78863c431e218f10c78863c431e218f10c78863c431e218f10c78863c431e218f10c78863c431e218f10c78863c431e218f10c78863c431e218f10c78863c431e218f10c78863c431e218f10c78863c431e218f10c78863c431e218f10c78863c431e218f10c78863c431e218f10c78863c431e218f10c78863c431e218f10c78863c431e218f10c78863c431e218f10c78863c431e218f10c78863c431e218f10c78863c431e218f10c78863c431e218f10c78863c431e218f10c78863c431e218f10c78863c431e218f10c78863c431e218f10c78863c431e218f10c78863c431e218f10c78863c431e218f10c78863c431e218f10c78863c431e218f10c78863c4327c18f10c9f063c431b250f10c87063c433de18f10ca1943c431de18f10c88063c432a618f10cc8864f032d6196b0c8b8643831b2519b285c863c0326c193c0c96064f0317218f10c8b86510317219730c5c862e4315a18b90c5c862e43172193e0c70861dc317218b90c3b861dc30ee18b90c3b862e430f018b90c5c861e0315a18770c3c061e0315618b90c568626031b650b90c68861dc319018780c5c861e4317018790c3c0619830d218960c59861a430c018a90c3e861a430c018670c34861a031d018850c1d063dc308018760c820632c30b81870281286184303e187f0c258602c30ac18f10c78863c43,
  0x6418320c19060c8306418320c19060c8306418320c19060c8306418320c19060c8306418320c19060c8306418320c190629830b218320c19060c8306418320c5d863e4306418eb0c19060c83064186d281a8634030ca18320c1a861c4306418fb281906044302218330c3f06044306418320c19060c83,
  0x688634431a218d10c688634431a218d10c688634431a218d10c688634431a218d10c688634431a218d10c688634431a218d10c688634431a218d10c688634431a218d10c688634431a218d10c688634431a218d10c688634431a218d10c688634431a218d10c688634431a218d10c688634431a218d10c688634431a218d10c688634431a218d10c688634431a218d10c688634431a218d10c688634431a218d10c688634431a218d10c688634431a218d10c688634431a218d10c688634431a218d10c688634431a218d10c688634431a218d10c688634431a218d10c688634431a218d10c688634431a218d10c688634431a218d10c688634431a218d10c688634431a218d10c688634031a218d10c688634431a218d10c688634031da18d10c688634031a018d10c6806964319a50d00c689433431a218d10c68062c0316018b00c58062c0316018cd0c58062b431a018d1285286344319a18b00c8a86204317e18b00c40861f831fc18ad0c4086204312c18fb0c4a862583110507f0c3f062b430ec18c60c78064c030fe189d0c2d863683110188d0c610653832ec18950c2906088304418c30c5f06088309618b10c2d060b0306c184a0c0c8619430d818d10c68863443,
  0xc018600c300618030c018600c300618030c018600c300618030c018600c300618030c018600c300618030c018600c300618030c018600c300618030c018600c300618030c018600c300618030c018600c300618030c018600c300618030c018600c300618030c018600c300621830c018600c43061d4321618600c798632030be18600c308617c30c218860c3f061f03142185f0c2f061d430f650610c308617830d218860c3a8625830b2505e0c300614031f618860c73941a4a0dc18600cae860fc30f218480c738614430c818600c30061803,
  0xc0c06060303018180c0c06060f8310a180c0c06063e4307c180c0c06060303,
  0x16c30b6185b0c2d8616c30b6185b0c2d8616c30b6185b0c2d8616c30b6185b0c2d8616c30b6185b0c2d8616c30b6185b0c2d8616c30b6185b0c2d8616c30b6185b0c2d8616c30b6185b0c2d8616c30b6185b0c2d8616c30b6185b0c2d8616c30b6185b0c2d8616c30ba185b0c2e8617430ba185b0c2e8617430ba185b0c47863e0a14c185b0c2d0616c314c185d0c2d86254319218c5282d8641431ca188a28478627c30f018f50c2d0613431a018910c710609c3050184a0c65062dc304c185b0c2d8616c3,
  0x38501c280e14070a038501c280e94074a038501c280e1415430b0501c280e941cc30e4181d2866860a0a0a818580c39860f4a04a501b280e941f430fa18fb0c1a86204303a181c280e14070a,
  0x6b0c35861ac30d6186b0c35861ac30d6186b0c35861ac30d6186b0c35861ac30d6186b0c35861ac30d6186b0c35861ac30d6186b0c35861ac30d6186b0c35861ac30d6186b0c35861ac30d6186b0c35861ac30d6186b0c35861ac30d6186b0c35861ac30d6186b0c35861a830d4186b0c35061a830d6186b0c35061ac30d4186b0c36061b43100186a0c65941ac3142186b0c35861ac30d8186c0c6b861a83220186c0c40861b430da18e50c4086204313a506e0c42862bc324418810c1c060d8306c18bd0c40860d830701873281c860e4307218360c32860e030fa186b0c35861ac3,
  0x2a18150c0a86054302a18150c0a86054302a18150c0a86038301c18150c0a86038301c18150c0a860543,
  0x26061303098184c0c26061303098184c0c26061303098184c0c26061303098184c0c26061303098184c0c26061303098184c0c26061303098184c0c26061303098184c0c26061303098184c0c26061303098184c0c26061303098184c0c38861843098184c0c26061303098184c0c2c861bc3098506e0c2506088a044504c0c2c86088a052509d0c0c94260a2a21822283b0622431a8184c0c26061303,
  0x20619030c818640c320619030c818640c320619030c818640c320619030c818640c320619030c818640c320619030c818640c320619030c818640c320619030c818640c320619030c818640c320619030c818640c320619030c818640c320619030c818640c320619030c818640c320619030c818640c320619030c818640c320619030c818640c320619030c818640c320619030c818640c320619030c818640c320619030c818640c320619030c818640c320619030c818640c320619030c818640c320619030c818640c320619030c818640c320619030c818640c320619030c818640c320619030c818640c320619030c818640c320619030c818640c320619030c818640c320619030c818640c320619030c818640c320619030c818640c320619030c818640c320019030c818640c320619030c818640c320019030c818640c320019030c818640c320619000c8186400320619030c81863fc320619030c81863fc320619030c81863fc320619030c8186340a1a051030c6e8633ca1fe19030c681437431fe18cf28a48633ca1a050cf287286320319218ff0c6e86404319019d80c648633ca2ba18c90c6794324320618c90c99061d4327218c90c390633ca19e50cf289506224311219340c9b06450326818720c44861cc30ea18760c3a0638431ba18890ca5061c830e418890c39861d4311218c70c3a862283114187b2820861f030e018750c3d0620431c2187c0c3e86338306c19030c818640c3,
  0xe4307218390c1c860e4307218390c1c860e4307218390c1c860e4307218390c1c860e4307218390c1c860e4307218390c1c860e4307218390c1c860e4307218390c1c860e4307218390c1c860e0307018390c1c860e0307018390c1c860e4307218380c1c860d8306e18390c1c860e43,
  0xc0c06060303018180c0c06060303,
  0x7c183e0c1f060f8307c183e0c1f060f8307c183e0c1f060f8307c183e0c1f060f8307c183e0c1f060f8307c183e0c1f060f8307c183e0c1f06210307c183e0c1f060f8307c183e0c41862dc307c183e0c1f860fc307e183e0c69060fc307c183e0c1f861f030fa183f0c1f8623431ac183e0c1f060f83,
  0x1f030f8187c0c3e061f030f8187c0c3e061f030f8187c0c3e061f030f8187c0c3e061f030f8187c0c3e061f030f8187c0c3e061f030f8187c0c3e061f030f8187c0c3e061f030f8187c0c3e061f030f8187c0c3e061f030f8187c0c3e061f030f8187c0c3e061f030f8187c0c3e061f030f8187c0c3e061f030f8187c0c3e061f030f8187c0c3e061f030f8187c0c3e061f030f8187c0c3e061f030f8187c0c3d061e830f8187c0c3d061e830f8187c0c828620ca204187a0c3e06244320a187c0c4794244333889690c3f06440319a18b20c3e861e8320819040c48862cc3348187c0c3d062a4307e187e0c9906104307e187c0c3e061f03,
  0x1f0c0f8607c303e181f0c0f8607c303e181f0c0f8607c303e181f0c0f86074303a181f0c0f86074303a181f0c0f8607c3,
  0x1a180d0c06860343,
  0x150c0a86054302a18150c0a86054302a18150c0a860543,
  0x6860343,
  0x343,
  0x343]

theorem cell0001_1_1 : cellOK w0001 A0001 1 778 1 (cells0001_1.getD 0 0) = true := by decide +kernel
theorem cell0001_1_2 : cellOK w0001 A0001 1 778 2 (cells0001_1.getD 1 0) = true := by decide +kernel
theorem cell0001_1_3 : cellOK w0001 A0001 1 778 3 (cells0001_1.getD 2 0) = true := by decide +kernel
theorem cell0001_1_4 : cellOK w0001 A0001 1 778 4 (cells0001_1.getD 3 0) = true := by decide +kernel
theorem cell0001_1_5 : cellOK w0001 A0001 1 778 5 (cells0001_1.getD 4 0) = true := by decide +kernel
theorem cell0001_1_6 : cellOK w0001 A0001 1 778 6 (cells0001_1.getD 5 0) = true := by decide +kernel
theorem cell0001_1_7 : cellOK w0001 A0001 1 778 7 (cells0001_1.getD 6 0) = true := by decide +kernel
theorem cell0001_1_8 : cellOK w0001 A0001 1 778 8 (cells0001_1.getD 7 0) = true := by decide +kernel
theorem cell0001_1_9 : cellOK w0001 A0001 1 778 9 (cells0001_1.getD 8 0) = true := by decide +kernel
theorem cell0001_1_10 : cellOK w0001 A0001 1 778 10 (cells0001_1.getD 9 0) = true := by decide +kernel
theorem cell0001_1_11 : cellOK w0001 A0001 1 778 11 (cells0001_1.getD 10 0) = true := by decide +kernel
theorem cell0001_1_12 : cellOK w0001 A0001 1 778 12 (cells0001_1.getD 11 0) = true := by decide +kernel
theorem cell0001_1_13 : cellOK w0001 A0001 1 778 13 (cells0001_1.getD 12 0) = true := by decide +kernel
theorem cell0001_1_14 : cellOK w0001 A0001 1 778 14 (cells0001_1.getD 13 0) = true := by decide +kernel
theorem cell0001_1_15 : cellOK w0001 A0001 1 778 15 (cells0001_1.getD 14 0) = true := by decide +kernel
theorem cell0001_1_16 : cellOK w0001 A0001 1 778 16 (cells0001_1.getD 15 0) = true := by decide +kernel
theorem cell0001_1_17 : cellOK w0001 A0001 1 778 17 (cells0001_1.getD 16 0) = true := by decide +kernel
theorem cell0001_1_18 : cellOK w0001 A0001 1 778 18 (cells0001_1.getD 17 0) = true := by decide +kernel
theorem cell0001_1_19 : cellOK w0001 A0001 1 778 19 (cells0001_1.getD 18 0) = true := by decide +kernel
theorem cell0001_1_20 : cellOK w0001 A0001 1 778 20 (cells0001_1.getD 19 0) = true := by decide +kernel
theorem cell0001_1_21 : cellOK w0001 A0001 1 778 21 (cells0001_1.getD 20 0) = true := by decide +kernel
theorem cell0001_1_22 : cellOK w0001 A0001 1 778 22 (cells0001_1.getD 21 0) = true := by decide +kernel
theorem cell0001_1_23 : cellOK w0001 A0001 1 778 23 (cells0001_1.getD 22 0) = true := by decide +kernel
theorem cell0001_1_24 : cellOK w0001 A0001 1 778 24 (cells0001_1.getD 23 0) = true := by decide +kernel
theorem cell0001_1_25 : cellOK w0001 A0001 1 778 25 (cells0001_1.getD 24 0) = true := by decide +kernel
theorem cell0001_1_26 : cellOK w0001 A0001 1 778 26 (cells0001_1.getD 25 0) = true := by decide +kernel
theorem cell0001_1_27 : cellOK w0001 A0001 1 778 27 (cells0001_1.getD 26 0) = true := by decide +kernel
theorem cell0001_1_28 : cellOK w0001 A0001 1 778 28 (cells0001_1.getD 27 0) = true := by decide +kernel
theorem cell0001_1_29 : cellOK w0001 A0001 1 778 29 (cells0001_1.getD 28 0) = true := by decide +kernel
theorem cell0001_1_30 : cellOK w0001 A0001 1 778 30 (cells0001_1.getD 29 0) = true := by decide +kernel

theorem cells0001_1_ok : ∀ p1, 1 ≤ p1 → p1 ≤ 30 → cellOK w0001 A0001 1 778 p1
    (cells0001_1.getD (p1 - 1) 0) = true :=
  all30
    cell0001_1_1 cell0001_1_2 cell0001_1_3 cell0001_1_4 cell0001_1_5 cell0001_1_6 cell0001_1_7 cell0001_1_8
    cell0001_1_9 cell0001_1_10 cell0001_1_11 cell0001_1_12 cell0001_1_13 cell0001_1_14 cell0001_1_15 cell0001_1_16
    cell0001_1_17 cell0001_1_18 cell0001_1_19 cell0001_1_20 cell0001_1_21 cell0001_1_22 cell0001_1_23 cell0001_1_24
    cell0001_1_25 cell0001_1_26 cell0001_1_27 cell0001_1_28 cell0001_1_29 cell0001_1_30

def cells0001_2 : List Nat := [
  0x5060403016180a0c0d061d0308218090c460613c306418070c7c06280304018c20c2886584305018680c398607c309818080c04860283,
  0x5080404016200a100d08110308818091038062c830881807101586174304020900c270610030e018b30c388628c301e18081004880284,
  0x36061b030d8186c0c36061b030d8186c0c36061b030d8186c0c36061b030d8186c0c36061b030d8186c0c36061b030d8186c0c36061b030d8186c0c36061b030d8186c0c36061b030d8186c0c36061b030d8186c0c36061b030d8186c0c35861b030d8186c0c35861b030d6186c0c35861b030d8186c0c35861a430d2186b0c35061b030d8186b0c358629430d2186a0c4a86324315c18690c62061f030e6186b0c4b063bca14818800c411436030f818b10c200634431a818e20c44862203080187b0c1f860f4313018480c39140d4306c18720c0a0607c306c18400c3a060f0303c18360c4b8602c30e818b40c40060543048180c0c09861643096186c0c36061b03,
  0x2086104308218410c2086104308218410c2086104308218410c2086104308218410c2086104308218410c2086104308218410c2086104308218410c2086108308418410c2106104308218410c208617c308418420c2106108308418420c2206108308618410c2586110308418440c22061f8a0f018430c3b06124308218490c648620c30d018880c4f060a0303e19670c60061583060184f0c3f062e0305e18410c20861043,
  0x304318218c10c6086304318218c10c6086304318218c10c6086304318218c10c6086304318218c10c6086304318218c10c6086304318218c10c6086304318218c10c6086304318218c10c6086304318218c10c6086304318218c10c6086304318218c10c6086304318218c10c6086304318218c10c6086304318218c10c6086304318218c10c6086304318218c10c6086304318218c10c6086304318218c10c6086304318218c10c6086304318218c10c6086304318218c10c6086304318218c10c6086304318218c10c6086304318218c10c6086304318218c10c6086304318218c10c6086304317a18c10c6086304318218c10c5e86304318218c10c5e862f4318018bd0c608630431f218bd0c60864ac31a818bd0c63942f8317e18c10c608630031a818d40c5e862e0318219030c7986204310218d40c7d0625433ca1a380c5c062d8312a18bd0c5c0642c31d050d10c5c066e4309218ea0c24861f8329a18d92872861e4315a191d0c2506248313818740c400624030a218490c2586130302e184a0c220605c3206504a0c2494100309018170c2486030305c18170c1c0611431fe180e0c0c1403031d818c10c60863043,
  0x280c14060a0305018280c14060a0305018280c14060a0305018280c14060a0305018280c14060a0305018280c14061dc309618280c18860c4305018280c40060a0323818280c4b862ac30bc18280c3a86210302e18280c65940b030a0181b0c0986108309c18280c14060a03,
  0x114188a0c45062283114188a0c45062283114188a0c45062283114188a0c45062283114188a0c45062283114188a0c45062283114188a0c45062283114188a0c45062283114188a0c45062283114188a0c45062283114188a0c45062283114188a0c45062283114188a0c45062283114188a0c45062283112188a0c44862283114188a0c45062243114188a0c44862243112188a0c4486224311218890c44862243112188a0c4486224311218890c4486224311218c4287c06440a21018890c500642031b018890c6c06339112450bc0c6a863cc318c19400c45862f4312418a00c570624430e618fc0c48861cc3124189228270614030a018db0c278620c309a18910c28063043130184d0c27862d4a0e618500c270617c319a18840c78061fc31ac184d0c2786160309a184f0c24061a43134188a0c45062283,
  0x17030b8185c0c2e0617030b8185c0c2e0617030b8185c0c2e0617030b8185c0c2e0617030b8185c0c2e0617030b8185c0c2e0617030b8185c0c2e0617030b8185c0c2e0617030b8185c0c2e0617030b8185c0c2e0617030b8185c0c2e0619430b8185c0c2e0617030b8185c0c2e0638030b818650c2e064c831ec185c0cb50622c308e18650c778611c3114185a284406120308e191d0c238611c308e188c0c240621c307e18470c23860fc309018ad0c2e0639430b0183f0c570615c3192185c0c17864843148185b0c0906090319c185c0c2e061703,
  0x34301a180d0c0686050301c180d0c0b060503070180d0c31861c0308e18e10c070614030d8180d0c06860343,
  0x700c38061c030e018700c38061c030e018700c38061c030e018700c38061c030e018700c38061c030e018700c38061c030e018700c38061c030e018700c38061c030e018700c38061c030e018700c38061c030e018700c38061c030e018700c38061c030e018700c38061c030e018700c38061c030e018700c38061c030e018700c38061f030f818700c38061f030e018700c38061c030e018700cb406218314e187c0c380612430f418700c98062c432b818a70c2486144311a18c50c2486124309218970c9b061f0310e189e0c6c06130308818490c2e06108308618d80c1514108329e189a0c1206100307a182c282c861d8309e18700c38061c03,
  0x590c2c8616430b218590c2c8616430b218590c2c8616430b218590c2c8616430b218590c2c8616430b218590c2c8616430b218590c2c8616430b218590c2c8616430b218590c2c8616430b218590c2c8616430b218590c2c8616430b218590c2c8616430b218590c2c8616430b218590c2c8616430b218590c2c8616830b218590c2c8634c30b218590c250612830b218590c2d061f831c218590c26062b8310e184c0c2586060303018ea0c0d06060313618590c3b8616030dc181a0c5e06104319e18590c2c861643,
  0x5e182f0c17860bc305e182f0c17860bc305e182f0c17860bc305e182f0c17860bc305e182f0c17862403168182f0c17861e4305e182f0c6c863d0313a18a00c66062d03398188e0c420613c308c189d0c420613c305e182f0c200625830b4187a0c0c861183038182f0c17860bc3,
  0x54302a18150c0a86054302a18150c0e86058302c18150c7a0605831c618150c0f0605431c018910c078602c301618150c0a860543,
  0x17860bc305e182f0c17860bc305e182f0c17860bc305e182f0c17860bc305e182f0c17860bc305e182f0c17860bc305e182f0c17860bc305e182f0c17860bc305e182f0c32860b43170182f0c17860c0325a182f0c17865843096191b0c1806200305c182f0c17860bc3,
  0x10c18860c4306218310c18860c4306218310c18860c4306218310c18860c4306218310c18860c4306218310c18860c4306218310c18860c4306218310c18860c4306218310c18860c4306218310c18860c4306218310c18860c4306218310c18860c4306218310c18860c4306218310c18860c4306218310c18860c4306218310c18860c4306218310c18860c4306218310c18860c4306218310e18860c4306218310c18860c4306218310c18860c4306218310c18860c4306218310c18870c3e06218314018860c6a0628031a818870c6a0665c31a818e80c338619831a4189e0c3e061bca0f8189d0c340619830ca1882284f0663c30d018a00c34060f030e418650c4206320316818680c5806380309818390c3a86200301e18860c43062183,
  0x3a861d430ea18750c3a861d430ea18750c3a861d430ea18750c3a861d430ea18750c3a861d430ea18750c3a861d430ea18750c3a861d430ea18750c3a861d430ea18750c3a861d430ea18750c3a861d430ea18750c3a861d430ea18750c3a861d430ea18750c3a861d430ea18750c3a861d430ea18750c3a861d430ea18750c3a861d830ec18750c3a861d830ea18750c3b8636830ee18750c7e061d831ac18770c49861e0320018760c520624c321a18b10c3b0636c314618930c5a0628c314618c8283b061d831f418a20c7e861d830ee18750c1a860d8307018b40c1c060d8306a18ae0c51940d830d018350c46061c8308a18750c3a861d43,
  0x70c038601c300e18070c038601c3,
  0x6a18350c1a860d4306a18350c1a860d4306a18350c1a860d4306a18350c1a860d4306a18350c1a860d4306a18350c1a860d4306a18350c1a860d4306a18350c1a860d4306a18350c1b060d4306a18350c1b060d8306a18350c1b86114308a187b0c1a862bc327e18350c1a860d43,
  0x7c183e0c1f060f8307c183e0c1f060f8307c183e0c1f060f8307c183e0c1f060f8307c183e0c1f060f8307c183e0c1f060f8307c183e0c1f060f8307c183e0c1f060f8307c183e0c1f060f4307c183e0c1f060f8307c183e0c1f861ac315a183e0c1f061ac3162183e0c56060e0314c186b0c8b860d83070183e0c1f060f83,
  0x720c39061c830e418720c39061c830e418720c39061c830e418720c39061c830e418720c39061c830e418720c39061c830e418720c39061c830e418720c39061c830e418720c39061c830e418720c39061c830e418720c39061c830e418720c39061c830e418720c39061c830e418720c39061c430e418720c39061c830e418720c38861c830e418720c38861c830e218710c38861c430e218720c54062a030e4187e0c5e0638c30f450710c38861eca0e818710c3d1424031c018740c84061c830e618760c4406100308018720c3886100307e18740c2006140317a18400c3786390318e18720c39061c83,
  0x18180c0c06060303018180c0c06060303,
  0x2a18150c0a86054302a18150c0a86228a13618150c0a86198316418150c0a860543,
  0x3c181e0c0f06078303c181e0c0f06098304c181e0c0f06098304c181e0c130611c309018260c130611c30a0181e0c0f060783,
  0x1e0c0f06078303c181e0c0f06078303c181e0c0f06078303c181e0c0f06078303c181e0c0f06078303c181e0c0f060783,
  0x18180c0c06060303,
  0x1a180d0c06860343,
  0x6060303,
  0x303,
  0x303,
  0x303]

theorem cell0001_2_1 : cellOK w0001 A0001 2 778 1 (cells0001_2.getD 0 0) = true := by decide +kernel
theorem cell0001_2_2 : cellOK w0001 A0001 2 778 2 (cells0001_2.getD 1 0) = true := by decide +kernel
theorem cell0001_2_3 : cellOK w0001 A0001 2 778 3 (cells0001_2.getD 2 0) = true := by decide +kernel
theorem cell0001_2_4 : cellOK w0001 A0001 2 778 4 (cells0001_2.getD 3 0) = true := by decide +kernel
theorem cell0001_2_5 : cellOK w0001 A0001 2 778 5 (cells0001_2.getD 4 0) = true := by decide +kernel
theorem cell0001_2_6 : cellOK w0001 A0001 2 778 6 (cells0001_2.getD 5 0) = true := by decide +kernel
theorem cell0001_2_7 : cellOK w0001 A0001 2 778 7 (cells0001_2.getD 6 0) = true := by decide +kernel
theorem cell0001_2_8 : cellOK w0001 A0001 2 778 8 (cells0001_2.getD 7 0) = true := by decide +kernel
theorem cell0001_2_9 : cellOK w0001 A0001 2 778 9 (cells0001_2.getD 8 0) = true := by decide +kernel
theorem cell0001_2_10 : cellOK w0001 A0001 2 778 10 (cells0001_2.getD 9 0) = true := by decide +kernel
theorem cell0001_2_11 : cellOK w0001 A0001 2 778 11 (cells0001_2.getD 10 0) = true := by decide +kernel
theorem cell0001_2_12 : cellOK w0001 A0001 2 778 12 (cells0001_2.getD 11 0) = true := by decide +kernel
theorem cell0001_2_13 : cellOK w0001 A0001 2 778 13 (cells0001_2.getD 12 0) = true := by decide +kernel
theorem cell0001_2_14 : cellOK w0001 A0001 2 778 14 (cells0001_2.getD 13 0) = true := by decide +kernel
theorem cell0001_2_15 : cellOK w0001 A0001 2 778 15 (cells0001_2.getD 14 0) = true := by decide +kernel
theorem cell0001_2_16 : cellOK w0001 A0001 2 778 16 (cells0001_2.getD 15 0) = true := by decide +kernel
theorem cell0001_2_17 : cellOK w0001 A0001 2 778 17 (cells0001_2.getD 16 0) = true := by decide +kernel
theorem cell0001_2_18 : cellOK w0001 A0001 2 778 18 (cells0001_2.getD 17 0) = true := by decide +kernel
theorem cell0001_2_19 : cellOK w0001 A0001 2 778 19 (cells0001_2.getD 18 0) = true := by decide +kernel
theorem cell0001_2_20 : cellOK w0001 A0001 2 778 20 (cells0001_2.getD 19 0) = true := by decide +kernel
theorem cell0001_2_21 : cellOK w0001 A0001 2 778 21 (cells0001_2.getD 20 0) = true := by decide +kernel
theorem cell0001_2_22 : cellOK w0001 A0001 2 778 22 (cells0001_2.getD 21 0) = true := by decide +kernel
theorem cell0001_2_23 : cellOK w0001 A0001 2 778 23 (cells0001_2.getD 22 0) = true := by decide +kernel
theorem cell0001_2_24 : cellOK w0001 A0001 2 778 24 (cells0001_2.getD 23 0) = true := by decide +kernel
theorem cell0001_2_25 : cellOK w0001 A0001 2 778 25 (cells0001_2.getD 24 0) = true := by decide +kernel
theorem cell0001_2_26 : cellOK w0001 A0001 2 778 26 (cells0001_2.getD 25 0) = true := by decide +kernel
theorem cell0001_2_27 : cellOK w0001 A0001 2 778 27 (cells0001_2.getD 26 0) = true := by decide +kernel
theorem cell0001_2_28 : cellOK w0001 A0001 2 778 28 (cells0001_2.getD 27 0) = true := by decide +kernel
theorem cell0001_2_29 : cellOK w0001 A0001 2 778 29 (cells0001_2.getD 28 0) = true := by decide +kernel
theorem cell0001_2_30 : cellOK w0001 A0001 2 778 30 (cells0001_2.getD 29 0) = true := by decide +kernel

theorem cells0001_2_ok : ∀ p1, 1 ≤ p1 → p1 ≤ 30 → cellOK w0001 A0001 2 778 p1
    (cells0001_2.getD (p1 - 1) 0) = true :=
  all30
    cell0001_2_1 cell0001_2_2 cell0001_2_3 cell0001_2_4 cell0001_2_5 cell0001_2_6 cell0001_2_7 cell0001_2_8
    cell0001_2_9 cell0001_2_10 cell0001_2_11 cell0001_2_12 cell0001_2_13 cell0001_2_14 cell0001_2_15 cell0001_2_16
    cell0001_2_17 cell0001_2_18 cell0001_2_19 cell0001_2_20 cell0001_2_21 cell0001_2_22 cell0001_2_23 cell0001_2_24
    cell0001_2_25 cell0001_2_26 cell0001_2_27 cell0001_2_28 cell0001_2_29 cell0001_2_30

def cells0001_3 : List Nat := [
  0x4f0c278613c309e184f0c278613c309e184f0c278613c309e184f0c278613c309e184f0c278613c309e184f0c278613c309e184f0c278613c309e18cd0c681413c319818920c56062b0309e19560c5a8613c309e18820c5a0613c30b018720c2786160322450dd0c408624030b0184b0c600612c309e19480c2586200310018590c5d8612c3094188a0c260612c307e18770d0d061583066186d0c328621430d618320c4b860ac30a4182f0c3f8629831b2183c0c3b861ec304018860c2b8606c305c18080c048613c3,
  0x278613c309e184f0c278613c309e184f0c278613c309e184f0c278613c309e184f0c278613c309e184f0c278613c309e184f0c278613c309e184f0c278613c3124184f0c570613c309e184f0c278613c315818930c2c862f4310618ac0c629420c32a6184f0c2786160309418be0c88060f8309618810c278613c309418580c25061ac30d818610c4c860f830ac184b0c76940f4a04c189e0c370615c30a8190a0ca8062fc3296187f0c4386180305450a4283d061bc305e186c0c260605030bc184f0c278613c3,
  0x17c30be185f0c2f8617c30be185f0c2f8617c30be185f0c2f8617c30be185f0c2f8617c30be185f0c2f8617c30be185f0c2f8617c30be185f0c2f8617c30be185f0c2f8617c30be185f0c2f8617c30be185f0c2f8617c30be185f0c2f8617c30be185f0c2f861d030f6185f0c7c0631030e8185f0c2f8615c30ae185e0c2b8615c30b01925282f86264308018740c2494150a08418580c72862b830f218b60c2006124a1b218430c2006108308018430c55062a032f418ba0c8a94444308418610c208614030be18d90c0e060cc30a618b20c4b06330306418960c28860a43030185f0c2f8617c3,
  0xc86064303218190c0c86064303218190c0c86048302418190c0b8604430dc18190c1086124309018190c0b861d830c218940c3786210308e18210c3f064b4310818210c2f06068302a18190c0c860643,
  0x3f0c1f860fc307e183f0c1f860fc307e183f0c1f860fc307e183f0c1f860fc307e183f0c1f860fc307e183f0c1f860fc307e183f0c1f860fc307e183f0c1f860fc307e183f0c1f86180307e183f0c1f8613c309e183f0c27861b430ae183f0c4f0613c309e183f0c1f860744122191a0c1f8615c302620610c2b8602840d619330c310604c401420d70c060812c309e18730c310629c3142503f0c1f860fc3,
  0x15860ac3056182b0c15860ac3056182b0c15860ac3056182b0c15860ac3056182b0c15860ac3056182b0c15860a83054182b0c51060d03068182b0c15861683056182a0c1a06240313a502b0c668605030b4182b0c41863d8303818a40c92064dc30fa189d0c30941bc307e182b0c15860ac3,
  0x3c061e030f018780c3c061e030f018780c3c061e030f018780c3c061e030f018780c3c061e030f018780c3c061e030f018780c3c061e030f018780c3c061e030f018780c3c061e030f018780c3c061e030f018780c3c061e030f018780c3c061e030f018780c3c061e030f018780c3c061e030f018780c3c061e030f018780c3c061e030f018780c3c061e830f018780c3c061e830f018780c3c061e030f018780c3d861e030f018780c3c0625d10f218780c3d8623c30f618780c3c063ec327418d80c3d8628031ae1882282686214310018b00c1e860f03106187a0c4b861c8309a186c28390622031c6183d0c228620c3162504c0c358613030f618990c0a06134a146183e0c1c0604c314218780c3c061e03,
  0x486024301218090c0506028303618090c0506170311418090c3f860b830e818090c04860243,
  0xf0c078603c301e180f0c07060603020180f0c078607c301e180f0c0b8631c306618510ce0061783128180f0c078603c3,
  0x5b862dc316e18b70c5b862dc316e18b70c5b862dc316e18b70c5b862dc316e18b70c5b862dc316e18b70c5b862dc316e18b70c5b862dc316e18b70c5b862dc316e18b70c5b862dc316e18b70c5b862dc316e18b70c5b862dc316e18b70c5b862dc316e18b70c5b862dc316e18b70c5b862dc316e18b70c5b862dc316e18b70c5b862dc316e18b70c5b862dc316e18b70c5b862dc316e18b70c5b862dc316e18b70c5b862dc316e18b70c5b862dc316e18b70c5b862dc316e18b70c5b862dc316e18b70c5b86430322c50b70c86862dc316e18b70d7d062dc316e19100c9c062dc343a18b70c6c86360322c50b70c5086360314218b70c6e862dc316e18fd28a9062fc31ec18a10c6f06374314218b70c508643c321618a10ca0062843284192f0cbd86580322c51380c5b8634c314418c50c5a062f0a116899d0c51862ec31e418a00c1e061c430dc18920c3d061ec3144187f285a06224a140183c0c3d860f030ca18e10c4f060f430f018a10c1e0648030f218640c5e064343056183c0c1586080310e18370c310605c302818b70c5b862dc3,
  0x4d0c2686134309a184d0c2686134309a184d0c2686134309a184d0c2686134309a184d0c2686134309a184d0c2686134309a184d0c2686134309a184d0c2686134309a184d0c2686134309a184d0c2686134309a184d0c2786138309a184d0c278613c309c184d0c2786134309a184f0c7206138309e184d0c27061bc3152184d0c4306374a09c18a10c5106130313218870c948613c30bc184f0c648613830f818980c7186140a04c184d0c26861343,
  0xa914548a2a4515228a914548a2a4515228a914548a2a4515228a914548a2a4515228a914548a2a4515228a914548a2a4515228a914548a2a4515228a914548a2a4515228a914548a2a4515228a914548a2a4515228a914548a2a4515228a914548a2a4515228a914548a2a4515228a914548a2a4515228a914548a2a4515228a914548a2a4515228a914548a2a4515228a914548a2a4515228a914548a2a4515228a914548a2a4515228a914548a2a4515228a914548a2a4515228a914548a2a4515228a914548a2a4515228a914548a2a4515228a914548a2a4515228a914548a2a4515228a914548a2a4515228a914548a2a4515228a914548a2a4515228a914548a2a4515228a914548a2a4515228a914548a2a4515228a914548a2a4515228a914548a2a4515228a914548a2a4515228a914548a2a4515228a914548a2a4515228a914548a2a4515228a914548a2a4515228a914548a2a4515228a914548a2a4515228a914548a2a4515228a914548a2a4515228a914548a2a4515228a914548a2a4515228a914548a2a4515228a914548a2a45152288b0645832a4515228a914458322c1952288b06458322c19160c8b06548a22c19160c8b0645832a45152288b0645032281952288a06450322819160c8a0645832a451140c7986548a22819140ca914450322819160c8a06450322818f30c8a06544a22819140c8a0645831ca515228729466c31f818f30c8a0645031f81951287e063f031e618fc0c6e863f033a019140c7e063f031b819140c7e0637031ca51cb0c8b06378313e18fe0c729437431ca50dc0c8a86394a29818df0c4486530320450f30c440627c311618e528a91422431cc509f0c4586398a12451720c440663c33fa18fb0c4506228311619320c4586220312451690c5406230317651400c448622c313e188b0c45063dc310218890c84062283118194c0c4586314310618b90c46061c830f018800cc386130309a18810c1e86134318618890ca486028301618bb0c2286028308e195228a914548a,
  0x270c138609c304e18270c138609c304e18270c138609c304e18270c438648c304e18270c1386098304a18270c3486098304c19010c1386090304c18250c1386094304e18270c12061dc30b018270c1206144304c18270c138609c3,
  0xa00c5006280314018a00c5006280314018a00c5006280314018a00c5006280314018a00c5006280314018a00c5006280314018a00c5006280314018a00c5006280314018a00c5006280314018a00c5006280314018a00c5006280314018a00c5006280314018a00c5006280314018a00c5006280314018a00c5006280314018a00c5006280314018a00c5006280314018a00c5006280314018a00c5006284314018a00c5006284314018a00c5006284314018a00c5006284314018a00c500635c31d618a00c7586280314018a00c8086280323219c20c5086280314019010c6b8628031ae18eb0c5106358327c18d60c5086354314218d70c3f8634030fe18a00c44061fc31be50a10c7b861a830d4187f0c44861a830d4186a0c3906234315818ab0c350615c30ae18c50c3d862043128507a0c390628830f018570c1f8622c30d41871283c06098a130186a0c0d860d0309e18a00c50062803,
  0x6c18360c1b060d8306c18360c1b060d8306c18360c1b060d8306c18360c1b060d8306c18360c1b060d8306c18360c1b060d8306c18360c1b060d8306c18360c1b060d8306c18360c1b060d4322e18360c1b860dc306e18360c52060d8306a18360c1b860d030d418370c5f0618030e818360c1b060d83,
  0x303018180c0c060604c3026180c0c060604c315a180c0c06060303,
  0x18818c40c6206310318818c40c6206310318818c40c6206310318818c40c6206310318818c40c6206310318818c40c6206310318818c40c6206310318818c40c6206310318818c40c6206310318818c40c6206310318818c40c6206310318818c40c6206310318818c40c6206310318818c40c6206310318818c40c6206310318818c40c6206310318818c40c6206310318818c40c6206310318818c40c6206310318818c40c6206310318818c40c6206310318818c40c6206310318818c40c6206310318818c40c6206310318818c40c6206310318818c40c6206310318818c40c6206310318818c40c6206310318818c40c62063e8318818c40c6286310318818c40c6206310318a18c50c4a94254a18a18c70c62063c831e218c40c4a9431031f4509528460631031f619590c5014454a18819950c6206234316619070c5f945f0319218c70ca306340311819350c5f944b0311818f30c76862543156190228670621c3156188d0c4a06214310a18860c3b0636c30e818bf0c4b0645c314a18870c5e06254a108189b0c2c86080a1b2186e0ca706228304250c40c62063103,
  0x3f861fc30fe187f0c3f861fc30fe187f0c3f861fc30fe187f0c3f861fc30fe187f0c3f861fc30fe187f0c3f861fc30fe187f0c3f861fc30fe187f0c3f861fc30fe187f0c3f861fc30fe187f0c3f861fc30fe187f0c3f861fc30fe187f0c3f861fc30fe187f0c3f861fc30fe187f0c3f861fc30fe187f0c3f861fc30fe187f0c3f861fc30fe187f0c3f861fc30fe187f0c3f861fc30fe187f0c3f861fc30fe187f0c3f863cc30fe187f0c3f861fc3206187f0cb3061fc30fe187e0c3f861fc30fe187f0cd58630430fe18ee0c35061f831e6187f0c3f861ac30d618e90c36063c430fe186d0c5e8634c30fe186b0c34062d830d618722835862703154506c0c1a860fc307a187f0c3f861fc3,
  0x1a060d0306818340c1a060d0306818340c1a060d0306818340c1a060d0306818340c1a060d0306818340c1a060d0306818340c1a060d0306818340c1a060d0306818340c1a860d8306c18340c1a860d4306e18340c1b860d8306a18340c1a060d8306e18340c1a060d03,
  0xa0c05060283014180a0c05060283,
  0x7b0c3d861ec30f6187b0c3d861ec30f6187b0c3d861ec30f6187b0c3d861ec30f6187b0c3d861ec30f6187b0c3d861ec30f6187b0c3d861ec30f6187b0c3d861ec30f6187b0c3d861ec30f6187b0c3d861ec30f6187b0c3d861ec30f6187b0c3d861ec30f6187b0c3d861ec30f6187b0c3d861ec30f6187b0c3d861ec30f6187b0c3d861e830f6187b0c3d861ec30f6187b0c3d061e830f4187b0c3d061e830f6187a0c3d861e830f6187a0c3d861ec30f4187a0c3d8622c3116187b0c3d8622c30f0187b0c4f861f0a0e450880c60861cc30e4187a0c50865a8a1ea18a10c3d0622030d4187a0c45860f4307a18720c61860f4307a187b0c3d861ec3,
  0x1f860fc307e183f0c1f860fc307e183f0c1f860fc307e183f0c1f860fc307e183f0c1f860fc307e183f0c1f860fc307e183f0c1f860fc307e183f0c1f860fc307e183f0c1f860f8307c183f0c1f860fc307c183f0c1f061a030d2183e0c1f061a03078183f0c1e061ec308a186a0c1e861103088183f0c1f860fc3,
  0x6c3036181b0c0d8606c3036181b0c0d8606c3036181b0c0d86074303a181b0c0d86074303a181b0c0d8606c3,
  0x16180b0c058602c3,
  0x130c098604c302618130c098604c302618130c098604c3,
  0x58602c3,
  0x2c3,
  0x2c3,
  0x2c3,
  0x2c3]

theorem cell0001_3_1 : cellOK w0001 A0001 3 778 1 (cells0001_3.getD 0 0) = true := by decide +kernel
theorem cell0001_3_2 : cellOK w0001 A0001 3 778 2 (cells0001_3.getD 1 0) = true := by decide +kernel
theorem cell0001_3_3 : cellOK w0001 A0001 3 778 3 (cells0001_3.getD 2 0) = true := by decide +kernel
theorem cell0001_3_4 : cellOK w0001 A0001 3 778 4 (cells0001_3.getD 3 0) = true := by decide +kernel
theorem cell0001_3_5 : cellOK w0001 A0001 3 778 5 (cells0001_3.getD 4 0) = true := by decide +kernel
theorem cell0001_3_6 : cellOK w0001 A0001 3 778 6 (cells0001_3.getD 5 0) = true := by decide +kernel
theorem cell0001_3_7 : cellOK w0001 A0001 3 778 7 (cells0001_3.getD 6 0) = true := by decide +kernel
theorem cell0001_3_8 : cellOK w0001 A0001 3 778 8 (cells0001_3.getD 7 0) = true := by decide +kernel
theorem cell0001_3_9 : cellOK w0001 A0001 3 778 9 (cells0001_3.getD 8 0) = true := by decide +kernel
theorem cell0001_3_10 : cellOK w0001 A0001 3 778 10 (cells0001_3.getD 9 0) = true := by decide +kernel
theorem cell0001_3_11 : cellOK w0001 A0001 3 778 11 (cells0001_3.getD 10 0) = true := by decide +kernel
theorem cell0001_3_12 : cellOK w0001 A0001 3 778 12 (cells0001_3.getD 11 0) = true := by decide +kernel
theorem cell0001_3_13 : cellOK w0001 A0001 3 778 13 (cells0001_3.getD 12 0) = true := by decide +kernel
theorem cell0001_3_14 : cellOK w0001 A0001 3 778 14 (cells0001_3.getD 13 0) = true := by decide +kernel
theorem cell0001_3_15 : cellOK w0001 A0001 3 778 15 (cells0001_3.getD 14 0) = true := by decide +kernel
theorem cell0001_3_16 : cellOK w0001 A0001 3 778 16 (cells0001_3.getD 15 0) = true := by decide +kernel
theorem cell0001_3_17 : cellOK w0001 A0001 3 778 17 (cells0001_3.getD 16 0) = true := by decide +kernel
theorem cell0001_3_18 : cellOK w0001 A0001 3 778 18 (cells0001_3.getD 17 0) = true := by decide +kernel
theorem cell0001_3_19 : cellOK w0001 A0001 3 778 19 (cells0001_3.getD 18 0) = true := by decide +kernel
theorem cell0001_3_20 : cellOK w0001 A0001 3 778 20 (cells0001_3.getD 19 0) = true := by decide +kernel
theorem cell0001_3_21 : cellOK w0001 A0001 3 778 21 (cells0001_3.getD 20 0) = true := by decide +kernel
theorem cell0001_3_22 : cellOK w0001 A0001 3 778 22 (cells0001_3.getD 21 0) = true := by decide +kernel
theorem cell0001_3_23 : cellOK w0001 A0001 3 778 23 (cells0001_3.getD 22 0) = true := by decide +kernel
theorem cell0001_3_24 : cellOK w0001 A0001 3 778 24 (cells0001_3.getD 23 0) = true := by decide +kernel
theorem cell0001_3_25 : cellOK w0001 A0001 3 778 25 (cells0001_3.getD 24 0) = true := by decide +kernel
theorem cell0001_3_26 : cellOK w0001 A0001 3 778 26 (cells0001_3.getD 25 0) = true := by decide +kernel
theorem cell0001_3_27 : cellOK w0001 A0001 3 778 27 (cells0001_3.getD 26 0) = true := by decide +kernel
theorem cell0001_3_28 : cellOK w0001 A0001 3 778 28 (cells0001_3.getD 27 0) = true := by decide +kernel
theorem cell0001_3_29 : cellOK w0001 A0001 3 778 29 (cells0001_3.getD 28 0) = true := by decide +kernel
theorem cell0001_3_30 : cellOK w0001 A0001 3 778 30 (cells0001_3.getD 29 0) = true := by decide +kernel

theorem cells0001_3_ok : ∀ p1, 1 ≤ p1 → p1 ≤ 30 → cellOK w0001 A0001 3 778 p1
    (cells0001_3.getD (p1 - 1) 0) = true :=
  all30
    cell0001_3_1 cell0001_3_2 cell0001_3_3 cell0001_3_4 cell0001_3_5 cell0001_3_6 cell0001_3_7 cell0001_3_8
    cell0001_3_9 cell0001_3_10 cell0001_3_11 cell0001_3_12 cell0001_3_13 cell0001_3_14 cell0001_3_15 cell0001_3_16
    cell0001_3_17 cell0001_3_18 cell0001_3_19 cell0001_3_20 cell0001_3_21 cell0001_3_22 cell0001_3_23 cell0001_3_24
    cell0001_3_25 cell0001_3_26 cell0001_3_27 cell0001_3_28 cell0001_3_29 cell0001_3_30

def cells0011_0 : List Nat := [
  0x40204411541008048b020e4107208070418821ec101e0809040f8204820200836080a82030901a08080403820201,
  0x4040382012100808078425c110c100708390413020ee0805083982054101048fa043d02010214c10060803840202,
  0xcb04658232c119608cb04658232c119608cb04658232c119608cb04658232c119608cb04658232c119608cb04658232c119608cb04658232c119608cb04658232c119608cb04658232c119608cb04658232c119608cb04658232c119608cb04658232c119608cb04658232c119608cb04658232c119608cb04658232c119608cb04658232c119608cb04658232c119608cb04658232c119608cb04658232c119608cb04658232c119608cb04658232c119608cb04658232c119608cb04658232c119608cb04658232c119608cb04658232c119608cb04658232c119608cb04658232c119608cb04658232c119608cb04658232c119608cb04658232c119608cb04658232c119608cb04658232c119608f30465827b0219608cb04658232c112a08cb044a82254137e08f5044a82254112a089504320425412a6089504320452c130810cb044a8225411d410ff04d28216c21e41127082d8416c20b410ec082d042b021b60864084c025b411460895043d821ec144e089b04400426c1152092d04950426c2068105c08110442c11a409e704540432010341022080d0407020b4101a081f821fc1064101a08218232020801065044a821b02158083a08478201c103e08cb04658232c1,
  0x34201a100d080684038202c100d082b0421c135e080d086604074104c480d080d0426c1114489f0427040282114080d0806840342,
  0x40a0385012280814078a358108c100714210433c10941005149602318101060ff0411040105322080614038a0205,
  0x16e04b7025b812dc096e04b7025b812dc096e04b7025b812dc096e04b7025b812dc096e04b7025b812dc096e04b7025b812dc096e04b7025b812dc096e04b7025b812dc096e04b7025b812dc096e04b7025b812dc096e04b7025b812dc096e04b7025b812dc096e04b7025b812dc096e04b7025b812dc096e04b7025b812dc096e04b7025b812dc096e04b7025b812dc096e04b7025b812dc096e04b7025b812dc096e04b7025b812dc096e04b7025b812dc096e04b7025b812dc096e04b7025b812dc096e04b7025b812dc096e04b7025b812dc096e04b7025b812dc096e04b7025b812dc096e04b7025b812dc096e04b7025b812dc096e04b7025b812dc096e04b7025b812dc096e04b7025b812dc096e04b7025b812dc096e04b7025b812dc096e04b7025b812dc096e04b7025b812dc096e04b7025b812dc096e04b7025b812dc096e04b7025b812dc096e04b7025b812dc096e04b7025b812dc096e04b7025b812dc096e04b7025b812dc096e04b7025b812dc096e04b7025b813de096e04b7025b8138e096e04f7825b812dc096e04b70288c14d4096e04b7027ec14d4096e04fd827bc12dc0a2304e3827b012dc09ef04b7025f8131c116e04c704638231c116e04c70465013de098e0a1b027ec12f2098e08bf825b812fc09c705350261c245e097904bf025f812fc097e04af025f812fc09ef04af0296022dc097f04d4045b812fc097e0568025f813d8115e049f829d81268099f049a025f812fe09ef058d0479c14060a9504de825cc12bc09e704d1025fc12bc093404d9044d012fe095e049b8266412e6093704bf824d0131e0974049a0250c1286095e209b822dc116e09fd209a022dc116e093704f38250c116e08b7045b8232022680934045b822dc116e08c8085b822dc116e08ce085b8240c116e08b70455022dc120208b704f6021d820ec10b7045b821d820ec10eb0437841d822b408d704d80414c10f6095a20361233c12d4406e082d82be020a609370838045d880b0104e08538223410b0105b0431040a010ca08bb042c040a0124c10580815820ac1058105b043602150212a089a08f202068203808a604058208c1022416e04b7025b81,
  0x4808240412020901048082404120209010480824041202090104808240414824d0104808240412020a4105208240412020a4114c0829043f020901052082904100414021de086f049f0420010c809d20413041c4102e08240412020901,
  0x1280494024a0125009280494024a0125009280494024a0125009280494024a0125009280494024a0125009280494024a0125009280494024a0125009280494024a0125009280494024a0125009280494024a0125009280494024a0125009280494024a0125009280494024a0125009280494024a0125009280494024a0125009280494024a0125009280494024a0125009280494024a0125009280494024a0125009280494024a0125009280494024a0125009280494024a0125009280494024a0125009280494024a0125009280494024a0125009280494024a0125009280494024a0125009280494024a0125009280494024a0125009280494024a0125009280494024a0125009280494024a0125009280494024a0125009280494024a0125009280494024a0125009280494024a0125009280494024a0125009280494024e812500928049d024ec125009280494024a01250093b0494024a01250093a049d02840225009280494024a0145611280494024a01250093a049d024a012500928049d823bc83fc092804b18258c125009280494025082254093a0494024e812760a4608ad823c0123e093b049d0248813044128047e02fa01232093a049f824d011e6093a05a10271812c8099b04bc823dc1232092104bb0448412ec10f7049f825d8236811260496825d82276119a08a3825e412dc116c04aa8230494de08f704bb0432010f4111e243d0441c1226099c086b0465502b209b80863043d81104144e24e0046c0120008bf043804dd010e210fe0821021c4208408c7042f82308210c084204478238821760842042e022dc209410cf04498226810ce0a160864820c820c20854082f82094217e0957081f8220811c609f904048427c202a11280494024a01,
  0x21041082084104208210410820841042082104108208410420821041082084104208210410020841042082104220223c10420821040f8215c10380821040e020b821060821042102060203810210410820841,
  0x2c1016080b04058202c1016080b04058202c1016080b0403c201e101608080403c202e101608440434020c6080f08040412021960816080b040582,
  0x16808b4045a022d0116808b4045a022d0116808b4045a022d0116808b4045a022d0116808b4045a022d0116808b4045a022d0116808b4045a022d0116808b4045a022d0116808b4045a022d0116808b4045a022d0116808b4045a022d0116808b4045a022d0116808b4045a022d0116808b4045a022d0116808b4045a022d0116808b4045a022d0116808b4045a022d0116808b4045a022d0116808b4045a022d0117208b4045c822e4117208b4045c822e4117208b9045c822d0117208b9045c822e4117208b4045a022e4117208b9045c822e4116808b4045c822e4116808b9045a022e4116808b9045c822e4117208b4045a0225011280894044a0222c112808b90445821f81116089404458222c111608b904458222c1168087e04498222c1116088b04870432021fe08930467845c81116087e04458226c1136089b043c0431c111608930467824101280118b044b046c011d4089608538249821ce088e043c04264136608b5083182228116610d504588235c10fa0877087c82070109410b4045a022d01,
  0x35821ac10d6086b0435821ac10d6086b0435821ac10d6086b0435821ac10d6086b0435821ac10d6086b0435821ac10d6086b0435821ac10d6086b0435821ac10d6086b0435821ac10d6086b0435821ac10d6086b0435821ac10d6086b0435821ac10d6086b0435821ac10d6086b0435821ac10d6086b0435821ac10d6086b044a829d0218e086b04480227c118e086b044f8231c110c08900449821ac112a08d00449823cc1266489304450465c113e08cb08d18237c1232089004ff8224c11b0096b08428248821940861049b02614112e086b04e902070202810fe080d840fc1014106b0435821ac1,
  0x1c408e204710238811c408e204710238811c408e204710238811c408e204710238811c408e204710238811c408e204710238811c408e204710238811c408e204710238811c408e204710238811c408e204710238811c408e204710238811c408e204710238811c408e204710238811c408e204710238811c408e204710238811c408e204710238811c408e204710238811c408e204710238811c408e204710238811c408e204710238811c408e204710238811c408e204710238811c408e204710238811c408e204710238811c408e204710238811c408e204710238811c408e204710238811c408e204710238811c408e204e3825c0232810e2050582434159208e2047102388123a0992088e82570221a08e2047102388123a090d048e8238811c408e204710247411c4091d045c8238811c408b904df842e411c408b904758265021d608b9045c822e4117208b90471023ac11c408b904dd04388117208b9045c822e411c40931048e823ac117208b9045c822e4117208b9048e8238411cc08b904e9823ac11cc08b90475823a4119608e20465822e4121c10b9046182430220c11d60469825a021e20927048e04114908a491d084304120908a11e304400479411260889088a8433020c0113304150433c121c087e404c02088213208e20471023881,
  0xc8206410320819040c8206410320819040c8206410320819040c8206410320819040c820fc21601019040c82250202a0819040c820641,
  0x1e410f20879043c821e410f20879043c821e410f20879043c821e410f20879043c821e410f20879043c821e410f20879043c821e410f20879043c821e410f20879043c821e410f20879043c821e410f20879043c821e410f20879043c821e410f20879043c821e410f20879043c821e410f20879043c821e410f20879043c821e410f20879043c821e410f20879043c821e410f20879043c821e410f20879043c8257c121e087904b6041e41128087904a1822e021c010740479821e410f208940436825fc22560879043c8210020801077046982100208010770427822ac108010400984046c4113e0877046d842602064111a0827820d021661079043c821e41,
  0x2420121009080484024201210090804840242,
  0x50c1286094304a18250c1286094304a18250c1286094304a18250c1286094304a18250c1286094304a18250c1286094304a18250c1286094304a18250c1286094304a18250c1286094304a18250c1286094304a18250c1286094304a18250c1286094304a18250c1286094304a18250c1286094304a18250c1286094304a18250c1286094304a18250c1286094304a18250c1286094304a18250c1286094304a18250c1286094304a18250c1286094304a18250c1286094304a18250c1286094304a18250c1286094304a18250c1286094304a18250c1286094304a18250c1286094304a18250c1286094304a18250c1286094304a18250c1286094304a18250c1286094304a18250c1286094304a18250c1286094304a18250c1286094304a18250c1286094304a18250c1286094304a18250c1286094304a18250c1286094304a18250c1286094304a18250c1286094304a18250c1286094304a18250c1286094304a18250c1286094304a18250c1286094304a18250c1286094304a18250c1286094304c9828382326094304ef8464c14fa094304a1824e0141e0a2304eb0450c13ae114304ef0450c133e0a0704df0275c22860b0b054f046b022860b2c04a18268412860a1204b9025a01286093804eb045a0132411df04ab0484812d0094304a1824e012d0096404a182474130e0970051f825a01300098f0863047a8118c121e046304318218c1168049784528227010c608630463825f8118408d80292c141c111d04f382318230e091d04c3822dc243609a808b2024bc239a091d04cd821fc118c1177043f8220411d0112304a302204110209230440821fc110208b7083f8273410ea08f60886826d820ce088104678240810fe08b70863042501154087504240412020ce1081042404120209011a505068233411ae0848082c8225c10ec094304a18250c1,
  0x104108208410420821041082084104208210410820841042082104108208410420821041082084104208210410820841042082104108208410420821041082084104208210410820841042082104108208410420821041082084104208210410820841042082104108208410420821041082084104208210410820841042082104108208410420821041082084104208210410820841042082104108208410420821041082084104350110410820854029f410f41082084a042cc1104108208a684320210411460873823dc118e08c2045304368224c10d4046b0221822fe0882087304698213c487c08a20229c113e08d404b0824401146094e05091015820e608a7043582210209c10820841042082,
  0x214110a0885044282214110a0885044282214110a0885044282214110a0885044282214110a0885044282214110a0885044282214110a0885044282214110a0885044282214110a0885044282214110a0885044282214110a0885044282214110a0885044282214110a0885044282214110a0885044282214110a0885044282214110a0885044282214110a0885044282214110a0885044282214110a0885044282214110a0885044282214110a088504428275c110a08850442822dc116e08850442824cc110a0885042a042dc1150108504260413020a810b1047d02214109810850426041302094104c08438422c10d6084c082504310111408d80425040fc111e0944085d02310221a10850442822141,
  0xb08058402c2016100b08058402c2,
  0x700838041c020e010700838041c020e010700838041c020e010700838041c020e010700838041c020e010700838041c020e010700838041c020e010700838041c020e010700838041c020e010700838041c020e010700838041c020e010700838041c020e010700838041c020e010700838041c020e010700838041c020e010700838041c020e010700838041c020e010700838041c020e01070084f04218224c116f04dd0435022f41070087b041c0211c128a0470022f813ac11db086b822b810dc10af0895021bc20e0113704a9822fc11ca098c085d02490109610700838041c02,
  0x7e083f041f820fc107e083f041f820fc107e083f041f820fc107e083f041f820fc107e083f041f820fc107e083f041f820fc107e083f041f820fc107e083f041f820fc107e083f041f820fc107e083f041f8219c10d2083f041f821901330083f0462822481230095308880212c20d6083f041f820fc1,
  0x261013080984070203810130809840702038101308098404c2,
  0x18100c0806040302,
  0x1a100d0806840342,
  0x241012080904048202410120809040482,
  0x302,
  0x302,
  0x302,
  0x302]

theorem cell0011_0_1 : cellOK w0011 A0011 0 1359 1 (cells0011_0.getD 0 0) = true := by decide +kernel
theorem cell0011_0_2 : cellOK w0011 A0011 0 1359 2 (cells0011_0.getD 1 0) = true := by decide +kernel
theorem cell0011_0_3 : cellOK w0011 A0011 0 1359 3 (cells0011_0.getD 2 0) = true := by decide +kernel
theorem cell0011_0_4 : cellOK w0011 A0011 0 1359 4 (cells0011_0.getD 3 0) = true := by decide +kernel
theorem cell0011_0_5 : cellOK w0011 A0011 0 1359 5 (cells0011_0.getD 4 0) = true := by decide +kernel
theorem cell0011_0_6 : cellOK w0011 A0011 0 1359 6 (cells0011_0.getD 5 0) = true := by decide +kernel
theorem cell0011_0_7 : cellOK w0011 A0011 0 1359 7 (cells0011_0.getD 6 0) = true := by decide +kernel
theorem cell0011_0_8 : cellOK w0011 A0011 0 1359 8 (cells0011_0.getD 7 0) = true := by decide +kernel
theorem cell0011_0_9 : cellOK w0011 A0011 0 1359 9 (cells0011_0.getD 8 0) = true := by decide +kernel
theorem cell0011_0_10 : cellOK w0011 A0011 0 1359 10 (cells0011_0.getD 9 0) = true := by decide +kernel
theorem cell0011_0_11 : cellOK w0011 A0011 0 1359 11 (cells0011_0.getD 10 0) = true := by decide +kernel
theorem cell0011_0_12 : cellOK w0011 A0011 0 1359 12 (cells0011_0.getD 11 0) = true := by decide +kernel
theorem cell0011_0_13 : cellOK w0011 A0011 0 1359 13 (cells0011_0.getD 12 0) = true := by decide +kernel
theorem cell0011_0_14 : cellOK w0011 A0011 0 1359 14 (cells0011_0.getD 13 0) = true := by decide +kernel
theorem cell0011_0_15 : cellOK w0011 A0011 0 1359 15 (cells0011_0.getD 14 0) = true := by decide +kernel
theorem cell0011_0_16 : cellOK w0011 A0011 0 1359 16 (cells0011_0.getD 15 0) = true := by decide +kernel
theorem cell0011_0_17 : cellOK w0011 A0011 0 1359 17 (cells0011_0.getD 16 0) = true := by decide +kernel
theorem cell0011_0_18 : cellOK w0011 A0011 0 1359 18 (cells0011_0.getD 17 0) = true := by decide +kernel
theorem cell0011_0_19 : cellOK w0011 A0011 0 1359 19 (cells0011_0.getD 18 0) = true := by decide +kernel
theorem cell0011_0_20 : cellOK w0011 A0011 0 1359 20 (cells0011_0.getD 19 0) = true := by decide +kernel
theorem cell0011_0_21 : cellOK w0011 A0011 0 1359 21 (cells0011_0.getD 20 0) = true := by decide +kernel
theorem cell0011_0_22 : cellOK w0011 A0011 0 1359 22 (cells0011_0.getD 21 0) = true := by decide +kernel
theorem cell0011_0_23 : cellOK w0011 A0011 0 1359 23 (cells0011_0.getD 22 0) = true := by decide +kernel
theorem cell0011_0_24 : cellOK w0011 A0011 0 1359 24 (cells0011_0.getD 23 0) = true := by decide +kernel
theorem cell0011_0_25 : cellOK w0011 A0011 0 1359 25 (cells0011_0.getD 24 0) = true := by decide +kernel
theorem cell0011_0_26 : cellOK w0011 A0011 0 1359 26 (cells0011_0.getD 25 0) = true := by decide +kernel
theorem cell0011_0_27 : cellOK w0011 A0011 0 1359 27 (cells0011_0.getD 26 0) = true := by decide +kernel
theorem cell0011_0_28 : cellOK w0011 A0011 0 1359 28 (cells0011_0.getD 27 0) = true := by decide +kernel
theorem cell0011_0_29 : cellOK w0011 A0011 0 1359 29 (cells0011_0.getD 28 0) = true := by decide +kernel
theorem cell0011_0_30 : cellOK w0011 A0011 0 1359 30 (cells0011_0.getD 29 0) = true := by decide +kernel

theorem cells0011_0_ok : ∀ p1, 1 ≤ p1 → p1 ≤ 30 → cellOK w0011 A0011 0 1359 p1
    (cells0011_0.getD (p1 - 1) 0) = true :=
  all30
    cell0011_0_1 cell0011_0_2 cell0011_0_3 cell0011_0_4 cell0011_0_5 cell0011_0_6 cell0011_0_7 cell0011_0_8
    cell0011_0_9 cell0011_0_10 cell0011_0_11 cell0011_0_12 cell0011_0_13 cell0011_0_14 cell0011_0_15 cell0011_0_16
    cell0011_0_17 cell0011_0_18 cell0011_0_19 cell0011_0_20 cell0011_0_21 cell0011_0_22 cell0011_0_23 cell0011_0_24
    cell0011_0_25 cell0011_0_26 cell0011_0_27 cell0011_0_28 cell0011_0_29 cell0011_0_30

def cells0011_1 : List Nat := [
  0x40203810120808040782328106c080704860255c12d008050459040742010420804078201010ce10060403820201,
  0x54012a0095004a80254012a0095004a80254012a0095004a80254012a0095004a80254012a0095004a80254012a0095004a80254012a0095004a80254012a0095004a80254012a0095004a80254012a0095004a80254012a0095004a80254012a0095004a80254012a0095004a80254012a0095004a80254012a0095004a80254012a0095004a80254012a0095004a80254012a0095004a80254012a0095004a80254012a0095004a80254012a0095004a80254012a0095004a80254012a0095004a80254012a0095004a80254012a0095004a80254012a0095004a80254012a0095004a80254012a0095004a80254012a0095004a80254012a0095004a80254012a0095004a80254012a0095004a80254012a0095004a80254012a0095004a80254012a0095004a80254012a0095004a80254012a0095004a80254012a0095004a8025e412a0095004a80254012a0095004a80254012a0095004a802540135c095004d70254012a0095004a80268412a009ae04a80254012a009ae04a80268412a0097904a8025e412a0095004a80254012a009a104a8026b812a0095004a8025e412f409ab04bd025e812a009ab04a80254012a00979055d025e812a009af08d20262c23e2117a04a8026d0130c097a04a8025e81348097a04d384a2812a0095004c28466012a009e10925027d8130a115204a8025981214090a04c48252421ba118604ad04574121408dd08b08250c21ba115d04a5843b82180096d24a58430011ba110a04ad0469c218008b804600267412ba098404b90258811da10b8048d024e011ca10c004630236011ba112a04ab028e481b6095304c3044a0122409890434841a422f6111f085b0216820b410c6042d0469c11b0086908600216822ca105a084f023d4209e085a0874021a42208089d0434848e81152106908548423c2310093a0411022b8104808cc04120207c120a085204278434810480822040d040901064084904388412c207a10e0040b820781014081f0444843d4202e115004a8025401,
  0x6302318118c08c6046302318118c08c6046302318118c08c6046302318118c08c6046302318118c08c6046302318118c08c6046302318118c08c6046302318118c08c6046302318118c08c6046302318118c08c6046302318118c08c6046302318118c08c6046302318118c08c6046302318118c08c6046302318118c08c6046302318118c08c6046302318118c08c6046302318118c08c6046302318118c08c6046302318118c08c6046302318118c08c6046302318118c08c6046302318118c08c6046302318118c08c6046302318118c08c6046302318118c08c6046302318118c08c6046302318118c08c6046302318118c08c6046302318118c08c604a102558119008c6049102804218210c6048f0231812ba08c805080231812a2119c047f04320119008b90863023f82226088f0863021b811900903086982304227c090d087a821bc10de088f08478428010de08810837821e8114c089404648420823f409bc042d0216811fa08c6044502338119e1161083b022f810a408b60421846e810e6115f0889022f811540881042e844741104091b08c102268113210be041104294206a48c704098224810360830041e0204c210c08c60463023181,
  0x1b080d8406c2036101b080e8406c203a101b080e84074205e101b0816841d8103a101d084f023ac2138081d080e84360126a101d081684b54213408b0083684188212a107b0439023681164081b080d8406c2,
  0xc0206010300818040c0206010300818040c0214010300818040c0206010300818040b820f4102a0818045d8245480260818040b021f810cc081304098491410281018040c020601,
  0xb01058082c0416020b01058082c0416020b01058082c0416020b01058082c0416020b01058082c04160209c10e4082c0416020b0104e082c0416020d4109208340423820a41058082c04af820c4206210490419020a414744829040982144111c085a045f022f810f2102c0416020b01,
  0xf02078103c081e040f02078103c081e040f02078103c081e040f02074103a081e040f020741040081e040f02078103e081d0413020801056101e04418454420ee101e043b0212c20a8081e040f020781,
  0x134209a104d082684134209a104d082684134209a104d082684134209a104d082684134209a104d082684134209a104d082684134209a104d082684134209a104d082684134209a104d082684134209a104d0826841342112084d08268418810ba104d08268413420ac104c08240212010a00856086d04118108c084d0824020f4116c10480527020f8108008ce049f8217c22d208c4041f021982214103e0426840e810aa103b0473041e422e2104d0826841342,
  0x139049c824e412720939049c824e412720939049c824e412720939049c824e412720939049c824e412720939049c824e412720939049c824e412720939049c824e412720939049c824e412720939049c824e412720939049c824e412720939049c824e412720939049c824e412720939049c824e412720939049c824e412720939049c824e412720939049c824e412720939049c824e412720939049c824e412720939049c824e412720939049c824e412720939049c824e412720939049c824e412720939049c824e412720939049c824e412720939049c824e412720939049c824e412720939049c824e412720939049c824e412720939049c824e412720939049c824e412720939049c824e412720939049c824e412720939049c824e412720939049c824e412720939049c824e412720939049c824e412720939049c824e412720939049c824e412720939049c824e412720939049c824e412720939049c824e412720939049c824e412720939049c824e412720939049c824e412720939049c824e412720939049c824e412720939049c824e412720939049c824e4146e113905ef024e412720926049c824e4173a0939057f02724133c093904bf02dd014da113904d38270c281a114604c882688138c097908810274813e211ee04d2828d41a801277049884408130209ca04da82698127209d004d282438145e121204c10255c22ac0a8920c102574147e49a50562829fc23c4095f0565024c8145c09b904750267c11e209930a23023ac2384093308e184530118c115c048d022e8131c11a0049d8470082020a2e0454826e012000958048e8482c219a090e04598233c138c08ba044f021d8215209830839022fc10b211310872041ac11d6107504308470421e610bf04770217c91fe098d04348418410b21096041b8442c904a0939049c824e41,
  0x48c2246112308918448c2246112308918448c2246112308918448c2246112308918448c2246112308918448c2246112308918448c2246112308918448c2246112308918448c2246112308918448c2246112308918448c2246112308918448c2246112308918448c2246112308918448c2246112308918448c2246112308918448c2246112308918448c2246112308918448c2246112308918448c2246112308918448c2246112308918448c2246112308918448c2246112308918448c2246112308918448c2246112308918448c2246112308918448c2246112308918448c2246112308918448c2246112308918448c2246112308918448c2246112308918448c2246112308918448c2246112308918448c2246112308918448c2246112308918448c2246112308918448c2246112308918448c2246112308918448c2246112308918448c224611230891846fc2414092308918446c2236112309780246c223611230927825a0136a111b08bf0248c257c091b08918446c2336094c04ba847e42442091b08bd8448c23a411230891844c812d8097604b40266812f6119e05800253012b40a1308c9023001180095a048d843001180094d0460022f4118008c0051b842f4139a093204a68260011d008c004d18434811f408c004e684348131e09ae04600261811f409410864023e812ac08d2048802300117c42c604898428421a809290887022f4119009110851041a4219c08e2049d022b8113610a90843021a821d608e8043c841e420f210f0043c841e4219a10bd241902618220c08b60473820d01068089b083c840d010ae08320453042b412900834042b822e420640834044e02318160008320426026301036112308918448c2,
  0x4702238111c088e044702238111c088e044702238111c088e044702238111c088e044702238111c088e044702238111c088e044702238111c088e044702238111c088e044702238111c088e044702238111c088e044702238111c088e044702238111c088e044702238111c088e044702238111c088e044702238111c088e044702238111c088e044702238111c088e044702238111c088e04470237411e6088e044702474111c088e045f022cc1288097a0447023b824660916045482238111c091804470223811fa088e04470226c2242088e046602c68111c088e047f843f813ae088e045e823c01136110f08410236c21b809be04590216c110408930833841042140086508cd843081154098e043e025f0106c08d2044984144115a106d0830020a42050109404088440c10b2088e0447022381,
  0x54202a1015080a84054202a1015080a84054202a1015080a84054202a1015080a840a810a8081d080f04100126a0815080a840542,
  0x6a1035081a840d4206a1035081a840d4206a1035081a840d4206a1035081a840d4206a1035081a840d4206a1035081a840d4206a1035081a840d4206a1035081a842b421a40835081a840a49124083508151242812500872086c8219020600835082e843b812b20830043a021a421ee1035081a840d42,
  0x290114808a4045202290114808a4045202290114808a4045202290114808a4045202290114808a4045202290114808a4045202290114808a4045202290114808a4045202290114808a4045202290114808a4045202290114808a4045202290114808a4045202290114808a4045202290114808a4045202290114808a4045202290114808a4045202290114808a4045202290114808a4045202290114808a4045202290114808a4045202290114808a4045202290114808a4045202290114808a4045202290114808a4045202290114808a4045202304118208a4046082304118208a4046082304118208a4045202290114808a404488232c22d210c1049f0238412a610c1049784220111208e7084482228140208e7091a82244215c088904338491c216e088a046d8421013c2088604338445c110408890462021581110093a042b0229810e210b40441020d810ac084e042b0212c205c08a40452022901,
  0x49022481124089204490224811240892044902248112408920449022481124089204490224811240892044902248112408920449022481124089204490224811240892044902248112408920449022481124089204490224811240892044902248112408920449022481124089204490224811240892044902248112408920449022481124089204490224811240892044902248112408920449022481124089204490224811240892044902248112408920449022481124089204490224811240892044902248112408920449022481124089204490224811240892044902248112408920449022481124089204490224811240892044902248112408920449022481124089204490224811240892044902248112408920449022481124089204490224811240892044902248112408920449022481124089204490224811240892044902248112408920449022481124089204490224811240892044902248112408920449022481124089204490224811240892044902248112408920449022481124089204490220049240880124e022481124089c04490227010f8249c0449022cc1100245da04e0224a10f82492044e0220048f624b3044e021f048fd24688434421a210f824988432821de49380868842fc217a10d108688432821a210d10865842fc21a210bf086884344217e10ca0865042fc21941156046884440116c11c5085f842c811a210d1085b843a813ba0938089102368139c08f824ae8437011c6098904ea822c8118808c604b902368128a085908590253423cc08b50872026341092113c0424842b4215c08d204298427811120959087b021f0137a10c00459020c420c409240892044902,
  0x1c040e020701038081c040e020701038081c040e020701038081c040e020701038081c040e020d81162101c040e02168106c081c040e020701,
  0x10c0886044302218110c0886044302218110c0886044302218110c0886044302218110c0886044302218110c0886044302218110c0886044302218110c0886044302218110c0886044302218110c0886044302218110c0886044302218110c0886044302218110c0886044302218110c0886044302218110c0886044302218110c0886044302218110c088604430221811100886044302218110c0886044302218110c0888044382218110c08880444022f8210e0888043e821f4116c0887045f042201110087d044402220116a087e045702288124008b8043d84348119408b504348448810f211da04788225810d808ae044e126f4209a10d7088584194210c08a5083a840a820541106080a120c4204210860443022181,
  0x236091b048d8246c1236091b048d8246c1236091b048d8246c1236091b048d8246c1236091b048d8246c1236091b048d8246c1236091b048d8246c1236091b048d8246c1236091b048d8246c1236091b048d8246c1236091b048d8246c1236091b048d8246c1236091b048d8246c1236091b048d8246c1236091b048d8246c1236091b048d8246c1236091b048d8246c1236091b048d8246c1236091b048d8246c1236091b048d8246c1236091b048d8246c1236091b048d8246c1236091b048d8246c1236091b048d8246c1236091b048d8246c1236091b048d8246c1236091b048d8246c1236091b048d8246c1236091b048d8246c1236091b048d8246c1236091b048d8246c1236091b048d8246c1236091b048d8246c1236091b048d8246c1236091b048d8246c1236091b048d8246c1236091b048d8246c1236091b048d8246c1236091b048d8246c1236091b048d8246c1236091b048d8246c1236091b048d8246c1236091b048d8246c1236091b048d824801236091b048d8246c1236091b04728246c1236091b048d825042236091b048d823d412f4111b0490023cc123608e504958446c120c0989087e904ac22e2091b0479823f481ea09062072902f811f6094204a702414120a091604a10239481ca40e5208d82418117c08bb04b90271822360905047290480117c090504828239412360905045f02258112c08f2044b02258117609260865022581180092004438241421ca40da04310251420c4086204848254811140862045f0218811aa1062045882230149810620437841042084107d0438821042086111b048d8246c1,
  0x654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ed02654132a099504e98465413a6119504ca82654132a099504ca8265413a611da04ca8276813b4099504ca82654132a09da04ca827441434099504ca82654132a099504ed0265413a611ab04f202aa816da1195050f8487c258211ab053902b9c25040a1f08b5846541322121a04db02718128c11b60519026442322116b08d4826e412d6116b09168264c230c11a9050382730142211b604c48465414a6117304d9026e81a46096b09b1845ac23640b0504f302914128c114608b58465c23140a2408db8279814ea11b204d902514232e114508ca8263c23f40945094882514232610ce08a2848cc24a211c8046e84518220608ce086e8479813da090304b1045e423cc08ce096c84338229c094508670430c1344114508818251412a409ca046182518212c095e045584374212c094e042f841b8112c089604a50225811aa107e042f8417c20fc085f08340235c1134099e044a822681146105f084702198107c089a043b842b4207c099504ca826541,
  0x32a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504ca82654132a099504d382654134e0995055384654132a099505008269c132a09d504ca829a8138e119504d38271c23d612a0053602a04270209c708ca828f014d809a705da845fc26180a5709bd0283c242c0a0e050082d4012fe117f08bf845f824ba429a04ee12614138e11c708e3845fc25a409a108e38468c130a0a3204c702444239e097f09200254823d8120e04df02548237c0b1604e90244423a40a53048884cf012a6121d08df0244423061111088884644222212ba048884938142a09a604f7846b81492098e0488844c412a4094e048a023f4244609e804e702478123c0953088f026f4123c08fd088f024a4126c09c7045b8448c226a091604cf0249412a41185085b84314216e10df085b84408135a0916045b842fc24940918045b842c8126408b708648218811640981045b842d42258091404310237011fa08c9047a8462810d408a804368431812ec088c04900255810ae110304710235421f6119504ca826541,
  0x15c08ae0457022b8115c08ae0457022b8115c08ae0457022b8115c08ae0457022b8115c08ae0457022b8115c08ae0457022b8115c08ae0457022b8115c08ae0457022b8115c08ae0457022b8115c08ae0457022b8115c08ae0457022b8115c08ae0457022b8115c08ae0457022b8115c08ae0457022b8115c08ae0457022b8115c08ae0457022b8115c08ae0457022b8115c08ae0457022b8115c08ae0457022b8115c08ae0457022b8115c08ae0457022b8115c08ae0457022b8115c08ae0457022b8115c08ae0457022b8115c08ae0457022b8115c08ae0457022b8115c08ae0457022b8115c08ae0457022b8115c08ae0457022b8115c08ae0457022b8115c08ae0457022b8112608ae044b021f8112608ae04498224c112608ae04570247811d808ca0449822b812280893044882678114008fd045982288151609d2046f0428811ae108904e5021b4210c08960443921d420ea106d087c82494211c08ae0457022b81,
  0x4c2026101308098404c2026101308098404c2026101308098404c2,
  0x16100b08058402c2,
  0x1308098404c2026101308098404c2026101308098404c2,
  0x221011080884044202210110808840442,
  0x2c2,
  0x2c2,
  0x2c2,
  0x2c2,
  0x2c2]

theorem cell0011_1_1 : cellOK w0011 A0011 1 1359 1 (cells0011_1.getD 0 0) = true := by decide +kernel
theorem cell0011_1_2 : cellOK w0011 A0011 1 1359 2 (cells0011_1.getD 1 0) = true := by decide +kernel
theorem cell0011_1_3 : cellOK w0011 A0011 1 1359 3 (cells0011_1.getD 2 0) = true := by decide +kernel
theorem cell0011_1_4 : cellOK w0011 A0011 1 1359 4 (cells0011_1.getD 3 0) = true := by decide +kernel
theorem cell0011_1_5 : cellOK w0011 A0011 1 1359 5 (cells0011_1.getD 4 0) = true := by decide +kernel
theorem cell0011_1_6 : cellOK w0011 A0011 1 1359 6 (cells0011_1.getD 5 0) = true := by decide +kernel
theorem cell0011_1_7 : cellOK w0011 A0011 1 1359 7 (cells0011_1.getD 6 0) = true := by decide +kernel
theorem cell0011_1_8 : cellOK w0011 A0011 1 1359 8 (cells0011_1.getD 7 0) = true := by decide +kernel
theorem cell0011_1_9 : cellOK w0011 A0011 1 1359 9 (cells0011_1.getD 8 0) = true := by decide +kernel
theorem cell0011_1_10 : cellOK w0011 A0011 1 1359 10 (cells0011_1.getD 9 0) = true := by decide +kernel
theorem cell0011_1_11 : cellOK w0011 A0011 1 1359 11 (cells0011_1.getD 10 0) = true := by decide +kernel
theorem cell0011_1_12 : cellOK w0011 A0011 1 1359 12 (cells0011_1.getD 11 0) = true := by decide +kernel
theorem cell0011_1_13 : cellOK w0011 A0011 1 1359 13 (cells0011_1.getD 12 0) = true := by decide +kernel
theorem cell0011_1_14 : cellOK w0011 A0011 1 1359 14 (cells0011_1.getD 13 0) = true := by decide +kernel
theorem cell0011_1_15 : cellOK w0011 A0011 1 1359 15 (cells0011_1.getD 14 0) = true := by decide +kernel
theorem cell0011_1_16 : cellOK w0011 A0011 1 1359 16 (cells0011_1.getD 15 0) = true := by decide +kernel
theorem cell0011_1_17 : cellOK w0011 A0011 1 1359 17 (cells0011_1.getD 16 0) = true := by decide +kernel
theorem cell0011_1_18 : cellOK w0011 A0011 1 1359 18 (cells0011_1.getD 17 0) = true := by decide +kernel
theorem cell0011_1_19 : cellOK w0011 A0011 1 1359 19 (cells0011_1.getD 18 0) = true := by decide +kernel
theorem cell0011_1_20 : cellOK w0011 A0011 1 1359 20 (cells0011_1.getD 19 0) = true := by decide +kernel
theorem cell0011_1_21 : cellOK w0011 A0011 1 1359 21 (cells0011_1.getD 20 0) = true := by decide +kernel
theorem cell0011_1_22 : cellOK w0011 A0011 1 1359 22 (cells0011_1.getD 21 0) = true := by decide +kernel
theorem cell0011_1_23 : cellOK w0011 A0011 1 1359 23 (cells0011_1.getD 22 0) = true := by decide +kernel
theorem cell0011_1_24 : cellOK w0011 A0011 1 1359 24 (cells0011_1.getD 23 0) = true := by decide +kernel
theorem cell0011_1_25 : cellOK w0011 A0011 1 1359 25 (cells0011_1.getD 24 0) = true := by decide +kernel
theorem cell0011_1_26 : cellOK w0011 A0011 1 1359 26 (cells0011_1.getD 25 0) = true := by decide +kernel
theorem cell0011_1_27 : cellOK w0011 A0011 1 1359 27 (cells0011_1.getD 26 0) = true := by decide +kernel
theorem cell0011_1_28 : cellOK w0011 A0011 1 1359 28 (cells0011_1.getD 27 0) = true := by decide +kernel
theorem cell0011_1_29 : cellOK w0011 A0011 1 1359 29 (cells0011_1.getD 28 0) = true := by decide +kernel
theorem cell0011_1_30 : cellOK w0011 A0011 1 1359 30 (cells0011_1.getD 29 0) = true := by decide +kernel

theorem cells0011_1_ok : ∀ p1, 1 ≤ p1 → p1 ≤ 30 → cellOK w0011 A0011 1 1359 p1
    (cells0011_1.getD (p1 - 1) 0) = true :=
  all30
    cell0011_1_1 cell0011_1_2 cell0011_1_3 cell0011_1_4 cell0011_1_5 cell0011_1_6 cell0011_1_7 cell0011_1_8
    cell0011_1_9 cell0011_1_10 cell0011_1_11 cell0011_1_12 cell0011_1_13 cell0011_1_14 cell0011_1_15 cell0011_1_16
    cell0011_1_17 cell0011_1_18 cell0011_1_19 cell0011_1_20 cell0011_1_21 cell0011_1_22 cell0011_1_23 cell0011_1_24
    cell0011_1_25 cell0011_1_26 cell0011_1_27 cell0011_1_28 cell0011_1_29 cell0011_1_30

def cells0011_2 : List Nat := [
  0x1210110825820242020106b083e8201c22160882082c8204820f60839040f02024202a08a4080582358100c10060403820242,
  0x40402020121008080d04088202210080840042f411141003081d0409c131e081008150408810f808060804840202,
  0x50a0405016280a140d0a40020a01009146a12150207010071446040c02040286408940419020bc089104a60404c8254080814048a0285,
  0x420821041082084104208210410820a4105208210414820a410520821041082084105208210414822a820fe0829043d8209010440829046c0206411e8116e08ac82058103408490410040ac10841016040890044107810210410820841,
  0x880244012200910048802440122009100488024401220091004880244012200910048802440122009100488024401220091004880244012200910048802440122009100488024401220091004880244012200910048802440122009100488024401220091004880244012200910048802440122009100488024401220091004880244012200910048802440122009100488024401220091004880244012200910048802440122009100488024401220091004880244012200910048802440122009100488024401220091004880244012200910048802440122009100488024401220091004880244012200910048802440122009100488024401220091004880244012200910048802440122009100488025482220091004a90454822a4111004a9045482290091004a402548247011560898824c4129009480498824c412600956088802548222009560888025482260093104a90468412ac111004880244012200910049882440122009310488024401220091004e602498126209e50509824801220097d0493024c4123a0910048a8252c128c09db049302398124c094604748249811d60940047302540116a094908f482440118208e90460822d4116a08b50470822d4118208b5045a82234111a08b5047e02234115008c1045a8247411ca088d045a823e4147208b4045a82234116a08b5045a82304108810b204220411020ae08b50422041a8153c805704360216810be08b5042d021a8116a1044082f8221410da084804a1020901074083d040c824502042083c0429822482194105408200209810440819042002044203411100488024401,
  0x708238411c208e104708238411c208e104708238411c208e104708238411c208e104708238411c208e104708238411c208e104708238411c208e104708238411c208e104708238411c208e104708238411c208e104708238411c208e104708238411c208e104708238411c208e104708238411c208e104708238411c208e104708238411c208e104708238411c208e104708238411c208e104708238411c208e104708238411c208e104708238411c208e104708238411c208e104708238411c208e104708238411c208e104708238411c208e104708238411c208e104708238411c208e104708238411c208e10470823a411c208e104708238411d208e1048b82678232208e1048b823a4122e08e104ba0445c122e09b90500023841508111704a4024f82276091704748249c11c208e104708265413420984087d824d41252111704a90437421c009ab04a88225411d81161089a82254144c097e087c8225411d810b7047a825b4112a089504ca022e41302089d08af021bc10ce089c083782254112a089504338236410ba086f04338229822681067044a04274250a08cd045682af410aa094d045082170115811650835821fc10aa109508460218410f21063086f8473012d408ae082b822c021a8086404080406c219a0861047d040c02032112208260401c21de08e10470823841,
  0x16080b04058202c1016080b04058202c1016080b04058202c1016080b04054202a1016080a8411020f60816088e82154115c101508168425020960816080b040582,
  0x2704138209c104e082704138209c104e082704138209c104e082704138209c104e082704138209c104e082704138209c104e082704138209c104e082704138209c104e082704138209c104e082704138209c104e08270413821c2084e085882114208a10e30422841142098104e082a04114220208cd044202118217e084e084682204218011a8045984110208a10b3089f823bc237e08b0044e821c010d0108d044604034200e10b408328200c2142084e0827041382,
  0x34081a040d020681034081a040d020681034081a040d020681034081a040d020701034081a040d8206c1144081a04108217c1106081b0444044541064081a040d020681,
  0x1e820f4107a083d041e820f4107a083d041e820f4107a083d041e820f4107a083d041e820f4107a083d041e820f4107a083d041e821b02198083d041e82400107a083d0447040f4107a08cc041e820f4140c103d041e820f4107a083d04328219010f8103d053e822601076083d0436021b41024105804258222021ba083c04040453410d2083d041e820f41,
  0x8020401020081004080204010200810040802040102008100408020401020081004080204010200818040802040102008148408020c6482008158434021101028080a12020903810200810040802,
  0x730439821cc10e608730439821cc10e608730439821cc10e608730439821cc10e608730439821cc10e608730439821cc10e608730439821cc10e608730439821cc10e608730439821cc10e608730439821cc10e608730439821cc10e608730439821cc10e608730439821cc10e608730439821cc10e608730439821cc10e608730439821cc10e608730439821cc10e608730439821cc10e608730439821cc10e608730439821cc10e608730439821cc10e608730439821cc10e608730439821cc10e608730439821cc10e608730439821cc10e608730439821cc10e608730439821cc10e608730439821cc10e608730439821cc10e608730439821cc10e608730439821cc10e608730439821cc10e608730468411cc10e608a50468412ca08e608730463411cc10e608a28239821cc115b04aa8239821cc10e608730439822ca08e608be02610226a08e6087304b88226a10e608dc8240413581138047f0236411b209360488824341202090104908451412100928049a821f8910c49180878824c8220209f6083f123d021c8107e24a1028c422a8107e246412518213410b4085d82249010410a1043f121b4116808800832822f0133c0894250a821d421081080083c026401200106f0496040d0106808740848040dc1104086508260405c102e083404098205c10ea10e60873043982,
  0x300818040c0206010300818040c0206010300818040c0206010300818040c0206010300818040c8206410300819040c8206010300819040c0206410320819040c0206010300818840e820701032081d0429020601032083802170209e0980043c84108107008300818040c02,
  0x1c200e100708038401c200e100708038401c2,
  0x4c4126209310498824c4126209310498824c4126209310498824c4126209310498824c4126209310498824c4126209310498824c4126209310498824c4126209310498824c4126209310498824c4126209310498824c4126209310498824c4126209310498824c4126209310498824c4126209310498824c4126209310498824c4126209310498824c4126209310498824c4126209310498824c4126209310498824c4126209310498824c4126209310498824c4126209310498824c4126209310498824c4126209310498824c4126209310498824c4126209310498824c4126209310498824c4126209310498824c4126209310498824c4126209310498824c4126209310498824c4126209310498824c4126209310498824c4126209310498824c4126209310498824c4126209310498824c4126209310498824c4126209310498824c4126209310498824c4126209310498824c4126209310498824c4126209310498824c4126209310498824c41262093104b8824e412620931049882620228609310498825e422f4117a0898825e422e209430498825e8226209390523024c412b2098008988256412701171048b045c0222c1138088b04720227011f5089c045641286093808bc843d0222c1131049c0456c22b209160898824c412ae0959047a0445822be0931049c043d0215a093a04ac8253c12fa093104d0025a412620a68090c824a412b2090d048b04390234a08ad047a04404115a08e508a18268012b81116084a82644120a09b9047182254112a091608988251410ea0875043a8232811c01075044d123ac1182087504948220021001075045d023b0124c08870483041cc107410bd0448844d4107210ac04220411821cc10cb044004134113209310498824c41,
  0x18a08c5046282314118a08c5046282314118a08c5046282314118a08c5046282314118a08c5046282314118a08c5046282314118a08c5046282314118a08c5046282314118a08c5046282314118a08c5046282314118a08c5046282314118a08c5046282314118a08c5046282314118a08c5046282314118a08c5046282314118a08c5046282314118a08c5046282314118a08c5046282314118a08c5046282314118a08c5046282314118a08c5046282314118a08c5046282314118a08c5046282314118a08c5046282314118a08c5046282314118a08c5046282314118a08c5046282314118a08c5046282314118a08c504dc82c28218a08c504bc84314143210c504d282504135808c50479043c8218a08c5047a0427c11ba0976086282544113e08fc08d58231c118a08dd0462826441242089f047b0466c11f810dd04ec043f0217a08c504b0822f4118410c504610464013fa08db050b829dc11981120406e02208213e08a9045d0227012100900088d821d410ea0880043c842e82292089a045304224108208d50436821d411aa10a9043804178202610c50462823141,
  0x17c10be085f042f8217c10be085f042f8217c10be085f042f8217c10be085f042f8217c10be085f042f8217c10be085f042f8217c10be085f042f8217c10be085f042f8217c10be085f042f8217c10be085f042f8217c10be085f042f8217c10be085f042f8217c10be085f042f8217c10be085f042f8217c10be085f04860217010be085f044b8223010be085f042f8265c10be085f04328217010ba08f1042f8221010ba085d04410218c81241120041a82304108c485d044a8225421e6085f042f8217c1,
  0x9080484024201210090804840242,
  0x4a0225011280894044a0225011280894044a0225011280894044a0225011280894044a0225011280894044a0225011280894044a0225011280894044a0225011280894044a0225011280894044a0225011280894044a0225011280894044a0225011280894044a0225011280894044a0225011280894044a0225011280894044a0225011280894044a0225011280894044a0225011280894044a0225011280894044a0225011280894044a0225011280894044a0225011280894044a0225011280894044a0225011280894044a0225011280894044a0225011280894044a0225011280894044a0225011280894044a0225011280894044a0225011280894044a0225011280894044a0225011280894044a0225011280894044a0225011280894044a0225011280894044a0225011280894044a0225011280894044a0225011280894044a0225011280894044a0225011280894044a0225011280894044a0225011280894044a0225011280894044a0225011280894044a0225011280894044a0225011280894044a0225011280894044a0225011280894044a0225011280894044a0225011280894044a0225011280894044a0229009280894044a02250112808728239411ca0aa904940439412000928089404428129408e5045882428121a090004728267411ca09490458823941250113b08588239411ca08e50472822c412d408b1045882330121a08e5045882394144c10e5046c824cc12a048b104b08263c11b209c8085882314121a08d9047a04678116208da047282128209410d904588220c135e08c90825041202094104a082504128211209e2087c821b02122084a08250421820d209280894044a02,
  0x25041282094104a0825041282094104a0825041282094104a0825041282094104a0825041282094104a0825041282094104a0825041282094104a0825041282094104a0825041282094104a0825041242092104a0824841242094104a0824841282094104908248414820a4104908290417c10d2084a092e1017c1130104a083a0227c119410690466821c410ca084a0825041282,
  0x682034101a080d040682034101a080d040682034101a080d040442022101a080d040442022101a080d040682,
  0x14100a0805040282,
  0x16100b08058402c2,
  0x201010080804040202010100808040402,
  0x282,
  0x282,
  0x282,
  0x282,
  0x282,
  0x282]

theorem cell0011_2_1 : cellOK w0011 A0011 2 1359 1 (cells0011_2.getD 0 0) = true := by decide +kernel
theorem cell0011_2_2 : cellOK w0011 A0011 2 1359 2 (cells0011_2.getD 1 0) = true := by decide +kernel
theorem cell0011_2_3 : cellOK w0011 A0011 2 1359 3 (cells0011_2.getD 2 0) = true := by decide +kernel
theorem cell0011_2_4 : cellOK w0011 A0011 2 1359 4 (cells0011_2.getD 3 0) = true := by decide +kernel
theorem cell0011_2_5 : cellOK w0011 A0011 2 1359 5 (cells0011_2.getD 4 0) = true := by decide +kernel
theorem cell0011_2_6 : cellOK w0011 A0011 2 1359 6 (cells0011_2.getD 5 0) = true := by decide +kernel
theorem cell0011_2_7 : cellOK w0011 A0011 2 1359 7 (cells0011_2.getD 6 0) = true := by decide +kernel
theorem cell0011_2_8 : cellOK w0011 A0011 2 1359 8 (cells0011_2.getD 7 0) = true := by decide +kernel
theorem cell0011_2_9 : cellOK w0011 A0011 2 1359 9 (cells0011_2.getD 8 0) = true := by decide +kernel
theorem cell0011_2_10 : cellOK w0011 A0011 2 1359 10 (cells0011_2.getD 9 0) = true := by decide +kernel
theorem cell0011_2_11 : cellOK w0011 A0011 2 1359 11 (cells0011_2.getD 10 0) = true := by decide +kernel
theorem cell0011_2_12 : cellOK w0011 A0011 2 1359 12 (cells0011_2.getD 11 0) = true := by decide +kernel
theorem cell0011_2_13 : cellOK w0011 A0011 2 1359 13 (cells0011_2.getD 12 0) = true := by decide +kernel
theorem cell0011_2_14 : cellOK w0011 A0011 2 1359 14 (cells0011_2.getD 13 0) = true := by decide +kernel
theorem cell0011_2_15 : cellOK w0011 A0011 2 1359 15 (cells0011_2.getD 14 0) = true := by decide +kernel
theorem cell0011_2_16 : cellOK w0011 A0011 2 1359 16 (cells0011_2.getD 15 0) = true := by decide +kernel
theorem cell0011_2_17 : cellOK w0011 A0011 2 1359 17 (cells0011_2.getD 16 0) = true := by decide +kernel
theorem cell0011_2_18 : cellOK w0011 A0011 2 1359 18 (cells0011_2.getD 17 0) = true := by decide +kernel
theorem cell0011_2_19 : cellOK w0011 A0011 2 1359 19 (cells0011_2.getD 18 0) = true := by decide +kernel
theorem cell0011_2_20 : cellOK w0011 A0011 2 1359 20 (cells0011_2.getD 19 0) = true := by decide +kernel
theorem cell0011_2_21 : cellOK w0011 A0011 2 1359 21 (cells0011_2.getD 20 0) = true := by decide +kernel
theorem cell0011_2_22 : cellOK w0011 A0011 2 1359 22 (cells0011_2.getD 21 0) = true := by decide +kernel
theorem cell0011_2_23 : cellOK w0011 A0011 2 1359 23 (cells0011_2.getD 22 0) = true := by decide +kernel
theorem cell0011_2_24 : cellOK w0011 A0011 2 1359 24 (cells0011_2.getD 23 0) = true := by decide +kernel
theorem cell0011_2_25 : cellOK w0011 A0011 2 1359 25 (cells0011_2.getD 24 0) = true := by decide +kernel
theorem cell0011_2_26 : cellOK w0011 A0011 2 1359 26 (cells0011_2.getD 25 0) = true := by decide +kernel
theorem cell0011_2_27 : cellOK w0011 A0011 2 1359 27 (cells0011_2.getD 26 0) = true := by decide +kernel
theorem cell0011_2_28 : cellOK w0011 A0011 2 1359 28 (cells0011_2.getD 27 0) = true := by decide +kernel
theorem cell0011_2_29 : cellOK w0011 A0011 2 1359 29 (cells0011_2.getD 28 0) = true := by decide +kernel
theorem cell0011_2_30 : cellOK w0011 A0011 2 1359 30 (cells0011_2.getD 29 0) = true := by decide +kernel

theorem cells0011_2_ok : ∀ p1, 1 ≤ p1 → p1 ≤ 30 → cellOK w0011 A0011 2 1359 p1
    (cells0011_2.getD (p1 - 1) 0) = true :=
  all30
    cell0011_2_1 cell0011_2_2 cell0011_2_3 cell0011_2_4 cell0011_2_5 cell0011_2_6 cell0011_2_7 cell0011_2_8
    cell0011_2_9 cell0011_2_10 cell0011_2_11 cell0011_2_12 cell0011_2_13 cell0011_2_14 cell0011_2_15 cell0011_2_16
    cell0011_2_17 cell0011_2_18 cell0011_2_19 cell0011_2_20 cell0011_2_21 cell0011_2_22 cell0011_2_23 cell0011_2_24
    cell0011_2_25 cell0011_2_26 cell0011_2_27 cell0011_2_28 cell0011_2_29 cell0011_2_30

def cells0011_3 : List Nat := [
  0x12100f0808840242022107308460215c1082102f082c020bc2092104004298228011a610cf04218235c21b610cc0466020242,
  0x404044212c08080831821b42108080708418411c101e100908458404010201084040a842cc218808080803840202,
  0x302030100e0806040b0225010b60805041f021a8115e100304a502034201440040402820181,
  0x538129c094e04a702538129c094e04a702538129c094e04a702538129c094e04a702538129c094e04a702538129c094e04a702538129c094e04a702538129c094e04a702538129c094e04a702538129c094e04a702538129c094e04a702538129c094e04a702538129c094e04a702538129c094e04a702538129c094e04a702538129c094e04a702538129c094e04a702538129c094e04a702538129c094e04a702538129c094e04a702538129c094e04a702538129c094e04a702538129c094e04a702538129c094e04a702538129c094e04a702538129c094e04a702538129c094e04a702538129c094e04a702538129c094e04a702538129c094e04a702538129c094e04a702538129c094e04a702538129c094e04a702538129c094e04a702538129c094e04a702538129c094e04a702538129c094e04a702538129c094e04a7025e0129c094e04a702538129c094e04a702538129c094e04a7025e01358094e04d602538129c094e04bb8267c129c094e04a7025e0129c097704cf8253812f0097704a702538129c094e04a702538129c094e04bc025e0129c094e04a7025e0129c094e04d6845e0129c094e04d6026a4129c094e04a7025e013de11a604bc026c812ee097804d60253812ee094e04d90253812ee094e04cd928d01306114e04c184474221009a204c604538135209b204840236c22b6099f04a48442011b61238086d8436c2210094e04840252421b610db086e0251c216c092508a4842f813ee10db08f402694216c08dc045b024a014660997046e027d821d610db09418238c234a097b08a90236413121166046c843641238091d08810235813ee093004338419c2250098508d00236410b0115004338419c2264119a044c84284114808f404f00215c210408d7086c8429010e808eb0869029ac20ce104d0433842dc109a113804100211c1044086708110207410a4086708410218010440822040c040841074081d047c040281026081f0410021141004094e04a7025381,
  0x98404c2026101308098404c2026101308098402c2016101308058402c20e40813081e040542016101308040405420a2100c0922020ec21e6101308098404c2,
  0x6508328419420ca106508328419420ca106508328419420ca106508328419420ca106508328419420ca106508328419420ca106508328419420ca106508328419420ca106508328419420ca106508328419420ca106508328419420ca106508328419420ca106508328419420ca106508328419420c6106508320419420c6106508328418c2322086508318419420ca106508328427810ca106408500440c214410630832845e8119408df0844024401104086508c20222010c008650830022fc128e1082042a020a810f2088504368410420e00881044b842e020c0085308380401c220010650832841942,
  0xa84054202a1015080a84054202a1015080a84054202a101508100407c2032101508138404c202a1015081e024301040101708290204420400815080a840542,
  0x1208090404820241014080904050214c204c0809041d020e8104a40090404820241,
  0x300218010c0086004300218010c0086004300218010c0086004300218010c0086004300218010c0086004300218010c0086004300218010c0086004300218010c0086004300218010c0086004300218010c0086004300218010c0086004300218010c0086004300218010c008600430021ec1170086004300218010c0086004300218010c00860044402180110a087b044402158111008a3089c043dc216208f104b884124207e108804488410421180888041d845e0105408cc041e022301078096204318416412b80834040b84248115008600430021801,
  0x15108a88454422a2115108a88454422a2115108a88454422a2115108a88454422a2115108a88454422a2115108a88454422a2115108a88454422a2115108a88454422a2115108a88454422a2115108a88454422a2115108a88454422a2115108a88454422a2115108a88454422a2115108a88454422a2115108a88454422a2115108a88454422a2115108a88454422a2115108a88454422a2115108a88454422a2115108a88454422a2115108a88454422a2115108a88454422a2115108a88454422a2115108a88454422a2115108a88454422a2115108a88454422a2115108a88454422a2115108a88454422a2115108a88454422a2115108a88454422a2115108a88454422a2115108a88454422a2115108a88454422a2115108a88454422a2115108a88454422a2115108a88454422a2115108a88454422a2115108a88454422a2115108a88454422a2115108a88454422a2115108a88454422a2115108a88454422a2115108a88454422a2115108a88454422a2115108a88454422a2115108a8845442304098204c1025442304095108c1026081304098204c1026081304098204c1025442304098204c1026081480098204f0845242292118204f5025242304098204c1026081292114908c3827901292118204da025cc22f8114908c38296c178a09a304a48476012a2114908df845442292118704a8845242316118204a484ab0129211490867025b0119c094908e08452421ba116504c702524219c08ce048d04394219c0949086e84374219c08ce046702338119c08ce04a9024e8121e10ce047284374219c09c404d002b3c222010dd08b18255c229e08dd086e84548143008e508670237421dc1144046284e28124008dd08db0422011e8089a04648278c117a1088044e84498114609df045c843c010c40950044c021b0113a08d708e20246c225810a0045b8215421de08960443822fc2148090c043b842881036106204298404c201e10f404088404c2026115108a8845442,
  0x2d0216810b4085a042d0216810b4085a042d0216810b4085a042d0216810b4085a042d0216810b4085a042d0216810b4085a042d0216810b4085a042d0216810b4085a042d0216810b4085a042d0216810b4085a042d0216810b4085a042d0216810b4085a042d0216810b4085a042d0216810b4085a042d0216810b4085a042d0216810b4085a042d0216810b4085a042d0216810b4085a042d0216810b4085a042d0216810b4085a042d0216810b4085a042d0216810b4085a042d0216810b40855842d0216810b4085a042d0217610ab085d842ac215610b40855842ac215610b4085d842ac20e848b4083a122ec217610bb085a042ec217610b4085a0424c212610b408498424c212610b408598438011761093087e02230216810b3089f826f820ee1107088784294214a10fa0451841b010fe0877084e8431c11a6109d087f023d42126089404281245c210e117308a20224c135a1093047a0223c21e80878043a0212410580893042d84138135809b0052a0226411d0082b0490020ac204008b4085a042d02,
  0x48102408120409020481024081204290204810921012040d0202810140812042084028101608120409020481,
  0x2f8417c20be105f082f8417c20be105f082f8417c20be105f082f8417c20be105f082f8417c20be105f082f8417c20be105f082f8417c20be105f082f8417c20be105f082f8417c20be105f082f8417c20be105f082f841a020be105f086c0217c20be105f08ac021a020be105f089b8217c20be1068082f841a023a808cb042f8417c20be105f08ec021bc20de10ee0437841bc20de105f083784a1410be106f0876022bc20c0117308b18416811d8085f08e78443c20c0106008140213c205e1028041902080204a085f082f8417c2,
  0xe82074103a081d040e82074103a081d040e82074103a081d040e820a81054081d040e82168103a081d040e82088112e101d042c020881042081d040e820741,
  0x8d024681234091a048d024681234091a048d024681234091a048d024681234091a048d024681234091a048d024681234091a048d024681234091a048d024681234091a048d024681234091a048d024681234091a048d024681234091a048d024681234091a048d024681234091a048d024681234091a048d024681234091a048d024681234091a048d024681234091a048d024681234091a048d024681234091a048d024681234091a048d024681234091a048d024681234091a048d024681234091a048d024681234091a048d024681234091a048d024681234091a048d024681234091a048d024681234091a048d024681234091a048d024681234091a048d024681234091a048d024681234091a048d024681234091a048d024681234091a048d024681234091a048d024681234091a048d024681234091a048d024681234091a048d024681234091a048d024681234091a048d024681234091a048d02468126c091a048d0254c1234091a04a9824d81234091a048d02468126e091a04b60247014a4091a04bc8446814100936048d0246812340948088d024501430091a048d024441234091a04a88479422a2111a04888246812a2115308c6823f813000951088382660148009ec0488827b0129c093f044f8445014f408e8046d8247012620a610484027381346119404e1823c411d009a7045202454221e0871089aa04142162109f0857842c4223a107108328219410ca09560420020f812fa08b108328218810c40865041f0218810ba0840041f0229012080862041d02334231408400420023181070106a047a020d410c4091a048d024681,
  0x38201c100e080704038201c1,
  0x6408320419020c8106408320419020c8106408320419020c8106408320419020c8106408320419020c8106408320419020c8106408320419020c81064083204190216010d008320419021881064083204268211c21b0104d04e98211c208e10320419020c81,
  0x26609330499824cc126609330499824cc126609330499824cc126609330499824cc126609330499824cc126609330499824cc126609330499824cc126609330499824cc126609330499824cc126609330499824cc126609330499824cc126609330499824cc126609330499824cc126609330499824cc126609330499824cc126609330499824cc126609330499824cc126609330499824cc126609330499824cc126609330499824cc126609330499824cc126609330499824cc126609330499824cc126609330499824cc126609330499824cc126609330499824cc126609330499824cc126609330499824cc126609330499824cc126609330499824cc126609330499824cc126609330499824cc126609330499824cc126609330499824cc126609330499824cc126609330499824cc1266093304a9024cc1266093304998254812a4093304998254812a4093304a9024cc126609520499824cc1266095204e004a7822a4093304a9024cc12a409330499824cc12a4095204a90254813a211520536825ec2352093304a90274823b611c008998280c93480a7a048e8258412c4097504ed843ec11f60acf087d0258411f408fa04d80274c2350096104b0823e811f608fa04d482474123608fb0492023e8144e4933048a843e811f4091d04b784454233c091b04ba823e8119648fa048c0283011f408fa04e0023e8117e11df048a8488c1260091b048b823e812e210fa057b8425c21f409300445842fc2116110c084984440116008fa04af822c01168088c087d842dc217210c2084b8428c111e10b404580283490fc08b4045a0238420ba487e045402320218610bc0454844cc112c10cf082e923c4106a0970081a821e011000868041d02660107409330499824cc1,
  0x20081004080204010200810040802040102008100408020401,
  0x1208090404820241,
  0x92104908248412420921049082484124209210490824841242092104908248412420921049082484124209210490824841242092104908248412420921049082484124209210490824841242092104908248412420921049082484120256208490824843f012ec08490898021f01092114808248450411d81049087a8414810a4087c042484350109210490824841242,
  0x88204410220811040882044102208110408820441,
  0x241,
  0x241,
  0x241,
  0x241,
  0x241,
  0x241,
  0x241,
  0x241]

theorem cell0011_3_1 : cellOK w0011 A0011 3 1359 1 (cells0011_3.getD 0 0) = true := by decide +kernel
theorem cell0011_3_2 : cellOK w0011 A0011 3 1359 2 (cells0011_3.getD 1 0) = true := by decide +kernel
theorem cell0011_3_3 : cellOK w0011 A0011 3 1359 3 (cells0011_3.getD 2 0) = true := by decide +kernel
theorem cell0011_3_4 : cellOK w0011 A0011 3 1359 4 (cells0011_3.getD 3 0) = true := by decide +kernel
theorem cell0011_3_5 : cellOK w0011 A0011 3 1359 5 (cells0011_3.getD 4 0) = true := by decide +kernel
theorem cell0011_3_6 : cellOK w0011 A0011 3 1359 6 (cells0011_3.getD 5 0) = true := by decide +kernel
theorem cell0011_3_7 : cellOK w0011 A0011 3 1359 7 (cells0011_3.getD 6 0) = true := by decide +kernel
theorem cell0011_3_8 : cellOK w0011 A0011 3 1359 8 (cells0011_3.getD 7 0) = true := by decide +kernel
theorem cell0011_3_9 : cellOK w0011 A0011 3 1359 9 (cells0011_3.getD 8 0) = true := by decide +kernel
theorem cell0011_3_10 : cellOK w0011 A0011 3 1359 10 (cells0011_3.getD 9 0) = true := by decide +kernel
theorem cell0011_3_11 : cellOK w0011 A0011 3 1359 11 (cells0011_3.getD 10 0) = true := by decide +kernel
theorem cell0011_3_12 : cellOK w0011 A0011 3 1359 12 (cells0011_3.getD 11 0) = true := by decide +kernel
theorem cell0011_3_13 : cellOK w0011 A0011 3 1359 13 (cells0011_3.getD 12 0) = true := by decide +kernel
theorem cell0011_3_14 : cellOK w0011 A0011 3 1359 14 (cells0011_3.getD 13 0) = true := by decide +kernel
theorem cell0011_3_15 : cellOK w0011 A0011 3 1359 15 (cells0011_3.getD 14 0) = true := by decide +kernel
theorem cell0011_3_16 : cellOK w0011 A0011 3 1359 16 (cells0011_3.getD 15 0) = true := by decide +kernel
theorem cell0011_3_17 : cellOK w0011 A0011 3 1359 17 (cells0011_3.getD 16 0) = true := by decide +kernel
theorem cell0011_3_18 : cellOK w0011 A0011 3 1359 18 (cells0011_3.getD 17 0) = true := by decide +kernel
theorem cell0011_3_19 : cellOK w0011 A0011 3 1359 19 (cells0011_3.getD 18 0) = true := by decide +kernel
theorem cell0011_3_20 : cellOK w0011 A0011 3 1359 20 (cells0011_3.getD 19 0) = true := by decide +kernel
theorem cell0011_3_21 : cellOK w0011 A0011 3 1359 21 (cells0011_3.getD 20 0) = true := by decide +kernel
theorem cell0011_3_22 : cellOK w0011 A0011 3 1359 22 (cells0011_3.getD 21 0) = true := by decide +kernel
theorem cell0011_3_23 : cellOK w0011 A0011 3 1359 23 (cells0011_3.getD 22 0) = true := by decide +kernel
theorem cell0011_3_24 : cellOK w0011 A0011 3 1359 24 (cells0011_3.getD 23 0) = true := by decide +kernel
theorem cell0011_3_25 : cellOK w0011 A0011 3 1359 25 (cells0011_3.getD 24 0) = true := by decide +kernel
theorem cell0011_3_26 : cellOK w0011 A0011 3 1359 26 (cells0011_3.getD 25 0) = true := by decide +kernel
theorem cell0011_3_27 : cellOK w0011 A0011 3 1359 27 (cells0011_3.getD 26 0) = true := by decide +kernel
theorem cell0011_3_28 : cellOK w0011 A0011 3 1359 28 (cells0011_3.getD 27 0) = true := by decide +kernel
theorem cell0011_3_29 : cellOK w0011 A0011 3 1359 29 (cells0011_3.getD 28 0) = true := by decide +kernel
theorem cell0011_3_30 : cellOK w0011 A0011 3 1359 30 (cells0011_3.getD 29 0) = true := by decide +kernel

theorem cells0011_3_ok : ∀ p1, 1 ≤ p1 → p1 ≤ 30 → cellOK w0011 A0011 3 1359 p1
    (cells0011_3.getD (p1 - 1) 0) = true :=
  all30
    cell0011_3_1 cell0011_3_2 cell0011_3_3 cell0011_3_4 cell0011_3_5 cell0011_3_6 cell0011_3_7 cell0011_3_8
    cell0011_3_9 cell0011_3_10 cell0011_3_11 cell0011_3_12 cell0011_3_13 cell0011_3_14 cell0011_3_15 cell0011_3_16
    cell0011_3_17 cell0011_3_18 cell0011_3_19 cell0011_3_20 cell0011_3_21 cell0011_3_22 cell0011_3_23 cell0011_3_24
    cell0011_3_25 cell0011_3_26 cell0011_3_27 cell0011_3_28 cell0011_3_29 cell0011_3_30

def cells0111_0 : List Nat := [
  0x1e000f000780038001c000f0007800680030000f00278011800a8380e000800300001c0010000780098002e0060001c001b000a6000f00078003c0,
  0x300030000e0006000b000fc00b80005002200140005e0003001380068001438040002800180,
  0x15800ac0056002b0015800ac0056002b0015800ac0056002b0015800ac0056002b0015800ac0056002b0015800ac0056002b0015800ac0056002b001e000ac0110002b00170e0f0006e002b0024000c800e8005d0013801100126003c00210002800260068001a001140004002b0015800ac0,
  0x3c001e000f00078003c001e000f00078003c001e000f000780038001e000e00070003c001e000e0005800c0001e00130004c003c001e006f801cc0026001c0009801ac01140013003a80090002a001e000f000780,
  0x16000b0005800280014000b0005800580028000b003a002b000e2000a0006001400014000b00058002c0,
  0x1f000f8007c003e001f000f8007c003e001f000f8007c003e001f00100007c003e001f000f8007c0040001f000f800a0003e001f00110007c003c001f002f800a0003e001f00288007c0068001f000f8007c0,
  0x120009000480024001400090005002ac02200009002e001f0004a38090004800240,
  0x4c0026001300098004c00260013000980048002200130008800480022001300088004c0026001100238004c0164001300098004c0,
  0x9000480024001200090004800240012000900048002400120009000480024001200090004800240012000900048002400120007001b8002400440007000340024006e0006c00360078000e00078003e00240012000900,
  0x1f000f8007c003e001f000f8007c003e001f000f8007c003e001f000f8007c003e001f000f8007c003e002200110007c003e001f001100088003e00220011000880044001d000e8007c0044001f000f800740044001d000f8007c003e001f000f8007c003e0022000fc0084003e002a000fc0068003a001d800f00068007400c4800d00040003e001f000f80,
  0x48002400120009000480024001200550004800ac0012000d0002800140012002700028001600120009000480,
  0xcc006600330019800cc006600330019800cc006600330019800cc006600330019800cc006600330019800cc006600330019800cc006600330019800cc006600330019800cc006600330019800cc006600330019800cc006600330036800e8005c00fd1c1c000cc008800330019800cc0,
  0xf00078003c001e000f00078003c001e000f00078003c001e000f00078003c001e000f00078003c001e000f00078003c001e000f00078003c001e000f00078003c001e000f00078003c001e000f00078003c001e000f00078003c0022000c00060003c001e000bc0078003c002d00234005e00740017801d00088003c001e000f00,
  0x4f00278013c009e004f00278013c009e004f00278013c009e004f00278013c009e004f00278013c009e004f00278013c009e004f00278013c009e004f00278013c009e004f00278013c009e004f00278013c009e004f00278013c009e004f00278013c009e004f003d0020c009e004f0027801200090004f003d80120008e00600041801a001c80048003a001a000a6005c002e0014c00a0006800270015000c0004f00278013c0,
  0x38001c000e000700038001c0,
  0x35c01ae00d7006b8035c01ae00d7006b8035c01ae00d7006b8035c01ae00d7006b8035c01ae00d7006b8035c01ae00d7006b8035c01ae00d7006b8035c01ae00d7006b8035c01ae00d7006b8035c01ae00d7006b8035c01ae00d7006b8035c01ae00d7006b8035c01ae00d7006b8035c01ae00d7006b8035c01ae00d7006b8035c01ae00d7006b8035c01ae00d7006b8035c01ae00d7006b8035c01ae00d7006b8035c01ae00d7006b8035c01ae00d7006b8035c01ae00d7006b8035c01ae00d7006b8035c01ae00d7006b8035c01ae00d7006b8035c01ae00d7006b8035c01ae00d7006b8035c01ae00d7006b8035c01ae00d700698035c01ae00d7006b8035c01ae00d7006b8035c01a600d700698034c01ae00d3006b8034c01a600d300698035c01a600d700698034801c438d3006b803fc01a600d300780034c044000d200690034801a6015800690041c01ae0111006d803480210012900420034801ae01001c4200210007c3884001f0e0f8708c38d700230e118708c38d2004200118721800461c6f000f8718600461c230e0f8708c388400230e210007c3943004a0012c009600c3006c0012c007a38ac00248e11800a00099002600118008c00d7006b8035c0,
  0x92004900248012400920049002480124009200490024801240092004900248012400920049002480124009200490024801240092004900248012400920049002480124009200490024801240092004900248012400920049002480124009200490024801240092004900248012400920049002480124009200490024801240092004900248012400920049002480124009200490024801240092004900248012400920062802480124009200490024801240092006280248018a00bc005e00248012400c500af8023001380092007800380021e00bc0046002e871180093006400480011800e000320019000c8008c004e001d40104008c004600128009400820056001280094008600320034001aa004a00250018000a80047002a0011c00a4008000230e120013600920049002480,
  0x20001000080004000200010000800040002000100008000400,
  0x1200090004800240,
  0xac0056002b0015800ac0056002b0015800ac0056002b0015800ac0056002b0015800ac0056002b0015800ac0056002b0015800ac0056002b0015800ac0056002b0015800ac0056002b0015800ac0056002b0015800ac0056002b0015800ac0056002b0015800ac0056002b0015800ac0056002b0018001160056002b002500184385600478027000ac0090002b0025001b00056007b801d0019c0083002b8016c00ac0056002b001580,
  0x88004400220011000880044002200110008800440,
  0x240,
  0x240,
  0x240,
  0x240,
  0x240,
  0x240,
  0x240,
  0x240,
  0x240]

theorem cell0111_0_1 : cellOK w0111 A0111 0 623 1 (cells0111_0.getD 0 0) = true := by decide +kernel
theorem cell0111_0_2 : cellOK w0111 A0111 0 623 2 (cells0111_0.getD 1 0) = true := by decide +kernel
theorem cell0111_0_3 : cellOK w0111 A0111 0 623 3 (cells0111_0.getD 2 0) = true := by decide +kernel
theorem cell0111_0_4 : cellOK w0111 A0111 0 623 4 (cells0111_0.getD 3 0) = true := by decide +kernel
theorem cell0111_0_5 : cellOK w0111 A0111 0 623 5 (cells0111_0.getD 4 0) = true := by decide +kernel
theorem cell0111_0_6 : cellOK w0111 A0111 0 623 6 (cells0111_0.getD 5 0) = true := by decide +kernel
theorem cell0111_0_7 : cellOK w0111 A0111 0 623 7 (cells0111_0.getD 6 0) = true := by decide +kernel
theorem cell0111_0_8 : cellOK w0111 A0111 0 623 8 (cells0111_0.getD 7 0) = true := by decide +kernel
theorem cell0111_0_9 : cellOK w0111 A0111 0 623 9 (cells0111_0.getD 8 0) = true := by decide +kernel
theorem cell0111_0_10 : cellOK w0111 A0111 0 623 10 (cells0111_0.getD 9 0) = true := by decide +kernel
theorem cell0111_0_11 : cellOK w0111 A0111 0 623 11 (cells0111_0.getD 10 0) = true := by decide +kernel
theorem cell0111_0_12 : cellOK w0111 A0111 0 623 12 (cells0111_0.getD 11 0) = true := by decide +kernel
theorem cell0111_0_13 : cellOK w0111 A0111 0 623 13 (cells0111_0.getD 12 0) = true := by decide +kernel
theorem cell0111_0_14 : cellOK w0111 A0111 0 623 14 (cells0111_0.getD 13 0) = true := by decide +kernel
theorem cell0111_0_15 : cellOK w0111 A0111 0 623 15 (cells0111_0.getD 14 0) = true := by decide +kernel
theorem cell0111_0_16 : cellOK w0111 A0111 0 623 16 (cells0111_0.getD 15 0) = true := by decide +kernel
theorem cell0111_0_17 : cellOK w0111 A0111 0 623 17 (cells0111_0.getD 16 0) = true := by decide +kernel
theorem cell0111_0_18 : cellOK w0111 A0111 0 623 18 (cells0111_0.getD 17 0) = true := by decide +kernel
theorem cell0111_0_19 : cellOK w0111 A0111 0 623 19 (cells0111_0.getD 18 0) = true := by decide +kernel
theorem cell0111_0_20 : cellOK w0111 A0111 0 623 20 (cells0111_0.getD 19 0) = true := by decide +kernel
theorem cell0111_0_21 : cellOK w0111 A0111 0 623 21 (cells0111_0.getD 20 0) = true := by decide +kernel
theorem cell0111_0_22 : cellOK w0111 A0111 0 623 22 (cells0111_0.getD 21 0) = true := by decide +kernel
theorem cell0111_0_23 : cellOK w0111 A0111 0 623 23 (cells0111_0.getD 22 0) = true := by decide +kernel
theorem cell0111_0_24 : cellOK w0111 A0111 0 623 24 (cells0111_0.getD 23 0) = true := by decide +kernel
theorem cell0111_0_25 : cellOK w0111 A0111 0 623 25 (cells0111_0.getD 24 0) = true := by decide +kernel
theorem cell0111_0_26 : cellOK w0111 A0111 0 623 26 (cells0111_0.getD 25 0) = true := by decide +kernel
theorem cell0111_0_27 : cellOK w0111 A0111 0 623 27 (cells0111_0.getD 26 0) = true := by decide +kernel
theorem cell0111_0_28 : cellOK w0111 A0111 0 623 28 (cells0111_0.getD 27 0) = true := by decide +kernel
theorem cell0111_0_29 : cellOK w0111 A0111 0 623 29 (cells0111_0.getD 28 0) = true := by decide +kernel
theorem cell0111_0_30 : cellOK w0111 A0111 0 623 30 (cells0111_0.getD 29 0) = true := by decide +kernel

theorem cells0111_0_ok : ∀ p1, 1 ≤ p1 → p1 ≤ 30 → cellOK w0111 A0111 0 623 p1
    (cells0111_0.getD (p1 - 1) 0) = true :=
  all30
    cell0111_0_1 cell0111_0_2 cell0111_0_3 cell0111_0_4 cell0111_0_5 cell0111_0_6 cell0111_0_7 cell0111_0_8
    cell0111_0_9 cell0111_0_10 cell0111_0_11 cell0111_0_12 cell0111_0_13 cell0111_0_14 cell0111_0_15 cell0111_0_16
    cell0111_0_17 cell0111_0_18 cell0111_0_19 cell0111_0_20 cell0111_0_21 cell0111_0_22 cell0111_0_23 cell0111_0_24
    cell0111_0_25 cell0111_0_26 cell0111_0_27 cell0111_0_28 cell0111_0_29 cell0111_0_30

def cells0111_1 : List Nat := [
  0xe000700078001c002e005300230001800e80042003a0002000fe00170013004980046000e00070001c0,
  0x10000800048005c000e0007000780108002200060053803d4007e0006002b80074008a00030002800200,
  0x2f8017c00be005f002f8017c00be005f002f8017c00be005f002f8017c00be005f002f8017c00be005f002f8017c00be005f002f8017c00be005f002f8017c00be005f002f8017c00be005f002f8017c015c005f00568017c0146005f0051802b4015c005f00570017c00d000a3002f8017c00d000ab004b002b800be0068002f802dc011400a300558008470423868000c8e07c7030385f000c0e218014200211c2b80120003038191c1b8e24801147086003d8009c005e0050000d00108004e0038002780058003400811c54000cc003c0057001f0012c002c005f002f8017c0,
  0x20c0106008300418020c0106008300418020c0106008300418020c0106008300418020c0106008300418020c0106008300418020c0106008300418020c0106008300418020c0106008300418020c0106008300418020c0106008300418020c0106008300418020c0106008300418020c0106008300418020c0106008300418020c0106008300418020c0106008300658032c0106008300418020c0106008300418032c0196011000418020c01960083007f801e400f200cb00418020c010600cb003c8018000f200790027801e4009e00cb001f001c0007c0060001f000f800ae0083002b8012c00ca003e00250016c01f4003e0027800f800b6006400248e17c014a385b00238021c006c005b00b9801e0007e0046001d00034012c003e0023000a800a4008300418020c0,
  0xa80054002a0015000a80054002a0015000a80038001c001500098003400c60015000e8018c01100015000a0026c00b2004a002e0011000440015000a800540,
  0xd4006a0035001a800d4006a0035001a800d4006a0035001a800d4006a0035001a800d4006a0035001a800d8006a0035001a800d4006c0035001b000d4006a0035001a800d4006e0035001b001c8008e0035001a8011c007e003500228010801583841001d001ac00ae003600108e01c000e010800238001000bc0035001a800d40,
  0x1000080004000200010000800040002000100008001140022001000238003c008c0010002d00278004a00100008000400,
  0x34001a000d000680034001a000d000680034001a000d000680034001a000d000640034001a000d000680034001a000d0012c00d6001a00270008c0056001a000d000680,
  0x76003b001d800ec0076003b001d800ec0076003b001d800ec0076003b001d800ec0076003b001d800ec0076003b001d800ec0076003b001d800ec0076003b001d800ec0076003b001d800ec0076003b001d800ec0076003b001d800ec0076003b001d800a8010c003b0041001480076005b001f800ec007600630017000ec004a003b001d800ec0,
  0x2400120009000480128009e0009000400158002200090004800240,
  0x78003c001e000f00078003c001e000f0007800600030000f000780208001e000f00078003c0,
  0x99004c8026401320099004c8026401320099004c8026401320099004c8026401320099004c8026401320099004c8026401320099004c8026401320099004c8026401320099004c8026401320099004c8026401320099004c8026401320099004c8026401320099004c8026401320099004c8026401320099004c8026401320099004c8026401320099004c8026401320099004c8026401320099004c8026401320099004c8026401320099004c8026401320099004c802640132009900518028c014600990078002640146009900518039c014600a300670020c013200990041801d4718600990041801b071d401fb005c801a80126008300558028c022e0083003a8e24c0118006c1c368e28c0178006c1cb9801a80172008c005c8017c00d00083001b8015c00ae0083001f8012c006a0035001a800d400a6006e002d8e0d4005a0099004c802640,
  0xb6005b002d8016c00b6005b002d8016c00b6005b002d8016c00b6005b002d8016c00b6005b002d8016c00b6005b002d8016c00b6005b002d8016c00b6005b002d8016c00b6005b002d8016c00b6005b002d8016c00b6005b002d8016c00b6005b002d8016c00b6005b002d8016c00b6005b002d8016c00b6005b002d8016c00b6005b002d8016c00b6005b002d8016c00b6005b002d8016c00b6005b002d8016c00b6005b002d8016c00b6005b002d8016c00b6005b002d8016c00b6005b002d8016c00b6005b002d8016c00b6005b002d8016c00b6005b002d8016c00b6005b002d8016c00b6005b002d8016c00b6005b001c4716c00b6005b802c000f600b6003d801c4716000711c5b802c0014a00b0004200294016c007b00388e1b000f600b0003d802dc00f4007b00388e1b8716c008400388e23400d800d700778018c019e00a1001e8e1f000dc00a5003d801b8011a00f70036001ec017a708300578020c022a00d700258014c016e0074002b800800040003e002e0006000b270b6005b002d80,
  0x700038001c000e000700038001c0,
  0x451c228e114708a38451c228e114708a38451c228e114708a38451c228e114708a38451c228e114708a38451c228e114708a38451c228e114708a38451c228e114708a38451c228e114708a38451c6580114708a38451c228e114719200451c55001ec008a384d1c228e1080084004d1c4600108008400bf0021000fc007e00420023000f4007e00cf0022800d4006c003e00268e17c007400451c228e1147,
  0x134009a004d002680134009a004d002680134009a004d002680134009a004d002680134009a004d002680134009a004d002680134009a004d002680134009a004d002680134009a004d002680134009a004d002680134009a004d002680134009a004d002680134009a004d002680134009a004d002680134009a004d002680134009a004d002680134009a004d002680134009a004d002680134009a004d002680134009a004d002680134009a004d002680134009a004d002680134009a004d002680134009a004d002680134009a004d002680134009a004d002e8010a009a004d002680134009a004d00214010a009a002d8016c00b60117005380248014000c3004d0029c0124005b0067002dc00ec38920049002100152009a007400108008400f2007000108043600950021000fc006e00420021000d4007c009a004d002680,
  0x8b1c458e22c7116388b1c458e22c7116388b1c458e22c7116388b1c458e22c7116388b1c458e22c7116388b1c458e22c7116388b1c458e22c7116388b1c458e22c7116388b1c458e22c7116388b1c458e22c7116388b1c458e22c7116388b1c458e22c7116388b1c458e22c7116388b1c458e22c7116388b1c458e22c7116388b1c458e22c7116388b1c458e22c7116388b1c458e22c7116388b1c458e22c7116388b1c458e22c7116388b1c458e22c7116388b1c458e22c7116388b1c458e22c7116388b1c458e22c7116388b1c458e22c716800851c5a0022c7104008b1c41002080104008b1c458e218023e008700458e21c010e00a3004d802080104008700438020800fe00cc00290033000b20082004100208009a00f50026801340126007a002900148009a008b1c458e22c7,
  0x1000080004000200,
  0xa2005100288014400a2005100288014400a2005100288014400a2005100288014400a2005100288014400a2005100288014400a2005100288014400a2005100288014400a2005100288014400a2005100288014400a2005100288014400a2005100288014400a20051002880114008a0051002700118008a0051002300128008a0045002280114008e004e00230012c0096004500628e0fc007c00510028801440,
  0x1100088004400220011000880044002200110008800440,
  0x200,
  0x200,
  0x200,
  0x200,
  0x200,
  0x200,
  0x200,
  0x200,
  0x200,
  0x200]

theorem cell0111_1_1 : cellOK w0111 A0111 1 623 1 (cells0111_1.getD 0 0) = true := by decide +kernel
theorem cell0111_1_2 : cellOK w0111 A0111 1 623 2 (cells0111_1.getD 1 0) = true := by decide +kernel
theorem cell0111_1_3 : cellOK w0111 A0111 1 623 3 (cells0111_1.getD 2 0) = true := by decide +kernel
theorem cell0111_1_4 : cellOK w0111 A0111 1 623 4 (cells0111_1.getD 3 0) = true := by decide +kernel
theorem cell0111_1_5 : cellOK w0111 A0111 1 623 5 (cells0111_1.getD 4 0) = true := by decide +kernel
theorem cell0111_1_6 : cellOK w0111 A0111 1 623 6 (cells0111_1.getD 5 0) = true := by decide +kernel
theorem cell0111_1_7 : cellOK w0111 A0111 1 623 7 (cells0111_1.getD 6 0) = true := by decide +kernel
theorem cell0111_1_8 : cellOK w0111 A0111 1 623 8 (cells0111_1.getD 7 0) = true := by decide +kernel
theorem cell0111_1_9 : cellOK w0111 A0111 1 623 9 (cells0111_1.getD 8 0) = true := by decide +kernel
theorem cell0111_1_10 : cellOK w0111 A0111 1 623 10 (cells0111_1.getD 9 0) = true := by decide +kernel
theorem cell0111_1_11 : cellOK w0111 A0111 1 623 11 (cells0111_1.getD 10 0) = true := by decide +kernel
theorem cell0111_1_12 : cellOK w0111 A0111 1 623 12 (cells0111_1.getD 11 0) = true := by decide +kernel
theorem cell0111_1_13 : cellOK w0111 A0111 1 623 13 (cells0111_1.getD 12 0) = true := by decide +kernel
theorem cell0111_1_14 : cellOK w0111 A0111 1 623 14 (cells0111_1.getD 13 0) = true := by decide +kernel
theorem cell0111_1_15 : cellOK w0111 A0111 1 623 15 (cells0111_1.getD 14 0) = true := by decide +kernel
theorem cell0111_1_16 : cellOK w0111 A0111 1 623 16 (cells0111_1.getD 15 0) = true := by decide +kernel
theorem cell0111_1_17 : cellOK w0111 A0111 1 623 17 (cells0111_1.getD 16 0) = true := by decide +kernel
theorem cell0111_1_18 : cellOK w0111 A0111 1 623 18 (cells0111_1.getD 17 0) = true := by decide +kernel
theorem cell0111_1_19 : cellOK w0111 A0111 1 623 19 (cells0111_1.getD 18 0) = true := by decide +kernel
theorem cell0111_1_20 : cellOK w0111 A0111 1 623 20 (cells0111_1.getD 19 0) = true := by decide +kernel
theorem cell0111_1_21 : cellOK w0111 A0111 1 623 21 (cells0111_1.getD 20 0) = true := by decide +kernel
theorem cell0111_1_22 : cellOK w0111 A0111 1 623 22 (cells0111_1.getD 21 0) = true := by decide +kernel
theorem cell0111_1_23 : cellOK w0111 A0111 1 623 23 (cells0111_1.getD 22 0) = true := by decide +kernel
theorem cell0111_1_24 : cellOK w0111 A0111 1 623 24 (cells0111_1.getD 23 0) = true := by decide +kernel
theorem cell0111_1_25 : cellOK w0111 A0111 1 623 25 (cells0111_1.getD 24 0) = true := by decide +kernel
theorem cell0111_1_26 : cellOK w0111 A0111 1 623 26 (cells0111_1.getD 25 0) = true := by decide +kernel
theorem cell0111_1_27 : cellOK w0111 A0111 1 623 27 (cells0111_1.getD 26 0) = true := by decide +kernel
theorem cell0111_1_28 : cellOK w0111 A0111 1 623 28 (cells0111_1.getD 27 0) = true := by decide +kernel
theorem cell0111_1_29 : cellOK w0111 A0111 1 623 29 (cells0111_1.getD 28 0) = true := by decide +kernel
theorem cell0111_1_30 : cellOK w0111 A0111 1 623 30 (cells0111_1.getD 29 0) = true := by decide +kernel

theorem cells0111_1_ok : ∀ p1, 1 ≤ p1 → p1 ≤ 30 → cellOK w0111 A0111 1 623 p1
    (cells0111_1.getD (p1 - 1) 0) = true :=
  all30
    cell0111_1_1 cell0111_1_2 cell0111_1_3 cell0111_1_4 cell0111_1_5 cell0111_1_6 cell0111_1_7 cell0111_1_8
    cell0111_1_9 cell0111_1_10 cell0111_1_11 cell0111_1_12 cell0111_1_13 cell0111_1_14 cell0111_1_15 cell0111_1_16
    cell0111_1_17 cell0111_1_18 cell0111_1_19 cell0111_1_20 cell0111_1_21 cell0111_1_22 cell0111_1_23 cell0111_1_24
    cell0111_1_25 cell0111_1_26 cell0111_1_27 cell0111_1_28 cell0111_1_29 cell0111_1_30

def cells0111_2 : List Nat := [
  0xe000f002c8001c001c0079003e0e01401bc0072001880020005a001c0008801140038012900948001c0,
  0x300018000e0006000c0012400b80006001f00108007c0000001e00024005200040003800180,
  0x1a000d0006800300018000d0006801a4002c000d000b80060006a000d000700080001a00180032800d8002a000d0006800340,
  0x200028000a0004000580454007a000300208003400d400020001800100,
  0x36001b000d8006c0036001b000d8006c0036001b000d8006c0036001b000d8006c0036001b000d8006c0036001b000b8006c00360017000d8005c00360017000b8006c00360017000b8005c002e0017000b8005c002e00170017000bc002e00108008400fa002e000f8e0b800a2002e002e80040011c006c00128006400300036001b000d80,
  0x14400a2005100288014400a2005100288014400a2005100288014400a2005100288014400a2005100288014400a2005100288014400a2005100288014400a2005100288014400a2005100288014400a2005100288014400a2005100350020c00a2005100288014400a20051002880144011c386a003500248013400510028801ac015e00510026800800050009a001700080002c0051002d00080001e002800260003800920028006c8012c700e000e00248000c00f800510028801440,
  0x40e038701238081c078e2e800d200071c248e134006e00051c1780078001070c2003300010706c00061c038e0207,
  0x210010800840042002100108008400420021001080084004c0021001300098004c0021001080098004200210014000a0003a0026001300098004c00260014001b4003a0021000e80070004c00210010800840,
  0xc0006000300018000c0006000300018000c0006000300018000c0006000300018000c0006000300018000c0006000300016800b4006000300018000b0005800300016800d80062002d001b000d8005a002c0018000d8004a002d001200118006a002d0012800a4004800300018000c00,
  0x14000a0005000280018001c00050002800140,
  0xd8006c0036001b000d8006c0036001b000d8006c0036001b000d8006c0036001b000d8006c0036001b000d8006c0036001b000d8006c00360017000b8006c0036001b000b4005800360016800b00058002e00530e0e00070002c001c000d00058002c0017000f4006a003e005c000c4005a0036001b000d80,
  0xc4006200310018800c4006200310018800c4006200310018800c4006200310018800c4006200310018800c4006200310018800c4006200310018800c4006200310018800c4006200310018800c4006200310018800c4006200310018800c4006200310018800c4006200310018800c4006200310018801a4006200310018801ee006200310018800c4006200310020801a8006200988014c7110006200310021c00a0389a002b0011c7138390d004b00114008a00481c2680114009e389a002e80124009a0045000880148010400620031001880,
  0x5e002f0017800bc005e002f0017800bc005e002f0017800bc005e002f0017800bc005e002f0017800bc005e002f0017800bc005e002f0017800bc005e002f0017800bc005e002f0017800bc005e002f0017800bc005e002f0017800bc005e002f0017800bc005e002f0017800bc005e002f0023000bc005e002f0017800bc005e00648017800bc005e002f00230016a005e002f0017800bc005e002f0017800bc00ba00748017800bc009100268017800bc005e002680204008a00b400260011800ac005e002f001780,
  0x700038001c000e000700038001c0,
  0x16800b4005a002d0016800b4005a002d0016800b4005a002d0016800b4005a002d0016800b4005a002d0016800b4005a002d0016800b4005a002d0016800b4005a002d0016800b4005a002d0016800b4005a002d0016800b4005a002d0016800b4005a002d0016800b4005a002d0016800b4005a002d0016800da0062002d0022070ea005a00398018800ea00af002d002d000f4005a00208010400820062002080104008200ad00850017800a4004100208017800a4005a002d001680,
  0x4900248012400920049002480124009200490024801240092004900248012400920049002480124009200490024801240092004900248012400920049002480124009200490024801240092004900248012400920049002480124009200490024801240092004900248012400c40049002480118009c004900248098800a0004900268010400bc010b00288010401c400490024801240,
  0x1e000f0007800600030000f000780060002e000f00078003c0,
  0x1000080004000200,
  0x1200090004800240,
  0x1c000e000700038001c000e0007000380,
  0x200,
  0x200,
  0x200,
  0x200,
  0x200,
  0x200,
  0x200,
  0x200,
  0x200,
  0x200]

theorem cell0111_2_1 : cellOK w0111 A0111 2 623 1 (cells0111_2.getD 0 0) = true := by decide +kernel
theorem cell0111_2_2 : cellOK w0111 A0111 2 623 2 (cells0111_2.getD 1 0) = true := by decide +kernel
theorem cell0111_2_3 : cellOK w0111 A0111 2 623 3 (cells0111_2.getD 2 0) = true := by decide +kernel
theorem cell0111_2_4 : cellOK w0111 A0111 2 623 4 (cells0111_2.getD 3 0) = true := by decide +kernel
theorem cell0111_2_5 : cellOK w0111 A0111 2 623 5 (cells0111_2.getD 4 0) = true := by decide +kernel
theorem cell0111_2_6 : cellOK w0111 A0111 2 623 6 (cells0111_2.getD 5 0) = true := by decide +kernel
theorem cell0111_2_7 : cellOK w0111 A0111 2 623 7 (cells0111_2.getD 6 0) = true := by decide +kernel
theorem cell0111_2_8 : cellOK w0111 A0111 2 623 8 (cells0111_2.getD 7 0) = true := by decide +kernel
theorem cell0111_2_9 : cellOK w0111 A0111 2 623 9 (cells0111_2.getD 8 0) = true := by decide +kernel
theorem cell0111_2_10 : cellOK w0111 A0111 2 623 10 (cells0111_2.getD 9 0) = true := by decide +kernel
theorem cell0111_2_11 : cellOK w0111 A0111 2 623 11 (cells0111_2.getD 10 0) = true := by decide +kernel
theorem cell0111_2_12 : cellOK w0111 A0111 2 623 12 (cells0111_2.getD 11 0) = true := by decide +kernel
theorem cell0111_2_13 : cellOK w0111 A0111 2 623 13 (cells0111_2.getD 12 0) = true := by decide +kernel
theorem cell0111_2_14 : cellOK w0111 A0111 2 623 14 (cells0111_2.getD 13 0) = true := by decide +kernel
theorem cell0111_2_15 : cellOK w0111 A0111 2 623 15 (cells0111_2.getD 14 0) = true := by decide +kernel
theorem cell0111_2_16 : cellOK w0111 A0111 2 623 16 (cells0111_2.getD 15 0) = true := by decide +kernel
theorem cell0111_2_17 : cellOK w0111 A0111 2 623 17 (cells0111_2.getD 16 0) = true := by decide +kernel
theorem cell0111_2_18 : cellOK w0111 A0111 2 623 18 (cells0111_2.getD 17 0) = true := by decide +kernel
theorem cell0111_2_19 : cellOK w0111 A0111 2 623 19 (cells0111_2.getD 18 0) = true := by decide +kernel
theorem cell0111_2_20 : cellOK w0111 A0111 2 623 20 (cells0111_2.getD 19 0) = true := by decide +kernel
theorem cell0111_2_21 : cellOK w0111 A0111 2 623 21 (cells0111_2.getD 20 0) = true := by decide +kernel
theorem cell0111_2_22 : cellOK w0111 A0111 2 623 22 (cells0111_2.getD 21 0) = true := by decide +kernel
theorem cell0111_2_23 : cellOK w0111 A0111 2 623 23 (cells0111_2.getD 22 0) = true := by decide +kernel
theorem cell0111_2_24 : cellOK w0111 A0111 2 623 24 (cells0111_2.getD 23 0) = true := by decide +kernel
theorem cell0111_2_25 : cellOK w0111 A0111 2 623 25 (cells0111_2.getD 24 0) = true := by decide +kernel
theorem cell0111_2_26 : cellOK w0111 A0111 2 623 26 (cells0111_2.getD 25 0) = true := by decide +kernel
theorem cell0111_2_27 : cellOK w0111 A0111 2 623 27 (cells0111_2.getD 26 0) = true := by decide +kernel
theorem cell0111_2_28 : cellOK w0111 A0111 2 623 28 (cells0111_2.getD 27 0) = true := by decide +kernel
theorem cell0111_2_29 : cellOK w0111 A0111 2 623 29 (cells0111_2.getD 28 0) = true := by decide +kernel
theorem cell0111_2_30 : cellOK w0111 A0111 2 623 30 (cells0111_2.getD 29 0) = true := by decide +kernel

theorem cells0111_2_ok : ∀ p1, 1 ≤ p1 → p1 ≤ 30 → cellOK w0111 A0111 2 623 p1
    (cells0111_2.getD (p1 - 1) 0) = true :=
  all30
    cell0111_2_1 cell0111_2_2 cell0111_2_3 cell0111_2_4 cell0111_2_5 cell0111_2_6 cell0111_2_7 cell0111_2_8
    cell0111_2_9 cell0111_2_10 cell0111_2_11 cell0111_2_12 cell0111_2_13 cell0111_2_14 cell0111_2_15 cell0111_2_16
    cell0111_2_17 cell0111_2_18 cell0111_2_19 cell0111_2_20 cell0111_2_21 cell0111_2_22 cell0111_2_23 cell0111_2_24
    cell0111_2_25 cell0111_2_26 cell0111_2_27 cell0111_2_28 cell0111_2_29 cell0111_2_30

def cells0111_3 : List Nat := [
  0xe000d00078001c001e003c00220029c0102005a0012001c8007000310008800340042002c00160001c0,
  0x30003c007a0006003f800cc00aa0005000b000cc00a00053002180084018e00060002800180,
  0x1280094004a0025001280094004a0025001280094004a0025001280094004a0025001280094004a0025001280094004a0025001280094004a0025001280094004a0025001280094004a0025001280094004a0025001280094004a0025001280094004a0025001280094004a0025001280094004a0025001280094004a0025001280094004a0025001280094004a0025001280094004a0025001280094004a0025001280094004a0025001280094004a0025001280094004a0025001280094004a0025001280094004a0025001280094004a0025001280094004a0025001280094004a0025001280094004a0025001280094004a0025001280094004a0025001280094004a0025001280094004a0025001280094004a0025001280094004a0025001280094004a0025001280094004a0025001280094004a0025001280094004a0025001280094004a0025001280094004a0025001280094004a00250012800b0804a002c201280094004a0025001280094006940250018c009400630025a0128008e805ac023a01280093804a8726a0161008e804b0026a01350094005c40232013500908048c01aa012700b08035402a001d100b0803fc025800d5006a80354021600d500478e23c71aa0150006a8035401aa00d5008c80430011e388f1c860023c7282012100670023001aa00d500478e23c711800ff00478e24001bc00971c478e230010e008c00478e3900218008c00478e23c71100088004400378011e388c00968023c70b2008f1c438018400b200971c2c8016400b20061002c8016400b20128002c8023000dc00590026800ec009a0059002a801b400aa006e003680068011c0095001f801100022004d004c8002000b2003f1c1e8004000120050000900084010201280094004a00,
  0xe000700038001c000e0008c0038001c00118008c0036001c000d800840118001c000b80060004200230011802a40030009400108017401f200180012000a400300021000c001840032001c000e000700,
  0x2e8017400ba005d002e8017400ba005d002e8017400ba005d002e8017400ba005d002e8017400ba005d002e8017400ba005d002e8017400ba005d002e8017400ba005d002e8017400ba005d002e801740158005d0055801740152005d0054802ac0160015d00508017400cc00e000820017400ba005d004e003e400cc00ab005a003840152005d00340007c703e3887000b8e074702c389a1c0b0e474009c005d002a802e4002c38161c249c118006c00161c3600094005a00161c0c00164004a008100128007c0030002d002800094004e005d002e801740,
  0xe000700038001c000e000700038001c000e000700038001c000e000700038001c000e000700038001c000e000700038001c000e000700038001c000e000700038001c000e000700038001c000e000700038001c000e000700038001c000e000700038001c000e000700038001c000e000700038001c000e000700044801c0012200700038001d400ea00700044801d400d600700038001c000e638750038001c000f238890038001d400f238750085001d400e200c20034000f000d000791c22800ec00760070004080114009a00bd001e000ec0076003b006d8027c00aa004400388010400a0003b004c0001c00860045002180018009200700038001c00,
  0x98004c0026001300098004c0026001300098004c0026001300098004c0026001300098004c0026001300098004c0026001300098004c0026001300098004c0026001300098004c0026001300098004c0026001300098004c0026001300098004c0026001300098004c0026001300098004c0026001300098004c0026001300098004c0026001300098004c0026001300098004c0026001300098004c00260013000980056802d8015a0098005b002d801540098004c002f4013200ad005680264016c00b6005e802d8013600bd0058802c401320099004c80194012c3899004d80290013200a4004280290012c38aa008e80314016200bd0032801f8017000a31c260021800ca007e002e801940090007d003480130009800650024003a400ca005800328019400980049000c8006400320065000c8013400320065000c0006400d4004700110005c00300098004c002600,
  0xa0005000280014000a0005000280014000a0005400280014000a8005000280014000a0011070420014004d0e084014c0014000a000500,
  0xa80054002a0015000a80054002a0015000a80054002a001500328005400a6001500f68010870760015002480100001a0015000a800540,
  0x480024001200090004800240012000900048002400120009000480024001200090004800240012000900048002400128009000460024001400094004a00240016800bc00ca00230012000c4008200240012000900,
  0x8c38461c230e118708c38461c230e118708c38461c230e118708c38461c230e118708c38461c230e118708c38461c230e118708c38461c230e118708c38461c230e118708c38461c3a80218008c38461c230e11c712c00461c6880234008c3875004a80154008e38461c2d9c174011a00cf002a80234008800461c3a80120009200641c2480100007e004400248031400ec008900208012400b2008d0039800e4010e00461c230e1187,
  0x1100088004400220011000880044002200110008800640032001100068006c003200110008800440,
  0x2280114008a0045002280114008a0045002280114008a0045002280114008a0045002280114008a0045002280114008a0045002280114008a0045002280114008a0045002280114008a0045002280114008a0045005480114008a00450022801a000e6004500228011400e600e90022800e0009a00730022800e4008a0045003c80230008200710022801b800b200450022801140,
  0x330019800cc006600330019800cc006600330019800cc006600330019800cc006600330019800cc006600330019800cc006600330019800cc006600330019800cc006600330019800cc006600330019800cc006600330019800cc006600330019800cc006600330019800cc006600330019800cc006600330019800cc006600330019800cc006600330019800cc006600330019800cc006600448022000cc0066007280204014800890043801dc009000a9002e8013400700081005500134009a00680026801440092004d00228005c00a000660033001980,
  0x320019000c8006400320019000c8006400320019000c8006400320019000c800640032001900088006400220019000c800640,
  0x6100308018400c2006100308018400c2006100308018400c2006100308018400c2006100308018400c2006100308018400c2006100308018400c2006100308018400c2006100308018400c2006100308018400c2006100308018400c2006100308018400c2006100308018400c2006100308018400c2006100308018400c20061002c8016400b00061002c002c400c20061002c8018400b00094006b001cc7162005800460014001180058003c8013c00ae005900280006c0036004f00110006c002600610030801840,
  0xa6005300298014c00a6005300298014c00a6005300298014c00a6005300298014c00a6005300298014c00a6005300298014c00a6005300298014c00a6005300298014c00a6005300298014c00a6005300298014c00a6005300298014c00a6005300298014c00a6005300280013c00a6005300298013c009e005300278014000a600500024801440090004f00248011c0092004f004a8012c00c200510028801840096005300298014c0,
  0x5300298014c00a6005300298014c00a6005300298014c00a6005300298014c00a6005300298014c00a6005300298014c00a6005300298014c00a6005300298014c00a6005300298014c00a6005300298014c00a6005300298014c00a6005300298016c00a6005300280014c00a60053002d8016c00b6005300298014000a0005000238015000ca005b002c80224011e0053004e00104008000570071802500138005300298014c0,
  0xd8006c0036001b000d8006c0036001b000d8006c0036001b000d800500028001b000d800500028001b000d8006c0,
  0x1100088004400220011000880044002200110008800440,
  0x46002300118008c0046002300118008c004600230011800880044002300118008800440023001100088004400220011800880044002300118008c0,
  0x200010000800040002000100008000400,
  0x10000800040002000100008000400,
  0x800040002000100008000400,
  0x1e000f00078003c0,
  0xf00078003c0,
  0x100008000400,
  0x8000400,
  0x400,
  0x400]

theorem cell0111_3_1 : cellOK w0111 A0111 3 623 1 (cells0111_3.getD 0 0) = true := by decide +kernel
theorem cell0111_3_2 : cellOK w0111 A0111 3 623 2 (cells0111_3.getD 1 0) = true := by decide +kernel
theorem cell0111_3_3 : cellOK w0111 A0111 3 623 3 (cells0111_3.getD 2 0) = true := by decide +kernel
theorem cell0111_3_4 : cellOK w0111 A0111 3 623 4 (cells0111_3.getD 3 0) = true := by decide +kernel
theorem cell0111_3_5 : cellOK w0111 A0111 3 623 5 (cells0111_3.getD 4 0) = true := by decide +kernel
theorem cell0111_3_6 : cellOK w0111 A0111 3 623 6 (cells0111_3.getD 5 0) = true := by decide +kernel
theorem cell0111_3_7 : cellOK w0111 A0111 3 623 7 (cells0111_3.getD 6 0) = true := by decide +kernel
theorem cell0111_3_8 : cellOK w0111 A0111 3 623 8 (cells0111_3.getD 7 0) = true := by decide +kernel
theorem cell0111_3_9 : cellOK w0111 A0111 3 623 9 (cells0111_3.getD 8 0) = true := by decide +kernel
theorem cell0111_3_10 : cellOK w0111 A0111 3 623 10 (cells0111_3.getD 9 0) = true := by decide +kernel
theorem cell0111_3_11 : cellOK w0111 A0111 3 623 11 (cells0111_3.getD 10 0) = true := by decide +kernel
theorem cell0111_3_12 : cellOK w0111 A0111 3 623 12 (cells0111_3.getD 11 0) = true := by decide +kernel
theorem cell0111_3_13 : cellOK w0111 A0111 3 623 13 (cells0111_3.getD 12 0) = true := by decide +kernel
theorem cell0111_3_14 : cellOK w0111 A0111 3 623 14 (cells0111_3.getD 13 0) = true := by decide +kernel
theorem cell0111_3_15 : cellOK w0111 A0111 3 623 15 (cells0111_3.getD 14 0) = true := by decide +kernel
theorem cell0111_3_16 : cellOK w0111 A0111 3 623 16 (cells0111_3.getD 15 0) = true := by decide +kernel
theorem cell0111_3_17 : cellOK w0111 A0111 3 623 17 (cells0111_3.getD 16 0) = true := by decide +kernel
theorem cell0111_3_18 : cellOK w0111 A0111 3 623 18 (cells0111_3.getD 17 0) = true := by decide +kernel
theorem cell0111_3_19 : cellOK w0111 A0111 3 623 19 (cells0111_3.getD 18 0) = true := by decide +kernel
theorem cell0111_3_20 : cellOK w0111 A0111 3 623 20 (cells0111_3.getD 19 0) = true := by decide +kernel
theorem cell0111_3_21 : cellOK w0111 A0111 3 623 21 (cells0111_3.getD 20 0) = true := by decide +kernel
theorem cell0111_3_22 : cellOK w0111 A0111 3 623 22 (cells0111_3.getD 21 0) = true := by decide +kernel
theorem cell0111_3_23 : cellOK w0111 A0111 3 623 23 (cells0111_3.getD 22 0) = true := by decide +kernel
theorem cell0111_3_24 : cellOK w0111 A0111 3 623 24 (cells0111_3.getD 23 0) = true := by decide +kernel
theorem cell0111_3_25 : cellOK w0111 A0111 3 623 25 (cells0111_3.getD 24 0) = true := by decide +kernel
theorem cell0111_3_26 : cellOK w0111 A0111 3 623 26 (cells0111_3.getD 25 0) = true := by decide +kernel
theorem cell0111_3_27 : cellOK w0111 A0111 3 623 27 (cells0111_3.getD 26 0) = true := by decide +kernel
theorem cell0111_3_28 : cellOK w0111 A0111 3 623 28 (cells0111_3.getD 27 0) = true := by decide +kernel
theorem cell0111_3_29 : cellOK w0111 A0111 3 623 29 (cells0111_3.getD 28 0) = true := by decide +kernel
theorem cell0111_3_30 : cellOK w0111 A0111 3 623 30 (cells0111_3.getD 29 0) = true := by decide +kernel

theorem cells0111_3_ok : ∀ p1, 1 ≤ p1 → p1 ≤ 30 → cellOK w0111 A0111 3 623 p1
    (cells0111_3.getD (p1 - 1) 0) = true :=
  all30
    cell0111_3_1 cell0111_3_2 cell0111_3_3 cell0111_3_4 cell0111_3_5 cell0111_3_6 cell0111_3_7 cell0111_3_8
    cell0111_3_9 cell0111_3_10 cell0111_3_11 cell0111_3_12 cell0111_3_13 cell0111_3_14 cell0111_3_15 cell0111_3_16
    cell0111_3_17 cell0111_3_18 cell0111_3_19 cell0111_3_20 cell0111_3_21 cell0111_3_22 cell0111_3_23 cell0111_3_24
    cell0111_3_25 cell0111_3_26 cell0111_3_27 cell0111_3_28 cell0111_3_29 cell0111_3_30

/-! ### The three words of period four -/

/-- **Every right half with at most two black cells among cells 1 to 778 enters the family under `0001`**, in every
phase, whatever lies beyond cell 778. -/
theorem sparse_0001 (φ : Nat) (x : Nat → Bool) (hx : AtMostTwo 778 x) :
    ∃ a ∈ A0001, ∃ t1, InFamily (drv (fun t => wordAt w0001 (t + φ)) x) a.1 (a.2 + φ) t1 := by
  refine gap_phase ?_
  rcases (show φ % 4 = 0 ∨ φ % 4 = 1 ∨ φ % 4 = 2 ∨ φ % 4 = 3 by omega) with h | h | h | h <;> rw [h]
  · exact two_absorption cells0001_0_ok (high_0001 0) x hx
  · exact two_absorption cells0001_1_ok (high_0001 1) x hx
  · exact two_absorption cells0001_2_ok (high_0001 2) x hx
  · exact two_absorption cells0001_3_ok (high_0001 3) x hx

/-- **Every right half with at most two black cells among cells 1 to 1359 enters the family under `0011`**, in every
phase, whatever lies beyond cell 1359. -/
theorem sparse_0011 (φ : Nat) (x : Nat → Bool) (hx : AtMostTwo 1359 x) :
    ∃ a ∈ A0011, ∃ t1, InFamily (drv (fun t => wordAt w0011 (t + φ)) x) a.1 (a.2 + φ) t1 := by
  refine gap_phase ?_
  rcases (show φ % 4 = 0 ∨ φ % 4 = 1 ∨ φ % 4 = 2 ∨ φ % 4 = 3 by omega) with h | h | h | h <;> rw [h]
  · exact two_absorption cells0011_0_ok (high_0011 0) x hx
  · exact two_absorption cells0011_1_ok (high_0011 1) x hx
  · exact two_absorption cells0011_2_ok (high_0011 2) x hx
  · exact two_absorption cells0011_3_ok (high_0011 3) x hx

/-- **Every right half with at most two black cells among cells 1 to 623 enters the family under `0111`**, in every
phase, whatever lies beyond cell 623. -/
theorem sparse_0111 (φ : Nat) (x : Nat → Bool) (hx : AtMostTwo 623 x) :
    ∃ a ∈ A0111, ∃ t1, InFamily (drv (fun t => wordAt w0111 (t + φ)) x) a.1 (a.2 + φ) t1 := by
  refine gap_phase ?_
  rcases (show φ % 4 = 0 ∨ φ % 4 = 1 ∨ φ % 4 = 2 ∨ φ % 4 = 3 by omega) with h | h | h | h <;> rw [h]
  · exact two_absorption cells0111_0_ok (high_0111 0) x hx
  · exact two_absorption cells0111_1_ok (high_0111 1) x hx
  · exact two_absorption cells0111_2_ok (high_0111 2) x hx
  · exact two_absorption cells0111_3_ok (high_0111 3) x hx

/-- One black cell is at most two. -/
theorem atMostTwo_of_one {G p : Nat} {x : Nat → Bool} (hx : ∀ q, q ≠ p → x q = false) : AtMostTwo G x := by
  intro a b c _ hab hbc _ ha hb _
  by_cases h : a = p
  · subst h; rw [hx b (by omega)] at hb; exact Bool.false_ne_true hb
  · rw [hx a h] at ha; exact Bool.false_ne_true ha

/-- One black cell, anywhere, enters the family under `0001`. -/
theorem oneCell_0001 (φ p : Nat) (x : Nat → Bool) (hx : ∀ q, q ≠ p → x q = false) :
    ∃ a ∈ A0001, ∃ t1, InFamily (drv (fun t => wordAt w0001 (t + φ)) x) a.1 (a.2 + φ) t1 :=
  sparse_0001 φ x (atMostTwo_of_one hx)

/-- One black cell, anywhere, enters the family under `0011`. -/
theorem oneCell_0011 (φ p : Nat) (x : Nat → Bool) (hx : ∀ q, q ≠ p → x q = false) :
    ∃ a ∈ A0011, ∃ t1, InFamily (drv (fun t => wordAt w0011 (t + φ)) x) a.1 (a.2 + φ) t1 :=
  sparse_0011 φ x (atMostTwo_of_one hx)

/-- One black cell, anywhere, enters the family under `0111`. -/
theorem oneCell_0111 (φ p : Nat) (x : Nat → Bool) (hx : ∀ q, q ≠ p → x q = false) :
    ∃ a ∈ A0111, ∃ t1, InFamily (drv (fun t => wordAt w0111 (t + φ)) x) a.1 (a.2 + φ) t1 :=
  sparse_0111 φ x (atMostTwo_of_one hx)

/-! ### No center column repeats the word -/

/-- No finite configuration with at most two black cells among the cells `1 .. G` has a center column that repeats `w`
from phase `φ`. -/
def SparseRight (w : List Bool) (G φ : Nat) : Prop :=
  ¬ ∃ y : Int → Bool, FinConfig y ∧ AtMostTwo G (fun p => y (p : Int)) ∧ ∀ t, evol y t 0 = wordAt w (t + φ)

/-- Absorption for the sparse halves excludes the word, by the kit's masked Jen for finite configurations. -/
theorem sparseRight_of_absorption {w : List Bool} {A : List (Nat × Nat)} {G φ : Nat}
    (hA : ∀ a ∈ A, aligned w a.1 a.2 = true) (hw : ∃ ψ, wordAt w ψ = true)
    (habs : ∀ x : Nat → Bool, AtMostTwo G x →
      ∃ a ∈ A, ∃ t1, InFamily (drv (fun t => wordAt w (t + φ)) x) a.1 (a.2 + φ) t1) : SparseRight w G φ := by
  rintro ⟨y, hfin, hR, hc⟩
  obtain ⟨a, haA, t1, hF⟩ := habs (fun p => y (p : Int)) hR
  exact no_finite_of_family (hA a haA) φ hfin hc hw t1 hF

/-- **No finite configuration with at most two black cells among cells 1 to 778 has a center column that repeats
`0001`**, in any phase, whatever its left half and its cells beyond 778. -/
theorem sparseRight_0001 (φ : Nat) : SparseRight w0001 778 φ :=
  sparseRight_of_absorption A0001_ok ⟨3, rfl⟩ (sparse_0001 φ)

/-- **No finite configuration with at most two black cells among cells 1 to 1359 has a center column that repeats
`0011`**, in any phase, whatever its left half and its cells beyond 1359. -/
theorem sparseRight_0011 (φ : Nat) : SparseRight w0011 1359 φ :=
  sparseRight_of_absorption A0011_ok ⟨3, rfl⟩ (sparse_0011 φ)

/-- **No finite configuration with at most two black cells among cells 1 to 623 has a center column that repeats
`0111`**, in any phase, whatever its left half and its cells beyond 623. -/
theorem sparseRight_0111 (φ : Nat) : SparseRight w0111 623 φ :=
  sparseRight_of_absorption A0111_ok ⟨3, rfl⟩ (sparse_0111 φ)

end Rule30Open
