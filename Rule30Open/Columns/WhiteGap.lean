module

public import Rule30Open.Columns.EmptyRight

/-!
# A white gap shields a small right half: absorption for every right half that is white past its first cells

Before a right half driven by a word of period four enters the kit's ether-and-wall family, the cells that decide
entry, columns `1 .. k + 13` at the entry step `t1`, have seen only the initial cells `1 .. t1 + k + 13`
(`drv_cone`). The family is a trap, so what lies further right cannot undo entry. So every check of `EmptyRight`, a
small right half entering at step `t1` and depth `k`, holds for every right half that agrees with it up to cell
`t1 + k + 13`, whatever lies beyond (`inFamily_of_check_cone`, `gap_absorption`).

* `gap_0001`, `gap_0011`, `gap_0111`: every right half whose cells `7 .. B` are white enters the family, with
  `B = 316`, `535` and `310`, in every phase, whatever its first six cells and its cells beyond `B`.
* `gapRight_0001`, `gapRight_0011`, `gapRight_0111`: so no finite configuration whose cells `7 .. B` are white has a
  center column that repeats the word, whatever its left half.
* `high_0001`, `high_0011`, `high_0111`: every right half white on cells `1 .. 30` enters the family, for each of the
  three words. For `0001` this is the kit's `Rule30EtherSingleCell.absorption_high`.

The natural-language argument is `WhiteGap.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

open Ruliology.CellularAutomata
open Rule30Jen Rule30Realization Rule30Ether Rule30StripCertificates Rule30PeriodTwoSideways

/-- **The light cone of the driven right half.** Column `p` at time `t` reads only the initial cells `1 .. p + t`. -/
theorem drv_cone {c x y : Nat → Bool} : ∀ t p, (∀ q, 1 ≤ q → q ≤ p + t → x q = y q) → drv c x t p = drv c y t p
  | 0, 0, _ => by rw [drv_col0, drv_col0]
  | 0, p + 1, h => by
    rw [drv_init c x (p + 1) (by omega), drv_init c y (p + 1) (by omega)]
    exact h (p + 1) (by omega) (by omega)
  | t + 1, 0, _ => by rw [drv_col0, drv_col0]
  | t + 1, p + 1, h => by
    show rule (drv c x t p) (drv c x t (p + 1)) (drv c x t (p + 2)) =
      rule (drv c y t p) (drv c y t (p + 1)) (drv c y t (p + 2))
    rw [drv_cone t p fun q h1 h2 => h q h1 (by omega), drv_cone t (p + 1) fun q h1 h2 => h q h1 (by omega),
      drv_cone t (p + 2) fun q h1 h2 => h q h1 (by omega)]

/-- **Entry travels along the light cone.** A passing `familyCheck` for the packed half `r` at step `t1` and depth `k`
gives the family, at that step, for every right half that agrees with `r` on the cells `1 .. t1 + k + 13`. -/
theorem inFamily_of_check_cone {c x : Nat → Bool} {r j0 s t1 k : Nat} (h : familyCheck c r j0 s t1 k = true)
    (hx : ∀ q, 1 ≤ q → q ≤ t1 + k + 13 → x q = r.testBit (q - 1)) : InFamily (drv c x) j0 s t1 := by
  have hcone : ∀ p, p ≤ k + 13 → drv c x t1 p = drv c (fun p => r.testBit (p - 1)) t1 p := fun p hp =>
    drv_cone t1 p fun q h1 h2 => hx q h1 (by omega)
  unfold familyCheck at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  obtain ⟨⟨hk, hE⟩, hW⟩ := h
  refine ⟨k, hk, fun p hp1 hpk => ?_, ?_⟩
  · obtain ⟨i, rfl⟩ : ∃ i, p = i + 1 := ⟨p - 1, by omega⟩
    rw [hcone (i + 1) (by omega), ← Rule30EtherThree.rowN_eq_drv]
    exact hE i (by omega)
  · have e : rowOf (drv c x) t1 k 13 = seg (fun i => (Rule30EtherThree.rowN c r t1).testBit (k + i)) 13 := by
      unfold rowOf
      apply seg_congr
      intro i hi
      rw [hcone (k + i + 1) (by omega), Rule30EtherThree.rowN_eq_drv]
    rw [e]
    exact hW

/-- A right half white on the cells `n + 1 .. B` agrees, on the cells `1 .. B`, with the packed half of its first `n`
cells. -/
theorem pack_gap (n B : Nat) (x : Nat → Bool) (hx : ∀ p, n < p → p ≤ B → x p = false) :
    ∃ r, r < 2 ^ n ∧ ∀ q, 1 ≤ q → q ≤ B → x q = r.testBit (q - 1) := by
  obtain ⟨r, hr, hrk⟩ := Rule30ZeroBoundarySmall.exists_pack n (fun p => if p ≤ n then x p else false)
    fun k hk => ite_eq_right (by omega)
  refine ⟨r, hr, fun q h1 hqB => ?_⟩
  have e := hrk q h1
  unfold Rule30ZeroBoundarySmall.toFun at e
  rw [ite_eq_right (show q ≠ 0 by omega)] at e
  by_cases hq : q ≤ n
  · rw [ite_eq_left hq] at e
    exact e.symm
  · rw [ite_eq_right hq] at e
    rw [hx q (by omega) hqB, e]

/-- Every listed entry step, plus its depth, plus 13, is at most `B`. -/
def gapBound (entries : List (Nat × Nat)) (B : Nat) : Bool := entries.all fun e => decide (e.1 + e.2 + 13 ≤ B)

theorem getD_bound {entries : List (Nat × Nat)} {B : Nat} (hB : gapBound entries B = true) (h13 : 13 ≤ B) (r : Nat) :
    (entries.getD r (0, 0)).1 + (entries.getD r (0, 0)).2 + 13 ≤ B := by
  rw [List.getD_eq_getElem?_getD]
  cases h : entries[r]? with
  | none => simpa using h13
  | some e => simpa using List.all_eq_true.1 hB e (List.mem_of_getElem? h)

/-- **Absorption across a white gap.** If every right half of at most `n` cells passes its `smallCheck` and every
entry step plus depth plus 13 is at most `B`, then every right half whose cells `n + 1 .. B` are white enters the family,
whatever lies beyond `B`. -/
theorem gap_absorption {w : List Bool} {A : List (Nat × Nat)} {φ n B : Nat} {entries : List (Nat × Nat)}
    (hcheck : smallCheck w A φ n entries = true) (hB : gapBound entries B = true) (h13 : 13 ≤ B)
    (x : Nat → Bool) (hx : ∀ p, n < p → p ≤ B → x p = false) :
    ∃ a ∈ A, ∃ t1, InFamily (drv (fun t => wordAt w (t + φ)) x) a.1 (a.2 + φ) t1 := by
  obtain ⟨r, hr, hxr⟩ := pack_gap n B x hx
  unfold smallCheck at hcheck
  obtain ⟨a, haA, ha⟩ := List.any_eq_true.1 (List.all_eq_true.1 hcheck r (List.mem_range.2 hr))
  have hb := getD_bound hB h13 r
  exact ⟨a, haA, _, inFamily_of_check_cone ha fun q h1 h2 => hxr q h1 (by omega)⟩

/-- The family condition only reads the phase modulo 4. -/
theorem inFamily_phase {F : Nat → Nat → Bool} {j0 s s' t1 : Nat} (hs : s % 4 = s' % 4) (h : InFamily F j0 s t1) :
    InFamily F j0 s' t1 := by
  obtain ⟨k, hk, hE, hW⟩ := h
  refine ⟨k, hk, fun p hp1 hpk => ?_, ?_⟩
  · rw [hE p hp1 hpk]
    exact ether_congr rfl (by omega)
  · rw [show (t1 + s') % 4 = (t1 + s) % 4 by omega]
    exact hW

/-- A phase `φ` drives the half as `φ % 4` does. -/
theorem gap_phase {w : List Bool} {A : List (Nat × Nat)} {x : Nat → Bool} {φ : Nat}
    (h : ∃ a ∈ A, ∃ t1, InFamily (drv (fun t => wordAt w (t + φ % 4)) x) a.1 (a.2 + φ % 4) t1) :
    ∃ a ∈ A, ∃ t1, InFamily (drv (fun t => wordAt w (t + φ)) x) a.1 (a.2 + φ) t1 := by
  obtain ⟨a, haA, t1, hF⟩ := h
  have e : drv (fun t => wordAt w (t + φ)) x = drv (fun t => wordAt w (t + φ % 4)) x := by
    have hc : (fun t => wordAt w (t + φ)) = fun t => wordAt w (t + φ % 4) := by
      funext t
      unfold wordAt
      rw [show (t + φ) % 4 = (t + φ % 4) % 4 by omega]
    rw [hc]
  exact ⟨a, haA, t1, by rw [e]; exact inFamily_phase (by omega) hF⟩

/-! ### The three words of period four -/

theorem bound0001 : gapBound entries0001_0 316 = true ∧ gapBound entries0001_1 316 = true ∧
    gapBound entries0001_2 316 = true ∧ gapBound entries0001_3 316 = true := by decide

theorem bound0011 : gapBound entries0011_0 535 = true ∧ gapBound entries0011_1 535 = true ∧
    gapBound entries0011_2 535 = true ∧ gapBound entries0011_3 535 = true := by decide

theorem bound0111 : gapBound entries0111_0 310 = true ∧ gapBound entries0111_1 310 = true ∧
    gapBound entries0111_2 310 = true ∧ gapBound entries0111_3 310 = true := by decide

/-- **Every right half white on cells 7 to 316 enters the family under `0001`**, in every phase. -/
theorem gap_0001 (φ : Nat) (x : Nat → Bool) (hx : ∀ p, 6 < p → p ≤ 316 → x p = false) :
    ∃ a ∈ A0001, ∃ t1, InFamily (drv (fun t => wordAt w0001 (t + φ)) x) a.1 (a.2 + φ) t1 := by
  refine gap_phase ?_
  obtain ⟨b0, b1, b2, b3⟩ := bound0001
  rcases (show φ % 4 = 0 ∨ φ % 4 = 1 ∨ φ % 4 = 2 ∨ φ % 4 = 3 by omega) with h | h | h | h <;> rw [h]
  · exact gap_absorption check0001_0 b0 (by omega) x hx
  · exact gap_absorption check0001_1 b1 (by omega) x hx
  · exact gap_absorption check0001_2 b2 (by omega) x hx
  · exact gap_absorption check0001_3 b3 (by omega) x hx

/-- **Every right half white on cells 7 to 535 enters the family under `0011`**, in every phase. -/
theorem gap_0011 (φ : Nat) (x : Nat → Bool) (hx : ∀ p, 6 < p → p ≤ 535 → x p = false) :
    ∃ a ∈ A0011, ∃ t1, InFamily (drv (fun t => wordAt w0011 (t + φ)) x) a.1 (a.2 + φ) t1 := by
  refine gap_phase ?_
  obtain ⟨b0, b1, b2, b3⟩ := bound0011
  rcases (show φ % 4 = 0 ∨ φ % 4 = 1 ∨ φ % 4 = 2 ∨ φ % 4 = 3 by omega) with h | h | h | h <;> rw [h]
  · exact gap_absorption check0011_0 b0 (by omega) x hx
  · exact gap_absorption check0011_1 b1 (by omega) x hx
  · exact gap_absorption check0011_2 b2 (by omega) x hx
  · exact gap_absorption check0011_3 b3 (by omega) x hx

/-- **Every right half white on cells 7 to 310 enters the family under `0111`**, in every phase. -/
theorem gap_0111 (φ : Nat) (x : Nat → Bool) (hx : ∀ p, 6 < p → p ≤ 310 → x p = false) :
    ∃ a ∈ A0111, ∃ t1, InFamily (drv (fun t => wordAt w0111 (t + φ)) x) a.1 (a.2 + φ) t1 := by
  refine gap_phase ?_
  obtain ⟨b0, b1, b2, b3⟩ := bound0111
  rcases (show φ % 4 = 0 ∨ φ % 4 = 1 ∨ φ % 4 = 2 ∨ φ % 4 = 3 by omega) with h | h | h | h <;> rw [h]
  · exact gap_absorption check0111_0 b0 (by omega) x hx
  · exact gap_absorption check0111_1 b1 (by omega) x hx
  · exact gap_absorption check0111_2 b2 (by omega) x hx
  · exact gap_absorption check0111_3 b3 (by omega) x hx

/-! ### No center column repeats the word across a white gap -/

/-- No finite configuration whose cells `n + 1 .. B` are white has a center column that repeats `w` from phase `φ`. -/
def GapRight (w : List Bool) (n B φ : Nat) : Prop :=
  ¬ ∃ y : Int → Bool, FinConfig y ∧ (∀ p : Int, (n : Int) < p → p ≤ (B : Int) → y p = false) ∧
    ∀ t, evol y t 0 = wordAt w (t + φ)

/-- Absorption across the gap excludes the word, by the kit's masked Jen for finite configurations. -/
theorem gapRight_of_absorption {w : List Bool} {A : List (Nat × Nat)} {n B φ : Nat}
    (hA : ∀ a ∈ A, aligned w a.1 a.2 = true) (hw : ∃ ψ, wordAt w ψ = true)
    (habs : ∀ x : Nat → Bool, (∀ p, n < p → p ≤ B → x p = false) →
      ∃ a ∈ A, ∃ t1, InFamily (drv (fun t => wordAt w (t + φ)) x) a.1 (a.2 + φ) t1) : GapRight w n B φ := by
  rintro ⟨y, hfin, hR, hc⟩
  obtain ⟨a, haA, t1, hF⟩ := habs (fun p => y (p : Int)) fun p h1 h2 => hR p (by omega) (by omega)
  exact no_finite_of_family (hA a haA) φ hfin hc hw t1 hF

/-- **No finite configuration whose cells 7 to 316 are white has a center column that repeats `0001`**, in any
phase and whatever its left half and its cells beyond 316. -/
theorem gapRight_0001 (φ : Nat) : GapRight w0001 6 316 φ :=
  gapRight_of_absorption A0001_ok ⟨3, rfl⟩ (gap_0001 φ)

/-- **No finite configuration whose cells 7 to 535 are white has a center column that repeats `0011`**, in any
phase and whatever its left half and its cells beyond 535. -/
theorem gapRight_0011 (φ : Nat) : GapRight w0011 6 535 φ :=
  gapRight_of_absorption A0011_ok ⟨3, rfl⟩ (gap_0011 φ)

/-- **No finite configuration whose cells 7 to 310 are white has a center column that repeats `0111`**, in any
phase and whatever its left half and its cells beyond 310. -/
theorem gapRight_0111 (φ : Nat) : GapRight w0111 6 310 φ :=
  gapRight_of_absorption A0111_ok ⟨3, rfl⟩ (gap_0111 φ)

/-! ### Right halves white on cells 1 to 30 -/

/-- If the white half enters by step `t1` at depth `k` with `t1 + k + 13 ≤ 30`, every right half white on cells
`1 .. 30` enters at the same step. -/
theorem high_absorption {w : List Bool} {A : List (Nat × Nat)} {φ n : Nat} {entries : List (Nat × Nat)}
    (hcheck : smallCheck w A φ n entries = true)
    (h0 : (entries.getD 0 (0, 0)).1 + (entries.getD 0 (0, 0)).2 + 13 ≤ 30)
    (x : Nat → Bool) (hx : ∀ p, 1 ≤ p → p ≤ 30 → x p = false) :
    ∃ a ∈ A, ∃ t1, InFamily (drv (fun t => wordAt w (t + φ)) x) a.1 (a.2 + φ) t1 := by
  unfold smallCheck at hcheck
  obtain ⟨a, haA, ha⟩ := List.any_eq_true.1 (List.all_eq_true.1 hcheck 0 (List.mem_range.2 (Nat.two_pow_pos n)))
  exact ⟨a, haA, _, inFamily_of_check_cone ha fun q h1 h2 => by rw [hx q h1 (by omega), Nat.zero_testBit]⟩

/-- **Every right half white on cells 1 to 30 enters the family under `0001`**, in every phase. -/
theorem high_0001 (φ : Nat) (x : Nat → Bool) (hx : ∀ p, 1 ≤ p → p ≤ 30 → x p = false) :
    ∃ a ∈ A0001, ∃ t1, InFamily (drv (fun t => wordAt w0001 (t + φ)) x) a.1 (a.2 + φ) t1 := by
  refine gap_phase ?_
  rcases (show φ % 4 = 0 ∨ φ % 4 = 1 ∨ φ % 4 = 2 ∨ φ % 4 = 3 by omega) with h | h | h | h <;> rw [h]
  · exact high_absorption check0001_0 (by decide) x hx
  · exact high_absorption check0001_1 (by decide) x hx
  · exact high_absorption check0001_2 (by decide) x hx
  · exact high_absorption check0001_3 (by decide) x hx

/-- **Every right half white on cells 1 to 30 enters the family under `0011`**, in every phase. -/
theorem high_0011 (φ : Nat) (x : Nat → Bool) (hx : ∀ p, 1 ≤ p → p ≤ 30 → x p = false) :
    ∃ a ∈ A0011, ∃ t1, InFamily (drv (fun t => wordAt w0011 (t + φ)) x) a.1 (a.2 + φ) t1 := by
  refine gap_phase ?_
  rcases (show φ % 4 = 0 ∨ φ % 4 = 1 ∨ φ % 4 = 2 ∨ φ % 4 = 3 by omega) with h | h | h | h <;> rw [h]
  · exact high_absorption check0011_0 (by decide) x hx
  · exact high_absorption check0011_1 (by decide) x hx
  · exact high_absorption check0011_2 (by decide) x hx
  · exact high_absorption check0011_3 (by decide) x hx

/-- **Every right half white on cells 1 to 30 enters the family under `0111`**, in every phase. -/
theorem high_0111 (φ : Nat) (x : Nat → Bool) (hx : ∀ p, 1 ≤ p → p ≤ 30 → x p = false) :
    ∃ a ∈ A0111, ∃ t1, InFamily (drv (fun t => wordAt w0111 (t + φ)) x) a.1 (a.2 + φ) t1 := by
  refine gap_phase ?_
  rcases (show φ % 4 = 0 ∨ φ % 4 = 1 ∨ φ % 4 = 2 ∨ φ % 4 = 3 by omega) with h | h | h | h <;> rw [h]
  · exact high_absorption check0111_0 (by decide) x hx
  · exact high_absorption check0111_1 (by decide) x hx
  · exact high_absorption check0111_2 (by decide) x hx
  · exact high_absorption check0111_3 (by decide) x hx

end Rule30Open
