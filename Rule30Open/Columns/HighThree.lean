module

public import Rule30Open.Columns.WhiteGap

/-!
# Least period three: a right half white on its first 1,317 cells enters the kit's trap for `001`

The kit reduces the word `001` to three open statements, one of them `AbsorptionT t001`: every finite right half,
driven by `001`, enters the kit's period-21 trap `t001`. [EmptyRight.md](EmptyRight.md) shows that the white right half
enters, at step 1270, 1269 or 1268 by phase (`emptyRight_001`). The trap reads only columns `1 .. 47`, and by the light
cone (`drv_cone`) those columns at step `t1` have seen only the initial cells `1 .. t1 + 47`. So every right half white
on cells `1 .. 1317` enters at the same step, whatever lies beyond, and no finite configuration with such a right half
has a center column that repeats `001`, whatever its left half (`highRight_001`).

The natural-language argument is `HighThree.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

open Ruliology.CellularAutomata
open Rule30Jen Rule30Realization Rule30Ether Rule30StripCertificates Rule30PeriodTwoSideways

/-- No finite configuration whose cells `1 .. B` are white has a center column that repeats `w` from phase `φ`. -/
def HighRight3 (w : List Bool) (B φ : Nat) : Prop :=
  ¬ ∃ y : Int → Bool, FinConfig y ∧ (∀ p : Int, 0 < p → p ≤ (B : Int) → y p = false) ∧
    ∀ t, evol y t 0 = Rule30EtherThree.wordAt3 w (t + φ)

/-- **Entry of the white half travels along the light cone.** If the white right half is in `t001` at step `t1`, so
is every right half white on cells `1 .. t1 + 47`. -/
theorem highRight3_of_entry {φ t1 : Nat} (ht1 : 2 ≤ t1) (hph : (t1 + φ) % 3 = Rule30EtherThree.t001.lab 597 % 3)
    (h : Rule30EtherThree.t001.st 597 =
      Rule30EtherThree.rowN (fun t => Rule30EtherThree.wordAt3 Rule30EtherThree.w001 (t + φ)) 0 t1 % 2 ^ 47) :
    HighRight3 Rule30EtherThree.w001 (t1 + 47) φ := by
  rintro ⟨y, hfin, hR, hc⟩
  refine no_finite_of_ptrap Rule30EtherThree.t001 Rule30EtherThree.t001_check (by decide) φ hfin hc ⟨2, rfl⟩ t1 597
    ht1 (by decide) hph ⟨Rule30EtherThree.PTrap.st_lt _ 597, fun k hk => ?_⟩
  have hb : Rule30EtherThree.t001.b = 47 := rfl
  rw [hb] at hk
  rw [h, Nat.testBit_mod_two_pow, decide_eq_true hk, Bool.true_and, Rule30EtherThree.rowN_eq_drv,
    show 0 + 1 + k = k + 1 by omega]
  exact drv_cone t1 (k + 1) fun q h1 h2 => by rw [Nat.zero_testBit, hR q (by omega) (by omega)]

/-- More white cells only strengthen the hypothesis. -/
theorem highRight3_mono {w : List Bool} {B B' φ : Nat} (hB : B ≤ B') (h : HighRight3 w B φ) : HighRight3 w B' φ := by
  rintro ⟨y, hfin, hR, hc⟩
  exact h ⟨y, hfin, fun p h1 h2 => hR p h1 (by omega), hc⟩

/-- **No finite configuration whose cells 1 to 1,317 are white has a center column that repeats `001`**, in any phase
and whatever its left half and its cells beyond 1,317. -/
theorem highRight_001 (φ : Nat) : HighRight3 Rule30EtherThree.w001 1317 φ := by
  have hmod : HighRight3 Rule30EtherThree.w001 1317 (φ % 3) → HighRight3 Rule30EtherThree.w001 1317 φ := by
    rintro h ⟨y, hfin, hR, hc⟩
    refine h ⟨y, hfin, hR, fun t => ?_⟩
    rw [hc t]
    unfold Rule30EtherThree.wordAt3
    rw [show (t + φ) % 3 = (t + φ % 3) % 3 by omega]
  refine hmod ?_
  rcases (show φ % 3 = 0 ∨ φ % 3 = 1 ∨ φ % 3 = 2 by omega) with h | h | h <;> rw [h]
  · exact highRight3_of_entry (by decide) (by decide) Rule30EtherThree.rowN_empty_eq
  · exact highRight3_mono (by decide) (highRight3_of_entry (by decide) (by decide) rowN_001_1)
  · exact highRight3_mono (by decide) (highRight3_of_entry (by decide) (by decide) rowN_001_2)

end Rule30Open
