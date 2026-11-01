module

public import Rule30Open.Columns.ClassSplit
public import Rule30Open.Columns.ClassBlocks17SplitA3
public import Rule30Open.Columns.ClassBlocks17SplitB3

/-!
# The game with cyclic classes excludes `00011111111110101` and `01111011111111111`

[ClassGame](ClassGame.md) proves, for any block with a valid `ClassCert`, that no column of the orbit of a row with a
leftmost 1 repeats it (`class_column`). The class-test survey at period 17 and 17 cells finds three blocks that the
class test closes at 17 cells and not at 16 and that nothing else in this repository or the kit excludes. This module
proves the exclusion of `00011111111110101` and `01111011111111111`, whose certificates at 17 cells are checked over the
modules [ClassBlocks17SplitA1](ClassBlocks17SplitA1.md), [ClassBlocks17SplitA2](ClassBlocks17SplitA2.md),
[ClassBlocks17SplitA3](ClassBlocks17SplitA3.md), [ClassBlocks17SplitB1](ClassBlocks17SplitB1.md),
[ClassBlocks17SplitB2](ClassBlocks17SplitB2.md), [ClassBlocks17SplitB3](ClassBlocks17SplitB3.md), made by
`computations/class_blocks_split.py`. `ClassCert.levelOk_append` ([ClassSplit](ClassSplit.md)) carries the checks of the
widths to the full certificates. The third block, `01010111111111111`, is in
[ClassBlocks17Cells](ClassBlocks17Cells.md).

For each block `b` there is one section with `cls<b>_levels`, `cls<b>_valid` and the theorems `column_not_<b>`
(every column of every row with a leftmost 1), `center_not_<b>` (the center column) and
`not_eventually_<b>` (the kit's form).

The natural-language argument is `ClassBlocks17Split.md`, beside this file.
-/

@[expose] public section

-- Sequential elaboration: the kernel checks would otherwise run in parallel and stack their memory.
set_option Elab.async false

namespace Rule30Open

open Ruliology.CellularAutomata
open Rule30StripCertificateTable (wordOf)

/-! ### The block 00011111111110101 at 17 cells

Widths 1 to 17 check 205,288 nodes, with heights up to 87; the classes cover
the 58,385 nodes of height 0 at 17 cells, with 216 ranks and labels modulo 17 and 51. -/

section
/-- Every width passes at every phase on the full certificate of `00011111111110101`. -/
theorem cls00011111111110101_levels :
    ∀ j, j < 17 → ∀ φ, φ < 17 → cls00011111111110101.levelOk j φ = true := by
  intro j hj φ hφ
  by_cases h0 : j < 15
  · have hl : cls00011111111110101W15.levels.length = 15 := rfl
    rw [ClassCert.levelOk_append cls00011111111110101W15 cls00011111111110101
      [cls00011111111110101L16, cls00011111111110101L17] rfl rfl (by omega) φ]
    exact cls00011111111110101W15_levels j (by omega) (by omega) φ hφ
  have hl : cls00011111111110101W17.levels.length = 17 := rfl
  rw [ClassCert.levelOk_append cls00011111111110101W17 cls00011111111110101
      [] rfl rfl (by omega) φ]
  exact cls00011111111110101W17_levels j (by omega) (by omega) φ hφ

/-- The certificate of `00011111111110101` passes at every width and phase. -/
theorem cls00011111111110101_valid : cls00011111111110101.Valid := by
  have hP : cls00011111111110101.block.length = 17 := Rule30StripCertificateTable.wordOf_length _ _
  have hW : cls00011111111110101.levels.length = 17 := rfl
  exact ⟨by omega, by omega, fun j φ hj hφ => cls00011111111110101_levels j (by omega) φ (by omega),
    fun φ hφ => cls00011111111110101_f φ (by omega)⟩

/-- **No column repeats 00011111111110101.** In the orbit of a row with a leftmost 1, no column repeats the block
`00011111111110101`, from any time `T` on and read from any phase. -/
theorem column_not_00011111111110101 (init : Int → Bool) (m : Int) (hm : init m = true)
    (hz : ∀ x : Int, x < m → init x = false) (k : Int) (T shift : Nat)
    (h : ∀ t : Nat, T ≤ t → evolve init t k = (wordOf 17 0b00011111111110101).getD ((t + shift) % 17) false) : False :=
  class_column init m hm hz cls00011111111110101 cls00011111111110101_valid k T shift fun t ht => by
    rw [h t ht]
    show _ = bit (wordOf 17 0b00011111111110101) ((t + shift) % (wordOf 17 0b00011111111110101).length)
    rw [bit_eq_getD, Rule30StripCertificateTable.wordOf_length]

/-- **The center column does not repeat 00011111111110101**, from any time `T` on and read from any phase. -/
theorem center_not_00011111111110101 (T shift : Nat)
    (h : ∀ t : Nat, T ≤ t → Rule30Prize.center t = (wordOf 17 0b00011111111110101).getD ((t + shift) % 17) false) :
    False :=
  column_not_00011111111110101 single 0 rfl (fun x hx => decide_eq_false (by omega)) 0 T shift fun t ht => by
    rw [evolve_single_center, h t ht]

/-- The same in the kit's form: `00011111111110101` is not an `EventuallyWord` of the center column. -/
theorem not_eventually_00011111111110101 : ¬ Rule30StripCertificates.EventuallyWord (wordOf 17 0b00011111111110101) :=
  class_not_eventuallyWord cls00011111111110101 cls00011111111110101_valid

end

/-! ### The block 01111011111111111 at 17 cells

Widths 1 to 17 check 227,810 nodes, with heights up to 79; the classes cover
the 65,607 nodes of height 0 at 17 cells, with 268 ranks and labels modulo 17. -/

section
/-- Every width passes at every phase on the full certificate of `01111011111111111`. -/
theorem cls01111011111111111_levels :
    ∀ j, j < 17 → ∀ φ, φ < 17 → cls01111011111111111.levelOk j φ = true := by
  intro j hj φ hφ
  by_cases h0 : j < 15
  · have hl : cls01111011111111111W15.levels.length = 15 := rfl
    rw [ClassCert.levelOk_append cls01111011111111111W15 cls01111011111111111
      [cls01111011111111111L16, cls01111011111111111L17] rfl rfl (by omega) φ]
    exact cls01111011111111111W15_levels j (by omega) (by omega) φ hφ
  have hl : cls01111011111111111W17.levels.length = 17 := rfl
  rw [ClassCert.levelOk_append cls01111011111111111W17 cls01111011111111111
      [] rfl rfl (by omega) φ]
  exact cls01111011111111111W17_levels j (by omega) (by omega) φ hφ

/-- The certificate of `01111011111111111` passes at every width and phase. -/
theorem cls01111011111111111_valid : cls01111011111111111.Valid := by
  have hP : cls01111011111111111.block.length = 17 := Rule30StripCertificateTable.wordOf_length _ _
  have hW : cls01111011111111111.levels.length = 17 := rfl
  exact ⟨by omega, by omega, fun j φ hj hφ => cls01111011111111111_levels j (by omega) φ (by omega),
    fun φ hφ => cls01111011111111111_f φ (by omega)⟩

/-- **No column repeats 01111011111111111.** In the orbit of a row with a leftmost 1, no column repeats the block
`01111011111111111`, from any time `T` on and read from any phase. -/
theorem column_not_01111011111111111 (init : Int → Bool) (m : Int) (hm : init m = true)
    (hz : ∀ x : Int, x < m → init x = false) (k : Int) (T shift : Nat)
    (h : ∀ t : Nat, T ≤ t → evolve init t k = (wordOf 17 0b01111011111111111).getD ((t + shift) % 17) false) : False :=
  class_column init m hm hz cls01111011111111111 cls01111011111111111_valid k T shift fun t ht => by
    rw [h t ht]
    show _ = bit (wordOf 17 0b01111011111111111) ((t + shift) % (wordOf 17 0b01111011111111111).length)
    rw [bit_eq_getD, Rule30StripCertificateTable.wordOf_length]

/-- **The center column does not repeat 01111011111111111**, from any time `T` on and read from any phase. -/
theorem center_not_01111011111111111 (T shift : Nat)
    (h : ∀ t : Nat, T ≤ t → Rule30Prize.center t = (wordOf 17 0b01111011111111111).getD ((t + shift) % 17) false) :
    False :=
  column_not_01111011111111111 single 0 rfl (fun x hx => decide_eq_false (by omega)) 0 T shift fun t ht => by
    rw [evolve_single_center, h t ht]

/-- The same in the kit's form: `01111011111111111` is not an `EventuallyWord` of the center column. -/
theorem not_eventually_01111011111111111 : ¬ Rule30StripCertificates.EventuallyWord (wordOf 17 0b01111011111111111) :=
  class_not_eventuallyWord cls01111011111111111 cls01111011111111111_valid

end

end Rule30Open
