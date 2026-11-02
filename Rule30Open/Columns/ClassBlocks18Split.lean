module

public import Rule30Open.Columns.ClassSplit
public import Rule30Open.Columns.ClassBlocks18SplitA2
public import Rule30Open.Columns.ClassBlocks18SplitB2
public import Rule30Open.Columns.ClassBlocks18SplitC2
public import Rule30Open.Columns.ClassBlocks18SplitD2
public import Rule30Open.Columns.ClassBlocks18SplitE2
public import Rule30Open.Columns.ClassBlocks18SplitF3
public import Rule30Open.Columns.ClassBlocks18SplitG3
public import Rule30Open.Columns.ClassBlocks18SplitH3
public import Rule30Open.Columns.ClassBlocks18SplitI3
public import Rule30Open.Columns.ClassBlocks18SplitJ3

/-!
# The game with cyclic classes excludes ten blocks of period 18

[ClassGame](ClassGame.md) proves, for any block with a valid `ClassCert`, that no column of the orbit of a row with a
leftmost 1 repeats it (`class_column`). The class-test survey at period 18 and 16 cells finds fifteen blocks that the
game or the class test closes and that nothing else in this repository or the kit excludes. This module proves the
exclusion of `001010100111111111`, `001111001111111111`, `011110111111111111`, `000000000011000101`,
`000011111111111101`, `000000000011111001`, `000000000001000001`, `000010111111111001`, `001011111111110111` and
`000000011011111001`, each from a certificate at the least width at which the class test closes it, checked over the
modules [ClassBlocks18SplitA1](ClassBlocks18SplitA1.md), [ClassBlocks18SplitA2](ClassBlocks18SplitA2.md),
[ClassBlocks18SplitB1](ClassBlocks18SplitB1.md), [ClassBlocks18SplitB2](ClassBlocks18SplitB2.md),
[ClassBlocks18SplitC1](ClassBlocks18SplitC1.md), [ClassBlocks18SplitC2](ClassBlocks18SplitC2.md),
[ClassBlocks18SplitD1](ClassBlocks18SplitD1.md), [ClassBlocks18SplitD2](ClassBlocks18SplitD2.md),
[ClassBlocks18SplitE1](ClassBlocks18SplitE1.md), [ClassBlocks18SplitE2](ClassBlocks18SplitE2.md),
[ClassBlocks18SplitF1](ClassBlocks18SplitF1.md), [ClassBlocks18SplitF2](ClassBlocks18SplitF2.md),
[ClassBlocks18SplitF3](ClassBlocks18SplitF3.md), [ClassBlocks18SplitG1](ClassBlocks18SplitG1.md),
[ClassBlocks18SplitG2](ClassBlocks18SplitG2.md), [ClassBlocks18SplitG3](ClassBlocks18SplitG3.md),
[ClassBlocks18SplitH1](ClassBlocks18SplitH1.md), [ClassBlocks18SplitH2](ClassBlocks18SplitH2.md),
[ClassBlocks18SplitH3](ClassBlocks18SplitH3.md), [ClassBlocks18SplitI1](ClassBlocks18SplitI1.md),
[ClassBlocks18SplitI2](ClassBlocks18SplitI2.md), [ClassBlocks18SplitI3](ClassBlocks18SplitI3.md),
[ClassBlocks18SplitJ1](ClassBlocks18SplitJ1.md), [ClassBlocks18SplitJ2](ClassBlocks18SplitJ2.md),
[ClassBlocks18SplitJ3](ClassBlocks18SplitJ3.md), made by `computations/class_blocks_18_split.py`.
`ClassCert.levelOk_append` ([ClassSplit](ClassSplit.md)) carries the checks of the widths to the full certificates. The
other five blocks are in [ClassBlocks18](ClassBlocks18.md), [ClassBlocks18Mid](ClassBlocks18Mid.md) and
[ClassBlocks18Wide](ClassBlocks18Wide.md).

For each block `b` there is one section with `cls<b>_levels`, `cls<b>_valid` and the theorems `column_not_<b>`
(every column of every row with a leftmost 1), `center_not_<b>` (the center column) and
`not_eventually_<b>` (the kit's form).

The natural-language argument is `ClassBlocks18Split.md`, beside this file.
-/

@[expose] public section

-- Sequential elaboration: the kernel checks would otherwise run in parallel and stack their memory.
set_option Elab.async false

namespace Rule30Open

open Ruliology.CellularAutomata
open Rule30StripCertificateTable (wordOf)

/-! ### The block 001010100111111111 at 14 cells

Widths 1 to 14 check 66,196 nodes, with heights up to 45; the classes cover
the 21,009 nodes of height 0 at 14 cells, with 107 ranks and labels modulo 18 and 36. -/

section
/-- Every width passes at every phase on the full certificate of `001010100111111111`. -/
theorem cls001010100111111111_levels :
    ∀ j, j < 14 → ∀ φ, φ < 18 → cls001010100111111111.levelOk j φ = true := by
  intro j hj φ hφ
  have hl : cls001010100111111111W14.levels.length = 14 := rfl
  rw [ClassCert.levelOk_append cls001010100111111111W14 cls001010100111111111
      [] rfl rfl (by omega) φ]
  exact cls001010100111111111W14_levels j (by omega) (by omega) φ hφ

/-- The certificate of `001010100111111111` passes at every width and phase. -/
theorem cls001010100111111111_valid : cls001010100111111111.Valid := by
  have hP : cls001010100111111111.block.length = 18 := Rule30StripCertificateTable.wordOf_length _ _
  have hW : cls001010100111111111.levels.length = 14 := rfl
  exact ⟨by omega, by omega, fun j φ hj hφ => cls001010100111111111_levels j (by omega) φ (by omega),
    fun φ hφ => cls001010100111111111_f φ (by omega)⟩

/-- **No column repeats 001010100111111111.** In the orbit of a row with a leftmost 1, no column repeats the block
`001010100111111111`, from any time `T` on and read from any phase. -/
theorem column_not_001010100111111111 (init : Int → Bool) (m : Int) (hm : init m = true)
    (hz : ∀ x : Int, x < m → init x = false) (k : Int) (T shift : Nat)
    (h : ∀ t : Nat, T ≤ t → evolve init t k = (wordOf 18 0b001010100111111111).getD ((t + shift) % 18) false) : False :=
  class_column init m hm hz cls001010100111111111 cls001010100111111111_valid k T shift fun t ht => by
    rw [h t ht]
    show _ = bit (wordOf 18 0b001010100111111111) ((t + shift) % (wordOf 18 0b001010100111111111).length)
    rw [bit_eq_getD, Rule30StripCertificateTable.wordOf_length]

/-- **The center column does not repeat 001010100111111111**, from any time `T` on and read from any phase. -/
theorem center_not_001010100111111111 (T shift : Nat)
    (h : ∀ t : Nat, T ≤ t → Rule30Prize.center t = (wordOf 18 0b001010100111111111).getD ((t + shift) % 18) false) :
    False :=
  column_not_001010100111111111 single 0 rfl (fun x hx => decide_eq_false (by omega)) 0 T shift fun t ht => by
    rw [evolve_single_center, h t ht]

/-- The same in the kit's form: `001010100111111111` is not an `EventuallyWord` of the center column. -/
theorem not_eventually_001010100111111111 : ¬ Rule30StripCertificates.EventuallyWord (wordOf 18 0b001010100111111111) :=
  class_not_eventuallyWord cls001010100111111111 cls001010100111111111_valid

end

/-! ### The block 001111001111111111 at 15 cells

Widths 1 to 15 check 70,070 nodes, with heights up to 37; the classes cover
the 19,812 nodes of height 0 at 15 cells, with 138 ranks and labels modulo 18. -/

section
/-- Every width passes at every phase on the full certificate of `001111001111111111`. -/
theorem cls001111001111111111_levels :
    ∀ j, j < 15 → ∀ φ, φ < 18 → cls001111001111111111.levelOk j φ = true := by
  intro j hj φ hφ
  have hl : cls001111001111111111W15.levels.length = 15 := rfl
  rw [ClassCert.levelOk_append cls001111001111111111W15 cls001111001111111111
      [] rfl rfl (by omega) φ]
  exact cls001111001111111111W15_levels j (by omega) (by omega) φ hφ

/-- The certificate of `001111001111111111` passes at every width and phase. -/
theorem cls001111001111111111_valid : cls001111001111111111.Valid := by
  have hP : cls001111001111111111.block.length = 18 := Rule30StripCertificateTable.wordOf_length _ _
  have hW : cls001111001111111111.levels.length = 15 := rfl
  exact ⟨by omega, by omega, fun j φ hj hφ => cls001111001111111111_levels j (by omega) φ (by omega),
    fun φ hφ => cls001111001111111111_f φ (by omega)⟩

/-- **No column repeats 001111001111111111.** In the orbit of a row with a leftmost 1, no column repeats the block
`001111001111111111`, from any time `T` on and read from any phase. -/
theorem column_not_001111001111111111 (init : Int → Bool) (m : Int) (hm : init m = true)
    (hz : ∀ x : Int, x < m → init x = false) (k : Int) (T shift : Nat)
    (h : ∀ t : Nat, T ≤ t → evolve init t k = (wordOf 18 0b001111001111111111).getD ((t + shift) % 18) false) : False :=
  class_column init m hm hz cls001111001111111111 cls001111001111111111_valid k T shift fun t ht => by
    rw [h t ht]
    show _ = bit (wordOf 18 0b001111001111111111) ((t + shift) % (wordOf 18 0b001111001111111111).length)
    rw [bit_eq_getD, Rule30StripCertificateTable.wordOf_length]

/-- **The center column does not repeat 001111001111111111**, from any time `T` on and read from any phase. -/
theorem center_not_001111001111111111 (T shift : Nat)
    (h : ∀ t : Nat, T ≤ t → Rule30Prize.center t = (wordOf 18 0b001111001111111111).getD ((t + shift) % 18) false) :
    False :=
  column_not_001111001111111111 single 0 rfl (fun x hx => decide_eq_false (by omega)) 0 T shift fun t ht => by
    rw [evolve_single_center, h t ht]

/-- The same in the kit's form: `001111001111111111` is not an `EventuallyWord` of the center column. -/
theorem not_eventually_001111001111111111 : ¬ Rule30StripCertificates.EventuallyWord (wordOf 18 0b001111001111111111) :=
  class_not_eventuallyWord cls001111001111111111 cls001111001111111111_valid

end

/-! ### The block 011110111111111111 at 15 cells

Widths 1 to 15 check 80,736 nodes, with heights up to 80; the classes cover
the 20,080 nodes of height 0 at 15 cells, with 137 ranks and labels modulo 18 and 54. -/

section
/-- Every width passes at every phase on the full certificate of `011110111111111111`. -/
theorem cls011110111111111111_levels :
    ∀ j, j < 15 → ∀ φ, φ < 18 → cls011110111111111111.levelOk j φ = true := by
  intro j hj φ hφ
  have hl : cls011110111111111111W15.levels.length = 15 := rfl
  rw [ClassCert.levelOk_append cls011110111111111111W15 cls011110111111111111
      [] rfl rfl (by omega) φ]
  exact cls011110111111111111W15_levels j (by omega) (by omega) φ hφ

/-- The certificate of `011110111111111111` passes at every width and phase. -/
theorem cls011110111111111111_valid : cls011110111111111111.Valid := by
  have hP : cls011110111111111111.block.length = 18 := Rule30StripCertificateTable.wordOf_length _ _
  have hW : cls011110111111111111.levels.length = 15 := rfl
  exact ⟨by omega, by omega, fun j φ hj hφ => cls011110111111111111_levels j (by omega) φ (by omega),
    fun φ hφ => cls011110111111111111_f φ (by omega)⟩

/-- **No column repeats 011110111111111111.** In the orbit of a row with a leftmost 1, no column repeats the block
`011110111111111111`, from any time `T` on and read from any phase. -/
theorem column_not_011110111111111111 (init : Int → Bool) (m : Int) (hm : init m = true)
    (hz : ∀ x : Int, x < m → init x = false) (k : Int) (T shift : Nat)
    (h : ∀ t : Nat, T ≤ t → evolve init t k = (wordOf 18 0b011110111111111111).getD ((t + shift) % 18) false) : False :=
  class_column init m hm hz cls011110111111111111 cls011110111111111111_valid k T shift fun t ht => by
    rw [h t ht]
    show _ = bit (wordOf 18 0b011110111111111111) ((t + shift) % (wordOf 18 0b011110111111111111).length)
    rw [bit_eq_getD, Rule30StripCertificateTable.wordOf_length]

/-- **The center column does not repeat 011110111111111111**, from any time `T` on and read from any phase. -/
theorem center_not_011110111111111111 (T shift : Nat)
    (h : ∀ t : Nat, T ≤ t → Rule30Prize.center t = (wordOf 18 0b011110111111111111).getD ((t + shift) % 18) false) :
    False :=
  column_not_011110111111111111 single 0 rfl (fun x hx => decide_eq_false (by omega)) 0 T shift fun t ht => by
    rw [evolve_single_center, h t ht]

/-- The same in the kit's form: `011110111111111111` is not an `EventuallyWord` of the center column. -/
theorem not_eventually_011110111111111111 : ¬ Rule30StripCertificates.EventuallyWord (wordOf 18 0b011110111111111111) :=
  class_not_eventuallyWord cls011110111111111111 cls011110111111111111_valid

end

/-! ### The block 000000000011000101 at 15 cells

Widths 1 to 15 check 80,020 nodes, with heights up to 55; the classes cover
the 21,670 nodes of height 0 at 15 cells, with 208 ranks and labels modulo 18 and 36. -/

section
/-- Every width passes at every phase on the full certificate of `000000000011000101`. -/
theorem cls000000000011000101_levels :
    ∀ j, j < 15 → ∀ φ, φ < 18 → cls000000000011000101.levelOk j φ = true := by
  intro j hj φ hφ
  have hl : cls000000000011000101W15.levels.length = 15 := rfl
  rw [ClassCert.levelOk_append cls000000000011000101W15 cls000000000011000101
      [] rfl rfl (by omega) φ]
  exact cls000000000011000101W15_levels j (by omega) (by omega) φ hφ

/-- The certificate of `000000000011000101` passes at every width and phase. -/
theorem cls000000000011000101_valid : cls000000000011000101.Valid := by
  have hP : cls000000000011000101.block.length = 18 := Rule30StripCertificateTable.wordOf_length _ _
  have hW : cls000000000011000101.levels.length = 15 := rfl
  exact ⟨by omega, by omega, fun j φ hj hφ => cls000000000011000101_levels j (by omega) φ (by omega),
    fun φ hφ => cls000000000011000101_f φ (by omega)⟩

/-- **No column repeats 000000000011000101.** In the orbit of a row with a leftmost 1, no column repeats the block
`000000000011000101`, from any time `T` on and read from any phase. -/
theorem column_not_000000000011000101 (init : Int → Bool) (m : Int) (hm : init m = true)
    (hz : ∀ x : Int, x < m → init x = false) (k : Int) (T shift : Nat)
    (h : ∀ t : Nat, T ≤ t → evolve init t k = (wordOf 18 0b000000000011000101).getD ((t + shift) % 18) false) : False :=
  class_column init m hm hz cls000000000011000101 cls000000000011000101_valid k T shift fun t ht => by
    rw [h t ht]
    show _ = bit (wordOf 18 0b000000000011000101) ((t + shift) % (wordOf 18 0b000000000011000101).length)
    rw [bit_eq_getD, Rule30StripCertificateTable.wordOf_length]

/-- **The center column does not repeat 000000000011000101**, from any time `T` on and read from any phase. -/
theorem center_not_000000000011000101 (T shift : Nat)
    (h : ∀ t : Nat, T ≤ t → Rule30Prize.center t = (wordOf 18 0b000000000011000101).getD ((t + shift) % 18) false) :
    False :=
  column_not_000000000011000101 single 0 rfl (fun x hx => decide_eq_false (by omega)) 0 T shift fun t ht => by
    rw [evolve_single_center, h t ht]

/-- The same in the kit's form: `000000000011000101` is not an `EventuallyWord` of the center column. -/
theorem not_eventually_000000000011000101 : ¬ Rule30StripCertificates.EventuallyWord (wordOf 18 0b000000000011000101) :=
  class_not_eventuallyWord cls000000000011000101 cls000000000011000101_valid

end

/-! ### The block 000011111111111101 at 15 cells

Widths 1 to 15 check 88,328 nodes, with heights up to 51; the classes cover
the 25,091 nodes of height 0 at 15 cells, with 232 ranks and labels modulo 18 and 36. -/

section
/-- Every width passes at every phase on the full certificate of `000011111111111101`. -/
theorem cls000011111111111101_levels :
    ∀ j, j < 15 → ∀ φ, φ < 18 → cls000011111111111101.levelOk j φ = true := by
  intro j hj φ hφ
  have hl : cls000011111111111101W15.levels.length = 15 := rfl
  rw [ClassCert.levelOk_append cls000011111111111101W15 cls000011111111111101
      [] rfl rfl (by omega) φ]
  exact cls000011111111111101W15_levels j (by omega) (by omega) φ hφ

/-- The certificate of `000011111111111101` passes at every width and phase. -/
theorem cls000011111111111101_valid : cls000011111111111101.Valid := by
  have hP : cls000011111111111101.block.length = 18 := Rule30StripCertificateTable.wordOf_length _ _
  have hW : cls000011111111111101.levels.length = 15 := rfl
  exact ⟨by omega, by omega, fun j φ hj hφ => cls000011111111111101_levels j (by omega) φ (by omega),
    fun φ hφ => cls000011111111111101_f φ (by omega)⟩

/-- **No column repeats 000011111111111101.** In the orbit of a row with a leftmost 1, no column repeats the block
`000011111111111101`, from any time `T` on and read from any phase. -/
theorem column_not_000011111111111101 (init : Int → Bool) (m : Int) (hm : init m = true)
    (hz : ∀ x : Int, x < m → init x = false) (k : Int) (T shift : Nat)
    (h : ∀ t : Nat, T ≤ t → evolve init t k = (wordOf 18 0b000011111111111101).getD ((t + shift) % 18) false) : False :=
  class_column init m hm hz cls000011111111111101 cls000011111111111101_valid k T shift fun t ht => by
    rw [h t ht]
    show _ = bit (wordOf 18 0b000011111111111101) ((t + shift) % (wordOf 18 0b000011111111111101).length)
    rw [bit_eq_getD, Rule30StripCertificateTable.wordOf_length]

/-- **The center column does not repeat 000011111111111101**, from any time `T` on and read from any phase. -/
theorem center_not_000011111111111101 (T shift : Nat)
    (h : ∀ t : Nat, T ≤ t → Rule30Prize.center t = (wordOf 18 0b000011111111111101).getD ((t + shift) % 18) false) :
    False :=
  column_not_000011111111111101 single 0 rfl (fun x hx => decide_eq_false (by omega)) 0 T shift fun t ht => by
    rw [evolve_single_center, h t ht]

/-- The same in the kit's form: `000011111111111101` is not an `EventuallyWord` of the center column. -/
theorem not_eventually_000011111111111101 : ¬ Rule30StripCertificates.EventuallyWord (wordOf 18 0b000011111111111101) :=
  class_not_eventuallyWord cls000011111111111101 cls000011111111111101_valid

end

/-! ### The block 000000000011111001 at 16 cells

Widths 1 to 16 check 105,158 nodes, with heights up to 53; the classes cover
the 30,320 nodes of height 0 at 16 cells, with 197 ranks and labels modulo 18 and 36. -/

section
/-- Every width passes at every phase on the full certificate of `000000000011111001`. -/
theorem cls000000000011111001_levels :
    ∀ j, j < 16 → ∀ φ, φ < 18 → cls000000000011111001.levelOk j φ = true := by
  intro j hj φ hφ
  by_cases h0 : j < 15
  · have hl : cls000000000011111001W15.levels.length = 15 := rfl
    rw [ClassCert.levelOk_append cls000000000011111001W15 cls000000000011111001
      [cls000000000011111001L16] rfl rfl (by omega) φ]
    exact cls000000000011111001W15_levels j (by omega) (by omega) φ hφ
  have hl : cls000000000011111001W16.levels.length = 16 := rfl
  rw [ClassCert.levelOk_append cls000000000011111001W16 cls000000000011111001
      [] rfl rfl (by omega) φ]
  exact cls000000000011111001W16_levels j (by omega) (by omega) φ hφ

/-- The certificate of `000000000011111001` passes at every width and phase. -/
theorem cls000000000011111001_valid : cls000000000011111001.Valid := by
  have hP : cls000000000011111001.block.length = 18 := Rule30StripCertificateTable.wordOf_length _ _
  have hW : cls000000000011111001.levels.length = 16 := rfl
  exact ⟨by omega, by omega, fun j φ hj hφ => cls000000000011111001_levels j (by omega) φ (by omega),
    fun φ hφ => cls000000000011111001_f φ (by omega)⟩

/-- **No column repeats 000000000011111001.** In the orbit of a row with a leftmost 1, no column repeats the block
`000000000011111001`, from any time `T` on and read from any phase. -/
theorem column_not_000000000011111001 (init : Int → Bool) (m : Int) (hm : init m = true)
    (hz : ∀ x : Int, x < m → init x = false) (k : Int) (T shift : Nat)
    (h : ∀ t : Nat, T ≤ t → evolve init t k = (wordOf 18 0b000000000011111001).getD ((t + shift) % 18) false) : False :=
  class_column init m hm hz cls000000000011111001 cls000000000011111001_valid k T shift fun t ht => by
    rw [h t ht]
    show _ = bit (wordOf 18 0b000000000011111001) ((t + shift) % (wordOf 18 0b000000000011111001).length)
    rw [bit_eq_getD, Rule30StripCertificateTable.wordOf_length]

/-- **The center column does not repeat 000000000011111001**, from any time `T` on and read from any phase. -/
theorem center_not_000000000011111001 (T shift : Nat)
    (h : ∀ t : Nat, T ≤ t → Rule30Prize.center t = (wordOf 18 0b000000000011111001).getD ((t + shift) % 18) false) :
    False :=
  column_not_000000000011111001 single 0 rfl (fun x hx => decide_eq_false (by omega)) 0 T shift fun t ht => by
    rw [evolve_single_center, h t ht]

/-- The same in the kit's form: `000000000011111001` is not an `EventuallyWord` of the center column. -/
theorem not_eventually_000000000011111001 : ¬ Rule30StripCertificates.EventuallyWord (wordOf 18 0b000000000011111001) :=
  class_not_eventuallyWord cls000000000011111001 cls000000000011111001_valid

end

/-! ### The block 000000000001000001 at 16 cells

Widths 1 to 16 check 118,106 nodes, with heights up to 98; the classes cover
the 23,267 nodes of height 0 at 16 cells, with 102 ranks and labels modulo 18. -/

section
/-- Every width passes at every phase on the full certificate of `000000000001000001`. -/
theorem cls000000000001000001_levels :
    ∀ j, j < 16 → ∀ φ, φ < 18 → cls000000000001000001.levelOk j φ = true := by
  intro j hj φ hφ
  by_cases h0 : j < 15
  · have hl : cls000000000001000001W15.levels.length = 15 := rfl
    rw [ClassCert.levelOk_append cls000000000001000001W15 cls000000000001000001
      [cls000000000001000001L16] rfl rfl (by omega) φ]
    exact cls000000000001000001W15_levels j (by omega) (by omega) φ hφ
  have hl : cls000000000001000001W16.levels.length = 16 := rfl
  rw [ClassCert.levelOk_append cls000000000001000001W16 cls000000000001000001
      [] rfl rfl (by omega) φ]
  exact cls000000000001000001W16_levels j (by omega) (by omega) φ hφ

/-- The certificate of `000000000001000001` passes at every width and phase. -/
theorem cls000000000001000001_valid : cls000000000001000001.Valid := by
  have hP : cls000000000001000001.block.length = 18 := Rule30StripCertificateTable.wordOf_length _ _
  have hW : cls000000000001000001.levels.length = 16 := rfl
  exact ⟨by omega, by omega, fun j φ hj hφ => cls000000000001000001_levels j (by omega) φ (by omega),
    fun φ hφ => cls000000000001000001_f φ (by omega)⟩

/-- **No column repeats 000000000001000001.** In the orbit of a row with a leftmost 1, no column repeats the block
`000000000001000001`, from any time `T` on and read from any phase. -/
theorem column_not_000000000001000001 (init : Int → Bool) (m : Int) (hm : init m = true)
    (hz : ∀ x : Int, x < m → init x = false) (k : Int) (T shift : Nat)
    (h : ∀ t : Nat, T ≤ t → evolve init t k = (wordOf 18 0b000000000001000001).getD ((t + shift) % 18) false) : False :=
  class_column init m hm hz cls000000000001000001 cls000000000001000001_valid k T shift fun t ht => by
    rw [h t ht]
    show _ = bit (wordOf 18 0b000000000001000001) ((t + shift) % (wordOf 18 0b000000000001000001).length)
    rw [bit_eq_getD, Rule30StripCertificateTable.wordOf_length]

/-- **The center column does not repeat 000000000001000001**, from any time `T` on and read from any phase. -/
theorem center_not_000000000001000001 (T shift : Nat)
    (h : ∀ t : Nat, T ≤ t → Rule30Prize.center t = (wordOf 18 0b000000000001000001).getD ((t + shift) % 18) false) :
    False :=
  column_not_000000000001000001 single 0 rfl (fun x hx => decide_eq_false (by omega)) 0 T shift fun t ht => by
    rw [evolve_single_center, h t ht]

/-- The same in the kit's form: `000000000001000001` is not an `EventuallyWord` of the center column. -/
theorem not_eventually_000000000001000001 : ¬ Rule30StripCertificates.EventuallyWord (wordOf 18 0b000000000001000001) :=
  class_not_eventuallyWord cls000000000001000001 cls000000000001000001_valid

end

/-! ### The block 000010111111111001 at 16 cells

Widths 1 to 16 check 119,668 nodes, with heights up to 85; the classes cover
the 32,054 nodes of height 0 at 16 cells, with 102 ranks and labels modulo 18 and 36. -/

section
/-- Every width passes at every phase on the full certificate of `000010111111111001`. -/
theorem cls000010111111111001_levels :
    ∀ j, j < 16 → ∀ φ, φ < 18 → cls000010111111111001.levelOk j φ = true := by
  intro j hj φ hφ
  by_cases h0 : j < 15
  · have hl : cls000010111111111001W15.levels.length = 15 := rfl
    rw [ClassCert.levelOk_append cls000010111111111001W15 cls000010111111111001
      [cls000010111111111001L16] rfl rfl (by omega) φ]
    exact cls000010111111111001W15_levels j (by omega) (by omega) φ hφ
  have hl : cls000010111111111001W16.levels.length = 16 := rfl
  rw [ClassCert.levelOk_append cls000010111111111001W16 cls000010111111111001
      [] rfl rfl (by omega) φ]
  exact cls000010111111111001W16_levels j (by omega) (by omega) φ hφ

/-- The certificate of `000010111111111001` passes at every width and phase. -/
theorem cls000010111111111001_valid : cls000010111111111001.Valid := by
  have hP : cls000010111111111001.block.length = 18 := Rule30StripCertificateTable.wordOf_length _ _
  have hW : cls000010111111111001.levels.length = 16 := rfl
  exact ⟨by omega, by omega, fun j φ hj hφ => cls000010111111111001_levels j (by omega) φ (by omega),
    fun φ hφ => cls000010111111111001_f φ (by omega)⟩

/-- **No column repeats 000010111111111001.** In the orbit of a row with a leftmost 1, no column repeats the block
`000010111111111001`, from any time `T` on and read from any phase. -/
theorem column_not_000010111111111001 (init : Int → Bool) (m : Int) (hm : init m = true)
    (hz : ∀ x : Int, x < m → init x = false) (k : Int) (T shift : Nat)
    (h : ∀ t : Nat, T ≤ t → evolve init t k = (wordOf 18 0b000010111111111001).getD ((t + shift) % 18) false) : False :=
  class_column init m hm hz cls000010111111111001 cls000010111111111001_valid k T shift fun t ht => by
    rw [h t ht]
    show _ = bit (wordOf 18 0b000010111111111001) ((t + shift) % (wordOf 18 0b000010111111111001).length)
    rw [bit_eq_getD, Rule30StripCertificateTable.wordOf_length]

/-- **The center column does not repeat 000010111111111001**, from any time `T` on and read from any phase. -/
theorem center_not_000010111111111001 (T shift : Nat)
    (h : ∀ t : Nat, T ≤ t → Rule30Prize.center t = (wordOf 18 0b000010111111111001).getD ((t + shift) % 18) false) :
    False :=
  column_not_000010111111111001 single 0 rfl (fun x hx => decide_eq_false (by omega)) 0 T shift fun t ht => by
    rw [evolve_single_center, h t ht]

/-- The same in the kit's form: `000010111111111001` is not an `EventuallyWord` of the center column. -/
theorem not_eventually_000010111111111001 : ¬ Rule30StripCertificates.EventuallyWord (wordOf 18 0b000010111111111001) :=
  class_not_eventuallyWord cls000010111111111001 cls000010111111111001_valid

end

/-! ### The block 001011111111110111 at 16 cells

Widths 1 to 16 check 150,174 nodes, with heights up to 52; the classes cover
the 43,557 nodes of height 0 at 16 cells, with 189 ranks and labels modulo 18 and 36. -/

section
/-- Every width passes at every phase on the full certificate of `001011111111110111`. -/
theorem cls001011111111110111_levels :
    ∀ j, j < 16 → ∀ φ, φ < 18 → cls001011111111110111.levelOk j φ = true := by
  intro j hj φ hφ
  by_cases h0 : j < 15
  · have hl : cls001011111111110111W15.levels.length = 15 := rfl
    rw [ClassCert.levelOk_append cls001011111111110111W15 cls001011111111110111
      [cls001011111111110111L16] rfl rfl (by omega) φ]
    exact cls001011111111110111W15_levels j (by omega) (by omega) φ hφ
  have hl : cls001011111111110111W16.levels.length = 16 := rfl
  rw [ClassCert.levelOk_append cls001011111111110111W16 cls001011111111110111
      [] rfl rfl (by omega) φ]
  exact cls001011111111110111W16_levels j (by omega) (by omega) φ hφ

/-- The certificate of `001011111111110111` passes at every width and phase. -/
theorem cls001011111111110111_valid : cls001011111111110111.Valid := by
  have hP : cls001011111111110111.block.length = 18 := Rule30StripCertificateTable.wordOf_length _ _
  have hW : cls001011111111110111.levels.length = 16 := rfl
  exact ⟨by omega, by omega, fun j φ hj hφ => cls001011111111110111_levels j (by omega) φ (by omega),
    fun φ hφ => cls001011111111110111_f φ (by omega)⟩

/-- **No column repeats 001011111111110111.** In the orbit of a row with a leftmost 1, no column repeats the block
`001011111111110111`, from any time `T` on and read from any phase. -/
theorem column_not_001011111111110111 (init : Int → Bool) (m : Int) (hm : init m = true)
    (hz : ∀ x : Int, x < m → init x = false) (k : Int) (T shift : Nat)
    (h : ∀ t : Nat, T ≤ t → evolve init t k = (wordOf 18 0b001011111111110111).getD ((t + shift) % 18) false) : False :=
  class_column init m hm hz cls001011111111110111 cls001011111111110111_valid k T shift fun t ht => by
    rw [h t ht]
    show _ = bit (wordOf 18 0b001011111111110111) ((t + shift) % (wordOf 18 0b001011111111110111).length)
    rw [bit_eq_getD, Rule30StripCertificateTable.wordOf_length]

/-- **The center column does not repeat 001011111111110111**, from any time `T` on and read from any phase. -/
theorem center_not_001011111111110111 (T shift : Nat)
    (h : ∀ t : Nat, T ≤ t → Rule30Prize.center t = (wordOf 18 0b001011111111110111).getD ((t + shift) % 18) false) :
    False :=
  column_not_001011111111110111 single 0 rfl (fun x hx => decide_eq_false (by omega)) 0 T shift fun t ht => by
    rw [evolve_single_center, h t ht]

/-- The same in the kit's form: `001011111111110111` is not an `EventuallyWord` of the center column. -/
theorem not_eventually_001011111111110111 : ¬ Rule30StripCertificates.EventuallyWord (wordOf 18 0b001011111111110111) :=
  class_not_eventuallyWord cls001011111111110111 cls001011111111110111_valid

end

/-! ### The block 000000011011111001 at 16 cells

Widths 1 to 16 check 152,538 nodes, with heights up to 68; the classes cover
the 42,159 nodes of height 0 at 16 cells, with 173 ranks and labels modulo 18. -/

section
/-- Every width passes at every phase on the full certificate of `000000011011111001`. -/
theorem cls000000011011111001_levels :
    ∀ j, j < 16 → ∀ φ, φ < 18 → cls000000011011111001.levelOk j φ = true := by
  intro j hj φ hφ
  by_cases h0 : j < 15
  · have hl : cls000000011011111001W15.levels.length = 15 := rfl
    rw [ClassCert.levelOk_append cls000000011011111001W15 cls000000011011111001
      [cls000000011011111001L16] rfl rfl (by omega) φ]
    exact cls000000011011111001W15_levels j (by omega) (by omega) φ hφ
  have hl : cls000000011011111001W16.levels.length = 16 := rfl
  rw [ClassCert.levelOk_append cls000000011011111001W16 cls000000011011111001
      [] rfl rfl (by omega) φ]
  exact cls000000011011111001W16_levels j (by omega) (by omega) φ hφ

/-- The certificate of `000000011011111001` passes at every width and phase. -/
theorem cls000000011011111001_valid : cls000000011011111001.Valid := by
  have hP : cls000000011011111001.block.length = 18 := Rule30StripCertificateTable.wordOf_length _ _
  have hW : cls000000011011111001.levels.length = 16 := rfl
  exact ⟨by omega, by omega, fun j φ hj hφ => cls000000011011111001_levels j (by omega) φ (by omega),
    fun φ hφ => cls000000011011111001_f φ (by omega)⟩

/-- **No column repeats 000000011011111001.** In the orbit of a row with a leftmost 1, no column repeats the block
`000000011011111001`, from any time `T` on and read from any phase. -/
theorem column_not_000000011011111001 (init : Int → Bool) (m : Int) (hm : init m = true)
    (hz : ∀ x : Int, x < m → init x = false) (k : Int) (T shift : Nat)
    (h : ∀ t : Nat, T ≤ t → evolve init t k = (wordOf 18 0b000000011011111001).getD ((t + shift) % 18) false) : False :=
  class_column init m hm hz cls000000011011111001 cls000000011011111001_valid k T shift fun t ht => by
    rw [h t ht]
    show _ = bit (wordOf 18 0b000000011011111001) ((t + shift) % (wordOf 18 0b000000011011111001).length)
    rw [bit_eq_getD, Rule30StripCertificateTable.wordOf_length]

/-- **The center column does not repeat 000000011011111001**, from any time `T` on and read from any phase. -/
theorem center_not_000000011011111001 (T shift : Nat)
    (h : ∀ t : Nat, T ≤ t → Rule30Prize.center t = (wordOf 18 0b000000011011111001).getD ((t + shift) % 18) false) :
    False :=
  column_not_000000011011111001 single 0 rfl (fun x hx => decide_eq_false (by omega)) 0 T shift fun t ht => by
    rw [evolve_single_center, h t ht]

/-- The same in the kit's form: `000000011011111001` is not an `EventuallyWord` of the center column. -/
theorem not_eventually_000000011011111001 : ¬ Rule30StripCertificates.EventuallyWord (wordOf 18 0b000000011011111001) :=
  class_not_eventuallyWord cls000000011011111001 cls000000011011111001_valid

end

end Rule30Open
