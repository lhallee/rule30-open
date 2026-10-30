module

public import Rule30Open.Columns.BitGame

/-!
# The game decided in the kernel excludes 62 more blocks of period 21 that need 9 to 12 cells

[BitGame](BitGame.md) decides the finite game in the kernel from the block alone (`gameCheck`), and `bitGame_column`
turns a passing check into an exclusion. Here the check runs on the 62 blocks of period 21 that the game excludes at a
width of 9 to 12 and that neither the kit nor [WallSets](WallSets.md) excludes.

* `blocks21Wide`: the blocks, each as its least rotation, with the parameters of `gameCheck`; `blocks21Wide_check`: every
  check passes.
* `center_not_blocks21Wide`, `not_eventually_blocks21Wide`: the center column of the single cell does not eventually repeat
  any of them, in any rotation, and in the kit's form `EventuallyWord`.

The natural-language argument is `BitBlocks21Wide.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

open Ruliology.CellularAutomata BitGame

/-- The blocks of period 21 that the game excludes at a width of 9 to 12 and that the kit and `WallSets` do not
exclude, each as its least rotation `wordOf 21 bits`, with the width `K`, the steps `D`, the rounds and the search fuel
of `gameCheck`, from `computations/bit_game.py`. -/
def blocks21Wide : List ((Nat × Nat) × (Nat × Nat × Nat × Nat)) := [
    ((21, 0b000000000000000000111), (11, 37, 1, 300)), ((21, 0b000000000000000110001), (12, 32, 1, 300)),
    ((21, 0b000000000000000110101), (11, 126, 0, 300)), ((21, 0b000000000000000111011), (9, 39, 1, 300)),
    ((21, 0b000000000000001001011), (10, 62, 1, 300)), ((21, 0b000000000000001001101), (9, 59, 1, 300)),
    ((21, 0b000000000000011001111), (9, 66, 0, 300)), ((21, 0b000000000000011011111), (10, 30, 1, 300)),
    ((21, 0b000000000000011100011), (11, 124, 0, 300)), ((21, 0b000000000000011111001), (10, 62, 1, 300)),
    ((21, 0b000000000000100001011), (11, 57, 1, 300)), ((21, 0b000000000000101001111), (10, 35, 1, 300)),
    ((21, 0b000000000000101101011), (9, 34, 2, 300)), ((21, 0b000000000000110110111), (10, 122, 0, 300)),
    ((21, 0b000000000000111100001), (11, 77, 2, 300)), ((21, 0b000000000001001011011), (9, 51, 2, 300)),
    ((21, 0b000000000001101100101), (11, 65, 1, 300)), ((21, 0b000000000001101101111), (10, 106, 0, 300)),
    ((21, 0b000000000001101111111), (9, 23, 1, 300)), ((21, 0b000000000010000000101), (11, 54, 1, 300)),
    ((21, 0b000000000010001001111), (11, 37, 1, 300)), ((21, 0b000000000010111111101), (12, 55, 1, 300)),
    ((21, 0b000000000011011101111), (11, 78, 1, 300)), ((21, 0b000000000101111100111), (11, 91, 1, 300)),
    ((21, 0b000000000110100100001), (12, 132, 0, 300)), ((21, 0b000000000110110000001), (11, 33, 2, 300)),
    ((21, 0b000000000110110011111), (11, 43, 2, 300)), ((21, 0b000000000110110100011), (12, 62, 2, 300)),
    ((21, 0b000000001011111110011), (9, 60, 0, 300)), ((21, 0b000000001011111110111), (9, 57, 1, 300)),
    ((21, 0b000000001101111111001), (9, 67, 1, 300)), ((21, 0b000000001110100000011), (9, 68, 0, 300)),
    ((21, 0b000000010111110011011), (10, 37, 1, 300)), ((21, 0b000000011000111111011), (11, 65, 1, 300)),
    ((21, 0b000000011011111111001), (10, 39, 1, 300)), ((21, 0b000000101111100111011), (10, 73, 2, 300)),
    ((21, 0b000000101111100111111), (12, 126, 0, 300)), ((21, 0b000000101111111001001), (10, 47, 2, 300)),
    ((21, 0b000000101111111101111), (9, 81, 1, 300)), ((21, 0b000000101111111111001), (9, 40, 1, 300)),
    ((21, 0b000000110111111111001), (12, 74, 1, 300)), ((21, 0b000001010011111111001), (11, 71, 1, 300)),
    ((21, 0b000001010011111111011), (11, 64, 1, 300)), ((21, 0b000001011100111111011), (12, 104, 1, 300)),
    ((21, 0b000010100111111111011), (12, 71, 1, 300)), ((21, 0b000010111111100111111), (12, 56, 1, 300)),
    ((21, 0b000011111111110011111), (10, 40, 1, 300)), ((21, 0b000011111111111100111), (10, 54, 1, 300)),
    ((21, 0b000011111111111111001), (9, 38, 1, 300)), ((21, 0b000101001111111111001), (10, 56, 1, 300)),
    ((21, 0b000101001111111111011), (12, 62, 1, 300)), ((21, 0b000101011111111111011), (10, 55, 0, 300)),
    ((21, 0b000101110011111111001), (11, 64, 1, 300)), ((21, 0b000101111111111111001), (11, 54, 1, 300)),
    ((21, 0b000111110011111111111), (11, 37, 1, 300)), ((21, 0b000111111111111001011), (9, 36, 1, 300)),
    ((21, 0b001010111111111111011), (12, 112, 0, 300)), ((21, 0b001110101111111111111), (12, 74, 1, 300)),
    ((21, 0b001111100111111111101), (11, 58, 1, 300)), ((21, 0b001111110011111111011), (12, 82, 1, 300)),
    ((21, 0b001111111001111111111), (12, 121, 0, 300)), ((21, 0b001111111111111010101), (11, 78, 1, 300))]

set_option Elab.async false

set_option maxHeartbeats 0 in
theorem check_000000000000000000111 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000000000000111) 11 37 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000000000110001 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000000000110001) 12 32 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000000000110101 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000000000110101) 11 126 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000000000111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000000000111011) 9 39 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000000001001011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000000001001011) 10 62 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000000001001101 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000000001001101) 9 59 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000000011001111 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000000011001111) 9 66 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000000011011111 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000000011011111) 10 30 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000000011100011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000000011100011) 11 124 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000000011111001 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000000011111001) 10 62 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000000100001011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000000100001011) 11 57 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000000101001111 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000000101001111) 10 35 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000000101101011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000000101101011) 9 34 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000000110110111 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000000110110111) 10 122 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000000111100001 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000000111100001) 11 77 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000001001011011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000001001011011) 9 51 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000001101100101 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000001101100101) 11 65 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000001101101111 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000001101101111) 10 106 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000001101111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000001101111111) 9 23 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000010000000101 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000010000000101) 11 54 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000010001001111 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000010001001111) 11 37 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000010111111101 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000010111111101) 12 55 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000011011101111 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000011011101111) 11 78 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000101111100111 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000101111100111) 11 91 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000110100100001 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000110100100001) 12 132 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000110110000001 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000110110000001) 11 33 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000110110011111 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000110110011111) 11 43 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000110110100011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000110110100011) 12 62 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000001011111110011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000001011111110011) 9 60 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000001011111110111 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000001011111110111) 9 57 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000001101111111001 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000001101111111001) 9 67 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000001110100000011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000001110100000011) 9 68 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000010111110011011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000010111110011011) 10 37 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000011000111111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000011000111111011) 11 65 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000011011111111001 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000011011111111001) 10 39 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000101111100111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000101111100111011) 10 73 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000101111100111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000101111100111111) 12 126 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000101111111001001 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000101111111001001) 10 47 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000101111111101111 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000101111111101111) 9 81 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000101111111111001 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000101111111111001) 9 40 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000110111111111001 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000110111111111001) 12 74 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000001010011111111001 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000001010011111111001) 11 71 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000001010011111111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000001010011111111011) 11 64 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000001011100111111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000001011100111111011) 12 104 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000010100111111111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000010100111111111011) 12 71 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000010111111100111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000010111111100111111) 12 56 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000011111111110011111 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000011111111110011111) 10 40 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000011111111111100111 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000011111111111100111) 10 54 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000011111111111111001 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000011111111111111001) 9 38 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000101001111111111001 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000101001111111111001) 10 56 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000101001111111111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000101001111111111011) 12 62 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000101011111111111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000101011111111111011) 10 55 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000101110011111111001 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000101110011111111001) 11 64 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000101111111111111001 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000101111111111111001) 11 54 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000111110011111111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000111110011111111111) 11 37 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000111111111111001011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000111111111111001011) 9 36 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_001010111111111111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b001010111111111111011) 12 112 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_001110101111111111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b001110101111111111111) 12 74 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_001111100111111111101 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b001111100111111111101) 11 58 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_001111110011111111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b001111110011111111011) 12 82 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_001111111001111111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b001111111001111111111) 12 121 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_001111111111111010101 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b001111111111111010101) 11 78 1 300 = true := by decide +kernel

theorem blocks21Wide_check : ∀ e ∈ blocks21Wide,
    gameCheck (Rule30StripCertificateTable.wordOf e.1.1 e.1.2) e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2 = true := by
  intro e he
  simp only [blocks21Wide, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl
  · exact check_000000000000000000111
  · exact check_000000000000000110001
  · exact check_000000000000000110101
  · exact check_000000000000000111011
  · exact check_000000000000001001011
  · exact check_000000000000001001101
  · exact check_000000000000011001111
  · exact check_000000000000011011111
  · exact check_000000000000011100011
  · exact check_000000000000011111001
  · exact check_000000000000100001011
  · exact check_000000000000101001111
  · exact check_000000000000101101011
  · exact check_000000000000110110111
  · exact check_000000000000111100001
  · exact check_000000000001001011011
  · exact check_000000000001101100101
  · exact check_000000000001101101111
  · exact check_000000000001101111111
  · exact check_000000000010000000101
  · exact check_000000000010001001111
  · exact check_000000000010111111101
  · exact check_000000000011011101111
  · exact check_000000000101111100111
  · exact check_000000000110100100001
  · exact check_000000000110110000001
  · exact check_000000000110110011111
  · exact check_000000000110110100011
  · exact check_000000001011111110011
  · exact check_000000001011111110111
  · exact check_000000001101111111001
  · exact check_000000001110100000011
  · exact check_000000010111110011011
  · exact check_000000011000111111011
  · exact check_000000011011111111001
  · exact check_000000101111100111011
  · exact check_000000101111100111111
  · exact check_000000101111111001001
  · exact check_000000101111111101111
  · exact check_000000101111111111001
  · exact check_000000110111111111001
  · exact check_000001010011111111001
  · exact check_000001010011111111011
  · exact check_000001011100111111011
  · exact check_000010100111111111011
  · exact check_000010111111100111111
  · exact check_000011111111110011111
  · exact check_000011111111111100111
  · exact check_000011111111111111001
  · exact check_000101001111111111001
  · exact check_000101001111111111011
  · exact check_000101011111111111011
  · exact check_000101110011111111001
  · exact check_000101111111111111001
  · exact check_000111110011111111111
  · exact check_000111111111111001011
  · exact check_001010111111111111011
  · exact check_001110101111111111111
  · exact check_001111100111111111101
  · exact check_001111110011111111011
  · exact check_001111111001111111111
  · exact check_001111111111111010101

/-- **The 62 blocks**: for each entry of `blocks21Wide`, the center column is not, from any time `T` on, the block
`wordOf 21 bits`, read from any phase. -/
theorem center_not_blocks21Wide (e : (Nat × Nat) × (Nat × Nat × Nat × Nat)) (he : e ∈ blocks21Wide) (T shift : Nat)
    (h : ∀ t : Nat, T ≤ t → Rule30Prize.center t =
      (Rule30StripCertificateTable.wordOf e.1.1 e.1.2).getD ((t + shift) % e.1.1) false) : False :=
  center_not_bitGame _ _ _ _ _ (blocks21Wide_check e he) T shift fun t ht => by
    rw [h t ht, Rule30StripCertificateTable.wordOf_length]

/-- The same in the kit's form: none of the 62 blocks is an `EventuallyWord` of the center column. -/
theorem not_eventually_blocks21Wide (e : (Nat × Nat) × (Nat × Nat × Nat × Nat)) (he : e ∈ blocks21Wide) :
    ¬ Rule30StripCertificates.EventuallyWord (Rule30StripCertificateTable.wordOf e.1.1 e.1.2) :=
  bitGame_not_eventuallyWord _ _ _ _ _ (blocks21Wide_check e he)

end Rule30Open
