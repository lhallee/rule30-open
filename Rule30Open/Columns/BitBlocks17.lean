module

public import Rule30Open.Columns.BitGame
public import Rule30Open.Columns.WallSets

/-!
# The game decided in the kernel and the window-set check exclude 99 more blocks of period 17

[BitGame](BitGame.md) decides the finite game in the kernel from the block alone (`gameCheck`), and `bitGame_column`
turns a passing check into an exclusion. Here the check runs on the 64 blocks of period 17 that the game excludes at a
width of at most 12 and that neither the kit nor [WallSets](WallSets.md) excludes.

* `blocks17`: the blocks, each as its least rotation, with the parameters of `gameCheck`; `blocks17_check`: every
  check passes.
* `center_not_blocks17`, `not_eventually_blocks17`: the center column of the single cell does not eventually repeat
  any of them, in any rotation, and in the kit's form `EventuallyWord`.
* `wallBlocks17`, `center_not_wallBlocks17`: the 35 other blocks of period 17 that the game excludes beyond the kit,
  each passing `WallSets.wallSet`, so `center_wall_set_block` excludes them.

The natural-language argument is `BitBlocks17.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

open Ruliology.CellularAutomata BitGame

/-- The blocks of period 17 that the game excludes at a width of at most 12 and that the kit and `WallSets` do not
exclude, each as its least rotation `wordOf 17 bits`, with the width `K`, the steps `D`, the rounds and the search fuel
of `gameCheck`, from `computations/bit_game.py`. -/
def blocks17 : List ((Nat × Nat) × (Nat × Nat × Nat × Nat)) := [
    ((17, 0b00000000000000101), (7, 12, 2, 300)), ((17, 0b00000000000001101), (6, 13, 2, 300)),
    ((17, 0b00000000000001111), (6, 14, 2, 300)), ((17, 0b00000000000010001), (8, 24, 3, 300)),
    ((17, 0b00000000000010011), (6, 31, 1, 300)), ((17, 0b00000000000011011), (6, 30, 1, 300)),
    ((17, 0b00000000000011101), (7, 13, 2, 300)), ((17, 0b00000000000011111), (8, 24, 3, 300)),
    ((17, 0b00000000000101001), (6, 12, 2, 300)), ((17, 0b00000000000101011), (6, 33, 1, 300)),
    ((17, 0b00000000000101111), (6, 38, 1, 300)), ((17, 0b00000000000110011), (6, 31, 1, 300)),
    ((17, 0b00000000000110111), (8, 45, 1, 300)), ((17, 0b00000000001000011), (6, 32, 1, 300)),
    ((17, 0b00000000001001111), (6, 16, 2, 300)), ((17, 0b00000000001010011), (6, 31, 1, 300)),
    ((17, 0b00000000001010101), (8, 22, 3, 300)), ((17, 0b00000000001011011), (6, 46, 1, 300)),
    ((17, 0b00000000001011111), (8, 27, 2, 300)), ((17, 0b00000000001101001), (9, 62, 2, 300)),
    ((17, 0b00000000001101011), (6, 24, 2, 300)), ((17, 0b00000000001101111), (6, 14, 2, 300)),
    ((17, 0b00000000001111011), (6, 31, 1, 300)), ((17, 0b00000000010010011), (9, 32, 3, 300)),
    ((17, 0b00000000010100011), (6, 31, 1, 300)), ((17, 0b00000000010100111), (8, 37, 2, 300)),
    ((17, 0b00000000010111001), (6, 33, 2, 300)), ((17, 0b00000000010111011), (6, 47, 1, 300)),
    ((17, 0b00000000010111111), (6, 15, 2, 300)), ((17, 0b00000000011000011), (6, 32, 1, 300)),
    ((17, 0b00000000011011001), (8, 16, 4, 300)), ((17, 0b00000000011011011), (6, 38, 1, 300)),
    ((17, 0b00000000100000011), (6, 25, 2, 300)), ((17, 0b00000000100110011), (6, 20, 2, 300)),
    ((17, 0b00000000101001011), (6, 58, 1, 300)), ((17, 0b00000000101011011), (6, 24, 2, 300)),
    ((17, 0b00000000101100011), (6, 41, 1, 300)), ((17, 0b00000000101101111), (6, 51, 1, 300)),
    ((17, 0b00000000101111011), (6, 24, 2, 300)), ((17, 0b00000000101111111), (6, 15, 2, 300)),
    ((17, 0b00000000110100011), (6, 25, 2, 300)), ((17, 0b00000000110111011), (8, 57, 2, 300)),
    ((17, 0b00000000111100011), (6, 46, 1, 300)), ((17, 0b00000001010011011), (7, 26, 2, 300)),
    ((17, 0b00000001011100011), (9, 51, 2, 300)), ((17, 0b00000001011111011), (7, 64, 1, 300)),
    ((17, 0b00000001011111111), (5, 27, 1, 300)), ((17, 0b00000001101111011), (8, 26, 3, 300)),
    ((17, 0b00000010110000011), (6, 33, 2, 300)), ((17, 0b00000010111111011), (9, 44, 2, 300)),
    ((17, 0b00000101111111001), (10, 50, 2, 300)), ((17, 0b00000101111111011), (6, 37, 1, 300)),
    ((17, 0b00000111011111111), (6, 28, 1, 300)), ((17, 0b00001011111111001), (8, 32, 2, 300)),
    ((17, 0b00001011111111011), (6, 24, 1, 300)), ((17, 0b00001110011111111), (8, 39, 2, 300)),
    ((17, 0b00011001011111111), (6, 28, 1, 300)), ((17, 0b00100101111111111), (12, 70, 2, 300)),
    ((17, 0b00100110111111111), (11, 34, 3, 300)), ((17, 0b00101001111111011), (10, 58, 3, 300)),
    ((17, 0b00101010011111111), (12, 45, 2, 300)), ((17, 0b00111100111111111), (10, 36, 3, 300)),
    ((17, 0b00111111110110101), (11, 40, 2, 300)), ((17, 0b01101101111111111), (8, 32, 2, 300))]

set_option Elab.async false

set_option maxHeartbeats 0 in
theorem check_00000000000000101 :
    gameCheck (Rule30StripCertificateTable.wordOf 17 0b00000000000000101) 7 12 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000000001101 :
    gameCheck (Rule30StripCertificateTable.wordOf 17 0b00000000000001101) 6 13 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000000001111 :
    gameCheck (Rule30StripCertificateTable.wordOf 17 0b00000000000001111) 6 14 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000000010001 :
    gameCheck (Rule30StripCertificateTable.wordOf 17 0b00000000000010001) 8 24 3 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000000010011 :
    gameCheck (Rule30StripCertificateTable.wordOf 17 0b00000000000010011) 6 31 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000000011011 :
    gameCheck (Rule30StripCertificateTable.wordOf 17 0b00000000000011011) 6 30 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000000011101 :
    gameCheck (Rule30StripCertificateTable.wordOf 17 0b00000000000011101) 7 13 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000000011111 :
    gameCheck (Rule30StripCertificateTable.wordOf 17 0b00000000000011111) 8 24 3 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000000101001 :
    gameCheck (Rule30StripCertificateTable.wordOf 17 0b00000000000101001) 6 12 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000000101011 :
    gameCheck (Rule30StripCertificateTable.wordOf 17 0b00000000000101011) 6 33 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000000101111 :
    gameCheck (Rule30StripCertificateTable.wordOf 17 0b00000000000101111) 6 38 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000000110011 :
    gameCheck (Rule30StripCertificateTable.wordOf 17 0b00000000000110011) 6 31 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000000110111 :
    gameCheck (Rule30StripCertificateTable.wordOf 17 0b00000000000110111) 8 45 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000001000011 :
    gameCheck (Rule30StripCertificateTable.wordOf 17 0b00000000001000011) 6 32 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000001001111 :
    gameCheck (Rule30StripCertificateTable.wordOf 17 0b00000000001001111) 6 16 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000001010011 :
    gameCheck (Rule30StripCertificateTable.wordOf 17 0b00000000001010011) 6 31 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000001010101 :
    gameCheck (Rule30StripCertificateTable.wordOf 17 0b00000000001010101) 8 22 3 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000001011011 :
    gameCheck (Rule30StripCertificateTable.wordOf 17 0b00000000001011011) 6 46 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000001011111 :
    gameCheck (Rule30StripCertificateTable.wordOf 17 0b00000000001011111) 8 27 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000001101001 :
    gameCheck (Rule30StripCertificateTable.wordOf 17 0b00000000001101001) 9 62 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000001101011 :
    gameCheck (Rule30StripCertificateTable.wordOf 17 0b00000000001101011) 6 24 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000001101111 :
    gameCheck (Rule30StripCertificateTable.wordOf 17 0b00000000001101111) 6 14 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000001111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 17 0b00000000001111011) 6 31 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000010010011 :
    gameCheck (Rule30StripCertificateTable.wordOf 17 0b00000000010010011) 9 32 3 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000010100011 :
    gameCheck (Rule30StripCertificateTable.wordOf 17 0b00000000010100011) 6 31 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000010100111 :
    gameCheck (Rule30StripCertificateTable.wordOf 17 0b00000000010100111) 8 37 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000010111001 :
    gameCheck (Rule30StripCertificateTable.wordOf 17 0b00000000010111001) 6 33 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000010111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 17 0b00000000010111011) 6 47 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000010111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 17 0b00000000010111111) 6 15 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000011000011 :
    gameCheck (Rule30StripCertificateTable.wordOf 17 0b00000000011000011) 6 32 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000011011001 :
    gameCheck (Rule30StripCertificateTable.wordOf 17 0b00000000011011001) 8 16 4 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000011011011 :
    gameCheck (Rule30StripCertificateTable.wordOf 17 0b00000000011011011) 6 38 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000100000011 :
    gameCheck (Rule30StripCertificateTable.wordOf 17 0b00000000100000011) 6 25 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000100110011 :
    gameCheck (Rule30StripCertificateTable.wordOf 17 0b00000000100110011) 6 20 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000101001011 :
    gameCheck (Rule30StripCertificateTable.wordOf 17 0b00000000101001011) 6 58 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000101011011 :
    gameCheck (Rule30StripCertificateTable.wordOf 17 0b00000000101011011) 6 24 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000101100011 :
    gameCheck (Rule30StripCertificateTable.wordOf 17 0b00000000101100011) 6 41 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000101101111 :
    gameCheck (Rule30StripCertificateTable.wordOf 17 0b00000000101101111) 6 51 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000101111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 17 0b00000000101111011) 6 24 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000101111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 17 0b00000000101111111) 6 15 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000110100011 :
    gameCheck (Rule30StripCertificateTable.wordOf 17 0b00000000110100011) 6 25 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000110111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 17 0b00000000110111011) 8 57 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000111100011 :
    gameCheck (Rule30StripCertificateTable.wordOf 17 0b00000000111100011) 6 46 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000001010011011 :
    gameCheck (Rule30StripCertificateTable.wordOf 17 0b00000001010011011) 7 26 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000001011100011 :
    gameCheck (Rule30StripCertificateTable.wordOf 17 0b00000001011100011) 9 51 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000001011111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 17 0b00000001011111011) 7 64 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000001011111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 17 0b00000001011111111) 5 27 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000001101111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 17 0b00000001101111011) 8 26 3 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000010110000011 :
    gameCheck (Rule30StripCertificateTable.wordOf 17 0b00000010110000011) 6 33 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000010111111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 17 0b00000010111111011) 9 44 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000101111111001 :
    gameCheck (Rule30StripCertificateTable.wordOf 17 0b00000101111111001) 10 50 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000101111111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 17 0b00000101111111011) 6 37 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000111011111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 17 0b00000111011111111) 6 28 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00001011111111001 :
    gameCheck (Rule30StripCertificateTable.wordOf 17 0b00001011111111001) 8 32 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00001011111111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 17 0b00001011111111011) 6 24 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00001110011111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 17 0b00001110011111111) 8 39 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00011001011111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 17 0b00011001011111111) 6 28 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00100101111111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 17 0b00100101111111111) 12 70 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00100110111111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 17 0b00100110111111111) 11 34 3 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00101001111111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 17 0b00101001111111011) 10 58 3 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00101010011111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 17 0b00101010011111111) 12 45 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00111100111111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 17 0b00111100111111111) 10 36 3 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00111111110110101 :
    gameCheck (Rule30StripCertificateTable.wordOf 17 0b00111111110110101) 11 40 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_01101101111111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 17 0b01101101111111111) 8 32 2 300 = true := by decide +kernel

theorem blocks17_check : ∀ e ∈ blocks17,
    gameCheck (Rule30StripCertificateTable.wordOf e.1.1 e.1.2) e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2 = true := by
  intro e he
  simp only [blocks17, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact check_00000000000000101
  · exact check_00000000000001101
  · exact check_00000000000001111
  · exact check_00000000000010001
  · exact check_00000000000010011
  · exact check_00000000000011011
  · exact check_00000000000011101
  · exact check_00000000000011111
  · exact check_00000000000101001
  · exact check_00000000000101011
  · exact check_00000000000101111
  · exact check_00000000000110011
  · exact check_00000000000110111
  · exact check_00000000001000011
  · exact check_00000000001001111
  · exact check_00000000001010011
  · exact check_00000000001010101
  · exact check_00000000001011011
  · exact check_00000000001011111
  · exact check_00000000001101001
  · exact check_00000000001101011
  · exact check_00000000001101111
  · exact check_00000000001111011
  · exact check_00000000010010011
  · exact check_00000000010100011
  · exact check_00000000010100111
  · exact check_00000000010111001
  · exact check_00000000010111011
  · exact check_00000000010111111
  · exact check_00000000011000011
  · exact check_00000000011011001
  · exact check_00000000011011011
  · exact check_00000000100000011
  · exact check_00000000100110011
  · exact check_00000000101001011
  · exact check_00000000101011011
  · exact check_00000000101100011
  · exact check_00000000101101111
  · exact check_00000000101111011
  · exact check_00000000101111111
  · exact check_00000000110100011
  · exact check_00000000110111011
  · exact check_00000000111100011
  · exact check_00000001010011011
  · exact check_00000001011100011
  · exact check_00000001011111011
  · exact check_00000001011111111
  · exact check_00000001101111011
  · exact check_00000010110000011
  · exact check_00000010111111011
  · exact check_00000101111111001
  · exact check_00000101111111011
  · exact check_00000111011111111
  · exact check_00001011111111001
  · exact check_00001011111111011
  · exact check_00001110011111111
  · exact check_00011001011111111
  · exact check_00100101111111111
  · exact check_00100110111111111
  · exact check_00101001111111011
  · exact check_00101010011111111
  · exact check_00111100111111111
  · exact check_00111111110110101
  · exact check_01101101111111111

/-- The blocks of period 17 that the game excludes and the kit does not, and that `WallSets` excludes, each as its least
rotation `wordOf 17 bits`. -/
def wallBlocks17 : List Nat := [
    0b00000010111111111, 0b00000100111111111, 0b00000101111111111, 0b00000110111111111, 0b00000111111111011,
    0b00001010111111111, 0b00001011111111111, 0b00001110111111111, 0b00001111111111011, 0b00010011111111111,
    0b00010110111111111, 0b00010111111111011, 0b00010111111111111, 0b00011000111111111, 0b00011001111111111,
    0b00011010111111111, 0b00011011111111111, 0b00011101111111111, 0b00011111111111011, 0b00101011111111111,
    0b00101110111111111, 0b00101111111111011, 0b00101111111111111, 0b00111011111111111, 0b00111110111111111,
    0b00111111111111011, 0b00111111111111101, 0b01011011111111111, 0b01011110111111111, 0b01011111111111011,
    0b01011111111111111, 0b01101110111111111, 0b01101111111111111, 0b01110111111111111, 0b01111101111111111]

theorem wallBlocks17_all : wallBlocks17.all (fun bits => wallSet (Rule30StripCertificateTable.wordOf 17 bits)) = true := by
  decide +kernel

/-- **The blocks of `WallSets`**: for each entry of `wallBlocks17`, the center column does not repeat the block from any
time `T` on. -/
theorem center_not_wallBlocks17 (bits : Nat) (hb : bits ∈ wallBlocks17) (T : Nat)
    (hcol : ∀ t : Nat, T ≤ t → Rule30Prize.center t = cyc (Rule30StripCertificateTable.wordOf 17 bits) (t - T)) :
    False :=
  center_wall_set_block T _ (List.all_eq_true.1 wallBlocks17_all bits hb) hcol

/-- **The 64 blocks**: for each entry of `blocks17`, the center column is not, from any time `T` on, the block
`wordOf 17 bits`, read from any phase. -/
theorem center_not_blocks17 (e : (Nat × Nat) × (Nat × Nat × Nat × Nat)) (he : e ∈ blocks17) (T shift : Nat)
    (h : ∀ t : Nat, T ≤ t → Rule30Prize.center t =
      (Rule30StripCertificateTable.wordOf e.1.1 e.1.2).getD ((t + shift) % e.1.1) false) : False :=
  center_not_bitGame _ _ _ _ _ (blocks17_check e he) T shift fun t ht => by
    rw [h t ht, Rule30StripCertificateTable.wordOf_length]

/-- The same in the kit's form: none of the 64 blocks is an `EventuallyWord` of the center column. -/
theorem not_eventually_blocks17 (e : (Nat × Nat) × (Nat × Nat × Nat × Nat)) (he : e ∈ blocks17) :
    ¬ Rule30StripCertificates.EventuallyWord (Rule30StripCertificateTable.wordOf e.1.1 e.1.2) :=
  bitGame_not_eventuallyWord _ _ _ _ _ (blocks17_check e he)

end Rule30Open
