module

public import Rule30Open.Columns.BitGame

/-!
# The game decided in the kernel excludes 97 more blocks of period 21 that need 7 to 8 cells

[BitGame](BitGame.md) decides the finite game in the kernel from the block alone (`gameCheck`), and `bitGame_column`
turns a passing check into an exclusion. Here the check runs on the 97 blocks of period 21 that the game excludes at a
width of 7 to 8 and that neither the kit nor [WallSets](WallSets.md) excludes.

* `blocks21Mid`: the blocks, each as its least rotation, with the parameters of `gameCheck`; `blocks21Mid_check`: every
  check passes.
* `center_not_blocks21Mid`, `not_eventually_blocks21Mid`: the center column of the single cell does not eventually repeat
  any of them, in any rotation, and in the kit's form `EventuallyWord`.

The natural-language argument is `BitBlocks21Mid.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

open Ruliology.CellularAutomata BitGame

/-- The blocks of period 21 that the game excludes at a width of 7 to 8 and that the kit and `WallSets` do not
exclude, each as its least rotation `wordOf 21 bits`, with the width `K`, the steps `D`, the rounds and the search fuel
of `gameCheck`, from `computations/bit_game.py`. -/
def blocks21Mid : List ((Nat × Nat) × (Nat × Nat × Nat × Nat)) := [
    ((21, 0b000000000000000000101), (7, 12, 1, 300)), ((21, 0b000000000000000001001), (8, 61, 0, 300)),
    ((21, 0b000000000000000010001), (8, 24, 1, 300)), ((21, 0b000000000000000011101), (7, 13, 1, 300)),
    ((21, 0b000000000000000011111), (8, 24, 1, 300)), ((21, 0b000000000000000100011), (8, 64, 0, 300)),
    ((21, 0b000000000000000101101), (8, 20, 2, 300)), ((21, 0b000000000000000110111), (8, 57, 0, 300)),
    ((21, 0b000000000000000111001), (8, 58, 1, 300)), ((21, 0b000000000000000111111), (8, 60, 0, 300)),
    ((21, 0b000000000000001010101), (8, 22, 1, 300)), ((21, 0b000000000000001011111), (8, 24, 1, 300)),
    ((21, 0b000000000000001100101), (8, 57, 1, 300)), ((21, 0b000000000000001101001), (8, 62, 1, 300)),
    ((21, 0b000000000000001110111), (8, 58, 1, 300)), ((21, 0b000000000000010000011), (8, 56, 0, 300)),
    ((21, 0b000000000000010010011), (8, 47, 1, 300)), ((21, 0b000000000000010100111), (8, 56, 0, 300)),
    ((21, 0b000000000000011011001), (8, 16, 1, 300)), ((21, 0b000000000000011101011), (8, 49, 1, 300)),
    ((21, 0b000000000000011110011), (8, 44, 1, 300)), ((21, 0b000000000000100000001), (8, 30, 1, 300)),
    ((21, 0b000000000000100101011), (8, 49, 1, 300)), ((21, 0b000000000000101110101), (8, 25, 1, 300)),
    ((21, 0b000000000000110101111), (8, 64, 0, 300)), ((21, 0b000000000000110110101), (8, 25, 1, 300)),
    ((21, 0b000000000000111001011), (8, 74, 0, 300)), ((21, 0b000000000000111010011), (8, 48, 0, 300)),
    ((21, 0b000000000001011100111), (8, 21, 1, 300)), ((21, 0b000000000001101111001), (8, 58, 2, 300)),
    ((21, 0b000000000010000000001), (8, 48, 1, 300)), ((21, 0b000000000010101111111), (8, 23, 1, 300)),
    ((21, 0b000000000010111001111), (8, 26, 1, 300)), ((21, 0b000000000010111110101), (7, 20, 2, 300)),
    ((21, 0b000000000011101000011), (8, 35, 1, 300)), ((21, 0b000000000101001111111), (8, 22, 1, 300)),
    ((21, 0b000000001011110110011), (7, 31, 1, 300)), ((21, 0b000000001011111011011), (8, 37, 1, 300)),
    ((21, 0b000000001011111111001), (7, 30, 1, 300)), ((21, 0b000000001101110000011), (8, 44, 1, 300)),
    ((21, 0b000000010100111111011), (7, 29, 1, 300)), ((21, 0b000000010111001111011), (8, 44, 1, 300)),
    ((21, 0b000000010111111101111), (7, 16, 1, 300)), ((21, 0b000000010111111111001), (7, 37, 1, 300)),
    ((21, 0b000000011011111111011), (7, 29, 1, 300)), ((21, 0b000000101001111111011), (7, 38, 1, 300)),
    ((21, 0b000000101111110110011), (8, 52, 1, 300)), ((21, 0b000000101111111110101), (7, 39, 1, 300)),
    ((21, 0b000000110111111111011), (8, 28, 1, 300)), ((21, 0b000001011111111111001), (8, 29, 1, 300)),
    ((21, 0b000010011111111111111), (7, 30, 1, 300)), ((21, 0b000010100111111111001), (8, 43, 1, 300)),
    ((21, 0b000010111111111111001), (7, 36, 1, 300)), ((21, 0b000011011111111111011), (8, 33, 1, 300)),
    ((21, 0b000011100111111111111), (7, 53, 1, 300)), ((21, 0b000011111111111111101), (7, 32, 1, 300)),
    ((21, 0b000110111111111111001), (8, 40, 1, 300)), ((21, 0b000110111111111111011), (8, 37, 1, 300)),
    ((21, 0b000111001111111111111), (7, 47, 1, 300)), ((21, 0b000111111111111101101), (8, 46, 1, 300)),
    ((21, 0b000111111111111110101), (8, 54, 1, 300)), ((21, 0b000111111111111111101), (7, 32, 0, 300)),
    ((21, 0b001001010011111111111), (8, 49, 2, 300)), ((21, 0b001001011111111111111), (7, 27, 1, 300)),
    ((21, 0b001001101111111111111), (8, 36, 1, 300)), ((21, 0b001001111111111111011), (7, 28, 0, 300)),
    ((21, 0b001001111111111111101), (8, 45, 1, 300)), ((21, 0b001001111111111111111), (7, 32, 0, 300)),
    ((21, 0b001010011111111111011), (7, 30, 1, 300)), ((21, 0b001010100111111111111), (7, 44, 1, 300)),
    ((21, 0b001011011111111111111), (7, 24, 1, 300)), ((21, 0b001011111111111111101), (7, 49, 0, 300)),
    ((21, 0b001100111111111111111), (7, 58, 0, 300)), ((21, 0b001101001111111111111), (8, 92, 0, 300)),
    ((21, 0b001101111111111111011), (7, 28, 0, 300)), ((21, 0b001101111111111111101), (7, 49, 0, 300)),
    ((21, 0b001101111111111111111), (7, 39, 0, 300)), ((21, 0b001110011111111111101), (8, 30, 2, 300)),
    ((21, 0b001110111111111111101), (7, 25, 0, 300)), ((21, 0b001111001111111111111), (7, 27, 1, 300)),
    ((21, 0b001111011111111111111), (7, 23, 1, 300)), ((21, 0b001111101111111111101), (7, 25, 0, 300)),
    ((21, 0b001111110011111111111), (7, 30, 1, 300)), ((21, 0b001111110100111111111), (7, 29, 1, 300)),
    ((21, 0b001111111011111111101), (7, 25, 0, 300)), ((21, 0b001111111100111111111), (8, 33, 1, 300)),
    ((21, 0b001111111111011011011), (8, 77, 0, 300)), ((21, 0b001111111111110101011), (8, 44, 2, 300)),
    ((21, 0b001111111111110110101), (7, 29, 1, 300)), ((21, 0b001111111111111010111), (7, 32, 1, 300)),
    ((21, 0b001111111111111011101), (7, 31, 1, 300)), ((21, 0b001111111111111110101), (7, 49, 0, 300)),
    ((21, 0b001111111111111110111), (7, 27, 0, 300)), ((21, 0b010101111111111111011), (7, 49, 0, 300)),
    ((21, 0b010101111111111111111), (7, 39, 0, 300)), ((21, 0b011011011111111111111), (7, 27, 1, 300)),
    ((21, 0b011110111111111111111), (7, 30, 0, 300))]

set_option Elab.async false

set_option maxHeartbeats 0 in
theorem check_000000000000000000101 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000000000000101) 7 12 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000000000001001 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000000000001001) 8 61 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000000000010001 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000000000010001) 8 24 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000000000011101 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000000000011101) 7 13 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000000000011111 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000000000011111) 8 24 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000000000100011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000000000100011) 8 64 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000000000101101 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000000000101101) 8 20 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000000000110111 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000000000110111) 8 57 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000000000111001 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000000000111001) 8 58 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000000000111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000000000111111) 8 60 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000000001010101 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000000001010101) 8 22 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000000001011111 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000000001011111) 8 24 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000000001100101 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000000001100101) 8 57 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000000001101001 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000000001101001) 8 62 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000000001110111 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000000001110111) 8 58 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000000010000011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000000010000011) 8 56 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000000010010011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000000010010011) 8 47 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000000010100111 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000000010100111) 8 56 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000000011011001 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000000011011001) 8 16 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000000011101011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000000011101011) 8 49 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000000011110011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000000011110011) 8 44 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000000100000001 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000000100000001) 8 30 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000000100101011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000000100101011) 8 49 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000000101110101 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000000101110101) 8 25 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000000110101111 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000000110101111) 8 64 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000000110110101 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000000110110101) 8 25 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000000111001011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000000111001011) 8 74 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000000111010011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000000111010011) 8 48 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000001011100111 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000001011100111) 8 21 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000001101111001 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000001101111001) 8 58 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000010000000001 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000010000000001) 8 48 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000010101111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000010101111111) 8 23 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000010111001111 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000010111001111) 8 26 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000010111110101 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000010111110101) 7 20 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000011101000011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000011101000011) 8 35 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000101001111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000101001111111) 8 22 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000001011110110011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000001011110110011) 7 31 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000001011111011011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000001011111011011) 8 37 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000001011111111001 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000001011111111001) 7 30 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000001101110000011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000001101110000011) 8 44 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000010100111111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000010100111111011) 7 29 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000010111001111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000010111001111011) 8 44 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000010111111101111 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000010111111101111) 7 16 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000010111111111001 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000010111111111001) 7 37 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000011011111111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000011011111111011) 7 29 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000101001111111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000101001111111011) 7 38 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000101111110110011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000101111110110011) 8 52 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000101111111110101 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000101111111110101) 7 39 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000110111111111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000110111111111011) 8 28 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000001011111111111001 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000001011111111111001) 8 29 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000010011111111111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000010011111111111111) 7 30 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000010100111111111001 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000010100111111111001) 8 43 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000010111111111111001 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000010111111111111001) 7 36 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000011011111111111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000011011111111111011) 8 33 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000011100111111111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000011100111111111111) 7 53 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000011111111111111101 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000011111111111111101) 7 32 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000110111111111111001 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000110111111111111001) 8 40 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000110111111111111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000110111111111111011) 8 37 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000111001111111111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000111001111111111111) 7 47 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000111111111111101101 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000111111111111101101) 8 46 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000111111111111110101 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000111111111111110101) 8 54 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000111111111111111101 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000111111111111111101) 7 32 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_001001010011111111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b001001010011111111111) 8 49 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_001001011111111111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b001001011111111111111) 7 27 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_001001101111111111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b001001101111111111111) 8 36 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_001001111111111111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b001001111111111111011) 7 28 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_001001111111111111101 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b001001111111111111101) 8 45 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_001001111111111111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b001001111111111111111) 7 32 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_001010011111111111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b001010011111111111011) 7 30 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_001010100111111111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b001010100111111111111) 7 44 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_001011011111111111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b001011011111111111111) 7 24 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_001011111111111111101 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b001011111111111111101) 7 49 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_001100111111111111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b001100111111111111111) 7 58 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_001101001111111111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b001101001111111111111) 8 92 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_001101111111111111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b001101111111111111011) 7 28 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_001101111111111111101 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b001101111111111111101) 7 49 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_001101111111111111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b001101111111111111111) 7 39 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_001110011111111111101 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b001110011111111111101) 8 30 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_001110111111111111101 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b001110111111111111101) 7 25 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_001111001111111111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b001111001111111111111) 7 27 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_001111011111111111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b001111011111111111111) 7 23 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_001111101111111111101 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b001111101111111111101) 7 25 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_001111110011111111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b001111110011111111111) 7 30 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_001111110100111111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b001111110100111111111) 7 29 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_001111111011111111101 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b001111111011111111101) 7 25 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_001111111100111111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b001111111100111111111) 8 33 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_001111111111011011011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b001111111111011011011) 8 77 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_001111111111110101011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b001111111111110101011) 8 44 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_001111111111110110101 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b001111111111110110101) 7 29 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_001111111111111010111 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b001111111111111010111) 7 32 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_001111111111111011101 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b001111111111111011101) 7 31 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_001111111111111110101 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b001111111111111110101) 7 49 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_001111111111111110111 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b001111111111111110111) 7 27 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_010101111111111111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b010101111111111111011) 7 49 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_010101111111111111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b010101111111111111111) 7 39 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_011011011111111111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b011011011111111111111) 7 27 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_011110111111111111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b011110111111111111111) 7 30 0 300 = true := by decide +kernel

theorem blocks21Mid_check : ∀ e ∈ blocks21Mid,
    gameCheck (Rule30StripCertificateTable.wordOf e.1.1 e.1.2) e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2 = true := by
  intro e he
  simp only [blocks21Mid, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact check_000000000000000000101
  · exact check_000000000000000001001
  · exact check_000000000000000010001
  · exact check_000000000000000011101
  · exact check_000000000000000011111
  · exact check_000000000000000100011
  · exact check_000000000000000101101
  · exact check_000000000000000110111
  · exact check_000000000000000111001
  · exact check_000000000000000111111
  · exact check_000000000000001010101
  · exact check_000000000000001011111
  · exact check_000000000000001100101
  · exact check_000000000000001101001
  · exact check_000000000000001110111
  · exact check_000000000000010000011
  · exact check_000000000000010010011
  · exact check_000000000000010100111
  · exact check_000000000000011011001
  · exact check_000000000000011101011
  · exact check_000000000000011110011
  · exact check_000000000000100000001
  · exact check_000000000000100101011
  · exact check_000000000000101110101
  · exact check_000000000000110101111
  · exact check_000000000000110110101
  · exact check_000000000000111001011
  · exact check_000000000000111010011
  · exact check_000000000001011100111
  · exact check_000000000001101111001
  · exact check_000000000010000000001
  · exact check_000000000010101111111
  · exact check_000000000010111001111
  · exact check_000000000010111110101
  · exact check_000000000011101000011
  · exact check_000000000101001111111
  · exact check_000000001011110110011
  · exact check_000000001011111011011
  · exact check_000000001011111111001
  · exact check_000000001101110000011
  · exact check_000000010100111111011
  · exact check_000000010111001111011
  · exact check_000000010111111101111
  · exact check_000000010111111111001
  · exact check_000000011011111111011
  · exact check_000000101001111111011
  · exact check_000000101111110110011
  · exact check_000000101111111110101
  · exact check_000000110111111111011
  · exact check_000001011111111111001
  · exact check_000010011111111111111
  · exact check_000010100111111111001
  · exact check_000010111111111111001
  · exact check_000011011111111111011
  · exact check_000011100111111111111
  · exact check_000011111111111111101
  · exact check_000110111111111111001
  · exact check_000110111111111111011
  · exact check_000111001111111111111
  · exact check_000111111111111101101
  · exact check_000111111111111110101
  · exact check_000111111111111111101
  · exact check_001001010011111111111
  · exact check_001001011111111111111
  · exact check_001001101111111111111
  · exact check_001001111111111111011
  · exact check_001001111111111111101
  · exact check_001001111111111111111
  · exact check_001010011111111111011
  · exact check_001010100111111111111
  · exact check_001011011111111111111
  · exact check_001011111111111111101
  · exact check_001100111111111111111
  · exact check_001101001111111111111
  · exact check_001101111111111111011
  · exact check_001101111111111111101
  · exact check_001101111111111111111
  · exact check_001110011111111111101
  · exact check_001110111111111111101
  · exact check_001111001111111111111
  · exact check_001111011111111111111
  · exact check_001111101111111111101
  · exact check_001111110011111111111
  · exact check_001111110100111111111
  · exact check_001111111011111111101
  · exact check_001111111100111111111
  · exact check_001111111111011011011
  · exact check_001111111111110101011
  · exact check_001111111111110110101
  · exact check_001111111111111010111
  · exact check_001111111111111011101
  · exact check_001111111111111110101
  · exact check_001111111111111110111
  · exact check_010101111111111111011
  · exact check_010101111111111111111
  · exact check_011011011111111111111
  · exact check_011110111111111111111

/-- **The 97 blocks**: for each entry of `blocks21Mid`, the center column is not, from any time `T` on, the block
`wordOf 21 bits`, read from any phase. -/
theorem center_not_blocks21Mid (e : (Nat × Nat) × (Nat × Nat × Nat × Nat)) (he : e ∈ blocks21Mid) (T shift : Nat)
    (h : ∀ t : Nat, T ≤ t → Rule30Prize.center t =
      (Rule30StripCertificateTable.wordOf e.1.1 e.1.2).getD ((t + shift) % e.1.1) false) : False :=
  center_not_bitGame _ _ _ _ _ (blocks21Mid_check e he) T shift fun t ht => by
    rw [h t ht, Rule30StripCertificateTable.wordOf_length]

/-- The same in the kit's form: none of the 97 blocks is an `EventuallyWord` of the center column. -/
theorem not_eventually_blocks21Mid (e : (Nat × Nat) × (Nat × Nat × Nat × Nat)) (he : e ∈ blocks21Mid) :
    ¬ Rule30StripCertificates.EventuallyWord (Rule30StripCertificateTable.wordOf e.1.1 e.1.2) :=
  bitGame_not_eventuallyWord _ _ _ _ _ (blocks21Mid_check e he)

end Rule30Open
