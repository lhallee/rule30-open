module

public import Rule30Open.Columns.BitGame
public import Rule30Open.Columns.WallSets

/-!
# The game decided in the kernel and the window-set check exclude 220 more blocks of period 21

[BitGame](BitGame.md) decides the finite game in the kernel from the block alone (`gameCheck`), and `bitGame_column`
turns a passing check into an exclusion. Here the check runs on the 109 blocks of period 21 that the game excludes at a
width of 5 to 6 and that neither the kit nor [WallSets](WallSets.md) excludes.

* `blocks21`: the blocks, each as its least rotation, with the parameters of `gameCheck`; `blocks21_check`: every
  check passes.
* `center_not_blocks21`, `not_eventually_blocks21`: the center column of the single cell does not eventually repeat
  any of them, in any rotation, and in the kit's form `EventuallyWord`.
* `wallBlocks21`, `center_not_wallBlocks21`: the 111 blocks of period 21 that the game excludes beyond the
  kit and that pass `WallSets.wallSet`, so `center_wall_set_block` excludes them.

The natural-language argument is `BitBlocks21.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

open Ruliology.CellularAutomata BitGame

/-- The blocks of period 21 that the game excludes at a width of 5 to 6 and that the kit and `WallSets` do not
exclude, each as its least rotation `wordOf 21 bits`, with the width `K`, the steps `D`, the rounds and the search fuel
of `gameCheck`, from `computations/bit_game.py`. -/
def blocks21 : List ((Nat × Nat) × (Nat × Nat × Nat × Nat)) := [
    ((21, 0b000000000000000001111), (6, 14, 1, 300)), ((21, 0b000000000000000010011), (6, 35, 0, 300)),
    ((21, 0b000000000000000011011), (6, 34, 0, 300)), ((21, 0b000000000000000101001), (6, 12, 1, 300)),
    ((21, 0b000000000000000101111), (6, 42, 0, 300)), ((21, 0b000000000000000110011), (6, 35, 0, 300)),
    ((21, 0b000000000000001000011), (6, 35, 0, 300)), ((21, 0b000000000000001001111), (6, 16, 1, 300)),
    ((21, 0b000000000000001010011), (6, 34, 0, 300)), ((21, 0b000000000000001011011), (6, 37, 0, 300)),
    ((21, 0b000000000000001101011), (6, 37, 0, 300)), ((21, 0b000000000000001101111), (6, 14, 1, 300)),
    ((21, 0b000000000000001111011), (6, 35, 0, 300)), ((21, 0b000000000000010100011), (6, 35, 0, 300)),
    ((21, 0b000000000000010111001), (6, 39, 0, 300)), ((21, 0b000000000000010111011), (6, 37, 0, 300)),
    ((21, 0b000000000000010111111), (6, 15, 1, 300)), ((21, 0b000000000000011000011), (6, 35, 0, 300)),
    ((21, 0b000000000000011011011), (6, 35, 0, 300)), ((21, 0b000000000000100000011), (6, 35, 0, 300)),
    ((21, 0b000000000000100110011), (6, 35, 0, 300)), ((21, 0b000000000000101001011), (6, 37, 0, 300)),
    ((21, 0b000000000000101011011), (6, 37, 0, 300)), ((21, 0b000000000000101100011), (6, 35, 0, 300)),
    ((21, 0b000000000000101101111), (6, 45, 0, 300)), ((21, 0b000000000000101110011), (6, 34, 0, 300)),
    ((21, 0b000000000000101111011), (6, 35, 0, 300)), ((21, 0b000000000000101111111), (6, 15, 1, 300)),
    ((21, 0b000000000000110100011), (6, 35, 0, 300)), ((21, 0b000000000000110111011), (6, 37, 0, 300)),
    ((21, 0b000000000000110111111), (6, 40, 0, 300)), ((21, 0b000000000000111100011), (6, 35, 0, 300)),
    ((21, 0b000000000001010000011), (6, 35, 0, 300)), ((21, 0b000000000001010011011), (6, 35, 0, 300)),
    ((21, 0b000000000001010011111), (6, 14, 1, 300)), ((21, 0b000000000001011100011), (6, 35, 0, 300)),
    ((21, 0b000000000001011111001), (6, 40, 0, 300)), ((21, 0b000000000001011111011), (6, 35, 0, 300)),
    ((21, 0b000000000001011111111), (5, 31, 0, 300)), ((21, 0b000000000001100000011), (6, 35, 0, 300)),
    ((21, 0b000000000001101100011), (6, 35, 0, 300)), ((21, 0b000000000001101111011), (6, 35, 0, 300)),
    ((21, 0b000000000010000000011), (6, 36, 0, 300)), ((21, 0b000000000010000001111), (6, 14, 1, 300)),
    ((21, 0b000000000010011000011), (6, 36, 0, 300)), ((21, 0b000000000010100100011), (6, 36, 0, 300)),
    ((21, 0b000000000010100111011), (6, 56, 0, 300)), ((21, 0b000000000010100111111), (6, 39, 0, 300)),
    ((21, 0b000000000010101100011), (6, 35, 0, 300)), ((21, 0b000000000010110000011), (6, 35, 0, 300)),
    ((21, 0b000000000010110110011), (6, 36, 0, 300)), ((21, 0b000000000010111001011), (6, 49, 0, 300)),
    ((21, 0b000000000010111011011), (6, 56, 0, 300)), ((21, 0b000000000010111100011), (6, 36, 0, 300)),
    ((21, 0b000000000010111101111), (6, 49, 0, 300)), ((21, 0b000000000010111110011), (6, 35, 0, 300)),
    ((21, 0b000000000010111111011), (6, 37, 0, 300)), ((21, 0b000000000011000000001), (6, 44, 0, 300)),
    ((21, 0b000000000011010000011), (6, 36, 0, 300)), ((21, 0b000000000011011100011), (6, 36, 0, 300)),
    ((21, 0b000000000011011111011), (6, 39, 0, 300)), ((21, 0b000000000011011111111), (6, 32, 0, 300)),
    ((21, 0b000000000011110000011), (6, 35, 0, 300)), ((21, 0b000000000101000000011), (6, 35, 0, 300)),
    ((21, 0b000000000101001100011), (6, 36, 0, 300)), ((21, 0b000000000101001111011), (6, 35, 0, 300)),
    ((21, 0b000000000101011111111), (6, 32, 0, 300)), ((21, 0b000000000101110000011), (6, 35, 0, 300)),
    ((21, 0b000000000101110011011), (6, 39, 0, 300)), ((21, 0b000000000101110011111), (6, 47, 0, 300)),
    ((21, 0b000000000101111100011), (6, 35, 0, 300)), ((21, 0b000000000101111111001), (6, 37, 1, 300)),
    ((21, 0b000000000101111111011), (6, 38, 0, 300)), ((21, 0b000000000110000000011), (6, 35, 0, 300)),
    ((21, 0b000000000110000001011), (6, 32, 0, 300)), ((21, 0b000000000110110000011), (6, 36, 0, 300)),
    ((21, 0b000000000110111100011), (6, 36, 0, 300)), ((21, 0b000000000110111111011), (6, 39, 0, 300)),
    ((21, 0b000000000111011111111), (6, 32, 0, 300)), ((21, 0b000000001000000110011), (6, 29, 1, 300)),
    ((21, 0b000000001001100000011), (6, 19, 1, 300)), ((21, 0b000000001010010000011), (6, 29, 1, 300)),
    ((21, 0b000000001010011100011), (6, 30, 1, 300)), ((21, 0b000000001010011111011), (6, 51, 0, 300)),
    ((21, 0b000000001010110000011), (6, 27, 1, 300)), ((21, 0b000000001011000000011), (6, 45, 0, 300)),
    ((21, 0b000000001011000001111), (6, 37, 1, 300)), ((21, 0b000000001011011000011), (6, 29, 1, 300)),
    ((21, 0b000000001011100100011), (6, 27, 1, 300)), ((21, 0b000000001011101100011), (6, 27, 1, 300)),
    ((21, 0b000000001011110000011), (6, 28, 1, 300)), ((21, 0b000000001011111001011), (6, 41, 1, 300)),
    ((21, 0b000000001011111100011), (6, 48, 0, 300)), ((21, 0b000000001011111101111), (6, 15, 2, 300)),
    ((21, 0b000000001011111110101), (6, 49, 1, 300)), ((21, 0b000000001011111111011), (6, 41, 0, 300)),
    ((21, 0b000000001101000000011), (6, 29, 1, 300)), ((21, 0b000000001101111100011), (6, 22, 1, 300)),
    ((21, 0b000000001101111111011), (6, 23, 1, 300)), ((21, 0b000000001111000000011), (6, 52, 0, 300)),
    ((21, 0b000000010111111100011), (6, 39, 0, 300)), ((21, 0b000000011000000101111), (6, 41, 0, 300)),
    ((21, 0b000000011000101111111), (6, 39, 0, 300)), ((21, 0b000000011001011111111), (6, 32, 0, 300)),
    ((21, 0b000000101111110000011), (6, 41, 0, 300)), ((21, 0b000000101111111100011), (6, 28, 0, 300)),
    ((21, 0b000000111011111111011), (6, 32, 0, 300)), ((21, 0b000001011111110000011), (6, 41, 0, 300)),
    ((21, 0b000001100001011111111), (6, 28, 0, 300))]

set_option Elab.async false

set_option maxHeartbeats 0 in
theorem check_000000000000000001111 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000000000001111) 6 14 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000000000010011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000000000010011) 6 35 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000000000011011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000000000011011) 6 34 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000000000101001 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000000000101001) 6 12 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000000000101111 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000000000101111) 6 42 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000000000110011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000000000110011) 6 35 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000000001000011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000000001000011) 6 35 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000000001001111 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000000001001111) 6 16 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000000001010011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000000001010011) 6 34 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000000001011011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000000001011011) 6 37 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000000001101011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000000001101011) 6 37 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000000001101111 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000000001101111) 6 14 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000000001111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000000001111011) 6 35 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000000010100011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000000010100011) 6 35 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000000010111001 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000000010111001) 6 39 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000000010111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000000010111011) 6 37 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000000010111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000000010111111) 6 15 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000000011000011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000000011000011) 6 35 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000000011011011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000000011011011) 6 35 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000000100000011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000000100000011) 6 35 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000000100110011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000000100110011) 6 35 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000000101001011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000000101001011) 6 37 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000000101011011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000000101011011) 6 37 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000000101100011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000000101100011) 6 35 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000000101101111 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000000101101111) 6 45 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000000101110011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000000101110011) 6 34 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000000101111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000000101111011) 6 35 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000000101111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000000101111111) 6 15 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000000110100011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000000110100011) 6 35 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000000110111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000000110111011) 6 37 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000000110111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000000110111111) 6 40 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000000111100011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000000111100011) 6 35 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000001010000011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000001010000011) 6 35 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000001010011011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000001010011011) 6 35 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000001010011111 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000001010011111) 6 14 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000001011100011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000001011100011) 6 35 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000001011111001 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000001011111001) 6 40 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000001011111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000001011111011) 6 35 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000001011111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000001011111111) 5 31 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000001100000011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000001100000011) 6 35 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000001101100011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000001101100011) 6 35 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000001101111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000001101111011) 6 35 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000010000000011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000010000000011) 6 36 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000010000001111 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000010000001111) 6 14 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000010011000011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000010011000011) 6 36 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000010100100011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000010100100011) 6 36 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000010100111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000010100111011) 6 56 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000010100111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000010100111111) 6 39 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000010101100011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000010101100011) 6 35 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000010110000011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000010110000011) 6 35 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000010110110011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000010110110011) 6 36 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000010111001011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000010111001011) 6 49 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000010111011011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000010111011011) 6 56 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000010111100011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000010111100011) 6 36 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000010111101111 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000010111101111) 6 49 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000010111110011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000010111110011) 6 35 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000010111111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000010111111011) 6 37 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000011000000001 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000011000000001) 6 44 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000011010000011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000011010000011) 6 36 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000011011100011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000011011100011) 6 36 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000011011111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000011011111011) 6 39 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000011011111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000011011111111) 6 32 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000011110000011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000011110000011) 6 35 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000101000000011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000101000000011) 6 35 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000101001100011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000101001100011) 6 36 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000101001111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000101001111011) 6 35 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000101011111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000101011111111) 6 32 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000101110000011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000101110000011) 6 35 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000101110011011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000101110011011) 6 39 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000101110011111 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000101110011111) 6 47 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000101111100011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000101111100011) 6 35 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000101111111001 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000101111111001) 6 37 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000101111111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000101111111011) 6 38 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000110000000011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000110000000011) 6 35 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000110000001011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000110000001011) 6 32 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000110110000011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000110110000011) 6 36 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000110111100011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000110111100011) 6 36 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000110111111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000110111111011) 6 39 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000111011111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000000111011111111) 6 32 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000001000000110011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000001000000110011) 6 29 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000001001100000011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000001001100000011) 6 19 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000001010010000011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000001010010000011) 6 29 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000001010011100011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000001010011100011) 6 30 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000001010011111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000001010011111011) 6 51 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000001010110000011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000001010110000011) 6 27 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000001011000000011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000001011000000011) 6 45 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000001011000001111 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000001011000001111) 6 37 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000001011011000011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000001011011000011) 6 29 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000001011100100011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000001011100100011) 6 27 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000001011101100011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000001011101100011) 6 27 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000001011110000011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000001011110000011) 6 28 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000001011111001011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000001011111001011) 6 41 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000001011111100011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000001011111100011) 6 48 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000001011111101111 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000001011111101111) 6 15 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000001011111110101 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000001011111110101) 6 49 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000001011111111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000001011111111011) 6 41 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000001101000000011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000001101000000011) 6 29 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000001101111100011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000001101111100011) 6 22 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000001101111111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000001101111111011) 6 23 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000001111000000011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000001111000000011) 6 52 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000010111111100011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000010111111100011) 6 39 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000011000000101111 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000011000000101111) 6 41 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000011000101111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000011000101111111) 6 39 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000011001011111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000011001011111111) 6 32 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000101111110000011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000101111110000011) 6 41 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000101111111100011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000101111111100011) 6 28 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000111011111111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000000111011111111011) 6 32 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000001011111110000011 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000001011111110000011) 6 41 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000001100001011111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 21 0b000001100001011111111) 6 28 0 300 = true := by decide +kernel

theorem blocks21_check : ∀ e ∈ blocks21,
    gameCheck (Rule30StripCertificateTable.wordOf e.1.1 e.1.2) e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2 = true := by
  intro e he
  simp only [blocks21, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact check_000000000000000001111
  · exact check_000000000000000010011
  · exact check_000000000000000011011
  · exact check_000000000000000101001
  · exact check_000000000000000101111
  · exact check_000000000000000110011
  · exact check_000000000000001000011
  · exact check_000000000000001001111
  · exact check_000000000000001010011
  · exact check_000000000000001011011
  · exact check_000000000000001101011
  · exact check_000000000000001101111
  · exact check_000000000000001111011
  · exact check_000000000000010100011
  · exact check_000000000000010111001
  · exact check_000000000000010111011
  · exact check_000000000000010111111
  · exact check_000000000000011000011
  · exact check_000000000000011011011
  · exact check_000000000000100000011
  · exact check_000000000000100110011
  · exact check_000000000000101001011
  · exact check_000000000000101011011
  · exact check_000000000000101100011
  · exact check_000000000000101101111
  · exact check_000000000000101110011
  · exact check_000000000000101111011
  · exact check_000000000000101111111
  · exact check_000000000000110100011
  · exact check_000000000000110111011
  · exact check_000000000000110111111
  · exact check_000000000000111100011
  · exact check_000000000001010000011
  · exact check_000000000001010011011
  · exact check_000000000001010011111
  · exact check_000000000001011100011
  · exact check_000000000001011111001
  · exact check_000000000001011111011
  · exact check_000000000001011111111
  · exact check_000000000001100000011
  · exact check_000000000001101100011
  · exact check_000000000001101111011
  · exact check_000000000010000000011
  · exact check_000000000010000001111
  · exact check_000000000010011000011
  · exact check_000000000010100100011
  · exact check_000000000010100111011
  · exact check_000000000010100111111
  · exact check_000000000010101100011
  · exact check_000000000010110000011
  · exact check_000000000010110110011
  · exact check_000000000010111001011
  · exact check_000000000010111011011
  · exact check_000000000010111100011
  · exact check_000000000010111101111
  · exact check_000000000010111110011
  · exact check_000000000010111111011
  · exact check_000000000011000000001
  · exact check_000000000011010000011
  · exact check_000000000011011100011
  · exact check_000000000011011111011
  · exact check_000000000011011111111
  · exact check_000000000011110000011
  · exact check_000000000101000000011
  · exact check_000000000101001100011
  · exact check_000000000101001111011
  · exact check_000000000101011111111
  · exact check_000000000101110000011
  · exact check_000000000101110011011
  · exact check_000000000101110011111
  · exact check_000000000101111100011
  · exact check_000000000101111111001
  · exact check_000000000101111111011
  · exact check_000000000110000000011
  · exact check_000000000110000001011
  · exact check_000000000110110000011
  · exact check_000000000110111100011
  · exact check_000000000110111111011
  · exact check_000000000111011111111
  · exact check_000000001000000110011
  · exact check_000000001001100000011
  · exact check_000000001010010000011
  · exact check_000000001010011100011
  · exact check_000000001010011111011
  · exact check_000000001010110000011
  · exact check_000000001011000000011
  · exact check_000000001011000001111
  · exact check_000000001011011000011
  · exact check_000000001011100100011
  · exact check_000000001011101100011
  · exact check_000000001011110000011
  · exact check_000000001011111001011
  · exact check_000000001011111100011
  · exact check_000000001011111101111
  · exact check_000000001011111110101
  · exact check_000000001011111111011
  · exact check_000000001101000000011
  · exact check_000000001101111100011
  · exact check_000000001101111111011
  · exact check_000000001111000000011
  · exact check_000000010111111100011
  · exact check_000000011000000101111
  · exact check_000000011000101111111
  · exact check_000000011001011111111
  · exact check_000000101111110000011
  · exact check_000000101111111100011
  · exact check_000000111011111111011
  · exact check_000001011111110000011
  · exact check_000001100001011111111

/-- The blocks of period 21 that the game excludes and the kit does not, and that `WallSets` excludes, each as its least
rotation `wordOf 21 bits`. -/
def wallBlocks21 : List Nat := [
    0b000000000010111111111, 0b000000000100111111111, 0b000000000101111111111, 0b000000000110111111111,
    0b000000000111111111011, 0b000000001010111111111, 0b000000001011111111111, 0b000000001110111111111,
    0b000000001111111111011, 0b000000010011111111111, 0b000000010110111111111, 0b000000010111111111011,
    0b000000010111111111111, 0b000000011000111111111, 0b000000011001111111111, 0b000000011010111111111,
    0b000000011011111111111, 0b000000011101111111111, 0b000000011111111100011, 0b000000011111111111011,
    0b000000101011111111111, 0b000000101110111111111, 0b000000101111111111011, 0b000000101111111111111,
    0b000000111011111111111, 0b000000111110111111111, 0b000000111111111100011, 0b000000111111111111011,
    0b000001001111111111111, 0b000001011011111111111, 0b000001011110111111111, 0b000001011111111100011,
    0b000001011111111111011, 0b000001011111111111111, 0b000001100000111111111, 0b000001100001111111111,
    0b000001100010111111111, 0b000001100011111111111, 0b000001100101111111111, 0b000001100111111111111,
    0b000001101011111111111, 0b000001101110111111111, 0b000001101111111111111, 0b000001110111111111011,
    0b000001110111111111111, 0b000001111101111111111, 0b000001111111111100011, 0b000001111111111111011,
    0b000010101111111111111, 0b000010111011111111111, 0b000010111110111111111, 0b000010111111111100011,
    0b000010111111111111011, 0b000010111111111111111, 0b000011101111111111011, 0b000011101111111111111,
    0b000011111010111111111, 0b000011111011111111111, 0b000011111110111111111, 0b000011111111111100011,
    0b000011111111111111011, 0b000100111111111111111, 0b000101101111111111111, 0b000101111011111111111,
    0b000101111110111111111, 0b000101111111111100011, 0b000101111111111111011, 0b000101111111111111111,
    0b000110001110111111111, 0b000110001111111111111, 0b000110010111111111111, 0b000110011101111111111,
    0b000110011111111111111, 0b000110101111111111111, 0b000110111011111111111, 0b000110111110111111111,
    0b000110111111111111111, 0b000111011111111111011, 0b000111011111111111111, 0b000111110111111111011,
    0b000111110111111111111, 0b000111111101111111111, 0b000111111111111111011, 0b001010111111111111111,
    0b001011101111111111111, 0b001011111011111111111, 0b001011111110111111111, 0b001011111111111111011,
    0b001011111111111111111, 0b001110111111111111011, 0b001110111111111111111, 0b001111101011111111111,
    0b001111101110111111111, 0b001111101111111111011, 0b001111101111111111111, 0b001111111011111111111,
    0b001111111111111111011, 0b001111111111111111101, 0b010110111111111111111, 0b010111101111111111111,
    0b010111111011111111111, 0b010111111110111111111, 0b010111111111111111011, 0b010111111111111111111,
    0b011011101111111111111, 0b011011111011111111111, 0b011011111110111111111, 0b011011111111111111111,
    0b011101111111111111111, 0b011111011111111111111, 0b011111110111111111111]

theorem wallBlocks21_all : wallBlocks21.all (fun bits => wallSet (Rule30StripCertificateTable.wordOf 21 bits)) = true := by
  decide +kernel

/-- **The blocks of `WallSets`**: for each entry of `wallBlocks21`, the center column does not repeat the block from any
time `T` on. -/
theorem center_not_wallBlocks21 (bits : Nat) (hb : bits ∈ wallBlocks21) (T : Nat)
    (hcol : ∀ t : Nat, T ≤ t → Rule30Prize.center t = cyc (Rule30StripCertificateTable.wordOf 21 bits) (t - T)) :
    False :=
  center_wall_set_block T _ (List.all_eq_true.1 wallBlocks21_all bits hb) hcol

/-- **The 109 blocks**: for each entry of `blocks21`, the center column is not, from any time `T` on, the block
`wordOf 21 bits`, read from any phase. -/
theorem center_not_blocks21 (e : (Nat × Nat) × (Nat × Nat × Nat × Nat)) (he : e ∈ blocks21) (T shift : Nat)
    (h : ∀ t : Nat, T ≤ t → Rule30Prize.center t =
      (Rule30StripCertificateTable.wordOf e.1.1 e.1.2).getD ((t + shift) % e.1.1) false) : False :=
  center_not_bitGame _ _ _ _ _ (blocks21_check e he) T shift fun t ht => by
    rw [h t ht, Rule30StripCertificateTable.wordOf_length]

/-- The same in the kit's form: none of the 109 blocks is an `EventuallyWord` of the center column. -/
theorem not_eventually_blocks21 (e : (Nat × Nat) × (Nat × Nat × Nat × Nat)) (he : e ∈ blocks21) :
    ¬ Rule30StripCertificates.EventuallyWord (Rule30StripCertificateTable.wordOf e.1.1 e.1.2) :=
  bitGame_not_eventuallyWord _ _ _ _ _ (blocks21_check e he)

end Rule30Open
