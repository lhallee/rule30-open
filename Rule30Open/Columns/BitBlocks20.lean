module

public import Rule30Open.Columns.BitGame
public import Rule30Open.Columns.WallSets

/-!
# The game decided in the kernel and the window-set check exclude 160 more blocks of period 20

[BitGame](BitGame.md) decides the finite game in the kernel from the block alone (`gameCheck`), and `bitGame_column`
turns a passing check into an exclusion. Here the check runs on the 79 blocks of period 20 that the game excludes at a
width of 5 or 6 and that neither the kit nor [WallSets](WallSets.md) excludes.

* `blocks20`: the blocks, each as its least rotation, with the parameters of `gameCheck`; `blocks20_check`: every check
  passes.
* `center_not_blocks20`, `not_eventually_blocks20`: the center column of the single cell does not eventually repeat any
  of them, in any rotation, and in the kit's form `EventuallyWord`.
* `wallBlocks20`, `center_not_wallBlocks20`: the 81 blocks of period 20 that the game excludes beyond the kit and that
  pass `WallSets.wallSet`, so `center_wall_set_block` excludes them.

The natural-language argument is `BitBlocks20.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

open Ruliology.CellularAutomata BitGame

/-- The blocks of period 20 that the game excludes at a width of 5 or 6 and that the kit and `WallSets` do not
exclude, each as its least rotation `wordOf 20 bits`, with the width `K`, the steps `D`, the rounds and the search fuel
of `gameCheck`, from `computations/bit_game.py`. -/
def blocks20 : List ((Nat × Nat) × (Nat × Nat × Nat × Nat)) := [
    ((20, 0b00000000000000001111), (6, 14, 1, 300)), ((20, 0b00000000000000010011), (6, 34, 0, 300)),
    ((20, 0b00000000000000011011), (6, 33, 0, 300)), ((20, 0b00000000000000101001), (6, 12, 1, 300)),
    ((20, 0b00000000000000101111), (6, 41, 0, 300)), ((20, 0b00000000000000110011), (6, 34, 0, 300)),
    ((20, 0b00000000000001000011), (6, 34, 0, 300)), ((20, 0b00000000000001001111), (6, 16, 1, 300)),
    ((20, 0b00000000000001010011), (6, 33, 0, 300)), ((20, 0b00000000000001011011), (6, 36, 0, 300)),
    ((20, 0b00000000000001101011), (6, 36, 0, 300)), ((20, 0b00000000000001101111), (6, 14, 1, 300)),
    ((20, 0b00000000000001111011), (6, 34, 0, 300)), ((20, 0b00000000000010100011), (6, 34, 0, 300)),
    ((20, 0b00000000000010111001), (6, 38, 0, 300)), ((20, 0b00000000000010111011), (6, 36, 0, 300)),
    ((20, 0b00000000000010111111), (6, 15, 1, 300)), ((20, 0b00000000000011000011), (6, 34, 0, 300)),
    ((20, 0b00000000000011011011), (6, 34, 0, 300)), ((20, 0b00000000000100000011), (6, 34, 0, 300)),
    ((20, 0b00000000000100110011), (6, 34, 0, 300)), ((20, 0b00000000000101001011), (6, 36, 0, 300)),
    ((20, 0b00000000000101011011), (6, 36, 0, 300)), ((20, 0b00000000000101100011), (6, 34, 0, 300)),
    ((20, 0b00000000000101101111), (6, 44, 0, 300)), ((20, 0b00000000000101110011), (6, 33, 0, 300)),
    ((20, 0b00000000000101111011), (6, 34, 0, 300)), ((20, 0b00000000000101111111), (6, 15, 1, 300)),
    ((20, 0b00000000000110100011), (6, 34, 0, 300)), ((20, 0b00000000000110111011), (6, 36, 0, 300)),
    ((20, 0b00000000000110111111), (6, 39, 0, 300)), ((20, 0b00000000000111100011), (6, 34, 0, 300)),
    ((20, 0b00000000001010000011), (6, 35, 0, 300)), ((20, 0b00000000001010011011), (6, 38, 0, 300)),
    ((20, 0b00000000001010011111), (6, 14, 1, 300)), ((20, 0b00000000001011100011), (6, 34, 0, 300)),
    ((20, 0b00000000001011111001), (6, 58, 0, 300)), ((20, 0b00000000001011111011), (6, 38, 0, 300)),
    ((20, 0b00000000001011111111), (6, 37, 0, 300)), ((20, 0b00000000001100000011), (6, 35, 0, 300)),
    ((20, 0b00000000001101100011), (6, 35, 0, 300)), ((20, 0b00000000001101111011), (6, 38, 0, 300)),
    ((20, 0b00000000010000000011), (6, 35, 0, 300)), ((20, 0b00000000010000001111), (6, 14, 1, 300)),
    ((20, 0b00000000010011000011), (6, 35, 0, 300)), ((20, 0b00000000010100100011), (6, 35, 0, 300)),
    ((20, 0b00000000010100111011), (6, 25, 1, 300)), ((20, 0b00000000010100111111), (6, 38, 0, 300)),
    ((20, 0b00000000010101100011), (6, 35, 0, 300)), ((20, 0b00000000010110000011), (6, 34, 0, 300)),
    ((20, 0b00000000010110110011), (6, 35, 0, 300)), ((20, 0b00000000010111001011), (6, 48, 0, 300)),
    ((20, 0b00000000010111011011), (6, 54, 0, 300)), ((20, 0b00000000010111100011), (6, 34, 0, 300)),
    ((20, 0b00000000010111101111), (6, 48, 0, 300)), ((20, 0b00000000010111110011), (6, 34, 0, 300)),
    ((20, 0b00000000010111111011), (6, 36, 0, 300)), ((20, 0b00000000011010000011), (6, 35, 0, 300)),
    ((20, 0b00000000011011100011), (6, 35, 0, 300)), ((20, 0b00000000011011111011), (6, 38, 0, 300)),
    ((20, 0b00000000011011111111), (6, 31, 0, 300)), ((20, 0b00000000011110000011), (6, 34, 0, 300)),
    ((20, 0b00000000101001100011), (6, 46, 0, 300)), ((20, 0b00000000101001111011), (6, 28, 1, 300)),
    ((20, 0b00000000101011111111), (5, 30, 0, 300)), ((20, 0b00000000101110000011), (6, 43, 0, 300)),
    ((20, 0b00000000101111100011), (6, 23, 1, 300)), ((20, 0b00000000101111111011), (6, 53, 0, 300)),
    ((20, 0b00000000110110000011), (6, 21, 1, 300)), ((20, 0b00000000110111100011), (6, 27, 1, 300)),
    ((20, 0b00000000110111111011), (6, 23, 1, 300)), ((20, 0b00000000111011111111), (6, 31, 0, 300)),
    ((20, 0b00000001011000001111), (6, 36, 1, 300)), ((20, 0b00000001011111101111), (6, 15, 1, 300)),
    ((20, 0b00000001011111111011), (6, 26, 0, 300)), ((20, 0b00000010111111100011), (6, 38, 0, 300)),
    ((20, 0b00000101111111100011), (6, 30, 0, 300)), ((20, 0b00000110001011111111), (6, 30, 0, 300)),
    ((20, 0b00001111101011111111), (5, 30, 0, 300))]

set_option Elab.async false

set_option maxHeartbeats 0 in
theorem check_00000000000000001111 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000000000001111) 6 14 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000000000010011 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000000000010011) 6 34 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000000000011011 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000000000011011) 6 33 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000000000101001 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000000000101001) 6 12 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000000000101111 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000000000101111) 6 41 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000000000110011 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000000000110011) 6 34 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000000001000011 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000000001000011) 6 34 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000000001001111 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000000001001111) 6 16 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000000001010011 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000000001010011) 6 33 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000000001011011 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000000001011011) 6 36 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000000001101011 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000000001101011) 6 36 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000000001101111 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000000001101111) 6 14 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000000001111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000000001111011) 6 34 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000000010100011 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000000010100011) 6 34 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000000010111001 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000000010111001) 6 38 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000000010111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000000010111011) 6 36 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000000010111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000000010111111) 6 15 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000000011000011 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000000011000011) 6 34 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000000011011011 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000000011011011) 6 34 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000000100000011 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000000100000011) 6 34 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000000100110011 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000000100110011) 6 34 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000000101001011 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000000101001011) 6 36 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000000101011011 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000000101011011) 6 36 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000000101100011 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000000101100011) 6 34 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000000101101111 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000000101101111) 6 44 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000000101110011 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000000101110011) 6 33 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000000101111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000000101111011) 6 34 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000000101111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000000101111111) 6 15 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000000110100011 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000000110100011) 6 34 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000000110111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000000110111011) 6 36 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000000110111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000000110111111) 6 39 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000000111100011 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000000111100011) 6 34 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000001010000011 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000001010000011) 6 35 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000001010011011 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000001010011011) 6 38 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000001010011111 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000001010011111) 6 14 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000001011100011 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000001011100011) 6 34 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000001011111001 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000001011111001) 6 58 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000001011111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000001011111011) 6 38 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000001011111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000001011111111) 6 37 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000001100000011 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000001100000011) 6 35 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000001101100011 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000001101100011) 6 35 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000001101111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000001101111011) 6 38 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000010000000011 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000010000000011) 6 35 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000010000001111 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000010000001111) 6 14 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000010011000011 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000010011000011) 6 35 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000010100100011 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000010100100011) 6 35 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000010100111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000010100111011) 6 25 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000010100111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000010100111111) 6 38 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000010101100011 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000010101100011) 6 35 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000010110000011 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000010110000011) 6 34 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000010110110011 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000010110110011) 6 35 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000010111001011 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000010111001011) 6 48 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000010111011011 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000010111011011) 6 54 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000010111100011 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000010111100011) 6 34 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000010111101111 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000010111101111) 6 48 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000010111110011 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000010111110011) 6 34 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000010111111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000010111111011) 6 36 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000011010000011 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000011010000011) 6 35 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000011011100011 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000011011100011) 6 35 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000011011111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000011011111011) 6 38 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000011011111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000011011111111) 6 31 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000011110000011 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000011110000011) 6 34 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000101001100011 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000101001100011) 6 46 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000101001111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000101001111011) 6 28 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000101011111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000101011111111) 5 30 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000101110000011 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000101110000011) 6 43 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000101111100011 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000101111100011) 6 23 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000101111111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000101111111011) 6 53 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000110110000011 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000110110000011) 6 21 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000110111100011 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000110111100011) 6 27 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000110111111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000110111111011) 6 23 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000111011111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000111011111111) 6 31 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000001011000001111 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000001011000001111) 6 36 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000001011111101111 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000001011111101111) 6 15 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000001011111111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000001011111111011) 6 26 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000010111111100011 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000010111111100011) 6 38 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000101111111100011 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000101111111100011) 6 30 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000110001011111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000110001011111111) 6 30 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00001111101011111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00001111101011111111) 5 30 0 300 = true := by decide +kernel

theorem blocks20_check : ∀ e ∈ blocks20,
    gameCheck (Rule30StripCertificateTable.wordOf e.1.1 e.1.2) e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2 = true := by
  intro e he
  simp only [blocks20, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl
  · exact check_00000000000000001111
  · exact check_00000000000000010011
  · exact check_00000000000000011011
  · exact check_00000000000000101001
  · exact check_00000000000000101111
  · exact check_00000000000000110011
  · exact check_00000000000001000011
  · exact check_00000000000001001111
  · exact check_00000000000001010011
  · exact check_00000000000001011011
  · exact check_00000000000001101011
  · exact check_00000000000001101111
  · exact check_00000000000001111011
  · exact check_00000000000010100011
  · exact check_00000000000010111001
  · exact check_00000000000010111011
  · exact check_00000000000010111111
  · exact check_00000000000011000011
  · exact check_00000000000011011011
  · exact check_00000000000100000011
  · exact check_00000000000100110011
  · exact check_00000000000101001011
  · exact check_00000000000101011011
  · exact check_00000000000101100011
  · exact check_00000000000101101111
  · exact check_00000000000101110011
  · exact check_00000000000101111011
  · exact check_00000000000101111111
  · exact check_00000000000110100011
  · exact check_00000000000110111011
  · exact check_00000000000110111111
  · exact check_00000000000111100011
  · exact check_00000000001010000011
  · exact check_00000000001010011011
  · exact check_00000000001010011111
  · exact check_00000000001011100011
  · exact check_00000000001011111001
  · exact check_00000000001011111011
  · exact check_00000000001011111111
  · exact check_00000000001100000011
  · exact check_00000000001101100011
  · exact check_00000000001101111011
  · exact check_00000000010000000011
  · exact check_00000000010000001111
  · exact check_00000000010011000011
  · exact check_00000000010100100011
  · exact check_00000000010100111011
  · exact check_00000000010100111111
  · exact check_00000000010101100011
  · exact check_00000000010110000011
  · exact check_00000000010110110011
  · exact check_00000000010111001011
  · exact check_00000000010111011011
  · exact check_00000000010111100011
  · exact check_00000000010111101111
  · exact check_00000000010111110011
  · exact check_00000000010111111011
  · exact check_00000000011010000011
  · exact check_00000000011011100011
  · exact check_00000000011011111011
  · exact check_00000000011011111111
  · exact check_00000000011110000011
  · exact check_00000000101001100011
  · exact check_00000000101001111011
  · exact check_00000000101011111111
  · exact check_00000000101110000011
  · exact check_00000000101111100011
  · exact check_00000000101111111011
  · exact check_00000000110110000011
  · exact check_00000000110111100011
  · exact check_00000000110111111011
  · exact check_00000000111011111111
  · exact check_00000001011000001111
  · exact check_00000001011111101111
  · exact check_00000001011111111011
  · exact check_00000010111111100011
  · exact check_00000101111111100011
  · exact check_00000110001011111111
  · exact check_00001111101011111111

/-- The blocks of period 20 that the game excludes and the kit does not, and that `WallSets` excludes, each as its least
rotation `wordOf 20 bits`. -/
def wallBlocks20 : List Nat := [
    0b00000000010111111111, 0b00000000101111111111, 0b00000000111111111011, 0b00000001001111111111,
    0b00000001011111111111, 0b00000001100111111111, 0b00000001101111111111, 0b00000001110111111111,
    0b00000001111111111011, 0b00000010101111111111, 0b00000010111111111011, 0b00000010111111111111,
    0b00000011101111111111, 0b00000011111111100011, 0b00000011111111111011, 0b00000100111111111111,
    0b00000101101111111111, 0b00000101111111111011, 0b00000101111111111111, 0b00000110000111111111,
    0b00000110001111111111, 0b00000110010111111111, 0b00000110011111111111, 0b00000110101111111111,
    0b00000110111111111111, 0b00000111011111111111, 0b00000111110111111111, 0b00000111111111100011,
    0b00000111111111111011, 0b00001010111111111111, 0b00001011101111111111, 0b00001011111111100011,
    0b00001011111111111011, 0b00001011111111111111, 0b00001110111111111011, 0b00001110111111111111,
    0b00001111101111111111, 0b00001111111111100011, 0b00001111111111111011, 0b00010011111111111111,
    0b00010110111111111111, 0b00010111101111111111, 0b00010111111111100011, 0b00010111111111111011,
    0b00010111111111111111, 0b00011000111111111111, 0b00011001011111111111, 0b00011001110111111111,
    0b00011001111111111111, 0b00011010111111111111, 0b00011011101111111111, 0b00011011111111111111,
    0b00011101111111111011, 0b00011101111111111111, 0b00011111011111111111, 0b00011111110111111111,
    0b00011111111111111011, 0b00101011111111111111, 0b00101110111111111111, 0b00101111101111111111,
    0b00101111111111111011, 0b00101111111111111111, 0b00111011111111111011, 0b00111011111111111111,
    0b00111110101111111111, 0b00111110111111111011, 0b00111110111111111111, 0b00111111101111111111,
    0b00111111111111111011, 0b00111111111111111101, 0b01011011111111111111, 0b01011110111111111111,
    0b01011111101111111111, 0b01011111111111111011, 0b01011111111111111111, 0b01101110111111111111,
    0b01101111101111111111, 0b01101111111111111111, 0b01110111111111111111, 0b01111101111111111111,
    0b01111111011111111111]

theorem wallBlocks20_all : wallBlocks20.all (fun bits => wallSet (Rule30StripCertificateTable.wordOf 20 bits)) = true := by
  decide +kernel

/-- **The blocks of `WallSets`**: for each entry of `wallBlocks20`, the center column does not repeat the block from any
time `T` on. -/
theorem center_not_wallBlocks20 (bits : Nat) (hb : bits ∈ wallBlocks20) (T : Nat)
    (hcol : ∀ t : Nat, T ≤ t → Rule30Prize.center t = cyc (Rule30StripCertificateTable.wordOf 20 bits) (t - T)) :
    False :=
  center_wall_set_block T _ (List.all_eq_true.1 wallBlocks20_all bits hb) hcol

/-- **The 79 blocks**: for each entry of `blocks20`, the center column is not, from any time `T` on, the block
`wordOf 20 bits`, read from any phase. -/
theorem center_not_blocks20 (e : (Nat × Nat) × (Nat × Nat × Nat × Nat)) (he : e ∈ blocks20) (T shift : Nat)
    (h : ∀ t : Nat, T ≤ t → Rule30Prize.center t =
      (Rule30StripCertificateTable.wordOf e.1.1 e.1.2).getD ((t + shift) % e.1.1) false) : False :=
  center_not_bitGame _ _ _ _ _ (blocks20_check e he) T shift fun t ht => by
    rw [h t ht, Rule30StripCertificateTable.wordOf_length]

/-- The same in the kit's form: none of the 79 blocks is an `EventuallyWord` of the center column. -/
theorem not_eventually_blocks20 (e : (Nat × Nat) × (Nat × Nat × Nat × Nat)) (he : e ∈ blocks20) :
    ¬ Rule30StripCertificates.EventuallyWord (Rule30StripCertificateTable.wordOf e.1.1 e.1.2) :=
  bitGame_not_eventuallyWord _ _ _ _ _ (blocks20_check e he)

end Rule30Open
