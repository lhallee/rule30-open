module

public import Rule30Open.Columns.BitGame
public import Rule30Open.Columns.WallSets

/-!
# The game decided in the kernel and the window-set check exclude 133 more blocks of period 19

[BitGame](BitGame.md) decides the finite game in the kernel from the block alone (`gameCheck`), and `bitGame_column`
turns a passing check into an exclusion. Here the check runs on the 66 blocks of period 19 that the game excludes at a
width of 5 or 6 and that neither the kit nor [WallSets](WallSets.md) excludes.

* `blocks19`: the blocks, each as its least rotation, with the parameters of `gameCheck`; `blocks19_check`: every check
  passes.
* `center_not_blocks19`, `not_eventually_blocks19`: the center column of the single cell does not eventually repeat any
  of them, in any rotation, and in the kit's form `EventuallyWord`.
* `wallBlocks19`, `center_not_wallBlocks19`: the 67 blocks of period 19 that the game excludes beyond the kit and that
  pass `WallSets.wallSet`, so `center_wall_set_block` excludes them.

The natural-language argument is `BitBlocks19.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

open Ruliology.CellularAutomata BitGame

/-- The blocks of period 19 that the game excludes at a width of 5 or 6 and that the kit and `WallSets` do not
exclude, each as its least rotation `wordOf 19 bits`, with the width `K`, the steps `D`, the rounds and the search fuel
of `gameCheck`, from `computations/bit_game.py`. -/
def blocks19 : List ((Nat × Nat) × (Nat × Nat × Nat × Nat)) := [
    ((19, 0b0000000000000001111), (6, 14, 1, 300)), ((19, 0b0000000000000010011), (6, 33, 0, 300)),
    ((19, 0b0000000000000011011), (6, 32, 0, 300)), ((19, 0b0000000000000101001), (6, 12, 1, 300)),
    ((19, 0b0000000000000101111), (6, 40, 0, 300)), ((19, 0b0000000000000110011), (6, 33, 0, 300)),
    ((19, 0b0000000000001000011), (6, 33, 0, 300)), ((19, 0b0000000000001001111), (6, 16, 1, 300)),
    ((19, 0b0000000000001010011), (6, 32, 0, 300)), ((19, 0b0000000000001011011), (6, 35, 0, 300)),
    ((19, 0b0000000000001101011), (6, 35, 0, 300)), ((19, 0b0000000000001101111), (6, 14, 1, 300)),
    ((19, 0b0000000000001111011), (6, 33, 0, 300)), ((19, 0b0000000000010100011), (6, 33, 0, 300)),
    ((19, 0b0000000000010111001), (6, 37, 0, 300)), ((19, 0b0000000000010111011), (6, 35, 0, 300)),
    ((19, 0b0000000000010111111), (6, 15, 1, 300)), ((19, 0b0000000000011000011), (6, 33, 0, 300)),
    ((19, 0b0000000000011011011), (6, 33, 0, 300)), ((19, 0b0000000000100000011), (6, 34, 0, 300)),
    ((19, 0b0000000000100110011), (6, 34, 0, 300)), ((19, 0b0000000000101001011), (6, 45, 0, 300)),
    ((19, 0b0000000000101011011), (6, 26, 1, 300)), ((19, 0b0000000000101100011), (6, 33, 0, 300)),
    ((19, 0b0000000000101101111), (6, 43, 0, 300)), ((19, 0b0000000000101110011), (6, 33, 0, 300)),
    ((19, 0b0000000000101111011), (6, 37, 0, 300)), ((19, 0b0000000000101111111), (6, 15, 1, 300)),
    ((19, 0b0000000000110100011), (6, 34, 0, 300)), ((19, 0b0000000000110111011), (6, 23, 1, 300)),
    ((19, 0b0000000000110111111), (6, 38, 0, 300)), ((19, 0b0000000000111100011), (6, 33, 0, 300)),
    ((19, 0b0000000001010000011), (6, 33, 0, 300)), ((19, 0b0000000001010011011), (6, 37, 0, 300)),
    ((19, 0b0000000001010011111), (6, 14, 1, 300)), ((19, 0b0000000001011100011), (6, 33, 0, 300)),
    ((19, 0b0000000001011111001), (6, 42, 1, 300)), ((19, 0b0000000001011111011), (6, 36, 0, 300)),
    ((19, 0b0000000001011111111), (5, 29, 0, 300)), ((19, 0b0000000001100000011), (6, 33, 0, 300)),
    ((19, 0b0000000001101100011), (6, 34, 0, 300)), ((19, 0b0000000001101111011), (6, 37, 0, 300)),
    ((19, 0b0000000010000000011), (6, 31, 1, 300)), ((19, 0b0000000010000001111), (6, 14, 1, 300)),
    ((19, 0b0000000010011000011), (6, 19, 1, 300)), ((19, 0b0000000010100100011), (6, 27, 1, 300)),
    ((19, 0b0000000010100111011), (6, 23, 1, 300)), ((19, 0b0000000010101100011), (6, 50, 0, 300)),
    ((19, 0b0000000010110000011), (6, 49, 0, 300)), ((19, 0b0000000010110110011), (6, 27, 1, 300)),
    ((19, 0b0000000010111011011), (6, 45, 1, 300)), ((19, 0b0000000010111100011), (6, 21, 1, 300)),
    ((19, 0b0000000010111111011), (6, 50, 0, 300)), ((19, 0b0000000011010000011), (6, 27, 1, 300)),
    ((19, 0b0000000011011100011), (6, 22, 1, 300)), ((19, 0b0000000011011111011), (6, 23, 1, 300)),
    ((19, 0b0000000011110000011), (6, 44, 0, 300)), ((19, 0b0000000101111111011), (6, 37, 0, 300)),
    ((19, 0b0000000110000001011), (6, 40, 0, 300)), ((19, 0b0000000111011111111), (6, 30, 0, 300)),
    ((19, 0b0000001011110000011), (6, 53, 0, 300)), ((19, 0b0000001011111111011), (6, 26, 0, 300)),
    ((19, 0b0000010111111100011), (6, 39, 0, 300)), ((19, 0b0000011000101111111), (6, 37, 0, 300)),
    ((19, 0b0000011001011111111), (6, 30, 0, 300)), ((19, 0b0000101111111100011), (6, 21, 0, 300))]

set_option Elab.async false

set_option maxHeartbeats 0 in
theorem check_0000000000000001111 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000000000001111) 6 14 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000000000010011 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000000000010011) 6 33 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000000000011011 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000000000011011) 6 32 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000000000101001 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000000000101001) 6 12 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000000000101111 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000000000101111) 6 40 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000000000110011 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000000000110011) 6 33 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000000001000011 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000000001000011) 6 33 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000000001001111 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000000001001111) 6 16 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000000001010011 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000000001010011) 6 32 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000000001011011 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000000001011011) 6 35 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000000001101011 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000000001101011) 6 35 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000000001101111 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000000001101111) 6 14 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000000001111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000000001111011) 6 33 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000000010100011 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000000010100011) 6 33 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000000010111001 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000000010111001) 6 37 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000000010111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000000010111011) 6 35 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000000010111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000000010111111) 6 15 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000000011000011 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000000011000011) 6 33 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000000011011011 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000000011011011) 6 33 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000000100000011 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000000100000011) 6 34 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000000100110011 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000000100110011) 6 34 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000000101001011 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000000101001011) 6 45 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000000101011011 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000000101011011) 6 26 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000000101100011 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000000101100011) 6 33 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000000101101111 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000000101101111) 6 43 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000000101110011 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000000101110011) 6 33 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000000101111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000000101111011) 6 37 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000000101111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000000101111111) 6 15 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000000110100011 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000000110100011) 6 34 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000000110111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000000110111011) 6 23 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000000110111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000000110111111) 6 38 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000000111100011 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000000111100011) 6 33 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000001010000011 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000001010000011) 6 33 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000001010011011 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000001010011011) 6 37 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000001010011111 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000001010011111) 6 14 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000001011100011 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000001011100011) 6 33 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000001011111001 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000001011111001) 6 42 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000001011111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000001011111011) 6 36 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000001011111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000001011111111) 5 29 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000001100000011 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000001100000011) 6 33 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000001101100011 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000001101100011) 6 34 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000001101111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000001101111011) 6 37 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000010000000011 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000010000000011) 6 31 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000010000001111 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000010000001111) 6 14 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000010011000011 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000010011000011) 6 19 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000010100100011 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000010100100011) 6 27 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000010100111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000010100111011) 6 23 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000010101100011 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000010101100011) 6 50 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000010110000011 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000010110000011) 6 49 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000010110110011 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000010110110011) 6 27 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000010111011011 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000010111011011) 6 45 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000010111100011 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000010111100011) 6 21 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000010111111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000010111111011) 6 50 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000011010000011 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000011010000011) 6 27 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000011011100011 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000011011100011) 6 22 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000011011111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000011011111011) 6 23 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000011110000011 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000011110000011) 6 44 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000101111111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000101111111011) 6 37 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000110000001011 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000110000001011) 6 40 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000111011111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000111011111111) 6 30 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000001011110000011 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000001011110000011) 6 53 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000001011111111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000001011111111011) 6 26 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000010111111100011 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000010111111100011) 6 39 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000011000101111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000011000101111111) 6 37 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000011001011111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000011001011111111) 6 30 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000101111111100011 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000101111111100011) 6 21 0 300 = true := by decide +kernel

theorem blocks19_check : ∀ e ∈ blocks19,
    gameCheck (Rule30StripCertificateTable.wordOf e.1.1 e.1.2) e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2 = true := by
  intro e he
  simp only [blocks19, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact check_0000000000000001111
  · exact check_0000000000000010011
  · exact check_0000000000000011011
  · exact check_0000000000000101001
  · exact check_0000000000000101111
  · exact check_0000000000000110011
  · exact check_0000000000001000011
  · exact check_0000000000001001111
  · exact check_0000000000001010011
  · exact check_0000000000001011011
  · exact check_0000000000001101011
  · exact check_0000000000001101111
  · exact check_0000000000001111011
  · exact check_0000000000010100011
  · exact check_0000000000010111001
  · exact check_0000000000010111011
  · exact check_0000000000010111111
  · exact check_0000000000011000011
  · exact check_0000000000011011011
  · exact check_0000000000100000011
  · exact check_0000000000100110011
  · exact check_0000000000101001011
  · exact check_0000000000101011011
  · exact check_0000000000101100011
  · exact check_0000000000101101111
  · exact check_0000000000101110011
  · exact check_0000000000101111011
  · exact check_0000000000101111111
  · exact check_0000000000110100011
  · exact check_0000000000110111011
  · exact check_0000000000110111111
  · exact check_0000000000111100011
  · exact check_0000000001010000011
  · exact check_0000000001010011011
  · exact check_0000000001010011111
  · exact check_0000000001011100011
  · exact check_0000000001011111001
  · exact check_0000000001011111011
  · exact check_0000000001011111111
  · exact check_0000000001100000011
  · exact check_0000000001101100011
  · exact check_0000000001101111011
  · exact check_0000000010000000011
  · exact check_0000000010000001111
  · exact check_0000000010011000011
  · exact check_0000000010100100011
  · exact check_0000000010100111011
  · exact check_0000000010101100011
  · exact check_0000000010110000011
  · exact check_0000000010110110011
  · exact check_0000000010111011011
  · exact check_0000000010111100011
  · exact check_0000000010111111011
  · exact check_0000000011010000011
  · exact check_0000000011011100011
  · exact check_0000000011011111011
  · exact check_0000000011110000011
  · exact check_0000000101111111011
  · exact check_0000000110000001011
  · exact check_0000000111011111111
  · exact check_0000001011110000011
  · exact check_0000001011111111011
  · exact check_0000010111111100011
  · exact check_0000011000101111111
  · exact check_0000011001011111111
  · exact check_0000101111111100011

/-- The blocks of period 19 that the game excludes and the kit does not, and that `WallSets` excludes, each as its least
rotation `wordOf 19 bits`. -/
def wallBlocks19 : List Nat := [
    0b0000000010111111111, 0b0000000100111111111, 0b0000000101111111111, 0b0000000110111111111, 0b0000000111111111011,
    0b0000001010111111111, 0b0000001011111111111, 0b0000001110111111111, 0b0000001111111111011, 0b0000010011111111111,
    0b0000010110111111111, 0b0000010111111111011, 0b0000010111111111111, 0b0000011000111111111, 0b0000011001111111111,
    0b0000011010111111111, 0b0000011011111111111, 0b0000011101111111111, 0b0000011111111100011, 0b0000011111111111011,
    0b0000101011111111111, 0b0000101110111111111, 0b0000101111111111011, 0b0000101111111111111, 0b0000111011111111111,
    0b0000111110111111111, 0b0000111111111100011, 0b0000111111111111011, 0b0001001111111111111, 0b0001011011111111111,
    0b0001011110111111111, 0b0001011111111100011, 0b0001011111111111011, 0b0001011111111111111, 0b0001100011111111111,
    0b0001100101111111111, 0b0001100111111111111, 0b0001101011111111111, 0b0001101110111111111, 0b0001101111111111111,
    0b0001110111111111011, 0b0001110111111111111, 0b0001111101111111111, 0b0001111111111111011, 0b0010101111111111111,
    0b0010111011111111111, 0b0010111110111111111, 0b0010111111111111011, 0b0010111111111111111, 0b0011101111111111011,
    0b0011101111111111111, 0b0011111010111111111, 0b0011111011111111111, 0b0011111110111111111, 0b0011111111111111011,
    0b0011111111111111101, 0b0101101111111111111, 0b0101111011111111111, 0b0101111110111111111, 0b0101111111111111011,
    0b0101111111111111111, 0b0110111011111111111, 0b0110111110111111111, 0b0110111111111111111, 0b0111011111111111111,
    0b0111110111111111111, 0b0111111101111111111]

theorem wallBlocks19_all : wallBlocks19.all (fun bits => wallSet (Rule30StripCertificateTable.wordOf 19 bits)) = true := by
  decide +kernel

/-- **The blocks of `WallSets`**: for each entry of `wallBlocks19`, the center column does not repeat the block from any
time `T` on. -/
theorem center_not_wallBlocks19 (bits : Nat) (hb : bits ∈ wallBlocks19) (T : Nat)
    (hcol : ∀ t : Nat, T ≤ t → Rule30Prize.center t = cyc (Rule30StripCertificateTable.wordOf 19 bits) (t - T)) :
    False :=
  center_wall_set_block T _ (List.all_eq_true.1 wallBlocks19_all bits hb) hcol

/-- **The 66 blocks**: for each entry of `blocks19`, the center column is not, from any time `T` on, the block
`wordOf 19 bits`, read from any phase. -/
theorem center_not_blocks19 (e : (Nat × Nat) × (Nat × Nat × Nat × Nat)) (he : e ∈ blocks19) (T shift : Nat)
    (h : ∀ t : Nat, T ≤ t → Rule30Prize.center t =
      (Rule30StripCertificateTable.wordOf e.1.1 e.1.2).getD ((t + shift) % e.1.1) false) : False :=
  center_not_bitGame _ _ _ _ _ (blocks19_check e he) T shift fun t ht => by
    rw [h t ht, Rule30StripCertificateTable.wordOf_length]

/-- The same in the kit's form: none of the 66 blocks is an `EventuallyWord` of the center column. -/
theorem not_eventually_blocks19 (e : (Nat × Nat) × (Nat × Nat × Nat × Nat)) (he : e ∈ blocks19) :
    ¬ Rule30StripCertificates.EventuallyWord (Rule30StripCertificateTable.wordOf e.1.1 e.1.2) :=
  bitGame_not_eventuallyWord _ _ _ _ _ (blocks19_check e he)

end Rule30Open
