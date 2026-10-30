module

public import Rule30Open.Columns.BitGame
public import Rule30Open.Columns.WallSets

/-!
# The game decided in the kernel and the window-set check exclude 122 more blocks of period 18

[BitGame](BitGame.md) decides the finite game in the kernel from the block alone (`gameCheck`), and `bitGame_column`
turns a passing check into an exclusion. Here the check runs on the 77 blocks of period 18 that the game excludes at a
width of at most 12 and that neither the kit nor [WallSets](WallSets.md) excludes.

* `blocks18`: the blocks, each as its least rotation, with the parameters of `gameCheck`; `blocks18_check`: every
  check passes.
* `center_not_blocks18`, `not_eventually_blocks18`: the center column of the single cell does not eventually repeat
  any of them, in any rotation, and in the kit's form `EventuallyWord`.
* `wallBlocks18`, `center_not_wallBlocks18`: the 45 other blocks of period 18 that the game excludes beyond the kit,
  each passing `WallSets.wallSet`, so `center_wall_set_block` excludes them.

The natural-language argument is `BitBlocks18.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

open Ruliology.CellularAutomata BitGame

/-- The blocks of period 18 that the game excludes at a width of at most 12 and that the kit and `WallSets` do not
exclude, each as its least rotation `wordOf 18 bits`, with the width `K`, the steps `D`, the rounds and the search fuel
of `gameCheck`, from `computations/bit_game.py`. -/
def blocks18 : List ((Nat × Nat) × (Nat × Nat × Nat × Nat)) := [
    ((18, 0b000000000000000101), (7, 12, 2, 300)), ((18, 0b000000000000001111), (6, 14, 2, 300)),
    ((18, 0b000000000000010001), (8, 24, 2, 300)), ((18, 0b000000000000010011), (6, 32, 1, 300)),
    ((18, 0b000000000000011011), (6, 31, 1, 300)), ((18, 0b000000000000011101), (7, 13, 2, 300)),
    ((18, 0b000000000000011111), (8, 24, 3, 300)), ((18, 0b000000000000101001), (6, 12, 2, 300)),
    ((18, 0b000000000000101011), (6, 34, 1, 300)), ((18, 0b000000000000101101), (10, 60, 3, 300)),
    ((18, 0b000000000000101111), (6, 39, 1, 300)), ((18, 0b000000000000110011), (6, 32, 1, 300)),
    ((18, 0b000000000000110111), (8, 47, 1, 300)), ((18, 0b000000000001000011), (6, 32, 1, 300)),
    ((18, 0b000000000001001111), (6, 16, 2, 300)), ((18, 0b000000000001010011), (6, 31, 1, 300)),
    ((18, 0b000000000001010101), (8, 22, 2, 300)), ((18, 0b000000000001011011), (6, 34, 1, 300)),
    ((18, 0b000000000001011111), (8, 24, 2, 300)), ((18, 0b000000000001101001), (9, 89, 1, 300)),
    ((18, 0b000000000001101011), (6, 34, 1, 300)), ((18, 0b000000000001101111), (6, 14, 2, 300)),
    ((18, 0b000000000001111011), (6, 32, 1, 300)), ((18, 0b000000000010100011), (6, 33, 1, 300)),
    ((18, 0b000000000010100111), (8, 57, 1, 300)), ((18, 0b000000000010111001), (6, 44, 1, 300)),
    ((18, 0b000000000010111011), (6, 50, 1, 300)), ((18, 0b000000000010111111), (6, 15, 2, 300)),
    ((18, 0b000000000011000011), (6, 33, 1, 300)), ((18, 0b000000000011011001), (8, 16, 3, 300)),
    ((18, 0b000000000011011011), (6, 39, 1, 300)), ((18, 0b000000000011011111), (10, 33, 2, 300)),
    ((18, 0b000000000100000011), (6, 33, 1, 300)), ((18, 0b000000000100110011), (6, 33, 1, 300)),
    ((18, 0b000000000101001011), (6, 50, 1, 300)), ((18, 0b000000000101001111), (10, 29, 2, 300)),
    ((18, 0b000000000101011011), (6, 50, 1, 300)), ((18, 0b000000000101100011), (6, 32, 1, 300)),
    ((18, 0b000000000101101111), (6, 42, 1, 300)), ((18, 0b000000000101110011), (6, 32, 1, 300)),
    ((18, 0b000000000101110101), (9, 24, 3, 300)), ((18, 0b000000000101111011), (6, 34, 1, 300)),
    ((18, 0b000000000101111111), (6, 15, 2, 300)), ((18, 0b000000000110100011), (6, 33, 1, 300)),
    ((18, 0b000000000110111011), (6, 22, 2, 300)), ((18, 0b000000000110111111), (6, 37, 1, 300)),
    ((18, 0b000000000111100011), (6, 32, 1, 300)), ((18, 0b000000001010000011), (7, 48, 1, 300)),
    ((18, 0b000000001010011011), (6, 29, 2, 300)), ((18, 0b000000001011100011), (6, 41, 1, 300)),
    ((18, 0b000000001011111011), (6, 24, 2, 300)), ((18, 0b000000001011111111), (6, 29, 1, 300)),
    ((18, 0b000000001100000011), (6, 25, 2, 300)), ((18, 0b000000001101100011), (6, 22, 2, 300)),
    ((18, 0b000000001101111011), (6, 25, 2, 300)), ((18, 0b000000010000001111), (12, 72, 1, 300)),
    ((18, 0b000000010100111011), (10, 32, 3, 300)), ((18, 0b000000010111101111), (6, 36, 2, 300)),
    ((18, 0b000000010111111011), (7, 49, 2, 300)), ((18, 0b000000011011111011), (11, 55, 3, 300)),
    ((18, 0b000000101011111111), (5, 28, 1, 300)), ((18, 0b000000101110000011), (8, 42, 2, 300)),
    ((18, 0b000000101111111001), (10, 55, 2, 300)), ((18, 0b000000101111111011), (6, 36, 1, 300)),
    ((18, 0b000000110111111011), (10, 41, 3, 300)), ((18, 0b000001011111111011), (6, 28, 1, 300)),
    ((18, 0b000011011111111001), (10, 38, 2, 300)), ((18, 0b000101111111100011), (6, 25, 1, 300)),
    ((18, 0b000110111111111001), (8, 34, 2, 300)), ((18, 0b000111111111100111), (12, 58, 2, 300)),
    ((18, 0b001001111111111101), (10, 36, 3, 300)), ((18, 0b001010011111111011), (9, 33, 3, 300)),
    ((18, 0b001100111111111111), (7, 26, 2, 300)), ((18, 0b001111101011111111), (5, 27, 1, 300)),
    ((18, 0b001111110011111111), (8, 41, 2, 300)), ((18, 0b010101111111111111), (7, 23, 2, 300)),
    ((18, 0b011011011111111111), (7, 24, 2, 300))]

set_option Elab.async false

set_option maxHeartbeats 0 in
theorem check_000000000000000101 :
    gameCheck (Rule30StripCertificateTable.wordOf 18 0b000000000000000101) 7 12 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000000001111 :
    gameCheck (Rule30StripCertificateTable.wordOf 18 0b000000000000001111) 6 14 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000000010001 :
    gameCheck (Rule30StripCertificateTable.wordOf 18 0b000000000000010001) 8 24 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000000010011 :
    gameCheck (Rule30StripCertificateTable.wordOf 18 0b000000000000010011) 6 32 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000000011011 :
    gameCheck (Rule30StripCertificateTable.wordOf 18 0b000000000000011011) 6 31 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000000011101 :
    gameCheck (Rule30StripCertificateTable.wordOf 18 0b000000000000011101) 7 13 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000000011111 :
    gameCheck (Rule30StripCertificateTable.wordOf 18 0b000000000000011111) 8 24 3 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000000101001 :
    gameCheck (Rule30StripCertificateTable.wordOf 18 0b000000000000101001) 6 12 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000000101011 :
    gameCheck (Rule30StripCertificateTable.wordOf 18 0b000000000000101011) 6 34 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000000101101 :
    gameCheck (Rule30StripCertificateTable.wordOf 18 0b000000000000101101) 10 60 3 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000000101111 :
    gameCheck (Rule30StripCertificateTable.wordOf 18 0b000000000000101111) 6 39 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000000110011 :
    gameCheck (Rule30StripCertificateTable.wordOf 18 0b000000000000110011) 6 32 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000000110111 :
    gameCheck (Rule30StripCertificateTable.wordOf 18 0b000000000000110111) 8 47 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000001000011 :
    gameCheck (Rule30StripCertificateTable.wordOf 18 0b000000000001000011) 6 32 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000001001111 :
    gameCheck (Rule30StripCertificateTable.wordOf 18 0b000000000001001111) 6 16 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000001010011 :
    gameCheck (Rule30StripCertificateTable.wordOf 18 0b000000000001010011) 6 31 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000001010101 :
    gameCheck (Rule30StripCertificateTable.wordOf 18 0b000000000001010101) 8 22 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000001011011 :
    gameCheck (Rule30StripCertificateTable.wordOf 18 0b000000000001011011) 6 34 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000001011111 :
    gameCheck (Rule30StripCertificateTable.wordOf 18 0b000000000001011111) 8 24 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000001101001 :
    gameCheck (Rule30StripCertificateTable.wordOf 18 0b000000000001101001) 9 89 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000001101011 :
    gameCheck (Rule30StripCertificateTable.wordOf 18 0b000000000001101011) 6 34 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000001101111 :
    gameCheck (Rule30StripCertificateTable.wordOf 18 0b000000000001101111) 6 14 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000001111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 18 0b000000000001111011) 6 32 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000010100011 :
    gameCheck (Rule30StripCertificateTable.wordOf 18 0b000000000010100011) 6 33 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000010100111 :
    gameCheck (Rule30StripCertificateTable.wordOf 18 0b000000000010100111) 8 57 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000010111001 :
    gameCheck (Rule30StripCertificateTable.wordOf 18 0b000000000010111001) 6 44 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000010111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 18 0b000000000010111011) 6 50 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000010111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 18 0b000000000010111111) 6 15 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000011000011 :
    gameCheck (Rule30StripCertificateTable.wordOf 18 0b000000000011000011) 6 33 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000011011001 :
    gameCheck (Rule30StripCertificateTable.wordOf 18 0b000000000011011001) 8 16 3 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000011011011 :
    gameCheck (Rule30StripCertificateTable.wordOf 18 0b000000000011011011) 6 39 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000011011111 :
    gameCheck (Rule30StripCertificateTable.wordOf 18 0b000000000011011111) 10 33 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000100000011 :
    gameCheck (Rule30StripCertificateTable.wordOf 18 0b000000000100000011) 6 33 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000100110011 :
    gameCheck (Rule30StripCertificateTable.wordOf 18 0b000000000100110011) 6 33 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000101001011 :
    gameCheck (Rule30StripCertificateTable.wordOf 18 0b000000000101001011) 6 50 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000101001111 :
    gameCheck (Rule30StripCertificateTable.wordOf 18 0b000000000101001111) 10 29 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000101011011 :
    gameCheck (Rule30StripCertificateTable.wordOf 18 0b000000000101011011) 6 50 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000101100011 :
    gameCheck (Rule30StripCertificateTable.wordOf 18 0b000000000101100011) 6 32 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000101101111 :
    gameCheck (Rule30StripCertificateTable.wordOf 18 0b000000000101101111) 6 42 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000101110011 :
    gameCheck (Rule30StripCertificateTable.wordOf 18 0b000000000101110011) 6 32 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000101110101 :
    gameCheck (Rule30StripCertificateTable.wordOf 18 0b000000000101110101) 9 24 3 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000101111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 18 0b000000000101111011) 6 34 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000101111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 18 0b000000000101111111) 6 15 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000110100011 :
    gameCheck (Rule30StripCertificateTable.wordOf 18 0b000000000110100011) 6 33 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000110111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 18 0b000000000110111011) 6 22 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000110111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 18 0b000000000110111111) 6 37 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000111100011 :
    gameCheck (Rule30StripCertificateTable.wordOf 18 0b000000000111100011) 6 32 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000001010000011 :
    gameCheck (Rule30StripCertificateTable.wordOf 18 0b000000001010000011) 7 48 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000001010011011 :
    gameCheck (Rule30StripCertificateTable.wordOf 18 0b000000001010011011) 6 29 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000001011100011 :
    gameCheck (Rule30StripCertificateTable.wordOf 18 0b000000001011100011) 6 41 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000001011111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 18 0b000000001011111011) 6 24 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000001011111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 18 0b000000001011111111) 6 29 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000001100000011 :
    gameCheck (Rule30StripCertificateTable.wordOf 18 0b000000001100000011) 6 25 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000001101100011 :
    gameCheck (Rule30StripCertificateTable.wordOf 18 0b000000001101100011) 6 22 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000001101111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 18 0b000000001101111011) 6 25 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000010000001111 :
    gameCheck (Rule30StripCertificateTable.wordOf 18 0b000000010000001111) 12 72 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000010100111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 18 0b000000010100111011) 10 32 3 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000010111101111 :
    gameCheck (Rule30StripCertificateTable.wordOf 18 0b000000010111101111) 6 36 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000010111111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 18 0b000000010111111011) 7 49 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000011011111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 18 0b000000011011111011) 11 55 3 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000101011111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 18 0b000000101011111111) 5 28 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000101110000011 :
    gameCheck (Rule30StripCertificateTable.wordOf 18 0b000000101110000011) 8 42 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000101111111001 :
    gameCheck (Rule30StripCertificateTable.wordOf 18 0b000000101111111001) 10 55 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000101111111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 18 0b000000101111111011) 6 36 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000110111111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 18 0b000000110111111011) 10 41 3 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000001011111111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 18 0b000001011111111011) 6 28 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000011011111111001 :
    gameCheck (Rule30StripCertificateTable.wordOf 18 0b000011011111111001) 10 38 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000101111111100011 :
    gameCheck (Rule30StripCertificateTable.wordOf 18 0b000101111111100011) 6 25 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000110111111111001 :
    gameCheck (Rule30StripCertificateTable.wordOf 18 0b000110111111111001) 8 34 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000111111111100111 :
    gameCheck (Rule30StripCertificateTable.wordOf 18 0b000111111111100111) 12 58 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_001001111111111101 :
    gameCheck (Rule30StripCertificateTable.wordOf 18 0b001001111111111101) 10 36 3 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_001010011111111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 18 0b001010011111111011) 9 33 3 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_001100111111111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 18 0b001100111111111111) 7 26 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_001111101011111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 18 0b001111101011111111) 5 27 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_001111110011111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 18 0b001111110011111111) 8 41 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_010101111111111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 18 0b010101111111111111) 7 23 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_011011011111111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 18 0b011011011111111111) 7 24 2 300 = true := by decide +kernel

theorem blocks18_check : ∀ e ∈ blocks18,
    gameCheck (Rule30StripCertificateTable.wordOf e.1.1 e.1.2) e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2 = true := by
  intro e he
  simp only [blocks18, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl
  · exact check_000000000000000101
  · exact check_000000000000001111
  · exact check_000000000000010001
  · exact check_000000000000010011
  · exact check_000000000000011011
  · exact check_000000000000011101
  · exact check_000000000000011111
  · exact check_000000000000101001
  · exact check_000000000000101011
  · exact check_000000000000101101
  · exact check_000000000000101111
  · exact check_000000000000110011
  · exact check_000000000000110111
  · exact check_000000000001000011
  · exact check_000000000001001111
  · exact check_000000000001010011
  · exact check_000000000001010101
  · exact check_000000000001011011
  · exact check_000000000001011111
  · exact check_000000000001101001
  · exact check_000000000001101011
  · exact check_000000000001101111
  · exact check_000000000001111011
  · exact check_000000000010100011
  · exact check_000000000010100111
  · exact check_000000000010111001
  · exact check_000000000010111011
  · exact check_000000000010111111
  · exact check_000000000011000011
  · exact check_000000000011011001
  · exact check_000000000011011011
  · exact check_000000000011011111
  · exact check_000000000100000011
  · exact check_000000000100110011
  · exact check_000000000101001011
  · exact check_000000000101001111
  · exact check_000000000101011011
  · exact check_000000000101100011
  · exact check_000000000101101111
  · exact check_000000000101110011
  · exact check_000000000101110101
  · exact check_000000000101111011
  · exact check_000000000101111111
  · exact check_000000000110100011
  · exact check_000000000110111011
  · exact check_000000000110111111
  · exact check_000000000111100011
  · exact check_000000001010000011
  · exact check_000000001010011011
  · exact check_000000001011100011
  · exact check_000000001011111011
  · exact check_000000001011111111
  · exact check_000000001100000011
  · exact check_000000001101100011
  · exact check_000000001101111011
  · exact check_000000010000001111
  · exact check_000000010100111011
  · exact check_000000010111101111
  · exact check_000000010111111011
  · exact check_000000011011111011
  · exact check_000000101011111111
  · exact check_000000101110000011
  · exact check_000000101111111001
  · exact check_000000101111111011
  · exact check_000000110111111011
  · exact check_000001011111111011
  · exact check_000011011111111001
  · exact check_000101111111100011
  · exact check_000110111111111001
  · exact check_000111111111100111
  · exact check_001001111111111101
  · exact check_001010011111111011
  · exact check_001100111111111111
  · exact check_001111101011111111
  · exact check_001111110011111111
  · exact check_010101111111111111
  · exact check_011011011111111111

/-- The blocks of period 18 that the game excludes and the kit does not, and that `WallSets` excludes, each as its least
rotation `wordOf 18 bits`. -/
def wallBlocks18 : List Nat := [
    0b000000010111111111, 0b000000101111111111, 0b000000111111111011, 0b000001001111111111, 0b000001011111111111,
    0b000001100111111111, 0b000001101111111111, 0b000001110111111111, 0b000001111111111011, 0b000010101111111111,
    0b000010111111111011, 0b000010111111111111, 0b000011101111111111, 0b000011111111100011, 0b000011111111111011,
    0b000100111111111111, 0b000101101111111111, 0b000101111111111011, 0b000101111111111111, 0b000110001111111111,
    0b000110010111111111, 0b000110011111111111, 0b000110101111111111, 0b000110111111111111, 0b000111011111111111,
    0b000111110111111111, 0b000111111111111011, 0b001010111111111111, 0b001011101111111111, 0b001011111111111011,
    0b001011111111111111, 0b001110111111111011, 0b001110111111111111, 0b001111101111111111, 0b001111111111111011,
    0b001111111111111101, 0b010110111111111111, 0b010111101111111111, 0b010111111111111011, 0b010111111111111111,
    0b011011101111111111, 0b011011111111111111, 0b011101111111111111, 0b011111011111111111, 0b011111110111111111]

theorem wallBlocks18_all : wallBlocks18.all (fun bits => wallSet (Rule30StripCertificateTable.wordOf 18 bits)) = true := by
  decide +kernel

/-- **The blocks of `WallSets`**: for each entry of `wallBlocks18`, the center column does not repeat the block from any
time `T` on. -/
theorem center_not_wallBlocks18 (bits : Nat) (hb : bits ∈ wallBlocks18) (T : Nat)
    (hcol : ∀ t : Nat, T ≤ t → Rule30Prize.center t = cyc (Rule30StripCertificateTable.wordOf 18 bits) (t - T)) :
    False :=
  center_wall_set_block T _ (List.all_eq_true.1 wallBlocks18_all bits hb) hcol

/-- **The 77 blocks**: for each entry of `blocks18`, the center column is not, from any time `T` on, the block
`wordOf 18 bits`, read from any phase. -/
theorem center_not_blocks18 (e : (Nat × Nat) × (Nat × Nat × Nat × Nat)) (he : e ∈ blocks18) (T shift : Nat)
    (h : ∀ t : Nat, T ≤ t → Rule30Prize.center t =
      (Rule30StripCertificateTable.wordOf e.1.1 e.1.2).getD ((t + shift) % e.1.1) false) : False :=
  center_not_bitGame _ _ _ _ _ (blocks18_check e he) T shift fun t ht => by
    rw [h t ht, Rule30StripCertificateTable.wordOf_length]

/-- The same in the kit's form: none of the 77 blocks is an `EventuallyWord` of the center column. -/
theorem not_eventually_blocks18 (e : (Nat × Nat) × (Nat × Nat × Nat × Nat)) (he : e ∈ blocks18) :
    ¬ Rule30StripCertificates.EventuallyWord (Rule30StripCertificateTable.wordOf e.1.1 e.1.2) :=
  bitGame_not_eventuallyWord _ _ _ _ _ (blocks18_check e he)

end Rule30Open
