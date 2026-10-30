module

public import Rule30Open.Columns.BitGame

/-!
# The game decided in the kernel excludes 55 more blocks of period 20 that need 7 or 8 cells

[BitGame](BitGame.md) decides the finite game in the kernel from the block alone (`gameCheck`), and `bitGame_column`
turns a passing check into an exclusion. Here the check runs on the 55 blocks of period 20 that the game excludes at a
width of 7 or 8 and that neither the kit nor [WallSets](WallSets.md) excludes.

* `blocks20Mid`: the blocks, each as its least rotation, with the parameters of `gameCheck`; `blocks20Mid_check`: every
  check passes.
* `center_not_blocks20Mid`, `not_eventually_blocks20Mid`: the center column of the single cell does not eventually
  repeat any of them, in any rotation, and in the kit's form `EventuallyWord`.

The natural-language argument is `BitBlocks20Mid.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

open Ruliology.CellularAutomata BitGame

/-- The blocks of period 20 that the game excludes at a width of 7 or 8 and that the kit and `WallSets` do not
exclude, each as its least rotation `wordOf 20 bits`, with the width `K`, the steps `D`, the rounds and the search fuel
of `gameCheck`, from `computations/bit_game.py`. -/
def blocks20Mid : List ((Nat × Nat) × (Nat × Nat × Nat × Nat)) := [
    ((20, 0b00000000000000000101), (7, 12, 1, 300)), ((20, 0b00000000000000010001), (8, 24, 1, 300)),
    ((20, 0b00000000000000011101), (7, 13, 1, 300)), ((20, 0b00000000000000011111), (8, 24, 2, 300)),
    ((20, 0b00000000000000100011), (8, 82, 0, 300)), ((20, 0b00000000000000110111), (8, 57, 0, 300)),
    ((20, 0b00000000000000111111), (8, 35, 1, 300)), ((20, 0b00000000000001010101), (8, 22, 1, 300)),
    ((20, 0b00000000000001011111), (8, 24, 1, 300)), ((20, 0b00000000000001101001), (8, 48, 1, 300)),
    ((20, 0b00000000000001110111), (8, 54, 1, 300)), ((20, 0b00000000000010000101), (8, 30, 1, 300)),
    ((20, 0b00000000000010010011), (8, 43, 1, 300)), ((20, 0b00000000000010100111), (8, 58, 0, 300)),
    ((20, 0b00000000000011011001), (8, 16, 2, 300)), ((20, 0b00000000000011110011), (8, 53, 1, 300)),
    ((20, 0b00000000000100000001), (8, 30, 1, 300)), ((20, 0b00000000000101110101), (8, 25, 1, 300)),
    ((20, 0b00000000000110101111), (8, 61, 0, 300)), ((20, 0b00000000001111100001), (8, 33, 2, 300)),
    ((20, 0b00000000010101111111), (8, 26, 1, 300)), ((20, 0b00000000010111001111), (8, 26, 1, 300)),
    ((20, 0b00000000010111110101), (7, 20, 2, 300)), ((20, 0b00000000101000000011), (7, 28, 1, 300)),
    ((20, 0b00000000101110011011), (8, 43, 1, 300)), ((20, 0b00000000101111111001), (7, 37, 2, 300)),
    ((20, 0b00000001010011111011), (7, 27, 1, 300)), ((20, 0b00000010111111101111), (8, 18, 2, 300)),
    ((20, 0b00001001111111111111), (7, 24, 1, 300)), ((20, 0b00001011111111101111), (8, 39, 2, 300)),
    ((20, 0b00001101111111111001), (8, 61, 1, 300)), ((20, 0b00011011111111111001), (8, 36, 1, 300)),
    ((20, 0b00011100111111111111), (7, 26, 1, 300)), ((20, 0b00011111111111011011), (8, 30, 1, 300)),
    ((20, 0b00011111111111100111), (7, 26, 1, 300)), ((20, 0b00011111111111110101), (8, 42, 1, 300)),
    ((20, 0b00100111111111111101), (8, 39, 1, 300)), ((20, 0b00101001111111111011), (8, 49, 1, 300)),
    ((20, 0b00101101111111111111), (8, 43, 1, 300)), ((20, 0b00101111111111111101), (7, 30, 1, 300)),
    ((20, 0b00110011111111111111), (7, 57, 0, 300)), ((20, 0b00110111111111111011), (8, 40, 1, 300)),
    ((20, 0b00110111111111111111), (7, 51, 0, 300)), ((20, 0b00111011111111111101), (8, 43, 0, 300)),
    ((20, 0b00111100111111111101), (8, 92, 1, 300)), ((20, 0b00111100111111111111), (7, 27, 1, 300)),
    ((20, 0b00111111001111111111), (8, 39, 1, 300)), ((20, 0b00111111111101111111), (8, 24, 2, 300)),
    ((20, 0b00111111111110110101), (7, 29, 2, 300)), ((20, 0b00111111111111011101), (8, 93, 0, 300)),
    ((20, 0b00111111111111101111), (8, 44, 1, 300)), ((20, 0b00111111111111110101), (7, 24, 1, 300)),
    ((20, 0b01010111111111111011), (7, 26, 1, 300)), ((20, 0b01010111111111111111), (7, 57, 0, 300)),
    ((20, 0b01101101111111111111), (7, 24, 1, 300))]

set_option Elab.async false

set_option maxHeartbeats 0 in
theorem check_00000000000000000101 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000000000000101) 7 12 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000000000010001 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000000000010001) 8 24 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000000000011101 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000000000011101) 7 13 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000000000011111 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000000000011111) 8 24 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000000000100011 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000000000100011) 8 82 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000000000110111 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000000000110111) 8 57 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000000000111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000000000111111) 8 35 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000000001010101 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000000001010101) 8 22 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000000001011111 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000000001011111) 8 24 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000000001101001 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000000001101001) 8 48 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000000001110111 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000000001110111) 8 54 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000000010000101 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000000010000101) 8 30 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000000010010011 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000000010010011) 8 43 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000000010100111 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000000010100111) 8 58 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000000011011001 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000000011011001) 8 16 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000000011110011 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000000011110011) 8 53 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000000100000001 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000000100000001) 8 30 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000000101110101 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000000101110101) 8 25 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000000110101111 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000000110101111) 8 61 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000001111100001 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000001111100001) 8 33 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000010101111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000010101111111) 8 26 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000010111001111 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000010111001111) 8 26 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000010111110101 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000010111110101) 7 20 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000101000000011 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000101000000011) 7 28 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000101110011011 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000101110011011) 8 43 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000101111111001 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000101111111001) 7 37 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000001010011111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000001010011111011) 7 27 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000010111111101111 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000010111111101111) 8 18 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00001001111111111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00001001111111111111) 7 24 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00001011111111101111 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00001011111111101111) 8 39 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00001101111111111001 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00001101111111111001) 8 61 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00011011111111111001 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00011011111111111001) 8 36 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00011100111111111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00011100111111111111) 7 26 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00011111111111011011 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00011111111111011011) 8 30 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00011111111111100111 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00011111111111100111) 7 26 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00011111111111110101 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00011111111111110101) 8 42 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00100111111111111101 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00100111111111111101) 8 39 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00101001111111111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00101001111111111011) 8 49 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00101101111111111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00101101111111111111) 8 43 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00101111111111111101 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00101111111111111101) 7 30 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00110011111111111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00110011111111111111) 7 57 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00110111111111111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00110111111111111011) 8 40 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00110111111111111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00110111111111111111) 7 51 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00111011111111111101 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00111011111111111101) 8 43 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00111100111111111101 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00111100111111111101) 8 92 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00111100111111111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00111100111111111111) 7 27 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00111111001111111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00111111001111111111) 8 39 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00111111111101111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00111111111101111111) 8 24 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00111111111110110101 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00111111111110110101) 7 29 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00111111111111011101 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00111111111111011101) 8 93 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00111111111111101111 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00111111111111101111) 8 44 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00111111111111110101 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00111111111111110101) 7 24 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_01010111111111111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b01010111111111111011) 7 26 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_01010111111111111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b01010111111111111111) 7 57 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_01101101111111111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b01101101111111111111) 7 24 1 300 = true := by decide +kernel

theorem blocks20Mid_check : ∀ e ∈ blocks20Mid,
    gameCheck (Rule30StripCertificateTable.wordOf e.1.1 e.1.2) e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2 = true := by
  intro e he
  simp only [blocks20Mid, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact check_00000000000000000101
  · exact check_00000000000000010001
  · exact check_00000000000000011101
  · exact check_00000000000000011111
  · exact check_00000000000000100011
  · exact check_00000000000000110111
  · exact check_00000000000000111111
  · exact check_00000000000001010101
  · exact check_00000000000001011111
  · exact check_00000000000001101001
  · exact check_00000000000001110111
  · exact check_00000000000010000101
  · exact check_00000000000010010011
  · exact check_00000000000010100111
  · exact check_00000000000011011001
  · exact check_00000000000011110011
  · exact check_00000000000100000001
  · exact check_00000000000101110101
  · exact check_00000000000110101111
  · exact check_00000000001111100001
  · exact check_00000000010101111111
  · exact check_00000000010111001111
  · exact check_00000000010111110101
  · exact check_00000000101000000011
  · exact check_00000000101110011011
  · exact check_00000000101111111001
  · exact check_00000001010011111011
  · exact check_00000010111111101111
  · exact check_00001001111111111111
  · exact check_00001011111111101111
  · exact check_00001101111111111001
  · exact check_00011011111111111001
  · exact check_00011100111111111111
  · exact check_00011111111111011011
  · exact check_00011111111111100111
  · exact check_00011111111111110101
  · exact check_00100111111111111101
  · exact check_00101001111111111011
  · exact check_00101101111111111111
  · exact check_00101111111111111101
  · exact check_00110011111111111111
  · exact check_00110111111111111011
  · exact check_00110111111111111111
  · exact check_00111011111111111101
  · exact check_00111100111111111101
  · exact check_00111100111111111111
  · exact check_00111111001111111111
  · exact check_00111111111101111111
  · exact check_00111111111110110101
  · exact check_00111111111111011101
  · exact check_00111111111111101111
  · exact check_00111111111111110101
  · exact check_01010111111111111011
  · exact check_01010111111111111111
  · exact check_01101101111111111111

/-- **The 55 blocks**: for each entry of `blocks20Mid`, the center column is not, from any time `T` on, the block
`wordOf 20 bits`, read from any phase. -/
theorem center_not_blocks20Mid (e : (Nat × Nat) × (Nat × Nat × Nat × Nat)) (he : e ∈ blocks20Mid) (T shift : Nat)
    (h : ∀ t : Nat, T ≤ t → Rule30Prize.center t =
      (Rule30StripCertificateTable.wordOf e.1.1 e.1.2).getD ((t + shift) % e.1.1) false) : False :=
  center_not_bitGame _ _ _ _ _ (blocks20Mid_check e he) T shift fun t ht => by
    rw [h t ht, Rule30StripCertificateTable.wordOf_length]

/-- The same in the kit's form: none of the 55 blocks is an `EventuallyWord` of the center column. -/
theorem not_eventually_blocks20Mid (e : (Nat × Nat) × (Nat × Nat × Nat × Nat)) (he : e ∈ blocks20Mid) :
    ¬ Rule30StripCertificates.EventuallyWord (Rule30StripCertificateTable.wordOf e.1.1 e.1.2) :=
  bitGame_not_eventuallyWord _ _ _ _ _ (blocks20Mid_check e he)

end Rule30Open
