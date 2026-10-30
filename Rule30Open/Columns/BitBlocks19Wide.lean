module

public import Rule30Open.Columns.BitGame

/-!
# The game decided in the kernel excludes 57 more blocks of period 19 that need 7 to 12 cells

[BitGame](BitGame.md) decides the finite game in the kernel from the block alone (`gameCheck`), and `bitGame_column`
turns a passing check into an exclusion. Here the check runs on the 57 blocks of period 19 that the game excludes at a
width of 7 to 12 and that neither the kit nor [WallSets](WallSets.md) excludes.

* `blocks19Wide`: the blocks, each as its least rotation, with the parameters of `gameCheck`; `blocks19Wide_check`:
  every check passes.
* `center_not_blocks19Wide`, `not_eventually_blocks19Wide`: the center column of the single cell does not eventually
  repeat any of them, in any rotation, and in the kit's form `EventuallyWord`.

The natural-language argument is `BitBlocks19Wide.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

open Ruliology.CellularAutomata BitGame

/-- The blocks of period 19 that the game excludes at a width of 7 to 12 and that the kit and `WallSets` do not
exclude, each as its least rotation `wordOf 19 bits`, with the width `K`, the steps `D`, the rounds and the search fuel
of `gameCheck`, from `computations/bit_game.py`. -/
def blocks19Wide : List ((Nat × Nat) × (Nat × Nat × Nat × Nat)) := [
    ((19, 0b0000000000000000101), (7, 12, 1, 300)), ((19, 0b0000000000000010001), (8, 24, 1, 300)),
    ((19, 0b0000000000000011101), (7, 13, 1, 300)), ((19, 0b0000000000000011111), (8, 24, 2, 300)),
    ((19, 0b0000000000000100011), (8, 30, 2, 300)), ((19, 0b0000000000000101101), (9, 23, 2, 300)),
    ((19, 0b0000000000000110111), (8, 55, 0, 300)), ((19, 0b0000000000000111011), (11, 45, 2, 300)),
    ((19, 0b0000000000001010101), (8, 22, 1, 300)), ((19, 0b0000000000001011111), (8, 24, 1, 300)),
    ((19, 0b0000000000001101001), (8, 62, 1, 300)), ((19, 0b0000000000001110111), (10, 53, 1, 300)),
    ((19, 0b0000000000010010011), (8, 40, 1, 300)), ((19, 0b0000000000010100111), (8, 56, 0, 300)),
    ((19, 0b0000000000011011001), (8, 16, 2, 300)), ((19, 0b0000000000011011111), (10, 30, 1, 300)),
    ((19, 0b0000000000011100011), (12, 133, 0, 300)), ((19, 0b0000000000100000001), (8, 34, 2, 300)),
    ((19, 0b0000000000100001011), (11, 54, 1, 300)), ((19, 0b0000000000101110101), (9, 24, 2, 300)),
    ((19, 0b0000000001011100111), (10, 26, 2, 300)), ((19, 0b0000000001101111001), (9, 78, 2, 300)),
    ((19, 0b0000000001101111111), (11, 49, 1, 300)), ((19, 0b0000000010111001011), (9, 69, 0, 300)),
    ((19, 0b0000000010111101111), (9, 44, 1, 300)), ((19, 0b0000000101110011011), (7, 46, 1, 300)),
    ((19, 0b0000000101111100011), (12, 76, 0, 300)), ((19, 0b0000000101111111001), (9, 56, 1, 300)),
    ((19, 0b0000000110111111001), (12, 49, 3, 300)), ((19, 0b0000000110111111011), (8, 109, 0, 300)),
    ((19, 0b0000001010011111011), (8, 28, 2, 300)), ((19, 0b0000001011111100011), (12, 72, 1, 300)),
    ((19, 0b0000001011111111001), (9, 38, 1, 300)), ((19, 0b0000010111111111001), (10, 40, 1, 300)),
    ((19, 0b0000101111111111001), (8, 41, 1, 300)), ((19, 0b0000111001111111111), (7, 51, 1, 300)),
    ((19, 0b0000111111111100111), (10, 77, 1, 300)), ((19, 0b0000111111111111101), (7, 25, 1, 300)),
    ((19, 0b0001010011111111001), (9, 62, 2, 300)), ((19, 0b0001101111111111001), (8, 38, 1, 300)),
    ((19, 0b0010010100111111111), (10, 76, 2, 300)), ((19, 0b0010010111111111111), (8, 27, 2, 300)),
    ((19, 0b0010011111111111101), (10, 43, 2, 300)), ((19, 0b0010100111111111011), (9, 40, 1, 300)),
    ((19, 0b0010101001111111111), (12, 44, 1, 300)), ((19, 0b0011001111111111111), (7, 26, 1, 300)),
    ((19, 0b0011010011111111111), (12, 70, 1, 300)), ((19, 0b0011011111111111011), (8, 31, 1, 300)),
    ((19, 0b0011011111111111111), (7, 25, 1, 300)), ((19, 0b0011110011111111111), (7, 27, 1, 300)),
    ((19, 0b0011111100111111111), (8, 46, 1, 300)), ((19, 0b0011111111011011011), (8, 50, 2, 300)),
    ((19, 0b0011111111110110101), (7, 29, 1, 300)), ((19, 0b0011111111111011101), (8, 61, 1, 300)),
    ((19, 0b0101011111111111111), (7, 23, 1, 300)), ((19, 0b0110110111111111111), (7, 24, 1, 300)),
    ((19, 0b0111101111111111111), (8, 34, 1, 300))]

set_option Elab.async false

set_option maxHeartbeats 0 in
theorem check_0000000000000000101 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000000000000101) 7 12 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000000000010001 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000000000010001) 8 24 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000000000011101 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000000000011101) 7 13 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000000000011111 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000000000011111) 8 24 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000000000100011 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000000000100011) 8 30 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000000000101101 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000000000101101) 9 23 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000000000110111 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000000000110111) 8 55 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000000000111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000000000111011) 11 45 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000000001010101 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000000001010101) 8 22 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000000001011111 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000000001011111) 8 24 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000000001101001 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000000001101001) 8 62 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000000001110111 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000000001110111) 10 53 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000000010010011 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000000010010011) 8 40 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000000010100111 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000000010100111) 8 56 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000000011011001 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000000011011001) 8 16 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000000011011111 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000000011011111) 10 30 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000000011100011 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000000011100011) 12 133 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000000100000001 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000000100000001) 8 34 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000000100001011 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000000100001011) 11 54 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000000101110101 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000000101110101) 9 24 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000001011100111 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000001011100111) 10 26 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000001101111001 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000001101111001) 9 78 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000001101111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000001101111111) 11 49 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000010111001011 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000010111001011) 9 69 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000010111101111 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000010111101111) 9 44 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000101110011011 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000101110011011) 7 46 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000101111100011 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000101111100011) 12 76 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000101111111001 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000101111111001) 9 56 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000110111111001 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000110111111001) 12 49 3 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000000110111111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000000110111111011) 8 109 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000001010011111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000001010011111011) 8 28 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000001011111100011 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000001011111100011) 12 72 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000001011111111001 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000001011111111001) 9 38 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000010111111111001 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000010111111111001) 10 40 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000101111111111001 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000101111111111001) 8 41 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000111001111111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000111001111111111) 7 51 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000111111111100111 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000111111111100111) 10 77 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000111111111111101 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0000111111111111101) 7 25 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0001010011111111001 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0001010011111111001) 9 62 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0001101111111111001 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0001101111111111001) 8 38 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0010010100111111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0010010100111111111) 10 76 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0010010111111111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0010010111111111111) 8 27 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0010011111111111101 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0010011111111111101) 10 43 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0010100111111111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0010100111111111011) 9 40 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0010101001111111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0010101001111111111) 12 44 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0011001111111111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0011001111111111111) 7 26 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0011010011111111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0011010011111111111) 12 70 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0011011111111111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0011011111111111011) 8 31 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0011011111111111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0011011111111111111) 7 25 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0011110011111111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0011110011111111111) 7 27 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0011111100111111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0011111100111111111) 8 46 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0011111111011011011 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0011111111011011011) 8 50 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0011111111110110101 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0011111111110110101) 7 29 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0011111111111011101 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0011111111111011101) 8 61 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0101011111111111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0101011111111111111) 7 23 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0110110111111111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0110110111111111111) 7 24 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0111101111111111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 19 0b0111101111111111111) 8 34 1 300 = true := by decide +kernel

theorem blocks19Wide_check : ∀ e ∈ blocks19Wide,
    gameCheck (Rule30StripCertificateTable.wordOf e.1.1 e.1.2) e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2 = true := by
  intro e he
  simp only [blocks19Wide, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact check_0000000000000000101
  · exact check_0000000000000010001
  · exact check_0000000000000011101
  · exact check_0000000000000011111
  · exact check_0000000000000100011
  · exact check_0000000000000101101
  · exact check_0000000000000110111
  · exact check_0000000000000111011
  · exact check_0000000000001010101
  · exact check_0000000000001011111
  · exact check_0000000000001101001
  · exact check_0000000000001110111
  · exact check_0000000000010010011
  · exact check_0000000000010100111
  · exact check_0000000000011011001
  · exact check_0000000000011011111
  · exact check_0000000000011100011
  · exact check_0000000000100000001
  · exact check_0000000000100001011
  · exact check_0000000000101110101
  · exact check_0000000001011100111
  · exact check_0000000001101111001
  · exact check_0000000001101111111
  · exact check_0000000010111001011
  · exact check_0000000010111101111
  · exact check_0000000101110011011
  · exact check_0000000101111100011
  · exact check_0000000101111111001
  · exact check_0000000110111111001
  · exact check_0000000110111111011
  · exact check_0000001010011111011
  · exact check_0000001011111100011
  · exact check_0000001011111111001
  · exact check_0000010111111111001
  · exact check_0000101111111111001
  · exact check_0000111001111111111
  · exact check_0000111111111100111
  · exact check_0000111111111111101
  · exact check_0001010011111111001
  · exact check_0001101111111111001
  · exact check_0010010100111111111
  · exact check_0010010111111111111
  · exact check_0010011111111111101
  · exact check_0010100111111111011
  · exact check_0010101001111111111
  · exact check_0011001111111111111
  · exact check_0011010011111111111
  · exact check_0011011111111111011
  · exact check_0011011111111111111
  · exact check_0011110011111111111
  · exact check_0011111100111111111
  · exact check_0011111111011011011
  · exact check_0011111111110110101
  · exact check_0011111111111011101
  · exact check_0101011111111111111
  · exact check_0110110111111111111
  · exact check_0111101111111111111

/-- **The 57 blocks**: for each entry of `blocks19Wide`, the center column is not, from any time `T` on, the block
`wordOf 19 bits`, read from any phase. -/
theorem center_not_blocks19Wide (e : (Nat × Nat) × (Nat × Nat × Nat × Nat)) (he : e ∈ blocks19Wide) (T shift : Nat)
    (h : ∀ t : Nat, T ≤ t → Rule30Prize.center t =
      (Rule30StripCertificateTable.wordOf e.1.1 e.1.2).getD ((t + shift) % e.1.1) false) : False :=
  center_not_bitGame _ _ _ _ _ (blocks19Wide_check e he) T shift fun t ht => by
    rw [h t ht, Rule30StripCertificateTable.wordOf_length]

/-- The same in the kit's form: none of the 57 blocks is an `EventuallyWord` of the center column. -/
theorem not_eventually_blocks19Wide (e : (Nat × Nat) × (Nat × Nat × Nat × Nat)) (he : e ∈ blocks19Wide) :
    ¬ Rule30StripCertificates.EventuallyWord (Rule30StripCertificateTable.wordOf e.1.1 e.1.2) :=
  bitGame_not_eventuallyWord _ _ _ _ _ (blocks19Wide_check e he)

end Rule30Open
