module

public import Rule30Open.Columns.BitGame

/-!
# The game decided in the kernel excludes 44 more blocks of period 20 that need 9 to 12 cells

[BitGame](BitGame.md) decides the finite game in the kernel from the block alone (`gameCheck`), and `bitGame_column`
turns a passing check into an exclusion. Here the check runs on the 44 blocks of period 20 that the game excludes at a
width of 9 to 12 and that neither the kit nor [WallSets](WallSets.md) excludes.

* `blocks20Wide`: the blocks, each as its least rotation, with the parameters of `gameCheck`; `blocks20Wide_check`:
  every check passes.
* `center_not_blocks20Wide`, `not_eventually_blocks20Wide`: the center column of the single cell does not eventually
  repeat any of them, in any rotation, and in the kit's form `EventuallyWord`.

The natural-language argument is `BitBlocks20Wide.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

open Ruliology.CellularAutomata BitGame

/-- The blocks of period 20 that the game excludes at a width of 9 to 12 and that the kit and `WallSets` do not
exclude, each as its least rotation `wordOf 20 bits`, with the width `K`, the steps `D`, the rounds and the search fuel
of `gameCheck`, from `computations/bit_game.py`. -/
def blocks20Wide : List ((Nat × Nat) × (Nat × Nat × Nat × Nat)) := [
    ((20, 0b00000000000000000111), (11, 37, 1, 300)), ((20, 0b00000000000000001001), (10, 82, 0, 300)),
    ((20, 0b00000000000000110101), (11, 64, 1, 300)), ((20, 0b00000000000000111011), (12, 73, 2, 300)),
    ((20, 0b00000000000001100011), (9, 59, 0, 300)), ((20, 0b00000000000001111111), (12, 87, 1, 300)),
    ((20, 0b00000000000010001011), (11, 55, 1, 300)), ((20, 0b00000000000011011111), (10, 30, 1, 300)),
    ((20, 0b00000000000011100011), (9, 33, 1, 300)), ((20, 0b00000000000011111001), (9, 55, 2, 300)),
    ((20, 0b00000000000101001111), (10, 46, 1, 300)), ((20, 0b00000000000110110011), (10, 61, 0, 300)),
    ((20, 0b00000000000110110111), (9, 56, 1, 300)), ((20, 0b00000000000111010011), (9, 51, 0, 300)),
    ((20, 0b00000000001000001011), (11, 69, 1, 300)), ((20, 0b00000000001001011011), (11, 113, 1, 300)),
    ((20, 0b00000000001011100111), (11, 66, 1, 300)), ((20, 0b00000000001101111111), (9, 23, 1, 300)),
    ((20, 0b00000000011101000011), (11, 86, 0, 300)), ((20, 0b00000000011110011111), (11, 53, 0, 300)),
    ((20, 0b00000001011100111011), (9, 42, 2, 300)), ((20, 0b00000001011110011111), (9, 32, 2, 300)),
    ((20, 0b00000001011110110011), (10, 77, 0, 300)), ((20, 0b00000001011111110011), (10, 59, 0, 300)),
    ((20, 0b00000001011111111001), (11, 111, 0, 300)), ((20, 0b00000001100000010111), (9, 53, 1, 300)),
    ((20, 0b00000010100111111011), (11, 108, 0, 300)), ((20, 0b00000010111110000011), (9, 28, 1, 300)),
    ((20, 0b00000010111110110011), (10, 36, 2, 300)), ((20, 0b00000011011111111001), (11, 41, 2, 300)),
    ((20, 0b00000101111111110011), (9, 31, 1, 300)), ((20, 0b00000101111111111001), (10, 72, 1, 300)),
    ((20, 0b00001011111110011111), (9, 64, 0, 300)), ((20, 0b00001011111111111001), (11, 133, 0, 300)),
    ((20, 0b00001110011111111111), (11, 68, 2, 300)), ((20, 0b00001111111111001111), (10, 60, 0, 300)),
    ((20, 0b00001111111111110011), (10, 40, 1, 300)), ((20, 0b00010111111111111001), (9, 48, 1, 300)),
    ((20, 0b00011111111111101101), (9, 65, 1, 300)), ((20, 0b00110011111111111011), (9, 42, 0, 300)),
    ((20, 0b00111110111111111101), (10, 42, 1, 300)), ((20, 0b00111111111011011011), (10, 58, 1, 300)),
    ((20, 0b00111111111110101011), (11, 57, 1, 300)), ((20, 0b00111111111111010111), (9, 86, 0, 300))]

set_option Elab.async false

set_option maxHeartbeats 0 in
theorem check_00000000000000000111 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000000000000111) 11 37 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000000000001001 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000000000001001) 10 82 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000000000110101 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000000000110101) 11 64 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000000000111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000000000111011) 12 73 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000000001100011 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000000001100011) 9 59 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000000001111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000000001111111) 12 87 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000000010001011 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000000010001011) 11 55 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000000011011111 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000000011011111) 10 30 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000000011100011 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000000011100011) 9 33 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000000011111001 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000000011111001) 9 55 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000000101001111 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000000101001111) 10 46 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000000110110011 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000000110110011) 10 61 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000000110110111 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000000110110111) 9 56 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000000111010011 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000000111010011) 9 51 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000001000001011 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000001000001011) 11 69 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000001001011011 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000001001011011) 11 113 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000001011100111 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000001011100111) 11 66 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000001101111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000001101111111) 9 23 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000011101000011 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000011101000011) 11 86 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000011110011111 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000000011110011111) 11 53 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000001011100111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000001011100111011) 9 42 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000001011110011111 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000001011110011111) 9 32 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000001011110110011 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000001011110110011) 10 77 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000001011111110011 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000001011111110011) 10 59 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000001011111111001 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000001011111111001) 11 111 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000001100000010111 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000001100000010111) 9 53 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000010100111111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000010100111111011) 11 108 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000010111110000011 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000010111110000011) 9 28 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000010111110110011 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000010111110110011) 10 36 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000011011111111001 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000011011111111001) 11 41 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000101111111110011 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000101111111110011) 9 31 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000101111111111001 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00000101111111111001) 10 72 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00001011111110011111 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00001011111110011111) 9 64 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00001011111111111001 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00001011111111111001) 11 133 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00001110011111111111 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00001110011111111111) 11 68 2 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00001111111111001111 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00001111111111001111) 10 60 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00001111111111110011 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00001111111111110011) 10 40 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00010111111111111001 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00010111111111111001) 9 48 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00011111111111101101 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00011111111111101101) 9 65 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00110011111111111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00110011111111111011) 9 42 0 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00111110111111111101 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00111110111111111101) 10 42 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00111111111011011011 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00111111111011011011) 10 58 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00111111111110101011 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00111111111110101011) 11 57 1 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00111111111111010111 :
    gameCheck (Rule30StripCertificateTable.wordOf 20 0b00111111111111010111) 9 86 0 300 = true := by decide +kernel

theorem blocks20Wide_check : ∀ e ∈ blocks20Wide,
    gameCheck (Rule30StripCertificateTable.wordOf e.1.1 e.1.2) e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2 = true := by
  intro e he
  simp only [blocks20Wide, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  · exact check_00000000000000000111
  · exact check_00000000000000001001
  · exact check_00000000000000110101
  · exact check_00000000000000111011
  · exact check_00000000000001100011
  · exact check_00000000000001111111
  · exact check_00000000000010001011
  · exact check_00000000000011011111
  · exact check_00000000000011100011
  · exact check_00000000000011111001
  · exact check_00000000000101001111
  · exact check_00000000000110110011
  · exact check_00000000000110110111
  · exact check_00000000000111010011
  · exact check_00000000001000001011
  · exact check_00000000001001011011
  · exact check_00000000001011100111
  · exact check_00000000001101111111
  · exact check_00000000011101000011
  · exact check_00000000011110011111
  · exact check_00000001011100111011
  · exact check_00000001011110011111
  · exact check_00000001011110110011
  · exact check_00000001011111110011
  · exact check_00000001011111111001
  · exact check_00000001100000010111
  · exact check_00000010100111111011
  · exact check_00000010111110000011
  · exact check_00000010111110110011
  · exact check_00000011011111111001
  · exact check_00000101111111110011
  · exact check_00000101111111111001
  · exact check_00001011111110011111
  · exact check_00001011111111111001
  · exact check_00001110011111111111
  · exact check_00001111111111001111
  · exact check_00001111111111110011
  · exact check_00010111111111111001
  · exact check_00011111111111101101
  · exact check_00110011111111111011
  · exact check_00111110111111111101
  · exact check_00111111111011011011
  · exact check_00111111111110101011
  · exact check_00111111111111010111

/-- **The 44 blocks**: for each entry of `blocks20Wide`, the center column is not, from any time `T` on, the block
`wordOf 20 bits`, read from any phase. -/
theorem center_not_blocks20Wide (e : (Nat × Nat) × (Nat × Nat × Nat × Nat)) (he : e ∈ blocks20Wide) (T shift : Nat)
    (h : ∀ t : Nat, T ≤ t → Rule30Prize.center t =
      (Rule30StripCertificateTable.wordOf e.1.1 e.1.2).getD ((t + shift) % e.1.1) false) : False :=
  center_not_bitGame _ _ _ _ _ (blocks20Wide_check e he) T shift fun t ht => by
    rw [h t ht, Rule30StripCertificateTable.wordOf_length]

/-- The same in the kit's form: none of the 44 blocks is an `EventuallyWord` of the center column. -/
theorem not_eventually_blocks20Wide (e : (Nat × Nat) × (Nat × Nat × Nat × Nat)) (he : e ∈ blocks20Wide) :
    ¬ Rule30StripCertificates.EventuallyWord (Rule30StripCertificateTable.wordOf e.1.1 e.1.2) :=
  bitGame_not_eventuallyWord _ _ _ _ _ (blocks20Wide_check e he)

end Rule30Open
