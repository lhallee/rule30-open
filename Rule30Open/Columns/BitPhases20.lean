module

public import Rule30Open.Columns.BitPhases

/-!
# The game decided phase by phase in the kernel excludes the 15 blocks of period 20 that need 13 or 14 cells

[BitPhases](BitPhases.md) checks the finite game in the kernel one phase at a time (`phaseCheck`), and
`center_not_phases_list` turns a list of blocks whose phases all pass into exclusions. Here the checks run on the
15 blocks of period 20 that the game excludes at width 13 or 14 and that neither the kit nor
[WallSets](WallSets.md) excludes.

* `blocksPhases20`: the blocks, each as its least rotation, with the width of their checks, and one theorem per
  phase of each.
* `center_not_blocksPhases20`, `not_eventually_blocksPhases20`: the center column of the single cell does not eventually
  repeat any of them, in any rotation, and in the kit's form `EventuallyWord`.

The natural-language argument is `BitPhases20.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

open Ruliology.CellularAutomata BitGame

open Rule30StripCertificateTable (wordOf)

set_option Elab.async false

set_option maxHeartbeats 0 in
theorem w00000000000000110001_0 : phaseCheck (wordOf 20 0b00000000000000110001) 14 0 1 300 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000000110001_1 : phaseCheck (wordOf 20 0b00000000000000110001) 14 0 3 300 1 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000000110001_2 : phaseCheck (wordOf 20 0b00000000000000110001) 14 0 1 300 2 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000000110001_3 : phaseCheck (wordOf 20 0b00000000000000110001) 14 0 1 300 3 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000000110001_4 : phaseCheck (wordOf 20 0b00000000000000110001) 14 0 1 300 4 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000000110001_5 : phaseCheck (wordOf 20 0b00000000000000110001) 14 0 1 300 5 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000000110001_6 : phaseCheck (wordOf 20 0b00000000000000110001) 14 0 1 300 6 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000000110001_7 : phaseCheck (wordOf 20 0b00000000000000110001) 14 0 1 300 7 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000000110001_8 : phaseCheck (wordOf 20 0b00000000000000110001) 14 0 1 300 8 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000000110001_9 : phaseCheck (wordOf 20 0b00000000000000110001) 14 0 1 300 9 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000000110001_10 : phaseCheck (wordOf 20 0b00000000000000110001) 14 0 1 300 10 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000000110001_11 : phaseCheck (wordOf 20 0b00000000000000110001) 14 0 1 300 11 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000000110001_12 : phaseCheck (wordOf 20 0b00000000000000110001) 14 0 1 300 12 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000000110001_13 : phaseCheck (wordOf 20 0b00000000000000110001) 14 0 1 300 13 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000000110001_14 : phaseCheck (wordOf 20 0b00000000000000110001) 14 0 0 300 14 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000000110001_15 : phaseCheck (wordOf 20 0b00000000000000110001) 14 0 0 300 15 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000000110001_16 : phaseCheck (wordOf 20 0b00000000000000110001) 14 0 2 300 16 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000000110001_17 : phaseCheck (wordOf 20 0b00000000000000110001) 14 0 1 300 17 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000000110001_18 : phaseCheck (wordOf 20 0b00000000000000110001) 14 0 1 300 18 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000000110001_19 : phaseCheck (wordOf 20 0b00000000000000110001) 14 0 0 300 19 = true := by
  decide +kernel

/-- Every phase of `00000000000000110001` at width 14. -/
theorem w00000000000000110001 : ∀ φ, φ < 20 → ∃ D rounds fuel,
    phaseCheck (wordOf 20 0b00000000000000110001) 14 D rounds fuel φ = true
  | 0, _ => ⟨0, 1, 300, w00000000000000110001_0⟩
  | 1, _ => ⟨0, 3, 300, w00000000000000110001_1⟩
  | 2, _ => ⟨0, 1, 300, w00000000000000110001_2⟩
  | 3, _ => ⟨0, 1, 300, w00000000000000110001_3⟩
  | 4, _ => ⟨0, 1, 300, w00000000000000110001_4⟩
  | 5, _ => ⟨0, 1, 300, w00000000000000110001_5⟩
  | 6, _ => ⟨0, 1, 300, w00000000000000110001_6⟩
  | 7, _ => ⟨0, 1, 300, w00000000000000110001_7⟩
  | 8, _ => ⟨0, 1, 300, w00000000000000110001_8⟩
  | 9, _ => ⟨0, 1, 300, w00000000000000110001_9⟩
  | 10, _ => ⟨0, 1, 300, w00000000000000110001_10⟩
  | 11, _ => ⟨0, 1, 300, w00000000000000110001_11⟩
  | 12, _ => ⟨0, 1, 300, w00000000000000110001_12⟩
  | 13, _ => ⟨0, 1, 300, w00000000000000110001_13⟩
  | 14, _ => ⟨0, 0, 300, w00000000000000110001_14⟩
  | 15, _ => ⟨0, 0, 300, w00000000000000110001_15⟩
  | 16, _ => ⟨0, 2, 300, w00000000000000110001_16⟩
  | 17, _ => ⟨0, 1, 300, w00000000000000110001_17⟩
  | 18, _ => ⟨0, 1, 300, w00000000000000110001_18⟩
  | 19, _ => ⟨0, 0, 300, w00000000000000110001_19⟩
  | _ + 20, h => absurd h (by omega)

set_option maxHeartbeats 0 in
theorem w00000000000001000001_0 : phaseCheck (wordOf 20 0b00000000000001000001) 13 0 1 300 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000001000001_1 : phaseCheck (wordOf 20 0b00000000000001000001) 13 0 2 300 1 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000001000001_2 : phaseCheck (wordOf 20 0b00000000000001000001) 13 0 1 300 2 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000001000001_3 : phaseCheck (wordOf 20 0b00000000000001000001) 13 0 1 300 3 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000001000001_4 : phaseCheck (wordOf 20 0b00000000000001000001) 13 0 1 300 4 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000001000001_5 : phaseCheck (wordOf 20 0b00000000000001000001) 13 0 1 300 5 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000001000001_6 : phaseCheck (wordOf 20 0b00000000000001000001) 13 0 1 300 6 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000001000001_7 : phaseCheck (wordOf 20 0b00000000000001000001) 13 0 1 300 7 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000001000001_8 : phaseCheck (wordOf 20 0b00000000000001000001) 13 0 1 300 8 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000001000001_9 : phaseCheck (wordOf 20 0b00000000000001000001) 13 0 1 300 9 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000001000001_10 : phaseCheck (wordOf 20 0b00000000000001000001) 13 0 1 300 10 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000001000001_11 : phaseCheck (wordOf 20 0b00000000000001000001) 13 0 1 300 11 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000001000001_12 : phaseCheck (wordOf 20 0b00000000000001000001) 13 0 1 300 12 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000001000001_13 : phaseCheck (wordOf 20 0b00000000000001000001) 13 0 0 300 13 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000001000001_14 : phaseCheck (wordOf 20 0b00000000000001000001) 13 0 1 300 14 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000001000001_15 : phaseCheck (wordOf 20 0b00000000000001000001) 13 0 1 300 15 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000001000001_16 : phaseCheck (wordOf 20 0b00000000000001000001) 13 0 1 300 16 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000001000001_17 : phaseCheck (wordOf 20 0b00000000000001000001) 13 0 1 300 17 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000001000001_18 : phaseCheck (wordOf 20 0b00000000000001000001) 13 0 1 300 18 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000001000001_19 : phaseCheck (wordOf 20 0b00000000000001000001) 13 0 0 300 19 = true := by
  decide +kernel

/-- Every phase of `00000000000001000001` at width 13. -/
theorem w00000000000001000001 : ∀ φ, φ < 20 → ∃ D rounds fuel,
    phaseCheck (wordOf 20 0b00000000000001000001) 13 D rounds fuel φ = true
  | 0, _ => ⟨0, 1, 300, w00000000000001000001_0⟩
  | 1, _ => ⟨0, 2, 300, w00000000000001000001_1⟩
  | 2, _ => ⟨0, 1, 300, w00000000000001000001_2⟩
  | 3, _ => ⟨0, 1, 300, w00000000000001000001_3⟩
  | 4, _ => ⟨0, 1, 300, w00000000000001000001_4⟩
  | 5, _ => ⟨0, 1, 300, w00000000000001000001_5⟩
  | 6, _ => ⟨0, 1, 300, w00000000000001000001_6⟩
  | 7, _ => ⟨0, 1, 300, w00000000000001000001_7⟩
  | 8, _ => ⟨0, 1, 300, w00000000000001000001_8⟩
  | 9, _ => ⟨0, 1, 300, w00000000000001000001_9⟩
  | 10, _ => ⟨0, 1, 300, w00000000000001000001_10⟩
  | 11, _ => ⟨0, 1, 300, w00000000000001000001_11⟩
  | 12, _ => ⟨0, 1, 300, w00000000000001000001_12⟩
  | 13, _ => ⟨0, 0, 300, w00000000000001000001_13⟩
  | 14, _ => ⟨0, 1, 300, w00000000000001000001_14⟩
  | 15, _ => ⟨0, 1, 300, w00000000000001000001_15⟩
  | 16, _ => ⟨0, 1, 300, w00000000000001000001_16⟩
  | 17, _ => ⟨0, 1, 300, w00000000000001000001_17⟩
  | 18, _ => ⟨0, 1, 300, w00000000000001000001_18⟩
  | 19, _ => ⟨0, 0, 300, w00000000000001000001_19⟩
  | _ + 20, h => absurd h (by omega)

set_option maxHeartbeats 0 in
theorem w00000000000001010001_0 : phaseCheck (wordOf 20 0b00000000000001010001) 14 0 1 300 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000001010001_1 : phaseCheck (wordOf 20 0b00000000000001010001) 14 0 1 300 1 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000001010001_2 : phaseCheck (wordOf 20 0b00000000000001010001) 14 0 2 300 2 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000001010001_3 : phaseCheck (wordOf 20 0b00000000000001010001) 14 0 2 300 3 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000001010001_4 : phaseCheck (wordOf 20 0b00000000000001010001) 14 0 2 300 4 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000001010001_5 : phaseCheck (wordOf 20 0b00000000000001010001) 14 0 2 300 5 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000001010001_6 : phaseCheck (wordOf 20 0b00000000000001010001) 14 0 2 300 6 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000001010001_7 : phaseCheck (wordOf 20 0b00000000000001010001) 14 0 2 300 7 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000001010001_8 : phaseCheck (wordOf 20 0b00000000000001010001) 14 0 1 300 8 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000001010001_9 : phaseCheck (wordOf 20 0b00000000000001010001) 14 0 1 300 9 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000001010001_10 : phaseCheck (wordOf 20 0b00000000000001010001) 14 0 1 300 10 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000001010001_11 : phaseCheck (wordOf 20 0b00000000000001010001) 14 0 2 300 11 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000001010001_12 : phaseCheck (wordOf 20 0b00000000000001010001) 14 0 2 300 12 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000001010001_13 : phaseCheck (wordOf 20 0b00000000000001010001) 14 0 0 300 13 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000001010001_14 : phaseCheck (wordOf 20 0b00000000000001010001) 14 0 1 300 14 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000001010001_15 : phaseCheck (wordOf 20 0b00000000000001010001) 14 0 0 300 15 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000001010001_16 : phaseCheck (wordOf 20 0b00000000000001010001) 14 0 1 300 16 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000001010001_17 : phaseCheck (wordOf 20 0b00000000000001010001) 14 0 1 300 17 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000001010001_18 : phaseCheck (wordOf 20 0b00000000000001010001) 14 0 2 300 18 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000001010001_19 : phaseCheck (wordOf 20 0b00000000000001010001) 14 0 0 300 19 = true := by
  decide +kernel

/-- Every phase of `00000000000001010001` at width 14. -/
theorem w00000000000001010001 : ∀ φ, φ < 20 → ∃ D rounds fuel,
    phaseCheck (wordOf 20 0b00000000000001010001) 14 D rounds fuel φ = true
  | 0, _ => ⟨0, 1, 300, w00000000000001010001_0⟩
  | 1, _ => ⟨0, 1, 300, w00000000000001010001_1⟩
  | 2, _ => ⟨0, 2, 300, w00000000000001010001_2⟩
  | 3, _ => ⟨0, 2, 300, w00000000000001010001_3⟩
  | 4, _ => ⟨0, 2, 300, w00000000000001010001_4⟩
  | 5, _ => ⟨0, 2, 300, w00000000000001010001_5⟩
  | 6, _ => ⟨0, 2, 300, w00000000000001010001_6⟩
  | 7, _ => ⟨0, 2, 300, w00000000000001010001_7⟩
  | 8, _ => ⟨0, 1, 300, w00000000000001010001_8⟩
  | 9, _ => ⟨0, 1, 300, w00000000000001010001_9⟩
  | 10, _ => ⟨0, 1, 300, w00000000000001010001_10⟩
  | 11, _ => ⟨0, 2, 300, w00000000000001010001_11⟩
  | 12, _ => ⟨0, 2, 300, w00000000000001010001_12⟩
  | 13, _ => ⟨0, 0, 300, w00000000000001010001_13⟩
  | 14, _ => ⟨0, 1, 300, w00000000000001010001_14⟩
  | 15, _ => ⟨0, 0, 300, w00000000000001010001_15⟩
  | 16, _ => ⟨0, 1, 300, w00000000000001010001_16⟩
  | 17, _ => ⟨0, 1, 300, w00000000000001010001_17⟩
  | 18, _ => ⟨0, 2, 300, w00000000000001010001_18⟩
  | 19, _ => ⟨0, 0, 300, w00000000000001010001_19⟩
  | _ + 20, h => absurd h (by omega)

set_option maxHeartbeats 0 in
theorem w00000000000011000101_0 : phaseCheck (wordOf 20 0b00000000000011000101) 14 0 1 300 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000011000101_1 : phaseCheck (wordOf 20 0b00000000000011000101) 14 0 2 300 1 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000011000101_2 : phaseCheck (wordOf 20 0b00000000000011000101) 14 0 3 300 2 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000011000101_3 : phaseCheck (wordOf 20 0b00000000000011000101) 14 0 3 300 3 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000011000101_4 : phaseCheck (wordOf 20 0b00000000000011000101) 14 0 3 300 4 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000011000101_5 : phaseCheck (wordOf 20 0b00000000000011000101) 14 0 2 300 5 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000011000101_6 : phaseCheck (wordOf 20 0b00000000000011000101) 14 0 1 300 6 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000011000101_7 : phaseCheck (wordOf 20 0b00000000000011000101) 14 0 1 300 7 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000011000101_8 : phaseCheck (wordOf 20 0b00000000000011000101) 14 0 1 300 8 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000011000101_9 : phaseCheck (wordOf 20 0b00000000000011000101) 14 0 1 300 9 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000011000101_10 : phaseCheck (wordOf 20 0b00000000000011000101) 14 0 1 300 10 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000011000101_11 : phaseCheck (wordOf 20 0b00000000000011000101) 14 0 1 300 11 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000011000101_12 : phaseCheck (wordOf 20 0b00000000000011000101) 14 0 0 300 12 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000011000101_13 : phaseCheck (wordOf 20 0b00000000000011000101) 14 0 0 300 13 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000011000101_14 : phaseCheck (wordOf 20 0b00000000000011000101) 14 0 1 300 14 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000011000101_15 : phaseCheck (wordOf 20 0b00000000000011000101) 14 0 1 300 15 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000011000101_16 : phaseCheck (wordOf 20 0b00000000000011000101) 14 0 1 300 16 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000011000101_17 : phaseCheck (wordOf 20 0b00000000000011000101) 14 0 0 300 17 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000011000101_18 : phaseCheck (wordOf 20 0b00000000000011000101) 14 0 1 300 18 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000000011000101_19 : phaseCheck (wordOf 20 0b00000000000011000101) 14 0 0 300 19 = true := by
  decide +kernel

/-- Every phase of `00000000000011000101` at width 14. -/
theorem w00000000000011000101 : ∀ φ, φ < 20 → ∃ D rounds fuel,
    phaseCheck (wordOf 20 0b00000000000011000101) 14 D rounds fuel φ = true
  | 0, _ => ⟨0, 1, 300, w00000000000011000101_0⟩
  | 1, _ => ⟨0, 2, 300, w00000000000011000101_1⟩
  | 2, _ => ⟨0, 3, 300, w00000000000011000101_2⟩
  | 3, _ => ⟨0, 3, 300, w00000000000011000101_3⟩
  | 4, _ => ⟨0, 3, 300, w00000000000011000101_4⟩
  | 5, _ => ⟨0, 2, 300, w00000000000011000101_5⟩
  | 6, _ => ⟨0, 1, 300, w00000000000011000101_6⟩
  | 7, _ => ⟨0, 1, 300, w00000000000011000101_7⟩
  | 8, _ => ⟨0, 1, 300, w00000000000011000101_8⟩
  | 9, _ => ⟨0, 1, 300, w00000000000011000101_9⟩
  | 10, _ => ⟨0, 1, 300, w00000000000011000101_10⟩
  | 11, _ => ⟨0, 1, 300, w00000000000011000101_11⟩
  | 12, _ => ⟨0, 0, 300, w00000000000011000101_12⟩
  | 13, _ => ⟨0, 0, 300, w00000000000011000101_13⟩
  | 14, _ => ⟨0, 1, 300, w00000000000011000101_14⟩
  | 15, _ => ⟨0, 1, 300, w00000000000011000101_15⟩
  | 16, _ => ⟨0, 1, 300, w00000000000011000101_16⟩
  | 17, _ => ⟨0, 0, 300, w00000000000011000101_17⟩
  | 18, _ => ⟨0, 1, 300, w00000000000011000101_18⟩
  | 19, _ => ⟨0, 0, 300, w00000000000011000101_19⟩
  | _ + 20, h => absurd h (by omega)

set_option maxHeartbeats 0 in
theorem w00000000001100101111_0 : phaseCheck (wordOf 20 0b00000000001100101111) 14 0 1 300 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000001100101111_1 : phaseCheck (wordOf 20 0b00000000001100101111) 14 0 2 300 1 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000001100101111_2 : phaseCheck (wordOf 20 0b00000000001100101111) 14 0 2 300 2 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000001100101111_3 : phaseCheck (wordOf 20 0b00000000001100101111) 14 0 2 300 3 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000001100101111_4 : phaseCheck (wordOf 20 0b00000000001100101111) 14 0 1 300 4 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000001100101111_5 : phaseCheck (wordOf 20 0b00000000001100101111) 14 0 1 300 5 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000001100101111_6 : phaseCheck (wordOf 20 0b00000000001100101111) 14 0 1 300 6 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000001100101111_7 : phaseCheck (wordOf 20 0b00000000001100101111) 14 0 1 300 7 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000001100101111_8 : phaseCheck (wordOf 20 0b00000000001100101111) 14 0 1 300 8 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000001100101111_9 : phaseCheck (wordOf 20 0b00000000001100101111) 14 0 1 300 9 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000001100101111_10 : phaseCheck (wordOf 20 0b00000000001100101111) 14 0 0 300 10 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000001100101111_11 : phaseCheck (wordOf 20 0b00000000001100101111) 14 0 0 300 11 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000001100101111_12 : phaseCheck (wordOf 20 0b00000000001100101111) 14 0 1 300 12 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000001100101111_13 : phaseCheck (wordOf 20 0b00000000001100101111) 14 0 1 300 13 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000001100101111_14 : phaseCheck (wordOf 20 0b00000000001100101111) 14 0 0 300 14 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000001100101111_15 : phaseCheck (wordOf 20 0b00000000001100101111) 14 0 1 300 15 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000001100101111_16 : phaseCheck (wordOf 20 0b00000000001100101111) 14 0 0 300 16 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000001100101111_17 : phaseCheck (wordOf 20 0b00000000001100101111) 14 0 0 300 17 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000001100101111_18 : phaseCheck (wordOf 20 0b00000000001100101111) 14 0 0 300 18 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000001100101111_19 : phaseCheck (wordOf 20 0b00000000001100101111) 14 0 0 300 19 = true := by
  decide +kernel

/-- Every phase of `00000000001100101111` at width 14. -/
theorem w00000000001100101111 : ∀ φ, φ < 20 → ∃ D rounds fuel,
    phaseCheck (wordOf 20 0b00000000001100101111) 14 D rounds fuel φ = true
  | 0, _ => ⟨0, 1, 300, w00000000001100101111_0⟩
  | 1, _ => ⟨0, 2, 300, w00000000001100101111_1⟩
  | 2, _ => ⟨0, 2, 300, w00000000001100101111_2⟩
  | 3, _ => ⟨0, 2, 300, w00000000001100101111_3⟩
  | 4, _ => ⟨0, 1, 300, w00000000001100101111_4⟩
  | 5, _ => ⟨0, 1, 300, w00000000001100101111_5⟩
  | 6, _ => ⟨0, 1, 300, w00000000001100101111_6⟩
  | 7, _ => ⟨0, 1, 300, w00000000001100101111_7⟩
  | 8, _ => ⟨0, 1, 300, w00000000001100101111_8⟩
  | 9, _ => ⟨0, 1, 300, w00000000001100101111_9⟩
  | 10, _ => ⟨0, 0, 300, w00000000001100101111_10⟩
  | 11, _ => ⟨0, 0, 300, w00000000001100101111_11⟩
  | 12, _ => ⟨0, 1, 300, w00000000001100101111_12⟩
  | 13, _ => ⟨0, 1, 300, w00000000001100101111_13⟩
  | 14, _ => ⟨0, 0, 300, w00000000001100101111_14⟩
  | 15, _ => ⟨0, 1, 300, w00000000001100101111_15⟩
  | 16, _ => ⟨0, 0, 300, w00000000001100101111_16⟩
  | 17, _ => ⟨0, 0, 300, w00000000001100101111_17⟩
  | 18, _ => ⟨0, 0, 300, w00000000001100101111_18⟩
  | 19, _ => ⟨0, 0, 300, w00000000001100101111_19⟩
  | _ + 20, h => absurd h (by omega)

set_option maxHeartbeats 0 in
theorem w00000000110001111011_0 : phaseCheck (wordOf 20 0b00000000110001111011) 13 0 1 300 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000110001111011_1 : phaseCheck (wordOf 20 0b00000000110001111011) 13 0 1 300 1 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000110001111011_2 : phaseCheck (wordOf 20 0b00000000110001111011) 13 0 1 300 2 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000110001111011_3 : phaseCheck (wordOf 20 0b00000000110001111011) 13 0 1 300 3 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000110001111011_4 : phaseCheck (wordOf 20 0b00000000110001111011) 13 0 1 300 4 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000110001111011_5 : phaseCheck (wordOf 20 0b00000000110001111011) 13 0 1 300 5 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000110001111011_6 : phaseCheck (wordOf 20 0b00000000110001111011) 13 0 1 300 6 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000110001111011_7 : phaseCheck (wordOf 20 0b00000000110001111011) 13 0 1 300 7 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000110001111011_8 : phaseCheck (wordOf 20 0b00000000110001111011) 13 0 0 300 8 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000110001111011_9 : phaseCheck (wordOf 20 0b00000000110001111011) 13 0 0 300 9 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000110001111011_10 : phaseCheck (wordOf 20 0b00000000110001111011) 13 0 1 300 10 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000110001111011_11 : phaseCheck (wordOf 20 0b00000000110001111011) 13 0 1 300 11 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000110001111011_12 : phaseCheck (wordOf 20 0b00000000110001111011) 13 0 1 300 12 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000110001111011_13 : phaseCheck (wordOf 20 0b00000000110001111011) 13 0 0 300 13 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000110001111011_14 : phaseCheck (wordOf 20 0b00000000110001111011) 13 0 0 300 14 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000110001111011_15 : phaseCheck (wordOf 20 0b00000000110001111011) 13 0 0 300 15 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000110001111011_16 : phaseCheck (wordOf 20 0b00000000110001111011) 13 0 0 300 16 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000110001111011_17 : phaseCheck (wordOf 20 0b00000000110001111011) 13 0 1 300 17 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000110001111011_18 : phaseCheck (wordOf 20 0b00000000110001111011) 13 0 0 300 18 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000000110001111011_19 : phaseCheck (wordOf 20 0b00000000110001111011) 13 0 0 300 19 = true := by
  decide +kernel

/-- Every phase of `00000000110001111011` at width 13. -/
theorem w00000000110001111011 : ∀ φ, φ < 20 → ∃ D rounds fuel,
    phaseCheck (wordOf 20 0b00000000110001111011) 13 D rounds fuel φ = true
  | 0, _ => ⟨0, 1, 300, w00000000110001111011_0⟩
  | 1, _ => ⟨0, 1, 300, w00000000110001111011_1⟩
  | 2, _ => ⟨0, 1, 300, w00000000110001111011_2⟩
  | 3, _ => ⟨0, 1, 300, w00000000110001111011_3⟩
  | 4, _ => ⟨0, 1, 300, w00000000110001111011_4⟩
  | 5, _ => ⟨0, 1, 300, w00000000110001111011_5⟩
  | 6, _ => ⟨0, 1, 300, w00000000110001111011_6⟩
  | 7, _ => ⟨0, 1, 300, w00000000110001111011_7⟩
  | 8, _ => ⟨0, 0, 300, w00000000110001111011_8⟩
  | 9, _ => ⟨0, 0, 300, w00000000110001111011_9⟩
  | 10, _ => ⟨0, 1, 300, w00000000110001111011_10⟩
  | 11, _ => ⟨0, 1, 300, w00000000110001111011_11⟩
  | 12, _ => ⟨0, 1, 300, w00000000110001111011_12⟩
  | 13, _ => ⟨0, 0, 300, w00000000110001111011_13⟩
  | 14, _ => ⟨0, 0, 300, w00000000110001111011_14⟩
  | 15, _ => ⟨0, 0, 300, w00000000110001111011_15⟩
  | 16, _ => ⟨0, 0, 300, w00000000110001111011_16⟩
  | 17, _ => ⟨0, 1, 300, w00000000110001111011_17⟩
  | 18, _ => ⟨0, 0, 300, w00000000110001111011_18⟩
  | 19, _ => ⟨0, 0, 300, w00000000110001111011_19⟩
  | _ + 20, h => absurd h (by omega)

set_option maxHeartbeats 0 in
theorem w00000001011111100011_0 : phaseCheck (wordOf 20 0b00000001011111100011) 13 0 1 300 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000001011111100011_1 : phaseCheck (wordOf 20 0b00000001011111100011) 13 0 1 300 1 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000001011111100011_2 : phaseCheck (wordOf 20 0b00000001011111100011) 13 0 1 300 2 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000001011111100011_3 : phaseCheck (wordOf 20 0b00000001011111100011) 13 0 1 300 3 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000001011111100011_4 : phaseCheck (wordOf 20 0b00000001011111100011) 13 0 1 300 4 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000001011111100011_5 : phaseCheck (wordOf 20 0b00000001011111100011) 13 0 1 300 5 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000001011111100011_6 : phaseCheck (wordOf 20 0b00000001011111100011) 13 0 1 300 6 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000001011111100011_7 : phaseCheck (wordOf 20 0b00000001011111100011) 13 0 0 300 7 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000001011111100011_8 : phaseCheck (wordOf 20 0b00000001011111100011) 13 0 1 300 8 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000001011111100011_9 : phaseCheck (wordOf 20 0b00000001011111100011) 13 0 0 300 9 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000001011111100011_10 : phaseCheck (wordOf 20 0b00000001011111100011) 13 0 0 300 10 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000001011111100011_11 : phaseCheck (wordOf 20 0b00000001011111100011) 13 0 0 300 11 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000001011111100011_12 : phaseCheck (wordOf 20 0b00000001011111100011) 13 0 0 300 12 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000001011111100011_13 : phaseCheck (wordOf 20 0b00000001011111100011) 13 0 0 300 13 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000001011111100011_14 : phaseCheck (wordOf 20 0b00000001011111100011) 13 0 0 300 14 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000001011111100011_15 : phaseCheck (wordOf 20 0b00000001011111100011) 13 0 2 300 15 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000001011111100011_16 : phaseCheck (wordOf 20 0b00000001011111100011) 13 0 1 300 16 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000001011111100011_17 : phaseCheck (wordOf 20 0b00000001011111100011) 13 0 1 300 17 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000001011111100011_18 : phaseCheck (wordOf 20 0b00000001011111100011) 13 0 0 300 18 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000001011111100011_19 : phaseCheck (wordOf 20 0b00000001011111100011) 13 0 0 300 19 = true := by
  decide +kernel

/-- Every phase of `00000001011111100011` at width 13. -/
theorem w00000001011111100011 : ∀ φ, φ < 20 → ∃ D rounds fuel,
    phaseCheck (wordOf 20 0b00000001011111100011) 13 D rounds fuel φ = true
  | 0, _ => ⟨0, 1, 300, w00000001011111100011_0⟩
  | 1, _ => ⟨0, 1, 300, w00000001011111100011_1⟩
  | 2, _ => ⟨0, 1, 300, w00000001011111100011_2⟩
  | 3, _ => ⟨0, 1, 300, w00000001011111100011_3⟩
  | 4, _ => ⟨0, 1, 300, w00000001011111100011_4⟩
  | 5, _ => ⟨0, 1, 300, w00000001011111100011_5⟩
  | 6, _ => ⟨0, 1, 300, w00000001011111100011_6⟩
  | 7, _ => ⟨0, 0, 300, w00000001011111100011_7⟩
  | 8, _ => ⟨0, 1, 300, w00000001011111100011_8⟩
  | 9, _ => ⟨0, 0, 300, w00000001011111100011_9⟩
  | 10, _ => ⟨0, 0, 300, w00000001011111100011_10⟩
  | 11, _ => ⟨0, 0, 300, w00000001011111100011_11⟩
  | 12, _ => ⟨0, 0, 300, w00000001011111100011_12⟩
  | 13, _ => ⟨0, 0, 300, w00000001011111100011_13⟩
  | 14, _ => ⟨0, 0, 300, w00000001011111100011_14⟩
  | 15, _ => ⟨0, 2, 300, w00000001011111100011_15⟩
  | 16, _ => ⟨0, 1, 300, w00000001011111100011_16⟩
  | 17, _ => ⟨0, 1, 300, w00000001011111100011_17⟩
  | 18, _ => ⟨0, 0, 300, w00000001011111100011_18⟩
  | 19, _ => ⟨0, 0, 300, w00000001011111100011_19⟩
  | _ + 20, h => absurd h (by omega)

set_option maxHeartbeats 0 in
theorem w00000001101111111011_0 : phaseCheck (wordOf 20 0b00000001101111111011) 14 0 2 300 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000001101111111011_1 : phaseCheck (wordOf 20 0b00000001101111111011) 14 0 1 300 1 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000001101111111011_2 : phaseCheck (wordOf 20 0b00000001101111111011) 14 0 1 300 2 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000001101111111011_3 : phaseCheck (wordOf 20 0b00000001101111111011) 14 0 1 300 3 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000001101111111011_4 : phaseCheck (wordOf 20 0b00000001101111111011) 14 0 1 300 4 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000001101111111011_5 : phaseCheck (wordOf 20 0b00000001101111111011) 14 0 1 300 5 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000001101111111011_6 : phaseCheck (wordOf 20 0b00000001101111111011) 14 0 1 300 6 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000001101111111011_7 : phaseCheck (wordOf 20 0b00000001101111111011) 14 0 0 300 7 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000001101111111011_8 : phaseCheck (wordOf 20 0b00000001101111111011) 14 0 0 300 8 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000001101111111011_9 : phaseCheck (wordOf 20 0b00000001101111111011) 14 0 2 300 9 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000001101111111011_10 : phaseCheck (wordOf 20 0b00000001101111111011) 14 0 0 300 10 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000001101111111011_11 : phaseCheck (wordOf 20 0b00000001101111111011) 14 0 0 300 11 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000001101111111011_12 : phaseCheck (wordOf 20 0b00000001101111111011) 14 0 0 300 12 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000001101111111011_13 : phaseCheck (wordOf 20 0b00000001101111111011) 14 0 0 300 13 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000001101111111011_14 : phaseCheck (wordOf 20 0b00000001101111111011) 14 0 0 300 14 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000001101111111011_15 : phaseCheck (wordOf 20 0b00000001101111111011) 14 0 0 300 15 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000001101111111011_16 : phaseCheck (wordOf 20 0b00000001101111111011) 14 0 0 300 16 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000001101111111011_17 : phaseCheck (wordOf 20 0b00000001101111111011) 14 0 1 300 17 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000001101111111011_18 : phaseCheck (wordOf 20 0b00000001101111111011) 14 0 0 300 18 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000001101111111011_19 : phaseCheck (wordOf 20 0b00000001101111111011) 14 0 0 300 19 = true := by
  decide +kernel

/-- Every phase of `00000001101111111011` at width 14. -/
theorem w00000001101111111011 : ∀ φ, φ < 20 → ∃ D rounds fuel,
    phaseCheck (wordOf 20 0b00000001101111111011) 14 D rounds fuel φ = true
  | 0, _ => ⟨0, 2, 300, w00000001101111111011_0⟩
  | 1, _ => ⟨0, 1, 300, w00000001101111111011_1⟩
  | 2, _ => ⟨0, 1, 300, w00000001101111111011_2⟩
  | 3, _ => ⟨0, 1, 300, w00000001101111111011_3⟩
  | 4, _ => ⟨0, 1, 300, w00000001101111111011_4⟩
  | 5, _ => ⟨0, 1, 300, w00000001101111111011_5⟩
  | 6, _ => ⟨0, 1, 300, w00000001101111111011_6⟩
  | 7, _ => ⟨0, 0, 300, w00000001101111111011_7⟩
  | 8, _ => ⟨0, 0, 300, w00000001101111111011_8⟩
  | 9, _ => ⟨0, 2, 300, w00000001101111111011_9⟩
  | 10, _ => ⟨0, 0, 300, w00000001101111111011_10⟩
  | 11, _ => ⟨0, 0, 300, w00000001101111111011_11⟩
  | 12, _ => ⟨0, 0, 300, w00000001101111111011_12⟩
  | 13, _ => ⟨0, 0, 300, w00000001101111111011_13⟩
  | 14, _ => ⟨0, 0, 300, w00000001101111111011_14⟩
  | 15, _ => ⟨0, 0, 300, w00000001101111111011_15⟩
  | 16, _ => ⟨0, 0, 300, w00000001101111111011_16⟩
  | 17, _ => ⟨0, 1, 300, w00000001101111111011_17⟩
  | 18, _ => ⟨0, 0, 300, w00000001101111111011_18⟩
  | 19, _ => ⟨0, 0, 300, w00000001101111111011_19⟩
  | _ + 20, h => absurd h (by omega)

set_option maxHeartbeats 0 in
theorem w00000101111111001001_0 : phaseCheck (wordOf 20 0b00000101111111001001) 14 0 1 300 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000101111111001001_1 : phaseCheck (wordOf 20 0b00000101111111001001) 14 0 3 300 1 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000101111111001001_2 : phaseCheck (wordOf 20 0b00000101111111001001) 14 0 2 300 2 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000101111111001001_3 : phaseCheck (wordOf 20 0b00000101111111001001) 14 0 1 300 3 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000101111111001001_4 : phaseCheck (wordOf 20 0b00000101111111001001) 14 0 1 300 4 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000101111111001001_5 : phaseCheck (wordOf 20 0b00000101111111001001) 14 0 0 300 5 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000101111111001001_6 : phaseCheck (wordOf 20 0b00000101111111001001) 14 0 1 300 6 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000101111111001001_7 : phaseCheck (wordOf 20 0b00000101111111001001) 14 0 0 300 7 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000101111111001001_8 : phaseCheck (wordOf 20 0b00000101111111001001) 14 0 0 300 8 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000101111111001001_9 : phaseCheck (wordOf 20 0b00000101111111001001) 14 0 0 300 9 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000101111111001001_10 : phaseCheck (wordOf 20 0b00000101111111001001) 14 0 0 300 10 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000101111111001001_11 : phaseCheck (wordOf 20 0b00000101111111001001) 14 0 0 300 11 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000101111111001001_12 : phaseCheck (wordOf 20 0b00000101111111001001) 14 0 0 300 12 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000101111111001001_13 : phaseCheck (wordOf 20 0b00000101111111001001) 14 0 0 300 13 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000101111111001001_14 : phaseCheck (wordOf 20 0b00000101111111001001) 14 0 3 300 14 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000101111111001001_15 : phaseCheck (wordOf 20 0b00000101111111001001) 14 0 1 300 15 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000101111111001001_16 : phaseCheck (wordOf 20 0b00000101111111001001) 14 0 0 300 16 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000101111111001001_17 : phaseCheck (wordOf 20 0b00000101111111001001) 14 0 1 300 17 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000101111111001001_18 : phaseCheck (wordOf 20 0b00000101111111001001) 14 0 3 300 18 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000101111111001001_19 : phaseCheck (wordOf 20 0b00000101111111001001) 14 0 0 300 19 = true := by
  decide +kernel

/-- Every phase of `00000101111111001001` at width 14. -/
theorem w00000101111111001001 : ∀ φ, φ < 20 → ∃ D rounds fuel,
    phaseCheck (wordOf 20 0b00000101111111001001) 14 D rounds fuel φ = true
  | 0, _ => ⟨0, 1, 300, w00000101111111001001_0⟩
  | 1, _ => ⟨0, 3, 300, w00000101111111001001_1⟩
  | 2, _ => ⟨0, 2, 300, w00000101111111001001_2⟩
  | 3, _ => ⟨0, 1, 300, w00000101111111001001_3⟩
  | 4, _ => ⟨0, 1, 300, w00000101111111001001_4⟩
  | 5, _ => ⟨0, 0, 300, w00000101111111001001_5⟩
  | 6, _ => ⟨0, 1, 300, w00000101111111001001_6⟩
  | 7, _ => ⟨0, 0, 300, w00000101111111001001_7⟩
  | 8, _ => ⟨0, 0, 300, w00000101111111001001_8⟩
  | 9, _ => ⟨0, 0, 300, w00000101111111001001_9⟩
  | 10, _ => ⟨0, 0, 300, w00000101111111001001_10⟩
  | 11, _ => ⟨0, 0, 300, w00000101111111001001_11⟩
  | 12, _ => ⟨0, 0, 300, w00000101111111001001_12⟩
  | 13, _ => ⟨0, 0, 300, w00000101111111001001_13⟩
  | 14, _ => ⟨0, 3, 300, w00000101111111001001_14⟩
  | 15, _ => ⟨0, 1, 300, w00000101111111001001_15⟩
  | 16, _ => ⟨0, 0, 300, w00000101111111001001_16⟩
  | 17, _ => ⟨0, 1, 300, w00000101111111001001_17⟩
  | 18, _ => ⟨0, 3, 300, w00000101111111001001_18⟩
  | 19, _ => ⟨0, 0, 300, w00000101111111001001_19⟩
  | _ + 20, h => absurd h (by omega)

set_option maxHeartbeats 0 in
theorem w00000101111111110111_0 : phaseCheck (wordOf 20 0b00000101111111110111) 14 0 1 300 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000101111111110111_1 : phaseCheck (wordOf 20 0b00000101111111110111) 14 0 2 300 1 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000101111111110111_2 : phaseCheck (wordOf 20 0b00000101111111110111) 14 0 2 300 2 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000101111111110111_3 : phaseCheck (wordOf 20 0b00000101111111110111) 14 0 1 300 3 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000101111111110111_4 : phaseCheck (wordOf 20 0b00000101111111110111) 14 0 3 300 4 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000101111111110111_5 : phaseCheck (wordOf 20 0b00000101111111110111) 14 0 0 300 5 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000101111111110111_6 : phaseCheck (wordOf 20 0b00000101111111110111) 14 0 2 300 6 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000101111111110111_7 : phaseCheck (wordOf 20 0b00000101111111110111) 14 0 0 300 7 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000101111111110111_8 : phaseCheck (wordOf 20 0b00000101111111110111) 14 0 0 300 8 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000101111111110111_9 : phaseCheck (wordOf 20 0b00000101111111110111) 14 0 0 300 9 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000101111111110111_10 : phaseCheck (wordOf 20 0b00000101111111110111) 14 0 0 300 10 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000101111111110111_11 : phaseCheck (wordOf 20 0b00000101111111110111) 14 0 0 300 11 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000101111111110111_12 : phaseCheck (wordOf 20 0b00000101111111110111) 14 0 0 300 12 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000101111111110111_13 : phaseCheck (wordOf 20 0b00000101111111110111) 14 0 0 300 13 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000101111111110111_14 : phaseCheck (wordOf 20 0b00000101111111110111) 14 0 0 300 14 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000101111111110111_15 : phaseCheck (wordOf 20 0b00000101111111110111) 14 0 0 300 15 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000101111111110111_16 : phaseCheck (wordOf 20 0b00000101111111110111) 14 0 1 300 16 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000101111111110111_17 : phaseCheck (wordOf 20 0b00000101111111110111) 14 0 0 300 17 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000101111111110111_18 : phaseCheck (wordOf 20 0b00000101111111110111) 14 0 0 300 18 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00000101111111110111_19 : phaseCheck (wordOf 20 0b00000101111111110111) 14 0 0 300 19 = true := by
  decide +kernel

/-- Every phase of `00000101111111110111` at width 14. -/
theorem w00000101111111110111 : ∀ φ, φ < 20 → ∃ D rounds fuel,
    phaseCheck (wordOf 20 0b00000101111111110111) 14 D rounds fuel φ = true
  | 0, _ => ⟨0, 1, 300, w00000101111111110111_0⟩
  | 1, _ => ⟨0, 2, 300, w00000101111111110111_1⟩
  | 2, _ => ⟨0, 2, 300, w00000101111111110111_2⟩
  | 3, _ => ⟨0, 1, 300, w00000101111111110111_3⟩
  | 4, _ => ⟨0, 3, 300, w00000101111111110111_4⟩
  | 5, _ => ⟨0, 0, 300, w00000101111111110111_5⟩
  | 6, _ => ⟨0, 2, 300, w00000101111111110111_6⟩
  | 7, _ => ⟨0, 0, 300, w00000101111111110111_7⟩
  | 8, _ => ⟨0, 0, 300, w00000101111111110111_8⟩
  | 9, _ => ⟨0, 0, 300, w00000101111111110111_9⟩
  | 10, _ => ⟨0, 0, 300, w00000101111111110111_10⟩
  | 11, _ => ⟨0, 0, 300, w00000101111111110111_11⟩
  | 12, _ => ⟨0, 0, 300, w00000101111111110111_12⟩
  | 13, _ => ⟨0, 0, 300, w00000101111111110111_13⟩
  | 14, _ => ⟨0, 0, 300, w00000101111111110111_14⟩
  | 15, _ => ⟨0, 0, 300, w00000101111111110111_15⟩
  | 16, _ => ⟨0, 1, 300, w00000101111111110111_16⟩
  | 17, _ => ⟨0, 0, 300, w00000101111111110111_17⟩
  | 18, _ => ⟨0, 0, 300, w00000101111111110111_18⟩
  | 19, _ => ⟨0, 0, 300, w00000101111111110111_19⟩
  | _ + 20, h => absurd h (by omega)

set_option maxHeartbeats 0 in
theorem w00001011111111001001_0 : phaseCheck (wordOf 20 0b00001011111111001001) 14 0 1 300 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00001011111111001001_1 : phaseCheck (wordOf 20 0b00001011111111001001) 14 0 3 300 1 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00001011111111001001_2 : phaseCheck (wordOf 20 0b00001011111111001001) 14 0 2 300 2 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00001011111111001001_3 : phaseCheck (wordOf 20 0b00001011111111001001) 14 0 1 300 3 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00001011111111001001_4 : phaseCheck (wordOf 20 0b00001011111111001001) 14 0 0 300 4 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00001011111111001001_5 : phaseCheck (wordOf 20 0b00001011111111001001) 14 0 1 300 5 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00001011111111001001_6 : phaseCheck (wordOf 20 0b00001011111111001001) 14 0 0 300 6 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00001011111111001001_7 : phaseCheck (wordOf 20 0b00001011111111001001) 14 0 0 300 7 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00001011111111001001_8 : phaseCheck (wordOf 20 0b00001011111111001001) 14 0 0 300 8 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00001011111111001001_9 : phaseCheck (wordOf 20 0b00001011111111001001) 14 0 0 300 9 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00001011111111001001_10 : phaseCheck (wordOf 20 0b00001011111111001001) 14 0 0 300 10 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00001011111111001001_11 : phaseCheck (wordOf 20 0b00001011111111001001) 14 0 0 300 11 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00001011111111001001_12 : phaseCheck (wordOf 20 0b00001011111111001001) 14 0 0 300 12 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00001011111111001001_13 : phaseCheck (wordOf 20 0b00001011111111001001) 14 0 0 300 13 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00001011111111001001_14 : phaseCheck (wordOf 20 0b00001011111111001001) 14 0 1 300 14 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00001011111111001001_15 : phaseCheck (wordOf 20 0b00001011111111001001) 14 0 1 300 15 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00001011111111001001_16 : phaseCheck (wordOf 20 0b00001011111111001001) 14 0 0 300 16 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00001011111111001001_17 : phaseCheck (wordOf 20 0b00001011111111001001) 14 0 1 300 17 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00001011111111001001_18 : phaseCheck (wordOf 20 0b00001011111111001001) 14 0 2 300 18 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00001011111111001001_19 : phaseCheck (wordOf 20 0b00001011111111001001) 14 0 0 300 19 = true := by
  decide +kernel

/-- Every phase of `00001011111111001001` at width 14. -/
theorem w00001011111111001001 : ∀ φ, φ < 20 → ∃ D rounds fuel,
    phaseCheck (wordOf 20 0b00001011111111001001) 14 D rounds fuel φ = true
  | 0, _ => ⟨0, 1, 300, w00001011111111001001_0⟩
  | 1, _ => ⟨0, 3, 300, w00001011111111001001_1⟩
  | 2, _ => ⟨0, 2, 300, w00001011111111001001_2⟩
  | 3, _ => ⟨0, 1, 300, w00001011111111001001_3⟩
  | 4, _ => ⟨0, 0, 300, w00001011111111001001_4⟩
  | 5, _ => ⟨0, 1, 300, w00001011111111001001_5⟩
  | 6, _ => ⟨0, 0, 300, w00001011111111001001_6⟩
  | 7, _ => ⟨0, 0, 300, w00001011111111001001_7⟩
  | 8, _ => ⟨0, 0, 300, w00001011111111001001_8⟩
  | 9, _ => ⟨0, 0, 300, w00001011111111001001_9⟩
  | 10, _ => ⟨0, 0, 300, w00001011111111001001_10⟩
  | 11, _ => ⟨0, 0, 300, w00001011111111001001_11⟩
  | 12, _ => ⟨0, 0, 300, w00001011111111001001_12⟩
  | 13, _ => ⟨0, 0, 300, w00001011111111001001_13⟩
  | 14, _ => ⟨0, 1, 300, w00001011111111001001_14⟩
  | 15, _ => ⟨0, 1, 300, w00001011111111001001_15⟩
  | 16, _ => ⟨0, 0, 300, w00001011111111001001_16⟩
  | 17, _ => ⟨0, 1, 300, w00001011111111001001_17⟩
  | 18, _ => ⟨0, 2, 300, w00001011111111001001_18⟩
  | 19, _ => ⟨0, 0, 300, w00001011111111001001_19⟩
  | _ + 20, h => absurd h (by omega)

set_option maxHeartbeats 0 in
theorem w00010111111111110111_0 : phaseCheck (wordOf 20 0b00010111111111110111) 13 0 1 300 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00010111111111110111_1 : phaseCheck (wordOf 20 0b00010111111111110111) 13 0 2 300 1 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00010111111111110111_2 : phaseCheck (wordOf 20 0b00010111111111110111) 13 0 1 300 2 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00010111111111110111_3 : phaseCheck (wordOf 20 0b00010111111111110111) 13 0 0 300 3 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00010111111111110111_4 : phaseCheck (wordOf 20 0b00010111111111110111) 13 0 2 300 4 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00010111111111110111_5 : phaseCheck (wordOf 20 0b00010111111111110111) 13 0 0 300 5 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00010111111111110111_6 : phaseCheck (wordOf 20 0b00010111111111110111) 13 0 0 300 6 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00010111111111110111_7 : phaseCheck (wordOf 20 0b00010111111111110111) 13 0 0 300 7 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00010111111111110111_8 : phaseCheck (wordOf 20 0b00010111111111110111) 13 0 0 300 8 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00010111111111110111_9 : phaseCheck (wordOf 20 0b00010111111111110111) 13 0 0 300 9 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00010111111111110111_10 : phaseCheck (wordOf 20 0b00010111111111110111) 13 0 0 300 10 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00010111111111110111_11 : phaseCheck (wordOf 20 0b00010111111111110111) 13 0 0 300 11 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00010111111111110111_12 : phaseCheck (wordOf 20 0b00010111111111110111) 13 0 0 300 12 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00010111111111110111_13 : phaseCheck (wordOf 20 0b00010111111111110111) 13 0 0 300 13 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00010111111111110111_14 : phaseCheck (wordOf 20 0b00010111111111110111) 13 0 0 300 14 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00010111111111110111_15 : phaseCheck (wordOf 20 0b00010111111111110111) 13 0 0 300 15 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00010111111111110111_16 : phaseCheck (wordOf 20 0b00010111111111110111) 13 0 1 300 16 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00010111111111110111_17 : phaseCheck (wordOf 20 0b00010111111111110111) 13 0 0 300 17 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00010111111111110111_18 : phaseCheck (wordOf 20 0b00010111111111110111) 13 0 0 300 18 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00010111111111110111_19 : phaseCheck (wordOf 20 0b00010111111111110111) 13 0 0 300 19 = true := by
  decide +kernel

/-- Every phase of `00010111111111110111` at width 13. -/
theorem w00010111111111110111 : ∀ φ, φ < 20 → ∃ D rounds fuel,
    phaseCheck (wordOf 20 0b00010111111111110111) 13 D rounds fuel φ = true
  | 0, _ => ⟨0, 1, 300, w00010111111111110111_0⟩
  | 1, _ => ⟨0, 2, 300, w00010111111111110111_1⟩
  | 2, _ => ⟨0, 1, 300, w00010111111111110111_2⟩
  | 3, _ => ⟨0, 0, 300, w00010111111111110111_3⟩
  | 4, _ => ⟨0, 2, 300, w00010111111111110111_4⟩
  | 5, _ => ⟨0, 0, 300, w00010111111111110111_5⟩
  | 6, _ => ⟨0, 0, 300, w00010111111111110111_6⟩
  | 7, _ => ⟨0, 0, 300, w00010111111111110111_7⟩
  | 8, _ => ⟨0, 0, 300, w00010111111111110111_8⟩
  | 9, _ => ⟨0, 0, 300, w00010111111111110111_9⟩
  | 10, _ => ⟨0, 0, 300, w00010111111111110111_10⟩
  | 11, _ => ⟨0, 0, 300, w00010111111111110111_11⟩
  | 12, _ => ⟨0, 0, 300, w00010111111111110111_12⟩
  | 13, _ => ⟨0, 0, 300, w00010111111111110111_13⟩
  | 14, _ => ⟨0, 0, 300, w00010111111111110111_14⟩
  | 15, _ => ⟨0, 0, 300, w00010111111111110111_15⟩
  | 16, _ => ⟨0, 1, 300, w00010111111111110111_16⟩
  | 17, _ => ⟨0, 0, 300, w00010111111111110111_17⟩
  | 18, _ => ⟨0, 0, 300, w00010111111111110111_18⟩
  | 19, _ => ⟨0, 0, 300, w00010111111111110111_19⟩
  | _ + 20, h => absurd h (by omega)

set_option maxHeartbeats 0 in
theorem w00100101110011111111_0 : phaseCheck (wordOf 20 0b00100101110011111111) 13 0 2 300 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00100101110011111111_1 : phaseCheck (wordOf 20 0b00100101110011111111) 13 0 1 300 1 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00100101110011111111_2 : phaseCheck (wordOf 20 0b00100101110011111111) 13 0 0 300 2 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00100101110011111111_3 : phaseCheck (wordOf 20 0b00100101110011111111) 13 0 1 300 3 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00100101110011111111_4 : phaseCheck (wordOf 20 0b00100101110011111111) 13 0 3 300 4 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00100101110011111111_5 : phaseCheck (wordOf 20 0b00100101110011111111) 13 0 0 300 5 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00100101110011111111_6 : phaseCheck (wordOf 20 0b00100101110011111111) 13 0 1 300 6 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00100101110011111111_7 : phaseCheck (wordOf 20 0b00100101110011111111) 13 0 0 300 7 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00100101110011111111_8 : phaseCheck (wordOf 20 0b00100101110011111111) 13 0 0 300 8 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00100101110011111111_9 : phaseCheck (wordOf 20 0b00100101110011111111) 13 0 0 300 9 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00100101110011111111_10 : phaseCheck (wordOf 20 0b00100101110011111111) 13 0 2 300 10 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00100101110011111111_11 : phaseCheck (wordOf 20 0b00100101110011111111) 13 0 3 300 11 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00100101110011111111_12 : phaseCheck (wordOf 20 0b00100101110011111111) 13 0 0 300 12 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00100101110011111111_13 : phaseCheck (wordOf 20 0b00100101110011111111) 13 0 0 300 13 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00100101110011111111_14 : phaseCheck (wordOf 20 0b00100101110011111111) 13 0 0 300 14 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00100101110011111111_15 : phaseCheck (wordOf 20 0b00100101110011111111) 13 0 0 300 15 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00100101110011111111_16 : phaseCheck (wordOf 20 0b00100101110011111111) 13 0 0 300 16 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00100101110011111111_17 : phaseCheck (wordOf 20 0b00100101110011111111) 13 0 0 300 17 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00100101110011111111_18 : phaseCheck (wordOf 20 0b00100101110011111111) 13 0 0 300 18 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00100101110011111111_19 : phaseCheck (wordOf 20 0b00100101110011111111) 13 0 0 300 19 = true := by
  decide +kernel

/-- Every phase of `00100101110011111111` at width 13. -/
theorem w00100101110011111111 : ∀ φ, φ < 20 → ∃ D rounds fuel,
    phaseCheck (wordOf 20 0b00100101110011111111) 13 D rounds fuel φ = true
  | 0, _ => ⟨0, 2, 300, w00100101110011111111_0⟩
  | 1, _ => ⟨0, 1, 300, w00100101110011111111_1⟩
  | 2, _ => ⟨0, 0, 300, w00100101110011111111_2⟩
  | 3, _ => ⟨0, 1, 300, w00100101110011111111_3⟩
  | 4, _ => ⟨0, 3, 300, w00100101110011111111_4⟩
  | 5, _ => ⟨0, 0, 300, w00100101110011111111_5⟩
  | 6, _ => ⟨0, 1, 300, w00100101110011111111_6⟩
  | 7, _ => ⟨0, 0, 300, w00100101110011111111_7⟩
  | 8, _ => ⟨0, 0, 300, w00100101110011111111_8⟩
  | 9, _ => ⟨0, 0, 300, w00100101110011111111_9⟩
  | 10, _ => ⟨0, 2, 300, w00100101110011111111_10⟩
  | 11, _ => ⟨0, 3, 300, w00100101110011111111_11⟩
  | 12, _ => ⟨0, 0, 300, w00100101110011111111_12⟩
  | 13, _ => ⟨0, 0, 300, w00100101110011111111_13⟩
  | 14, _ => ⟨0, 0, 300, w00100101110011111111_14⟩
  | 15, _ => ⟨0, 0, 300, w00100101110011111111_15⟩
  | 16, _ => ⟨0, 0, 300, w00100101110011111111_16⟩
  | 17, _ => ⟨0, 0, 300, w00100101110011111111_17⟩
  | 18, _ => ⟨0, 0, 300, w00100101110011111111_18⟩
  | 19, _ => ⟨0, 0, 300, w00100101110011111111_19⟩
  | _ + 20, h => absurd h (by omega)

set_option maxHeartbeats 0 in
theorem w00101001111111111101_0 : phaseCheck (wordOf 20 0b00101001111111111101) 14 0 1 300 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00101001111111111101_1 : phaseCheck (wordOf 20 0b00101001111111111101) 14 0 1 300 1 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00101001111111111101_2 : phaseCheck (wordOf 20 0b00101001111111111101) 14 0 0 300 2 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00101001111111111101_3 : phaseCheck (wordOf 20 0b00101001111111111101) 14 0 1 300 3 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00101001111111111101_4 : phaseCheck (wordOf 20 0b00101001111111111101) 14 0 0 300 4 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00101001111111111101_5 : phaseCheck (wordOf 20 0b00101001111111111101) 14 0 2 300 5 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00101001111111111101_6 : phaseCheck (wordOf 20 0b00101001111111111101) 14 0 3 300 6 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00101001111111111101_7 : phaseCheck (wordOf 20 0b00101001111111111101) 14 0 0 300 7 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00101001111111111101_8 : phaseCheck (wordOf 20 0b00101001111111111101) 14 0 0 300 8 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00101001111111111101_9 : phaseCheck (wordOf 20 0b00101001111111111101) 14 0 0 300 9 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00101001111111111101_10 : phaseCheck (wordOf 20 0b00101001111111111101) 14 0 0 300 10 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00101001111111111101_11 : phaseCheck (wordOf 20 0b00101001111111111101) 14 0 0 300 11 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00101001111111111101_12 : phaseCheck (wordOf 20 0b00101001111111111101) 14 0 0 300 12 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00101001111111111101_13 : phaseCheck (wordOf 20 0b00101001111111111101) 14 0 0 300 13 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00101001111111111101_14 : phaseCheck (wordOf 20 0b00101001111111111101) 14 0 0 300 14 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00101001111111111101_15 : phaseCheck (wordOf 20 0b00101001111111111101) 14 0 0 300 15 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00101001111111111101_16 : phaseCheck (wordOf 20 0b00101001111111111101) 14 0 0 300 16 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00101001111111111101_17 : phaseCheck (wordOf 20 0b00101001111111111101) 14 0 0 300 17 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00101001111111111101_18 : phaseCheck (wordOf 20 0b00101001111111111101) 14 0 1 300 18 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w00101001111111111101_19 : phaseCheck (wordOf 20 0b00101001111111111101) 14 0 0 300 19 = true := by
  decide +kernel

/-- Every phase of `00101001111111111101` at width 14. -/
theorem w00101001111111111101 : ∀ φ, φ < 20 → ∃ D rounds fuel,
    phaseCheck (wordOf 20 0b00101001111111111101) 14 D rounds fuel φ = true
  | 0, _ => ⟨0, 1, 300, w00101001111111111101_0⟩
  | 1, _ => ⟨0, 1, 300, w00101001111111111101_1⟩
  | 2, _ => ⟨0, 0, 300, w00101001111111111101_2⟩
  | 3, _ => ⟨0, 1, 300, w00101001111111111101_3⟩
  | 4, _ => ⟨0, 0, 300, w00101001111111111101_4⟩
  | 5, _ => ⟨0, 2, 300, w00101001111111111101_5⟩
  | 6, _ => ⟨0, 3, 300, w00101001111111111101_6⟩
  | 7, _ => ⟨0, 0, 300, w00101001111111111101_7⟩
  | 8, _ => ⟨0, 0, 300, w00101001111111111101_8⟩
  | 9, _ => ⟨0, 0, 300, w00101001111111111101_9⟩
  | 10, _ => ⟨0, 0, 300, w00101001111111111101_10⟩
  | 11, _ => ⟨0, 0, 300, w00101001111111111101_11⟩
  | 12, _ => ⟨0, 0, 300, w00101001111111111101_12⟩
  | 13, _ => ⟨0, 0, 300, w00101001111111111101_13⟩
  | 14, _ => ⟨0, 0, 300, w00101001111111111101_14⟩
  | 15, _ => ⟨0, 0, 300, w00101001111111111101_15⟩
  | 16, _ => ⟨0, 0, 300, w00101001111111111101_16⟩
  | 17, _ => ⟨0, 0, 300, w00101001111111111101_17⟩
  | 18, _ => ⟨0, 1, 300, w00101001111111111101_18⟩
  | 19, _ => ⟨0, 0, 300, w00101001111111111101_19⟩
  | _ + 20, h => absurd h (by omega)

set_option maxHeartbeats 0 in
theorem w01111011111111111111_0 : phaseCheck (wordOf 20 0b01111011111111111111) 14 0 1 300 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w01111011111111111111_1 : phaseCheck (wordOf 20 0b01111011111111111111) 14 0 0 300 1 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w01111011111111111111_2 : phaseCheck (wordOf 20 0b01111011111111111111) 14 0 0 300 2 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w01111011111111111111_3 : phaseCheck (wordOf 20 0b01111011111111111111) 14 0 0 300 3 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w01111011111111111111_4 : phaseCheck (wordOf 20 0b01111011111111111111) 14 0 0 300 4 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w01111011111111111111_5 : phaseCheck (wordOf 20 0b01111011111111111111) 14 0 2 300 5 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w01111011111111111111_6 : phaseCheck (wordOf 20 0b01111011111111111111) 14 0 0 300 6 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w01111011111111111111_7 : phaseCheck (wordOf 20 0b01111011111111111111) 14 0 0 300 7 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w01111011111111111111_8 : phaseCheck (wordOf 20 0b01111011111111111111) 14 0 0 300 8 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w01111011111111111111_9 : phaseCheck (wordOf 20 0b01111011111111111111) 14 0 0 300 9 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w01111011111111111111_10 : phaseCheck (wordOf 20 0b01111011111111111111) 14 0 0 300 10 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w01111011111111111111_11 : phaseCheck (wordOf 20 0b01111011111111111111) 14 0 0 300 11 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w01111011111111111111_12 : phaseCheck (wordOf 20 0b01111011111111111111) 14 0 0 300 12 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w01111011111111111111_13 : phaseCheck (wordOf 20 0b01111011111111111111) 14 0 0 300 13 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w01111011111111111111_14 : phaseCheck (wordOf 20 0b01111011111111111111) 14 0 0 300 14 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w01111011111111111111_15 : phaseCheck (wordOf 20 0b01111011111111111111) 14 0 0 300 15 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w01111011111111111111_16 : phaseCheck (wordOf 20 0b01111011111111111111) 14 0 0 300 16 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w01111011111111111111_17 : phaseCheck (wordOf 20 0b01111011111111111111) 14 0 0 300 17 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w01111011111111111111_18 : phaseCheck (wordOf 20 0b01111011111111111111) 14 0 0 300 18 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w01111011111111111111_19 : phaseCheck (wordOf 20 0b01111011111111111111) 14 0 0 300 19 = true := by
  decide +kernel

/-- Every phase of `01111011111111111111` at width 14. -/
theorem w01111011111111111111 : ∀ φ, φ < 20 → ∃ D rounds fuel,
    phaseCheck (wordOf 20 0b01111011111111111111) 14 D rounds fuel φ = true
  | 0, _ => ⟨0, 1, 300, w01111011111111111111_0⟩
  | 1, _ => ⟨0, 0, 300, w01111011111111111111_1⟩
  | 2, _ => ⟨0, 0, 300, w01111011111111111111_2⟩
  | 3, _ => ⟨0, 0, 300, w01111011111111111111_3⟩
  | 4, _ => ⟨0, 0, 300, w01111011111111111111_4⟩
  | 5, _ => ⟨0, 2, 300, w01111011111111111111_5⟩
  | 6, _ => ⟨0, 0, 300, w01111011111111111111_6⟩
  | 7, _ => ⟨0, 0, 300, w01111011111111111111_7⟩
  | 8, _ => ⟨0, 0, 300, w01111011111111111111_8⟩
  | 9, _ => ⟨0, 0, 300, w01111011111111111111_9⟩
  | 10, _ => ⟨0, 0, 300, w01111011111111111111_10⟩
  | 11, _ => ⟨0, 0, 300, w01111011111111111111_11⟩
  | 12, _ => ⟨0, 0, 300, w01111011111111111111_12⟩
  | 13, _ => ⟨0, 0, 300, w01111011111111111111_13⟩
  | 14, _ => ⟨0, 0, 300, w01111011111111111111_14⟩
  | 15, _ => ⟨0, 0, 300, w01111011111111111111_15⟩
  | 16, _ => ⟨0, 0, 300, w01111011111111111111_16⟩
  | 17, _ => ⟨0, 0, 300, w01111011111111111111_17⟩
  | 18, _ => ⟨0, 0, 300, w01111011111111111111_18⟩
  | 19, _ => ⟨0, 0, 300, w01111011111111111111_19⟩
  | _ + 20, h => absurd h (by omega)

/-- The blocks of this module, each as its least rotation `wordOf n bits`, with the width of its checks. -/
def blocksPhases20 : List ((Nat × Nat) × Nat) := [
    ((20, 0b00000000000000110001), 14), ((20, 0b00000000000001000001), 13), ((20, 0b00000000000001010001), 14),
    ((20, 0b00000000000011000101), 14), ((20, 0b00000000001100101111), 14), ((20, 0b00000000110001111011), 13),
    ((20, 0b00000001011111100011), 13), ((20, 0b00000001101111111011), 14), ((20, 0b00000101111111001001), 14),
    ((20, 0b00000101111111110111), 14), ((20, 0b00001011111111001001), 14), ((20, 0b00010111111111110111), 13),
    ((20, 0b00100101110011111111), 13), ((20, 0b00101001111111111101), 14), ((20, 0b01111011111111111111), 14)]

theorem blocksPhases20_phases : ∀ e ∈ blocksPhases20, ∀ φ, φ < e.1.1 → ∃ D rounds fuel,
    phaseCheck (wordOf e.1.1 e.1.2) e.2 D rounds fuel φ = true := by
  intro e he
  simp only [blocksPhases20, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact w00000000000000110001
  · exact w00000000000001000001
  · exact w00000000000001010001
  · exact w00000000000011000101
  · exact w00000000001100101111
  · exact w00000000110001111011
  · exact w00000001011111100011
  · exact w00000001101111111011
  · exact w00000101111111001001
  · exact w00000101111111110111
  · exact w00001011111111001001
  · exact w00010111111111110111
  · exact w00100101110011111111
  · exact w00101001111111111101
  · exact w01111011111111111111

theorem blocksPhases20_pos : ∀ e ∈ blocksPhases20, 1 ≤ e.2 ∧ 1 ≤ e.1.1 := by decide

/-- **The center column does not eventually repeat any of the 15 blocks of `blocksPhases20`**, from any time on
and in any rotation. -/
theorem center_not_blocksPhases20 (e : (Nat × Nat) × Nat) (he : e ∈ blocksPhases20) (T shift : Nat)
    (h : ∀ t : Nat, T ≤ t → Rule30Prize.center t = (wordOf e.1.1 e.1.2).getD ((t + shift) % e.1.1) false) :
    False :=
  center_not_phases_list blocksPhases20 blocksPhases20_pos blocksPhases20_phases e he T shift h

/-- The same in the kit's form `Rule30StripCertificates.EventuallyWord`. -/
theorem not_eventually_blocksPhases20 (e : (Nat × Nat) × Nat) (he : e ∈ blocksPhases20) :
    ¬ Rule30StripCertificates.EventuallyWord (wordOf e.1.1 e.1.2) :=
  phases_list_not_eventually blocksPhases20 blocksPhases20_pos blocksPhases20_phases e he

end Rule30Open
