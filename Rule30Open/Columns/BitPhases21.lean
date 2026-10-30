module

public import Rule30Open.Columns.BitPhases

/-!
# The game decided phase by phase in the kernel excludes the 35 blocks of period 21 that need 13 or 14 cells

[BitPhases](BitPhases.md) checks the finite game in the kernel one phase at a time (`phaseCheck`), and
`center_not_phases_list` turns a list of blocks whose phases all pass into exclusions. Here the checks run on the
35 blocks of period 21 that the game excludes at width 13 or 14 and that neither the kit nor
[WallSets](WallSets.md) excludes.

* `blocksPhases21`: the blocks, each as its least rotation, with the width of their checks, and one theorem per
  phase of each.
* `center_not_blocksPhases21`, `not_eventually_blocksPhases21`: the center column of the single cell does not eventually
  repeat any of them, in any rotation, and in the kit's form `EventuallyWord`.

The natural-language argument is `BitPhases21.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

open Ruliology.CellularAutomata BitGame

open Rule30StripCertificateTable (wordOf)

set_option Elab.async false

set_option maxHeartbeats 0 in
theorem w000000000000001000001_0 : phaseCheck (wordOf 21 0b000000000000001000001) 13 0 1 300 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000001000001_1 : phaseCheck (wordOf 21 0b000000000000001000001) 13 0 2 300 1 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000001000001_2 : phaseCheck (wordOf 21 0b000000000000001000001) 13 0 1 300 2 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000001000001_3 : phaseCheck (wordOf 21 0b000000000000001000001) 13 0 1 300 3 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000001000001_4 : phaseCheck (wordOf 21 0b000000000000001000001) 13 0 1 300 4 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000001000001_5 : phaseCheck (wordOf 21 0b000000000000001000001) 13 0 1 300 5 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000001000001_6 : phaseCheck (wordOf 21 0b000000000000001000001) 13 0 1 300 6 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000001000001_7 : phaseCheck (wordOf 21 0b000000000000001000001) 13 0 1 300 7 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000001000001_8 : phaseCheck (wordOf 21 0b000000000000001000001) 13 0 1 300 8 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000001000001_9 : phaseCheck (wordOf 21 0b000000000000001000001) 13 0 1 300 9 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000001000001_10 : phaseCheck (wordOf 21 0b000000000000001000001) 13 0 1 300 10 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000001000001_11 : phaseCheck (wordOf 21 0b000000000000001000001) 13 0 1 300 11 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000001000001_12 : phaseCheck (wordOf 21 0b000000000000001000001) 13 0 1 300 12 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000001000001_13 : phaseCheck (wordOf 21 0b000000000000001000001) 13 0 1 300 13 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000001000001_14 : phaseCheck (wordOf 21 0b000000000000001000001) 13 0 0 300 14 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000001000001_15 : phaseCheck (wordOf 21 0b000000000000001000001) 13 0 1 300 15 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000001000001_16 : phaseCheck (wordOf 21 0b000000000000001000001) 13 0 1 300 16 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000001000001_17 : phaseCheck (wordOf 21 0b000000000000001000001) 13 0 1 300 17 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000001000001_18 : phaseCheck (wordOf 21 0b000000000000001000001) 13 0 1 300 18 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000001000001_19 : phaseCheck (wordOf 21 0b000000000000001000001) 13 0 1 300 19 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000001000001_20 : phaseCheck (wordOf 21 0b000000000000001000001) 13 0 0 300 20 = true := by
  decide +kernel

/-- Every phase of `000000000000001000001` at width 13. -/
theorem w000000000000001000001 : ∀ φ, φ < 21 → ∃ D rounds fuel,
    phaseCheck (wordOf 21 0b000000000000001000001) 13 D rounds fuel φ = true
  | 0, _ => ⟨0, 1, 300, w000000000000001000001_0⟩
  | 1, _ => ⟨0, 2, 300, w000000000000001000001_1⟩
  | 2, _ => ⟨0, 1, 300, w000000000000001000001_2⟩
  | 3, _ => ⟨0, 1, 300, w000000000000001000001_3⟩
  | 4, _ => ⟨0, 1, 300, w000000000000001000001_4⟩
  | 5, _ => ⟨0, 1, 300, w000000000000001000001_5⟩
  | 6, _ => ⟨0, 1, 300, w000000000000001000001_6⟩
  | 7, _ => ⟨0, 1, 300, w000000000000001000001_7⟩
  | 8, _ => ⟨0, 1, 300, w000000000000001000001_8⟩
  | 9, _ => ⟨0, 1, 300, w000000000000001000001_9⟩
  | 10, _ => ⟨0, 1, 300, w000000000000001000001_10⟩
  | 11, _ => ⟨0, 1, 300, w000000000000001000001_11⟩
  | 12, _ => ⟨0, 1, 300, w000000000000001000001_12⟩
  | 13, _ => ⟨0, 1, 300, w000000000000001000001_13⟩
  | 14, _ => ⟨0, 0, 300, w000000000000001000001_14⟩
  | 15, _ => ⟨0, 1, 300, w000000000000001000001_15⟩
  | 16, _ => ⟨0, 1, 300, w000000000000001000001_16⟩
  | 17, _ => ⟨0, 1, 300, w000000000000001000001_17⟩
  | 18, _ => ⟨0, 1, 300, w000000000000001000001_18⟩
  | 19, _ => ⟨0, 1, 300, w000000000000001000001_19⟩
  | 20, _ => ⟨0, 0, 300, w000000000000001000001_20⟩
  | _ + 21, h => absurd h (by omega)

set_option maxHeartbeats 0 in
theorem w000000000000001010001_0 : phaseCheck (wordOf 21 0b000000000000001010001) 14 0 1 300 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000001010001_1 : phaseCheck (wordOf 21 0b000000000000001010001) 14 0 1 300 1 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000001010001_2 : phaseCheck (wordOf 21 0b000000000000001010001) 14 0 2 300 2 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000001010001_3 : phaseCheck (wordOf 21 0b000000000000001010001) 14 0 2 300 3 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000001010001_4 : phaseCheck (wordOf 21 0b000000000000001010001) 14 0 2 300 4 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000001010001_5 : phaseCheck (wordOf 21 0b000000000000001010001) 14 0 2 300 5 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000001010001_6 : phaseCheck (wordOf 21 0b000000000000001010001) 14 0 2 300 6 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000001010001_7 : phaseCheck (wordOf 21 0b000000000000001010001) 14 0 2 300 7 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000001010001_8 : phaseCheck (wordOf 21 0b000000000000001010001) 14 0 1 300 8 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000001010001_9 : phaseCheck (wordOf 21 0b000000000000001010001) 14 0 1 300 9 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000001010001_10 : phaseCheck (wordOf 21 0b000000000000001010001) 14 0 1 300 10 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000001010001_11 : phaseCheck (wordOf 21 0b000000000000001010001) 14 0 1 300 11 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000001010001_12 : phaseCheck (wordOf 21 0b000000000000001010001) 14 0 2 300 12 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000001010001_13 : phaseCheck (wordOf 21 0b000000000000001010001) 14 0 2 300 13 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000001010001_14 : phaseCheck (wordOf 21 0b000000000000001010001) 14 0 0 300 14 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000001010001_15 : phaseCheck (wordOf 21 0b000000000000001010001) 14 0 1 300 15 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000001010001_16 : phaseCheck (wordOf 21 0b000000000000001010001) 14 0 0 300 16 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000001010001_17 : phaseCheck (wordOf 21 0b000000000000001010001) 14 0 1 300 17 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000001010001_18 : phaseCheck (wordOf 21 0b000000000000001010001) 14 0 1 300 18 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000001010001_19 : phaseCheck (wordOf 21 0b000000000000001010001) 14 0 2 300 19 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000001010001_20 : phaseCheck (wordOf 21 0b000000000000001010001) 14 0 0 300 20 = true := by
  decide +kernel

/-- Every phase of `000000000000001010001` at width 14. -/
theorem w000000000000001010001 : ∀ φ, φ < 21 → ∃ D rounds fuel,
    phaseCheck (wordOf 21 0b000000000000001010001) 14 D rounds fuel φ = true
  | 0, _ => ⟨0, 1, 300, w000000000000001010001_0⟩
  | 1, _ => ⟨0, 1, 300, w000000000000001010001_1⟩
  | 2, _ => ⟨0, 2, 300, w000000000000001010001_2⟩
  | 3, _ => ⟨0, 2, 300, w000000000000001010001_3⟩
  | 4, _ => ⟨0, 2, 300, w000000000000001010001_4⟩
  | 5, _ => ⟨0, 2, 300, w000000000000001010001_5⟩
  | 6, _ => ⟨0, 2, 300, w000000000000001010001_6⟩
  | 7, _ => ⟨0, 2, 300, w000000000000001010001_7⟩
  | 8, _ => ⟨0, 1, 300, w000000000000001010001_8⟩
  | 9, _ => ⟨0, 1, 300, w000000000000001010001_9⟩
  | 10, _ => ⟨0, 1, 300, w000000000000001010001_10⟩
  | 11, _ => ⟨0, 1, 300, w000000000000001010001_11⟩
  | 12, _ => ⟨0, 2, 300, w000000000000001010001_12⟩
  | 13, _ => ⟨0, 2, 300, w000000000000001010001_13⟩
  | 14, _ => ⟨0, 0, 300, w000000000000001010001_14⟩
  | 15, _ => ⟨0, 1, 300, w000000000000001010001_15⟩
  | 16, _ => ⟨0, 0, 300, w000000000000001010001_16⟩
  | 17, _ => ⟨0, 1, 300, w000000000000001010001_17⟩
  | 18, _ => ⟨0, 1, 300, w000000000000001010001_18⟩
  | 19, _ => ⟨0, 2, 300, w000000000000001010001_19⟩
  | 20, _ => ⟨0, 0, 300, w000000000000001010001_20⟩
  | _ + 21, h => absurd h (by omega)

set_option maxHeartbeats 0 in
theorem w000000000000001111111_0 : phaseCheck (wordOf 21 0b000000000000001111111) 14 0 1 300 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000001111111_1 : phaseCheck (wordOf 21 0b000000000000001111111) 14 0 3 300 1 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000001111111_2 : phaseCheck (wordOf 21 0b000000000000001111111) 14 0 3 300 2 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000001111111_3 : phaseCheck (wordOf 21 0b000000000000001111111) 14 0 3 300 3 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000001111111_4 : phaseCheck (wordOf 21 0b000000000000001111111) 14 0 2 300 4 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000001111111_5 : phaseCheck (wordOf 21 0b000000000000001111111) 14 0 2 300 5 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000001111111_6 : phaseCheck (wordOf 21 0b000000000000001111111) 14 0 2 300 6 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000001111111_7 : phaseCheck (wordOf 21 0b000000000000001111111) 14 0 2 300 7 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000001111111_8 : phaseCheck (wordOf 21 0b000000000000001111111) 14 0 1 300 8 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000001111111_9 : phaseCheck (wordOf 21 0b000000000000001111111) 14 0 1 300 9 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000001111111_10 : phaseCheck (wordOf 21 0b000000000000001111111) 14 0 1 300 10 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000001111111_11 : phaseCheck (wordOf 21 0b000000000000001111111) 14 0 1 300 11 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000001111111_12 : phaseCheck (wordOf 21 0b000000000000001111111) 14 0 1 300 12 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000001111111_13 : phaseCheck (wordOf 21 0b000000000000001111111) 14 0 1 300 13 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000001111111_14 : phaseCheck (wordOf 21 0b000000000000001111111) 14 0 0 300 14 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000001111111_15 : phaseCheck (wordOf 21 0b000000000000001111111) 14 0 0 300 15 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000001111111_16 : phaseCheck (wordOf 21 0b000000000000001111111) 14 0 0 300 16 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000001111111_17 : phaseCheck (wordOf 21 0b000000000000001111111) 14 0 0 300 17 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000001111111_18 : phaseCheck (wordOf 21 0b000000000000001111111) 14 0 0 300 18 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000001111111_19 : phaseCheck (wordOf 21 0b000000000000001111111) 14 0 0 300 19 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000001111111_20 : phaseCheck (wordOf 21 0b000000000000001111111) 14 0 0 300 20 = true := by
  decide +kernel

/-- Every phase of `000000000000001111111` at width 14. -/
theorem w000000000000001111111 : ∀ φ, φ < 21 → ∃ D rounds fuel,
    phaseCheck (wordOf 21 0b000000000000001111111) 14 D rounds fuel φ = true
  | 0, _ => ⟨0, 1, 300, w000000000000001111111_0⟩
  | 1, _ => ⟨0, 3, 300, w000000000000001111111_1⟩
  | 2, _ => ⟨0, 3, 300, w000000000000001111111_2⟩
  | 3, _ => ⟨0, 3, 300, w000000000000001111111_3⟩
  | 4, _ => ⟨0, 2, 300, w000000000000001111111_4⟩
  | 5, _ => ⟨0, 2, 300, w000000000000001111111_5⟩
  | 6, _ => ⟨0, 2, 300, w000000000000001111111_6⟩
  | 7, _ => ⟨0, 2, 300, w000000000000001111111_7⟩
  | 8, _ => ⟨0, 1, 300, w000000000000001111111_8⟩
  | 9, _ => ⟨0, 1, 300, w000000000000001111111_9⟩
  | 10, _ => ⟨0, 1, 300, w000000000000001111111_10⟩
  | 11, _ => ⟨0, 1, 300, w000000000000001111111_11⟩
  | 12, _ => ⟨0, 1, 300, w000000000000001111111_12⟩
  | 13, _ => ⟨0, 1, 300, w000000000000001111111_13⟩
  | 14, _ => ⟨0, 0, 300, w000000000000001111111_14⟩
  | 15, _ => ⟨0, 0, 300, w000000000000001111111_15⟩
  | 16, _ => ⟨0, 0, 300, w000000000000001111111_16⟩
  | 17, _ => ⟨0, 0, 300, w000000000000001111111_17⟩
  | 18, _ => ⟨0, 0, 300, w000000000000001111111_18⟩
  | 19, _ => ⟨0, 0, 300, w000000000000001111111_19⟩
  | 20, _ => ⟨0, 0, 300, w000000000000001111111_20⟩
  | _ + 21, h => absurd h (by omega)

set_option maxHeartbeats 0 in
theorem w000000000000010010001_0 : phaseCheck (wordOf 21 0b000000000000010010001) 14 0 1 300 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000010010001_1 : phaseCheck (wordOf 21 0b000000000000010010001) 14 0 1 300 1 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000010010001_2 : phaseCheck (wordOf 21 0b000000000000010010001) 14 0 2 300 2 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000010010001_3 : phaseCheck (wordOf 21 0b000000000000010010001) 14 0 1 300 3 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000010010001_4 : phaseCheck (wordOf 21 0b000000000000010010001) 14 0 1 300 4 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000010010001_5 : phaseCheck (wordOf 21 0b000000000000010010001) 14 0 1 300 5 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000010010001_6 : phaseCheck (wordOf 21 0b000000000000010010001) 14 0 1 300 6 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000010010001_7 : phaseCheck (wordOf 21 0b000000000000010010001) 14 0 1 300 7 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000010010001_8 : phaseCheck (wordOf 21 0b000000000000010010001) 14 0 1 300 8 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000010010001_9 : phaseCheck (wordOf 21 0b000000000000010010001) 14 0 1 300 9 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000010010001_10 : phaseCheck (wordOf 21 0b000000000000010010001) 14 0 1 300 10 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000010010001_11 : phaseCheck (wordOf 21 0b000000000000010010001) 14 0 1 300 11 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000010010001_12 : phaseCheck (wordOf 21 0b000000000000010010001) 14 0 1 300 12 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000010010001_13 : phaseCheck (wordOf 21 0b000000000000010010001) 14 0 0 300 13 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000010010001_14 : phaseCheck (wordOf 21 0b000000000000010010001) 14 0 1 300 14 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000010010001_15 : phaseCheck (wordOf 21 0b000000000000010010001) 14 0 1 300 15 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000010010001_16 : phaseCheck (wordOf 21 0b000000000000010010001) 14 0 0 300 16 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000010010001_17 : phaseCheck (wordOf 21 0b000000000000010010001) 14 0 1 300 17 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000010010001_18 : phaseCheck (wordOf 21 0b000000000000010010001) 14 0 1 300 18 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000010010001_19 : phaseCheck (wordOf 21 0b000000000000010010001) 14 0 2 300 19 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000010010001_20 : phaseCheck (wordOf 21 0b000000000000010010001) 14 0 0 300 20 = true := by
  decide +kernel

/-- Every phase of `000000000000010010001` at width 14. -/
theorem w000000000000010010001 : ∀ φ, φ < 21 → ∃ D rounds fuel,
    phaseCheck (wordOf 21 0b000000000000010010001) 14 D rounds fuel φ = true
  | 0, _ => ⟨0, 1, 300, w000000000000010010001_0⟩
  | 1, _ => ⟨0, 1, 300, w000000000000010010001_1⟩
  | 2, _ => ⟨0, 2, 300, w000000000000010010001_2⟩
  | 3, _ => ⟨0, 1, 300, w000000000000010010001_3⟩
  | 4, _ => ⟨0, 1, 300, w000000000000010010001_4⟩
  | 5, _ => ⟨0, 1, 300, w000000000000010010001_5⟩
  | 6, _ => ⟨0, 1, 300, w000000000000010010001_6⟩
  | 7, _ => ⟨0, 1, 300, w000000000000010010001_7⟩
  | 8, _ => ⟨0, 1, 300, w000000000000010010001_8⟩
  | 9, _ => ⟨0, 1, 300, w000000000000010010001_9⟩
  | 10, _ => ⟨0, 1, 300, w000000000000010010001_10⟩
  | 11, _ => ⟨0, 1, 300, w000000000000010010001_11⟩
  | 12, _ => ⟨0, 1, 300, w000000000000010010001_12⟩
  | 13, _ => ⟨0, 0, 300, w000000000000010010001_13⟩
  | 14, _ => ⟨0, 1, 300, w000000000000010010001_14⟩
  | 15, _ => ⟨0, 1, 300, w000000000000010010001_15⟩
  | 16, _ => ⟨0, 0, 300, w000000000000010010001_16⟩
  | 17, _ => ⟨0, 1, 300, w000000000000010010001_17⟩
  | 18, _ => ⟨0, 1, 300, w000000000000010010001_18⟩
  | 19, _ => ⟨0, 2, 300, w000000000000010010001_19⟩
  | 20, _ => ⟨0, 0, 300, w000000000000010010001_20⟩
  | _ + 21, h => absurd h (by omega)

set_option maxHeartbeats 0 in
theorem w000000000000011000101_0 : phaseCheck (wordOf 21 0b000000000000011000101) 13 0 1 300 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000011000101_1 : phaseCheck (wordOf 21 0b000000000000011000101) 13 0 1 300 1 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000011000101_2 : phaseCheck (wordOf 21 0b000000000000011000101) 13 0 2 300 2 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000011000101_3 : phaseCheck (wordOf 21 0b000000000000011000101) 13 0 3 300 3 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000011000101_4 : phaseCheck (wordOf 21 0b000000000000011000101) 13 0 3 300 4 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000011000101_5 : phaseCheck (wordOf 21 0b000000000000011000101) 13 0 2 300 5 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000011000101_6 : phaseCheck (wordOf 21 0b000000000000011000101) 13 0 1 300 6 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000011000101_7 : phaseCheck (wordOf 21 0b000000000000011000101) 13 0 1 300 7 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000011000101_8 : phaseCheck (wordOf 21 0b000000000000011000101) 13 0 1 300 8 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000011000101_9 : phaseCheck (wordOf 21 0b000000000000011000101) 13 0 1 300 9 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000011000101_10 : phaseCheck (wordOf 21 0b000000000000011000101) 13 0 1 300 10 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000011000101_11 : phaseCheck (wordOf 21 0b000000000000011000101) 13 0 1 300 11 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000011000101_12 : phaseCheck (wordOf 21 0b000000000000011000101) 13 0 1 300 12 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000011000101_13 : phaseCheck (wordOf 21 0b000000000000011000101) 13 0 0 300 13 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000011000101_14 : phaseCheck (wordOf 21 0b000000000000011000101) 13 0 0 300 14 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000011000101_15 : phaseCheck (wordOf 21 0b000000000000011000101) 13 0 1 300 15 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000011000101_16 : phaseCheck (wordOf 21 0b000000000000011000101) 13 0 1 300 16 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000011000101_17 : phaseCheck (wordOf 21 0b000000000000011000101) 13 0 1 300 17 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000011000101_18 : phaseCheck (wordOf 21 0b000000000000011000101) 13 0 0 300 18 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000011000101_19 : phaseCheck (wordOf 21 0b000000000000011000101) 13 0 1 300 19 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000011000101_20 : phaseCheck (wordOf 21 0b000000000000011000101) 13 0 0 300 20 = true := by
  decide +kernel

/-- Every phase of `000000000000011000101` at width 13. -/
theorem w000000000000011000101 : ∀ φ, φ < 21 → ∃ D rounds fuel,
    phaseCheck (wordOf 21 0b000000000000011000101) 13 D rounds fuel φ = true
  | 0, _ => ⟨0, 1, 300, w000000000000011000101_0⟩
  | 1, _ => ⟨0, 1, 300, w000000000000011000101_1⟩
  | 2, _ => ⟨0, 2, 300, w000000000000011000101_2⟩
  | 3, _ => ⟨0, 3, 300, w000000000000011000101_3⟩
  | 4, _ => ⟨0, 3, 300, w000000000000011000101_4⟩
  | 5, _ => ⟨0, 2, 300, w000000000000011000101_5⟩
  | 6, _ => ⟨0, 1, 300, w000000000000011000101_6⟩
  | 7, _ => ⟨0, 1, 300, w000000000000011000101_7⟩
  | 8, _ => ⟨0, 1, 300, w000000000000011000101_8⟩
  | 9, _ => ⟨0, 1, 300, w000000000000011000101_9⟩
  | 10, _ => ⟨0, 1, 300, w000000000000011000101_10⟩
  | 11, _ => ⟨0, 1, 300, w000000000000011000101_11⟩
  | 12, _ => ⟨0, 1, 300, w000000000000011000101_12⟩
  | 13, _ => ⟨0, 0, 300, w000000000000011000101_13⟩
  | 14, _ => ⟨0, 0, 300, w000000000000011000101_14⟩
  | 15, _ => ⟨0, 1, 300, w000000000000011000101_15⟩
  | 16, _ => ⟨0, 1, 300, w000000000000011000101_16⟩
  | 17, _ => ⟨0, 1, 300, w000000000000011000101_17⟩
  | 18, _ => ⟨0, 0, 300, w000000000000011000101_18⟩
  | 19, _ => ⟨0, 1, 300, w000000000000011000101_19⟩
  | 20, _ => ⟨0, 0, 300, w000000000000011000101_20⟩
  | _ + 21, h => absurd h (by omega)

set_option maxHeartbeats 0 in
theorem w000000000000100001111_0 : phaseCheck (wordOf 21 0b000000000000100001111) 13 0 2 300 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000100001111_1 : phaseCheck (wordOf 21 0b000000000000100001111) 13 0 1 300 1 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000100001111_2 : phaseCheck (wordOf 21 0b000000000000100001111) 13 0 1 300 2 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000100001111_3 : phaseCheck (wordOf 21 0b000000000000100001111) 13 0 1 300 3 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000100001111_4 : phaseCheck (wordOf 21 0b000000000000100001111) 13 0 1 300 4 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000100001111_5 : phaseCheck (wordOf 21 0b000000000000100001111) 13 0 1 300 5 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000100001111_6 : phaseCheck (wordOf 21 0b000000000000100001111) 13 0 1 300 6 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000100001111_7 : phaseCheck (wordOf 21 0b000000000000100001111) 13 0 1 300 7 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000100001111_8 : phaseCheck (wordOf 21 0b000000000000100001111) 13 0 1 300 8 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000100001111_9 : phaseCheck (wordOf 21 0b000000000000100001111) 13 0 1 300 9 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000100001111_10 : phaseCheck (wordOf 21 0b000000000000100001111) 13 0 1 300 10 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000100001111_11 : phaseCheck (wordOf 21 0b000000000000100001111) 13 0 1 300 11 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000100001111_12 : phaseCheck (wordOf 21 0b000000000000100001111) 13 0 0 300 12 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000100001111_13 : phaseCheck (wordOf 21 0b000000000000100001111) 13 0 1 300 13 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000100001111_14 : phaseCheck (wordOf 21 0b000000000000100001111) 13 0 1 300 14 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000100001111_15 : phaseCheck (wordOf 21 0b000000000000100001111) 13 0 1 300 15 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000100001111_16 : phaseCheck (wordOf 21 0b000000000000100001111) 13 0 1 300 16 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000100001111_17 : phaseCheck (wordOf 21 0b000000000000100001111) 13 0 0 300 17 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000100001111_18 : phaseCheck (wordOf 21 0b000000000000100001111) 13 0 0 300 18 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000100001111_19 : phaseCheck (wordOf 21 0b000000000000100001111) 13 0 0 300 19 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000100001111_20 : phaseCheck (wordOf 21 0b000000000000100001111) 13 0 0 300 20 = true := by
  decide +kernel

/-- Every phase of `000000000000100001111` at width 13. -/
theorem w000000000000100001111 : ∀ φ, φ < 21 → ∃ D rounds fuel,
    phaseCheck (wordOf 21 0b000000000000100001111) 13 D rounds fuel φ = true
  | 0, _ => ⟨0, 2, 300, w000000000000100001111_0⟩
  | 1, _ => ⟨0, 1, 300, w000000000000100001111_1⟩
  | 2, _ => ⟨0, 1, 300, w000000000000100001111_2⟩
  | 3, _ => ⟨0, 1, 300, w000000000000100001111_3⟩
  | 4, _ => ⟨0, 1, 300, w000000000000100001111_4⟩
  | 5, _ => ⟨0, 1, 300, w000000000000100001111_5⟩
  | 6, _ => ⟨0, 1, 300, w000000000000100001111_6⟩
  | 7, _ => ⟨0, 1, 300, w000000000000100001111_7⟩
  | 8, _ => ⟨0, 1, 300, w000000000000100001111_8⟩
  | 9, _ => ⟨0, 1, 300, w000000000000100001111_9⟩
  | 10, _ => ⟨0, 1, 300, w000000000000100001111_10⟩
  | 11, _ => ⟨0, 1, 300, w000000000000100001111_11⟩
  | 12, _ => ⟨0, 0, 300, w000000000000100001111_12⟩
  | 13, _ => ⟨0, 1, 300, w000000000000100001111_13⟩
  | 14, _ => ⟨0, 1, 300, w000000000000100001111_14⟩
  | 15, _ => ⟨0, 1, 300, w000000000000100001111_15⟩
  | 16, _ => ⟨0, 1, 300, w000000000000100001111_16⟩
  | 17, _ => ⟨0, 0, 300, w000000000000100001111_17⟩
  | 18, _ => ⟨0, 0, 300, w000000000000100001111_18⟩
  | 19, _ => ⟨0, 0, 300, w000000000000100001111_19⟩
  | 20, _ => ⟨0, 0, 300, w000000000000100001111_20⟩
  | _ + 21, h => absurd h (by omega)

set_option maxHeartbeats 0 in
theorem w000000000000100100111_0 : phaseCheck (wordOf 21 0b000000000000100100111) 14 0 1 300 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000100100111_1 : phaseCheck (wordOf 21 0b000000000000100100111) 14 0 1 300 1 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000100100111_2 : phaseCheck (wordOf 21 0b000000000000100100111) 14 0 2 300 2 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000100100111_3 : phaseCheck (wordOf 21 0b000000000000100100111) 14 0 2 300 3 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000100100111_4 : phaseCheck (wordOf 21 0b000000000000100100111) 14 0 2 300 4 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000100100111_5 : phaseCheck (wordOf 21 0b000000000000100100111) 14 0 2 300 5 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000100100111_6 : phaseCheck (wordOf 21 0b000000000000100100111) 14 0 2 300 6 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000100100111_7 : phaseCheck (wordOf 21 0b000000000000100100111) 14 0 1 300 7 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000100100111_8 : phaseCheck (wordOf 21 0b000000000000100100111) 14 0 1 300 8 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000100100111_9 : phaseCheck (wordOf 21 0b000000000000100100111) 14 0 1 300 9 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000100100111_10 : phaseCheck (wordOf 21 0b000000000000100100111) 14 0 1 300 10 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000100100111_11 : phaseCheck (wordOf 21 0b000000000000100100111) 14 0 1 300 11 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000100100111_12 : phaseCheck (wordOf 21 0b000000000000100100111) 14 0 0 300 12 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000100100111_13 : phaseCheck (wordOf 21 0b000000000000100100111) 14 0 1 300 13 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000100100111_14 : phaseCheck (wordOf 21 0b000000000000100100111) 14 0 1 300 14 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000100100111_15 : phaseCheck (wordOf 21 0b000000000000100100111) 14 0 0 300 15 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000100100111_16 : phaseCheck (wordOf 21 0b000000000000100100111) 14 0 1 300 16 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000100100111_17 : phaseCheck (wordOf 21 0b000000000000100100111) 14 0 1 300 17 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000100100111_18 : phaseCheck (wordOf 21 0b000000000000100100111) 14 0 0 300 18 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000100100111_19 : phaseCheck (wordOf 21 0b000000000000100100111) 14 0 0 300 19 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000100100111_20 : phaseCheck (wordOf 21 0b000000000000100100111) 14 0 0 300 20 = true := by
  decide +kernel

/-- Every phase of `000000000000100100111` at width 14. -/
theorem w000000000000100100111 : ∀ φ, φ < 21 → ∃ D rounds fuel,
    phaseCheck (wordOf 21 0b000000000000100100111) 14 D rounds fuel φ = true
  | 0, _ => ⟨0, 1, 300, w000000000000100100111_0⟩
  | 1, _ => ⟨0, 1, 300, w000000000000100100111_1⟩
  | 2, _ => ⟨0, 2, 300, w000000000000100100111_2⟩
  | 3, _ => ⟨0, 2, 300, w000000000000100100111_3⟩
  | 4, _ => ⟨0, 2, 300, w000000000000100100111_4⟩
  | 5, _ => ⟨0, 2, 300, w000000000000100100111_5⟩
  | 6, _ => ⟨0, 2, 300, w000000000000100100111_6⟩
  | 7, _ => ⟨0, 1, 300, w000000000000100100111_7⟩
  | 8, _ => ⟨0, 1, 300, w000000000000100100111_8⟩
  | 9, _ => ⟨0, 1, 300, w000000000000100100111_9⟩
  | 10, _ => ⟨0, 1, 300, w000000000000100100111_10⟩
  | 11, _ => ⟨0, 1, 300, w000000000000100100111_11⟩
  | 12, _ => ⟨0, 0, 300, w000000000000100100111_12⟩
  | 13, _ => ⟨0, 1, 300, w000000000000100100111_13⟩
  | 14, _ => ⟨0, 1, 300, w000000000000100100111_14⟩
  | 15, _ => ⟨0, 0, 300, w000000000000100100111_15⟩
  | 16, _ => ⟨0, 1, 300, w000000000000100100111_16⟩
  | 17, _ => ⟨0, 1, 300, w000000000000100100111_17⟩
  | 18, _ => ⟨0, 0, 300, w000000000000100100111_18⟩
  | 19, _ => ⟨0, 0, 300, w000000000000100100111_19⟩
  | 20, _ => ⟨0, 0, 300, w000000000000100100111_20⟩
  | _ + 21, h => absurd h (by omega)

set_option maxHeartbeats 0 in
theorem w000000000000101000001_0 : phaseCheck (wordOf 21 0b000000000000101000001) 13 0 1 300 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000101000001_1 : phaseCheck (wordOf 21 0b000000000000101000001) 13 0 2 300 1 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000101000001_2 : phaseCheck (wordOf 21 0b000000000000101000001) 13 0 2 300 2 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000101000001_3 : phaseCheck (wordOf 21 0b000000000000101000001) 13 0 2 300 3 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000101000001_4 : phaseCheck (wordOf 21 0b000000000000101000001) 13 0 2 300 4 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000101000001_5 : phaseCheck (wordOf 21 0b000000000000101000001) 13 0 3 300 5 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000101000001_6 : phaseCheck (wordOf 21 0b000000000000101000001) 13 0 3 300 6 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000101000001_7 : phaseCheck (wordOf 21 0b000000000000101000001) 13 0 3 300 7 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000101000001_8 : phaseCheck (wordOf 21 0b000000000000101000001) 13 0 2 300 8 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000101000001_9 : phaseCheck (wordOf 21 0b000000000000101000001) 13 0 2 300 9 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000101000001_10 : phaseCheck (wordOf 21 0b000000000000101000001) 13 0 2 300 10 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000101000001_11 : phaseCheck (wordOf 21 0b000000000000101000001) 13 0 1 300 11 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000101000001_12 : phaseCheck (wordOf 21 0b000000000000101000001) 13 0 0 300 12 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000101000001_13 : phaseCheck (wordOf 21 0b000000000000101000001) 13 0 1 300 13 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000101000001_14 : phaseCheck (wordOf 21 0b000000000000101000001) 13 0 0 300 14 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000101000001_15 : phaseCheck (wordOf 21 0b000000000000101000001) 13 0 2 300 15 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000101000001_16 : phaseCheck (wordOf 21 0b000000000000101000001) 13 0 2 300 16 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000101000001_17 : phaseCheck (wordOf 21 0b000000000000101000001) 13 0 2 300 17 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000101000001_18 : phaseCheck (wordOf 21 0b000000000000101000001) 13 0 2 300 18 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000101000001_19 : phaseCheck (wordOf 21 0b000000000000101000001) 13 0 2 300 19 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000101000001_20 : phaseCheck (wordOf 21 0b000000000000101000001) 13 0 0 300 20 = true := by
  decide +kernel

/-- Every phase of `000000000000101000001` at width 13. -/
theorem w000000000000101000001 : ∀ φ, φ < 21 → ∃ D rounds fuel,
    phaseCheck (wordOf 21 0b000000000000101000001) 13 D rounds fuel φ = true
  | 0, _ => ⟨0, 1, 300, w000000000000101000001_0⟩
  | 1, _ => ⟨0, 2, 300, w000000000000101000001_1⟩
  | 2, _ => ⟨0, 2, 300, w000000000000101000001_2⟩
  | 3, _ => ⟨0, 2, 300, w000000000000101000001_3⟩
  | 4, _ => ⟨0, 2, 300, w000000000000101000001_4⟩
  | 5, _ => ⟨0, 3, 300, w000000000000101000001_5⟩
  | 6, _ => ⟨0, 3, 300, w000000000000101000001_6⟩
  | 7, _ => ⟨0, 3, 300, w000000000000101000001_7⟩
  | 8, _ => ⟨0, 2, 300, w000000000000101000001_8⟩
  | 9, _ => ⟨0, 2, 300, w000000000000101000001_9⟩
  | 10, _ => ⟨0, 2, 300, w000000000000101000001_10⟩
  | 11, _ => ⟨0, 1, 300, w000000000000101000001_11⟩
  | 12, _ => ⟨0, 0, 300, w000000000000101000001_12⟩
  | 13, _ => ⟨0, 1, 300, w000000000000101000001_13⟩
  | 14, _ => ⟨0, 0, 300, w000000000000101000001_14⟩
  | 15, _ => ⟨0, 2, 300, w000000000000101000001_15⟩
  | 16, _ => ⟨0, 2, 300, w000000000000101000001_16⟩
  | 17, _ => ⟨0, 2, 300, w000000000000101000001_17⟩
  | 18, _ => ⟨0, 2, 300, w000000000000101000001_18⟩
  | 19, _ => ⟨0, 2, 300, w000000000000101000001_19⟩
  | 20, _ => ⟨0, 0, 300, w000000000000101000001_20⟩
  | _ + 21, h => absurd h (by omega)

set_option maxHeartbeats 0 in
theorem w000000000000110010111_0 : phaseCheck (wordOf 21 0b000000000000110010111) 13 0 3 300 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000110010111_1 : phaseCheck (wordOf 21 0b000000000000110010111) 13 0 1 300 1 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000110010111_2 : phaseCheck (wordOf 21 0b000000000000110010111) 13 0 1 300 2 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000110010111_3 : phaseCheck (wordOf 21 0b000000000000110010111) 13 0 1 300 3 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000110010111_4 : phaseCheck (wordOf 21 0b000000000000110010111) 13 0 1 300 4 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000110010111_5 : phaseCheck (wordOf 21 0b000000000000110010111) 13 0 1 300 5 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000110010111_6 : phaseCheck (wordOf 21 0b000000000000110010111) 13 0 1 300 6 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000110010111_7 : phaseCheck (wordOf 21 0b000000000000110010111) 13 0 1 300 7 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000110010111_8 : phaseCheck (wordOf 21 0b000000000000110010111) 13 0 1 300 8 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000110010111_9 : phaseCheck (wordOf 21 0b000000000000110010111) 13 0 1 300 9 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000110010111_10 : phaseCheck (wordOf 21 0b000000000000110010111) 13 0 1 300 10 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000110010111_11 : phaseCheck (wordOf 21 0b000000000000110010111) 13 0 1 300 11 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000110010111_12 : phaseCheck (wordOf 21 0b000000000000110010111) 13 0 0 300 12 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000110010111_13 : phaseCheck (wordOf 21 0b000000000000110010111) 13 0 0 300 13 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000110010111_14 : phaseCheck (wordOf 21 0b000000000000110010111) 13 0 1 300 14 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000110010111_15 : phaseCheck (wordOf 21 0b000000000000110010111) 13 0 1 300 15 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000110010111_16 : phaseCheck (wordOf 21 0b000000000000110010111) 13 0 0 300 16 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000110010111_17 : phaseCheck (wordOf 21 0b000000000000110010111) 13 0 1 300 17 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000110010111_18 : phaseCheck (wordOf 21 0b000000000000110010111) 13 0 0 300 18 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000110010111_19 : phaseCheck (wordOf 21 0b000000000000110010111) 13 0 0 300 19 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000110010111_20 : phaseCheck (wordOf 21 0b000000000000110010111) 13 0 0 300 20 = true := by
  decide +kernel

/-- Every phase of `000000000000110010111` at width 13. -/
theorem w000000000000110010111 : ∀ φ, φ < 21 → ∃ D rounds fuel,
    phaseCheck (wordOf 21 0b000000000000110010111) 13 D rounds fuel φ = true
  | 0, _ => ⟨0, 3, 300, w000000000000110010111_0⟩
  | 1, _ => ⟨0, 1, 300, w000000000000110010111_1⟩
  | 2, _ => ⟨0, 1, 300, w000000000000110010111_2⟩
  | 3, _ => ⟨0, 1, 300, w000000000000110010111_3⟩
  | 4, _ => ⟨0, 1, 300, w000000000000110010111_4⟩
  | 5, _ => ⟨0, 1, 300, w000000000000110010111_5⟩
  | 6, _ => ⟨0, 1, 300, w000000000000110010111_6⟩
  | 7, _ => ⟨0, 1, 300, w000000000000110010111_7⟩
  | 8, _ => ⟨0, 1, 300, w000000000000110010111_8⟩
  | 9, _ => ⟨0, 1, 300, w000000000000110010111_9⟩
  | 10, _ => ⟨0, 1, 300, w000000000000110010111_10⟩
  | 11, _ => ⟨0, 1, 300, w000000000000110010111_11⟩
  | 12, _ => ⟨0, 0, 300, w000000000000110010111_12⟩
  | 13, _ => ⟨0, 0, 300, w000000000000110010111_13⟩
  | 14, _ => ⟨0, 1, 300, w000000000000110010111_14⟩
  | 15, _ => ⟨0, 1, 300, w000000000000110010111_15⟩
  | 16, _ => ⟨0, 0, 300, w000000000000110010111_16⟩
  | 17, _ => ⟨0, 1, 300, w000000000000110010111_17⟩
  | 18, _ => ⟨0, 0, 300, w000000000000110010111_18⟩
  | 19, _ => ⟨0, 0, 300, w000000000000110010111_19⟩
  | 20, _ => ⟨0, 0, 300, w000000000000110010111_20⟩
  | _ + 21, h => absurd h (by omega)

set_option maxHeartbeats 0 in
theorem w000000000000110100111_0 : phaseCheck (wordOf 21 0b000000000000110100111) 13 0 1 300 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000110100111_1 : phaseCheck (wordOf 21 0b000000000000110100111) 13 0 3 300 1 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000110100111_2 : phaseCheck (wordOf 21 0b000000000000110100111) 13 0 3 300 2 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000110100111_3 : phaseCheck (wordOf 21 0b000000000000110100111) 13 0 3 300 3 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000110100111_4 : phaseCheck (wordOf 21 0b000000000000110100111) 13 0 2 300 4 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000110100111_5 : phaseCheck (wordOf 21 0b000000000000110100111) 13 0 1 300 5 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000110100111_6 : phaseCheck (wordOf 21 0b000000000000110100111) 13 0 1 300 6 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000110100111_7 : phaseCheck (wordOf 21 0b000000000000110100111) 13 0 1 300 7 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000110100111_8 : phaseCheck (wordOf 21 0b000000000000110100111) 13 0 1 300 8 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000110100111_9 : phaseCheck (wordOf 21 0b000000000000110100111) 13 0 1 300 9 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000110100111_10 : phaseCheck (wordOf 21 0b000000000000110100111) 13 0 1 300 10 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000110100111_11 : phaseCheck (wordOf 21 0b000000000000110100111) 13 0 1 300 11 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000110100111_12 : phaseCheck (wordOf 21 0b000000000000110100111) 13 0 0 300 12 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000110100111_13 : phaseCheck (wordOf 21 0b000000000000110100111) 13 0 0 300 13 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000110100111_14 : phaseCheck (wordOf 21 0b000000000000110100111) 13 0 1 300 14 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000110100111_15 : phaseCheck (wordOf 21 0b000000000000110100111) 13 0 0 300 15 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000110100111_16 : phaseCheck (wordOf 21 0b000000000000110100111) 13 0 1 300 16 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000110100111_17 : phaseCheck (wordOf 21 0b000000000000110100111) 13 0 1 300 17 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000110100111_18 : phaseCheck (wordOf 21 0b000000000000110100111) 13 0 0 300 18 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000110100111_19 : phaseCheck (wordOf 21 0b000000000000110100111) 13 0 0 300 19 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000000110100111_20 : phaseCheck (wordOf 21 0b000000000000110100111) 13 0 0 300 20 = true := by
  decide +kernel

/-- Every phase of `000000000000110100111` at width 13. -/
theorem w000000000000110100111 : ∀ φ, φ < 21 → ∃ D rounds fuel,
    phaseCheck (wordOf 21 0b000000000000110100111) 13 D rounds fuel φ = true
  | 0, _ => ⟨0, 1, 300, w000000000000110100111_0⟩
  | 1, _ => ⟨0, 3, 300, w000000000000110100111_1⟩
  | 2, _ => ⟨0, 3, 300, w000000000000110100111_2⟩
  | 3, _ => ⟨0, 3, 300, w000000000000110100111_3⟩
  | 4, _ => ⟨0, 2, 300, w000000000000110100111_4⟩
  | 5, _ => ⟨0, 1, 300, w000000000000110100111_5⟩
  | 6, _ => ⟨0, 1, 300, w000000000000110100111_6⟩
  | 7, _ => ⟨0, 1, 300, w000000000000110100111_7⟩
  | 8, _ => ⟨0, 1, 300, w000000000000110100111_8⟩
  | 9, _ => ⟨0, 1, 300, w000000000000110100111_9⟩
  | 10, _ => ⟨0, 1, 300, w000000000000110100111_10⟩
  | 11, _ => ⟨0, 1, 300, w000000000000110100111_11⟩
  | 12, _ => ⟨0, 0, 300, w000000000000110100111_12⟩
  | 13, _ => ⟨0, 0, 300, w000000000000110100111_13⟩
  | 14, _ => ⟨0, 1, 300, w000000000000110100111_14⟩
  | 15, _ => ⟨0, 0, 300, w000000000000110100111_15⟩
  | 16, _ => ⟨0, 1, 300, w000000000000110100111_16⟩
  | 17, _ => ⟨0, 1, 300, w000000000000110100111_17⟩
  | 18, _ => ⟨0, 0, 300, w000000000000110100111_18⟩
  | 19, _ => ⟨0, 0, 300, w000000000000110100111_19⟩
  | 20, _ => ⟨0, 0, 300, w000000000000110100111_20⟩
  | _ + 21, h => absurd h (by omega)

set_option maxHeartbeats 0 in
theorem w000000000001100100011_0 : phaseCheck (wordOf 21 0b000000000001100100011) 14 0 3 300 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000001100100011_1 : phaseCheck (wordOf 21 0b000000000001100100011) 14 0 2 300 1 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000001100100011_2 : phaseCheck (wordOf 21 0b000000000001100100011) 14 0 2 300 2 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000001100100011_3 : phaseCheck (wordOf 21 0b000000000001100100011) 14 0 2 300 3 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000001100100011_4 : phaseCheck (wordOf 21 0b000000000001100100011) 14 0 1 300 4 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000001100100011_5 : phaseCheck (wordOf 21 0b000000000001100100011) 14 0 1 300 5 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000001100100011_6 : phaseCheck (wordOf 21 0b000000000001100100011) 14 0 1 300 6 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000001100100011_7 : phaseCheck (wordOf 21 0b000000000001100100011) 14 0 1 300 7 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000001100100011_8 : phaseCheck (wordOf 21 0b000000000001100100011) 14 0 1 300 8 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000001100100011_9 : phaseCheck (wordOf 21 0b000000000001100100011) 14 0 1 300 9 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000001100100011_10 : phaseCheck (wordOf 21 0b000000000001100100011) 14 0 1 300 10 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000001100100011_11 : phaseCheck (wordOf 21 0b000000000001100100011) 14 0 0 300 11 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000001100100011_12 : phaseCheck (wordOf 21 0b000000000001100100011) 14 0 0 300 12 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000001100100011_13 : phaseCheck (wordOf 21 0b000000000001100100011) 14 0 1 300 13 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000001100100011_14 : phaseCheck (wordOf 21 0b000000000001100100011) 14 0 1 300 14 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000001100100011_15 : phaseCheck (wordOf 21 0b000000000001100100011) 14 0 0 300 15 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000001100100011_16 : phaseCheck (wordOf 21 0b000000000001100100011) 14 0 1 300 16 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000001100100011_17 : phaseCheck (wordOf 21 0b000000000001100100011) 14 0 1 300 17 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000001100100011_18 : phaseCheck (wordOf 21 0b000000000001100100011) 14 0 2 300 18 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000001100100011_19 : phaseCheck (wordOf 21 0b000000000001100100011) 14 0 0 300 19 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000001100100011_20 : phaseCheck (wordOf 21 0b000000000001100100011) 14 0 0 300 20 = true := by
  decide +kernel

/-- Every phase of `000000000001100100011` at width 14. -/
theorem w000000000001100100011 : ∀ φ, φ < 21 → ∃ D rounds fuel,
    phaseCheck (wordOf 21 0b000000000001100100011) 14 D rounds fuel φ = true
  | 0, _ => ⟨0, 3, 300, w000000000001100100011_0⟩
  | 1, _ => ⟨0, 2, 300, w000000000001100100011_1⟩
  | 2, _ => ⟨0, 2, 300, w000000000001100100011_2⟩
  | 3, _ => ⟨0, 2, 300, w000000000001100100011_3⟩
  | 4, _ => ⟨0, 1, 300, w000000000001100100011_4⟩
  | 5, _ => ⟨0, 1, 300, w000000000001100100011_5⟩
  | 6, _ => ⟨0, 1, 300, w000000000001100100011_6⟩
  | 7, _ => ⟨0, 1, 300, w000000000001100100011_7⟩
  | 8, _ => ⟨0, 1, 300, w000000000001100100011_8⟩
  | 9, _ => ⟨0, 1, 300, w000000000001100100011_9⟩
  | 10, _ => ⟨0, 1, 300, w000000000001100100011_10⟩
  | 11, _ => ⟨0, 0, 300, w000000000001100100011_11⟩
  | 12, _ => ⟨0, 0, 300, w000000000001100100011_12⟩
  | 13, _ => ⟨0, 1, 300, w000000000001100100011_13⟩
  | 14, _ => ⟨0, 1, 300, w000000000001100100011_14⟩
  | 15, _ => ⟨0, 0, 300, w000000000001100100011_15⟩
  | 16, _ => ⟨0, 1, 300, w000000000001100100011_16⟩
  | 17, _ => ⟨0, 1, 300, w000000000001100100011_17⟩
  | 18, _ => ⟨0, 2, 300, w000000000001100100011_18⟩
  | 19, _ => ⟨0, 0, 300, w000000000001100100011_19⟩
  | 20, _ => ⟨0, 0, 300, w000000000001100100011_20⟩
  | _ + 21, h => absurd h (by omega)

set_option maxHeartbeats 0 in
theorem w000000000001101100111_0 : phaseCheck (wordOf 21 0b000000000001101100111) 14 0 1 300 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000001101100111_1 : phaseCheck (wordOf 21 0b000000000001101100111) 14 0 2 300 1 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000001101100111_2 : phaseCheck (wordOf 21 0b000000000001101100111) 14 0 2 300 2 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000001101100111_3 : phaseCheck (wordOf 21 0b000000000001101100111) 14 0 2 300 3 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000001101100111_4 : phaseCheck (wordOf 21 0b000000000001101100111) 14 0 1 300 4 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000001101100111_5 : phaseCheck (wordOf 21 0b000000000001101100111) 14 0 1 300 5 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000001101100111_6 : phaseCheck (wordOf 21 0b000000000001101100111) 14 0 1 300 6 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000001101100111_7 : phaseCheck (wordOf 21 0b000000000001101100111) 14 0 1 300 7 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000001101100111_8 : phaseCheck (wordOf 21 0b000000000001101100111) 14 0 1 300 8 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000001101100111_9 : phaseCheck (wordOf 21 0b000000000001101100111) 14 0 1 300 9 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000001101100111_10 : phaseCheck (wordOf 21 0b000000000001101100111) 14 0 1 300 10 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000001101100111_11 : phaseCheck (wordOf 21 0b000000000001101100111) 14 0 0 300 11 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000001101100111_12 : phaseCheck (wordOf 21 0b000000000001101100111) 14 0 0 300 12 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000001101100111_13 : phaseCheck (wordOf 21 0b000000000001101100111) 14 0 1 300 13 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000001101100111_14 : phaseCheck (wordOf 21 0b000000000001101100111) 14 0 0 300 14 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000001101100111_15 : phaseCheck (wordOf 21 0b000000000001101100111) 14 0 0 300 15 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000001101100111_16 : phaseCheck (wordOf 21 0b000000000001101100111) 14 0 1 300 16 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000001101100111_17 : phaseCheck (wordOf 21 0b000000000001101100111) 14 0 1 300 17 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000001101100111_18 : phaseCheck (wordOf 21 0b000000000001101100111) 14 0 0 300 18 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000001101100111_19 : phaseCheck (wordOf 21 0b000000000001101100111) 14 0 0 300 19 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000001101100111_20 : phaseCheck (wordOf 21 0b000000000001101100111) 14 0 0 300 20 = true := by
  decide +kernel

/-- Every phase of `000000000001101100111` at width 14. -/
theorem w000000000001101100111 : ∀ φ, φ < 21 → ∃ D rounds fuel,
    phaseCheck (wordOf 21 0b000000000001101100111) 14 D rounds fuel φ = true
  | 0, _ => ⟨0, 1, 300, w000000000001101100111_0⟩
  | 1, _ => ⟨0, 2, 300, w000000000001101100111_1⟩
  | 2, _ => ⟨0, 2, 300, w000000000001101100111_2⟩
  | 3, _ => ⟨0, 2, 300, w000000000001101100111_3⟩
  | 4, _ => ⟨0, 1, 300, w000000000001101100111_4⟩
  | 5, _ => ⟨0, 1, 300, w000000000001101100111_5⟩
  | 6, _ => ⟨0, 1, 300, w000000000001101100111_6⟩
  | 7, _ => ⟨0, 1, 300, w000000000001101100111_7⟩
  | 8, _ => ⟨0, 1, 300, w000000000001101100111_8⟩
  | 9, _ => ⟨0, 1, 300, w000000000001101100111_9⟩
  | 10, _ => ⟨0, 1, 300, w000000000001101100111_10⟩
  | 11, _ => ⟨0, 0, 300, w000000000001101100111_11⟩
  | 12, _ => ⟨0, 0, 300, w000000000001101100111_12⟩
  | 13, _ => ⟨0, 1, 300, w000000000001101100111_13⟩
  | 14, _ => ⟨0, 0, 300, w000000000001101100111_14⟩
  | 15, _ => ⟨0, 0, 300, w000000000001101100111_15⟩
  | 16, _ => ⟨0, 1, 300, w000000000001101100111_16⟩
  | 17, _ => ⟨0, 1, 300, w000000000001101100111_17⟩
  | 18, _ => ⟨0, 0, 300, w000000000001101100111_18⟩
  | 19, _ => ⟨0, 0, 300, w000000000001101100111_19⟩
  | 20, _ => ⟨0, 0, 300, w000000000001101100111_20⟩
  | _ + 21, h => absurd h (by omega)

set_option maxHeartbeats 0 in
theorem w000000000011001001011_0 : phaseCheck (wordOf 21 0b000000000011001001011) 14 0 3 300 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000011001001011_1 : phaseCheck (wordOf 21 0b000000000011001001011) 14 0 2 300 1 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000011001001011_2 : phaseCheck (wordOf 21 0b000000000011001001011) 14 0 2 300 2 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000011001001011_3 : phaseCheck (wordOf 21 0b000000000011001001011) 14 0 1 300 3 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000011001001011_4 : phaseCheck (wordOf 21 0b000000000011001001011) 14 0 1 300 4 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000011001001011_5 : phaseCheck (wordOf 21 0b000000000011001001011) 14 0 1 300 5 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000011001001011_6 : phaseCheck (wordOf 21 0b000000000011001001011) 14 0 1 300 6 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000011001001011_7 : phaseCheck (wordOf 21 0b000000000011001001011) 14 0 1 300 7 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000011001001011_8 : phaseCheck (wordOf 21 0b000000000011001001011) 14 0 1 300 8 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000011001001011_9 : phaseCheck (wordOf 21 0b000000000011001001011) 14 0 1 300 9 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000011001001011_10 : phaseCheck (wordOf 21 0b000000000011001001011) 14 0 0 300 10 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000011001001011_11 : phaseCheck (wordOf 21 0b000000000011001001011) 14 0 0 300 11 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000011001001011_12 : phaseCheck (wordOf 21 0b000000000011001001011) 14 0 2 300 12 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000011001001011_13 : phaseCheck (wordOf 21 0b000000000011001001011) 14 0 1 300 13 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000011001001011_14 : phaseCheck (wordOf 21 0b000000000011001001011) 14 0 0 300 14 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000011001001011_15 : phaseCheck (wordOf 21 0b000000000011001001011) 14 0 1 300 15 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000011001001011_16 : phaseCheck (wordOf 21 0b000000000011001001011) 14 0 2 300 16 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000011001001011_17 : phaseCheck (wordOf 21 0b000000000011001001011) 14 0 0 300 17 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000011001001011_18 : phaseCheck (wordOf 21 0b000000000011001001011) 14 0 2 300 18 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000011001001011_19 : phaseCheck (wordOf 21 0b000000000011001001011) 14 0 0 300 19 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000011001001011_20 : phaseCheck (wordOf 21 0b000000000011001001011) 14 0 0 300 20 = true := by
  decide +kernel

/-- Every phase of `000000000011001001011` at width 14. -/
theorem w000000000011001001011 : ∀ φ, φ < 21 → ∃ D rounds fuel,
    phaseCheck (wordOf 21 0b000000000011001001011) 14 D rounds fuel φ = true
  | 0, _ => ⟨0, 3, 300, w000000000011001001011_0⟩
  | 1, _ => ⟨0, 2, 300, w000000000011001001011_1⟩
  | 2, _ => ⟨0, 2, 300, w000000000011001001011_2⟩
  | 3, _ => ⟨0, 1, 300, w000000000011001001011_3⟩
  | 4, _ => ⟨0, 1, 300, w000000000011001001011_4⟩
  | 5, _ => ⟨0, 1, 300, w000000000011001001011_5⟩
  | 6, _ => ⟨0, 1, 300, w000000000011001001011_6⟩
  | 7, _ => ⟨0, 1, 300, w000000000011001001011_7⟩
  | 8, _ => ⟨0, 1, 300, w000000000011001001011_8⟩
  | 9, _ => ⟨0, 1, 300, w000000000011001001011_9⟩
  | 10, _ => ⟨0, 0, 300, w000000000011001001011_10⟩
  | 11, _ => ⟨0, 0, 300, w000000000011001001011_11⟩
  | 12, _ => ⟨0, 2, 300, w000000000011001001011_12⟩
  | 13, _ => ⟨0, 1, 300, w000000000011001001011_13⟩
  | 14, _ => ⟨0, 0, 300, w000000000011001001011_14⟩
  | 15, _ => ⟨0, 1, 300, w000000000011001001011_15⟩
  | 16, _ => ⟨0, 2, 300, w000000000011001001011_16⟩
  | 17, _ => ⟨0, 0, 300, w000000000011001001011_17⟩
  | 18, _ => ⟨0, 2, 300, w000000000011001001011_18⟩
  | 19, _ => ⟨0, 0, 300, w000000000011001001011_19⟩
  | 20, _ => ⟨0, 0, 300, w000000000011001001011_20⟩
  | _ + 21, h => absurd h (by omega)

set_option maxHeartbeats 0 in
theorem w000000000100101111011_0 : phaseCheck (wordOf 21 0b000000000100101111011) 14 0 2 300 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000100101111011_1 : phaseCheck (wordOf 21 0b000000000100101111011) 14 0 1 300 1 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000100101111011_2 : phaseCheck (wordOf 21 0b000000000100101111011) 14 0 1 300 2 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000100101111011_3 : phaseCheck (wordOf 21 0b000000000100101111011) 14 0 1 300 3 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000100101111011_4 : phaseCheck (wordOf 21 0b000000000100101111011) 14 0 1 300 4 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000100101111011_5 : phaseCheck (wordOf 21 0b000000000100101111011) 14 0 1 300 5 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000100101111011_6 : phaseCheck (wordOf 21 0b000000000100101111011) 14 0 1 300 6 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000100101111011_7 : phaseCheck (wordOf 21 0b000000000100101111011) 14 0 1 300 7 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000100101111011_8 : phaseCheck (wordOf 21 0b000000000100101111011) 14 0 1 300 8 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000100101111011_9 : phaseCheck (wordOf 21 0b000000000100101111011) 14 0 0 300 9 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000100101111011_10 : phaseCheck (wordOf 21 0b000000000100101111011) 14 0 1 300 10 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000100101111011_11 : phaseCheck (wordOf 21 0b000000000100101111011) 14 0 1 300 11 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000100101111011_12 : phaseCheck (wordOf 21 0b000000000100101111011) 14 0 0 300 12 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000100101111011_13 : phaseCheck (wordOf 21 0b000000000100101111011) 14 0 1 300 13 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000100101111011_14 : phaseCheck (wordOf 21 0b000000000100101111011) 14 0 0 300 14 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000100101111011_15 : phaseCheck (wordOf 21 0b000000000100101111011) 14 0 0 300 15 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000100101111011_16 : phaseCheck (wordOf 21 0b000000000100101111011) 14 0 0 300 16 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000100101111011_17 : phaseCheck (wordOf 21 0b000000000100101111011) 14 0 0 300 17 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000100101111011_18 : phaseCheck (wordOf 21 0b000000000100101111011) 14 0 1 300 18 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000100101111011_19 : phaseCheck (wordOf 21 0b000000000100101111011) 14 0 0 300 19 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000100101111011_20 : phaseCheck (wordOf 21 0b000000000100101111011) 14 0 0 300 20 = true := by
  decide +kernel

/-- Every phase of `000000000100101111011` at width 14. -/
theorem w000000000100101111011 : ∀ φ, φ < 21 → ∃ D rounds fuel,
    phaseCheck (wordOf 21 0b000000000100101111011) 14 D rounds fuel φ = true
  | 0, _ => ⟨0, 2, 300, w000000000100101111011_0⟩
  | 1, _ => ⟨0, 1, 300, w000000000100101111011_1⟩
  | 2, _ => ⟨0, 1, 300, w000000000100101111011_2⟩
  | 3, _ => ⟨0, 1, 300, w000000000100101111011_3⟩
  | 4, _ => ⟨0, 1, 300, w000000000100101111011_4⟩
  | 5, _ => ⟨0, 1, 300, w000000000100101111011_5⟩
  | 6, _ => ⟨0, 1, 300, w000000000100101111011_6⟩
  | 7, _ => ⟨0, 1, 300, w000000000100101111011_7⟩
  | 8, _ => ⟨0, 1, 300, w000000000100101111011_8⟩
  | 9, _ => ⟨0, 0, 300, w000000000100101111011_9⟩
  | 10, _ => ⟨0, 1, 300, w000000000100101111011_10⟩
  | 11, _ => ⟨0, 1, 300, w000000000100101111011_11⟩
  | 12, _ => ⟨0, 0, 300, w000000000100101111011_12⟩
  | 13, _ => ⟨0, 1, 300, w000000000100101111011_13⟩
  | 14, _ => ⟨0, 0, 300, w000000000100101111011_14⟩
  | 15, _ => ⟨0, 0, 300, w000000000100101111011_15⟩
  | 16, _ => ⟨0, 0, 300, w000000000100101111011_16⟩
  | 17, _ => ⟨0, 0, 300, w000000000100101111011_17⟩
  | 18, _ => ⟨0, 1, 300, w000000000100101111011_18⟩
  | 19, _ => ⟨0, 0, 300, w000000000100101111011_19⟩
  | 20, _ => ⟨0, 0, 300, w000000000100101111011_20⟩
  | _ + 21, h => absurd h (by omega)

set_option maxHeartbeats 0 in
theorem w000000000111100111111_0 : phaseCheck (wordOf 21 0b000000000111100111111) 14 0 1 300 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000111100111111_1 : phaseCheck (wordOf 21 0b000000000111100111111) 14 0 1 300 1 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000111100111111_2 : phaseCheck (wordOf 21 0b000000000111100111111) 14 0 1 300 2 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000111100111111_3 : phaseCheck (wordOf 21 0b000000000111100111111) 14 0 1 300 3 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000111100111111_4 : phaseCheck (wordOf 21 0b000000000111100111111) 14 0 1 300 4 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000111100111111_5 : phaseCheck (wordOf 21 0b000000000111100111111) 14 0 1 300 5 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000111100111111_6 : phaseCheck (wordOf 21 0b000000000111100111111) 14 0 1 300 6 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000111100111111_7 : phaseCheck (wordOf 21 0b000000000111100111111) 14 0 1 300 7 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000111100111111_8 : phaseCheck (wordOf 21 0b000000000111100111111) 14 0 1 300 8 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000111100111111_9 : phaseCheck (wordOf 21 0b000000000111100111111) 14 0 0 300 9 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000111100111111_10 : phaseCheck (wordOf 21 0b000000000111100111111) 14 0 0 300 10 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000111100111111_11 : phaseCheck (wordOf 21 0b000000000111100111111) 14 0 0 300 11 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000111100111111_12 : phaseCheck (wordOf 21 0b000000000111100111111) 14 0 0 300 12 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000111100111111_13 : phaseCheck (wordOf 21 0b000000000111100111111) 14 0 1 300 13 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000111100111111_14 : phaseCheck (wordOf 21 0b000000000111100111111) 14 0 1 300 14 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000111100111111_15 : phaseCheck (wordOf 21 0b000000000111100111111) 14 0 0 300 15 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000111100111111_16 : phaseCheck (wordOf 21 0b000000000111100111111) 14 0 0 300 16 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000111100111111_17 : phaseCheck (wordOf 21 0b000000000111100111111) 14 0 0 300 17 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000111100111111_18 : phaseCheck (wordOf 21 0b000000000111100111111) 14 0 0 300 18 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000111100111111_19 : phaseCheck (wordOf 21 0b000000000111100111111) 14 0 0 300 19 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000111100111111_20 : phaseCheck (wordOf 21 0b000000000111100111111) 14 0 0 300 20 = true := by
  decide +kernel

/-- Every phase of `000000000111100111111` at width 14. -/
theorem w000000000111100111111 : ∀ φ, φ < 21 → ∃ D rounds fuel,
    phaseCheck (wordOf 21 0b000000000111100111111) 14 D rounds fuel φ = true
  | 0, _ => ⟨0, 1, 300, w000000000111100111111_0⟩
  | 1, _ => ⟨0, 1, 300, w000000000111100111111_1⟩
  | 2, _ => ⟨0, 1, 300, w000000000111100111111_2⟩
  | 3, _ => ⟨0, 1, 300, w000000000111100111111_3⟩
  | 4, _ => ⟨0, 1, 300, w000000000111100111111_4⟩
  | 5, _ => ⟨0, 1, 300, w000000000111100111111_5⟩
  | 6, _ => ⟨0, 1, 300, w000000000111100111111_6⟩
  | 7, _ => ⟨0, 1, 300, w000000000111100111111_7⟩
  | 8, _ => ⟨0, 1, 300, w000000000111100111111_8⟩
  | 9, _ => ⟨0, 0, 300, w000000000111100111111_9⟩
  | 10, _ => ⟨0, 0, 300, w000000000111100111111_10⟩
  | 11, _ => ⟨0, 0, 300, w000000000111100111111_11⟩
  | 12, _ => ⟨0, 0, 300, w000000000111100111111_12⟩
  | 13, _ => ⟨0, 1, 300, w000000000111100111111_13⟩
  | 14, _ => ⟨0, 1, 300, w000000000111100111111_14⟩
  | 15, _ => ⟨0, 0, 300, w000000000111100111111_15⟩
  | 16, _ => ⟨0, 0, 300, w000000000111100111111_16⟩
  | 17, _ => ⟨0, 0, 300, w000000000111100111111_17⟩
  | 18, _ => ⟨0, 0, 300, w000000000111100111111_18⟩
  | 19, _ => ⟨0, 0, 300, w000000000111100111111_19⟩
  | 20, _ => ⟨0, 0, 300, w000000000111100111111_20⟩
  | _ + 21, h => absurd h (by omega)

set_option maxHeartbeats 0 in
theorem w000000000111110000001_0 : phaseCheck (wordOf 21 0b000000000111110000001) 13 0 1 300 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000111110000001_1 : phaseCheck (wordOf 21 0b000000000111110000001) 13 0 3 300 1 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000111110000001_2 : phaseCheck (wordOf 21 0b000000000111110000001) 13 0 1 300 2 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000111110000001_3 : phaseCheck (wordOf 21 0b000000000111110000001) 13 0 1 300 3 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000111110000001_4 : phaseCheck (wordOf 21 0b000000000111110000001) 13 0 1 300 4 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000111110000001_5 : phaseCheck (wordOf 21 0b000000000111110000001) 13 0 1 300 5 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000111110000001_6 : phaseCheck (wordOf 21 0b000000000111110000001) 13 0 1 300 6 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000111110000001_7 : phaseCheck (wordOf 21 0b000000000111110000001) 13 0 1 300 7 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000111110000001_8 : phaseCheck (wordOf 21 0b000000000111110000001) 13 0 1 300 8 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000111110000001_9 : phaseCheck (wordOf 21 0b000000000111110000001) 13 0 0 300 9 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000111110000001_10 : phaseCheck (wordOf 21 0b000000000111110000001) 13 0 0 300 10 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000111110000001_11 : phaseCheck (wordOf 21 0b000000000111110000001) 13 0 0 300 11 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000111110000001_12 : phaseCheck (wordOf 21 0b000000000111110000001) 13 0 0 300 12 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000111110000001_13 : phaseCheck (wordOf 21 0b000000000111110000001) 13 0 0 300 13 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000111110000001_14 : phaseCheck (wordOf 21 0b000000000111110000001) 13 0 1 300 14 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000111110000001_15 : phaseCheck (wordOf 21 0b000000000111110000001) 13 0 4 300 15 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000111110000001_16 : phaseCheck (wordOf 21 0b000000000111110000001) 13 0 1 300 16 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000111110000001_17 : phaseCheck (wordOf 21 0b000000000111110000001) 13 0 1 300 17 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000111110000001_18 : phaseCheck (wordOf 21 0b000000000111110000001) 13 0 1 300 18 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000111110000001_19 : phaseCheck (wordOf 21 0b000000000111110000001) 13 0 1 300 19 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000000111110000001_20 : phaseCheck (wordOf 21 0b000000000111110000001) 13 0 0 300 20 = true := by
  decide +kernel

/-- Every phase of `000000000111110000001` at width 13. -/
theorem w000000000111110000001 : ∀ φ, φ < 21 → ∃ D rounds fuel,
    phaseCheck (wordOf 21 0b000000000111110000001) 13 D rounds fuel φ = true
  | 0, _ => ⟨0, 1, 300, w000000000111110000001_0⟩
  | 1, _ => ⟨0, 3, 300, w000000000111110000001_1⟩
  | 2, _ => ⟨0, 1, 300, w000000000111110000001_2⟩
  | 3, _ => ⟨0, 1, 300, w000000000111110000001_3⟩
  | 4, _ => ⟨0, 1, 300, w000000000111110000001_4⟩
  | 5, _ => ⟨0, 1, 300, w000000000111110000001_5⟩
  | 6, _ => ⟨0, 1, 300, w000000000111110000001_6⟩
  | 7, _ => ⟨0, 1, 300, w000000000111110000001_7⟩
  | 8, _ => ⟨0, 1, 300, w000000000111110000001_8⟩
  | 9, _ => ⟨0, 0, 300, w000000000111110000001_9⟩
  | 10, _ => ⟨0, 0, 300, w000000000111110000001_10⟩
  | 11, _ => ⟨0, 0, 300, w000000000111110000001_11⟩
  | 12, _ => ⟨0, 0, 300, w000000000111110000001_12⟩
  | 13, _ => ⟨0, 0, 300, w000000000111110000001_13⟩
  | 14, _ => ⟨0, 1, 300, w000000000111110000001_14⟩
  | 15, _ => ⟨0, 4, 300, w000000000111110000001_15⟩
  | 16, _ => ⟨0, 1, 300, w000000000111110000001_16⟩
  | 17, _ => ⟨0, 1, 300, w000000000111110000001_17⟩
  | 18, _ => ⟨0, 1, 300, w000000000111110000001_18⟩
  | 19, _ => ⟨0, 1, 300, w000000000111110000001_19⟩
  | 20, _ => ⟨0, 0, 300, w000000000111110000001_20⟩
  | _ + 21, h => absurd h (by omega)

set_option maxHeartbeats 0 in
theorem w000000001001011111011_0 : phaseCheck (wordOf 21 0b000000001001011111011) 13 0 2 300 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000001001011111011_1 : phaseCheck (wordOf 21 0b000000001001011111011) 13 0 2 300 1 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000001001011111011_2 : phaseCheck (wordOf 21 0b000000001001011111011) 13 0 1 300 2 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000001001011111011_3 : phaseCheck (wordOf 21 0b000000001001011111011) 13 0 1 300 3 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000001001011111011_4 : phaseCheck (wordOf 21 0b000000001001011111011) 13 0 1 300 4 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000001001011111011_5 : phaseCheck (wordOf 21 0b000000001001011111011) 13 0 1 300 5 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000001001011111011_6 : phaseCheck (wordOf 21 0b000000001001011111011) 13 0 1 300 6 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000001001011111011_7 : phaseCheck (wordOf 21 0b000000001001011111011) 13 0 1 300 7 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000001001011111011_8 : phaseCheck (wordOf 21 0b000000001001011111011) 13 0 0 300 8 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000001001011111011_9 : phaseCheck (wordOf 21 0b000000001001011111011) 13 0 1 300 9 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000001001011111011_10 : phaseCheck (wordOf 21 0b000000001001011111011) 13 0 1 300 10 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000001001011111011_11 : phaseCheck (wordOf 21 0b000000001001011111011) 13 0 0 300 11 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000001001011111011_12 : phaseCheck (wordOf 21 0b000000001001011111011) 13 0 1 300 12 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000001001011111011_13 : phaseCheck (wordOf 21 0b000000001001011111011) 13 0 0 300 13 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000001001011111011_14 : phaseCheck (wordOf 21 0b000000001001011111011) 13 0 0 300 14 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000001001011111011_15 : phaseCheck (wordOf 21 0b000000001001011111011) 13 0 0 300 15 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000001001011111011_16 : phaseCheck (wordOf 21 0b000000001001011111011) 13 0 0 300 16 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000001001011111011_17 : phaseCheck (wordOf 21 0b000000001001011111011) 13 0 0 300 17 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000001001011111011_18 : phaseCheck (wordOf 21 0b000000001001011111011) 13 0 2 300 18 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000001001011111011_19 : phaseCheck (wordOf 21 0b000000001001011111011) 13 0 0 300 19 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000001001011111011_20 : phaseCheck (wordOf 21 0b000000001001011111011) 13 0 0 300 20 = true := by
  decide +kernel

/-- Every phase of `000000001001011111011` at width 13. -/
theorem w000000001001011111011 : ∀ φ, φ < 21 → ∃ D rounds fuel,
    phaseCheck (wordOf 21 0b000000001001011111011) 13 D rounds fuel φ = true
  | 0, _ => ⟨0, 2, 300, w000000001001011111011_0⟩
  | 1, _ => ⟨0, 2, 300, w000000001001011111011_1⟩
  | 2, _ => ⟨0, 1, 300, w000000001001011111011_2⟩
  | 3, _ => ⟨0, 1, 300, w000000001001011111011_3⟩
  | 4, _ => ⟨0, 1, 300, w000000001001011111011_4⟩
  | 5, _ => ⟨0, 1, 300, w000000001001011111011_5⟩
  | 6, _ => ⟨0, 1, 300, w000000001001011111011_6⟩
  | 7, _ => ⟨0, 1, 300, w000000001001011111011_7⟩
  | 8, _ => ⟨0, 0, 300, w000000001001011111011_8⟩
  | 9, _ => ⟨0, 1, 300, w000000001001011111011_9⟩
  | 10, _ => ⟨0, 1, 300, w000000001001011111011_10⟩
  | 11, _ => ⟨0, 0, 300, w000000001001011111011_11⟩
  | 12, _ => ⟨0, 1, 300, w000000001001011111011_12⟩
  | 13, _ => ⟨0, 0, 300, w000000001001011111011_13⟩
  | 14, _ => ⟨0, 0, 300, w000000001001011111011_14⟩
  | 15, _ => ⟨0, 0, 300, w000000001001011111011_15⟩
  | 16, _ => ⟨0, 0, 300, w000000001001011111011_16⟩
  | 17, _ => ⟨0, 0, 300, w000000001001011111011_17⟩
  | 18, _ => ⟨0, 2, 300, w000000001001011111011_18⟩
  | 19, _ => ⟨0, 0, 300, w000000001001011111011_19⟩
  | 20, _ => ⟨0, 0, 300, w000000001001011111011_20⟩
  | _ + 21, h => absurd h (by omega)

set_option maxHeartbeats 0 in
theorem w000000001011100111011_0 : phaseCheck (wordOf 21 0b000000001011100111011) 14 0 1 300 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000001011100111011_1 : phaseCheck (wordOf 21 0b000000001011100111011) 14 0 2 300 1 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000001011100111011_2 : phaseCheck (wordOf 21 0b000000001011100111011) 14 0 2 300 2 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000001011100111011_3 : phaseCheck (wordOf 21 0b000000001011100111011) 14 0 2 300 3 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000001011100111011_4 : phaseCheck (wordOf 21 0b000000001011100111011) 14 0 1 300 4 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000001011100111011_5 : phaseCheck (wordOf 21 0b000000001011100111011) 14 0 1 300 5 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000001011100111011_6 : phaseCheck (wordOf 21 0b000000001011100111011) 14 0 1 300 6 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000001011100111011_7 : phaseCheck (wordOf 21 0b000000001011100111011) 14 0 1 300 7 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000001011100111011_8 : phaseCheck (wordOf 21 0b000000001011100111011) 14 0 0 300 8 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000001011100111011_9 : phaseCheck (wordOf 21 0b000000001011100111011) 14 0 1 300 9 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000001011100111011_10 : phaseCheck (wordOf 21 0b000000001011100111011) 14 0 0 300 10 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000001011100111011_11 : phaseCheck (wordOf 21 0b000000001011100111011) 14 0 0 300 11 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000001011100111011_12 : phaseCheck (wordOf 21 0b000000001011100111011) 14 0 0 300 12 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000001011100111011_13 : phaseCheck (wordOf 21 0b000000001011100111011) 14 0 1 300 13 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000001011100111011_14 : phaseCheck (wordOf 21 0b000000001011100111011) 14 0 2 300 14 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000001011100111011_15 : phaseCheck (wordOf 21 0b000000001011100111011) 14 0 0 300 15 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000001011100111011_16 : phaseCheck (wordOf 21 0b000000001011100111011) 14 0 0 300 16 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000001011100111011_17 : phaseCheck (wordOf 21 0b000000001011100111011) 14 0 0 300 17 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000001011100111011_18 : phaseCheck (wordOf 21 0b000000001011100111011) 14 0 1 300 18 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000001011100111011_19 : phaseCheck (wordOf 21 0b000000001011100111011) 14 0 0 300 19 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000001011100111011_20 : phaseCheck (wordOf 21 0b000000001011100111011) 14 0 0 300 20 = true := by
  decide +kernel

/-- Every phase of `000000001011100111011` at width 14. -/
theorem w000000001011100111011 : ∀ φ, φ < 21 → ∃ D rounds fuel,
    phaseCheck (wordOf 21 0b000000001011100111011) 14 D rounds fuel φ = true
  | 0, _ => ⟨0, 1, 300, w000000001011100111011_0⟩
  | 1, _ => ⟨0, 2, 300, w000000001011100111011_1⟩
  | 2, _ => ⟨0, 2, 300, w000000001011100111011_2⟩
  | 3, _ => ⟨0, 2, 300, w000000001011100111011_3⟩
  | 4, _ => ⟨0, 1, 300, w000000001011100111011_4⟩
  | 5, _ => ⟨0, 1, 300, w000000001011100111011_5⟩
  | 6, _ => ⟨0, 1, 300, w000000001011100111011_6⟩
  | 7, _ => ⟨0, 1, 300, w000000001011100111011_7⟩
  | 8, _ => ⟨0, 0, 300, w000000001011100111011_8⟩
  | 9, _ => ⟨0, 1, 300, w000000001011100111011_9⟩
  | 10, _ => ⟨0, 0, 300, w000000001011100111011_10⟩
  | 11, _ => ⟨0, 0, 300, w000000001011100111011_11⟩
  | 12, _ => ⟨0, 0, 300, w000000001011100111011_12⟩
  | 13, _ => ⟨0, 1, 300, w000000001011100111011_13⟩
  | 14, _ => ⟨0, 2, 300, w000000001011100111011_14⟩
  | 15, _ => ⟨0, 0, 300, w000000001011100111011_15⟩
  | 16, _ => ⟨0, 0, 300, w000000001011100111011_16⟩
  | 17, _ => ⟨0, 0, 300, w000000001011100111011_17⟩
  | 18, _ => ⟨0, 1, 300, w000000001011100111011_18⟩
  | 19, _ => ⟨0, 0, 300, w000000001011100111011_19⟩
  | 20, _ => ⟨0, 0, 300, w000000001011100111011_20⟩
  | _ + 21, h => absurd h (by omega)

set_option maxHeartbeats 0 in
theorem w000000001101100111011_0 : phaseCheck (wordOf 21 0b000000001101100111011) 14 0 2 300 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000001101100111011_1 : phaseCheck (wordOf 21 0b000000001101100111011) 14 0 2 300 1 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000001101100111011_2 : phaseCheck (wordOf 21 0b000000001101100111011) 14 0 1 300 2 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000001101100111011_3 : phaseCheck (wordOf 21 0b000000001101100111011) 14 0 1 300 3 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000001101100111011_4 : phaseCheck (wordOf 21 0b000000001101100111011) 14 0 1 300 4 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000001101100111011_5 : phaseCheck (wordOf 21 0b000000001101100111011) 14 0 1 300 5 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000001101100111011_6 : phaseCheck (wordOf 21 0b000000001101100111011) 14 0 1 300 6 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000001101100111011_7 : phaseCheck (wordOf 21 0b000000001101100111011) 14 0 1 300 7 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000001101100111011_8 : phaseCheck (wordOf 21 0b000000001101100111011) 14 0 0 300 8 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000001101100111011_9 : phaseCheck (wordOf 21 0b000000001101100111011) 14 0 0 300 9 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000001101100111011_10 : phaseCheck (wordOf 21 0b000000001101100111011) 14 0 1 300 10 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000001101100111011_11 : phaseCheck (wordOf 21 0b000000001101100111011) 14 0 0 300 11 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000001101100111011_12 : phaseCheck (wordOf 21 0b000000001101100111011) 14 0 0 300 12 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000001101100111011_13 : phaseCheck (wordOf 21 0b000000001101100111011) 14 0 1 300 13 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000001101100111011_14 : phaseCheck (wordOf 21 0b000000001101100111011) 14 0 1 300 14 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000001101100111011_15 : phaseCheck (wordOf 21 0b000000001101100111011) 14 0 0 300 15 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000001101100111011_16 : phaseCheck (wordOf 21 0b000000001101100111011) 14 0 0 300 16 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000001101100111011_17 : phaseCheck (wordOf 21 0b000000001101100111011) 14 0 0 300 17 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000001101100111011_18 : phaseCheck (wordOf 21 0b000000001101100111011) 14 0 1 300 18 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000001101100111011_19 : phaseCheck (wordOf 21 0b000000001101100111011) 14 0 0 300 19 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000001101100111011_20 : phaseCheck (wordOf 21 0b000000001101100111011) 14 0 0 300 20 = true := by
  decide +kernel

/-- Every phase of `000000001101100111011` at width 14. -/
theorem w000000001101100111011 : ∀ φ, φ < 21 → ∃ D rounds fuel,
    phaseCheck (wordOf 21 0b000000001101100111011) 14 D rounds fuel φ = true
  | 0, _ => ⟨0, 2, 300, w000000001101100111011_0⟩
  | 1, _ => ⟨0, 2, 300, w000000001101100111011_1⟩
  | 2, _ => ⟨0, 1, 300, w000000001101100111011_2⟩
  | 3, _ => ⟨0, 1, 300, w000000001101100111011_3⟩
  | 4, _ => ⟨0, 1, 300, w000000001101100111011_4⟩
  | 5, _ => ⟨0, 1, 300, w000000001101100111011_5⟩
  | 6, _ => ⟨0, 1, 300, w000000001101100111011_6⟩
  | 7, _ => ⟨0, 1, 300, w000000001101100111011_7⟩
  | 8, _ => ⟨0, 0, 300, w000000001101100111011_8⟩
  | 9, _ => ⟨0, 0, 300, w000000001101100111011_9⟩
  | 10, _ => ⟨0, 1, 300, w000000001101100111011_10⟩
  | 11, _ => ⟨0, 0, 300, w000000001101100111011_11⟩
  | 12, _ => ⟨0, 0, 300, w000000001101100111011_12⟩
  | 13, _ => ⟨0, 1, 300, w000000001101100111011_13⟩
  | 14, _ => ⟨0, 1, 300, w000000001101100111011_14⟩
  | 15, _ => ⟨0, 0, 300, w000000001101100111011_15⟩
  | 16, _ => ⟨0, 0, 300, w000000001101100111011_16⟩
  | 17, _ => ⟨0, 0, 300, w000000001101100111011_17⟩
  | 18, _ => ⟨0, 1, 300, w000000001101100111011_18⟩
  | 19, _ => ⟨0, 0, 300, w000000001101100111011_19⟩
  | 20, _ => ⟨0, 0, 300, w000000001101100111011_20⟩
  | _ + 21, h => absurd h (by omega)

set_option maxHeartbeats 0 in
theorem w000000010111111100111_0 : phaseCheck (wordOf 21 0b000000010111111100111) 14 0 1 300 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000010111111100111_1 : phaseCheck (wordOf 21 0b000000010111111100111) 14 0 2 300 1 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000010111111100111_2 : phaseCheck (wordOf 21 0b000000010111111100111) 14 0 2 300 2 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000010111111100111_3 : phaseCheck (wordOf 21 0b000000010111111100111) 14 0 1 300 3 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000010111111100111_4 : phaseCheck (wordOf 21 0b000000010111111100111) 14 0 2 300 4 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000010111111100111_5 : phaseCheck (wordOf 21 0b000000010111111100111) 14 0 1 300 5 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000010111111100111_6 : phaseCheck (wordOf 21 0b000000010111111100111) 14 0 1 300 6 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000010111111100111_7 : phaseCheck (wordOf 21 0b000000010111111100111) 14 0 0 300 7 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000010111111100111_8 : phaseCheck (wordOf 21 0b000000010111111100111) 14 0 1 300 8 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000010111111100111_9 : phaseCheck (wordOf 21 0b000000010111111100111) 14 0 0 300 9 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000010111111100111_10 : phaseCheck (wordOf 21 0b000000010111111100111) 14 0 0 300 10 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000010111111100111_11 : phaseCheck (wordOf 21 0b000000010111111100111) 14 0 0 300 11 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000010111111100111_12 : phaseCheck (wordOf 21 0b000000010111111100111) 14 0 0 300 12 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000010111111100111_13 : phaseCheck (wordOf 21 0b000000010111111100111) 14 0 0 300 13 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000010111111100111_14 : phaseCheck (wordOf 21 0b000000010111111100111) 14 0 0 300 14 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000010111111100111_15 : phaseCheck (wordOf 21 0b000000010111111100111) 14 0 0 300 15 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000010111111100111_16 : phaseCheck (wordOf 21 0b000000010111111100111) 14 0 3 300 16 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000010111111100111_17 : phaseCheck (wordOf 21 0b000000010111111100111) 14 0 1 300 17 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000010111111100111_18 : phaseCheck (wordOf 21 0b000000010111111100111) 14 0 0 300 18 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000010111111100111_19 : phaseCheck (wordOf 21 0b000000010111111100111) 14 0 0 300 19 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000010111111100111_20 : phaseCheck (wordOf 21 0b000000010111111100111) 14 0 0 300 20 = true := by
  decide +kernel

/-- Every phase of `000000010111111100111` at width 14. -/
theorem w000000010111111100111 : ∀ φ, φ < 21 → ∃ D rounds fuel,
    phaseCheck (wordOf 21 0b000000010111111100111) 14 D rounds fuel φ = true
  | 0, _ => ⟨0, 1, 300, w000000010111111100111_0⟩
  | 1, _ => ⟨0, 2, 300, w000000010111111100111_1⟩
  | 2, _ => ⟨0, 2, 300, w000000010111111100111_2⟩
  | 3, _ => ⟨0, 1, 300, w000000010111111100111_3⟩
  | 4, _ => ⟨0, 2, 300, w000000010111111100111_4⟩
  | 5, _ => ⟨0, 1, 300, w000000010111111100111_5⟩
  | 6, _ => ⟨0, 1, 300, w000000010111111100111_6⟩
  | 7, _ => ⟨0, 0, 300, w000000010111111100111_7⟩
  | 8, _ => ⟨0, 1, 300, w000000010111111100111_8⟩
  | 9, _ => ⟨0, 0, 300, w000000010111111100111_9⟩
  | 10, _ => ⟨0, 0, 300, w000000010111111100111_10⟩
  | 11, _ => ⟨0, 0, 300, w000000010111111100111_11⟩
  | 12, _ => ⟨0, 0, 300, w000000010111111100111_12⟩
  | 13, _ => ⟨0, 0, 300, w000000010111111100111_13⟩
  | 14, _ => ⟨0, 0, 300, w000000010111111100111_14⟩
  | 15, _ => ⟨0, 0, 300, w000000010111111100111_15⟩
  | 16, _ => ⟨0, 3, 300, w000000010111111100111_16⟩
  | 17, _ => ⟨0, 1, 300, w000000010111111100111_17⟩
  | 18, _ => ⟨0, 0, 300, w000000010111111100111_18⟩
  | 19, _ => ⟨0, 0, 300, w000000010111111100111_19⟩
  | 20, _ => ⟨0, 0, 300, w000000010111111100111_20⟩
  | _ + 21, h => absurd h (by omega)

set_option maxHeartbeats 0 in
theorem w000000101110011111011_0 : phaseCheck (wordOf 21 0b000000101110011111011) 14 0 2 300 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000101110011111011_1 : phaseCheck (wordOf 21 0b000000101110011111011) 14 0 1 300 1 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000101110011111011_2 : phaseCheck (wordOf 21 0b000000101110011111011) 14 0 1 300 2 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000101110011111011_3 : phaseCheck (wordOf 21 0b000000101110011111011) 14 0 1 300 3 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000101110011111011_4 : phaseCheck (wordOf 21 0b000000101110011111011) 14 0 1 300 4 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000101110011111011_5 : phaseCheck (wordOf 21 0b000000101110011111011) 14 0 1 300 5 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000101110011111011_6 : phaseCheck (wordOf 21 0b000000101110011111011) 14 0 0 300 6 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000101110011111011_7 : phaseCheck (wordOf 21 0b000000101110011111011) 14 0 1 300 7 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000101110011111011_8 : phaseCheck (wordOf 21 0b000000101110011111011) 14 0 0 300 8 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000101110011111011_9 : phaseCheck (wordOf 21 0b000000101110011111011) 14 0 0 300 9 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000101110011111011_10 : phaseCheck (wordOf 21 0b000000101110011111011) 14 0 0 300 10 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000101110011111011_11 : phaseCheck (wordOf 21 0b000000101110011111011) 14 0 1 300 11 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000101110011111011_12 : phaseCheck (wordOf 21 0b000000101110011111011) 14 0 2 300 12 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000101110011111011_13 : phaseCheck (wordOf 21 0b000000101110011111011) 14 0 0 300 13 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000101110011111011_14 : phaseCheck (wordOf 21 0b000000101110011111011) 14 0 0 300 14 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000101110011111011_15 : phaseCheck (wordOf 21 0b000000101110011111011) 14 0 0 300 15 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000101110011111011_16 : phaseCheck (wordOf 21 0b000000101110011111011) 14 0 0 300 16 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000101110011111011_17 : phaseCheck (wordOf 21 0b000000101110011111011) 14 0 0 300 17 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000101110011111011_18 : phaseCheck (wordOf 21 0b000000101110011111011) 14 0 1 300 18 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000101110011111011_19 : phaseCheck (wordOf 21 0b000000101110011111011) 14 0 0 300 19 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000000101110011111011_20 : phaseCheck (wordOf 21 0b000000101110011111011) 14 0 0 300 20 = true := by
  decide +kernel

/-- Every phase of `000000101110011111011` at width 14. -/
theorem w000000101110011111011 : ∀ φ, φ < 21 → ∃ D rounds fuel,
    phaseCheck (wordOf 21 0b000000101110011111011) 14 D rounds fuel φ = true
  | 0, _ => ⟨0, 2, 300, w000000101110011111011_0⟩
  | 1, _ => ⟨0, 1, 300, w000000101110011111011_1⟩
  | 2, _ => ⟨0, 1, 300, w000000101110011111011_2⟩
  | 3, _ => ⟨0, 1, 300, w000000101110011111011_3⟩
  | 4, _ => ⟨0, 1, 300, w000000101110011111011_4⟩
  | 5, _ => ⟨0, 1, 300, w000000101110011111011_5⟩
  | 6, _ => ⟨0, 0, 300, w000000101110011111011_6⟩
  | 7, _ => ⟨0, 1, 300, w000000101110011111011_7⟩
  | 8, _ => ⟨0, 0, 300, w000000101110011111011_8⟩
  | 9, _ => ⟨0, 0, 300, w000000101110011111011_9⟩
  | 10, _ => ⟨0, 0, 300, w000000101110011111011_10⟩
  | 11, _ => ⟨0, 1, 300, w000000101110011111011_11⟩
  | 12, _ => ⟨0, 2, 300, w000000101110011111011_12⟩
  | 13, _ => ⟨0, 0, 300, w000000101110011111011_13⟩
  | 14, _ => ⟨0, 0, 300, w000000101110011111011_14⟩
  | 15, _ => ⟨0, 0, 300, w000000101110011111011_15⟩
  | 16, _ => ⟨0, 0, 300, w000000101110011111011_16⟩
  | 17, _ => ⟨0, 0, 300, w000000101110011111011_17⟩
  | 18, _ => ⟨0, 1, 300, w000000101110011111011_18⟩
  | 19, _ => ⟨0, 0, 300, w000000101110011111011_19⟩
  | 20, _ => ⟨0, 0, 300, w000000101110011111011_20⟩
  | _ + 21, h => absurd h (by omega)

set_option maxHeartbeats 0 in
theorem w000001101111111111001_0 : phaseCheck (wordOf 21 0b000001101111111111001) 14 0 1 300 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000001101111111111001_1 : phaseCheck (wordOf 21 0b000001101111111111001) 14 0 3 300 1 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000001101111111111001_2 : phaseCheck (wordOf 21 0b000001101111111111001) 14 0 1 300 2 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000001101111111111001_3 : phaseCheck (wordOf 21 0b000001101111111111001) 14 0 1 300 3 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000001101111111111001_4 : phaseCheck (wordOf 21 0b000001101111111111001) 14 0 1 300 4 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000001101111111111001_5 : phaseCheck (wordOf 21 0b000001101111111111001) 14 0 0 300 5 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000001101111111111001_6 : phaseCheck (wordOf 21 0b000001101111111111001) 14 0 0 300 6 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000001101111111111001_7 : phaseCheck (wordOf 21 0b000001101111111111001) 14 0 3 300 7 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000001101111111111001_8 : phaseCheck (wordOf 21 0b000001101111111111001) 14 0 0 300 8 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000001101111111111001_9 : phaseCheck (wordOf 21 0b000001101111111111001) 14 0 0 300 9 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000001101111111111001_10 : phaseCheck (wordOf 21 0b000001101111111111001) 14 0 0 300 10 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000001101111111111001_11 : phaseCheck (wordOf 21 0b000001101111111111001) 14 0 0 300 11 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000001101111111111001_12 : phaseCheck (wordOf 21 0b000001101111111111001) 14 0 0 300 12 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000001101111111111001_13 : phaseCheck (wordOf 21 0b000001101111111111001) 14 0 0 300 13 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000001101111111111001_14 : phaseCheck (wordOf 21 0b000001101111111111001) 14 0 0 300 14 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000001101111111111001_15 : phaseCheck (wordOf 21 0b000001101111111111001) 14 0 0 300 15 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000001101111111111001_16 : phaseCheck (wordOf 21 0b000001101111111111001) 14 0 0 300 16 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000001101111111111001_17 : phaseCheck (wordOf 21 0b000001101111111111001) 14 0 0 300 17 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000001101111111111001_18 : phaseCheck (wordOf 21 0b000001101111111111001) 14 0 1 300 18 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000001101111111111001_19 : phaseCheck (wordOf 21 0b000001101111111111001) 14 0 1 300 19 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000001101111111111001_20 : phaseCheck (wordOf 21 0b000001101111111111001) 14 0 0 300 20 = true := by
  decide +kernel

/-- Every phase of `000001101111111111001` at width 14. -/
theorem w000001101111111111001 : ∀ φ, φ < 21 → ∃ D rounds fuel,
    phaseCheck (wordOf 21 0b000001101111111111001) 14 D rounds fuel φ = true
  | 0, _ => ⟨0, 1, 300, w000001101111111111001_0⟩
  | 1, _ => ⟨0, 3, 300, w000001101111111111001_1⟩
  | 2, _ => ⟨0, 1, 300, w000001101111111111001_2⟩
  | 3, _ => ⟨0, 1, 300, w000001101111111111001_3⟩
  | 4, _ => ⟨0, 1, 300, w000001101111111111001_4⟩
  | 5, _ => ⟨0, 0, 300, w000001101111111111001_5⟩
  | 6, _ => ⟨0, 0, 300, w000001101111111111001_6⟩
  | 7, _ => ⟨0, 3, 300, w000001101111111111001_7⟩
  | 8, _ => ⟨0, 0, 300, w000001101111111111001_8⟩
  | 9, _ => ⟨0, 0, 300, w000001101111111111001_9⟩
  | 10, _ => ⟨0, 0, 300, w000001101111111111001_10⟩
  | 11, _ => ⟨0, 0, 300, w000001101111111111001_11⟩
  | 12, _ => ⟨0, 0, 300, w000001101111111111001_12⟩
  | 13, _ => ⟨0, 0, 300, w000001101111111111001_13⟩
  | 14, _ => ⟨0, 0, 300, w000001101111111111001_14⟩
  | 15, _ => ⟨0, 0, 300, w000001101111111111001_15⟩
  | 16, _ => ⟨0, 0, 300, w000001101111111111001_16⟩
  | 17, _ => ⟨0, 0, 300, w000001101111111111001_17⟩
  | 18, _ => ⟨0, 1, 300, w000001101111111111001_18⟩
  | 19, _ => ⟨0, 1, 300, w000001101111111111001_19⟩
  | 20, _ => ⟨0, 0, 300, w000001101111111111001_20⟩
  | _ + 21, h => absurd h (by omega)

set_option maxHeartbeats 0 in
theorem w000011111100111111111_0 : phaseCheck (wordOf 21 0b000011111100111111111) 14 0 1 300 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000011111100111111111_1 : phaseCheck (wordOf 21 0b000011111100111111111) 14 0 1 300 1 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000011111100111111111_2 : phaseCheck (wordOf 21 0b000011111100111111111) 14 0 1 300 2 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000011111100111111111_3 : phaseCheck (wordOf 21 0b000011111100111111111) 14 0 1 300 3 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000011111100111111111_4 : phaseCheck (wordOf 21 0b000011111100111111111) 14 0 0 300 4 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000011111100111111111_5 : phaseCheck (wordOf 21 0b000011111100111111111) 14 0 0 300 5 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000011111100111111111_6 : phaseCheck (wordOf 21 0b000011111100111111111) 14 0 0 300 6 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000011111100111111111_7 : phaseCheck (wordOf 21 0b000011111100111111111) 14 0 0 300 7 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000011111100111111111_8 : phaseCheck (wordOf 21 0b000011111100111111111) 14 0 0 300 8 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000011111100111111111_9 : phaseCheck (wordOf 21 0b000011111100111111111) 14 0 0 300 9 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000011111100111111111_10 : phaseCheck (wordOf 21 0b000011111100111111111) 14 0 1 300 10 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000011111100111111111_11 : phaseCheck (wordOf 21 0b000011111100111111111) 14 0 1 300 11 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000011111100111111111_12 : phaseCheck (wordOf 21 0b000011111100111111111) 14 0 0 300 12 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000011111100111111111_13 : phaseCheck (wordOf 21 0b000011111100111111111) 14 0 0 300 13 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000011111100111111111_14 : phaseCheck (wordOf 21 0b000011111100111111111) 14 0 0 300 14 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000011111100111111111_15 : phaseCheck (wordOf 21 0b000011111100111111111) 14 0 0 300 15 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000011111100111111111_16 : phaseCheck (wordOf 21 0b000011111100111111111) 14 0 0 300 16 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000011111100111111111_17 : phaseCheck (wordOf 21 0b000011111100111111111) 14 0 0 300 17 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000011111100111111111_18 : phaseCheck (wordOf 21 0b000011111100111111111) 14 0 0 300 18 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000011111100111111111_19 : phaseCheck (wordOf 21 0b000011111100111111111) 14 0 0 300 19 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000011111100111111111_20 : phaseCheck (wordOf 21 0b000011111100111111111) 14 0 0 300 20 = true := by
  decide +kernel

/-- Every phase of `000011111100111111111` at width 14. -/
theorem w000011111100111111111 : ∀ φ, φ < 21 → ∃ D rounds fuel,
    phaseCheck (wordOf 21 0b000011111100111111111) 14 D rounds fuel φ = true
  | 0, _ => ⟨0, 1, 300, w000011111100111111111_0⟩
  | 1, _ => ⟨0, 1, 300, w000011111100111111111_1⟩
  | 2, _ => ⟨0, 1, 300, w000011111100111111111_2⟩
  | 3, _ => ⟨0, 1, 300, w000011111100111111111_3⟩
  | 4, _ => ⟨0, 0, 300, w000011111100111111111_4⟩
  | 5, _ => ⟨0, 0, 300, w000011111100111111111_5⟩
  | 6, _ => ⟨0, 0, 300, w000011111100111111111_6⟩
  | 7, _ => ⟨0, 0, 300, w000011111100111111111_7⟩
  | 8, _ => ⟨0, 0, 300, w000011111100111111111_8⟩
  | 9, _ => ⟨0, 0, 300, w000011111100111111111_9⟩
  | 10, _ => ⟨0, 1, 300, w000011111100111111111_10⟩
  | 11, _ => ⟨0, 1, 300, w000011111100111111111_11⟩
  | 12, _ => ⟨0, 0, 300, w000011111100111111111_12⟩
  | 13, _ => ⟨0, 0, 300, w000011111100111111111_13⟩
  | 14, _ => ⟨0, 0, 300, w000011111100111111111_14⟩
  | 15, _ => ⟨0, 0, 300, w000011111100111111111_15⟩
  | 16, _ => ⟨0, 0, 300, w000011111100111111111_16⟩
  | 17, _ => ⟨0, 0, 300, w000011111100111111111_17⟩
  | 18, _ => ⟨0, 0, 300, w000011111100111111111_18⟩
  | 19, _ => ⟨0, 0, 300, w000011111100111111111_19⟩
  | 20, _ => ⟨0, 0, 300, w000011111100111111111_20⟩
  | _ + 21, h => absurd h (by omega)

set_option maxHeartbeats 0 in
theorem w000011111110011111111_0 : phaseCheck (wordOf 21 0b000011111110011111111) 14 0 2 300 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000011111110011111111_1 : phaseCheck (wordOf 21 0b000011111110011111111) 14 0 1 300 1 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000011111110011111111_2 : phaseCheck (wordOf 21 0b000011111110011111111) 14 0 1 300 2 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000011111110011111111_3 : phaseCheck (wordOf 21 0b000011111110011111111) 14 0 1 300 3 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000011111110011111111_4 : phaseCheck (wordOf 21 0b000011111110011111111) 14 0 0 300 4 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000011111110011111111_5 : phaseCheck (wordOf 21 0b000011111110011111111) 14 0 0 300 5 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000011111110011111111_6 : phaseCheck (wordOf 21 0b000011111110011111111) 14 0 0 300 6 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000011111110011111111_7 : phaseCheck (wordOf 21 0b000011111110011111111) 14 0 0 300 7 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000011111110011111111_8 : phaseCheck (wordOf 21 0b000011111110011111111) 14 0 0 300 8 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000011111110011111111_9 : phaseCheck (wordOf 21 0b000011111110011111111) 14 0 0 300 9 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000011111110011111111_10 : phaseCheck (wordOf 21 0b000011111110011111111) 14 0 0 300 10 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000011111110011111111_11 : phaseCheck (wordOf 21 0b000011111110011111111) 14 0 1 300 11 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000011111110011111111_12 : phaseCheck (wordOf 21 0b000011111110011111111) 14 0 2 300 12 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000011111110011111111_13 : phaseCheck (wordOf 21 0b000011111110011111111) 14 0 0 300 13 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000011111110011111111_14 : phaseCheck (wordOf 21 0b000011111110011111111) 14 0 0 300 14 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000011111110011111111_15 : phaseCheck (wordOf 21 0b000011111110011111111) 14 0 0 300 15 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000011111110011111111_16 : phaseCheck (wordOf 21 0b000011111110011111111) 14 0 0 300 16 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000011111110011111111_17 : phaseCheck (wordOf 21 0b000011111110011111111) 14 0 0 300 17 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000011111110011111111_18 : phaseCheck (wordOf 21 0b000011111110011111111) 14 0 0 300 18 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000011111110011111111_19 : phaseCheck (wordOf 21 0b000011111110011111111) 14 0 0 300 19 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000011111110011111111_20 : phaseCheck (wordOf 21 0b000011111110011111111) 14 0 0 300 20 = true := by
  decide +kernel

/-- Every phase of `000011111110011111111` at width 14. -/
theorem w000011111110011111111 : ∀ φ, φ < 21 → ∃ D rounds fuel,
    phaseCheck (wordOf 21 0b000011111110011111111) 14 D rounds fuel φ = true
  | 0, _ => ⟨0, 2, 300, w000011111110011111111_0⟩
  | 1, _ => ⟨0, 1, 300, w000011111110011111111_1⟩
  | 2, _ => ⟨0, 1, 300, w000011111110011111111_2⟩
  | 3, _ => ⟨0, 1, 300, w000011111110011111111_3⟩
  | 4, _ => ⟨0, 0, 300, w000011111110011111111_4⟩
  | 5, _ => ⟨0, 0, 300, w000011111110011111111_5⟩
  | 6, _ => ⟨0, 0, 300, w000011111110011111111_6⟩
  | 7, _ => ⟨0, 0, 300, w000011111110011111111_7⟩
  | 8, _ => ⟨0, 0, 300, w000011111110011111111_8⟩
  | 9, _ => ⟨0, 0, 300, w000011111110011111111_9⟩
  | 10, _ => ⟨0, 0, 300, w000011111110011111111_10⟩
  | 11, _ => ⟨0, 1, 300, w000011111110011111111_11⟩
  | 12, _ => ⟨0, 2, 300, w000011111110011111111_12⟩
  | 13, _ => ⟨0, 0, 300, w000011111110011111111_13⟩
  | 14, _ => ⟨0, 0, 300, w000011111110011111111_14⟩
  | 15, _ => ⟨0, 0, 300, w000011111110011111111_15⟩
  | 16, _ => ⟨0, 0, 300, w000011111110011111111_16⟩
  | 17, _ => ⟨0, 0, 300, w000011111110011111111_17⟩
  | 18, _ => ⟨0, 0, 300, w000011111110011111111_18⟩
  | 19, _ => ⟨0, 0, 300, w000011111110011111111_19⟩
  | 20, _ => ⟨0, 0, 300, w000011111110011111111_20⟩
  | _ + 21, h => absurd h (by omega)

set_option maxHeartbeats 0 in
theorem w000101111111110110011_0 : phaseCheck (wordOf 21 0b000101111111110110011) 13 0 2 300 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000101111111110110011_1 : phaseCheck (wordOf 21 0b000101111111110110011) 13 0 1 300 1 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000101111111110110011_2 : phaseCheck (wordOf 21 0b000101111111110110011) 13 0 1 300 2 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000101111111110110011_3 : phaseCheck (wordOf 21 0b000101111111110110011) 13 0 0 300 3 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000101111111110110011_4 : phaseCheck (wordOf 21 0b000101111111110110011) 13 0 1 300 4 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000101111111110110011_5 : phaseCheck (wordOf 21 0b000101111111110110011) 13 0 0 300 5 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000101111111110110011_6 : phaseCheck (wordOf 21 0b000101111111110110011) 13 0 0 300 6 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000101111111110110011_7 : phaseCheck (wordOf 21 0b000101111111110110011) 13 0 0 300 7 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000101111111110110011_8 : phaseCheck (wordOf 21 0b000101111111110110011) 13 0 0 300 8 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000101111111110110011_9 : phaseCheck (wordOf 21 0b000101111111110110011) 13 0 0 300 9 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000101111111110110011_10 : phaseCheck (wordOf 21 0b000101111111110110011) 13 0 0 300 10 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000101111111110110011_11 : phaseCheck (wordOf 21 0b000101111111110110011) 13 0 0 300 11 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000101111111110110011_12 : phaseCheck (wordOf 21 0b000101111111110110011) 13 0 0 300 12 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000101111111110110011_13 : phaseCheck (wordOf 21 0b000101111111110110011) 13 0 0 300 13 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000101111111110110011_14 : phaseCheck (wordOf 21 0b000101111111110110011) 13 0 1 300 14 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000101111111110110011_15 : phaseCheck (wordOf 21 0b000101111111110110011) 13 0 0 300 15 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000101111111110110011_16 : phaseCheck (wordOf 21 0b000101111111110110011) 13 0 0 300 16 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000101111111110110011_17 : phaseCheck (wordOf 21 0b000101111111110110011) 13 0 1 300 17 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000101111111110110011_18 : phaseCheck (wordOf 21 0b000101111111110110011) 13 0 1 300 18 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000101111111110110011_19 : phaseCheck (wordOf 21 0b000101111111110110011) 13 0 0 300 19 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000101111111110110011_20 : phaseCheck (wordOf 21 0b000101111111110110011) 13 0 0 300 20 = true := by
  decide +kernel

/-- Every phase of `000101111111110110011` at width 13. -/
theorem w000101111111110110011 : ∀ φ, φ < 21 → ∃ D rounds fuel,
    phaseCheck (wordOf 21 0b000101111111110110011) 13 D rounds fuel φ = true
  | 0, _ => ⟨0, 2, 300, w000101111111110110011_0⟩
  | 1, _ => ⟨0, 1, 300, w000101111111110110011_1⟩
  | 2, _ => ⟨0, 1, 300, w000101111111110110011_2⟩
  | 3, _ => ⟨0, 0, 300, w000101111111110110011_3⟩
  | 4, _ => ⟨0, 1, 300, w000101111111110110011_4⟩
  | 5, _ => ⟨0, 0, 300, w000101111111110110011_5⟩
  | 6, _ => ⟨0, 0, 300, w000101111111110110011_6⟩
  | 7, _ => ⟨0, 0, 300, w000101111111110110011_7⟩
  | 8, _ => ⟨0, 0, 300, w000101111111110110011_8⟩
  | 9, _ => ⟨0, 0, 300, w000101111111110110011_9⟩
  | 10, _ => ⟨0, 0, 300, w000101111111110110011_10⟩
  | 11, _ => ⟨0, 0, 300, w000101111111110110011_11⟩
  | 12, _ => ⟨0, 0, 300, w000101111111110110011_12⟩
  | 13, _ => ⟨0, 0, 300, w000101111111110110011_13⟩
  | 14, _ => ⟨0, 1, 300, w000101111111110110011_14⟩
  | 15, _ => ⟨0, 0, 300, w000101111111110110011_15⟩
  | 16, _ => ⟨0, 0, 300, w000101111111110110011_16⟩
  | 17, _ => ⟨0, 1, 300, w000101111111110110011_17⟩
  | 18, _ => ⟨0, 1, 300, w000101111111110110011_18⟩
  | 19, _ => ⟨0, 0, 300, w000101111111110110011_19⟩
  | 20, _ => ⟨0, 0, 300, w000101111111110110011_20⟩
  | _ + 21, h => absurd h (by omega)

set_option maxHeartbeats 0 in
theorem w000101111111111011001_0 : phaseCheck (wordOf 21 0b000101111111111011001) 13 0 1 300 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000101111111111011001_1 : phaseCheck (wordOf 21 0b000101111111111011001) 13 0 1 300 1 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000101111111111011001_2 : phaseCheck (wordOf 21 0b000101111111111011001) 13 0 4 300 2 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000101111111111011001_3 : phaseCheck (wordOf 21 0b000101111111111011001) 13 0 0 300 3 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000101111111111011001_4 : phaseCheck (wordOf 21 0b000101111111111011001) 13 0 4 300 4 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000101111111111011001_5 : phaseCheck (wordOf 21 0b000101111111111011001) 13 0 0 300 5 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000101111111111011001_6 : phaseCheck (wordOf 21 0b000101111111111011001) 13 0 0 300 6 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000101111111111011001_7 : phaseCheck (wordOf 21 0b000101111111111011001) 13 0 0 300 7 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000101111111111011001_8 : phaseCheck (wordOf 21 0b000101111111111011001) 13 0 0 300 8 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000101111111111011001_9 : phaseCheck (wordOf 21 0b000101111111111011001) 13 0 0 300 9 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000101111111111011001_10 : phaseCheck (wordOf 21 0b000101111111111011001) 13 0 0 300 10 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000101111111111011001_11 : phaseCheck (wordOf 21 0b000101111111111011001) 13 0 0 300 11 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000101111111111011001_12 : phaseCheck (wordOf 21 0b000101111111111011001) 13 0 0 300 12 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000101111111111011001_13 : phaseCheck (wordOf 21 0b000101111111111011001) 13 0 0 300 13 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000101111111111011001_14 : phaseCheck (wordOf 21 0b000101111111111011001) 13 0 0 300 14 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000101111111111011001_15 : phaseCheck (wordOf 21 0b000101111111111011001) 13 0 1 300 15 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000101111111111011001_16 : phaseCheck (wordOf 21 0b000101111111111011001) 13 0 0 300 16 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000101111111111011001_17 : phaseCheck (wordOf 21 0b000101111111111011001) 13 0 0 300 17 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000101111111111011001_18 : phaseCheck (wordOf 21 0b000101111111111011001) 13 0 1 300 18 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000101111111111011001_19 : phaseCheck (wordOf 21 0b000101111111111011001) 13 0 1 300 19 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000101111111111011001_20 : phaseCheck (wordOf 21 0b000101111111111011001) 13 0 0 300 20 = true := by
  decide +kernel

/-- Every phase of `000101111111111011001` at width 13. -/
theorem w000101111111111011001 : ∀ φ, φ < 21 → ∃ D rounds fuel,
    phaseCheck (wordOf 21 0b000101111111111011001) 13 D rounds fuel φ = true
  | 0, _ => ⟨0, 1, 300, w000101111111111011001_0⟩
  | 1, _ => ⟨0, 1, 300, w000101111111111011001_1⟩
  | 2, _ => ⟨0, 4, 300, w000101111111111011001_2⟩
  | 3, _ => ⟨0, 0, 300, w000101111111111011001_3⟩
  | 4, _ => ⟨0, 4, 300, w000101111111111011001_4⟩
  | 5, _ => ⟨0, 0, 300, w000101111111111011001_5⟩
  | 6, _ => ⟨0, 0, 300, w000101111111111011001_6⟩
  | 7, _ => ⟨0, 0, 300, w000101111111111011001_7⟩
  | 8, _ => ⟨0, 0, 300, w000101111111111011001_8⟩
  | 9, _ => ⟨0, 0, 300, w000101111111111011001_9⟩
  | 10, _ => ⟨0, 0, 300, w000101111111111011001_10⟩
  | 11, _ => ⟨0, 0, 300, w000101111111111011001_11⟩
  | 12, _ => ⟨0, 0, 300, w000101111111111011001_12⟩
  | 13, _ => ⟨0, 0, 300, w000101111111111011001_13⟩
  | 14, _ => ⟨0, 0, 300, w000101111111111011001_14⟩
  | 15, _ => ⟨0, 1, 300, w000101111111111011001_15⟩
  | 16, _ => ⟨0, 0, 300, w000101111111111011001_16⟩
  | 17, _ => ⟨0, 0, 300, w000101111111111011001_17⟩
  | 18, _ => ⟨0, 1, 300, w000101111111111011001_18⟩
  | 19, _ => ⟨0, 1, 300, w000101111111111011001_19⟩
  | 20, _ => ⟨0, 0, 300, w000101111111111011001_20⟩
  | _ + 21, h => absurd h (by omega)

set_option maxHeartbeats 0 in
theorem w000111110101111111111_0 : phaseCheck (wordOf 21 0b000111110101111111111) 13 0 1 300 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000111110101111111111_1 : phaseCheck (wordOf 21 0b000111110101111111111) 13 0 1 300 1 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000111110101111111111_2 : phaseCheck (wordOf 21 0b000111110101111111111) 13 0 1 300 2 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000111110101111111111_3 : phaseCheck (wordOf 21 0b000111110101111111111) 13 0 0 300 3 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000111110101111111111_4 : phaseCheck (wordOf 21 0b000111110101111111111) 13 0 0 300 4 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000111110101111111111_5 : phaseCheck (wordOf 21 0b000111110101111111111) 13 0 0 300 5 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000111110101111111111_6 : phaseCheck (wordOf 21 0b000111110101111111111) 13 0 0 300 6 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000111110101111111111_7 : phaseCheck (wordOf 21 0b000111110101111111111) 13 0 0 300 7 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000111110101111111111_8 : phaseCheck (wordOf 21 0b000111110101111111111) 13 0 1 300 8 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000111110101111111111_9 : phaseCheck (wordOf 21 0b000111110101111111111) 13 0 0 300 9 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000111110101111111111_10 : phaseCheck (wordOf 21 0b000111110101111111111) 13 0 2 300 10 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000111110101111111111_11 : phaseCheck (wordOf 21 0b000111110101111111111) 13 0 0 300 11 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000111110101111111111_12 : phaseCheck (wordOf 21 0b000111110101111111111) 13 0 0 300 12 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000111110101111111111_13 : phaseCheck (wordOf 21 0b000111110101111111111) 13 0 0 300 13 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000111110101111111111_14 : phaseCheck (wordOf 21 0b000111110101111111111) 13 0 0 300 14 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000111110101111111111_15 : phaseCheck (wordOf 21 0b000111110101111111111) 13 0 0 300 15 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000111110101111111111_16 : phaseCheck (wordOf 21 0b000111110101111111111) 13 0 0 300 16 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000111110101111111111_17 : phaseCheck (wordOf 21 0b000111110101111111111) 13 0 0 300 17 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000111110101111111111_18 : phaseCheck (wordOf 21 0b000111110101111111111) 13 0 0 300 18 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000111110101111111111_19 : phaseCheck (wordOf 21 0b000111110101111111111) 13 0 0 300 19 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000111110101111111111_20 : phaseCheck (wordOf 21 0b000111110101111111111) 13 0 0 300 20 = true := by
  decide +kernel

/-- Every phase of `000111110101111111111` at width 13. -/
theorem w000111110101111111111 : ∀ φ, φ < 21 → ∃ D rounds fuel,
    phaseCheck (wordOf 21 0b000111110101111111111) 13 D rounds fuel φ = true
  | 0, _ => ⟨0, 1, 300, w000111110101111111111_0⟩
  | 1, _ => ⟨0, 1, 300, w000111110101111111111_1⟩
  | 2, _ => ⟨0, 1, 300, w000111110101111111111_2⟩
  | 3, _ => ⟨0, 0, 300, w000111110101111111111_3⟩
  | 4, _ => ⟨0, 0, 300, w000111110101111111111_4⟩
  | 5, _ => ⟨0, 0, 300, w000111110101111111111_5⟩
  | 6, _ => ⟨0, 0, 300, w000111110101111111111_6⟩
  | 7, _ => ⟨0, 0, 300, w000111110101111111111_7⟩
  | 8, _ => ⟨0, 1, 300, w000111110101111111111_8⟩
  | 9, _ => ⟨0, 0, 300, w000111110101111111111_9⟩
  | 10, _ => ⟨0, 2, 300, w000111110101111111111_10⟩
  | 11, _ => ⟨0, 0, 300, w000111110101111111111_11⟩
  | 12, _ => ⟨0, 0, 300, w000111110101111111111_12⟩
  | 13, _ => ⟨0, 0, 300, w000111110101111111111_13⟩
  | 14, _ => ⟨0, 0, 300, w000111110101111111111_14⟩
  | 15, _ => ⟨0, 0, 300, w000111110101111111111_15⟩
  | 16, _ => ⟨0, 0, 300, w000111110101111111111_16⟩
  | 17, _ => ⟨0, 0, 300, w000111110101111111111_17⟩
  | 18, _ => ⟨0, 0, 300, w000111110101111111111_18⟩
  | 19, _ => ⟨0, 0, 300, w000111110101111111111_19⟩
  | 20, _ => ⟨0, 0, 300, w000111110101111111111_20⟩
  | _ + 21, h => absurd h (by omega)

set_option maxHeartbeats 0 in
theorem w000111111001111111111_0 : phaseCheck (wordOf 21 0b000111111001111111111) 13 0 1 300 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000111111001111111111_1 : phaseCheck (wordOf 21 0b000111111001111111111) 13 0 1 300 1 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000111111001111111111_2 : phaseCheck (wordOf 21 0b000111111001111111111) 13 0 1 300 2 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000111111001111111111_3 : phaseCheck (wordOf 21 0b000111111001111111111) 13 0 0 300 3 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000111111001111111111_4 : phaseCheck (wordOf 21 0b000111111001111111111) 13 0 0 300 4 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000111111001111111111_5 : phaseCheck (wordOf 21 0b000111111001111111111) 13 0 0 300 5 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000111111001111111111_6 : phaseCheck (wordOf 21 0b000111111001111111111) 13 0 0 300 6 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000111111001111111111_7 : phaseCheck (wordOf 21 0b000111111001111111111) 13 0 0 300 7 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000111111001111111111_8 : phaseCheck (wordOf 21 0b000111111001111111111) 13 0 0 300 8 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000111111001111111111_9 : phaseCheck (wordOf 21 0b000111111001111111111) 13 0 2 300 9 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000111111001111111111_10 : phaseCheck (wordOf 21 0b000111111001111111111) 13 0 1 300 10 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000111111001111111111_11 : phaseCheck (wordOf 21 0b000111111001111111111) 13 0 0 300 11 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000111111001111111111_12 : phaseCheck (wordOf 21 0b000111111001111111111) 13 0 0 300 12 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000111111001111111111_13 : phaseCheck (wordOf 21 0b000111111001111111111) 13 0 0 300 13 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000111111001111111111_14 : phaseCheck (wordOf 21 0b000111111001111111111) 13 0 0 300 14 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000111111001111111111_15 : phaseCheck (wordOf 21 0b000111111001111111111) 13 0 0 300 15 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000111111001111111111_16 : phaseCheck (wordOf 21 0b000111111001111111111) 13 0 0 300 16 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000111111001111111111_17 : phaseCheck (wordOf 21 0b000111111001111111111) 13 0 0 300 17 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000111111001111111111_18 : phaseCheck (wordOf 21 0b000111111001111111111) 13 0 0 300 18 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000111111001111111111_19 : phaseCheck (wordOf 21 0b000111111001111111111) 13 0 0 300 19 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000111111001111111111_20 : phaseCheck (wordOf 21 0b000111111001111111111) 13 0 0 300 20 = true := by
  decide +kernel

/-- Every phase of `000111111001111111111` at width 13. -/
theorem w000111111001111111111 : ∀ φ, φ < 21 → ∃ D rounds fuel,
    phaseCheck (wordOf 21 0b000111111001111111111) 13 D rounds fuel φ = true
  | 0, _ => ⟨0, 1, 300, w000111111001111111111_0⟩
  | 1, _ => ⟨0, 1, 300, w000111111001111111111_1⟩
  | 2, _ => ⟨0, 1, 300, w000111111001111111111_2⟩
  | 3, _ => ⟨0, 0, 300, w000111111001111111111_3⟩
  | 4, _ => ⟨0, 0, 300, w000111111001111111111_4⟩
  | 5, _ => ⟨0, 0, 300, w000111111001111111111_5⟩
  | 6, _ => ⟨0, 0, 300, w000111111001111111111_6⟩
  | 7, _ => ⟨0, 0, 300, w000111111001111111111_7⟩
  | 8, _ => ⟨0, 0, 300, w000111111001111111111_8⟩
  | 9, _ => ⟨0, 2, 300, w000111111001111111111_9⟩
  | 10, _ => ⟨0, 1, 300, w000111111001111111111_10⟩
  | 11, _ => ⟨0, 0, 300, w000111111001111111111_11⟩
  | 12, _ => ⟨0, 0, 300, w000111111001111111111_12⟩
  | 13, _ => ⟨0, 0, 300, w000111111001111111111_13⟩
  | 14, _ => ⟨0, 0, 300, w000111111001111111111_14⟩
  | 15, _ => ⟨0, 0, 300, w000111111001111111111_15⟩
  | 16, _ => ⟨0, 0, 300, w000111111001111111111_16⟩
  | 17, _ => ⟨0, 0, 300, w000111111001111111111_17⟩
  | 18, _ => ⟨0, 0, 300, w000111111001111111111_18⟩
  | 19, _ => ⟨0, 0, 300, w000111111001111111111_19⟩
  | 20, _ => ⟨0, 0, 300, w000111111001111111111_20⟩
  | _ + 21, h => absurd h (by omega)

set_option maxHeartbeats 0 in
theorem w000111111111100111111_0 : phaseCheck (wordOf 21 0b000111111111100111111) 14 0 3 300 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000111111111100111111_1 : phaseCheck (wordOf 21 0b000111111111100111111) 14 0 1 300 1 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000111111111100111111_2 : phaseCheck (wordOf 21 0b000111111111100111111) 14 0 1 300 2 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000111111111100111111_3 : phaseCheck (wordOf 21 0b000111111111100111111) 14 0 0 300 3 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000111111111100111111_4 : phaseCheck (wordOf 21 0b000111111111100111111) 14 0 0 300 4 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000111111111100111111_5 : phaseCheck (wordOf 21 0b000111111111100111111) 14 0 0 300 5 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000111111111100111111_6 : phaseCheck (wordOf 21 0b000111111111100111111) 14 0 0 300 6 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000111111111100111111_7 : phaseCheck (wordOf 21 0b000111111111100111111) 14 0 0 300 7 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000111111111100111111_8 : phaseCheck (wordOf 21 0b000111111111100111111) 14 0 0 300 8 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000111111111100111111_9 : phaseCheck (wordOf 21 0b000111111111100111111) 14 0 0 300 9 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000111111111100111111_10 : phaseCheck (wordOf 21 0b000111111111100111111) 14 0 0 300 10 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000111111111100111111_11 : phaseCheck (wordOf 21 0b000111111111100111111) 14 0 0 300 11 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000111111111100111111_12 : phaseCheck (wordOf 21 0b000111111111100111111) 14 0 0 300 12 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000111111111100111111_13 : phaseCheck (wordOf 21 0b000111111111100111111) 14 0 1 300 13 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000111111111100111111_14 : phaseCheck (wordOf 21 0b000111111111100111111) 14 0 1 300 14 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000111111111100111111_15 : phaseCheck (wordOf 21 0b000111111111100111111) 14 0 0 300 15 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000111111111100111111_16 : phaseCheck (wordOf 21 0b000111111111100111111) 14 0 0 300 16 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000111111111100111111_17 : phaseCheck (wordOf 21 0b000111111111100111111) 14 0 0 300 17 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000111111111100111111_18 : phaseCheck (wordOf 21 0b000111111111100111111) 14 0 0 300 18 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000111111111100111111_19 : phaseCheck (wordOf 21 0b000111111111100111111) 14 0 0 300 19 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000111111111100111111_20 : phaseCheck (wordOf 21 0b000111111111100111111) 14 0 0 300 20 = true := by
  decide +kernel

/-- Every phase of `000111111111100111111` at width 14. -/
theorem w000111111111100111111 : ∀ φ, φ < 21 → ∃ D rounds fuel,
    phaseCheck (wordOf 21 0b000111111111100111111) 14 D rounds fuel φ = true
  | 0, _ => ⟨0, 3, 300, w000111111111100111111_0⟩
  | 1, _ => ⟨0, 1, 300, w000111111111100111111_1⟩
  | 2, _ => ⟨0, 1, 300, w000111111111100111111_2⟩
  | 3, _ => ⟨0, 0, 300, w000111111111100111111_3⟩
  | 4, _ => ⟨0, 0, 300, w000111111111100111111_4⟩
  | 5, _ => ⟨0, 0, 300, w000111111111100111111_5⟩
  | 6, _ => ⟨0, 0, 300, w000111111111100111111_6⟩
  | 7, _ => ⟨0, 0, 300, w000111111111100111111_7⟩
  | 8, _ => ⟨0, 0, 300, w000111111111100111111_8⟩
  | 9, _ => ⟨0, 0, 300, w000111111111100111111_9⟩
  | 10, _ => ⟨0, 0, 300, w000111111111100111111_10⟩
  | 11, _ => ⟨0, 0, 300, w000111111111100111111_11⟩
  | 12, _ => ⟨0, 0, 300, w000111111111100111111_12⟩
  | 13, _ => ⟨0, 1, 300, w000111111111100111111_13⟩
  | 14, _ => ⟨0, 1, 300, w000111111111100111111_14⟩
  | 15, _ => ⟨0, 0, 300, w000111111111100111111_15⟩
  | 16, _ => ⟨0, 0, 300, w000111111111100111111_16⟩
  | 17, _ => ⟨0, 0, 300, w000111111111100111111_17⟩
  | 18, _ => ⟨0, 0, 300, w000111111111100111111_18⟩
  | 19, _ => ⟨0, 0, 300, w000111111111100111111_19⟩
  | 20, _ => ⟨0, 0, 300, w000111111111100111111_20⟩
  | _ + 21, h => absurd h (by omega)

set_option maxHeartbeats 0 in
theorem w000111111111110110011_0 : phaseCheck (wordOf 21 0b000111111111110110011) 13 0 1 300 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000111111111110110011_1 : phaseCheck (wordOf 21 0b000111111111110110011) 13 0 1 300 1 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000111111111110110011_2 : phaseCheck (wordOf 21 0b000111111111110110011) 13 0 1 300 2 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000111111111110110011_3 : phaseCheck (wordOf 21 0b000111111111110110011) 13 0 0 300 3 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000111111111110110011_4 : phaseCheck (wordOf 21 0b000111111111110110011) 13 0 0 300 4 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000111111111110110011_5 : phaseCheck (wordOf 21 0b000111111111110110011) 13 0 0 300 5 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000111111111110110011_6 : phaseCheck (wordOf 21 0b000111111111110110011) 13 0 0 300 6 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000111111111110110011_7 : phaseCheck (wordOf 21 0b000111111111110110011) 13 0 0 300 7 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000111111111110110011_8 : phaseCheck (wordOf 21 0b000111111111110110011) 13 0 0 300 8 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000111111111110110011_9 : phaseCheck (wordOf 21 0b000111111111110110011) 13 0 0 300 9 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000111111111110110011_10 : phaseCheck (wordOf 21 0b000111111111110110011) 13 0 0 300 10 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000111111111110110011_11 : phaseCheck (wordOf 21 0b000111111111110110011) 13 0 0 300 11 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000111111111110110011_12 : phaseCheck (wordOf 21 0b000111111111110110011) 13 0 0 300 12 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000111111111110110011_13 : phaseCheck (wordOf 21 0b000111111111110110011) 13 0 0 300 13 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000111111111110110011_14 : phaseCheck (wordOf 21 0b000111111111110110011) 13 0 1 300 14 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000111111111110110011_15 : phaseCheck (wordOf 21 0b000111111111110110011) 13 0 0 300 15 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000111111111110110011_16 : phaseCheck (wordOf 21 0b000111111111110110011) 13 0 0 300 16 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000111111111110110011_17 : phaseCheck (wordOf 21 0b000111111111110110011) 13 0 1 300 17 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000111111111110110011_18 : phaseCheck (wordOf 21 0b000111111111110110011) 13 0 1 300 18 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000111111111110110011_19 : phaseCheck (wordOf 21 0b000111111111110110011) 13 0 0 300 19 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w000111111111110110011_20 : phaseCheck (wordOf 21 0b000111111111110110011) 13 0 0 300 20 = true := by
  decide +kernel

/-- Every phase of `000111111111110110011` at width 13. -/
theorem w000111111111110110011 : ∀ φ, φ < 21 → ∃ D rounds fuel,
    phaseCheck (wordOf 21 0b000111111111110110011) 13 D rounds fuel φ = true
  | 0, _ => ⟨0, 1, 300, w000111111111110110011_0⟩
  | 1, _ => ⟨0, 1, 300, w000111111111110110011_1⟩
  | 2, _ => ⟨0, 1, 300, w000111111111110110011_2⟩
  | 3, _ => ⟨0, 0, 300, w000111111111110110011_3⟩
  | 4, _ => ⟨0, 0, 300, w000111111111110110011_4⟩
  | 5, _ => ⟨0, 0, 300, w000111111111110110011_5⟩
  | 6, _ => ⟨0, 0, 300, w000111111111110110011_6⟩
  | 7, _ => ⟨0, 0, 300, w000111111111110110011_7⟩
  | 8, _ => ⟨0, 0, 300, w000111111111110110011_8⟩
  | 9, _ => ⟨0, 0, 300, w000111111111110110011_9⟩
  | 10, _ => ⟨0, 0, 300, w000111111111110110011_10⟩
  | 11, _ => ⟨0, 0, 300, w000111111111110110011_11⟩
  | 12, _ => ⟨0, 0, 300, w000111111111110110011_12⟩
  | 13, _ => ⟨0, 0, 300, w000111111111110110011_13⟩
  | 14, _ => ⟨0, 1, 300, w000111111111110110011_14⟩
  | 15, _ => ⟨0, 0, 300, w000111111111110110011_15⟩
  | 16, _ => ⟨0, 0, 300, w000111111111110110011_16⟩
  | 17, _ => ⟨0, 1, 300, w000111111111110110011_17⟩
  | 18, _ => ⟨0, 1, 300, w000111111111110110011_18⟩
  | 19, _ => ⟨0, 0, 300, w000111111111110110011_19⟩
  | 20, _ => ⟨0, 0, 300, w000111111111110110011_20⟩
  | _ + 21, h => absurd h (by omega)

set_option maxHeartbeats 0 in
theorem w001011111111111110111_0 : phaseCheck (wordOf 21 0b001011111111111110111) 13 0 1 300 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w001011111111111110111_1 : phaseCheck (wordOf 21 0b001011111111111110111) 13 0 1 300 1 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w001011111111111110111_2 : phaseCheck (wordOf 21 0b001011111111111110111) 13 0 0 300 2 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w001011111111111110111_3 : phaseCheck (wordOf 21 0b001011111111111110111) 13 0 2 300 3 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w001011111111111110111_4 : phaseCheck (wordOf 21 0b001011111111111110111) 13 0 0 300 4 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w001011111111111110111_5 : phaseCheck (wordOf 21 0b001011111111111110111) 13 0 0 300 5 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w001011111111111110111_6 : phaseCheck (wordOf 21 0b001011111111111110111) 13 0 0 300 6 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w001011111111111110111_7 : phaseCheck (wordOf 21 0b001011111111111110111) 13 0 0 300 7 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w001011111111111110111_8 : phaseCheck (wordOf 21 0b001011111111111110111) 13 0 0 300 8 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w001011111111111110111_9 : phaseCheck (wordOf 21 0b001011111111111110111) 13 0 0 300 9 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w001011111111111110111_10 : phaseCheck (wordOf 21 0b001011111111111110111) 13 0 0 300 10 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w001011111111111110111_11 : phaseCheck (wordOf 21 0b001011111111111110111) 13 0 0 300 11 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w001011111111111110111_12 : phaseCheck (wordOf 21 0b001011111111111110111) 13 0 0 300 12 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w001011111111111110111_13 : phaseCheck (wordOf 21 0b001011111111111110111) 13 0 0 300 13 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w001011111111111110111_14 : phaseCheck (wordOf 21 0b001011111111111110111) 13 0 0 300 14 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w001011111111111110111_15 : phaseCheck (wordOf 21 0b001011111111111110111) 13 0 0 300 15 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w001011111111111110111_16 : phaseCheck (wordOf 21 0b001011111111111110111) 13 0 0 300 16 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w001011111111111110111_17 : phaseCheck (wordOf 21 0b001011111111111110111) 13 0 1 300 17 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w001011111111111110111_18 : phaseCheck (wordOf 21 0b001011111111111110111) 13 0 0 300 18 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w001011111111111110111_19 : phaseCheck (wordOf 21 0b001011111111111110111) 13 0 0 300 19 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w001011111111111110111_20 : phaseCheck (wordOf 21 0b001011111111111110111) 13 0 0 300 20 = true := by
  decide +kernel

/-- Every phase of `001011111111111110111` at width 13. -/
theorem w001011111111111110111 : ∀ φ, φ < 21 → ∃ D rounds fuel,
    phaseCheck (wordOf 21 0b001011111111111110111) 13 D rounds fuel φ = true
  | 0, _ => ⟨0, 1, 300, w001011111111111110111_0⟩
  | 1, _ => ⟨0, 1, 300, w001011111111111110111_1⟩
  | 2, _ => ⟨0, 0, 300, w001011111111111110111_2⟩
  | 3, _ => ⟨0, 2, 300, w001011111111111110111_3⟩
  | 4, _ => ⟨0, 0, 300, w001011111111111110111_4⟩
  | 5, _ => ⟨0, 0, 300, w001011111111111110111_5⟩
  | 6, _ => ⟨0, 0, 300, w001011111111111110111_6⟩
  | 7, _ => ⟨0, 0, 300, w001011111111111110111_7⟩
  | 8, _ => ⟨0, 0, 300, w001011111111111110111_8⟩
  | 9, _ => ⟨0, 0, 300, w001011111111111110111_9⟩
  | 10, _ => ⟨0, 0, 300, w001011111111111110111_10⟩
  | 11, _ => ⟨0, 0, 300, w001011111111111110111_11⟩
  | 12, _ => ⟨0, 0, 300, w001011111111111110111_12⟩
  | 13, _ => ⟨0, 0, 300, w001011111111111110111_13⟩
  | 14, _ => ⟨0, 0, 300, w001011111111111110111_14⟩
  | 15, _ => ⟨0, 0, 300, w001011111111111110111_15⟩
  | 16, _ => ⟨0, 0, 300, w001011111111111110111_16⟩
  | 17, _ => ⟨0, 1, 300, w001011111111111110111_17⟩
  | 18, _ => ⟨0, 0, 300, w001011111111111110111_18⟩
  | 19, _ => ⟨0, 0, 300, w001011111111111110111_19⟩
  | 20, _ => ⟨0, 0, 300, w001011111111111110111_20⟩
  | _ + 21, h => absurd h (by omega)

set_option maxHeartbeats 0 in
theorem w001101001111111111011_0 : phaseCheck (wordOf 21 0b001101001111111111011) 13 0 1 300 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w001101001111111111011_1 : phaseCheck (wordOf 21 0b001101001111111111011) 13 0 1 300 1 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w001101001111111111011_2 : phaseCheck (wordOf 21 0b001101001111111111011) 13 0 0 300 2 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w001101001111111111011_3 : phaseCheck (wordOf 21 0b001101001111111111011) 13 0 0 300 3 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w001101001111111111011_4 : phaseCheck (wordOf 21 0b001101001111111111011) 13 0 3 300 4 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w001101001111111111011_5 : phaseCheck (wordOf 21 0b001101001111111111011) 13 0 0 300 5 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w001101001111111111011_6 : phaseCheck (wordOf 21 0b001101001111111111011) 13 0 1 300 6 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w001101001111111111011_7 : phaseCheck (wordOf 21 0b001101001111111111011) 13 0 2 300 7 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w001101001111111111011_8 : phaseCheck (wordOf 21 0b001101001111111111011) 13 0 0 300 8 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w001101001111111111011_9 : phaseCheck (wordOf 21 0b001101001111111111011) 13 0 0 300 9 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w001101001111111111011_10 : phaseCheck (wordOf 21 0b001101001111111111011) 13 0 0 300 10 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w001101001111111111011_11 : phaseCheck (wordOf 21 0b001101001111111111011) 13 0 0 300 11 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w001101001111111111011_12 : phaseCheck (wordOf 21 0b001101001111111111011) 13 0 0 300 12 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w001101001111111111011_13 : phaseCheck (wordOf 21 0b001101001111111111011) 13 0 0 300 13 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w001101001111111111011_14 : phaseCheck (wordOf 21 0b001101001111111111011) 13 0 0 300 14 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w001101001111111111011_15 : phaseCheck (wordOf 21 0b001101001111111111011) 13 0 0 300 15 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w001101001111111111011_16 : phaseCheck (wordOf 21 0b001101001111111111011) 13 0 0 300 16 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w001101001111111111011_17 : phaseCheck (wordOf 21 0b001101001111111111011) 13 0 0 300 17 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w001101001111111111011_18 : phaseCheck (wordOf 21 0b001101001111111111011) 13 0 1 300 18 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w001101001111111111011_19 : phaseCheck (wordOf 21 0b001101001111111111011) 13 0 0 300 19 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w001101001111111111011_20 : phaseCheck (wordOf 21 0b001101001111111111011) 13 0 0 300 20 = true := by
  decide +kernel

/-- Every phase of `001101001111111111011` at width 13. -/
theorem w001101001111111111011 : ∀ φ, φ < 21 → ∃ D rounds fuel,
    phaseCheck (wordOf 21 0b001101001111111111011) 13 D rounds fuel φ = true
  | 0, _ => ⟨0, 1, 300, w001101001111111111011_0⟩
  | 1, _ => ⟨0, 1, 300, w001101001111111111011_1⟩
  | 2, _ => ⟨0, 0, 300, w001101001111111111011_2⟩
  | 3, _ => ⟨0, 0, 300, w001101001111111111011_3⟩
  | 4, _ => ⟨0, 3, 300, w001101001111111111011_4⟩
  | 5, _ => ⟨0, 0, 300, w001101001111111111011_5⟩
  | 6, _ => ⟨0, 1, 300, w001101001111111111011_6⟩
  | 7, _ => ⟨0, 2, 300, w001101001111111111011_7⟩
  | 8, _ => ⟨0, 0, 300, w001101001111111111011_8⟩
  | 9, _ => ⟨0, 0, 300, w001101001111111111011_9⟩
  | 10, _ => ⟨0, 0, 300, w001101001111111111011_10⟩
  | 11, _ => ⟨0, 0, 300, w001101001111111111011_11⟩
  | 12, _ => ⟨0, 0, 300, w001101001111111111011_12⟩
  | 13, _ => ⟨0, 0, 300, w001101001111111111011_13⟩
  | 14, _ => ⟨0, 0, 300, w001101001111111111011_14⟩
  | 15, _ => ⟨0, 0, 300, w001101001111111111011_15⟩
  | 16, _ => ⟨0, 0, 300, w001101001111111111011_16⟩
  | 17, _ => ⟨0, 0, 300, w001101001111111111011_17⟩
  | 18, _ => ⟨0, 1, 300, w001101001111111111011_18⟩
  | 19, _ => ⟨0, 0, 300, w001101001111111111011_19⟩
  | 20, _ => ⟨0, 0, 300, w001101001111111111011_20⟩
  | _ + 21, h => absurd h (by omega)

set_option maxHeartbeats 0 in
theorem w001111010011111111111_0 : phaseCheck (wordOf 21 0b001111010011111111111) 14 0 1 300 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w001111010011111111111_1 : phaseCheck (wordOf 21 0b001111010011111111111) 14 0 1 300 1 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w001111010011111111111_2 : phaseCheck (wordOf 21 0b001111010011111111111) 14 0 0 300 2 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w001111010011111111111_3 : phaseCheck (wordOf 21 0b001111010011111111111) 14 0 0 300 3 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w001111010011111111111_4 : phaseCheck (wordOf 21 0b001111010011111111111) 14 0 0 300 4 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w001111010011111111111_5 : phaseCheck (wordOf 21 0b001111010011111111111) 14 0 0 300 5 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w001111010011111111111_6 : phaseCheck (wordOf 21 0b001111010011111111111) 14 0 2 300 6 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w001111010011111111111_7 : phaseCheck (wordOf 21 0b001111010011111111111) 14 0 0 300 7 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w001111010011111111111_8 : phaseCheck (wordOf 21 0b001111010011111111111) 14 0 1 300 8 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w001111010011111111111_9 : phaseCheck (wordOf 21 0b001111010011111111111) 14 0 1 300 9 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w001111010011111111111_10 : phaseCheck (wordOf 21 0b001111010011111111111) 14 0 0 300 10 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w001111010011111111111_11 : phaseCheck (wordOf 21 0b001111010011111111111) 14 0 0 300 11 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w001111010011111111111_12 : phaseCheck (wordOf 21 0b001111010011111111111) 14 0 0 300 12 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w001111010011111111111_13 : phaseCheck (wordOf 21 0b001111010011111111111) 14 0 0 300 13 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w001111010011111111111_14 : phaseCheck (wordOf 21 0b001111010011111111111) 14 0 0 300 14 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w001111010011111111111_15 : phaseCheck (wordOf 21 0b001111010011111111111) 14 0 0 300 15 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w001111010011111111111_16 : phaseCheck (wordOf 21 0b001111010011111111111) 14 0 0 300 16 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w001111010011111111111_17 : phaseCheck (wordOf 21 0b001111010011111111111) 14 0 0 300 17 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w001111010011111111111_18 : phaseCheck (wordOf 21 0b001111010011111111111) 14 0 0 300 18 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w001111010011111111111_19 : phaseCheck (wordOf 21 0b001111010011111111111) 14 0 0 300 19 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w001111010011111111111_20 : phaseCheck (wordOf 21 0b001111010011111111111) 14 0 0 300 20 = true := by
  decide +kernel

/-- Every phase of `001111010011111111111` at width 14. -/
theorem w001111010011111111111 : ∀ φ, φ < 21 → ∃ D rounds fuel,
    phaseCheck (wordOf 21 0b001111010011111111111) 14 D rounds fuel φ = true
  | 0, _ => ⟨0, 1, 300, w001111010011111111111_0⟩
  | 1, _ => ⟨0, 1, 300, w001111010011111111111_1⟩
  | 2, _ => ⟨0, 0, 300, w001111010011111111111_2⟩
  | 3, _ => ⟨0, 0, 300, w001111010011111111111_3⟩
  | 4, _ => ⟨0, 0, 300, w001111010011111111111_4⟩
  | 5, _ => ⟨0, 0, 300, w001111010011111111111_5⟩
  | 6, _ => ⟨0, 2, 300, w001111010011111111111_6⟩
  | 7, _ => ⟨0, 0, 300, w001111010011111111111_7⟩
  | 8, _ => ⟨0, 1, 300, w001111010011111111111_8⟩
  | 9, _ => ⟨0, 1, 300, w001111010011111111111_9⟩
  | 10, _ => ⟨0, 0, 300, w001111010011111111111_10⟩
  | 11, _ => ⟨0, 0, 300, w001111010011111111111_11⟩
  | 12, _ => ⟨0, 0, 300, w001111010011111111111_12⟩
  | 13, _ => ⟨0, 0, 300, w001111010011111111111_13⟩
  | 14, _ => ⟨0, 0, 300, w001111010011111111111_14⟩
  | 15, _ => ⟨0, 0, 300, w001111010011111111111_15⟩
  | 16, _ => ⟨0, 0, 300, w001111010011111111111_16⟩
  | 17, _ => ⟨0, 0, 300, w001111010011111111111_17⟩
  | 18, _ => ⟨0, 0, 300, w001111010011111111111_18⟩
  | 19, _ => ⟨0, 0, 300, w001111010011111111111_19⟩
  | 20, _ => ⟨0, 0, 300, w001111010011111111111_20⟩
  | _ + 21, h => absurd h (by omega)

set_option maxHeartbeats 0 in
theorem w001111111111101111111_0 : phaseCheck (wordOf 21 0b001111111111101111111) 14 0 1 300 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w001111111111101111111_1 : phaseCheck (wordOf 21 0b001111111111101111111) 14 0 2 300 1 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w001111111111101111111_2 : phaseCheck (wordOf 21 0b001111111111101111111) 14 0 0 300 2 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w001111111111101111111_3 : phaseCheck (wordOf 21 0b001111111111101111111) 14 0 0 300 3 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w001111111111101111111_4 : phaseCheck (wordOf 21 0b001111111111101111111) 14 0 0 300 4 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w001111111111101111111_5 : phaseCheck (wordOf 21 0b001111111111101111111) 14 0 0 300 5 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w001111111111101111111_6 : phaseCheck (wordOf 21 0b001111111111101111111) 14 0 0 300 6 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w001111111111101111111_7 : phaseCheck (wordOf 21 0b001111111111101111111) 14 0 0 300 7 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w001111111111101111111_8 : phaseCheck (wordOf 21 0b001111111111101111111) 14 0 0 300 8 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w001111111111101111111_9 : phaseCheck (wordOf 21 0b001111111111101111111) 14 0 0 300 9 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w001111111111101111111_10 : phaseCheck (wordOf 21 0b001111111111101111111) 14 0 0 300 10 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w001111111111101111111_11 : phaseCheck (wordOf 21 0b001111111111101111111) 14 0 0 300 11 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w001111111111101111111_12 : phaseCheck (wordOf 21 0b001111111111101111111) 14 0 0 300 12 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w001111111111101111111_13 : phaseCheck (wordOf 21 0b001111111111101111111) 14 0 1 300 13 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w001111111111101111111_14 : phaseCheck (wordOf 21 0b001111111111101111111) 14 0 0 300 14 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w001111111111101111111_15 : phaseCheck (wordOf 21 0b001111111111101111111) 14 0 0 300 15 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w001111111111101111111_16 : phaseCheck (wordOf 21 0b001111111111101111111) 14 0 0 300 16 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w001111111111101111111_17 : phaseCheck (wordOf 21 0b001111111111101111111) 14 0 0 300 17 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w001111111111101111111_18 : phaseCheck (wordOf 21 0b001111111111101111111) 14 0 0 300 18 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w001111111111101111111_19 : phaseCheck (wordOf 21 0b001111111111101111111) 14 0 0 300 19 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w001111111111101111111_20 : phaseCheck (wordOf 21 0b001111111111101111111) 14 0 0 300 20 = true := by
  decide +kernel

/-- Every phase of `001111111111101111111` at width 14. -/
theorem w001111111111101111111 : ∀ φ, φ < 21 → ∃ D rounds fuel,
    phaseCheck (wordOf 21 0b001111111111101111111) 14 D rounds fuel φ = true
  | 0, _ => ⟨0, 1, 300, w001111111111101111111_0⟩
  | 1, _ => ⟨0, 2, 300, w001111111111101111111_1⟩
  | 2, _ => ⟨0, 0, 300, w001111111111101111111_2⟩
  | 3, _ => ⟨0, 0, 300, w001111111111101111111_3⟩
  | 4, _ => ⟨0, 0, 300, w001111111111101111111_4⟩
  | 5, _ => ⟨0, 0, 300, w001111111111101111111_5⟩
  | 6, _ => ⟨0, 0, 300, w001111111111101111111_6⟩
  | 7, _ => ⟨0, 0, 300, w001111111111101111111_7⟩
  | 8, _ => ⟨0, 0, 300, w001111111111101111111_8⟩
  | 9, _ => ⟨0, 0, 300, w001111111111101111111_9⟩
  | 10, _ => ⟨0, 0, 300, w001111111111101111111_10⟩
  | 11, _ => ⟨0, 0, 300, w001111111111101111111_11⟩
  | 12, _ => ⟨0, 0, 300, w001111111111101111111_12⟩
  | 13, _ => ⟨0, 1, 300, w001111111111101111111_13⟩
  | 14, _ => ⟨0, 0, 300, w001111111111101111111_14⟩
  | 15, _ => ⟨0, 0, 300, w001111111111101111111_15⟩
  | 16, _ => ⟨0, 0, 300, w001111111111101111111_16⟩
  | 17, _ => ⟨0, 0, 300, w001111111111101111111_17⟩
  | 18, _ => ⟨0, 0, 300, w001111111111101111111_18⟩
  | 19, _ => ⟨0, 0, 300, w001111111111101111111_19⟩
  | 20, _ => ⟨0, 0, 300, w001111111111101111111_20⟩
  | _ + 21, h => absurd h (by omega)

set_option maxHeartbeats 0 in
theorem w010111110111111111111_0 : phaseCheck (wordOf 21 0b010111110111111111111) 14 0 1 300 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w010111110111111111111_1 : phaseCheck (wordOf 21 0b010111110111111111111) 14 0 0 300 1 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w010111110111111111111_2 : phaseCheck (wordOf 21 0b010111110111111111111) 14 0 1 300 2 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w010111110111111111111_3 : phaseCheck (wordOf 21 0b010111110111111111111) 14 0 0 300 3 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w010111110111111111111_4 : phaseCheck (wordOf 21 0b010111110111111111111) 14 0 0 300 4 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w010111110111111111111_5 : phaseCheck (wordOf 21 0b010111110111111111111) 14 0 0 300 5 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w010111110111111111111_6 : phaseCheck (wordOf 21 0b010111110111111111111) 14 0 0 300 6 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w010111110111111111111_7 : phaseCheck (wordOf 21 0b010111110111111111111) 14 0 0 300 7 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w010111110111111111111_8 : phaseCheck (wordOf 21 0b010111110111111111111) 14 0 2 300 8 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w010111110111111111111_9 : phaseCheck (wordOf 21 0b010111110111111111111) 14 0 0 300 9 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w010111110111111111111_10 : phaseCheck (wordOf 21 0b010111110111111111111) 14 0 0 300 10 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w010111110111111111111_11 : phaseCheck (wordOf 21 0b010111110111111111111) 14 0 0 300 11 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w010111110111111111111_12 : phaseCheck (wordOf 21 0b010111110111111111111) 14 0 0 300 12 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w010111110111111111111_13 : phaseCheck (wordOf 21 0b010111110111111111111) 14 0 0 300 13 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w010111110111111111111_14 : phaseCheck (wordOf 21 0b010111110111111111111) 14 0 0 300 14 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w010111110111111111111_15 : phaseCheck (wordOf 21 0b010111110111111111111) 14 0 0 300 15 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w010111110111111111111_16 : phaseCheck (wordOf 21 0b010111110111111111111) 14 0 0 300 16 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w010111110111111111111_17 : phaseCheck (wordOf 21 0b010111110111111111111) 14 0 0 300 17 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w010111110111111111111_18 : phaseCheck (wordOf 21 0b010111110111111111111) 14 0 0 300 18 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w010111110111111111111_19 : phaseCheck (wordOf 21 0b010111110111111111111) 14 0 0 300 19 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w010111110111111111111_20 : phaseCheck (wordOf 21 0b010111110111111111111) 14 0 0 300 20 = true := by
  decide +kernel

/-- Every phase of `010111110111111111111` at width 14. -/
theorem w010111110111111111111 : ∀ φ, φ < 21 → ∃ D rounds fuel,
    phaseCheck (wordOf 21 0b010111110111111111111) 14 D rounds fuel φ = true
  | 0, _ => ⟨0, 1, 300, w010111110111111111111_0⟩
  | 1, _ => ⟨0, 0, 300, w010111110111111111111_1⟩
  | 2, _ => ⟨0, 1, 300, w010111110111111111111_2⟩
  | 3, _ => ⟨0, 0, 300, w010111110111111111111_3⟩
  | 4, _ => ⟨0, 0, 300, w010111110111111111111_4⟩
  | 5, _ => ⟨0, 0, 300, w010111110111111111111_5⟩
  | 6, _ => ⟨0, 0, 300, w010111110111111111111_6⟩
  | 7, _ => ⟨0, 0, 300, w010111110111111111111_7⟩
  | 8, _ => ⟨0, 2, 300, w010111110111111111111_8⟩
  | 9, _ => ⟨0, 0, 300, w010111110111111111111_9⟩
  | 10, _ => ⟨0, 0, 300, w010111110111111111111_10⟩
  | 11, _ => ⟨0, 0, 300, w010111110111111111111_11⟩
  | 12, _ => ⟨0, 0, 300, w010111110111111111111_12⟩
  | 13, _ => ⟨0, 0, 300, w010111110111111111111_13⟩
  | 14, _ => ⟨0, 0, 300, w010111110111111111111_14⟩
  | 15, _ => ⟨0, 0, 300, w010111110111111111111_15⟩
  | 16, _ => ⟨0, 0, 300, w010111110111111111111_16⟩
  | 17, _ => ⟨0, 0, 300, w010111110111111111111_17⟩
  | 18, _ => ⟨0, 0, 300, w010111110111111111111_18⟩
  | 19, _ => ⟨0, 0, 300, w010111110111111111111_19⟩
  | 20, _ => ⟨0, 0, 300, w010111110111111111111_20⟩
  | _ + 21, h => absurd h (by omega)

/-- The blocks of this module, each as its least rotation `wordOf n bits`, with the width of its checks. -/
def blocksPhases21 : List ((Nat × Nat) × Nat) := [
    ((21, 0b000000000000001000001), 13), ((21, 0b000000000000001010001), 14), ((21, 0b000000000000001111111), 14),
    ((21, 0b000000000000010010001), 14), ((21, 0b000000000000011000101), 13), ((21, 0b000000000000100001111), 13),
    ((21, 0b000000000000100100111), 14), ((21, 0b000000000000101000001), 13), ((21, 0b000000000000110010111), 13),
    ((21, 0b000000000000110100111), 13), ((21, 0b000000000001100100011), 14), ((21, 0b000000000001101100111), 14),
    ((21, 0b000000000011001001011), 14), ((21, 0b000000000100101111011), 14), ((21, 0b000000000111100111111), 14),
    ((21, 0b000000000111110000001), 13), ((21, 0b000000001001011111011), 13), ((21, 0b000000001011100111011), 14),
    ((21, 0b000000001101100111011), 14), ((21, 0b000000010111111100111), 14), ((21, 0b000000101110011111011), 14),
    ((21, 0b000001101111111111001), 14), ((21, 0b000011111100111111111), 14), ((21, 0b000011111110011111111), 14),
    ((21, 0b000101111111110110011), 13), ((21, 0b000101111111111011001), 13), ((21, 0b000111110101111111111), 13),
    ((21, 0b000111111001111111111), 13), ((21, 0b000111111111100111111), 14), ((21, 0b000111111111110110011), 13),
    ((21, 0b001011111111111110111), 13), ((21, 0b001101001111111111011), 13), ((21, 0b001111010011111111111), 14),
    ((21, 0b001111111111101111111), 14), ((21, 0b010111110111111111111), 14)]

theorem blocksPhases21_phases : ∀ e ∈ blocksPhases21, ∀ φ, φ < e.1.1 → ∃ D rounds fuel,
    phaseCheck (wordOf e.1.1 e.1.2) e.2 D rounds fuel φ = true := by
  intro e he
  simp only [blocksPhases21, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact w000000000000001000001
  · exact w000000000000001010001
  · exact w000000000000001111111
  · exact w000000000000010010001
  · exact w000000000000011000101
  · exact w000000000000100001111
  · exact w000000000000100100111
  · exact w000000000000101000001
  · exact w000000000000110010111
  · exact w000000000000110100111
  · exact w000000000001100100011
  · exact w000000000001101100111
  · exact w000000000011001001011
  · exact w000000000100101111011
  · exact w000000000111100111111
  · exact w000000000111110000001
  · exact w000000001001011111011
  · exact w000000001011100111011
  · exact w000000001101100111011
  · exact w000000010111111100111
  · exact w000000101110011111011
  · exact w000001101111111111001
  · exact w000011111100111111111
  · exact w000011111110011111111
  · exact w000101111111110110011
  · exact w000101111111111011001
  · exact w000111110101111111111
  · exact w000111111001111111111
  · exact w000111111111100111111
  · exact w000111111111110110011
  · exact w001011111111111110111
  · exact w001101001111111111011
  · exact w001111010011111111111
  · exact w001111111111101111111
  · exact w010111110111111111111

theorem blocksPhases21_pos : ∀ e ∈ blocksPhases21, 1 ≤ e.2 ∧ 1 ≤ e.1.1 := by decide

/-- **The center column does not eventually repeat any of the 35 blocks of `blocksPhases21`**, from any time on
and in any rotation. -/
theorem center_not_blocksPhases21 (e : (Nat × Nat) × Nat) (he : e ∈ blocksPhases21) (T shift : Nat)
    (h : ∀ t : Nat, T ≤ t → Rule30Prize.center t = (wordOf e.1.1 e.1.2).getD ((t + shift) % e.1.1) false) :
    False :=
  center_not_phases_list blocksPhases21 blocksPhases21_pos blocksPhases21_phases e he T shift h

/-- The same in the kit's form `Rule30StripCertificates.EventuallyWord`. -/
theorem not_eventually_blocksPhases21 (e : (Nat × Nat) × Nat) (he : e ∈ blocksPhases21) :
    ¬ Rule30StripCertificates.EventuallyWord (wordOf e.1.1 e.1.2) :=
  phases_list_not_eventually blocksPhases21 blocksPhases21_pos blocksPhases21_phases e he

end Rule30Open
