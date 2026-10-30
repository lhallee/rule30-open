module

public import Rule30Open.Columns.BitPhases

/-!
# The game decided phase by phase in the kernel excludes the 11 blocks of period 19 that need 13 or 14 cells

[BitPhases](BitPhases.md) checks the finite game in the kernel one phase at a time (`phaseCheck`), and
`center_not_phases_list` turns a list of blocks whose phases all pass into exclusions. Here the checks run on the
11 blocks of period 19 that the game excludes at width 13 or 14 and that neither the kit nor
[WallSets](WallSets.md) excludes.

* `blocksPhases19`: the blocks, each as its least rotation, with the width of their checks, and one theorem per
  phase of each.
* `center_not_blocksPhases19`, `not_eventually_blocksPhases19`: the center column of the single cell does not eventually
  repeat any of them, in any rotation, and in the kit's form `EventuallyWord`.

The natural-language argument is `BitPhases19.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

open Ruliology.CellularAutomata BitGame

open Rule30StripCertificateTable (wordOf)

set_option Elab.async false

set_option maxHeartbeats 0 in
theorem w0000000000001111111_0 : phaseCheck (wordOf 19 0b0000000000001111111) 14 0 1 300 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000000001111111_1 : phaseCheck (wordOf 19 0b0000000000001111111) 14 0 2 300 1 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000000001111111_2 : phaseCheck (wordOf 19 0b0000000000001111111) 14 0 2 300 2 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000000001111111_3 : phaseCheck (wordOf 19 0b0000000000001111111) 14 0 2 300 3 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000000001111111_4 : phaseCheck (wordOf 19 0b0000000000001111111) 14 0 2 300 4 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000000001111111_5 : phaseCheck (wordOf 19 0b0000000000001111111) 14 0 2 300 5 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000000001111111_6 : phaseCheck (wordOf 19 0b0000000000001111111) 14 0 2 300 6 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000000001111111_7 : phaseCheck (wordOf 19 0b0000000000001111111) 14 0 2 300 7 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000000001111111_8 : phaseCheck (wordOf 19 0b0000000000001111111) 14 0 2 300 8 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000000001111111_9 : phaseCheck (wordOf 19 0b0000000000001111111) 14 0 1 300 9 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000000001111111_10 : phaseCheck (wordOf 19 0b0000000000001111111) 14 0 1 300 10 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000000001111111_11 : phaseCheck (wordOf 19 0b0000000000001111111) 14 0 1 300 11 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000000001111111_12 : phaseCheck (wordOf 19 0b0000000000001111111) 14 0 0 300 12 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000000001111111_13 : phaseCheck (wordOf 19 0b0000000000001111111) 14 0 0 300 13 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000000001111111_14 : phaseCheck (wordOf 19 0b0000000000001111111) 14 0 0 300 14 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000000001111111_15 : phaseCheck (wordOf 19 0b0000000000001111111) 14 0 0 300 15 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000000001111111_16 : phaseCheck (wordOf 19 0b0000000000001111111) 14 0 0 300 16 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000000001111111_17 : phaseCheck (wordOf 19 0b0000000000001111111) 14 0 0 300 17 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000000001111111_18 : phaseCheck (wordOf 19 0b0000000000001111111) 14 0 0 300 18 = true := by
  decide +kernel

/-- Every phase of `0000000000001111111` at width 14. -/
theorem w0000000000001111111 : ∀ φ, φ < 19 → ∃ D rounds fuel,
    phaseCheck (wordOf 19 0b0000000000001111111) 14 D rounds fuel φ = true
  | 0, _ => ⟨0, 1, 300, w0000000000001111111_0⟩
  | 1, _ => ⟨0, 2, 300, w0000000000001111111_1⟩
  | 2, _ => ⟨0, 2, 300, w0000000000001111111_2⟩
  | 3, _ => ⟨0, 2, 300, w0000000000001111111_3⟩
  | 4, _ => ⟨0, 2, 300, w0000000000001111111_4⟩
  | 5, _ => ⟨0, 2, 300, w0000000000001111111_5⟩
  | 6, _ => ⟨0, 2, 300, w0000000000001111111_6⟩
  | 7, _ => ⟨0, 2, 300, w0000000000001111111_7⟩
  | 8, _ => ⟨0, 2, 300, w0000000000001111111_8⟩
  | 9, _ => ⟨0, 1, 300, w0000000000001111111_9⟩
  | 10, _ => ⟨0, 1, 300, w0000000000001111111_10⟩
  | 11, _ => ⟨0, 1, 300, w0000000000001111111_11⟩
  | 12, _ => ⟨0, 0, 300, w0000000000001111111_12⟩
  | 13, _ => ⟨0, 0, 300, w0000000000001111111_13⟩
  | 14, _ => ⟨0, 0, 300, w0000000000001111111_14⟩
  | 15, _ => ⟨0, 0, 300, w0000000000001111111_15⟩
  | 16, _ => ⟨0, 0, 300, w0000000000001111111_16⟩
  | 17, _ => ⟨0, 0, 300, w0000000000001111111_17⟩
  | 18, _ => ⟨0, 0, 300, w0000000000001111111_18⟩
  | _ + 19, h => absurd h (by omega)

set_option maxHeartbeats 0 in
theorem w0000000000101001111_0 : phaseCheck (wordOf 19 0b0000000000101001111) 13 0 1 300 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000000101001111_1 : phaseCheck (wordOf 19 0b0000000000101001111) 13 0 1 300 1 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000000101001111_2 : phaseCheck (wordOf 19 0b0000000000101001111) 13 0 1 300 2 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000000101001111_3 : phaseCheck (wordOf 19 0b0000000000101001111) 13 0 1 300 3 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000000101001111_4 : phaseCheck (wordOf 19 0b0000000000101001111) 13 0 1 300 4 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000000101001111_5 : phaseCheck (wordOf 19 0b0000000000101001111) 13 0 1 300 5 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000000101001111_6 : phaseCheck (wordOf 19 0b0000000000101001111) 13 0 1 300 6 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000000101001111_7 : phaseCheck (wordOf 19 0b0000000000101001111) 13 0 1 300 7 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000000101001111_8 : phaseCheck (wordOf 19 0b0000000000101001111) 13 0 1 300 8 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000000101001111_9 : phaseCheck (wordOf 19 0b0000000000101001111) 13 0 1 300 9 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000000101001111_10 : phaseCheck (wordOf 19 0b0000000000101001111) 13 0 0 300 10 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000000101001111_11 : phaseCheck (wordOf 19 0b0000000000101001111) 13 0 1 300 11 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000000101001111_12 : phaseCheck (wordOf 19 0b0000000000101001111) 13 0 0 300 12 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000000101001111_13 : phaseCheck (wordOf 19 0b0000000000101001111) 13 0 1 300 13 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000000101001111_14 : phaseCheck (wordOf 19 0b0000000000101001111) 13 0 1 300 14 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000000101001111_15 : phaseCheck (wordOf 19 0b0000000000101001111) 13 0 0 300 15 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000000101001111_16 : phaseCheck (wordOf 19 0b0000000000101001111) 13 0 0 300 16 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000000101001111_17 : phaseCheck (wordOf 19 0b0000000000101001111) 13 0 0 300 17 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000000101001111_18 : phaseCheck (wordOf 19 0b0000000000101001111) 13 0 0 300 18 = true := by
  decide +kernel

/-- Every phase of `0000000000101001111` at width 13. -/
theorem w0000000000101001111 : ∀ φ, φ < 19 → ∃ D rounds fuel,
    phaseCheck (wordOf 19 0b0000000000101001111) 13 D rounds fuel φ = true
  | 0, _ => ⟨0, 1, 300, w0000000000101001111_0⟩
  | 1, _ => ⟨0, 1, 300, w0000000000101001111_1⟩
  | 2, _ => ⟨0, 1, 300, w0000000000101001111_2⟩
  | 3, _ => ⟨0, 1, 300, w0000000000101001111_3⟩
  | 4, _ => ⟨0, 1, 300, w0000000000101001111_4⟩
  | 5, _ => ⟨0, 1, 300, w0000000000101001111_5⟩
  | 6, _ => ⟨0, 1, 300, w0000000000101001111_6⟩
  | 7, _ => ⟨0, 1, 300, w0000000000101001111_7⟩
  | 8, _ => ⟨0, 1, 300, w0000000000101001111_8⟩
  | 9, _ => ⟨0, 1, 300, w0000000000101001111_9⟩
  | 10, _ => ⟨0, 0, 300, w0000000000101001111_10⟩
  | 11, _ => ⟨0, 1, 300, w0000000000101001111_11⟩
  | 12, _ => ⟨0, 0, 300, w0000000000101001111_12⟩
  | 13, _ => ⟨0, 1, 300, w0000000000101001111_13⟩
  | 14, _ => ⟨0, 1, 300, w0000000000101001111_14⟩
  | 15, _ => ⟨0, 0, 300, w0000000000101001111_15⟩
  | 16, _ => ⟨0, 0, 300, w0000000000101001111_16⟩
  | 17, _ => ⟨0, 0, 300, w0000000000101001111_17⟩
  | 18, _ => ⟨0, 0, 300, w0000000000101001111_18⟩
  | _ + 19, h => absurd h (by omega)

set_option maxHeartbeats 0 in
theorem w0000000000110101111_0 : phaseCheck (wordOf 19 0b0000000000110101111) 14 0 2 300 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000000110101111_1 : phaseCheck (wordOf 19 0b0000000000110101111) 14 0 1 300 1 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000000110101111_2 : phaseCheck (wordOf 19 0b0000000000110101111) 14 0 1 300 2 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000000110101111_3 : phaseCheck (wordOf 19 0b0000000000110101111) 14 0 1 300 3 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000000110101111_4 : phaseCheck (wordOf 19 0b0000000000110101111) 14 0 1 300 4 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000000110101111_5 : phaseCheck (wordOf 19 0b0000000000110101111) 14 0 1 300 5 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000000110101111_6 : phaseCheck (wordOf 19 0b0000000000110101111) 14 0 1 300 6 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000000110101111_7 : phaseCheck (wordOf 19 0b0000000000110101111) 14 0 1 300 7 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000000110101111_8 : phaseCheck (wordOf 19 0b0000000000110101111) 14 0 1 300 8 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000000110101111_9 : phaseCheck (wordOf 19 0b0000000000110101111) 14 0 1 300 9 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000000110101111_10 : phaseCheck (wordOf 19 0b0000000000110101111) 14 0 0 300 10 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000000110101111_11 : phaseCheck (wordOf 19 0b0000000000110101111) 14 0 0 300 11 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000000110101111_12 : phaseCheck (wordOf 19 0b0000000000110101111) 14 0 1 300 12 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000000110101111_13 : phaseCheck (wordOf 19 0b0000000000110101111) 14 0 0 300 13 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000000110101111_14 : phaseCheck (wordOf 19 0b0000000000110101111) 14 0 1 300 14 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000000110101111_15 : phaseCheck (wordOf 19 0b0000000000110101111) 14 0 0 300 15 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000000110101111_16 : phaseCheck (wordOf 19 0b0000000000110101111) 14 0 0 300 16 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000000110101111_17 : phaseCheck (wordOf 19 0b0000000000110101111) 14 0 0 300 17 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000000110101111_18 : phaseCheck (wordOf 19 0b0000000000110101111) 14 0 0 300 18 = true := by
  decide +kernel

/-- Every phase of `0000000000110101111` at width 14. -/
theorem w0000000000110101111 : ∀ φ, φ < 19 → ∃ D rounds fuel,
    phaseCheck (wordOf 19 0b0000000000110101111) 14 D rounds fuel φ = true
  | 0, _ => ⟨0, 2, 300, w0000000000110101111_0⟩
  | 1, _ => ⟨0, 1, 300, w0000000000110101111_1⟩
  | 2, _ => ⟨0, 1, 300, w0000000000110101111_2⟩
  | 3, _ => ⟨0, 1, 300, w0000000000110101111_3⟩
  | 4, _ => ⟨0, 1, 300, w0000000000110101111_4⟩
  | 5, _ => ⟨0, 1, 300, w0000000000110101111_5⟩
  | 6, _ => ⟨0, 1, 300, w0000000000110101111_6⟩
  | 7, _ => ⟨0, 1, 300, w0000000000110101111_7⟩
  | 8, _ => ⟨0, 1, 300, w0000000000110101111_8⟩
  | 9, _ => ⟨0, 1, 300, w0000000000110101111_9⟩
  | 10, _ => ⟨0, 0, 300, w0000000000110101111_10⟩
  | 11, _ => ⟨0, 0, 300, w0000000000110101111_11⟩
  | 12, _ => ⟨0, 1, 300, w0000000000110101111_12⟩
  | 13, _ => ⟨0, 0, 300, w0000000000110101111_13⟩
  | 14, _ => ⟨0, 1, 300, w0000000000110101111_14⟩
  | 15, _ => ⟨0, 0, 300, w0000000000110101111_15⟩
  | 16, _ => ⟨0, 0, 300, w0000000000110101111_16⟩
  | 17, _ => ⟨0, 0, 300, w0000000000110101111_17⟩
  | 18, _ => ⟨0, 0, 300, w0000000000110101111_18⟩
  | _ + 19, h => absurd h (by omega)

set_option maxHeartbeats 0 in
theorem w0000000001001010111_0 : phaseCheck (wordOf 19 0b0000000001001010111) 14 0 1 300 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000001001010111_1 : phaseCheck (wordOf 19 0b0000000001001010111) 14 0 1 300 1 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000001001010111_2 : phaseCheck (wordOf 19 0b0000000001001010111) 14 0 1 300 2 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000001001010111_3 : phaseCheck (wordOf 19 0b0000000001001010111) 14 0 1 300 3 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000001001010111_4 : phaseCheck (wordOf 19 0b0000000001001010111) 14 0 1 300 4 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000001001010111_5 : phaseCheck (wordOf 19 0b0000000001001010111) 14 0 1 300 5 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000001001010111_6 : phaseCheck (wordOf 19 0b0000000001001010111) 14 0 1 300 6 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000001001010111_7 : phaseCheck (wordOf 19 0b0000000001001010111) 14 0 1 300 7 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000001001010111_8 : phaseCheck (wordOf 19 0b0000000001001010111) 14 0 1 300 8 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000001001010111_9 : phaseCheck (wordOf 19 0b0000000001001010111) 14 0 0 300 9 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000001001010111_10 : phaseCheck (wordOf 19 0b0000000001001010111) 14 0 1 300 10 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000001001010111_11 : phaseCheck (wordOf 19 0b0000000001001010111) 14 0 1 300 11 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000001001010111_12 : phaseCheck (wordOf 19 0b0000000001001010111) 14 0 0 300 12 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000001001010111_13 : phaseCheck (wordOf 19 0b0000000001001010111) 14 0 1 300 13 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000001001010111_14 : phaseCheck (wordOf 19 0b0000000001001010111) 14 0 0 300 14 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000001001010111_15 : phaseCheck (wordOf 19 0b0000000001001010111) 14 0 4 300 15 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000001001010111_16 : phaseCheck (wordOf 19 0b0000000001001010111) 14 0 0 300 16 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000001001010111_17 : phaseCheck (wordOf 19 0b0000000001001010111) 14 0 0 300 17 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000001001010111_18 : phaseCheck (wordOf 19 0b0000000001001010111) 14 0 0 300 18 = true := by
  decide +kernel

/-- Every phase of `0000000001001010111` at width 14. -/
theorem w0000000001001010111 : ∀ φ, φ < 19 → ∃ D rounds fuel,
    phaseCheck (wordOf 19 0b0000000001001010111) 14 D rounds fuel φ = true
  | 0, _ => ⟨0, 1, 300, w0000000001001010111_0⟩
  | 1, _ => ⟨0, 1, 300, w0000000001001010111_1⟩
  | 2, _ => ⟨0, 1, 300, w0000000001001010111_2⟩
  | 3, _ => ⟨0, 1, 300, w0000000001001010111_3⟩
  | 4, _ => ⟨0, 1, 300, w0000000001001010111_4⟩
  | 5, _ => ⟨0, 1, 300, w0000000001001010111_5⟩
  | 6, _ => ⟨0, 1, 300, w0000000001001010111_6⟩
  | 7, _ => ⟨0, 1, 300, w0000000001001010111_7⟩
  | 8, _ => ⟨0, 1, 300, w0000000001001010111_8⟩
  | 9, _ => ⟨0, 0, 300, w0000000001001010111_9⟩
  | 10, _ => ⟨0, 1, 300, w0000000001001010111_10⟩
  | 11, _ => ⟨0, 1, 300, w0000000001001010111_11⟩
  | 12, _ => ⟨0, 0, 300, w0000000001001010111_12⟩
  | 13, _ => ⟨0, 1, 300, w0000000001001010111_13⟩
  | 14, _ => ⟨0, 0, 300, w0000000001001010111_14⟩
  | 15, _ => ⟨0, 4, 300, w0000000001001010111_15⟩
  | 16, _ => ⟨0, 0, 300, w0000000001001010111_16⟩
  | 17, _ => ⟨0, 0, 300, w0000000001001010111_17⟩
  | 18, _ => ⟨0, 0, 300, w0000000001001010111_18⟩
  | _ + 19, h => absurd h (by omega)

set_option maxHeartbeats 0 in
theorem w0000000101001111011_0 : phaseCheck (wordOf 19 0b0000000101001111011) 13 0 3 300 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000101001111011_1 : phaseCheck (wordOf 19 0b0000000101001111011) 13 0 2 300 1 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000101001111011_2 : phaseCheck (wordOf 19 0b0000000101001111011) 13 0 1 300 2 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000101001111011_3 : phaseCheck (wordOf 19 0b0000000101001111011) 13 0 1 300 3 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000101001111011_4 : phaseCheck (wordOf 19 0b0000000101001111011) 13 0 1 300 4 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000101001111011_5 : phaseCheck (wordOf 19 0b0000000101001111011) 13 0 1 300 5 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000101001111011_6 : phaseCheck (wordOf 19 0b0000000101001111011) 13 0 1 300 6 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000101001111011_7 : phaseCheck (wordOf 19 0b0000000101001111011) 13 0 0 300 7 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000101001111011_8 : phaseCheck (wordOf 19 0b0000000101001111011) 13 0 1 300 8 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000101001111011_9 : phaseCheck (wordOf 19 0b0000000101001111011) 13 0 0 300 9 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000101001111011_10 : phaseCheck (wordOf 19 0b0000000101001111011) 13 0 2 300 10 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000101001111011_11 : phaseCheck (wordOf 19 0b0000000101001111011) 13 0 2 300 11 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000101001111011_12 : phaseCheck (wordOf 19 0b0000000101001111011) 13 0 0 300 12 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000101001111011_13 : phaseCheck (wordOf 19 0b0000000101001111011) 13 0 0 300 13 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000101001111011_14 : phaseCheck (wordOf 19 0b0000000101001111011) 13 0 0 300 14 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000101001111011_15 : phaseCheck (wordOf 19 0b0000000101001111011) 13 0 0 300 15 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000101001111011_16 : phaseCheck (wordOf 19 0b0000000101001111011) 13 0 2 300 16 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000101001111011_17 : phaseCheck (wordOf 19 0b0000000101001111011) 13 0 0 300 17 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000000101001111011_18 : phaseCheck (wordOf 19 0b0000000101001111011) 13 0 0 300 18 = true := by
  decide +kernel

/-- Every phase of `0000000101001111011` at width 13. -/
theorem w0000000101001111011 : ∀ φ, φ < 19 → ∃ D rounds fuel,
    phaseCheck (wordOf 19 0b0000000101001111011) 13 D rounds fuel φ = true
  | 0, _ => ⟨0, 3, 300, w0000000101001111011_0⟩
  | 1, _ => ⟨0, 2, 300, w0000000101001111011_1⟩
  | 2, _ => ⟨0, 1, 300, w0000000101001111011_2⟩
  | 3, _ => ⟨0, 1, 300, w0000000101001111011_3⟩
  | 4, _ => ⟨0, 1, 300, w0000000101001111011_4⟩
  | 5, _ => ⟨0, 1, 300, w0000000101001111011_5⟩
  | 6, _ => ⟨0, 1, 300, w0000000101001111011_6⟩
  | 7, _ => ⟨0, 0, 300, w0000000101001111011_7⟩
  | 8, _ => ⟨0, 1, 300, w0000000101001111011_8⟩
  | 9, _ => ⟨0, 0, 300, w0000000101001111011_9⟩
  | 10, _ => ⟨0, 2, 300, w0000000101001111011_10⟩
  | 11, _ => ⟨0, 2, 300, w0000000101001111011_11⟩
  | 12, _ => ⟨0, 0, 300, w0000000101001111011_12⟩
  | 13, _ => ⟨0, 0, 300, w0000000101001111011_13⟩
  | 14, _ => ⟨0, 0, 300, w0000000101001111011_14⟩
  | 15, _ => ⟨0, 0, 300, w0000000101001111011_15⟩
  | 16, _ => ⟨0, 2, 300, w0000000101001111011_16⟩
  | 17, _ => ⟨0, 0, 300, w0000000101001111011_17⟩
  | 18, _ => ⟨0, 0, 300, w0000000101001111011_18⟩
  | _ + 19, h => absurd h (by omega)

set_option maxHeartbeats 0 in
theorem w0000001011011000011_0 : phaseCheck (wordOf 19 0b0000001011011000011) 13 0 2 300 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000001011011000011_1 : phaseCheck (wordOf 19 0b0000001011011000011) 13 0 1 300 1 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000001011011000011_2 : phaseCheck (wordOf 19 0b0000001011011000011) 13 0 1 300 2 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000001011011000011_3 : phaseCheck (wordOf 19 0b0000001011011000011) 13 0 1 300 3 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000001011011000011_4 : phaseCheck (wordOf 19 0b0000001011011000011) 13 0 1 300 4 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000001011011000011_5 : phaseCheck (wordOf 19 0b0000001011011000011) 13 0 1 300 5 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000001011011000011_6 : phaseCheck (wordOf 19 0b0000001011011000011) 13 0 0 300 6 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000001011011000011_7 : phaseCheck (wordOf 19 0b0000001011011000011) 13 0 1 300 7 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000001011011000011_8 : phaseCheck (wordOf 19 0b0000001011011000011) 13 0 0 300 8 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000001011011000011_9 : phaseCheck (wordOf 19 0b0000001011011000011) 13 0 0 300 9 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000001011011000011_10 : phaseCheck (wordOf 19 0b0000001011011000011) 13 0 2 300 10 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000001011011000011_11 : phaseCheck (wordOf 19 0b0000001011011000011) 13 0 0 300 11 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000001011011000011_12 : phaseCheck (wordOf 19 0b0000001011011000011) 13 0 0 300 12 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000001011011000011_13 : phaseCheck (wordOf 19 0b0000001011011000011) 13 0 2 300 13 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000001011011000011_14 : phaseCheck (wordOf 19 0b0000001011011000011) 13 0 1 300 14 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000001011011000011_15 : phaseCheck (wordOf 19 0b0000001011011000011) 13 0 1 300 15 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000001011011000011_16 : phaseCheck (wordOf 19 0b0000001011011000011) 13 0 1 300 16 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000001011011000011_17 : phaseCheck (wordOf 19 0b0000001011011000011) 13 0 0 300 17 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000001011011000011_18 : phaseCheck (wordOf 19 0b0000001011011000011) 13 0 0 300 18 = true := by
  decide +kernel

/-- Every phase of `0000001011011000011` at width 13. -/
theorem w0000001011011000011 : ∀ φ, φ < 19 → ∃ D rounds fuel,
    phaseCheck (wordOf 19 0b0000001011011000011) 13 D rounds fuel φ = true
  | 0, _ => ⟨0, 2, 300, w0000001011011000011_0⟩
  | 1, _ => ⟨0, 1, 300, w0000001011011000011_1⟩
  | 2, _ => ⟨0, 1, 300, w0000001011011000011_2⟩
  | 3, _ => ⟨0, 1, 300, w0000001011011000011_3⟩
  | 4, _ => ⟨0, 1, 300, w0000001011011000011_4⟩
  | 5, _ => ⟨0, 1, 300, w0000001011011000011_5⟩
  | 6, _ => ⟨0, 0, 300, w0000001011011000011_6⟩
  | 7, _ => ⟨0, 1, 300, w0000001011011000011_7⟩
  | 8, _ => ⟨0, 0, 300, w0000001011011000011_8⟩
  | 9, _ => ⟨0, 0, 300, w0000001011011000011_9⟩
  | 10, _ => ⟨0, 2, 300, w0000001011011000011_10⟩
  | 11, _ => ⟨0, 0, 300, w0000001011011000011_11⟩
  | 12, _ => ⟨0, 0, 300, w0000001011011000011_12⟩
  | 13, _ => ⟨0, 2, 300, w0000001011011000011_13⟩
  | 14, _ => ⟨0, 1, 300, w0000001011011000011_14⟩
  | 15, _ => ⟨0, 1, 300, w0000001011011000011_15⟩
  | 16, _ => ⟨0, 1, 300, w0000001011011000011_16⟩
  | 17, _ => ⟨0, 0, 300, w0000001011011000011_17⟩
  | 18, _ => ⟨0, 0, 300, w0000001011011000011_18⟩
  | _ + 19, h => absurd h (by omega)

set_option maxHeartbeats 0 in
theorem w0000100111111111111_0 : phaseCheck (wordOf 19 0b0000100111111111111) 13 0 1 300 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000100111111111111_1 : phaseCheck (wordOf 19 0b0000100111111111111) 13 0 1 300 1 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000100111111111111_2 : phaseCheck (wordOf 19 0b0000100111111111111) 13 0 1 300 2 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000100111111111111_3 : phaseCheck (wordOf 19 0b0000100111111111111) 13 0 1 300 3 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000100111111111111_4 : phaseCheck (wordOf 19 0b0000100111111111111) 13 0 0 300 4 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000100111111111111_5 : phaseCheck (wordOf 19 0b0000100111111111111) 13 0 1 300 5 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000100111111111111_6 : phaseCheck (wordOf 19 0b0000100111111111111) 13 0 2 300 6 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000100111111111111_7 : phaseCheck (wordOf 19 0b0000100111111111111) 13 0 0 300 7 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000100111111111111_8 : phaseCheck (wordOf 19 0b0000100111111111111) 13 0 0 300 8 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000100111111111111_9 : phaseCheck (wordOf 19 0b0000100111111111111) 13 0 0 300 9 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000100111111111111_10 : phaseCheck (wordOf 19 0b0000100111111111111) 13 0 0 300 10 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000100111111111111_11 : phaseCheck (wordOf 19 0b0000100111111111111) 13 0 0 300 11 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000100111111111111_12 : phaseCheck (wordOf 19 0b0000100111111111111) 13 0 0 300 12 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000100111111111111_13 : phaseCheck (wordOf 19 0b0000100111111111111) 13 0 0 300 13 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000100111111111111_14 : phaseCheck (wordOf 19 0b0000100111111111111) 13 0 0 300 14 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000100111111111111_15 : phaseCheck (wordOf 19 0b0000100111111111111) 13 0 0 300 15 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000100111111111111_16 : phaseCheck (wordOf 19 0b0000100111111111111) 13 0 0 300 16 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000100111111111111_17 : phaseCheck (wordOf 19 0b0000100111111111111) 13 0 0 300 17 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000100111111111111_18 : phaseCheck (wordOf 19 0b0000100111111111111) 13 0 0 300 18 = true := by
  decide +kernel

/-- Every phase of `0000100111111111111` at width 13. -/
theorem w0000100111111111111 : ∀ φ, φ < 19 → ∃ D rounds fuel,
    phaseCheck (wordOf 19 0b0000100111111111111) 13 D rounds fuel φ = true
  | 0, _ => ⟨0, 1, 300, w0000100111111111111_0⟩
  | 1, _ => ⟨0, 1, 300, w0000100111111111111_1⟩
  | 2, _ => ⟨0, 1, 300, w0000100111111111111_2⟩
  | 3, _ => ⟨0, 1, 300, w0000100111111111111_3⟩
  | 4, _ => ⟨0, 0, 300, w0000100111111111111_4⟩
  | 5, _ => ⟨0, 1, 300, w0000100111111111111_5⟩
  | 6, _ => ⟨0, 2, 300, w0000100111111111111_6⟩
  | 7, _ => ⟨0, 0, 300, w0000100111111111111_7⟩
  | 8, _ => ⟨0, 0, 300, w0000100111111111111_8⟩
  | 9, _ => ⟨0, 0, 300, w0000100111111111111_9⟩
  | 10, _ => ⟨0, 0, 300, w0000100111111111111_10⟩
  | 11, _ => ⟨0, 0, 300, w0000100111111111111_11⟩
  | 12, _ => ⟨0, 0, 300, w0000100111111111111_12⟩
  | 13, _ => ⟨0, 0, 300, w0000100111111111111_13⟩
  | 14, _ => ⟨0, 0, 300, w0000100111111111111_14⟩
  | 15, _ => ⟨0, 0, 300, w0000100111111111111_15⟩
  | 16, _ => ⟨0, 0, 300, w0000100111111111111_16⟩
  | 17, _ => ⟨0, 0, 300, w0000100111111111111_17⟩
  | 18, _ => ⟨0, 0, 300, w0000100111111111111_18⟩
  | _ + 19, h => absurd h (by omega)

set_option maxHeartbeats 0 in
theorem w0000101111111001001_0 : phaseCheck (wordOf 19 0b0000101111111001001) 13 0 1 300 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000101111111001001_1 : phaseCheck (wordOf 19 0b0000101111111001001) 13 0 2 300 1 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000101111111001001_2 : phaseCheck (wordOf 19 0b0000101111111001001) 13 0 2 300 2 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000101111111001001_3 : phaseCheck (wordOf 19 0b0000101111111001001) 13 0 1 300 3 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000101111111001001_4 : phaseCheck (wordOf 19 0b0000101111111001001) 13 0 0 300 4 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000101111111001001_5 : phaseCheck (wordOf 19 0b0000101111111001001) 13 0 1 300 5 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000101111111001001_6 : phaseCheck (wordOf 19 0b0000101111111001001) 13 0 0 300 6 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000101111111001001_7 : phaseCheck (wordOf 19 0b0000101111111001001) 13 0 0 300 7 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000101111111001001_8 : phaseCheck (wordOf 19 0b0000101111111001001) 13 0 0 300 8 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000101111111001001_9 : phaseCheck (wordOf 19 0b0000101111111001001) 13 0 0 300 9 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000101111111001001_10 : phaseCheck (wordOf 19 0b0000101111111001001) 13 0 0 300 10 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000101111111001001_11 : phaseCheck (wordOf 19 0b0000101111111001001) 13 0 0 300 11 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000101111111001001_12 : phaseCheck (wordOf 19 0b0000101111111001001) 13 0 0 300 12 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000101111111001001_13 : phaseCheck (wordOf 19 0b0000101111111001001) 13 0 1 300 13 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000101111111001001_14 : phaseCheck (wordOf 19 0b0000101111111001001) 13 0 1 300 14 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000101111111001001_15 : phaseCheck (wordOf 19 0b0000101111111001001) 13 0 0 300 15 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000101111111001001_16 : phaseCheck (wordOf 19 0b0000101111111001001) 13 0 1 300 16 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000101111111001001_17 : phaseCheck (wordOf 19 0b0000101111111001001) 13 0 2 300 17 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0000101111111001001_18 : phaseCheck (wordOf 19 0b0000101111111001001) 13 0 0 300 18 = true := by
  decide +kernel

/-- Every phase of `0000101111111001001` at width 13. -/
theorem w0000101111111001001 : ∀ φ, φ < 19 → ∃ D rounds fuel,
    phaseCheck (wordOf 19 0b0000101111111001001) 13 D rounds fuel φ = true
  | 0, _ => ⟨0, 1, 300, w0000101111111001001_0⟩
  | 1, _ => ⟨0, 2, 300, w0000101111111001001_1⟩
  | 2, _ => ⟨0, 2, 300, w0000101111111001001_2⟩
  | 3, _ => ⟨0, 1, 300, w0000101111111001001_3⟩
  | 4, _ => ⟨0, 0, 300, w0000101111111001001_4⟩
  | 5, _ => ⟨0, 1, 300, w0000101111111001001_5⟩
  | 6, _ => ⟨0, 0, 300, w0000101111111001001_6⟩
  | 7, _ => ⟨0, 0, 300, w0000101111111001001_7⟩
  | 8, _ => ⟨0, 0, 300, w0000101111111001001_8⟩
  | 9, _ => ⟨0, 0, 300, w0000101111111001001_9⟩
  | 10, _ => ⟨0, 0, 300, w0000101111111001001_10⟩
  | 11, _ => ⟨0, 0, 300, w0000101111111001001_11⟩
  | 12, _ => ⟨0, 0, 300, w0000101111111001001_12⟩
  | 13, _ => ⟨0, 1, 300, w0000101111111001001_13⟩
  | 14, _ => ⟨0, 1, 300, w0000101111111001001_14⟩
  | 15, _ => ⟨0, 0, 300, w0000101111111001001_15⟩
  | 16, _ => ⟨0, 1, 300, w0000101111111001001_16⟩
  | 17, _ => ⟨0, 2, 300, w0000101111111001001_17⟩
  | 18, _ => ⟨0, 0, 300, w0000101111111001001_18⟩
  | _ + 19, h => absurd h (by omega)

set_option maxHeartbeats 0 in
theorem w0001011100111111011_0 : phaseCheck (wordOf 19 0b0001011100111111011) 14 0 3 300 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0001011100111111011_1 : phaseCheck (wordOf 19 0b0001011100111111011) 14 0 2 300 1 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0001011100111111011_2 : phaseCheck (wordOf 19 0b0001011100111111011) 14 0 1 300 2 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0001011100111111011_3 : phaseCheck (wordOf 19 0b0001011100111111011) 14 0 0 300 3 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0001011100111111011_4 : phaseCheck (wordOf 19 0b0001011100111111011) 14 0 1 300 4 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0001011100111111011_5 : phaseCheck (wordOf 19 0b0001011100111111011) 14 0 0 300 5 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0001011100111111011_6 : phaseCheck (wordOf 19 0b0001011100111111011) 14 0 0 300 6 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0001011100111111011_7 : phaseCheck (wordOf 19 0b0001011100111111011) 14 0 0 300 7 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0001011100111111011_8 : phaseCheck (wordOf 19 0b0001011100111111011) 14 0 2 300 8 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0001011100111111011_9 : phaseCheck (wordOf 19 0b0001011100111111011) 14 0 4 300 9 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0001011100111111011_10 : phaseCheck (wordOf 19 0b0001011100111111011) 14 0 0 300 10 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0001011100111111011_11 : phaseCheck (wordOf 19 0b0001011100111111011) 14 0 0 300 11 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0001011100111111011_12 : phaseCheck (wordOf 19 0b0001011100111111011) 14 0 0 300 12 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0001011100111111011_13 : phaseCheck (wordOf 19 0b0001011100111111011) 14 0 0 300 13 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0001011100111111011_14 : phaseCheck (wordOf 19 0b0001011100111111011) 14 0 0 300 14 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0001011100111111011_15 : phaseCheck (wordOf 19 0b0001011100111111011) 14 0 0 300 15 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0001011100111111011_16 : phaseCheck (wordOf 19 0b0001011100111111011) 14 0 3 300 16 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0001011100111111011_17 : phaseCheck (wordOf 19 0b0001011100111111011) 14 0 0 300 17 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0001011100111111011_18 : phaseCheck (wordOf 19 0b0001011100111111011) 14 0 0 300 18 = true := by
  decide +kernel

/-- Every phase of `0001011100111111011` at width 14. -/
theorem w0001011100111111011 : ∀ φ, φ < 19 → ∃ D rounds fuel,
    phaseCheck (wordOf 19 0b0001011100111111011) 14 D rounds fuel φ = true
  | 0, _ => ⟨0, 3, 300, w0001011100111111011_0⟩
  | 1, _ => ⟨0, 2, 300, w0001011100111111011_1⟩
  | 2, _ => ⟨0, 1, 300, w0001011100111111011_2⟩
  | 3, _ => ⟨0, 0, 300, w0001011100111111011_3⟩
  | 4, _ => ⟨0, 1, 300, w0001011100111111011_4⟩
  | 5, _ => ⟨0, 0, 300, w0001011100111111011_5⟩
  | 6, _ => ⟨0, 0, 300, w0001011100111111011_6⟩
  | 7, _ => ⟨0, 0, 300, w0001011100111111011_7⟩
  | 8, _ => ⟨0, 2, 300, w0001011100111111011_8⟩
  | 9, _ => ⟨0, 4, 300, w0001011100111111011_9⟩
  | 10, _ => ⟨0, 0, 300, w0001011100111111011_10⟩
  | 11, _ => ⟨0, 0, 300, w0001011100111111011_11⟩
  | 12, _ => ⟨0, 0, 300, w0001011100111111011_12⟩
  | 13, _ => ⟨0, 0, 300, w0001011100111111011_13⟩
  | 14, _ => ⟨0, 0, 300, w0001011100111111011_14⟩
  | 15, _ => ⟨0, 0, 300, w0001011100111111011_15⟩
  | 16, _ => ⟨0, 3, 300, w0001011100111111011_16⟩
  | 17, _ => ⟨0, 0, 300, w0001011100111111011_17⟩
  | 18, _ => ⟨0, 0, 300, w0001011100111111011_18⟩
  | _ + 19, h => absurd h (by omega)

set_option maxHeartbeats 0 in
theorem w0001011111111111001_0 : phaseCheck (wordOf 19 0b0001011111111111001) 13 0 1 300 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0001011111111111001_1 : phaseCheck (wordOf 19 0b0001011111111111001) 13 0 2 300 1 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0001011111111111001_2 : phaseCheck (wordOf 19 0b0001011111111111001) 13 0 1 300 2 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0001011111111111001_3 : phaseCheck (wordOf 19 0b0001011111111111001) 13 0 0 300 3 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0001011111111111001_4 : phaseCheck (wordOf 19 0b0001011111111111001) 13 0 1 300 4 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0001011111111111001_5 : phaseCheck (wordOf 19 0b0001011111111111001) 13 0 0 300 5 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0001011111111111001_6 : phaseCheck (wordOf 19 0b0001011111111111001) 13 0 0 300 6 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0001011111111111001_7 : phaseCheck (wordOf 19 0b0001011111111111001) 13 0 0 300 7 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0001011111111111001_8 : phaseCheck (wordOf 19 0b0001011111111111001) 13 0 0 300 8 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0001011111111111001_9 : phaseCheck (wordOf 19 0b0001011111111111001) 13 0 0 300 9 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0001011111111111001_10 : phaseCheck (wordOf 19 0b0001011111111111001) 13 0 0 300 10 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0001011111111111001_11 : phaseCheck (wordOf 19 0b0001011111111111001) 13 0 0 300 11 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0001011111111111001_12 : phaseCheck (wordOf 19 0b0001011111111111001) 13 0 0 300 12 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0001011111111111001_13 : phaseCheck (wordOf 19 0b0001011111111111001) 13 0 0 300 13 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0001011111111111001_14 : phaseCheck (wordOf 19 0b0001011111111111001) 13 0 0 300 14 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0001011111111111001_15 : phaseCheck (wordOf 19 0b0001011111111111001) 13 0 0 300 15 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0001011111111111001_16 : phaseCheck (wordOf 19 0b0001011111111111001) 13 0 1 300 16 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0001011111111111001_17 : phaseCheck (wordOf 19 0b0001011111111111001) 13 0 1 300 17 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0001011111111111001_18 : phaseCheck (wordOf 19 0b0001011111111111001) 13 0 0 300 18 = true := by
  decide +kernel

/-- Every phase of `0001011111111111001` at width 13. -/
theorem w0001011111111111001 : ∀ φ, φ < 19 → ∃ D rounds fuel,
    phaseCheck (wordOf 19 0b0001011111111111001) 13 D rounds fuel φ = true
  | 0, _ => ⟨0, 1, 300, w0001011111111111001_0⟩
  | 1, _ => ⟨0, 2, 300, w0001011111111111001_1⟩
  | 2, _ => ⟨0, 1, 300, w0001011111111111001_2⟩
  | 3, _ => ⟨0, 0, 300, w0001011111111111001_3⟩
  | 4, _ => ⟨0, 1, 300, w0001011111111111001_4⟩
  | 5, _ => ⟨0, 0, 300, w0001011111111111001_5⟩
  | 6, _ => ⟨0, 0, 300, w0001011111111111001_6⟩
  | 7, _ => ⟨0, 0, 300, w0001011111111111001_7⟩
  | 8, _ => ⟨0, 0, 300, w0001011111111111001_8⟩
  | 9, _ => ⟨0, 0, 300, w0001011111111111001_9⟩
  | 10, _ => ⟨0, 0, 300, w0001011111111111001_10⟩
  | 11, _ => ⟨0, 0, 300, w0001011111111111001_11⟩
  | 12, _ => ⟨0, 0, 300, w0001011111111111001_12⟩
  | 13, _ => ⟨0, 0, 300, w0001011111111111001_13⟩
  | 14, _ => ⟨0, 0, 300, w0001011111111111001_14⟩
  | 15, _ => ⟨0, 0, 300, w0001011111111111001_15⟩
  | 16, _ => ⟨0, 1, 300, w0001011111111111001_16⟩
  | 17, _ => ⟨0, 1, 300, w0001011111111111001_17⟩
  | 18, _ => ⟨0, 0, 300, w0001011111111111001_18⟩
  | _ + 19, h => absurd h (by omega)

set_option maxHeartbeats 0 in
theorem w0010011011111111111_0 : phaseCheck (wordOf 19 0b0010011011111111111) 13 0 1 300 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0010011011111111111_1 : phaseCheck (wordOf 19 0b0010011011111111111) 13 0 1 300 1 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0010011011111111111_2 : phaseCheck (wordOf 19 0b0010011011111111111) 13 0 0 300 2 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0010011011111111111_3 : phaseCheck (wordOf 19 0b0010011011111111111) 13 0 1 300 3 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0010011011111111111_4 : phaseCheck (wordOf 19 0b0010011011111111111) 13 0 2 300 4 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0010011011111111111_5 : phaseCheck (wordOf 19 0b0010011011111111111) 13 0 0 300 5 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0010011011111111111_6 : phaseCheck (wordOf 19 0b0010011011111111111) 13 0 0 300 6 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0010011011111111111_7 : phaseCheck (wordOf 19 0b0010011011111111111) 13 0 2 300 7 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0010011011111111111_8 : phaseCheck (wordOf 19 0b0010011011111111111) 13 0 0 300 8 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0010011011111111111_9 : phaseCheck (wordOf 19 0b0010011011111111111) 13 0 0 300 9 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0010011011111111111_10 : phaseCheck (wordOf 19 0b0010011011111111111) 13 0 0 300 10 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0010011011111111111_11 : phaseCheck (wordOf 19 0b0010011011111111111) 13 0 0 300 11 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0010011011111111111_12 : phaseCheck (wordOf 19 0b0010011011111111111) 13 0 0 300 12 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0010011011111111111_13 : phaseCheck (wordOf 19 0b0010011011111111111) 13 0 0 300 13 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0010011011111111111_14 : phaseCheck (wordOf 19 0b0010011011111111111) 13 0 0 300 14 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0010011011111111111_15 : phaseCheck (wordOf 19 0b0010011011111111111) 13 0 0 300 15 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0010011011111111111_16 : phaseCheck (wordOf 19 0b0010011011111111111) 13 0 0 300 16 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0010011011111111111_17 : phaseCheck (wordOf 19 0b0010011011111111111) 13 0 0 300 17 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w0010011011111111111_18 : phaseCheck (wordOf 19 0b0010011011111111111) 13 0 0 300 18 = true := by
  decide +kernel

/-- Every phase of `0010011011111111111` at width 13. -/
theorem w0010011011111111111 : ∀ φ, φ < 19 → ∃ D rounds fuel,
    phaseCheck (wordOf 19 0b0010011011111111111) 13 D rounds fuel φ = true
  | 0, _ => ⟨0, 1, 300, w0010011011111111111_0⟩
  | 1, _ => ⟨0, 1, 300, w0010011011111111111_1⟩
  | 2, _ => ⟨0, 0, 300, w0010011011111111111_2⟩
  | 3, _ => ⟨0, 1, 300, w0010011011111111111_3⟩
  | 4, _ => ⟨0, 2, 300, w0010011011111111111_4⟩
  | 5, _ => ⟨0, 0, 300, w0010011011111111111_5⟩
  | 6, _ => ⟨0, 0, 300, w0010011011111111111_6⟩
  | 7, _ => ⟨0, 2, 300, w0010011011111111111_7⟩
  | 8, _ => ⟨0, 0, 300, w0010011011111111111_8⟩
  | 9, _ => ⟨0, 0, 300, w0010011011111111111_9⟩
  | 10, _ => ⟨0, 0, 300, w0010011011111111111_10⟩
  | 11, _ => ⟨0, 0, 300, w0010011011111111111_11⟩
  | 12, _ => ⟨0, 0, 300, w0010011011111111111_12⟩
  | 13, _ => ⟨0, 0, 300, w0010011011111111111_13⟩
  | 14, _ => ⟨0, 0, 300, w0010011011111111111_14⟩
  | 15, _ => ⟨0, 0, 300, w0010011011111111111_15⟩
  | 16, _ => ⟨0, 0, 300, w0010011011111111111_16⟩
  | 17, _ => ⟨0, 0, 300, w0010011011111111111_17⟩
  | 18, _ => ⟨0, 0, 300, w0010011011111111111_18⟩
  | _ + 19, h => absurd h (by omega)

/-- The blocks of this module, each as its least rotation `wordOf n bits`, with the width of its checks. -/
def blocksPhases19 : List ((Nat × Nat) × Nat) := [
    ((19, 0b0000000000001111111), 14), ((19, 0b0000000000101001111), 13), ((19, 0b0000000000110101111), 14),
    ((19, 0b0000000001001010111), 14), ((19, 0b0000000101001111011), 13), ((19, 0b0000001011011000011), 13),
    ((19, 0b0000100111111111111), 13), ((19, 0b0000101111111001001), 13), ((19, 0b0001011100111111011), 14),
    ((19, 0b0001011111111111001), 13), ((19, 0b0010011011111111111), 13)]

theorem blocksPhases19_phases : ∀ e ∈ blocksPhases19, ∀ φ, φ < e.1.1 → ∃ D rounds fuel,
    phaseCheck (wordOf e.1.1 e.1.2) e.2 D rounds fuel φ = true := by
  intro e he
  simp only [blocksPhases19, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact w0000000000001111111
  · exact w0000000000101001111
  · exact w0000000000110101111
  · exact w0000000001001010111
  · exact w0000000101001111011
  · exact w0000001011011000011
  · exact w0000100111111111111
  · exact w0000101111111001001
  · exact w0001011100111111011
  · exact w0001011111111111001
  · exact w0010011011111111111

theorem blocksPhases19_pos : ∀ e ∈ blocksPhases19, 1 ≤ e.2 ∧ 1 ≤ e.1.1 := by decide

/-- **The center column does not eventually repeat any of the 11 blocks of `blocksPhases19`**, from any time on
and in any rotation. -/
theorem center_not_blocksPhases19 (e : (Nat × Nat) × Nat) (he : e ∈ blocksPhases19) (T shift : Nat)
    (h : ∀ t : Nat, T ≤ t → Rule30Prize.center t = (wordOf e.1.1 e.1.2).getD ((t + shift) % e.1.1) false) :
    False :=
  center_not_phases_list blocksPhases19 blocksPhases19_pos blocksPhases19_phases e he T shift h

/-- The same in the kit's form `Rule30StripCertificates.EventuallyWord`. -/
theorem not_eventually_blocksPhases19 (e : (Nat × Nat) × Nat) (he : e ∈ blocksPhases19) :
    ¬ Rule30StripCertificates.EventuallyWord (wordOf e.1.1 e.1.2) :=
  phases_list_not_eventually blocksPhases19 blocksPhases19_pos blocksPhases19_phases e he

end Rule30Open
