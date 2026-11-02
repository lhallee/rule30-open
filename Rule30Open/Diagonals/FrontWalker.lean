module

public import Rule30Open.Diagonals.SettledSlope

/-!
# A walk through the settled left diagonals bounds when they settle, and black center runs with it

Read the single seed's pattern along the left diagonals, `D j t = cell t (j - t)`. The reset bound of
`SettledSlope` (`pair_repeats_of_white_runs`) charges each diagonal `i` the longest white run of its periodic part.
The diagonal after it forgets its past at the first black cell of diagonal `i` after the earlier onsets, so the charge
that matters is the white run the walk actually meets, not the longest one.

* `FrontWalk w J`: `w 1 ≥ 1`, and for `1 ≤ i ≤ J` diagonal `i` has a black cell at some time in
  `[w i, w (i + 1))`, or is eventually white and `w i ≤ w (i + 1)`. The least such `w` is the walk that starts at
  time 1 on diagonal 1 and, on diagonal `i` from time `w i`, slides to its first black cell `r` and steps to
  `w (i + 1) = r + 1`; on the space-time diagram it moves straight down from a black cell and down-left from a white
  one.
* `pair_repeats_of_walk`: along a front walk, the pair `(D j, D (j + 1))` repeats with a common period from time
  `w (j + 1)` on, for every `j ≤ J`.
* `black_run_le_of_walk`: if `w (j + 1) ≤ 2 j + δ` for `j ≤ J` and the antiphase alternations of every pair `j ≤ J`
  are eventually bounded by `A`, a black run of the center column from time `a ≥ 1` with `⌊4a/9⌋ ≤ J` has
  `9 L ≤ 3 a + 60 A + 60 δ + 200`. The slope is `1/3`.
* `black_run_le_of_steep_walk`: the same with `w (j + 1) ≤ ⌈41 j / 20⌉ + δ` and `⌊16a/37⌋ ≤ J` gives
  `185 L ≤ 63 a + 1200 A + 1200 δ + 4000`, the slope `63/185`.

None of the hypotheses on `w` and `A` is proved for all depths. They are checked on a finite table
(`computations/front_walker.py`); see `FrontWalker.md`.

The natural-language argument is `FrontWalker.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

open Ruliology.CellularAutomata
open Ruliology.CellularAutomata.Rule30Diagonals
open Ruliology.CellularAutomata.Rule30CenterRuns
open Rule30Jen Rule30Prize

/-- `w` is a front walk to depth `J`: it starts at a time `w 1 ≥ 1`, and from time `w i` diagonal `i` has a black
cell before `w (i + 1)`, or is eventually white and the walk does not go back in time. -/
def FrontWalk (w : Nat → Nat) (J : Nat) : Prop :=
  1 ≤ w 1 ∧ ∀ i, 1 ≤ i → i ≤ J →
    (EventuallyWhite (D i) ∧ w i ≤ w (i + 1)) ∨ ∃ r, w i ≤ r ∧ r < w (i + 1) ∧ D i r = true

/-- **The walk bounds the settling.** Along a front walk to depth `J`, the pair `(D j, D (j + 1))` repeats with a
common period from time `w (j + 1)` on, for every `j ≤ J`. -/
theorem pair_repeats_of_walk (w : Nat → Nat) (J : Nat) (hw : FrontWalk w J) :
    ∀ j, j ≤ J → ∃ P, 0 < P ∧ RepeatsFrom (D j) (w (j + 1)) P ∧ RepeatsFrom (D (j + 1)) (w (j + 1)) P
  | 0, _ => ⟨1, Nat.one_pos, fun t _ => by rw [D_zero, D_zero], fun t ht => by
      have h1 : 1 ≤ t := Nat.le_trans hw.1 ht
      obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
      rw [D_one, D_one]⟩
  | j + 1, hj => by
    obtain ⟨P, hP, h0, h1⟩ := pair_repeats_of_walk w J hw j (by omega)
    rcases hw.2 (j + 1) (by omega) (by omega) with ⟨hwh, hle⟩ | ⟨r, hr1, hr2, hr⟩
    · obtain ⟨s1, s2⟩ := pair_step_white h0 (white_of_repeats hP h1 hwh)
      exact ⟨2 * P, by omega, s1.mono hle, s2.mono hle⟩
    · exact ⟨P, hP, h1.mono (by omega),
        fun t ht => D_periodic_of_black j (w (j + 1)) P r h0 h1 hr1 hr t (by omega)⟩

/-- **Black runs from a walk of slope 2.** If `w` is a front walk to depth `J` with `w (j + 1) ≤ 2 j + δ` for
`j ≤ J`, and the antiphase alternations of every pair `j ≤ J` are eventually bounded by `A`, then a black run of the
center column from time `a ≥ 1` with `⌊4a/9⌋ ≤ J` has `9 L ≤ 3 a + 60 A + 60 δ + 200`. -/
theorem black_run_le_of_walk (w : Nat → Nat) (J δ A : Nat) (hw : FrontWalk w J)
    (hS : ∀ j, j ≤ J → w (j + 1) ≤ 2 * j + δ)
    (hA : ∀ j, j ≤ J → ∃ T, AltBound j T A)
    (a L : Nat) (ha : 1 ≤ a) (hJ : 4 * a / 9 ≤ J) (h : ∀ i, i < L → center (a + i) = true) :
    9 * L ≤ 3 * a + 60 * A + 60 * δ + 200 := by
  refine Classical.byContradiction fun hcon => ?_
  have hLa : L ≤ a := black_run_le a L ha h
  obtain ⟨j, hj⟩ : ∃ j, j = 4 * a / 9 := ⟨_, rfl⟩
  obtain ⟨s0, hs0⟩ : ∃ s0, s0 = (a + 2 - j - L) / 2 := ⟨_, rfl⟩
  obtain ⟨P, hP, h0, h1⟩ := pair_repeats_of_walk w J hw j (by omega)
  obtain ⟨T', hB⟩ := hA j (by omega)
  have hSj := hS j (by omega)
  exact black_run_window a L j s0 A (w (j + 1)) h (by omega) (by omega) (by omega)
    (altBound_of_repeats hP h0 h1 hB)

/-- The same for a walk of slope `41/20`: `w (j + 1) ≤ ⌈41 j / 20⌉ + δ` and `⌊16a/37⌋ ≤ J` give
`185 L ≤ 63 a + 1200 A + 1200 δ + 4000`. The slope is `63/185`. -/
theorem black_run_le_of_steep_walk (w : Nat → Nat) (J δ A : Nat) (hw : FrontWalk w J)
    (hS : ∀ j, j ≤ J → w (j + 1) ≤ (41 * j + 19) / 20 + δ)
    (hA : ∀ j, j ≤ J → ∃ T, AltBound j T A)
    (a L : Nat) (ha : 1 ≤ a) (hJ : 16 * a / 37 ≤ J) (h : ∀ i, i < L → center (a + i) = true) :
    185 * L ≤ 63 * a + 1200 * A + 1200 * δ + 4000 := by
  refine Classical.byContradiction fun hcon => ?_
  have hLa : L ≤ a := black_run_le a L ha h
  obtain ⟨j, hj⟩ : ∃ j, j = 16 * a / 37 := ⟨_, rfl⟩
  obtain ⟨s0, hs0⟩ : ∃ s0, s0 = (a + 2 - j - L) / 2 := ⟨_, rfl⟩
  obtain ⟨P, hP, h0, h1⟩ := pair_repeats_of_walk w J hw j (by omega)
  obtain ⟨T', hB⟩ := hA j (by omega)
  have hSj := hS j (by omega)
  exact black_run_window a L j s0 A (w (j + 1)) h (by omega) (by omega) (by omega)
    (altBound_of_repeats hP h0 h1 hB)

end Rule30Open
