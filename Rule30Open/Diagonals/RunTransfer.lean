module

public import Rule30Open.Diagonals.SettledSlope
public import Rule30Open.Diagonals.DrivenSkeleton

/-!
# A white run of a left diagonal is a run of agreement of the two diagonals before it, and a black run is a white run two diagonals before

Read the left diagonals of a row white left of a cell, or of the single cell, as an array `b i t` with the step
`b (i + 2) (t + 1) = b i t xor (b (i + 1) t || b (i + 2) t)` (`DiagStep` of `DrivenSkeleton`, or `DiagStepFrom` from
a time on). Two consecutive cells of diagonal `i + 2` decide a relation between the two diagonals before it:

* `run_white_white_iff`: if `b (i + 2) t` is white, `b (i + 2) (t + 1)` is white exactly when `b i t = b (i + 1) t`.
* `run_black_black_iff`: if `b (i + 2) t` is black, `b (i + 2) (t + 1)` is black exactly when `b i t` is white.
* `agree_of_white_run`, `white_run_of_agree`: diagonal `i + 2` is white at the `r + 1` times `s .. s + r` exactly
  when it is white at `s` and diagonals `i` and `i + 1` agree at the `r` times `s .. s + r - 1`.
* `white_of_black_run`, `black_run_of_white`: diagonal `i + 2` is black at `s .. s + r` exactly when it is black at
  `s` and diagonal `i` is white at `s .. s + r - 1`.
* `blackWithin_of_disagreeWithin`, `whiteWithin_of_blackWithin`: so if diagonals `i` and `i + 1` differ somewhere in
  every `m` consecutive times from `T` on, diagonal `i + 2` is black somewhere in every `m + 1` consecutive times
  (its white runs are at most the longest agreement run plus one); and if diagonal `i` is black somewhere in every `m`
  consecutive times, diagonal `i + 2` is white somewhere in every `m + 1` (its black runs are at most the longest
  white run two diagonals before, plus one).
* `D_blackWithin_of_disagreeWithin`, `D_whiteWithin_of_blackWithin`: the same for the single cell's diagonals `D`,
  in the form `BlackWithin` that the reset bound `SettledSlope.pair_repeats_of_white_runs` takes.

The lemmas move a run from one diagonal to the two before it without shortening it, so they do not bound the white
runs; `RunTransfer.md` says what they give and where the bound stops.

The natural-language argument is `RunTransfer.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

open Ruliology.CellularAutomata
open Ruliology.CellularAutomata.Rule30Diagonals

/-- Every `m` consecutive times from `T` on contain a time at which `f` and `g` differ: their runs of agreement from
`T` on are shorter than `m`. -/
def DisagreeWithin (f g : Nat → Bool) (T m : Nat) : Prop :=
  ∀ t, T ≤ t → ∃ r, t ≤ r ∧ r < t + m ∧ f r ≠ g r

/-- Every `c` consecutive times from `T` on contain a white cell of `f`: its black runs from `T` on are shorter than
`c`. -/
def WhiteWithin (f : Nat → Bool) (T c : Nat) : Prop :=
  ∀ t, T ≤ t → ∃ r, t ≤ r ∧ r < t + c ∧ f r = false

/-- **Two white cells.** If diagonal `i + 2` is white at `t`, it is white at `t + 1` exactly when diagonals `i` and
`i + 1` agree at `t`. -/
theorem run_white_white_iff {b : Nat → Nat → Bool} {i T t : Nat} (hb : DiagStepFrom b i T) (ht : T ≤ t)
    (hw : b (i + 2) t = false) : b (i + 2) (t + 1) = false ↔ b i t = b (i + 1) t := by
  rw [hb t ht, hw]
  cases b i t <;> cases b (i + 1) t <;> decide

/-- **Two black cells.** If diagonal `i + 2` is black at `t`, it is black at `t + 1` exactly when diagonal `i` is
white at `t`. -/
theorem run_black_black_iff {b : Nat → Nat → Bool} {i T t : Nat} (hb : DiagStepFrom b i T) (ht : T ≤ t)
    (hk : b (i + 2) t = true) : b (i + 2) (t + 1) = true ↔ b i t = false := by
  rw [hb t ht, hk]
  cases b i t <;> cases b (i + 1) t <;> decide

/-- **A white run is a run of agreement.** If diagonal `i + 2` is white at the times `s .. s + r`, diagonals `i` and
`i + 1` agree at the times `s .. s + r - 1`. -/
theorem agree_of_white_run {b : Nat → Nat → Bool} {i T s r : Nat} (hb : DiagStepFrom b i T) (hs : T ≤ s)
    (hw : ∀ k, k ≤ r → b (i + 2) (s + k) = false) : ∀ k, k < r → b i (s + k) = b (i + 1) (s + k) := by
  intro k hk
  have h1 := hw (k + 1) (by omega)
  rw [← Nat.add_assoc] at h1
  exact (run_white_white_iff hb (by omega) (hw k (by omega))).1 h1

/-- **A run of agreement is a white run.** If diagonal `i + 2` is white at `s` and diagonals `i` and `i + 1` agree at
the times `s .. s + r - 1`, diagonal `i + 2` is white at the times `s .. s + r`. -/
theorem white_run_of_agree {b : Nat → Nat → Bool} {i T s r : Nat} (hb : DiagStepFrom b i T) (hs : T ≤ s)
    (h0 : b (i + 2) s = false) (ha : ∀ k, k < r → b i (s + k) = b (i + 1) (s + k)) :
    ∀ k, k ≤ r → b (i + 2) (s + k) = false
  | 0, _ => h0
  | k + 1, hk => by
    have ih := white_run_of_agree hb hs h0 ha k (by omega)
    rw [← Nat.add_assoc]
    exact (run_white_white_iff hb (by omega) ih).2 (ha k (by omega))

/-- **A black run is a white run two diagonals before.** If diagonal `i + 2` is black at the times `s .. s + r`,
diagonal `i` is white at the times `s .. s + r - 1`. -/
theorem white_of_black_run {b : Nat → Nat → Bool} {i T s r : Nat} (hb : DiagStepFrom b i T) (hs : T ≤ s)
    (hk : ∀ k, k ≤ r → b (i + 2) (s + k) = true) : ∀ k, k < r → b i (s + k) = false := by
  intro k hlt
  have h1 := hk (k + 1) (by omega)
  rw [← Nat.add_assoc] at h1
  exact (run_black_black_iff hb (by omega) (hk k (by omega))).1 h1

/-- **The converse.** If diagonal `i + 2` is black at `s` and diagonal `i` is white at the times `s .. s + r - 1`,
diagonal `i + 2` is black at the times `s .. s + r`. -/
theorem black_run_of_white {b : Nat → Nat → Bool} {i T s r : Nat} (hb : DiagStepFrom b i T) (hs : T ≤ s)
    (h0 : b (i + 2) s = true) (hw : ∀ k, k < r → b i (s + k) = false) :
    ∀ k, k ≤ r → b (i + 2) (s + k) = true
  | 0, _ => h0
  | k + 1, hk => by
    have ih := black_run_of_white hb hs h0 hw k (by omega)
    rw [← Nat.add_assoc]
    exact (run_black_black_iff hb (by omega) ih).2 (hw k (by omega))

/-- **White runs are at most the agreement runs plus one.** If diagonals `i` and `i + 1` differ somewhere in every `m`
consecutive times from `T` on, diagonal `i + 2` is black somewhere in every `m + 1` consecutive times from `T` on. -/
theorem blackWithin_of_disagreeWithin {b : Nat → Nat → Bool} {i T m : Nat} (hb : DiagStepFrom b i T)
    (hd : DisagreeWithin (b i) (b (i + 1)) T m) : BlackWithin (b (i + 2)) T (m + 1) := by
  intro t ht
  obtain ⟨r, hr1, hr2, hne⟩ := hd t ht
  cases h0 : b (i + 2) r with
  | true => exact ⟨r, hr1, by omega, h0⟩
  | false =>
    cases h1 : b (i + 2) (r + 1) with
    | true => exact ⟨r + 1, by omega, by omega, h1⟩
    | false => exact absurd ((run_white_white_iff hb (by omega) h0).1 h1) hne

/-- **Black runs are at most the white runs two diagonals before, plus one.** If diagonal `i` is black somewhere in
every `m` consecutive times from `T` on, diagonal `i + 2` is white somewhere in every `m + 1` consecutive times from
`T` on. -/
theorem whiteWithin_of_blackWithin {b : Nat → Nat → Bool} {i T m : Nat} (hb : DiagStepFrom b i T)
    (hd : BlackWithin (b i) T m) : WhiteWithin (b (i + 2)) T (m + 1) := by
  intro t ht
  obtain ⟨r, hr1, hr2, hk⟩ := hd t ht
  cases h0 : b (i + 2) r with
  | false => exact ⟨r, hr1, by omega, h0⟩
  | true =>
    cases h1 : b (i + 2) (r + 1) with
    | false => exact ⟨r + 1, by omega, by omega, h1⟩
    | true =>
      have := (run_black_black_iff hb (by omega) h0).1 h1
      rw [hk] at this
      exact absurd this (by decide)

/-- The single cell's diagonals obey the step at every time. -/
theorem D_diagStep : DiagStep D := fun i t => D_step i t

/-- **The single cell's white runs.** If `D j` and `D (j + 1)` differ somewhere in every `m` consecutive times from
`T` on, `D (j + 2)` has a black cell in every `m + 1` consecutive times from `T` on: the cost `c (j + 2)` of the reset
bound `pair_repeats_of_white_runs` can be taken to be `m + 1`. -/
theorem D_blackWithin_of_disagreeWithin {j T m : Nat} (hd : DisagreeWithin (D j) (D (j + 1)) T m) :
    BlackWithin (D (j + 2)) T (m + 1) :=
  blackWithin_of_disagreeWithin (b := D) (D_diagStep.from j T) hd

/-- **The single cell's black runs.** If `D j` has a black cell in every `m` consecutive times from `T` on,
`D (j + 2)` has a white cell in every `m + 1` consecutive times from `T` on. -/
theorem D_whiteWithin_of_blackWithin {j T m : Nat} (hd : BlackWithin (D j) T m) :
    WhiteWithin (D (j + 2)) T (m + 1) :=
  whiteWithin_of_blackWithin (b := D) (D_diagStep.from j T) hd

end Rule30Open
