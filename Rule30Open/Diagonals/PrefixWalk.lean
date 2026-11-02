module

public import Ruliology.CellularAutomata.Rule30FiniteDiagonals
public import Rule30Open.Diagonals.DrivenSkeleton

/-!
# Behind a walk, the left diagonals forget the cells of the row past a prefix

Take two rows `x` and `x'`, both white left of a cell `lo`, and read their left diagonals
`Ld x lo k t = evol x t (lo - t + k)` (the kit's `Rule30FiniteDiagonals.Ld`). Diagonal `k` depends only on the cells
`lo, ..., lo + k`, and diagonal `k + 2` is fed by the two before it:
`Ld (k + 2) (t + 1) = Ld k t xor (Ld (k + 1) t || Ld (k + 2) t)` (`DiagStep` and `Ld_diagStep` of
`DrivenSkeleton`, from the kit's `Rule30FiniteDiagonals.Ld_step`).

* `forget_of_black`, `agree_or_flip_of_white`: the shift `0` cases of `DrivenSkeleton.shift_of_black` and
  `DrivenSkeleton.shift_or_flip_of_white`. If two arrays with the step agree on diagonals `k` and `k + 1` from time
  `s` on, and diagonal `k + 1` is black at a time `r ≥ s`, they agree on diagonal `k + 2` from time `r + 1` on;
  where diagonal `k + 1` is white from `s` on, diagonal `k + 2` of one is that of the other or its complement.
* `agree_of_walk`: so if they agree on the diagonals `m` and `m + 1` at all times, and `w` is a walk from depth
  `m + 1` (`PrefixWalk`: diagonal `k` has a black cell at a time `r` with `w k ≤ r < w (k + 1)`, for `m < k < d`),
  they agree on every diagonal `k ≤ d` from time `w k` on.
* `Ld_agree_of_prefix`, `Ld_agree_of_walk`, `Ld_repeats_of_walk`: for rows, agreeing on the cells
  `lo, ..., lo + m + 1` is agreeing on the diagonals `0, ..., m + 1` at all times. So along a walk on the diagonals of
  `x'` from depth `m + 1`, **every** row `x` with the same cells `lo, ..., lo + m + 1` has the diagonal `d` of `x'`
  from time `w d` on, and if that diagonal of `x'` repeats with period `P` from `T`, the diagonal `d` of `x` repeats
  with period `P` from `max (w d) T`. The bound holds for all `d` and every choice of the cells past the prefix.

This is the pruning rule of the branch and bound `computations/seed_onsets_prune.c`, which finds the latest onset of
each left diagonal over all rows white left of a black cell (`findings/diagonals/seed-uniform-onsets.md`): a prefix
whose walk bound is at most the latest onset found at every depth is not extended. The walk advances about two times
per depth, so as an induction over depths this gives slope 2, the front walk of the single cell.

The natural-language argument is `PrefixWalk.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

open Ruliology.CellularAutomata Ruliology.CellularAutomata.Rule30FiniteDiagonals Ruliology.CellularAutomata.Rule30Realization

/-- A walk from depth `m + 1` to depth `d` along the diagonals of `b`: for `m < k < d`, diagonal `k` is black at
some time `r` with `w k ≤ r < w (k + 1)`. -/
def PrefixWalk (b : Nat → Nat → Bool) (w : Nat → Nat) (m d : Nat) : Prop :=
  ∀ k, m + 1 ≤ k → k < d → ∃ r, w k ≤ r ∧ r < w (k + 1) ∧ b k r = true

/-- **Behind a black cell, the next diagonal forgets.** Two arrays with the step that agree on diagonals `k` and
`k + 1` from time `s` on, with diagonal `k + 1` black at `r ≥ s`, agree on diagonal `k + 2` from time `r + 1` on.
This is `DrivenSkeleton.shift_of_black` with the shift `0`. -/
theorem forget_of_black {b b' : Nat → Nat → Bool} (hb : DiagStep b) (hb' : DiagStep b') {k s r : Nat}
    (h0 : ∀ t, s ≤ t → b k t = b' k t) (h1 : ∀ t, s ≤ t → b (k + 1) t = b' (k + 1) t) (hr : s ≤ r)
    (hblack : b (k + 1) r = true) : ∀ t, r + 1 ≤ t → b (k + 2) t = b' (k + 2) t :=
  shift_of_black (h := 0) (hb.from k s) hb' h0 h1 hr hblack

/-- **Agreement along a walk.** Two arrays with the step that agree on the diagonals `m` and `m + 1` at all times
agree on every diagonal `k` with `m + 1 ≤ k ≤ d` from time `w k` on, for a walk `w` along the first array. -/
theorem agree_of_walk {b b' : Nat → Nat → Bool} (hb : DiagStep b) (hb' : DiagStep b') {w : Nat → Nat} {m d : Nat}
    (h0 : ∀ t, b m t = b' m t) (h1 : ∀ t, b (m + 1) t = b' (m + 1) t) (hw : PrefixWalk b w m d) :
    ∀ k, m + 1 ≤ k → k ≤ d → ∀ t, w k ≤ t → b k t = b' k t := by
  have pair : ∀ n, m + 1 + n ≤ d →
      (∀ t, w (m + 1 + n) ≤ t → b (m + n) t = b' (m + n) t) ∧
        (∀ t, w (m + 1 + n) ≤ t → b (m + 1 + n) t = b' (m + 1 + n) t) := by
    intro n
    induction n with
    | zero => exact fun _ => ⟨fun t _ => by simpa using h0 t, fun t _ => by simpa using h1 t⟩
    | succ n ih =>
      intro hn
      obtain ⟨ih0, ih1⟩ := ih (by omega)
      obtain ⟨r, hr0, hr1, hr⟩ := hw (m + 1 + n) (by omega) (by omega)
      have e : m + n + 1 = m + 1 + n := by omega
      have hnext := forget_of_black hb hb' (k := m + n) (s := w (m + 1 + n)) (r := r) ih0
        (fun t ht => by rw [e]; exact ih1 t ht) hr0 (by rw [e]; exact hr)
      refine ⟨fun t ht => ?_, fun t ht => ?_⟩
      · rw [show m + (n + 1) = m + 1 + n by omega]
        exact ih1 t (by rw [show m + 1 + (n + 1) = m + 1 + n + 1 by omega] at ht; omega)
      · rw [show m + 1 + (n + 1) = m + n + 2 by omega] at ht ⊢
        exact hnext t (by rw [show m + n + 2 = m + 1 + n + 1 by omega] at ht; omega)
  intro k hk hkd t ht
  have := (pair (k - (m + 1)) (by omega)).2 t (by rwa [show m + 1 + (k - (m + 1)) = k by omega])
  rwa [show m + 1 + (k - (m + 1)) = k by omega] at this

/-- **A white diagonal passes on one bit.** If two arrays with the step agree on diagonal `k` from time `s` on and
are both white on diagonal `k + 1` from `s` on, then from `s` on diagonal `k + 2` of one is that of the other or its
complement. This is `DrivenSkeleton.shift_or_flip_of_white` with the shift `0`. -/
theorem agree_or_flip_of_white {b b' : Nat → Nat → Bool} (hb : DiagStep b) (hb' : DiagStep b') {k s : Nat}
    (h0 : ∀ t, s ≤ t → b k t = b' k t) (hw : ∀ t, s ≤ t → b (k + 1) t = false)
    (hw' : ∀ t, s ≤ t → b' (k + 1) t = false) :
    (∀ t, s ≤ t → b (k + 2) t = b' (k + 2) t) ∨ (∀ t, s ≤ t → b (k + 2) t = !b' (k + 2) t) :=
  shift_or_flip_of_white (h := 0) (hb.from k s) hb' h0 (fun t ht => (hw t ht).trans (hw' t ht).symm) hw

/-- Agreement from `w` on carries a period of the second sequence to the first, from `max w T`. -/
theorem repeats_of_agree {f g : Nat → Bool} {w T P : Nat} (hfg : ∀ t, w ≤ t → f t = g t)
    (hg : ∀ t, T ≤ t → g (t + P) = g t) : ∀ t, max w T ≤ t → f (t + P) = f t := by
  intro t ht
  rw [hfg (t + P) (by omega), hfg t (by omega), hg t (by omega)]

/-! ### Rows white left of a cell -/

/-- Diagonal `k` starts at the cell `lo + k`. -/
theorem Ld_zero_time (x : Int → Bool) (lo : Int) (k : Nat) : Ld x lo k 0 = x (lo + k) := by
  show evol x 0 (lo - ((0 : Nat) : Int) + (k : Int)) = x (lo + k)
  rw [evol_congr (p := lo - ((0 : Nat) : Int) + (k : Int)) (q := lo + k) (by omega)]
  rfl

/-- **The diagonals see only their cells.** Two rows white left of `lo` that agree on the cells `lo, ..., lo + n`
agree on the diagonals `0, ..., n` at all times. -/
theorem Ld_agree_of_prefix {x x' : Int → Bool} {lo : Int} (hx : ∀ p, p < lo → x p = false)
    (hx' : ∀ p, p < lo → x' p = false) {n : Nat} (hagree : ∀ i : Nat, i ≤ n → x (lo + i) = x' (lo + i)) :
    ∀ k, k ≤ n → ∀ t, Ld x lo k t = Ld x' lo k t := by
  have d0 : 0 ≤ n → ∀ t, Ld x lo 0 t = Ld x' lo 0 t := by
    intro h0 t
    induction t with
    | zero => rw [Ld_zero_time, Ld_zero_time]; exact hagree _ h0
    | succ t iht => rw [Ld_zero_succ hx, Ld_zero_succ hx', iht]
  have pair : ∀ k, k + 1 ≤ n →
      (∀ t, Ld x lo k t = Ld x' lo k t) ∧ (∀ t, Ld x lo (k + 1) t = Ld x' lo (k + 1) t) := by
    intro k
    induction k with
    | zero =>
      intro h1
      have a0 := d0 (by omega)
      refine ⟨a0, fun t => ?_⟩
      induction t with
      | zero => rw [Ld_zero_time, Ld_zero_time]; exact hagree _ h1
      | succ t iht => rw [Ld_one_succ hx, Ld_one_succ hx', iht, a0 t]
    | succ k ih =>
      intro hk
      obtain ⟨a, b⟩ := ih (by omega)
      refine ⟨b, fun t => ?_⟩
      induction t with
      | zero => rw [Ld_zero_time, Ld_zero_time]; exact hagree _ hk
      | succ t iht =>
        show Ld x lo (k + 2) (t + 1) = Ld x' lo (k + 2) (t + 1)
        rw [Ld_step, Ld_step, a t, b t, show k + 2 = k + 1 + 1 from rfl, iht]
  intro k hk t
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · exact d0 hk t
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    exact (pair j hk).2 t

/-- **Behind a walk, a row forgets its cells past the prefix.** Let `x` and `x'` be white left of `lo` and agree on
the cells `lo, ..., lo + m + 1`, and let `w` be a walk from depth `m + 1` to `d` along the diagonals of `x'`. Then
every diagonal `k` of `x` with `m + 1 ≤ k ≤ d` equals that of `x'` from time `w k` on. -/
theorem Ld_agree_of_walk {x x' : Int → Bool} {lo : Int} (hx : ∀ p, p < lo → x p = false)
    (hx' : ∀ p, p < lo → x' p = false) {m d : Nat} {w : Nat → Nat}
    (hagree : ∀ i : Nat, i ≤ m + 1 → x (lo + i) = x' (lo + i)) (hw : PrefixWalk (Ld x' lo) w m d) :
    ∀ k, m + 1 ≤ k → k ≤ d → ∀ t, w k ≤ t → Ld x lo k t = Ld x' lo k t := by
  have hp := Ld_agree_of_prefix hx hx' hagree
  intro k hk hkd t ht
  exact (agree_of_walk (Ld_diagStep x' lo) (Ld_diagStep x lo) (fun t => (hp m (by omega) t).symm)
    (fun t => (hp (m + 1) (by omega) t).symm) hw k hk hkd t ht).symm

/-- **The walk bound on onsets.** With `x`, `x'` and `w` as in `Ld_agree_of_walk`, if diagonal `d` of `x'` repeats
with period `P` from time `T`, then diagonal `d` of `x` repeats with period `P` from time `max (w d) T`, whatever the
cells of `x` right of `lo + m + 1`. -/
theorem Ld_repeats_of_walk {x x' : Int → Bool} {lo : Int} (hx : ∀ p, p < lo → x p = false)
    (hx' : ∀ p, p < lo → x' p = false) {m d T P : Nat} {w : Nat → Nat} (hmd : m + 1 ≤ d)
    (hagree : ∀ i : Nat, i ≤ m + 1 → x (lo + i) = x' (lo + i)) (hw : PrefixWalk (Ld x' lo) w m d)
    (hP : ∀ t, T ≤ t → Ld x' lo d (t + P) = Ld x' lo d t) :
    ∀ t, max (w d) T ≤ t → Ld x lo d (t + P) = Ld x lo d t :=
  repeats_of_agree (Ld_agree_of_walk hx hx' hagree hw d hmd (Nat.le_refl d)) hP

end Rule30Open
