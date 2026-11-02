module

public import Ruliology.CellularAutomata.Rule30FiniteDiagonals
public import Ruliology.CellularAutomata.Rule30FiniteConfigs
public import Rule30Open.Diagonals.DrivenSkeleton
public import Rule30Open.Diagonals.PrefixWalk

/-!
# Behind a white diagonal both classes of the next diagonal are realized: the skeletons form a tree

Read a row `x` that is white left of a cell `lo` along its left diagonals, `Ld x lo i t = evol x t (lo - t + i)`
(the kit's `Rule30FiniteDiagonals.Ld`). `DrivenSkeleton.skeleton_step` says that behind a diagonal `w` that is white
from some time on, diagonal `w + 1` of any second such row is, up to a time shift, either the first row's diagonal
or its complement. This module shows that the complement is always realized.

* `flip_white_complements`: if diagonal `w` of `x` is white at every time, flipping the cell `lo + w + 1` keeps the
  row white left of `lo`, keeps the diagonals `0, …, w`, and complements diagonal `w + 1` at every time. Diagonal
  `i` sees only the cells `lo, …, lo + i` (`PrefixWalk.Ld_agree_of_prefix`), and behind a white diagonal the step
  is `D (w + 1) (t + 1) = D (w - 1) t xor D (w + 1) t`, which carries the flip forever.
* `Ld_reanchor`: the row at time `s`, read from the cell `lo - s`, has the diagonals of `x` read `s` steps later.
* `branch_realized`: so if diagonal `w` of a row white left of a black cell is white from time `s` on, some row
  white left of a black cell has the diagonals `0, …, w` of `x` read `s` steps later and diagonal `w + 1`
  complemented. `branch_not_shift`: when no time shift carries that diagonal of `x` to its complement, the new
  diagonal `w + 1` is not a time shift of the old one, so the two rows settle to different classes.
* `IsFrontStep`, `walk_phase_transfer`, `shifted_walk_close`: the step of the least front walk of `FrontWalker`
  (from `t`, one past the first black cell at or after `t`, or `t` if there is none) is monotone and, on diagonals
  that repeat with period `P` from `T`, commutes with adding `P`. So two front walks along the same diagonals that
  start within `P` of each other stay within `P` at every depth, and a walk along diagonals that are another row's
  read `h` steps later is, shifted by `h`, a walk along the other row's.

With `DrivenSkeleton`, the eventual skeletons of the rows white left of a black cell form a binary tree: at each
eventually white diagonal whose predecessor has even weight per period, both classes of the next diagonal occur.

The natural-language argument is `SkeletonTree.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

open Ruliology.CellularAutomata Ruliology.CellularAutomata.Rule30FiniteDiagonals Ruliology.CellularAutomata.Rule30Realization

/-- The row `x` with the cell `q` flipped. -/
def flipCell (x : Int → Bool) (q : Int) : Int → Bool := fun p => if p = q then !x p else x p

/-- Flipping a cell at or right of `lo` keeps a row white left of `lo`. -/
theorem flipAt_white_left {x : Int → Bool} {lo q : Int} (hx : ∀ p, p < lo → x p = false) (hq : lo ≤ q) :
    ∀ p, p < lo → flipCell x q p = false := by
  intro p hp
  unfold flipCell
  rw [ite_eq_right (by omega)]
  exact hx p hp

/-- **The flip behind a white diagonal.** If diagonal `w` of a row white left of `lo` is white at every time,
flipping the cell `lo + w + 1` keeps the row white left of `lo`, keeps the diagonals `0, …, w` and complements
diagonal `w + 1` at every time. -/
theorem flip_white_complements {x : Int → Bool} {lo : Int} (hx : ∀ p, p < lo → x p = false) {w : Nat}
    (hw : ∀ t, Ld x lo w t = false) :
    (∀ p, p < lo → flipCell x (lo + ((w + 1 : Nat) : Int)) p = false) ∧
      (∀ i, i ≤ w → ∀ t, Ld (flipCell x (lo + ((w + 1 : Nat) : Int))) lo i t = Ld x lo i t) ∧
      (∀ t, Ld (flipCell x (lo + ((w + 1 : Nat) : Int))) lo (w + 1) t = !Ld x lo (w + 1) t) := by
  have hy := flipAt_white_left (x := x) (q := lo + ((w + 1 : Nat) : Int)) hx (by omega)
  have hagree : ∀ i, i ≤ w → ∀ t, Ld (flipCell x (lo + ((w + 1 : Nat) : Int))) lo i t = Ld x lo i t :=
    Ld_agree_of_prefix hy hx (n := w) (fun i hi => by
      show (if lo + (i : Int) = lo + ((w + 1 : Nat) : Int) then _ else _) = _
      rw [ite_eq_right (by omega)])
  refine ⟨hy, hagree, fun t => ?_⟩
  induction t with
  | zero =>
    rw [Ld_zero_time, Ld_zero_time]
    show (if lo + ((w + 1 : Nat) : Int) = lo + ((w + 1 : Nat) : Int) then _ else _) = _
    rw [ite_eq_left rfl]
  | succ t ih =>
    cases w with
    | zero =>
      rw [Ld_one_succ hy, Ld_one_succ hx, hagree 0 (Nat.le_refl 0) t, hw t, ih]
      simp
    | succ k =>
      show Ld _ lo (k + 2) (t + 1) = !Ld x lo (k + 2) (t + 1)
      rw [Ld_step, Ld_step, hagree k (by omega) t, hagree (k + 1) (Nat.le_refl _) t, hw t]
      have ih' : Ld (flipCell x (lo + ((k + 1 + 1 : Nat) : Int))) lo (k + 2) t = !Ld x lo (k + 2) t := ih
      rw [ih']
      generalize Ld x lo k t = p
      generalize Ld x lo (k + 2) t = q
      cases p <;> cases q <;> rfl

/-- Evolving the row at time `s` for `t` steps is evolving `x` for `s + t` steps. -/
theorem evol_evol (x : Int → Bool) (s t : Nat) : evol (evol x s) t = evol x (s + t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    funext p
    show Rule30Jen.rule (evol (evol x s) t (p - 1)) (evol (evol x s) t p) (evol (evol x s) t (p + 1)) =
      Rule30Jen.rule (evol x (s + t) (p - 1)) (evol x (s + t) p) (evol x (s + t) (p + 1))
    rw [ih]

/-- **Re-anchoring.** The row at time `s`, read from the cell `lo - s`, has the diagonals of `x` read `s` steps
later. -/
theorem Ld_reanchor (x : Int → Bool) (lo : Int) (s i t : Nat) :
    Ld (evol x s) (lo - s) i t = Ld x lo i (s + t) := by
  show evol (evol x s) t (lo - s - t + i) = evol x (s + t) (lo - ((s + t : Nat) : Int) + i)
  rw [evol_evol]
  exact evol_congr (by omega)

/-- The row at time `s` of a row white left of `lo` is white left of `lo - s`. -/
theorem evol_white_left {x : Int → Bool} {lo : Int} (hx : ∀ p, p < lo → x p = false) (s : Nat) :
    ∀ p, p < lo - s → evol x s p = false :=
  fun p hp => Rule30FiniteConfigs.evol_eq_false_of_lt hx s p hp

/-- **Both classes are realized.** If diagonal `w` of a row white left of a black cell `lo` is white from time `s`
on, some row white left of a black cell `lo'` has the diagonals `0, …, w` of `x` read `s` steps later and the
complement of diagonal `w + 1` of `x` read `s` steps later. -/
theorem branch_realized {x : Int → Bool} {lo : Int} (hx : ∀ p, p < lo → x p = false) (hblack : x lo = true)
    {w s : Nat} (hw : ∀ t, s ≤ t → Ld x lo w t = false) :
    ∃ (y : Int → Bool) (lo' : Int), (∀ p, p < lo' → y p = false) ∧ y lo' = true ∧
      (∀ i, i ≤ w → ∀ t, Ld y lo' i t = Ld x lo i (t + s)) ∧
      (∀ t, Ld y lo' (w + 1) t = !Ld x lo (w + 1) (t + s)) := by
  have hz := evol_white_left hx s
  have hwz : ∀ t, Ld (evol x s) (lo - s) w t = false := fun t => by
    rw [Ld_reanchor]; exact hw _ (by omega)
  obtain ⟨hy, hlow, hflip⟩ := flip_white_complements hz hwz
  refine ⟨_, lo - s, hy, ?_, fun i hi t => ?_, fun t => ?_⟩
  · have h0 : Ld x lo 0 s = true := by
      have hb : Ld x lo 0 0 = true := by rw [Ld_zero_time]; simpa using hblack
      rcases Nat.eq_zero_or_pos s with rfl | hs
      · exact hb
      · exact (base_pair hx hb s hs).1
    show (if lo - s = lo - s + ((w + 1 : Nat) : Int) then _ else _) = true
    rw [ite_eq_right (by omega)]
    have e : Ld (evol x s) (lo - s) 0 0 = Ld x lo 0 s := by rw [Ld_reanchor, Nat.add_zero]
    rw [Ld_zero_time] at e
    simpa using e.trans h0
  · rw [hlow i hi t, Ld_reanchor, Nat.add_comm s t]
  · rw [hflip t, Ld_reanchor, Nat.add_comm s t]

/-- **The new branch is not a time shift of the old.** If diagonal `w + 1` of the realized row is the complement of
that of `x` read `s` steps later, and no time shift carries diagonal `w + 1` of `x` to its complement from any
time on, then diagonal `w + 1` of the realized row is not diagonal `w + 1` of `x` read with any time shift from any
time on. -/
theorem branch_not_shift {f g : Nat → Bool} {s : Nat} (hg : ∀ t, g t = !f (t + s))
    (hnc : ∀ d U, ∃ u, U ≤ u ∧ f (u + d) = f u) (T h : Nat) : ¬ ∀ t, T ≤ t → g t = f (t + h) := by
  intro hs
  have key : ∀ t, T ≤ t → f (t + h) = !f (t + s) := fun t ht => (hs t ht).symm.trans (hg t)
  by_cases hhs : s ≤ h
  · obtain ⟨u, hu, hfu⟩ := hnc (h - s) (T + s)
    have := key (u - s) (by omega)
    rw [show u - s + h = u + (h - s) by omega, show u - s + s = u by omega, hfu] at this
    cases e : f u <;> simp [e] at this
  · obtain ⟨u, hu, hfu⟩ := hnc (s - h) (T + h)
    have := key (u - h) (by omega)
    rw [show u - h + h = u by omega, show u - h + s = u + (s - h) by omega, hfu] at this
    cases e : f u <;> simp [e] at this

/-! ### The front walk does not depend on its phase -/

/-- One step of the least front walk along `f` from `t`: to one past the first black cell `r ≥ t`, or stay at `t`
if `f` is white from `t` on. -/
def IsFrontStep (f : Nat → Bool) (t t' : Nat) : Prop :=
  (∃ r, t ≤ r ∧ f r = true ∧ (∀ q, t ≤ q → q < r → f q = false) ∧ t' = r + 1) ∨
    ((∀ q, t ≤ q → f q = false) ∧ t' = t)

theorem IsFrontStep.le {f : Nat → Bool} {t t' : Nat} (h : IsFrontStep f t t') : t ≤ t' := by
  rcases h with ⟨r, hr, -, -, rfl⟩ | ⟨-, rfl⟩ <;> omega

/-- The step is monotone. -/
theorem IsFrontStep.mono {f : Nat → Bool} {a a' b b' : Nat} (ha : IsFrontStep f a a') (hb : IsFrontStep f b b')
    (hab : a ≤ b) : a' ≤ b' := by
  rcases ha with ⟨r, hr, hfr, hmin, ea⟩ | ⟨hwa, ea⟩
  · rcases hb with ⟨r', hr', hfr', -, eb⟩ | ⟨hwb, eb⟩
    · by_cases hrr : r ≤ r'
      · omega
      · have := hmin r' (by omega) (by omega)
        rw [hfr'] at this
        exact absurd this (by decide)
    · by_cases hrb : b ≤ r
      · have := hwb r hrb
        rw [hfr] at this
        exact absurd this (by decide)
      · omega
  · rcases hb with ⟨r', hr', hfr', -, eb⟩ | ⟨-, eb⟩
    · have := hwa r' (by omega)
      rw [hfr'] at this
      exact absurd this (by decide)
    · omega

/-- On a sequence that repeats with period `P` from `T`, the step commutes with adding `P`. -/
theorem IsFrontStep.add_period {f : Nat → Bool} {T P t t' : Nat} (hper : ∀ q, T ≤ q → f (q + P) = f q)
    (hT : T ≤ t) (h : IsFrontStep f t t') : IsFrontStep f (t + P) (t' + P) := by
  rcases h with ⟨r, hr, hfr, hmin, rfl⟩ | ⟨hw, rfl⟩
  · refine Or.inl ⟨r + P, by omega, by rw [hper r (by omega)]; exact hfr, fun q hq1 hq2 => ?_, by omega⟩
    rw [show q = (q - P) + P by omega, hper (q - P) (by omega)]
    exact hmin _ (by omega) (by omega)
  · refine Or.inr ⟨fun q hq => ?_, rfl⟩
    rw [show q = (q - P) + P by omega, hper (q - P) (by omega)]
    exact hw _ (by omega)

/-- **Phase transfer.** Two front walks along the same diagonals, all repeating with period `P` from `T`, that
start at or after `T` within `P` of each other stay within `P` of each other at every depth. -/
theorem walk_phase_transfer {f : Nat → Nat → Bool} {T P : Nat} (hper : ∀ i q, T ≤ q → f i (q + P) = f i q)
    {u v : Nat → Nat} (hu : ∀ j, IsFrontStep (f j) (u j) (u (j + 1)))
    (hv : ∀ j, IsFrontStep (f j) (v j) (v (j + 1))) (hT : T ≤ u 0) (h0 : u 0 ≤ v 0) (h1 : v 0 ≤ u 0 + P) :
    ∀ j, u j ≤ v j ∧ v j ≤ u j + P := by
  have hge : ∀ j, T ≤ u j := by
    intro j
    induction j with
    | zero => exact hT
    | succ j ih => exact Nat.le_trans ih (hu j).le
  intro j
  induction j with
  | zero => exact ⟨h0, h1⟩
  | succ j ih =>
    exact ⟨(hu j).mono (hv j) ih.1,
      (hv j).mono ((hu j).add_period (hper j) (hge j)) ih.2⟩

/-- So the advance of the two walks over any stretch of depths differs by at most `P`. -/
theorem walk_advance_close {f : Nat → Nat → Bool} {T P : Nat} (hper : ∀ i q, T ≤ q → f i (q + P) = f i q)
    {u v : Nat → Nat} (hu : ∀ j, IsFrontStep (f j) (u j) (u (j + 1)))
    (hv : ∀ j, IsFrontStep (f j) (v j) (v (j + 1))) (hT : T ≤ u 0) (h0 : u 0 ≤ v 0) (h1 : v 0 ≤ u 0 + P)
    (j k : Nat) : v k + u j ≤ u k + v j + P ∧ u k + v j ≤ v k + u j + P := by
  have a := walk_phase_transfer hper hu hv hT h0 h1 j
  have b := walk_phase_transfer hper hu hv hT h0 h1 k
  omega

/-- A front step along a sequence that is another one read `h` steps later, from `T` on, is, shifted by `h`, a
front step along the other. -/
theorem IsFrontStep.shift {f g : Nat → Bool} {T h t t' : Nat} (hg : ∀ q, T ≤ q → g q = f (q + h)) (hT : T ≤ t)
    (hs : IsFrontStep g t t') : IsFrontStep f (t + h) (t' + h) := by
  rcases hs with ⟨r, hr, hgr, hmin, rfl⟩ | ⟨hw, rfl⟩
  · refine Or.inl ⟨r + h, by omega, by rw [← hg r (by omega)]; exact hgr, fun q hq1 hq2 => ?_, by omega⟩
    rw [show q = (q - h) + h by omega, ← hg (q - h) (by omega)]
    exact hmin _ (by omega) (by omega)
  · refine Or.inr ⟨fun q hq => ?_, rfl⟩
    rw [show q = (q - h) + h by omega, ← hg (q - h) (by omega)]
    exact hw _ (by omega)

/-- **Walks on one branch.** If the diagonals `g` are the diagonals `f` read `h` steps later from `T` on, and the
diagonals `f` repeat with period `P` from `T`, a front walk `u` along `g` from `u 0 ≥ T`, shifted by `h`, stays
within `P` of every front walk `v` along `f` that starts within `P` after it. -/
theorem shifted_walk_close {f g : Nat → Nat → Bool} {T P h : Nat} (hper : ∀ i q, T ≤ q → f i (q + P) = f i q)
    (hg : ∀ i q, T ≤ q → g i q = f i (q + h)) {u v : Nat → Nat}
    (hu : ∀ j, IsFrontStep (g j) (u j) (u (j + 1)))
    (hv : ∀ j, IsFrontStep (f j) (v j) (v (j + 1))) (hT : T ≤ u 0) (h0 : u 0 + h ≤ v 0)
    (h1 : v 0 ≤ u 0 + h + P) : ∀ j, u j + h ≤ v j ∧ v j ≤ u j + h + P := by
  have hge : ∀ j, T ≤ u j := by
    intro j
    induction j with
    | zero => exact hT
    | succ j ih => exact Nat.le_trans ih (hu j).le
  exact walk_phase_transfer (u := fun j => u j + h) hper (fun j => (hu j).shift (hg j) (hge j)) hv
    (by omega) h0 h1

end Rule30Open
