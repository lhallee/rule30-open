module

public import Ruliology.CellularAutomata.Rule30Ether

/-!
# A second infinite right half that never enters the ether-and-wall family

Rule 30 has a background of period 8 in time and 80 cells in space. Eight of its 80 columns repeat `0001`
(`colOK`). The right half beside such a column, driven by `0001`, is the background itself, so it repeats with period
8 in time (`drv_eq`, `Fb_period`). It is in the kit's ether-and-wall family (`Rule30Ether.InFamily`) at no time and for
no alignment of the ether (`not_inFamily`): the half carries the ether on at most its first 7 columns, whatever the
time and the alignment of the ether, and the family needs the ether on every column up to the wall. The aligned ether,
which no wall state follows, is another infinite half that stays out; this half has no ether beyond 7 cells.

This is a statement about an infinite half. The kit's `Absorption` is about finitely supported halves, and this one has
black cells at arbitrarily large columns (`background_half_unbounded`), so it is not a counterexample to it.

The natural-language argument is `BackgroundHalves.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

open Ruliology.CellularAutomata Ruliology.CellularAutomata.Rule30Jen Ruliology.CellularAutomata.Rule30Ether

/-- The background of period 8 on 80 cells: byte `j` is column `j`, bit `ph` of it the cell at phase `ph`. -/
def ringNat : Nat :=
  129515908046530454386509417356051773082116734454544663000816092763128142297534647278019020151134972248641385504902878830557068758445768559890336752400908053155324557995697394187465329393231045

/-- Column `j` of the background at phase `ph`, both read modulo the periods. -/
def ringBit (j ph : Nat) : Bool := ringNat.testBit (8 * (j % 80) + ph % 8)

theorem ringBit_congr {j j' ph ph' : Nat} (hj : j % 80 = j' % 80) (hph : ph % 8 = ph' % 8) :
    ringBit j ph = ringBit j' ph' := by
  unfold ringBit; rw [hj, hph]

theorem ring_rule_small : ∀ a, a < 80 → ∀ b, b < 8 →
    ringBit (a + 1) (b + 1) = rule (ringBit a b) (ringBit (a + 1) b) (ringBit (a + 2) b) := by
  decide +kernel

/-- **The background is a rule-30 orbit**, left neighbor first. -/
theorem ring_rule (j ph : Nat) :
    ringBit (j + 1) (ph + 1) = rule (ringBit j ph) (ringBit (j + 1) ph) (ringBit (j + 2) ph) := by
  have h := ring_rule_small (j % 80) (Nat.mod_lt _ (by decide)) (ph % 8) (Nat.mod_lt _ (by decide))
  rw [ringBit_congr (j := j % 80 + 1) (j' := j + 1) (ph := ph % 8 + 1) (ph' := ph + 1) (by omega) (by omega),
    ringBit_congr (j := j % 80) (j' := j) (ph := ph % 8) (ph' := ph) (by omega) (by omega),
    ringBit_congr (j := j % 80 + 1) (j' := j + 1) (ph := ph % 8) (ph' := ph) (by omega) (by omega),
    ringBit_congr (j := j % 80 + 2) (j' := j + 2) (ph := ph % 8) (ph' := ph) (by omega) (by omega)] at h
  exact h

/-- Column `x0` reads `0001` from phase `ph0`: the cells at the phases `ph0, ph0 + 1, ...` are `0, 0, 0, 1, ...`. -/
def colOK (x0 ph0 : Nat) : Bool := (List.range 8).all fun t => ringBit x0 (t + ph0) == wordAt w0001 t

/-- The columns of the background that repeat `0001`, as pairs of column and phase (a column of period 4 reads the word
from two phases). -/
theorem colOK_list : ((List.range 80).flatMap fun x0 => (List.range 8).filterMap fun ph0 =>
    if colOK x0 ph0 then some (x0, ph0) else none) =
    [(8, 2), (8, 6), (18, 1), (18, 5), (28, 0), (28, 4), (38, 3), (38, 7), (48, 2), (48, 6), (58, 1), (58, 5), (68, 0),
      (68, 4), (78, 3), (78, 7)] := by decide +kernel

theorem colOK_spec {x0 ph0 : Nat} (h : colOK x0 ph0 = true) (t : Nat) : ringBit x0 (t + ph0) = wordAt w0001 t := by
  have h1 := List.all_eq_true.1 h (t % 8) (List.mem_range.2 (Nat.mod_lt _ (by decide)))
  have e1 : ringBit x0 (t + ph0) = ringBit x0 (t % 8 + ph0) := ringBit_congr rfl (by omega)
  have e2 : wordAt w0001 t = wordAt w0001 (t % 8) := by unfold wordAt; congr 1; omega
  rw [e1, e2]; exact beq_iff_eq.1 h1

/-- The half beside column `x0`: column `p` of it at time `t` is column `x0 + p` of the background at phase `t + ph0`.
Column 0 is the column `x0` itself. -/
def Fb (x0 ph0 : Nat) (t p : Nat) : Bool := ringBit (x0 + p) (t + ph0)

theorem Fb_period (x0 ph0 t p : Nat) : Fb x0 ph0 (t + 8) p = Fb x0 ph0 t p :=
  ringBit_congr rfl (by omega)

theorem Fb_space_period (x0 ph0 t p : Nat) : Fb x0 ph0 t (p + 80) = Fb x0 ph0 t p :=
  ringBit_congr (by omega) rfl

/-- **The half beside a `0001` column of the background, driven by `0001`, is the background**: the driven half `drv`
of the kit, started from the half at time 0, reads `Fb` at every time. -/
theorem drv_eq (x0 ph0 : Nat) (h : colOK x0 ph0 = true) : ∀ t p,
    drv (fun t => wordAt w0001 (t + 0)) (fun p => Fb x0 ph0 0 p) t p = Fb x0 ph0 t p := by
  intro t
  induction t with
  | zero =>
    intro p
    cases p with
    | zero => simpa [drv, Fb] using (colOK_spec h 0).symm
    | succ p => simp [drv]
  | succ t ih =>
    intro p
    cases p with
    | zero =>
      show wordAt w0001 (t + 1 + 0) = ringBit (x0 + 0) (t + 1 + ph0)
      exact (colOK_spec h (t + 1)).symm
    | succ p =>
      show rule (drv _ _ t p) (drv _ _ t (p + 1)) (drv _ _ t (p + 2)) = Fb x0 ph0 (t + 1) (p + 1)
      rw [ih p, ih (p + 1), ih (p + 2)]
      have := ring_rule (x0 + p) (t + ph0)
      unfold Fb
      rw [ringBit_congr (j := x0 + (p + 1)) (j' := x0 + p + 1) (ph := t + 1 + ph0) (ph' := t + ph0 + 1) (by omega)
        (by omega), this,
        ringBit_congr (j := x0 + p + 1) (j' := x0 + (p + 1)) (ph := t + ph0) (ph' := t + ph0) (by omega) rfl,
        ringBit_congr (j := x0 + p + 2) (j' := x0 + (p + 2)) (ph := t + ph0) (ph' := t + ph0) (by omega) rfl]

/-- The half beside column 8 has black cells at arbitrarily large columns, so it is not finitely supported. -/
theorem background_half_unbounded : ∀ n, ∃ p, n < p ∧ Fb 8 2 0 p = true := by
  have h : Fb 8 2 0 (5 + 80 * 0) = true := by decide +kernel
  have step : ∀ m, Fb 8 2 0 (5 + 80 * m) = true := by
    intro m
    induction m with
    | zero => exact h
    | succ m ih => rw [show 5 + 80 * (m + 1) = 5 + 80 * m + 80 by omega, Fb_space_period]; exact ih
  intro n
  exact ⟨5 + 80 * (n + 1), by omega, step (n + 1)⟩

/-- For every `0001` column, time, and alignment `(j, s)` of the ether, the half differs from the ether
`ether (j + p + 1) (ph + s)` at some column `p + 1` with `p < 8`. -/
theorem prefix_short : ∀ x0 ∈ List.range 80, ∀ ph0 ∈ List.range 8, colOK x0 ph0 = true → ∀ ph ∈ List.range 8,
    ∀ j ∈ List.range 7, ∀ s ∈ List.range 4, ∃ p ∈ List.range 8, Fb x0 ph0 ph (p + 1) ≠ ether (j + (p + 1)) (ph + s) := by
  decide +kernel

/-- No wall state follows a short ether prefix: for every `0001` column, time and alignment, and every `k < 8` with
`(j + k) % 7 = 2` and the ether on columns `1 .. k`, the 13 cells after column `k` are not a wall state. -/
theorem wall_absent : ∀ x0 ∈ List.range 80, ∀ ph0 ∈ List.range 8, colOK x0 ph0 = true → ∀ ph ∈ List.range 8,
    ∀ j ∈ List.range 7, ∀ s ∈ List.range 4, ∀ k ∈ List.range 8, (j + k) % 7 = 2 →
      (∀ p ∈ List.range k, Fb x0 ph0 ph (p + 1) = ether (j + (p + 1)) (ph + s)) →
      ((ph + s) % 4, rowOf (Fb x0 ph0) ph k 13) ∉ wallStates := by
  decide +kernel

/-- **The half beside a `0001` column of the 80-cell background is in the family at no time, for no alignment.** -/
theorem not_inFamily (x0 ph0 : Nat) (hx : x0 < 80) (hp : ph0 < 8) (h : colOK x0 ph0 = true) (j0 s t1 : Nat) :
    ¬ InFamily (Fb x0 ph0) j0 s t1 := by
  rintro ⟨k, hk, hE, hW⟩
  have hF : ∀ p, Fb x0 ph0 t1 p = Fb x0 ph0 (t1 % 8) p := fun p => ringBit_congr rfl (by omega)
  have hether : ∀ p, ether (j0 + p) (t1 + s) = ether (j0 % 7 + p) (t1 % 8 + s % 4) :=
    fun p => ether_congr (by omega) (by omega)
  obtain ⟨p, hpN, hne⟩ := prefix_short x0 (List.mem_range.2 hx) ph0 (List.mem_range.2 hp) h (t1 % 8)
    (List.mem_range.2 (Nat.mod_lt _ (by decide))) (j0 % 7) (List.mem_range.2 (Nat.mod_lt _ (by decide))) (s % 4)
    (List.mem_range.2 (Nat.mod_lt _ (by decide)))
  have hpN := List.mem_range.1 hpN
  by_cases hkp : p + 1 ≤ k
  · apply hne
    rw [← hF, ← hether]
    exact hE (p + 1) (by omega) hkp
  · apply wall_absent x0 (List.mem_range.2 hx) ph0 (List.mem_range.2 hp) h (t1 % 8)
      (List.mem_range.2 (Nat.mod_lt _ (by decide))) (j0 % 7) (List.mem_range.2 (Nat.mod_lt _ (by decide))) (s % 4)
      (List.mem_range.2 (Nat.mod_lt _ (by decide))) k (List.mem_range.2 (by omega)) (by omega)
    · intro q hq
      have hq := List.mem_range.1 hq
      rw [← hF, ← hether]
      exact hE (q + 1) (by omega) (by omega)
    · have e1 : rowOf (Fb x0 ph0) t1 k 13 = rowOf (Fb x0 ph0) (t1 % 8) k 13 := by
        unfold rowOf; congr 1; funext i; exact hF _
      rw [show (t1 % 8 + s % 4) % 4 = (t1 + s) % 4 by omega, ← e1]
      exact hW

/-- **The infinite half beside a `0001` column of the background, driven by `0001`, never enters the family**: the
kit's `InFamily` fails for the driven half at every time and every alignment of the ether. -/
theorem background_half_not_inFamily (x0 ph0 : Nat) (hx : x0 < 80) (hp : ph0 < 8) (h : colOK x0 ph0 = true)
    (j0 s t1 : Nat) :
    ¬ InFamily (drv (fun t => wordAt w0001 (t + 0)) (fun p => Fb x0 ph0 0 p)) j0 s t1 := by
  have e : drv (fun t => wordAt w0001 (t + 0)) (fun p => Fb x0 ph0 0 p) = Fb x0 ph0 :=
    funext fun t => funext fun p => drv_eq x0 ph0 h t p
  rw [e]
  exact not_inFamily x0 ph0 hx hp h j0 s t1

/-- The same for the kit's alignments of `0001`, in the form of the conclusion of `Absorption`. -/
theorem background_half_not_absorbed (x0 ph0 : Nat) (hx : x0 < 80) (hp : ph0 < 8) (h : colOK x0 ph0 = true) :
    ¬ ∃ a ∈ A0001, ∃ t1,
      InFamily (drv (fun t => wordAt w0001 (t + 0)) (fun p => Fb x0 ph0 0 p)) a.1 (a.2 + 0) t1 := by
  rintro ⟨a, _, t1, ht⟩
  exact background_half_not_inFamily x0 ph0 hx hp h a.1 (a.2 + 0) t1 ht

/-- For the `0001` column 8 of the background: an infinite half, with black cells at arbitrarily large columns, that
the kit's family contains at no time and for no alignment. -/
theorem background_half_8 : ∃ x : Nat → Bool, (∀ n, ∃ p, n < p ∧ x p = true) ∧
    ∀ j0 s t1, ¬ InFamily (drv (fun t => wordAt w0001 (t + 0)) x) j0 s t1 :=
  ⟨fun p => Fb 8 2 0 p, background_half_unbounded,
    fun j0 s t1 => background_half_not_inFamily 8 2 (by decide) (by decide) (by decide +kernel) j0 s t1⟩

end Rule30Open
