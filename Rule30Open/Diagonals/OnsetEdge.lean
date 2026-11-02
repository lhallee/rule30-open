module

public import Rule30Open.Diagonals.SettledSlope
public import Rule30Open.Foundations.Official

/-!
# The onsets of the left diagonals are the left edge of a difference pattern

Two Rule 30 histories `evolve a` and `evolve b` that agree left of cell `L` at time `t` and differ at `L` have their
*edge* at `L`. Rule 30 is the exclusive or of the left neighbor with the OR of the cell and its right neighbor, so the
edge moves by a law that reads four cells:

* `diffEdge_left`: if the shared cell `L - 1` is white, the edge moves to `L - 1`;
* `diffEdge_stay`: if it is black and the copy that is white at `L` is also white at `L + 1`, the edge stays at `L`;
* `diffEdge_retreat`: if it is black and the copy white at `L` is black at `L + 1`, the copies agree up to `L` in
  the next row, and they differ at `L + 1` exactly when the other copy is black at `L + 1` or `L + 2`.

Agreement left of a cell spreads by at most one cell per step (`agree_below_succ`, `agree_below_add`), so a cell of a
left diagonal, which moves left one cell per step, stays left of the edge once it is.

For the single seed and its translate `evolve single (t + P) (x - P)` (`evolve_translate`), agreement on the left
diagonal `D i` at time `t` is `D i t = D i (t + P)`. So the edge is right of diagonal `j` at time `t` exactly when
every diagonal `i ≤ j` repeats with period `P` from `t` on (`edge_right_iff`): the running maximum of the onsets is
the time the edge passes diagonal `j`.

`EdgeBound c` is the hypothesis that the edge gains depth at rate `2/3`: at every time `t`, for some period `P > 0`,
the seed agrees with its translate by `P` on every diagonal `i` with `3 i + c < 2 t`. It is open. Under it every
diagonal `j` repeats from `⌈3j/2⌉ + ⌈c/2⌉ + 1` (`settling_of_edgeBound`), and black center runs have slope `3/13`
(`black_run_le_of_edgeBound`, through `SettledSlope.black_run_le_of_settling`).

The natural-language argument is `OnsetEdge.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

open Ruliology.CellularAutomata
open Ruliology.CellularAutomata.Rule30Diagonals
open Rule30Jen Rule30Prize

theorem onsetEdge_step (init : Int → Bool) (t : Nat) (x : Int) :
    evolve init (t + 1) x = rule30 (evolve init t (x - 1)) (evolve init t x) (evolve init t (x + 1)) := rfl

/-! ### The edge law -/

/-- **Agreement spreads at most one cell per step.** If two histories agree left of `L` at time `t`, they agree left
of `L - 1` at time `t + 1`. -/
theorem agree_below_succ (a b : Int → Bool) (t : Nat) (L : Int)
    (h : ∀ x : Int, x < L → evolve a t x = evolve b t x) :
    ∀ x : Int, x < L - 1 → evolve a (t + 1) x = evolve b (t + 1) x := by
  intro x hx
  rw [onsetEdge_step, onsetEdge_step, h (x - 1) (by omega), h x (by omega), h (x + 1) (by omega)]

theorem agree_below_add (a b : Int → Bool) (t : Nat) (L : Int)
    (h : ∀ x : Int, x < L → evolve a t x = evolve b t x) :
    ∀ n : Nat, ∀ x : Int, x < L - n → evolve a (t + n) x = evolve b (t + n) x := by
  intro n
  induction n with
  | zero => intro x hx; exact h x (by omega)
  | succ n ih =>
    intro x hx
    exact agree_below_succ a b (t + n) (L - n) ih x (by omega)

/-- **Edge law, white shared cell.** If the histories agree left of `L`, differ at `L`, and the shared cell `L - 1`
is white, then at the next time they agree left of `L - 1` and differ at `L - 1`. -/
theorem diffEdge_left (a b : Int → Bool) (t : Nat) (L : Int)
    (hagree : ∀ x : Int, x < L → evolve a t x = evolve b t x) (hdiff : evolve a t L ≠ evolve b t L)
    (hw : evolve a t (L - 1) = false) :
    (∀ x : Int, x < L - 1 → evolve a (t + 1) x = evolve b (t + 1) x) ∧
      evolve a (t + 1) (L - 1) ≠ evolve b (t + 1) (L - 1) := by
  refine ⟨agree_below_succ a b t L hagree, ?_⟩
  have hw' : evolve b t (L - 1) = false := (hagree (L - 1) (by omega)).symm.trans hw
  rw [onsetEdge_step, onsetEdge_step, hagree (L - 1 - 1) (by omega), show L - 1 + 1 = L by omega, hw, hw']
  revert hdiff
  cases evolve a t L <;> cases evolve b t L <;> cases evolve b t (L - 1 - 1) <;> decide

/-- **Edge law, black shared cell, stay.** If the shared cell `L - 1` is black and the copy `a`, white at `L`, is also
white at `L + 1`, then at the next time the histories agree left of `L` and differ at `L`. -/
theorem diffEdge_stay (a b : Int → Bool) (t : Nat) (L : Int)
    (hagree : ∀ x : Int, x < L → evolve a t x = evolve b t x) (hdiff : evolve a t L ≠ evolve b t L)
    (hblack : evolve a t (L - 1) = true) (h0 : evolve a t L = false) (h1 : evolve a t (L + 1) = false) :
    (∀ x : Int, x < L → evolve a (t + 1) x = evolve b (t + 1) x) ∧ evolve a (t + 1) L ≠ evolve b (t + 1) L := by
  have hb0 : evolve b t L = true := by
    revert hdiff; rw [h0]; cases evolve b t L <;> decide
  have hblack' : evolve b t (L - 1) = true := (hagree (L - 1) (by omega)).symm.trans hblack
  refine ⟨fun x hx => ?_, ?_⟩
  · rcases (show x < L - 1 ∨ x = L - 1 by omega) with hx | rfl
    · exact agree_below_succ a b t L hagree x hx
    · rw [onsetEdge_step, onsetEdge_step, hagree (L - 1 - 1) (by omega), hblack, hblack']
      cases evolve b t (L - 1 - 1) <;> cases evolve a t (L - 1 + 1) <;> cases evolve b t (L - 1 + 1) <;> rfl
  · rw [onsetEdge_step, onsetEdge_step, hblack, hblack', h0, h1, hb0]
    cases evolve b t (L + 1) <;> decide

/-- **Edge law, black shared cell, retreat.** If the shared cell `L - 1` is black and the copy `a`, white at `L`, is
black at `L + 1`, then at the next time the histories agree left of `L + 1`, and they differ at `L + 1` exactly when
the copy `b` is black at `L + 1` or at `L + 2`. -/
theorem diffEdge_retreat (a b : Int → Bool) (t : Nat) (L : Int)
    (hagree : ∀ x : Int, x < L → evolve a t x = evolve b t x) (hdiff : evolve a t L ≠ evolve b t L)
    (hblack : evolve a t (L - 1) = true) (h0 : evolve a t L = false) (h1 : evolve a t (L + 1) = true) :
    (∀ x : Int, x < L + 1 → evolve a (t + 1) x = evolve b (t + 1) x) ∧
      (evolve a (t + 1) (L + 1) ≠ evolve b (t + 1) (L + 1) ↔
        (evolve b t (L + 1) || evolve b t (L + 2)) = true) := by
  have hb0 : evolve b t L = true := by
    revert hdiff; rw [h0]; cases evolve b t L <;> decide
  have hblack' : evolve b t (L - 1) = true := (hagree (L - 1) (by omega)).symm.trans hblack
  refine ⟨fun x hx => ?_, ?_⟩
  · rcases (show x < L - 1 ∨ x = L - 1 ∨ x = L by omega) with hx | rfl | rfl
    · exact agree_below_succ a b t L hagree x hx
    · rw [onsetEdge_step, onsetEdge_step, hagree (L - 1 - 1) (by omega), hblack, hblack']
      cases evolve b t (L - 1 - 1) <;> cases evolve a t (L - 1 + 1) <;> cases evolve b t (L - 1 + 1) <;> rfl
    · rw [onsetEdge_step, onsetEdge_step, hblack, hblack', h0, hb0, h1]
      cases evolve b t (x + 1) <;> rfl
  · rw [onsetEdge_step, onsetEdge_step, show L + 1 - 1 = L by omega, h0, hb0, h1,
      show L + 1 + 1 = L + 2 by omega]
    cases evolve b t (L + 1) <;> cases evolve b t (L + 2) <;> cases evolve a t (L + 2) <;> decide

/-! ### The single seed against its translate -/

/-- Rule 30 commutes with translations in space and time: the history of the row `x ↦ evolve init s (x - c)` is
`evolve init (n + s) (x - c)`. -/
theorem evolve_translate (init : Int → Bool) (s : Nat) (c : Int) :
    ∀ n : Nat, ∀ x : Int, evolve (fun y => evolve init s (y - c)) n x = evolve init (n + s) (x - c) := by
  intro n
  induction n with
  | zero => intro x; rw [Nat.zero_add]; rfl
  | succ n ih =>
    intro x
    rw [onsetEdge_step, ih, ih, ih, show n + 1 + s = (n + s) + 1 by omega, onsetEdge_step,
      show x - 1 - c = x - c - 1 by omega, show x + 1 - c = x - c + 1 by omega]

/-- The single seed's left diagonal in terms of `evolve`. -/
theorem D_eq_evolve (i t : Nat) : D i t = evolve single t ((i : Int) - t) := by
  rw [evolve_single_eq_cell]; rfl

/-- **The edge passes diagonal `j` when every diagonal up to `j` has settled.** The seed and its translate by `P`
steps and `P` cells agree at time `t` on every cell `x ≤ j - t` (the edge is right of diagonal `j`) exactly when every
diagonal `i ≤ j` repeats with period `P` from time `t` on. -/
theorem edge_right_iff (P j t : Nat) :
    (∀ x : Int, x ≤ (j : Int) - t → evolve single t x = evolve single (t + P) (x - P)) ↔
      ∀ i, i ≤ j → RepeatsFrom (D i) t P := by
  constructor
  · intro h i hi s hs
    have hagree : ∀ x : Int, x < (j : Int) - t + 1 →
        evolve single t x = evolve (fun y => evolve single P (y - P)) t x := by
      intro x hx
      rw [evolve_translate]
      exact h x (by omega)
    have key := agree_below_add single (fun y => evolve single P (y - P)) t ((j : Int) - t + 1) hagree (s - t)
      ((i : Int) - s) (by omega)
    rw [show t + (s - t) = s by omega, evolve_translate] at key
    rw [D_eq_evolve, D_eq_evolve, key, show s + P = s + P by rfl]
    congr 1
    omega
  · intro h x hx
    by_cases hneg : x + t < 0
    · have h1 : evolve single t x = false := by
        rw [evolve_single_eq_cell]; exact cell_eq_false_of_lt t x (by omega)
      have h2 : evolve single (t + P) (x - P) = false := by
        rw [evolve_single_eq_cell]; exact cell_eq_false_of_lt (t + P) (x - P) (by omega)
      rw [h1, h2]
    · obtain ⟨i, hi⟩ : ∃ i : Nat, (i : Int) = x + t := ⟨(x + t).toNat, by omega⟩
      have hrep := h i (by omega) t (Nat.le_refl t)
      rw [D_eq_evolve, D_eq_evolve] at hrep
      rw [show x = (i : Int) - t by omega, show (i : Int) - t - P = (i : Int) - ((t + P : Nat) : Int) by omega]
      exact hrep.symm

/-! ### The edge hypothesis and the slope it gives -/

/-- **The edge gains depth at rate `2/3` (open).** At every time `t`, for some period `P > 0`, the seed agrees with its
translate by `P` steps and `P` cells on every diagonal `i` with `3 i + c < 2 t`: the edge's diagonal is at least
`(2 t - c)/3`. -/
def EdgeBound (c : Nat) : Prop :=
  ∀ t : Nat, ∃ P, 0 < P ∧ ∀ x : Int, 3 * (x + t) + c < 2 * t → evolve single t x = evolve single (t + P) (x - P)

/-- Under the edge hypothesis every diagonal up to `j` repeats, with one period, from time `⌊(3j + c)/2⌋ + 1`. -/
theorem repeats_of_edgeBound (c : Nat) (h : EdgeBound c) (j : Nat) :
    ∃ P, 0 < P ∧ ∀ i, i ≤ j → RepeatsFrom (D i) ((3 * j + c) / 2 + 1) P := by
  obtain ⟨P, hP, hb⟩ := h ((3 * j + c) / 2 + 1)
  refine ⟨P, hP, (edge_right_iff P j _).mp fun x hx => hb x ?_⟩
  omega

/-- **Linear settling from the edge.** Under the edge hypothesis every diagonal `j` repeats from
`⌈3j/2⌉ + ⌈c/2⌉ + 1`, the settling hypothesis of `SettledSlope.black_run_le_of_settling` with
`δ = ⌈c/2⌉ + 1`. -/
theorem settling_of_edgeBound (c : Nat) (h : EdgeBound c) (j : Nat) :
    ∃ P, 0 < P ∧ RepeatsFrom (D j) ((3 * j + 1) / 2 + ((c + 1) / 2 + 1)) P := by
  obtain ⟨P, hP, hr⟩ := repeats_of_edgeBound c h j
  exact ⟨P, hP, (hr j (Nat.le_refl j)).mono (by omega)⟩

/-- **Black runs of slope `3/13` from the edge.** If the edge gains depth at rate `2/3` (`EdgeBound c`) and the
antiphase alternations of every settled pair `j ≤ J` are eventually bounded by `A`, a black run of the center column
of length `L` from time `a ≥ 1` with `⌊8a/13⌋ ≤ J` has `13 L ≤ 3 a + 130 A + 130 (⌈c/2⌉ + 1) + 260`. -/
theorem black_run_le_of_edgeBound (c J A : Nat) (h : EdgeBound c) (hA : ∀ j, j ≤ J → ∃ T, AltBound j T A)
    (a L : Nat) (ha : 1 ≤ a) (hJ : 8 * a / 13 ≤ J) (hrun : ∀ i, i < L → center (a + i) = true) :
    13 * L ≤ 3 * a + 130 * A + 130 * ((c + 1) / 2 + 1) + 260 :=
  black_run_le_of_settling J ((c + 1) / 2 + 1) A (fun j _ => settling_of_edgeBound c h j) hA a L ha hJ hrun

end Rule30Open
