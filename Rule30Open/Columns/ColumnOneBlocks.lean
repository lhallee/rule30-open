module

public import Ruliology.CellularAutomata.Rule30Ether

/-!
# Beside `0001`, column 1 moves in blocks of four along a graph of 13 edges

Take any rule-30 evolution `F` of the columns `p ≥ 0` (`Rule30Ether.IsR30`) whose column `0` repeats `0001` from a
time `T` on, black exactly at the times `t ≡ 3 (mod 4)`. The kit's driven half `Rule30Ether.drv (wordAt w0001) x` is
one, with `T = 0`, for every right half `x`, finite or not. Call the times `4n, …, 4n + 3` block `n`. For every block
with `T ≤ 4n`:

* `column_one_blocks` (A): column `1` on block `n` reads `0^a 1^(4-a)` (`cobWord a`) with `a = colOneVal F (4n)` the
  number of its white cells, and the pair of consecutive values `(a_n, a_(n+1))` is one of the 13 edges `cobEdges`:
  `0 → 1, 2, 3, 4`, `1 → 2, 3, 4`, `2 → 1, 2`, `3 → 2, 3`, `4 → 0, 1`.
* `column_one_blocks` (B): if `a_n = a_(n+1) = 3`, columns `1` to `4` on block `n` are the kit's ether with alignment
  `(5, 0)` (`0001, 0011, 0110, 1101`) and column `5` is white at phase 2; if `a_n = a_(n+1) = 2`, columns `1` to `3`
  are the ether with alignment `(6, 0)` (`0011, 0110, 1101`) and column `4` is white at phase 2.
* `column_one_white_period_four` (C): if column `1` repeats with period 4 at the white times of the drive (phases
  `0, 1, 2`) from some time on, then `a_n` is eventually constant `3` or constant `2`;
  `column_one_period_four` is the same under period 4 at all times, and `column_one_period_four_ether` adds the forced
  ether of (B) at every later block.
* `cob_loops`, `cob_two_cycles`: only `2` and `3` carry a loop, and the 2-cycles of the graph are `(0, 4)`, `(1, 2)`
  and `(1, 4)`.
* `drv_column_one_blocks`, `drv_column_one_white_period_four`: the same for the kit's driven half, for every `x`.
* `cob_edges_realized`: each of the 13 edges is followed by blocks `0` and `1` of some driven half supported in cells
  `1` to `8`, so the graph is the exact set of one-step transitions.

**Method.** Column `1` on blocks `n` and `n + 1`, and columns `1` to `5` on block `n`, lie in the light cone of
columns `1` to `8` at time `4n` and the drive. `cobRows` computes that cone row by row with the kit's `lin3`
(`cob_rows`, through `rowOf_succ`), and `cobCheck_all` checks the three statements on all `2^8` rows of 8 cells
(`decide +kernel`). Statement (C) is then a short induction over blocks: equal white readings on consecutive blocks
and an edge of the graph force the two values to be equal and in `{2, 3}` (`cob_white_rigid`).

The natural-language argument is `ColumnOneBlocks.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

open Ruliology.CellularAutomata Ruliology.CellularAutomata.Rule30Jen Ruliology.CellularAutomata.Rule30Ether
  Ruliology.CellularAutomata.Rule30StripCertificates

/-! ### Blocks of column 1 and the graph -/

/-- Column `1` of `F` on the four times from `t0`. -/
def colOneWord (F : Nat → Nat → Bool) (t0 : Nat) : List Bool :=
  [F t0 1, F (t0 + 1) 1, F (t0 + 2) 1, F (t0 + 3) 1]

/-- The block value: the number of white cells of column `1` on the four times from `t0`. -/
def colOneVal (F : Nat → Nat → Bool) (t0 : Nat) : Nat := (colOneWord F t0).count false

/-- The block `0^a 1^(4-a)`. -/
def cobWord (a : Nat) : List Bool := List.replicate a false ++ List.replicate (4 - a) true

/-- The 13 edges of the block graph of column `1`. -/
def cobEdges : List (Nat × Nat) :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 1), (2, 2), (3, 2), (3, 3), (4, 0), (4, 1)]

theorem cobEdges_length : cobEdges.length = 13 := rfl

theorem cobEdges_nodup : cobEdges.Nodup := by decide

/-- Only the values `2` and `3` carry a loop. -/
theorem cob_loops (a : Nat) : (a, a) ∈ cobEdges ↔ a = 2 ∨ a = 3 := by
  have key : ∀ e ∈ cobEdges, e.1 = e.2 → e.1 = 2 ∨ e.1 = 3 := by decide
  constructor
  · intro h
    exact key _ h rfl
  · rintro (rfl | rfl) <;> decide

/-- The 2-cycles of the graph: the pairs `x < y` with both `x → y` and `y → x`. -/
theorem cob_two_cycles : ((List.range 5).flatMap fun x => (List.range 5).filterMap fun y =>
    if x < y ∧ (x, y) ∈ cobEdges ∧ (y, x) ∈ cobEdges then some (x, y) else none) =
    [(0, 4), (1, 2), (1, 4)] := by decide

theorem colOneWord_getD (F : Nat → Nat → Bool) (t : Nat) :
    ∀ i, i < 4 → (colOneWord F t).getD i false = F (t + i) 1
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | _ + 4, h => absurd h (by omega)

theorem colOneVal_le (F : Nat → Nat → Bool) (t : Nat) : colOneVal F t ≤ 4 :=
  List.count_le_length

/-! ### The light cone of eight cells -/

/-- The rows of the cone above a row `r` of columns `1, 2, …` at a time of drive phase `0`: row `k` is columns
`1, …, |r| - k` at `k` steps later, with column `0` reading `0001`. -/
def cobRows (r : List Bool) : Nat → List Bool
  | 0 => r
  | k + 1 => lin3 (wordAt w0001 k :: cobRows r k)

theorem cob_seg_getD (f : Nat → Bool) : ∀ (n i : Nat), i < n → (seg f n).getD i false = f i
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | _ + 1, 0, _ => rfl
  | n + 1, i + 1, h => by
    show (seg (fun j => f (j + 1)) n).getD i false = f (i + 1)
    exact cob_seg_getD (fun j => f (j + 1)) n i (by omega)

theorem cob_rows {F : Nat → Nat → Bool} (hF : IsR30 F) {t0 : Nat}
    (hd : ∀ k, k ≤ 6 → F (t0 + k) 0 = wordAt w0001 k) :
    ∀ k, k ≤ 7 → rowOf F (t0 + k) 0 (8 - k) = cobRows (rowOf F t0 0 8) k
  | 0, _ => rfl
  | k + 1, hk => by
    have ih := cob_rows hF hd k (by omega)
    have e := rowOf_succ hF (t0 + k) 0 (8 - (k + 1))
    have e2 : rowOf F (t0 + k) 0 (8 - (k + 1)) ++ [F (t0 + k) (0 + (8 - (k + 1)) + 1)] =
        rowOf F (t0 + k) 0 (8 - k) := by
      rw [show 8 - k = 8 - (k + 1) + 1 by omega]
      unfold rowOf
      rw [seg_succ]
    rw [show t0 + (k + 1) = t0 + k + 1 by omega, e, e2, ih, hd k (by omega)]
    rfl

/-- A cell of the cone, read from `cobRows`. -/
theorem cob_cell {F : Nat → Nat → Bool} (hF : IsR30 F) {t0 : Nat}
    (hd : ∀ k, k ≤ 6 → F (t0 + k) 0 = wordAt w0001 k) (t k p q : Nat) (ht : t = t0 + k) (hp : p = q + 1)
    (hk : k ≤ 7) (hq : q + k < 8) : F t p = (cobRows (rowOf F t0 0 8) k).getD q false := by
  subst ht hp
  rw [← cob_rows hF hd k hk]
  unfold rowOf
  rw [cob_seg_getD _ _ _ (by omega)]
  simp

theorem cob_row8 (F : Nat → Nat → Bool) (t0 : Nat) :
    rowOf F t0 0 8 = [F t0 1, F t0 2, F t0 3, F t0 4, F t0 5, F t0 6, F t0 7, F t0 8] := rfl

/-! ### The kernel check on all rows of 8 cells -/

/-- Column `1` on the four steps from step `s` of the cone. -/
def cobCol1 (r : List Bool) (s : Nat) : List Bool :=
  [(cobRows r s).getD 0 false, (cobRows r (s + 1)).getD 0 false, (cobRows r (s + 2)).getD 0 false,
    (cobRows r (s + 3)).getD 0 false]

/-- Columns `1, …, m` of the cone at steps `0` to `3` are the ether with alignment `(j0, 0)`. -/
def cobEtherOK (r : List Bool) (j0 m : Nat) : Bool :=
  (List.range 4).all fun φ => (List.range m).all fun q => (cobRows r φ).getD q false == ether (j0 + (q + 1)) φ

/-- Statements (A) and (B) on the cone of the row `r`. -/
def cobCheck (r : List Bool) : Bool :=
  (cobCol1 r 0 == cobWord ((cobCol1 r 0).count false)) &&
  cobEdges.contains ((cobCol1 r 0).count false, (cobCol1 r 4).count false) &&
  (!((cobCol1 r 0).count false == 3 && (cobCol1 r 4).count false == 3) ||
    (cobEtherOK r 5 4 && !(cobRows r 2).getD 4 false)) &&
  (!((cobCol1 r 0).count false == 2 && (cobCol1 r 4).count false == 2) ||
    (cobEtherOK r 6 3 && !(cobRows r 2).getD 3 false))

/-- **The check on every row of 8 cells** (256 rows, kernel evaluation). -/
theorem cobCheck_all : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool,
    cobCheck [b0, b1, b2, b3, b4, b5, b6, b7] = true := by
  decide +kernel

/-! ### Back to the evolution -/

section Cone

variable {F : Nat → Nat → Bool} (hF : IsR30 F) {t0 : Nat}
  (hd : ∀ k, k ≤ 6 → F (t0 + k) 0 = wordAt w0001 k)
include hF hd

omit hF hd in
theorem cob_check_F : cobCheck (rowOf F t0 0 8) = true := by
  rw [cob_row8]; exact cobCheck_all _ _ _ _ _ _ _ _

theorem colOneWord_cone0 : colOneWord F t0 = cobCol1 (rowOf F t0 0 8) 0 := by
  unfold colOneWord cobCol1
  rw [cob_cell hF hd t0 0 1 0 (by omega) rfl (by omega) (by omega),
    cob_cell hF hd (t0 + 1) (0 + 1) 1 0 (by omega) rfl (by omega) (by omega),
    cob_cell hF hd (t0 + 2) (0 + 2) 1 0 (by omega) rfl (by omega) (by omega),
    cob_cell hF hd (t0 + 3) (0 + 3) 1 0 (by omega) rfl (by omega) (by omega)]

theorem colOneWord_cone4 : colOneWord F (t0 + 4) = cobCol1 (rowOf F t0 0 8) 4 := by
  unfold colOneWord cobCol1
  rw [cob_cell hF hd (t0 + 4) 4 1 0 (by omega) rfl (by omega) (by omega),
    cob_cell hF hd (t0 + 4 + 1) (4 + 1) 1 0 (by omega) rfl (by omega) (by omega),
    cob_cell hF hd (t0 + 4 + 2) (4 + 2) 1 0 (by omega) rfl (by omega) (by omega),
    cob_cell hF hd (t0 + 4 + 3) (4 + 3) 1 0 (by omega) rfl (by omega) (by omega)]

theorem cob_ether_of {j0 m : Nat} (hm : m ≤ 4) (h : cobEtherOK (rowOf F t0 0 8) j0 m = true) :
    ∀ p φ, 1 ≤ p → p ≤ m → φ < 4 → F (t0 + φ) p = ether (j0 + p) φ := by
  intro p φ hp1 hpm hφ
  have h1 := List.all_eq_true.1 h φ (List.mem_range.2 hφ)
  have h2 := List.all_eq_true.1 h1 (p - 1) (List.mem_range.2 (by omega))
  rw [cob_cell hF hd (t0 + φ) φ p (p - 1) rfl (by omega) (by omega) (by omega), beq_iff_eq.1 h2]
  congr 1
  omega

/-- **(A), block form.** Column `1` on the block from `t0` reads `0^a 1^(4-a)`. -/
theorem col_one_block_form : colOneWord F t0 = cobWord (colOneVal F t0) := by
  have h := cob_check_F (F := F) (t0 := t0)
  simp only [cobCheck, Bool.and_eq_true] at h
  unfold colOneVal
  rw [colOneWord_cone0 hF hd]
  exact beq_iff_eq.1 h.1.1.1

/-- **(A), transitions.** Consecutive blocks follow an edge of the graph. -/
theorem col_one_block_edge : (colOneVal F t0, colOneVal F (t0 + 4)) ∈ cobEdges := by
  have h := cob_check_F (F := F) (t0 := t0)
  simp only [cobCheck, Bool.and_eq_true] at h
  unfold colOneVal
  rw [colOneWord_cone0 hF hd, colOneWord_cone4 hF hd]
  exact List.contains_iff_mem.1 h.1.1.2

/-- **(B) at the value 3.** Columns `1` to `4` are the ether with alignment `(5, 0)` on the block, ending in B3,
and column `5` is white at phase 2. -/
theorem col_one_force_three (h3 : colOneVal F t0 = 3) (h3' : colOneVal F (t0 + 4) = 3) :
    (∀ p φ, 1 ≤ p → p ≤ 4 → φ < 4 → F (t0 + φ) p = ether (5 + p) φ) ∧ F (t0 + 2) 5 = false := by
  have h := cob_check_F (F := F) (t0 := t0)
  simp only [cobCheck, Bool.and_eq_true] at h
  have hC := h.1.2
  unfold colOneVal at h3 h3'
  rw [colOneWord_cone0 hF hd] at h3
  rw [colOneWord_cone4 hF hd] at h3'
  rw [h3, h3'] at hC
  simp only [beq_self_eq_true, Bool.and_self, Bool.not_true, Bool.false_or, Bool.and_eq_true,
    Bool.not_eq_true'] at hC
  refine ⟨cob_ether_of hF hd (by omega) hC.1, ?_⟩
  rw [cob_cell hF hd (t0 + 2) 2 5 4 rfl rfl (by omega) (by omega)]
  exact hC.2

/-- **(B) at the value 2.** Columns `1` to `3` are the ether with alignment `(6, 0)` on the block, ending in B3,
and column `4` is white at phase 2. -/
theorem col_one_force_two (h2 : colOneVal F t0 = 2) (h2' : colOneVal F (t0 + 4) = 2) :
    (∀ p φ, 1 ≤ p → p ≤ 3 → φ < 4 → F (t0 + φ) p = ether (6 + p) φ) ∧ F (t0 + 2) 4 = false := by
  have h := cob_check_F (F := F) (t0 := t0)
  simp only [cobCheck, Bool.and_eq_true] at h
  have hC := h.2
  unfold colOneVal at h2 h2'
  rw [colOneWord_cone0 hF hd] at h2
  rw [colOneWord_cone4 hF hd] at h2'
  rw [h2, h2'] at hC
  simp only [beq_self_eq_true, Bool.and_self, Bool.not_true, Bool.false_or, Bool.and_eq_true,
    Bool.not_eq_true'] at hC
  refine ⟨cob_ether_of hF hd (by omega) hC.1, ?_⟩
  rw [cob_cell hF hd (t0 + 2) 2 4 3 rfl rfl (by omega) (by omega)]
  exact hC.2

end Cone

/-! ### Statement (C): period four forces a loop -/

/-- Equal readings at the white phases on an edge of the graph force a loop, at `2` or `3`. -/
theorem cob_white_rigid : ∀ e ∈ cobEdges,
    ((List.range 3).all fun i => (cobWord e.1).getD i false == (cobWord e.2).getD i false) = true →
    e.1 = e.2 ∧ (e.1 = 2 ∨ e.1 = 3) := by decide

/-- One step of (C): if column `1` reads the same at phases `0, 1, 2` of two consecutive blocks, the two block values
are equal and lie in `{2, 3}`. -/
theorem cob_step {F : Nat → Nat → Bool} (hF : IsR30 F) {t0 : Nat}
    (hd : ∀ k, k ≤ 6 → F (t0 + k) 0 = wordAt w0001 k)
    (hd4 : ∀ k, k ≤ 6 → F (t0 + 4 + k) 0 = wordAt w0001 k)
    (hr : ∀ i, i < 3 → F (t0 + 4 + i) 1 = F (t0 + i) 1) :
    colOneVal F (t0 + 4) = colOneVal F t0 ∧ (colOneVal F t0 = 2 ∨ colOneVal F t0 = 3) := by
  have he := col_one_block_edge hF hd
  have hf0 := col_one_block_form hF hd
  have hf1 := col_one_block_form hF hd4
  have hall : ((List.range 3).all fun i =>
      (cobWord (colOneVal F t0)).getD i false == (cobWord (colOneVal F (t0 + 4))).getD i false) = true := by
    refine List.all_eq_true.2 fun i hi => beq_iff_eq.2 ?_
    have hi3 := List.mem_range.1 hi
    rw [← hf0, ← hf1, colOneWord_getD F t0 i (by omega), colOneWord_getD F (t0 + 4) i (by omega), hr i hi3]
  have := cob_white_rigid _ he hall
  exact ⟨this.1.symm, this.2⟩

theorem cob_drive_shift {F : Nat → Nat → Bool} {T : Nat} (hc : ∀ t, T ≤ t → F t 0 = wordAt w0001 t)
    (n : Nat) (hn : T ≤ 4 * n) : ∀ k, k ≤ 6 → F (4 * n + k) 0 = wordAt w0001 k := by
  intro k _
  rw [hc _ (by omega)]
  unfold wordAt
  rw [show (4 * n + k) % 4 = k % 4 by omega]

/-- **Statements (A) and (B)** for every rule-30 evolution of the columns `p ≥ 0` whose column `0` repeats `0001`
from time `T` on, at every block `n` with `T ≤ 4n`. -/
theorem column_one_blocks {F : Nat → Nat → Bool} (hF : IsR30 F) {T : Nat}
    (hc : ∀ t, T ≤ t → F t 0 = wordAt w0001 t) (n : Nat) (hn : T ≤ 4 * n) :
    colOneWord F (4 * n) = cobWord (colOneVal F (4 * n)) ∧
    (colOneVal F (4 * n), colOneVal F (4 * n + 4)) ∈ cobEdges ∧
    (colOneVal F (4 * n) = 3 → colOneVal F (4 * n + 4) = 3 →
      (∀ p φ, 1 ≤ p → p ≤ 4 → φ < 4 → F (4 * n + φ) p = ether (5 + p) (4 * n + φ)) ∧
      F (4 * n + 2) 5 = false) ∧
    (colOneVal F (4 * n) = 2 → colOneVal F (4 * n + 4) = 2 →
      (∀ p φ, 1 ≤ p → p ≤ 3 → φ < 4 → F (4 * n + φ) p = ether (6 + p) (4 * n + φ)) ∧
      F (4 * n + 2) 4 = false) := by
  have hd := cob_drive_shift hc n hn
  refine ⟨col_one_block_form hF hd, col_one_block_edge hF hd, fun h3 h3' => ?_, fun h2 h2' => ?_⟩
  · obtain ⟨hE, hW⟩ := col_one_force_three hF hd h3 h3'
    exact ⟨fun p φ h1 h2 h3 => by rw [hE p φ h1 h2 h3]; exact ether_congr rfl (by omega), hW⟩
  · obtain ⟨hE, hW⟩ := col_one_force_two hF hd h2 h2'
    exact ⟨fun p φ h1 h2 h3 => by rw [hE p φ h1 h2 h3]; exact ether_congr rfl (by omega), hW⟩

/-- **Statement (C), white phases.** If column `1` repeats with period 4 at the white times of the drive from some
time on, the block value is eventually constant `3` or constant `2`. -/
theorem column_one_white_period_four {F : Nat → Nat → Bool} (hF : IsR30 F) {T : Nat}
    (hc : ∀ t, T ≤ t → F t 0 = wordAt w0001 t)
    (hper : ∃ N, ∀ t, N ≤ t → t % 4 < 3 → F (t + 4) 1 = F t 1) :
    ∃ N, (∀ n, N ≤ n → colOneVal F (4 * n) = 3) ∨ (∀ n, N ≤ n → colOneVal F (4 * n) = 2) := by
  obtain ⟨N, hN⟩ := hper
  have step : ∀ n, N + T ≤ n →
      colOneVal F (4 * (n + 1)) = colOneVal F (4 * n) ∧ (colOneVal F (4 * n) = 2 ∨ colOneVal F (4 * n) = 3) := by
    intro n hn
    have hd := cob_drive_shift hc n (by omega)
    have hd4 : ∀ k, k ≤ 6 → F (4 * n + 4 + k) 0 = wordAt w0001 k := by
      have := cob_drive_shift hc (n + 1) (by omega)
      intro k hk; rw [← this k hk]; congr 1
    have hr : ∀ i, i < 3 → F (4 * n + 4 + i) 1 = F (4 * n + i) 1 := by
      intro i hi
      rw [show 4 * n + 4 + i = 4 * n + i + 4 by omega]
      exact hN _ (by omega) (by omega)
    rw [show 4 * (n + 1) = 4 * n + 4 by omega]
    exact cob_step hF hd hd4 hr
  have hconst' : ∀ k, colOneVal F (4 * (N + T + k)) = colOneVal F (4 * (N + T)) := by
    intro k
    induction k with
    | zero => rfl
    | succ m ih => rw [← Nat.add_assoc, (step (N + T + m) (by omega)).1, ih]
  have hconst : ∀ n, N + T ≤ n → colOneVal F (4 * n) = colOneVal F (4 * (N + T)) := by
    intro n hn
    have := hconst' (n - (N + T))
    rwa [show N + T + (n - (N + T)) = n by omega] at this
  refine ⟨N + T, ?_⟩
  rcases (step (N + T) (Nat.le_refl _)).2 with h | h
  · exact Or.inr fun n hn => (hconst n hn).trans h
  · exact Or.inl fun n hn => (hconst n hn).trans h

/-- **Statement (C).** If column `1` repeats with period 4 from some time on, the block value is eventually constant
`3` or constant `2`. -/
theorem column_one_period_four {F : Nat → Nat → Bool} (hF : IsR30 F) {T : Nat}
    (hc : ∀ t, T ≤ t → F t 0 = wordAt w0001 t)
    (hper : ∃ N, ∀ t, N ≤ t → F (t + 4) 1 = F t 1) :
    ∃ N, (∀ n, N ≤ n → colOneVal F (4 * n) = 3) ∨ (∀ n, N ≤ n → colOneVal F (4 * n) = 2) := by
  obtain ⟨N, hN⟩ := hper
  exact column_one_white_period_four hF hc ⟨N, fun t ht _ => hN t ht⟩

/-- **(C) with (B).** Under period 4 at the white phases, the aligned ether is forced at every later block: on
columns `1` to `4` with alignment `(5, 0)`, or on columns `1` to `3` with alignment `(6, 0)`, with the next column
white at phase 2. -/
theorem column_one_period_four_ether {F : Nat → Nat → Bool} (hF : IsR30 F) {T : Nat}
    (hc : ∀ t, T ≤ t → F t 0 = wordAt w0001 t)
    (hper : ∃ N, ∀ t, N ≤ t → t % 4 < 3 → F (t + 4) 1 = F t 1) :
    ∃ N, (∀ n, N ≤ n → (∀ p φ, 1 ≤ p → p ≤ 4 → φ < 4 → F (4 * n + φ) p = ether (5 + p) (4 * n + φ)) ∧
        F (4 * n + 2) 5 = false) ∨
      (∀ n, N ≤ n → (∀ p φ, 1 ≤ p → p ≤ 3 → φ < 4 → F (4 * n + φ) p = ether (6 + p) (4 * n + φ)) ∧
        F (4 * n + 2) 4 = false) := by
  obtain ⟨N, hN⟩ := column_one_white_period_four hF hc hper
  refine ⟨N + T, ?_⟩
  rcases hN with h | h
  · refine Or.inl fun n hn => (column_one_blocks hF hc n (by omega)).2.2.1 (h n (by omega)) ?_
    rw [show 4 * n + 4 = 4 * (n + 1) by omega]; exact h (n + 1) (by omega)
  · refine Or.inr fun n hn => (column_one_blocks hF hc n (by omega)).2.2.2 (h n (by omega)) ?_
    rw [show 4 * n + 4 = 4 * (n + 1) by omega]; exact h (n + 1) (by omega)

/-! ### The kit's driven half -/

theorem drv_w0001_col0 (x : Nat → Bool) : ∀ t, 0 ≤ t → drv (wordAt w0001) x t 0 = wordAt w0001 t :=
  fun t _ => drv_col0 _ x t

/-- **(A) and (B) for every right half driven by `0001`**: the kit's `drv (wordAt w0001) x`, any `x`, any block. -/
theorem drv_column_one_blocks (x : Nat → Bool) (n : Nat) :
    let F := drv (wordAt w0001) x
    colOneWord F (4 * n) = cobWord (colOneVal F (4 * n)) ∧
    (colOneVal F (4 * n), colOneVal F (4 * n + 4)) ∈ cobEdges ∧
    (colOneVal F (4 * n) = 3 → colOneVal F (4 * n + 4) = 3 →
      (∀ p φ, 1 ≤ p → p ≤ 4 → φ < 4 → F (4 * n + φ) p = ether (5 + p) (4 * n + φ)) ∧
      F (4 * n + 2) 5 = false) ∧
    (colOneVal F (4 * n) = 2 → colOneVal F (4 * n + 4) = 2 →
      (∀ p φ, 1 ≤ p → p ≤ 3 → φ < 4 → F (4 * n + φ) p = ether (6 + p) (4 * n + φ)) ∧
      F (4 * n + 2) 4 = false) :=
  column_one_blocks (drv_isR30 _ x) (drv_w0001_col0 x) n (Nat.zero_le _)

/-- **(C) for every right half driven by `0001`.** -/
theorem drv_column_one_white_period_four (x : Nat → Bool)
    (hper : ∃ N, ∀ t, N ≤ t → t % 4 < 3 → drv (wordAt w0001) x (t + 4) 1 = drv (wordAt w0001) x t 1) :
    ∃ N, (∀ n, N ≤ n → colOneVal (drv (wordAt w0001) x) (4 * n) = 3) ∨
      (∀ n, N ≤ n → colOneVal (drv (wordAt w0001) x) (4 * n) = 2) :=
  column_one_white_period_four (drv_isR30 _ x) (drv_w0001_col0 x) hper

/-! ### Every edge occurs -/

/-- All rows of `n` cells. -/
def cobAllRows : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (cobAllRows n).flatMap fun r => [false :: r, true :: r]

/-- A row of 8 cells whose cone follows the edge `e` on its first two blocks (the first one found). -/
def cobWitness (e : Nat × Nat) : List Bool :=
  ((cobAllRows 8).find? fun r => ((cobCol1 r 0).count false, (cobCol1 r 4).count false) == e).getD []

theorem cobWitness_ok : ∀ e ∈ cobEdges, (cobWitness e).length = 8 ∧
    ((cobCol1 (cobWitness e) 0).count false, (cobCol1 (cobWitness e) 4).count false) = e := by
  decide +kernel

/-- **Every edge occurs**: for each of the 13 edges, a right half supported in cells `1` to `8`, driven by `0001`
from time `0`, has blocks `0` and `1` of column `1` following that edge. So no edge can be removed from the graph. -/
theorem cob_edges_realized : ∀ e ∈ cobEdges, ∃ x : Nat → Bool, (∀ p, 8 < p → x p = false) ∧
    (colOneVal (drv (wordAt w0001) x) 0, colOneVal (drv (wordAt w0001) x) 4) = e := by
  intro e he
  obtain ⟨hl, hv⟩ := cobWitness_ok e he
  refine ⟨fun p => (cobWitness e).getD (p - 1) false, fun p hp => ?_, ?_⟩
  · show (cobWitness e).getD (p - 1) false = false
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl
  · have hd : ∀ k, k ≤ 6 → drv (wordAt w0001) (fun p => (cobWitness e).getD (p - 1) false) (0 + k) 0 =
        wordAt w0001 k := fun k _ => by rw [Nat.zero_add]; exact drv_col0 _ _ _
    have hr : rowOf (drv (wordAt w0001) (fun p => (cobWitness e).getD (p - 1) false)) 0 0 8 = cobWitness e := by
      have h1 : rowOf (drv (wordAt w0001) (fun p => (cobWitness e).getD (p - 1) false)) 0 0 8 =
          seg (fun i => (cobWitness e).getD i false) 8 := by
        unfold rowOf
        congr 1
        funext i
        rw [drv_init _ _ _ (by omega)]
        simp
      rw [h1, ← hl, seg_getD_self]
    have h0 := colOneWord_cone0 (drv_isR30 _ _) hd
    have h4 := colOneWord_cone4 (drv_isR30 _ _) hd
    rw [Nat.zero_add] at h4
    unfold colOneVal
    rw [h0, h4, hr]
    exact hv

end Rule30Open
