module

public import Rule30Open.Foundations.Evolve
public import Rule30Open.Foundations.Official
public import Rule30Open.Foundations.RightHalf
public import Rule30Open.Columns.AdjacentColumns

/-!
# A finite game on the cells right of a column

A column `k` that repeats a block from time `T` drives the cells right of it. Keep cells `k + 1 .. k + K`
and let cell `k + K + 1` be anything at each step: every real row is one play of this game (`game_cells`).
A certificate ranks the game's nodes (phase, cells) so that no move lowers the rank, a move from a
transient rank raises it, and at every other rank column `k - 1`, which the rule reads off the node
(`left_cell`), is a function of the phase. Along a real row the rank then settles (`settles`), so column
`k - 1` repeats with the block, and `adjacent_columns` rules the block out (`game_column`).

`GameCert.check` checks a certificate by computation, and `computations/game.py` builds them. The two
certificates here rule out the blocks 01111111 and 00000011, which the long-runs theorem does not reach
(`center_not_01111111`, `center_not_00000011`). The kit excludes both blocks by certificates of its own
(`Rule30StripCertificates.not_eventually_01111111` and `not_eventually_00000011`); these are independent
proofs, and the game reaches every column of every row with a leftmost 1, not only the center.

The natural-language argument is `FiniteGame.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

open Ruliology.CellularAutomata

/-- The game's move: the cells `x .. x + K - 1` one step later, from those cells, the cell `c` left of them and the
cell `u` right of them now. -/
def gameStep (c : Bool) (cells : List Bool) (u : Bool) : List Bool := driveStep c (cells ++ [u])

/-- The cells as a number, cell `x + i` at bit `i`. -/
def cellsCode (cells : List Bool) : Nat := cells.foldr (fun b acc => 2 * acc + if b then 1 else 0) 0

/-- Column `k - 1` at a node, from column `k` now (`c`) and next (`c'`) and the first of the cells. -/
def leftValue (c c' : Bool) (cells : List Bool) : Bool := xor c' (c || cells.headD false)

/-- Entry `i` of a list of bits, false past its end. -/
def bit : List Bool → Nat → Bool
  | [], _ => false
  | a :: _, 0 => a
  | _ :: rest, i + 1 => bit rest i

/-- Bit `i` of `n`. -/
def flag (n i : Nat) : Bool := n / 2 ^ i % 2 == 1

/-- A certificate for a block: its width, a rank below 256 for each node (phase, cells), the transient ranks, and
column `k - 1` at each other rank and phase, all packed in numbers: the rank of the node `phase * 2 ^ width +
cellsCode cells` in 8 bits from bit 8 times the node, whether rank `r` is transient at bit `r`, and the value at
rank `r` and `phase` at bit `r * period + phase`. -/
structure GameCert where
  block : List Bool
  width : Nat
  ranks : Nat
  transient : Nat
  values : Nat

namespace GameCert

def rank (g : GameCert) (phase : Nat) (cells : List Bool) : Nat :=
  g.ranks / 2 ^ (8 * (phase * 2 ^ g.width + cellsCode cells)) % 256

def center (g : GameCert) (phase : Nat) : Bool := bit g.block (phase % g.block.length)

def moveOk (g : GameCert) (phase : Nat) (cells : List Bool) (u : Bool) : Bool :=
  if flag g.transient (g.rank phase cells) then
    decide (g.rank phase cells < g.rank ((phase + 1) % g.block.length) (gameStep (g.center phase) cells u))
  else
    decide (g.rank phase cells ≤ g.rank ((phase + 1) % g.block.length) (gameStep (g.center phase) cells u))

def nodeOk (g : GameCert) (phase : Nat) (cells : List Bool) : Bool :=
  g.moveOk phase cells false && g.moveOk phase cells true &&
    (flag g.transient (g.rank phase cells) ||
      flag g.values (g.rank phase cells * g.block.length + phase) ==
        leftValue (g.center phase) (g.center (phase + 1)) cells)

/-- Every node of the game passes. -/
def check (g : GameCert) : Bool :=
  (List.range g.block.length).all fun phase => (allLists g.width).all fun cells => g.nodeOk phase cells

end GameCert

/-- Every real row is a play: the cells `x .. x + K - 1` one step later are the game's move from cell `x - 1` and the
real cell `x + K`. -/
theorem game_cells (init : Int → Bool) (t K : Nat) (x : Int) :
    cellsFrom init (t + 1) x K = gameStep (evolve init t (x - 1)) (cellsFrom init t x K) (evolve init t (x + K)) := by
  show cellsFrom init (t + 1) x K = driveStep (evolve init t (x - 1)) (cellsFrom init t x K ++ [evolve init t (x + K)])
  rw [← cellsFrom_succ, driveStep_cells]

theorem mod_succ_mod (a n : Nat) : (a % n + 1) % n = (a + 1) % n := by
  rw [Nat.add_mod (a % n) 1 n, Nat.mod_mod, ← Nat.add_mod]

/-- A rank that never falls and is bounded settles. -/
theorem settles (f : Nat → Nat) (B : Nat) (bound : ∀ t, f t ≤ B) :
    ∀ n T, B - f T ≤ n → (∀ t, T ≤ t → f t ≤ f (t + 1)) → ∃ t1, T ≤ t1 ∧ ∀ t, t1 ≤ t → f t = f t1 := by
  intro n
  induction n with
  | zero =>
    intro T hroom hmono
    refine ⟨T, Nat.le_refl _, fun t ht => ?_⟩
    have up : ∀ d, f T ≤ f (T + d) := fun d => by
      induction d with
      | zero => exact Nat.le_refl _
      | succ d ih => exact Nat.le_trans ih (hmono (T + d) (by omega))
    have h1 := up (t - T)
    rw [show T + (t - T) = t by omega] at h1
    have h2 := bound t
    omega
  | succ n ih =>
    intro T hroom hmono
    by_cases hflat : ∀ t, T ≤ t → f t = f T
    · exact ⟨T, Nat.le_refl _, hflat⟩
    · have ⟨t', ht', hne⟩ : ∃ t', T ≤ t' ∧ f t' ≠ f T :=
        Classical.byContradiction fun hno => hflat fun t ht => Classical.byContradiction fun hne => hno ⟨t, ht, hne⟩
      have up : ∀ d, f T ≤ f (T + d) := fun d => by
        induction d with
        | zero => exact Nat.le_refl _
        | succ d ih => exact Nat.le_trans ih (hmono (T + d) (by omega))
      have hgt : f T < f t' := by
        have h1 := up (t' - T)
        rw [show T + (t' - T) = t' by omega] at h1
        omega
      obtain ⟨t1, ht1, hconst⟩ := ih t' (by have := bound t'; omega) fun t ht => hmono t (by omega)
      exact ⟨t1, by omega, hconst⟩

/-- No column of the orbit of a row with a leftmost 1 repeats, from some time on, a block that has a certificate. -/
theorem game_column (init : Int → Bool) (m : Int) (hm : init m = true) (hz : ∀ x : Int, x < m → init x = false)
    (g : GameCert) (hg : g.check = true) (hP : 0 < g.block.length) (hw : 0 < g.width) (k : Int) (T shift : Nat)
    (h : ∀ t : Nat, T ≤ t → evolve init t k = g.center (t + shift)) : False := by
  let phase : Nat → Nat := fun t => (t + shift) % g.block.length
  let cells : Nat → List Bool := fun t => cellsFrom init t (k + 1) g.width
  have hcenter : ∀ t, T ≤ t → evolve init t k = g.center (phase t) := fun t ht => by
    rw [h t ht]
    show bit g.block ((t + shift) % g.block.length) = bit g.block ((t + shift) % g.block.length % g.block.length)
    rw [Nat.mod_mod]
  have hnext : ∀ t, g.center (phase t + 1) = g.center (phase (t + 1)) := fun t => by
    show bit g.block (((t + shift) % g.block.length + 1) % g.block.length) =
      bit g.block ((t + 1 + shift) % g.block.length % g.block.length)
    rw [Nat.mod_mod, mod_succ_mod, show t + 1 + shift = t + shift + 1 by omega]
  have hphase : ∀ t, phase (t + 1) = (phase t + 1) % g.block.length := fun t => by
    show (t + 1 + shift) % g.block.length = ((t + shift) % g.block.length + 1) % g.block.length
    rw [mod_succ_mod, show t + 1 + shift = t + shift + 1 by omega]
  have hperiod : ∀ t, phase (t + g.block.length) = phase t := fun t => by
    show (t + g.block.length + shift) % g.block.length = (t + shift) % g.block.length
    rw [show t + g.block.length + shift = t + shift + g.block.length by omega, Nat.add_mod_right]
  have node : ∀ t, g.nodeOk (phase t) (cells t) = true := fun t => by
    have hall := List.all_eq_true.mp hg (phase t) (List.mem_range.mpr (Nat.mod_lt _ hP))
    have hlen : (cells t).length = g.width := length_cellsFrom init t _ _
    exact List.all_eq_true.mp hall (cells t) (hlen ▸ mem_allLists (cells t))
  have step : ∀ t, T ≤ t → cells (t + 1) =
      gameStep (g.center (phase t)) (cells t) (evolve init t (k + 1 + g.width)) := fun t ht => by
    show cellsFrom init (t + 1) (k + 1) g.width = _
    rw [game_cells init t g.width (k + 1), show k + 1 - 1 = k by omega, hcenter t ht]
  let R : Nat → Nat := fun t => g.rank (phase t) (cells t)
  have rise : ∀ t, T ≤ t → (flag g.transient (R t) = true → R t < R (t + 1)) ∧ R t ≤ R (t + 1) := fun t ht => by
    have hmove : g.moveOk (phase t) (cells t) (evolve init t (k + 1 + g.width)) = true := by
      have hn := node t
      simp only [GameCert.nodeOk, Bool.and_eq_true] at hn
      cases evolve init t (k + 1 + g.width)
      · exact hn.1.1
      · exact hn.1.2
    have hR : R (t + 1) = g.rank ((phase t + 1) % g.block.length)
        (gameStep (g.center (phase t)) (cells t) (evolve init t (k + 1 + g.width))) := by
      show g.rank (phase (t + 1)) (cells (t + 1)) = _
      rw [hphase t, step t ht]
    rw [hR]
    show (flag g.transient (g.rank (phase t) (cells t)) = true → _) ∧ _
    unfold GameCert.moveOk at hmove
    cases htr : flag g.transient (g.rank (phase t) (cells t)) with
    | true =>
      simp only [htr, ite_true, decide_eq_true_eq] at hmove
      exact ⟨fun _ => hmove, Nat.le_of_lt hmove⟩
    | false =>
      simp only [htr, Bool.false_eq_true, ite_false, decide_eq_true_eq] at hmove
      exact ⟨fun hf => Bool.noConfusion hf, hmove⟩
  have bound : ∀ t, R t ≤ 255 := fun t => Nat.le_of_lt_succ (Nat.mod_lt _ (by decide))
  obtain ⟨t1, ht1, hconst⟩ := settles R _ bound _ T (Nat.le_refl _) fun t ht => (rise t ht).2
  have stable : flag g.transient (R t1) = false := by
    cases htr : flag g.transient (R t1) with
    | false => rfl
    | true =>
      have hlt := (rise t1 ht1).1 htr
      rw [hconst (t1 + 1) (by omega)] at hlt
      exact absurd hlt (Nat.lt_irrefl _)
  have left : ∀ t, t1 ≤ t → evolve init t (k - 1) = flag g.values (R t1 * g.block.length + phase t) := fun t ht => by
    have hn := node t
    simp only [GameCert.nodeOk, Bool.and_eq_true, Bool.or_eq_true] at hn
    have hv := hn.2
    have hRt : g.rank (phase t) (cells t) = R t1 := hconst t ht
    rw [hRt, stable] at hv
    have hv' : flag g.values (R t1 * g.block.length + phase t) =
        leftValue (g.center (phase t)) (g.center (phase t + 1)) (cells t) := by
      cases hv with
      | inl hf => exact Bool.noConfusion hf
      | inr hb => exact beq_iff_eq.mp hb
    rw [hv', left_cell init t k, hcenter (t + 1) (by omega), hcenter t (by omega), hnext t]
    show xor (g.center (phase (t + 1))) (g.center (phase t) || evolve init t (k + 1)) =
      xor (g.center (phase (t + 1))) (g.center (phase t) || (cellsFrom init t (k + 1) g.width).headD false)
    rw [headD_cellsFrom init t (k + 1) g.width hw]
  exact adjacent_columns init m hm hz (k - 1) t1 g.block.length hP
    (fun t ht => by rw [left (t + g.block.length) (by omega), left t ht, hperiod t])
    (fun t ht => by
      rw [show k - 1 + 1 = k by omega, hcenter (t + g.block.length) (by omega), hcenter t (by omega), hperiod t])

/-- The block 01111111 at width 5, from `game_certificate("01111111", 5)` in `computations/game.py`. -/
def cert01111111 : GameCert where
  block := [false, true, true, true, true, true, true, true]
  width := 5
  ranks := 0x1b1b0802001b1b061b1b000a001b1b141b1b0802001b0006041b000a001b1b14121b0802001b1b06121b001b001b1b1b121b0802001b0006041b001b001b1b1b1b1b1b02001b1b061b1b0010001b1b1b1b101b02001b0006041b0010001b1b1b1b1b0e02001b0e1b1b1b001b001b061b1b1b0e02001b001b041b001b001b061b1b121b02001b1b0c1b12001b001b1b0c1b1b1b020012000c1b12001b001b1b040208021b00101b1b0a02001b00101b1b02081b0c0006001b0a02001b00101b1b1b0c02081b00061b1b0c0a001b000e1b180c02081b0006001b040a001b000e1b0c1b0802001b16060c1b000a001b161b0c1b0802001b0006041b000a001b161b
  transient := 0x5555555
  values := 0x81000000000000000000000000000000000000000000000000000000

/-- The block 00000011 at width 6, from `game_certificate("00000011", 6)` in `computations/game.py`. -/
def cert00000011 : GameCert where
  block := [false, false, false, false, false, false, true, true]
  width := 6
  ranks := 0x3220335001e030c1b030035002d1b1203221b35000900181b03003500241b3500220335001e1b0c1b000035001b0012030f1b350009001b0603003500221b353503350318000c030318350035001b1835033518090022000318350035002a183500350315000c180018350018001b000f0335180900220003063500350022182203350322000c030315350035001215270335150900350003153500350035152200350322000c15001535001500120018033515090035000306350035003515350335033500150303123500350022123503351209002400031235003500351235002a0335001512001235002a0022000f0335120900220003063500350035123503350322000c03032735002700350f3503350f12003500032735002700350f3500350322000c0f00273500270035002203350f12003500030635002700350f35032d03350022030324350035001b0c3503242409003500030f35003500240c350035033500220c00241500240022003503242409003500030f35003500240c1521030c2700352122211200350035091809030c2400350022062100350035092100030c35000321002112002a00350018090321220035002406210035003509351e1e03000c151e3527001e001e351e351e1b03002100093524001e0022350600301e03001e15033500001e0012001e351e0f03002100093522000600223506
  transient := 0x9249249249249
  values := 0x9f0000000000000000000000000000000000009e00000000000000000000000000000000000000000000000000000000000000000000

theorem cert01111111_check : cert01111111.check = true := by decide +kernel

theorem cert00000011_check : cert00000011.check = true := by decide +kernel

/-- No column of the single seed's orbit repeats 01111111, in any rotation, from some time on. -/
theorem single_not_01111111 (k : Int) (T shift : Nat)
    (h : ∀ t : Nat, T ≤ t → evolve single t k = cert01111111.center (t + shift)) : False :=
  game_column single 0 rfl (fun x hx => decide_eq_false (by omega)) cert01111111 cert01111111_check (by decide)
    (by decide) k T shift h

/-- No column of the single seed's orbit repeats 00000011, in any rotation, from some time on. -/
theorem single_not_00000011 (k : Int) (T shift : Nat)
    (h : ∀ t : Nat, T ≤ t → evolve single t k = cert00000011.center (t + shift)) : False :=
  game_column single 0 rfl (fun x hx => decide_eq_false (by omega)) cert00000011 cert00000011_check (by decide)
    (by decide) k T shift h

/-- Official form: the center column does not repeat 01111111, in any rotation, from some time on. -/
theorem center_not_01111111 (T shift : Nat)
    (h : ∀ t : Nat, T ≤ t → Rule30Prize.center t = cert01111111.center (t + shift)) : False :=
  single_not_01111111 0 T shift fun t ht => (evolve_single_center t).trans (h t ht)

/-- Official form: the center column does not repeat 00000011, in any rotation, from some time on. -/
theorem center_not_00000011 (T shift : Nat)
    (h : ∀ t : Nat, T ≤ t → Rule30Prize.center t = cert00000011.center (t + shift)) : False :=
  single_not_00000011 0 T shift fun t ht => (evolve_single_center t).trans (h t ht)

end Rule30Open
