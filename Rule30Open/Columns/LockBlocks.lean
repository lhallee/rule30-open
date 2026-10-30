module

public import Rule30Open.Columns.LockWord

/-!
# A steering sequence forces a lock, for blocks of any period

Let column `k` repeat a block `b` of period `P` from time `T`. A window is the cells `k + 1, …, k + K`; one step of it
needs column `k` and the cell `k + K + 1`. Call a window locked at a phase when along every continuation, whatever the
cell beyond does, the column left of `k` reads one value at each phase: then that column repeats with period `P`,
and Jen's theorem on adjacent columns gives a contradiction. Here one fixed sequence of values of the cell beyond
brings every window, started at any phase, to a window whose forward closure the kernel checks to be locked. So
column `k + K + 1` never reads the sequence after time `T`. [LockWord](LockWord.md) does the same for the three words
of period four with the kit's ether-and-wall family as the lock; here the lock is computed for the block.

* **All windows at once** (`sinitP`, `goStep`, `strict`, `srunB`, `srunB_spec`). As in `LockWord`, slice `j` holds cell
  `k + j + 1` of all `P · 2^K` windows, the one started at phase `p` as `r` at bit `p · 2^K + r`, and one step is Rule
  30 on the slices, taken in one pass along them.
* **The lock** (`seedAll`, `closeAll`, `phaseDet`, `lockCheckB`). After the sequence, every window equals one of the
  listed windows of its phase (`hitsB`). BitGame's search `fwdClose`, from the listed windows of each phase, finds
  their closure under both values of the cell beyond; `fwdOk` checks that the union holds them and is closed, and
  `phaseDet` that on it the column left of `k` reads one value at each phase.
* `lockBlock_column`: in the orbit of a row with a leftmost 1, if column `k` repeats `b` from time `T` and
  `lockCheckB` holds, column `k + K + 1` does not read the sequence from any time `t₀ ≥ T`.
* `center_lockBlock`, and for an entry `Steered` at width 13 `center_lock_steered` and `not_eventually_steered`: the
  same for the center column of the single cell, and the sufficient condition it gives in the kit's form.
  [LockBlocks11](LockBlocks11.md) and [LockBlocks12](LockBlocks12.md) check the entries for 50 blocks.

The natural-language argument is `LockBlocks.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

open Ruliology.CellularAutomata

namespace LockBlocks

open BitGame LockWord

/-! ### All windows at once -/

/-- Slice `j` of all windows at the start: bit `p · 2^K + r` is bit `j` of `r`, for `P` start phases. -/
def sinitP (K P : Nat) : List Nat :=
  (List.range K).map fun j => BitGame.rep (Nat.pow 2 K) (Rule30ZeroBoundaryLanes.pat K j) P

theorem sinitP_length (K P : Nat) : (sinitP K P).length = K := by simp [sinitP]

theorem sinitP_spec (K P j g : Nat) (hj : j < K) (hg : g < P * 2 ^ K) :
    ((sinitP K P).getD j 0).testBit g = (g % 2 ^ K).testBit j := by
  unfold sinitP
  rw [getD_map_range _ _ _ _ hj]
  show (BitGame.rep (2 ^ K) (Rule30ZeroBoundaryLanes.pat K j) P).testBit g = _
  rw [BitGame.rep_testBit _ _ (BitGame.pat_lt K j hj), BitGame.pat_testBit K j _ hj,
    decide_eq_true hg, decide_eq_true (Nat.mod_lt _ (Nat.two_pow_pos K))]
  rfl

/-- One step of every window in one pass along the slices: slice `j` from slices `j - 1`, `j` and `j + 1`, with `prev`
before the first and `ub` after the last. -/
def goStep (ub : Nat) : Nat → List Nat → List Nat
  | _, [] => []
  | prev, [cur] => [Nat.xor prev (Nat.lor cur ub)]
  | prev, cur :: next :: rest => Nat.xor prev (Nat.lor cur next) :: goStep ub cur (next :: rest)

theorem goStep_length (ub : Nat) : ∀ (prev : Nat) (S : List Nat), (goStep ub prev S).length = S.length
  | _, [] => rfl
  | _, [_] => rfl
  | _, _ :: next :: rest => by
    show (goStep ub _ (next :: rest)).length + 1 = (next :: rest).length + 1
    rw [goStep_length ub _ (next :: rest)]

theorem goStep_getD (ub : Nat) : ∀ (prev : Nat) (S : List Nat) (j : Nat), j < S.length →
    (goStep ub prev S).getD j 0 = Nat.xor (if j = 0 then prev else S.getD (j - 1) 0)
      (Nat.lor (S.getD j 0) (if j + 1 = S.length then ub else S.getD (j + 1) 0))
  | _, [], j, h => absurd h (Nat.not_lt_zero j)
  | prev, [cur], j, h => by
    obtain rfl : j = 0 := by simp at h; omega
    rfl
  | prev, cur :: next :: rest, 0, _ => by
    show Nat.xor prev (Nat.lor cur next) = Nat.xor prev (Nat.lor cur (if 0 + 1 = rest.length + 2 then ub else next))
    rw [ite_eq_right (by omega)]
  | prev, cur :: next :: rest, j + 1, h => by
    have hj : j < (next :: rest).length := by simp at h ⊢; omega
    have e1 : (if j = 0 then cur else (next :: rest).getD (j - 1) 0) = (cur :: next :: rest).getD j 0 := by
      cases j with
      | zero => rfl
      | succ j => rfl
    have e2 : (j + 1 = (next :: rest).length) ↔ (j + 1 + 1 = (cur :: next :: rest).length) := by simp
    show (goStep ub cur (next :: rest)).getD j 0 =
      Nat.xor (if j + 1 = 0 then prev else (cur :: next :: rest).getD (j + 1 - 1) 0)
        (Nat.lor ((cur :: next :: rest).getD (j + 1) 0) (if j + 1 + 1 = (cur :: next :: rest).length then ub
          else (cur :: next :: rest).getD (j + 1 + 1) 0))
    rw [goStep_getD ub cur (next :: rest) j hj, e1, ite_eq_right (show ¬ (j + 1 = 0) by omega),
      show j + 1 - 1 = j by omega]
    by_cases h2 : j + 1 = (next :: rest).length
    · rw [ite_eq_left h2, ite_eq_left (e2.1 h2)]; rfl
    · rw [ite_eq_right h2, ite_eq_right (fun h3 => h2 (e2.2 h3))]; rfl

/-- `k S`, once every entry of `S` is evaluated: `all` reads each entry before the run goes on, so the kernel never
holds a chain of unevaluated steps. -/
def strict (S : List Nat) (k : List Nat → List Nat) : List Nat := cond (S.all (Nat.ble 0)) (k S) S

theorem strict_eq (S : List Nat) (k : List Nat → List Nat) : strict S k = k S := by
  have h : S.all (Nat.ble 0) = true := List.all_eq_true.2 fun x _ => by rw [Nat.ble_eq]; exact Nat.zero_le x
  unfold strict
  rw [h, Bool.cond_true]

/-- The windows after the cell beyond reads `us`, from step `i`: at step `i` the column of the window started at phase
`p` reads `b` at phase `p + i`. -/
def srunB (b : List Bool) (K N : Nat) : Nat → List Bool → List Nat → List Nat
  | _, [], S => S
  | i, u :: us, S => strict (goStep (cond u (ones N) 0) (sel (Nat.pow 2 K) (fun p => col b (p + i)) b.length) S)
      (srunB b K N (i + 1) us)

/-- One window after the cell beyond reads `us`, the column at phase `ph` first. -/
def wrunB (b : List Bool) (K : Nat) : Nat → List Bool → Nat → Nat
  | _, [], r => r
  | ph, u :: us, r => wrunB b K (ph + 1) us (GameMask.move K (col b ph) u r)

/-- The phase matters only modulo the period. -/
theorem wrunB_mod (b : List Bool) (K : Nat) : ∀ (us : List Bool) (ph ph' r : Nat), ph % b.length = ph' % b.length →
    wrunB b K ph us r = wrunB b K ph' us r
  | [], _, _, _, _ => rfl
  | u :: us, ph, ph', r, h => by
    show wrunB b K (ph + 1) us (GameMask.move K (col b ph) u r) =
      wrunB b K (ph' + 1) us (GameMask.move K (col b ph') u r)
    have hc : col b ph = col b ph' := by unfold col; rw [h]
    rw [hc]
    exact wrunB_mod b K us (ph + 1) (ph' + 1) _ (by rw [Nat.add_mod, h, ← Nat.add_mod])

/-- One step of the slices is one step of every window. -/
theorem goStep_spec (K N cm : Nat) (u : Bool) (S : List Nat) (hS0 : S.length = K) (g r : Nat) (hr : r < 2 ^ K)
    (hg : g < N) (hS : ∀ j, j < K → (S.getD j 0).testBit g = r.testBit j) (j : Nat) (hj : j < K) :
    ((goStep (cond u (ones N) 0) cm S).getD j 0).testBit g = (GameMask.move K (cm.testBit g) u r).testBit j := by
  rw [goStep_getD _ _ S j (by omega), BitGame.move_testBit K _ u r hr j hj]
  unfold BitGame.nextCell
  show ((if j = 0 then cm else S.getD (j - 1) 0) ^^^
    (S.getD j 0 ||| if j + 1 = S.length then cond u (ones N) 0 else S.getD (j + 1) 0)).testBit g = _
  rw [Nat.testBit_xor, Nat.testBit_or, hS0]
  have e1 : (if j = 0 then cm else S.getD (j - 1) 0).testBit g = (if j = 0 then cm.testBit g else r.testBit (j - 1)) := by
    by_cases h0 : j = 0
    · rw [ite_eq_left h0, ite_eq_left h0]
    · rw [ite_eq_right h0, ite_eq_right h0, hS (j - 1) (by omega)]
  have e2 : (if j + 1 = K then cond u (ones N) 0 else S.getD (j + 1) 0).testBit g =
      (if j + 1 = K then u else r.testBit (j + 1)) := by
    by_cases h1 : j + 1 = K
    · rw [ite_eq_left h1, ite_eq_left h1]
      cases u
      · simp
      · rw [Bool.cond_true, ones_testBit, decide_eq_true hg]
    · rw [ite_eq_right h1, ite_eq_right h1, hS (j + 1) (by omega)]
  rw [e1, e2, hS j hj]

/-- **The slices hold every window's run.** -/
theorem srunB_spec (b : List Bool) (K : Nat) : ∀ (us : List Bool) (i : Nat) (S : List Nat) (g r : Nat),
    S.length = K → g < b.length * 2 ^ K → r < 2 ^ K → (∀ j, j < K → (S.getD j 0).testBit g = r.testBit j) →
    ∀ j, j < K → ((srunB b K (b.length * 2 ^ K) i us S).getD j 0).testBit g =
      (wrunB b K (g / 2 ^ K + i) us r).testBit j
  | [], _, _, _, _, _, _, _, hS, j, hj => hS j hj
  | u :: us, i, S, g, r, hS0, hg, hr, hS, j, hj => by
    have hcm : (sel (Nat.pow 2 K) (fun p => col b (p + i)) b.length).testBit g = col b (g / 2 ^ K + i) := by
      rw [sel_testBit (Nat.pow 2 K) _ (Nat.two_pow_pos K)]
      show (decide (g < b.length * 2 ^ K) && col b (g / 2 ^ K + i)) = _
      rw [decide_eq_true hg, Bool.true_and]
    show ((strict (goStep (cond u (ones (b.length * 2 ^ K)) 0)
        (sel (Nat.pow 2 K) (fun p => col b (p + i)) b.length) S) (srunB b K (b.length * 2 ^ K) (i + 1) us)).getD j
          0).testBit g =
      (wrunB b K (g / 2 ^ K + i + 1) us (GameMask.move K (col b (g / 2 ^ K + i)) u r)).testBit j
    rw [strict_eq]
    rw [srunB_spec b K us (i + 1) _ g _ (by rw [goStep_length, hS0]) hg (BitGame.move_lt K _ u r)
      (fun j hj => by rw [goStep_spec K _ _ u S hS0 g r hr hg hS j hj, hcm]) j hj, Nat.add_assoc]

/-! ### Where the windows end -/

/-- Bit `g` is set when the window of bit `g` ends equal to one of the listed windows of its final phase. -/
def hitsB (b : List Bool) (K L : Nat) (S : List Nat) : List (Nat × List Nat) → Nat
  | [] => 0
  | (φ, ss) :: gs => Nat.lor
      (Nat.land (sel (Nat.pow 2 K) (fun p => Nat.beq ((p + L) % b.length) φ) b.length)
        (ss.foldr (fun s acc => Nat.lor (matchS (b.length * 2 ^ K) s S K) acc) 0))
      (hitsB b K L S gs)

theorem foldr_match_spec (N K : Nat) (S : List Nat) (g : Nat) : ∀ ss : List Nat,
    (ss.foldr (fun s acc => Nat.lor (matchS N s S K) acc) 0).testBit g = true →
      ∃ s ∈ ss, ∀ j, j < K → (S.getD j 0).testBit g = s.testBit j
  | [], h => by simp at h
  | s :: ss, h => by
    have h' : (matchS N s S K ||| ss.foldr (fun s acc => Nat.lor (matchS N s S K) acc) 0).testBit g = true := h
    rw [Nat.testBit_or, Bool.or_eq_true] at h'
    rcases h' with h1 | h1
    · exact ⟨s, List.mem_cons_self, (matchS_spec N s S g K h1).2⟩
    · obtain ⟨s', hs', hm⟩ := foldr_match_spec N K S g ss h1
      exact ⟨s', List.mem_cons_of_mem s hs', hm⟩

theorem hitsB_spec (b : List Bool) (K L : Nat) (S : List Nat) (g : Nat) : ∀ gs : List (Nat × List Nat),
    (hitsB b K L S gs).testBit g = true → ∃ e ∈ gs, (g / 2 ^ K + L) % b.length = e.1 ∧
      ∃ s ∈ e.2, ∀ j, j < K → (S.getD j 0).testBit g = s.testBit j
  | [], h => by simp [hitsB] at h
  | (φ, ss) :: gs, h => by
    have h' : ((sel (Nat.pow 2 K) (fun p => Nat.beq ((p + L) % b.length) φ) b.length &&&
        ss.foldr (fun s acc => Nat.lor (matchS (b.length * 2 ^ K) s S K) acc) 0) |||
        hitsB b K L S gs).testBit g = true := h
    rw [Nat.testBit_or, Bool.or_eq_true] at h'
    rcases h' with h1 | h1
    · rw [Nat.testBit_and, Bool.and_eq_true, sel_testBit (Nat.pow 2 K) _ (Nat.two_pow_pos K), Bool.and_eq_true] at h1
      obtain ⟨⟨_, hph⟩, hm⟩ := h1
      exact ⟨(φ, ss), List.mem_cons_self, Nat.eq_of_beq_eq_true hph, foldr_match_spec _ K S g ss hm⟩
    · obtain ⟨e', he', hrest⟩ := hitsB_spec b K L S g gs h1
      exact ⟨e', List.mem_cons_of_mem _ he', hrest⟩

/-! ### The locks -/

/-- The listed windows of phase `φ` as a table. -/
def seedT (K φ : Nat) (ss : List Nat) : Nat :=
  ss.foldr (fun s acc => Nat.lor (Nat.pow 2 (φ * 2 ^ (K + 2) + s)) acc) 0

theorem seedT_testBit (K φ : Nat) : ∀ (ss : List Nat) (s : Nat), s ∈ ss → (seedT K φ ss).testBit (φ * 2 ^ (K + 2) + s)
    = true
  | [], s, h => absurd h List.not_mem_nil
  | x :: ss, s, h => by
    show (2 ^ (φ * 2 ^ (K + 2) + x) ||| seedT K φ ss).testBit _ = true
    rw [Nat.testBit_or, Bool.or_eq_true]
    rcases List.mem_cons.1 h with rfl | h'
    · left; rw [Nat.testBit_two_pow_self]
    · right; exact seedT_testBit K φ ss s h'

/-- On `F` the column left of `k` reads one value at each phase. -/
def phaseDet (b : List Bool) (K F : Nat) : Bool :=
  (List.range b.length).all fun φ =>
    Nat.beq (Nat.land (Nat.land F (blockSel K (fun ψ => Nat.beq ψ φ) b.length)) (valMask b K)) 0 ||
      Nat.beq (Nat.land (Nat.land F (blockSel K (fun ψ => Nat.beq ψ φ) b.length))
        (Nat.xor (full b.length K) (valMask b K))) 0

theorem phaseDet_spec {b : List Bool} {K F : Nat} (h : phaseDet b K F = true) (φ r r' : Nat) (hφ : φ < b.length)
    (hr : r < 2 ^ (K + 2)) (hr' : r' < 2 ^ (K + 2)) (h1 : F.testBit (φ * 2 ^ (K + 2) + r) = true)
    (h2 : F.testBit (φ * 2 ^ (K + 2) + r') = true) :
    value b φ (φ * 2 ^ (K + 2) + r) = value b φ (φ * 2 ^ (K + 2) + r') := by
  have hB := Nat.two_pow_pos (K + 2)
  unfold phaseDet at h
  have hφ' := List.all_eq_true.1 h φ (List.mem_range.2 hφ)
  have hg := blk_lt hφ hr
  have hg' := blk_lt hφ hr'
  have hd : (φ * 2 ^ (K + 2) + r) / 2 ^ (K + 2) = φ := by
    rw [Nat.mul_comm, Nat.mul_add_div hB, Nat.div_eq_of_lt hr, Nat.add_zero]
  have hd' : (φ * 2 ^ (K + 2) + r') / 2 ^ (K + 2) = φ := by
    rw [Nat.mul_comm, Nat.mul_add_div hB, Nat.div_eq_of_lt hr', Nat.add_zero]
  have bit_of_zero : ∀ M x, Nat.beq M 0 = true → M.testBit x = false := fun M x hM => by
    rw [Nat.eq_of_beq_eq_true hM]; exact Nat.zero_testBit x
  rw [Bool.or_eq_true] at hφ'
  rcases hφ' with h0 | h0
  · -- no node of value 1 at phase `φ`
    have e1 := bit_of_zero _ (φ * 2 ^ (K + 2) + r) h0
    have e2 := bit_of_zero _ (φ * 2 ^ (K + 2) + r') h0
    have t1 : ((F &&& blockSel K (fun ψ => Nat.beq ψ φ) b.length) &&& valMask b K).testBit (φ * 2 ^ (K + 2) + r) =
      false := e1
    have t2 : ((F &&& blockSel K (fun ψ => Nat.beq ψ φ) b.length) &&& valMask b K).testBit (φ * 2 ^ (K + 2) + r') =
      false := e2
    rw [Nat.testBit_and, Nat.testBit_and, h1, blockSel_testBit, valMask_testBit _ _ _ hg, hd, decide_eq_true hg]
      at t1
    rw [Nat.testBit_and, Nat.testBit_and, h2, blockSel_testBit, valMask_testBit _ _ _ hg', hd', decide_eq_true hg']
      at t2
    simp only [Nat.beq_refl, Bool.true_and] at t1 t2
    rw [t1, t2]
  · -- no node of value 0 at phase `φ`
    have e1 := bit_of_zero _ (φ * 2 ^ (K + 2) + r) h0
    have e2 := bit_of_zero _ (φ * 2 ^ (K + 2) + r') h0
    have t1 : ((F &&& blockSel K (fun ψ => Nat.beq ψ φ) b.length) &&& (full b.length K ^^^ valMask b K)).testBit
      (φ * 2 ^ (K + 2) + r) = false := e1
    have t2 : ((F &&& blockSel K (fun ψ => Nat.beq ψ φ) b.length) &&& (full b.length K ^^^ valMask b K)).testBit
      (φ * 2 ^ (K + 2) + r') = false := e2
    rw [Nat.testBit_and, Nat.testBit_and, Nat.testBit_xor, h1, blockSel_testBit, full_testBit,
      valMask_testBit _ _ _ hg, hd, decide_eq_true hg] at t1
    rw [Nat.testBit_and, Nat.testBit_and, Nat.testBit_xor, h2, blockSel_testBit, full_testBit,
      valMask_testBit _ _ _ hg', hd', decide_eq_true hg'] at t2
    simp only [Nat.beq_refl, Bool.true_and] at t1 t2
    cases v1 : value b φ (φ * 2 ^ (K + 2) + r) <;> cases v2 : value b φ (φ * 2 ^ (K + 2) + r') <;>
      simp_all

/-- All the listed windows, of every phase, as one table. -/
def seedAll (K : Nat) (gs : List (Nat × List Nat)) : Nat :=
  gs.foldr (fun gr acc => Nat.lor (seedT K gr.1 gr.2) acc) 0

theorem seedAll_testBit (K : Nat) : ∀ (gs : List (Nat × List Nat)) (gr : Nat × List Nat) (s : Nat), gr ∈ gs →
    s ∈ gr.2 → (seedAll K gs).testBit (gr.1 * 2 ^ (K + 2) + s) = true
  | [], _, _, h, _ => absurd h List.not_mem_nil
  | x :: gs, gr, s, h, hs => by
    show (seedT K x.1 x.2 ||| seedAll K gs).testBit _ = true
    rw [Nat.testBit_or, Bool.or_eq_true]
    rcases List.mem_cons.1 h with rfl | h'
    · left; exact seedT_testBit K gr.1 gr.2 s hs
    · right; exact seedAll_testBit K gs gr s h' hs

/-- The searches from the listed windows of each phase, side by side. -/
def closeAll (b : List Bool) (K fuel A : Nat) (gs : List (Nat × List Nat)) : Nat :=
  gs.foldr (fun gr acc => Nat.lor (fwdClose b K fuel A gr.1) acc) 0

/-- **The check**: after the cell beyond reads `us`, every window, from every start phase, ends equal to a listed
window of its final phase; the listed windows lie below `2 ^ K` and their phases below the period; and the searches
from them give a set that holds them, is closed, and gives the column left of `k` one value at each phase. -/
def lockCheckB (b : List Bool) (K : Nat) (us : List Bool) (groups : List (Nat × List Nat)) (fuel : Nat) : Bool :=
  Nat.ble 1 K && Nat.ble 1 b.length &&
    Nat.beq (hitsB b K us.length (srunB b K (b.length * 2 ^ K) 0 us (sinitP K b.length)) groups)
      (ones (b.length * 2 ^ K)) &&
    groups.all (fun gr => Nat.blt gr.1 b.length && gr.2.all (fun s => Nat.blt s (Nat.pow 2 K))) &&
    fwdOk b K (seedAll K groups) (closeAll b K fuel (seedAll K groups) groups) &&
    phaseDet b K (closeAll b K fuel (seedAll K groups) groups)

end LockBlocks

open BitGame LockWord LockBlocks

/-- The window of the true row after the cell beyond reads `us`. -/
theorem codeFrom_wrunB (init : Int → Bool) (b : List Bool) (K : Nat) (k : Int) (T shift : Nat)
    (h : ∀ t : Nat, T ≤ t → evolve init t k = col b (t + shift)) :
    ∀ (us : List Bool) (t0 : Nat), T ≤ t0 →
      (∀ i, i < us.length → evolve init (t0 + i) (k + 1 + (K : Int)) = us.getD i false) →
      codeFrom init (t0 + us.length) (k + 1) K = wrunB b K (t0 + shift) us (codeFrom init t0 (k + 1) K)
  | [], t0, _, _ => rfl
  | u :: us, t0, ht0, hu => by
    have hstep : codeFrom init (t0 + 1) (k + 1) K = GameMask.move K (col b (t0 + shift)) u (codeFrom init t0 (k + 1) K)
        := by
      rw [codeFrom_succ, GameMask.move_eq, show k + 1 - 1 = k by omega, h t0 ht0]
      congr 1
      have e := hu 0 (by simp)
      rw [Nat.add_zero] at e
      exact e
    have ih := codeFrom_wrunB init b K k T shift h us (t0 + 1) (by omega) (fun i hi => by
      have e := hu (i + 1) (by simp; omega)
      rw [show t0 + 1 + i = t0 + (i + 1) by omega, e]
      rfl)
    rw [show t0 + (u :: us).length = t0 + 1 + us.length by simp; omega, ih, hstep,
      show t0 + 1 + shift = t0 + shift + 1 by omega]
    rfl

/-- **A steering sequence forces a lock.** In the orbit of a row with a leftmost 1, let column `k` repeat the block
`b` from time `T`. If `lockCheckB` holds for `b`, `K` and `us`, the cell `k + K + 1` does not read `us` from any time
`t₀ ≥ T`. -/
theorem lockBlock_column (init : Int → Bool) (m : Int) (hm : init m = true) (hz : ∀ x : Int, x < m → init x = false)
    (b : List Bool) (K : Nat) (us : List Bool) (groups : List (Nat × List Nat)) (fuel : Nat)
    (hc : lockCheckB b K us groups fuel = true) (k : Int) (T shift : Nat)
    (h : ∀ t : Nat, T ≤ t → evolve init t k = col b (t + shift)) (t0 : Nat) (ht0 : T ≤ t0)
    (hu : ∀ i, i < us.length → evolve init (t0 + i) (k + 1 + (K : Int)) = us.getD i false) : False := by
  unfold lockCheckB at hc
  simp only [Bool.and_eq_true, Nat.ble_eq, List.all_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨hK, hP⟩, hhit⟩, hgroups⟩, hok⟩, hdet⟩ := hc
  have hB := Nat.two_pow_pos (K + 2)
  have hBK := Nat.two_pow_pos K
  have hKB : 2 ^ K < 2 ^ (K + 2) := Nat.pow_lt_pow_right (by decide) (by omega)
  let P := b.length
  let phase : Nat → Nat := fun t => (t + shift) % P
  let code : Nat → Nat := fun t => codeFrom init t (k + 1) K
  have hcode : ∀ t, code t < 2 ^ K := fun t => codeFrom_lt init t K (k + 1)
  have hpos : ∀ t, pos init b K k shift t = phase t * 2 ^ (K + 2) + code t := fun t => rfl
  -- the window after the sequence, from the slices
  let L := us.length
  let p := phase t0
  let g := p * 2 ^ K + code t0
  have hp : p < P := Nat.mod_lt _ hP
  have hg : g < P * 2 ^ K := by
    have : p * 2 ^ K + 2 ^ K ≤ P * 2 ^ K := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hp
    have := hcode t0
    omega
  have hgdiv : g / 2 ^ K = p := by
    show (p * 2 ^ K + code t0) / 2 ^ K = p
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hBK, Nat.div_eq_of_lt (hcode t0), Nat.zero_add]
  have hgmod : g % 2 ^ K = code t0 := by
    show (p * 2 ^ K + code t0) % 2 ^ K = code t0
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (hcode t0)]
  have hwin : code (t0 + L) = wrunB b K (g / 2 ^ K + 0) us (code t0) := by
    show codeFrom init (t0 + us.length) (k + 1) K = _
    rw [codeFrom_wrunB init b K k T shift h us t0 ht0 hu, hgdiv, Nat.add_zero]
    exact wrunB_mod b K us _ _ _ (by show (t0 + shift) % P = (t0 + shift) % P % P; rw [Nat.mod_mod])
  have hsl := srunB_spec b K us 0 (sinitP K P) g (code t0) (sinitP_length K P) hg (hcode t0)
    (fun j hj => by rw [sinitP_spec K P j g hj hg, hgmod])
  have hall : (hitsB b K L (srunB b K (P * 2 ^ K) 0 us (sinitP K P)) groups).testBit g = true := by
    rw [Nat.eq_of_beq_eq_true hhit, ones_testBit, decide_eq_true hg]
  obtain ⟨e, he, hph, s, hs, hbits⟩ := hitsB_spec b K L _ g groups hall
  -- the true window is the listed window `s`, at the group's phase
  have hcodeL : code (t0 + L) = s := by
    have hsK : s < 2 ^ K := by
      have h' := (hgroups e he).2 s hs
      rw [Nat.blt_eq] at h'
      exact h'
    apply Nat.eq_of_testBit_eq
    intro j
    by_cases hj : j < K
    · rw [hwin, ← hsl j hj, hbits j hj]
    · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (hcode _) (Nat.pow_le_pow_right (by decide) (by omega))),
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hsK (Nat.pow_le_pow_right (by decide) (by omega)))]
  have hphase : phase (t0 + L) = e.1 := by
    rw [← hph, hgdiv]
    show (t0 + us.length + shift) % P = ((t0 + shift) % P + us.length) % P
    rw [Nat.mod_add_mod, show t0 + us.length + shift = t0 + shift + us.length by omega]
  -- the closure of the listed windows holds the play from then on
  unfold fwdOk at hok
  simp only [Bool.and_eq_true] at hok
  obtain ⟨hseed0, hclosed⟩ := hok
  let A := seedAll K groups
  let F := closeAll b K fuel A groups
  have hseed : ∀ g, (post b K A).testBit g = true → F.testBit g = true := fun g hg' => by
    have e := Nat.eq_of_beq_eq_true hseed0
    have this : (F ||| post b K A).testBit g = F.testBit g := by
      rw [show (F ||| post b K A) = Nat.lor F (post b K A) from rfl, e]
    rw [Nat.testBit_or, hg', Bool.or_true] at this
    exact this.symm
  have hA : A.testBit (pos init b K k shift (t0 + L)) = true := by
    rw [hpos, hphase, hcodeL]
    exact seedAll_testBit K groups e s he hs
  have hF := play_fwd init b K hK k T shift hP h A F hseed hclosed (t0 + L) (by omega) hA
  -- so the column left of `k` reads one value at each phase from then on
  have hleft : ∀ t, T ≤ t → evolve init t (k - 1) = value b (phase t) (code t) := fun t ht => by
    rw [left_cell init t k, h (t + 1) (by omega), h t ht]
    unfold value col
    have e1 : (t + 1 + shift) % P = (phase t + 1) % P := by
      show _ = ((t + shift) % P + 1) % P
      rw [mod_succ_mod, show t + 1 + shift = t + shift + 1 by omega]
    have e2 : (t + shift) % P = phase t % P := by
      show _ = (t + shift) % P % P; rw [Nat.mod_mod]
    rw [e1, e2, testBit_codeFrom, decide_eq_true (by omega), Bool.true_and, show k + 1 + ((0 : Nat) : Int) = k + 1 by
      omega]
  have hvalue : ∀ t, value b (phase t) (code t) = value b (phase t) (phase t * 2 ^ (K + 2) + code t) := fun t => by
    unfold value; rw [testBit_zero_blk]
  have hconst : ∀ t1 t2, t0 + L + 1 ≤ t1 → t0 + L + 1 ≤ t2 → phase t1 = phase t2 →
      value b (phase t1) (code t1) = value b (phase t2) (code t2) := by
    intro t1 t2 h1 h2 e12
    have f1 := hF (t1 - (t0 + L + 1))
    have f2 := hF (t2 - (t0 + L + 1))
    rw [show t0 + L + 1 + (t1 - (t0 + L + 1)) = t1 by omega, hpos] at f1
    rw [show t0 + L + 1 + (t2 - (t0 + L + 1)) = t2 by omega, hpos, ← e12] at f2
    rw [hvalue t1, hvalue t2, ← e12]
    exact phaseDet_spec hdet (phase t1) (code t1) (code t2) (Nat.mod_lt _ hP) (by have := hcode t1; omega)
      (by have := hcode t2; omega) f1 f2
  have hphase' : ∀ t, phase (t + P) = phase t := fun t => by
    show (t + P + shift) % P = (t + shift) % P
    rw [show t + P + shift = t + shift + P by omega, Nat.add_mod_right]
  exact adjacent_columns init m hm hz (k - 1) (t0 + L + 1 + T) P hP
    (fun t ht => by
      rw [hleft (t + P) (by omega), hleft t (by omega)]
      exact hconst _ _ (by omega) (by omega) (hphase' t))
    (fun t ht => by
      rw [show k - 1 + 1 = k by omega, h (t + P) (by omega), h t (by omega)]
      unfold col
      rw [show t + P + shift = t + shift + P by omega, Nat.add_mod_right])

/-- **The center column of the single cell**: if it repeats `b` from time `T`, read from phase `shift`, and `lockCheckB`
holds for `b`, `K` and the `L` values at the bits of `n`, column `K + 1` does not read them from any time `t₀ ≥ T`. -/
theorem center_lockBlock (b : List Bool) (K n L : Nat) (groups : List (Nat × List Nat)) (fuel : Nat)
    (hc : lockCheckB b K (bitsOf n L) groups fuel = true) (T shift : Nat)
    (h : ∀ t : Nat, T ≤ t → Rule30Prize.center t = b.getD ((t + shift) % b.length) false) (t0 : Nat) (ht0 : T ≤ t0) :
    ∃ i, i < L ∧ Rule30Jen.cell (t0 + i) ((K : Int) + 1) ≠ n.testBit i := by
  refine Classical.byContradiction fun hne => ?_
  refine lockBlock_column single 0 rfl (fun x hx => decide_eq_false (by omega)) b K (bitsOf n L) groups fuel hc 0 T
    shift (fun t ht => ?_) t0 ht0 fun i hi => ?_
  · rw [evolve_single_center, h t ht]
    unfold col
    rw [bit_eq_getD]
  · rw [bitsOf_length] at hi
    rw [bitsOf_getD n L i hi, evolve_single_eq_cell, show (0 : Int) + 1 + (K : Int) = (K : Int) + 1 by omega]
    exact Classical.byContradiction fun h' => hne ⟨i, hi, h'⟩

namespace LockBlocks

/-- A block `wordOf period bits` with a steering sequence for width 13, value `i` at bit `i` of `seq`, of `len` values,
and the windows where it leaves each start, by final phase. -/
structure Steered where
  period : Nat
  bits : Nat
  seq : Nat
  len : Nat
  groups : List (Nat × List Nat)

/-- `lockCheckB` for the entry at width 13, with search fuel 300. -/
def Steered.check (e : Steered) : Bool :=
  lockCheckB (Rule30StripCertificateTable.wordOf e.period e.bits) 13 (bitsOf e.seq e.len) e.groups 300

end LockBlocks

/-- **An entry whose check passes**: once the center column repeats its block from time `T`, read from phase `shift`,
column 14 does not read the entry's sequence from any time `t₀ ≥ T`. -/
theorem center_lock_steered (e : Steered) (hc : e.check = true) (T shift : Nat)
    (h : ∀ t : Nat, T ≤ t → Rule30Prize.center t =
      (Rule30StripCertificateTable.wordOf e.period e.bits).getD ((t + shift) % e.period) false) (t0 : Nat)
    (ht0 : T ≤ t0) : ∃ i, i < e.len ∧ Rule30Jen.cell (t0 + i) 14 ≠ e.seq.testBit i :=
  center_lockBlock _ 13 e.seq e.len e.groups 300 hc T shift
    (fun t ht => by rw [h t ht, Rule30StripCertificateTable.wordOf_length]) t0 ht0

/-- **A sufficient condition**, in the kit's form: if column 14 reads the entry's sequence at arbitrarily late times, the
center column does not eventually repeat the entry's block (`Rule30StripCertificates.EventuallyWord`). -/
theorem not_eventually_steered (e : Steered) (hc : e.check = true)
    (hw : ∀ N, ∃ t0, N ≤ t0 ∧ ∀ i, i < e.len → Rule30Jen.cell (t0 + i) 14 = e.seq.testBit i) :
    ¬ Rule30StripCertificates.EventuallyWord (Rule30StripCertificateTable.wordOf e.period e.bits) := by
  have hP : 0 < (Rule30StripCertificateTable.wordOf e.period e.bits).length := by
    have hc' := hc
    unfold Steered.check lockCheckB at hc'
    simp only [Bool.and_eq_true, Nat.ble_eq] at hc'
    exact hc'.1.1.1.1.2
  rintro ⟨T, hT⟩
  obtain ⟨t0, ht0, hr⟩ := hw T
  obtain ⟨i, hi, hne⟩ := center_lock_steered e hc T (e.period * T - T) (fun t ht => by
    rw [Rule30StripCertificateTable.wordOf_length] at hP
    rw [← evolve_single_center, evolve_single_eq_cell]
    show Rule30Jen.cell t 0 = _
    have hLT : T ≤ e.period * T := Nat.le_mul_of_pos_left T hP
    rw [hT t ht, Rule30StripCertificateTable.wordOf_length,
      show t + (e.period * T - T) = t - T + e.period * T by omega, Nat.add_mul_mod_self_left]) t0 ht0
  exact hne (hr i hi)

end Rule30Open
