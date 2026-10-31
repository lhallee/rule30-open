module

public import Rule30Open.Columns.MissedTraps
public import Rule30Open.Columns.ElevenTraps
public import Rule30Open.Columns.TwelveTraps
public import Rule30Open.Columns.FourteenTraps
public import Rule30Open.Columns.CensusTraps13
public import Rule30Open.Columns.CensusTraps14
public import Rule30Open.Columns.CensusTraps15

/-!
# Refuting entry from the few windows that can reach a trap

A trap of [WordTraps](WordTraps.md) reduces its block to entry (`WTrap.Absorption`). [MissedTraps](MissedTraps.md)
refutes entry with a closed set of windows apart from the trap. Some traps fail the test of reach only in a game wider
than any closed set apart from them that the kernel can hold, and there the nodes that can reach the trap can be few.
This module refutes entry with those nodes instead. A set of windows that holds the trap's states, cut to its width,
and every window with a move into one of its own, holds every node that can reach the trap, so a right half whose first
cells start outside it never has them in a state of the trap. The method is checked here on the census trap of
`000001010110101` of MissedTraps, which 123 of the 3,840 nodes of the game of 8 cells can reach.

* `back`, `pre`, `pre_move`: the rule is permutive in its left cell, so the old window is fixed by the new one, its
  last cell and the cell beyond it, cell by cell from the right; `pre` computes it with the column's value it needs.
* `WinSet`, `WinSet.mem`, `WinSet.mem_spec`: windows of `K` cells by label modulo the block's period, each label's
  windows packed in increasing order, and membership by binary search, sound because it compares at the index found.
* `WinSet.backOK`: every window with a move into window `i` of label `l` is in the set at the label before.
* `not_absorption_back`: such a set that holds the trap's states, and a window outside it, refute entry into the trap.
* `WinSet.avoids`, `not_absorption_fwd`: when instead few nodes cannot reach the trap, a closed set among them refutes
  entry, as `not_absorption` of MissedTraps does, with separation checked against the trap's states cut to a set of
  windows (`WinSet.holds`), a few per label, instead of against every state of the trap.

The natural-language argument is `ReachRefuted.md`, beside this file.
-/

@[expose] public section

-- Sequential elaboration: the kernel checks would otherwise run in parallel and stack their memory.
set_option Elab.async false

namespace Rule30Open

open Ruliology.CellularAutomata BitGame

/-- The old window from the new window `v`, from the top cell down: `hi` is old bit `i`, `hi2` old bit `i + 1` (the
cell beyond for the top bit), and `acc` the old bits from `i` up. Returns the old window and the column's value that
the rule needs at bit 0. -/
def back (v : Nat) : Nat → Bool → Bool → Nat → Nat × Bool
  | 0, hi, hi2, acc => (acc, v.testBit 0 ^^ (hi || hi2))
  | i + 1, hi, hi2, acc =>
    back v i (v.testBit (i + 1) ^^ (hi || hi2)) hi (acc ||| (v.testBit (i + 1) ^^ (hi || hi2)).toNat <<< i)

/-- The old window of `K` cells with last cell `last` that moves to `v` when the cell beyond is `z`, and the column's
value the move needs. -/
def pre (K v : Nat) (last z : Bool) : Nat × Bool := back v (K - 1) last z (last.toNat <<< (K - 1))

/-- The bits of `r` from `i` up are those from `i + 1` up and bit `i`. -/
theorem shift_or_bit (r i : Nat) : (r >>> (i + 1)) <<< (i + 1) ||| (r.testBit i).toNat <<< i = (r >>> i) <<< i := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftRight, Nat.testBit_shiftLeft,
    Rule30StripCertificates.testBit_toNat, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  by_cases h1 : i + 1 ≤ j
  · rw [decide_eq_true h1, decide_eq_true (by omega : i ≤ j), decide_eq_false (by omega : ¬ j - i = 0)]
    simp only [Bool.true_and, Bool.false_and, Bool.or_false]
    congr 1
    omega
  · rw [decide_eq_false h1, Bool.false_and, Bool.false_or]
    by_cases h2 : i ≤ j
    · have hj : j = i := by omega
      subst hj
      simp
    · rw [decide_eq_false h2]
      simp

/-- Walked down from bit `i` of a move of `r`, with bits `i` and `i + 1` of `r` and its bits from `i` up, `back` returns
`r` and the column's value of the move. -/
theorem back_spec (K : Nat) (c z : Bool) (r : Nat) (hr : r < 2 ^ K) :
    ∀ i, i < K → back (Rule30StripCertificates.stripStep K c z r) i (r.testBit i)
      (if i + 1 = K then z else r.testBit (i + 1)) ((r >>> i) <<< i) = (r, c)
  | 0, hK => by
    simp only [back, Nat.shiftRight_zero, Nat.shiftLeft_zero]
    rw [Rule30StripCertificates.testBit_stripStep K c z r hr 0 hK, ite_eq_left rfl]
    simp only [Rule30Jen.rule]
    cases c <;> cases (r.testBit 0) <;> cases (if 0 + 1 = K then z else r.testBit (0 + 1)) <;> rfl
  | i + 1, hK => by
    have hv := Rule30StripCertificates.testBit_stripStep K c z r hr (i + 1) hK
    have hlo : ((Rule30StripCertificates.stripStep K c z r).testBit (i + 1) ^^
        (r.testBit (i + 1) || if i + 1 + 1 = K then z else r.testBit (i + 1 + 1))) = r.testBit i := by
      rw [hv, ite_eq_right (show ¬ (i + 1 = 0) by omega), Nat.add_sub_cancel]
      simp only [Rule30Jen.rule]
      cases r.testBit i <;> cases r.testBit (i + 1) <;>
        cases (if i + 1 + 1 = K then z else r.testBit (i + 1 + 1)) <;> rfl
    simp only [back]
    rw [hlo, shift_or_bit]
    have h := back_spec K c z r hr i (by omega)
    rwa [ite_eq_right (show ¬ i + 1 = K by omega)] at h

/-- **The old window from the new one.** -/
theorem pre_move (K : Nat) (hK : 0 < K) (c z : Bool) (r : Nat) (hr : r < 2 ^ K) :
    pre K (Rule30StripCertificates.stripStep K c z r) (r.testBit (K - 1)) z = (r, c) := by
  have h := back_spec K c z r hr (K - 1) (by omega)
  rw [ite_eq_left (show K - 1 + 1 = K by omega)] at h
  have hacc : (r >>> (K - 1)) <<< (K - 1) = (r.testBit (K - 1)).toNat <<< (K - 1) := by
    congr 1
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_shiftRight, Rule30StripCertificates.testBit_toNat]
    by_cases hj : j = 0
    · subst hj
      simp
    · rw [decide_eq_false hj, Bool.false_and]
      exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hr (Nat.pow_le_pow_right (by decide) (by omega)))
  rw [hacc] at h
  exact h

/-- The label before that of `a + 1`, modulo `m`, is that of `a`. -/
theorem pred_label (a m : Nat) (hm : 0 < m) : ((a + 1) % m + m - 1) % m = a % m := by
  rcases Nat.lt_or_ge m 2 with h1 | h1
  · have : m = 1 := by omega
    subst this
    simp
  have hr : a % m < m := Nat.mod_lt _ hm
  have h2 : (a + 1) % m = (a % m + 1) % m := by
    rw [Nat.add_mod, Nat.mod_eq_of_lt (show 1 < m by omega)]
  rcases Nat.lt_or_ge (a % m + 1) m with h | h
  · rw [h2, Nat.mod_eq_of_lt h, show a % m + 1 + m - 1 = a % m + m by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hr]
  · have h3 : a % m + 1 = m := by omega
    rw [h2, h3, Nat.mod_self, show 0 + m - 1 = a % m by omega, Nat.mod_eq_of_lt hr]

/-- Windows of `K` cells beside a column that repeats `b`, by label modulo its period: at label `l`, `sizes[l]`
windows packed in `rows[l]`, `K` bits each, in increasing order. -/
structure WinSet where
  b : List Bool
  K : Nat
  sizes : List Nat
  rows : List Nat

namespace WinSet

variable (S : WinSet)

def cnt (l : Nat) : Nat := S.sizes.getD l 0

def win (l i : Nat) : Nat := (S.rows.getD l 0 >>> (S.K * i)) % 2 ^ S.K

/-- The least index in `[lo, hi)` whose window at label `l` is at least `w`, in `f` halvings. -/
def find (l w : Nat) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | f + 1, lo, hi =>
    if lo < hi then
      if S.win l ((lo + hi) / 2) < w then find l w f ((lo + hi) / 2 + 1) hi else find l w f lo ((lo + hi) / 2)
    else lo

def memAt (l w i : Nat) : Bool := decide (i < S.cnt l) && S.win l i == w

/-- Window `w` is in the set at label `l`. -/
def mem (l w : Nat) : Bool := S.memAt l w (S.find l w 64 0 (S.cnt l))

theorem mem_spec {l w : Nat} (h : S.mem l w = true) : ∃ i, i < S.cnt l ∧ S.win l i = w := by
  unfold mem memAt at h
  rw [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact ⟨_, h.1, h.2⟩

/-- A window moving to `v` with last cell `last` and the cell beyond `z`, when the column reads `c` before, is in the
set at label `l`. -/
def predOK (l : Nat) (c : Bool) (v : Nat) (last z : Bool) : Bool :=
  !((pre S.K v last z).2 == c) || S.mem l (pre S.K v last z).1

/-- Every window with a move into window `i` of label `l` is in the set at the label before. -/
def backOK (l i : Nat) : Bool :=
  S.predOK ((l + S.b.length - 1) % S.b.length) (col S.b ((l + S.b.length - 1) % S.b.length)) (S.win l i) false false &&
  S.predOK ((l + S.b.length - 1) % S.b.length) (col S.b ((l + S.b.length - 1) % S.b.length)) (S.win l i) false true &&
  S.predOK ((l + S.b.length - 1) % S.b.length) (col S.b ((l + S.b.length - 1) % S.b.length)) (S.win l i) true false &&
  S.predOK ((l + S.b.length - 1) % S.b.length) (col S.b ((l + S.b.length - 1) % S.b.length)) (S.win l i) true true

/-- **The check**: every window of every label is closed under predecessors. -/
def check : Bool :=
  decide (0 < S.K) && decide (0 < S.b.length) &&
    Rule30EtherThree.allBelowT (fun l => Rule30EtherThree.allBelowT (S.backOK l) (S.cnt l)) S.b.length

/-- The states of the trap `C`, cut to `K` cells, with their labels modulo the period, are in the set. -/
def holds (C : WTrap) : Bool :=
  Rule30EtherThree.allBelowT (fun j => S.mem (C.lab j % S.b.length) (C.st j % 2 ^ S.K)) C.n

/-- Window `w` is not in the set at label `l`. -/
def misses (l w : Nat) : Bool :=
  decide (l < S.b.length) && decide (w < 2 ^ S.K) && Rule30EtherThree.allBelowT (fun i => !(S.win l i == w)) (S.cnt l)

theorem allBelowT_of_forall {p : Nat → Bool} :
    ∀ {n}, (∀ i, i < n → p i = true) → Rule30EtherThree.allBelowT p n = true
  | 0, _ => rfl
  | n + 1, h => by
    rw [Rule30EtherThree.allBelowT, Bool.and_eq_true]
    exact ⟨h n (by omega), allBelowT_of_forall (fun i hi => h i (by omega))⟩

/-- `p` holds at `lo + c - 1, …, lo`, walked from the top as `Rule30EtherThree.allBelowT` walks its range. -/
def allRangeT (p : Nat → Bool) (lo : Nat) : Nat → Bool
  | 0 => true
  | c + 1 => p (lo + c) && allRangeT p lo c

theorem allRangeT_spec {p : Nat → Bool} {lo : Nat} :
    ∀ {c}, allRangeT p lo c = true → ∀ i, lo ≤ i → i < lo + c → p i = true
  | 0, _, i, _, h2 => absurd h2 (by omega)
  | c + 1, h, i, h1, h2 => by
    rw [allRangeT, Bool.and_eq_true] at h
    by_cases hin : i < lo + c
    · exact allRangeT_spec h.2 i h1 hin
    · rw [show i = lo + c by omega]
      exact h.1

/-- Parts of `c` from `0` to `c q` and a last one of `r` cover the range below `c q + r`. -/
theorem allRange_cover {p : Nat → Bool} {c q r : Nat} (hc : 0 < c)
    (h : ∀ k, k < q → allRangeT p (c * k) c = true) (hr : allRangeT p (c * q) r = true) :
    ∀ i, i < c * q + r → p i = true := by
  intro i hi
  by_cases hq : i < c * q
  · have hk : i / c < q := (Nat.div_lt_iff_lt_mul hc).mpr (by rw [Nat.mul_comm]; exact hq)
    have h1 : c * (i / c) ≤ i := Nat.mul_div_le i c
    have h2 : i < c * (i / c) + c := by
      have := Nat.div_add_mod i c
      have := Nat.mod_lt i hc
      omega
    exact allRangeT_spec (h (i / c) hk) i h1 h2
  · exact allRangeT_spec hr i (by omega) hi

/-- The check from one check per label, for sets too large for one kernel check. -/
theorem check_of_labels (hK : 0 < S.K) (hP : 0 < S.b.length)
    (h : ∀ l, l < S.b.length → Rule30EtherThree.allBelowT (S.backOK l) (S.cnt l) = true) : S.check = true := by
  unfold check
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨hK, hP⟩, allBelowT_of_forall h⟩

theorem backOK_spec {l i : Nat} (h : S.backOK l i = true) (last z : Bool) :
    S.predOK ((l + S.b.length - 1) % S.b.length) (col S.b ((l + S.b.length - 1) % S.b.length)) (S.win l i) last z
      = true := by
  unfold backOK at h
  simp only [Bool.and_eq_true] at h
  cases last <;> cases z
  · exact h.1.1.1
  · exact h.1.1.2
  · exact h.1.2
  · exact h.2

end WinSet

/-- The windows of `K` cells of a driven right half, step by step from `w0`. -/
def winSeq (F : Nat → Nat → Bool) (K w0 : Nat) : Nat → Nat
  | 0 => w0
  | s + 1 => Rule30StripCertificates.stripStep K (F s 0) (F s (0 + 1 + K)) (winSeq F K w0 s)

theorem winSeq_enc {F : Nat → Nat → Bool} (hF : Rule30Ether.IsR30 F) {K w0 : Nat}
    (h0 : Rule30EtherThree.EncF F K 0 0 w0) : ∀ s, Rule30EtherThree.EncF F K s 0 (winSeq F K w0 s)
  | 0 => h0
  | s + 1 => Rule30EtherThree.encF_step hF (winSeq_enc hF h0 s)

/-- **A set closed under predecessors that holds a trap's states refutes entry into it.** If `S` holds the states of
the trap `C` cut to its `K ≤ C.K` cells, with their labels modulo the period, and every window with a move into one of
its windows, then the right half whose first `K` cells are a window `w0` missing from `S` at label `l0`, white beyond,
driven from phase `l0`, never has its first `C.K` cells in a state of `C`. -/
theorem not_absorption_back (C : WTrap) (S : WinSet) (hb : S.b = C.b) (hK : S.K ≤ C.K) (hS : S.check = true)
    (hin : S.holds C = true) (l0 w0 : Nat) (hout : S.misses l0 w0 = true) : ¬ C.Absorption := by
  intro hA
  unfold WinSet.check at hS
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hS
  obtain ⟨⟨hK0, hP⟩, hall⟩ := hS
  unfold WinSet.misses at hout
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hout
  obtain ⟨⟨hl0, hw0⟩, hmiss⟩ := hout
  have hback : ∀ l, l < S.b.length → ∀ i, i < S.cnt l → S.backOK l i = true := fun l hl i hi =>
    Rule30EtherThree.allBelowT_spec (Rule30EtherThree.allBelowT_spec hall l hl) i hi
  -- The right half: `w0`, white beyond.
  let x : Nat → Bool := fun q => decide (1 ≤ q) && w0.testBit (q - 1)
  have hfin : ∀ q, S.K < q → x q = false := by
    intro q hq
    show (decide (1 ≤ q) && w0.testBit (q - 1)) = false
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hw0 (Nat.pow_le_pow_right (by decide) (by omega))),
      Bool.and_false]
  obtain ⟨t1, i, hi, hph, hr⟩ := hA x S.K hfin l0
  let c : Nat → Bool := fun t => C.b.getD ((t + l0) % C.b.length) false
  let F := Rule30Ether.drv c x
  have h0 : Rule30EtherThree.EncF F S.K 0 0 w0 := by
    refine ⟨hw0, fun k hk => ?_⟩
    show _ = Rule30Ether.drv c x 0 (0 + 1 + k)
    rw [Rule30Ether.drv_init c x (0 + 1 + k) (by omega)]
    show _ = (decide (1 ≤ 0 + 1 + k) && w0.testBit (0 + 1 + k - 1))
    rw [decide_eq_true (by omega), Bool.true_and, show 0 + 1 + k - 1 = k by omega]
  have henc := winSeq_enc (Rule30Ether.drv_isR30 c x) h0
  -- At the entry time the first `S.K` cells are the trap's state cut to them.
  have hcut : winSeq F S.K w0 t1 = C.st i % 2 ^ S.K := by
    apply Nat.eq_of_testBit_eq
    intro k
    by_cases hk : k < S.K
    · rw [Nat.testBit_mod_two_pow, decide_eq_true hk, Bool.true_and, (henc t1).2 k hk, hr.2 k (by omega)]
    · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (henc t1).1 (Nat.pow_le_pow_right (by decide) (by omega))),
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
          (Nat.pow_le_pow_right (by decide) (by omega)))]
  -- Backward from the entry time, every window of the half is in `S`.
  have hm : S.b.length = C.b.length := by rw [hb]
  have key : ∀ d, d ≤ t1 → ∃ j, j < S.cnt ((l0 + (t1 - d)) % S.b.length) ∧
      S.win ((l0 + (t1 - d)) % S.b.length) j = winSeq F S.K w0 (t1 - d) := by
    intro d
    induction d with
    | zero =>
      intro _
      have h := S.mem_spec (Rule30EtherThree.allBelowT_spec hin i hi)
      rw [Nat.sub_zero, hcut, Nat.add_comm l0 t1, hm, hph, ← hm]
      exact h
    | succ d ih =>
      intro hd
      obtain ⟨j, hj, hwin⟩ := ih (by omega)
      have hs : t1 - d = (t1 - (d + 1)) + 1 := by omega
      rw [hs] at hj hwin
      generalize t1 - (d + 1) = s at hj hwin ⊢
      have hlab : ((l0 + (s + 1)) % S.b.length + S.b.length - 1) % S.b.length = (l0 + s) % S.b.length := by
        rw [← Nat.add_assoc]
        exact pred_label (l0 + s) S.b.length hP
      have hok := S.backOK_spec (hback _ (Nat.mod_lt _ hP) j hj) ((winSeq F S.K w0 s).testBit (S.K - 1))
        (F s (0 + 1 + S.K))
      rw [hlab, hwin] at hok
      have hpre := pre_move S.K hK0 (F s 0) (F s (0 + 1 + S.K)) (winSeq F S.K w0 s) (henc s).1
      have hcol : col S.b ((l0 + s) % S.b.length) = F s 0 := by
        show col S.b ((l0 + s) % S.b.length) = Rule30Ether.drv c x s 0
        rw [Rule30Ether.drv_col0]
        show col S.b ((l0 + s) % S.b.length) = C.b.getD ((s + l0) % C.b.length) false
        unfold col
        rw [bit_eq_getD, Nat.mod_mod, hb, Nat.add_comm l0 s]
      unfold WinSet.predOK at hok
      simp only [winSeq] at hok
      rw [hpre, hcol] at hok
      simp only [beq_self_eq_true, Bool.not_true, Bool.false_or] at hok
      exact S.mem_spec hok
  obtain ⟨j, hj, hwin⟩ := key t1 (Nat.le_refl _)
  rw [Nat.sub_self, Nat.add_zero, Nat.mod_eq_of_lt hl0] at hj hwin
  have h := Rule30EtherThree.allBelowT_spec hmiss j hj
  simp only [hwin, Bool.not_eq_eq_eq_not, Bool.not_true, beq_eq_false_iff_ne, ne_eq] at h
  exact h rfl

/-- No state of the closed set `S`, cut to the set's `K` cells, is a window of the set at the label of the same phase:
a check of each state of `S` against the few windows of its label. -/
def WinSet.avoids (T : WinSet) (S : WTrap) : Bool :=
  Rule30EtherThree.allBelowT (fun j => Rule30EtherThree.allBelowT
    (fun i => !(T.win (S.lab j % T.b.length) i == S.st j % 2 ^ T.K)) (T.cnt (S.lab j % T.b.length))) S.n

/-- **A closed set that avoids a set holding a trap's states refutes entry into it.** If `S` is a closed set of windows
for the block of the trap `C` (`WTrap.closedCheck` of [MissedTraps](MissedTraps.md)), and `T` a set of windows no
wider than either that holds the states of `C` cut to it (`WinSet.holds`) and that no state of `S`, cut to it, meets at
the label of the same phase (`WinSet.avoids`), the right half whose first `S.K` cells are state `0` of `S`, white
beyond, driven from the phase of that state's label, never enters `C`. -/
theorem not_absorption_fwd (C S : WTrap) (T : WinSet) (hS : S.closedCheck = true) (hb : S.b = C.b)
    (hTb : T.b = C.b) (hTS : T.K ≤ S.K) (hTC : T.K ≤ C.K) (hin : T.holds C = true) (hav : T.avoids S = true)
    (h0 : 0 < S.n) : ¬ C.Absorption := by
  intro hA
  unfold WTrap.closedCheck at hS
  rw [Bool.and_eq_true, decide_eq_true_eq] at hS
  obtain ⟨hm, hall⟩ := hS
  have hdvd : S.b.length ∣ S.m := Nat.dvd_of_mod_eq_zero hm
  have hok : ∀ j, j < S.n → S.lab j < S.m ∧ S.edgeOK j false = true ∧ S.edgeOK j true = true := by
    intro j hj
    have h := Rule30EtherThree.allBelowT_spec hall j hj
    unfold WTrap.closedOK at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1.1, h.1.2, h.2⟩
  have hedge : ∀ j, j < S.n → ∀ z : Bool, S.nxt j z < S.n ∧
      S.st (S.nxt j z) = GameMask.move S.K (col S.b (S.lab j)) z (S.st j) ∧
      S.lab (S.nxt j z) = (S.lab j + 1) % S.m := by
    intro j hj z
    have h : S.edgeOK j z = true := by
      cases z
      · exact (hok j hj).2.1
      · exact (hok j hj).2.2
    unfold WTrap.edgeOK at h
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    exact ⟨h.1.1, h.1.2, h.2⟩
  have hlt : ∀ j, S.st j < 2 ^ S.K := fun j => Nat.mod_lt _ (Nat.two_pow_pos _)
  -- The right half: state `0` of `S`, white beyond.
  let x : Nat → Bool := fun q => decide (1 ≤ q) && (S.st 0).testBit (q - 1)
  have hfin : ∀ q, S.K < q → x q = false := by
    intro q hq
    show (decide (1 ≤ q) && (S.st 0).testBit (q - 1)) = false
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (hlt 0) (Nat.pow_le_pow_right (by decide) (by omega))),
      Bool.and_false]
  obtain ⟨t1, i, hi, hph, hr⟩ := hA x S.K hfin (S.lab 0)
  let c : Nat → Bool := fun t => C.b.getD ((t + S.lab 0) % C.b.length) false
  -- Its first `S.K` cells stay in `S`.
  have inv : ∀ s, ∃ j, j < S.n ∧ Rule30EtherThree.EncF (Rule30Ether.drv c x) S.K s 0 (S.st j) ∧
      S.lab j = (S.lab 0 + s) % S.m := by
    intro s
    induction s with
    | zero =>
      refine ⟨0, h0, ⟨hlt 0, fun k hk => ?_⟩, by rw [Nat.add_zero, Nat.mod_eq_of_lt (hok 0 h0).1]⟩
      rw [Rule30Ether.drv_init c x (0 + 1 + k) (by omega)]
      show _ = (decide (1 ≤ 0 + 1 + k) && (S.st 0).testBit (0 + 1 + k - 1))
      rw [decide_eq_true (by omega), Bool.true_and, show 0 + 1 + k - 1 = k by omega]
    | succ s ih =>
      obtain ⟨j, hj, henc, hlab⟩ := ih
      obtain ⟨hn, hst, hl⟩ := hedge j hj (Rule30Ether.drv c x s (0 + 1 + S.K))
      refine ⟨_, hn, ?_, ?_⟩
      · have hcol : col S.b (S.lab j) = Rule30Ether.drv c x s 0 := by
          rw [Rule30Ether.drv_col0]
          show col S.b (S.lab j) = C.b.getD ((s + S.lab 0) % C.b.length) false
          unfold col
          rw [bit_eq_getD, hlab, Nat.mod_mod_of_dvd _ hdvd, hb, Nat.add_comm (S.lab 0) s]
        rw [hst, GameMask.move_eq, hcol]
        exact Rule30EtherThree.encF_step (Rule30Ether.drv_isR30 c x) henc
      · rw [hl, hlab, Nat.mod_add_mod, Nat.add_assoc]
  obtain ⟨j, hj, henc, hlab⟩ := inv t1
  -- The state of the trap and that state of `S`, both cut to `T.K` cells, agree, with labels of the same phase.
  have hcut : C.st i % 2 ^ T.K = S.st j % 2 ^ T.K := by
    apply Nat.eq_of_testBit_eq
    intro k
    rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
    by_cases hk : k < T.K
    · rw [decide_eq_true hk, Bool.true_and, Bool.true_and, hr.2 k (by omega), henc.2 k (by omega)]
    · rw [decide_eq_false hk, Bool.false_and, Bool.false_and]
  have hphase : C.lab i % T.b.length = S.lab j % T.b.length := by
    rw [hTb, hlab, Nat.mod_mod_of_dvd _ (by rw [← hb]; exact hdvd), ← hph, Nat.add_comm t1 (S.lab 0)]
  obtain ⟨k, hk, hwin⟩ := T.mem_spec (Rule30EtherThree.allBelowT_spec hin i hi)
  rw [hcut, hphase] at hwin
  rw [hphase] at hk
  have h := Rule30EtherThree.allBelowT_spec (Rule30EtherThree.allBelowT_spec hav j hj) k hk
  simp [hwin] at h

/-! ### The sets, from `python -m computations.lock_chain --lean-back` -/

/-- The windows of 8 cells from which the trap `cen000001010110101` can be reached, by label: 123 of the 3,840 nodes of the game. -/
def back_cen000001010110101 : WinSet :=
  { b := [false, false, false, false, false, true, false, true, false, true, true, false, true, false, true], K := 8,
    sizes := [2, 7, 8, 12, 14, 10, 7, 7, 10, 9, 7, 6, 10, 10, 4],
    rows := [48252,
      61575427218618912,
      17351146090586122016,
      77353009413575456493272176648,
      5028202834352312458242496489000712,
      1090010940512139301622018,
      65261012410391098,
      61303856420305191,
      1175238504422133128379681,
      4518571198387741476108,
      66656343767850007,
      264757629176615,
      1180161047453125362980872,
      1166088133187621903736078,
      2774869267] }

theorem back_cen000001010110101_0_0 : WinSet.allRangeT (back_cen000001010110101.backOK 0) (1024 * 0) 2 = true := by
  decide +kernel

theorem back_cen000001010110101_0 : Rule30EtherThree.allBelowT (back_cen000001010110101.backOK 0) (back_cen000001010110101.cnt 0) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 2) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen000001010110101_0_0 i (by have h : i < 2 := hi; omega)

theorem back_cen000001010110101_1_0 : WinSet.allRangeT (back_cen000001010110101.backOK 1) (1024 * 0) 7 = true := by
  decide +kernel

theorem back_cen000001010110101_1 : Rule30EtherThree.allBelowT (back_cen000001010110101.backOK 1) (back_cen000001010110101.cnt 1) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 7) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen000001010110101_1_0 i (by have h : i < 7 := hi; omega)

theorem back_cen000001010110101_2_0 : WinSet.allRangeT (back_cen000001010110101.backOK 2) (1024 * 0) 8 = true := by
  decide +kernel

theorem back_cen000001010110101_2 : Rule30EtherThree.allBelowT (back_cen000001010110101.backOK 2) (back_cen000001010110101.cnt 2) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 8) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen000001010110101_2_0 i (by have h : i < 8 := hi; omega)

theorem back_cen000001010110101_3_0 : WinSet.allRangeT (back_cen000001010110101.backOK 3) (1024 * 0) 12 = true := by
  decide +kernel

theorem back_cen000001010110101_3 : Rule30EtherThree.allBelowT (back_cen000001010110101.backOK 3) (back_cen000001010110101.cnt 3) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 12) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen000001010110101_3_0 i (by have h : i < 12 := hi; omega)

theorem back_cen000001010110101_4_0 : WinSet.allRangeT (back_cen000001010110101.backOK 4) (1024 * 0) 14 = true := by
  decide +kernel

theorem back_cen000001010110101_4 : Rule30EtherThree.allBelowT (back_cen000001010110101.backOK 4) (back_cen000001010110101.cnt 4) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 14) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen000001010110101_4_0 i (by have h : i < 14 := hi; omega)

theorem back_cen000001010110101_5_0 : WinSet.allRangeT (back_cen000001010110101.backOK 5) (1024 * 0) 10 = true := by
  decide +kernel

theorem back_cen000001010110101_5 : Rule30EtherThree.allBelowT (back_cen000001010110101.backOK 5) (back_cen000001010110101.cnt 5) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 10) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen000001010110101_5_0 i (by have h : i < 10 := hi; omega)

theorem back_cen000001010110101_6_0 : WinSet.allRangeT (back_cen000001010110101.backOK 6) (1024 * 0) 7 = true := by
  decide +kernel

theorem back_cen000001010110101_6 : Rule30EtherThree.allBelowT (back_cen000001010110101.backOK 6) (back_cen000001010110101.cnt 6) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 7) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen000001010110101_6_0 i (by have h : i < 7 := hi; omega)

theorem back_cen000001010110101_7_0 : WinSet.allRangeT (back_cen000001010110101.backOK 7) (1024 * 0) 7 = true := by
  decide +kernel

theorem back_cen000001010110101_7 : Rule30EtherThree.allBelowT (back_cen000001010110101.backOK 7) (back_cen000001010110101.cnt 7) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 7) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen000001010110101_7_0 i (by have h : i < 7 := hi; omega)

theorem back_cen000001010110101_8_0 : WinSet.allRangeT (back_cen000001010110101.backOK 8) (1024 * 0) 10 = true := by
  decide +kernel

theorem back_cen000001010110101_8 : Rule30EtherThree.allBelowT (back_cen000001010110101.backOK 8) (back_cen000001010110101.cnt 8) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 10) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen000001010110101_8_0 i (by have h : i < 10 := hi; omega)

theorem back_cen000001010110101_9_0 : WinSet.allRangeT (back_cen000001010110101.backOK 9) (1024 * 0) 9 = true := by
  decide +kernel

theorem back_cen000001010110101_9 : Rule30EtherThree.allBelowT (back_cen000001010110101.backOK 9) (back_cen000001010110101.cnt 9) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 9) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen000001010110101_9_0 i (by have h : i < 9 := hi; omega)

theorem back_cen000001010110101_10_0 : WinSet.allRangeT (back_cen000001010110101.backOK 10) (1024 * 0) 7 = true := by
  decide +kernel

theorem back_cen000001010110101_10 : Rule30EtherThree.allBelowT (back_cen000001010110101.backOK 10) (back_cen000001010110101.cnt 10) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 7) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen000001010110101_10_0 i (by have h : i < 7 := hi; omega)

theorem back_cen000001010110101_11_0 : WinSet.allRangeT (back_cen000001010110101.backOK 11) (1024 * 0) 6 = true := by
  decide +kernel

theorem back_cen000001010110101_11 : Rule30EtherThree.allBelowT (back_cen000001010110101.backOK 11) (back_cen000001010110101.cnt 11) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 6) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen000001010110101_11_0 i (by have h : i < 6 := hi; omega)

theorem back_cen000001010110101_12_0 : WinSet.allRangeT (back_cen000001010110101.backOK 12) (1024 * 0) 10 = true := by
  decide +kernel

theorem back_cen000001010110101_12 : Rule30EtherThree.allBelowT (back_cen000001010110101.backOK 12) (back_cen000001010110101.cnt 12) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 10) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen000001010110101_12_0 i (by have h : i < 10 := hi; omega)

theorem back_cen000001010110101_13_0 : WinSet.allRangeT (back_cen000001010110101.backOK 13) (1024 * 0) 10 = true := by
  decide +kernel

theorem back_cen000001010110101_13 : Rule30EtherThree.allBelowT (back_cen000001010110101.backOK 13) (back_cen000001010110101.cnt 13) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 10) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen000001010110101_13_0 i (by have h : i < 10 := hi; omega)

theorem back_cen000001010110101_14_0 : WinSet.allRangeT (back_cen000001010110101.backOK 14) (1024 * 0) 4 = true := by
  decide +kernel

theorem back_cen000001010110101_14 : Rule30EtherThree.allBelowT (back_cen000001010110101.backOK 14) (back_cen000001010110101.cnt 14) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 4) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen000001010110101_14_0 i (by have h : i < 4 := hi; omega)

theorem back_cen000001010110101_check : back_cen000001010110101.check = true :=
  WinSet.check_of_labels _ (by decide) (by decide) fun l hl =>
    match l, hl with
    | 0, _ => back_cen000001010110101_0
    | 1, _ => back_cen000001010110101_1
    | 2, _ => back_cen000001010110101_2
    | 3, _ => back_cen000001010110101_3
    | 4, _ => back_cen000001010110101_4
    | 5, _ => back_cen000001010110101_5
    | 6, _ => back_cen000001010110101_6
    | 7, _ => back_cen000001010110101_7
    | 8, _ => back_cen000001010110101_8
    | 9, _ => back_cen000001010110101_9
    | 10, _ => back_cen000001010110101_10
    | 11, _ => back_cen000001010110101_11
    | 12, _ => back_cen000001010110101_12
    | 13, _ => back_cen000001010110101_13
    | 14, _ => back_cen000001010110101_14
    | _ + 15, h => absurd h (by show ¬ _ < 15; omega)

theorem back_cen000001010110101_holds : back_cen000001010110101.holds cen000001010110101 = true := by decide +kernel

/-- **Some finitely supported right half driven by `000001010110101` never enters `cen000001010110101`.** -/
theorem cen000001010110101_not_absorption_back : ¬ cen000001010110101.Absorption :=
  not_absorption_back _ back_cen000001010110101 rfl (by decide) back_cen000001010110101_check back_cen000001010110101_holds 0 0 (by decide +kernel)

/-- The windows of 22 cells from which the trap `tw0_40` can be reached, by label: 544 of the 50,331,648 nodes of the game. -/
def back_tw0_40 : WinSet :=
  { b := [false, false, false, true, false, false, true, true, false, true, false, true], K := 22,
    sizes := [128, 61, 27, 37, 17, 48, 48, 43, 37, 28, 12, 58],
    rows := [50061943449795237698146480379542418372333839183269049124422882428162923077217931798990910449781313220011254950092802838625916080326085526056290416074647444656526332130141369966313842608539029786972571259743683775801166458439461463891907770889373822502124868435995425611973011096598729932430292353562291738702803030391489443855831663915168617472905267310487715314435792722560262552663960809504786023849637006086636938800393899551602769767353373322772041074099423366656183428424806422568297266956014217821207337569874360371667813880140385239903738328163424030576866495151655304549662834076240150215549059458164371291075280032125489124535318483977493638782241743816544535188775846832605236502197956497806771592613679343985422714168523694999526118691113506667693384721851360672770772288374644443997446374898382893052010032365858024612376760139496045521,
      95360696446704733470920222033081015600708675416934395285934807871347881564252036638249538962553613909864370723116002384465277230740140392738402194880607674611920619554284407890781377683721062611808792050710828106606362310636509972171300749473737145111653679082298942730644584998723107887984161592769846084127763764361371862669211877488974596195430772863701064873357183002759458071742417371044100295379035,
      64316940895309269936502307473925558102034960063241491365203681348603904004793476242876869936710726356912413881658450459696877955247795540970284064857401467447335562417069078150345,
      106658223938262957337536793324640826774142136874495168156003835851626747695891986524145857829255311146237140433184393264573379249192771071294259599458687456619798175440991571970006291894917384820334173816334198295170999741245765068233976817190783,
      38199053929493162994938802648210155435651532342677285340431132852657019180787767834808621836271765908610405861632,
      770571927503522822658462918008406715306964433057162494971645265748868591736637639255530031255678538889512953640641614256483390708714443988809535245255783185222438753537548261904749465164089181277391095470018133723109748404046595513133260764287602394896806768426154660696890584190286866889004465606163862337683871252352,
      767544117193769775674100816444555161250652481784486206752230853489888431860603034478862497271477109216301904314497491387521753284344163876430589582620442359091442254158621450256305147835088252749877726462566941031193484814854351141433603970831273020589351690400944278051101045432043299811592428307406582586553856442560,
      589048301148027296386061228856625045255134329115095789418054442304246197775199690461990618886708453053976553246810697496112801026511038255188935778627694537064039914637602183507004283114596659857862622356252607576799153147832333164432178757422192737922439015915297555419610596960690529,
      106389497530543559419272060331726632417592697879746993845695734145125860321980297715552935598591670793464139138407526845062917898266009710168003676478705104504570826590222332127696449283430197822399833120428366692852009493718197316257041679987506,
      262878031209411418866320957390675891484578687517862981472325520647985801381132499519599425766506293160546440831484931541234270792922154227278600640546788842685581973169458876505584295391,
      28857820162406616692365575280764805626260542919961209553637922353822392016716864,
      1283918869847829696802754019238217839143890105602485301789803720500692090844424841666961831393195613032866871063655751724369550004778472570027362172203783963057369501937347583215480746818065076465631839683230806530666533395409520035888197342158045577625921757782446892021416771913114691730350745612757634367245036189548243905185872322672890081115982411899573210649798077019634047949054] }

theorem back_tw0_40_0_0 : WinSet.allRangeT (back_tw0_40.backOK 0) (1024 * 0) 128 = true := by
  decide +kernel

theorem back_tw0_40_0 : Rule30EtherThree.allBelowT (back_tw0_40.backOK 0) (back_tw0_40.cnt 0) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 128) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_tw0_40_0_0 i (by have h : i < 128 := hi; omega)

theorem back_tw0_40_1_0 : WinSet.allRangeT (back_tw0_40.backOK 1) (1024 * 0) 61 = true := by
  decide +kernel

theorem back_tw0_40_1 : Rule30EtherThree.allBelowT (back_tw0_40.backOK 1) (back_tw0_40.cnt 1) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 61) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_tw0_40_1_0 i (by have h : i < 61 := hi; omega)

theorem back_tw0_40_2_0 : WinSet.allRangeT (back_tw0_40.backOK 2) (1024 * 0) 27 = true := by
  decide +kernel

theorem back_tw0_40_2 : Rule30EtherThree.allBelowT (back_tw0_40.backOK 2) (back_tw0_40.cnt 2) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 27) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_tw0_40_2_0 i (by have h : i < 27 := hi; omega)

theorem back_tw0_40_3_0 : WinSet.allRangeT (back_tw0_40.backOK 3) (1024 * 0) 37 = true := by
  decide +kernel

theorem back_tw0_40_3 : Rule30EtherThree.allBelowT (back_tw0_40.backOK 3) (back_tw0_40.cnt 3) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 37) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_tw0_40_3_0 i (by have h : i < 37 := hi; omega)

theorem back_tw0_40_4_0 : WinSet.allRangeT (back_tw0_40.backOK 4) (1024 * 0) 17 = true := by
  decide +kernel

theorem back_tw0_40_4 : Rule30EtherThree.allBelowT (back_tw0_40.backOK 4) (back_tw0_40.cnt 4) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 17) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_tw0_40_4_0 i (by have h : i < 17 := hi; omega)

theorem back_tw0_40_5_0 : WinSet.allRangeT (back_tw0_40.backOK 5) (1024 * 0) 48 = true := by
  decide +kernel

theorem back_tw0_40_5 : Rule30EtherThree.allBelowT (back_tw0_40.backOK 5) (back_tw0_40.cnt 5) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 48) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_tw0_40_5_0 i (by have h : i < 48 := hi; omega)

theorem back_tw0_40_6_0 : WinSet.allRangeT (back_tw0_40.backOK 6) (1024 * 0) 48 = true := by
  decide +kernel

theorem back_tw0_40_6 : Rule30EtherThree.allBelowT (back_tw0_40.backOK 6) (back_tw0_40.cnt 6) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 48) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_tw0_40_6_0 i (by have h : i < 48 := hi; omega)

theorem back_tw0_40_7_0 : WinSet.allRangeT (back_tw0_40.backOK 7) (1024 * 0) 43 = true := by
  decide +kernel

theorem back_tw0_40_7 : Rule30EtherThree.allBelowT (back_tw0_40.backOK 7) (back_tw0_40.cnt 7) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 43) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_tw0_40_7_0 i (by have h : i < 43 := hi; omega)

theorem back_tw0_40_8_0 : WinSet.allRangeT (back_tw0_40.backOK 8) (1024 * 0) 37 = true := by
  decide +kernel

theorem back_tw0_40_8 : Rule30EtherThree.allBelowT (back_tw0_40.backOK 8) (back_tw0_40.cnt 8) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 37) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_tw0_40_8_0 i (by have h : i < 37 := hi; omega)

theorem back_tw0_40_9_0 : WinSet.allRangeT (back_tw0_40.backOK 9) (1024 * 0) 28 = true := by
  decide +kernel

theorem back_tw0_40_9 : Rule30EtherThree.allBelowT (back_tw0_40.backOK 9) (back_tw0_40.cnt 9) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 28) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_tw0_40_9_0 i (by have h : i < 28 := hi; omega)

theorem back_tw0_40_10_0 : WinSet.allRangeT (back_tw0_40.backOK 10) (1024 * 0) 12 = true := by
  decide +kernel

theorem back_tw0_40_10 : Rule30EtherThree.allBelowT (back_tw0_40.backOK 10) (back_tw0_40.cnt 10) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 12) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_tw0_40_10_0 i (by have h : i < 12 := hi; omega)

theorem back_tw0_40_11_0 : WinSet.allRangeT (back_tw0_40.backOK 11) (1024 * 0) 58 = true := by
  decide +kernel

theorem back_tw0_40_11 : Rule30EtherThree.allBelowT (back_tw0_40.backOK 11) (back_tw0_40.cnt 11) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 58) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_tw0_40_11_0 i (by have h : i < 58 := hi; omega)

theorem back_tw0_40_check : back_tw0_40.check = true :=
  WinSet.check_of_labels _ (by decide) (by decide) fun l hl =>
    match l, hl with
    | 0, _ => back_tw0_40_0
    | 1, _ => back_tw0_40_1
    | 2, _ => back_tw0_40_2
    | 3, _ => back_tw0_40_3
    | 4, _ => back_tw0_40_4
    | 5, _ => back_tw0_40_5
    | 6, _ => back_tw0_40_6
    | 7, _ => back_tw0_40_7
    | 8, _ => back_tw0_40_8
    | 9, _ => back_tw0_40_9
    | 10, _ => back_tw0_40_10
    | 11, _ => back_tw0_40_11
    | _ + 12, h => absurd h (by show ¬ _ < 12; omega)

theorem back_tw0_40_holds : back_tw0_40.holds tw0_40 = true := by decide +kernel

/-- **Some finitely supported right half driven by `000100110101` never enters `tw0_40`.** -/
theorem tw0_40_not_absorption_back : ¬ tw0_40.Absorption :=
  not_absorption_back _ back_tw0_40 rfl (by decide) back_tw0_40_check back_tw0_40_holds 0 0 (by decide +kernel)

/-- The windows of 22 cells from which the trap `el1_22` can be reached, by label: 558 of the 46,137,344 nodes of the game. -/
def back_el1_22 : WinSet :=
  { b := [false, false, false, false, true, true, false, false, true, true, true], K := 22,
    sizes := [105, 43, 57, 31, 26, 11, 34, 18, 81, 100, 52],
    rows := [238348649606695378676290091476710134355095863893753983882569394714747171390543694729189993368012595417337737985249112451118751598965179060844154343364724570727562761546394738349567521851594539220432067583781621076037168266302270833668336936933232913845599142809372252018623111581307321089781940221435770466445828006601493085393132420163033487172217379443060968221617597807979628310698087735761303889851397317259931965328724211803333590369580331993008535694489140057595995316651688705196717064351873310068144363282875898880004392531898761108780041781774706161984807607162610809350338596315693788200984910803107839698170735312381655365029325006632932202215123374870403149886855666453990977275185873,
      578918599427065503627572546123439131200063120442340114873021554517991279432358823465119699615308396210283367411037107195928202025964951448846479945126152963662787243595914046889496918089770077184668350782463412653939891606536476363303510458359967717869964976376916634811318396591839835,
      309519338050975758247931906851415497289891964621914375729735302876841188955100719837122341885783964703341459561079354307046250388605098564606052995246153599985506802768997486559193908698284287502502644002043984959392756058727447894835894799007219104283887482177409932480712701809488683207705271438473415785922344369802664956163009943269013758477041321599177909762484883083509010,
      19939067380404875113814100388446801701315798626759956091133011037294632040523260011710690500875874140141024228789068565872910725300942098175096612279051432111849464910551650195196007007677872333055970002367,
      15053528877124033200277316910030565601733253722631490083232064079917477975740341439997369649632495578937429664349420623355459344895728267942741214124938413326370144671296641,
      6831866090134285252423536476386932016351202586379445910616146119443556290,
      1460684147151645131876776713363780069652152193706259104111024351781629157774110299401658734796464391882156077706608765417559247512324432141509827335790333678585707233356891536658743566979787375623558954124295286786529576392102,
      158757914552347370210466886712573178152991096371625901905464176756513540158279279300474190810993342411469646105197800960,
      267247201731949103302775823143770027300485242235756062958339630892049250843727997347207213686180052761246029268377851560052964362599757039097792718820328042438135561471945526096752516013199771700209207729035354000121203508091101696948339228829805999382287929932054372561672626114503010731645327625243714250445663243111594609173984657162124374732046054521478982970217645008288556117787117422368521532918354586153929760704783327426366071187419083311046237228087771798548686385650469463724476234446683497802922547427604972956025532020968704,
      184105471314613908163421014797276809396157076425195507154244636105061000270505930014266493111354219279385065113465311607557188900527176122906031760754692210798235474929306380588765980249443781712386986641431704882813368657600783573268506354521554930423530604229680444132843440395322623098658105974621145073613193214811664202803297695757876478940432300858616123694048406767902319159749630583318841067047538380519752725423856607730267647963825160313010705717688199366134389844944511117534589713272462562277515792325910963727938684854955588153369376755792328241186913282067870975819404237382375543639655593187626793437080072242169444197005759396114310976103163903279,
      232710418568844338351284661462380184621541099582033683008130701930801139083382039151956230771767671970088276125187794309369951159708064405465537740089488555215848100460816106651816723305837069021270674809777082356521500146320976294974069428766247393569479206419171729321866377693298672642661734873222832034986333469063059621951471696291460826592] }

theorem back_el1_22_0_0 : WinSet.allRangeT (back_el1_22.backOK 0) (1024 * 0) 105 = true := by
  decide +kernel

theorem back_el1_22_0 : Rule30EtherThree.allBelowT (back_el1_22.backOK 0) (back_el1_22.cnt 0) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 105) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_el1_22_0_0 i (by have h : i < 105 := hi; omega)

theorem back_el1_22_1_0 : WinSet.allRangeT (back_el1_22.backOK 1) (1024 * 0) 43 = true := by
  decide +kernel

theorem back_el1_22_1 : Rule30EtherThree.allBelowT (back_el1_22.backOK 1) (back_el1_22.cnt 1) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 43) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_el1_22_1_0 i (by have h : i < 43 := hi; omega)

theorem back_el1_22_2_0 : WinSet.allRangeT (back_el1_22.backOK 2) (1024 * 0) 57 = true := by
  decide +kernel

theorem back_el1_22_2 : Rule30EtherThree.allBelowT (back_el1_22.backOK 2) (back_el1_22.cnt 2) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 57) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_el1_22_2_0 i (by have h : i < 57 := hi; omega)

theorem back_el1_22_3_0 : WinSet.allRangeT (back_el1_22.backOK 3) (1024 * 0) 31 = true := by
  decide +kernel

theorem back_el1_22_3 : Rule30EtherThree.allBelowT (back_el1_22.backOK 3) (back_el1_22.cnt 3) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 31) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_el1_22_3_0 i (by have h : i < 31 := hi; omega)

theorem back_el1_22_4_0 : WinSet.allRangeT (back_el1_22.backOK 4) (1024 * 0) 26 = true := by
  decide +kernel

theorem back_el1_22_4 : Rule30EtherThree.allBelowT (back_el1_22.backOK 4) (back_el1_22.cnt 4) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 26) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_el1_22_4_0 i (by have h : i < 26 := hi; omega)

theorem back_el1_22_5_0 : WinSet.allRangeT (back_el1_22.backOK 5) (1024 * 0) 11 = true := by
  decide +kernel

theorem back_el1_22_5 : Rule30EtherThree.allBelowT (back_el1_22.backOK 5) (back_el1_22.cnt 5) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 11) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_el1_22_5_0 i (by have h : i < 11 := hi; omega)

theorem back_el1_22_6_0 : WinSet.allRangeT (back_el1_22.backOK 6) (1024 * 0) 34 = true := by
  decide +kernel

theorem back_el1_22_6 : Rule30EtherThree.allBelowT (back_el1_22.backOK 6) (back_el1_22.cnt 6) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 34) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_el1_22_6_0 i (by have h : i < 34 := hi; omega)

theorem back_el1_22_7_0 : WinSet.allRangeT (back_el1_22.backOK 7) (1024 * 0) 18 = true := by
  decide +kernel

theorem back_el1_22_7 : Rule30EtherThree.allBelowT (back_el1_22.backOK 7) (back_el1_22.cnt 7) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 18) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_el1_22_7_0 i (by have h : i < 18 := hi; omega)

theorem back_el1_22_8_0 : WinSet.allRangeT (back_el1_22.backOK 8) (1024 * 0) 81 = true := by
  decide +kernel

theorem back_el1_22_8 : Rule30EtherThree.allBelowT (back_el1_22.backOK 8) (back_el1_22.cnt 8) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 81) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_el1_22_8_0 i (by have h : i < 81 := hi; omega)

theorem back_el1_22_9_0 : WinSet.allRangeT (back_el1_22.backOK 9) (1024 * 0) 100 = true := by
  decide +kernel

theorem back_el1_22_9 : Rule30EtherThree.allBelowT (back_el1_22.backOK 9) (back_el1_22.cnt 9) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 100) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_el1_22_9_0 i (by have h : i < 100 := hi; omega)

theorem back_el1_22_10_0 : WinSet.allRangeT (back_el1_22.backOK 10) (1024 * 0) 52 = true := by
  decide +kernel

theorem back_el1_22_10 : Rule30EtherThree.allBelowT (back_el1_22.backOK 10) (back_el1_22.cnt 10) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 52) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_el1_22_10_0 i (by have h : i < 52 := hi; omega)

theorem back_el1_22_check : back_el1_22.check = true :=
  WinSet.check_of_labels _ (by decide) (by decide) fun l hl =>
    match l, hl with
    | 0, _ => back_el1_22_0
    | 1, _ => back_el1_22_1
    | 2, _ => back_el1_22_2
    | 3, _ => back_el1_22_3
    | 4, _ => back_el1_22_4
    | 5, _ => back_el1_22_5
    | 6, _ => back_el1_22_6
    | 7, _ => back_el1_22_7
    | 8, _ => back_el1_22_8
    | 9, _ => back_el1_22_9
    | 10, _ => back_el1_22_10
    | _ + 11, h => absurd h (by show ¬ _ < 11; omega)

theorem back_el1_22_holds : back_el1_22.holds el1_22 = true := by decide +kernel

/-- **Some finitely supported right half driven by `00001100111` never enters `el1_22`.** -/
theorem el1_22_not_absorption_back : ¬ el1_22.Absorption :=
  not_absorption_back _ back_el1_22 rfl (by decide) back_el1_22_check back_el1_22_holds 0 0 (by decide +kernel)

/-- The windows of 22 cells from which the trap `cen00000110101111` can be reached, by label: 1,622 of the 58,720,256 nodes of the game. -/
def back_cen00000110101111 : WinSet :=
  { b := [false, false, false, false, false, true, true, false, true, false, true, true, true, true], K := 22,
    sizes := [68, 55, 78, 94, 112, 54, 46, 249, 163, 246, 136, 72, 165, 84],
    rows := [2133015612237313840297828713022286175694992419287652069074358079319666907447808488599000360622846476339041746937915288795802654762270994907998438827092224248428563705475275488401324998884292631857406478459773513321834484602082260048731903969396133220435350602489125368384952959621943017826795002008067539725482062291595068728788017033367385114463043553129756482006658677349344870414382283475861202793129661573482912606603340664891239001534043955136537,
      17515161881483881445437668200276957853962605811384234463394315397172986511384329473983056419772411925599492195439651139694593502928294575494065053797616741846130617280029845685193969812060009873132901847629130628916994089092303979183815786326529865594455867675892743649084465977447564302625916601895088351507945416893987018226094404405232077078905454254306648672367,
      3603137844130134262744164422220694232331454302423948769824288283156964089090475336410558913772986487923070228376810064726554484601807031630406130765328820764880136044208032771128227222086864577753489429920735460830367551651104299331415429593205918092284265366119720220604043287580246546762739865324432296989015848367037237354373884498808852864488819473355289161589848170351086445867480363488809955901460693274781838353307322391269812192791470409236834196439680008427933572955217604005364147974842100052101127645232289,
      33659236274446614341307176226909903377439844300214011843684800427050455550779976569127115564801005258550458004121450616571962327059308959319762695981775825344456023619199395570115862891925883441588525091972746923044634756444436166124579865949843737728510353677876619712028642292859075617428178196733165053424888990089536834975429209364711783788011348274735364976393306173802436212476228039352024591315887016636962950443413762205053773876744056903464474384776353518049150245079527190390363572378882464779547476649587483089549650721621140789124734358028037257174563495836241817944344346407577355376143098346255773483711613684,
      5444056674782656227807833980901181347826934308140254388568504112959210845559196898432092631802456424956799747366925489518283751121533251170160030289524146082652283048846353204848614159803938133170176980366491286645947565680644105435753548912789344366623065757343333063814556031458050390722971448598593104059020822185078266766301771176740660706326393467261648497991662286649687924593806819915657358776108221393815078228401582883352162317237970765713684734440130782947608016119578846352188696048878510328333672411224691509981968133405191202031643353278348299363484165958838330394198661632650496231295479913590131568595581200093621296487701191598490316248909452754878061119290581155517802525031209366304319759802059268333331127646390827270288173,
      4147232624920638493565417268301493226400866669605493466151582993356146301218738068929099262904129817948239113048381235475581252911016482443764255573914584205292960163805506008386424803182519085151919577894323006308798860830176949237640751190893928156852441766762916563119936408826321857971631833850914339910498321326265694252029628183062478891477825302336972,
      43172337065453613681988411758301753647521290037408254123416549234420835940986532300938725703822712694157226685413091025615987972265517676618804506918501572960505738092370671412947102883349421403624209270245831356361920255912964388461834790287707993980274766156772071925384066437398163841051340813386248924,
      109730717031576211443341942438078221260590798242959780346883742832829422211186013193961470370662118815125893193177442843838210886290363182583902018179824723297335863816153398885724983383486722547504341554664053005542751363570058474825992803219115954178293882659399606587399753824730384626752194431153308835048461817433195392905593361429146313105124972617294182182536899935075217376695736173108796449514521938036351565446279626407079554634807720662665340394780624990418756998868363748078154128276649391771201440620973057311778325315296952181047973719997737538028276456344536475949315080239834645545104115222141703572856118111410634035190670094721447584205402683525017569395594026814906173617556228822711217676839279833805953133781145409868351929952080199084696323193103689540323948353664173174914465031766299214098825016599870607946511595216007848885747899079214912338667009763154038739621492746624815447267438074059673160115242711925329350272429939927268721958820438388215040083806506176802015793668611444223499584902724054861193580558714595883485222943693181638855256299297313287757998770379229160481382750812525514433782648751169149584377239192531549040900090812563554857536136744609258071320926975266482149108524352022009525574897221125994551963426815848089084403804425923529294432405947150799674746978583922089319702737602568957508841123377463497328894095752614966826414631796404249046287138294482400886338708182483427400689357043657866241016123613744647320800894617255709164077884788101819573899593380450659992881971235939222951647214112681969647458876822991717346284283979525286282938860680022973971055554006643063523336439342730615906912714987,
      310989914306002025713609067540233374993179721279892555237017971302412833235174294992977264380404794109992206134559221510273770863061532570119006407086972031296031369202779858957506605434419453393858916026127878642176737591211569438301943385838183239618183898250546863390746984635242765982786717069598388754423098130493954978585404888906971411499246728095028059502314005640945172069931624698126767502316764636656803507634564217425840505441234326260859510673340519318665178815167791409271130333460215777651478408932460771265030955338325944215189490003765303019803326670248380809018518504404060231441847851020127592668517751920325636174571434191254664080873512584493121373481411044651014297671955882012921915453154932399990751568596566015808601704847178113413473055823831865529597161597011020473882804057021986156969990633665200998086265052670677878806598535350426854141457206755606610346443745168828412813299531094808820392852884274345244812109680958017304955093970536299885810913855169462232642002428404770034193319995523687284127657983033010673655843384545385103156050406682957289,
      1481780746868808064090450104035071737736278928600712951148476583749438181867788847374431889296239732872049185756646737206510111310652229491297133174712706930566878867467891003403677502339532082272520279328794023433661556369031664242616587576914004305074279677400136354057552174935668115647757965642448867502300874545900224036332665030157390767576906213874769839967244201478488247417756764293854309351824611009838865717243255473493709768493949856922130025938457341150513028123256250226608718846114689069128182567953026011182154404677193382340361240813640514780065952065956704121102392149160358298762120419616613525848249567433506227186073889370894448219678022109491077913163704591291884932805209948987045767232590469992221048085970833825639587564604769647369955429288025292364816789151736221896458238249396971147908523997252585972019982176113129172598440349294923504147679148276516476175082978743080841894705606540895576831159830752111912440627423300829025786841706321496671001340498328276331487910109496043572391531404498032576294118575997655647912685829866958079452175864545971433419408365313289739653237040070167890286765863212413382937423868741706298296233380367162275483272894402527289284795306715796514287291692646862160962225776279779040673423542326193510056005771133290651949694596026345563709685412519946563056716967298398560270197809901510688789604506792537717726987619700200271094430218609147390696945252828742450783806622502220091988898304409151576053537112415683563453277838116512482267932156840135318949208734391212069516051384206861087328572894692484540920261544727535884237747334128505625979398981824695375381921925,
      4729374033997707189957963136158735550622649286987894250211139907114259572761602049335356315436939300385588768346257721476415684734086526905048209433912333077502086875995866174244835603099230394807099451491870978256610353840410773848012537688312767215527502849852900119274656407392959738611189083448250040193964644255440624738125367670236149026221589093451008223840649936159052024088930937863098848023620355155945412614389137912283355874559102138122848202181598981344108407842031613672875225496301119816203111823398506659676199678369585022947738682892058763772140536168572312036013725145197644089742952889948101911750089175183080351157575763961714809961667670135554106139298382813700764688617606451209257859689361306104316541130783637622740646232489663803089562494756465902447996957962773760268517141860331334591611886602979628724473851288342471327690723884322613665075618083338603952435812370737005005,
      667222932769206780747107113130553087482503463851586805128424697535207764653701760016097685687948269395480046719143236160968373465957278157964367058836984031778155353413999559994546698100076438330061267364259265012060456212462974460061284575010427054096054564930681117316980700494403135512696269964983579794122477664540501242398711905527041948511307389393209871558403456946807637771367412610404581446816356948611467529382564406571041158443768782899288869208918936241500636442892,
      5480169106468154266377118984855143776381217428768170060251129856825494242662411114029060964815788461407307062688316463891788354152695402826224788272754845807992811642373281131883818695899870742100783722263455980697155937150207870502181130121167119855940484120144285115470874559797980536225649649028511062111880969577497959511720151626288002437148084932181229040530342868582070038154420764446139551496209215534545791643897732575868240771093657241214895411452856268594286283909337925511672731981651023700513229562693081762304828400098872538951390819275876537285530721657661847584089270495893723707543994750356390426997099535597108651043650767042543410953651756327381465985677331947492407826644209578194937770507062875809011877124365918641385076315236494086211060762846878620630811934375657302147710576017642494791513980097823153286867248423237009457207716546135390936354363168129033218558210376950025396177167548861541511490602873872105579818591179040928495069889378693269218454518868227138629020398695617674823506481155903640435554715961933193513451083744931781293362827714430928402171157283407,
      20105940392929769224663450786510790943755911475074678700648810941269063910766384179772984360561333378614617230340080005597470467350301752051808280654684561169834406233533457372016789027976697379515250897046936007938985564096061559171559139628255072482988578505072644328925246670152818104758590327265731141702475882313382552946784179298091855660966248825776615810314427501015650354463618523301802113134577575193912362718089687711828018032404887578170487838186720607821719027707846706856604867532274232189772496941241004546784484333375729523857913423874492400] }

theorem back_cen00000110101111_0_0 : WinSet.allRangeT (back_cen00000110101111.backOK 0) (1024 * 0) 68 = true := by
  decide +kernel

theorem back_cen00000110101111_0 : Rule30EtherThree.allBelowT (back_cen00000110101111.backOK 0) (back_cen00000110101111.cnt 0) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 68) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen00000110101111_0_0 i (by have h : i < 68 := hi; omega)

theorem back_cen00000110101111_1_0 : WinSet.allRangeT (back_cen00000110101111.backOK 1) (1024 * 0) 55 = true := by
  decide +kernel

theorem back_cen00000110101111_1 : Rule30EtherThree.allBelowT (back_cen00000110101111.backOK 1) (back_cen00000110101111.cnt 1) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 55) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen00000110101111_1_0 i (by have h : i < 55 := hi; omega)

theorem back_cen00000110101111_2_0 : WinSet.allRangeT (back_cen00000110101111.backOK 2) (1024 * 0) 78 = true := by
  decide +kernel

theorem back_cen00000110101111_2 : Rule30EtherThree.allBelowT (back_cen00000110101111.backOK 2) (back_cen00000110101111.cnt 2) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 78) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen00000110101111_2_0 i (by have h : i < 78 := hi; omega)

theorem back_cen00000110101111_3_0 : WinSet.allRangeT (back_cen00000110101111.backOK 3) (1024 * 0) 94 = true := by
  decide +kernel

theorem back_cen00000110101111_3 : Rule30EtherThree.allBelowT (back_cen00000110101111.backOK 3) (back_cen00000110101111.cnt 3) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 94) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen00000110101111_3_0 i (by have h : i < 94 := hi; omega)

theorem back_cen00000110101111_4_0 : WinSet.allRangeT (back_cen00000110101111.backOK 4) (1024 * 0) 112 = true := by
  decide +kernel

theorem back_cen00000110101111_4 : Rule30EtherThree.allBelowT (back_cen00000110101111.backOK 4) (back_cen00000110101111.cnt 4) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 112) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen00000110101111_4_0 i (by have h : i < 112 := hi; omega)

theorem back_cen00000110101111_5_0 : WinSet.allRangeT (back_cen00000110101111.backOK 5) (1024 * 0) 54 = true := by
  decide +kernel

theorem back_cen00000110101111_5 : Rule30EtherThree.allBelowT (back_cen00000110101111.backOK 5) (back_cen00000110101111.cnt 5) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 54) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen00000110101111_5_0 i (by have h : i < 54 := hi; omega)

theorem back_cen00000110101111_6_0 : WinSet.allRangeT (back_cen00000110101111.backOK 6) (1024 * 0) 46 = true := by
  decide +kernel

theorem back_cen00000110101111_6 : Rule30EtherThree.allBelowT (back_cen00000110101111.backOK 6) (back_cen00000110101111.cnt 6) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 46) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen00000110101111_6_0 i (by have h : i < 46 := hi; omega)

theorem back_cen00000110101111_7_0 : WinSet.allRangeT (back_cen00000110101111.backOK 7) (1024 * 0) 249 = true := by
  decide +kernel

theorem back_cen00000110101111_7 : Rule30EtherThree.allBelowT (back_cen00000110101111.backOK 7) (back_cen00000110101111.cnt 7) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 249) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen00000110101111_7_0 i (by have h : i < 249 := hi; omega)

theorem back_cen00000110101111_8_0 : WinSet.allRangeT (back_cen00000110101111.backOK 8) (1024 * 0) 163 = true := by
  decide +kernel

theorem back_cen00000110101111_8 : Rule30EtherThree.allBelowT (back_cen00000110101111.backOK 8) (back_cen00000110101111.cnt 8) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 163) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen00000110101111_8_0 i (by have h : i < 163 := hi; omega)

theorem back_cen00000110101111_9_0 : WinSet.allRangeT (back_cen00000110101111.backOK 9) (1024 * 0) 246 = true := by
  decide +kernel

theorem back_cen00000110101111_9 : Rule30EtherThree.allBelowT (back_cen00000110101111.backOK 9) (back_cen00000110101111.cnt 9) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 246) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen00000110101111_9_0 i (by have h : i < 246 := hi; omega)

theorem back_cen00000110101111_10_0 : WinSet.allRangeT (back_cen00000110101111.backOK 10) (1024 * 0) 136 = true := by
  decide +kernel

theorem back_cen00000110101111_10 : Rule30EtherThree.allBelowT (back_cen00000110101111.backOK 10) (back_cen00000110101111.cnt 10) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 136) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen00000110101111_10_0 i (by have h : i < 136 := hi; omega)

theorem back_cen00000110101111_11_0 : WinSet.allRangeT (back_cen00000110101111.backOK 11) (1024 * 0) 72 = true := by
  decide +kernel

theorem back_cen00000110101111_11 : Rule30EtherThree.allBelowT (back_cen00000110101111.backOK 11) (back_cen00000110101111.cnt 11) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 72) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen00000110101111_11_0 i (by have h : i < 72 := hi; omega)

theorem back_cen00000110101111_12_0 : WinSet.allRangeT (back_cen00000110101111.backOK 12) (1024 * 0) 165 = true := by
  decide +kernel

theorem back_cen00000110101111_12 : Rule30EtherThree.allBelowT (back_cen00000110101111.backOK 12) (back_cen00000110101111.cnt 12) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 165) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen00000110101111_12_0 i (by have h : i < 165 := hi; omega)

theorem back_cen00000110101111_13_0 : WinSet.allRangeT (back_cen00000110101111.backOK 13) (1024 * 0) 84 = true := by
  decide +kernel

theorem back_cen00000110101111_13 : Rule30EtherThree.allBelowT (back_cen00000110101111.backOK 13) (back_cen00000110101111.cnt 13) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 84) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen00000110101111_13_0 i (by have h : i < 84 := hi; omega)

theorem back_cen00000110101111_check : back_cen00000110101111.check = true :=
  WinSet.check_of_labels _ (by decide) (by decide) fun l hl =>
    match l, hl with
    | 0, _ => back_cen00000110101111_0
    | 1, _ => back_cen00000110101111_1
    | 2, _ => back_cen00000110101111_2
    | 3, _ => back_cen00000110101111_3
    | 4, _ => back_cen00000110101111_4
    | 5, _ => back_cen00000110101111_5
    | 6, _ => back_cen00000110101111_6
    | 7, _ => back_cen00000110101111_7
    | 8, _ => back_cen00000110101111_8
    | 9, _ => back_cen00000110101111_9
    | 10, _ => back_cen00000110101111_10
    | 11, _ => back_cen00000110101111_11
    | 12, _ => back_cen00000110101111_12
    | 13, _ => back_cen00000110101111_13
    | _ + 14, h => absurd h (by show ¬ _ < 14; omega)

theorem back_cen00000110101111_holds : back_cen00000110101111.holds cen00000110101111 = true := by decide +kernel

/-- **Some finitely supported right half driven by `00000110101111` never enters `cen00000110101111`.** -/
theorem cen00000110101111_not_absorption_back : ¬ cen00000110101111.Absorption :=
  not_absorption_back _ back_cen00000110101111 rfl (by decide) back_cen00000110101111_check back_cen00000110101111_holds 0 0 (by decide +kernel)

/-- The windows of 22 cells from which the trap `cen0000010000111` can be reached, by label: 3,676 of the 54,525,952 nodes of the game. -/
def back_cen0000010000111 : WinSet :=
  { b := [false, false, false, false, false, true, false, false, false, false, true, true, true], K := 22,
    sizes := [115, 91, 45, 272, 327, 483, 407, 451, 383, 531, 268, 162, 141],
    rows := [399901316809535661738012155772826361077380743533461528827590814270229659539262122594007231127478568592668685796294914208840017448187942764606807225725779041775011892347242320135956128466475895284824046067977963860859906050445736041339450995993149673648496215490148130398207046574967497496047171923361182216520545429536730820276471166179339528934361523978392879053893936727350014487564419045679354662797179081989242280732528496191965927307222974394947472018356267882767153754500524867870002209010420305802086369487434532975020569876021068286764957221700160936823564345013770407162852931042454196432740990322509519472888469502733918934428527249708855110943872584107498543360192012745999370091923510963429882514957682245470457146590028165519238116720008112583535450,
      446986178924124247618623742893326329435351383927658411556399918407880073668338405754001212884072396558306475796981634451018662446348085057981437750301580968838312444349482934530425588231353044480764750133741415662477070433641620434120937324558664154308034703554657274327475937583129158966992458938302290954113553523788546494018054560321126516451900436818421181794729403343333142700121951339647717334959586339771626106708161909876081636536485415382884632271924153453040409689310360889693924300869908318730615879613426167238210017049253748921728324677256389981463954783865591456776705774109756422023584358,
      10134228363238090511173807136195436295974398796514458136667218874946258210586633934863094671376177384858181054686809844142519194318981409350163768588570050155219699350424576919509175253748676317222701583301679685165785320396044417965278427636258421864077110871946316084913797978585548130371544122402,
      22947897097859726479056759961490752551356948405430912650982898724220429158974601339167777879163312663509650717327891467154977594514072663588488099280827426013596729980601778467401504859566376576905745614837784036755318184614316901683196085348113490994420404614110938804310169718762296613477875108879291200007193983755191089587452875605892523449110014186833943469576807004343335642442452921250459285338545397707459853061210247355077182148757847518984569318700333163110141044597716205221918559333133695695999950309108169517443411920130239745663240408266160217529482362540162585262596249565765240329910537904788826689606635288938343932803681128642687902161850551137392829223480482084509368511890809884193910097444139378458551475831993552368003166810568914384363282660614270540002566495895401080771198597911878086728051171399009378199582055460327804323528922132664151823820893359028983824857739599280589487773866195778234845582518708577492399040561864938613012892494107843066341239594300268339771438871317363437491650411992072253613161148780928732797935369554518501957060389420744075025000729269164041349282691994888787045116600397872762693798674646562444705760003500977587974186091312547321283462689473201556736118794409135167910883466351199506862667515937325388543864634762587863575134133376060545409166199711756236651843890279180635622161237181456238766146456576836465506671892263860274472959283573923869533915287465908499327679335451745828602361052172141535690779272486136664863788373750328277796411973335927691096411956983712366051006856558437353539439976866620952073336439060301061760400202617444963272379289520515404835609128515426844593441401860461835047391257422563116659300406296864614377675533853133707129998550472872168458233246888457108023705621030823657501421892630768267085901601449508340240,
      407063492083139575789078292244824213989442113378059731154293282910056215330021338056850068350188172718912418219645749712016847052953053047955126067426479489549874883895651688869344659412817908917592104609408116974749009871934202208441274504578045699606393821085590430339070302025973185640325856445646354816512188031419158426226146949987574878643847423211805891865573152624369876016328649399750566904486173755128941435898687699876881580748139395478105302257110922599439985662777657610359642151740536990925621926774744650447257881024323000155910935628322394380503675783226551839806190677390658728120230280570034347293949083206747184260832956973413663894359521413136835764832773770477063561213374550446584844631005720468483184487775652212358546142544475743277341909150213117926134281878125014847865035411341916268468562889653048493555245990557109012388438655425649754117943625713391914291671415070556517310337041384078375414322523737824447567080462288775012823636222050116761824258845774034837002813258786250062756235547088277782215375582602565281965436957342291772770645443353793196331584648319713367778461911631622787656216105419620278333497095380847887322782416537933586602371288800585629568284761512448338817092618022795499225668055824448859969121545597608257473991912441347466005951805273024616787497542019091882050521548830537216630143491964379612612411179489732918739587744604367975830607630209131757927832543577658622498532492096838773363731444827867025976931690963030021801498003239865225114043380937419831366009177542865264908495342318026031428183279607447226467384825508433136460329639536123592657516418309926706628111033961052868710926781446585607952652917872357183486422452195264402372957867131786104204095338134591767812373659535711802996182459730265129293644159122092231889065348783718779829914569260015080003745922281207215659294791862258036526052042854514563655073631593271503604393714887605572235381433863102365834423137703701919523749766257949530736070673857199585027918163271874499911318612485010457071706106464850882579662134647141605581736215425512802223277771949253881852596603286792721253073523465779998186773167249322020691515210595672136877880,
      5551162102008681323794424978425633346084471310885824628678257446154031723603035295512655899724645768247938411781982835558775991778619919026106295605753090998041051912807288053008720968860953780034346448644899738447124034397757616760796242745455461590583675769278455105368994922914797354775064124230760459385190850302696865020325501044369622851949758044768856072485221752008892256835305348780008799637373909301141044643647002175135517249098339797300602472620973309924504367835045822813535311171032109271116161489005606666534058567425458983313001580905390141508223801243788613165071532913330563449683478781375425378209695687290014410858051921874387842716728887668154837033285322267723486796965393953466276267125482240144699229346045929990118082837406531454805006239548395673381203944120640946295845873988800050514887296110510185020278901951101098059963487114487900710749848522879047143889840666906188787564765480578926252931488106217710115054169394617492643812523237712020722250110584816908261635934571503700129291595125812891905226807524247591343013962555166387616778746766444488102909096928237091081277661774200193695457842153089665453279828550802263703265114267476222950128048076896037810774620176683678100306908609109066239907896293901667140192708653948559436611614892089716489295760096975156056682376162046699877743238662702749408724870963103792352001087737395489771459568173833229807824595468987058463770116668970495166882550313390536530737025320573308399642984848031431763426689984777655678571447820756129899551412829119378878162500364525217668596710330688048265488694588228016354469251933773301753821253743455076849230399971317502736826434382675665360135987723616309486695148990135945307216342374852038644102079062406239814273770396853366108825244494280513892682135196377301919411652365079352594298171692458754324408854649655038522189739569594835479691314867997689184341236439639148486280581535873417863352195818067284895484844976102086317118939456510676630676856671917183106714041094212083195018407342273803972596749659038944050566216686657754420770256738968902125097644516311115872764705187044022985435927498667730455755931426063048227593038794460766252099465112131627513398533821384018748987039963654150244186163860004232205880141207939699875011584233241268393294532353417380951593483555122226061658593027417850688778519319330877534221275494889993775527778348571800993131980193334556158169300358248309749456952862403972851173002086687917490409387453749251059323550841131055044066293875296682914581322107435287250832743123161600238532941354242504607439835350317894365565180345732680717278322050575874913403254018646336246325701403869777946919384282279871596838488194913718890093411865224522941978333410138969820105755387189688467492231975038148137033631684600716649710181155559139872847784010318186600207862988249517200577905683637941141715487947674010436005310480962204093184450731799663996564881689742022497756209131337041023879867588685088542952802046205158636275833459424159985676765154382724818809555426847978469948385478120991692916597017956135004062853498477284195728942159842138911392861791719385156536376377891677180890145431336867579342692995281505664192786780962996263503423080908,
      26399535684727515688299213067763694128018352895848884057411594646294424263903347197298933559528262453302792062321056502957527678533195785477253083637285962705728189361409258355285742917515856214996521591710788734505667250701941971822669969123038704008956135987812446380591652952923639655822237516257761448579650977800818303098725375580371012938869218504694834896707061639233232118756476721287302723776102979123420325102924850329566060053966726871695222725501407930102670644379784116386160954206037081959453656216270305966228005959684797079811939364396460413901558654962204341206796735949486716539222731941857943546719619611714042754023881124342265716161474737527936687213035244011674308022539400986971215977917628314527154474408673658069310285848016382179305657909083012985965844740173170322449120799159022397004463518630428321677606660143210066798509422236065598010446307982547608915593083590542226161336586993892437571505186882400409242057511102801573702744653666948813304541766977014616390159544322225538901857048935201164540443361337117096979133836204964384699690701573361555776740658754116695798439575269208987220924087528373967913828310825509418926875444628714156656067510352535257090955526817071723578656883956551795193239259931257208991937174677766315257323707943834971729602614117261913870246162240313680404298280100378279252071029202314564289674388255248125833137791851780969701620686202740826979708013622371916613621990848659847320868636157817510009210540607774018328093327556958887413448553458198193056415870838754347712090427800135848985527770069652043713159146850335391658651790192068861805366780468733365829443657944935538451253448500443290764838901212733689084905135091629908425129834574849825908092628004414660453278723061918067742109459229225849005680036374774320038509875142368265632574695809589571280935523711537663252859967857295554027251098953160586143429961873452735213057944830775324877053596762344350477154817371409919031015299837900719565957484092356646438265004750375587488909449768770356180371028466513495654703194848251667721816639276232479026393916842524596862142558892295906129845799665033855074427251160717105700277005391420853159490886013103454408282619981749993027696274379252741198517597860603274712424288133702173386188578064494535411557316734244064882879662021665977195695909799130030721026929593457340795898223869735872583797025839799015002407157274125655561630735305575885385155736691783329658439090517543268564647467484250893889613929777458633734517317632706180491868895042750404177795764332839739886319170372152231926159997186336177287383581372468648724255714978659436521759455758247097294748289693338719299221320373268005688008129488595080250772953243255,
      65955576581859364336829243311669389673864260921610612971354462544766034099557504994061678077103068899425496536447425876776989195516401251664915777160316963058196042182144217446038141872425023708283060862703776304516915921801653803739082820096357716308233138241822602679225212830366407136086988461585665715885179966301465715656995174080407257591008213809416697090224138785532527494202469384200742824610862724624766233579495782978044830859473376224817773376982162511438392198586217591788272496467815718907220672961940400664288712552415737910720022112881310999028471582241698601808333517265927989257236263381941741463756389829749105212320754090048647072616537648948336413516412233638869485275734271406889633402927188358940337896997067380720729371881371546978897353065288231240214874081365146004952219453267232569804634958651212657205571712676238254851917373275464915422162225740234369290527414331849547227650373461397006161654278267200030098594705469266038358797041834672353986926700408571415948222923111575451834930882511507628642041914263078303784264898774588825048642447155744625032828977635751219603524276018288715090374674045130210060677282896690157817647248590460309331200683595989312321803919331644881602050701030941596336260043185866598679158525679977863756615364744024957642722342222937855384415430140012840295509828163099116290860971408881765476518149542253772741857686683570280377728095084195662968296816923967129520381574720908340015143262405205098447358718142521817052654497854847909268709683412994792117747542172441451142255422586729670460182218019917485426960821168454378418716226936407600805537622256794022461993956458671822773926313648709607870030304069123522717138048084726949315605472895968603993557511280731868060747364047705096897077748406841661930805979719112939043923571865271854473173703160880354002454359164363163313157587139503348794240372227842954794752928255133850252651465546739761903922207719891618256701873965246644451249975694608616585710198010432854935410133225797452576534703816650759405156227152195691361337449162367621049784122332372283707517750284228058521850165131298306516445459329214398941715656352769809509514517372521954493820950368966265756540508077456522719213582408896214076849725633706489309484107657298877118582466237230677176475179746253609618640082903899410454378211826595057071142348442715624846320788520356277660088624145144279294165670636707612916021650574631467276228943110782962549773464974652567201598201141134182759714577563420522567810012763390470891330200589674179715439575136578156628254484407497466031087794108571848141648861982686186100390421667992118020399546267332579345666781484300069500320690993876399623162819950355517969732698288980500383818059305448450023333916301007987628113760926010679840411102795109957606158953299791307342654144168603046319044423417283509337232955231397287485459390284351130395622017587713526284392646071533282906768210909373519347958017986112588235325522322529183361245922588522613308131531812768087,
      30067533458871074462161577367525656810665624858718092350606913403540508701846959115468689354273069241868422876509648949284289013923312800573558791007360371480892688135415559049924649107358059587716866823192498511510708089264963320152415847790844451546018730459355842014274885543925289171516870641887607356003252757986953350655690515288455065171118375160329691505287241308255188711664018285042457792374024824538931312099838826713310113166270886768129690230968868895947183493927963522750609513160728184209061545846865818024805659414555465501857548659640847238563990949696955680929316035844162000392832963386530501657315261553972625630859644195003939407479837735047473868928305720631938797167373567808713856975912388680080733507896056868319919533747115701258901464784696317820250308645597259686917680505724189759834659330454276373606463788503934402645376445501219908100337845010677925132061713036774828065010237900752636275906123017280838188941080338078647074019348942996588614115346876201596844230110717391137869671745859405847042770620327179694945146475154344478046261536758044172362992198556609480757761620744870601159842778456299185069123966220252343620063340988321366180352143262552522520192077043199117251437783206462637247666892584207442089983311671660217427011773162545058047321342218702768411906945280685462012855917521748961177838748949790089263724988823705841707805718352517558926621904564789823075840547211586993570366508281281584413011031870828304216546862517512558794839284944880959621792219447328417181207722379545695709646713456804416382652047587508137176564205569879060939736303582539445899323243022730761192237807011619276874355750388640073490207765461081405919736834728881870226694205299664437019506870740594880819305915748071983782675185570269968852135056021130431515064213322967720895636520925165890989971968332694042310272981642151451704203408672864865537611509183750678474849409363382934548855138849046642046452260031195027894605384832810488734706955735788524634970171951090016344719377738205840035322993902730147873988338845677386436790130581219396359388470884523592696756810990007506024240285657062354848976753626747557526959168214887058242273443336396259371523104310526799339803546097337864088364482891192899133323906725308834407362376789589779117965585189953580493478053048902218536801888757270607035558425182063230857192340222622103984288412357569666986401790840970063879464578989405755100115672790835060864169825886475998907365180692043970413085777666349846736146908614719672108004153063278078800596372830556264,
      4289447665914828100459187160395008305699855880203396023585855884777679383990530284775271301074585043484182966409027451574747584853549186536822851232105916956727848727896144895212083542985235301414601492169374196882376495545832647788890180756197963219819668053084305407741727333517706525435924617994979156604464609510668010657623232884254169373918796768066139262347900191087440625485492451253194535351254913557631313961237919621617891137897695968156915192891246837747690670879621991722712737991454500524832324123126470921632639580249859168023981652349976215920152283936607601359529802577884418159489664037421981757827357017832358635801842580360781134036487991505088680287415874992931566558429708040009895472810574220323689756474914465710467637622271906214200480232836529460037386416164607623630476746206872557071695593135317639895106420059269918974196181110429338374518487526386903307555971087990495742982876769874697982424551758971925152755671900888015148134952344323311500921754963551499095664411714906303188031965222682546414153479282244022681893805409966197200368058780825385691830520739393807349304242620382200596535978002008414987082454962574217334498384399938656455802094721143958797749485875912247571758579059106178443842219364737369582701551388791672798846505617936382827568467592555222402191732563805823510704537018899170865726731180383775658558135871549976264422887788526488158045634464000049398646095952077206885986758358133650022589623818746737103352879917225201393541519537389040640993426739666454867165623823167223504135483713791547105929487092751656709481759477383198605916169037830373491968223056989165936164111088708748569330965354303011002297830136048078631122850270558197610707040151793758333230073922678742980596509154333394694001355475880160875971982584002841708115199837251416478806172255950716867379778682759043713592907006706346446918321560333884711306285286947920643613679094615494209626729626968997088645913953819015370616870183026047394266536263763917846023987471024644512766549558677661405835650028736103545118607270734811680328669627241758871167481343854692253540749076032264933697375224019860682663367956386052437529953405333760874225965991342376092997011613772503787896380829545886623576266169957166923742202690325750299337401005543873858260333167998833532199846046816236663819384452218845826987016724775339293917911577203622193796369050818248379782207709263297823233669660527763058640616580478643461961344913938783017167839618896124785806541156136136556965497364037871661444402404488024459465022204152578922438622153295410186358524787697469044462818070420072536032746735836267770294334081503166271936785272848474604654561126964966361120542033616218461752994414888719107317530566644477309474179853228258525016038162200854337301239045890285910533606154426540347101948762518438251576173690166022982243898872470051477304894001544092886850719060284704402782953014070433508707018362335058948842626157334237773154282688112268462991584713846622028124765073117211435039068742373336717092432511747596273545485831550300001002463424514183123689627397258737402178193167738616125675812418523605440360161948660367457277274758465345666642759369389879331550307994211755164252523787689936465839822215703841312789410458497838151117179531598280591725782719791098082105158570951189003137442644645466902634811392833625233686687824468622196063034111802284382097026466477209866115123831783194640176123974154105925626032437886545394442751015106067144156974195310011615527938443351336802407416165517735124533362,
      74616160330188600972681675306957056359304980211491520956350675480771313901320238141092170152171808451096647055440361416118417738750967758740296629402463757739811000975703473771046605549603244055800770592441780032415466285088295074184566367103441554233311374526563524112033543225326724376694715177624521009350475479319421289492495312746784237804051958334972353665215789386924646742447917993169242092186271370973676141948847700191977544519531126744442572267703840626450334050495346503661626382689944798738777634173887335380695867011724298032192276120372477811105859326009041395027192578020109155685238977499072783589583969515943237992620397311106067976499191437357150588323079315494358861271491878483123629660170383415745001660422866733879674965942152918842487087183456037299203753855182573859318334028790961097755559538209636165537862786621065614927176609094880845082823836862759639200692212191580825698136411742908987554993141125108870216513354426380894189856114628139576624217436303467549194566709799440551726247366767330523852253947556442320453426852512801549630779433216501066978828514920871710026354896431962665805792414776136488271829619777019011818204474878610763687600761788922063833505261649690741698886851811652376159998322039973842627709073591583678695231264427752655141986671376260252742320070359402789041175679458741447376612854065285335647679367089022226247560163044075692113278243761107088979487819464899813116168034648521203747158330907029078538712573688973791299393746328251848261499366274030966417344846077434034708122756009376503219582742930516437826052165152865630296722850654921702146079547361996565078230525150182725914684344244662556992517875866194070221554955378595238063980381753498481697300065094421441667568270672824749930868094863008535782447120543,
      74280501582304804576943251747730612913814126840646849646906594534906307301846035202871724412011992994163161480728813865146581972273958398819118343398167142459960501766177655665313624528082625371676558929174030238648560219049063095541584918537660339078840585185391577510761022609479378225732667684800614935247328565423915543914987179907886278377554439679998802552410308796323458594209772960159799819647467580168520016095133920938488527043999817472594777239068909263581737613734847063592097595369420941526122647520258387335659375241109931177424989670910411622064121164657414044355852073131728070523663019994472184106900704393648608556045569121059266398599203677331046772920083511416974294804005145452157941615757120546379506063824919449409678497551851856544018461792474004341635787255914960155844638517620756721972194866272567247080339319067284685269424239179840327621207149162605496607992511562135543725371709764573188609550953596152157038490177301866864426708436604942141374006112131333877216255764283025674400412389473751407028353559589494591612662436817146909296643015136,
      6199255978624316462694118893326876893162666910300570047300341427467089494688676972785677303544968716971644901211120336759829996557138826080267870896310111477538159372326062467872901522704670454667147479479217133598298343130926976002103165086236671508990153657508041519126697027680291383791035291769726849021656406013892491828042481886172783829440497153470929793963013713617609151883687885614744722100069256941629998937072741102824532425160284064252993765522215470193794816032783934261117572821039387962013759956686813990936336315658085499233585981709103167522777290354999209239539058983939816245494085500125912155802744715746214253281098787343722792597103404173355325660996810439064942526866998965261037928423084339450742635470867267025631773098415050913803174525562393703457437965741383762250045201985904767915533160677427244872283220938970032734222667483519932279732355308984244885607236080064583612552328950521412190370471302136369] }

theorem back_cen0000010000111_0_0 : WinSet.allRangeT (back_cen0000010000111.backOK 0) (1024 * 0) 115 = true := by
  decide +kernel

theorem back_cen0000010000111_0 : Rule30EtherThree.allBelowT (back_cen0000010000111.backOK 0) (back_cen0000010000111.cnt 0) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 115) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen0000010000111_0_0 i (by have h : i < 115 := hi; omega)

theorem back_cen0000010000111_1_0 : WinSet.allRangeT (back_cen0000010000111.backOK 1) (1024 * 0) 91 = true := by
  decide +kernel

theorem back_cen0000010000111_1 : Rule30EtherThree.allBelowT (back_cen0000010000111.backOK 1) (back_cen0000010000111.cnt 1) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 91) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen0000010000111_1_0 i (by have h : i < 91 := hi; omega)

theorem back_cen0000010000111_2_0 : WinSet.allRangeT (back_cen0000010000111.backOK 2) (1024 * 0) 45 = true := by
  decide +kernel

theorem back_cen0000010000111_2 : Rule30EtherThree.allBelowT (back_cen0000010000111.backOK 2) (back_cen0000010000111.cnt 2) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 45) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen0000010000111_2_0 i (by have h : i < 45 := hi; omega)

theorem back_cen0000010000111_3_0 : WinSet.allRangeT (back_cen0000010000111.backOK 3) (1024 * 0) 272 = true := by
  decide +kernel

theorem back_cen0000010000111_3 : Rule30EtherThree.allBelowT (back_cen0000010000111.backOK 3) (back_cen0000010000111.cnt 3) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 272) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen0000010000111_3_0 i (by have h : i < 272 := hi; omega)

theorem back_cen0000010000111_4_0 : WinSet.allRangeT (back_cen0000010000111.backOK 4) (1024 * 0) 327 = true := by
  decide +kernel

theorem back_cen0000010000111_4 : Rule30EtherThree.allBelowT (back_cen0000010000111.backOK 4) (back_cen0000010000111.cnt 4) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 327) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen0000010000111_4_0 i (by have h : i < 327 := hi; omega)

theorem back_cen0000010000111_5_0 : WinSet.allRangeT (back_cen0000010000111.backOK 5) (1024 * 0) 483 = true := by
  decide +kernel

theorem back_cen0000010000111_5 : Rule30EtherThree.allBelowT (back_cen0000010000111.backOK 5) (back_cen0000010000111.cnt 5) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 483) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen0000010000111_5_0 i (by have h : i < 483 := hi; omega)

theorem back_cen0000010000111_6_0 : WinSet.allRangeT (back_cen0000010000111.backOK 6) (1024 * 0) 407 = true := by
  decide +kernel

theorem back_cen0000010000111_6 : Rule30EtherThree.allBelowT (back_cen0000010000111.backOK 6) (back_cen0000010000111.cnt 6) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 407) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen0000010000111_6_0 i (by have h : i < 407 := hi; omega)

theorem back_cen0000010000111_7_0 : WinSet.allRangeT (back_cen0000010000111.backOK 7) (1024 * 0) 451 = true := by
  decide +kernel

theorem back_cen0000010000111_7 : Rule30EtherThree.allBelowT (back_cen0000010000111.backOK 7) (back_cen0000010000111.cnt 7) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 451) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen0000010000111_7_0 i (by have h : i < 451 := hi; omega)

theorem back_cen0000010000111_8_0 : WinSet.allRangeT (back_cen0000010000111.backOK 8) (1024 * 0) 383 = true := by
  decide +kernel

theorem back_cen0000010000111_8 : Rule30EtherThree.allBelowT (back_cen0000010000111.backOK 8) (back_cen0000010000111.cnt 8) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 383) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen0000010000111_8_0 i (by have h : i < 383 := hi; omega)

theorem back_cen0000010000111_9_0 : WinSet.allRangeT (back_cen0000010000111.backOK 9) (1024 * 0) 531 = true := by
  decide +kernel

theorem back_cen0000010000111_9 : Rule30EtherThree.allBelowT (back_cen0000010000111.backOK 9) (back_cen0000010000111.cnt 9) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 531) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen0000010000111_9_0 i (by have h : i < 531 := hi; omega)

theorem back_cen0000010000111_10_0 : WinSet.allRangeT (back_cen0000010000111.backOK 10) (1024 * 0) 268 = true := by
  decide +kernel

theorem back_cen0000010000111_10 : Rule30EtherThree.allBelowT (back_cen0000010000111.backOK 10) (back_cen0000010000111.cnt 10) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 268) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen0000010000111_10_0 i (by have h : i < 268 := hi; omega)

theorem back_cen0000010000111_11_0 : WinSet.allRangeT (back_cen0000010000111.backOK 11) (1024 * 0) 162 = true := by
  decide +kernel

theorem back_cen0000010000111_11 : Rule30EtherThree.allBelowT (back_cen0000010000111.backOK 11) (back_cen0000010000111.cnt 11) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 162) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen0000010000111_11_0 i (by have h : i < 162 := hi; omega)

theorem back_cen0000010000111_12_0 : WinSet.allRangeT (back_cen0000010000111.backOK 12) (1024 * 0) 141 = true := by
  decide +kernel

theorem back_cen0000010000111_12 : Rule30EtherThree.allBelowT (back_cen0000010000111.backOK 12) (back_cen0000010000111.cnt 12) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 141) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen0000010000111_12_0 i (by have h : i < 141 := hi; omega)

theorem back_cen0000010000111_check : back_cen0000010000111.check = true :=
  WinSet.check_of_labels _ (by decide) (by decide) fun l hl =>
    match l, hl with
    | 0, _ => back_cen0000010000111_0
    | 1, _ => back_cen0000010000111_1
    | 2, _ => back_cen0000010000111_2
    | 3, _ => back_cen0000010000111_3
    | 4, _ => back_cen0000010000111_4
    | 5, _ => back_cen0000010000111_5
    | 6, _ => back_cen0000010000111_6
    | 7, _ => back_cen0000010000111_7
    | 8, _ => back_cen0000010000111_8
    | 9, _ => back_cen0000010000111_9
    | 10, _ => back_cen0000010000111_10
    | 11, _ => back_cen0000010000111_11
    | 12, _ => back_cen0000010000111_12
    | _ + 13, h => absurd h (by show ¬ _ < 13; omega)

theorem back_cen0000010000111_holds : back_cen0000010000111.holds cen0000010000111 = true := by decide +kernel

/-- **Some finitely supported right half driven by `0000010000111` never enters `cen0000010000111`.** -/
theorem cen0000010000111_not_absorption_back : ¬ cen0000010000111.Absorption :=
  not_absorption_back _ back_cen0000010000111 rfl (by decide) back_cen0000010000111_check back_cen0000010000111_holds 0 0 (by decide +kernel)

/-- The windows of 22 cells from which the trap `fo0_46` can be reached, by label: 4,051 of the 58,720,256 nodes of the game. -/
def back_fo0_46 : WinSet :=
  { b := [false, true, false, true, false, true, false, true, true, true, true, false, true, true], K := 22,
    sizes := [283, 235, 152, 308, 481, 292, 335, 324, 521, 260, 247, 178, 219, 216],
    rows := [163134402198914618706263561481311045723373208954987069004886242569445994082334958300734826731528604478876898921732523014530757456175425930506368943015498279967890360571034521989891607930147313587851655596831589357724761553410113057421609374118401882802856680126154962184509501448640396305203469716643310896847749123058325836975416899590911289293481920840095600716852160784181556463348987487425302330908544908027221164222971432903644358012077524702428625898175418183233730246242561605528243215613951833093195658529021132033760704885811253619370342487064876505101154794645539860473967757391047685275533495503959065511809557606763858471641409694560369090290852489426193995559694736669796727819213850513423078247565380527651262227129806789095115259681758894364132395091870350154305069420795089062906655364261085898074871134701479059946764210957785878716565006738987126396135456245624387858029958904024115576629283252792622180295257285387506223842642488706481626738277847999977516358402089669050433622536697598007712834631701334782822925091173600870671044731128455450685471600798055426859333009406757154498751698819170243323040469733991114936882026276902880149511157657549821703006994009506332431605485883110346793097445960453333008809876308603567435987284114657249952649354133525729030880270721273626580411522964087367328623102545705193921670555761848387282945199074927740020365127739734857732158344435653661993749637728613929521715445640631576552013251828496072200459301844109090689559793879930467492559246002896326063057832473678634273432601318894603132351919133381789842016202828281673387162293580755938336909996674055728258514815709422359153108501837006793640672489732729355893417069097083897972738302733285929227403400442876817440860632214115495307630866511416743071897552815742651186071279372348326394703306637914279187738640680178245330669734902652885784304642922276469623,
      211237029131134645675951776291092856113685906351563954240607158102915606077023040669565688486712531941864207495357410864494570420387503496182924835648473787650617226302399835361105134711436474951644989118882475056418163991627376999145734317099848992580627837484781819882822108858678875327067774032378838330443200977590292498476984401708531587322112962515357371059570084576862117917446327727354385721587936887534539773018240062726717955521560653656978178222360407648590102355037728103386831419705088733057070635961061791474240767316896263989615962789060036934680686694040343371505503263875553955192778995060869358517060269188368235302497489068157205745638198584210110535540726521076137584019181867779799687091627225150285676298210647202279109975674113220864332478631901037332959699908721969022790989649182139511760953641738424623983296546549875499980441742878339373738759631014653107798552750901102968951937003331120925853698132189108347155161049738061768798100463247151007452530370551201896554277041280675707378345871821204369424392953568296531942650921167272934258344579303221511020064526411791966356359524513378015879122886801374954859554459777871817712901668034107263218260878892813611583322744574387059603909990349420465300872709320036461028039553482344616105319191144343083883241334606769052837910026109362482172294748926681263734030972628075259776469502579367192253784957260326365096412594411100805053140242767746950466904098379573614592255495921916847290664990168048713704674804844841129287845329803612868074140432364879215149879569607753228366122086,
      44005037499668691146653669594628886437737276606315748861561613077269305777165929241813605063349785673105726703697270775350975085649497421889860176590177933385496278289016735744339519303743941518832215658219264949299573606910834950084549394058665088989741236716347731945248805769083654680095840578343449140967828254825675058491950993879402770740386697920600368074672407483051425360305067758634427330978917172018056775562406895093491813530778345159971845932309775209126763686856393032581644924138493895250510736619251920144101208684445497670715253652592045315750370870836358804411939523275162598451916206355002100992355153451842435213472108209393383827922043415983152184340655322815607485644105773414024020711260664152583863952723023898186472658146008870176678107746177996364861673015445053766799510509632552206211058200661149417786970354299478011797505596551779583964187103552478396920489389061081978697468944825379572216398134201847016466594801319894816594318454951773044817850573689753129181506035054024378,
      600960440470164554901118263059686189863361628251161229727957103086284189665792787726102084587017129588713036680275948941062115036692649269934660238108893176236272919105724374282164149453390101118040438529950435941765202232819098791903106467470484487727769773169661592912573866250335690288481576686400306595890052993771883275180090943523794325067873542766525118283895271721617554566451609048107225470709480479286379268262824852256341554025404248983388043319139983883234364386434097272705566730589561891636309598870256147974786039445105499812320679246249000396836726549052344901351463382123683186804868813324261245367355154426033333434959290746239830749176665698897529312723731896401348486297993692347462826596663495440821426301578522497142821792833478929703356221396604404393443170593155649235816995479913796823202829152123744288991853087240433198674196879425486417968807659749188639659519582175934545522007676300674089526468954475444875367932551615674572997133111773587454334698011595331491365451291476358249162255840960180494492756377727335118351068457046696583898331511008286190747197087060470934600686497439647701628529125755060775120200982004181199327454862542464204655797805216802166364403360797962181787979472837246106746777629877176987639816932661655206728574634540069790083317417177468396092751646350430313445169994884384069177905429457858627868962477538196567786859352835451237314044634059648531690073915755258166431485392981995458448776330025949198026878139951048690705428896065414202543046378228086394231730191613575488311799292247333548915256894781972212124634188582245591330354960195941502533134710708734699109727395749250799637986279426498228434576021816225349737507245108686827452445667867820085001745068522017674512256151351487381281688653677498713333851917431206810672844068332385219717300398202162229059108354269009126905907431695899133214933846019847319670318397731027411145429641448158608002053065129693545136761729427163481914127000167764112841190128690721291946936998237978267734978461759268216289081803751702728285224,
      315541837341430533980900969381472912776898376905979478463254635631974527349628490011926226477223303899561955798577284869873065223855790369034747814333252551730692101511131313080061923757413092654985912423839166870142264089502058901632765770467899660278852326401080094449876167626639471408511071557210676033853227162457551939633394488043408278859982348486991639528604833761810499057436765483264439402141217344156369101235878422287222687469949321930040504184210752715766026352293393910433868311023503346853706403729931832687357829021672746244557900440749977890307132562861445660360689754783195429644838939088543125893598415426495484354955940185504197607256946509825461534056406832779521267197347684419419757272024259010757195998649939415074268509805549927236370254651268547774630542994258819592203969931820167397087489277394885348184011568255442067005156653408857220702268157484201798640248116116047956874346116677685307386056613471910680211035790818924307150045395935742475197420465712166972662357186935572936022246128356677649014235555437450999788167021962536720855719021946650804094598267238757824396817046675584402083158203917907116977865210079771037704951842511826239601992159669236071517663514666743422668210192618585108926055560626723095139350223594112306206281682419778538493100450899351181198652625551948087250521378153650711293450840297009999768293022329907109995721640862270474129214402656787001529445043960401949891568102376979504430016144633462097839865271833615620782546606409902738579838920354157691948850072751648664646447207553774924183469916144080524336599346212448916940251892718775377274297319205611897926070608631839763032585432983092753031574129951138752970157204852389574244236134247090632442918654168193658605616866655621554847433943065945013498864249761805617792820700122615668337291831983437834884468727050447510761356970884394336214645657375818462050676340048743581200648982858090485774657676264221545397393534823972209844140597938631321104185387907793668742746682672762183622633415308404673704228942550717550127309849724432870664962217276687295330842289122951473654463457564464761867613726831571061821119208140327031684607371659177375670336722217640377555646366389962494949831750540466697933261554306254553270101136833072825789599997386135780593664688088151709739063657346098847050439383237344848314548369664653245419717130283634761836121647638869897140271119762546900661002559991782884236466537105029444810476753151121299587718917833984830040264720369175576119350709402559588229814695872915913381615879221860595737117752179351383322148651566859082115083868262998131537359117868317360129630609968471987352593827261265342180195744218412111224197423529312607009933598972072789992991781675646706851481914324214682568569399209639788752820326815603174414156604941731148967481183742615551737941284711793951237391222929696333394040893558374730278360682000628798439839654805475479799507747327226305517633415231586064534272043726220777166281182840254827816367278940980481506816427356990837536426099618361492357728168376848177147241450400950121265653292167131651005714720382998371429389965874122219182384472503731973727927409638624744347818899323029077208277530389252487,
      65499154085681691125852064136861204653342372053696015808492420849849284028000448156508643711371423158283800813910317418589016845146461344361053417239536699818773102303604334702751036602758877060131600895468162085912629627070252405854569935590721698997156437427965179946886553295569619397622761116347311223126047737509380197754074298262505949104025725098913324139514098637785371304224323100703776763231463473255004155393353256161157897623433180348428690267076375182395201520904843110610542491251096933225598775935067878331870413347572317594157903172742237740468476024115476344320372889048388233571897926819207836072221458255896081751690719338025031183479511574916139328458869481785940415457020519742467106705538804816242007166355325361441738471471985059082493349337429940969290480936089066109397303850320584012243764817405586423827519847006482339651240552682907379761081685070558334960383292708010692575947476787371737408446905366948038870111454786543942886607654445935976174941108573912089523359681646352877754245907027791285643828237780084759199084435908647868234377367643460522060895602447548540917811878337564573335700814777463761786556854329736687516977901301615668896589789904074802366246125284860448861859003032177933860325567419364996918149141015603896005186618395952510549555309333457093032173962326608167619612392343584610628280706859323971114321655347899961282423327604011072529842300847599730019255300894745450544113918637033408868207559664956589046279815176689669962739812149831007884390841674510668355596734908311797909404168947865703462111506236858271355034556846752190515448893572977332157131166282062233699432674508248755063522663721813624632362347936975750151480160685992482254801206905832838874473415747143314228550305833480899908872339456264902916235572143113905005291673492978725766765520405149761465317397985169883093547203895616887531527032092695535823419109940796864569466788562823277936570512733463469881299444,
      38981023707169165522108765038863547603884814160244109290275391270879492783785726506465022820359750653465887901646010124116894768673004247104427566251863328343825225857681381448814238314188508036945877813837930967462554915427704896651269746528816763778922371549480896164736197837129175178534918495869329268700447732914701030929886647651756674200331736329650314874921506404353932677879519481277434100990228394450742131919010260996998809430895245203567708196116193649175965681560918777002325530595938843972589609254466555006166415002718158956852412881864692918959203113149279044526290527424965997016000956031502336060964029345156530385567417827548138141916775127667872434751409992656130332155165818710680880324242193781237123298941358589503087721710188974896640582757859046157946596148634571248146433341866347903044023621792918942987338746416366220231851405790640800028908180219103476562850614275368583639792540972692377128341133269222803783189677748379916740012099646245231702740202487691802379742791516322824044924632198747336622600801909077433481788862231902304186693531584463240006968726795183248160441152989595276231675109236563771854455485267265144640554902017171427911822781912380499023661006992778297131398490573401144546152899082932652012950950586939013235415376293624288999065277035657688254514810502503152697535845120626437312065539493410834704036992435708272056179727261967964250657575845155969334963111235220510014369995627755235716563095317721730039871051325555364318864325443603407019679277300953379834990840990726374359412452290180686185148438909298490907513931383622419162315537441847044826261586554197267773498967903687493978199316486974605102411960031307204629866009952910846579238199124819131282588900773489470870108863257936158840207098551039911396508027666531180639714218951423221047932293883177321603837119934351565207632457400937525733839578686544345608591873443672643367250121871699944404404560142984744035563302283333073099082578646365361532111855433303803532140214393324515234590184129237886531968438439179482412499651489601760726856936296262548887043032201070785215334499287271801860527985740909192492410737350310955693424464035557062371606923362219339539628042502025079301611907515533802606565,
      5516783762896477067103945009745622021764273314670892687125356008773442956674098062813209220605836985269817474497963793750692695146673482758295792083933405677515917041067401493278863520212773122983412706739785945185772715109824170506527855664724227949827067636523093286989958736793481177903168826081096838297907835104745422354345420618881526504146979027180491783893479139731311701808037372664063625639571262670283018745967129734796192032261813998660945111217617321987638750061602851654703023939041555750716736791972241971023621231356334646721678837762452939676639451674353873058385247265656482780167722281831143215628601016459095134342877830206874754887035363123097089088244806136243633226549855803640658209056430993731136730768985654466413173510443215387029946249519469831255343944397008442159176356334622051118938091519363184146918484560786670034319734959186227315995469272942257400344031162310266089300801282710943568060947706705303556540597208462495859466216107919363524936147246855978333594407543391804402934453116494598144407746616696816414200922008469959754685461134662990585261758504247482854580807054650438098997388647240218096583116624603089505120075747584056759350679615052201359669998848059808299470544138101594702504947301929524338022609155383807027000626424886374713381395295843956913447971431704556290971007323420642603728734120739158954290667916612447364625195122389717349143739136865854158405147248929501463093150069384189967668838466474715435136395880521132924165793704891275590847872526171067656847501523885624158375221553387102391861583804182638688088622216208180413770390130014775697830901677618831444752779972768010048944718436769905693790111037070953445387212288924844835792293692687978386852210380937069808429290148986684699441912007673000553731942368806620673307816395993529631018557884738028673603130653265769333879258977172932235053300129418664953002908332348016369992853401606304654306359425540006760253014331727394992612440971473759785470310047748920258383805449531642704888760845542322183341711208949061967248337004431640829225511146113672120373125634987233894165707114514534056636546192229832041014990431232978847578,
      2543656851541940720928602154857067627186654353509507764980622447113344336855746051307253701578380540301432990863551543247327397069218192666486731660716905336933744815234532348244613163380005167490610468829533165544160038514399772038858339436375247086260182635674386086758364937621779429630089617409801711348359083734170456463440462178370911141511446250575230929988535795879444396044614630251039900588903495645456562237791919783646601112156907570479314419433288534221727233307017733476718043764416783017651204029177892322442377405701868071639906794115081622095478018394750947985086155915388935554399731920651306963221000499718926874469271738701441471353659959105645611083018874319310596141976019543602015030144225126326173766330370842851847435871283877060422844998559210007106640710724621268169768767732229984822140239475974714273925806498679809741042719578382098273486747650498772381050756854040292070544508361846249228711055916553509937859364804591342741040921750953526653003520712801110452626263581732313289905595140224308110449756114120761822191746944310924060938334139128673698438105764804413043103593143188287936280477616243690601421300779664824337024567664183911815583406890821485704106183783227155091665561000151931280390123744983679353062555395285735794235729154415615330534302174363457254143456980024941783648679169155659563120261028779839591917364888216389203461221273460324972301150765431444434618385077820585824362070417541091404996620647111137885915818214527596792932171404990537790357770014612106151568074859581016680693682752859832675419507977264561687972362617018475505948992429921524770374172734347245793161517689082453331292287003868266686816446968671151814572410929031409028614093558529618125003785954765202249185681203825776139195311814418571465189927499274234527371091552671258907686239247259610109670750253310409476974641701280193451049173035918160975857274542356258381572356335821507833624493993462817102217881372720171975273718286652284551078364360963959460763669275665199556684900110692152568527317266184608397881345075700870533622593708109238815589663772573048361193616457126542948022654026812576907979181657634628025062716698862273111856007975871344524846381630478674961613062123756516069624071342770052921617712650914539733185798456085675176043854444343952934133145269849613023469784021970589063992912674801586132936080355507428447928117532595209570554416505928087575171562287261725167690490020402174491723771774077261088038225982981873930334418621892644567708516917340692378560654639370391185305597210392809013735362973510454171223918592213498157249000458024872608549724033731850388604881850414892968142519666663563114733711596663335628734639446982073916134561854512976073671465411944329788871681818201877102013195504196286263020944126484259022883963794312481577321088487224795956829943104152928026413447898552781497198840998959208379891830011212388355263070746086087592725401457944910956640557048307247902128228789968159427779033330944023024859271984242143910266024824050994779187775552009595495610424314845402392623734207244670006535757266840324588990091596367478814072350061982196381172302893127607277490964744007644835301583294078091156169602564492280745624190944352219508654536960847756422622054529603282678636376446699312844361685570068819236841548546853559692726302019203057339108112837713156306120568002854568882926529619393309864177597765079864146841750763960844673346295800515205921619117768936817545962797926730,
      778237235150343275994547447473296420399895148689984774071531880610539997394148803648547924758034135855461833475623457860007179366770163466753348336790099572494292816460308850455651361754037683824606042571284233299245860836717002153822645320237337522045786846504034434205000305955840369639294361186730909382420344776521303126418971253475635427757369283915161030412565115751796432918400727801065735667753728138153019009891899947550792555957389773297529211998336916152450796963252902517344403449504683186267032511901127593969192828564157172977761955147184217491419041167757131448850016495025583129469708823191137755214064387730669222359445993209156853712525824538315815516794533517952256163866182591335914655667202996141465103197838245944793699710071735769750100806899358929102316390553356118153173426312692540250477493479968637176849667516648197945437680298541265575824834222265537677679219051646195382022516502767407691620837822805355819174783965025025999202711249434443438632494888737128381422333615031637710347470509544679798167772165548682127421272190171217909659359584899420806850967841769518589654915235853250316878101268316164601394117008116242797406461203744521568122244841011020028821407465292110515606200738036184269122438668067459122056915444732080539712697691335158586793013959941382131526631233206774580794337312932822475452996813969198204023877457793798968266319387853359601188231681887027832959032992647030379847795913911197127514783400568549062276761240877756941864731448341601348575457827744271710949386507164862454305291360194784637216799713951642484422032978932544113875040172568459916531117065799553479850876486696998948145935623173196130199607340174825609872401931738286357935099231618526998096609549960,
      6263741749217355999599936704963776225676908536866902054424444126173869467498093833804423124962822813705957995230059188274000723004897586734803788901347653813214060893018676557980982610873833784757029318830773125037613771892468657410285064422585257386300810925130781521762011193663055340408353690945179177488640357783890875966357444024514207526420191997452483297220382614349091843820923391422151113159747012029336354524023762624626320137751617085507724378103376536073399849234451189390297698646175287021065715512704048838348596718509462492029531375418602389528160523674770164718268550049320463252044491432056643559773662087941220543053420808391191792208294450009412249674987839673606325572063998368242988927638674475715250311066990293760147914105614469602025329551621220041981281498688842995690511106130460600287185203945028967294429857367724284985673095683215212137746850916134760007276656654617118673874671747936431913208922168016194639341252167282251061650420581270801321347507406727872180691023317187922143992490509134558110128963891342141591975792727905388693399413806957150505513297067668561447700801736483481666487101045005694389472399520519901178101844491461352155624472028012197139987841661250870304158392016895150074340875323340146337455838288677116972010493547170204831756565299330189724578362936934816335543753836629384153452081834800787672266850163523190564776362109288613797317488828698786606816803340981090036921606806362746323693351854878605092784622709831139303307315266456178824792786643592762059065645163229997707119864958261171471852989937917270882872432480373806971827724170154052336730430879814813387545664838173757,
      678428709904647207710534226366641956644921912201624406249190169120167325307405251333518615145842518974475212741059773022615183733079522920334495346966990939165759010154894500897173569675311318149436225962481984294688401718798510077671037342340487912053687168282982435884892174056086890887949324525522625181506689476698497547086076013866371164694583957009414781245475174520395920522902185480311658654212863483232031624656475869857055910080702837536537092170224482599011796384446251311920954161122803590693214638647230856655796348400420473404494883617359125525564525064158959063408234638500711888725015519466882555919888332079615056315903051251156396934028485529718605270485744838330420736671251615790875354436493790339699576391947034176615590222940672549671175436328967595635609377815035784770211009247542021284754137423180031377265421683928907761985298137469038702016593481503738220774725305020552122618421709030309484141962311443106702467583173537713464439157114736660461125500754213141450562010940398607879887046719393118530292298455183854063652207358661844896398962592671565392038238015019805440570954386768553712448653982414507698836162513547994647971784825581839403513286212,
      22969543019804710362233974999101966906908833872615287957407987999985158857205949608887855954915881003154381255658920615556695020527170797400905081654653604285561841225234484719910420052853682564804015673665835595447832785599981638164039246878236224619428727943141109600880139425130494556265318907497838111084895019439579712663018226247816416343728348104492685692682588252239417039726919273320096325900659817927106125985924824496858660209812856846305063903926456264243251042011187341502048221343975221046362479196829723956378171307393062551190373877701275909481492820726883536106852236906551395931595976897541138375302094983774634512497047957608019794323178710297122318188987300313411223271579591683504737305026165079610794536025465595178305790561101630264099913045573359873826161343587970111452243488780116802289104044913114386039260039371168371151215707453502096659081562656814170912570397160270904847363608761857781187676306095678313697088440705760743563131020100042851979223118634045008786026070527680044877245569400319119527035357793078752627660105299918015633612561507807112811834899865121084554489184643233835907971874954584498688438520105869890136161732112156621513745176088738914330850835629354915003751726840709051591121533931114867940173464449925043524026306160605124583965060549916234335210709891070706392101627716776807436743075468064987984397633708795019708851787072857567641316315402249715833571425386486805316419628569716136128175673182,
      310900682405443701967422784273448996430957333499799064465490835543064233693886386643117910957349970325888268692157990484048436995664383463446762576044040481276976757760365202103909925039227042688890859527463567775243827687989727358074303922264127457744004654030197809663645820737106313518439255597752327096149329975345806048057839474094468889584277620060035465951391525114251963693294842144368720366795384492742166723391493751326946317736512663677678295983787995043441683356374704486276178978638236237998575480303888833502385513166129252668859706181362958705662536790414530842360248856282253223191855528413324801570769003814164251372566764788567330656206554138620056432614759302180455927162679453867338811761841782850796324528869080621032587690211030722189784381162612739419376120366412006046847737609918661644188904548541260059415640324211793000563297109680241956222502329122499005745162057373427439728454693182086159805312964622652666371283859135341968979341077226671586647488754510913093397163105016660925289377112340205010068396129051454233323254114252569728381863661620026225312792032900219021781526194458124153646419440226446914457391517566816102211813450572738461592075620438685905266051839681971076046457668608931050172547102798443680739314335970332778263566336730712716328943500329769573669341623671445027461457571572983814483232828269511076290774544728500069896833501575260307655056080917643873499906789112743951547240780] }

theorem back_fo0_46_0_0 : WinSet.allRangeT (back_fo0_46.backOK 0) (1024 * 0) 283 = true := by
  decide +kernel

theorem back_fo0_46_0 : Rule30EtherThree.allBelowT (back_fo0_46.backOK 0) (back_fo0_46.cnt 0) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 283) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_fo0_46_0_0 i (by have h : i < 283 := hi; omega)

theorem back_fo0_46_1_0 : WinSet.allRangeT (back_fo0_46.backOK 1) (1024 * 0) 235 = true := by
  decide +kernel

theorem back_fo0_46_1 : Rule30EtherThree.allBelowT (back_fo0_46.backOK 1) (back_fo0_46.cnt 1) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 235) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_fo0_46_1_0 i (by have h : i < 235 := hi; omega)

theorem back_fo0_46_2_0 : WinSet.allRangeT (back_fo0_46.backOK 2) (1024 * 0) 152 = true := by
  decide +kernel

theorem back_fo0_46_2 : Rule30EtherThree.allBelowT (back_fo0_46.backOK 2) (back_fo0_46.cnt 2) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 152) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_fo0_46_2_0 i (by have h : i < 152 := hi; omega)

theorem back_fo0_46_3_0 : WinSet.allRangeT (back_fo0_46.backOK 3) (1024 * 0) 308 = true := by
  decide +kernel

theorem back_fo0_46_3 : Rule30EtherThree.allBelowT (back_fo0_46.backOK 3) (back_fo0_46.cnt 3) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 308) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_fo0_46_3_0 i (by have h : i < 308 := hi; omega)

theorem back_fo0_46_4_0 : WinSet.allRangeT (back_fo0_46.backOK 4) (1024 * 0) 481 = true := by
  decide +kernel

theorem back_fo0_46_4 : Rule30EtherThree.allBelowT (back_fo0_46.backOK 4) (back_fo0_46.cnt 4) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 481) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_fo0_46_4_0 i (by have h : i < 481 := hi; omega)

theorem back_fo0_46_5_0 : WinSet.allRangeT (back_fo0_46.backOK 5) (1024 * 0) 292 = true := by
  decide +kernel

theorem back_fo0_46_5 : Rule30EtherThree.allBelowT (back_fo0_46.backOK 5) (back_fo0_46.cnt 5) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 292) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_fo0_46_5_0 i (by have h : i < 292 := hi; omega)

theorem back_fo0_46_6_0 : WinSet.allRangeT (back_fo0_46.backOK 6) (1024 * 0) 335 = true := by
  decide +kernel

theorem back_fo0_46_6 : Rule30EtherThree.allBelowT (back_fo0_46.backOK 6) (back_fo0_46.cnt 6) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 335) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_fo0_46_6_0 i (by have h : i < 335 := hi; omega)

theorem back_fo0_46_7_0 : WinSet.allRangeT (back_fo0_46.backOK 7) (1024 * 0) 324 = true := by
  decide +kernel

theorem back_fo0_46_7 : Rule30EtherThree.allBelowT (back_fo0_46.backOK 7) (back_fo0_46.cnt 7) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 324) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_fo0_46_7_0 i (by have h : i < 324 := hi; omega)

theorem back_fo0_46_8_0 : WinSet.allRangeT (back_fo0_46.backOK 8) (1024 * 0) 521 = true := by
  decide +kernel

theorem back_fo0_46_8 : Rule30EtherThree.allBelowT (back_fo0_46.backOK 8) (back_fo0_46.cnt 8) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 521) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_fo0_46_8_0 i (by have h : i < 521 := hi; omega)

theorem back_fo0_46_9_0 : WinSet.allRangeT (back_fo0_46.backOK 9) (1024 * 0) 260 = true := by
  decide +kernel

theorem back_fo0_46_9 : Rule30EtherThree.allBelowT (back_fo0_46.backOK 9) (back_fo0_46.cnt 9) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 260) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_fo0_46_9_0 i (by have h : i < 260 := hi; omega)

theorem back_fo0_46_10_0 : WinSet.allRangeT (back_fo0_46.backOK 10) (1024 * 0) 247 = true := by
  decide +kernel

theorem back_fo0_46_10 : Rule30EtherThree.allBelowT (back_fo0_46.backOK 10) (back_fo0_46.cnt 10) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 247) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_fo0_46_10_0 i (by have h : i < 247 := hi; omega)

theorem back_fo0_46_11_0 : WinSet.allRangeT (back_fo0_46.backOK 11) (1024 * 0) 178 = true := by
  decide +kernel

theorem back_fo0_46_11 : Rule30EtherThree.allBelowT (back_fo0_46.backOK 11) (back_fo0_46.cnt 11) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 178) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_fo0_46_11_0 i (by have h : i < 178 := hi; omega)

theorem back_fo0_46_12_0 : WinSet.allRangeT (back_fo0_46.backOK 12) (1024 * 0) 219 = true := by
  decide +kernel

theorem back_fo0_46_12 : Rule30EtherThree.allBelowT (back_fo0_46.backOK 12) (back_fo0_46.cnt 12) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 219) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_fo0_46_12_0 i (by have h : i < 219 := hi; omega)

theorem back_fo0_46_13_0 : WinSet.allRangeT (back_fo0_46.backOK 13) (1024 * 0) 216 = true := by
  decide +kernel

theorem back_fo0_46_13 : Rule30EtherThree.allBelowT (back_fo0_46.backOK 13) (back_fo0_46.cnt 13) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 216) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_fo0_46_13_0 i (by have h : i < 216 := hi; omega)

theorem back_fo0_46_check : back_fo0_46.check = true :=
  WinSet.check_of_labels _ (by decide) (by decide) fun l hl =>
    match l, hl with
    | 0, _ => back_fo0_46_0
    | 1, _ => back_fo0_46_1
    | 2, _ => back_fo0_46_2
    | 3, _ => back_fo0_46_3
    | 4, _ => back_fo0_46_4
    | 5, _ => back_fo0_46_5
    | 6, _ => back_fo0_46_6
    | 7, _ => back_fo0_46_7
    | 8, _ => back_fo0_46_8
    | 9, _ => back_fo0_46_9
    | 10, _ => back_fo0_46_10
    | 11, _ => back_fo0_46_11
    | 12, _ => back_fo0_46_12
    | 13, _ => back_fo0_46_13
    | _ + 14, h => absurd h (by show ¬ _ < 14; omega)

theorem back_fo0_46_holds : back_fo0_46.holds fo0_46 = true := by decide +kernel

/-- **Some finitely supported right half driven by `01010101111011` never enters `fo0_46`.** -/
theorem fo0_46_not_absorption_back : ¬ fo0_46.Absorption :=
  not_absorption_back _ back_fo0_46 rfl (by decide) back_fo0_46_check back_fo0_46_holds 0 0 (by decide +kernel)

/-- The windows of 22 cells from which the trap `cen000011110101001` can be reached, by label: 816 of the 62,914,560 nodes of the game. -/
def back_cen000011110101001 : WinSet :=
  { b := [false, false, false, false, true, true, true, true, false, true, false, true, false, false, true], K := 22,
    sizes := [143, 134, 58, 26, 15, 7, 3, 2, 7, 3, 20, 70, 49, 74, 205],
    rows := [109729469903205693646691010010812735083612131632342003205664059116465934703680535070901243292746378586652666454234615221029984017382999595045705467763352057295252520365450322013623704440567665249045918701666116128085109989010967385995277352313286490416959845097574107962030492130957081797948613794179684869627617973604836042553170356178489746062315599378969521062737517218664637524408509664325994028366853515395827705714884027167037627478510372069691731571663808881727486376942062910765285122053885396015227368145834681726273561796183261086652493407285870261701462264098967170228702568285076710496498075123407346923351929827393418625864104079655475252822998886142837060402967719780869166344521293903289126208074370230989041050453783000498037420399371133777837629381329422038509678128805895308921028651500517703732270398207821790376183421398831500783063199311726475144334684871785713429973936680518311802133283241465980056274043257777080321030750527,
      273128977558887633980205780464614101630839781927570942945035288721928303594194687517699627228446263107279805332826016502758037597659600322848330950400167267154098606623001359365243788318385972077820605555176282730844184352412438944173379570917160546761663079387469147124761987032549474844891171365459939885017382130700813086770714281685431635269798368073077117455517221948535540506671844379448703959544424391770301946015854058363401278062847722872642708547961931296813896231545360873534635531191201081472979463411420285010686880166441751723573981049317253939911540801884505710897867672650035631927148907998894312564435742591242550746099611021074846776515737031554218468362005980405073683228664540214133134901788718062540380013789802354227192030443485182042014017163520048431794176745861847945140679798635118014552785900740335076544019749264388425001996202157000869803413340152204827296705,
      1300486546541866350899951439585967371180274931358917690481869095206705618200794973076940152970196753236411761948681433995034938424817156697812711780883699017948302763118626717767188305474920038313027017001100404514307810764818476714107336725099013628217325832645382577499192860592341455786731200967632524737711279401961705300750657563399071303523676878701089501980300710312384909018211,
      15177660436235210117735476310572005001407443779531912398191149240064696223276752512578691660562561631882032685890925644042166527569472529322198986985977949462913756971404981,
      2068915119400360498436434686064828751585937497035045845102445277775887851688098535827693184716264085,
      21362658873712036887672422288352141203087023860,
      46414509047993090583,
      12342865487664,
      17311267755064557388710076427327687651299001401,
      66645666635898801743,
      2804296725054287843957933303033041603886371122991798084893517610711038462745009732379795858195851298004636897690298072059467609968257,
      38528349023173904950168579310684330172633825630850928252144013538688556583976289900592185819567071917092062654829011527384110925352718920908931535874441327470235399594561437642783395007395884787429803126774676571859192249309069862491143432733548125864897452626814570221617833306972274329968490060510308494623540951934065163211956436039639726749724942740224304450482000492879038225952105041343895225752566224832377211139923015460597879363877128127641699013286169517,
      3081530713635346387517618051460274556983132159360419158024772753828849967257370562884110212177958648510673277563625558362778486432220782858482576955805053896065644928421969345411314686625601847025791402218059927766272748401606503139898812920062391848139251499414797802705514610163995440245822160764321275500150900475566233764,
      11899824347786664748661131367503575098228550757458149312416901420085823211834591652803928159345028340048639112244683739306105295633920698539933089039049495767541219718096268288137248784368468251034455889739889479281814953678022642379782004666836617137963114190121182118612719965465586334019039304926135698847527964097789046186946377987018714785879850651953930269750399352307981332540814959801332799241125972190300753329050781707890724239081396255495086964004616804157023369892682867249520848,
      44183935320031628362975171113355797046951360264006750761178381512844952472309652806213008909684438188059443797751420672771716791362303075773867027612194103667228512010600692204272832108807280537153549713064785691898666001066963325950830618376320356412553452275032890454571817638741598809280490739948428696753021137535273581201444439395110249140633077445727782843437660155134412057074512873985102322288970402192496982046974821556904621005839666426712540075333325796956303265925137313123126387367555683602960220131741186765095418914436487997152753364371252358450044014716240127966552462103088021560569362399514829507589771259409661204806479460440358078193847026475778499230447396548184026766079702020682741686431637727939888114020507840414135195741830517028523010414372639553102075162112439321502138262577008268961071034038975676586704083693313202126215432838787313412803654921696350588965979022112590594146678534874811879173835789140776648492190422745402166681206958333674236202862215264789257072402541852993632248811932822942782117191989692992831796909266448862803112708794545958294249950697104296916346323972360776913508572540943794067509651342533153827898947031807906867587656708295328083486454153137050446242941196405805458055961964482929228884889458964768390786198357370328158809561933563472603227139160420563112774662220714528275561054608619602230378724] }

theorem back_cen000011110101001_0_0 : WinSet.allRangeT (back_cen000011110101001.backOK 0) (1024 * 0) 143 = true := by
  decide +kernel

theorem back_cen000011110101001_0 : Rule30EtherThree.allBelowT (back_cen000011110101001.backOK 0) (back_cen000011110101001.cnt 0) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 143) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen000011110101001_0_0 i (by have h : i < 143 := hi; omega)

theorem back_cen000011110101001_1_0 : WinSet.allRangeT (back_cen000011110101001.backOK 1) (1024 * 0) 134 = true := by
  decide +kernel

theorem back_cen000011110101001_1 : Rule30EtherThree.allBelowT (back_cen000011110101001.backOK 1) (back_cen000011110101001.cnt 1) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 134) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen000011110101001_1_0 i (by have h : i < 134 := hi; omega)

theorem back_cen000011110101001_2_0 : WinSet.allRangeT (back_cen000011110101001.backOK 2) (1024 * 0) 58 = true := by
  decide +kernel

theorem back_cen000011110101001_2 : Rule30EtherThree.allBelowT (back_cen000011110101001.backOK 2) (back_cen000011110101001.cnt 2) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 58) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen000011110101001_2_0 i (by have h : i < 58 := hi; omega)

theorem back_cen000011110101001_3_0 : WinSet.allRangeT (back_cen000011110101001.backOK 3) (1024 * 0) 26 = true := by
  decide +kernel

theorem back_cen000011110101001_3 : Rule30EtherThree.allBelowT (back_cen000011110101001.backOK 3) (back_cen000011110101001.cnt 3) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 26) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen000011110101001_3_0 i (by have h : i < 26 := hi; omega)

theorem back_cen000011110101001_4_0 : WinSet.allRangeT (back_cen000011110101001.backOK 4) (1024 * 0) 15 = true := by
  decide +kernel

theorem back_cen000011110101001_4 : Rule30EtherThree.allBelowT (back_cen000011110101001.backOK 4) (back_cen000011110101001.cnt 4) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 15) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen000011110101001_4_0 i (by have h : i < 15 := hi; omega)

theorem back_cen000011110101001_5_0 : WinSet.allRangeT (back_cen000011110101001.backOK 5) (1024 * 0) 7 = true := by
  decide +kernel

theorem back_cen000011110101001_5 : Rule30EtherThree.allBelowT (back_cen000011110101001.backOK 5) (back_cen000011110101001.cnt 5) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 7) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen000011110101001_5_0 i (by have h : i < 7 := hi; omega)

theorem back_cen000011110101001_6_0 : WinSet.allRangeT (back_cen000011110101001.backOK 6) (1024 * 0) 3 = true := by
  decide +kernel

theorem back_cen000011110101001_6 : Rule30EtherThree.allBelowT (back_cen000011110101001.backOK 6) (back_cen000011110101001.cnt 6) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 3) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen000011110101001_6_0 i (by have h : i < 3 := hi; omega)

theorem back_cen000011110101001_7_0 : WinSet.allRangeT (back_cen000011110101001.backOK 7) (1024 * 0) 2 = true := by
  decide +kernel

theorem back_cen000011110101001_7 : Rule30EtherThree.allBelowT (back_cen000011110101001.backOK 7) (back_cen000011110101001.cnt 7) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 2) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen000011110101001_7_0 i (by have h : i < 2 := hi; omega)

theorem back_cen000011110101001_8_0 : WinSet.allRangeT (back_cen000011110101001.backOK 8) (1024 * 0) 7 = true := by
  decide +kernel

theorem back_cen000011110101001_8 : Rule30EtherThree.allBelowT (back_cen000011110101001.backOK 8) (back_cen000011110101001.cnt 8) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 7) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen000011110101001_8_0 i (by have h : i < 7 := hi; omega)

theorem back_cen000011110101001_9_0 : WinSet.allRangeT (back_cen000011110101001.backOK 9) (1024 * 0) 3 = true := by
  decide +kernel

theorem back_cen000011110101001_9 : Rule30EtherThree.allBelowT (back_cen000011110101001.backOK 9) (back_cen000011110101001.cnt 9) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 3) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen000011110101001_9_0 i (by have h : i < 3 := hi; omega)

theorem back_cen000011110101001_10_0 : WinSet.allRangeT (back_cen000011110101001.backOK 10) (1024 * 0) 20 = true := by
  decide +kernel

theorem back_cen000011110101001_10 : Rule30EtherThree.allBelowT (back_cen000011110101001.backOK 10) (back_cen000011110101001.cnt 10) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 20) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen000011110101001_10_0 i (by have h : i < 20 := hi; omega)

theorem back_cen000011110101001_11_0 : WinSet.allRangeT (back_cen000011110101001.backOK 11) (1024 * 0) 70 = true := by
  decide +kernel

theorem back_cen000011110101001_11 : Rule30EtherThree.allBelowT (back_cen000011110101001.backOK 11) (back_cen000011110101001.cnt 11) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 70) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen000011110101001_11_0 i (by have h : i < 70 := hi; omega)

theorem back_cen000011110101001_12_0 : WinSet.allRangeT (back_cen000011110101001.backOK 12) (1024 * 0) 49 = true := by
  decide +kernel

theorem back_cen000011110101001_12 : Rule30EtherThree.allBelowT (back_cen000011110101001.backOK 12) (back_cen000011110101001.cnt 12) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 49) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen000011110101001_12_0 i (by have h : i < 49 := hi; omega)

theorem back_cen000011110101001_13_0 : WinSet.allRangeT (back_cen000011110101001.backOK 13) (1024 * 0) 74 = true := by
  decide +kernel

theorem back_cen000011110101001_13 : Rule30EtherThree.allBelowT (back_cen000011110101001.backOK 13) (back_cen000011110101001.cnt 13) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 74) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen000011110101001_13_0 i (by have h : i < 74 := hi; omega)

theorem back_cen000011110101001_14_0 : WinSet.allRangeT (back_cen000011110101001.backOK 14) (1024 * 0) 205 = true := by
  decide +kernel

theorem back_cen000011110101001_14 : Rule30EtherThree.allBelowT (back_cen000011110101001.backOK 14) (back_cen000011110101001.cnt 14) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 205) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen000011110101001_14_0 i (by have h : i < 205 := hi; omega)

theorem back_cen000011110101001_check : back_cen000011110101001.check = true :=
  WinSet.check_of_labels _ (by decide) (by decide) fun l hl =>
    match l, hl with
    | 0, _ => back_cen000011110101001_0
    | 1, _ => back_cen000011110101001_1
    | 2, _ => back_cen000011110101001_2
    | 3, _ => back_cen000011110101001_3
    | 4, _ => back_cen000011110101001_4
    | 5, _ => back_cen000011110101001_5
    | 6, _ => back_cen000011110101001_6
    | 7, _ => back_cen000011110101001_7
    | 8, _ => back_cen000011110101001_8
    | 9, _ => back_cen000011110101001_9
    | 10, _ => back_cen000011110101001_10
    | 11, _ => back_cen000011110101001_11
    | 12, _ => back_cen000011110101001_12
    | 13, _ => back_cen000011110101001_13
    | 14, _ => back_cen000011110101001_14
    | _ + 15, h => absurd h (by show ¬ _ < 15; omega)

theorem back_cen000011110101001_holds : back_cen000011110101001.holds cen000011110101001 = true := by decide +kernel

/-- **Some finitely supported right half driven by `000011110101001` never enters `cen000011110101001`.** -/
theorem cen000011110101001_not_absorption_back : ¬ cen000011110101001.Absorption :=
  not_absorption_back _ back_cen000011110101001 rfl (by decide) back_cen000011110101001_check back_cen000011110101001_holds 0 0 (by decide +kernel)

/-- The windows of 22 cells from which the trap `cen000011011110111` can be reached, by label: 3,746 of the 62,914,560 nodes of the game. -/
def back_cen000011011110111 : WinSet :=
  { b := [false, false, false, false, true, true, false, true, true, true, true, false, true, true, true], K := 22,
    sizes := [93, 84, 82, 80, 118, 61, 57, 39, 495, 352, 883, 548, 367, 304, 183],
    rows := [8060087284917257029289008280167452026626995203989208335280139302594803537999027253228524973216566141705311489248274156718899618155643171768245155585738482784364813775069099558305975019411178019105143530000277819768793699975824476955810593690040199466820089450693189800203160197490676640529617336992215160673888569924510672671793877959161965432118376746356763374071397007911208495516795864440467104488954218546936344765829753245068336903482049091805663889237859705420334288468362996892480178767717918452185505035752287492456779785659344917811207715908779978465825623677220894030705027093819818992350619516918302783778,
      20106765114425814621335265624966212926961556452869375481072607793685254954616895785582821182584152057459591083307722450903670987382387430436974264048619378697302555400094292680300792097762191639538907117807654931522736059476012516238124113667471762349789653255117140329487065736972082063602580308236823620742372749172646143511883199174643751337827612963012793791429073937901224867740161709315733755308659004469372003508575915282764279783478194936841565667851277036729073884576951065107468349575744975107046262564942440732504498143053485906021829903099383799,
      1142887660161529140662751959586223971247890996075887093565647235242003602680601355879184216646769913186096108522387306932559975849069564276293133747576778164755136444210742066024044540589358663415196883592199737283890792015990425449410434902667394721110188561114740215053276058990764795555019006887049933197777525450350909880158766552249926201389720325174828038344360961542603552342820445369610523701233425111976218448359277115961568437884181309134483730968398911191759289275721828197216988448357160747333128552732256546259606682722139914635238,
      64933742077453581094440245511142151571794595928695118958029288271247097388257218382572639612583840468307724560398022346207725395742949045488693717933328225337314829197590560966379168428518321816869798356604613254443065536456803966158679619362271278830149165733055028429843901550677984110384678951226871686386439011259224386044281899035911890028322514596648853326405366988172642872685618670681002531044924548437610301097723942244013548476566248744698395580297778868055451927676629186160447997540954787487119407509717572504776607803,
      29411527901574120135237845986478832235463055658622504476046484922668079937004968548095551402907999531702570972601186964119873902813255500897662918651095323164799465359161462613414378496008719851898321958382389041781848055713008924344407889145280122150683437538002346529078746860577384090759578418388807944454010945191784894191811760536108187027197947203350991422116530449186662168923795991641162739906172823380712388583685478254030631960553269456275859032168307288127778827676068292708567087569241861229646038304732877437362328475402261197610690305176343666758735007469440743415102996965996929247038050579682815741566377207559775184149368781498164612796330951192137764200618472794366741871989618440569720144886848758560412780545799379532077187942775031295151892747246153269539511369,
      95432356323005842890451843026388033186742055132493435261357570498759449541163891727973934954460607893883485394709523083421593308409318113309726045959892650666125964961686605114165271202250582144800773451288230431794203050129979030289719074618215279917705965591685520486179739879195696939139460515732558133005114745729655676795528065160374148768261396877566174495497621749617068454430582477374885508272455,
      307159058649442524192255089166014095957411860559859756218909182178926831404331439273028886479912989411110923633544766388693886724630771204430726710454956771084647720337704244340049949327060221371671559405631026424470338008031226200070013192093756055497422270615102637275158391511797372444147600435080557768400109346018805340909393445809770469185931786964644524524768957321764966,
      1871334695286360757497468182098303442079832480077500881756887578475648480573286494534948874307196968324019734571917512047401220451359583287973580436445475307400896233688164228024604063834193318135117861341776311719886529004470930898727879517406710455783731387,
      164187126253149662817911393811731912714278482203254099178806955865310639186939767763644743650926180866517400300381979791874060296841890321332497271721327883898828832833844882167486995362643489653483376781075774828770355659011730619180239520165316212946505196935805111004743778646330367128031035117611920886070517524865746580851319446602125485226107424362511407228646486015720135608356094514201863206198205892875433682735398811951324007049401372236653061454677993607693444606639123814452764593375566079523440197999269973353557833462500305873758343547313877903077283378244001950486751928573151374674559612733933766222067429279727826517052883210524122040232024193151193057054964861807976765602996463376264826864829531957670605675856053965170044672541982914270648278942738516732131588960023736616280561649138452689505981682580322000238974761771287695098269306497881554886782002304054622888967559508309755180425612468375929490717261155343197064343216458507703098836430345657758627788467699171928637953907619113015189945677761462179835954957271568274438795021220738080479577863365463345043793982799123933299265578765922236954588152524546669831890043085060493164889924136373542422009858781766153745075872743157550803253152350133819453017098035298562764107033664110616058819431223970479800793538067663900984352556924496470680166004419452982122093336544084541213585140424456117209703525885896459682487447594916585495218362784387631381955711319327340625536064728821763229830794732749031679993153743583750856249752651199998835171327344625901511106699464848459250875131582198231392744319841608801248252879602498509478942555235472115070555532504034082865040532536462049300483099024841116524886391303861383753714841446006753818795640930330601250955340626382089802039437374098612762906784024590924940767800567542331403296845905053688631891011218256532196494103681948253778631050776458505327857636668749786637689029452537501143081859441082785476271949485276577003500443624448748436002068754038310538790558438234658538057557018900057055806918426589693851342533904767276419168610595838177048533439661053198899194814721860601048555126475192694684061004413756233702344631990317438724181673210225743658160568859023161905507332272510746211702151455628485238892095504018281297991002328563011538947332167999321513799734086289168370569696263248010858740657297232369579444018472277668166181304085030877174912112522396745113595643750117245196928218872851643757372221414318051433965464116020289060597568804964639353301438536026256293383667795567952852972936539696635243780776651174294768543061253608629751124303959481184948379250828147365400884041229807655054962430834706757759906617336540730097609483528616005346792722534569092465895533987882241187115908247343666158920028253690235000806777256521280934408481022665462808460836083752246526745210932431446833802713717636360799782537639944884794687583483615351166015590544757420768351920890650167374908598543973071168837645840255561902852361947648569995163322008653041457808497269764667135635775370974959051288139702300253714323786114272282888236946286904515643200206968894233066745303012419322794135372924576640209234222410788442259701953001956802296243339240687131711872120128603250795276942734186020241471605652119286082220508751874339438963552818479243651,
      1493600379016589793506461621573384532743715650342839753918645895365852910105667541552618977388932689995776918348549701242961214679817151327042355602098252889974588870303454226480816359239563407967447014246156653257084692158980253719610443277170603552416344891845654466028834412716872033225604053728176670109775688981125789244559966882648173905440465446428701960147264506804912439040787361474964338471091024615902184096976586699819481679591725841316355521074383320409543702957617472256160371258214348826359229075670113438413456551549091841692749535503639478833903225434953666853885837152921368866346082276819914433670250840984996201582526349406421962088893009125538095926693815181471948722602311552818801802401109199331529256286604911245722610411073657172122016662178013208728595097714564664661505306714153503781898704534112025587074917598414976322144328655008406358072397433912965738590003831092382978730745381691069624945762942188419508728667854459091968249096937937187304074717566441823139756024026251125948896610940494573635482774635627658931347464078871636558916681760616330307817281781412227393902438395942467146339680338137026217350457298767270322382536549441803749492947309795278062664263575425896862304040017454806423918397292864250767408094747513251048989390974538334374285656482001803066187336430444700346566914643923703085466040404812165446977267191007069649672364705115484336251693614766560845228941241356698229345815906011388749153141022119991419570146849159560289439078007245811018087409691848788529387746553523705168854760467376292767858248486203622453990463161843101169200450226101851975051835035074068885060567401359906603362146319882656818258812049314500739753449361224738117209138852123388059333528028026970302292956421693173342613174480894394919147337896137427938650360690984353261842452829281256111922054228479946051866716309914925116521932544583245598281328164682533921938191211476076027060957871200496608797261396425057714542258825362228398404275106713363122504586995888861059844910886386858721659611613607787922015300062244345570530385325681966705155101081919055404924980675552699910659776594089670863640432970950728457957623714664514866567803216928168364264753257161241657270785047440265313026116483946129433408533644422846636438324040131936322790598445521145313284756328896569326186217655679494217663541956,
      6436567810002522720406368953281662693456649511808705609759076634560915346058509133515100780549753151061891490692082602601095626769301588227822482487487655344200424601578997756661511589378409449095776819618280471205488744883531066872403050762395513071893613478368923988882258861635878723945531596722222976182164038961149758917826152085538905002834899003246955496327951263309501536192972248445683544027902090836847047550878996093828858661941727754833331097924798949970763159109787361671604844776177207812931274230877351584031480601419730000250418225092601899516818521963344154105954386532647975922822115463894802452937005726072783136151993898426566056496103623235511118874437587979893686251352956624119858461618770716497430846719646660876362270133415651887243669098000971678609188028995254891621934138888280449403856728326257869474097056154484648103278342228323748156529768176044359092819354380375900434616401227684681076259072067517548495056196729467940555489535488206649058705610194110459158393728870778411299033066121052722409124598545761883695960256357259778178714051640953389891772982997569740305487021155856484122470441339700160090689816140258051379500864916300524836386266375835353945036069679911008762599693492048216523404948887466410668084273964520649061662954945191748325715802493900273735459866251107144966508230304179905839377607910223362614976997075946204196933708469701095138725082827634883881836108916014454040292639575898298497951580060514987212139391194774540470487909692075311517027964858036864482199281235940288929689726343877471104174856877010548065975637330983658703261829009384834826967027110859734885542437762101187129740205062850417891913139615323170953368923660976730018036195040942999177560057819268408154792818355301364797472133803881907546799552715605882608232503404753863382547003331337773790396779241032530195893711060252126996012445497770995791987415328300981767861450977731918904844070669518938863561416941474683286026887187871482831576992038216633437915348629836708539262217122071749820810644816517807945639207188888216819777277464111564487068167161812615427429607805840473621486417737721942026099601595634650167828802685362959378738443589440340021341924049566560471461124531305441851087946736650577112050104094226635067139614837574219871976064248730369104969206425409826462114585003280283027380510219584376050906371118134393667039261619322502272477418568831667437577519042765968028640311641879705585182413074599873207181160649647076816753411822605224974815648973569914609189618725127731183709681523940763839112333177968985967454727546996905151414723188861397086824534659524495273102725674632785350746225154002700387445939995101743456003981911436963039389708416853041406906105682860363936242047072950678712312345857899493630918334637190547799809866059029563154561582349496277381754455257906739388998348182696906068659463556563982277756028871924285218282210055722815186248862953652571598772316460721858782722428968293769486020409141228326363319708133631414430825194247098579087831316399500805735301318927139020885364845963255029442656591297323378060304161247304360314659895961508105047688458002605163950020914299796840356939301780757708654395126002489251475745060212824124706842613444583971925784193842596596744091214164570827793427242345310578025816734862868506306097190731624848619838966537001445238997109539382384416756936933586282906377464246309656821999779621507977653036304401257449627473409729300236158279955628153807399938228216419790966788116961895502149593873819827492660162181922876407494220404773360627001880417786345362106722544149479858479418785914116983706947422260704579549067543839516799451811642595735727697583189952918503155389168712750903495343360761490763101804175272736584093357007085831644031195341122752748102972208631216458240719616412304815290301091734644391667400655630296143637661119467664226329725743580890298099197520547056960290606387152469915750837072365961573411826676332252050049996368054817404993258689521883630375970200287525284598811842998762735253593756728936513621790751473265936154700787105444168140290429343851308820741017771576750854338440590028166979260993674193744122504691311975823673446211233057016246653748451008377604636350728784679141891216657753441851747277224026290180191061844267836792989621522390310270185502330986767266787104705026497703734855699991389198634047025778482693198939402076974300921852559919937003279885432643120344856151672867527779577186536407578191752535273669640263648673891184689903328100482138221749057769615572705148972569325832318482116061888776210238915297716693202653566963420941617482349420407245402394556816337693972367182621965901322504119879473195254049665463361227358582147522138360277062311346951347434516590659614305651665883284832731795901293676350839621212770988144364516048730316400639785958617261029451046679833541009648283640506985168964346964486785074324508227957958135561453141555076843988653726891618896412092102755325454185214338154585454384843092950624039436032910592722143552360436382344082345076022194980970398794603680549392320576890526115120376940133117962554554606858858783546069203499986292993443689487585981839749338490708660598750013778216271250569122827249204531339165544377840368144079182008605410381075139956023480806630226747093798484803608830743684219802606751295118663350107191303610881366598086631077199610216715182249322888791575695672838614149264198524334675461349548487490177176126039934697571361709989687590071330161850887792801727135660927019423363356642712586159136269012545137639604368005384617483767300216452336356220838184393978401226657951613381378439218216477565496467671893016223059435870453518683945386955764495758862609177855155230809805702997429528519813215761131518566942809125559395715125199680425502046228349928779477983362095115244957534614113573757491344097548834095800500446554486780985631,
      165030748425963493516442409981278811202663350703005329364728374910315480420952158377442830643980922784059949910922753513498455645040776885718385709760630731992268002280016000585818485995241325407829662351982100351832967147065541501846783749468699453045733685230861891303332981467910654192329751077218928929484930988193124649891750168689259411826043083011250631500844247884775270468693019475541828399753595978736149095575106345757223499757278008070095336641576553319803184730466571921808789356379408298187423347303812372923332465599316431301725893434006960633293657442632182915521733108878446735397264256520847008146368526132778272276435228709247255304412276195275017419231818526401802481602795273470544104105466538581920612354158705174693616848240410877122624754602123551741224438417942389562259487697822525308843538545187880899898612369209038524036266658392894912180560927438193121764123426593470137842848101206263620408600618170823422775176031471519985453920785306473900116491744246638664673643488512598999493007012042211989315045258667199964066341396128302698967189536202090516736725971867876884655561900318438460329296110764326899316955530621511430436598612356042154787996479108384963681002295776123474673593599590069690432854724265186518759012074487829982614146105575882293705016595634039340865799227292205445303449190490062236902908934131229015692598848304226801356216629548375877817687637884068243800157591902949874983244024514157633232032001796626316460139119231278946490814267874720309769177314880655887808355582849308046561490784761543367406297210114751878836494284602587151691118752844008659127225208451735121706941586234120044628763506889396587659862999532309721662222367365581266534832894602102752851887165178095901409582243312748043042705989515745323334132325054911307196965292700258741837374784919432515239673978597757110748738760420105720460885300845545887297598709992867625316808497076224469024050175001747844161706135182802290087593434497712705668982645835906956436600894034813393151110928142403364254438432719574455076163695785822934629748981321795270724990811212871347952223864155244777901340257598097556504803888670878221850903162462476175442765036891880053843861008203478532217027058019457278508694470288214038772199669654928767638554825639768589050533320295632701182868706692165930659391894910412763049108611076289982209324723214872793299313565131804901232359962798813518236544281972430009894914288862829360546428850926171501197932345649539128941217125482903385103548377260589869959161225802350578868515841644004533879927121413497808516163134789845113917601858703005548235814956326443133425884513104454241752772090397122196349083448297224512440913080470709961237547611471859247890944977406049439353274499635364992983468335492383806098093620581648801541190645050333967027034472876018120794714598358738091559829831709562375352485007939406805114238804462023956458385600614315449277778412356111522889188340423687903370380067255379839188140080448567466118961092825208784758555586905973226472011789381324002926159845885148778204480905489959534915085081489735912472229623470568362881011989766877396001748941002746767520371801677757613356700454913994613959244655896218114284234685399026761008920447229037416481939616937009807015056095756265386621596756060709165720908371562296447938784872090007312298777895119332442448725125165592658762556606032072861482005257714901385499582016472589343393533491756368119043633377027252526318572662934789497627010791738325110361607125383705925028875688986422247157867859412559532346331302237887214292263321274624256802375027032454291236749774552675748379434110053917313147986772896,
      3280085223970100316849528032433948816382129212160355234585629310272824937591770042276094984463598669131220546575844723166366827354800506787256998137429353043443749278701147492954206557381906658333880186772513613926864244093774807639552348955985503188804218349049834521241441908648809016083861625261282227909093712509666170957571641492991953775744621230289761395433751381269130128264801093347070108297038529592184626046504838776077001829204571787488847282185359849212660489100479943227742537469730909186187608013027852767571047137811729034996589659653565475266386466127015177985634435932168405695580664056899509528393288945844960553808731503816817289075998375815504596821288252963338369989169068918739310167630477241107389652733890093870093210362895511271784013639333814130432703242172161497800678661087109660463382631760319213079507181138761435573811161962534830202364968629765011287212913524627023361535191567324143838243849198808639354402512322477891544435070432884950526718128145093296265417151927825087170341299878102584808697759849220412517490548621773558584066834457621335127261544490859387564016839794180446743175283548280773664165447427392435783013853397796648572636554317488935591388555221427882384272781457050674425609911280567267334847671270901756623501606732442599818702662006726489921675206768064800200648882582825830965014427365969285355700888198017445808814486346875973582484279502269512606568936955468221966795413310863514625377780703705574659475486766327339908621915229724377069180262644237096022115405686801389292302494017913982303891205690934476367751552169104179119810013580422039686827108172189228763163142052054336352067354827913175109326775335548212736925038000277653200185315218896480228321294416551240564245010620834661056397214520814241413845876334100311108257257605781401299926935509089363526700718322342074324732892057371224208945099166557058667060156710935642136355971670549003853207604044059210058544416528830242256633910816776992225770898241719125362011953271747328326197882776241794767177140383926580260056549670768600112944589666519368744677064663789673448542894822584313615565962165053921570392801300711055990449517745854039328645436984778947199296983237055590593013040409555192327953263698276846014463333671683851583409516530051851215315180204432829471337109951283004723792203827565339786588248364669237131082322482025373911497736328121888034260780888479244821058940589354801907654825085446915248,
      1942622095346884464250319418717023712447883486753665466892776509491682061804937709086982427402928654397803641653588781351794735004719173259712384811459108787323050151121558441837550090530772479682295746963331403614221707550873000588138365477837345425783363393522386529469637385026450267976710511466779301869034612559058121054186792080276651977362651832665737157543902114018739367550772294908718739246447704960934547886559377651315066217932523731218081519190558263241257898570813235035912500315230915722874145473787313983141037405873882734609008692387909391711785448715159435349756952353469244454303447984538009141356485449053906854203861176368952928379236764600294678334130477796431921773371886627794337063686730310279445709116119172388304043259237486899512875369169802636963967866058205831233694836353423755243950630027641126331400147839858859153636355749238916859129772153237328046343072124402374937614305748265477835567989767456614529689087386051810731305346099122596602506235078914942843592752794442817172741807704182138239219406911849268896572141638513265936503588174630919524156945202408185710827723143257351033783604929308822132357252228919087628814329935311978675594571550851792343573783009142626276902667744105412540782100976609584327862365077990072040636056222872460835788182610218808853207463046623620871014952005507438587410021155796121575964263024736799267651155573520369786552405172731467574376971264470846239242604855726869578151157942243078746605709031452844908035233828705662163581763301723998104930248669145595282262883650650786542339942895398028201401979306473992524141646514625027528922658806566206728392015559418653152317882391408227923987303639445455224847317474058107086241185833116291074243202698189248587579710324179281179248541150699929030861036738283326483334339136805603255949504637656265026459323244094747803275620523207580315527419188806867279399807488789392869380544171184322171532223544333555709387194975047036709412858008657825396185553250299396552101804336572790149811872611700633,
      883305362010140293647841956605636518461769425236224560334366644461878381980313805869339381663359882024451539895972338736966438622633963517704765315992559517931978195328847859495557824819465975630293860383354707726287239025333054102616411397506198429770893744312930834200605813090982944729911532244633943983144089720344418336436440815709177788957530919966493752090208971995508295035528792186022673440424085300510100615096887021485945218772670874262991054463534279411442095580464248492967864586956027889808672523210266816254565422214864373049004798758500268484348295555962196604487659416681650073382748836100574483378963031571125162616622444272644296676385235847865118207291083682894566188518465704227824983601950950584570479336311584996884194256007139067006439721252169324061105670095322616597932725466038587776050571808170296863008187961884611373818354180526873543943790399211505199261662526449936619433946935305052447478040352582450788628880300321450569601739117363069085403321139142665963652982739378827422367723980294497941885952151227934644158634950230972660708205005949428752749871459951813702076617143545040511689678571991563438754530294636152869480250251321649730262240346140214035524040095690430147989742] }

theorem back_cen000011011110111_0_0 : WinSet.allRangeT (back_cen000011011110111.backOK 0) (1024 * 0) 93 = true := by
  decide +kernel

theorem back_cen000011011110111_0 : Rule30EtherThree.allBelowT (back_cen000011011110111.backOK 0) (back_cen000011011110111.cnt 0) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 93) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen000011011110111_0_0 i (by have h : i < 93 := hi; omega)

theorem back_cen000011011110111_1_0 : WinSet.allRangeT (back_cen000011011110111.backOK 1) (1024 * 0) 84 = true := by
  decide +kernel

theorem back_cen000011011110111_1 : Rule30EtherThree.allBelowT (back_cen000011011110111.backOK 1) (back_cen000011011110111.cnt 1) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 84) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen000011011110111_1_0 i (by have h : i < 84 := hi; omega)

theorem back_cen000011011110111_2_0 : WinSet.allRangeT (back_cen000011011110111.backOK 2) (1024 * 0) 82 = true := by
  decide +kernel

theorem back_cen000011011110111_2 : Rule30EtherThree.allBelowT (back_cen000011011110111.backOK 2) (back_cen000011011110111.cnt 2) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 82) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen000011011110111_2_0 i (by have h : i < 82 := hi; omega)

theorem back_cen000011011110111_3_0 : WinSet.allRangeT (back_cen000011011110111.backOK 3) (1024 * 0) 80 = true := by
  decide +kernel

theorem back_cen000011011110111_3 : Rule30EtherThree.allBelowT (back_cen000011011110111.backOK 3) (back_cen000011011110111.cnt 3) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 80) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen000011011110111_3_0 i (by have h : i < 80 := hi; omega)

theorem back_cen000011011110111_4_0 : WinSet.allRangeT (back_cen000011011110111.backOK 4) (1024 * 0) 118 = true := by
  decide +kernel

theorem back_cen000011011110111_4 : Rule30EtherThree.allBelowT (back_cen000011011110111.backOK 4) (back_cen000011011110111.cnt 4) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 118) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen000011011110111_4_0 i (by have h : i < 118 := hi; omega)

theorem back_cen000011011110111_5_0 : WinSet.allRangeT (back_cen000011011110111.backOK 5) (1024 * 0) 61 = true := by
  decide +kernel

theorem back_cen000011011110111_5 : Rule30EtherThree.allBelowT (back_cen000011011110111.backOK 5) (back_cen000011011110111.cnt 5) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 61) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen000011011110111_5_0 i (by have h : i < 61 := hi; omega)

theorem back_cen000011011110111_6_0 : WinSet.allRangeT (back_cen000011011110111.backOK 6) (1024 * 0) 57 = true := by
  decide +kernel

theorem back_cen000011011110111_6 : Rule30EtherThree.allBelowT (back_cen000011011110111.backOK 6) (back_cen000011011110111.cnt 6) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 57) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen000011011110111_6_0 i (by have h : i < 57 := hi; omega)

theorem back_cen000011011110111_7_0 : WinSet.allRangeT (back_cen000011011110111.backOK 7) (1024 * 0) 39 = true := by
  decide +kernel

theorem back_cen000011011110111_7 : Rule30EtherThree.allBelowT (back_cen000011011110111.backOK 7) (back_cen000011011110111.cnt 7) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 39) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen000011011110111_7_0 i (by have h : i < 39 := hi; omega)

theorem back_cen000011011110111_8_0 : WinSet.allRangeT (back_cen000011011110111.backOK 8) (1024 * 0) 495 = true := by
  decide +kernel

theorem back_cen000011011110111_8 : Rule30EtherThree.allBelowT (back_cen000011011110111.backOK 8) (back_cen000011011110111.cnt 8) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 495) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen000011011110111_8_0 i (by have h : i < 495 := hi; omega)

theorem back_cen000011011110111_9_0 : WinSet.allRangeT (back_cen000011011110111.backOK 9) (1024 * 0) 352 = true := by
  decide +kernel

theorem back_cen000011011110111_9 : Rule30EtherThree.allBelowT (back_cen000011011110111.backOK 9) (back_cen000011011110111.cnt 9) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 352) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen000011011110111_9_0 i (by have h : i < 352 := hi; omega)

theorem back_cen000011011110111_10_0 : WinSet.allRangeT (back_cen000011011110111.backOK 10) (1024 * 0) 883 = true := by
  decide +kernel

theorem back_cen000011011110111_10 : Rule30EtherThree.allBelowT (back_cen000011011110111.backOK 10) (back_cen000011011110111.cnt 10) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 883) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen000011011110111_10_0 i (by have h : i < 883 := hi; omega)

theorem back_cen000011011110111_11_0 : WinSet.allRangeT (back_cen000011011110111.backOK 11) (1024 * 0) 548 = true := by
  decide +kernel

theorem back_cen000011011110111_11 : Rule30EtherThree.allBelowT (back_cen000011011110111.backOK 11) (back_cen000011011110111.cnt 11) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 548) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen000011011110111_11_0 i (by have h : i < 548 := hi; omega)

theorem back_cen000011011110111_12_0 : WinSet.allRangeT (back_cen000011011110111.backOK 12) (1024 * 0) 367 = true := by
  decide +kernel

theorem back_cen000011011110111_12 : Rule30EtherThree.allBelowT (back_cen000011011110111.backOK 12) (back_cen000011011110111.cnt 12) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 367) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen000011011110111_12_0 i (by have h : i < 367 := hi; omega)

theorem back_cen000011011110111_13_0 : WinSet.allRangeT (back_cen000011011110111.backOK 13) (1024 * 0) 304 = true := by
  decide +kernel

theorem back_cen000011011110111_13 : Rule30EtherThree.allBelowT (back_cen000011011110111.backOK 13) (back_cen000011011110111.cnt 13) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 304) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen000011011110111_13_0 i (by have h : i < 304 := hi; omega)

theorem back_cen000011011110111_14_0 : WinSet.allRangeT (back_cen000011011110111.backOK 14) (1024 * 0) 183 = true := by
  decide +kernel

theorem back_cen000011011110111_14 : Rule30EtherThree.allBelowT (back_cen000011011110111.backOK 14) (back_cen000011011110111.cnt 14) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 183) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen000011011110111_14_0 i (by have h : i < 183 := hi; omega)

theorem back_cen000011011110111_check : back_cen000011011110111.check = true :=
  WinSet.check_of_labels _ (by decide) (by decide) fun l hl =>
    match l, hl with
    | 0, _ => back_cen000011011110111_0
    | 1, _ => back_cen000011011110111_1
    | 2, _ => back_cen000011011110111_2
    | 3, _ => back_cen000011011110111_3
    | 4, _ => back_cen000011011110111_4
    | 5, _ => back_cen000011011110111_5
    | 6, _ => back_cen000011011110111_6
    | 7, _ => back_cen000011011110111_7
    | 8, _ => back_cen000011011110111_8
    | 9, _ => back_cen000011011110111_9
    | 10, _ => back_cen000011011110111_10
    | 11, _ => back_cen000011011110111_11
    | 12, _ => back_cen000011011110111_12
    | 13, _ => back_cen000011011110111_13
    | 14, _ => back_cen000011011110111_14
    | _ + 15, h => absurd h (by show ¬ _ < 15; omega)

theorem back_cen000011011110111_holds : back_cen000011011110111.holds cen000011011110111 = true := by decide +kernel

/-- **Some finitely supported right half driven by `000011011110111` never enters `cen000011011110111`.** -/
theorem cen000011011110111_not_absorption_back : ¬ cen000011011110111.Absorption :=
  not_absorption_back _ back_cen000011011110111 rfl (by decide) back_cen000011011110111_check back_cen000011011110111_holds 0 0 (by decide +kernel)

/-- The windows of 22 cells from which the trap `cen000100101010101` can be reached, by label: 4,449 of the 62,914,560 nodes of the game. -/
def back_cen000100101010101 : WinSet :=
  { b := [false, false, false, true, false, false, true, false, true, false, true, false, true, false, true], K := 22,
    sizes := [160, 365, 372, 339, 171, 249, 200, 457, 252, 364, 382, 216, 363, 276, 283],
    rows := [4221858314597802345482829702997725095541519571615998965344557441442666658926048419794315313266431493807691228172125211202189424309417221904305530614024079363986728819415901272201371617260090772201675353326786750736006379147615084111858424230495799933586900643596906041136160970737891361084980566436429078284617548791900707989819010993531148798574067124557774417884845492294132495408676588839914813530569920675306426609112704333490583649818223199932287944929171543633178074089901520302273777735148811069275753200555614941743747581954124273286660699035671680982395816066974037555412876668231363499632270082945621132760018705917755809877907561225728097572517287241190592137376068131521413622119532366639411219037372319944497301010661013843097650958835752031695616097888964350321622864262318075462705301795251326465391203169148000871805800687704154483769484405273236534766237704357944160085761944024494436729933227175094754557343838116670582551951971157922071458558771432723948196890250395190355726616791553062981466652438704331667091075894119555173110424577012656,
      186524212274325802131451019021538674084617154613638536905265819251703867000197808740506105044807175935311663532745107893012129483605455432281017529890976058858846343036850735770186666080448773943376861824507612349814337680066490722202089336896462976235001831572458071338340734657749550425446604532858333157408389983756402421664591595811895009168886412434307030189093080490036256244264311681486782258795297559486111211450236568810709990002638214210288032600668416082881261378881967606528916200345007450553562875557895695704998447864505295415294064085028619721513905606106116999753496041617092642576538616022141342662961885955191565536477250093790955113822001878311821240055019913741970742867935234960663237331195280888296155245318022045650928921030073465801812856681908858046444519140464836395898622495399268675553849126488772988490226296022005907492208019523909674684105630041988106433344766931637592840988712715452667718300514327614785128070113719063340411266336643500884984669305503444866700789269062451485142209637875189335259277622004688598875945880865570428401857847928978978942560377595396400808966047169645340250592844763139317995677523804627340056568316312287485818321592549422798414472092038740213390761033514192163209775953503466127040686729788895101348205837422396179354982337268618184246687832604059929706359291991248941708282504550572770842479263819032054780750084264389269150143835815089341145046356963050155574987486926913851801690829068976467791249465572039189203822063145295643468113528327910728304036799058939273208517462429802383972299620900913483889971665360553418035509719460152316563124738795619169336390427254102207148318167135689993531445087462417914192761714096503729500210817937733449686757238567333170908432953419713898517703500012748240066568259576832372795621250252743113398831175392127083303778608831950995678324475436979043425443060868163398815903147252259879434397082485802427812224625646900002054143297127332909729726614114181984212859123831172742189426329623975929619914536054302843163867151645320971135366726466744071509258173089217102590944481815196083921328613006148294419822839438195880826170920040679089420473199088029312677579651117583007709735675444855873875635379573795675247924655522542334676765510773512461018739924073844338630466762645869267161405575279616379154016604220984395522687628733699978319681338539053168014960178081383311688703221039540754994000075217723042301720,
      4257269878618180282148793432601144926684767806435185120635468878008756177950520168526332476806960508796510199357254378001126333955687843330633472223023152759672326598073336109121281719748111284357222391687579582539802173113463914481423348364221011522299870220616891921579353140037625794290502195693380830662677804368900893615237574520811955413950375778503902555218549319562658207204253989643899538076964860411822308955536590199477263912070486260235043627129641132490280655090980343490047389449506173052518015030410978238943266610162141130631330275888590958762644043614274631360216772421309733852580606064883099481452337107441010066208534994623117718591475389277896411144576858840043358590409800372835994928980515325784954566361149019435275224981694188909881805380354724568591563670290456010132278454198339811970357257401226026450818259598279526151301170858472846768599144638837473252801359266244539319801041765056654170308503577875895845771151370497523605020595162963082952163407211609806925288070233704636208254123713274197158467238958623890316361365310040338784369980571074593435224843160567753164223435248786118077753611800914056800828223983740271919041118636778664892191498370757968285220879152975207517320301576634015212398525502962128933051422936748498873238005244716342749064159529101157968677724103757399273873628707859159388122259550016653537357863425534098675749088503781875127526609310197553882742062374603976741673975140594113971887361741506819640559834042981611690672135396497043744069469608710987402284296573466318851724647213804391889548211043708024483855341415024738475324913791122759753185352550126484207965366140571978800709979885294711853423411520365561956782873223158411030872785118303388249676351295518016896931341574303143074917199396710604001734762825519523830588981975794523655825820920412469148114726134813547018375265030781288131000323869017362446117101295912662864980291514756411760151729053284084165023689559525006918328198229843105079844414347547115062804651342907610558926552609645336222390847939163976033564714710391453722133408206465313125024238132233297827098127418189276069863299628803144800677422012959601872835774491090300141639957858951587966160771757871299936921895153739094222575568726542606775891105979139455498493699199108008100903583542005378049242384769715344262677800734105666793174268477088135932775425565928770950151685844323184817048806618526228087052785348686046256255121925972866277571195357940957626871886553024940,
      12040655308852381608732368596031974537981307546200709264190151780575741743616089588845200397908779323708425088125144475411718310642193690599052354810367989882925520035253229993108857591692081616412283433526048303806993448789779674057471457241409620044203528884666945772213033948411087583833129832196962898688696649093563410940723937662901804650686350251682976635788987887707697157693697708205657426426727513655007318887932987491471570091587857595838506525085114725225259600362814217380489084649309286245248913923615487948689338900940829287411666330700273326467655736296489314140602838706859078993628067745174052289693533055885527171018270782272309274184697750945188569346944321255444034286777059833059548973962417893073252438642427974781981379643562654388704124974866863281928971953058957848794826399594053222448831114542324182502945865300306381112712802340424783323965089773266319827655968428361402787361165954486058707303562997669573927682459384764031339263509328722837171191488655428169557035731730088603875813912391894138474226914510043884238759519693185655299499923887550711946011356739576854796452357226582863599521628764795820715861933212086620923075505941188711889144504318557990592356143841370117164872107885244134983698934821063532868913821108946184989291593923218817510483441022061616601209796796021584807625964749378411367109505714670435470385146067292438681091322928353085849862196306127477775104830662873215525722526263902055163068679143019380093309513567307988136979927496166752463253131287197046252868604595733475565837984837851416915379561155605457657852174101166842253967600321295310485857107385831682826241080566520886953050422880999045876442890961977694846013424768943635427199067148931933459277823063399592485938423193829130823044985324251305777338894949384288638347689333372438752256886758731243120985726673311054715917323235013155629693874612661382257125042891428868268334938324311841259011499767731595256359687129514048182906543278351049458951230706575269745172495579598392364338518896227038381776975619706693099845272874430286949558995951835997731925759330370582621247454737250365489080999977437387736037337348512216656036371905550780270840152489972761677927698735951829606427346132348612004446763901398782062465493507750,
      29647238619434584243797520373638212165208582039076503133734480074533071470314282934424497059907708621835866421194632687452921972282980776598544689661481892088975799622776753259432880678682414336885784965203523534997708611677306642691447513383541475563570897766834406497472258104212178195769943164619834281200552349181542448247251345837349820371124790328911646679805168780455255723405323354660894017926972225574095300888101318933880165817687945018843675850720910765855940403208197970687637033163991013623910316342017619747764618316428202625000224794040264920191378300839293828942630865613729625643474012227491332307221960320721556837545995814747188828284963367792608433545611653349145039375656924069314531180405763701963172488608967378078274636151106457431740950315688235328672400410306503819777591574133370033826023102210091210371173263146725413441392575876830195343292950714655869251668544766651364202973751075287804370320375996851454345231699781290038016238200669278213159476537873396084532024835150194390558636012342971172956812696087664803727022285370368502171117981426376526891084115158610116435105747495817330992084398054067322,
      110182108325686561186896277041343373789043804809900789916344886102756296484656625111559385556792886284446595563655328161784549843542852620110275458165058432132772028429931383355418632086769426619065022886693320277486710298595641864622750445050310783429550450707812942523128217483469169711423880165096124303410032797297656222390684957114729269144238133441991223572439254184540916908688044704133215204744626068489773890061016284864020143762254686516705603900010218691394046159890331971206166778965773646267610812934149028838335794062137156598584187947252441253585531007070256608536491377626037487963665709830383437411840301035768536458393252440996084574038393836696509046402116091176809250901979437331063503830902315005867374775660012800786533928145915354171291308223772222044302691305280262458459896828593420762789898306721803403447402659115091912776061435276674398765402420356969251341689059024265783456742351866905898912103216944033607345242533208777328214084684887659173407232579219736243816198486625350881694550327787458915629765390019521972483600443835035770386123409640960184461728911250464633658688343427550534107414135144005685499470970521544908974751904793610891845767170756241045120529664095189873600441603464241780856904902043465995697682606054955507208088941816970414236895561811035526376856245736736772839794729078902653393479878887781973856251780603691627429062559751753671502595695510066769730544650997073408088140802759868569501519253658339053237049254331304226890579625641265389118163039815677558450265783850382351388954219618133389180420520238857533290853767706245443820466341226484825153215605611794248202447714924320124043947679207,
      34023814664769256474927571474005944233319021628813833627320590638887832656948997354821775897356091542216869398334992759066254561038560398674296924692099609829243960224050839086325200760938878791432683441748833622710539003665299628008055347070783774977452233423285447279498094248642940464827706690108393407868340085842853827892961180734842443748843819899360846945987751765800276249433594450426756287355402067698298809361291188178356886188530721462963412165854008355707531566888805706760335014602717623489559823590210712009226770805443232805650655976838293036527386292246064540992934793614864526382504182169303374931572042356660029333682964157298939206204943917579825515944678520909539185440837360888504293810700360420607837996518259600625340355710296493734622175302528402161054993264449347031676081634943442482834013950032153186893705334450030741614551974786580156855681936308674367973572086026253550118897372235002028556557638133151960073968885513048718010216447101742857611855668330765708289800491736323238850762660132516680184818984193265130354666094301910881450177120306004957263902213967944946395955122829246870231317635320898309651703407818375961079634441484511849181677349773318477385772884720303357823505362483954181567366573348245995836049609946097762918665429063558497573751556668165580391173234198480007954270522599,
      359228445248967687081748909724137906085736074309313478610486383551179238415161913850260411564081598517905385492770992384428593932207591295996933613609803243703855166878204340411656254671584915747792422115377447477468793795713377419715815350800979837625198913457792076375573545013595257471908580053670750923494204380641756407120969889961121055419227392069260963247488524774176540876848606410151356370221684509998012272157928525759331635603856783133505784035299110717544025514536609128769976098229795060996609245113040680923060394121785249538322303603873933510594455658333368088152591787276265415358029479974158542174176876341831007850275714434031186940130601176917315884149438098669072778017444860098184834514449778628266373597163855727930249188035880757640597363770934485449330945815933771568015860743096826951734669847905535022954421155430275688095948087979373954611853048234111603560488109715299019226798950208648763202859024301085058513173263419959979759920899598530505103952127184434032813987131921864201389785570226825125538501227978348825288140668925530031764513225621545558760068498022912606016898778106305306436330593834400787092464115240442704135412821572290705465263749662658866165134101308152985877031665069580253632169519602014317991137906786914621014241457906758194013331880808512471297308754902576110072845909647153093128719917989219777273300149949261139346866001353230101503380272283161911357404288133244868081993367068769253421972475720886546467834335105264407810247852010291538770836301237015789700592966489375259600989025700910345406230788658999050492805064495579783331405746570525888048587043344667185166897929893233938713390150026819249314236736019801289805117167148185799650275896988028420968493663624183990782779795739307398393448312139221446481916271347251694039643985219941279044399378878844970439212206059939714733291237542272062823614154271706510506522747776088032942257189345947299779316149690607818573758322079292610731459777737660418491185382005154987789075080604516019206544229874441015587096819867964431460888926256398785328115554787698144074601028384297447747191610677822950256403112344263148444471397992011730058732933190252001274361810753371493158306320720291550150374771471211081542641574400487295037266691085715809497153310183503874943529524151294927613232248078608145628393330755833100426039748821507882898489018080997795004019527889557575154434906820429534019032390798019747426357653488707434480357106316835399725761966548884998795166886591307849553304688085811446474245219679298849752295622211690547391728779138161088148147345572258580998772081997394782757413717079996904857123782939309204795392744059856405545874258960587222307128584693451676088912505366239152209015168676574956561961961964563730608913944529100540185824444867748842012831065974681795923195066295166279766294615458499735415461141094067392505369449306374587629702430413126443964695801991293496013661036374288531970971282277735454126836576032634384377724296327170379159785469224230971587199459547680723508794361285657495005,
      8128024624556694625406235805548553958849553764445055474825189426378998136036104076169896254602819763597056962379206097262556966208980171430383341442735206867308447086691664407782958085001923723761256151837955530681687326537332193828329063973554800724184247091531111323291856254037087929946194405556271388413785195315783004262715606123442099712388138880160394329139068154810287650408342781202014110251517031702587686216784716417750344034000905732960715429097022037151898861742738848196440953011295106401629276229657285929866639058197619404657075574376516561106368580194031921754063736850457564741290913850668456797738721938855564925529726208013675025994292605581339467693509038731058621513830771846177353125660025019146170285843652805158642440685677087431977760640142072568770881982746449372126652582049186232752206017110628000003903471700936965999073734232633280447603162981938347504672201894592642975359959014546441605591675062612769220272028724317562617735007273041077275716346703958168388839232978130023594180025775163739055740578957829890064367868602807263917886289595401252978538338284516473143025527427843662215631476077894333949885173920619053544048374956385950100845655337542501185977563711443722131917525583009312280943312250837262356748447640076062162099252745274436562813113295919431065948642356136100501035374606762908684394387758533751264144817641531510328515223370108154859024609800314587964179402541266142730816473688798151610008478163802412575373221854472172358862527902615951139349175997252991426340131947514583103901036826469057652738744906149775987276467858469595369580450413652594459364404763039464074858166168456229548286649293787761686601564949573,
      44448650232202284426232706326018285269220651173955013829442277780839268062317784644994725810489747254732415724473271485364445568869908418790158861614761620192441267358928855147561681940447425174172581951359483979850932622979554094003775825183164732707295828747163693142247240285151587190890069059200802437105234022325255172436445528656309204198240617935276831550184507544207100328387013919169181548794299413787842128814970872031779402783979201592505302011857539344846374719015260207416014909880402058531383389386601733366034724427005770422858033918725377729068399539387574999386671428610550915669411265530614212850286703970467742587033093815563309413624058822298908674224402780329299123426368843141134954945930615970612467775682927794272238772655059832747278753106535577548807709272165978985528092303905120089596186313738034433281233238938390082423178833636593747467395742687340723349679856687503542888212177498545217579735656242489998209732695382898513625818668213501877569096027172583962672809631434447563424895892858591012663745755287150652424457140572203129233666232562965938089778566702760030139466732334501069024764176863412588715705778918569660966105379743689828388820410751338846820364568879616213197583152903627069067775115595147602153125007355992458758146527434427215581254216854430470150656894521529855095228842058728097851910314336596239920810288989936675831601102029426845625842985261856203159259094745413831296687059466705598242802426846168136451092913286693384371289990503779464831117190612188581467642899413351020855482661879521888622709059164573968649348881340518754327246695428153376758147308287397736179589014570184674233244918089840220689974483103989702999270979467252644621952413143021652350884987883716185172436215055736370575925699047401774157690280403557637315381564375376234761554371851880835042695310749784032498105804289960746135619603597645302487745667782596426956188997003819668907328706918321457370819001588014943576170103281655901464595194405993535526072716817794037275675411606049110123823478403718117092525525189170678233408493596206044193077499456092467629067329462150674847735638588232498470450672366250819778399852284293653177936881454714917527758466816296557591503048690003236392798748238294284276771876892515310326516319574457422555434894170892981670365793148390176440351934862879336577271157017046815005853034172937286129927534545038762879528948377161396608955815867451884,
      7179135825072921876336450517762672674936050908565381519657998842894833429573262978168177734277990170161114565249009678473005083707179550900502392112617882261970011109655336326804537098384407313801675810537927119745275274890826994605312783635811503107387138165264333725814469722152390829828405255291680364746191529772127280852846071997310950339446035623859038383130664633049428258958619286083285304372034825131042256465958159572311493437860264757559127427823116129784310771461272376131516109139475393067458137511084560251015748923599583512277515992123660617086351225672521052198673533538007244751698000648920171228592972972296523227629003700232286762270614162951406700818764189488178318641151684850145661338692001568420917982366609182406105597867997953084453603181663816421588830559443628481311104605625740133373993065582065577281910025943514335440617698696999306377647909244125387495028318296964352166409923135172085086504286025663904969678990294587136112029424101783046986493998929150192357869541473413388579816296579798006665986366262105732349523653130463777875105547254349548907485143526661374190344922293534736405243615861716800844660136845955264680848623040430428611902975998551354565741458567507765545938417849882075176146181825068035516807405509067240787882082400410736048733223546477500520720786194483018608831319429466407855218846394798384041525198836718757170116543926730911117019136954804844627969802933920218335307351733934669490275731140773824753604290156019348220177193800381186281505959541356050397630969256828586094862292139250846446489034385113908645714317004555233040545400936181632161223742679088852236310258919837504200639184156680948251145891439279081241770141224278097867089155969499718461008409272690806624820704661943063876160352047807057391260275471113649765283888372076067315786884925669350737687812179624823110666740713130886112518154216330883470844038869118534847892006071444022340722187479990571665764356507556763693329078417254159415559063623391404035057471127282249121385136878417307306821362850370560874116169257548293879308172930430871382906348849953929837183362810565091640669032591206357987865756520842123400745061922337800333033316350057259747804622308714229661294544594122061090252814174305437417978800957857292500733352260587869888369473638059630741645891595006026014073679960981482616724704790227502267771331300037461992269732573357659936277688181735708550673930324728625436309246534452162959557454371026072185157421339678449692951258012559919418757294849926200145500780010281588490500046922,
      312266663614982404381081642199490582111986472547129367406138535872460126668915685823036842991247047337713445497389312002477858587620414424269224702156857811796752944089610092669626225391695469726797853428643693983055632447995872563818404907455580559134671373804011928793814698174952750696244455731080394087710619928675183842327514870344450198528951121095456320779342746039047993658489047623409137689083215976187351880427399423478936909787344677155327147037604860343858646869301242721623325897972212600902709060989513359178429220688627350082044168641136815699696343290275888489895024399679604650867043480667504235025357256966808770350378482201538718776646526819176690958581407652802275607039328806198206110781848478747166545202153983372872487053455135607229450065526224653091129876332063632946116763391553806043818405830036428516368450783707400980323312384923065650218801207226332784706651001634938926564792662171998569867199005867878623362524750101813032079876385569737792200972902610984250318931862665375627828289650089217250042233288996492831964414451626464463409777665118893435986507402614493294665969161234684635230383689151635052014253594603608941348179729750978590631716422250062241694718035559298911922673772357222214549478033235277484503895586815685043599570441471368958521833509513958741971956164603624226616926320253528392884776824309710601649940040245463137225274080821585248174698545191531074208001609793445846598025466,
      10547792501877931037493624507149288262145909207472485011744810299811768294383903214660076252318731559703920886586444231092729007078821004054585000185444508782908921495898036311872131511294106340174668939904568496516989188170263384664220503507365542008849462327439725134277559159997701236745617096998327594931349898487541452859725423591035749038925523803137370596071511623902468123007551333657580625443190844926734757166753894314749735640441671160415958198319450819980032857214232518031867283389959794586481068372413417773907201982808222344653176488499850479581946481707440017173465324165766225731992316643382338557928924625562611201316898053291768570037742493734218840114442193731105453284661687015137727798720394484319468098746440790077630940902892763034407805515638362541493545395897201451665592399883345420043293620156784558739915444344944968695213268154961212013989224890835755819826451236281581197162481175322135671689074641190103950420980312889221698292823501134236005234521379704261870600609877419738592672425056206476276661528193243607846448066583295090166449261287779913504892477526083948730288570307283402502016618449014687297553260549592667521006765155063595531561397263215246245606857320321925618004433207007946051179431168764750462229958163296423673094858480905491799047475956055708220347648350230233736053125662399430945189528336963976331714772710027831878246890694719874797411085712004313752667160189805013989377458475917194129085883960857560566972420444722987051017783085339941148974460566911823418930456706243053239932100645999469913578025832605162128829826694077611878913811356417910871400277394713597418032276369540685991226249951444916156700607401118723731428633205483280934004557772133338395587106273179244673687813944176123383833795918385399766583313726656428259274992911773302806084910680174467514155867101888160181672538652086765555882725411169671593672732141186836569749940575981744851796359355348497780902139687329767000075905030923243589512732038878026398299401994695595338070964326566111317246822315011545050921077784860176728380240336711046346157781863316391293083357044782681662282920460762335489608682255298844286870634083900884443388196908761817577431964132349317771729262757221678889996918206581543536034473655694189635210939931224078314151906595883966528603530740303886112741288391705523800876543793085744960337012608332928665793936245758433722582383183256000873986261259,
      7146114772788536142478892971381721523056221857078260874136019882420910070436322455413270887003111507092484712930922971456271001979649665826690555356250778882767533354357579428651291888042338525889060574956776811610027079712487607418055601197631284581235165462317695445391304732245872313718009851532570524952791033064265177150329022267662847624315523843232073599935427357910279736113059923753755407944782238231880655168665742098049163693896872734504167668781989654909847799387479352762432335875756952639113384834930462595996509389253034533233937785296458659990224711023698457089842077856986930241800509590300294158030264541068925885033834138970609812796060583521425904174602368522371841631530612266173255477253976320485874560460782273426095952942248800406798436005855716970617810099227030113583037734242388186229959472106083575952232275924301274483891122277291683861488150753792561300989939008019950826990904509940253946545986765599454168421654744149970576843199671581444420479892094950264717753187328991672672105476633398035419750486695038769653595984626473469513421183792699019429624758990448474301781438715811944754487317926787448559038996586851010555890897076182298304703889754004370973663745251685807043107093784459748876210074233573425062367769112865084173764439278846344478968909569689953276859812696226604185569034936086662075205034563350168791856279278935854411470131440619679754012394243777296168576740395383135264363109807992462850994282709604023425237465762250085156835594224644201679186019612271430003729587092633907891852615203269108917912926672178196424588212012766452421061926988085900104053372117547560476420131892626249353138192362596205854807984076158094178581214702445454125272877658144390324384194504646657425636646439743227117469410390537994040655607458706135837454770351298559067962038562378814029477970840,
      162266917488055592163904838489302546929196742788046381364739864764932855275416110648214641722617579162468442661187633415876223381815898314430117442872124644709060830094756512504541678474274529550694196694786748555491706755121210516519381618532350481372312037758980724885386532933843053764788520640696737053297518903063731275557370481087250445293301225706241530514162912186986757255900295774489119319716739201698587887308294186693041776160915838376044070400640934919600562036865951387667767431117084118995881947548522338215591546514927465863672597052652622942605165655698075893875973625793443732220786203842938031276873017445103349045246546037387517981697901424719533498772541418021364601041206579256122276690728495643498525870839322992147503988197483467323262598550379112076489678205885544281329970406036896142525900471973707293535831768224682061616869183849490729717479560296820697950546106164393623652458069632474456620425763478163306552031673853275382078403913047555804356106022391259074752102131427698118719661179786218467666431612129402762197054441785141978242598707617167835237852290157857809387509833543803204646479796274556709452486980600702941476894915684016530398015917799011593508788939624624691344295080933214426719113242610112143106747837689384934262803334749255261028646356261368484756305083541722396982689485866368565449539049704721831384323465159938990469301416658922432256181506333837491962015746575367955719956665363388876750217564188826068488879957086093628104219791519096431143103769052774623013374424622934579684179282312166572996272036054682838610034436989594753667112699793736270810677068468793443850343340544810991806580137845817677439617557211342840344647731241392702468057494789042077545845800241118263883230004294762969620769517797478350238685385969429348486587082680670522168451057885245860973737396769322055436851711491419189781172571133160981740] }

theorem back_cen000100101010101_0_0 : WinSet.allRangeT (back_cen000100101010101.backOK 0) (1024 * 0) 160 = true := by
  decide +kernel

theorem back_cen000100101010101_0 : Rule30EtherThree.allBelowT (back_cen000100101010101.backOK 0) (back_cen000100101010101.cnt 0) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 160) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen000100101010101_0_0 i (by have h : i < 160 := hi; omega)

theorem back_cen000100101010101_1_0 : WinSet.allRangeT (back_cen000100101010101.backOK 1) (1024 * 0) 365 = true := by
  decide +kernel

theorem back_cen000100101010101_1 : Rule30EtherThree.allBelowT (back_cen000100101010101.backOK 1) (back_cen000100101010101.cnt 1) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 365) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen000100101010101_1_0 i (by have h : i < 365 := hi; omega)

theorem back_cen000100101010101_2_0 : WinSet.allRangeT (back_cen000100101010101.backOK 2) (1024 * 0) 372 = true := by
  decide +kernel

theorem back_cen000100101010101_2 : Rule30EtherThree.allBelowT (back_cen000100101010101.backOK 2) (back_cen000100101010101.cnt 2) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 372) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen000100101010101_2_0 i (by have h : i < 372 := hi; omega)

theorem back_cen000100101010101_3_0 : WinSet.allRangeT (back_cen000100101010101.backOK 3) (1024 * 0) 339 = true := by
  decide +kernel

theorem back_cen000100101010101_3 : Rule30EtherThree.allBelowT (back_cen000100101010101.backOK 3) (back_cen000100101010101.cnt 3) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 339) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen000100101010101_3_0 i (by have h : i < 339 := hi; omega)

theorem back_cen000100101010101_4_0 : WinSet.allRangeT (back_cen000100101010101.backOK 4) (1024 * 0) 171 = true := by
  decide +kernel

theorem back_cen000100101010101_4 : Rule30EtherThree.allBelowT (back_cen000100101010101.backOK 4) (back_cen000100101010101.cnt 4) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 171) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen000100101010101_4_0 i (by have h : i < 171 := hi; omega)

theorem back_cen000100101010101_5_0 : WinSet.allRangeT (back_cen000100101010101.backOK 5) (1024 * 0) 249 = true := by
  decide +kernel

theorem back_cen000100101010101_5 : Rule30EtherThree.allBelowT (back_cen000100101010101.backOK 5) (back_cen000100101010101.cnt 5) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 249) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen000100101010101_5_0 i (by have h : i < 249 := hi; omega)

theorem back_cen000100101010101_6_0 : WinSet.allRangeT (back_cen000100101010101.backOK 6) (1024 * 0) 200 = true := by
  decide +kernel

theorem back_cen000100101010101_6 : Rule30EtherThree.allBelowT (back_cen000100101010101.backOK 6) (back_cen000100101010101.cnt 6) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 200) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen000100101010101_6_0 i (by have h : i < 200 := hi; omega)

theorem back_cen000100101010101_7_0 : WinSet.allRangeT (back_cen000100101010101.backOK 7) (1024 * 0) 457 = true := by
  decide +kernel

theorem back_cen000100101010101_7 : Rule30EtherThree.allBelowT (back_cen000100101010101.backOK 7) (back_cen000100101010101.cnt 7) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 457) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen000100101010101_7_0 i (by have h : i < 457 := hi; omega)

theorem back_cen000100101010101_8_0 : WinSet.allRangeT (back_cen000100101010101.backOK 8) (1024 * 0) 252 = true := by
  decide +kernel

theorem back_cen000100101010101_8 : Rule30EtherThree.allBelowT (back_cen000100101010101.backOK 8) (back_cen000100101010101.cnt 8) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 252) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen000100101010101_8_0 i (by have h : i < 252 := hi; omega)

theorem back_cen000100101010101_9_0 : WinSet.allRangeT (back_cen000100101010101.backOK 9) (1024 * 0) 364 = true := by
  decide +kernel

theorem back_cen000100101010101_9 : Rule30EtherThree.allBelowT (back_cen000100101010101.backOK 9) (back_cen000100101010101.cnt 9) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 364) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen000100101010101_9_0 i (by have h : i < 364 := hi; omega)

theorem back_cen000100101010101_10_0 : WinSet.allRangeT (back_cen000100101010101.backOK 10) (1024 * 0) 382 = true := by
  decide +kernel

theorem back_cen000100101010101_10 : Rule30EtherThree.allBelowT (back_cen000100101010101.backOK 10) (back_cen000100101010101.cnt 10) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 382) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen000100101010101_10_0 i (by have h : i < 382 := hi; omega)

theorem back_cen000100101010101_11_0 : WinSet.allRangeT (back_cen000100101010101.backOK 11) (1024 * 0) 216 = true := by
  decide +kernel

theorem back_cen000100101010101_11 : Rule30EtherThree.allBelowT (back_cen000100101010101.backOK 11) (back_cen000100101010101.cnt 11) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 216) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen000100101010101_11_0 i (by have h : i < 216 := hi; omega)

theorem back_cen000100101010101_12_0 : WinSet.allRangeT (back_cen000100101010101.backOK 12) (1024 * 0) 363 = true := by
  decide +kernel

theorem back_cen000100101010101_12 : Rule30EtherThree.allBelowT (back_cen000100101010101.backOK 12) (back_cen000100101010101.cnt 12) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 363) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen000100101010101_12_0 i (by have h : i < 363 := hi; omega)

theorem back_cen000100101010101_13_0 : WinSet.allRangeT (back_cen000100101010101.backOK 13) (1024 * 0) 276 = true := by
  decide +kernel

theorem back_cen000100101010101_13 : Rule30EtherThree.allBelowT (back_cen000100101010101.backOK 13) (back_cen000100101010101.cnt 13) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 276) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen000100101010101_13_0 i (by have h : i < 276 := hi; omega)

theorem back_cen000100101010101_14_0 : WinSet.allRangeT (back_cen000100101010101.backOK 14) (1024 * 0) 283 = true := by
  decide +kernel

theorem back_cen000100101010101_14 : Rule30EtherThree.allBelowT (back_cen000100101010101.backOK 14) (back_cen000100101010101.cnt 14) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 283) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen000100101010101_14_0 i (by have h : i < 283 := hi; omega)

theorem back_cen000100101010101_check : back_cen000100101010101.check = true :=
  WinSet.check_of_labels _ (by decide) (by decide) fun l hl =>
    match l, hl with
    | 0, _ => back_cen000100101010101_0
    | 1, _ => back_cen000100101010101_1
    | 2, _ => back_cen000100101010101_2
    | 3, _ => back_cen000100101010101_3
    | 4, _ => back_cen000100101010101_4
    | 5, _ => back_cen000100101010101_5
    | 6, _ => back_cen000100101010101_6
    | 7, _ => back_cen000100101010101_7
    | 8, _ => back_cen000100101010101_8
    | 9, _ => back_cen000100101010101_9
    | 10, _ => back_cen000100101010101_10
    | 11, _ => back_cen000100101010101_11
    | 12, _ => back_cen000100101010101_12
    | 13, _ => back_cen000100101010101_13
    | 14, _ => back_cen000100101010101_14
    | _ + 15, h => absurd h (by show ¬ _ < 15; omega)

theorem back_cen000100101010101_holds : back_cen000100101010101.holds cen000100101010101 = true := by decide +kernel

/-- **Some finitely supported right half driven by `000100101010101` never enters `cen000100101010101`.** -/
theorem cen000100101010101_not_absorption_back : ¬ cen000100101010101.Absorption :=
  not_absorption_back _ back_cen000100101010101 rfl (by decide) back_cen000100101010101_check back_cen000100101010101_holds 0 0 (by decide +kernel)

end Rule30Open
