module

public import Rule30Open.Columns.MissedTraps
public import Rule30Open.Columns.ElevenTraps
public import Rule30Open.Columns.TwelveTraps
public import Rule30Open.Columns.ThirteenTraps
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

/-- The windows of 22 cells from which the trap `cen0000001011101` can be reached, by label: 5,728 of the 54,525,952 nodes of the game. -/
def back_cen0000001011101 : WinSet :=
  { b := [false, false, false, false, false, false, true, false, true, true, true, false, true], K := 22,
    sizes := [326, 336, 551, 501, 522, 422, 261, 229, 270, 449, 734, 593, 534],
    rows := [97071173141070691509838743373190233424262657536613397347862639278867671409085750739105738805603613104443458133037043795354587457763880534942986973113590202842338870358066807485983523084276429082859057737794345021504689579807693674772206265198582248005374591263266139253757739974587515015323541273013427631526272891130414866631012293101811219354967597614461408116997569689875482075215544039450042133225391140016684150966373254157598066371152717530453340460010337065843571808393113481977596327123353782101029353773692141171359582040282185091720805675992523923039025869249152754529463399037872781420546603169669480760617736520290760079954491100463253757961967489495535085784114575516255608901307297252356773615011852348381378167922687756089955593475881055542741017526777834266172482913008582658376894902646573253649512019223969935639984151200427295355470315411617532262503729178956648170287250462024278628792762802798041960823704907774890575891779782312771944308862601182449977422875126189187362460471391353045315766615333791148837423143012239081793877787699366328210895378876720437150516241567695396791620457865239484159192968260846656863618141991549909709809338576255181612124610559608882693261559928296666554907061222445520881813531551165077250522566248096178256627409657932450522989428768658984344221914594985598402815265564104709985071654069443141316933400506250033319616816175172951442944761452076720620355584789480833015188719697051391008751138936630475844480049819537178978046102431212182944890290205283679943062825519046227186847594285972988785744813435693082736621198944139521859108330284018154315764708928904925838717956797475339671786782398162716262662330151459916036468428157758297796814929419722418367256404279350849612539877767452669009826596799514355490119579760337185830973783282559833727311279277412956452632537121115320677039234678348996472650442419641556639397542141813920836686748204932984993718687081889561911603424768238384384166127329367689330315235817210799456429588016350434001195327590827964099726721662870124589912602227427145423080501956437108325845437490446980831197140514755032566603046883013972319188689972351728718141544858648970,
      162939584124495113404184410103232991082530386009156189522427650513165378349086844818299950937569227753075604785580588151239169545970025417819207328802166487793035860611991201276650137715428130702352828583953970958881770352113619903496291004172650546074584279963519449579078166150995071728212825848960898860213851415665654749203039698986740331812716162710956661479905623454548993257724995881661080315792055604762492659939612519399455240524896005175167678035060249935797470092552296669466360429273791045187955853025778198316339887182978935239708048330102780457893128365215014993720835269752097390169319689125126220071321678816742772535594260432596077896857557106756244794349212554557560467964536008302830301726263325513125285348182117408200416715250941967658013784029552077578946412830490409137317293877057195400086783964799929305130413055430272419738660008428369305132643233437358199341515825464850110293885140162617342407314720372166879865340422188919516571449131795931975497147876688914920303653592421218737604645226228612823166593574407696483617338319266166163798417065977842405704155674817480988020006582897617064592704483833085975527383203696267650131108097267356147309340779453533978442453252723088852631534814589845769439410703369178819516328963975999652165450187350649267028229972615563378875018132260066441093469665076931080736985867606569293305224692334945049537172406863452258718063873117596008453541492718972452855641730518539902518604269649867682806023944556533859144454451816568932025516171916806143405187806272729596022189206219822707088109448256610283426357698820977735797268715457865786092685888797723775406982674187834950268993562314487871418887836785947370006274404776188266130875726831920697110796408148675813382413683897213664750385355400583819168385206602443620393165910302159034951736341211858817805434689016412696173283717464468607759332703913200777761057987111261548959559375335524167040504660552106973646326183799232856994096630512316085956965672257387987150956115806296800120037751376891121717876095638023104309485955773824105446862094940979420031561654282593199367794296463974607528742231157714073414519622549093752481093473296928582118966207147718286443472019200627833780617742029212776598257795803,
      12172683110019671857514763165498139976958117876050615763592333102490641087730445106784697073390011900362975051049858590357268779123943395171843418566739684183486387084571269773825507410152993850478852182834240686329894952087656722275662906992968926596877896117448688845928986745939767273605312491321754827319105367138410825096587342088637976812848925575745056809397423597978893773116817601068858480697066813883620507491382215652136600053376998208203764777356383428201446832990844226272916603927096442280869310995294981061551552722677014106045318341608151500014646650966397466295290219784848696837964903657430074184104418343094444623165606589705414095394710222578507144607211856872529864005197728174379137853879701737612587326074507368196940803603587872073917863294320963777158269253167930800923038488836624521692713048545528381874014798157516101622173433905607675634212333797665225359075188942894549155544497695111003541909928476487792207960099792175686665909062624275854405372286087672634338004451421762441310520238402268598231744930471910543725818867389477525515817219413917718651492905446595951829772425029136497302743093950086709432152985389529930388284034074817044646972046624428328166571030916891052812362350832707736531332767506864168557024533178637658289271573657188483727806250567174504367537926588894954522433920629649536979222607301574903762372851455018158368030160832796383380987974435868679831597921317187330936654332080131347089196186568388662142854957574535602126890135305188523801877388210325693732970387746457117332370638133478309991097546296941437933910040744840748502668869564534433335482918212706162584461525127023613317701548220656088754727993574617240259966963491455644112382897338413013883914596772703823234203136070518092437466603201361248241537941961890430072487849016258254103773678674150006616831622647777342711116742090671639980238366963332778632008934062749119607911385703390996638354648209983219383933159268424884993510185736311724819816485728332464260663008126244352328549549458039005043183638540895851231763387111530143289653050920945150641816420324072794819006055510860766363769622513068989837315212085554905475874133774949880999142081521473973743267593126424444512541074923871135325578636863101895806219853645237038061164602298668473256300719064757776333151231874253713986525866400949819164412038319003613597568092594518399381655971362259609056096761921197654551030232391414764303248595952294786778144010414088855784863921853703521039605312822820910873973555123563612346335872894437352381132863650565040074083399770572291283664606921173726490134281550412697422596241201316974219243662564050885115842988841993288946078102301044430199339651901076081457548849329987122903623687399110362583603940976580876493208326853088919421421784412826913037663773316185649714781002288742289577466940410853713123504298791027172379662356253055270210379262745905289873199545211743697668429328640471806813282907950313841235994139794219429772324724744712068591161565247632592680452357893775453504721817761854990530325665898196493988966952307546304264823094269026076542906885175854703280954512446127239772542991529077841033134630788703880534609888697217293815692943646242546378507713932905850735230238018263965199804717853383360940502076571188864043546813575241544046065788992744359408613950970208116100742580026017017583058027299283773178802801782523735931465024416161964811657074190998785333482024427850698108117717088100479402949074817936670503702674977157550642842395454170953106223385011735651488272346499938210480071009175102574308762255477633614972559989445722907200034794442979086718432218604969499533282373303543468184871458834600,
      895931559123250311984081845870896722930221790574273822716039527554506264254121350717763593779428828748903085092377612834904970495947629063523107020102576256420752450287541945575732402338957515582376085288757945491966083639060153218801327236897843827958526997092762116469533174658741953036402907186747193126457868021379538456822119045351591725201755292860212194456583688160411745972283968212769143412558096336095267870220158409128284423966853531694250399077143930785938296299989707211025602571027625081247954659508759043818022838216680815389668382785504216411371099899465989593770119020507991920708308385380947914477475264963682476934838818036477286303598821836689092581516251359773300669119763388519338790853094640440535077613439625762096563122906387105751592967842843922819161764293383373694940346380914575411453325914673195318738955038601461992426981004398699588385965569680171402179307380345244572445662387902258282686727020007181268595552866524539070379596163571000867308761621916564933662000942333548907337372860939047854560816693018280556360610377685568163892698339683601377300150705072432637922267929287848801348603637721053624732018249402080130267075159162351813644179876560042317190226684867238070288439494887096262685867069517883262461835261421534023860825873734212492378162437145384097868816979593258891626051786386838601644939218839705162876638772550447288880730041506472472099771785316719907616358094546437563804948159694736226426968676956215657177264865778333803930267800766672964088310872594411202208724953059731190921042597366542293570177861428821744303311757525072537784750440101346972773261186278676706025541668819957124451502013152636252179472595017832304336731134969493751842939198674666845632482798195203663518447750082891813453984086245396242849187975906209490341857630072487388955343549862411246772770626281877442841400855536283053167306943352119990941268271427061832040885111575236068945376998074125588526179395784250582759769744336822373814593402066299912105773280846957548095536074360421949180382055147005560005534834885487774574623817042306984423559407149111652574684601316605921886753274442744084480124430987743444721414955092893695126458912296552148307398458251859948020968540551266721342375457145883381077212144198955010333645759221200237051571799400948145739817439790750171404419075608626786549041268480874102592188110525953044821315671397692713237423068455321128426166481625679795832050395073797784459746761663096994611890962522715188205452709755179689089534553028573020520957181136641715025066300211764368976034350751668000536240273088853577740379742216597477908189555860666153811329271889954329808097144254753481458046698467746998562839733403122167480342011098380259500019433985908214113224726734168808086557895996553871633432150210114055756271917760428473967288310646169159753666124509710130790414233786769230712257562618822000880962227687327907998329665626471720269859747352968066581949590333168566476854106066147055810017832835670439619176410457568246409184201783832787415590207599321833015961484499382778066105383846231058553538877604190399360284839213105353202521137747458932448761403591589741563528428406539378291624835351642041503340089557809418401632755126636933872028328006419573815725110071384774107776261170073687578985427953328223455352514785313808655860343964462382844102,
      10676456348036985775558201581282704149555100173738255326026969186360459915505608087342154744574384664726634844749865156135750605091040735155777340945541873984625338593291491125810681803177540944506991702768877068679622144326405919088765076906001522266274178914119168895051135808315293343370842702231182617544027696443070942530071049469109785860225231962206171029893441552621929316386040292918089884044225519441826426969727141270612621875847895961745824003721254391573940552333580622106344547917888990705123935877477100892869240165034330750505856073557528993178858706816371079403460673707733177137610677475258320174211602583682504696579215812509887807985791679781657515306975403408291922507795774967409393010033057669043581918736970947113436665652857032000642526301401718435629366181232697503530119311570968570268109681696626815499371062869645952911400017487615743553096622409628292961735768273160005320038206922748330267165444442219534736139640164257232965121731157627272513614368859486048349330225930863818198170415527356411956388994649541247619696171566594205138348478589680623069751766929207732075162092963481251651959810381675671683343176435996372706402735550591228841433802576717684541757925887330595686933689132491365412685887577270715966116564473540070417225030673719993411926511343125047194939075902769278422926353389776640549090436620858098033523175883848139367745870067740811782056892004764471238657323049235169668938780483510606462632165440773913542096767015392693758738144442995771129158402951456338021774586583756148701022532356554121015728638348912087450283573944158025559071407915972021807338687334338351311018783541434206703094722291714050477097698149908814978306872787997752997129430118707866907255242538560283410275305683142008149961105129261047540176407747397952418130568218509561037057852784960725266066810026066636321858456127893693583343705738357302417189143347492998195563281567320922168743482028984854662844629142976398142254011825466593517108862238283715440557257131966344971474517746203395075096849278351923272228653265868212360454250361111023548321259400744867321387781465033590116428882514571978507037667543168189638897180240863855619047149956558874108655145587712437727993408343085375120725727873451040640146903872439084297939746752005961472218271618226111781816706011839729099470220408244174238420979253854887463413996759377095463887812651198482469580536307736914260463755673626151206832606510188779820059910823680861235495742472438875169481947736365501160610164191241770708218298447869485553904822417221477922054161629446184943215372545665766266103446515826527524500495691555640500334369551381222322205281450123526121747442560808388826655176470567742386446581135200952845089656543553989349130283533368639403188362018764307034063669469605300660745668041678653302743506020537316302051906643826589991281409436466312628296069158953995136261571796227382539484842705388201795504040974171458306753242698588080073083812261804819221893021443153868988699971062736719947397101222794754189212238935632556610301900799877959801759929202508353096810664836528481008716140904757479190636353339489256629720931800228528920219289915180957605350959389079003456178589501636472489223032830501143015382645709604274186396443045031916320228031927705013454184737601870165501898690762950445343641827493763829352287006271424181419695748517276997895201462532238270487144242174123656203259585724830418723177061975684363013156996815282018928180359927942873407,
      57865579405777194383695793791000015875494278651032875039164973594527234724776055847942355861451227346508155856911504975333575918975611296846211895030028002983704314870594827015700995604796471817916278353693581480498049232697339631665622488436651367964099098200580813234597355243674303209162439979456956655624670375382037905338292886607172460561886543197663727269931042213358860868674669898067946869640366166043122465541562446025657639963669324448048436854158188554347505558416512925221625077391047897330901984059851027805407008835048442322166531768756358226564053146732339898766146564791043163363435283275050521505311180926590791466277081749968099246289710215665085302263286299008743894573128867070409619745325373692538364720485009259441565394864469251288968047051623559378079215487705401435114732464901240530976394060111157757510664177707867734306594421257731480642417793713272619588619234993358872316054308429650259439089485906131361368920474579174925305576239529264793587011077337497498922214517963998041954288122573570043261467123869886307018524110196614327736633842751851585350519280207731729124669179175494946230735646255357695516173142980466723019251335389360230269178361313979224704346331458449105110500170609488978378995768897416947208417844952364056992171764732430557925967528781674753403489421321159738097601515462652935707639045509075593057356378957781172014008322196302656362944585003798106841739213450935764084613467320957253441903354332939054065252239300371815847975925858433392300022378921886507394678577530753722144114244151071328563397140222440651909554215449103468303923634089104355237625307301530687583273041435331678061593954922642732062528375092812994639838801601273723506540874973040362616028999634671605123711867058606982988497639644805644418202020363825054265722444750709866559533218720087106677665735338492332916769393521616449591146825539300695127636497111376077983970958309273564876181990452106048611974393074244447454973658034015764280324222480401537695460997852840561254074823464710301031857898426531314590063683603635684003741060949975085709361052768702212036132595940236500493060988124064260084571908823701696123954275596412842971535771186128901582949220880221742682835973320341518582995892359440064149994933063495597548801748545697155915062092485758346752942502666795097877623435869517453470637235176857425445517889851089157525318756718716490184221778731965075484481816123497786843741949742824762939750623110365517779590186400811840187271828730629826489959469915006049612366168743911685143015210022093627782840180655682680543251606806330085884012877224822441281660732845968725526997000080050354048776584320307257242355176651599192285633431567952702885901672854872769432383407200453059194711939077490737628894031161173244757434808667329361043680910059927957930945,
      3266378431094617969764790417866011725859008624385703752007448379909252459909365846518137463309364754583698116449238944646358540835123731481139705994903414676614512898666485490979546205207964475291693699695726184230608049659930239999353233585983904660109749903389596942268914951424386975176410404619009427576876999387490571432019849745897394552175143124475871342877159595626818807744450063367822050837062460208386344978043099716407647345178969017839175274413582854474759775893811191393999368118397209255365042973656262171999507599294070458295312774255784684396181068263533714636723791862071735320290365837353641905592276592282875673942245874402648143855091259052982541102354522952699617227838624209756040316302765147424566204667051376836441392327822747185005107457109686207736193577968905143124026586694388272334080063836379523807390218628548659974751699288180021926849327764976650093141989443551374929127939913892934923387271156581507613592156454185255608157194512788037508157267338211640761094586031531215039783257098600607166231124535294327587201023639242726530245099648397126668007466316699081885226797690762607066885024704276501211618963473456419477882606241215145461365416738116376470334908415802898100737085090584063361757199562943531019798822207189272931311035014863057297154761594281933605946307608826628488453195478957717660052253132081162589380415096350771919986245803743851528040875352172128430223962854908588057022046169902033912740861742900469407599657574679525470483063544521047528340046109004924991302148540411354972232867861721295502913413769676817568529681399718875581792725694942298275595599022737025002552635057519258583265465298141235669149357416520803029748566473815029932272248035235972397538696230179177571,
      38171192469936914993721532706527616586908190570070364842798649617013545546223540811691314180521761049437396691275187675467236439784835711709645593320860648894747538931682051598765775931398764150158642779067702306646939038291762978222488675746074800771583545206207400438335382715405044452874960517536268187976990424996752746227726326118090582869890450513091297010564692494388637722196433520346988185464179061703995581428178909291658442627189605716684478863558352605518437396730403221314497260227045965931380331093337770904599007101327149360802828908905579152495639345226949631467873896263215096629019271366022848997474321288391164667846862234461232080432664787204594832774127434953198705179146971328345590692592583443579618527291451539139648631439619645779725801158417754004792970585208063701860703867678796006567457018631573459588573801867912154495661250616476407366651502518786801337210101404531143034512563517629279748759626086950075725741438200750413821921883893208015429511666164134432588776985101567081561263803981619356421974159684021754753833091603230254838177823718316840463752460625655120965052288114502702908643983666237364270861349296604058337365147330229866069096037839578561823969343845305400151653768464582137447540222634022935630522110940912894061359108054060424348640016105031981897328371968118625502491770744450895232071759417230786819783551132122207273412645126695263799670361505820609251091550262779509878472210094803174792229168294108514146317782160579878743465624876266822951477520411393611794520,
      1307052174041703451019387073007405371867892855830871886260844951888407722816778544880323112227536436215773959220775896344539136624594527227327795611307384246777642622877910527818629672267362944874250429093991191640045542266022181495103371528364978905247208473743158969190374753810994546983322278464755622288929817514112356736356655341014919264624141851216393811654464479466000532529141627237151555688674555315068287981546494465192382669798355998162247674302455591139565379733685435967978775242135554648497391453532196177645991057263228029689442263034138320874229380381145892698817305665679722832196372657407914590133680653783623645653596812816464561679591771958431318753394910062106146546430720624061145570757186337914891744716852190031129680925438854927688808513554896810507898590018259462410984887749009460324798533592100797082950083607165442958873800077176823890338690845671918943360278263144627016699963182912742973260608410013232976163719563827408210551207185671611899777373603084723642106336236892971594691799961409751012025930008717954595700278102139381457597015161247413685910538559027965569045845776159385160404177245948530975954862823097156343979013075419028247226703309219576926443112659646401314384661350677644420573823060210676498150036081944173926537565154499338808266426051656062688736843254523491960071489575236722016358077489743897437503470503397025592194240299003741747773745548286565762069621158146807800923892229460087518784610629992461497180591571094824354432165580100645804541646132010900158699672770477475308173880788365941959556104882140440062720492739862094991816435587529007671986771120790586055102618703064708857345181202539705296889930937555199645666878364749528853362670444800752073211660920867821595296384390876541817096617858973661937222685358911769410542796,
      3746361784894913853924171245025346027644132144802866534005838388921188251800392128940226416930722175667332319253403808494440558008432589224237878905845033908539381970953844318463376705707956897573166761405071152976873882135338231581536301884170929550173247530851295582589805684692646690064360063442469150271742229138276662196228358624255962550525041113649707710651487970465707733243542648815335290284360825554650564356144000816398979163782674873850531599963930095461109366082474247628055002702075418217501766829627084757705852492138472545511333857101928320654520598769502917481876665252712845877373805238368781936014411778279819478728712063999419185632321195147016625641432478662029832444196558966563355080867249621368253884905780012171571659287246270458892274171834109805127091417311446341344360622118863649477597241044394773845238573014793425999776246215037017627908149971257353106506590495652041302225384103381117939869973273994215516518506400152449324731807921180232279830622941341868915603760545133557321456107762789394175230831740999094899176862150018702094630881617566864105142489505535186809390528812362777910781618001553583225076738316803002565700775644540728213116473480574166727466684698125744097190722399281616067289144891758847542942510102502760072797985772249013497640687177229064723431869160278312222676742797272104253073643496448297858101171031145552295747855350692698047367978779776417645334200996658062405922913841006437786003878805250756946729781049583323306779777542355628423532824103588833966336256908710690140862287028919769906159803866835895842314602225537102335398054242147189821087918516145881074373877907775840821917719175141131284025505275568935792199230352814773203473966484974039722586233513101698088530623756778707798569844363862906622177283509152237656768231207470857476453163009397402254746235983724165003150913154041546586194465853032529331182054960676819455393739192336053083726854416109835510738909350118289776736095273798017043101071699362321471435405777515481265563795821990164259892356013342284043772161630722817235768550181964357117076975236671803183887056449720088190431105332445133507714543577526692548697664151675441016179452873657696771007437548790107316902626282325858517719246942522629835293764178589713305154525248110910820505969916024315580820313254985499931045655431878929197613542434996772131243360376428910795439664057995874878932642182823972634380062261921857856896238882769533259118228586696263240015134040865539102137369897996992538487795609381498674391712786574222039743067875848911001567981902014282874809335405517346760823716574486972340475320013198132727166818076793999253667086008513204036755624921243056527698219604398115759797906402937544671957927094688808323931180941933919776787652342437508469264627149012652585109027509944481006365966713147188461509184177463118432859515945013321630318245530118248421435200667047788676645269544652111649736035649857183039963795931213043798451531892558057569212248989537899909475,
      10765365374913458192206932250808300002294616252247262855546932976342540883804369549595952685403448992844142199662556103870796371204361761305377434152122362443823001385805393090913774423952155239572100070558460427679273279341144242086338108222419189892343776636816786520596664306725343200163684916925103775480833672886011735103201262013471612020076113481148904059674279577390898864774382418042434825738517079644171256329968140040072362775534413827714066515574245764160232264431273117423019330327077046085613808523533136504279698968482441900382677906036105084867677407866017828477712768478003651250932004514586996544795116016469385888284720455687032711539270736756191952942704923347370931876633536765467313768759237628637673035838050199896268110451667915757877851532853583431803928816556051364167976056544351961365173988976968073779578060582352625969560944109711720776488443966191307670235307535403872147265170294583760300227418010069732659077375805014876828818468779707515791382802645852030884737253079138317091241531150561760790224874021601723949594314869454203998131611962528804823798695718512342288391035478933343067808040324656373394926782462488776392447532356477472895307876814244052646509297281520839987906530815770941952787484224800780234336482385016770295351266066004567868425858166925874944235446950750653196624887763249195182954768237444512652218503011673522785453558515535100102481582418061583205798798524743849431738328313400335728674497318391991448377944805028399153454772501106342729626732439835126232298384561050603660874463138871842816615982917102835729609844578160149804448660939971744866840022240115383558599984864452634376283609325552783421464938421842912689718857798050457982808377232449581168054972784597540219638191915799049249897802137184730435132721523762233968281186588475747229552077110808170354790052836423397304980355315057457619918061078094028525685586939209219456899688767562255882351082876449085807392865668177144866037584985497507301865459032529338750322871968275870378926347123278843131989972696515676620099954983281129298418256382866963507442943964819600361743025747312634474438405791749623978804173426148749054941727215687732708042985377684468546205779806377117102539125945377095688099488161658602354981895710507420583607294260649742130840036156745186547377562666478254147684309063781175122679364817998115083748889970944947911217840644181143718355718670767610618499706399182717547579016445729943179130365620469382371207894915722722015269533637507987482013625406038213997858225157923900008604191366764541543148678895301812316985309095802643292337501260803243923558230610816075267688793581567100010431745807532930436691881200207828979623468579289941606765749358161706072300761703677443449410857132341730247539293798866204496835556641184725095379182573364276350840380099295305724259553767940907146827205742155596931804765297405613602380508317499569143026047610373373610198123164746846276027132974576622421425280284860924221067306526657169394102947880117719092658324395107868799084005039692614650912068801297166168048308879061908453761050731238759773633843198162034330082965872131819269956668381000570387556749647426071015362343179314152157206099375455396266497678718787208319457732067156572497997099261327671755131406898567169541997421816803275668017277877966032800479789686825137462011449310375891261146078436008054112578829426366686641230810369957113415531098363457725771344156801086050627455337734733107878698791281422647244068317461907026654809204637997611729881739985057532759097246110870989387103466207154121477800873687450866721021884456441057300316754672406570130689777796609910311503244044164348853268432478528794067644422766735523820243347806440208267244870085094115106662568422236189744764259559343822353203629504458778626000300320072164285249312383375497368523525951892111698860470614291529914727876621817192722159620825250197073635632137180505602317322881444876792838253855127056801880204231856657895222837569233201039620947786417650532341409892963949556304076967341898143399268728552622128178160220150151425128849157052985072880514244650680345708165507862617616086865797020568869297886954276122684063415911876242436765985515698665250628060419341507116427608324021643731118648337288444091182936074606759617591812231301914109017877534295600965980108218077665451639688766924211182572378592026827049724108481768105806692026738725799822054566550885733933214232101728972998476945572846809606329129032152230984489483789053977469209243011322535564044234251134275431826935339205620643532666044137640698934989084361329610070388763877932736635938883544532941827055721674529509363929637458664246763522288723050795775622838811242112557722707294431609411171120509718612307068648350488438737206869231273956059102496865187737264424751241761752659603898104199245010280026063818065224658925012505009747970276798600538828075725211306134,
      1726462338117430535313943493506326674114159561926411963622780603805982048313826444914975694617813107708281578500151807844129386385708462651732144513681323724054529365919164404216938629742500741723055813617246314951978989510164258158552149792198713181668313586864480253437562538941414928926246347226282906690752851657609837166769522430170920945637831734595953389367608904532709117828562009525291479044246500581509069210883215545477606948167895039509907640044705254242298531364172879771481498339934434704248551619167328413917109329290128828332519363998224653416534722402857777908328141690832402911251464113988374626192071194333780112043822403549129905116078570387314365611241182297364820837136625156874475582778587693302591130782454692349743223679659179892397068555873643303261378844176036696183122931759559209825361839175432210524064478977545394338723388248312506830977876829588479232885635357878783769597389252259854612019376126451335275867134346815301851202234715891991335131753021249512622149059077947145614381750825337067233032917000045533632344478451563101308110362632590574170008364951814650881462393234764205570941613269940773364132570142533331841168766985829311908519602042375421769787809175830022058030199164468009291896931522949337141443821141009327334668331114395638100793315143321141074564203095139726751974830668937534517729307088028724500252381674483521830342022276102430728441573638398290846978296871483365070335871328912446211750174604781147536101395838720554326670087510679054774086485919007151558140373331204645886584300660240893999605246030667938907123727506402464468980685985914532018649908534473144308381064008451805345226124911266978837724656493028216423052545646226959751099461394798216402920947350261624948524753911806340179954815585953883706038323527548452769398280502582945148282297607342355383997436210079280139398434668139957624324201649192754338364218535674831825515519142614541457502075124583887291697980612967073262965941174902388785009626771750343908213009856667394997828761400765320373232282693463798153464759617619695383597905409397386555987278674928309592711805371226500297202768755913987754031764449059267732462148737653709259051587193548295170962013599202751155478662703452855759594818614363216184566460397172371162560670231302776504421638615469287763736982665862667382040028509823607713569470741656853989883590418918055972107006277493662267309412526793419369168341847984751512031387089564941568863403279800586901307407297310971702674662623276196404187861731754525789694848279272580351324786992694083154782763577850833995647711532178843725424084474198378379065259322338364840935638658682083459400393408922842458949215698895296187897109332456706154527007351579036255470237259915062726699447056724041077331933728392882972276727310073546402312363290473965179950211555793745978591857122928804555647192033855281090269422915268070886892325061595663316408002431922275790485324583252905222610833925795922579365394926628453258522825258942660366686808101165261627275236438720153162240132006239267974558361550138155171323342696544212041371641253407589046297909111576277051392804648259352308002669463905499460551636265157645609541997912687334019656831599846045707229052822290052357315597179860270925380777079608174105038451168413755782947115766862695800527036170015332109902061572988104008386309765253465532940278644933033131617766833284100597202774539627700984387554681045455750901406851331939234031407956103122982650459168354600747697236238422051466279814459191874735509890515743775372066242721678574034259189260342526576826812990664959855112329465607712616835848550870744455070219572909181728186239174967248546452196188982056335458979020235040974674004055361545528236652570022607354073657773705720807132152089806059490432453129327676891197399322027573589845009697067832577247289302652066227344313965888873028461079693222839618598774012013847186848300050146360924275581892439046761588254067392168068217,
      316492393447619304429601917786383186529539144017588091419362032931801495363253644492841058087724803782812859606032255476526647111992482558852864812076370184047280532061723203633184592032294311100810481528924905718423182901528435243522768307032027974289525354538199878760031697041128008966662855415648263389155414757148799541358010703907621423265630285133903182528619834982412995190259923751142275652659427422756502698305205602335894667595247557070498246136790621132137893930672751391561420343135093205048291060784013877209371461479681557454217818628603091362379114366369437797135363894213076759417786592522535684901729214887949644865899211806677728679429109073271432352606414108376174519177860154956043943601800618444014844687320927885876846182268473893046271807185575927976664828035858131146369945531338238486417031303792536271509282502986825719939433401696707694043406260441074945927342363343498465421485053296881015529054618667453371009689340298251100064041053977038297918932565669384450093245438550573977109573769807488186939809688295732944502896440676396042726632178682004444705762471757366825936972262388931467725692558773176929815207327977111951160226940115006532310489170324344987695314525802597854986703618896340259413619418014724586448716519043281013898289984789769686614058323189420317792739672583249248394907470503543614981826084040383981217857627278167805913063959040433401423421359561584351314651741106314073265994294875063016337273300869618345610727911240146471938381488509407367710481167853839504945497707513924425184869681852125797857104051523273337631284828541754671333899851639223188866137958105293505141031460828489306267963188374276663145088319144844174953006121545774072571678933124281744664339421307545136274924323012889625182672389140126810898858602285775053459999123549846860725811893295732403658243662974234191752119732672816655064107018286562874455176547077460569771861673006750641235962501706938848705478383741373688867270513511946695065466715299140264950732105970368320548952069258271393967546233367002953792654930253787464015315679474439344952192792437088414658001672538040275934128940535599578620024770287434048421678899563011971398318707375655635321260318474887483766797549407655574735610913105835836203704049001300561398257768593822914528476223488068387008678869201548152865633752203876107997029425902804010269422701104450691834085867901795487555572499172643322400271490978784667394245582939863453933158736710435045029054650660456073572214792494917548172978436726233244115907701974939420228521011113793855209345130897754953780671133681285451662337190971376920495179388677876040577318354775571057015793530058324447973743670239953555292794005158465905756309707023845007334569290757289395694768979491061314564367000413620633859923272707161630899556816368555222625034344677761643210011457419403309611688610770861901562628155607376068388579293774237848519411391200169623291146475071426268182898619333354137045930548493239764090598994156979204991533385413241515286040527392349652255743773628056772442648892494913869354662819082668188819093415850500232251998524932023184501382497051368220513295381337730777441530491500392616483307799195788460868653829125778823229487229207845295650707384170938891974049563063780665920116987731276040594014858145829264604642699806630083157203613374089189920060623168513633295032709442291521386955583590135320713464517944959341680185670641907503614802642769046200557544860162902983178479726058506877085360659894213910419134686481719942536027550265492213687090399364222728840151226] }

theorem back_cen0000001011101_0_0 : WinSet.allRangeT (back_cen0000001011101.backOK 0) (1024 * 0) 326 = true := by
  decide +kernel

theorem back_cen0000001011101_0 : Rule30EtherThree.allBelowT (back_cen0000001011101.backOK 0) (back_cen0000001011101.cnt 0) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 326) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen0000001011101_0_0 i (by have h : i < 326 := hi; omega)

theorem back_cen0000001011101_1_0 : WinSet.allRangeT (back_cen0000001011101.backOK 1) (1024 * 0) 336 = true := by
  decide +kernel

theorem back_cen0000001011101_1 : Rule30EtherThree.allBelowT (back_cen0000001011101.backOK 1) (back_cen0000001011101.cnt 1) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 336) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen0000001011101_1_0 i (by have h : i < 336 := hi; omega)

theorem back_cen0000001011101_2_0 : WinSet.allRangeT (back_cen0000001011101.backOK 2) (1024 * 0) 551 = true := by
  decide +kernel

theorem back_cen0000001011101_2 : Rule30EtherThree.allBelowT (back_cen0000001011101.backOK 2) (back_cen0000001011101.cnt 2) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 551) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen0000001011101_2_0 i (by have h : i < 551 := hi; omega)

theorem back_cen0000001011101_3_0 : WinSet.allRangeT (back_cen0000001011101.backOK 3) (1024 * 0) 501 = true := by
  decide +kernel

theorem back_cen0000001011101_3 : Rule30EtherThree.allBelowT (back_cen0000001011101.backOK 3) (back_cen0000001011101.cnt 3) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 501) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen0000001011101_3_0 i (by have h : i < 501 := hi; omega)

theorem back_cen0000001011101_4_0 : WinSet.allRangeT (back_cen0000001011101.backOK 4) (1024 * 0) 522 = true := by
  decide +kernel

theorem back_cen0000001011101_4 : Rule30EtherThree.allBelowT (back_cen0000001011101.backOK 4) (back_cen0000001011101.cnt 4) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 522) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen0000001011101_4_0 i (by have h : i < 522 := hi; omega)

theorem back_cen0000001011101_5_0 : WinSet.allRangeT (back_cen0000001011101.backOK 5) (1024 * 0) 422 = true := by
  decide +kernel

theorem back_cen0000001011101_5 : Rule30EtherThree.allBelowT (back_cen0000001011101.backOK 5) (back_cen0000001011101.cnt 5) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 422) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen0000001011101_5_0 i (by have h : i < 422 := hi; omega)

theorem back_cen0000001011101_6_0 : WinSet.allRangeT (back_cen0000001011101.backOK 6) (1024 * 0) 261 = true := by
  decide +kernel

theorem back_cen0000001011101_6 : Rule30EtherThree.allBelowT (back_cen0000001011101.backOK 6) (back_cen0000001011101.cnt 6) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 261) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen0000001011101_6_0 i (by have h : i < 261 := hi; omega)

theorem back_cen0000001011101_7_0 : WinSet.allRangeT (back_cen0000001011101.backOK 7) (1024 * 0) 229 = true := by
  decide +kernel

theorem back_cen0000001011101_7 : Rule30EtherThree.allBelowT (back_cen0000001011101.backOK 7) (back_cen0000001011101.cnt 7) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 229) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen0000001011101_7_0 i (by have h : i < 229 := hi; omega)

theorem back_cen0000001011101_8_0 : WinSet.allRangeT (back_cen0000001011101.backOK 8) (1024 * 0) 270 = true := by
  decide +kernel

theorem back_cen0000001011101_8 : Rule30EtherThree.allBelowT (back_cen0000001011101.backOK 8) (back_cen0000001011101.cnt 8) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 270) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen0000001011101_8_0 i (by have h : i < 270 := hi; omega)

theorem back_cen0000001011101_9_0 : WinSet.allRangeT (back_cen0000001011101.backOK 9) (1024 * 0) 449 = true := by
  decide +kernel

theorem back_cen0000001011101_9 : Rule30EtherThree.allBelowT (back_cen0000001011101.backOK 9) (back_cen0000001011101.cnt 9) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 449) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen0000001011101_9_0 i (by have h : i < 449 := hi; omega)

theorem back_cen0000001011101_10_0 : WinSet.allRangeT (back_cen0000001011101.backOK 10) (1024 * 0) 734 = true := by
  decide +kernel

theorem back_cen0000001011101_10 : Rule30EtherThree.allBelowT (back_cen0000001011101.backOK 10) (back_cen0000001011101.cnt 10) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 734) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen0000001011101_10_0 i (by have h : i < 734 := hi; omega)

theorem back_cen0000001011101_11_0 : WinSet.allRangeT (back_cen0000001011101.backOK 11) (1024 * 0) 593 = true := by
  decide +kernel

theorem back_cen0000001011101_11 : Rule30EtherThree.allBelowT (back_cen0000001011101.backOK 11) (back_cen0000001011101.cnt 11) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 593) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen0000001011101_11_0 i (by have h : i < 593 := hi; omega)

theorem back_cen0000001011101_12_0 : WinSet.allRangeT (back_cen0000001011101.backOK 12) (1024 * 0) 534 = true := by
  decide +kernel

theorem back_cen0000001011101_12 : Rule30EtherThree.allBelowT (back_cen0000001011101.backOK 12) (back_cen0000001011101.cnt 12) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 534) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_cen0000001011101_12_0 i (by have h : i < 534 := hi; omega)

theorem back_cen0000001011101_check : back_cen0000001011101.check = true :=
  WinSet.check_of_labels _ (by decide) (by decide) fun l hl =>
    match l, hl with
    | 0, _ => back_cen0000001011101_0
    | 1, _ => back_cen0000001011101_1
    | 2, _ => back_cen0000001011101_2
    | 3, _ => back_cen0000001011101_3
    | 4, _ => back_cen0000001011101_4
    | 5, _ => back_cen0000001011101_5
    | 6, _ => back_cen0000001011101_6
    | 7, _ => back_cen0000001011101_7
    | 8, _ => back_cen0000001011101_8
    | 9, _ => back_cen0000001011101_9
    | 10, _ => back_cen0000001011101_10
    | 11, _ => back_cen0000001011101_11
    | 12, _ => back_cen0000001011101_12
    | _ + 13, h => absurd h (by show ¬ _ < 13; omega)

theorem back_cen0000001011101_holds : back_cen0000001011101.holds cen0000001011101 = true := by decide +kernel

/-- **Some finitely supported right half driven by `0000001011101` never enters `cen0000001011101`.** -/
theorem cen0000001011101_not_absorption_back : ¬ cen0000001011101.Absorption :=
  not_absorption_back _ back_cen0000001011101 rfl (by decide) back_cen0000001011101_check back_cen0000001011101_holds 0 0 (by decide +kernel)

/-- The windows of 22 cells from which the trap `el1_23` can be reached, by label: 7,707 of the 46,137,344 nodes of the game. -/
def back_el1_23 : WinSet :=
  { b := [false, false, false, false, true, false, true, true, false, false, true], K := 22,
    sizes := [723, 586, 450, 756, 390, 362, 932, 779, 935, 1035, 759],
    rows := [1523898711764249187409231027544051701319817247023642608367681854283234290354176604037974932271014592092478445531680112373184274972895119658158291512989508712574311863328252176284278559354424502545492608458828914911224120615955326965717143173051684705121116757847051599959885092253098602123662709889314625682057527230573416043630541501301720942901003029952101400428201736534302094376950111620011167118344649451817150302872066901017923964291713731900762473974200196161503988599571675153132937028937960741724004025118535111858751567333886276449810032190409301932820980436242955013784311519994735010506813080737007307576480927629401809876376099231661840029520250983650763921551445482487756779154044531865184124547707808700316345706830424579261005517703686067119522743919552050434370934505820912915848268168416620665830076761473658569072909734216960260753292423638992781294995426317364147100768538863267872601971009165726045033785127958320681383904549426113653498022608636790077391215253115107297176447229299308702066660710160945607916469577397683659721667456622778374882771087542530068799875055385489077813288745618784143384476847481123621281015397459954831935813956741769650105803402759214133642594149605517876626199791482655806781077682076143212635355571918041806731666054599975944667178418987214438703882256265257418332823729342505767677560758991072196321343989834135292402790074502216712973854323436799490186404316372567613433694124814040906400001693195645222248417520148803698147513565026213915727782870822293408212858524485652174063393156994725616828217618044920880574752999439446303124462929037755706971726125935273961218723535948515305500133286968316490976077442452122597314744003875337919587097556161728396791630219178488877772760820786428809718859423226583219115439507877866442228973678627979211597635097568157644617060409536313240999888362800326384601477682222024054448675655972339264504243509687169393513707512467966376370483274460594438895080827555967319748445045602534183997876319429086045048805985457988340009060900407879866077726120783989923559196202461386694011866849267300943105286955183636045062241674121707610105544059600531018486707791731218360215819090028200143224892787039208554350348134770143742157373439207506248019768673359540379303460121169795946678796270814052597676377981164466592777803829298883863856341874449389222334108960453431294520128177672895571535721278226039965949479448794599662071957918243422627915312942710781030210659061956608250313312276753558268162608170938943300809563228718487025142684527325562096637365160771315382409798848059459089390687777267353589435785978054207202953738414661278577916789486764229633714227037019325172116863571120018770366416157775202036210044941304227201185362240970308153973230363315145578550481720190462690679457459455217433158834473668525190467678592548430345496601956354578225275878158471144069812395139162601719958644792308966062220686256051806908095680183672158723905085373888588388846580523044083077937626136767508246483485409548229293215912380121387326686848410491380479002038245230010080206276110007416621834693176192454258749416506620541997897282907584585910637537688325970685246102907964900015569177674766652049316250818358220813341144852078573927579182360568417658338747675704736419462233167281600144423035122685851332563012532463906910201917716166088474570852965331026565565642167432360788178571000490798650902198688110847744698574324512184234914057417931780788531992783132667299163403365338442297974699689059849020757639979900077754741390363445256909127429669006344117603684994408218757979868173164401710440118847612619523126035056830509319694834437588295505775770200416474981285536360468568888225409945196574165087330575456601745759239697117921928760154455716415772140968725529031548206385721990076030840232406363575451377072680379080814841949810931005690797729674653317508977672620965174708849918662343572164086895537819200539336160580971118435048576277461134413875036894715240348477986804474751957996968412941703593523568263960375871362672508361878407829290870666479326741070159191580184141229859118386961485498376049254484834328049328879211583330117062009300581962619784281176666919406494618494803353472323776344320621578069690827087695868263707857340255431059208704745040450947333004239358241073878432265090792872822084272750512221524314808882846349654878855924785624337512848122688970383856502528576799745612078541745310785379519055083110291903664694462646963640418421467572121169243839411640047824153519056590743785408655639808783723662606085096709134952846701102800998488912863037769338421880733427191938455282691477290491777807720147967518975910955410639956559181505492911904814027056110015884927831064984778904499815299445961944460002299947314702516676770899042625377254753986610686570927490559116839,
      75562390255257826846279927292456330920688834484758203976695429216330131301999067477784918081215374080304376558524134103649706185093560122218601374653357643748294504806560722909083994878832597220582558680865577175812447176097098575208011858475030211371302470179312435764382449167894522219020529543358007449624763406312191191984800336337452007077055622921329703648693928971107637667925119911972028594507574948115497506516895654503474307768039462966203437620568053736176368871092901377423074453061879561452253957652407285125460463101625708509422335318645819989128248776900327679760777083378298150792486905349442377528748317482617441147694393069956841551330082789001728684369327738166713165348749269130856728333374370257431987553342762277245873106798462492528939705713422452805966202165977794351663286209147135334866467384350983672347622717238291838509974297740079209681749807316058147890699765359656904648258258451454298003890762100132552414696447557851493571387389500950035449504445578842532824873703298556733256342460914683420567246196422091026563990393530600048869059983406452617348808705221800307507092696430171402415810198336285627446285485679896425188802509153888757686117600394277485077902108504805669760726612301756927871470078987655687642441257780483844647774765414251844952283185657084270362307516155653276747195321463832446105439694730720135695070925983593425068848124488958578480189677484555143768922751909212243422827181254863907054899949741224374990587206145921883261743754492603600507786851544341146829351890274811910499747052964923250392047960592843188248539021588990559996296816336360782070696734873680076441729532698940306338466804803417967882676755008842476300821358161534005597772625025822688506170506063015065005133299966576247843968723211315203632657283661879846986216839383058063146360804194016442915467305319488429100294440849295467581392025868847658641302977552750443952313657451641337466275218364353655458760761657828941810315728676753768374153701951299909697352484642684659877937700085277560533197069870002657169223039173844091773634778261772901197288829737529522925545504751129898551656145478839245415124944551069951958531512751295483929852929818896703560236866683236216623369274900162964678707592318930773148988721121118086002987279089689038698829608650016796380005846772200200596811651280156868572157415631941876929897597685470969811144585025331218873433157055228038285015968311638848166980971833702949168377928860212086438369810162631351348210247879021478390235186271114054347779564337377266515799045464514559328499458428748001164910029186668870503562029696252996672874030673482232592258485454592660509241443995696465710828201688708505121447968291406906744378941262720836651634943867428194471926959884918471945725826931767621579413508904198541631810063639776611203738032466560974947381435936055306609082276257748781440907438848567085066565100982067720615449124261934907178988003031516801303040908848789289683418713521877087470925329882480068166272295152801462281487588183853141393251152876734773526284284542282417787919772770151194196564809261754089175941429905088879707102355695762930208816372534854921379657953452252598456351082294044649457211468866025929699100335084167616917997300227993865088074969634368377006861440930249735680627020481632840726525117058535915032394141441727053198595390129268034106182106228054712218577373147904979109306729544510627989474066469562019794456303361998018104087681829029910180018053927606425609049869099807795040618390197196108031558826195804501370622210144273448591573186459805746121149870270850781207629496664122035909464069418343041561451350988871884779255856295529877698829542698765948776959447898589162208425601460636617411831029158175447801970144008895776352270959316109138308216862654986973261479731156954615491816475687517276211676949629402028552335283672771930342973952758399321737045667366926108546832533912,
      15726565789905665635378532608466382584818482361192346028220120065451610605175982139305731078561906879459658437252708970149337640546774891427597644328698665865170528593158905848550393220608623283367658001504328638287338886628509590090571682921933647957017870824719651029063633190388982184134955449559327714073610183478380762983800480493955858044071659408479360363463413701348015057681703520838125902113481812700066404765126853644795608658928353816192123074777060846465036007756936788768312536956457300059369417435017763899317731647968723262721314370796436343338987444892507745132757777064140782816248556943433108511105046749860839616367769044999200911653856803545815329241697427678001202432817349650846746437575245060906951176208029523074155492346647061869875341281256893833542723069655256311547735450831263481453763594992255985619624975105042100511211971484273440295837057597228723802331950998136670486545079484940149711809223558372423903620751545736879833265786815430547212187993385007043359546553070045230419094349413931014199784083228817562480000250713871444985460983269379240103366879518983440792289081255296278371691082548709621924339475464160686796818114421514461444279622261492247627641036327694664590230740336306036880584728878361985114033469537658720899535272214193077366514934941779177257748918818204260836887968802971106662712958735475507506214545863543731036456143781330434472122487894325937323808883017817651930146646290998639232342474686143025283314810731908692131966878326889796186124002623645386790112846221783996821512275215065130515334154283766035633773136871772561118128044869756625177570510682535592696131632987739900056232952029249935457394747142106684631241181784033741091476464251505507056599163487219331540363992442579870199616281219939346547856841199489306348073654408271727716282266040418509562206938801425584007991107371598540757658864601209361734840027918340953655260923086880563129679687534292139067191523386705640104487529710885276794162383326519619298559697989885344754218642434149980485290721571116850896058804707261704713104583083359154454911077065970390731261092785950205568521093204471730996115871488128703641209456590637824335069876752963537097264689226416821955761445810294968622757450663045914042816514303456924255676756683583998389443269230409110974009498573274998985837047712249460415397638208411939021512581028306996612268408511044427870734462060178484734011724031802854476885077977257799554425907114887356883646452373443962941688145198453373847092412554748825425173917621446969061590985856799248444874678417268305485390870860546599896698769759688393698222336882852475589683690225126389869990948128142099152634414205663462948112414819425120334785355595520855851975658646107928608493660899864162184411858593175703365091446889210635877433886755410312480061339885111848263719010057184371934375451770454117136251209550179378888979213695570363620484139112000582408793724453060814513407920826642729491970615777968270602776615924956665053454539023,
      537488569691273265083197430386407784879796204999986836212396390518443292383877484402463842868403060267869749927808755555916844765537624139326688129167631592401402898787014269832481997984747625398154728518847347491863771688945885074301331107989795748410488093118687439455837024715596658759633767175061347324030914507097257383866440138388963203090592888587277562452350819900559198762541183213656820773867784644222642962121518772379678033383328176752633631751057435088352065545194363702070341674237060514266879709335967233852140221559110447944400554537434301067203409445781533883955418400443085869324712904468916646496751253022673720392444513251597798550950704675472845006761985191037146109742162140312961594265910612836161641357108349345386765921874713318498460919680064946705100578715798660357531042907913853995554192870914647955067494806614198650149917752212020805771304147510454381924797085098110430444283406070741550641094401662902107358387554645408257940628430217525355054045293274339835298007325732057715208457339625105527365073499589106088814498714125824851661173768737005422728390416541346711661812243600235499174295689877466395256191009617860698676912515430306553116136037018879070691717417458469336296972600394806584173792611219176561573642731411972626091827941281924876151411408074477870743128632885141516016584724506642746220725684547574064594013393352110066259217103978740583547222632238756903717187769181104275058513509221982140637096298168023051323837064446843827508448717525457151758549629759353002792776667532365109903469660385161743021663717494534062696397414559526638319655310936897741184209878322325511274534966701896676125069806986736109123858557398659658479335815239884105973032302584858113660430056239585744935917795172715630861224845732661384507370926254380478035059084011700098770858767803594099093027492709477659575217710532043183155837551299271214990971736846138260309140460313839968534047550008677876622992644154534840963336567858526498005303949109672645497189781049605369157718639228576142823417689726081815963127016457945292220222559884294092894938930175267101660994369631631250453140806341426079131359550336336881999766181601468692388857533939741903237501205211783184253690575133024213665449877744974982318692365060428164991216775675296855063573917735906870747571790874679006518210793410808312696398363549368161442167601769199045952507474281444696041173738722895078001910027977055915284076883757907984835682265937920866975863749685416790428965538675990682526448334781315010914407198377472753260750631974736569612913631698109658206319483993192890914384469452131772593886386531267226751121388953065271775794401522759687530526654003771931087538938670837975915624393695089346304736635548533970281862112448813672412801795160365505583735348754198636455127163741981706040522091862062976721483703816335074725393490431244363219295200309551438637102484537097033750757826782740198451388909902676353646633708579782853437405873602723339304747158796136140167174527869766239358593120606922029477293177573191251595786969936339733031882038674984645070696659226020981709388158579794454011073990441360093115540756124266012529089024460194977788218653696686048919444109327515667596803675978995397813308576652706924754788816830990141566119374735569436028109426860233493574955964065628579825971256528964389240932810059050119437364765914953177548488479432357117212873770402187061900443261174025932343844623545204010319108447396193198107300915256661555193614023938432490986014435423130670904707123820315894300366552285891846356411644584675735042851343364456980480341375030675670417875864295057547822184417656691898716329260962707558810204745632171171544914705438343517056475404507514209417486579430675013762067349196025473544969224144655554654178536884268002145903879859785246846061721435172208018583144630789055299340804418851994006779519576232886887324581072458328235081746544541953531846462399569083504299726342574784573120817362173132080260387738261456384678006608685897263681920961873711410657427607528132685343411448450847570548416979438852014393475370841449538407917814477569299104447383488936888237958866775505829521291262012672995965759503002919562916724607655376155428047341451153804329175478308053436315130298490266287587419311258490737139103378641588145279156535064544877072797112671467203099809897310042643408823490540043332794980797704926426964351654593745378558635750056889419372805627917511639872365584298035044263632593765571929637508588869707981565564684113919132902469330559616354418367775000326769923571998464209956600667207907900348948533160635652984357390987787176353218693870411194858950570324449402555811168314817365552613771976181484668079185027485047055785961091406344986125977047660160043953484832056132697044086407123860581547523312853493466769978572029235390665236178862983789162999340381037260321108994034799612298173367716213214123231282739907161820286391114829052513249666997636372601622146582549035651766684433361521389109507189451948832039535269219757075456853620563057,
      683890877131159735531482410483035895009552023470565407756861494318016777779766644451486651741873992440311643777245627000472303875300046911907298271870576446777790991488548176635196981670300270027585010363220222729910974593046937551719628704806535770727272490310864676625012637345618831711090275382435512496714269167881796612665389719739200307381693695557960479199492136064493143086775811116741629200126502645415966821524822531348168602760673565416028249790113367006758564526295846486580820409032286108088266502719490295074838142698275339450708252552587800814216608836991574478857712735793965562586953950662669669716261927687616819949732194174038922460089291106718455302487348895410343962160222291133897911478180226689559848483601489653821672781715014001573152987012940579833491410973787414718756197234152659623095972609189095159926668753915740125538602241081731012181216427735874889114445892790162294192567724755424908581495848429655404546551169529101618639073351215491351915407976159603130258487001005099347348980002791072182154674767246564377608042723516304552535707063248608257818552674134233677325232482541850698824407435026376089864435266386024023797521212866123270146951652832680931502570281991064880425405051895279094123149828359186301260551848359843587764324194960635790252158140416316793000529675643533521059145534376893316013228758845536580371278380960035343539878916420156006003569379244111662227793848992775598252021212675792465230882522767606486822947998897567011593903914094710103747117673983881482239826787404627825375293924626798471591640867557945092623882344203933434970366199365991945297013296272180410949705804449619735773105967960005873356614285719305175967513265588513159614428662676248971354391310921358725676663733760627339136948522608381917834469780332696416493665628620007162968784252783778704478804299718076022163488310419554380763705264923561210128649999394486327681206266484848808250482055130926169289473571422113725975609001190820922033770566221290695530801574239828255721931801068152853562001252251963719036897627704095087556264353861178790710420011680312087681112083910042114229353597161661739397113933237517103009713370208771656609135301773381273151356060900581617106312554897551719045656624418790992363346277074312972678709006544693303262683034302371646958030612932738954185463099773550739243940546264119521786768717347311944906227515104136667894649904642927207130697696448229379066967609450811812253045325777752887433224787096029037021958913775535026687191648474415984775494822795935418688646637819780090965752577291018364876380774242140546182162075,
      2517977693499432363415300915235699162793969101615993486648436337924353380781691611300943278913127944799416207924034637183450378156686327144781966126542118839941373682311188930620597149820689723111664203590950997911589097508468585168663811936308077935291155563592749626391939645739219776923014220212419025464792435554117643411495358135765831591500705456266926131155426334636850396683463316380346627425007182706983894401227120894699237747249066987210578255706499964793338101594877304228659869613009762829981812631583114138920811078672772881898346611865282930063421130842808554207752594801777562077086985904742456854053678028915604473033383115823863568713771869186774975956353878980922161498121261160269469235775206292140791898131942389065713110497930713774691902525244661056371478304688595585434330034588385181414043028522226357490139990451233575466786493167263137190864117424582088410377709820896219684997826447557118824753856799974873507863191422365474044736376131940117578302626814657617197755125398953692020521394286484587791315014847203005999658067268629718400538518958629362950429942820907510799234997416438537018336287664622808978736254213797056818744219544451600060431768847680984427738841526104379793875356804435966195197254111853268805238817064952808955146421895572770189460099233099322512437692066081327275342456770360940544004889912576538510578982788703266067177843176043624938795627155166676307844028293550111472512767624469263896440379296120661307757481639341485245551376862187449160802251940027554990435601214258077014042353294753457818300099627439267826571291831201975023048795911138215890696665134175368020972396236784710604420982681385606439575751121485839466732157442700520039761747569474761032722161796542057432088442360799256165010160274096815663880554119719382839487283614211457789404564328053337100365074121570855176514554291394969158709725449149448626080508359466381987556517757374936608207195805193355631535654267639351719405445359628129992048230399037341279208394173657845369812848012158793961553489956391933008549206516513628444396735802479515319113288598651167427104286886902573532999976965055748711445233195832321941047595109912169266763001406518964304398724545685653169700364037046770729520563235046880741650109008823606521474586561438393531615202140888314754835330508441430563360022282442789113388423552910236433456312489893592497563199013343640377941147186420435125272,
      20838076284516546333373894486636460486812723208768327224244323782942759435158634307082311229584553259836088587102476981365838551458509183717987584936901542206983712760400605032883929990225316097619907965767712040454253178095296546134283897045334135696202830987825572684015187993965781593640679680843034872636880827201581186714927821260656383446740453170668254086449635063830781694640111877593060102488409859529057192053323295555543524827829142114593341694415620585281385312265552226306890533619949805827471973607033161701916582089470620368008057153442082745440221249715693548888378676636731599628803291872649791591788745790192888258785191145489347331274672635500173684781565667381521645086993772898844050355271540552798825456345972619875394501330095040105329129718510342014228583895485132209554657689254897026164098768512684111825393565954930668136286902142615047017380935376411575823567369672779213010705398528684003419148424872744505121626805436837875907087929621359167552467389125439565842457017896622220036292112113709563102189046637013166673627708839898882079363882631138728173845479510918694961117788732105545805012698614093618684728540592744425743435041990700136903668058264959850411372049486131709022196486280544478525986699330280574526081568842788092920144840167564172681252271298464843131710287995214445725765414667662152346371052080276675294772828095559083246329247020040441866484023818271420476561094563723205821051931678638192948576629398308568169862354454633799481530692821633542107476038293834036873313198439220980669173760063093311541099527590509015871191118610111671450742090681772349160938864009304844756200445568860023117584338806744791062826683736598090293168576717658047997669675034960306101400386151532471623261225353435550413096516997401756647976509398206728625246359773367752808583341388668459173679916371587005644629415882028716576796501529600834427898317791628305540963979991741711764742542892413992927293274616667985596550898307559367498074552994146856181233601027228665977325074251146235861061239434900982701421628930676475680619059328296996130503226925537918359596404156598455131756242152708260305603553309051276102951262532532826496965553630709605336606623635767321124505304058038568633536596249592834509292794376170858767271957923240404316706430864571006270436483272489154285822797275894368312148401684190997525075114077687435118575589083487892852611064487365860434603317567051909484189067457526435449873302361287349113488682672363371768888589081898421606296445352619958179142592303380343815825340046744237385992552378970330536916011526614148718641473864206123375282450183336592623784391677144582555156636457048724877703739669883476829593089579900890055769148233546752232211264708996455194943224747554202929635863136601917179573533157432920593136863063374692480462804178400295296638680414631238949137209911228753485132692251070526745465360465883796926580287099091521130878736326942304547770322940497983158917631978219728506063773092031748883719119800284760932507031856577430148413137212202370993335565161454007301134142580308836112325830131971067117817050871207530810131867626292669811538517129408065993010115720773402226929482358431821766824115605035850435725887742611903939665218872895884800964177574458175805994991049145980208262771813914532012024048207011080589883000353123756029857158032860416922531911180874060794416043748082492681422253564914880897948951396492341846298639106658646534679632549970906555524827513789773867621593004069301390571743337516411412222239085894843059265125776927506282757723893152750578422747198336231181448351307448704726446618707352368613187030809859920196782684168418666621823815226165864367558664326305412713083067969531850312553206707174990360417191379420632939852706808001740286840373132720906474732086488627983118451135524442073110094631121232516419255477016098955456603598623875149209399419821708240844857415640025162109114782175251442834659863062723029983385915545948575374154219925048939372763154858399646919094109627050996092807455936790230203277357076758534888683605584184297292968508567152734388015593502290424952481435593437074227434993907357906421091921108791580601410495102058359370213477143054468854193372997556508650134318201024388501762845971721072987447069495290341071757794272040278803670227904221050990266407565896094152933969842347891956293711372247159828505391063015486651298072856099906347485521177260228696199100036737694561438222546714905482862764029075491752105725490823338225463806187302739952391477311547935525476101329124936071979523100454463316569086602644660394302514503000491188358565704645593599799824030822679541448958851572425249639128845494556055099725342198954596997841644662743502292764969443511223566781439651780005909979293262073014806292285041379728206232881390269466268621480393439482549806245229142827617383969002589622771885018934714075094101333523161692529719713082882870703439851100720090833640925934119395348383955067906730434803180607417955769741947599197345529138534410705573955463516717731173361452817731234628735167299916856653373561691104351539896096547053039493439950239135611914728424562812356980902707746100846832543287707503938022400380673060466667858571649494807381740820418716365157782636040373302971460771310048865435515397730580652684922325567185812285426139483656628724776219536555240341884260832483430967550121509678702169681585956355372089893832505477265733198435742794275711995535781930981425920725016191620483523931387665191450132346190711215034978201395413244449847134931896762281750965417153389848502494764559524386896572864843224473932375654141982030141890163895135017092070268319506623441508711583064151593405753002442558055626812091268401691985126148385550335181033749826852620935831519023299184272393391701667705571190605467025846703506890553857857460999105497765807686137220851753941505522748214974268423193156187844226632664538862116837275580954138513092244111472135239738143526582872724794575730378511404738158559503416413532026219152757911140835590712448807484978458358437556281566115718583554608373367751774519642391939864495223687205129458752905723794087960138425249141160364623927582699915463512133530369159657231538201088439092468,
      112735506185815638971356776685850468995879402117137736791556994099333458957052795088995826750564500264338235940439956542820339477525588295047038210907096323721701167274442046331884069468482182861297010867404677762094588240619952283717037935313409102354927843081323464689842113720929319240648424688108445889186004868831765645582941893811520224785176327076871632751478895082743305891929177622509398848860808145917445694857072644692748383491884598155571785191653919620637989439841813357948049328007218784006089019852718161641700420136309448656696844743292104671813104900952128616813642550291756339466583071809213190868613325566484800802751058723448502153665321226851066032685623002027085446982051974354712066506657738772793635946033252541472419837135362791482711099840453152927372616743095853408961881248149292534491335945767553048272865097132912350518287861132507419921584585078536706814482875563524568389526608885804632655369389597796048215389678758446087079943592114643376420287561407468015432722094427168735619411810752813079683236063077583129438501904033730674782103467208778965438628772394932612425127509151505384878758065054007151182142728848068635714136939755196619375871188971811387476035917347431128752584339265341868953654803694575566769297287554219402816919727774974820615130898020932664323100990558760708017210581132352634306094743659302166452247823451553934163649571771710493985619549681139380617315103026354726014628610674014803967628629484099757995232951292461348458544426603733901559153649551708555015423629933708173238908946396783196973077234178272215249032552961381530441059032266373617746930497305278523777839449404292182973161320318251489921994381821161701968510699008635862480769413861674346972105521739048784101770866754219505424174170700842424813261120469013364180930227273967197514930400893431456809344738120161277054866208126630006481511697156731175376860548980656212536344148454983818017494965975086522983009526808268403719389164364407226534473306965278416507601513808433134359707334658936313043027079300111007189307117781344287072642361265252797162555410781905138680802644073446035938172083127792467912987417522179812276309222495613779772838517076830756955638016974213922376594286379025331242145420924363283178585547813531129692320226810866528253958783220084487788305060334466796353291352289216555324855950546499806871772322867703655139766501797014240821017164152521878872397502241812919474943525371507805692754851254518142770622975363416477407856612803336576276827616456477674852863917350884942419329711731939501889050707941780617953960029439290890982490735674806613220785251025032127925452734684249816541137641609609251811326396697190576918208876356234846856993199995973352724190421412349142166492106079736479947333188409484380475166343874417447554479868638901224225853719536726629596425328147097614311044486029148728748219002657909574020449018477518430518295830172543163377098368134478803875957054770269688518681049951103827113802831417637293411968496953109987977929089641049445411814733323008858132614755153816679898835233319927409485263645026083219249168026706907380589597529330505334428761848726458844159129651656609731629417392927399852378919674056224038699822231428995133990817549429236428789534035522023392100735107692070714737836447084810841115310894871849026754395861664988926887061414934610112803928264668007758454617239254143895920312957210740483257978471325555568348361189684059289797070564814385622848103497446904240546473069532556893692598324889328156726214523916739019777047127569024440614926533569353176384778640396180291075281559651140295347395090691182643292992497051487602683589826931804830740078117621841640220888164556689048838053610520768531312204975011817831292836225249187626559248577673389662016446713621551621258589659126885345799011699368475653876317686229241710696956811296563101140639540753870182171425897668631718861895012699829777424889232326040712073750905730456905004186790701005921447890379148382596142881782840331956609991283388873882757334407609866751350783019259230822463052498960353167606005514178341481492700515260460873211080014342859198860380003102444136023795596281559275199565771109604551441623766208436004824641691016489716301494982294746531694735653704938135531140849188732015414270131471061304438025582083828627563585181585614293624899024565662966676647856008288043685003487695017547636333927764560089628326535566563484132257765758606433047166768260451531632047125194047250601376360864614992196517426254937466726775923920259284947784782500904762804428483985742010067381355852342199600742724255762878055282300549966658841331102720514709682706555262495316051934355845395792010796719383767980277302665445943550731989064917614436558010290651912732732072479469158899983595655006595248083114157438079568896509480717413993352335652085916549247775286837493464523391772320648163202689566527655004140950336276513676169479757459954506643960252714925223845091975810942670849585136280521426620833898596853315084299594509758310662132343669322657888270433746378158986220462196100959935614265664979859812670279112926230374291713601899050001283275185859010163280846583281044133888591852594356089614503703,
      1538163948151111184522348018352752457236470052231912741152987085700426587994499586936095504502592824651030259694512834289499883304936207773979326881616298591826708963961351139154145666735896499168772938295823775114033687865990133077347971629499061526667616933695953788441685884251494922089187318808873847684291843506650906368344980005707860777276969212052980902932247186643501913914891419015390865498950327489029504887905290310878773512351374805024943905702733357932325891066117263431313360140386955387395366567481581211904265210365528747987663914761338094717018312043262361805979863220668649830667745684817794238845198573982455657991419151825983375847065062174511174075567707548010503423655856436339999204350618756263275927152140844806476799446873629368060325742869890076383647699437489197017208050848151527738359538297871514428055321105366520701664415859565896099476833321648291000853380402443997381895099941139602867276000016227447285161381286764159663467207600518003982109124652024392761012823080241573069503546945154572707116275871023624101138247608076715098942247377067629271679972906518910921142360091179362963172747018607134905880300560918161416418307152642302798766192630415264483330717347518959604780922497182445931682896428205277229579031191761873751745013402994612051656220661628266233348327477247151476731038718547591096953689282999476637051243396917133768988257246503014481839785514246115194070987555385084868558234955857088770547582557893818981244169362947197473794593459696486991525302479347970747843690171107446930798795219896701181059072922202274582897335018173681514705120035727536741492818068016050412928776384663347254736621864074066872882963740157496185026164124625731011178020158814546995895269552231158814218614598561585494723046675728180981068927816397213062948170173776391945785769888009380729056200053806408708868318145775788620579208044381401595008945322665738771039838158634133963809273483098497867042125661373283879676812741762280487181686618945317667427044026885633249774708971905685018713147350711854545310299552457953810988890672442475143343001818616498706650981866312056831179569809246040260804827156781020145465788723569539973536983345648457505991866209200788378714196769341867541568426288961275546711590838003424545721976551793935569600024555227747784070978967911882284173747699774469913858115750609505269741569456066018759631731856880161950306495202120190511142593684018609250754655994666879276091217108954198260307147311785483826272708666845726292280129463677769713434205444082329712087768002591539148638837166369885292095246132561480200758341767540241781153307535532854604860073913431875525225026439008583658711542056980924689772222795632382435630679713744539082939131561466381906351522725972026639040088513403663220284767480578615226490932301156904593432356629309271601370022632652109978041821887940404462759436215854831858409198678639759754820582890509028977488721653243547997534683257764344386455803058721858054944357930653744370157964052926613757873601150145880443605443873386309205874215002213009067006661911602738262689217532316664201967897835093484609407492176766591779775328801190863348817040387652499497422594675881477579851543044860975236906060922921131722320172963348750633586766586518126585413826931098052563020124642900281521591571058739894400017180948926708281363487576839942947178828876794313766551937237230668029663010236107257715815251378547062487286589424694450131854294495473945046130622036652612682801134552293411852172196060613223075173896336368240826656359450085563315602315780112850423012464049614787118296978416132616606874564839129265227153924282775292490281307012722314793872802785965058283031927756739393324390044861467335518139641142681656078617296713655981830883161088166838834656084981535589872731359531059614790767222231772967723597492448221508483464184394589037946817855837538060171042835064268713328967056121440343603605059279282558709871898493151116905045394278018808234870405087251981798773846362614381697954653940669444652817708529953025611474279901335329930640064530743707523925438093417973377943348664239608585464755028279849998383224643102778682800112430510683432511192416344450680889908533024917503828444063704583433821080878296442444656359708345066800482920767268556258673806581315489481516238902399279119492272398260478928065428475915217889771162430995110476303952333969410118801198811683257814839817309230890181907415932562389844722733865663151994575729780551432452329457480991555801275224490183267697479882847945326729597125767451621566313224911718710229265259288223554456949225762475161927443390242169933786145772884036249609099573679103297683763092748692401900764172689397770265312252976782222851968912802760753278661651370914788482017511570903557629258711645938728231475108297860963877872665897471112776744753646889723361818744931542058631331820971228480190292851929376494300068268549422157593267759688533990493633648603731334241126023814195408503215770819122409885004144333021646241239589116929857078753101110227469902197776429660987630753256950562760359352230827330538018534794787495716437771941042925487309301429735912493543071122942199576893895249050629913651614273103137281455438035137233070436994993028556142409173115849352846613492232295601133905876159770170153292789799886113549179381732494222870714793320293143206887506804358691731825112507345509495586573602264988171864344013724017610189850955169742097320881536913867871640907606915318568355763148355868454202031269960348692384351782699299472607411061431348117349950094489006515550576472149012969534996848045614809252529597520749775074767873802008526102053664514740732452728429799950636311065114653903400289642039390952735636386126878358736374126899807210381724380365881122879874949071052777659174543949004499943828947896154106177958409524330786728269610498099590214701272754164709434352876014954973293708816405328210114206935735541334466298190088403702982706461155242739345061052620925096686221459789022889134268227768341726058966810591604185343676509848328244993666100881349905219122399921347000731933959027104196943848500527291796212051052327878613385530998227278342707725272226955257847210336194415060433621789660798935220575153448524227543152,
      283768441481996339003381090912808425227079925288556543135353543830155094808494968844658561089962736419617243439028483317340769078976972723071450097070731400480256529367790376114395869595687508635767766485820795064776306974453781155021627937197696520623152026633123349919664852253607406690708406698006281884717130660512449385854041801062484089162476945546482950257932194367879600757007744688674175134475195166138364035646136201870707096936723999964410918564165443330170632591544007047762723277429084224706762120689489085660243792795329227467452600474163794632635184811152546929778908494797480059108264923539489264825934295878205616489016194511103519392348504054557925778009475875129372909730079676428991238446703785734727900816376758238930892245307457981997073396180866957636925844785423414357253298847683165386183171661677041051815063839119089239043125186572836551423031889437251257643512896123380208664268175052955361887763055903948898241173814559955605174858622021917044905811236898925160232697665711754987944174921085386240215805652082621696320481652546329046200048241842763759647954789298122363115188430352663771008163352205959283749655088781476329264871873950355766634319031761564246598707683715436387925585638903797893582976011809035392754353663316156639401750540394302683335656134733743612882906874030085528893454324235303870024337637066804485106304958758324650707224666641773051193884354816802557405155919931776406729416751812487224896546223813955932673523862780809822866936137120748316491723983138483356275879023531083050508527212169217299869505075113884630429956652366114726506968895492397952773785505319995857615788544555338297590703624213390586564826674178452963376243611520683345174603566635695135624906027668566088890456636306083533681192981042314896881283602480865590580612574875568786546051239695798918183610888309177124831534906792651868451499441211204083267256984440808462351651938954853805718277267629169965007271255491340768725971430460977366066370783823053440508559997644682787949375247216949153802098583968639501191088121326884676940153041841499339197602350052732965753552887166397163907932554360727136389590583988434357462472405822909779587605066553560046792663614374828066016899531757929585259543235920827312525355557944448547193236071961053270036803643382596558826451946561945930499041547304563552995774515383616322696588844666479774662988032964768497866768849332142723713398272689023859426721004527560027057282402346690588204344330627119476023976719332348452064632280832743305087430272036574504094987601652171075312730024422538999982611164977872480125588272259498383580493915876903354938924147631624007072394729808032518656025208613219256299016843768986240236239720054059042065387296225508148174467938793630440284496737868126753732212412080486027926516291521280643456398904274459335923466506613052554978500498871625814211450004724597517318573379062130169368914214970719232113536639196626202812932038199163640502653790238922140158269469998155910270126978752917737998722574714178282526988086567748835731695509712006828434665846983441991594244425367479447926113332604210215380920225239192159245137186251264526849471156037192872510546187846028454445934356099976265632525821269712156335441299758979479147970225820711293627769327818557930431905338293924966490984801595494393888150450629419573878189290698613216433176429801980448677524077399453454527427102501137854174335367159784864885035413277042961584473314803278149353186032628850355561085102444444500437712300299860396548491887015280624645953975439001030238022068720773347013609492437406229843228040085211358761905713532150878011204069668945011172674247571397841773808633113286950940656405083799803796280928547667278559023931648943579623063026346794868435343831698934726850167985923763604342439688581798531986933534102654249479667592982852055355458312405245799495747647952514490722644386752751639147258397825413470878915674376384639303856258223674149038337550990014283245173905195344815802613705857692996868811561929223818051352861550770560813033520516802834361891677560432649380342290265193202816641474000143141286598809864052630272817981633847003346537332362195429729780583624295718525546322787344972409055699451442563642029910098187950094108222787539230453810773092027545091010867932538832772606283686519020593792172669851703895525707923671943190309645922434895691102916875264518203077447705684887210152222540127176991468310454072211861839408888238029689909411453390924624948411617510065905574603551063206520213391974695844515952749429055981922234937328413597871314157743245662452453510405468908509838749785403502597009082338338045686919607703454921218395649791267876089724161128258744996448067650372048989263173116754658671535965717765103075696996538081318513122263436778717888406180664619428337100159604466987935463830565515639532619377209397891271199201183163859074627835146379962141314181171395493651408903393082686156764558380132295536964565622343218757362776544635557984928616861370335634658351547017997962206527753285015777662107239249259501846081774321763290563704686004967114060233866779469537338212264270932369388887222728422231294139951490485451517478465200538901447124796421478033951772701624086274341019843275928955806559830405969887044395050846488070035197872860021617571689472483254593363786195383731028353028153128612938283319548936751400391831140398084081516619083307430561013321698840932594347322283212824967783004440920457085724748631804949452425624627501463120869276820775987867885596199702891256573196068610449800072720887765340265572553757520063031236394295461428415519022690526341907026585744923785910032780965656064637921399197977152215386264549564903782718123960150601546141422134741929284828451706040618904653759247432255604179783426906199953414701641725952104077339186179336494112526222727969717589150866877695616143171846769764342954683672928730860358703162058196353242583950720589123388613595083035722150585875107742349282226547933042457845093243529160161224131646012214294137837967258991096428998698852210641165239244291161773048893750636641184520171835871817543038990334473968100055927416563520971514556812409705455364365441989954298249240607670449486649243792931336187930520569050460684437890167182789351661299012579411657680755093753175317203547018879926709840732541774338358397527236531115636618708405681923444268358557291435968568165203130609623872104352676068968117379715194700997506593753200226916233908349575785278746450976618007982080204220675352636138481521872945662471154854492975023555184692589826065786530543054853455015307140689203763423157947711777028350707122845529967868108579297790124288631610867771353006292527670194305603138223375057570150389873971282792981404038410216157513364658498863388266586977309353066594541779182693399654650954478830008368474229379114736287478319961457659136799187733129891639171244254163664228820451480,
      39697628088287290373110920671120480047402601411426406825955837136675791630909621650444701306509219151202973928321138057753393147869038725220172738581824117530796112807291050091739373984404252543926557168491289317004049417938889525872073609718035005802931536132854443002273842845893258461905418404376485542474862587716335741162036977910326870196808285779710763535003547020994935806748779672592458827044719591227024552434405327676869527312983135891447254897916309580053910242704712609244455743770168745824008364394261898532009871200053900141766175719165100213587720909333053439616490702553322845152078139618084518458710716013467048285347420996315577817690214914183832013982377453775024927636422928661065487344074052190883997462253184474377638272719781446729060763579020966936462925580805609595349045803164325325818950713601629104012468959421510171429530957642943284289578432347536799027361733447179353334026148489013441779428028781054344656956485380031294725912151740467529420515446949387784551079357187644671767337480439675754271003805171336040706217724320516812101808138393848821251251515239278317754700033977521457894711037970456473847734144896445049677789114943386553551315830122479654654370042831833903414258535283275570294138454593494146712170611224978240133755740408675878689480782122689491216556116683660849499617477539037266553913754421437580379649105956828206025155638342656613976394302231415581652443775300050710256436355577900254071963642453094437487990941225760587907041766986489346585330127575347871558096958454680767245577027724971028768401369181529290589222819703372283649251484219858962617256119244547976316537430372673828439705836089750919839666302175259961102216742801159285522122017380753151587987660927969479190960274585753547768306890364371689287679330374503341543178719435040753412071477701144018655689519183653216212623461059138700984987087513002935615526232026732126076955161434911435764366136225870588685584984542151521880400651547832230626862785012823363083534994502554953399631455985075399537751043068949034563642800990862976869454009168204940936050756037005497421064366053434185409306832310938139420238735262637417846109354852684241878261375191670611684393110068996555109109524751439258755076415456913092276997397960804115424044885923850734633976159334484220557187379501657019762582848284901615374060322141829933269604908909898333304882802424957747041475149712152047633496558604386199349620573499280866329721295929033294796496973201586072149488257446218770319930208897109596453607265351410030987813020170218596497725253431402396812316921943881293222743819498115430658962107495402575516031369272076459941368491376905361907581855367233372065791990939510551377774743554273416235923175515759866915373571524258991816428320412920684747705410888403647142669590423010140317544564049869021151466920957599296582560813283531660992546089263342602302475782829601926328805398308378570220072998918800268354856430338026594608980652036355883988459955733116673609715780254775995638693851274052360619445423507454071181625297347870210576409560748494441749619627131763421850717511956921781138247904523852606295424054717768694798053994222097051510036771234164602796363444118992393828225216572070487656287717716694656052026075592202288885453875197719048900629604033276441605477768721282159182781222763934659143039990495287496786370900984603534427445031188438047675657122939968679977694727214053825746812821605167958615837491262112524915755394909622772775916975668110022654411315816877556760008072814365640661392606267658763603644182821255678746874636698213892253054341802407635093643796565423630211106337656480392340227298629244852439851769105707255766800684796323292895904296715787371214068373097667127115996190095263229442536721700425185005548793748479957000927165885335728554659771742110652433094635053295679814666855630393163306117736904505169390730026554414193390121646882301252167138446832194332129535713194562383844358567010280211534230649256954235766673286409314047645307324561804132900058245294817580722016654387545744011242056930488618506556745271544701037712711310808348180220899355093925622789699130814574637310789163298958192294969542888727307787459076201056087296549449087059722919600947458410826540726766735998803089362174188693475937223925331353969834337235780708265681525746502479037398788681847653793825444309634294626321141050984288594173502084113258599895273140184340551669481421755502721625773433591850664957272093223797552266163994543092533034110938651190513244980773547898236372145429779933942851268923965302278220827912892416763276613633243278297755849075730749447415747626420712512829190324058760482892970145162121421187855070594700839579524620611222718639901559672706520463112266374015285540569841957992314060931690129140598090512227866853083436856119472616019253051284196683597572187228444079222410350547321421779818394033617646903879865541746390763984191282485127284668911905467544896978364052732819333921525155845062601485536819285171082608663443401533057072836274706473066532019798091505861356] }

theorem back_el1_23_0_0 : WinSet.allRangeT (back_el1_23.backOK 0) (1024 * 0) 723 = true := by
  decide +kernel

theorem back_el1_23_0 : Rule30EtherThree.allBelowT (back_el1_23.backOK 0) (back_el1_23.cnt 0) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 723) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_el1_23_0_0 i (by have h : i < 723 := hi; omega)

theorem back_el1_23_1_0 : WinSet.allRangeT (back_el1_23.backOK 1) (1024 * 0) 586 = true := by
  decide +kernel

theorem back_el1_23_1 : Rule30EtherThree.allBelowT (back_el1_23.backOK 1) (back_el1_23.cnt 1) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 586) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_el1_23_1_0 i (by have h : i < 586 := hi; omega)

theorem back_el1_23_2_0 : WinSet.allRangeT (back_el1_23.backOK 2) (1024 * 0) 450 = true := by
  decide +kernel

theorem back_el1_23_2 : Rule30EtherThree.allBelowT (back_el1_23.backOK 2) (back_el1_23.cnt 2) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 450) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_el1_23_2_0 i (by have h : i < 450 := hi; omega)

theorem back_el1_23_3_0 : WinSet.allRangeT (back_el1_23.backOK 3) (1024 * 0) 756 = true := by
  decide +kernel

theorem back_el1_23_3 : Rule30EtherThree.allBelowT (back_el1_23.backOK 3) (back_el1_23.cnt 3) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 756) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_el1_23_3_0 i (by have h : i < 756 := hi; omega)

theorem back_el1_23_4_0 : WinSet.allRangeT (back_el1_23.backOK 4) (1024 * 0) 390 = true := by
  decide +kernel

theorem back_el1_23_4 : Rule30EtherThree.allBelowT (back_el1_23.backOK 4) (back_el1_23.cnt 4) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 390) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_el1_23_4_0 i (by have h : i < 390 := hi; omega)

theorem back_el1_23_5_0 : WinSet.allRangeT (back_el1_23.backOK 5) (1024 * 0) 362 = true := by
  decide +kernel

theorem back_el1_23_5 : Rule30EtherThree.allBelowT (back_el1_23.backOK 5) (back_el1_23.cnt 5) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 362) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_el1_23_5_0 i (by have h : i < 362 := hi; omega)

theorem back_el1_23_6_0 : WinSet.allRangeT (back_el1_23.backOK 6) (1024 * 0) 932 = true := by
  decide +kernel

theorem back_el1_23_6 : Rule30EtherThree.allBelowT (back_el1_23.backOK 6) (back_el1_23.cnt 6) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 932) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_el1_23_6_0 i (by have h : i < 932 := hi; omega)

theorem back_el1_23_7_0 : WinSet.allRangeT (back_el1_23.backOK 7) (1024 * 0) 779 = true := by
  decide +kernel

theorem back_el1_23_7 : Rule30EtherThree.allBelowT (back_el1_23.backOK 7) (back_el1_23.cnt 7) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 779) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_el1_23_7_0 i (by have h : i < 779 := hi; omega)

theorem back_el1_23_8_0 : WinSet.allRangeT (back_el1_23.backOK 8) (1024 * 0) 935 = true := by
  decide +kernel

theorem back_el1_23_8 : Rule30EtherThree.allBelowT (back_el1_23.backOK 8) (back_el1_23.cnt 8) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 935) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_el1_23_8_0 i (by have h : i < 935 := hi; omega)

theorem back_el1_23_9_0 : WinSet.allRangeT (back_el1_23.backOK 9) (1024 * 0) 1024 = true := by
  decide +kernel

theorem back_el1_23_9_1 : WinSet.allRangeT (back_el1_23.backOK 9) (1024 * 1) 11 = true := by
  decide +kernel

theorem back_el1_23_9 : Rule30EtherThree.allBelowT (back_el1_23.backOK 9) (back_el1_23.cnt 9) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 1) (r := 11) (by decide)
    (fun k hk =>
      match k, hk with
      | 0, _ => back_el1_23_9_0
      | _ + 1, h => absurd h (by omega))
    back_el1_23_9_1 i (by have h : i < 1035 := hi; omega)

theorem back_el1_23_10_0 : WinSet.allRangeT (back_el1_23.backOK 10) (1024 * 0) 759 = true := by
  decide +kernel

theorem back_el1_23_10 : Rule30EtherThree.allBelowT (back_el1_23.backOK 10) (back_el1_23.cnt 10) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 759) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_el1_23_10_0 i (by have h : i < 759 := hi; omega)

theorem back_el1_23_check : back_el1_23.check = true :=
  WinSet.check_of_labels _ (by decide) (by decide) fun l hl =>
    match l, hl with
    | 0, _ => back_el1_23_0
    | 1, _ => back_el1_23_1
    | 2, _ => back_el1_23_2
    | 3, _ => back_el1_23_3
    | 4, _ => back_el1_23_4
    | 5, _ => back_el1_23_5
    | 6, _ => back_el1_23_6
    | 7, _ => back_el1_23_7
    | 8, _ => back_el1_23_8
    | 9, _ => back_el1_23_9
    | 10, _ => back_el1_23_10
    | _ + 11, h => absurd h (by show ¬ _ < 11; omega)

theorem back_el1_23_holds : back_el1_23.holds el1_23 = true := by decide +kernel

/-- **Some finitely supported right half driven by `00001011001` never enters `el1_23`.** -/
theorem el1_23_not_absorption_back : ¬ el1_23.Absorption :=
  not_absorption_back _ back_el1_23 rfl (by decide) back_el1_23_check back_el1_23_holds 0 0 (by decide +kernel)

/-- The windows of 22 cells from which the trap `tw1_30` can be reached, by label: 9,825 of the 50,331,648 nodes of the game. -/
def back_tw1_30 : WinSet :=
  { b := [false, false, false, true, false, true, true, false, false, true, true, true], K := 22,
    sizes := [1379, 1779, 1315, 1223, 693, 520, 390, 246, 219, 297, 847, 917],
    rows := [4445380465869276532008214508674893806499251008781149019428636959176794663462713038130448827825321684434055761981905425396127897036829342005573006993063233236044070865597875583837728034922580958986760897981503228519401152397974840717188939948584506474696267155206628348455111813456227339750975208872781227049087343067126095211313398906608190067665614043332949679074453232768768530365595208338289389345874614915805295483807315279134695277863234988602873119971657245848708759833854208525488894784435779724773422856898841261502466478174521642221182157542380990289239595593044709388417765325995678743370597686800060750292540424486859245841745024642087115949126825092515825612254654645076213230050371262147625287537837509436477462934298073639204235328646640879720667640485360905660551707000410859273684117680522906986328884920395979030983526280349081009474250972695646948749120773633400126740155843531547454518685839834089651927371926089491454133184272860580972765299024434253049142377184815829344864679133207625786627658058674494794614821613084396052262035182809512219766205901866565747802395992120370208796803196310295598304889301125610007998313861284013027939955528598649241427180361500318408606595638881041725140548285029141302531316804261682045075220380244348557489855223632090698690820983796679411368838762193343456150300031379458034170813481478085386518944114349508045275620248796436241321101178488467572396043289350878463227955933196706180203920613445503695674209105082356197914299094447237021819194219341211913656473932984440293305534855643627609196256058192899856846330436736356114827641566093992005530007047005976474623787746415194579077429378281509734758038984148700924378887901980174285116363432534408268416160310388452754026612944399292933006976366032983422703544367871966240835882219595043316793875681594100122448051658330363187518916075429830723761337825443116370139650515118440995456575294118761080153285050388036120065241430698348145983839636853614148526472669935032364702313314953819012197348280129919491763980202446504735266920435083677687441249231795268226333385801081368655597696491858494424894087694863899920018796278599141080100066829696248199146078568506590563076599960701886398733726757354828092778849889429131227160139737210934734920801185886143819218866005327616011383026299124722802564265215491182693055031845167433983740326063324790255856438640873841923650016985635272661086344002463862577947046001884360812627662649960367364545123606077254152473949934365928549995404556624171047278890598461898067230381286091391134612446836161731198139281812101660934716972763336454850153333104198215384034349350452304088603086875461922309882505827528529403981742640051643519284720337985780773728737251419192473885693769415937008711001597967224471059695339825772183041096755802958436051238338746996482121128964856965612290323479899420117805526972725753423784393656402744350320503049954718886562533991975542352232452577417785640884765024359123143952312998380381415907527997769487262193327217990712669618536166851931222840263370829479974976048082862570707434440115165517516835175653051006930094420606217629493407210724109274582203999852531987234602693028616800337865116888016597377897985360917135017541641738650825065074991503946949568177087780461178265413783449782466890960436672786053774170390567531929516028712648802197958628473149554354330908330482353364869682777877105110596442043999611168350616538682825838863252132342743570597706605248513446337549329584428422307518975133823853121234488154281395826723511527942208469700779477206237493759538812827666801393418675833229182401074465375587334058111810405423396467053928917996302105380228976772019919352827817671715101399356790914545156863675196046663970156617921379815542648986302498249681887187860947474822141492849149758880679406588637279216520081401721768490804790237256682972498482760078863666757448676121355473410816609629049238157133609904633572866508529560479821050293618237658200039464117781618009672839966319243391371766374704102269031617592783539917306381041987402806090643812822900056275287739346452038266558510975371880036468509454107882061148632207954072847479553313935880394470299607509403486975751784081886949499629504853385772492015605361107720938585078279304826092479239764808673808076229650801128942553166491355526601543961426824979528613152091819963358539105233880586282593462450101039164061940703742916113308500223892375185636388345755243218781903615757501425801652474254167491831929233350314130427648829971480975657889355669373350070441766498437017308582377018734965175062645322424644712656078529824583629491970580272728739788361009120715302307142214337094263241888310640706651077752816701729166860537322221628661436855088700308181101974219755792783538141446452569673428455076036383518878757772607351029221872529391325848206738929143918697619762148615600621741186720862199815470598312888689897150770609244587186758226234069408341500612061871983599802666677307370271568137074852281487593269052175049557952235739359062736660343562567219568687471396167091278908480584409727654901169243292535030266788580664034579261840536636147492753596067193487441865003850910006946432464893823826342707279949628971747314025091803669837268123251740578877661058286058828628363270935445192295979503864057895639867138721200103787533944527016265742288674969224169854291366360035076328488959153287087613824068329098103024678465538617300130913015688171992917421331650840020188538345716970288041712806921699173316473248300734246298949632442375341942881348842206700212827974425297773740014530189560734569688393119861604196955381563056681100085910790229911374129953097671860509535147300378230062721278523504264370226215566959433484462834456424552135372530028249464425121280233316851657111682545776726426070478047426451919339411980796311933801113665576477667376547886434372930395664950500774965550137419060325409670903183855755962456611351496464553089034018545072309173412244339303608773428081675715469821817893295616687311570621834407252895712343341187876786671963634204591025908491547450300974484387604408443394835085275049812015125636001174459340994108662414653814132902497391380335817489690406577259297390506543525931538358402886811760383575875158703832564035460285012475180796065217352623374408880129801813543866318942023426353155021980071000509215055762729882776023613129665218734163747732278328766261361581516578955439030813611360654308471038143987598256315752570033589839111742775685132089808277753709930948492311644484188186385668369148203188682886378880156413349013897281987892210685634544570643733926541883287577125055426948642316764963393010572421489137413373051489186177539895554216945660945825041350724003675548481200172642664383394369861736664483498183637513834560367849296803797734063835375452579283228402261310229883883278384900215997589265660888628120198795822639972809332572505138101543945816672900363594514725360434060313623041211792729446039149182416589582523045242422962955926089746607339108340765027197913844857464039858625942519154779018291001992983617748480156636898373444955852693897011946144138109529684776124327936719177216075209144285495591525780583966856550418211817364012627154562193173475160934594098442587904213607018811411454085550832783540788994445590603220944451876295274273628975394694126684283583302778721397686744925492192005748984381252112898580387997550010578510583451568687994272817800536496250726428791389823936861796823657646308742876351587323014978740787059388323806037705135994472628901645996286229992358128511327721179085476391724219284847905515943609108022866742281898031885233393765649099318385185253209300206765142502778460490658376031713634357706500359179891085764444675997295548874207884437101765135602781779383294388249010139679198995019173415509857474442348602932117580801745156968665544532411554665673900687654082725275833858495089634518659698936187740282986080032453981389040769563187561480385972242184110214363974742344287822691601623683523661797749821499502553319081133614703132318051839909209601393776501848344395587084402603040246327210290442025629892556298520247424088929679068807479232696653875036315403997305223962162531722824565960010439832002966033566608882337933174884347372658614382156139173354346005182769128026973924385635544917389378106923796463858001468545943936017905805702049458309725266060454360280286472581459896801627226906248437115800892002653180165811378415735396176532520706500916591958914945615579279047995444723668704378625261620338555762075840056785608230395787559560487359409914699295771060147110069853955426347625208000640700464980372400986813275886037983730520354136452631991515397208832593684891222133284611002218038139508127782294445405493143823501113228786187331356473984220488242083335815581740953164587205222742116154642126041084366961799063733546369652177551299790394299673324909592025196575106241305470432227555777852449989193900089686136358669223609179987763626567067895344133865613388419851280925926696342085452063750011063325831007333888535986057149120126375366515384839207140971173660255576023516204675824414503100469142607736295546892700365048529749074573307302001515325973237520663262,
      5151819839213177838594368072233267322655862075940132606519395896843969069072564836497441104535747878298780588833902831880133056553739199475359062871258970026547113615980223092895089360139964004917285362786337694340573115692047270724285041343781657448683841496273940281714705886412638892180460475574628654133025184492677804571130247277626280643324795037957182265076239999397129280774881363555574723013567057319464937280863680577317464458543039047316653496799576139010998817173191393516713580634773187195947301981828992892212947650358958901678571747937536655990920069734065226717916391635937694851645358845041554098585134347487719929716862358037047328631313451167082172881292115862975247529155962410975315677684620981443597765150209107397588726335764671128728751734545685396773051542709086666555990425943544406379998785402258666263624963668048070471615336197302290356211247853286333752724114988377318796484724908268364324168868135597087283613577177136897141672356290684650022561932857642613119741735790185986876171798809873637571851387620021589973500389489896795558215360696796882852622097352013187839545303706234703001231838560941215078360180975658420193641626468108084417837398481287152703887550394489555424966982836200673342080624748486823370130325503862920594835282695318736310399304777208778386036072425541005982052721572747365421816218588360542564838609686620051725461728787202831809491686642851709686493068284894177198964875811666748774272481436575906587502055265788460117067623015704145718677660686768962127671791953991022571402431357989339329490062072594089003127276163334025274244414252554980632401686678104998529108593883563289552328264527315662053433656267843311753795584775585251070152794681633044091781365175169719391071182656579676582173538813563199697201776909308352999204379688087588650164583742676736482961188670017168491261704358095932471724748970157631574948176413532367472791295479818496339946271666509410111448809228324877230990907652633158101901518913857070583591977522868196707661757614280280358967817864585430977949648130970875303084786711180138262293086722278895691259542539242806744320135859352164205411419556512287599195583709617295859875394686435202572765052373552799200205961452434589666606977735436678028476002789637693003899455035326401888261516988881482821871170569477143559253523709751618581788559914186557025249559076565698985904336399644621844788422377486222430405885012106223868407730355372901739864289857055441381302579876732140445865748013482131182591587323700493807219125782440268041721830463881811639752871781778464926283352541198194107802944781403965790816921882190426937248203290866166615855619924464952959137746058616658341265713130668956380512011822628483527714161942673152918378725902512557750536000503020067132825262999033891982069905991315760183613969854062830520093385942988883336178797969948002618644688930978871028552372473727526467008814258408612546829993292714876069191502936183352870889681359599164124261122982675710501836477000793632064786340883201830188738431862744864174036562778820439682126102633426899482814993851681373782393549702493177826565086309671286043901492445584627298657038325056671206349939136025486507810179929534934452737048892421466000040940924677930973284243909523847509763179100099464249780974727336881474864342298321472263317351927120660759817149125697650026930718838891344221899362073166710785462342136433641928173202330055724902045548527748788522511057460534959220851930324841148070224707196322523563028096994147667625485759291776446309350067992522638347770994337726247428658018404826699267757837111887233225310949340478084668271570241348818948625249398248266062671941920756783056462540018777075775317143784591423641585493750435755302209590101692543960926643397785427253125840344147773315192941939922557997289696426419347683713217384867885606859281013601391397909000985151646409585898391448904157985347937586436876503484263993726919926213013530382427892980212231139021725885919341755779170868818733095684788424588313830140925846810085335501996787494642723932731881081916444545777433948930424386960420720120135428175823414468162856421247025443176780620323707743437805169411610087394346795107184378444238912075428287273513997722340487241866664899205944606738041884741616558592048123039395573117253133839107644257484247758376678149242517061358883557807636923158333824295839250856571792789579835406705281070536481069112369934662190612360733221238727281034388640979563151191145423201863165252339006881880673192464337160328973699847588499475977054551469793195260933078361243395198484958434113121719887581766919843289310785420923479520745442163735997101319914124356185752347597777843359894369950877544170240901730303739399750490149752555179934746655112252597430580577927827184619144560477853207829584958177688182215194192921542433856643449782891659205235354815992749473708363635460541051685270907660717647681256026114281479402852451801559548569009966880285309706401369049242463598685418258311971273529365124955292572143148225983875815605244488513225685571554801981030581134663224304628728796399894832986389637076167274614063371038328153502920885122261939636997952985118242956810357085795002525354028073472500279918334143896108914476952595010517412996094444774181002205231648519229739688645578896996100420463557251839688810528207853627067191028208210208175642085714226690560094414193106130622092171776121200726352126383475658616032600364843065526433993889423681120422397064446901634287552171544377049003900014313616523673722611229977310575620758911504732205019420295945710352171825301236254752043054624040423038175922154563778647752613310487341071458655404578495954229079369742955780744730259530349322236109977926105553962533685884501567784201795883043179081926710386575592301089364062866869904954572457147329842417354172717792416398077880363450876330409155308803070231713571230343725560794986558008641520602636402007779316846561699339401755513907050244182688425659131061090609007913373619226856512491950172450103426961459499276078011186203355754252224837344281786545101642712736223478488960911564366986397309574694194212928109492631329759837250098012083632126812973688999913895683380119584633095041882565105330517961765864143057725639472664275064782335030528800454718335335279203061100822573130072210853827017286261622303225007057737500267098764818055015147141393043671757080769198519796766815345370413851934809347440252620411922824621962303712449083927413440827194097100070187053025735958126124103559629261986493985903409562674077619118789031770981539538791550141893507190236388488989796136103558103417795854404637480632592525541089035233910314073433757463598632732818473527968053977574371702101939001311555206440289710717969027357337113861319551051273382932970317476778800546089176827529709493306148194127160546943592213153182199146511856548253272232237899581757908328791110528111341046296454106687378641640325884060506616063171391733920211595093158326398558105185551936761414496125502954771856280744589136088024172901362495164553624797868424949409872351182601629149465973452761759054828963910976111274807885964225562088425884778232135356876859348262032467995706888052607914457312915548400738105228769484122335703470248048845889739483287221392721120405203092498812082809283273053861596533505948372961024498008974392287210483289504960045846005992292485759334716110733347788158342901017651216019811391795810597713917932362193564721810147184394257115069797297895971039803449130588715077541134353730299647037656148520151656291083831951310630338348161130263153289411743105494760086503963633365638360920770061447147799977354296936572592722981538417923789564481782861748945010107454928930736014377565802010150735944461926174582817487415518734949974126442931137138225068779779769787861826435538209189381951455993726166129833439550751307170034996451145488782532553844506332849256817380517440139642116182394411413300950860921447781909789157871092682172823361629823103664739721022338748119646086676073958741788873607440195864566718180084309369454169703701666212758166965394148870121745858288893167662564032407627079861170015279000396107210568322879173644918409973959679921836976582019318979933880279264431274826395579749637147876101195647864408066519895996031769607327998420470573803409265433897289725100833795147125366187096247979822829799898555396005070304296158662592102565779791638892871274186950601617023421562204452097918714028789582162259101918761428321344080161353849719893091738737462707723277205579575157507466574135037546871862043891888119221989044502759069724592671087019143431427411418457802875715142568964783745514915007420788531465682579765548535077997942140061319950132927557714045925893902285731239534828245181847372057019138145435216673865424926553128676183902527065408541809278218747580812938036718148388230800542536782614360110312077544406393947894600935355241849039160294213091488351001667529663003673259500350651853642501367201521231804709260157102643710120357641817828865838272513090141493491485195845533017912979622297597338903020754482925753079947598812891704199397489280462161409922683655958335229689615088027106348762344526487532420246982785946751004607932490791771279028451271938119943088986141919963217606303447820362511828481220951334525007214388933556530819025232356006496957673134818528509889979802590923463352976845346273629117306968644278034361284827957445792943394355480930787297660780407401463050525827739814893183041640140010767528172532714285112251997762143130315289855852629509251869354859192613208828968096453919506272427885934167886062717762685239679039391613810884805796413936754920070207508213162695873357518888281179203021107856635886834282866583191500907030980021463446410696737342108225903760913656562464091454234617978929554782480425921583536834125954021596339912644607319791548558817760418447977613828581774942856451673073547452701962861314142187389110598854808831789546641067310676021251914981186916268161306144932695366217086163975305864193191658447188540738982728697158006480447573961434014126882559864967089931864407659286846828659288668108897815849638557651524406532840798629726244337566863868885783138454199972015173402079488405576222319396563746896787714164065426889970946395295440749021860973109507785011387859018344655591143652162615420082417700140368509185467560310687247764321847725123914590133259779299192348581565965130392335520933058822321625467965912343063968858041266454516263454960719691094604581638167525928359204001194485222844962003331042895228455029615680650668872726971688937870066295611266361742078531958688342939115151734708221748683760690444199877126459398977043603228113934349041415370306554131514358930716182647336691181996347075700336483353267125407609190845459539721527025443330743836152668557936157684079462524765851756002674726008121607343705974208432205196762703506025136078349554208033399026382807128703468458434491882114535499647566698923057963946386904298251963823796062885580048102253218921672260553893788398538598679743675611214251908143769975432946235124539580963238095371974193157113574590683502660996513682095013430431099541887763185219042141131641237542658111909274329391772248127948873308746263741731723701494823933751620270535172864647438954728032912879031939335801977618535403831738211261566066299252128354668810730421591483821516206919539317179285801651728277822462684617711299025066980659254535465936448596912200248530036861948943677938322236264560845331902847707771928181768431258314935925752986459500442880304349160177113880285414712069290602210762147132978986318021302323978795339549797028381872309919214130316448081726749050988298447607967188463882790799185272089005661495601026520296188086349991771264704405112874971372560762236678799868770183707365153459563460681226112323778269473841767898965479139345782985254820353409058,
      627721644369229198087702303353393767029158995423547067138358072215424812411044162253559566261195799211878329669783140923674831317108137528657722289166487830063052664089448824857897005285950670211367018541431122476271846286724220172588236566009445273471422367448679010900843031969745871835926009699513533944200276513298789514807411840378528994415810010988929930475109362236120267723191238441874443986322481461319265488682413853882760442037553573821728394642897765424154340244491006197716965719103030708538272403456408789814917523816756478962752746481952613596643878026648769058108096984027055809582867900326171313156291831000588979132395986078421402249883465986182674943566163734573399000695526086514770591446844227346703016997834476807585302785881958791848570946552285801022341265844303853486990454935126999651455804435560396236308271745270711582799280512102284908518573225577035060359884601334482376173385683921333293724298039966781808419647543341127616332643482918206526021343891800669431620801573616504789030427523819370922473247677219777250048605293877412008334117031684911521985280317518380809988890877483400639298151709576780866254431460590775428197539264635273239618535720289749627446722306362371049298197563423436816810933256002111759019047519745908472171582251828714794815562389041296181451272184111414978485210982314490580048443343520828860153884670540448098450914483654995550406292218452009874245867394360544761298172126117336269522481155798566694735519361683860677257126214817798917532588325698312875985303551268002359851281925609276930120169558338664201504913614046448610406690927629238583379004707459662109725765045442975417779550599442067246383940173876342166052031394931391943207683541129157767754073700802275121850227492699715221855568615126127897506837465351340383209468608551236017867593033282155578320402419305924858094493530557548957919425731053225408255466678308916510138029926377163037787692163487936741935673210055943164460225692745199148860466694942458884710938004552018889672948204236418426594301729351736574012187708902174505642896758001237787977006906603322661925369080355196975590346629927393828173090753704127698584878050719582915983400056714075059721998046194108025028334825519814174736916013547702879385362753769967284464609630420701676085695827607895876663635455356756942016225568035834228167272487497821390989744398991677728613195340787474431844151899915113010873565445012280687003810603192619494103812085680104180460251561007355993669473990967232433935396661657068737393923789514382194202594359721603913378584540690014997606156895127323771169806435146939247057226557675463713787856807917456051244387702708833273934905641228516371006262105715073197357937869677642318131471836452937181772907462624296441807806583958884638055837674943695515660422294607636950788292889144247515992886103298749302683010129980016550479829276696344199886880218929811384387970255511677629460000081892462239108452530191752063210412171378305603683710232437511298512423792676466995230518186578793222969742686714132139456031295174161383742609237540298190501854610138521493382420459927181498326519241043752272941637319743067315854192633172405112376289846225217322218166871165396583478836061389911941918147819687539934118067256493204873851905678338790893278407811794627310783426377795180505246285771038958787431141186484798795697265017992079959920124105892666265905126487494638583356023081420448556010418086585696415369733799386487971621533180665596529716199866046425032546106835460591179092134189657655295052976322222219726979599344647144995403315768579724425265005912726260155506899080489399745465256020022757557447793703324976169965995067480587165587478282407521280586907376208570446916919876866613804959249719560398508356850511761548006106980312194868680774390306691017846544361065247446196728532629959098466331399100276027246969218000824326925797244483327696608106406483821236642770827176763673757919263938783355557157187149679688418927537813834954812988784085971942615588002615768304848717928728219218038729101504772176070501417788351526707916691119421465809458842335750750530434054501018473746241318035828897219265542869598932176550132885518625226851321643447129857869682816578447863468909109300888134613682043926140365982406688632163626865966678489014484139416158316206824029273931871922939083259326934370538556624662581232455943190569602174155463009693088130062006411860022421129177340058590074899502331617200519112563939558144278017682170197311456611563497922916550979674103239864619474518635680333487214594143731470978008458710889941591712065148339013655936826466770081713778753952437381762229070385853616432482659564580286535526466717463863368195110914178228760869758724164545825627382615739319780421400187970404625898291107348137655208759755660340103629418322011341975684929319402402579408528265206204007976037086060580933919374387457733976778766679094844954204424159080987534232080762480244834718539742230234606188081357607471929287890393821118587160990987884884798597807410917757514357185510249021096061299533304952180659546757027276151204796681880220021368020124868124704695426433418470113676088129526302525611359512053529801241495744795595495370019527567672496317123645337852360761124460261583337401175754477076340786769886060036080369984937927462352034993898098873090774451156931058461601823073201048384819520930732978539616639694197920532704396823546028313247911411583453124450893178818578998231321653306027416843534111789897326027651241510575309086413432778797177395554875569904553136212144102191764242338275020726966034593116535581920700621540810664817913002714357001128764789360566751513307745895812552668891597711022210432459911056849014476786761620804921281469759825023695681911825512549537812810319160161243356339636155361242291859718121638480518921621862627763366852342492060950479524053927239914255576601160324825975303897289243841944553013576230383327727102245220062822415718049869203615798576485383337139716428663303822768364964534050731631809442482758072040296987444347364241140456752513332191315968927508437970679847337290086282393674682803918694156811823880336370067706082262116763906192372766441193240361406202414836298327240116037705580474115548413115927435632743938468219492508779102142099497216717156323849494693256646587175011940592852576274963396861168373781621770614646969966518127831418865343220389477047559806765011663948471397743422961812733559151053072753669077648059907106474604464602434042415063666032704034202694848469019428501036404128259829304057955400422878998996253059516381466817027837643282091424050267522740055365581095458219592136095707527889554907687406541927691835725252483254737453792096274898292385633430673655684148520266327348462586507800982521474581069373845104840008385367392155268931489149828293533235377739921136418669597005681490495941227465917003523743913631402758684228618349688750177049421336251035620166577365343826793910856938113800273215807811893958466113926268294785604857324936050205148997247071179197409541050475470576916943818186650547789989533620457464969396431826636564784158095267086326891575413068753447895973424656257595854285076356195910524197164032590796937336836313460173464421128447045536487496123794293687164292157827155749566463742511625649212672497436138842132622008034186784663828227159579993968156194631866403055866562728364581023228002931224384764249060999470974694605217787937894309444135263956847973052333666309500501379450583470554813175831030393996662793084416563466094199038590193502967466363225755621142855614692938915487004511947730272143476640860344457406049323619000891443878505464076815531295611299144020037954518964971081078004253520337501744388492145878523331199372087456724683403401587972034654112981540063252324758294615000786354513932817484151002646471367687352351944227954914519788567302879364569660486755563772245288177552380542042550067460151946065195945092652064941075111898537768085263336538043961915966420989041031604101748872832955089259059718069400237490826852970683614161511699640764026956615392769772368249199673668235803211280879170729883876087554682000566702727430947304952844176318764506151610125122199910432043291886030771799606781445503384614209505444767667128054367034174718348326042978897720147961756591689220147043256740823174843265042562681031342744259194167410986423614500174209354874210232915180028613809272036741086173772370342483515759913117221684017804482720638170217430603755918908884737470624417215633791657129483844645615186644073602210153731317758133240717494082476283160526034248174624782974490149636812119026536882244430580882697242068376531807297767574517932120261770044543857340375314362953366801496724440331859763599098234766723666224998452840710994251222263837753463,
      325867362445045584212146274008850396709690000730922350160221170852274539217041540914494446042663118391453531519209239626109152218768810466493234979478999542575722994014973703791878185660451790835651165571204649267458265106163789790902949239209671676099766585022254546201606899481261893744217985651517921655336571607687693630897578069493923884069608703234162526559399401232382332964254309848346029126218996485366213557269006639096809891561862576172561589041397824043613424797162432938375005835611179349916013735496438352163752251107186068414179406639259225397388998488846063542649627667703656841611955362532183822202683604206670306595856334518829070322253996437384435126115212064484597670701596001668659408411632682287051052968117764161791187042654087910838412522173646930689028573339907730681029240625650398673273417095590414220199504012162237671946486313539907278601015502743730932774953812227748640193346610713357736283301027399119317644209878282863554344713249110608749734757306809143065157144662213954517176110414568662391756994241920471187252865428477775143329529895796908107868156938311321644727866402858327506919387498117047388838179085266827217712280007054669706954431684636781600660938456317248530959764068866465566748369611002054134845620479477876485863436593250849895654909289917130538833977188756628167640581694078319576037103384227615959373929593803737010131852819503345411650263046187225089254889917957414835600662900538139084575002678948871881891672149795562580589006041166666428678946814778533821959998590029780872873504339890763121307966007845878925308981561326229998420629968393708342120342251663738299541034131788285702457199818075013238225073312154651991337270730425423097857300699384048066938380615382155127564584886791354508871622474204449803486525653024114820867348203477172826637655313702049147248916545524688431370393966718291092760317116397125132278501718971032922980254511482246811434081177509956782171878162116860790633046383866082469013139950354173839017166030656267910571674996017597115697979288464389987671167679542484098748442328163790386174835372961404088805305130264270416687755498696667679969243992915345257961440725950083862480840427637826564289227445070509750361217970371635686531236875352426515008391963698429576760752930212239748673661375667224747686234071785837172762256499354351799906480220023247938955367785544429593014278999179451525249533701291628621695915563468984385120071181302591398453155140392202280794411378512677622452703343445350264794785069805942243329833477765655331919033293905010566367266793328565470156357655011814652038716934526047181551343187900455761584079972600394639603772554474747759040454515018178880500926022245972332007273958282395544297188764283042989383075034974042492103658776952810020628541890507358528365754741699687967010844244445996682713307463872578971403506397844142218455659899261289734189075230504031806174600478312054298326373457505216550703278794472553408798577593455499356455811870526037908768969427723606898665146918378765690947566878953482777237566944946952993054375924253771434464961056300579613732536469856576368276289913492295500220194923491140566917128434198712954419168400432767144105922764567314688451837377215825325185474392214576481321780515964494382089600099240718191539278808346844156764626088829083658049300831135808799635046190598790971050580516999244647060848166942649591456826161215127106745658620007964209058175415225860421276210898494584959964921248929254352151295502154099818372369033571351617933838175508911146127249661936312951642643230662356131914571376902808145392824560232069779028180814550784078655554892767959765095044391562864318341422393962861663525753341723285502577260710831882149847850986693345256943663608672161236935633101584647382806425240666500955525930192585246210429069928111227194884892013908084788899818488444776418891642611453710846290337800900653952789468303821806047496531283197247123703660589849818896186989602880288145452852129358444812640757994212678887651820120669683518845888558653772453160159597759045574041646288787956422219174932904846375948651460125310459601288884520321160608937440412191513238062496983924613689786768349736198222726326925116690456975354598276134246263514051162042479375696461459022085574484403463530963491088427918351679313714397757165780984931874256927793213920492759410553660749112483211129549288818537944224808047074943750509162529607008262961770598604236683720994957905376516506013831287992204815074046861063749025973113397199756201737580843775923266875411071234940379600717302100285380974892776079498805630260460655175527740334146561037374522056987294657018852254176183871529754587680890435023108434169525251598496033430727295199186523182403090090000841898899489810576647240556587672799513014174728085745998443331265781324927090107337283974158144366233505311344404107120773411129285750366137002481839675878636160425861515740695867071852353691289735026233753836709723855882936173360184234691979238529532699725637146046917450650892872199320604934554475483674090546036667406190051601120364291084159553399165260916773916354808449948173482901513549479284019846362391818591377965112876909268309549340801121389470607171455861090115105018883205080959548022063890691649305746489071490413361714211091105812510590521738147631747672451400540047352760230862932234286784752402843802326025515366574218360459706996002543757705394283056317248138701324636208040607214177176537454148622282129196152896884965506016476148594163191438397994614448097314088130907016282560228864286997783949199873995301257628160213381689583095055644814374577792197782969615078414619619181595944816567903176051628160870799223305972469135235967637102326816731405665502496195572771815608723279892015775772222665663550895264675923519781793116002590296060181220437057102563648152554615124526429496116074120334429517490227250559506782961871873474352066717872012551546015059143324229235891378411870738182973179838639303195589318314549093006759785397929086182556793543621661698750308941337407674988642257263067932453945541866378184295996587516122612876675063807533689929542464655845754976061595968246386425357043882421205040287675379108028970856940317157034604210258936685295043510620830693170380964885542838162621888923641210905872193674418793670569245561024008541757023775705846899782775444657691552277265427989234401413493081037863317627812598215666765379827457757988750870669677685716555971384840335166201997345003973256015526049470201288290422648788611103766910209423899257123309271382596158794354215503297566236763371590292767414757517141416421468101197773338980695510219240396256919596803036199703559666672494890941786633617106217603518863588774792898732995361401763247339392417592916311825084161611428847242918276021197018893704093024012281426119997593406119337024747576610855290371429088324857739767081182815714101804415010936621826847507882653989131404485144878955620881534932086949758700788266939291304593380047528235806401278401041052018686232852959763960926044193946445607073634720778113420525348360953127127915761786610635370801865658245741578392119575061607559821100718539363243379375413984861400371130611905863555891662492688399821142721534345377561187981674442050875199022555580133063789361567950498235914641289411183234634795338782086992503005748475462659881944068699987498334532842183173605897483655148954213098879149546060086865201526785044605468948675832488297184697392771637463010126528010537946885758243456773963150274771250606938139377657876784765774368986028162578432510220407509370546915365879995669137620098114193151228788071990251167413399683961481472915569421300135067086964375385282568092739570420727675224440319613330288564195483136871590688651586320965637335280310311640902701165655257142761544687930116254918101415784167691611093451423798507081528602673597240744577732405044586805828917106877209653067977724511465959227957200443911945778666182388325347853720120509639085114914260284873257035087096327895493802405176162892469512388153699661903163543846688476407908641948317293504168547380993954589035041633202817083951644886289694657056761970316587609180149383313,
      318630149435568505170435256190068038182858439993714920471717689907202146371635052192141472064764761548307610719634564225456907917814788486460231969738572202117154745916521523519423623250243485758293222676330479605287203127645572929074501401014988722879162786096462655579698378159991280137722626751377995319768830754636531752184689936678383306448215077929050494127082647470575991683979265011001937897404479119427155366808448424180332494187753994617165105779447883402281184380683017606212053889070476387056064745607961120918070731040526165249116765939473774823303532367265970832418508984913980405804453436471651221029039639526781827059835370324691373024194550541995337717324895722115871881010024468073480859685210331652190792713643106746098414194769603016632500472405886024302630285581094377037840967475088049680878920475736545539600442262373503591045541698187059763779607339460571248383779032353330916705022279398737187749732395258778747589567217186856149572211297350594172231676375577340171058636189030927408028215499938976704792964915975945520526894911286922440393922434115358248777679760265439441938756268870613005992780091668836468726346010231250471793575738754040471072065616917526803241015700292968857826181616680769841777956515259399970068678107273020826175004087798584897350854517503267777527694167018450396580272431953312780646793274260404129067015965741766700893553964115557652615109994391904664311242869209456654969708323287076469633413972707570733769954247467885078501905654785893546609929364246559358477661065161863689847569681028194587395581968325681253519659999709765168522066513477318945168079709393291217031911727744606312449831767144906166465856600196140966244761505449748949340893049515725446519327566842518195148257698390266069813322648963907692059440142740193779250778547480389374401265864544420080119784650229982464357016405436555801966282785246322106092382309991205717797715299468919519029553360573542627664703544353169841588209884779362515158161038396567890005940133816744653237185359696833700267960309997812119828682918191425008002395615419964328566847828748795000527388951644300137620500071470466928949884788954952440697676390627882520897128761072663850563358670677716566779933631294592111231240649328530826523742853246650839864210772238133689532597799236965388779991452190838001602103007807625892489081227950146935760022914039397989083387190877263100608079890745735855622563274423411983476794053526710998957656651512343184202273404079680420300938298607128703571703078219219575140600379797593918285718202389510212932734385095594342915954635916974640449807354851559918148639237976132583542985770620743389980917753804758293341130498211929916855039060641122135876440436952385758160708636056422002721542966686284086161398652584957918408023039729565697060460386088553428805811654627631110339831956321989636975577449206149259656374806917274025645064305705662554704575298565500283663897913090871296889994574628284250999047240197371514736249403933037699131660222784439463856740892173073484368702285470709956412531414705481613116259079276213246526354695332134744635547868798596871345464276176435727165236868131621406765456214023584879162063826059408158207688446944368591902232444656813619061073506107096078448790555108876471892797500953484453994717261182505419704822669569432364484826100082738148148715872777377315779390156710117019897289161867634635782887538103197158085142169836879607921273224684359802870759081550481961231197452106136275975774533332304892631294058836315781763973381660844354237802359362883316227090596939424071841654207679061508142271613492228727703124851191755689123202445467699688809477111542296444077522115191921935518476574638249707093028114051600465783644805525229557867466842039774684849316410921311531791321602929829374881138867039821080828733188527046054267481413518359612224556366641135409858008871068932144703893904769386050729775022833794524211971055712691855273694280241656940863809344735382786325953905515154268973013671519735526748480488712357478982280213026338802959120418604104635198276375589392812321286048284549913667241746487554166418233670023986759822865574303638241473678397334140727933632620505797815392558837871559106137518950840443274498701446376874817014923031112860832548888236498251792785314675308361373939629625497715391045614071735795285148564201212099366574212630107613567910672092485027210270452526580793024710553404592530333902893482214347105151584806908226646748636299091259495813629270084945863090526814978258329803296546478103812997907990253984941242511077776363825751533363542026934883108351012551006269033530259407354,
      606725944208646526817434830810150361345651915837568446422405150263591136682913471025469919786135146359291146358638379328740035186184861107174933479884340522482516397261479490347515047655821392465438899636795132759608462334978066765478567427882465297436006642913809793965680827144204675748179372039482959547881951704712001657462434425410568794299245588348407242373095803188308606879142779843829177475835769598142041551625962506013194763560840925671716378517654872647468688960906787346782098026651890028121009333599627906014620917159490074184927454394342835945764516456782039887402142701132916284058600016497348239814929661695903020249288109123784363080283253889921733475363618265526096299237730157018606374019317761819069282433936861788053809315591980404345943959258195568574192103936293520462220031206815879406392100226243560878090369681323973794504374573921785737825468049273129750307608885076278540819070351188940879322228606838730481439594905961633637007678187577336049978146128538185070193080648706515236572359698839443056948833890600760447258751365711363246349290172263407158189853247472728792235282323436932648190107507195501555535006946305334472285061256264959837169539248004878951185536866827005565643564946011976063978829793019261370371195280093082994368214945224677693564538189090848797417138296938084778725760482107243343017008927356399818274241966385704546579871163116875716322906458491285168451079354403471654311924305161329308904294432463047238940912035046270115796862906256628204860576205467693068955372717145493049747007312222727826626690107598591387506423002551425923537761270577982724861107594046353840064714236236465262356429660414779747036955128038043215510266026588602929970220623994027397340798604161789518495082539905975199159385397011862707576219581248347681734942314589303798185392611388135288067501241344440235759844557587177325570368590385450253884250558521916801939485484465287107719703442424491989745145023181456979488436606728746768476658649561805124351519121179144912676647848156375264088386153201486870891282675780443471851227598025891137051184074640304501960280737179324475015999467343224823279470205931740824347033326512312460722202855084947748979769690035315206971787533861505197425280745047856164521451079887298144017041797249564431940681878025875683413831298833088650285204671227962100376715028168042641090667831305668505947019756003161626749868624776259422476373649352618875531474718647000384418826421289401268702845681471397000561489556680345074963239271021317365492792537347651484332827680648496771538490277165041619612234855410812336302918911947153496776199257272720172073298323551990465472754100952628228453256435890608530474598670609605656585566894723046325487599140256977129741308598853461859937111787762908124839548929442950676917801176580157085470775899351723600498023793458514964472680743828633423941084211944940184009844375909329347443769007082183248282816360516359978118144938643507491616783328030635904773259004737109737773928675434904324501624872090851486766140957768524377330373119164008038376217650610739863730964135147466942113163989370115280833141919317919554582771440837585870300519871800541573419888321841749450310884594210905754233037267400387202521010445040076069478034653734765933917671024158588297734755463728968790802213238220361702283364106551984745380337436556883632859360176425486863081471692343507149269873539775898760578627947732269090652927485884555962367902485864905128804875,
      686998817517124743648422635501142258954840988515310909744856242295087700210272720515102067339567540184627807515052991287238507101630946288014407076045560715373221796825266675499280386995322157153484501190690555988664457002854399628179811779145219086490862915490662112298773957816771546796450542631474473533833362059848272014761210381198586842572767851581091761030059418437652342084191569152414966858485784429466741732107880864361373048436463022740909963753184234197146855177017557562169215648491339085523378888021229805361591435192421031790488379396409828427073587239192153306067674329275714199375851110125212879451943449635282678727750545123392232823143104590149717209224124596696568995542656856682087014218383266997954992387455849369389412101368024627534924294433854308436787297995179958235889352461551297104211919307174412512517714736718659600587165222499703634941578323492767896822081424905860413683121040001488778272775279168494577644434257756114931745587003634273966491677500014183482182456912894617740759953000974845998826360869987715449596933659030948880197637981742005454947354142717128120760083589911740836955709533311003709752007561562449063128059259180268156668986493102864151442978323088252305939301257275314281031951212419150561911008757668809538308302624811669328094466994462081079958392316484684488992518806788730531875365229323676995022100273955990319442512806281698870833599939540582843223569229698868851119372062342917979023978497550316973851458733283709045915852296109478276685808154514259041102251168169485764617559016563226664614546784501275938275644100612811610290604674071835455524431753755299410320633828404097430976200128047654521777966667435916925819546745160016118389538772095204376808249486878802669685560690340741617410420192185944379414507132637821235561397455324384986159463761144244898581915159589494245007366561922241287734800513751853592976441062209518315822351610242935312500652666188253230138334195173779720188056099592327083219710966627410171967641616128205887753615176628508284303199120871160107404748465164788191342255462834552999250683503753309547706413356664064311436503842654051108886316470044846536000495821475090616594954891884765781508340513091651357142985907753922940271874235034190463107318422610896928522661930754260850709228006107383760286171767627602896804072425296307152760555080657279373249229247775333786225798397486872305391614552643993444480540417540206389380895406266248682418564056503082483543333022334558238537755479641819789493284214504352893840057989072626871782133786388211230590802840617340153082862191286171522406812440,
      1493313690363006029302811764605981904377993232127645711908114091039402202715661489852347210450482638435153420968879558429272189508984962084927866375598053742888925391109039711486657499155068995144315463243912941735117386562026917696515845237397414602646439036540214652102795856707525404826167396586145006555779548139154320873060451457032429355655899541784349384160772791143133601904185942759723868345641492733672766098687390665932071500530019735097210918359918482301310992779710691034929090955222707547861941000652520640071559151515906787190714492311213192219901226001942198633895022036178440696287230202356244012423665592207568174006501095576986424537385784289683246463986443171349228507043325428020220116376687292621582636297530885217928571675053479662667303492896644992859247658717010053860416493820971420013851499314062253577169982880506680989072307407638727548354545411806707886846592907390427737912540361893555668421756012390158150436429943705765332738476292038960815475720519990614971897622570499085951065695269955622411356558999455212300526487745089044281179806682616985109599450379699368536368580724262453351910458858009690648190017835294071929376582738262641206238751018107977772615469812867223143341394102604959282753817266693038911677873028463792958028990684568258376357862198710973682038819612117930054894943082743968716156565453736396078819910608848037436750553189598773852860055121870087018329355833134868988888469587469126226711390600303444102108900544863750289572612060869551142518822071321525278451674736191828567495419257676656937822296454051943677535550229326164849481633805882250685341051805157221534030369014,
      23029994936544950173544028827707361717057876972901278686612422715466485613524110580012463049650193964002166474173960493023868831394789447579838395066946359129682313036451417833206538524846081127204158066035879081281489926046601029299003405927213295749625788592653618088999897129809303488733866551833087030584337403031359703620779367407840682213248030353484365437604752680483233674709822801531745174900764092306816346774934490994801364671869583358407096409941918620249573563734815930087453092582002552869922356200678965368163706370295277847282919525339746315054917249067896959668078933174166628400652326277647892976892875211749845532193217723600053256054432120760648466061394089031762351350638318647702224503340458624192422659194104269206883414843176681671008853346741132252581264927709448747051667533888320873781655927696753862896981725437257239728147037581660614645210065605971116130352611073474702895481424707095468129332403066756674613317869407425512348374249714712076349531734283101210101256693926765903537437037131126159897058430538583810606866656319559744256266831894308346710260263378498695432587384192010035306383746683064446594625465406975913313657184368608598874084530983997879315690787546045252020512359529132612318040690633530120193468195717992964565311433923655014680282816546484853866648400739982593266912224546977849341164994035181878937044043981901964154188415881053727154997246377440605865358388341821298300410963340718836594073669504,
      84983619080617666810893502373836107879592456764897104823879964598304535269300202603357973400274016165743025971419603358669830313699248586861916552221124881581885148861354996596600934067761676834430850788830333495670045626137844883785256019536040994663038288002392785079955957372127147293248349603122413006025844179367605860214014811068096727013914321485770961947368037358576808852405782005242453937730382772703502576828219026139281182434983581904315547015599609747666102997856921184045532992030649176208484232288185459045859233448430757586491302963260908731253231528207515918269986817248030368747524411311450320179865380437598183766326206763188575743190430090476912857086482378897797550728219785812233858653827492180362876233792278299313623448805849579607679088227342493237610510046794714431449413660762696336442546653295743441040936949009422769726627049227203401281789895126291108222501678040429700465821707784364348580071561733494180026294317727300403812230434727385656367402836568345466401510506742027297894468496705085605576301879400606999456611751467610450375170591111134569202294546187003407112684572968281029549418219427432353279389710514220130913606694444556340767037289259000071587012408947236975499439607452390172665249567419575604951579025531819196085327820306519241834905484975194635689135933427765806315371372208394144562213856266648023887316799267247328660581737447677539371966059658063829836230400019629515561550091531393715451515525915224324385996723901986333823131044510276629309776688950468856067932304139836659764022960840176000676415688419958423438216192207449339382625230957939769825067357791492718926015596489743384642208871695129627715920326224991997791573009619059083840280804190007820087651614098147746510520065975668305393675779438483583242111636461065196181556159744637912338142033174041287594581665716750328414999795330643852632725497885603527657516123236787109904074846926673968626832346465389239486246794781267041595785608797000438911168,
      246876907204714043513130440381675081018944597901257044495245799153761528523041263406328056675008296383109872741187492798106454911165896401696190354223306841549378206608538119424624216300839011131597105505643632416713028340263188232135650776847130345276276076712361651734917621579741809312694914393768290444198099013114006406247847512053676826822820567563670693327585186738114928711059964407437816216345295223709405280566820324258754691008206184685216895645419931565240741969107134508356905036608746697640445772596753172447931890079897123579253992540827816829100024846560001095382899260719789873421228206105298810809766470422781731679115684047896900440995976784794948856728391891496729942570713665365656861601955069002119824258261991097493684641401416528434122901736386315478718477762519848716823869681881274015882180713349888404069304362396687697999028281752910465532197986581586139219671987190103279569595216499172190746272780828948246325876861861747108433024706377268804114169938595176940546425994247890976926504086397926911265357172827665398322317110115837641541149615136314021541899324051893328908657025785657095344501829794964607406995128393491200835952391985364137038912884959953148716591122036343741725286035093308509614049261535137113964935506676724650846904305528859967542540498139733640896782324024420855981169232448210294442868800017011469807477595909179289440891837790274082957285476313768403255841294995027291629379199987529145386566102072182220221915809217537279738051637369137169769336133178955002953824593136864782182682681403333022920782478609602994595653175277469245261469320098805238494279802631578469710735695302631446515782417103509185266461510430981614547595392292108171003391400418820628181490112411788603101555398356471932295655464916550608483416619155201406330109084513775924540272643915090098414413841340232556906377355930193983201682108332792528092538011639538002483613121850151320641358424319254407314403255024125643007616257458138017309491284719535220349977421811094185951164899028834299051410022686345334273546915755783725245667280678787985106079656665849991757371839082993176620045555376031180065801722291854372235007960412248781929441304619426858084684392564347469716409954103801998198673092718406164039161305127155149730832208296133039406819559813333970274326998382897866208064252573721181525439188250820306129388246690930977570149032006955251990796165709184552251788380807567018270535848294880469708114978015664013764510694516003236035912412848963548777578932215380965152309207701003270148214268814921140646947968689953672079587046313417914054209074103536061638526369960611608428442924411031559257233699591184262189086062557893739821776458620765216563096719434031522296033272449999253861357379402950719917632200789996288564445235432826633082900922608869370438669155050380131778555244715380429252574904841760280179290080824590827589359175591207050731902476675093410056439734414662023755963888650155456646977911168346660281154863141315782592871242893340460286476473994962605210163237318722431689129192309656302606968638936390441834697762420703383704361236455833991607650315789512192664360938333073374116994443894659850031234850161249339075507804733478313661108085799022334586578452112033219473662409409967036251033317257185194767479214447159754577916240730348443260941177133881359288025718663600125099165182896655937432195934803239912997949653490563012324910581654497163054388158027473918456142516528713621982864589360938107125988957860040396856892412509773290334366633064951249535874719450104672476901241133138740012185983046704382549051639545624466275812294351886043972010018477306865037569125962395431687676022582463741286861835873882810716094697425111570802301026530491504025265405389008432264617643635104430366655874868034881163677161873312678795803235040172451193384345517145711359041032238113334936376958833289021985079778315088914462251669299410631069566682073353384374471638972938589764250119089007694209570063695017097386696573682627861893574591959035050167925732575852069609124406607351403911239428745091745622238418669949999019890925178465329863061993837059457243720814759140770921329689529261352376141901666203752800229135343480955114404056363686449584674667339132279034897432726672493914464247147877759819188273947182506489449592885398223772785575106907552476705160357360669663292071015181603302401657288834913372988282857223911696636408069801901745300216373988712443202632877244156720485301118177240453168482336336377794065356204755735586363578545966613645736463205068941563985976801870459356862799401465186336319389675956940671016619782197217509497765232510473874808250683392824977247229762696521026381741860255663821938229838205518794795612435914775514729832803988206876866966651489701417168967726026604702969947161692115499161476455299701476637659096368881791612422430628439414816885774424343528096065907730529106112735057681116637744749755237701970860803777298930746025285678420120641485778035048204808301336893499498175251764220670383617190545800485048540437368852319354756718443744527667694313204138002955385032259915357968200616342085356030814367236508264187383836763700015489275239543585777347710474182172874121139366228918571670492094828867022009712212978073908306380996096366874700582020622495607596774290950819025616348557363592267377958131088528627711107692021204081900125734270939225778731341778060362685956556923744890587614299419100332647219604683848629593265888463411481996852409555167253520150959970995203693965393783934399729491064164282940387789574847915072788035194671181454886856818227339655189960595832640473334030360692216294923298190398422,
      9530019691357477407839370629489626572207942009108250343445144257839133724758049635807369718713795974375280779159647831978680818693221178034507358079874936241120261574048604478183415750636146772428955569374820917103903708567460338608688249343094414617149118602605010221077981605705546929387605327196282055292011043399064073958615824939929272111406158255103027464172303083364135696202786283582448699758478667306505398628384127696980505179497248125065250061107326310890346528292003458144672780752687218328853356642208391172340147512234515802336671682567254603900589277019659546634423513085328293047304619056678450394448373036773770032054659088936785670940167163942476578974103656909443784223669115498792448646345620556472272807817051001893014100405868834597902874149975527628881905856810098531554026319250458176407647367222297125844167398636056648915734090171994196518166925046713115226416977670025451971223357783593570348456291103580380640335032723952181642351423001364715828725592948724193810450648567390918959477795358771908099057955859569100389580490337907205483698950628857838547369319716354329383792820530471330767744583073054776805074314501750824906592871247207038604759218999807821917843077782856342960519033173712207451812411851275308830726714953524147602098004000125500619114994765054658104768382560067035905956954522284538790709476607680732627494874043973941695726874787197259941452301145299375616759834278780743341229724368918001878597803794689869254732035753088438686894413280201735855870022759914439175974461053910914727424724495532517900267081489093547009869427654327125622641134239718267256008340089039030966392135476827266891826401105331837675407045756666793660191398641399204907582470182256840487621490488416487218033090041663971902108564761285143223565649334924733045882826736557009044408599568539204032562336119837652169050939548433639799893810043231191885342360834633471298808146933545196171642360571439760652779078834147955935590024168587282415556659280445034755347102923876437009139392508719570569398168759729821208115537849302052310496265493334862744583811096730250367617790611778945069921229200798161174515156092188135822407383432525856422334690388764650041859002378935315819277416300444624624607881216255467194574786992378471525045102330705178687759014738208433145232613222277436160750028573130126662696381849561042330625437689781924703665991349015410481282151953843064828383929947009527652586851598482841567796256801848150632358104193002904971624745669603501532079242191340872874457018087813385465639576935714047549431770234223662414975218633135226301133304353051331631651489646000923565058247755245922240496290809078982859325115917026839785032528027459342018306592984444043399324404611241207639484788877239903954089190543749450525185156696078356618371041914820730012134408020860344848699632854771845830449087210501155032441477450426468647868549125183858417252091985986290037317878697979896681139114067987557368500800773538871939105069353108072506297604504127532234118058565203328806667855949820334137238843513449715391179075253820094992212752676504685396301128867962123277761991097400688529120479081464389056497100091634615766899511520678134651714141370243837401514470437042812950423517555782600172898073839334635557899608754420996925019143860868550150930050925311865011963991382944063445027372977242624930056615529007385100002686276617044137297386424712899989205840221806279357291496570878002904692090101443097234192298365358773463860655940610023798919413181948362872544821157349300045040184105524817766767628462445177913792730035952049713103049297680574166981193770728934167395980508454455024427602773171846281138642237373542530917834257371649044953137035508808332379507653864529821681549962583743735299789285005494521832577055830872868185769979067030073067109738663417923770248273536285538296510325300671514959766191712925979420091199987347546648135127177967998845831355683102865250494673290526294849118098336302240207429055601291456577561015628434782193229544214100027596032079885709664314200643865604997283380003803051202377783605537859265477327325797913701814286690086098421746088689139879354390110180857589180372342846950626937250912601182138725123008807228777688446671152646182947850683091417007065382930751523471528852082329371810594686105749462109858047361053706642292352733821113913015491035297689253911179385251253114020251537218994725089209821881673489228841777197706551365972270816520896343904473946413320753678102841952921483412029618906309605233031323035491802502327549711513566462474674430595131479270059259923476968045318833466863559860872351753681169972059990145112842999515552133221674236223407979045379045000539990612426625190431559838112291052101180458645024307391795127566321429594579227289054300260344771037552392691774869698480200643454197588555973686511814927413766191203868535358587757137534511606952055529254475079289024017180493068176484519830292885364664203189248640724050872742508637766555451820650636399284009659317967843618839542129151874328166798661124720371870426361671872748818045023650417016623308880278464340780069702801230643060097951620966573381845508626863472715437146037965996617438918330661386821971107570685483388453874984183662587227548993853288100714371761128768675866261762845111604372964995402335406941336886186657546967655678021939037991674214991126966170379746292052978975302986275892501317316069756705245090892249456181567715726158873574370006531993751556042619698929952372819844426094635784310982866929072638693951268787311673349845960890908950535328584351028650129204804451979885059051077125074951572407504609137480385740128712733306690027240511098113116355242077354776820084343106737858502959507193526976875768766678340019978564701263266627804187576265046863581743749910985964953787593637923463767981172125959883583865480374513318140373850746341201798801227092032963891445818415487648962519039747731949291377845762665860852413362843860806302901244816268711065888625297093671096708304367944470830875053853840660612087688838887750719139217347187294879903587668380968321249321228333567127066771849] }

theorem back_tw1_30_0_0 : WinSet.allRangeT (back_tw1_30.backOK 0) (1024 * 0) 1024 = true := by
  decide +kernel

theorem back_tw1_30_0_1 : WinSet.allRangeT (back_tw1_30.backOK 0) (1024 * 1) 355 = true := by
  decide +kernel

theorem back_tw1_30_0 : Rule30EtherThree.allBelowT (back_tw1_30.backOK 0) (back_tw1_30.cnt 0) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 1) (r := 355) (by decide)
    (fun k hk =>
      match k, hk with
      | 0, _ => back_tw1_30_0_0
      | _ + 1, h => absurd h (by omega))
    back_tw1_30_0_1 i (by have h : i < 1379 := hi; omega)

theorem back_tw1_30_1_0 : WinSet.allRangeT (back_tw1_30.backOK 1) (1024 * 0) 1024 = true := by
  decide +kernel

theorem back_tw1_30_1_1 : WinSet.allRangeT (back_tw1_30.backOK 1) (1024 * 1) 755 = true := by
  decide +kernel

theorem back_tw1_30_1 : Rule30EtherThree.allBelowT (back_tw1_30.backOK 1) (back_tw1_30.cnt 1) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 1) (r := 755) (by decide)
    (fun k hk =>
      match k, hk with
      | 0, _ => back_tw1_30_1_0
      | _ + 1, h => absurd h (by omega))
    back_tw1_30_1_1 i (by have h : i < 1779 := hi; omega)

theorem back_tw1_30_2_0 : WinSet.allRangeT (back_tw1_30.backOK 2) (1024 * 0) 1024 = true := by
  decide +kernel

theorem back_tw1_30_2_1 : WinSet.allRangeT (back_tw1_30.backOK 2) (1024 * 1) 291 = true := by
  decide +kernel

theorem back_tw1_30_2 : Rule30EtherThree.allBelowT (back_tw1_30.backOK 2) (back_tw1_30.cnt 2) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 1) (r := 291) (by decide)
    (fun k hk =>
      match k, hk with
      | 0, _ => back_tw1_30_2_0
      | _ + 1, h => absurd h (by omega))
    back_tw1_30_2_1 i (by have h : i < 1315 := hi; omega)

theorem back_tw1_30_3_0 : WinSet.allRangeT (back_tw1_30.backOK 3) (1024 * 0) 1024 = true := by
  decide +kernel

theorem back_tw1_30_3_1 : WinSet.allRangeT (back_tw1_30.backOK 3) (1024 * 1) 199 = true := by
  decide +kernel

theorem back_tw1_30_3 : Rule30EtherThree.allBelowT (back_tw1_30.backOK 3) (back_tw1_30.cnt 3) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 1) (r := 199) (by decide)
    (fun k hk =>
      match k, hk with
      | 0, _ => back_tw1_30_3_0
      | _ + 1, h => absurd h (by omega))
    back_tw1_30_3_1 i (by have h : i < 1223 := hi; omega)

theorem back_tw1_30_4_0 : WinSet.allRangeT (back_tw1_30.backOK 4) (1024 * 0) 693 = true := by
  decide +kernel

theorem back_tw1_30_4 : Rule30EtherThree.allBelowT (back_tw1_30.backOK 4) (back_tw1_30.cnt 4) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 693) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_tw1_30_4_0 i (by have h : i < 693 := hi; omega)

theorem back_tw1_30_5_0 : WinSet.allRangeT (back_tw1_30.backOK 5) (1024 * 0) 520 = true := by
  decide +kernel

theorem back_tw1_30_5 : Rule30EtherThree.allBelowT (back_tw1_30.backOK 5) (back_tw1_30.cnt 5) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 520) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_tw1_30_5_0 i (by have h : i < 520 := hi; omega)

theorem back_tw1_30_6_0 : WinSet.allRangeT (back_tw1_30.backOK 6) (1024 * 0) 390 = true := by
  decide +kernel

theorem back_tw1_30_6 : Rule30EtherThree.allBelowT (back_tw1_30.backOK 6) (back_tw1_30.cnt 6) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 390) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_tw1_30_6_0 i (by have h : i < 390 := hi; omega)

theorem back_tw1_30_7_0 : WinSet.allRangeT (back_tw1_30.backOK 7) (1024 * 0) 246 = true := by
  decide +kernel

theorem back_tw1_30_7 : Rule30EtherThree.allBelowT (back_tw1_30.backOK 7) (back_tw1_30.cnt 7) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 246) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_tw1_30_7_0 i (by have h : i < 246 := hi; omega)

theorem back_tw1_30_8_0 : WinSet.allRangeT (back_tw1_30.backOK 8) (1024 * 0) 219 = true := by
  decide +kernel

theorem back_tw1_30_8 : Rule30EtherThree.allBelowT (back_tw1_30.backOK 8) (back_tw1_30.cnt 8) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 219) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_tw1_30_8_0 i (by have h : i < 219 := hi; omega)

theorem back_tw1_30_9_0 : WinSet.allRangeT (back_tw1_30.backOK 9) (1024 * 0) 297 = true := by
  decide +kernel

theorem back_tw1_30_9 : Rule30EtherThree.allBelowT (back_tw1_30.backOK 9) (back_tw1_30.cnt 9) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 297) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_tw1_30_9_0 i (by have h : i < 297 := hi; omega)

theorem back_tw1_30_10_0 : WinSet.allRangeT (back_tw1_30.backOK 10) (1024 * 0) 847 = true := by
  decide +kernel

theorem back_tw1_30_10 : Rule30EtherThree.allBelowT (back_tw1_30.backOK 10) (back_tw1_30.cnt 10) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 847) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_tw1_30_10_0 i (by have h : i < 847 := hi; omega)

theorem back_tw1_30_11_0 : WinSet.allRangeT (back_tw1_30.backOK 11) (1024 * 0) 917 = true := by
  decide +kernel

theorem back_tw1_30_11 : Rule30EtherThree.allBelowT (back_tw1_30.backOK 11) (back_tw1_30.cnt 11) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 917) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_tw1_30_11_0 i (by have h : i < 917 := hi; omega)

theorem back_tw1_30_check : back_tw1_30.check = true :=
  WinSet.check_of_labels _ (by decide) (by decide) fun l hl =>
    match l, hl with
    | 0, _ => back_tw1_30_0
    | 1, _ => back_tw1_30_1
    | 2, _ => back_tw1_30_2
    | 3, _ => back_tw1_30_3
    | 4, _ => back_tw1_30_4
    | 5, _ => back_tw1_30_5
    | 6, _ => back_tw1_30_6
    | 7, _ => back_tw1_30_7
    | 8, _ => back_tw1_30_8
    | 9, _ => back_tw1_30_9
    | 10, _ => back_tw1_30_10
    | 11, _ => back_tw1_30_11
    | _ + 12, h => absurd h (by show ¬ _ < 12; omega)

theorem back_tw1_30_holds : back_tw1_30.holds tw1_30 = true := by decide +kernel

/-- **Some finitely supported right half driven by `000101100111` never enters `tw1_30`.** -/
theorem tw1_30_not_absorption_back : ¬ tw1_30.Absorption :=
  not_absorption_back _ back_tw1_30 rfl (by decide) back_tw1_30_check back_tw1_30_holds 0 0 (by decide +kernel)

/-- The windows of 22 cells from which the trap `th0_18` can be reached, by label: 10,154 of the 54,525,952 nodes of the game. -/
def back_th0_18 : WinSet :=
  { b := [false, false, true, false, false, true, false, false, true, true, true, false, true], K := 22,
    sizes := [674, 744, 566, 578, 743, 1598, 1297, 1071, 987, 502, 563, 374, 457],
    rows := [469861659574289270395350591936049882329666628381233260455783376193756442596808873059550115846885556807832974131270163391814081022819246313946021919048383278259668859614912806319170421024513179947179045453479083309825986626881346512407478029548260343976601081460786553272309873931689037403124070705647981325062246853766830826976426084247895181413641903208707953033816445485911917374636329654279072509726350684741542250828787478934783034016273983385844458717734737044500526799607952459622308004739129472429576504963326650222270533120454566603938630837397575349726447877155341425450791685792400351155722873042815374359224417129101354879552604265541882760710609914986325878762432896974133487580370381509862569751994234186888591615507364415003172055666903135406737477606766103626791718297226584118235350034902412100120030056595635322654357668802355103084766688645333950827613768194912232696121726562645670696368827719136550181559274085307596016318037885680288282262299181820593802538581496196726728690863475468272503659056036591184800514808187354761930885130393102894972738695474896789240992902674001137648088158280733844718340051542139684543601756847488812391161759588313223794274269699750617755651363886186832691037735489203469900706522781380778833937268913307697016315938290592469788099629522955406254803928439871448476927591934054078495839487926957346415368972230670146187093851123855634588481664146366191765336166637679856634518134107124866625355934221895225470597470290208321736879877175411118541055244492451664001701773712127280149115667192753039165608302352495764575044202936616921631487165329989196192513565207122735593730098598137347780564173794873263749522761863504818412284927272197721512054840545818470758009085675930013215820109505437808131579231657342067867920996730234741832429207850657000496442030235061508069405881382008738231041159203548353921233419407052315227894455418939746328077020341401269531185596650873978748366665349794527413488891877506128416737781820227207948315727835733260100645591752609824100896108629671113278893507784454844639687504382473964017047395428421445484416401410700448414345905106466317300920365581744953919970203628676272163279924935050598610937774530617448568343957274846308680429145140372932697022449050475349420225037808995688538325361951851074695367443180891199756390285067759396508035807826514089964396134135754155765958788711252785917422952530566131231934976993311719510843352052157744739053497692904589451692794801099785107547100897030745696541982866838113105372606460214079093438347726464112085032010817713924716958854512954139542403308303601692444804553609279655844475877598784232117995953764094530233280782238000890161705651787348380494049757979234790741754485949963606607872793304653516087767854142668885423777559918202618565200333175655545621973506004002473853270756452051947260738268240752704678900714781244882009270893288644764123723239738168907036834000493969349906167625909341365486854935105231892672082793911890650022900173451585252849922307672941508868005048681133016700933725906679869415894688623838863459313804135420022107348203304643186760018028194418638434340414641856182083866033690292568797493446163147379457541768825508977492367633380535895099816305556489399723633774177426444795868177358393697587338900826618384314154565445599148034748639890490555491081512857125166767951857594174600261532985986817279072521789302458921936472150694949451752795282894711659629769413805442839800346523803096241252554582617806557633405403267957560230362370444433250450095367352528865325852869799344942557135829297044198634810608567353295508340049388428574740523047207858073384076253782559592308573381879653156880474896246822465002290821760399681646418535100202247901597219765328878598536808629062860829331144817851825910087180538182614609417172207219922115019465652673472047375283590084017266569053505731206085784272794164936803325164988949966634951252761904590525400343178273416541101034431677482388333778116222678131397427426655019802513811924777518829877287415358155993826707253147086051037133050261910357965384885488279192580100982891746944637360335769265983873077388970062938149200114183169389505081979602330843664296171021442960173490389225391930316282971884349713488583610785870788767438110729653538388641398099952763507088815222629194526435997052688942739639600777034583761990064437961755019736661276223222028663808706053997805415899246183961397641309134520359762651426696660542755523445109343653514849336430241,
      18134276732649672909433714664180854194084960161836693056383294971728677118299657055925063295234048945879860493525952391840061146421226408621359779865258342065341093115307808955453121728082882752083963199713234681334793695016706920617214594066420606689099078843991480062927838273331378203383307479995355548782254346230397757487175961105109124483111469787755038231860515847722923089891540329961898858684611402094428446122079530040367295581503840322036248929171842215577924909950391516790710971794984842423754844638210770882169925642137011867360054206464284746405140619972368380781102502346668298013202675280991125541212109600495635403346253322534203279084078911100845102135518927795843058888688224815825257352239361964302977948588961273612718285739600676184101018750502934337299637967350732220091544215712749436305122099953799003406572620221594639618238981742846591517610758640024718010825430479465189741168910741832116131432671806978468586368657784352057903310798885428825475663137694169433372417978207032913900202671715386604653558410151485605197103598941361654618232848449674624771710332232919856841218815537264590849404597614524751202655055839073438094820410437716163174028993945150896632380916752259907114977726895812594295044076575671966631958559265151606807920148118924088803811329377092609403792431265715336743175311888701627440210148164810059324346840247660855897575632002663931483489271308928072943997359351342803407019188690923541006719584990973489771993512706449024952507344903964337673798817329286628036980429628708596363111647400722639235553798311874260009408283837253253956761361663863986142277924387758134383465786588282663684803933782381881548299971112214980434095920614457083143578317089998488683208226952782723296278968119129001534085992402987536723179025111900881026579598019971479766007910089413520073071605246441528889992321161026715869064978149173224792609094936939399287833273024383342423906878873484575252012937937501686175150868594420482460327551382836526727648318527602366625942036405550729756445603020896741615137473603494138781379311017766724587458184926095528103175237939833824459994526755195197822873287997594978954139375436299081487043417008157213513091433569865882472139848305149617342823501132827443728882483858017259904689026210522912140573776647737011713442254313662419295767985325015470338526485626065881546713871261441561377021990226444240012430580230444932223895388645511597152339779594639771347230760418243531448303397710106562943802140252214430608921390452149199778690009985169049847342185409662719097509466090237994468461693529704630122184052159120303942200357684794021786716304434826060372552533436945016734064940688974515395425125523628675720562303012536794564033989279084209696939453734744845132099729721036873585555619604235269990971997761466965095427485392413731556741192870614765803529664148514928081437927997218060729961933962976606966639103668267434880840526997368744353229478429300072993582525105796238837405671929086429221655987580640449425687805777267168916218079552004325706505948462019206925081799891068287497417195292755637281993395222678447434263581064157966492841807695874107666901027901485727359971548590860008887772243828564574966441492478174133201841156451685928718140243960958194942690892386655212915762828899351896290449520188895611017124174660621405228915788193699156026720931222900955051424613158203886948770986916093612421924911273314717804949580183290833269455493160787255304268385193879299818956430096129645486237030732940736725060242707379038542237872902087199858144945620831252460744548870369085432616338619851898086214058461224398566804167053319864239116417578754528529096562300141690782626074360271431145236064570726579169403332114233021824948505656013290034899651677042045944736957658581545399197312607380550336122575805058561624938283115808959903441586756265020064163549764916330449744149760162907571365782044753188413923314194708999876572612330421850848845504182851031236757227272805186252226690206536908845143273735004761019103355779203985030655085147477214127895165254185643528830329236416047120431324327976781438876768721487391132577595991070466902866793503587328170515958863572615265893969416628212305997597117629858582394606247615888238984376952244625098594633662361483831882283337943812333953896538492521805367833523583037443507293899846324642496627619691404070403745678119738577644629140359416699784520320886039287168697322739470324848709372069455696771557522851703983959731971560630121867824169059431824732199905407863900170755885344113613000075847473407903527119597231426764928870668188010108348324247845537843487721713261493840238624035908778388428126084521307564894091610539211322566696480579912861465480918523260363011160695883197541316158571303097108101682038772594573797933185289300871564712294613370256314792106031249187750012573947121428985726201702091431456083853755784189537129573160473989836977212381349047003896465877709064396332867154,
      26584907860607742922526784217328320307382994024096506268902688958426061406519667987207462099519825762249026110552474834007406542185987529343960139461775068751104255940950236022377921348493091397249658848167223173086815183334923727449800992348974682429924370497405938761512322967948670208549330466979605339533134374797203737102267510934892475861065586360797652919383364281689251402076738334388462338044210114187782674568341579618686528586413691456438865943086289390765378760709085703747378617181234744874219335490467157495526950923124013925926189965633712779715173491615418489858232196018963378214358716957720387698716827655715005287878763408792561253879967818345110008537228014167048948149372315023213791356403211264889330711691076289888975459700736764295200756690511313800631713123855319965441627547746475313942827980061205979525456429784210002517817750600393084784183599147872804661579193133355904067140824428451380218430971801708290889791653489002188275506871029685296056704062705674832094071880898086952496866904422496953609050616165282871119454782626618703974384562447908679206123892203541400467523699584303622377221100629571393629346852073577860590186555189765529107713701884348487674589905032962610399972397731407388069074225441179653192584995825243099574279279522846140085969558371035209635217617157079932859385009176521789397941645576934427657946076430106042956920987694146268351526644138572629573855282824548406651904177724309240326119275262383676562045990184638930563977803503503643263226485581285746148491762346500585572342042547290014640523425581873875150701526482802278526648100938869439142635043773041938279558275842372099166330851140492255168330789227584505045556165352935997721279356083254063875789805449673984893188344756164383800117430502344286224331471466963799841740804020501277955008417378441436864146818353579210908411144547354207711637103510583550108250035203395580928098142704260869987180690426237862783165868962941800687368880127899762256724277570978003038112382949164320643956442940193489779184706600154617715447277726186354672932071415081374538819220978611770952263837058209231659388757730024013033488829185404215761812177174088563789439988981851043858723440582854858117694060962494144934981594457304686882648653622423935289690918475253643498777608354939488650093449890483773240096606231529761595140211245379149368985366665978729688418444086540289086375994271338633608705755835137034414686583045709730560869046979438862552950637265040010269053275173917220879868005856404798943280022925509153306636717454811151868409794035489870617902364016139689915591815556742256291328812428781274183436349999673085974766894080360277782324654693608103506283615153779383794547294514018342243252647732932499820187302895162436591539476345031261289798977630403283209108228968170045258963234671447346713306063538806702080226060801202489213291466754149671280400598552694598608149228118805106929905387173493664517245509782628186244181207211440852076232105232110521523307523809009388327022632388257596697436977898310589715930877325530375264249995465208353662531291204570809274266994065748387349634082479425631614465292701154938130084661823563529671704059981698638029948732115348887706103625998820660813642780666848420793716716723035997725306177235849275762974866956936268907095730514735042852433199091161321666752728330320613574451306007912969924762182541045820897962830886500416666054982108746281288009053947869999046141185258536370925818228897291162199008550834518407975440474749076179474633392432536051749512239632062745211938072356688297806245162904497035201279024448812590981408167528333438573953917094054750155891022591075096476293262183549033971520538980659520523055538184917407359450745637232359671184844304572569495043799852793737520095,
      788879547930344494260392936018303532654030462432061543480871572285510609451122340031920169801997306726729206676718803411638060673151188828520977343194104906302737564981436664291566529093345674118577078768897416719989971609937705528980477194151326851664217854400721118963619053343127048126696982523909914410832611985432068278466998424100938213500019644815093612233712213766269280955865140067557780402439206076405747426804906343283719518700491052223105750871803147808432160492318515746924813162747934999955475142454737850264602976603954382285944591169917526682240410114377420522728221077738101927048492945069712927217722934100365194665431094005143854126685775491967509379446583290519711556227754290752924538450368847534167996213844135585326290765563599258110755557767991748050877369047915486930982067836075079173684076693359999809706276832382215605853309413213762876017019812984962062119666776594588836359633021318769166117478302690212224645092175960027096138074485292652883233478424842756049168222730536360887686907643053762071915057834933674127688992670016357345384082808803281605479738439936348542260163110101851709946813209682483593177887631589574406560699797474907339705479719897782214247535628855233811266068277349835646099563183096588204929230833525843470160194283500143788045191528468882372485047676874066028741135215222363260129648289798124510988542483674925988698654541021729003795953636897356781007777857169442357789502168999754802957287673641288197376695336749148257050803812686120603050732925156769554440985339069811336398171281312789426494839207915452286150004548435218825132688589184504297611953685846654040940551656007120807778582870249196696752804460737954894366139406244090474697522565434807756928464851969689225214034613969756844019038522302056948611804584489190954169303711311333664295887731806336693556540708206055727785218829163153208700749374923120097343797648323413214504887717403065881094681616019184645218974087889196751155915834999433941528574884749108926526797424483004434231707369530354343905046005734509130003707327897497823945316139749723193165373541385614588449182674126680609034469733745222325209108098191888941585184766504678853364613963001301499439339731470130682459959626253965644511142563272211438033223883572309452037601547929491348409855461736045351299971081116998329782322960117961362469963967791205115140859472626393095336909001265444885916162702014031426632020438761116816204130877578837289539294944388312528841089641393733567607456650398032041296644363522512125222517492245173612331580114651441532395282427060416660324322173459317988648489711661760849924167077512078776342270540412509009384662406992237691218612273654618786773905641422943082506019187647418876726979382369709144033255886932098614819919255864128996745682012494093843922010526289070658165854901119845738410888504187116495057842317432595343829935549912660149422877990619597801363215539413976339151020160887458744667797753324962030663141558931775756527036424480280006724872282531210627850492578960169375093417481584866958184926951884426850675988478694188868775424088352095204034844610248159433467422907965276589326391884058938075647642631592479517821708338121569790524947920187029310834522959395751628552980404776300634356264635142541599665391872344305923128756651789311626237138348921489462431397428155618935046405479675230345557413922090176175000292326881499578036459625835780135845157843130759123312757624500961980783504629579551729944850977522075993589409943717076769088429504823641620040845962217710536726260649917734184896737923685316465042874294296828656478711773858162136736655248167775371028549957889806624622660911424455075387378455078345592500635038794474513539244816818139581415028119187713727337452438978995619155050735338247566659535286093682807265180409275965683038984581035999700786409207214815907996537719713,
      4327694778571791553590355605261768646958868581048951870509991154159147260782169358218174851315761948800844249079444407669994027737575809079991732004266099051761987529670115780085597915958629651019137805136959434107526694911937271035250752487296961705025447677243952866986286417723372469678567580978957727670119637013242674277259276098672425256398241602398639181735681590328060630789390898610572003854412507936440817438576802851538184292115708245865005730276238754870565818333797656571480375472864397303908012049216511080354501601490074845930694818281991559241324211876343138400892857967286774005031095831221772825215971583775582453139175265762520272195110616730932009729878848002364317068434485906922965080934160005970001814008699929350484503706294361749321473490826115588243237909323987920367503287753255752693598809467590377298259782199543121343343899901861731634136757796369241370704882020278347411459103989332800224736803893449021980736069187014386037055583862198612729520059534887446948128373119291077176933122805363158357669891844160143044268003563823379925688906635182402045831949233057916324062896192547430747210031518739178169282854914416702538792174264072186438451898567139667855838838561279297571470591550668092519070827923631307204755498309864104430873472581988808853646497774842279761958032215632925696172204804566004341977918416553205183662138965384173030117378371846357065276912918817750962774966334989616416625791153697274925841154546623559687698137495896928124922905290729130732518802221164023923167304084210258659782077365856492616676007783058875638359751994099691358163376954995637068706248892945277973563854821043734800428762567099994332323508280782767720201949563201308238344346747155206429882692089550168424647147679921772249195313943694791122842647133536267904232638299539933503761121332497052969667168478190048642241525867033544039109363203095863688618472356959284922860846505202319365242753550791316488116839734666575164289362418962353013669650849467812510120539111751649649565106299033573291447015941560459617474299776668510196395915179342353548957919979236346148176523784688688509769389684186954997416898275929557530743526316538896883307387479022545670148153488506772413364437357698269365796804325527979514974527073906622108752556424735343596241367322149066233639172937596306791791765701128336841884324883478417669953175596860446199686823279463630638288280330874934579158929878537848035823966207748149579174230355671965911777452083722124291287503977248299663799508860937250437308048458439063324988126435427115892063428806392369747401034581894576060837363055290072161743414926990292462574212613743736109867964717606707792428355128437742954434486041029832302612598906820960438449640482992916348445369372110674439103923792239621065926121685072931509263556926361640454998013072382947632467015495932091960985971795183685198131844267167115129056849355882913294165822922251043210631700576755793308509435677513353995106630946221201640284144445866609323024671643948252842885933227607653385590576625236484610629356183752543945529107249050329301996437166140220452553494386075203358732377381218123607205233124736821019758012460555700692141468507775117016673440204946663009489319952003265891148677424136085805263948716793242688213865471816694207694579739593997511797038991582617925761227380231291300707004890697513899260648540961297905823140688814122419013477710238429998472579865058975676684553263943749885116231420404881078909919784405623563864519157187077966995060489226210324874248850705744301064585733448498512819130664661542311052121098143676293779390272428981383623881088434810869741442151397581841525989443038902596523831436282024055386974534552661669268138388373647084898976065662963541151042516826578931608612252983454331424532303913017063860834902733351411207093207060285149726755597726001340878419642470081779888552546043021607290105789697029308800751813851186242305258013490591494933294528995167363693885609988544905172375252351081134243236241749297605770227327644146597908332324912015020725942365370522470185854254960637335898752075946474664633250690225624302966855958085864864679903397892149386960409720584920283678076875579080814258625806105340209624334440560211573107578729216501876680860332199419675723873828813130116538040327339608739474080605986041187849635795080316874912979246955362018400374895133309157201421892010727600017577037136299973119602693118811458108096492151262695996496631930042659775204287554055095789252705786702982333598394159949320090951681216615787403496185025573358331690007349250804372095065365119554048143342353233606024797238659024424159752536285743194300489776419098008033524775973686087963520084169380326158536814714675420740234183563860311473320648316935194329729259424079459655221939099268284417418597954659099336138378135857019031603517524785327691048336487647538903875068433294390249322113748640864985052253763270364435255930731573688244593606244059947473075,
      102435286711755612110213629749017357235685528652136096121881508195129211955814644336805403611730364447536676162980665305076847166058483918253655159755351818144580366900238296354071768116998643994980515879578217159307201752315964744666004671857838735050341797578303977483345142558275832176511072536360926967086146063010133135658497886323065594872445596981514588257702421055372557270068762467569221099080096719656481351228534127624190170926035616975758042493708360036875362736941335231850829752619535590020248299865782738461234846246083944606504757821526614598225515996038579912525204379874049287458542749105678910366836420723610307469336272761857985891726922387153359613094728558810070392054180766099232934690177666135947938933835624140486912370005844509211400141880906156373017976548993759069581229462801654461580374042734159948707573756196014643836605250186514249941186077791572921629775971094769366421763059868874637293479189501727117531794583896050678655466868408671691123262740313457704199834059529730412334080371714945201926467300985525913801212977747528846873299512332294896754163935872607295157418252858764862957081836358070426868267374267666390488980301235916988477843329158917140606635406406693982264742957040301094249778226892949216626537729673825378496195327380303958507128725317514667974744540768302846426898984927999690346357470273666153732924291084126186002198498918163808067266874399531147423145012755018905115358865991798815033019164407213959454195464272724227685178851447475737403138495674023992510721451667428633017801666067915625720728530317752410288476867771827539952007494935707477355944369223814018513325664418302558480622445860494237389873063480076293472065127968071815216257839870958099131485385621878099678457151525797862249880120277822521359864264600637956759316012085965208394099133320670216807173952119115439988677473966083762933693104214896359986352648584741122363973071924894893170009919697808086046364452173793888204096676226176902457793046701804936070319682282917638364712052359046519752439563933648222044816991021776571643980215512381564052375490684991489203955265291442455572076241261061500669620374859808575824171525264840589092055731205391068133090250992465963790270667704640244710940224652912088305961097034294667998268473656509832817511959333879420587981940881474576673456276981498482890914865984360668930775556166998765631993456207136204733049342530224407742587799792980745013691656395314540450955180683955809188681696959298631928523157902918662686549031906922499334017484661407992805492265850177468849553177418707877020780452888392615616016082251936246366287052880872298374350687783736344576466380144258686541226361100427441191504232801487286899015751045519259967821429116771731419057455120570191531743484977500920460932774648888812937060760297659965250019342265522784526920980998736313631710666556722130464230494484341266705807996508573578716548181699790520438206418783528865399003317055824929200485768143343603514401415403792156355169032901261928940225826196303687766862941690952635082714448443335350499290577402516102867110740007674496904228408962959021876861096968171821149713488557191950446411053474108732902977449349273563860631166302532298132638568619728251411015427838813299943952644073429726321698806755624780632589286444669113956994804947334576554361526678001084421066852359901688058386553767232003788603366755135186534658875726487554208209742073211705894892178951724631008948115201297952277161492582742368859148142310649605242612055025269170062043871254022710180221676900713161149853868059363661250144235189833687399698118518998061500700057044480916907748295341015177753856810102537100407310994210902382291134342655596531813981661014010287837067881288537317207374871478886510840785968936134337151281767595929900296584320926343916689561257885130729994459807239304643930868274694831948092544390740489869176411555419349534371327463440600573348414816094528058801814708062261062795456805255965945150590705591700816800987647416926498798007352564291943903939404543805783660834714982518679386965918637709514685078350562882703456575841057329816642683193599648302578967091761679975856258071462236706515419510074304066014190838080402750855417838487249262493268520746525335648566218255196247411369375869565965927555266167795700062123439639401276393079361007198133145935011194766227758258410906599616489122129766747542275505451439784545386727781737635517301954847615213300049965695155353904856536720255186001335082458308463321679448029404318429955952137880342857653397644004130485555288213230811609403828055998664982214077767920064439870682543876427076869966609330107631213000440359191991945272479934220897463344336088129019687381408363435724001249343539533351651802590100178498296325093797224298093893656256901064218506629904302080050430570962489951339987512437799659625757693651638302767454643121743016218711500619136981054914855781197206394648394743876195259191275016397067994424235637196987143495286519369291116903009749677219720024290904564998772344276791235384130803788812535838595626967987444758159554349803298464547973240620889010446520989481857792124716423463846806870596146059382793702692738077852537436364828646652084920272374631205054467736765659826834403237886786716963290164612953057610553613500941012782960430767084125927319244993135766032817800816208279910850435768022539458146594598069972615785956563436583621690539753188716689280950556014823310019785569649888563193621405194283257476812622946220078292340920056456895486374143332814398062765380443513995470035761074928529841591755939485076750074826665382387135004403674043681208450187035934326706551871444567300376540011170898900326987017379435335431676965508760555890649836487390145656953744567593715735645250437416980790244110299833551103806367188562681104543396980268462626982954733167286638464786418917545157043821738197676741536359152177928494263706038261517668724168909623220889300144941951087643413164538202903829857765841982067546166691683641411761255673233656111145876770300987932092032629711991142686711586684549348372603774486370120154986993480404355782117754401297838983314662485801315732778797834740502721394835188133800452431275974548849718030723737590511726883614024181070412726782890460530901065339614874167904045371883311625670889266402470226458561054452073336604332829098885667456975291403840367761061747522433194178196215750464793800364923319190149736961741148396803947582094960221969266179143182587902938539942476345308706125274236762243012264318894992642486588491630750901522515245084920439165761399502981094001334980112613563509528806371156718017449042358382318690600072498293840554003651901265573698176027591024952182570827766348292326522720321765467712030736145341053568791690806332507773369680308519646266785702444038104475331328925691408373176144135086626112287377935985696841200767855304396145675327632424656783320033352165712298460643744988394589940157100149892827772974126031466314316785553349943440642204477373543067370029077846615881688712684657549500420973180134433066119405764433475934619659857878839285004155798866196870309614321068406573642468005042941929939249301342007644090752750817350508145617910692205091036597302640366977680502624416284853276092157258271262511194299924060558747780173773330350529873946904266341873590402891945209797365185492304398003900347185883949311992365491254046572494339376731319683157894965757403404368448194231626641334396004176534354159089153961363066204100398997293796227215671670571096453222091951128118066543950939541680820521715271622357798149815731718098266847581083124225629907367596425217798963270356591539321348681831533619781171278435373115131965033782430681601207346034796387921297248365697690901777054978717316897349581234681984235356297954718224307351678083486218956203282930123230627678708210518074558606217400817871816649001213120358630884543427057203498559226501656650663379853586348928757298760761729679744976984705121665155278055795539063190109589889603767276892781384582489546170286217764816862061720753496596003246494323716834008218035278264908811871089155494772767961470328091655795807516155276952943216214141829687509490649121381124989032987933590802404093770501923264564789347198932862583503051201298788217372145121650956760424717513621364399355607284575279908979785133486057736862649442139004227326328138812625242338305606781584387696027197719674616392174091495433528851108235114414397565492785287370145165875528868204804913201829665967617005109241489586510526111562219115304349114577906488061108123846349444579666806262542860596073443336036336474999331178757135770179099148339703887757581399338949365512218734404891903568179240909928828060570413384740039853069836231065596872660360695092038818173785235951144430162677863828847199215758336226560647008148958831408453974876191638306355568529830599865783519232370234409648607960672476172080044776015109119297784938912262547352298837051576622882060703940121343023845094309653244357166052683593133307007935081010600178373710382550034463714664431032429444594054524058151797305923240494218297341314041380967343007813049401915402123019521946518391524262381430817335081882645022106257251168015660425921665875065341228056342465021215149115493719213979510869232441310736434818130386756849627692757845332492241616058693109642647844316760529246896289874545195724508551205332849999639229502009549425051978877869355935431752083082488189454922666714845315734454037154026818077598780297947508818871740196626688174192526257204822537841536623789042146745824064047511386630493563684268392196705880534759087735756686575138023876042348417390638679646840007199782928525041795414602882211915649162548663344046318568744785114215521051821730852018235748517958966496964294601531568662404465001798467572526326609082579056759860713537609097486727254848355414854386252138907064374374854859113038777114467087888376499670940970938405791350514155564474155701124442470392022367180001777858442022892462289676449492303733516113845753007514642668880477545306569128050599522038355829548855651272715208218827182780644403123823545851715736412900199129353016816042352797962488937734104579704657209957677346188237441624211310905575056445158498587231452443480546193792028742103845066981576286298977680619309403295346871144454507327494594613619378318395540033318373246335373746348161728351062656439352525000018278129556544469029804596149620200496258333772403623927001486482279686255656966654491779773455776428480550719285960213218062212168090823932733631610147548266580437844901063428769049298573134945175594636726751884271911266655439495796266577887816725498504727426075187776324366,
      3887691833113176629876620738924043242895026930130893206626942975098035156335428802618235570605724342018688639484971411598849020860625538181908612099026211398862344196658578170146359724736660096968046507788383663404229017758862986452218621499577639238235414825087088968715965910350625894328743227165932122494640312095039708710940481634050927571751134397198333838627813259930977441778315208678920561178596998808982647312283946507834484558238589372368988090291367099485811004699838726173360422443448698048853985229504239280641643541872816073300660277296946126831522711212991711586357186634304151326274201539860122217923299005553257309733742467401923462658939229378336679630477119784471745528469164686400889133129175146412768464155921238574285289453941516667977608436689897247070598602049929669059863890905427196265049700054778866298075142130273100788676266101157752622909048652160845019645329157347851416963569249241895521978620634388939503212846947846719947955382071398243038012027395539951480691087256833726393705141382631251368407502737113275173603660915315727983578239453541087065863915203415947727271373539038084854033559771148099615301875832006842355004966483922952046079871906748568227285908963927760072332987292273074567960321191041794041623196530357253096174809378328816703937680228945058297932404897191173274467304626083045404152111821965620718070980472941838300095937919670284126668055348005877069080231441602753807108498811562441902918156595386891567587529990630678706199106557734931238292955782907662705460543735539159202214997773826070484119473400539700353336187212267105677925495401954795249931016153968525122968191070179618344779281479960494008872944432484621588526278265089221302425654842580678414691321444865617254161421858409967317818293557043396245570775538362206544242368592033464898837239251189547147946543346980426709626620514331887822707031143389737462557361271062470099156632970994256192175784512346857987821532400023655693674362144211427464781441292667933916879301155566685379622487808446112663171233395663104950292103078643677153693440423599994254281186996418704618891612835035950905430051343265162513598187234466327954503711077765506840614733914874334333194774374738726908632128553367236608510493188605732718865809271787471209554715558701075392928894067530071438110883730351078076333703319332727107929972277317711121959536903954776023440133239420600568366650991979111689221919792147935442159435460353937889147394934024976258375475149919588797001647246269036290883401791025464061257194787635309183339942903477121871420940231420458567258890451458808792331622177760976707253922461652758546681570322886303275433203838768325075368813902701947264801319625394800760527181785999095034761242424690573686481080750461751822979944226325826119898839217339053984079495705116198798558077242061980117786970341639003238268957406310576352207505052345637730139574441730034347343717998150566123702792278116086625305484279806521626323890040188441473366214713343653456232994155763864112209794260189331618786078513735608268493814489682911295552591956770854958630606205413697671989062800977219350822613809296355981826446397176612482225665738649555656619944927968842733184307747414689234635866131685756705300320301562246610297966011083872938493950246511249844825107381444360469736004815206394545585289358044990622731710361361781102191107119715944148535578161523851241086313996577430165711997820086476129637026349583216370118243303204943147091118399819899763308995574703591773947728936530095696009568019009001200392696588782024806839607889251813805609453177992682362908883231500491278822525761812278799395910758618611144403599701149097660340988739229169338026533813164409213922370104983059363762237860319005521717590109266533664606052181691396394999454183496778192684158923638573049658300121362239814404808930288213529117886142710126166138847860577527427239653561080916228631545709003409660445145005353462245948632942218760522434600118075552167451263119030655578823776572135124397956235066956353707670756722529985641255800506944215033381187794180284278194935807519071983512174448497942085860807259207766089569334385396511851814707829022522830698172283812205648330585516113651638649430562201063807008848668950160473904219283710708759266066334415756673464346447479009385113792389759145287970962068423157496944100421947626994482122300271962500090636976307037734216458025369700402602378106295085236002294291069094338669312394826412631284024302149760754773107169049125435906797374503858535421428467921005371991441310657559848915875966162010431794989259128425104876186701991446667485240044329072849386163588262428772609819949709101389109175421152439534106466715798960431390663908608603809644119878740488631200532398367946014456696421623963066280768577604419720555063180304773437030644588397272915190649236993955135009991491776583033487369617262845148020984095087214483984251814211786357199829982391835228216811733264125654207979911435302701940354722447585314575456245946740863221265944383048156511875090681162006393551662120013887067232810802868846175963994916830102941246866632025424687395400238454579690457502380452230856573104829383666325430237204672544068975056508614450883410336573506849741977657755400110993417522819703098316358341917272846042025550016587757264276670715747973459014855385177171306368723742965215074798709604805703139585062161603813980397375675402685532351521826202303013894230144690926308366409504917669428124609911039164387240450791986923211227675976742838348438628900959332741768273891262247660308992929002939674876922382894791288495695456563584674022566558511322471898217754767036516396588786395715390903545825615267689025233713844054174015472834728700847917190424572440233502552980497667886733112721729646726881515571948585550948382540180040572222399425947772272250568433205788508600674379085018078624561773311005103060727766253303306076729885663889758010115866541725687206160237038757050757565420395952782992852844192477114959923742210448549408345219317893666816311146650355262679983324988850308050785747088784098864781569776314325925376653629565249651445013405749122593811918112987079606885373179929453229681862782039220078870373755320736013567016659452857866603694183257526577218833678839275213588029074141192055921308915213007610574968478607895381611801220298665295503736447194782203645089851549176192366485391947018519339935976411870032161377453146220168952095760751004816629855377901711926113223635302348722344205836772431868240701383544918182510172897490913672980538872024609189024792450997224828203481350098444190353620735196308412117643513110876764385772802974047091469761036875566139419163646257776780047833642638906779157218774025967892226563494282248146354796077828590721723630971924027794263738479383069545379280661894627243262769166003333852951410824464588872371229389065676859402395328642978652702756350447196785752905579436583380115733890044240623591723295896002110157772515957417807727060903109180458604560510140930028678027315090805585221695771948333470343050405727039781711790757774346292900818295429957583156394429593660514984267641600899696931288816018955318101145936824460257545223943231621409414278977318339486413590865980856307574975975051813548500125921611304461761903197917702528448619931369981361563998317890675445345511812267653914524295807533735681856532751272733342347756870250662056743824908437486396348502842385528914265416602280560561958147026494131491042182112233341218408422253692669080837704027811660122530160220339686515486838730690110816588749049764991926997825484580256886685781407143689668432799882704453722837266762859779855716496881006904655584173544984173922070689305118838211663596511308929367427854728851894934658432437848574123353605556111337268786148869345956869094759049571051117794189668790582969850279047786078884843432105296875745030356817480829246809893794937812911654484913384033276650007526238703724233775097685034793143791223688917056269254375527019087460980110860417666906792957644166070693135918642566640494845385686150331841819737201547187084147191664431205922027048635798710258988242671602864133643896732057224933440829312639700537445741228367070236622844718284802144240903006232215196117702326982629706432040388781668092061077385042204042786375982861286649442494001297388090201612499381581675121618486633679956122875526178304853061641485611868985711864155453315068135921542360860462695904965759387041232032716269519236368180224489931402301373608928506022998180982398099742741836245225217465069432492375266368624524501930283379229396575291931468913719168431673138231257238092069275215573748614713441056857261458,
      7386966969427105654856127944566262791632243622520575449058213351972939353877873539742550064034541158155317423815366238083261285638826753380199648548641966969095314933643094366889185034149887799725752591438197648108297218005053330535617848653705080566952059448922090834764382332249554102608339443160101499167573092014651772778625148029241157130288888524037955152662415679369395291362843397826747517804860773267520277961294611935144209469223121584960119357303530492890749653566750168397534991287450350941365055363921156945352586398527810298839166867145527787990856964165229917519184905127741876136776236052260331459756439090698685667728989154058550346385471014429065358986785103600918095077536769925260147916308540159306042268961355841172005635609237773693317456976767383805254993750273222838103631104076165947567727731285164924461917608423740350905086567941418067832641112264426315064202975369243616643711110579451554958065600822613135177345527991403109262261054653463458793006035221863726130692577866915246499949589052436649479880595013023929330588271569271553763293212769441000358577877576342700515698834342338452866988155259218787888313340701287814103798693282397076544510215451131187891197390738729179748959703694577827490540165092730499993441040371024431378563454713488268357090652175958151768488647722406084847266107427642127442445899181945824439269142945515332953984987925555836495010387927945655590596317594879320407608492925393058583579101488452387047834281457602661168163209951092889694459706363188532238842478075419392913735106845454947948753519971663726465011911002375561769354314331498017948969745828779413083254540745721996091868489625239274975230172376725035084079004120948632910473731542450934782232398509129689108504377344947140075530609149807084715056185073625692546208518200068799043001283307275183914982945775681794607021038761311427702819934261125475130975927550358518727732715978692870060436470293236101600564009065997211544943249619627358124164980901293396371497292377134403283521628398211796497984628026749006956380581230691897853053977749771581947187611680900167091361179758260629023848828150215050872617309382867883802148407942737104373558199619883600363963349945847551182913766415052494396910457780518040188216342059709858375806436347876883410156696754036480280820393647063447445498307925656189361891892671186884788226243744365384332901060489938629355511041909425368077565372615518334783599252237273380108936003654768487636344329404077777067850131204113250713723040404340094798833438129546817494297375781431546863463369251741593785178472463820029992411887055928211172855094203508956201435472015286697687946194201099975376340444393740500293807076701285855865367969808675788489969904596169923541564319696918288313726181533705822607408217201691936115327356580567101518466398973616583002396872162372396342349604839144606316813660323842328918837082682730607179616534594455103264238782689590492880977129971493753482555642345672131152533985828306608629223464504488995774413405876691896767308390031727130908819645790474387402770082325993268789789431012106579448079178386256025449184064448949488680259875832481349952407449850893976330528737405413116832607909464117886842321554078425187527927142259685410548477487751623176002096364262209052957294725283351469668057944516510113031408231405312153380972416376525032740671643465926889335495733698693409949970262773839438186066933359837329698783789361889170174240782418889611969068853452688104495036307514684897352386207751968167118807787088141267307520241705127829612987540943007867784456773814092255221255521038468969313264008782808235112891133020446733176238599818554914405166052123511982090672187923780871647161920806196822492113940277479198179392780261222033378903643528860841292760322912691013377761550712347329509747809069224690938340090200293058927685426698909933693176566448425738110064446197413840645267472093431989248102703161333164982027810064607632930170929948861514132815257498136758887051899029783503692009750188168477599119761626514812921850262907955060355196374660986049378949742252894637276690820925006207115842637375585156375533325386459048987546183501872717835426953061034785621139833711316405703578917723347515086926943925132115542191111064753631625915259206434159451428520818787652246146965547791493116033343578768513390896652988103444980227324130335464632003483778583574027074804738085175213807086516451093386297081515870804739469304249397178196306739968131040440068121850802166177208641835907063628969605545614240218872835242011740115560051549745678704963457987901191381413143327040622462892547709199058069719142449238196486021179043317425447516208752368854370984192987616934521689452041564279745385962937560376253114709935458364046202389183241272879129416723035352495337620121885342394476133063923457499162026441222624436563819894233351425543530333507471157346682613887306107076196465253028750000320961092945138042976851878788469158863825123357212155237751027293657408147177950091457531587924481102172082265642050385965832017330610112873593642276647271596538604153584488429556426773737783670539939774768671729008269078902909052333295742583989903759165818051003197016986707145535676463047913368941234999161579599551422464535965511725779484980716734077121181649923663617687994157025648727564714238816757506794858523961383048560356489610692197692949271903509378390626287125265974219409965339438534357822463906642576625050464661485467299640327830788611145728026707524720299338489430295023546988360037427790867060980369895346767801872804200601676970370539039208826706470195597861272372457130095081467190206477759225220767318561635380961278521298199514485907014008965506011202077745633637240484128190370265014689018039738354461534419447027218705156357933564047256253914408253271549381786208748828908789013641177409700748260697777661321147531651979475740579003071015568991207519698417002526811292301103060432461783990900201785401694019500002776062173892470292395903033794128993884828974292364806246021068760801528361522592235183863483214042999817087457352255587515965204498865828786726399085589742869945319197512521874058326120257155238480475319249258260913322732096257002850701541152877843626582673245885894824447240606763125738735220499289893082885654106434179919363367986467430557531644216535785021415458486341747066020072603468580485523303661083163666868814740114054496112920739308863042915676135841454716585758172755865630500198740788849670620112943688993845126771951939583806217379639446084484725104756717209754331623653022184910538184269151936599365730622534402100836992603831554293251374910492938472179587517146509622521686551355792303659273984852846757408737841529476910923701007939900925680521799994152018046965305938566670853463099359907998621377642112273062522326363602536646181976925575067166616951275337969429203566605280813958579804976621402208100141008624129647434704168753841925058566887418837996283384760228141284083427773476802551782765966711158006713259531567821300145696065306106499696805334245020168818108438010021713275884759081361007925030470459388678563082299920860878891359080649546792996,
      366856823877249828514142554790835215505676435140592533687350822790412841990791854030616492614107430693023742960223688114776939073071018374878657458979810559106338260774593832638828492032222159938096011912179296239840684132113931149864745520316417488459810940760772731817381204984148310453774596424167514902519437516637276283896676191922435171384691643053708236520859411979775878919589709431111566330581820740626240914348981448183081274119506815113460588653165150576410815294319270077075682276003869909034897803818137936304592790065056421502901005515479467252046756424986683382531330515024052852978329962238228925118675716967719657854871721557382107476419799640534467955697002218021702980442379833452376894708859111102445664608287200080798362692161482444843258593722521427322048332213596528438248559922544813264788083474662323107585099522282220293651704326909035340709266372522051021185389751989580783901502627922991012525986134521821119019094013053763327037462231453004036736172031035472517152371130412502030109433196781427013208498056670288950221799018741584156761573642091869433877947908892061595187040477832634177921704515317668417913100460983944825783336511878051867633526245495878100106184812217570351313403882678519897187383759238447241017476426730992720078929596455645039219920441476180271434678253721913044013394840784367563933115280702046433822891019027185840077900788661387498577462579711308489234214042472730692913818230158728238284507036826268694353579062955447621590607230469588764566180512637133266398520221753129906974554667225256630810468619083077492058521431595341134271605031913594699630233779695506526010161048687946210789432080294048940570807899036520128426125385244840833250727902803594156156312528343510181935938246367264783354100636351666672027617930333380843252387776703390152405307244934945564589282728140851067064851552082383867440691090897978189265615611284772780486902306861588076668286011547734815240643622025016497050669817500868295996903327441888048535080367848254520509769893595760871406840812491671956245433455860636050010915729045918744413618502343436162004941875517206340377422460481987103455907171770899231149360010137376391760832473766104138151882780552131176777352299414335651327838666263272633367995085255290889179320596534413435862753220477140529638839140154817560666313466683420294083560803280767537678473051677752461914469547315409536637195703231945139450087343366754634501034194531913154543369912127245415005021004796682966360949051763163478422825998068187885995298277287018244468674746059576806611472504118706698992549185179123992538023666797193963920310971922341543179352136959130086699899479604027111347737081005472804595502053521750814449219552072984902615187913314579272481700070452418603582783115699236005818720111684538629072014121328911774930939200298029107156936405347620414095868159862912751148697929235906058660344937245506460469716775721440992943490368765183131538551422337488002097762831066921495299478574197500654762978634605058803192281526959811585583274557742617856252196396279365472340846628809186086259814221410578220905711586280929692757292579009651796170763981393508085925640976024778698176127972113589594082101491321451557105498096813969203901825612337290232536389666103240776771560550793641305630504013526066982036043448599567195142592997380311367538410521762931771490439046424509163272115647280993240628837159545392831755178165852233970238135503196801224790773679914366276508315561332586773419026526719663411721212653658332940005637417106579755818799212860061511128357466095952882988413382698426565846826624703380539049240582076127761569353136818105680768306163508137803880519507991328295175433969454894264457291457687888271684242526580884872882469185908540497391190665141520697394387247414172427857748833293248266570472144488877139910631985623868030499318401103232236920237245983178870518178608554194948864316710578997928870033711757879582622249921303783628689865295082758234385792569468500983862181855574103042761814631361544382702903823307765951209676994363641171224625031954208227637638042222630567988570504907845690918133148843962088239160150520755099902095059459217327083059010866221357640489684738508934994436259863822413899254741474758638782192868523107198847012570530773884736083820424828929586460004140494780754966922426901447561699340533681830399571609346782685899477901814680127091392831868887972151520769997232976156021308122124486788844373764370820175379660644003950692159039408203104132951119976948609083026196726663177758644719008813906855237218064349017211977997617423873279494545475077412764152946994309366786026206431392334619873786942036356955512704709209247146644824503522880926538308663509819284987273752630638596531239710998454638691925877073343470451678575607966242767613287861182660595882764618260936373453760343721404464963167904663620753507163603739809162043430759460326591784760866254347334169929681024616154173699237715251808036556618940852378680259905141914949349488816352052599873416996604762687289560440852427709108719925275180834868851794922776617302892614271417603713486300356942335490044740403372280043012884989205034529044931085570537355065706683602802337794835138728431916084866790820916669509949494575964203824627460645860073840163627910864698929330620783933360110831433758131800181368626243050815527465971800199737471340837666852347693449834543721151840535946476492436137971455067494529503984314303583253137129718236914613558433232953177961673337046731637246722234533044052667403529231086266347572983011579751314518899391446130110384082734948097717339692742509042562504892302813025609196799131865764694549698356276832049547692674931178382221341334428159866927898173862747760235087810789673522817552830754660078841213617964024927480080739478897445393202622148810666795989823855868935722307580990235018001158616656329549973327853137574408712109625078129757619259705278719025775688619888801575266880212030405976652676737097171697365393136936847913156827215568200552334305740057077440194414756178377637390161457223409129343311558655643408626857377806238535225044956278495409114504917994252871956644015674162222285375151608710925079200669029430756121933027128868308015650239635528891318704501194058147195765234960708502095599683209296348759374937998643766226406552235414586753439840921527583546746134595790693545703808807527607825198970805567906565398121782322010989750701666813498281473425400779830494174301057423307682638888070290424489927814392955877241023378535288483468319843392401121504102398480924606372839934498896240221135836929,
      3750058869825628143422252120389958525761635242940232892235595477425170100734396334191308586190717726928644370263368575388895561124410398107021548666739365135319736865229264630582380837423866207255505126388115781087959267354279242264215075731484991686661076973541129214114477998008146168055726651859773799808573477821173272154925356379791845327423717947192741998798257757522261657549918600465393110877355156523833425272522071944162715557388786571506044917161631675283245291562807525280131380674113768988953086968213697414111515938911522444367765934097284410399259219256129279731279600963993655481583614538140687548456715355630113614094998557751262776643133893637411149899493622720922469355813778367333308153227578770793072384775807965573212309420039616695713812848577395325864447439478782411558406901722176336715481294508724674264462297178107081049792614793539153678473392870663684118088084847015769051037559274281868932474052925151898109314335079323514502184397713825136867867082010618912688123719130290242476526095861114702051351689958526501973811509406515499434822794116933492058402246767798014302302082673087872217186256671356035356568108467323572706093514982795026062309311798567100696253005619593351813555028598756523045813310087006101881129905751819040758935862716231065584965259251861834491977498332819080133634623392083917811873362375611980079936611586575089774525116358341801827903036767173208116280423748947777222051358464384565143944570297102900023669822084124278221130641452472714737680093665573048669992396645867747843768306336539168710845506041215175441287081802705140325849575439934180685695837348338746940704225102308625530433315685884822538656641356317380882302531331817754430020061874141447823500193681244215877333944801990192425560018252962911591653765326470160130584094313607058068578302777352721744187949913438883994998817755883639192290590445843132709171756907303799232462368575582276532953091860271108734906150441706651410172249584178507244505028260356230020576241169479375791795827570383727764785269501546311507488826436431840570850753522753476142497316761511759869064059970017292313928669956674564062950145971025417821285107113929427989435672722038879100526932129770019801808943367369852973400762491383547591552060683022831540373175019497967589680956992854819213265576574639257139515947234100950802503782650662613790551908117948677859032402164666197443749394551530950228278584019888267726742006775897032915019161225205558612813153300625906513754336325177624147140127970523231546574376240478310222104063892163010538665292602249533006433390150827474324592045102532911018756128185847778256308297715720981188682359459719694351448642206278791967543587281861069408758442455329081118985934707507091130642557222615652167346965246291001103976836443027362505852846594337418954638855167990257385886323280226484030428151719934415905537354581277919148897561830092712605264631216366774209669243340443973264475429158333848304108043060648614156742275882432992862142659286024064128037236135777036679023851180542396884506811748900832722668065306082189014402545415519729637531624374935638369717248293337813203605121083231454468837630546037347036556147799438787497185793503187736298379013807740124696737341499426336304865850384589966571163655486518240895123107062667561015281798447075162562288083638643300244024236975038,
      360446842329603525251510519648759723803778957185704541603496886490991309516506662981893063154564277913680974210749159788023234928537489540026358144458580750085897501314375983030864961562641228686065415789871504607429000522401208876176702284529801189253922084785696483050265575437215627648347589702497761287755019361556020673193366541080677495109980939206879901866637317454202845888887433154158331261113763123121810061181051147775875984285593979540043741497650412285307488467351731546294045379413631755392034167683369008526416573591653165300064890309976756429989826707836861707162302137692579059572639428657910508884391101511457362400221025127894281865079190534872446554269251121426740388108839943877274609958467639125764685617898917147744662960981280602308061544469677262373561599443944833009227408619898676519043831789611739523632177205239381783403517094911491945509526102885333206286501027850074445845509571244847257338940623076855373836773587663546801747542276922789393520321186432242636409779159459906297138020247746058481533426916591907431953369225711413096462215374489260778875923193099002242037022966038257664014826042483526924256846967337788278335879680847470766119961214209845814269749887055181749532093303772102929472182910966045915612713881220610903677826500133732146128363497213675735941722592074875957999232522444716027811543891129370590479511854828808838280444351331906292745391089358993464198355355486808311557018254019363707693183054259274153581552308951025529355171887081624878453770206112160985230094399745264974749648777242934885265719046093231488501789214022077309269412075674345789204952654248039357341040357133407653358501297820652589608951486875691516389460875045872990266878697011448700507799409468494223603836731879637975030845826159456931610693556436427917815299256880430569935526699088366712393084595235293358331341532213149467389993910427005935894316363136848747594599392691873543173947502095596246730725423297248037365639541895419836303868467212522154772517225751763647120782411156190409278943322900976958360641437432097159453209650592147501174194036215904927181487941688862335303024594974101693812557166501681028567676162999140592052476585814407409650436760435443550520935541657762712489589774075157036722540952472807907877502143326639145376845312333085289569480378242883982693365554101233789965306004776167588837996047434099221450837280508705439929278224974352607422444822464322917755676532531902928791449608144841530952566075160879323548571488095608578298497967672574508090933748519442859768055370576811593493286529792692762322125166482609667167967606824634609793428520872844531917177411522691279098944668249348650083033444912831002353057548475237915497174025362081020496561596771980974014849085609381660417238658044850319309675056162413973185964403885447177412366043089285300347894112790875683773476299320253346687040225885023335655555773091074091032447958330658336501556948456040043032419105990984319584045085176237560477438979653917969667501148391415747582060327941974737768410416563353333104598222973275300572361592212552040694253057059799154388783102048126953848082441578746277189093142417002963380910602218489527176180120705996457780263052677314331709728670923533677699023192705128044829467964505479487405996017838488533643317631675505387871580034636553605697915479126960861780164443790988347850769617323875270204510923830254880065244508853207662954556948275662033481597788757409385798911801858988750020577772746751079135593703146589730207862138654960989857698546768866275495489644913421023263782292190959909586126614640633466430427458815596142464579362227759966701814974866132211408322182197651219519802090713020003395200499176389692155671433198634747546709345228907679971069512919491289179,
      74837461374796020874275271510987995407717621474059523152713877132462769253969347045275208638334544826497566378503500920119195631728908999433534162917728678858575596238660412082362394828374213689834163928625200609020345058771435343234843100228484478956426460828869847718329470118044870163093741694258114907481507715024830321213748355801121071335887372709451177723994772033543163161651755751109748470909217699437294511015818807970433258532579321558495644246849118427384858460007555199607733819366795472966737812710147447762462854405513871466690515647990006401307225197453741720963807355273234284526448508717887942566772003799987101453509799466542419764283924522194801187454008417725780954550917837952008826143890888139739729830105560345595478082608017666598331116564173616433740288802251600556394326359130361897753260833025346257879641547771578563250856376951278534018805720871843429819934402855268802312722046095770493493272356168229222914108441924846572779022712921904849659800990195114019429417983343602402661267260136925257487201374971080657624089350793704971974439455965115000504191944697816645592176680406683233063130743263915570991090821026017850473097988625373759651910451463207182529228239867072233124055713100971979979644363492342085531988380834691838252034494373908981221210134997264486249690018366166288690848149157242635879175654418477870485547508049170153533190489592544377042242181828527914513530044336987255218778321736550487593199966245389730625625963223812949108017217054085673615080701781473026988086634701905154962119791796636355186912024312430304284804750398807975738365674820913963477220134077706531928050160760696981827343516884902652457004640317225791089325979024159333688894697990932670402412613272709683436430631886840433189671647985383422982839381821368688975716721743045293170292919778201102140208664369228765031732661822217749628145555162120731833916905513674642102417605465249906738686951140992552551448585086475765666031989266379062887701198850660282347099515341818127050671454971466927058235312046497597475582549203496754746563659389459436209265376889558398838532078614870677401391720637581646757335173047554945031014512766686832589678001172213112980172595402640325153733384456648779959211054805356106622897076027805500823879498030011393451922133051623758501672848254597444454791771027228369686400679756561862011515287679944909690042523396285683297131260024994395805380238540686334151887107493957163873345532337260609614321495721227673600201331014,
      358302850827930243874871686967940901178896680303106414754619117057163174405584226388101555083300430331763464566196725558740419036018990685482287667637425232136097331469112728347494687531332616366354873152675201409505797562189230684519795845465816750571652451768307380945821873921960053494696675877149095123799664660150812258612754569532556776810476036675591633478150683872939633188291568435753125774413809173015784387684406536139666137702492356261181680469636865355806477964248649146676484780189800322388301543239913710770641021193095945808991813657481717398332670940546810949329342307131229339027955343144097276925055701639703762659201771211585982394287407224579168515382251935801472134874834255821239894649939481317674461921852263873043401262888689488444422135240493428013876946418957084810961354391061129163799784486329018336033582887284997885407973954106899542765434363005061332120245765414353921458078358386617299671983880399302967672979719460027521618584049738216215280722945575648444553041033034470453811890889795991390627276517241461878093993973162710861889703913810750320680912327229873164180128220578702592243406090952657982828021794445754095647680767623281593022009319310975058413474709515138506140024158740379088288109030006191046722898555705347261083964745330363353008780378716141577063331323354563380250236011351969681537507556270261991606915794722979034082325843202300172925424915423818509762390014203581131368998637132633722739979794370593617079864382891204257108344148359276744416641342161069556086189471066371263210865410716226013853946362246003294909465716611239734548359991523999581275966136069209049789079204462629448303413516351273315346570029756227313696337287434568055020676909712337781708127853665364787768094465892076021826215311242900541372822272704120479193000790022765007223310779375745768403202371738295160045421283429226984416198486082718028459017056049449579372105071220148066172926338856538471327059329343748458815611054320269276930003115985642498818443679048608096729398719600643588898553369981514947849263523518841603555426821051971811410884620200479150696394776052174080106578576202603869985912088274568111728195450426573651489742027910886024388050336404946753204832921249590351281380081652086209787054375028722477005619959722373306620537719424555268601549802615876139792314325964827143310651179761384078022549069025844824689278745172632697165629712326647931363916974667793200279068304321325885682544194117810559264615307947033931193962748172358106591912744144818360917559501348303028368849179171527874275541858111946368917128207766624498064632746256996813246431083757988133487675485246756926722035019514287342198291196530506621300060233476667157181567985538930134564817137203407387918662969918766336608949966008992111195894287022259660456342408006159222132243845957615709662852817859692091076581674290487552924549650291801842060537301386122888197450996654481148319744743494197434554921431711773838829367321187936805575534738748836820349465354555066300681892346147998983364739451761725547456] }

theorem back_th0_18_0_0 : WinSet.allRangeT (back_th0_18.backOK 0) (1024 * 0) 674 = true := by
  decide +kernel

theorem back_th0_18_0 : Rule30EtherThree.allBelowT (back_th0_18.backOK 0) (back_th0_18.cnt 0) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 674) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_th0_18_0_0 i (by have h : i < 674 := hi; omega)

theorem back_th0_18_1_0 : WinSet.allRangeT (back_th0_18.backOK 1) (1024 * 0) 744 = true := by
  decide +kernel

theorem back_th0_18_1 : Rule30EtherThree.allBelowT (back_th0_18.backOK 1) (back_th0_18.cnt 1) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 744) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_th0_18_1_0 i (by have h : i < 744 := hi; omega)

theorem back_th0_18_2_0 : WinSet.allRangeT (back_th0_18.backOK 2) (1024 * 0) 566 = true := by
  decide +kernel

theorem back_th0_18_2 : Rule30EtherThree.allBelowT (back_th0_18.backOK 2) (back_th0_18.cnt 2) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 566) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_th0_18_2_0 i (by have h : i < 566 := hi; omega)

theorem back_th0_18_3_0 : WinSet.allRangeT (back_th0_18.backOK 3) (1024 * 0) 578 = true := by
  decide +kernel

theorem back_th0_18_3 : Rule30EtherThree.allBelowT (back_th0_18.backOK 3) (back_th0_18.cnt 3) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 578) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_th0_18_3_0 i (by have h : i < 578 := hi; omega)

theorem back_th0_18_4_0 : WinSet.allRangeT (back_th0_18.backOK 4) (1024 * 0) 743 = true := by
  decide +kernel

theorem back_th0_18_4 : Rule30EtherThree.allBelowT (back_th0_18.backOK 4) (back_th0_18.cnt 4) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 743) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_th0_18_4_0 i (by have h : i < 743 := hi; omega)

theorem back_th0_18_5_0 : WinSet.allRangeT (back_th0_18.backOK 5) (1024 * 0) 1024 = true := by
  decide +kernel

theorem back_th0_18_5_1 : WinSet.allRangeT (back_th0_18.backOK 5) (1024 * 1) 574 = true := by
  decide +kernel

theorem back_th0_18_5 : Rule30EtherThree.allBelowT (back_th0_18.backOK 5) (back_th0_18.cnt 5) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 1) (r := 574) (by decide)
    (fun k hk =>
      match k, hk with
      | 0, _ => back_th0_18_5_0
      | _ + 1, h => absurd h (by omega))
    back_th0_18_5_1 i (by have h : i < 1598 := hi; omega)

theorem back_th0_18_6_0 : WinSet.allRangeT (back_th0_18.backOK 6) (1024 * 0) 1024 = true := by
  decide +kernel

theorem back_th0_18_6_1 : WinSet.allRangeT (back_th0_18.backOK 6) (1024 * 1) 273 = true := by
  decide +kernel

theorem back_th0_18_6 : Rule30EtherThree.allBelowT (back_th0_18.backOK 6) (back_th0_18.cnt 6) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 1) (r := 273) (by decide)
    (fun k hk =>
      match k, hk with
      | 0, _ => back_th0_18_6_0
      | _ + 1, h => absurd h (by omega))
    back_th0_18_6_1 i (by have h : i < 1297 := hi; omega)

theorem back_th0_18_7_0 : WinSet.allRangeT (back_th0_18.backOK 7) (1024 * 0) 1024 = true := by
  decide +kernel

theorem back_th0_18_7_1 : WinSet.allRangeT (back_th0_18.backOK 7) (1024 * 1) 47 = true := by
  decide +kernel

theorem back_th0_18_7 : Rule30EtherThree.allBelowT (back_th0_18.backOK 7) (back_th0_18.cnt 7) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 1) (r := 47) (by decide)
    (fun k hk =>
      match k, hk with
      | 0, _ => back_th0_18_7_0
      | _ + 1, h => absurd h (by omega))
    back_th0_18_7_1 i (by have h : i < 1071 := hi; omega)

theorem back_th0_18_8_0 : WinSet.allRangeT (back_th0_18.backOK 8) (1024 * 0) 987 = true := by
  decide +kernel

theorem back_th0_18_8 : Rule30EtherThree.allBelowT (back_th0_18.backOK 8) (back_th0_18.cnt 8) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 987) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_th0_18_8_0 i (by have h : i < 987 := hi; omega)

theorem back_th0_18_9_0 : WinSet.allRangeT (back_th0_18.backOK 9) (1024 * 0) 502 = true := by
  decide +kernel

theorem back_th0_18_9 : Rule30EtherThree.allBelowT (back_th0_18.backOK 9) (back_th0_18.cnt 9) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 502) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_th0_18_9_0 i (by have h : i < 502 := hi; omega)

theorem back_th0_18_10_0 : WinSet.allRangeT (back_th0_18.backOK 10) (1024 * 0) 563 = true := by
  decide +kernel

theorem back_th0_18_10 : Rule30EtherThree.allBelowT (back_th0_18.backOK 10) (back_th0_18.cnt 10) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 563) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_th0_18_10_0 i (by have h : i < 563 := hi; omega)

theorem back_th0_18_11_0 : WinSet.allRangeT (back_th0_18.backOK 11) (1024 * 0) 374 = true := by
  decide +kernel

theorem back_th0_18_11 : Rule30EtherThree.allBelowT (back_th0_18.backOK 11) (back_th0_18.cnt 11) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 374) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_th0_18_11_0 i (by have h : i < 374 := hi; omega)

theorem back_th0_18_12_0 : WinSet.allRangeT (back_th0_18.backOK 12) (1024 * 0) 457 = true := by
  decide +kernel

theorem back_th0_18_12 : Rule30EtherThree.allBelowT (back_th0_18.backOK 12) (back_th0_18.cnt 12) = true :=
  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover (c := 1024) (q := 0) (r := 457) (by decide)
    (fun k hk =>
      match k, hk with
      | _ + 0, h => absurd h (by omega))
    back_th0_18_12_0 i (by have h : i < 457 := hi; omega)

theorem back_th0_18_check : back_th0_18.check = true :=
  WinSet.check_of_labels _ (by decide) (by decide) fun l hl =>
    match l, hl with
    | 0, _ => back_th0_18_0
    | 1, _ => back_th0_18_1
    | 2, _ => back_th0_18_2
    | 3, _ => back_th0_18_3
    | 4, _ => back_th0_18_4
    | 5, _ => back_th0_18_5
    | 6, _ => back_th0_18_6
    | 7, _ => back_th0_18_7
    | 8, _ => back_th0_18_8
    | 9, _ => back_th0_18_9
    | 10, _ => back_th0_18_10
    | 11, _ => back_th0_18_11
    | 12, _ => back_th0_18_12
    | _ + 13, h => absurd h (by show ¬ _ < 13; omega)

theorem back_th0_18_holds : back_th0_18.holds th0_18 = true := by decide +kernel

/-- **Some finitely supported right half driven by `0010010011101` never enters `th0_18`.** -/
theorem th0_18_not_absorption_back : ¬ th0_18.Absorption :=
  not_absorption_back _ back_th0_18 rfl (by decide) back_th0_18_check back_th0_18_holds 0 0 (by decide +kernel)

end Rule30Open
