module

public import Rule30Open.Columns.MissedTraps

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

end Rule30Open
