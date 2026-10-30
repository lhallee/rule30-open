module

public import Rule30Open.Columns.BitGame
public import Ruliology.CellularAutomata.Rule30Ether
public import Ruliology.CellularAutomata.Rule30FiniteMaskedJen

/-!
# One word in a column beside the window forces the period-four lock

Let the center column repeat `w`, one of `0001`, `0011`, `0111`, from time `T`. A window is columns `1, …, K` as a
number, column `j + 1` at bit `j`; one step of it needs the center and column `K + 1`. The kit's ether-and-wall family
fits in the window at depth `k` when `k + 13 ≤ K`, and the least such widths are `16`, `14` and `13`. Once the row is
in the family, masked Jen gives a contradiction (`family_contra`). Here one fixed sequence of values of column `K + 1`
brings every window, started at any phase, into the family, so column `K + 1` never reads it after time `T`.

* **All windows at once** (`sinit`, `sstep`, `srun`, `srun_spec`). Slice `j` is one number holding column `j + 1` of
  all `4 · 2^K` windows: the window that was `r` at start phase `p` is bit `p · 2^K + r`. One step of every window is
  Rule 30 on the slices, with the center and column `K + 1` as masks.
* **Entry** (`code`, `matchS`, `trapHit`, `lockCheck`, `trapHit_spec`). Each of the kit's 109 wall states, after the
  ether columns, is one window of the family; `trapHit` marks the windows that end equal to one of them at the matching
  phase, and `lockCheck` asks that it mark them all.
* `lockWord_column`: in the orbit of a row with a leftmost 1, if the center repeats `w` from `T` and `lockCheck`
  holds, column `K + 1` does not read the sequence from any time `t₀ ≥ T`. `lock_0001`, `lock_0011`, `lock_0111` and
  `center_lock_0001`, `center_lock_0011`, `center_lock_0111` for the three words, in columns 17, 15 and 14, with
  sequences of 1,193, 955 and 381 values.

The natural-language argument is `LockWord.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

open Ruliology.CellularAutomata
open Rule30Ether
open Rule30StripCertificates (seg)

/-- `evolve` is the kit's `evol`. -/
theorem evolve_eq_evol (init : Int → Bool) : ∀ t, evolve init t = Rule30Realization.evol init t
  | 0 => funext fun _ => rfl
  | t + 1 => funext fun x => by
    show rule30 (evolve init t (x - 1)) (evolve init t x) (evolve init t (x + 1)) =
      Rule30Jen.rule (Rule30Realization.evol init t (x - 1)) (Rule30Realization.evol init t x)
        (Rule30Realization.evol init t (x + 1))
    rw [evolve_eq_evol init t]
    rfl

/-- **Entry excludes the word**, for a row with a leftmost 1: if the center repeats `w` from `T`, aligned with the
ether column `j0` shifted by `s`, and at a time `t1 ≥ T` columns `1, …, k` carry the ether and columns
`k + 1, …, k + 13` a wall state, contradiction. The kit's `ether_wall_trap`, for every such row. -/
theorem family_contra (init : Int → Bool) (m : Int) (hm : init m = true) (hz : ∀ x : Int, x < m → init x = false)
    (w : List Bool) (j0 s k T t1 : Nat) (hal : aligned w j0 s = true) (hk : (j0 + k) % 7 = 2)
    (hT : ∀ t, T ≤ t → evolve init t 0 = wordAt w (t - T)) (ht1 : T ≤ t1)
    (hE : ∀ p : Nat, 1 ≤ p → p ≤ k → evolve init t1 (p : Int) = ether (j0 + p) (t1 - T + s))
    (hW : ((t1 - T + s) % 4, rowOf (fun t p => evolve init t (p : Int)) t1 k 13) ∈ wallStates) : False := by
  have hF : IsR30 (fun t p => evolve init t (p : Int)) := by
    intro t p
    show rule30 (evolve init t (((p + 1 : Nat) : Int) - 1)) (evolve init t ((p + 1 : Nat) : Int))
        (evolve init t (((p + 1 : Nat) : Int) + 1)) =
      Rule30Jen.rule (evolve init t (p : Int)) (evolve init t ((p + 1 : Nat) : Int)) (evolve init t ((p + 2 : Nat) : Int))
    rw [show ((p + 1 : Nat) : Int) - 1 = (p : Int) by omega, show ((p + 1 : Nat) : Int) + 1 = ((p + 2 : Nat) : Int) by omega]
    rfl
  have hph : ∀ t, T ≤ t → (t + (s + 3 * T)) % 4 = (t - T + s) % 4 := by intro t ht; omega
  have h0 : ∀ t, T ≤ t → evolve init t 0 = ether j0 (t - T + s) := fun t ht => by
    rw [hT t ht, ← aligned_spec hal (t - T)]
  have inv := trap_invariant hF j0 (s + 3 * T) k t1 hk
    (fun t ht => by
      show evolve init t ((0 : Nat) : Int) = _
      rw [show ((0 : Nat) : Int) = 0 by rfl, h0 t (by omega)]
      exact ether_congr rfl (hph t (by omega)).symm)
    (fun p hp1 hpk => by
      show evolve init t1 (p : Int) = _
      rw [hE p hp1 hpk]
      exact ether_congr rfl (hph t1 ht1).symm)
    (by rw [hph t1 ht1]; exact hW)
  -- column 1 at the white times of the center is the ether column `j0 + 1`
  have key : ∀ t, t1 ≤ t → evolve init t 0 = false → evolve init t 1 = ether (j0 + 1) (t + (s + 3 * T)) := by
    intro t ht hw
    obtain ⟨hE', hW'⟩ := inv (t - t1)
    rw [show t1 + (t - t1) = t by omega] at hE' hW'
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · subst hk0
      have hw2 : ether 2 ((t + (s + 3 * T)) % 4) = false := by
        have e : evolve init t ((0 : Nat) : Int) = ether (j0 + 0) (t + (s + 3 * T)) := hE' 0 (Nat.le_refl 0)
        rw [show ((0 : Nat) : Int) = 0 by rfl, hw] at e
        rw [e]; exact ether_congr (by omega) (by omega)
      have hhead := (wall_facts hW').1 hw2
      rw [rowOf_head] at hhead
      have e1 : evolve init t ((0 + 1 : Nat) : Int) = ether 3 ((t + (s + 3 * T)) % 4) := hhead
      rw [show ((0 + 1 : Nat) : Int) = 1 by rfl] at e1
      rw [e1]; exact ether_congr (by omega) (by omega)
    · exact hE' 1 hk0
  have hev := evolve_eq_evol init
  refine Rule30FiniteMaskedJen.masked_jen hm hz 0 (T := t1) (P := 4) (by decide) ?_ ?_
  · intro t ht
    rw [← hev, ← hev, h0 (t + 4) (by omega), h0 t (by omega)]
    exact ether_congr rfl (by omega)
  · intro t ht hw
    rw [← hev] at hw
    have hw4 : evolve init (t + 4) 0 = false := by
      rw [h0 (t + 4) (by omega), ← hw, h0 t (by omega)]
      exact ether_congr rfl (by omega)
    rw [← hev, ← hev, show (0 : Int) + 1 = 1 by rfl, key (t + 4) (by omega) hw4, key t ht hw]
    exact ether_congr rfl (by omega)

namespace LockWord

/-! ### Masks -/

/-- `2 ^ n - 1`: the first `n` bits. -/
def ones (n : Nat) : Nat := Nat.sub (Nat.pow 2 n) 1

theorem ones_testBit (n g : Nat) : (ones n).testBit g = decide (g < n) := by
  show (2 ^ n - 1).testBit g = _
  rw [Nat.testBit_two_pow_sub_one]

/-- The blocks `p < n` of `B` bits for which `f p` holds, all ones. -/
def sel (B : Nat) (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => Nat.lor (sel B f n) (cond (f n) (Nat.shiftLeft (ones B) (Nat.mul n B)) 0)

theorem sel_testBit (B : Nat) (f : Nat → Bool) (hB : 0 < B) :
    ∀ n g, (sel B f n).testBit g = (decide (g < n * B) && f (g / B)) := by
  intro n
  induction n with
  | zero => intro g; simp [sel]
  | succ n ih =>
    intro g
    show (sel B f n ||| cond (f n) (ones B <<< (n * B)) 0).testBit g = _
    rw [Nat.testBit_or, ih]
    have hsucc : (n + 1) * B = n * B + B := Nat.succ_mul n B
    by_cases h1 : g < n * B
    · have hlow : (cond (f n) (ones B <<< (n * B)) 0).testBit g = false := by
        cases f n
        · simp
        · rw [Bool.cond_true, Nat.testBit_shiftLeft]; simp [show ¬ g ≥ n * B by omega]
      rw [hlow, Bool.or_false, decide_eq_true h1, decide_eq_true (by omega)]
    · have hdiv : g < (n + 1) * B → g / B = n := fun h => Nat.div_eq_of_lt_le (by omega) h
      rw [decide_eq_false h1, Bool.false_and, Bool.false_or]
      by_cases h2 : g < (n + 1) * B
      · rw [decide_eq_true h2, Bool.true_and, hdiv h2]
        cases f n
        · simp
        · rw [Bool.cond_true, Nat.testBit_shiftLeft, ones_testBit]; simp; omega
      · rw [decide_eq_false h2, Bool.false_and]
        cases f n
        · simp
        · rw [Bool.cond_true, Nat.testBit_shiftLeft, ones_testBit]; simp; omega

/-- `GameMask.bitOf` is `testBit`. -/
theorem bitOf_eq (n i : Nat) : GameMask.bitOf n i = n.testBit i := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  show Nat.beq (n >>> i % 2) 1 = _
  rw [Nat.shiftRight_eq_div_pow]
  cases h : Nat.beq (n / 2 ^ i % 2) 1
  · exact (decide_eq_false (Nat.ne_of_beq_eq_false h)).symm
  · exact (decide_eq_true (Nat.eq_of_beq_eq_true h)).symm

theorem getD_map_range {α : Type} (f : Nat → α) (K j : Nat) (d : α) (hj : j < K) :
    ((List.range K).map f).getD j d = f j := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]
  rfl

/-! ### All windows at once -/

/-- Slice `j` of all windows at the start: bit `p · 2^K + r` is bit `j` of `r`, for the four start phases `p`. -/
def sinit (K : Nat) : List Nat :=
  (List.range K).map fun j => BitGame.rep (Nat.pow 2 K) (Rule30ZeroBoundaryLanes.pat K j) 4

theorem sinit_spec (K j g : Nat) (hj : j < K) (hg : g < 4 * 2 ^ K) :
    ((sinit K).getD j 0).testBit g = (g % 2 ^ K).testBit j := by
  unfold sinit
  rw [getD_map_range _ _ _ _ hj]
  show (BitGame.rep (2 ^ K) (Rule30ZeroBoundaryLanes.pat K j) 4).testBit g = _
  rw [BitGame.rep_testBit _ _ (BitGame.pat_lt K j hj), BitGame.pat_testBit K j _ hj,
    decide_eq_true hg, decide_eq_true (Nat.mod_lt _ (Nat.two_pow_pos K))]
  rfl

/-- One step of every window: slice `j` becomes column `j + 1` at the next time, from the center mask `cm` and the
value `u` of column `K + 1`. -/
def sstep (K N cm : Nat) (u : Bool) (S : List Nat) : List Nat :=
  (List.range K).map fun j =>
    Nat.xor (if j = 0 then cm else S.getD (j - 1) 0)
      (Nat.lor (S.getD j 0) (if j + 1 = K then cond u (ones N) 0 else S.getD (j + 1) 0))

theorem sstep_spec (K N cm : Nat) (u : Bool) (S : List Nat) (g r : Nat) (hr : r < 2 ^ K) (hg : g < N)
    (hS : ∀ j, j < K → (S.getD j 0).testBit g = r.testBit j) (j : Nat) (hj : j < K) :
    ((sstep K N cm u S).getD j 0).testBit g = (GameMask.move K (cm.testBit g) u r).testBit j := by
  unfold sstep
  rw [getD_map_range _ _ _ _ hj, BitGame.move_testBit K _ u r hr j hj]
  unfold BitGame.nextCell
  show ((if j = 0 then cm else S.getD (j - 1) 0) ^^^
    (S.getD j 0 ||| if j + 1 = K then cond u (ones N) 0 else S.getD (j + 1) 0)).testBit g = _
  rw [Nat.testBit_xor, Nat.testBit_or]
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

/-- The windows after column `K + 1` reads `us`, from step `i`: at step `i` the center of the window started at phase
`p` is `w` at `p + i`. -/
def srun (w : List Bool) (K N : Nat) : Nat → List Bool → List Nat → List Nat
  | _, [], S => S
  | i, u :: us, S => srun w K N (i + 1) us (sstep K N (sel (Nat.pow 2 K) (fun p => wordAt w (p + i)) 4) u S)

/-- One window after column `K + 1` reads `us`, the center at phase `ph` first. -/
def wrun (w : List Bool) (K : Nat) : Nat → List Bool → Nat → Nat
  | _, [], r => r
  | ph, u :: us, r => wrun w K (ph + 1) us (GameMask.move K (wordAt w ph) u r)

theorem wrun_lt (w : List Bool) (K : Nat) : ∀ (us : List Bool) (ph r : Nat), r < 2 ^ K → wrun w K ph us r < 2 ^ K
  | [], _, _, hr => hr
  | u :: us, ph, r, _ => wrun_lt w K us (ph + 1) _ (BitGame.move_lt K _ u r)

/-- The phase matters only modulo 4. -/
theorem wrun_mod (w : List Bool) (K : Nat) : ∀ (us : List Bool) (ph ph' r : Nat), ph % 4 = ph' % 4 →
    wrun w K ph us r = wrun w K ph' us r
  | [], _, _, _, _ => rfl
  | u :: us, ph, ph', r, h => by
    show wrun w K (ph + 1) us (GameMask.move K (wordAt w ph) u r) = wrun w K (ph' + 1) us (GameMask.move K (wordAt w ph') u r)
    have hw : wordAt w ph = wordAt w ph' := by unfold wordAt; rw [h]
    rw [hw]
    exact wrun_mod w K us (ph + 1) (ph' + 1) _ (by omega)

/-- **The slices hold every window's run.** -/
theorem srun_spec (w : List Bool) (K : Nat) : ∀ (us : List Bool) (i : Nat) (S : List Nat) (g r : Nat),
    g < 4 * 2 ^ K → r < 2 ^ K → (∀ j, j < K → (S.getD j 0).testBit g = r.testBit j) →
    ∀ j, j < K → ((srun w K (4 * 2 ^ K) i us S).getD j 0).testBit g = (wrun w K (g / 2 ^ K + i) us r).testBit j
  | [], _, _, _, _, _, _, hS, j, hj => hS j hj
  | u :: us, i, S, g, r, hg, hr, hS, j, hj => by
    have hcm : (sel (Nat.pow 2 K) (fun p => wordAt w (p + i)) 4).testBit g = wordAt w (g / 2 ^ K + i) := by
      rw [sel_testBit (Nat.pow 2 K) _ (Nat.two_pow_pos K)]
      show (decide (g < 4 * 2 ^ K) && wordAt w (g / 2 ^ K + i)) = _
      rw [decide_eq_true hg, Bool.true_and]
    show ((srun w K (4 * 2 ^ K) (i + 1) us
        (sstep K (4 * 2 ^ K) (sel (Nat.pow 2 K) (fun p => wordAt w (p + i)) 4) u S)).getD j 0).testBit g =
      (wrun w K (g / 2 ^ K + i + 1) us (GameMask.move K (wordAt w (g / 2 ^ K + i)) u r)).testBit j
    rw [srun_spec w K us (i + 1) _ g _ hg (BitGame.move_lt K _ u r)
      (fun j hj => by rw [sstep_spec K _ _ u S g r hr hg hS j hj, hcm]) j hj, Nat.add_assoc]

/-! ### Entry into the family -/

/-- Bit `g`, below `N`, is set when the first `n` slices hold the bits of `s` at bit `g`. -/
def matchS (N s : Nat) (S : List Nat) : Nat → Nat
  | 0 => ones N
  | n + 1 => Nat.land (matchS N s S n) (cond (GameMask.bitOf s n) (S.getD n 0) (Nat.xor (ones N) (S.getD n 0)))

theorem matchS_spec (N s : Nat) (S : List Nat) (g : Nat) :
    ∀ n, (matchS N s S n).testBit g = true → g < N ∧ ∀ j, j < n → (S.getD j 0).testBit g = s.testBit j := by
  intro n
  induction n with
  | zero =>
    intro h
    rw [show matchS N s S 0 = ones N from rfl, ones_testBit] at h
    exact ⟨of_decide_eq_true h, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | succ n ih =>
    intro h
    have h' : ((matchS N s S n) &&& cond (GameMask.bitOf s n) (S.getD n 0) (ones N ^^^ S.getD n 0)).testBit g =
      true := h
    rw [Nat.testBit_and, Bool.and_eq_true] at h'
    obtain ⟨hg, hlow⟩ := ih h'.1
    refine ⟨hg, fun j hj => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
    · exact hlow j hj
    · subst hj
      have h2 := h'.2
      rw [bitOf_eq] at h2
      cases hs : s.testBit j
      · rw [hs, Bool.cond_false, Nat.testBit_xor, ones_testBit, decide_eq_true hg] at h2
        simpa using h2
      · rw [hs, Bool.cond_true] at h2
        exact h2

/-- The ether columns `j0 + 1, …, j0 + q` at ether phase `ψ`, column `j0 + i + 1` at bit `i`. -/
def etherBits (j0 ψ : Nat) : Nat → Nat
  | 0 => 0
  | q + 1 => Nat.lor (etherBits j0 ψ q) (cond (ether (j0 + q + 1) ψ) (Nat.pow 2 q) 0)

theorem etherBits_testBit (j0 ψ : Nat) : ∀ q i, (etherBits j0 ψ q).testBit i = (decide (i < q) && ether (j0 + i + 1) ψ)
  | 0, i => by simp [etherBits]
  | q + 1, i => by
    show (etherBits j0 ψ q ||| cond (ether (j0 + q + 1) ψ) (2 ^ q) 0).testBit i = _
    rw [Nat.testBit_or, etherBits_testBit j0 ψ q i]
    have hb : (cond (ether (j0 + q + 1) ψ) (2 ^ q) 0).testBit i = (decide (i = q) && ether (j0 + q + 1) ψ) := by
      cases ether (j0 + q + 1) ψ
      · simp
      · rw [Bool.cond_true, Nat.testBit_two_pow]
        by_cases h : i = q
        · simp [h]
        · simp [h, Ne.symm h]
    rw [hb]
    by_cases h1 : i < q
    · simp [h1, show i ≠ q by omega, show i < q + 1 by omega]
    · by_cases h2 : i = q
      · subst h2; simp
      · simp [h1, h2, show ¬ i < q + 1 by omega]

/-- A list of cells as a number, the first at bit 0. -/
def listBits : List Bool → Nat
  | [] => 0
  | b :: bs => Nat.lor (cond b 1 0) (Nat.shiftLeft (listBits bs) 1)

theorem listBits_testBit : ∀ (l : List Bool) (i : Nat), (listBits l).testBit i = l.getD i false
  | [], i => by simp [listBits]
  | b :: bs, 0 => by
    show (cond b 1 0 ||| listBits bs <<< 1).testBit 0 = b
    rw [Nat.testBit_or, Nat.testBit_shiftLeft]
    cases b <;> simp
  | b :: bs, i + 1 => by
    show (cond b 1 0 ||| listBits bs <<< 1).testBit (i + 1) = bs.getD i false
    rw [Nat.testBit_or, Nat.testBit_shiftLeft, show i + 1 - 1 = i by omega, listBits_testBit bs i]
    have hb : (cond b 1 0).testBit (i + 1) = false := by cases b <;> simp [Nat.testBit_succ]
    rw [hb]
    simp

/-- The window of the family at depth `k` for the wall entry `e`: the ether columns at the entry's phase, then its
cells. -/
def code (j0 k : Nat) (e : Nat × List Bool) : Nat := Nat.lor (etherBits j0 e.1 k) (Nat.shiftLeft (listBits e.2) k)

theorem code_low (j0 k : Nat) (e : Nat × List Bool) (q : Nat) (hq : q < k) :
    (code j0 k e).testBit q = ether (j0 + q + 1) e.1 := by
  show (etherBits j0 e.1 k ||| listBits e.2 <<< k).testBit q = _
  rw [Nat.testBit_or, etherBits_testBit, Nat.testBit_shiftLeft, decide_eq_true hq, Bool.true_and]
  simp [show ¬ q ≥ k by omega]

theorem code_high (j0 k : Nat) (e : Nat × List Bool) (i : Nat) :
    (code j0 k e).testBit (k + i) = e.2.getD i false := by
  show (etherBits j0 e.1 k ||| listBits e.2 <<< k).testBit (k + i) = _
  rw [Nat.testBit_or, etherBits_testBit, Nat.testBit_shiftLeft, listBits_testBit,
    decide_eq_false (show ¬ k + i < k by omega), Bool.false_and, Bool.false_or,
    decide_eq_true (show k + i ≥ k by omega), Bool.true_and, show k + i - k = i by omega]

/-- The windows that end in the family: bit `g` is set when the window of bit `g` equals the family's window for one of
the entries `es` whose phase is the ether phase that bit `g` ends at. -/
def trapHit (K L s j0 k : Nat) (S : List Nat) : List (Nat × List Bool) → Nat
  | [] => 0
  | e :: es => Nat.lor (Nat.land (sel (Nat.pow 2 K) (fun p => Nat.beq ((p + L + s) % 4) e.1) 4)
      (matchS (4 * 2 ^ K) (code j0 k e) S K)) (trapHit K L s j0 k S es)

theorem trapHit_spec (K L s j0 k : Nat) (S : List Nat) (g : Nat) : ∀ es : List (Nat × List Bool),
    (trapHit K L s j0 k S es).testBit g = true → ∃ e ∈ es, (g / 2 ^ K + L + s) % 4 = e.1 ∧
      ∀ j, j < K → (S.getD j 0).testBit g = (code j0 k e).testBit j
  | [], h => by simp [trapHit] at h
  | e :: es, h => by
    have h' : ((sel (Nat.pow 2 K) (fun p => Nat.beq ((p + L + s) % 4) e.1) 4 &&&
        matchS (4 * 2 ^ K) (code j0 k e) S K) ||| trapHit K L s j0 k S es).testBit g = true := h
    rw [Nat.testBit_or, Bool.or_eq_true] at h'
    rcases h' with h1 | h1
    · rw [Nat.testBit_and, Bool.and_eq_true, sel_testBit (Nat.pow 2 K) _ (Nat.two_pow_pos K), Bool.and_eq_true] at h1
      obtain ⟨⟨_, hph⟩, hm⟩ := h1
      refine ⟨e, List.mem_cons_self, Nat.eq_of_beq_eq_true hph, (matchS_spec _ _ S g K hm).2⟩
    · obtain ⟨e', he', hrest⟩ := trapHit_spec K L s j0 k S g es h1
      exact ⟨e', List.mem_cons_of_mem e he', hrest⟩

/-- **The check**: after column `K + 1` reads `us`, every window, from every start phase, is the family's window for
one of the kit's wall states. -/
def lockCheck (w : List Bool) (K j0 s k : Nat) (us : List Bool) : Bool :=
  Nat.beq (trapHit K us.length s j0 k (srun w K (4 * 2 ^ K) 0 us (sinit K)) wallStates) (ones (4 * 2 ^ K))

theorem wallStates_length : ∀ e ∈ wallStates, e.2.length = 13 := by decide

theorem wallStates_phase : ∀ e ∈ wallStates, e.1 < 4 := by decide

/-- A list is the segment of its own cells. -/
theorem seg_getD (l : List Bool) : ∀ n, l.length = n → seg (fun i => l.getD i false) n = l := by
  induction l with
  | nil => intro n h; subst h; rfl
  | cons b bs ih =>
    intro n h
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by simp at h; omega⟩
    show b :: seg (fun i => bs.getD i false) n' = b :: bs
    rw [ih n' (by simpa using h)]

end LockWord

open LockWord

/-- The window of the true row: columns `1, …, K` after column `K + 1` reads `us`. -/
theorem codeFrom_wrun (init : Int → Bool) (w : List Bool) (K T : Nat)
    (hT : ∀ t, T ≤ t → evolve init t 0 = wordAt w (t - T)) :
    ∀ (us : List Bool) (t0 : Nat), T ≤ t0 →
      (∀ i, i < us.length → evolve init (t0 + i) ((K : Int) + 1) = us.getD i false) →
      codeFrom init (t0 + us.length) 1 K = wrun w K (t0 - T) us (codeFrom init t0 1 K)
  | [], t0, _, _ => rfl
  | u :: us, t0, ht0, hu => by
    have hstep : codeFrom init (t0 + 1) 1 K = GameMask.move K (wordAt w (t0 - T)) u (codeFrom init t0 1 K) := by
      rw [codeFrom_succ, GameMask.move_eq, show (1 : Int) - 1 = 0 by rfl, hT t0 ht0]
      congr 1
      have e := hu 0 (by simp)
      rw [Nat.add_zero] at e
      rw [show (1 : Int) + (K : Int) = (K : Int) + 1 by omega, e]
      rfl
    have ih := codeFrom_wrun init w K T hT us (t0 + 1) (by omega) (fun i hi => by
      have e := hu (i + 1) (by simp; omega)
      rw [show t0 + 1 + i = t0 + (i + 1) by omega, e]
      rfl)
    rw [show t0 + (u :: us).length = t0 + 1 + us.length by simp; omega, ih, hstep,
      show t0 + 1 - T = t0 - T + 1 by omega]
    rfl

/-- **One word in column `K + 1` forces the lock.** In the orbit of a row with a leftmost 1, let the center repeat `w`
from time `T`, aligned with the ether column `j0` shifted by `s`, and let the family fit in the window at depth `k`. If
`lockCheck` holds, column `K + 1` does not read `us` from any time `t₀ ≥ T`. -/
theorem lockWord_column (w : List Bool) (K j0 s k : Nat) (us : List Bool) (hal : aligned w j0 s = true)
    (hk : (j0 + k) % 7 = 2) (hkK : k + 13 ≤ K) (hc : lockCheck w K j0 s k us = true)
    (init : Int → Bool) (m : Int) (hm : init m = true) (hz : ∀ x : Int, x < m → init x = false)
    (T : Nat) (hT : ∀ t, T ≤ t → evolve init t 0 = wordAt w (t - T)) (t0 : Nat) (ht0 : T ≤ t0)
    (hu : ∀ i, i < us.length → evolve init (t0 + i) ((K : Int) + 1) = us.getD i false) : False := by
  have hB := Nat.two_pow_pos K
  let r0 := codeFrom init t0 1 K
  have hr0 : r0 < 2 ^ K := codeFrom_lt init t0 K 1
  let p := (t0 - T) % 4
  let g := p * 2 ^ K + r0
  have hp : p < 4 := Nat.mod_lt _ (by decide)
  have hg : g < 4 * 2 ^ K := by
    have : p * 2 ^ K + 2 ^ K ≤ 4 * 2 ^ K := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hp
    omega
  have hgdiv : g / 2 ^ K = p := by
    show (p * 2 ^ K + r0) / 2 ^ K = p
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hB, Nat.div_eq_of_lt hr0, Nat.zero_add]
  have hgmod : g % 2 ^ K = r0 := by
    show (p * 2 ^ K + r0) % 2 ^ K = r0
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr0]
  -- the slices at bit `g` hold the true window at time `t0 + L`
  let t1 := t0 + us.length
  have hwin : codeFrom init t1 1 K = wrun w K (g / 2 ^ K + 0) us r0 := by
    rw [codeFrom_wrun init w K T hT us t0 ht0 hu, hgdiv, Nat.add_zero]
    exact wrun_mod w K us _ _ _ (by omega)
  have hsl := srun_spec w K us 0 (sinit K) g r0 hg hr0 (fun j hj => by rw [sinit_spec K j g hj hg, hgmod])
  -- every window ends in the family
  have hall : (trapHit K us.length s j0 k (srun w K (4 * 2 ^ K) 0 us (sinit K)) wallStates).testBit g = true := by
    unfold lockCheck at hc
    rw [Nat.eq_of_beq_eq_true hc, ones_testBit, decide_eq_true hg]
  obtain ⟨e, he, hph, hbits⟩ := trapHit_spec K us.length s j0 k _ g wallStates hall
  have hcell : ∀ j, j < K → evolve init t1 (1 + (j : Int)) = (code j0 k e).testBit j := by
    intro j hj
    have h1 := testBit_codeFrom init t1 K 1 j
    rw [hwin, ← hsl j hj, hbits j hj, decide_eq_true hj, Bool.true_and] at h1
    exact h1.symm
  have hphase : (t1 - T + s) % 4 = e.1 := by
    rw [← hph, hgdiv]
    show (t0 + us.length - T + s) % 4 = ((t0 - T) % 4 + us.length + s) % 4
    omega
  refine family_contra init m hm hz w j0 s k T t1 hal hk hT (by omega) (fun q hq1 hqk => ?_) ?_
  · have e1 := hcell (q - 1) (by omega)
    rw [code_low j0 k e (q - 1) (by omega), show 1 + ((q - 1 : Nat) : Int) = (q : Int) by omega] at e1
    rw [e1]
    exact ether_congr (by omega) (by rw [hphase, Nat.mod_eq_of_lt (wallStates_phase e he)])
  · rw [hphase]
    have hrow : rowOf (fun t p => evolve init t (p : Int)) t1 k 13 = e.2 := by
      unfold rowOf
      conv => rhs; rw [← seg_getD e.2 13 (wallStates_length e he)]
      refine Rule30Ether.seg_congr 13 _ _ fun i hi => ?_
      have e1 := hcell (k + i) (by omega)
      rw [code_high, show 1 + ((k + i : Nat) : Int) = ((k + i + 1 : Nat) : Int) by omega] at e1
      exact e1
    rw [hrow]
    exact he

/-! ### The three words -/

namespace LockWord

/-- The first `L` bits of `n`, bit `i` first. -/
def bitsOf (n L : Nat) : List Bool := (List.range L).map (GameMask.bitOf n)

theorem bitsOf_getD (n L i : Nat) (hi : i < L) : (bitsOf n L).getD i false = n.testBit i := by
  unfold bitsOf
  rw [getD_map_range _ _ _ _ hi, bitOf_eq]

theorem bitsOf_length (n L : Nat) : (bitsOf n L).length = L := by
  simp [bitsOf]

/-- The sequence for `0001`: 1,193 values of column 17, value `i` at bit `i`. -/
def word0001 : Nat := 0x1080140114010044408400a008a0080222042005004500401110210028022802008881080140114010044408400a008a0080222042005004500401110210028022802008894028000528050000a00000000000c00000000282024090140001400001144081140050000000c00300000003014028040402442000000000000000000000000000000000000000000000000088800000

/-- The sequence for `0011`: 955 values of column 15. -/
def word0011 : Nat := 0x1328ca8020088804ca32a00802004ca32a00a44481328ca802008880099465401004009946540148890265195004010026519500401002651020028404ca30000088a000002228000009400004528a00001328c14000001450402651502200008180900020602000000020602400000000000000000000

/-- The sequence for `0111`: 381 values of column 14. -/
def word0111 : Nat := 0x5000001114000004a00000240500000128014000450000aa0010240a008840485000000000000000000000000000000

end LockWord

open LockWord

set_option Elab.async false

set_option maxHeartbeats 0 in
theorem check_0001 : lockCheck w0001 16 6 0 3 (bitsOf word0001 1193) = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0011 : lockCheck w0011 14 1 3 1 (bitsOf word0011 955) = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0111 : lockCheck w0111 13 2 2 0 (bitsOf word0111 381) = true := by decide +kernel

/-- Instances: column `K + 1` reads the word for at most its length. -/
theorem lock_of_check {w : List Bool} {K j0 s k L n : Nat} (hal : aligned w j0 s = true) (hk : (j0 + k) % 7 = 2)
    (hkK : k + 13 ≤ K) (hc : lockCheck w K j0 s k (bitsOf n L) = true)
    (init : Int → Bool) (m : Int) (hm : init m = true) (hz : ∀ x : Int, x < m → init x = false)
    (T : Nat) (hT : ∀ t, T ≤ t → evolve init t 0 = wordAt w (t - T)) (t0 : Nat) (ht0 : T ≤ t0) :
    ∃ i, i < L ∧ evolve init (t0 + i) ((K : Int) + 1) ≠ n.testBit i := by
  refine Classical.byContradiction fun hne => ?_
  refine lockWord_column w K j0 s k (bitsOf n L) hal hk hkK hc init m hm hz T hT t0 ht0 fun i hi => ?_
  rw [bitsOf_length] at hi
  rw [bitsOf_getD n L i hi]
  exact Classical.byContradiction fun h => hne ⟨i, hi, h⟩

/-- **Column 17 never reads `word0001` once the center repeats `0001`**, in the orbit of a row with a leftmost 1. -/
theorem lock_0001 (init : Int → Bool) (m : Int) (hm : init m = true) (hz : ∀ x : Int, x < m → init x = false)
    (T : Nat) (hT : ∀ t, T ≤ t → evolve init t 0 = wordAt w0001 (t - T)) (t0 : Nat) (ht0 : T ≤ t0) :
    ∃ i, i < 1193 ∧ evolve init (t0 + i) 17 ≠ word0001.testBit i :=
  lock_of_check aligned_0001_6 (by decide) (by decide) check_0001 init m hm hz T hT t0 ht0

/-- **Column 15 never reads `word0011` once the center repeats `0011`.** -/
theorem lock_0011 (init : Int → Bool) (m : Int) (hm : init m = true) (hz : ∀ x : Int, x < m → init x = false)
    (T : Nat) (hT : ∀ t, T ≤ t → evolve init t 0 = wordAt w0011 (t - T)) (t0 : Nat) (ht0 : T ≤ t0) :
    ∃ i, i < 955 ∧ evolve init (t0 + i) 15 ≠ word0011.testBit i :=
  lock_of_check aligned_0011_1 (by decide) (by decide) check_0011 init m hm hz T hT t0 ht0

/-- **Column 14 never reads `word0111` once the center repeats `0111`.** -/
theorem lock_0111 (init : Int → Bool) (m : Int) (hm : init m = true) (hz : ∀ x : Int, x < m → init x = false)
    (T : Nat) (hT : ∀ t, T ≤ t → evolve init t 0 = wordAt w0111 (t - T)) (t0 : Nat) (ht0 : T ≤ t0) :
    ∃ i, i < 381 ∧ evolve init (t0 + i) 14 ≠ word0111.testBit i :=
  lock_of_check aligned_0111_2 (by decide) (by decide) check_0111 init m hm hz T hT t0 ht0

/-- The single cell: from the center's form to the row's. -/
theorem single_center_form (w : List Bool) (T : Nat)
    (hT : ∀ t, T ≤ t → Rule30Prize.center t = wordAt w (t - T)) :
    ∀ t, T ≤ t → evolve single t 0 = wordAt w (t - T) := fun t ht => by
  rw [evolve_single_center, hT t ht]

/-- **The center column of the single cell**: once it repeats `0001` from time `T`, column 17 never reads
`word0001`. -/
theorem center_lock_0001 (T : Nat) (hT : ∀ t, T ≤ t → Rule30Prize.center t = wordAt w0001 (t - T)) (t0 : Nat)
    (ht0 : T ≤ t0) : ∃ i, i < 1193 ∧ Rule30Jen.cell (t0 + i) 17 ≠ word0001.testBit i := by
  obtain ⟨i, hi, h⟩ := lock_0001 single 0 rfl (fun x hx => decide_eq_false (by omega)) T
    (single_center_form _ T hT) t0 ht0
  exact ⟨i, hi, by rwa [evolve_single_eq_cell] at h⟩

/-- **The center column of the single cell**: once it repeats `0011`, column 15 never reads `word0011`. -/
theorem center_lock_0011 (T : Nat) (hT : ∀ t, T ≤ t → Rule30Prize.center t = wordAt w0011 (t - T)) (t0 : Nat)
    (ht0 : T ≤ t0) : ∃ i, i < 955 ∧ Rule30Jen.cell (t0 + i) 15 ≠ word0011.testBit i := by
  obtain ⟨i, hi, h⟩ := lock_0011 single 0 rfl (fun x hx => decide_eq_false (by omega)) T
    (single_center_form _ T hT) t0 ht0
  exact ⟨i, hi, by rwa [evolve_single_eq_cell] at h⟩

/-- **The center column of the single cell**: once it repeats `0111`, column 14 never reads `word0111`. -/
theorem center_lock_0111 (T : Nat) (hT : ∀ t, T ≤ t → Rule30Prize.center t = wordAt w0111 (t - T)) (t0 : Nat)
    (ht0 : T ≤ t0) : ∃ i, i < 381 ∧ Rule30Jen.cell (t0 + i) 14 ≠ word0111.testBit i := by
  obtain ⟨i, hi, h⟩ := lock_0111 single 0 rfl (fun x hx => decide_eq_false (by omega)) T
    (single_center_form _ T hT) t0 ht0
  exact ⟨i, hi, by rwa [evolve_single_eq_cell] at h⟩

/-- **A sufficient condition for `0001`**: if column 17 of the single cell's orbit reads `word0001` from arbitrarily
late times, the center column does not eventually repeat `0001`, in any rotation. -/
theorem center_not_0001_of_word
    (h : ∀ N, ∃ t0, N ≤ t0 ∧ ∀ i, i < 1193 → Rule30Jen.cell (t0 + i) 17 = word0001.testBit i) :
    ¬ ∃ T, ∀ t, T ≤ t → Rule30Prize.center t = wordAt w0001 (t - T) := by
  rintro ⟨T, hT⟩
  obtain ⟨t0, ht0, hw⟩ := h T
  obtain ⟨i, hi, hne⟩ := center_lock_0001 T hT t0 ht0
  exact hne (hw i hi)

/-- **A sufficient condition for `0011`**, through column 15. -/
theorem center_not_0011_of_word
    (h : ∀ N, ∃ t0, N ≤ t0 ∧ ∀ i, i < 955 → Rule30Jen.cell (t0 + i) 15 = word0011.testBit i) :
    ¬ ∃ T, ∀ t, T ≤ t → Rule30Prize.center t = wordAt w0011 (t - T) := by
  rintro ⟨T, hT⟩
  obtain ⟨t0, ht0, hw⟩ := h T
  obtain ⟨i, hi, hne⟩ := center_lock_0011 T hT t0 ht0
  exact hne (hw i hi)

/-- **A sufficient condition for `0111`**, through column 14. -/
theorem center_not_0111_of_word
    (h : ∀ N, ∃ t0, N ≤ t0 ∧ ∀ i, i < 381 → Rule30Jen.cell (t0 + i) 14 = word0111.testBit i) :
    ¬ ∃ T, ∀ t, T ≤ t → Rule30Prize.center t = wordAt w0111 (t - T) := by
  rintro ⟨T, hT⟩
  obtain ⟨t0, ht0, hw⟩ := h T
  obtain ⟨i, hi, hne⟩ := center_lock_0111 T hT t0 ht0
  exact hne (hw i hi)

end Rule30Open
