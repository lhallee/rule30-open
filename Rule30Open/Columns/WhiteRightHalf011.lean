module

public import Rule30Open.PeriodTwo.WhiteRightHalf
public import Ruliology.CellularAutomata.Rule30Realization

/-!
# Against a white right half, no left half within depth 32,751 keeps the center on `011`

Fix a center column `c` and a white right half. The kit's realization (`Rule30Realization`) rebuilds the one row that
keeps the center on `c` against a right half: the right half is driven by `c` (`rh`), column `-1` is forced by the
center's update (`ycol`), and left-permutivity rebuilds every column to the left (`lc`). A configuration is determined
by its right half and its center column (`unique`), and column `-m` at time `t` sees `c` only up to time `m + t`
(`lc_congr`). So a row whose cells right of the center are white and whose center follows `c` through time `T` has, at
every depth `d ≤ T`, the cell `lc whiteRight c d 0` (`left_eq_lc`), and a left half within depth `W` loses `c` by the
first black depth of that row beyond `W` (`leaves_by_lc`). This holds for every center column; for the alternating one
it is the half of the kit's `exact_death_center` that `WhiteRightHalf` uses.

For the center repeating `011` (`col011`), the kernel computes the row to depth 32,768 in each of the three phases and
checks that every window of 16 depths starting at a depth up to 32,752 holds a black cell.

* `rh_white`: the white right half driven by `c` is the kit's `drv`, so `rowN` computes it as bit masks.
* `collectBits`, `collectBits_spec`: a loop that collects one bit per time; `colOneN` (column `1`) and `centerN`
  (column `0`) as numbers, `colOneN_testBit`, `centerN_testBit`.
* `colC`, `colC_testBit`: the columns rebuilt leftward from columns `1` and `0` by one recurrence; `psiLoop_colC`,
  `psiBitsC`, `psiBitsC_spec`: the row at time `0`, bit `d` being depth `d`, through `WhiteRightHalf.psiLoop`.
* `psi011_gaps`: the gaps, through `WhiteRightHalf.gapsCheck` (`gaps011_0` to `gaps011_2`).
* `white_right_leaves_011`: no configuration whose right half is white and whose left half lies within depth
  `W < 32752` keeps its center on `011`, in any phase, through time `W + 16`.

The natural-language argument is `WhiteRightHalf011.md`, beside this file.
-/

@[expose] public section

-- Sequential elaboration: the kernel checks would otherwise run in parallel and stack their memory.
set_option Elab.async false

namespace Rule30Open

open Ruliology.CellularAutomata

/-! ### Any center column against the white right half -/

/-- The white right half, as cells of a configuration. -/
def whiteRight : Int → Bool := fun _ => false

/-- The white right half, as the kit's driven half reads it. -/
def whiteHalf : Nat → Bool := fun _ => false

/-- **The white right half driven by `c`** is the kit's `drv` with the white start. -/
theorem rh_white (c : Nat → Bool) : ∀ t (p : Nat),
    Rule30Realization.rh whiteRight c t ((p + 1 : Nat) : Int) = Rule30Ether.drv c whiteHalf t (p + 1)
  | 0, p => (Rule30Ether.drv_init c whiteHalf (p + 1) (by omega)).symm
  | t + 1, p => by
    cases p with
    | zero =>
      show Rule30Jen.rule (if ((0 + 1 : Nat) : Int) = 1 then c t
            else Rule30Realization.rh whiteRight c t (((0 + 1 : Nat) : Int) - 1))
          (Rule30Realization.rh whiteRight c t ((0 + 1 : Nat) : Int))
          (Rule30Realization.rh whiteRight c t (((0 + 1 : Nat) : Int) + 1)) =
        Rule30Jen.rule (Rule30Ether.drv c whiteHalf t 0) (Rule30Ether.drv c whiteHalf t (0 + 1))
          (Rule30Ether.drv c whiteHalf t (1 + 1))
      rw [if_pos (show ((0 + 1 : Nat) : Int) = 1 by omega),
        show ((0 + 1 : Nat) : Int) + 1 = ((1 + 1 : Nat) : Int) by omega,
        rh_white c t 0, rh_white c t 1, Rule30Ether.drv_col0]
    | succ q =>
      show Rule30Jen.rule (if ((q + 1 + 1 : Nat) : Int) = 1 then c t
            else Rule30Realization.rh whiteRight c t (((q + 1 + 1 : Nat) : Int) - 1))
          (Rule30Realization.rh whiteRight c t ((q + 1 + 1 : Nat) : Int))
          (Rule30Realization.rh whiteRight c t (((q + 1 + 1 : Nat) : Int) + 1)) =
        Rule30Jen.rule (Rule30Ether.drv c whiteHalf t (q + 1)) (Rule30Ether.drv c whiteHalf t (q + 1 + 1))
          (Rule30Ether.drv c whiteHalf t (q + 1 + 1 + 1))
      rw [if_neg (show ¬ ((q + 1 + 1 : Nat) : Int) = 1 by omega),
        show ((q + 1 + 1 : Nat) : Int) - 1 = ((q + 1 : Nat) : Int) by omega,
        show ((q + 1 + 1 : Nat) : Int) + 1 = ((q + 1 + 1 + 1 : Nat) : Int) by omega,
        rh_white c t q, rh_white c t (q + 1), rh_white c t (q + 1 + 1)]

/-- **A row whose right half is white has, at depth `d`, the cell of the kit's rebuilt row for its own center
column.** -/
theorem left_eq_lc (x : Int → Bool) (hR : ∀ p : Int, 0 < p → x p = false) (d : Nat) :
    x (-(d : Int)) = Rule30Realization.lc whiteRight (fun t => Rule30Realization.evol x t 0) d 0 := by
  have hx : x = Rule30Realization.conf whiteRight (fun t => Rule30Realization.evol x t 0) :=
    Rule30Realization.unique
      (fun p hp => by
        rw [(Rule30Realization.realize whiteRight (fun t => Rule30Realization.evol x t 0)).1 p hp]
        exact hR p (by omega))
      (fun t => ((Rule30Realization.realize whiteRight (fun t => Rule30Realization.evol x t 0)).2 t).symm)
  have h1 : x (-(d : Int)) =
      Rule30Realization.conf whiteRight (fun t => Rule30Realization.evol x t 0) (-(d : Int)) :=
    congrFun hx _
  rw [h1]
  unfold Rule30Realization.conf
  rw [if_neg (show ¬ (1 : Int) ≤ -(d : Int) by omega), show (-(-(d : Int))).toNat = d by omega]

/-- **A left half within depth `W` loses the center column `c`** against the white right half by the first black depth
of the rebuilt row for `c` beyond `W`. -/
theorem leaves_by_lc (x : Int → Bool) (c : Nat → Bool) (W G : Nat) (hR : ∀ p : Int, 0 < p → x p = false)
    (hL : ∀ p : Int, p < -(W : Int) → x p = false)
    (hgap : ∃ d, W < d ∧ d ≤ W + G ∧ Rule30Realization.lc whiteRight c d 0 = true) :
    ∃ t, t ≤ W + G ∧ Rule30Realization.evol x t 0 ≠ c t := by
  obtain ⟨d, hd1, hd2, hd⟩ := hgap
  refine Classical.byContradiction fun hne => ?_
  have hall : ∀ t, t ≤ W + G → Rule30Realization.evol x t 0 = c t :=
    fun t ht => Classical.byContradiction fun h => hne ⟨t, ht, h⟩
  have hc : Rule30Realization.lc whiteRight (fun t => Rule30Realization.evol x t 0) d 0 =
      Rule30Realization.lc whiteRight c d 0 :=
    Rule30Realization.lc_congr whiteRight d 0 (fun s hs => hall s (by omega))
  have h1 := left_eq_lc x hR d
  rw [hc, hd, hL (-(d : Int)) (by omega)] at h1
  exact Bool.false_ne_true h1

/-! ### The rebuilt row as numbers -/

/-- Collect the bit `g t r` at bit `t`, for the times `t, t + 1, …`, with the state `r` stepped by `s`. -/
def collectBits (g : Nat → Nat → Bool) (s : Nat → Nat → Nat) : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, acc => acc
  | n + 1, t, r, acc =>
    if (Nat.ble 0 (if g t r = true then acc ||| (1 <<< t) else acc) && Nat.ble 0 (s t r)) = true
    then collectBits g s n (t + 1) (s t r) (if g t r = true then acc ||| (1 <<< t) else acc)
    else 0

theorem collectBits_succ (g : Nat → Nat → Bool) (s : Nat → Nat → Nat) (n t r acc : Nat) :
    collectBits g s (n + 1) t r acc =
      collectBits g s n (t + 1) (s t r) (if g t r = true then acc ||| (1 <<< t) else acc) := by
  rw [collectBits, Nat.ble_eq_true_of_le (Nat.zero_le _), Nat.ble_eq_true_of_le (Nat.zero_le _)]
  rfl

theorem collectBits_spec (g : Nat → Nat → Bool) (s : Nat → Nat → Nat) (st : Nat → Nat)
    (hs : ∀ t, s t (st t) = st (t + 1)) : ∀ n t acc, (∀ i, t ≤ i → acc.testBit i = false) → ∀ i,
    (collectBits g s n t (st t) acc).testBit i =
      if i < t then acc.testBit i else if i < t + n then g i (st i) else false := by
  intro n
  induction n with
  | zero =>
    intro t acc hacc i
    simp only [collectBits, Nat.add_zero]
    by_cases h : i < t
    · rw [ite_eq_left h]
    · rw [ite_eq_right h, ite_eq_right h, hacc i (by omega)]
  | succ n ih =>
    intro t acc hacc i
    have hbit : ∀ j, (if g t (st t) = true then acc ||| (1 <<< t) else acc).testBit j =
        (acc.testBit j || (decide (t = j) && g t (st t))) := by
      intro j
      cases g t (st t)
      · simp
      · simp [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow]
    rw [collectBits_succ, hs t, ih (t + 1) _ (by
        intro j hj
        rw [hbit j, hacc j (by omega), decide_eq_false (show ¬ t = j by omega)]
        rfl),
      hbit i]
    by_cases h1 : i < t
    · rw [ite_eq_left (show i < t + 1 by omega), ite_eq_left h1, decide_eq_false (show ¬ t = i by omega),
        Bool.false_and, Bool.or_false]
    · by_cases h2 : i = t
      · rw [ite_eq_left (show i < t + 1 by omega), ite_eq_right h1, ite_eq_left (show i < t + (n + 1) by omega),
          hacc i (by omega), decide_eq_true h2.symm, Bool.true_and, Bool.false_or, h2]
      · rw [ite_eq_right (show ¬ i < t + 1 by omega), ite_eq_right h1, show t + 1 + n = t + (n + 1) by omega]

/-- Column `1` of the white right half driven by `c`, at the times `0, …, N - 1`. -/
def colOneN (c : Nat → Bool) (N : Nat) : Nat :=
  collectBits (fun _ r => r.testBit 0) (fun t r => Rule30EtherThree.stepN (c t) r) N 0 0 0

/-- The center column `c` at the times `0, …, N`. -/
def centerN (c : Nat → Bool) (N : Nat) : Nat := collectBits (fun t _ => c t) (fun _ _ => 0) (N + 1) 0 0 0

theorem colOneN_testBit (c : Nat → Bool) (N t : Nat) (ht : t < N) :
    (colOneN c N).testBit t = Rule30Realization.rh whiteRight c t 1 := by
  have h := collectBits_spec (fun _ r => r.testBit 0) (fun t r => Rule30EtherThree.stepN (c t) r)
    (Rule30EtherThree.rowN c 0) (fun _ => rfl) N 0 0 (fun i _ => Nat.zero_testBit i) t
  have hr := Rule30EtherThree.rowN_eq_drv c 0 t 0
  have he : (fun p : Nat => (0 : Nat).testBit (p - 1)) = whiteHalf := by
    funext p; exact Nat.zero_testBit _
  rw [he] at hr
  unfold colOneN
  refine h.trans ?_
  rw [ite_eq_right (by omega), ite_eq_left (by omega)]
  show (Rule30EtherThree.rowN c 0 t).testBit 0 = Rule30Realization.rh whiteRight c t 1
  rw [hr]
  exact (rh_white c t 0).symm

theorem centerN_testBit (c : Nat → Bool) (N t : Nat) (ht : t ≤ N) : (centerN c N).testBit t = c t := by
  have h := collectBits_spec (fun t _ => c t) (fun _ _ => 0) (fun _ => 0) (fun _ => rfl) (N + 1) 0 0
    (fun i _ => Nat.zero_testBit i) t
  unfold centerN
  refine h.trans ?_
  rw [ite_eq_right (by omega), ite_eq_left (by omega)]

/-- The columns rebuilt leftward from column `1` (`A`) and column `0` (`B`): entry `m + 1` is column `-m`. -/
def colC (A B : Nat) : Nat → Nat
  | 0 => A
  | 1 => B
  | k + 2 => (colC A B (k + 1) >>> 1) ^^^ (colC A B (k + 1) ||| colC A B k)

/-- **The columns are the kit's rebuilt columns** while the bits of `A` and `B` they read are column `1` and the
center. -/
theorem colC_testBit (c : Nat → Bool) (A B N : Nat)
    (hA : ∀ t, t < N → A.testBit t = Rule30Realization.rh whiteRight c t 1) (hB : ∀ t, t ≤ N → B.testBit t = c t) :
    ∀ m t, t + m ≤ N → (colC A B (m + 1)).testBit t = Rule30Realization.lc whiteRight c m t := by
  have key : ∀ m, (∀ t, t + m ≤ N → (colC A B (m + 1)).testBit t = Rule30Realization.lc whiteRight c m t) ∧
      (∀ t, t + (m + 1) ≤ N → (colC A B (m + 2)).testBit t = Rule30Realization.lc whiteRight c (m + 1) t) := by
    intro m
    induction m with
    | zero =>
      refine ⟨fun t ht => ?_, fun t ht => ?_⟩
      · show B.testBit t = c t
        exact hB t (by omega)
      · show ((B >>> 1) ^^^ (B ||| A)).testBit t = xor (c (t + 1)) (c t || Rule30Realization.rh whiteRight c t 1)
        rw [Nat.testBit_xor, Nat.testBit_or, Nat.testBit_shiftRight, show 1 + t = t + 1 by omega,
          hB (t + 1) (by omega), hB t (by omega), hA t (by omega)]
    | succ m ih =>
      refine ⟨ih.2, fun t ht => ?_⟩
      show ((colC A B (m + 2) >>> 1) ^^^ (colC A B (m + 2) ||| colC A B (m + 1))).testBit t =
        xor (Rule30Realization.lc whiteRight c (m + 1) (t + 1))
          (Rule30Realization.lc whiteRight c (m + 1) t || Rule30Realization.lc whiteRight c m t)
      rw [Nat.testBit_xor, Nat.testBit_or, Nat.testBit_shiftRight, show 1 + t = t + 1 by omega,
        ih.2 (t + 1) (by omega), ih.2 t (by omega), ih.1 t (by omega)]
  exact fun m t ht => (key m).1 t ht

/-- `WhiteRightHalf.psiLoop` on the columns `colC`: it collects bit `0` of the columns `k, k + 1, …`. -/
theorem psiLoop_colC (A B : Nat) : ∀ n k acc, 1 ≤ k → (∀ i, k ≤ i → acc.testBit i = false) → ∀ i,
    (psiLoop n k (colC A B (k - 1)) (colC A B k) acc).testBit i =
      if i < k then acc.testBit i else if i < k + n then (colC A B i).testBit 0 else false := by
  intro n
  induction n with
  | zero =>
    intro k acc _ hacc i
    simp only [psiLoop, Nat.add_zero]
    by_cases h : i < k
    · rw [ite_eq_left h]
    · rw [ite_eq_right h, ite_eq_right h, hacc i (by omega)]
  | succ n ih =>
    intro k acc hk hacc i
    have hbit : ∀ j, (if (colC A B k).testBit 0 = true then acc ||| (1 <<< k) else acc).testBit j =
        (acc.testBit j || (decide (k = j) && (colC A B k).testBit 0)) := by
      intro j
      cases (colC A B k).testBit 0
      · simp
      · simp [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow]
    have hnext : (colC A B k >>> 1) ^^^ (colC A B k ||| colC A B (k - 1)) = colC A B (k + 1) := by
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      rfl
    rw [psiLoop_succ, hnext, show colC A B k = colC A B (k + 1 - 1) by rw [Nat.add_sub_cancel],
      ih (k + 1) _ (by omega) (by
        intro j hj
        rw [show k + 1 - 1 = k by omega, hbit j, hacc j (by omega), decide_eq_false (show ¬ k = j by omega)]
        rfl),
      show k + 1 - 1 = k by omega, hbit i]
    by_cases h1 : i < k
    · rw [ite_eq_left (show i < k + 1 by omega), ite_eq_left h1, decide_eq_false (show ¬ k = i by omega),
        Bool.false_and, Bool.or_false]
    · by_cases h2 : i = k
      · rw [ite_eq_left (show i < k + 1 by omega), ite_eq_right h1, ite_eq_left (show i < k + (n + 1) by omega),
          hacc i (by omega), decide_eq_true h2.symm, Bool.true_and, Bool.false_or, h2]
      · rw [ite_eq_right (show ¬ i < k + 1 by omega), ite_eq_right h1, show k + 1 + n = k + (n + 1) by omega]

/-- The row that keeps the center on `c` against the white right half, at the depths `0, …, N`, bit `d` being depth
`d`. -/
def psiBitsC (c : Nat → Bool) (N : Nat) : Nat := psiLoop (N + 1) 1 (colOneN c N) (centerN c N) 0 >>> 1

/-- **The computed bits are the kit's rebuilt row** at the depths up to `N`. -/
theorem psiBitsC_spec (c : Nat → Bool) (N d : Nat) (hd : d ≤ N) :
    (psiBitsC c N).testBit d = Rule30Realization.lc whiteRight c d 0 := by
  have h := psiLoop_colC (colOneN c N) (centerN c N) (N + 1) 1 0 (Nat.le_refl 1) (fun i _ => Nat.zero_testBit i)
    (1 + d)
  rw [show colC (colOneN c N) (centerN c N) (1 - 1) = colOneN c N from rfl,
    show colC (colOneN c N) (centerN c N) 1 = centerN c N from rfl] at h
  unfold psiBitsC
  rw [Nat.testBit_shiftRight, h, ite_eq_right (by omega), ite_eq_left (by omega), show 1 + d = d + 1 by omega]
  exact colC_testBit c (colOneN c N) (centerN c N) N (fun t ht => colOneN_testBit c N t ht)
    (fun t ht => centerN_testBit c N t ht) d 0 (by omega)

/-! ### The center on `011` -/

/-- The center column repeating `011` from phase `φ`: white exactly at the times `t` with `t + φ` a multiple of 3. -/
def col011 (φ t : Nat) : Bool := (t + φ) % 3 != 0

/-! The kernel checks the gaps of the rebuilt row to depth 32,768 in each phase. -/

theorem gaps011_0 : gapsCheck (psiBitsC (col011 0) 32768) 32768 16 32752 = true := by
  decide +kernel

theorem gaps011_1 : gapsCheck (psiBitsC (col011 1) 32768) 32768 16 32752 = true := by
  decide +kernel

theorem gaps011_2 : gapsCheck (psiBitsC (col011 2) 32768) 32768 16 32752 = true := by
  decide +kernel

/-- **The black cells of the row for `011` are never 16 or more apart** up to depth 32,768, in each phase: every
window of 16 depths beyond `W < 32752` holds one. -/
theorem psi011_gaps (φ : Nat) (hφ : φ < 3) (W : Nat) (hW : W < 32752) :
    ∃ d, W < d ∧ d ≤ W + 16 ∧ Rule30Realization.lc whiteRight (col011 φ) d 0 = true := by
  have hc : gapsCheck (psiBitsC (col011 φ) 32768) 32768 16 32752 = true := by
    rcases (show φ = 0 ∨ φ = 1 ∨ φ = 2 by omega) with rfl | rfl | rfl
    · exact gaps011_0
    · exact gaps011_1
    · exact gaps011_2
  obtain ⟨d, h1, h2, h3⟩ := gaps_of_check _ 32768 16 32752 (by decide) (by decide) hc W hW
  refine ⟨d, h1, h2, ?_⟩
  rw [← psiBitsC_spec (col011 φ) 32768 d (by omega)]
  exact h3

/-- **No left half within depth `W < 32752` keeps the center on `011` against the white right half**: the center of
every configuration whose cells right of it are white and whose cells left of `-W` are white leaves `011`, in any
phase `φ`, by time `W + 16`. -/
theorem white_right_leaves_011 (x : Int → Bool) (φ W : Nat) (hW : W < 32752)
    (hR : ∀ p : Int, 0 < p → x p = false) (hL : ∀ p : Int, p < -(W : Int) → x p = false) :
    ∃ t, t ≤ W + 16 ∧ Rule30Realization.evol x t 0 ≠ col011 φ t := by
  have hφ : col011 φ = col011 (φ % 3) := by
    funext t
    unfold col011
    rw [show (t + φ) % 3 = (t + φ % 3) % 3 by omega]
  rw [hφ]
  exact leaves_by_lc x (col011 (φ % 3)) W 16 hR hL (psi011_gaps (φ % 3) (Nat.mod_lt _ (by decide)) W hW)

end Rule30Open
