module

public import Rule30Open.Foundations.Evolve
public import Rule30Open.Foundations.Official
public import Rule30Open.PeriodTwo.Domains

/-!
# The cells left of a column count down its runs of 1s

A cell reading 1 has, left of it, the opposite of its next value (`left_of_one`), so while a column reads 1
the cell next to it reads 0, except at the last 1 of the run, where it reads 1. And while the column reads
1, the OR in that cell's update is 1, so the cells left of the column follow `heldOne`, Rule 30 beside a
column held at 1 (`left_heldOne`), which fixes domain B, 0 1 0 1 ... read from the column
(`heldOne_domainB`). One step back along a run, a half that reads 0 next to the column agrees with domain B
on one more cell than its image (`heldOne_agree_back`, `heldOne_differ_back`).

So when column `k` reads 1 at `b + 1` steps from `s` on and then 0, the cells left of it at `s` agree with
domain B on exactly their `b` nearest cells (`run_countdown`), in the orbit of every row. In the orbit of a
row with a leftmost 1 this bounds every run of 1s by the column's distance to the leftmost 1
(`run_bound`), and no column reads 1 forever (`no_ones_column`, `center_not_eventually_ones`): a proof of
that half of period 1 that does not go through Jen's theorem.

The natural-language argument is `RunCountdown.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

open Ruliology.CellularAutomata

/-- Rule 30 left of a column held at 1; bit `j` is the cell `j + 1` places left of the column. -/
def heldOne (u : Nat → Bool) : Nat → Bool
  | 0 => !(u 1)
  | j + 1 => xor (u (j + 2)) (u (j + 1) || u j)

theorem heldOne_domainB : heldOne domainB = domainB := by
  funext j
  cases j with
  | zero => rfl
  | succ j =>
    show xor (domainB (j + 2)) (domainB (j + 1) || domainB j) = domainB (j + 1)
    unfold domainB
    rcases Nat.mod_two_eq_zero_or_one j with h | h
    · rw [show (j + 2) % 2 = 0 by omega, show (j + 1) % 2 = 1 by omega, h]; rfl
    · rw [show (j + 2) % 2 = 1 by omega, show (j + 1) % 2 = 0 by omega, h]; rfl

theorem xor_cancel_right (a b x : Bool) (h : xor a x = xor b x) : a = b := by
  revert h; cases a <;> cases b <;> cases x <;> decide

theorem not_cancel (a b : Bool) (h : (!a) = !b) : a = b := by
  revert h; cases a <;> cases b <;> decide

theorem not_xor_left (a x : Bool) : (!(xor a x)) = xor (!a) x := by
  cases a <;> cases x <;> rfl

/-- While a column reads 1, the cells left of it follow `heldOne`. -/
theorem left_heldOne (init : Int → Bool) (k : Int) (t : Nat) (h1 : evolve init t k = true) :
    leftOf init (t + 1) k = heldOne (leftOf init t k) := by
  funext j
  cases j with
  | zero =>
    show rule30 (evolve init t (k - 1 - ((0 : Nat) : Int) - 1)) (evolve init t (k - 1 - ((0 : Nat) : Int)))
      (evolve init t (k - 1 - ((0 : Nat) : Int) + 1)) = !(evolve init t (k - 1 - ((1 : Nat) : Int)))
    rw [show k - 1 - ((0 : Nat) : Int) + 1 = k by omega, h1,
      show k - 1 - ((0 : Nat) : Int) - 1 = k - 1 - ((1 : Nat) : Int) by omega]
    generalize evolve init t (k - 1 - ((1 : Nat) : Int)) = a
    generalize evolve init t (k - 1 - ((0 : Nat) : Int)) = c
    cases a <;> cases c <;> rfl
  | succ j =>
    show rule30 (evolve init t (k - 1 - ((j + 1 : Nat) : Int) - 1)) (evolve init t (k - 1 - ((j + 1 : Nat) : Int)))
      (evolve init t (k - 1 - ((j + 1 : Nat) : Int) + 1)) =
      xor (evolve init t (k - 1 - ((j + 2 : Nat) : Int)))
        (evolve init t (k - 1 - ((j + 1 : Nat) : Int)) || evolve init t (k - 1 - (j : Int)))
    rw [show k - 1 - ((j + 1 : Nat) : Int) - 1 = k - 1 - ((j + 2 : Nat) : Int) by omega,
      show k - 1 - ((j + 1 : Nat) : Int) + 1 = k - 1 - (j : Int) by omega]
    rfl

/-- One step back along a run of 1s: a half that reads 0 next to the column, and whose `heldOne` image agrees with
domain B on its `n` lowest bits, agrees with domain B on its `n + 1` lowest bits. -/
theorem heldOne_agree_back (u : Nat → Bool) (h0 : u 0 = false) :
    ∀ n, (∀ j, j < n → heldOne u j = domainB j) → ∀ j, j < n + 1 → u j = domainB j := by
  intro n
  induction n with
  | zero => intro _ j hj; rw [show j = 0 by omega, h0]; rfl
  | succ n ih =>
    intro hk j hj
    have hlow := ih (fun i hi => hk i (by omega))
    by_cases hjn : j < n + 1
    · exact hlow j hjn
    · rw [show j = n + 1 by omega]
      have hn : heldOne u n = domainB n := hk n (by omega)
      cases n with
      | zero =>
        have h1 : (!(u 1)) = !(domainB 1) := hn
        exact not_cancel _ _ h1
      | succ n =>
        have e1 : heldOne u (n + 1) = xor (u (n + 2)) (domainB (n + 1) || domainB n) := by
          show xor (u (n + 2)) (u (n + 1) || u n) = _
          rw [hlow (n + 1) (by omega), hlow n (by omega)]
        have e2 : heldOne domainB (n + 1) = xor (domainB (n + 2)) (domainB (n + 1) || domainB n) := rfl
        rw [heldOne_domainB] at e2
        exact xor_cancel_right _ _ _ (e1.symm.trans (hn.trans e2))

/-- ... and if the image differs from domain B at bit `n`, the half differs from it at bit `n + 1`. -/
theorem heldOne_differ_back (u : Nat → Bool) (n : Nat) (hk : ∀ j, j < n + 1 → u j = domainB j)
    (hd : heldOne u n = !domainB n) : u (n + 1) = !domainB (n + 1) := by
  cases n with
  | zero =>
    have h1 : (!(u 1)) = !(!(domainB 1)) := hd
    exact not_cancel _ _ h1
  | succ n =>
    have e1 : heldOne u (n + 1) = xor (u (n + 2)) (domainB (n + 1) || domainB n) := by
      show xor (u (n + 2)) (u (n + 1) || u n) = _
      rw [hk (n + 1) (by omega), hk n (by omega)]
    have e2 : heldOne domainB (n + 1) = xor (domainB (n + 2)) (domainB (n + 1) || domainB n) := rfl
    rw [heldOne_domainB] at e2
    exact xor_cancel_right _ _ _
      (e1.symm.trans (hd.trans ((congrArg (fun b => !b) e2).trans (not_xor_left _ _))))

/-- The cells left of a column count down its runs of 1s: if column `k` reads 1 at the `b + 1` steps from `s` on and
0 at the next, the cells left of it at step `s` agree with domain B, 0 1 0 1 ... read from the column, on exactly
their `b` nearest cells. This holds in the orbit of every row. -/
theorem run_countdown (init : Int → Bool) (k : Int) (b : Nat) : ∀ s : Nat,
    (∀ i, i ≤ b → evolve init (s + i) k = true) → evolve init (s + b + 1) k = false →
    (∀ j, j < b → leftOf init s k j = domainB j) ∧ leftOf init s k b = !domainB b := by
  induction b with
  | zero =>
    intro s h1 h0
    refine ⟨fun j hj => absurd hj (Nat.not_lt_zero j), ?_⟩
    have hs : evolve init s k = true := h1 0 (Nat.le_refl 0)
    have hs' : evolve init (s + 1) k = false := h0
    show evolve init s (k - 1 - ((0 : Nat) : Int)) = !domainB 0
    rw [show k - 1 - ((0 : Nat) : Int) = k - 1 by omega, left_of_alternating init k s hs hs']
    rfl
  | succ b ih =>
    intro s h1 h0
    have hs : evolve init s k = true := h1 0 (Nat.zero_le _)
    obtain ⟨hk, hd⟩ := ih (s + 1)
      (fun i hi => by rw [show s + 1 + i = s + (i + 1) by omega]; exact h1 (i + 1) (by omega))
      (by rw [show s + 1 + b + 1 = s + (b + 1) + 1 by omega]; exact h0)
    have hstep := left_heldOne init k s hs
    have hk' : ∀ j, j < b → heldOne (leftOf init s k) j = domainB j := fun j hj => by
      rw [← congrFun hstep j]; exact hk j hj
    have hd' : heldOne (leftOf init s k) b = !domainB b := by rw [← congrFun hstep b]; exact hd
    have h0' : leftOf init s k 0 = false := by
      show evolve init s (k - 1 - ((0 : Nat) : Int)) = false
      rw [show k - 1 - ((0 : Nat) : Int) = k - 1 by omega, left_of_one init k s hs, h1 1 (by omega)]
      rfl
    have hagree := heldOne_agree_back (leftOf init s k) h0' b hk'
    exact ⟨hagree, heldOne_differ_back (leftOf init s k) b hagree hd'⟩

/-- In the orbit of a row with its leftmost 1 at `m`, a run of 1s of column `k` from step `s` is bounded by the distance
`k - (m - s)` from the column to the leftmost 1 at `s`: a run of odd length `b + 1` lasts at most that many steps, one
of even length at most two more. For even `b` the cell `b + 1` places left of the column reads 1, for odd `b ≥ 3` the
cell `b - 1` places left does, and neither lies left of the leftmost 1. -/
theorem run_bound (init : Int → Bool) (m : Int) (hm : init m = true) (hz : ∀ x : Int, x < m → init x = false)
    (k : Int) (b s : Nat) (hrun : ∀ i, i ≤ b → evolve init (s + i) k = true)
    (hend : evolve init (s + b + 1) k = false) :
    (b % 2 = 0 → (b : Int) + 1 ≤ k - (m - s)) ∧ (b % 2 = 1 → (b : Int) + 1 ≤ k - (m - s) + 2) := by
  have hc := run_countdown init k b s hrun hend
  have edge := (left_edge init m hm hz s).2
  -- a cell reading 1 at step `s` is not left of the leftmost 1
  have inside : ∀ x : Int, evolve init s x = true → ¬ x < m - s := fun x hx hlt => by
    have h0 := edge x hlt
    rw [hx] at h0
    exact absurd h0 (by decide)
  constructor
  · intro hb
    have h1 : evolve init s (k - 1 - (b : Int)) = true := by
      show leftOf init s k b = true
      rw [hc.2]
      show (!(b % 2 == 1)) = true
      rw [hb]; rfl
    have := inside _ h1
    omega
  · intro hb
    by_cases hb1 : b = 1
    · subst hb1
      have h0 : evolve init (s + 0) k = true := hrun 0 (by omega)
      rw [Nat.add_zero] at h0
      have := inside _ h0
      omega
    · have h1 : evolve init s (k - 1 - ((b - 2 : Nat) : Int)) = true := by
        show leftOf init s k (b - 2) = true
        rw [hc.1 (b - 2) (by omega)]
        show ((b - 2) % 2 == 1) = true
        rw [show (b - 2) % 2 = 1 by omega]; rfl
      have := inside _ h1
      omega

/-- In the orbit of a row with a leftmost 1, no column reads 1 from some step on: while it reads 1, each step back
the cells left of it agree with domain B on one more cell, so they would agree with it everywhere, but they read 0
left of the leftmost 1. -/
theorem no_ones_column (init : Int → Bool) (m : Int) (hm : init m = true) (hz : ∀ x : Int, x < m → init x = false)
    (k : Int) (T : Nat) (h : ∀ t : Nat, T ≤ t → evolve init t k = true) : False := by
  have agree : ∀ n : Nat, ∀ t : Nat, T ≤ t → ∀ j, j < n → leftOf init t k j = domainB j := by
    intro n
    induction n with
    | zero => intro t _ j hj; exact absurd hj (Nat.not_lt_zero j)
    | succ n ih =>
      intro t ht
      have hs := h t ht
      have h0 : leftOf init t k 0 = false := by
        show evolve init t (k - 1 - ((0 : Nat) : Int)) = false
        rw [show k - 1 - ((0 : Nat) : Int) = k - 1 by omega, left_of_one init k t hs, h (t + 1) (by omega)]
        rfl
      have hk : ∀ j, j < n → heldOne (leftOf init t k) j = domainB j := fun j hj => by
        rw [← congrFun (left_heldOne init k t hs) j]; exact ih (t + 1) (by omega) j hj
      exact heldOne_agree_back (leftOf init t k) h0 n hk
  -- an odd cell of domain B past the leftmost 1 reads 1 there, but the row reads 0
  obtain ⟨j0, hj0⟩ : ∃ j0 : Nat, j0 = 2 * (k - m + T).toNat + 1 := ⟨_, rfl⟩
  have hj := agree (j0 + 1) T (Nat.le_refl T) j0 (by omega)
  have hzero : evolve init T (k - 1 - (j0 : Int)) = false := (left_edge init m hm hz T).2 _ (by omega)
  have hodd : domainB j0 = true := by
    show (j0 % 2 == 1) = true
    rw [show j0 % 2 = 1 by omega]; rfl
  have hj' : evolve init T (k - 1 - (j0 : Int)) = domainB j0 := hj
  rw [hzero, hodd] at hj'
  exact Bool.false_ne_true hj'

/-- The single seed's center column, in particular, does not read 1 from some step on. -/
theorem single_no_ones (T : Nat) (h : ∀ t : Nat, T ≤ t → evolve single t 0 = true) : False :=
  no_ones_column single 0 rfl (fun x hx => decide_eq_false (by omega)) 0 T h

/-- A spot check: the single seed's center column reads 1 at steps 3, 4, 5 and 0 at 6, and at step 3 the cells left
of the center read 0 1 and then not 0, as domain B does on exactly two cells. -/
theorem run_countdown_spot :
    (List.range 4).map (fun i => evolve single (3 + i) 0) = [true, true, true, false] ∧
      (List.range 3).map (fun j => leftOf single 3 0 j) = [false, true, true] := by decide

/-- Official form: the prize's center column does not read 1 from some step on. -/
theorem center_not_eventually_ones (T : Nat) (h : ∀ t : Nat, T ≤ t → Rule30Prize.center t = true) : False :=
  single_no_ones T fun t ht => (evolve_single_center t).trans (h t ht)

end Rule30Open
