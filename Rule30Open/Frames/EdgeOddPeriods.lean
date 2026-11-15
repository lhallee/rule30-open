module

public import Ruliology.CellularAutomata.Rule30FrozenRuler

/-!
# The right-edge map has no periodic point of odd period but 0

The kit's edge map `Rule30FrozenRuler.T` is the 2-adic map `Φ(y) = y ⊕ (2y ∨ 4y)` on bit sequences, and
`Rule30FrozenRuler.iter n` is its `n`-th iterate.

* `fixed_point_eq_zero`: **the only fixed point of `T` is the white sequence.** The equation at bit `k + 1` forces bit
  `k` white, bit by bit, with no induction.
* `col_const_of_odd`: a Boolean sequence that flips by a constant `g` at every step and returns after an odd number of
  steps is constant (`g = false`).
* `fixed_of_odd_period`: **if `iter L c = c` with `L` odd, then `T c = c`.** By strong induction on the bit, every
  column `i ↦ iter i c k` is constant: its two inputs below are constant, so it flips by a constant at every step, and
  `col_const_of_odd` applies.
* `odd_period_eq_zero`: so `iter L c = c` with `L` odd forces `c` white.
* `col_period_of_odd`: a sequence that flips by a `p`-periodic input at every step and returns after `p * q` steps,
  `q` odd, has period `p`.
* `pow_two_period`: **if `iter (2 ^ a * q) c = c` with `q` odd, then `iter (2 ^ a) c = c`**, so the least period of
  every periodic point is a power of two. By strong induction on the bit, every column has period `2 ^ a`: its inputs
  do, so over each block of `2 ^ a` steps it flips by one fixed parity, and `col_period_of_odd` applies.
-/

@[expose] public section

namespace Rule30Open.Frames.EdgeOddPeriods

open Ruliology.CellularAutomata.Rule30FrozenRuler

theorem fixed_point_eq_zero (c : Nat → Bool) (h : T c = c) : ∀ k, c k = false := by
  intro k
  cases k with
  | zero =>
    have h1 := congrFun h 1
    simp only [T] at h1
    cases h0 : c 0 <;> cases h1' : c 1 <;> simp_all
  | succ j =>
    have h2 := congrFun h (j + 2)
    simp only [T] at h2
    cases a : c (j + 2) <;> cases b : c (j + 1) <;> cases d : c j <;> simp_all

theorem col_const_of_odd (f : Nat → Bool) (g : Bool) (L : Nat) (hL : L % 2 = 1)
    (hstep : ∀ i, f (i + 1) = xor (f i) g) (hper : f L = f 0) : ∀ i, f i = f 0 := by
  have even : ∀ m, f (2 * m) = f 0 := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      have e : 2 * (m + 1) = 2 * m + 1 + 1 := by omega
      rw [e, hstep, hstep, ih]
      cases f 0 <;> cases g <;> rfl
  have hg : g = false := by
    have e : L = 2 * (L / 2) + 1 := by omega
    have := hper
    rw [e, hstep, even] at this
    revert this
    generalize f 0 = a
    cases g <;> cases a <;> decide
  intro i
  induction i with
  | zero => rfl
  | succ i ih => rw [hstep, ih, hg]; cases f 0 <;> rfl

theorem fixed_of_odd_period (c : Nat → Bool) (L : Nat) (hL : L % 2 = 1) (h : iter L c = c) :
    T c = c := by
  have col : ∀ k, ∀ i, iter i c k = c k := by
    intro k
    induction k using Nat.strongRecOn with
    | _ k ih =>
      -- the step of column `k` and the constant it flips by
      have key : ∃ g : Bool, ∀ i, iter (i + 1) c k = xor (iter i c k) g := by
        match k, ih with
        | 0, _ => exact ⟨false, fun i => by show T (iter i c) 0 = _; simp [T]⟩
        | 1, ih =>
          refine ⟨c 0, fun i => ?_⟩
          show T (iter i c) 1 = _
          simp only [T]
          rw [ih 0 (by omega) i]
        | j + 2, ih =>
          refine ⟨c (j + 1) || c j, fun i => ?_⟩
          show T (iter i c) (j + 2) = _
          simp only [T]
          rw [ih (j + 1) (by omega) i, ih j (by omega) i]
      obtain ⟨g, hg⟩ := key
      have hper : iter L c k = iter 0 c k := by rw [h]; rfl
      intro i
      have := col_const_of_odd (fun i => iter i c k) g L hL hg hper i
      exact this
  funext k
  exact col k 1

theorem odd_period_eq_zero (c : Nat → Bool) (L : Nat) (hL : L % 2 = 1) (h : iter L c = c) :
    ∀ k, c k = false :=
  fixed_point_eq_zero c (fixed_of_odd_period c L hL h)

theorem col_period_of_odd (f g : Nat → Bool) (p q : Nat) (hq : q % 2 = 1)
    (hstep : ∀ i, f (i + 1) = xor (f i) (g i)) (hg : ∀ i, g (i + p) = g i) (hper : f (p * q) = f 0) :
    ∀ i, f (i + p) = f i := by
  have hconst : ∀ i, xor (f (i + p)) (f i) = xor (f p) (f 0) := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have e : i + 1 + p = (i + p) + 1 := by omega
      rw [e, hstep, hstep, hg]
      rw [← ih]
      generalize f (i + p) = A
      generalize f i = B
      generalize g i = G
      cases A <;> cases B <;> cases G <;> rfl
  have shift : ∀ i, f (i + p) = xor (f i) (xor (f p) (f 0)) := by
    intro i
    rw [← hconst i]
    generalize f (i + p) = A
    generalize f i = B
    cases A <;> cases B <;> rfl
  have even : ∀ m, f (p * (2 * m)) = f 0 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have e : p * (2 * (m + 1)) = p * (2 * m) + p + p := by
        rw [Nat.mul_add, Nat.mul_add]; omega
      rw [e, shift, shift, ih]
      generalize f 0 = A
      generalize xor (f p) A = S
      cases A <;> cases S <;> rfl
  have hs : xor (f p) (f 0) = false := by
    have e : p * q = p * (2 * (q / 2)) + p := by
      have : q = 2 * (q / 2) + 1 := by omega
      conv => lhs; rw [this]
      rw [Nat.mul_add, Nat.mul_one]
    have := hper
    rw [e, shift, even] at this
    revert this
    generalize f 0 = A
    generalize xor (f p) A = S
    cases A <;> cases S <;> decide
  intro i
  rw [shift, hs]
  cases f i <;> rfl

theorem pow_two_period (c : Nat → Bool) (a q : Nat) (hq : q % 2 = 1) (h : iter (2 ^ a * q) c = c) :
    iter (2 ^ a) c = c := by
  have col : ∀ k, ∀ i, iter (i + 2 ^ a) c k = iter i c k := by
    intro k
    induction k using Nat.strongRecOn with
    | _ k ih =>
      have key : ∃ g : Nat → Bool, (∀ i, g (i + 2 ^ a) = g i) ∧
          ∀ i, iter (i + 1) c k = xor (iter i c k) (g i) := by
        match k, ih with
        | 0, _ => exact ⟨fun _ => false, fun _ => rfl, fun i => by show T (iter i c) 0 = _; simp [T]⟩
        | 1, ih =>
          refine ⟨fun i => iter i c 0, fun i => ih 0 (by omega) i, fun i => ?_⟩
          show T (iter i c) 1 = _
          simp only [T]
        | j + 2, ih =>
          refine ⟨fun i => iter i c (j + 1) || iter i c j, fun i => ?_, fun i => ?_⟩
          · show (iter (i + 2 ^ a) c (j + 1) || iter (i + 2 ^ a) c j) = _
            rw [ih (j + 1) (by omega) i, ih j (by omega) i]
          · show T (iter i c) (j + 2) = _
            simp only [T]
      obtain ⟨g, hgp, hg⟩ := key
      have hper : iter (2 ^ a * q) c k = iter 0 c k := by rw [h]; rfl
      exact col_period_of_odd (fun i => iter i c k) g (2 ^ a) q hq hg hgp hper
  funext k
  have := col k 0
  rw [Nat.zero_add] at this
  exact this

end Rule30Open.Frames.EdgeOddPeriods
