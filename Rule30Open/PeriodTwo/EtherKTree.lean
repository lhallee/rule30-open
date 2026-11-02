module

public import Rule30Open.PeriodTwo.NoKTails16

/-!
# Every point of `K` whose tail from cell 28 on is the ether has a defect below cell 28

The ether is the cycle of four states of the held map on a ring of seven cells (`eth` of `EtherCensus`). For a half `u`
whose cells from `p` on are the ether at an alignment `(a, o)`, the defect `defect u a o t j` is cell `j` of
`heldOrbit u t` xor the ether at phase `a + t`. `EtherCensus16` bounds the defect of every such half with `p ≤ 16`, in
`K` or not. Here the condition of `K` is used: if `p ≤ 28` and `u` is in `K` (`InK`), the cells of `heldOrbit u t`
from 28 on are the ether at every step (`ether_k_tail_clear`), so the orbit of `u` and its itinerary are eventually
periodic (`ether_k_tail_eventually_periodic`, `ether_k_tail_itinerary`). This is conjecture (R) of the shift model for
the points of `K` whose tail from cell 28 on is the ether.

* **The tree of `K`.** `treeWith` of `NoKTails16` walks the heads of 28 cells under the ether: both values at an even
  cell, the one value at an odd cell `d` that keeps bit 0 of `heldNat^d` odd. A head off the tree breaks `K` at an odd
  step below 28 (`treeWith_sound`), so only its `2^14` leaves at each alignment need a test.
* **The test at a leaf** (`etherLeaf`, sound by `etherLeaf_sound`). Either `breakRun 32` of `NoKTails` finds an odd
  step below 64 at which bit 0 is 0, so `u` is not in `K`, or `runHead` of `EtherCensus` settles the defect of the head
  (a closed strip of 13 cells or a repeat) with every defect cell below 28, so the defect never reaches cell 28.
* **The census.** `etherTreeOK` runs the tree with this test at one alignment as one kernel computation; the 28
  alignments pass (`ktree`).

The natural-language argument is `EtherKTree.md`, beside this file.
-/

@[expose] public section

-- Sequential elaboration: the kernel checks would otherwise run in parallel and stack their memory.
set_option Elab.async false

namespace Rule30Open

/-! ### The test at a leaf -/

/-- The ether at the alignment `(a, o)` in the cells `H, …, 63`, and 0 below: bit `j` is the cell `j`. -/
def etherTail (H a o : Nat) : Nat := natOf (fun j => decide (H ≤ j) && eth a (j + o)) 64

/-- The test at a leaf `N` of the tree, which holds a head in the cells `0, …, H - 1` and the ether at `(a, o)` in
the cells `H, …, 63`: `breakRun R` finds a break of `K`, or `runHead` settles the defect of the head,
`(N xor the ether) mod 2^H`, with the bound `L` and `fuel` rounds. -/
def etherLeaf (R H L fuel a o : Nat) (N : Nat) : Bool :=
  breakRun R N || letN (Nat.mod (Nat.xor N (bgL a o)) (Nat.pow 2 H)) fun n =>
    runHead o L (bgL a o) (bgL (a + 1) o) (bgL (a + 2) o) (bgL (a + 3) o) (closedSet a) fuel 0 n n 0 4

/-- The tree of `K` over the heads of `H` cells under the ether at `(a, o)`, with `etherLeaf` at the leaves. -/
def etherTreeOK (R H L fuel a o : Nat) : Bool := treeWith (etherLeaf R H L fuel a o) H 0 (etherTail H a o)

private theorem xor_self_false (x : Bool) : xor x x = false := by cases x <;> rfl

/-- **The test at a leaf is sound**: if `u` has the ether at `(a, o)` from cell `H` on, agrees with a leaf `N` that
passes `etherLeaf` on the cells `0, …, 63`, and is in `K`, then its defect is clear from cell `L` on at every step. -/
theorem etherLeaf_sound (R H L fuel a o : Nat) (hR : 2 * R ≤ 64) (hH : H ≤ 64) (hHL : H ≤ L) (hL : L ≤ 126)
    (u : Nat → Bool) (hu : ∀ j, H ≤ j → u j = eth a (j + o)) (N : Nat) (h : etherLeaf R H L fuel a o N = true)
    (hN : ∀ i, i < 64 → N.testBit i = u i) (hK : InK u) : ∀ k j, L ≤ j → defect u a o k j = false := by
  unfold etherLeaf at h
  rw [Bool.or_eq_true, letN_eq] at h
  rcases h with hb | h
  · exact absurd hK (not_inK_of_breakRun R N hR u hN hb)
  · -- the defect of the head at step 0
    have he : Enc u a o 0 ((N ^^^ bgL a o) % 2 ^ H) := by
      intro j
      unfold defect
      rw [show heldOrbit u 0 j = u j from rfl, Nat.add_zero, Nat.testBit_mod_two_pow, Nat.testBit_xor]
      by_cases hj : j < H
      · rw [decide_eq_true hj, Bool.true_and, hN j (by omega), bgL_testBit a o j (by omega)]
      · rw [decide_eq_false hj, Bool.false_and, hu j (by omega), xor_self_false]
    refine runHead_sound u a o L hL fuel 0 _ _ 0 4 h rfl rfl (Nat.le_refl 0) he he ?_
    intro k j hk hj
    rw [show k = 0 by omega]
    unfold defect
    rw [show heldOrbit u 0 j = u j from rfl, Nat.add_zero, hu j (by omega), xor_self_false]

/-- **A census at one alignment bounds every point of `K` with the ether there from cell `H` on.** -/
theorem clear_of_etherTree (R H L fuel a o : Nat) (hR : 2 * R ≤ 64) (hH : H ≤ 64) (hHL : H ≤ L) (hL : L ≤ 126)
    (hT : etherTreeOK R H L fuel a o = true) (u : Nat → Bool) (hu : ∀ j, H ≤ j → u j = eth a (j + o))
    (hK : InK u) : ∀ k j, L ≤ j → defect u a o k j = false := by
  refine treeWith_sound (etherLeaf R H L fuel a o) H hH u _
    (fun N hl hN hK' => etherLeaf_sound R H L fuel a o hR hH hHL hL u hu N hl hN hK') H 0 _ (Nat.zero_add H) hT
    (fun i hi hor => ?_) (fun i _ hi => ?_) hK
  · unfold etherTail
    rw [natOf_testBit]
    rcases hor with hor | hor
    · omega
    · rw [hu i hor]; simp [hi, hor]
  · unfold etherTail
    rw [natOf_testBit]
    simp [show ¬ H ≤ i by omega]

/-! ### The census -/

theorem ktree_0_0 : etherTreeOK 32 28 28 16 0 0 = true := by
  decide +kernel

theorem ktree_0_1 : etherTreeOK 32 28 28 16 0 1 = true := by
  decide +kernel

theorem ktree_0_2 : etherTreeOK 32 28 28 16 0 2 = true := by
  decide +kernel

theorem ktree_0_3 : etherTreeOK 32 28 28 16 0 3 = true := by
  decide +kernel

theorem ktree_0_4 : etherTreeOK 32 28 28 16 0 4 = true := by
  decide +kernel

theorem ktree_0_5 : etherTreeOK 32 28 28 16 0 5 = true := by
  decide +kernel

theorem ktree_0_6 : etherTreeOK 32 28 28 16 0 6 = true := by
  decide +kernel

theorem ktree_1_0 : etherTreeOK 32 28 28 16 1 0 = true := by
  decide +kernel

theorem ktree_1_1 : etherTreeOK 32 28 28 16 1 1 = true := by
  decide +kernel

theorem ktree_1_2 : etherTreeOK 32 28 28 16 1 2 = true := by
  decide +kernel

theorem ktree_1_3 : etherTreeOK 32 28 28 16 1 3 = true := by
  decide +kernel

theorem ktree_1_4 : etherTreeOK 32 28 28 16 1 4 = true := by
  decide +kernel

theorem ktree_1_5 : etherTreeOK 32 28 28 16 1 5 = true := by
  decide +kernel

theorem ktree_1_6 : etherTreeOK 32 28 28 16 1 6 = true := by
  decide +kernel

theorem ktree_2_0 : etherTreeOK 32 28 28 16 2 0 = true := by
  decide +kernel

theorem ktree_2_1 : etherTreeOK 32 28 28 16 2 1 = true := by
  decide +kernel

theorem ktree_2_2 : etherTreeOK 32 28 28 16 2 2 = true := by
  decide +kernel

theorem ktree_2_3 : etherTreeOK 32 28 28 16 2 3 = true := by
  decide +kernel

theorem ktree_2_4 : etherTreeOK 32 28 28 16 2 4 = true := by
  decide +kernel

theorem ktree_2_5 : etherTreeOK 32 28 28 16 2 5 = true := by
  decide +kernel

theorem ktree_2_6 : etherTreeOK 32 28 28 16 2 6 = true := by
  decide +kernel

theorem ktree_3_0 : etherTreeOK 32 28 28 16 3 0 = true := by
  decide +kernel

theorem ktree_3_1 : etherTreeOK 32 28 28 16 3 1 = true := by
  decide +kernel

theorem ktree_3_2 : etherTreeOK 32 28 28 16 3 2 = true := by
  decide +kernel

theorem ktree_3_3 : etherTreeOK 32 28 28 16 3 3 = true := by
  decide +kernel

theorem ktree_3_4 : etherTreeOK 32 28 28 16 3 4 = true := by
  decide +kernel

theorem ktree_3_5 : etherTreeOK 32 28 28 16 3 5 = true := by
  decide +kernel

theorem ktree_3_6 : etherTreeOK 32 28 28 16 3 6 = true := by
  decide +kernel

theorem ktree (a o : Nat) (ha : a < 4) (ho : o < 7) : etherTreeOK 32 28 28 16 a o = true :=
  match a, o, ha, ho with
  | 0, 0, _, _ => ktree_0_0
  | 0, 1, _, _ => ktree_0_1
  | 0, 2, _, _ => ktree_0_2
  | 0, 3, _, _ => ktree_0_3
  | 0, 4, _, _ => ktree_0_4
  | 0, 5, _, _ => ktree_0_5
  | 0, 6, _, _ => ktree_0_6
  | 1, 0, _, _ => ktree_1_0
  | 1, 1, _, _ => ktree_1_1
  | 1, 2, _, _ => ktree_1_2
  | 1, 3, _, _ => ktree_1_3
  | 1, 4, _, _ => ktree_1_4
  | 1, 5, _, _ => ktree_1_5
  | 1, 6, _, _ => ktree_1_6
  | 2, 0, _, _ => ktree_2_0
  | 2, 1, _, _ => ktree_2_1
  | 2, 2, _, _ => ktree_2_2
  | 2, 3, _, _ => ktree_2_3
  | 2, 4, _, _ => ktree_2_4
  | 2, 5, _, _ => ktree_2_5
  | 2, 6, _, _ => ktree_2_6
  | 3, 0, _, _ => ktree_3_0
  | 3, 1, _, _ => ktree_3_1
  | 3, 2, _, _ => ktree_3_2
  | 3, 3, _, _ => ktree_3_3
  | 3, 4, _, _ => ktree_3_4
  | 3, 5, _, _ => ktree_3_5
  | 3, 6, _, _ => ktree_3_6
  | a + 4, _, ha, _ => absurd ha (by omega)
  | _, o + 7, _, ho => absurd ho (by omega)


/-! ### Every point of `K` with the ether from cell 28 on settles -/

/-- **The defect of every point of `K` whose tail from cell 28 on is the ether stays below cell 28.** If `u` is in `K`
and its cells from `p ≤ 28` on are the ether at the alignment `(a, o)`, then at every step `t` the cells from 28 on
are the ether at phase `a + t`. -/
theorem ether_k_tail_clear (u : Nat → Bool) (a o p : Nat) (hp : p ≤ 28)
    (hu : ∀ j, p ≤ j → u j = eth a (j + o)) (hK : InK u) :
    ∀ t j, 28 ≤ j → heldOrbit u t j = eth (a + t) (j + o) := by
  have hu' : ∀ j, 28 ≤ j → u j = eth (a % 4) (j + o % 7) := fun j hj => by
    rw [hu j (by omega)]; exact eth_congr (by omega) (by omega)
  have hc := clear_of_etherTree 32 28 28 16 (a % 4) (o % 7) (by decide) (by decide) (by decide) (by decide)
    (ktree (a % 4) (o % 7) (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))) u hu' hK
  intro t j hj
  rw [heldOrbit_eq_defect u (a % 4) (o % 7) t j, hc t j hj, Bool.false_xor]
  exact eth_congr (by omega) (by omega)

/-- **Every point of `K` whose tail from cell 28 on is the ether has an eventually periodic orbit.** -/
theorem ether_k_tail_eventually_periodic (u : Nat → Bool) (a o p : Nat) (hp : p ≤ 28)
    (hu : ∀ j, p ≤ j → u j = eth a (j + o)) (hK : InK u) :
    ∃ T P, 0 < P ∧ ∀ t, T ≤ t → heldOrbit u (t + P) = heldOrbit u t := by
  refine eventually_periodic_of_clear (a := a) (o := o) (L := 28) fun t j hj => ?_
  unfold defect
  rw [ether_k_tail_clear u a o p hp hu hK t j hj]
  cases eth (a + t) (j + o) <;> rfl

/-- **Conjecture (R) for the points of `K` whose tail from cell 28 on is the ether**: every 2-adic integer in `InK`
whose bits from `p ≤ 28` on are the ether at one of its alignments has an eventually periodic itinerary. -/
theorem ether_k_tail_itinerary (u : Nat → Bool) (a o p : Nat) (hp : p ≤ 28)
    (hu : ∀ j, p ≤ j → u j = eth a (j + o)) (hK : InK u) :
    ∃ pre n, 0 < n ∧ ∀ s, pre ≤ s → itinerary u (s + n) = itinerary u s := by
  obtain ⟨T, P, hP, h⟩ := ether_k_tail_eventually_periodic u a o p hp hu hK
  exact itinerary_of_eventually_periodic hP h

end Rule30Open
