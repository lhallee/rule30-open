module

public import Rule30Open.PeriodTwo.EtherKTree

/-!
# Every point of `K` whose tail from cell 32 on is the ether has a defect below cell 39

`EtherKTree` proves that the defect of a point of `K` (`InK`) whose tail from cell 28 on is the ether (`eth` of
`EtherCensus`) never reaches cell 28. This module runs the same census, `etherTreeOK` with `etherLeaf` at the leaves, on
the heads of 32 cells with the bound 39, so the cells of `heldOrbit u t` from 39 on are the ether at every step for every
point of `K` with the ether from cell 32 on (`ether_k_tail_clear32`), and the orbit and the itinerary of such a point are
eventually periodic (`ether_k_tail_eventually_periodic32`, `ether_k_tail_itinerary32`).

* **The cut.** The tree of one alignment, `2^16` leaves, is too large for one kernel check under 4.5 GB, so it is cut at
  cell 6: `treeWith_even_ok` and `treeWith_odd_ok` take one step of `treeWith` at an even and an odd cell, and the eight
  subtrees at cell 6 are checked one by one (`ktree32_a_o_k`), then joined by the walk over the cells 0 to 5
  (`ktree32_a_o`).
* **The census.** The 28 alignments pass (`ktree32`), and `clear_of_etherTree` of `EtherKTree` gives the theorems.

The natural-language argument is `EtherKTree32.md`, beside this file.
-/

@[expose] public section

-- Sequential elaboration: the kernel checks would otherwise run in parallel and stack their memory.
set_option Elab.async false

namespace Rule30Open

/-! ### One step of the tree -/

/-- At an even cell `d` the tree passes when both subtrees, with cell `d` at 0 and at 1, pass. -/
theorem treeWith_even_ok (leaf : Nat → Bool) (m d n n' : Nat) (hd : d % 2 = 0) (hn : n' = n ||| 2 ^ d)
    (h0 : treeWith leaf m (d + 1) n = true) (h1 : treeWith leaf m (d + 1) n' = true) :
    treeWith leaf (m + 1) d n = true := by
  subst hn
  rw [treeWith_succ, hd]
  simp [h0, h1]

/-- At an odd cell `d` the tree passes when the subtree with the value of cell `d` that keeps bit 0 of `heldNat^d` odd
passes. -/
theorem treeWith_odd_ok (leaf : Nat → Bool) (m d n n' : Nat) (hd : d % 2 = 1)
    (hn : n' = cond (colRaw d n) n (n ||| 2 ^ d)) (h : treeWith leaf m (d + 1) n' = true) :
    treeWith leaf (m + 1) d n = true := by
  subst hn
  rw [treeWith_succ, hd]
  cases hc : colRaw d n <;> simpa [hc] using h

/-! ### The census -/

theorem ktree32_0_0_0 : treeWith (etherLeaf 32 32 39 16 0 0) 26 6 4647998506626187306 = true := by
  decide +kernel

theorem ktree32_0_0_1 : treeWith (etherLeaf 32 32 39 16 0 0) 26 6 4647998506626187322 = true := by
  decide +kernel

theorem ktree32_0_0_2 : treeWith (etherLeaf 32 32 39 16 0 0) 26 6 4647998506626187302 = true := by
  decide +kernel

theorem ktree32_0_0_3 : treeWith (etherLeaf 32 32 39 16 0 0) 26 6 4647998506626187286 = true := by
  decide +kernel

theorem ktree32_0_0_4 : treeWith (etherLeaf 32 32 39 16 0 0) 26 6 4647998506626187265 = true := by
  decide +kernel

theorem ktree32_0_0_5 : treeWith (etherLeaf 32 32 39 16 0 0) 26 6 4647998506626187313 = true := by
  decide +kernel

theorem ktree32_0_0_6 : treeWith (etherLeaf 32 32 39 16 0 0) 26 6 4647998506626187301 = true := by
  decide +kernel

theorem ktree32_0_0_7 : treeWith (etherLeaf 32 32 39 16 0 0) 26 6 4647998506626187285 = true := by
  decide +kernel

theorem ktree32_0_0 : etherTreeOK 32 32 39 16 0 0 = true := by
  unfold etherTreeOK
  rw [show etherTail 32 0 0 = 4647998506626187264 by decide +kernel]
  exact (treeWith_even_ok _ 31 0 4647998506626187264 4647998506626187265 (by decide) (by decide) (treeWith_odd_ok _ 30 1 4647998506626187264 4647998506626187266 (by decide) (by decide +kernel) (treeWith_even_ok _ 29 2 4647998506626187266 4647998506626187270 (by decide) (by decide) (treeWith_odd_ok _ 28 3 4647998506626187266 4647998506626187274 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 4647998506626187274 4647998506626187290 (by decide) (by decide) (treeWith_odd_ok _ 26 5 4647998506626187274 4647998506626187306 (by decide) (by decide +kernel) ktree32_0_0_0) (treeWith_odd_ok _ 26 5 4647998506626187290 4647998506626187322 (by decide) (by decide +kernel) ktree32_0_0_1))) (treeWith_odd_ok _ 28 3 4647998506626187270 4647998506626187270 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 4647998506626187270 4647998506626187286 (by decide) (by decide) (treeWith_odd_ok _ 26 5 4647998506626187270 4647998506626187302 (by decide) (by decide +kernel) ktree32_0_0_2) (treeWith_odd_ok _ 26 5 4647998506626187286 4647998506626187286 (by decide) (by decide +kernel) ktree32_0_0_3))))) (treeWith_odd_ok _ 30 1 4647998506626187265 4647998506626187265 (by decide) (by decide +kernel) (treeWith_even_ok _ 29 2 4647998506626187265 4647998506626187269 (by decide) (by decide) (treeWith_odd_ok _ 28 3 4647998506626187265 4647998506626187265 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 4647998506626187265 4647998506626187281 (by decide) (by decide) (treeWith_odd_ok _ 26 5 4647998506626187265 4647998506626187265 (by decide) (by decide +kernel) ktree32_0_0_4) (treeWith_odd_ok _ 26 5 4647998506626187281 4647998506626187313 (by decide) (by decide +kernel) ktree32_0_0_5))) (treeWith_odd_ok _ 28 3 4647998506626187269 4647998506626187269 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 4647998506626187269 4647998506626187285 (by decide) (by decide) (treeWith_odd_ok _ 26 5 4647998506626187269 4647998506626187301 (by decide) (by decide +kernel) ktree32_0_0_6) (treeWith_odd_ok _ 26 5 4647998506626187285 4647998506626187285 (by decide) (by decide +kernel) ktree32_0_0_7))))))

theorem ktree32_0_1_0 : treeWith (etherLeaf 32 32 39 16 0 1) 26 6 2323999253313093674 = true := by
  decide +kernel

theorem ktree32_0_1_1 : treeWith (etherLeaf 32 32 39 16 0 1) 26 6 2323999253313093690 = true := by
  decide +kernel

theorem ktree32_0_1_2 : treeWith (etherLeaf 32 32 39 16 0 1) 26 6 2323999253313093670 = true := by
  decide +kernel

theorem ktree32_0_1_3 : treeWith (etherLeaf 32 32 39 16 0 1) 26 6 2323999253313093654 = true := by
  decide +kernel

theorem ktree32_0_1_4 : treeWith (etherLeaf 32 32 39 16 0 1) 26 6 2323999253313093633 = true := by
  decide +kernel

theorem ktree32_0_1_5 : treeWith (etherLeaf 32 32 39 16 0 1) 26 6 2323999253313093681 = true := by
  decide +kernel

theorem ktree32_0_1_6 : treeWith (etherLeaf 32 32 39 16 0 1) 26 6 2323999253313093669 = true := by
  decide +kernel

theorem ktree32_0_1_7 : treeWith (etherLeaf 32 32 39 16 0 1) 26 6 2323999253313093653 = true := by
  decide +kernel

theorem ktree32_0_1 : etherTreeOK 32 32 39 16 0 1 = true := by
  unfold etherTreeOK
  rw [show etherTail 32 0 1 = 2323999253313093632 by decide +kernel]
  exact (treeWith_even_ok _ 31 0 2323999253313093632 2323999253313093633 (by decide) (by decide) (treeWith_odd_ok _ 30 1 2323999253313093632 2323999253313093634 (by decide) (by decide +kernel) (treeWith_even_ok _ 29 2 2323999253313093634 2323999253313093638 (by decide) (by decide) (treeWith_odd_ok _ 28 3 2323999253313093634 2323999253313093642 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 2323999253313093642 2323999253313093658 (by decide) (by decide) (treeWith_odd_ok _ 26 5 2323999253313093642 2323999253313093674 (by decide) (by decide +kernel) ktree32_0_1_0) (treeWith_odd_ok _ 26 5 2323999253313093658 2323999253313093690 (by decide) (by decide +kernel) ktree32_0_1_1))) (treeWith_odd_ok _ 28 3 2323999253313093638 2323999253313093638 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 2323999253313093638 2323999253313093654 (by decide) (by decide) (treeWith_odd_ok _ 26 5 2323999253313093638 2323999253313093670 (by decide) (by decide +kernel) ktree32_0_1_2) (treeWith_odd_ok _ 26 5 2323999253313093654 2323999253313093654 (by decide) (by decide +kernel) ktree32_0_1_3))))) (treeWith_odd_ok _ 30 1 2323999253313093633 2323999253313093633 (by decide) (by decide +kernel) (treeWith_even_ok _ 29 2 2323999253313093633 2323999253313093637 (by decide) (by decide) (treeWith_odd_ok _ 28 3 2323999253313093633 2323999253313093633 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 2323999253313093633 2323999253313093649 (by decide) (by decide) (treeWith_odd_ok _ 26 5 2323999253313093633 2323999253313093633 (by decide) (by decide +kernel) ktree32_0_1_4) (treeWith_odd_ok _ 26 5 2323999253313093649 2323999253313093681 (by decide) (by decide +kernel) ktree32_0_1_5))) (treeWith_odd_ok _ 28 3 2323999253313093637 2323999253313093637 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 2323999253313093637 2323999253313093653 (by decide) (by decide) (treeWith_odd_ok _ 26 5 2323999253313093637 2323999253313093669 (by decide) (by decide +kernel) ktree32_0_1_6) (treeWith_odd_ok _ 26 5 2323999253313093653 2323999253313093653 (by decide) (by decide +kernel) ktree32_0_1_7))))))

theorem ktree32_0_2_0 : treeWith (etherLeaf 32 32 39 16 0 2) 26 6 1161999626656546858 = true := by
  decide +kernel

theorem ktree32_0_2_1 : treeWith (etherLeaf 32 32 39 16 0 2) 26 6 1161999626656546874 = true := by
  decide +kernel

theorem ktree32_0_2_2 : treeWith (etherLeaf 32 32 39 16 0 2) 26 6 1161999626656546854 = true := by
  decide +kernel

theorem ktree32_0_2_3 : treeWith (etherLeaf 32 32 39 16 0 2) 26 6 1161999626656546838 = true := by
  decide +kernel

theorem ktree32_0_2_4 : treeWith (etherLeaf 32 32 39 16 0 2) 26 6 1161999626656546817 = true := by
  decide +kernel

theorem ktree32_0_2_5 : treeWith (etherLeaf 32 32 39 16 0 2) 26 6 1161999626656546865 = true := by
  decide +kernel

theorem ktree32_0_2_6 : treeWith (etherLeaf 32 32 39 16 0 2) 26 6 1161999626656546853 = true := by
  decide +kernel

theorem ktree32_0_2_7 : treeWith (etherLeaf 32 32 39 16 0 2) 26 6 1161999626656546837 = true := by
  decide +kernel

theorem ktree32_0_2 : etherTreeOK 32 32 39 16 0 2 = true := by
  unfold etherTreeOK
  rw [show etherTail 32 0 2 = 1161999626656546816 by decide +kernel]
  exact (treeWith_even_ok _ 31 0 1161999626656546816 1161999626656546817 (by decide) (by decide) (treeWith_odd_ok _ 30 1 1161999626656546816 1161999626656546818 (by decide) (by decide +kernel) (treeWith_even_ok _ 29 2 1161999626656546818 1161999626656546822 (by decide) (by decide) (treeWith_odd_ok _ 28 3 1161999626656546818 1161999626656546826 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 1161999626656546826 1161999626656546842 (by decide) (by decide) (treeWith_odd_ok _ 26 5 1161999626656546826 1161999626656546858 (by decide) (by decide +kernel) ktree32_0_2_0) (treeWith_odd_ok _ 26 5 1161999626656546842 1161999626656546874 (by decide) (by decide +kernel) ktree32_0_2_1))) (treeWith_odd_ok _ 28 3 1161999626656546822 1161999626656546822 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 1161999626656546822 1161999626656546838 (by decide) (by decide) (treeWith_odd_ok _ 26 5 1161999626656546822 1161999626656546854 (by decide) (by decide +kernel) ktree32_0_2_2) (treeWith_odd_ok _ 26 5 1161999626656546838 1161999626656546838 (by decide) (by decide +kernel) ktree32_0_2_3))))) (treeWith_odd_ok _ 30 1 1161999626656546817 1161999626656546817 (by decide) (by decide +kernel) (treeWith_even_ok _ 29 2 1161999626656546817 1161999626656546821 (by decide) (by decide) (treeWith_odd_ok _ 28 3 1161999626656546817 1161999626656546817 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 1161999626656546817 1161999626656546833 (by decide) (by decide) (treeWith_odd_ok _ 26 5 1161999626656546817 1161999626656546817 (by decide) (by decide +kernel) ktree32_0_2_4) (treeWith_odd_ok _ 26 5 1161999626656546833 1161999626656546865 (by decide) (by decide +kernel) ktree32_0_2_5))) (treeWith_odd_ok _ 28 3 1161999626656546821 1161999626656546821 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 1161999626656546821 1161999626656546837 (by decide) (by decide) (treeWith_odd_ok _ 26 5 1161999626656546821 1161999626656546853 (by decide) (by decide +kernel) ktree32_0_2_6) (treeWith_odd_ok _ 26 5 1161999626656546837 1161999626656546837 (by decide) (by decide +kernel) ktree32_0_2_7))))))

theorem ktree32_0_3_0 : treeWith (etherLeaf 32 32 39 16 0 3) 26 6 580999811180789802 = true := by
  decide +kernel

theorem ktree32_0_3_1 : treeWith (etherLeaf 32 32 39 16 0 3) 26 6 580999811180789818 = true := by
  decide +kernel

theorem ktree32_0_3_2 : treeWith (etherLeaf 32 32 39 16 0 3) 26 6 580999811180789798 = true := by
  decide +kernel

theorem ktree32_0_3_3 : treeWith (etherLeaf 32 32 39 16 0 3) 26 6 580999811180789782 = true := by
  decide +kernel

theorem ktree32_0_3_4 : treeWith (etherLeaf 32 32 39 16 0 3) 26 6 580999811180789761 = true := by
  decide +kernel

theorem ktree32_0_3_5 : treeWith (etherLeaf 32 32 39 16 0 3) 26 6 580999811180789809 = true := by
  decide +kernel

theorem ktree32_0_3_6 : treeWith (etherLeaf 32 32 39 16 0 3) 26 6 580999811180789797 = true := by
  decide +kernel

theorem ktree32_0_3_7 : treeWith (etherLeaf 32 32 39 16 0 3) 26 6 580999811180789781 = true := by
  decide +kernel

theorem ktree32_0_3 : etherTreeOK 32 32 39 16 0 3 = true := by
  unfold etherTreeOK
  rw [show etherTail 32 0 3 = 580999811180789760 by decide +kernel]
  exact (treeWith_even_ok _ 31 0 580999811180789760 580999811180789761 (by decide) (by decide) (treeWith_odd_ok _ 30 1 580999811180789760 580999811180789762 (by decide) (by decide +kernel) (treeWith_even_ok _ 29 2 580999811180789762 580999811180789766 (by decide) (by decide) (treeWith_odd_ok _ 28 3 580999811180789762 580999811180789770 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 580999811180789770 580999811180789786 (by decide) (by decide) (treeWith_odd_ok _ 26 5 580999811180789770 580999811180789802 (by decide) (by decide +kernel) ktree32_0_3_0) (treeWith_odd_ok _ 26 5 580999811180789786 580999811180789818 (by decide) (by decide +kernel) ktree32_0_3_1))) (treeWith_odd_ok _ 28 3 580999811180789766 580999811180789766 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 580999811180789766 580999811180789782 (by decide) (by decide) (treeWith_odd_ok _ 26 5 580999811180789766 580999811180789798 (by decide) (by decide +kernel) ktree32_0_3_2) (treeWith_odd_ok _ 26 5 580999811180789782 580999811180789782 (by decide) (by decide +kernel) ktree32_0_3_3))))) (treeWith_odd_ok _ 30 1 580999811180789761 580999811180789761 (by decide) (by decide +kernel) (treeWith_even_ok _ 29 2 580999811180789761 580999811180789765 (by decide) (by decide) (treeWith_odd_ok _ 28 3 580999811180789761 580999811180789761 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 580999811180789761 580999811180789777 (by decide) (by decide) (treeWith_odd_ok _ 26 5 580999811180789761 580999811180789761 (by decide) (by decide +kernel) ktree32_0_3_4) (treeWith_odd_ok _ 26 5 580999811180789777 580999811180789809 (by decide) (by decide +kernel) ktree32_0_3_5))) (treeWith_odd_ok _ 28 3 580999811180789765 580999811180789765 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 580999811180789765 580999811180789781 (by decide) (by decide) (treeWith_odd_ok _ 26 5 580999811180789765 580999811180789797 (by decide) (by decide +kernel) ktree32_0_3_6) (treeWith_odd_ok _ 26 5 580999811180789781 580999811180789781 (by decide) (by decide +kernel) ktree32_0_3_7))))))

theorem ktree32_0_4_0 : treeWith (etherLeaf 32 32 39 16 0 4) 26 6 290499905590394922 = true := by
  decide +kernel

theorem ktree32_0_4_1 : treeWith (etherLeaf 32 32 39 16 0 4) 26 6 290499905590394938 = true := by
  decide +kernel

theorem ktree32_0_4_2 : treeWith (etherLeaf 32 32 39 16 0 4) 26 6 290499905590394918 = true := by
  decide +kernel

theorem ktree32_0_4_3 : treeWith (etherLeaf 32 32 39 16 0 4) 26 6 290499905590394902 = true := by
  decide +kernel

theorem ktree32_0_4_4 : treeWith (etherLeaf 32 32 39 16 0 4) 26 6 290499905590394881 = true := by
  decide +kernel

theorem ktree32_0_4_5 : treeWith (etherLeaf 32 32 39 16 0 4) 26 6 290499905590394929 = true := by
  decide +kernel

theorem ktree32_0_4_6 : treeWith (etherLeaf 32 32 39 16 0 4) 26 6 290499905590394917 = true := by
  decide +kernel

theorem ktree32_0_4_7 : treeWith (etherLeaf 32 32 39 16 0 4) 26 6 290499905590394901 = true := by
  decide +kernel

theorem ktree32_0_4 : etherTreeOK 32 32 39 16 0 4 = true := by
  unfold etherTreeOK
  rw [show etherTail 32 0 4 = 290499905590394880 by decide +kernel]
  exact (treeWith_even_ok _ 31 0 290499905590394880 290499905590394881 (by decide) (by decide) (treeWith_odd_ok _ 30 1 290499905590394880 290499905590394882 (by decide) (by decide +kernel) (treeWith_even_ok _ 29 2 290499905590394882 290499905590394886 (by decide) (by decide) (treeWith_odd_ok _ 28 3 290499905590394882 290499905590394890 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 290499905590394890 290499905590394906 (by decide) (by decide) (treeWith_odd_ok _ 26 5 290499905590394890 290499905590394922 (by decide) (by decide +kernel) ktree32_0_4_0) (treeWith_odd_ok _ 26 5 290499905590394906 290499905590394938 (by decide) (by decide +kernel) ktree32_0_4_1))) (treeWith_odd_ok _ 28 3 290499905590394886 290499905590394886 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 290499905590394886 290499905590394902 (by decide) (by decide) (treeWith_odd_ok _ 26 5 290499905590394886 290499905590394918 (by decide) (by decide +kernel) ktree32_0_4_2) (treeWith_odd_ok _ 26 5 290499905590394902 290499905590394902 (by decide) (by decide +kernel) ktree32_0_4_3))))) (treeWith_odd_ok _ 30 1 290499905590394881 290499905590394881 (by decide) (by decide +kernel) (treeWith_even_ok _ 29 2 290499905590394881 290499905590394885 (by decide) (by decide) (treeWith_odd_ok _ 28 3 290499905590394881 290499905590394881 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 290499905590394881 290499905590394897 (by decide) (by decide) (treeWith_odd_ok _ 26 5 290499905590394881 290499905590394881 (by decide) (by decide +kernel) ktree32_0_4_4) (treeWith_odd_ok _ 26 5 290499905590394897 290499905590394929 (by decide) (by decide +kernel) ktree32_0_4_5))) (treeWith_odd_ok _ 28 3 290499905590394885 290499905590394885 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 290499905590394885 290499905590394901 (by decide) (by decide) (treeWith_odd_ok _ 26 5 290499905590394885 290499905590394917 (by decide) (by decide +kernel) ktree32_0_4_6) (treeWith_odd_ok _ 26 5 290499905590394901 290499905590394901 (by decide) (by decide +kernel) ktree32_0_4_7))))))

theorem ktree32_0_5_0 : treeWith (etherLeaf 32 32 39 16 0 5) 26 6 145249952795197482 = true := by
  decide +kernel

theorem ktree32_0_5_1 : treeWith (etherLeaf 32 32 39 16 0 5) 26 6 145249952795197498 = true := by
  decide +kernel

theorem ktree32_0_5_2 : treeWith (etherLeaf 32 32 39 16 0 5) 26 6 145249952795197478 = true := by
  decide +kernel

theorem ktree32_0_5_3 : treeWith (etherLeaf 32 32 39 16 0 5) 26 6 145249952795197462 = true := by
  decide +kernel

theorem ktree32_0_5_4 : treeWith (etherLeaf 32 32 39 16 0 5) 26 6 145249952795197441 = true := by
  decide +kernel

theorem ktree32_0_5_5 : treeWith (etherLeaf 32 32 39 16 0 5) 26 6 145249952795197489 = true := by
  decide +kernel

theorem ktree32_0_5_6 : treeWith (etherLeaf 32 32 39 16 0 5) 26 6 145249952795197477 = true := by
  decide +kernel

theorem ktree32_0_5_7 : treeWith (etherLeaf 32 32 39 16 0 5) 26 6 145249952795197461 = true := by
  decide +kernel

theorem ktree32_0_5 : etherTreeOK 32 32 39 16 0 5 = true := by
  unfold etherTreeOK
  rw [show etherTail 32 0 5 = 145249952795197440 by decide +kernel]
  exact (treeWith_even_ok _ 31 0 145249952795197440 145249952795197441 (by decide) (by decide) (treeWith_odd_ok _ 30 1 145249952795197440 145249952795197442 (by decide) (by decide +kernel) (treeWith_even_ok _ 29 2 145249952795197442 145249952795197446 (by decide) (by decide) (treeWith_odd_ok _ 28 3 145249952795197442 145249952795197450 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 145249952795197450 145249952795197466 (by decide) (by decide) (treeWith_odd_ok _ 26 5 145249952795197450 145249952795197482 (by decide) (by decide +kernel) ktree32_0_5_0) (treeWith_odd_ok _ 26 5 145249952795197466 145249952795197498 (by decide) (by decide +kernel) ktree32_0_5_1))) (treeWith_odd_ok _ 28 3 145249952795197446 145249952795197446 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 145249952795197446 145249952795197462 (by decide) (by decide) (treeWith_odd_ok _ 26 5 145249952795197446 145249952795197478 (by decide) (by decide +kernel) ktree32_0_5_2) (treeWith_odd_ok _ 26 5 145249952795197462 145249952795197462 (by decide) (by decide +kernel) ktree32_0_5_3))))) (treeWith_odd_ok _ 30 1 145249952795197441 145249952795197441 (by decide) (by decide +kernel) (treeWith_even_ok _ 29 2 145249952795197441 145249952795197445 (by decide) (by decide) (treeWith_odd_ok _ 28 3 145249952795197441 145249952795197441 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 145249952795197441 145249952795197457 (by decide) (by decide) (treeWith_odd_ok _ 26 5 145249952795197441 145249952795197441 (by decide) (by decide +kernel) ktree32_0_5_4) (treeWith_odd_ok _ 26 5 145249952795197457 145249952795197489 (by decide) (by decide +kernel) ktree32_0_5_5))) (treeWith_odd_ok _ 28 3 145249952795197445 145249952795197445 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 145249952795197445 145249952795197461 (by decide) (by decide) (treeWith_odd_ok _ 26 5 145249952795197445 145249952795197477 (by decide) (by decide +kernel) ktree32_0_5_6) (treeWith_odd_ok _ 26 5 145249952795197461 145249952795197461 (by decide) (by decide +kernel) ktree32_0_5_7))))))

theorem ktree32_0_6_0 : treeWith (etherLeaf 32 32 39 16 0 6) 26 6 9295997013252374570 = true := by
  decide +kernel

theorem ktree32_0_6_1 : treeWith (etherLeaf 32 32 39 16 0 6) 26 6 9295997013252374586 = true := by
  decide +kernel

theorem ktree32_0_6_2 : treeWith (etherLeaf 32 32 39 16 0 6) 26 6 9295997013252374566 = true := by
  decide +kernel

theorem ktree32_0_6_3 : treeWith (etherLeaf 32 32 39 16 0 6) 26 6 9295997013252374550 = true := by
  decide +kernel

theorem ktree32_0_6_4 : treeWith (etherLeaf 32 32 39 16 0 6) 26 6 9295997013252374529 = true := by
  decide +kernel

theorem ktree32_0_6_5 : treeWith (etherLeaf 32 32 39 16 0 6) 26 6 9295997013252374577 = true := by
  decide +kernel

theorem ktree32_0_6_6 : treeWith (etherLeaf 32 32 39 16 0 6) 26 6 9295997013252374565 = true := by
  decide +kernel

theorem ktree32_0_6_7 : treeWith (etherLeaf 32 32 39 16 0 6) 26 6 9295997013252374549 = true := by
  decide +kernel

theorem ktree32_0_6 : etherTreeOK 32 32 39 16 0 6 = true := by
  unfold etherTreeOK
  rw [show etherTail 32 0 6 = 9295997013252374528 by decide +kernel]
  exact (treeWith_even_ok _ 31 0 9295997013252374528 9295997013252374529 (by decide) (by decide) (treeWith_odd_ok _ 30 1 9295997013252374528 9295997013252374530 (by decide) (by decide +kernel) (treeWith_even_ok _ 29 2 9295997013252374530 9295997013252374534 (by decide) (by decide) (treeWith_odd_ok _ 28 3 9295997013252374530 9295997013252374538 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 9295997013252374538 9295997013252374554 (by decide) (by decide) (treeWith_odd_ok _ 26 5 9295997013252374538 9295997013252374570 (by decide) (by decide +kernel) ktree32_0_6_0) (treeWith_odd_ok _ 26 5 9295997013252374554 9295997013252374586 (by decide) (by decide +kernel) ktree32_0_6_1))) (treeWith_odd_ok _ 28 3 9295997013252374534 9295997013252374534 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 9295997013252374534 9295997013252374550 (by decide) (by decide) (treeWith_odd_ok _ 26 5 9295997013252374534 9295997013252374566 (by decide) (by decide +kernel) ktree32_0_6_2) (treeWith_odd_ok _ 26 5 9295997013252374550 9295997013252374550 (by decide) (by decide +kernel) ktree32_0_6_3))))) (treeWith_odd_ok _ 30 1 9295997013252374529 9295997013252374529 (by decide) (by decide +kernel) (treeWith_even_ok _ 29 2 9295997013252374529 9295997013252374533 (by decide) (by decide) (treeWith_odd_ok _ 28 3 9295997013252374529 9295997013252374529 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 9295997013252374529 9295997013252374545 (by decide) (by decide) (treeWith_odd_ok _ 26 5 9295997013252374529 9295997013252374529 (by decide) (by decide +kernel) ktree32_0_6_4) (treeWith_odd_ok _ 26 5 9295997013252374545 9295997013252374577 (by decide) (by decide +kernel) ktree32_0_6_5))) (treeWith_odd_ok _ 28 3 9295997013252374533 9295997013252374533 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 9295997013252374533 9295997013252374549 (by decide) (by decide) (treeWith_odd_ok _ 26 5 9295997013252374533 9295997013252374565 (by decide) (by decide +kernel) ktree32_0_6_6) (treeWith_odd_ok _ 26 5 9295997013252374549 9295997013252374549 (by decide) (by decide +kernel) ktree32_0_6_7))))))

theorem ktree32_1_0_0 : treeWith (etherLeaf 32 32 39 16 1 0) 26 6 16267994773191655466 = true := by
  decide +kernel

theorem ktree32_1_0_1 : treeWith (etherLeaf 32 32 39 16 1 0) 26 6 16267994773191655482 = true := by
  decide +kernel

theorem ktree32_1_0_2 : treeWith (etherLeaf 32 32 39 16 1 0) 26 6 16267994773191655462 = true := by
  decide +kernel

theorem ktree32_1_0_3 : treeWith (etherLeaf 32 32 39 16 1 0) 26 6 16267994773191655446 = true := by
  decide +kernel

theorem ktree32_1_0_4 : treeWith (etherLeaf 32 32 39 16 1 0) 26 6 16267994773191655425 = true := by
  decide +kernel

theorem ktree32_1_0_5 : treeWith (etherLeaf 32 32 39 16 1 0) 26 6 16267994773191655473 = true := by
  decide +kernel

theorem ktree32_1_0_6 : treeWith (etherLeaf 32 32 39 16 1 0) 26 6 16267994773191655461 = true := by
  decide +kernel

theorem ktree32_1_0_7 : treeWith (etherLeaf 32 32 39 16 1 0) 26 6 16267994773191655445 = true := by
  decide +kernel

theorem ktree32_1_0 : etherTreeOK 32 32 39 16 1 0 = true := by
  unfold etherTreeOK
  rw [show etherTail 32 1 0 = 16267994773191655424 by decide +kernel]
  exact (treeWith_even_ok _ 31 0 16267994773191655424 16267994773191655425 (by decide) (by decide) (treeWith_odd_ok _ 30 1 16267994773191655424 16267994773191655426 (by decide) (by decide +kernel) (treeWith_even_ok _ 29 2 16267994773191655426 16267994773191655430 (by decide) (by decide) (treeWith_odd_ok _ 28 3 16267994773191655426 16267994773191655434 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 16267994773191655434 16267994773191655450 (by decide) (by decide) (treeWith_odd_ok _ 26 5 16267994773191655434 16267994773191655466 (by decide) (by decide +kernel) ktree32_1_0_0) (treeWith_odd_ok _ 26 5 16267994773191655450 16267994773191655482 (by decide) (by decide +kernel) ktree32_1_0_1))) (treeWith_odd_ok _ 28 3 16267994773191655430 16267994773191655430 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 16267994773191655430 16267994773191655446 (by decide) (by decide) (treeWith_odd_ok _ 26 5 16267994773191655430 16267994773191655462 (by decide) (by decide +kernel) ktree32_1_0_2) (treeWith_odd_ok _ 26 5 16267994773191655446 16267994773191655446 (by decide) (by decide +kernel) ktree32_1_0_3))))) (treeWith_odd_ok _ 30 1 16267994773191655425 16267994773191655425 (by decide) (by decide +kernel) (treeWith_even_ok _ 29 2 16267994773191655425 16267994773191655429 (by decide) (by decide) (treeWith_odd_ok _ 28 3 16267994773191655425 16267994773191655425 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 16267994773191655425 16267994773191655441 (by decide) (by decide) (treeWith_odd_ok _ 26 5 16267994773191655425 16267994773191655425 (by decide) (by decide +kernel) ktree32_1_0_4) (treeWith_odd_ok _ 26 5 16267994773191655441 16267994773191655473 (by decide) (by decide +kernel) ktree32_1_0_5))) (treeWith_odd_ok _ 28 3 16267994773191655429 16267994773191655429 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 16267994773191655429 16267994773191655445 (by decide) (by decide) (treeWith_odd_ok _ 26 5 16267994773191655429 16267994773191655461 (by decide) (by decide +kernel) ktree32_1_0_6) (treeWith_odd_ok _ 26 5 16267994773191655445 16267994773191655445 (by decide) (by decide +kernel) ktree32_1_0_7))))))

theorem ktree32_1_1_0 : treeWith (etherLeaf 32 32 39 16 1 1) 26 6 8133997386595827754 = true := by
  decide +kernel

theorem ktree32_1_1_1 : treeWith (etherLeaf 32 32 39 16 1 1) 26 6 8133997386595827770 = true := by
  decide +kernel

theorem ktree32_1_1_2 : treeWith (etherLeaf 32 32 39 16 1 1) 26 6 8133997386595827750 = true := by
  decide +kernel

theorem ktree32_1_1_3 : treeWith (etherLeaf 32 32 39 16 1 1) 26 6 8133997386595827734 = true := by
  decide +kernel

theorem ktree32_1_1_4 : treeWith (etherLeaf 32 32 39 16 1 1) 26 6 8133997386595827713 = true := by
  decide +kernel

theorem ktree32_1_1_5 : treeWith (etherLeaf 32 32 39 16 1 1) 26 6 8133997386595827761 = true := by
  decide +kernel

theorem ktree32_1_1_6 : treeWith (etherLeaf 32 32 39 16 1 1) 26 6 8133997386595827749 = true := by
  decide +kernel

theorem ktree32_1_1_7 : treeWith (etherLeaf 32 32 39 16 1 1) 26 6 8133997386595827733 = true := by
  decide +kernel

theorem ktree32_1_1 : etherTreeOK 32 32 39 16 1 1 = true := by
  unfold etherTreeOK
  rw [show etherTail 32 1 1 = 8133997386595827712 by decide +kernel]
  exact (treeWith_even_ok _ 31 0 8133997386595827712 8133997386595827713 (by decide) (by decide) (treeWith_odd_ok _ 30 1 8133997386595827712 8133997386595827714 (by decide) (by decide +kernel) (treeWith_even_ok _ 29 2 8133997386595827714 8133997386595827718 (by decide) (by decide) (treeWith_odd_ok _ 28 3 8133997386595827714 8133997386595827722 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 8133997386595827722 8133997386595827738 (by decide) (by decide) (treeWith_odd_ok _ 26 5 8133997386595827722 8133997386595827754 (by decide) (by decide +kernel) ktree32_1_1_0) (treeWith_odd_ok _ 26 5 8133997386595827738 8133997386595827770 (by decide) (by decide +kernel) ktree32_1_1_1))) (treeWith_odd_ok _ 28 3 8133997386595827718 8133997386595827718 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 8133997386595827718 8133997386595827734 (by decide) (by decide) (treeWith_odd_ok _ 26 5 8133997386595827718 8133997386595827750 (by decide) (by decide +kernel) ktree32_1_1_2) (treeWith_odd_ok _ 26 5 8133997386595827734 8133997386595827734 (by decide) (by decide +kernel) ktree32_1_1_3))))) (treeWith_odd_ok _ 30 1 8133997386595827713 8133997386595827713 (by decide) (by decide +kernel) (treeWith_even_ok _ 29 2 8133997386595827713 8133997386595827717 (by decide) (by decide) (treeWith_odd_ok _ 28 3 8133997386595827713 8133997386595827713 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 8133997386595827713 8133997386595827729 (by decide) (by decide) (treeWith_odd_ok _ 26 5 8133997386595827713 8133997386595827713 (by decide) (by decide +kernel) ktree32_1_1_4) (treeWith_odd_ok _ 26 5 8133997386595827729 8133997386595827761 (by decide) (by decide +kernel) ktree32_1_1_5))) (treeWith_odd_ok _ 28 3 8133997386595827717 8133997386595827717 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 8133997386595827717 8133997386595827733 (by decide) (by decide) (treeWith_odd_ok _ 26 5 8133997386595827717 8133997386595827749 (by decide) (by decide +kernel) ktree32_1_1_6) (treeWith_odd_ok _ 26 5 8133997386595827733 8133997386595827733 (by decide) (by decide +kernel) ktree32_1_1_7))))))

theorem ktree32_1_2_0 : treeWith (etherLeaf 32 32 39 16 1 2) 26 6 4066998691150430250 = true := by
  decide +kernel

theorem ktree32_1_2_1 : treeWith (etherLeaf 32 32 39 16 1 2) 26 6 4066998691150430266 = true := by
  decide +kernel

theorem ktree32_1_2_2 : treeWith (etherLeaf 32 32 39 16 1 2) 26 6 4066998691150430246 = true := by
  decide +kernel

theorem ktree32_1_2_3 : treeWith (etherLeaf 32 32 39 16 1 2) 26 6 4066998691150430230 = true := by
  decide +kernel

theorem ktree32_1_2_4 : treeWith (etherLeaf 32 32 39 16 1 2) 26 6 4066998691150430209 = true := by
  decide +kernel

theorem ktree32_1_2_5 : treeWith (etherLeaf 32 32 39 16 1 2) 26 6 4066998691150430257 = true := by
  decide +kernel

theorem ktree32_1_2_6 : treeWith (etherLeaf 32 32 39 16 1 2) 26 6 4066998691150430245 = true := by
  decide +kernel

theorem ktree32_1_2_7 : treeWith (etherLeaf 32 32 39 16 1 2) 26 6 4066998691150430229 = true := by
  decide +kernel

theorem ktree32_1_2 : etherTreeOK 32 32 39 16 1 2 = true := by
  unfold etherTreeOK
  rw [show etherTail 32 1 2 = 4066998691150430208 by decide +kernel]
  exact (treeWith_even_ok _ 31 0 4066998691150430208 4066998691150430209 (by decide) (by decide) (treeWith_odd_ok _ 30 1 4066998691150430208 4066998691150430210 (by decide) (by decide +kernel) (treeWith_even_ok _ 29 2 4066998691150430210 4066998691150430214 (by decide) (by decide) (treeWith_odd_ok _ 28 3 4066998691150430210 4066998691150430218 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 4066998691150430218 4066998691150430234 (by decide) (by decide) (treeWith_odd_ok _ 26 5 4066998691150430218 4066998691150430250 (by decide) (by decide +kernel) ktree32_1_2_0) (treeWith_odd_ok _ 26 5 4066998691150430234 4066998691150430266 (by decide) (by decide +kernel) ktree32_1_2_1))) (treeWith_odd_ok _ 28 3 4066998691150430214 4066998691150430214 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 4066998691150430214 4066998691150430230 (by decide) (by decide) (treeWith_odd_ok _ 26 5 4066998691150430214 4066998691150430246 (by decide) (by decide +kernel) ktree32_1_2_2) (treeWith_odd_ok _ 26 5 4066998691150430230 4066998691150430230 (by decide) (by decide +kernel) ktree32_1_2_3))))) (treeWith_odd_ok _ 30 1 4066998691150430209 4066998691150430209 (by decide) (by decide +kernel) (treeWith_even_ok _ 29 2 4066998691150430209 4066998691150430213 (by decide) (by decide) (treeWith_odd_ok _ 28 3 4066998691150430209 4066998691150430209 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 4066998691150430209 4066998691150430225 (by decide) (by decide) (treeWith_odd_ok _ 26 5 4066998691150430209 4066998691150430209 (by decide) (by decide +kernel) ktree32_1_2_4) (treeWith_odd_ok _ 26 5 4066998691150430225 4066998691150430257 (by decide) (by decide +kernel) ktree32_1_2_5))) (treeWith_odd_ok _ 28 3 4066998691150430213 4066998691150430213 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 4066998691150430213 4066998691150430229 (by decide) (by decide) (treeWith_odd_ok _ 26 5 4066998691150430213 4066998691150430245 (by decide) (by decide +kernel) ktree32_1_2_6) (treeWith_odd_ok _ 26 5 4066998691150430229 4066998691150430229 (by decide) (by decide +kernel) ktree32_1_2_7))))))

theorem ktree32_1_3_0 : treeWith (etherLeaf 32 32 39 16 1 3) 26 6 2033499343427731498 = true := by
  decide +kernel

theorem ktree32_1_3_1 : treeWith (etherLeaf 32 32 39 16 1 3) 26 6 2033499343427731514 = true := by
  decide +kernel

theorem ktree32_1_3_2 : treeWith (etherLeaf 32 32 39 16 1 3) 26 6 2033499343427731494 = true := by
  decide +kernel

theorem ktree32_1_3_3 : treeWith (etherLeaf 32 32 39 16 1 3) 26 6 2033499343427731478 = true := by
  decide +kernel

theorem ktree32_1_3_4 : treeWith (etherLeaf 32 32 39 16 1 3) 26 6 2033499343427731457 = true := by
  decide +kernel

theorem ktree32_1_3_5 : treeWith (etherLeaf 32 32 39 16 1 3) 26 6 2033499343427731505 = true := by
  decide +kernel

theorem ktree32_1_3_6 : treeWith (etherLeaf 32 32 39 16 1 3) 26 6 2033499343427731493 = true := by
  decide +kernel

theorem ktree32_1_3_7 : treeWith (etherLeaf 32 32 39 16 1 3) 26 6 2033499343427731477 = true := by
  decide +kernel

theorem ktree32_1_3 : etherTreeOK 32 32 39 16 1 3 = true := by
  unfold etherTreeOK
  rw [show etherTail 32 1 3 = 2033499343427731456 by decide +kernel]
  exact (treeWith_even_ok _ 31 0 2033499343427731456 2033499343427731457 (by decide) (by decide) (treeWith_odd_ok _ 30 1 2033499343427731456 2033499343427731458 (by decide) (by decide +kernel) (treeWith_even_ok _ 29 2 2033499343427731458 2033499343427731462 (by decide) (by decide) (treeWith_odd_ok _ 28 3 2033499343427731458 2033499343427731466 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 2033499343427731466 2033499343427731482 (by decide) (by decide) (treeWith_odd_ok _ 26 5 2033499343427731466 2033499343427731498 (by decide) (by decide +kernel) ktree32_1_3_0) (treeWith_odd_ok _ 26 5 2033499343427731482 2033499343427731514 (by decide) (by decide +kernel) ktree32_1_3_1))) (treeWith_odd_ok _ 28 3 2033499343427731462 2033499343427731462 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 2033499343427731462 2033499343427731478 (by decide) (by decide) (treeWith_odd_ok _ 26 5 2033499343427731462 2033499343427731494 (by decide) (by decide +kernel) ktree32_1_3_2) (treeWith_odd_ok _ 26 5 2033499343427731478 2033499343427731478 (by decide) (by decide +kernel) ktree32_1_3_3))))) (treeWith_odd_ok _ 30 1 2033499343427731457 2033499343427731457 (by decide) (by decide +kernel) (treeWith_even_ok _ 29 2 2033499343427731457 2033499343427731461 (by decide) (by decide) (treeWith_odd_ok _ 28 3 2033499343427731457 2033499343427731457 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 2033499343427731457 2033499343427731473 (by decide) (by decide) (treeWith_odd_ok _ 26 5 2033499343427731457 2033499343427731457 (by decide) (by decide +kernel) ktree32_1_3_4) (treeWith_odd_ok _ 26 5 2033499343427731473 2033499343427731505 (by decide) (by decide +kernel) ktree32_1_3_5))) (treeWith_odd_ok _ 28 3 2033499343427731461 2033499343427731461 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 2033499343427731461 2033499343427731477 (by decide) (by decide) (treeWith_odd_ok _ 26 5 2033499343427731461 2033499343427731493 (by decide) (by decide +kernel) ktree32_1_3_6) (treeWith_odd_ok _ 26 5 2033499343427731477 2033499343427731477 (by decide) (by decide +kernel) ktree32_1_3_7))))))

theorem ktree32_1_4_0 : treeWith (etherLeaf 32 32 39 16 1 4) 26 6 1016749669566382122 = true := by
  decide +kernel

theorem ktree32_1_4_1 : treeWith (etherLeaf 32 32 39 16 1 4) 26 6 1016749669566382138 = true := by
  decide +kernel

theorem ktree32_1_4_2 : treeWith (etherLeaf 32 32 39 16 1 4) 26 6 1016749669566382118 = true := by
  decide +kernel

theorem ktree32_1_4_3 : treeWith (etherLeaf 32 32 39 16 1 4) 26 6 1016749669566382102 = true := by
  decide +kernel

theorem ktree32_1_4_4 : treeWith (etherLeaf 32 32 39 16 1 4) 26 6 1016749669566382081 = true := by
  decide +kernel

theorem ktree32_1_4_5 : treeWith (etherLeaf 32 32 39 16 1 4) 26 6 1016749669566382129 = true := by
  decide +kernel

theorem ktree32_1_4_6 : treeWith (etherLeaf 32 32 39 16 1 4) 26 6 1016749669566382117 = true := by
  decide +kernel

theorem ktree32_1_4_7 : treeWith (etherLeaf 32 32 39 16 1 4) 26 6 1016749669566382101 = true := by
  decide +kernel

theorem ktree32_1_4 : etherTreeOK 32 32 39 16 1 4 = true := by
  unfold etherTreeOK
  rw [show etherTail 32 1 4 = 1016749669566382080 by decide +kernel]
  exact (treeWith_even_ok _ 31 0 1016749669566382080 1016749669566382081 (by decide) (by decide) (treeWith_odd_ok _ 30 1 1016749669566382080 1016749669566382082 (by decide) (by decide +kernel) (treeWith_even_ok _ 29 2 1016749669566382082 1016749669566382086 (by decide) (by decide) (treeWith_odd_ok _ 28 3 1016749669566382082 1016749669566382090 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 1016749669566382090 1016749669566382106 (by decide) (by decide) (treeWith_odd_ok _ 26 5 1016749669566382090 1016749669566382122 (by decide) (by decide +kernel) ktree32_1_4_0) (treeWith_odd_ok _ 26 5 1016749669566382106 1016749669566382138 (by decide) (by decide +kernel) ktree32_1_4_1))) (treeWith_odd_ok _ 28 3 1016749669566382086 1016749669566382086 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 1016749669566382086 1016749669566382102 (by decide) (by decide) (treeWith_odd_ok _ 26 5 1016749669566382086 1016749669566382118 (by decide) (by decide +kernel) ktree32_1_4_2) (treeWith_odd_ok _ 26 5 1016749669566382102 1016749669566382102 (by decide) (by decide +kernel) ktree32_1_4_3))))) (treeWith_odd_ok _ 30 1 1016749669566382081 1016749669566382081 (by decide) (by decide +kernel) (treeWith_even_ok _ 29 2 1016749669566382081 1016749669566382085 (by decide) (by decide) (treeWith_odd_ok _ 28 3 1016749669566382081 1016749669566382081 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 1016749669566382081 1016749669566382097 (by decide) (by decide) (treeWith_odd_ok _ 26 5 1016749669566382081 1016749669566382081 (by decide) (by decide +kernel) ktree32_1_4_4) (treeWith_odd_ok _ 26 5 1016749669566382097 1016749669566382129 (by decide) (by decide +kernel) ktree32_1_4_5))) (treeWith_odd_ok _ 28 3 1016749669566382085 1016749669566382085 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 1016749669566382085 1016749669566382101 (by decide) (by decide) (treeWith_odd_ok _ 26 5 1016749669566382085 1016749669566382117 (by decide) (by decide +kernel) ktree32_1_4_6) (treeWith_odd_ok _ 26 5 1016749669566382101 1016749669566382101 (by decide) (by decide +kernel) ktree32_1_4_7))))))

theorem ktree32_1_5_0 : treeWith (etherLeaf 32 32 39 16 1 5) 26 6 9731746871637966890 = true := by
  decide +kernel

theorem ktree32_1_5_1 : treeWith (etherLeaf 32 32 39 16 1 5) 26 6 9731746871637966906 = true := by
  decide +kernel

theorem ktree32_1_5_2 : treeWith (etherLeaf 32 32 39 16 1 5) 26 6 9731746871637966886 = true := by
  decide +kernel

theorem ktree32_1_5_3 : treeWith (etherLeaf 32 32 39 16 1 5) 26 6 9731746871637966870 = true := by
  decide +kernel

theorem ktree32_1_5_4 : treeWith (etherLeaf 32 32 39 16 1 5) 26 6 9731746871637966849 = true := by
  decide +kernel

theorem ktree32_1_5_5 : treeWith (etherLeaf 32 32 39 16 1 5) 26 6 9731746871637966897 = true := by
  decide +kernel

theorem ktree32_1_5_6 : treeWith (etherLeaf 32 32 39 16 1 5) 26 6 9731746871637966885 = true := by
  decide +kernel

theorem ktree32_1_5_7 : treeWith (etherLeaf 32 32 39 16 1 5) 26 6 9731746871637966869 = true := by
  decide +kernel

theorem ktree32_1_5 : etherTreeOK 32 32 39 16 1 5 = true := by
  unfold etherTreeOK
  rw [show etherTail 32 1 5 = 9731746871637966848 by decide +kernel]
  exact (treeWith_even_ok _ 31 0 9731746871637966848 9731746871637966849 (by decide) (by decide) (treeWith_odd_ok _ 30 1 9731746871637966848 9731746871637966850 (by decide) (by decide +kernel) (treeWith_even_ok _ 29 2 9731746871637966850 9731746871637966854 (by decide) (by decide) (treeWith_odd_ok _ 28 3 9731746871637966850 9731746871637966858 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 9731746871637966858 9731746871637966874 (by decide) (by decide) (treeWith_odd_ok _ 26 5 9731746871637966858 9731746871637966890 (by decide) (by decide +kernel) ktree32_1_5_0) (treeWith_odd_ok _ 26 5 9731746871637966874 9731746871637966906 (by decide) (by decide +kernel) ktree32_1_5_1))) (treeWith_odd_ok _ 28 3 9731746871637966854 9731746871637966854 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 9731746871637966854 9731746871637966870 (by decide) (by decide) (treeWith_odd_ok _ 26 5 9731746871637966854 9731746871637966886 (by decide) (by decide +kernel) ktree32_1_5_2) (treeWith_odd_ok _ 26 5 9731746871637966870 9731746871637966870 (by decide) (by decide +kernel) ktree32_1_5_3))))) (treeWith_odd_ok _ 30 1 9731746871637966849 9731746871637966849 (by decide) (by decide +kernel) (treeWith_even_ok _ 29 2 9731746871637966849 9731746871637966853 (by decide) (by decide) (treeWith_odd_ok _ 28 3 9731746871637966849 9731746871637966849 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 9731746871637966849 9731746871637966865 (by decide) (by decide) (treeWith_odd_ok _ 26 5 9731746871637966849 9731746871637966849 (by decide) (by decide +kernel) ktree32_1_5_4) (treeWith_odd_ok _ 26 5 9731746871637966865 9731746871637966897 (by decide) (by decide +kernel) ktree32_1_5_5))) (treeWith_odd_ok _ 28 3 9731746871637966853 9731746871637966853 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 9731746871637966853 9731746871637966869 (by decide) (by decide) (treeWith_odd_ok _ 26 5 9731746871637966853 9731746871637966885 (by decide) (by decide +kernel) ktree32_1_5_6) (treeWith_odd_ok _ 26 5 9731746871637966869 9731746871637966869 (by decide) (by decide +kernel) ktree32_1_5_7))))))

theorem ktree32_1_6_0 : treeWith (etherLeaf 32 32 39 16 1 6) 26 6 14089245472673759274 = true := by
  decide +kernel

theorem ktree32_1_6_1 : treeWith (etherLeaf 32 32 39 16 1 6) 26 6 14089245472673759290 = true := by
  decide +kernel

theorem ktree32_1_6_2 : treeWith (etherLeaf 32 32 39 16 1 6) 26 6 14089245472673759270 = true := by
  decide +kernel

theorem ktree32_1_6_3 : treeWith (etherLeaf 32 32 39 16 1 6) 26 6 14089245472673759254 = true := by
  decide +kernel

theorem ktree32_1_6_4 : treeWith (etherLeaf 32 32 39 16 1 6) 26 6 14089245472673759233 = true := by
  decide +kernel

theorem ktree32_1_6_5 : treeWith (etherLeaf 32 32 39 16 1 6) 26 6 14089245472673759281 = true := by
  decide +kernel

theorem ktree32_1_6_6 : treeWith (etherLeaf 32 32 39 16 1 6) 26 6 14089245472673759269 = true := by
  decide +kernel

theorem ktree32_1_6_7 : treeWith (etherLeaf 32 32 39 16 1 6) 26 6 14089245472673759253 = true := by
  decide +kernel

theorem ktree32_1_6 : etherTreeOK 32 32 39 16 1 6 = true := by
  unfold etherTreeOK
  rw [show etherTail 32 1 6 = 14089245472673759232 by decide +kernel]
  exact (treeWith_even_ok _ 31 0 14089245472673759232 14089245472673759233 (by decide) (by decide) (treeWith_odd_ok _ 30 1 14089245472673759232 14089245472673759234 (by decide) (by decide +kernel) (treeWith_even_ok _ 29 2 14089245472673759234 14089245472673759238 (by decide) (by decide) (treeWith_odd_ok _ 28 3 14089245472673759234 14089245472673759242 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 14089245472673759242 14089245472673759258 (by decide) (by decide) (treeWith_odd_ok _ 26 5 14089245472673759242 14089245472673759274 (by decide) (by decide +kernel) ktree32_1_6_0) (treeWith_odd_ok _ 26 5 14089245472673759258 14089245472673759290 (by decide) (by decide +kernel) ktree32_1_6_1))) (treeWith_odd_ok _ 28 3 14089245472673759238 14089245472673759238 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 14089245472673759238 14089245472673759254 (by decide) (by decide) (treeWith_odd_ok _ 26 5 14089245472673759238 14089245472673759270 (by decide) (by decide +kernel) ktree32_1_6_2) (treeWith_odd_ok _ 26 5 14089245472673759254 14089245472673759254 (by decide) (by decide +kernel) ktree32_1_6_3))))) (treeWith_odd_ok _ 30 1 14089245472673759233 14089245472673759233 (by decide) (by decide +kernel) (treeWith_even_ok _ 29 2 14089245472673759233 14089245472673759237 (by decide) (by decide) (treeWith_odd_ok _ 28 3 14089245472673759233 14089245472673759233 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 14089245472673759233 14089245472673759249 (by decide) (by decide) (treeWith_odd_ok _ 26 5 14089245472673759233 14089245472673759233 (by decide) (by decide +kernel) ktree32_1_6_4) (treeWith_odd_ok _ 26 5 14089245472673759249 14089245472673759281 (by decide) (by decide +kernel) ktree32_1_6_5))) (treeWith_odd_ok _ 28 3 14089245472673759237 14089245472673759237 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 14089245472673759237 14089245472673759253 (by decide) (by decide) (treeWith_odd_ok _ 26 5 14089245472673759237 14089245472673759269 (by decide) (by decide +kernel) ktree32_1_6_6) (treeWith_odd_ok _ 26 5 14089245472673759253 14089245472673759253 (by decide) (by decide +kernel) ktree32_1_6_7))))))

theorem ktree32_2_0_0 : treeWith (etherLeaf 32 32 39 16 2 0) 26 6 10603246592704118826 = true := by
  decide +kernel

theorem ktree32_2_0_1 : treeWith (etherLeaf 32 32 39 16 2 0) 26 6 10603246592704118842 = true := by
  decide +kernel

theorem ktree32_2_0_2 : treeWith (etherLeaf 32 32 39 16 2 0) 26 6 10603246592704118822 = true := by
  decide +kernel

theorem ktree32_2_0_3 : treeWith (etherLeaf 32 32 39 16 2 0) 26 6 10603246592704118806 = true := by
  decide +kernel

theorem ktree32_2_0_4 : treeWith (etherLeaf 32 32 39 16 2 0) 26 6 10603246592704118785 = true := by
  decide +kernel

theorem ktree32_2_0_5 : treeWith (etherLeaf 32 32 39 16 2 0) 26 6 10603246592704118833 = true := by
  decide +kernel

theorem ktree32_2_0_6 : treeWith (etherLeaf 32 32 39 16 2 0) 26 6 10603246592704118821 = true := by
  decide +kernel

theorem ktree32_2_0_7 : treeWith (etherLeaf 32 32 39 16 2 0) 26 6 10603246592704118805 = true := by
  decide +kernel

theorem ktree32_2_0 : etherTreeOK 32 32 39 16 2 0 = true := by
  unfold etherTreeOK
  rw [show etherTail 32 2 0 = 10603246592704118784 by decide +kernel]
  exact (treeWith_even_ok _ 31 0 10603246592704118784 10603246592704118785 (by decide) (by decide) (treeWith_odd_ok _ 30 1 10603246592704118784 10603246592704118786 (by decide) (by decide +kernel) (treeWith_even_ok _ 29 2 10603246592704118786 10603246592704118790 (by decide) (by decide) (treeWith_odd_ok _ 28 3 10603246592704118786 10603246592704118794 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 10603246592704118794 10603246592704118810 (by decide) (by decide) (treeWith_odd_ok _ 26 5 10603246592704118794 10603246592704118826 (by decide) (by decide +kernel) ktree32_2_0_0) (treeWith_odd_ok _ 26 5 10603246592704118810 10603246592704118842 (by decide) (by decide +kernel) ktree32_2_0_1))) (treeWith_odd_ok _ 28 3 10603246592704118790 10603246592704118790 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 10603246592704118790 10603246592704118806 (by decide) (by decide) (treeWith_odd_ok _ 26 5 10603246592704118790 10603246592704118822 (by decide) (by decide +kernel) ktree32_2_0_2) (treeWith_odd_ok _ 26 5 10603246592704118806 10603246592704118806 (by decide) (by decide +kernel) ktree32_2_0_3))))) (treeWith_odd_ok _ 30 1 10603246592704118785 10603246592704118785 (by decide) (by decide +kernel) (treeWith_even_ok _ 29 2 10603246592704118785 10603246592704118789 (by decide) (by decide) (treeWith_odd_ok _ 28 3 10603246592704118785 10603246592704118785 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 10603246592704118785 10603246592704118801 (by decide) (by decide) (treeWith_odd_ok _ 26 5 10603246592704118785 10603246592704118785 (by decide) (by decide +kernel) ktree32_2_0_4) (treeWith_odd_ok _ 26 5 10603246592704118801 10603246592704118833 (by decide) (by decide +kernel) ktree32_2_0_5))) (treeWith_odd_ok _ 28 3 10603246592704118789 10603246592704118789 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 10603246592704118789 10603246592704118805 (by decide) (by decide) (treeWith_odd_ok _ 26 5 10603246592704118789 10603246592704118821 (by decide) (by decide +kernel) ktree32_2_0_6) (treeWith_odd_ok _ 26 5 10603246592704118805 10603246592704118805 (by decide) (by decide +kernel) ktree32_2_0_7))))))

theorem ktree32_2_1_0 : treeWith (etherLeaf 32 32 39 16 2 1) 26 6 14524995331059351594 = true := by
  decide +kernel

theorem ktree32_2_1_1 : treeWith (etherLeaf 32 32 39 16 2 1) 26 6 14524995331059351610 = true := by
  decide +kernel

theorem ktree32_2_1_2 : treeWith (etherLeaf 32 32 39 16 2 1) 26 6 14524995331059351590 = true := by
  decide +kernel

theorem ktree32_2_1_3 : treeWith (etherLeaf 32 32 39 16 2 1) 26 6 14524995331059351574 = true := by
  decide +kernel

theorem ktree32_2_1_4 : treeWith (etherLeaf 32 32 39 16 2 1) 26 6 14524995331059351553 = true := by
  decide +kernel

theorem ktree32_2_1_5 : treeWith (etherLeaf 32 32 39 16 2 1) 26 6 14524995331059351601 = true := by
  decide +kernel

theorem ktree32_2_1_6 : treeWith (etherLeaf 32 32 39 16 2 1) 26 6 14524995331059351589 = true := by
  decide +kernel

theorem ktree32_2_1_7 : treeWith (etherLeaf 32 32 39 16 2 1) 26 6 14524995331059351573 = true := by
  decide +kernel

theorem ktree32_2_1 : etherTreeOK 32 32 39 16 2 1 = true := by
  unfold etherTreeOK
  rw [show etherTail 32 2 1 = 14524995331059351552 by decide +kernel]
  exact (treeWith_even_ok _ 31 0 14524995331059351552 14524995331059351553 (by decide) (by decide) (treeWith_odd_ok _ 30 1 14524995331059351552 14524995331059351554 (by decide) (by decide +kernel) (treeWith_even_ok _ 29 2 14524995331059351554 14524995331059351558 (by decide) (by decide) (treeWith_odd_ok _ 28 3 14524995331059351554 14524995331059351562 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 14524995331059351562 14524995331059351578 (by decide) (by decide) (treeWith_odd_ok _ 26 5 14524995331059351562 14524995331059351594 (by decide) (by decide +kernel) ktree32_2_1_0) (treeWith_odd_ok _ 26 5 14524995331059351578 14524995331059351610 (by decide) (by decide +kernel) ktree32_2_1_1))) (treeWith_odd_ok _ 28 3 14524995331059351558 14524995331059351558 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 14524995331059351558 14524995331059351574 (by decide) (by decide) (treeWith_odd_ok _ 26 5 14524995331059351558 14524995331059351590 (by decide) (by decide +kernel) ktree32_2_1_2) (treeWith_odd_ok _ 26 5 14524995331059351574 14524995331059351574 (by decide) (by decide +kernel) ktree32_2_1_3))))) (treeWith_odd_ok _ 30 1 14524995331059351553 14524995331059351553 (by decide) (by decide +kernel) (treeWith_even_ok _ 29 2 14524995331059351553 14524995331059351557 (by decide) (by decide) (treeWith_odd_ok _ 28 3 14524995331059351553 14524995331059351553 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 14524995331059351553 14524995331059351569 (by decide) (by decide) (treeWith_odd_ok _ 26 5 14524995331059351553 14524995331059351553 (by decide) (by decide +kernel) ktree32_2_1_4) (treeWith_odd_ok _ 26 5 14524995331059351569 14524995331059351601 (by decide) (by decide +kernel) ktree32_2_1_5))) (treeWith_odd_ok _ 28 3 14524995331059351557 14524995331059351557 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 14524995331059351557 14524995331059351573 (by decide) (by decide) (treeWith_odd_ok _ 26 5 14524995331059351557 14524995331059351589 (by decide) (by decide +kernel) ktree32_2_1_6) (treeWith_odd_ok _ 26 5 14524995331059351573 14524995331059351573 (by decide) (by decide +kernel) ktree32_2_1_7))))))

theorem ktree32_2_2_0 : treeWith (etherLeaf 32 32 39 16 2 2) 26 6 7262497665529675818 = true := by
  decide +kernel

theorem ktree32_2_2_1 : treeWith (etherLeaf 32 32 39 16 2 2) 26 6 7262497665529675834 = true := by
  decide +kernel

theorem ktree32_2_2_2 : treeWith (etherLeaf 32 32 39 16 2 2) 26 6 7262497665529675814 = true := by
  decide +kernel

theorem ktree32_2_2_3 : treeWith (etherLeaf 32 32 39 16 2 2) 26 6 7262497665529675798 = true := by
  decide +kernel

theorem ktree32_2_2_4 : treeWith (etherLeaf 32 32 39 16 2 2) 26 6 7262497665529675777 = true := by
  decide +kernel

theorem ktree32_2_2_5 : treeWith (etherLeaf 32 32 39 16 2 2) 26 6 7262497665529675825 = true := by
  decide +kernel

theorem ktree32_2_2_6 : treeWith (etherLeaf 32 32 39 16 2 2) 26 6 7262497665529675813 = true := by
  decide +kernel

theorem ktree32_2_2_7 : treeWith (etherLeaf 32 32 39 16 2 2) 26 6 7262497665529675797 = true := by
  decide +kernel

theorem ktree32_2_2 : etherTreeOK 32 32 39 16 2 2 = true := by
  unfold etherTreeOK
  rw [show etherTail 32 2 2 = 7262497665529675776 by decide +kernel]
  exact (treeWith_even_ok _ 31 0 7262497665529675776 7262497665529675777 (by decide) (by decide) (treeWith_odd_ok _ 30 1 7262497665529675776 7262497665529675778 (by decide) (by decide +kernel) (treeWith_even_ok _ 29 2 7262497665529675778 7262497665529675782 (by decide) (by decide) (treeWith_odd_ok _ 28 3 7262497665529675778 7262497665529675786 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 7262497665529675786 7262497665529675802 (by decide) (by decide) (treeWith_odd_ok _ 26 5 7262497665529675786 7262497665529675818 (by decide) (by decide +kernel) ktree32_2_2_0) (treeWith_odd_ok _ 26 5 7262497665529675802 7262497665529675834 (by decide) (by decide +kernel) ktree32_2_2_1))) (treeWith_odd_ok _ 28 3 7262497665529675782 7262497665529675782 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 7262497665529675782 7262497665529675798 (by decide) (by decide) (treeWith_odd_ok _ 26 5 7262497665529675782 7262497665529675814 (by decide) (by decide +kernel) ktree32_2_2_2) (treeWith_odd_ok _ 26 5 7262497665529675798 7262497665529675798 (by decide) (by decide +kernel) ktree32_2_2_3))))) (treeWith_odd_ok _ 30 1 7262497665529675777 7262497665529675777 (by decide) (by decide +kernel) (treeWith_even_ok _ 29 2 7262497665529675777 7262497665529675781 (by decide) (by decide) (treeWith_odd_ok _ 28 3 7262497665529675777 7262497665529675777 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 7262497665529675777 7262497665529675793 (by decide) (by decide) (treeWith_odd_ok _ 26 5 7262497665529675777 7262497665529675777 (by decide) (by decide +kernel) ktree32_2_2_4) (treeWith_odd_ok _ 26 5 7262497665529675793 7262497665529675825 (by decide) (by decide +kernel) ktree32_2_2_5))) (treeWith_odd_ok _ 28 3 7262497665529675781 7262497665529675781 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 7262497665529675781 7262497665529675797 (by decide) (by decide) (treeWith_odd_ok _ 26 5 7262497665529675781 7262497665529675813 (by decide) (by decide +kernel) ktree32_2_2_6) (treeWith_odd_ok _ 26 5 7262497665529675797 7262497665529675797 (by decide) (by decide +kernel) ktree32_2_2_7))))))

theorem ktree32_2_3_0 : treeWith (etherLeaf 32 32 39 16 2 3) 26 6 3631248832764837930 = true := by
  decide +kernel

theorem ktree32_2_3_1 : treeWith (etherLeaf 32 32 39 16 2 3) 26 6 3631248832764837946 = true := by
  decide +kernel

theorem ktree32_2_3_2 : treeWith (etherLeaf 32 32 39 16 2 3) 26 6 3631248832764837926 = true := by
  decide +kernel

theorem ktree32_2_3_3 : treeWith (etherLeaf 32 32 39 16 2 3) 26 6 3631248832764837910 = true := by
  decide +kernel

theorem ktree32_2_3_4 : treeWith (etherLeaf 32 32 39 16 2 3) 26 6 3631248832764837889 = true := by
  decide +kernel

theorem ktree32_2_3_5 : treeWith (etherLeaf 32 32 39 16 2 3) 26 6 3631248832764837937 = true := by
  decide +kernel

theorem ktree32_2_3_6 : treeWith (etherLeaf 32 32 39 16 2 3) 26 6 3631248832764837925 = true := by
  decide +kernel

theorem ktree32_2_3_7 : treeWith (etherLeaf 32 32 39 16 2 3) 26 6 3631248832764837909 = true := by
  decide +kernel

theorem ktree32_2_3 : etherTreeOK 32 32 39 16 2 3 = true := by
  unfold etherTreeOK
  rw [show etherTail 32 2 3 = 3631248832764837888 by decide +kernel]
  exact (treeWith_even_ok _ 31 0 3631248832764837888 3631248832764837889 (by decide) (by decide) (treeWith_odd_ok _ 30 1 3631248832764837888 3631248832764837890 (by decide) (by decide +kernel) (treeWith_even_ok _ 29 2 3631248832764837890 3631248832764837894 (by decide) (by decide) (treeWith_odd_ok _ 28 3 3631248832764837890 3631248832764837898 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 3631248832764837898 3631248832764837914 (by decide) (by decide) (treeWith_odd_ok _ 26 5 3631248832764837898 3631248832764837930 (by decide) (by decide +kernel) ktree32_2_3_0) (treeWith_odd_ok _ 26 5 3631248832764837914 3631248832764837946 (by decide) (by decide +kernel) ktree32_2_3_1))) (treeWith_odd_ok _ 28 3 3631248832764837894 3631248832764837894 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 3631248832764837894 3631248832764837910 (by decide) (by decide) (treeWith_odd_ok _ 26 5 3631248832764837894 3631248832764837926 (by decide) (by decide +kernel) ktree32_2_3_2) (treeWith_odd_ok _ 26 5 3631248832764837910 3631248832764837910 (by decide) (by decide +kernel) ktree32_2_3_3))))) (treeWith_odd_ok _ 30 1 3631248832764837889 3631248832764837889 (by decide) (by decide +kernel) (treeWith_even_ok _ 29 2 3631248832764837889 3631248832764837893 (by decide) (by decide) (treeWith_odd_ok _ 28 3 3631248832764837889 3631248832764837889 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 3631248832764837889 3631248832764837905 (by decide) (by decide) (treeWith_odd_ok _ 26 5 3631248832764837889 3631248832764837889 (by decide) (by decide +kernel) ktree32_2_3_4) (treeWith_odd_ok _ 26 5 3631248832764837905 3631248832764837937 (by decide) (by decide +kernel) ktree32_2_3_5))) (treeWith_odd_ok _ 28 3 3631248832764837893 3631248832764837893 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 3631248832764837893 3631248832764837909 (by decide) (by decide) (treeWith_odd_ok _ 26 5 3631248832764837893 3631248832764837925 (by decide) (by decide +kernel) ktree32_2_3_6) (treeWith_odd_ok _ 26 5 3631248832764837909 3631248832764837909 (by decide) (by decide +kernel) ktree32_2_3_7))))))

theorem ktree32_2_4_0 : treeWith (etherLeaf 32 32 39 16 2 4) 26 6 11038996451089711146 = true := by
  decide +kernel

theorem ktree32_2_4_1 : treeWith (etherLeaf 32 32 39 16 2 4) 26 6 11038996451089711162 = true := by
  decide +kernel

theorem ktree32_2_4_2 : treeWith (etherLeaf 32 32 39 16 2 4) 26 6 11038996451089711142 = true := by
  decide +kernel

theorem ktree32_2_4_3 : treeWith (etherLeaf 32 32 39 16 2 4) 26 6 11038996451089711126 = true := by
  decide +kernel

theorem ktree32_2_4_4 : treeWith (etherLeaf 32 32 39 16 2 4) 26 6 11038996451089711105 = true := by
  decide +kernel

theorem ktree32_2_4_5 : treeWith (etherLeaf 32 32 39 16 2 4) 26 6 11038996451089711153 = true := by
  decide +kernel

theorem ktree32_2_4_6 : treeWith (etherLeaf 32 32 39 16 2 4) 26 6 11038996451089711141 = true := by
  decide +kernel

theorem ktree32_2_4_7 : treeWith (etherLeaf 32 32 39 16 2 4) 26 6 11038996451089711125 = true := by
  decide +kernel

theorem ktree32_2_4 : etherTreeOK 32 32 39 16 2 4 = true := by
  unfold etherTreeOK
  rw [show etherTail 32 2 4 = 11038996451089711104 by decide +kernel]
  exact (treeWith_even_ok _ 31 0 11038996451089711104 11038996451089711105 (by decide) (by decide) (treeWith_odd_ok _ 30 1 11038996451089711104 11038996451089711106 (by decide) (by decide +kernel) (treeWith_even_ok _ 29 2 11038996451089711106 11038996451089711110 (by decide) (by decide) (treeWith_odd_ok _ 28 3 11038996451089711106 11038996451089711114 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 11038996451089711114 11038996451089711130 (by decide) (by decide) (treeWith_odd_ok _ 26 5 11038996451089711114 11038996451089711146 (by decide) (by decide +kernel) ktree32_2_4_0) (treeWith_odd_ok _ 26 5 11038996451089711130 11038996451089711162 (by decide) (by decide +kernel) ktree32_2_4_1))) (treeWith_odd_ok _ 28 3 11038996451089711110 11038996451089711110 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 11038996451089711110 11038996451089711126 (by decide) (by decide) (treeWith_odd_ok _ 26 5 11038996451089711110 11038996451089711142 (by decide) (by decide +kernel) ktree32_2_4_2) (treeWith_odd_ok _ 26 5 11038996451089711126 11038996451089711126 (by decide) (by decide +kernel) ktree32_2_4_3))))) (treeWith_odd_ok _ 30 1 11038996451089711105 11038996451089711105 (by decide) (by decide +kernel) (treeWith_even_ok _ 29 2 11038996451089711105 11038996451089711109 (by decide) (by decide) (treeWith_odd_ok _ 28 3 11038996451089711105 11038996451089711105 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 11038996451089711105 11038996451089711121 (by decide) (by decide) (treeWith_odd_ok _ 26 5 11038996451089711105 11038996451089711105 (by decide) (by decide +kernel) ktree32_2_4_4) (treeWith_odd_ok _ 26 5 11038996451089711121 11038996451089711153 (by decide) (by decide +kernel) ktree32_2_4_5))) (treeWith_odd_ok _ 28 3 11038996451089711109 11038996451089711109 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 11038996451089711109 11038996451089711125 (by decide) (by decide) (treeWith_odd_ok _ 26 5 11038996451089711109 11038996451089711141 (by decide) (by decide +kernel) ktree32_2_4_6) (treeWith_odd_ok _ 26 5 11038996451089711125 11038996451089711125 (by decide) (by decide +kernel) ktree32_2_4_7))))))

theorem ktree32_2_5_0 : treeWith (etherLeaf 32 32 39 16 2 5) 26 6 5519498223397371946 = true := by
  decide +kernel

theorem ktree32_2_5_1 : treeWith (etherLeaf 32 32 39 16 2 5) 26 6 5519498223397371962 = true := by
  decide +kernel

theorem ktree32_2_5_2 : treeWith (etherLeaf 32 32 39 16 2 5) 26 6 5519498223397371942 = true := by
  decide +kernel

theorem ktree32_2_5_3 : treeWith (etherLeaf 32 32 39 16 2 5) 26 6 5519498223397371926 = true := by
  decide +kernel

theorem ktree32_2_5_4 : treeWith (etherLeaf 32 32 39 16 2 5) 26 6 5519498223397371905 = true := by
  decide +kernel

theorem ktree32_2_5_5 : treeWith (etherLeaf 32 32 39 16 2 5) 26 6 5519498223397371953 = true := by
  decide +kernel

theorem ktree32_2_5_6 : treeWith (etherLeaf 32 32 39 16 2 5) 26 6 5519498223397371941 = true := by
  decide +kernel

theorem ktree32_2_5_7 : treeWith (etherLeaf 32 32 39 16 2 5) 26 6 5519498223397371925 = true := by
  decide +kernel

theorem ktree32_2_5 : etherTreeOK 32 32 39 16 2 5 = true := by
  unfold etherTreeOK
  rw [show etherTail 32 2 5 = 5519498223397371904 by decide +kernel]
  exact (treeWith_even_ok _ 31 0 5519498223397371904 5519498223397371905 (by decide) (by decide) (treeWith_odd_ok _ 30 1 5519498223397371904 5519498223397371906 (by decide) (by decide +kernel) (treeWith_even_ok _ 29 2 5519498223397371906 5519498223397371910 (by decide) (by decide) (treeWith_odd_ok _ 28 3 5519498223397371906 5519498223397371914 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 5519498223397371914 5519498223397371930 (by decide) (by decide) (treeWith_odd_ok _ 26 5 5519498223397371914 5519498223397371946 (by decide) (by decide +kernel) ktree32_2_5_0) (treeWith_odd_ok _ 26 5 5519498223397371930 5519498223397371962 (by decide) (by decide +kernel) ktree32_2_5_1))) (treeWith_odd_ok _ 28 3 5519498223397371910 5519498223397371910 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 5519498223397371910 5519498223397371926 (by decide) (by decide) (treeWith_odd_ok _ 26 5 5519498223397371910 5519498223397371942 (by decide) (by decide +kernel) ktree32_2_5_2) (treeWith_odd_ok _ 26 5 5519498223397371926 5519498223397371926 (by decide) (by decide +kernel) ktree32_2_5_3))))) (treeWith_odd_ok _ 30 1 5519498223397371905 5519498223397371905 (by decide) (by decide +kernel) (treeWith_even_ok _ 29 2 5519498223397371905 5519498223397371909 (by decide) (by decide) (treeWith_odd_ok _ 28 3 5519498223397371905 5519498223397371905 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 5519498223397371905 5519498223397371921 (by decide) (by decide) (treeWith_odd_ok _ 26 5 5519498223397371905 5519498223397371905 (by decide) (by decide +kernel) ktree32_2_5_4) (treeWith_odd_ok _ 26 5 5519498223397371921 5519498223397371953 (by decide) (by decide +kernel) ktree32_2_5_5))) (treeWith_odd_ok _ 28 3 5519498223397371909 5519498223397371909 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 5519498223397371909 5519498223397371925 (by decide) (by decide) (treeWith_odd_ok _ 26 5 5519498223397371909 5519498223397371941 (by decide) (by decide +kernel) ktree32_2_5_6) (treeWith_odd_ok _ 26 5 5519498223397371925 5519498223397371925 (by decide) (by decide +kernel) ktree32_2_5_7))))))

theorem ktree32_2_6_0 : treeWith (etherLeaf 32 32 39 16 2 6) 26 6 2759749111698685994 = true := by
  decide +kernel

theorem ktree32_2_6_1 : treeWith (etherLeaf 32 32 39 16 2 6) 26 6 2759749111698686010 = true := by
  decide +kernel

theorem ktree32_2_6_2 : treeWith (etherLeaf 32 32 39 16 2 6) 26 6 2759749111698685990 = true := by
  decide +kernel

theorem ktree32_2_6_3 : treeWith (etherLeaf 32 32 39 16 2 6) 26 6 2759749111698685974 = true := by
  decide +kernel

theorem ktree32_2_6_4 : treeWith (etherLeaf 32 32 39 16 2 6) 26 6 2759749111698685953 = true := by
  decide +kernel

theorem ktree32_2_6_5 : treeWith (etherLeaf 32 32 39 16 2 6) 26 6 2759749111698686001 = true := by
  decide +kernel

theorem ktree32_2_6_6 : treeWith (etherLeaf 32 32 39 16 2 6) 26 6 2759749111698685989 = true := by
  decide +kernel

theorem ktree32_2_6_7 : treeWith (etherLeaf 32 32 39 16 2 6) 26 6 2759749111698685973 = true := by
  decide +kernel

theorem ktree32_2_6 : etherTreeOK 32 32 39 16 2 6 = true := by
  unfold etherTreeOK
  rw [show etherTail 32 2 6 = 2759749111698685952 by decide +kernel]
  exact (treeWith_even_ok _ 31 0 2759749111698685952 2759749111698685953 (by decide) (by decide) (treeWith_odd_ok _ 30 1 2759749111698685952 2759749111698685954 (by decide) (by decide +kernel) (treeWith_even_ok _ 29 2 2759749111698685954 2759749111698685958 (by decide) (by decide) (treeWith_odd_ok _ 28 3 2759749111698685954 2759749111698685962 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 2759749111698685962 2759749111698685978 (by decide) (by decide) (treeWith_odd_ok _ 26 5 2759749111698685962 2759749111698685994 (by decide) (by decide +kernel) ktree32_2_6_0) (treeWith_odd_ok _ 26 5 2759749111698685978 2759749111698686010 (by decide) (by decide +kernel) ktree32_2_6_1))) (treeWith_odd_ok _ 28 3 2759749111698685958 2759749111698685958 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 2759749111698685958 2759749111698685974 (by decide) (by decide) (treeWith_odd_ok _ 26 5 2759749111698685958 2759749111698685990 (by decide) (by decide +kernel) ktree32_2_6_2) (treeWith_odd_ok _ 26 5 2759749111698685974 2759749111698685974 (by decide) (by decide +kernel) ktree32_2_6_3))))) (treeWith_odd_ok _ 30 1 2759749111698685953 2759749111698685953 (by decide) (by decide +kernel) (treeWith_even_ok _ 29 2 2759749111698685953 2759749111698685957 (by decide) (by decide) (treeWith_odd_ok _ 28 3 2759749111698685953 2759749111698685953 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 2759749111698685953 2759749111698685969 (by decide) (by decide) (treeWith_odd_ok _ 26 5 2759749111698685953 2759749111698685953 (by decide) (by decide +kernel) ktree32_2_6_4) (treeWith_odd_ok _ 26 5 2759749111698685969 2759749111698686001 (by decide) (by decide +kernel) ktree32_2_6_5))) (treeWith_odd_ok _ 28 3 2759749111698685957 2759749111698685957 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 2759749111698685957 2759749111698685973 (by decide) (by decide) (treeWith_odd_ok _ 26 5 2759749111698685957 2759749111698685989 (by decide) (by decide +kernel) ktree32_2_6_6) (treeWith_odd_ok _ 26 5 2759749111698685973 2759749111698685973 (by decide) (by decide +kernel) ktree32_2_6_7))))))

theorem ktree32_3_0_0 : treeWith (etherLeaf 32 32 39 16 3 0) 26 6 9150747056162209834 = true := by
  decide +kernel

theorem ktree32_3_0_1 : treeWith (etherLeaf 32 32 39 16 3 0) 26 6 9150747056162209850 = true := by
  decide +kernel

theorem ktree32_3_0_2 : treeWith (etherLeaf 32 32 39 16 3 0) 26 6 9150747056162209830 = true := by
  decide +kernel

theorem ktree32_3_0_3 : treeWith (etherLeaf 32 32 39 16 3 0) 26 6 9150747056162209814 = true := by
  decide +kernel

theorem ktree32_3_0_4 : treeWith (etherLeaf 32 32 39 16 3 0) 26 6 9150747056162209793 = true := by
  decide +kernel

theorem ktree32_3_0_5 : treeWith (etherLeaf 32 32 39 16 3 0) 26 6 9150747056162209841 = true := by
  decide +kernel

theorem ktree32_3_0_6 : treeWith (etherLeaf 32 32 39 16 3 0) 26 6 9150747056162209829 = true := by
  decide +kernel

theorem ktree32_3_0_7 : treeWith (etherLeaf 32 32 39 16 3 0) 26 6 9150747056162209813 = true := by
  decide +kernel

theorem ktree32_3_0 : etherTreeOK 32 32 39 16 3 0 = true := by
  unfold etherTreeOK
  rw [show etherTail 32 3 0 = 9150747056162209792 by decide +kernel]
  exact (treeWith_even_ok _ 31 0 9150747056162209792 9150747056162209793 (by decide) (by decide) (treeWith_odd_ok _ 30 1 9150747056162209792 9150747056162209794 (by decide) (by decide +kernel) (treeWith_even_ok _ 29 2 9150747056162209794 9150747056162209798 (by decide) (by decide) (treeWith_odd_ok _ 28 3 9150747056162209794 9150747056162209802 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 9150747056162209802 9150747056162209818 (by decide) (by decide) (treeWith_odd_ok _ 26 5 9150747056162209802 9150747056162209834 (by decide) (by decide +kernel) ktree32_3_0_0) (treeWith_odd_ok _ 26 5 9150747056162209818 9150747056162209850 (by decide) (by decide +kernel) ktree32_3_0_1))) (treeWith_odd_ok _ 28 3 9150747056162209798 9150747056162209798 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 9150747056162209798 9150747056162209814 (by decide) (by decide) (treeWith_odd_ok _ 26 5 9150747056162209798 9150747056162209830 (by decide) (by decide +kernel) ktree32_3_0_2) (treeWith_odd_ok _ 26 5 9150747056162209814 9150747056162209814 (by decide) (by decide +kernel) ktree32_3_0_3))))) (treeWith_odd_ok _ 30 1 9150747056162209793 9150747056162209793 (by decide) (by decide +kernel) (treeWith_even_ok _ 29 2 9150747056162209793 9150747056162209797 (by decide) (by decide) (treeWith_odd_ok _ 28 3 9150747056162209793 9150747056162209793 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 9150747056162209793 9150747056162209809 (by decide) (by decide) (treeWith_odd_ok _ 26 5 9150747056162209793 9150747056162209793 (by decide) (by decide +kernel) ktree32_3_0_4) (treeWith_odd_ok _ 26 5 9150747056162209809 9150747056162209841 (by decide) (by decide +kernel) ktree32_3_0_5))) (treeWith_odd_ok _ 28 3 9150747056162209797 9150747056162209797 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 9150747056162209797 9150747056162209813 (by decide) (by decide) (treeWith_odd_ok _ 26 5 9150747056162209797 9150747056162209829 (by decide) (by decide +kernel) ktree32_3_0_6) (treeWith_odd_ok _ 26 5 9150747056162209813 9150747056162209813 (by decide) (by decide +kernel) ktree32_3_0_7))))))

theorem ktree32_3_1_0 : treeWith (etherLeaf 32 32 39 16 3 1) 26 6 13798745562788397098 = true := by
  decide +kernel

theorem ktree32_3_1_1 : treeWith (etherLeaf 32 32 39 16 3 1) 26 6 13798745562788397114 = true := by
  decide +kernel

theorem ktree32_3_1_2 : treeWith (etherLeaf 32 32 39 16 3 1) 26 6 13798745562788397094 = true := by
  decide +kernel

theorem ktree32_3_1_3 : treeWith (etherLeaf 32 32 39 16 3 1) 26 6 13798745562788397078 = true := by
  decide +kernel

theorem ktree32_3_1_4 : treeWith (etherLeaf 32 32 39 16 3 1) 26 6 13798745562788397057 = true := by
  decide +kernel

theorem ktree32_3_1_5 : treeWith (etherLeaf 32 32 39 16 3 1) 26 6 13798745562788397105 = true := by
  decide +kernel

theorem ktree32_3_1_6 : treeWith (etherLeaf 32 32 39 16 3 1) 26 6 13798745562788397093 = true := by
  decide +kernel

theorem ktree32_3_1_7 : treeWith (etherLeaf 32 32 39 16 3 1) 26 6 13798745562788397077 = true := by
  decide +kernel

theorem ktree32_3_1 : etherTreeOK 32 32 39 16 3 1 = true := by
  unfold etherTreeOK
  rw [show etherTail 32 3 1 = 13798745562788397056 by decide +kernel]
  exact (treeWith_even_ok _ 31 0 13798745562788397056 13798745562788397057 (by decide) (by decide) (treeWith_odd_ok _ 30 1 13798745562788397056 13798745562788397058 (by decide) (by decide +kernel) (treeWith_even_ok _ 29 2 13798745562788397058 13798745562788397062 (by decide) (by decide) (treeWith_odd_ok _ 28 3 13798745562788397058 13798745562788397066 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 13798745562788397066 13798745562788397082 (by decide) (by decide) (treeWith_odd_ok _ 26 5 13798745562788397066 13798745562788397098 (by decide) (by decide +kernel) ktree32_3_1_0) (treeWith_odd_ok _ 26 5 13798745562788397082 13798745562788397114 (by decide) (by decide +kernel) ktree32_3_1_1))) (treeWith_odd_ok _ 28 3 13798745562788397062 13798745562788397062 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 13798745562788397062 13798745562788397078 (by decide) (by decide) (treeWith_odd_ok _ 26 5 13798745562788397062 13798745562788397094 (by decide) (by decide +kernel) ktree32_3_1_2) (treeWith_odd_ok _ 26 5 13798745562788397078 13798745562788397078 (by decide) (by decide +kernel) ktree32_3_1_3))))) (treeWith_odd_ok _ 30 1 13798745562788397057 13798745562788397057 (by decide) (by decide +kernel) (treeWith_even_ok _ 29 2 13798745562788397057 13798745562788397061 (by decide) (by decide) (treeWith_odd_ok _ 28 3 13798745562788397057 13798745562788397057 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 13798745562788397057 13798745562788397073 (by decide) (by decide) (treeWith_odd_ok _ 26 5 13798745562788397057 13798745562788397057 (by decide) (by decide +kernel) ktree32_3_1_4) (treeWith_odd_ok _ 26 5 13798745562788397073 13798745562788397105 (by decide) (by decide +kernel) ktree32_3_1_5))) (treeWith_odd_ok _ 28 3 13798745562788397061 13798745562788397061 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 13798745562788397061 13798745562788397077 (by decide) (by decide) (treeWith_odd_ok _ 26 5 13798745562788397061 13798745562788397093 (by decide) (by decide +kernel) ktree32_3_1_6) (treeWith_odd_ok _ 26 5 13798745562788397077 13798745562788397077 (by decide) (by decide +kernel) ktree32_3_1_7))))))

theorem ktree32_3_2_0 : treeWith (etherLeaf 32 32 39 16 3 2) 26 6 16122744816101490730 = true := by
  decide +kernel

theorem ktree32_3_2_1 : treeWith (etherLeaf 32 32 39 16 3 2) 26 6 16122744816101490746 = true := by
  decide +kernel

theorem ktree32_3_2_2 : treeWith (etherLeaf 32 32 39 16 3 2) 26 6 16122744816101490726 = true := by
  decide +kernel

theorem ktree32_3_2_3 : treeWith (etherLeaf 32 32 39 16 3 2) 26 6 16122744816101490710 = true := by
  decide +kernel

theorem ktree32_3_2_4 : treeWith (etherLeaf 32 32 39 16 3 2) 26 6 16122744816101490689 = true := by
  decide +kernel

theorem ktree32_3_2_5 : treeWith (etherLeaf 32 32 39 16 3 2) 26 6 16122744816101490737 = true := by
  decide +kernel

theorem ktree32_3_2_6 : treeWith (etherLeaf 32 32 39 16 3 2) 26 6 16122744816101490725 = true := by
  decide +kernel

theorem ktree32_3_2_7 : treeWith (etherLeaf 32 32 39 16 3 2) 26 6 16122744816101490709 = true := by
  decide +kernel

theorem ktree32_3_2 : etherTreeOK 32 32 39 16 3 2 = true := by
  unfold etherTreeOK
  rw [show etherTail 32 3 2 = 16122744816101490688 by decide +kernel]
  exact (treeWith_even_ok _ 31 0 16122744816101490688 16122744816101490689 (by decide) (by decide) (treeWith_odd_ok _ 30 1 16122744816101490688 16122744816101490690 (by decide) (by decide +kernel) (treeWith_even_ok _ 29 2 16122744816101490690 16122744816101490694 (by decide) (by decide) (treeWith_odd_ok _ 28 3 16122744816101490690 16122744816101490698 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 16122744816101490698 16122744816101490714 (by decide) (by decide) (treeWith_odd_ok _ 26 5 16122744816101490698 16122744816101490730 (by decide) (by decide +kernel) ktree32_3_2_0) (treeWith_odd_ok _ 26 5 16122744816101490714 16122744816101490746 (by decide) (by decide +kernel) ktree32_3_2_1))) (treeWith_odd_ok _ 28 3 16122744816101490694 16122744816101490694 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 16122744816101490694 16122744816101490710 (by decide) (by decide) (treeWith_odd_ok _ 26 5 16122744816101490694 16122744816101490726 (by decide) (by decide +kernel) ktree32_3_2_2) (treeWith_odd_ok _ 26 5 16122744816101490710 16122744816101490710 (by decide) (by decide +kernel) ktree32_3_2_3))))) (treeWith_odd_ok _ 30 1 16122744816101490689 16122744816101490689 (by decide) (by decide +kernel) (treeWith_even_ok _ 29 2 16122744816101490689 16122744816101490693 (by decide) (by decide) (treeWith_odd_ok _ 28 3 16122744816101490689 16122744816101490689 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 16122744816101490689 16122744816101490705 (by decide) (by decide) (treeWith_odd_ok _ 26 5 16122744816101490689 16122744816101490689 (by decide) (by decide +kernel) ktree32_3_2_4) (treeWith_odd_ok _ 26 5 16122744816101490705 16122744816101490737 (by decide) (by decide +kernel) ktree32_3_2_5))) (treeWith_odd_ok _ 28 3 16122744816101490693 16122744816101490693 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 16122744816101490693 16122744816101490709 (by decide) (by decide) (treeWith_odd_ok _ 26 5 16122744816101490693 16122744816101490725 (by decide) (by decide +kernel) ktree32_3_2_6) (treeWith_odd_ok _ 26 5 16122744816101490709 16122744816101490709 (by decide) (by decide +kernel) ktree32_3_2_7))))))

theorem ktree32_3_3_0 : treeWith (etherLeaf 32 32 39 16 3 3) 26 6 17284744442758037546 = true := by
  decide +kernel

theorem ktree32_3_3_1 : treeWith (etherLeaf 32 32 39 16 3 3) 26 6 17284744442758037562 = true := by
  decide +kernel

theorem ktree32_3_3_2 : treeWith (etherLeaf 32 32 39 16 3 3) 26 6 17284744442758037542 = true := by
  decide +kernel

theorem ktree32_3_3_3 : treeWith (etherLeaf 32 32 39 16 3 3) 26 6 17284744442758037526 = true := by
  decide +kernel

theorem ktree32_3_3_4 : treeWith (etherLeaf 32 32 39 16 3 3) 26 6 17284744442758037505 = true := by
  decide +kernel

theorem ktree32_3_3_5 : treeWith (etherLeaf 32 32 39 16 3 3) 26 6 17284744442758037553 = true := by
  decide +kernel

theorem ktree32_3_3_6 : treeWith (etherLeaf 32 32 39 16 3 3) 26 6 17284744442758037541 = true := by
  decide +kernel

theorem ktree32_3_3_7 : treeWith (etherLeaf 32 32 39 16 3 3) 26 6 17284744442758037525 = true := by
  decide +kernel

theorem ktree32_3_3 : etherTreeOK 32 32 39 16 3 3 = true := by
  unfold etherTreeOK
  rw [show etherTail 32 3 3 = 17284744442758037504 by decide +kernel]
  exact (treeWith_even_ok _ 31 0 17284744442758037504 17284744442758037505 (by decide) (by decide) (treeWith_odd_ok _ 30 1 17284744442758037504 17284744442758037506 (by decide) (by decide +kernel) (treeWith_even_ok _ 29 2 17284744442758037506 17284744442758037510 (by decide) (by decide) (treeWith_odd_ok _ 28 3 17284744442758037506 17284744442758037514 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 17284744442758037514 17284744442758037530 (by decide) (by decide) (treeWith_odd_ok _ 26 5 17284744442758037514 17284744442758037546 (by decide) (by decide +kernel) ktree32_3_3_0) (treeWith_odd_ok _ 26 5 17284744442758037530 17284744442758037562 (by decide) (by decide +kernel) ktree32_3_3_1))) (treeWith_odd_ok _ 28 3 17284744442758037510 17284744442758037510 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 17284744442758037510 17284744442758037526 (by decide) (by decide) (treeWith_odd_ok _ 26 5 17284744442758037510 17284744442758037542 (by decide) (by decide +kernel) ktree32_3_3_2) (treeWith_odd_ok _ 26 5 17284744442758037526 17284744442758037526 (by decide) (by decide +kernel) ktree32_3_3_3))))) (treeWith_odd_ok _ 30 1 17284744442758037505 17284744442758037505 (by decide) (by decide +kernel) (treeWith_even_ok _ 29 2 17284744442758037505 17284744442758037509 (by decide) (by decide) (treeWith_odd_ok _ 28 3 17284744442758037505 17284744442758037505 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 17284744442758037505 17284744442758037521 (by decide) (by decide) (treeWith_odd_ok _ 26 5 17284744442758037505 17284744442758037505 (by decide) (by decide +kernel) ktree32_3_3_4) (treeWith_odd_ok _ 26 5 17284744442758037521 17284744442758037553 (by decide) (by decide +kernel) ktree32_3_3_5))) (treeWith_odd_ok _ 28 3 17284744442758037509 17284744442758037509 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 17284744442758037509 17284744442758037525 (by decide) (by decide) (treeWith_odd_ok _ 26 5 17284744442758037509 17284744442758037541 (by decide) (by decide +kernel) ktree32_3_3_6) (treeWith_odd_ok _ 26 5 17284744442758037525 17284744442758037525 (by decide) (by decide +kernel) ktree32_3_3_7))))))

theorem ktree32_3_4_0 : treeWith (etherLeaf 32 32 39 16 3 4) 26 6 17865744258233794602 = true := by
  decide +kernel

theorem ktree32_3_4_1 : treeWith (etherLeaf 32 32 39 16 3 4) 26 6 17865744258233794618 = true := by
  decide +kernel

theorem ktree32_3_4_2 : treeWith (etherLeaf 32 32 39 16 3 4) 26 6 17865744258233794598 = true := by
  decide +kernel

theorem ktree32_3_4_3 : treeWith (etherLeaf 32 32 39 16 3 4) 26 6 17865744258233794582 = true := by
  decide +kernel

theorem ktree32_3_4_4 : treeWith (etherLeaf 32 32 39 16 3 4) 26 6 17865744258233794561 = true := by
  decide +kernel

theorem ktree32_3_4_5 : treeWith (etherLeaf 32 32 39 16 3 4) 26 6 17865744258233794609 = true := by
  decide +kernel

theorem ktree32_3_4_6 : treeWith (etherLeaf 32 32 39 16 3 4) 26 6 17865744258233794597 = true := by
  decide +kernel

theorem ktree32_3_4_7 : treeWith (etherLeaf 32 32 39 16 3 4) 26 6 17865744258233794581 = true := by
  decide +kernel

theorem ktree32_3_4 : etherTreeOK 32 32 39 16 3 4 = true := by
  unfold etherTreeOK
  rw [show etherTail 32 3 4 = 17865744258233794560 by decide +kernel]
  exact (treeWith_even_ok _ 31 0 17865744258233794560 17865744258233794561 (by decide) (by decide) (treeWith_odd_ok _ 30 1 17865744258233794560 17865744258233794562 (by decide) (by decide +kernel) (treeWith_even_ok _ 29 2 17865744258233794562 17865744258233794566 (by decide) (by decide) (treeWith_odd_ok _ 28 3 17865744258233794562 17865744258233794570 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 17865744258233794570 17865744258233794586 (by decide) (by decide) (treeWith_odd_ok _ 26 5 17865744258233794570 17865744258233794602 (by decide) (by decide +kernel) ktree32_3_4_0) (treeWith_odd_ok _ 26 5 17865744258233794586 17865744258233794618 (by decide) (by decide +kernel) ktree32_3_4_1))) (treeWith_odd_ok _ 28 3 17865744258233794566 17865744258233794566 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 17865744258233794566 17865744258233794582 (by decide) (by decide) (treeWith_odd_ok _ 26 5 17865744258233794566 17865744258233794598 (by decide) (by decide +kernel) ktree32_3_4_2) (treeWith_odd_ok _ 26 5 17865744258233794582 17865744258233794582 (by decide) (by decide +kernel) ktree32_3_4_3))))) (treeWith_odd_ok _ 30 1 17865744258233794561 17865744258233794561 (by decide) (by decide +kernel) (treeWith_even_ok _ 29 2 17865744258233794561 17865744258233794565 (by decide) (by decide) (treeWith_odd_ok _ 28 3 17865744258233794561 17865744258233794561 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 17865744258233794561 17865744258233794577 (by decide) (by decide) (treeWith_odd_ok _ 26 5 17865744258233794561 17865744258233794561 (by decide) (by decide +kernel) ktree32_3_4_4) (treeWith_odd_ok _ 26 5 17865744258233794577 17865744258233794609 (by decide) (by decide +kernel) ktree32_3_4_5))) (treeWith_odd_ok _ 28 3 17865744258233794565 17865744258233794565 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 17865744258233794565 17865744258233794581 (by decide) (by decide) (treeWith_odd_ok _ 26 5 17865744258233794565 17865744258233794597 (by decide) (by decide +kernel) ktree32_3_4_6) (treeWith_odd_ok _ 26 5 17865744258233794581 17865744258233794581 (by decide) (by decide +kernel) ktree32_3_4_7))))))

theorem ktree32_3_5_0 : treeWith (etherLeaf 32 32 39 16 3 5) 26 6 18156244163824189482 = true := by
  decide +kernel

theorem ktree32_3_5_1 : treeWith (etherLeaf 32 32 39 16 3 5) 26 6 18156244163824189498 = true := by
  decide +kernel

theorem ktree32_3_5_2 : treeWith (etherLeaf 32 32 39 16 3 5) 26 6 18156244163824189478 = true := by
  decide +kernel

theorem ktree32_3_5_3 : treeWith (etherLeaf 32 32 39 16 3 5) 26 6 18156244163824189462 = true := by
  decide +kernel

theorem ktree32_3_5_4 : treeWith (etherLeaf 32 32 39 16 3 5) 26 6 18156244163824189441 = true := by
  decide +kernel

theorem ktree32_3_5_5 : treeWith (etherLeaf 32 32 39 16 3 5) 26 6 18156244163824189489 = true := by
  decide +kernel

theorem ktree32_3_5_6 : treeWith (etherLeaf 32 32 39 16 3 5) 26 6 18156244163824189477 = true := by
  decide +kernel

theorem ktree32_3_5_7 : treeWith (etherLeaf 32 32 39 16 3 5) 26 6 18156244163824189461 = true := by
  decide +kernel

theorem ktree32_3_5 : etherTreeOK 32 32 39 16 3 5 = true := by
  unfold etherTreeOK
  rw [show etherTail 32 3 5 = 18156244163824189440 by decide +kernel]
  exact (treeWith_even_ok _ 31 0 18156244163824189440 18156244163824189441 (by decide) (by decide) (treeWith_odd_ok _ 30 1 18156244163824189440 18156244163824189442 (by decide) (by decide +kernel) (treeWith_even_ok _ 29 2 18156244163824189442 18156244163824189446 (by decide) (by decide) (treeWith_odd_ok _ 28 3 18156244163824189442 18156244163824189450 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 18156244163824189450 18156244163824189466 (by decide) (by decide) (treeWith_odd_ok _ 26 5 18156244163824189450 18156244163824189482 (by decide) (by decide +kernel) ktree32_3_5_0) (treeWith_odd_ok _ 26 5 18156244163824189466 18156244163824189498 (by decide) (by decide +kernel) ktree32_3_5_1))) (treeWith_odd_ok _ 28 3 18156244163824189446 18156244163824189446 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 18156244163824189446 18156244163824189462 (by decide) (by decide) (treeWith_odd_ok _ 26 5 18156244163824189446 18156244163824189478 (by decide) (by decide +kernel) ktree32_3_5_2) (treeWith_odd_ok _ 26 5 18156244163824189462 18156244163824189462 (by decide) (by decide +kernel) ktree32_3_5_3))))) (treeWith_odd_ok _ 30 1 18156244163824189441 18156244163824189441 (by decide) (by decide +kernel) (treeWith_even_ok _ 29 2 18156244163824189441 18156244163824189445 (by decide) (by decide) (treeWith_odd_ok _ 28 3 18156244163824189441 18156244163824189441 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 18156244163824189441 18156244163824189457 (by decide) (by decide) (treeWith_odd_ok _ 26 5 18156244163824189441 18156244163824189441 (by decide) (by decide +kernel) ktree32_3_5_4) (treeWith_odd_ok _ 26 5 18156244163824189457 18156244163824189489 (by decide) (by decide +kernel) ktree32_3_5_5))) (treeWith_odd_ok _ 28 3 18156244163824189445 18156244163824189445 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 18156244163824189445 18156244163824189461 (by decide) (by decide) (treeWith_odd_ok _ 26 5 18156244163824189445 18156244163824189477 (by decide) (by decide +kernel) ktree32_3_5_6) (treeWith_odd_ok _ 26 5 18156244163824189461 18156244163824189461 (by decide) (by decide +kernel) ktree32_3_5_7))))))

theorem ktree32_3_6_0 : treeWith (etherLeaf 32 32 39 16 3 6) 26 6 18301494116619386922 = true := by
  decide +kernel

theorem ktree32_3_6_1 : treeWith (etherLeaf 32 32 39 16 3 6) 26 6 18301494116619386938 = true := by
  decide +kernel

theorem ktree32_3_6_2 : treeWith (etherLeaf 32 32 39 16 3 6) 26 6 18301494116619386918 = true := by
  decide +kernel

theorem ktree32_3_6_3 : treeWith (etherLeaf 32 32 39 16 3 6) 26 6 18301494116619386902 = true := by
  decide +kernel

theorem ktree32_3_6_4 : treeWith (etherLeaf 32 32 39 16 3 6) 26 6 18301494116619386881 = true := by
  decide +kernel

theorem ktree32_3_6_5 : treeWith (etherLeaf 32 32 39 16 3 6) 26 6 18301494116619386929 = true := by
  decide +kernel

theorem ktree32_3_6_6 : treeWith (etherLeaf 32 32 39 16 3 6) 26 6 18301494116619386917 = true := by
  decide +kernel

theorem ktree32_3_6_7 : treeWith (etherLeaf 32 32 39 16 3 6) 26 6 18301494116619386901 = true := by
  decide +kernel

theorem ktree32_3_6 : etherTreeOK 32 32 39 16 3 6 = true := by
  unfold etherTreeOK
  rw [show etherTail 32 3 6 = 18301494116619386880 by decide +kernel]
  exact (treeWith_even_ok _ 31 0 18301494116619386880 18301494116619386881 (by decide) (by decide) (treeWith_odd_ok _ 30 1 18301494116619386880 18301494116619386882 (by decide) (by decide +kernel) (treeWith_even_ok _ 29 2 18301494116619386882 18301494116619386886 (by decide) (by decide) (treeWith_odd_ok _ 28 3 18301494116619386882 18301494116619386890 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 18301494116619386890 18301494116619386906 (by decide) (by decide) (treeWith_odd_ok _ 26 5 18301494116619386890 18301494116619386922 (by decide) (by decide +kernel) ktree32_3_6_0) (treeWith_odd_ok _ 26 5 18301494116619386906 18301494116619386938 (by decide) (by decide +kernel) ktree32_3_6_1))) (treeWith_odd_ok _ 28 3 18301494116619386886 18301494116619386886 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 18301494116619386886 18301494116619386902 (by decide) (by decide) (treeWith_odd_ok _ 26 5 18301494116619386886 18301494116619386918 (by decide) (by decide +kernel) ktree32_3_6_2) (treeWith_odd_ok _ 26 5 18301494116619386902 18301494116619386902 (by decide) (by decide +kernel) ktree32_3_6_3))))) (treeWith_odd_ok _ 30 1 18301494116619386881 18301494116619386881 (by decide) (by decide +kernel) (treeWith_even_ok _ 29 2 18301494116619386881 18301494116619386885 (by decide) (by decide) (treeWith_odd_ok _ 28 3 18301494116619386881 18301494116619386881 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 18301494116619386881 18301494116619386897 (by decide) (by decide) (treeWith_odd_ok _ 26 5 18301494116619386881 18301494116619386881 (by decide) (by decide +kernel) ktree32_3_6_4) (treeWith_odd_ok _ 26 5 18301494116619386897 18301494116619386929 (by decide) (by decide +kernel) ktree32_3_6_5))) (treeWith_odd_ok _ 28 3 18301494116619386885 18301494116619386885 (by decide) (by decide +kernel) (treeWith_even_ok _ 27 4 18301494116619386885 18301494116619386901 (by decide) (by decide) (treeWith_odd_ok _ 26 5 18301494116619386885 18301494116619386917 (by decide) (by decide +kernel) ktree32_3_6_6) (treeWith_odd_ok _ 26 5 18301494116619386901 18301494116619386901 (by decide) (by decide +kernel) ktree32_3_6_7))))))

theorem ktree32 (a o : Nat) (ha : a < 4) (ho : o < 7) : etherTreeOK 32 32 39 16 a o = true :=
  match a, o, ha, ho with
  | 0, 0, _, _ => ktree32_0_0
  | 0, 1, _, _ => ktree32_0_1
  | 0, 2, _, _ => ktree32_0_2
  | 0, 3, _, _ => ktree32_0_3
  | 0, 4, _, _ => ktree32_0_4
  | 0, 5, _, _ => ktree32_0_5
  | 0, 6, _, _ => ktree32_0_6
  | 1, 0, _, _ => ktree32_1_0
  | 1, 1, _, _ => ktree32_1_1
  | 1, 2, _, _ => ktree32_1_2
  | 1, 3, _, _ => ktree32_1_3
  | 1, 4, _, _ => ktree32_1_4
  | 1, 5, _, _ => ktree32_1_5
  | 1, 6, _, _ => ktree32_1_6
  | 2, 0, _, _ => ktree32_2_0
  | 2, 1, _, _ => ktree32_2_1
  | 2, 2, _, _ => ktree32_2_2
  | 2, 3, _, _ => ktree32_2_3
  | 2, 4, _, _ => ktree32_2_4
  | 2, 5, _, _ => ktree32_2_5
  | 2, 6, _, _ => ktree32_2_6
  | 3, 0, _, _ => ktree32_3_0
  | 3, 1, _, _ => ktree32_3_1
  | 3, 2, _, _ => ktree32_3_2
  | 3, 3, _, _ => ktree32_3_3
  | 3, 4, _, _ => ktree32_3_4
  | 3, 5, _, _ => ktree32_3_5
  | 3, 6, _, _ => ktree32_3_6
  | a + 4, _, ha, _ => absurd ha (by omega)
  | _, o + 7, _, ho => absurd ho (by omega)

/-! ### Every point of `K` with the ether from cell 32 on settles -/

/-- **The defect of every point of `K` whose tail from cell 32 on is the ether stays below cell 39.** If `u` is in `K`
and its cells from `p ≤ 32` on are the ether at the alignment `(a, o)`, then at every step `t` the cells from 39 on
are the ether at phase `a + t`. -/
theorem ether_k_tail_clear32 (u : Nat → Bool) (a o p : Nat) (hp : p ≤ 32)
    (hu : ∀ j, p ≤ j → u j = eth a (j + o)) (hK : InK u) :
    ∀ t j, 39 ≤ j → heldOrbit u t j = eth (a + t) (j + o) := by
  have hu' : ∀ j, 32 ≤ j → u j = eth (a % 4) (j + o % 7) := fun j hj => by
    rw [hu j (by omega)]; exact eth_congr (by omega) (by omega)
  have hc := clear_of_etherTree 32 32 39 16 (a % 4) (o % 7) (by decide) (by decide) (by decide) (by decide)
    (ktree32 (a % 4) (o % 7) (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))) u hu' hK
  intro t j hj
  rw [heldOrbit_eq_defect u (a % 4) (o % 7) t j, hc t j hj, Bool.false_xor]
  exact eth_congr (by omega) (by omega)

/-- **Every point of `K` whose tail from cell 32 on is the ether has an eventually periodic orbit.** -/
theorem ether_k_tail_eventually_periodic32 (u : Nat → Bool) (a o p : Nat) (hp : p ≤ 32)
    (hu : ∀ j, p ≤ j → u j = eth a (j + o)) (hK : InK u) :
    ∃ T P, 0 < P ∧ ∀ t, T ≤ t → heldOrbit u (t + P) = heldOrbit u t := by
  refine eventually_periodic_of_clear (a := a) (o := o) (L := 39) fun t j hj => ?_
  unfold defect
  rw [ether_k_tail_clear32 u a o p hp hu hK t j hj]
  cases eth (a + t) (j + o) <;> rfl

/-- **Conjecture (R) for the points of `K` whose tail from cell 32 on is the ether**: every 2-adic integer in `InK`
whose bits from `p ≤ 32` on are the ether at one of its alignments has an eventually periodic itinerary. -/
theorem ether_k_tail_itinerary32 (u : Nat → Bool) (a o p : Nat) (hp : p ≤ 32)
    (hu : ∀ j, p ≤ j → u j = eth a (j + o)) (hK : InK u) :
    ∃ pre n, 0 < n ∧ ∀ s, pre ≤ s → itinerary u (s + n) = itinerary u s := by
  obtain ⟨T, P, hP, h⟩ := ether_k_tail_eventually_periodic32 u a o p hp hu hK
  exact itinerary_of_eventually_periodic hP h

end Rule30Open
