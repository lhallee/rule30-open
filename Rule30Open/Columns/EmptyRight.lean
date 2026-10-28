module

public import Ruliology.CellularAutomata.Rule30Coupled
public import Ruliology.CellularAutomata.Rule30FiniteMaskedJen
public import Ruliology.CellularAutomata.Rule30EtherThreeReach
public import Ruliology.CellularAutomata.Rule30ZeroBoundarySmall

/-!
# Small right halves: no center column repeats a word of period four, nor 001 against a white one

The kit's milestone for period 2, `Rule30PeriodTwoSideways.CQ01Empty`, asks whether a finite configuration whose cells
right of the center are white can keep its center alternating forever, and is open. For the three words of least
period four it is settled here for every right half of at most six cells, in every phase and whatever the left half:
no finite configuration whose cells right of column 6 are white has a center column that repeats `0001`, `0011` or
`0111` (`smallRight_0001`, `smallRight_0011`, `smallRight_0111`). For `001` the white right half is settled
(`emptyRight_001`).

The right half of such a configuration is driven by the word (`Rule30Coupled.right_eq_drv`), whatever the left half
holds. Each of the 64 right halves of at most six cells is in the kit's ether-and-wall family by step 521 (`entries`,
`smallCheck`, a kernel computation of the driven half as bit masks with `Rule30EtherThree.rowN`). The family is a trap
(`Rule30Ether.trap_invariant`), and in it column 1 repeats with period 4 at the white times of the center, which masked
Jen for finite configurations (`Rule30FiniteMaskedJen.masked_jen`) forbids beside a center of period 4
(`no_finite_of_family`). This is the kit's `absorption_excludes`, carried from the single seed to every finite
configuration, for the right halves it is checked on. For `001` the trap is the kit's `Rule30EtherThree.t001`, which
the white right half enters at step 1268 to 1270 by phase, and `no_finite_of_ptrap` carries the kit's `PTrap.trap` the
same way.

The natural-language argument is `EmptyRight.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

open Ruliology.CellularAutomata
open Rule30Realization Rule30Ether Rule30StripCertificates Rule30PeriodTwoSideways

/-- **Entry excludes the word.** If the right half of a finite configuration whose center repeats `w` from phase `φ`,
driven by that center, is in the ether-and-wall family at some time for an alignment `(j0, s)` of `w`, contradiction. -/
theorem no_finite_of_family {w : List Bool} {j0 s : Nat} (hal : aligned w j0 s = true) (φ : Nat)
    {y : Int → Bool} (hfin : FinConfig y) (hc : ∀ t, evol y t 0 = wordAt w (t + φ))
    (hw : ∃ ψ, wordAt w ψ = true) (t1 : Nat)
    (hfam : InFamily (drv (fun t => wordAt w (t + φ)) fun p => y (p : Int)) j0 (s + φ) t1) : False := by
  obtain ⟨k, hk, hE, hW⟩ := hfam
  have h0 : ∀ t, t1 ≤ t →
      drv (fun t => wordAt w (t + φ)) (fun p => y (p : Int)) t 0 = ether j0 (t + (s + φ)) := by
    intro t _
    rw [drv_col0, ← aligned_spec hal (t + φ)]
    exact ether_congr rfl (by omega)
  have inv := trap_invariant (drv_isR30 _ _) j0 (s + φ) k t1 hk h0 hE hW
  -- column 1 at the white times of column 0 is the ether column `j0 + 1`
  have key : ∀ t, t1 ≤ t → drv (fun t => wordAt w (t + φ)) (fun p => y (p : Int)) t 0 = false →
      drv (fun t => wordAt w (t + φ)) (fun p => y (p : Int)) t 1 = ether (j0 + 1) (t + (s + φ)) := by
    intro t ht hwt
    obtain ⟨hE', hW'⟩ := inv (t - t1)
    rw [show t1 + (t - t1) = t by omega] at hE' hW'
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · subst hk0
      have hw2 : ether 2 ((t + (s + φ)) % 4) = false := by
        have e := hE' 0 (Nat.le_refl 0)
        rw [hwt] at e
        rw [e]; exact ether_congr (by omega) (by omega)
      have hhead := (wall_facts hW').1 hw2
      rw [rowOf_head] at hhead
      rw [hhead]; exact ether_congr (by omega) (by omega)
    · exact hE' 1 hk0
  -- the configuration's columns 0 and 1 are those of the driven half
  have hω : (fun t => evol y t 0) = fun t => wordAt w (t + φ) := funext hc
  have c0 : ∀ t, evol y t 0 = drv (fun t => wordAt w (t + φ)) (fun p => y (p : Int)) t 0 := fun t => by
    rw [hc, drv_col0]
  have c1 : ∀ t, evol y t ((1 : Nat) : Int) = drv (fun t => wordAt w (t + φ)) (fun p => y (p : Int)) t 1 :=
    fun t => by rw [Rule30Coupled.right_eq_drv y t 1, hω]
  have hne : ∃ p, y p = true := by
    refine Classical.byContradiction fun hz => ?_
    have hz' : ∀ p, y p = false := fun p => by
      cases h : y p
      · rfl
      · exact absurd ⟨p, h⟩ hz
    obtain ⟨ψ, hψ⟩ := hw
    have e := hc (ψ + 3 * φ)
    have e2 : wordAt w (ψ + 3 * φ + φ) = wordAt w ψ := by
      unfold wordAt; rw [show (ψ + 3 * φ + φ) % 4 = ψ % 4 by omega]
    rw [Rule30Coupled.evol_zero hz', e2, hψ] at e
    exact absurd e (by decide)
  obtain ⟨lo, hlo, hzero⟩ := Rule30FiniteConfigs.exists_leftmost hfin hne
  refine Rule30FiniteMaskedJen.masked_jen hlo hzero 0 (T := t1) (P := 4) (by decide) ?_ ?_
  · intro t ht
    rw [c0, c0, h0 (t + 4) (by omega), h0 t ht]
    exact ether_congr rfl (by omega)
  · intro t ht hwt
    rw [c0] at hwt
    have hw4 : drv (fun t => wordAt w (t + φ)) (fun p => y (p : Int)) (t + 4) 0 = false := by
      rw [h0 (t + 4) (by omega), ← hwt, h0 t ht]
      exact ether_congr rfl (by omega)
    show evol y (t + 4) ((1 : Nat) : Int) = evol y t ((1 : Nat) : Int)
    rw [c1, c1, key (t + 4) (by omega) hw4, key t ht hwt]
    exact ether_congr rfl (by omega)

/-- The family condition at time `t1` and depth `k`, read off the bit mask `rowN c x0 t1` of the driven right half
(bit `i` is column `i + 1`): column `k` is a B3, columns `1 .. k` carry the ether, and the next 13 a wall state. -/
def familyCheck (c : Nat → Bool) (x0 j0 s t1 k : Nat) : Bool :=
  (j0 + k) % 7 == 2 &&
    ((List.range k).all fun i => (Rule30EtherThree.rowN c x0 t1).testBit i == ether (j0 + (i + 1)) (t1 + s)) &&
    decide (((t1 + s) % 4, seg (fun i => (Rule30EtherThree.rowN c x0 t1).testBit (k + i)) 13) ∈ wallStates)

theorem inFamily_of_check {c : Nat → Bool} {x0 j0 s t1 k : Nat} (h : familyCheck c x0 j0 s t1 k = true) :
    InFamily (drv c fun p => x0.testBit (p - 1)) j0 s t1 := by
  unfold familyCheck at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  obtain ⟨⟨hk, hE⟩, hW⟩ := h
  refine ⟨k, hk, fun p hp1 hpk => ?_, ?_⟩
  · obtain ⟨i, rfl⟩ : ∃ i, p = i + 1 := ⟨p - 1, by omega⟩
    rw [← Rule30EtherThree.rowN_eq_drv]
    exact hE i (by omega)
  · have e : rowOf (drv c fun p => x0.testBit (p - 1)) t1 k 13 =
        seg (fun i => (Rule30EtherThree.rowN c x0 t1).testBit (k + i)) 13 := by
      unfold rowOf
      apply seg_congr
      intro i _
      rw [Rule30EtherThree.rowN_eq_drv]
    rw [e]
    exact hW

/-! ### Right halves of at most six cells -/

/-- No finite configuration whose cells right of column `n` are white has a center column that repeats `w` from phase
`φ`. -/
def SmallRight (w : List Bool) (n φ : Nat) : Prop :=
  ¬ ∃ y : Int → Bool, FinConfig y ∧ (∀ p : Int, (n : Int) < p → y p = false) ∧ ∀ t, evol y t 0 = wordAt w (t + φ)

/-- Every right half `r < 2 ^ n` (bit `i` is column `i + 1`) is in the family at the step and depth that `entries` lists
for it, through one of the alignments `A`. -/
def smallCheck (w : List Bool) (A : List (Nat × Nat)) (φ n : Nat) (entries : List (Nat × Nat)) : Bool :=
  (List.range (2 ^ n)).all fun r =>
    A.any fun a => familyCheck (fun t => wordAt w (t + φ)) r a.1 (a.2 + φ) (entries.getD r (0, 0)).1
      (entries.getD r (0, 0)).2

theorem smallRight_of_check {w : List Bool} {A : List (Nat × Nat)} {φ n : Nat} {entries : List (Nat × Nat)}
    (hA : ∀ a ∈ A, aligned w a.1 a.2 = true) (hw : ∃ ψ, wordAt w ψ = true)
    (h : smallCheck w A φ n entries = true) : SmallRight w n φ := by
  rintro ⟨y, hfin, hR, hc⟩
  obtain ⟨r, hr, hrk⟩ :=
    Rule30ZeroBoundarySmall.exists_pack n (fun p => y (p : Int)) (fun k hk => hR k (by omega))
  unfold smallCheck at h
  obtain ⟨a, haA, ha⟩ := List.any_eq_true.1 (List.all_eq_true.1 h r (List.mem_range.2 hr))
  refine no_finite_of_family (hA a haA) φ hfin hc hw (entries.getD r (0, 0)).1 ?_
  have e : drv (fun t => wordAt w (t + φ)) (fun p => y (p : Int)) =
      drv (fun t => wordAt w (t + φ)) fun p => r.testBit (p - 1) :=
    funext fun t => funext fun p => drv_congr (fun p hp => by
      rw [← hrk p hp]; unfold Rule30ZeroBoundarySmall.toFun; rw [ite_eq_right (by omega)]) t p
  rw [e]
  exact inFamily_of_check ha

/-- The phase only matters modulo 4. -/
theorem smallRight_mod {w : List Bool} {n φ : Nat} (h : SmallRight w n (φ % 4)) : SmallRight w n φ := by
  rintro ⟨y, hfin, hR, hc⟩
  refine h ⟨y, hfin, hR, fun t => ?_⟩
  rw [hc t]
  unfold wordAt
  rw [show (t + φ) % 4 = (t + φ % 4) % 4 by omega]

/-! The entry step and depth of every right half below `2 ^ 6`, by word and phase, from `lean_entries(6, kit_wall())`
in `computations/absorption.py`. -/

def entries0001_0 : List (Nat × Nat) :=
  [(14, 3), (10, 3), (78, 3), (11, 3), (8, 3), (8, 3), (78, 3), (90, 3), (8, 4), (117, 3), (78, 3), (90, 3), (7, 3),
   (6, 3), (18, 3), (94, 3), (152, 3), (217, 3), (106, 3), (105, 3), (6, 3), (10, 3), (18, 3), (94, 3), (7, 4),
   (117, 3), (78, 3), (90, 3), (34, 3), (24, 3), (45, 3), (78, 3), (74, 3), (33, 3), (122, 3), (203, 3), (93, 3),
   (23, 3), (21, 3), (63, 3), (6, 4), (117, 3), (78, 3), (90, 3), (34, 3), (24, 3), (45, 3), (78, 3), (152, 3),
   (217, 3), (106, 3), (105, 3), (7, 3), (10, 3), (18, 3), (94, 3), (82, 3), (62, 3), (26, 3), (126, 3), (139, 3),
   (162, 3), (93, 3), (103, 3)]
def entries0001_1 : List (Nat × Nat) :=
  [(13, 3), (10, 3), (48, 3), (9, 3), (142, 3), (10, 3), (48, 3), (77, 3), (113, 10), (89, 3), (48, 3), (77, 3),
   (142, 3), (7, 3), (7, 3), (32, 3), (117, 3), (93, 3), (136, 3), (17, 3), (142, 3), (5, 3), (6, 3), (32, 3),
   (113, 10), (89, 3), (48, 3), (77, 3), (7, 4), (33, 3), (117, 3), (116, 3), (97, 3), (77, 3), (300, 3), (44, 3),
   (41, 3), (23, 3), (33, 3), (108, 3), (113, 10), (89, 3), (48, 3), (77, 3), (6, 4), (33, 3), (117, 3), (116, 3),
   (117, 3), (93, 3), (136, 3), (17, 3), (142, 3), (9, 3), (5, 3), (32, 3), (151, 3), (66, 3), (54, 3), (216, 3),
   (80, 3), (104, 3), (53, 3), (105, 3)]
def entries0001_2 : List (Nat × Nat) :=
  [(12, 3), (10, 3), (10, 4), (9, 3), (108, 3), (8, 3), (9, 4), (47, 3), (65, 3), (76, 3), (8, 4), (47, 3), (108, 3),
   (9, 3), (141, 3), (28, 3), (193, 3), (31, 3), (15, 3), (6, 3), (108, 3), (6, 3), (141, 3), (28, 3), (65, 3),
   (76, 3), (9, 4), (47, 3), (112, 10), (22, 3), (66, 3), (88, 3), (40, 3), (115, 3), (163, 3), (116, 3), (75, 3),
   (32, 3), (6, 4), (17, 3), (65, 3), (76, 3), (6, 4), (47, 3), (112, 10), (22, 3), (66, 3), (88, 3), (193, 3),
   (31, 3), (15, 3), (5, 3), (108, 3), (4, 3), (141, 3), (28, 3), (116, 3), (59, 3), (40, 3), (92, 3), (127, 3),
   (16, 3), (27, 3), (135, 3)]
def entries0001_3 : List (Nat × Nat) :=
  [(11, 3), (79, 3), (79, 3), (9, 3), (95, 3), (8, 3), (79, 3), (9, 4), (25, 3), (46, 3), (79, 3), (8, 4), (95, 3),
   (7, 3), (107, 3), (153, 3), (63, 3), (27, 3), (94, 3), (140, 3), (95, 3), (8, 3), (107, 3), (153, 3), (25, 3),
   (46, 3), (79, 3), (7, 4), (64, 3), (94, 3), (123, 3), (75, 3), (43, 3), (87, 3), (20, 3), (65, 3), (24, 3),
   (21, 3), (111, 10), (77, 10), (25, 3), (46, 3), (79, 3), (8, 4), (64, 3), (94, 3), (123, 3), (75, 3), (63, 3),
   (27, 3), (94, 3), (140, 3), (95, 3), (5, 3), (107, 3), (153, 3), (192, 3), (28, 3), (177, 3), (30, 3), (116, 3),
   (5, 3), (112, 3), (14, 3)]
def entries0011_0 : List (Nat × Nat) :=
  [(12, 2), (8, 1), (8, 2), (7, 1), (203, 1), (8, 1), (7, 2), (104, 2), (13, 2), (13, 1), (6, 2), (104, 2), (203, 1),
   (5, 1), (16, 2), (5, 1), (8, 5), (12, 9), (166, 2), (146, 1), (203, 1), (3, 1), (16, 2), (4, 1), (13, 2), (13, 1),
   (7, 2), (104, 2), (72, 1), (333, 1), (218, 2), (16, 1), (366, 1), (21, 1), (4, 2), (140, 2), (31, 1), (30, 1),
   (17, 1), (12, 2), (13, 2), (13, 1), (4, 2), (104, 2), (72, 1), (333, 1), (218, 2), (16, 1), (7, 5), (11, 9),
   (166, 2), (146, 1), (203, 1), (7, 1), (16, 2), (3, 1), (22, 2), (18, 2), (214, 2), (99, 1), (267, 2), (10, 1),
   (195, 1), (521, 1)]
def entries0011_1 : List (Nat × Nat) :=
  [(11, 2), (8, 1), (336, 1), (7, 1), (198, 1), (6, 1), (336, 1), (7, 2), (27, 2), (103, 2), (336, 1), (6, 2),
   (198, 1), (7, 1), (202, 1), (215, 1), (24, 1), (4, 1), (23, 2), (15, 2), (198, 1), (4, 1), (202, 1), (215, 1),
   (27, 2), (103, 2), (336, 1), (5, 2), (12, 2), (54, 1), (14, 1), (12, 1), (44, 1), (15, 1), (245, 2), (217, 2),
   (134, 1), (332, 1), (71, 1), (14, 1), (27, 2), (103, 2), (336, 1), (6, 2), (12, 2), (54, 1), (14, 1), (12, 1),
   (24, 1), (3, 1), (23, 2), (15, 2), (198, 1), (2, 1), (202, 1), (215, 1), (7, 5), (14, 1), (39, 1), (11, 9),
   (98, 1), (145, 1), (18, 1), (165, 2)]
def entries0011_2 : List (Nat × Nat) :=
  [(10, 2), (9, 2), (8, 2), (7, 1), (10, 5), (6, 1), (9, 2), (335, 1), (33, 1), (6, 2), (6, 2), (335, 1), (9, 5),
   (5, 1), (197, 1), (20, 2), (272, 1), (214, 1), (124, 1), (201, 1), (8, 5), (6, 1), (197, 1), (20, 2), (33, 1),
   (5, 2), (4, 2), (335, 1), (26, 2), (11, 8), (180, 2), (102, 2), (225, 1), (11, 1), (34, 1), (13, 1), (298, 1),
   (53, 1), (11, 2), (17, 1), (33, 1), (4, 2), (8, 2), (335, 1), (26, 2), (10, 8), (180, 2), (102, 2), (272, 1),
   (214, 1), (124, 1), (201, 1), (9, 5), (3, 1), (197, 1), (20, 2), (23, 1), (13, 1), (73, 1), (3, 1), (44, 1),
   (14, 2), (22, 2), (22, 2)]
def entries0011_3 : List (Nat × Nat) :=
  [(9, 1), (9, 2), (8, 2), (204, 1), (6, 1), (204, 1), (7, 2), (14, 2), (334, 1), (219, 2), (8, 2), (14, 2), (5, 1),
   (204, 1), (167, 2), (9, 5), (19, 2), (215, 2), (196, 1), (268, 2), (4, 1), (204, 1), (167, 2), (8, 5), (334, 1),
   (219, 2), (5, 2), (14, 2), (13, 2), (32, 1), (5, 2), (367, 1), (101, 2), (67, 1), (179, 2), (266, 1), (10, 8),
   (12, 1), (149, 1), (25, 2), (334, 1), (219, 2), (3, 2), (14, 2), (13, 2), (32, 1), (4, 2), (367, 1), (19, 2),
   (215, 2), (196, 1), (268, 2), (5, 1), (204, 1), (167, 2), (7, 5), (111, 2), (271, 1), (213, 1), (139, 1), (200, 1),
   (8, 1), (123, 1), (37, 1)]
def entries0111_0 : List (Nat × Nat) :=
  [(9, 0), (15, 0), (6, 0), (15, 0), (43, 0), (15, 0), (5, 0), (36, 0), (30, 0), (83, 0), (4, 0), (36, 0), (43, 0),
   (15, 0), (22, 0), (295, 0), (11, 0), (108, 0), (10, 7), (56, 0), (43, 0), (15, 0), (22, 0), (295, 0), (30, 0),
   (83, 0), (5, 0), (36, 0), (51, 0), (27, 0), (32, 0), (39, 0), (31, 0), (56, 0), (26, 0), (16, 0), (2, 0), (103, 0),
   (15, 0), (25, 0), (30, 0), (83, 0), (2, 0), (36, 0), (51, 0), (27, 0), (32, 0), (39, 0), (11, 0), (108, 0), (9, 7),
   (56, 0), (43, 0), (15, 0), (22, 0), (295, 0), (40, 0), (92, 0), (12, 0), (83, 0), (16, 0), (31, 0), (198, 0),
   (24, 0)]
def entries0111_1 : List (Nat × Nat) :=
  [(8, 0), (7, 0), (8, 0), (14, 0), (95, 0), (14, 0), (5, 0), (5, 0), (131, 0), (35, 0), (3, 0), (4, 0), (95, 0),
   (14, 0), (42, 0), (55, 0), (21, 0), (294, 0), (69, 0), (21, 0), (95, 0), (14, 0), (42, 0), (55, 0), (131, 0),
   (35, 0), (7, 0), (3, 0), (29, 0), (22, 0), (10, 0), (82, 0), (53, 0), (38, 0), (29, 0), (31, 0), (22, 0), (26, 0),
   (50, 0), (51, 0), (131, 0), (35, 0), (7, 0), (4, 0), (29, 0), (22, 0), (10, 0), (82, 0), (21, 0), (294, 0),
   (69, 0), (21, 0), (95, 0), (14, 0), (42, 0), (55, 0), (10, 0), (71, 0), (58, 0), (107, 0), (158, 0), (55, 0),
   (61, 0), (9, 7)]
def entries0111_2 : List (Nat × Nat) :=
  [(8, 0), (7, 0), (6, 0), (297, 0), (13, 0), (297, 0), (7, 0), (29, 0), (4, 0), (28, 0), (4, 0), (29, 0), (13, 0),
   (297, 0), (200, 0), (94, 0), (54, 0), (69, 0), (41, 0), (30, 0), (13, 0), (297, 0), (200, 0), (94, 0), (3, 0),
   (28, 0), (2, 0), (29, 0), (72, 0), (130, 0), (34, 0), (113, 0), (81, 0), (17, 0), (9, 0), (94, 0), (21, 0),
   (101, 0), (72, 0), (28, 0), (2, 0), (28, 0), (6, 0), (29, 0), (72, 0), (130, 0), (34, 0), (113, 0), (54, 0),
   (69, 0), (41, 0), (30, 0), (13, 0), (297, 0), (200, 0), (94, 0), (54, 0), (20, 0), (293, 0), (26, 0), (20, 0),
   (34, 0), (68, 0), (153, 0)]
def entries0111_3 : List (Nat × Nat) :=
  [(16, 0), (7, 0), (6, 0), (44, 0), (296, 0), (44, 0), (5, 0), (31, 0), (28, 0), (33, 0), (6, 0), (31, 0), (296, 0),
   (44, 0), (11, 7), (12, 0), (93, 0), (13, 0), (199, 0), (17, 0), (296, 0), (44, 0), (10, 7), (12, 0), (28, 0),
   (33, 0), (3, 0), (31, 0), (26, 0), (3, 0), (27, 0), (32, 0), (112, 0), (17, 0), (33, 0), (65, 0), (129, 0),
   (69, 0), (145, 0), (71, 0), (28, 0), (33, 0), (1, 0), (31, 0), (26, 0), (2, 0), (27, 0), (32, 0), (93, 0), (13, 0),
   (199, 0), (17, 0), (296, 0), (44, 0), (9, 7), (12, 0), (17, 0), (53, 0), (68, 0), (22, 0), (29, 0), (70, 0),
   (40, 0), (10, 0)]

/-- **No finite configuration whose right half has at most six cells has a center column that repeats `0001`**, in
any phase and whatever its left half. -/
theorem smallRight_0001 (φ : Nat) : SmallRight w0001 6 φ := by
  refine smallRight_mod ?_
  rcases (show φ % 4 = 0 ∨ φ % 4 = 1 ∨ φ % 4 = 2 ∨ φ % 4 = 3 by omega) with h | h | h | h <;> rw [h]
  · exact smallRight_of_check (entries := entries0001_0) A0001_ok ⟨3, rfl⟩ (by decide +kernel)
  · exact smallRight_of_check (entries := entries0001_1) A0001_ok ⟨3, rfl⟩ (by decide +kernel)
  · exact smallRight_of_check (entries := entries0001_2) A0001_ok ⟨3, rfl⟩ (by decide +kernel)
  · exact smallRight_of_check (entries := entries0001_3) A0001_ok ⟨3, rfl⟩ (by decide +kernel)

/-- **No finite configuration whose right half has at most six cells has a center column that repeats `0011`.** -/
theorem smallRight_0011 (φ : Nat) : SmallRight w0011 6 φ := by
  refine smallRight_mod ?_
  rcases (show φ % 4 = 0 ∨ φ % 4 = 1 ∨ φ % 4 = 2 ∨ φ % 4 = 3 by omega) with h | h | h | h <;> rw [h]
  · exact smallRight_of_check (entries := entries0011_0) A0011_ok ⟨3, rfl⟩ (by decide +kernel)
  · exact smallRight_of_check (entries := entries0011_1) A0011_ok ⟨3, rfl⟩ (by decide +kernel)
  · exact smallRight_of_check (entries := entries0011_2) A0011_ok ⟨3, rfl⟩ (by decide +kernel)
  · exact smallRight_of_check (entries := entries0011_3) A0011_ok ⟨3, rfl⟩ (by decide +kernel)

/-- **No finite configuration whose right half has at most six cells has a center column that repeats `0111`.** -/
theorem smallRight_0111 (φ : Nat) : SmallRight w0111 6 φ := by
  refine smallRight_mod ?_
  rcases (show φ % 4 = 0 ∨ φ % 4 = 1 ∨ φ % 4 = 2 ∨ φ % 4 = 3 by omega) with h | h | h | h <;> rw [h]
  · exact smallRight_of_check (entries := entries0111_0) A0111_ok ⟨3, rfl⟩ (by decide +kernel)
  · exact smallRight_of_check (entries := entries0111_1) A0111_ok ⟨3, rfl⟩ (by decide +kernel)
  · exact smallRight_of_check (entries := entries0111_2) A0111_ok ⟨3, rfl⟩ (by decide +kernel)
  · exact smallRight_of_check (entries := entries0111_3) A0111_ok ⟨3, rfl⟩ (by decide +kernel)

/-! ### The white right half -/

/-- **The counterpart of the kit's `CQ01Empty`** for a word of length 4: no finite configuration whose cells right of
the center are white has a center column that repeats `w` from phase `φ`. -/
def EmptyRight (w : List Bool) (φ : Nat) : Prop :=
  ¬ ∃ y : Int → Bool, FinConfig y ∧ (∀ p : Int, 0 < p → y p = false) ∧ ∀ t, evol y t 0 = wordAt w (t + φ)

theorem emptyRight_of_smallRight {w : List Bool} {n φ : Nat} (h : SmallRight w n φ) : EmptyRight w φ := by
  rintro ⟨y, hfin, hR, hc⟩
  exact h ⟨y, hfin, fun p hp => hR p (by omega), hc⟩

/-- No finite configuration with a white right half has a center column that repeats `0001`. -/
theorem emptyRight_0001 (φ : Nat) : EmptyRight w0001 φ := emptyRight_of_smallRight (smallRight_0001 φ)

/-- No finite configuration with a white right half has a center column that repeats `0011`. -/
theorem emptyRight_0011 (φ : Nat) : EmptyRight w0011 φ := emptyRight_of_smallRight (smallRight_0011 φ)

/-- No finite configuration with a white right half has a center column that repeats `0111`. -/
theorem emptyRight_0111 (φ : Nat) : EmptyRight w0111 φ := emptyRight_of_smallRight (smallRight_0111 φ)

/-! ### The word `001` and the kit's period-three trap -/

/-- **Entry into a labelled trap excludes the word**, for the period-three traps of the kit's
`Rule30EtherThreeTrap`: if the right half of a finite configuration whose center repeats `C.w` from phase `φ`, driven
by that center, is a state of a checked trap with the label of the right phase, contradiction. -/
theorem no_finite_of_ptrap (C : Rule30EtherThree.PTrap) (hC : C.check = true) (hb : 0 < C.b) (φ : Nat)
    {y : Int → Bool} (hfin : FinConfig y) (hc : ∀ t, evol y t 0 = Rule30EtherThree.wordAt3 C.w (t + φ))
    (hw : ∃ ψ, Rule30EtherThree.wordAt3 C.w ψ = true) (t1 i : Nat) (ht1 : 2 ≤ t1) (hi : i < C.n)
    (hph : (t1 + φ) % 3 = C.lab i % 3)
    (hr : Rule30EtherThree.EncF (drv (fun t => Rule30EtherThree.wordAt3 C.w (t + φ)) fun p => y (p : Int))
      C.b t1 0 (C.st i)) : False := by
  obtain ⟨hm, hm3, -⟩ := Rule30EtherThree.PTrap.facts C hC
  have hword : ∀ t, (3 - φ % 3) % 3 ≤ t →
      Rule30EtherThree.wordAt3 C.w (t + φ) = Rule30EtherThree.wordAt3 C.w (t - (3 - φ % 3) % 3) := by
    intro t _
    unfold Rule30EtherThree.wordAt3
    congr 1
    omega
  have inv := Rule30EtherThree.PTrap.invariant C hC (drv_isR30 _ _) ((3 - φ % 3) % 3)
    (fun t ht => by rw [drv_col0, hword t ht]) t1 i (by omega) hi (by omega) hr
  -- column 1 at the white times is the label function `u`
  have key : ∀ t, t1 ≤ t →
      drv (fun t => Rule30EtherThree.wordAt3 C.w (t + φ)) (fun p => y (p : Int)) t 0 = false →
      drv (fun t => Rule30EtherThree.wordAt3 C.w (t + φ)) (fun p => y (p : Int)) t 1 =
        C.u.testBit ((C.lab i + (t - t1)) % C.m) := by
    intro t ht hwt
    obtain ⟨j, hj, hr', hl'⟩ := inv (t - t1)
    rw [show t1 + (t - t1) = t by omega] at hr'
    obtain ⟨-, -, -, -, hu⟩ := Rule30EtherThree.PTrap.step C hC hj false
    have hphase : (t - (3 - φ % 3) % 3) % 3 = C.lab j % 3 := by
      rw [hl', show t - (3 - φ % 3) % 3 = (t1 - (3 - φ % 3) % 3) + (t - t1) by omega]
      exact Rule30EtherThree.PTrap.phase_lab C hC _ _ (by omega) _
    have hw' : Rule30EtherThree.wordAt3 C.w (C.lab j % 3) = false := by
      rw [← hwt, drv_col0, hword t (by omega)]
      unfold Rule30EtherThree.wordAt3
      rw [Nat.mod_mod, hphase]
    rw [← hl', ← hu hw', Rule30EtherThree.encF_head hr' hb]
  have hω : (fun t => evol y t 0) = fun t => Rule30EtherThree.wordAt3 C.w (t + φ) := funext hc
  have c0 : ∀ t, evol y t 0 =
      drv (fun t => Rule30EtherThree.wordAt3 C.w (t + φ)) (fun p => y (p : Int)) t 0 := fun t => by
    rw [hc, drv_col0]
  have c1 : ∀ t, evol y t ((1 : Nat) : Int) =
      drv (fun t => Rule30EtherThree.wordAt3 C.w (t + φ)) (fun p => y (p : Int)) t 1 :=
    fun t => by rw [Rule30Coupled.right_eq_drv y t 1, hω]
  have hne : ∃ p, y p = true := by
    refine Classical.byContradiction fun hz => ?_
    have hz' : ∀ p, y p = false := fun p => by
      cases h : y p
      · rfl
      · exact absurd ⟨p, h⟩ hz
    obtain ⟨ψ, hψ⟩ := hw
    have e := hc (ψ + 2 * φ)
    have e2 : Rule30EtherThree.wordAt3 C.w (ψ + 2 * φ + φ) = Rule30EtherThree.wordAt3 C.w ψ := by
      unfold Rule30EtherThree.wordAt3; rw [show (ψ + 2 * φ + φ) % 3 = ψ % 3 by omega]
    rw [Rule30Coupled.evol_zero hz', e2, hψ] at e
    exact absurd e (by decide)
  obtain ⟨lo, hlo, hzero⟩ := Rule30FiniteConfigs.exists_leftmost hfin hne
  have hper0 : ∀ t, t1 ≤ t → evol y (t + C.m) 0 = evol y t 0 := by
    intro t _
    rw [hc, hc]
    unfold Rule30EtherThree.wordAt3
    obtain ⟨q, hq⟩ := Nat.dvd_of_mod_eq_zero hm3
    rw [hq, show (t + 3 * q + φ) % 3 = (t + φ) % 3 by omega]
  refine Rule30FiniteMaskedJen.masked_jen hlo hzero 0 (T := t1) (P := C.m) hm hper0 ?_
  intro t ht hwt
  have hwm : evol y (t + C.m) 0 = false := by rw [hper0 t ht]; exact hwt
  rw [c0] at hwt hwm
  show evol y (t + C.m) ((1 : Nat) : Int) = evol y t ((1 : Nat) : Int)
  rw [c1, c1, key (t + C.m) (by omega) hwm, key t ht hwt,
    show C.lab i + (t + C.m - t1) = (C.lab i + (t - t1)) + C.m * 1 by omega, Nat.add_mul_mod_self_left]

/-- The counterpart of `EmptyRight` for a word of length three. -/
def EmptyRight3 (w : List Bool) (φ : Nat) : Prop :=
  ¬ ∃ y : Int → Bool, FinConfig y ∧ (∀ p : Int, 0 < p → y p = false) ∧
    ∀ t, evol y t 0 = Rule30EtherThree.wordAt3 w (t + φ)

theorem rowN_001_1 : Rule30EtherThree.t001.st 597 =
    Rule30EtherThree.rowN (fun t => Rule30EtherThree.wordAt3 Rule30EtherThree.w001 (t + 1)) 0 1269 % 2 ^ 47 := by
  decide +kernel

theorem rowN_001_2 : Rule30EtherThree.t001.st 597 =
    Rule30EtherThree.rowN (fun t => Rule30EtherThree.wordAt3 Rule30EtherThree.w001 (t + 2)) 0 1268 % 2 ^ 47 := by
  decide +kernel

theorem emptyRight3_of_entry {φ t1 : Nat} (ht1 : 2 ≤ t1) (hph : (t1 + φ) % 3 = Rule30EtherThree.t001.lab 597 % 3)
    (h : Rule30EtherThree.t001.st 597 =
      Rule30EtherThree.rowN (fun t => Rule30EtherThree.wordAt3 Rule30EtherThree.w001 (t + φ)) 0 t1 % 2 ^ 47) :
    EmptyRight3 Rule30EtherThree.w001 φ := by
  rintro ⟨y, hfin, hR, hc⟩
  refine no_finite_of_ptrap Rule30EtherThree.t001 Rule30EtherThree.t001_check (by decide) φ hfin hc ⟨2, rfl⟩ t1 597
    ht1 (by decide) hph ⟨Rule30EtherThree.PTrap.st_lt _ 597, fun k hk => ?_⟩
  have hb : Rule30EtherThree.t001.b = 47 := rfl
  rw [hb] at hk
  rw [h, Nat.testBit_mod_two_pow, decide_eq_true hk, Bool.true_and, Rule30EtherThree.rowN_eq_drv,
    show 0 + 1 + k = k + 1 by omega]
  exact drv_congr (fun p hp => by rw [Nat.zero_testBit, hR p (by omega)]) t1 (k + 1)

/-- **No finite configuration with a white right half has a center column that repeats `001`.** The white right half
is in the kit's trap `t001` at step 1270, 1269 or 1268 by phase (the kit's `t001_reached` at phase 0). -/
theorem emptyRight_001 (φ : Nat) : EmptyRight3 Rule30EtherThree.w001 φ := by
  have hmod : EmptyRight3 Rule30EtherThree.w001 (φ % 3) → EmptyRight3 Rule30EtherThree.w001 φ := by
    rintro h ⟨y, hfin, hR, hc⟩
    refine h ⟨y, hfin, hR, fun t => ?_⟩
    rw [hc t]
    unfold Rule30EtherThree.wordAt3
    rw [show (t + φ) % 3 = (t + φ % 3) % 3 by omega]
  refine hmod ?_
  rcases (show φ % 3 = 0 ∨ φ % 3 = 1 ∨ φ % 3 = 2 by omega) with h | h | h <;> rw [h]
  · exact emptyRight3_of_entry (by decide) (by decide) Rule30EtherThree.rowN_empty_eq
  · exact emptyRight3_of_entry (by decide) (by decide) rowN_001_1
  · exact emptyRight3_of_entry (by decide) (by decide) rowN_001_2

end Rule30Open
