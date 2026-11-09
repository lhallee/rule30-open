module

public import Rule30Open.Complexity.LateSeedCut

/-!
# Late seeds separate the `a` leftmost cells for `11 ≤ a ≤ 13`, at every `t` from a threshold on

The kernel checks of [LateSeedCut](LateSeedCut.lean) for more cells. For each `a` the low `J = 2R + 3` bits of the left
edge repeat with period 8 from `s0` on (`edge_period_J`), `lateCheck` passes at every `t` from the threshold to
`t0 + 7`, `t0 = s0 + R + 1 + ⌈a/2⌉` (`late_checks_a_i`, split so that the kernel checks the parts in parallel), and
`lateSep_all` gives every `t` from the threshold on (`lateSep_a`). The row statements follow from
`late_seed_cut_of_sep` and `late_seed_width_of_sep`.

The natural-language argument is `LateSeedCutWide.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

theorem edge_period_37 : edgeFrame (46 + 8) % 2 ^ 37 = edgeFrame 46 % 2 ^ 37 := by
  decide +kernel

theorem edge_period_39 : edgeFrame (48 + 8) % 2 ^ 39 = edgeFrame 48 % 2 ^ 39 := by
  decide +kernel

theorem late_checks_11_0 : (List.range' 19 4).all (fun t => lateCheck 11 t 17) = true := by
  decide +kernel

theorem late_checks_11_1 : (List.range' 23 4).all (fun t => lateCheck 11 t 17) = true := by
  decide +kernel

theorem late_checks_11_2 : (List.range' 27 4).all (fun t => lateCheck 11 t 17) = true := by
  decide +kernel

theorem late_checks_11_3 : (List.range' 31 4).all (fun t => lateCheck 11 t 17) = true := by
  decide +kernel

theorem late_checks_11_4 : (List.range' 35 4).all (fun t => lateCheck 11 t 17) = true := by
  decide +kernel

theorem late_checks_11_5 : (List.range' 39 4).all (fun t => lateCheck 11 t 17) = true := by
  decide +kernel

theorem late_checks_11_6 : (List.range' 43 4).all (fun t => lateCheck 11 t 17) = true := by
  decide +kernel

theorem late_checks_11_7 : (List.range' 47 4).all (fun t => lateCheck 11 t 17) = true := by
  decide +kernel

theorem late_checks_11_8 : (List.range' 51 4).all (fun t => lateCheck 11 t 17) = true := by
  decide +kernel

theorem late_checks_11_9 : (List.range' 55 4).all (fun t => lateCheck 11 t 17) = true := by
  decide +kernel

theorem late_checks_11_10 : (List.range' 59 4).all (fun t => lateCheck 11 t 17) = true := by
  decide +kernel

theorem late_checks_11_11 : (List.range' 63 4).all (fun t => lateCheck 11 t 17) = true := by
  decide +kernel

theorem late_checks_11_12 : (List.range' 67 4).all (fun t => lateCheck 11 t 17) = true := by
  decide +kernel

theorem late_checks_11_13 : (List.range' 71 4).all (fun t => lateCheck 11 t 17) = true := by
  decide +kernel

theorem late_checks_11_14 : (List.range' 75 3).all (fun t => lateCheck 11 t 17) = true := by
  decide +kernel

theorem late_checks_11 : ∀ t, 19 ≤ t → t < 78 → lateCheck 11 t 17 = true := by
  intro t h1 h2
  by_cases c0 : t < 23
  · exact checks_of_all 11 17 19 4 late_checks_11_0 t (by omega) (by omega)
  by_cases c1 : t < 27
  · exact checks_of_all 11 17 23 4 late_checks_11_1 t (by omega) (by omega)
  by_cases c2 : t < 31
  · exact checks_of_all 11 17 27 4 late_checks_11_2 t (by omega) (by omega)
  by_cases c3 : t < 35
  · exact checks_of_all 11 17 31 4 late_checks_11_3 t (by omega) (by omega)
  by_cases c4 : t < 39
  · exact checks_of_all 11 17 35 4 late_checks_11_4 t (by omega) (by omega)
  by_cases c5 : t < 43
  · exact checks_of_all 11 17 39 4 late_checks_11_5 t (by omega) (by omega)
  by_cases c6 : t < 47
  · exact checks_of_all 11 17 43 4 late_checks_11_6 t (by omega) (by omega)
  by_cases c7 : t < 51
  · exact checks_of_all 11 17 47 4 late_checks_11_7 t (by omega) (by omega)
  by_cases c8 : t < 55
  · exact checks_of_all 11 17 51 4 late_checks_11_8 t (by omega) (by omega)
  by_cases c9 : t < 59
  · exact checks_of_all 11 17 55 4 late_checks_11_9 t (by omega) (by omega)
  by_cases c10 : t < 63
  · exact checks_of_all 11 17 59 4 late_checks_11_10 t (by omega) (by omega)
  by_cases c11 : t < 67
  · exact checks_of_all 11 17 63 4 late_checks_11_11 t (by omega) (by omega)
  by_cases c12 : t < 71
  · exact checks_of_all 11 17 67 4 late_checks_11_12 t (by omega) (by omega)
  by_cases c13 : t < 75
  · exact checks_of_all 11 17 71 4 late_checks_11_13 t (by omega) (by omega)
  exact checks_of_all 11 17 75 3 late_checks_11_14 t (by omega) (by omega)

theorem lateSep_11 : ∀ t, 19 ≤ t → LateSep 11 17 t :=
  lateSep_all 11 17 37 8 46 19 (by decide) (by decide) edge_period_37 (by decide) (by decide)
    (fun t h1 h2 => late_checks_11 t h1 (by omega))

theorem late_checks_12_0 : (List.range' 21 4).all (fun t => lateCheck 12 t 18) = true := by
  decide +kernel

theorem late_checks_12_1 : (List.range' 25 4).all (fun t => lateCheck 12 t 18) = true := by
  decide +kernel

theorem late_checks_12_2 : (List.range' 29 4).all (fun t => lateCheck 12 t 18) = true := by
  decide +kernel

theorem late_checks_12_3 : (List.range' 33 4).all (fun t => lateCheck 12 t 18) = true := by
  decide +kernel

theorem late_checks_12_4 : (List.range' 37 4).all (fun t => lateCheck 12 t 18) = true := by
  decide +kernel

theorem late_checks_12_5 : (List.range' 41 4).all (fun t => lateCheck 12 t 18) = true := by
  decide +kernel

theorem late_checks_12_6 : (List.range' 45 4).all (fun t => lateCheck 12 t 18) = true := by
  decide +kernel

theorem late_checks_12_7 : (List.range' 49 4).all (fun t => lateCheck 12 t 18) = true := by
  decide +kernel

theorem late_checks_12_8 : (List.range' 53 4).all (fun t => lateCheck 12 t 18) = true := by
  decide +kernel

theorem late_checks_12_9 : (List.range' 57 4).all (fun t => lateCheck 12 t 18) = true := by
  decide +kernel

theorem late_checks_12_10 : (List.range' 61 4).all (fun t => lateCheck 12 t 18) = true := by
  decide +kernel

theorem late_checks_12_11 : (List.range' 65 4).all (fun t => lateCheck 12 t 18) = true := by
  decide +kernel

theorem late_checks_12_12 : (List.range' 69 4).all (fun t => lateCheck 12 t 18) = true := by
  decide +kernel

theorem late_checks_12_13 : (List.range' 73 4).all (fun t => lateCheck 12 t 18) = true := by
  decide +kernel

theorem late_checks_12_14 : (List.range' 77 4).all (fun t => lateCheck 12 t 18) = true := by
  decide +kernel

theorem late_checks_12 : ∀ t, 21 ≤ t → t < 81 → lateCheck 12 t 18 = true := by
  intro t h1 h2
  by_cases c0 : t < 25
  · exact checks_of_all 12 18 21 4 late_checks_12_0 t (by omega) (by omega)
  by_cases c1 : t < 29
  · exact checks_of_all 12 18 25 4 late_checks_12_1 t (by omega) (by omega)
  by_cases c2 : t < 33
  · exact checks_of_all 12 18 29 4 late_checks_12_2 t (by omega) (by omega)
  by_cases c3 : t < 37
  · exact checks_of_all 12 18 33 4 late_checks_12_3 t (by omega) (by omega)
  by_cases c4 : t < 41
  · exact checks_of_all 12 18 37 4 late_checks_12_4 t (by omega) (by omega)
  by_cases c5 : t < 45
  · exact checks_of_all 12 18 41 4 late_checks_12_5 t (by omega) (by omega)
  by_cases c6 : t < 49
  · exact checks_of_all 12 18 45 4 late_checks_12_6 t (by omega) (by omega)
  by_cases c7 : t < 53
  · exact checks_of_all 12 18 49 4 late_checks_12_7 t (by omega) (by omega)
  by_cases c8 : t < 57
  · exact checks_of_all 12 18 53 4 late_checks_12_8 t (by omega) (by omega)
  by_cases c9 : t < 61
  · exact checks_of_all 12 18 57 4 late_checks_12_9 t (by omega) (by omega)
  by_cases c10 : t < 65
  · exact checks_of_all 12 18 61 4 late_checks_12_10 t (by omega) (by omega)
  by_cases c11 : t < 69
  · exact checks_of_all 12 18 65 4 late_checks_12_11 t (by omega) (by omega)
  by_cases c12 : t < 73
  · exact checks_of_all 12 18 69 4 late_checks_12_12 t (by omega) (by omega)
  by_cases c13 : t < 77
  · exact checks_of_all 12 18 73 4 late_checks_12_13 t (by omega) (by omega)
  exact checks_of_all 12 18 77 4 late_checks_12_14 t (by omega) (by omega)

theorem lateSep_12 : ∀ t, 21 ≤ t → LateSep 12 18 t :=
  lateSep_all 12 18 39 8 48 21 (by decide) (by decide) edge_period_39 (by decide) (by decide)
    (fun t h1 h2 => late_checks_12 t h1 (by omega))

theorem late_checks_13_0 : (List.range' 24 4).all (fun t => lateCheck 13 t 17) = true := by
  decide +kernel

theorem late_checks_13_1 : (List.range' 28 4).all (fun t => lateCheck 13 t 17) = true := by
  decide +kernel

theorem late_checks_13_2 : (List.range' 32 4).all (fun t => lateCheck 13 t 17) = true := by
  decide +kernel

theorem late_checks_13_3 : (List.range' 36 4).all (fun t => lateCheck 13 t 17) = true := by
  decide +kernel

theorem late_checks_13_4 : (List.range' 40 4).all (fun t => lateCheck 13 t 17) = true := by
  decide +kernel

theorem late_checks_13_5 : (List.range' 44 4).all (fun t => lateCheck 13 t 17) = true := by
  decide +kernel

theorem late_checks_13_6 : (List.range' 48 4).all (fun t => lateCheck 13 t 17) = true := by
  decide +kernel

theorem late_checks_13_7 : (List.range' 52 4).all (fun t => lateCheck 13 t 17) = true := by
  decide +kernel

theorem late_checks_13_8 : (List.range' 56 4).all (fun t => lateCheck 13 t 17) = true := by
  decide +kernel

theorem late_checks_13_9 : (List.range' 60 4).all (fun t => lateCheck 13 t 17) = true := by
  decide +kernel

theorem late_checks_13_10 : (List.range' 64 4).all (fun t => lateCheck 13 t 17) = true := by
  decide +kernel

theorem late_checks_13_11 : (List.range' 68 4).all (fun t => lateCheck 13 t 17) = true := by
  decide +kernel

theorem late_checks_13_12 : (List.range' 72 4).all (fun t => lateCheck 13 t 17) = true := by
  decide +kernel

theorem late_checks_13_13 : (List.range' 76 3).all (fun t => lateCheck 13 t 17) = true := by
  decide +kernel

theorem late_checks_13 : ∀ t, 24 ≤ t → t < 79 → lateCheck 13 t 17 = true := by
  intro t h1 h2
  by_cases c0 : t < 28
  · exact checks_of_all 13 17 24 4 late_checks_13_0 t (by omega) (by omega)
  by_cases c1 : t < 32
  · exact checks_of_all 13 17 28 4 late_checks_13_1 t (by omega) (by omega)
  by_cases c2 : t < 36
  · exact checks_of_all 13 17 32 4 late_checks_13_2 t (by omega) (by omega)
  by_cases c3 : t < 40
  · exact checks_of_all 13 17 36 4 late_checks_13_3 t (by omega) (by omega)
  by_cases c4 : t < 44
  · exact checks_of_all 13 17 40 4 late_checks_13_4 t (by omega) (by omega)
  by_cases c5 : t < 48
  · exact checks_of_all 13 17 44 4 late_checks_13_5 t (by omega) (by omega)
  by_cases c6 : t < 52
  · exact checks_of_all 13 17 48 4 late_checks_13_6 t (by omega) (by omega)
  by_cases c7 : t < 56
  · exact checks_of_all 13 17 52 4 late_checks_13_7 t (by omega) (by omega)
  by_cases c8 : t < 60
  · exact checks_of_all 13 17 56 4 late_checks_13_8 t (by omega) (by omega)
  by_cases c9 : t < 64
  · exact checks_of_all 13 17 60 4 late_checks_13_9 t (by omega) (by omega)
  by_cases c10 : t < 68
  · exact checks_of_all 13 17 64 4 late_checks_13_10 t (by omega) (by omega)
  by_cases c11 : t < 72
  · exact checks_of_all 13 17 68 4 late_checks_13_11 t (by omega) (by omega)
  by_cases c12 : t < 76
  · exact checks_of_all 13 17 72 4 late_checks_13_12 t (by omega) (by omega)
  exact checks_of_all 13 17 76 3 late_checks_13_13 t (by omega) (by omega)

theorem lateSep_13 : ∀ t, 24 ≤ t → LateSep 13 17 t :=
  lateSep_all 13 17 37 8 46 24 (by decide) (by decide) edge_period_37 (by decide) (by decide)
    (fun t h1 h2 => late_checks_13 t h1 (by omega))

/-- The first `t` of the theorem for `a` cells, `11 ≤ a ≤ 13`. -/
def lateStartWide : Nat → Nat
  | 11 => 19 | 12 => 21 | 13 => 24 | _ => 0

/-- The largest `R` of the probes, `11 ≤ a ≤ 13`. -/
def lateRWide : Nat → Nat
  | 11 => 17 | 12 => 18 | 13 => 17 | _ => 0

theorem lateSep_leWide (a t : Nat) (ha : 11 ≤ a) (ha' : a ≤ 13) (ht : lateStartWide a ≤ t) :
    LateSep a (lateRWide a) t := by
  rcases (show a = 11 ∨ a = 12 ∨ a = 13 by omega) with rfl | rfl | rfl
  · exact lateSep_11 t ht
  · exact lateSep_12 t ht
  · exact lateSep_13 t ht

/-- **Late seeds separate the `a` leftmost cells of the cone, for every `t ≥ lateStartWide a`**
(`11 ≤ a ≤ 13`): two rows that differ somewhere on the cells `-t .. -t + a - 1` have different centers after `t`
steps for the white completion from `-t + a` on, or for the completion white except one black cell at
`t - (a % 2) - 2R - d` with `R ≤ lateRWide a`, `d ≤ 1`. -/
theorem late_seed_cut_wide (a t : Nat) (ha : 11 ≤ a) (ha' : a ≤ 13) (ht : lateStartWide a ≤ t) (x y : Int → Bool)
    (i : Int) (hi1 : -(t : Int) ≤ i) (hi2 : i < -(t : Int) + a) (hne : x i ≠ y i) :
    evolve (spliceAt (-(t : Int) + a) x (fun _ => false)) t 0 ≠
        evolve (spliceAt (-(t : Int) + a) y (fun _ => false)) t 0 ∨
      ∃ R d : Nat, R ≤ lateRWide a ∧ d ≤ 1 ∧ R + d + (a + 1) / 2 ≤ t ∧
        evolve (spliceAt (-(t : Int) + a) x (fun j => single (j - ((t : Int) - (a % 2 : Nat) - 2 * R - d)))) t 0 ≠
        evolve (spliceAt (-(t : Int) + a) y (fun j => single (j - ((t : Int) - (a % 2 : Nat) - 2 * R - d)))) t 0 :=
  late_seed_cut_of_sep a (lateRWide a) t (lateSep_leWide a t ha ha' ht) x y i hi1 hi2 hne

/-- **The width at the cut, for every `t ≥ lateStartWide a`** (`11 ≤ a ≤ 13`): every factorization of the
center after `t` steps through states at the cut after the `a` leftmost cells has at least `2 ^ a` states. -/
theorem late_seed_width_wide (a t : Nat) (ha : 11 ≤ a) (ha' : a ≤ 13) (ht : lateStartWide a ≤ t) {S : Type}
    (F : (Int → Bool) → S) (G : S → (Int → Bool) → Bool)
    (hFG : ∀ x z : Int → Bool, evolve (spliceAt (-(t : Int) + a) x z) t 0 = G (F x) z) :
    ∀ P Q : Nat, P < 2 ^ a → Q < 2 ^ a → F (rowN P (-(t : Int))) = F (rowN Q (-(t : Int))) → P = Q :=
  late_seed_width_of_sep a (lateRWide a) t (lateSep_leWide a t ha ha' ht) F G hFG

end Rule30Open
