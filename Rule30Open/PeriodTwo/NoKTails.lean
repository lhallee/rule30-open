module

public import Rule30Open.PeriodTwo.EtherCensus

/-!
# No head of up to 12 cells on four traveling backgrounds is in `K`

A background is a cycle of `P` states of the held map on a ring of `L` cells (`ringCell`, a cycle by `ringCell_step`),
laid on the cells `j ≥ 0` of a half at an alignment `(a, o)`: cell `j` is ring cell `j + o` of state `a`. For four of the
backgrounds of the tail census, with `(L, P) = (4, 8)`, `(5, 5)`, `(10, 15)` and `(12, 3)`, no point of `K` (`InK`) has
the background from a cell `p ≤ 12` on, at any alignment (`no_k_tail_48`, `no_k_tail_55`, `no_k_tail_1015`,
`no_k_tail_123`).

* **A finite truncation decides.** Bit 0 of `heldOrbit u t` reads only the cells `0, …, t` of `u` (`column_triangular`
  of `ShiftModel`; `column_eq_of_agree`). So for `t < 64` it is bit 0 of `heldNat^t N`, where the number `N` holds
  the cells `0, …, 63` of `u`: the head `natOf u 12` in the cells `0, …, 11` and the background in the cells
  `12, …, 63` (`tailWord`).
* **The checker.** `breakRun R N` steps `N` twice per round with the raw operations (`heldRaw`) and succeeds when bit 0
  is 0 after the first step of a round, an odd step `2 s + 1 < 2 R` (`breakRun_sound`, `breakRun_start`).
* **Tables.** The cells `12, …, 63` depend on the alignment only through the ring word read from cell `o` of state
  `a`, so the alignments share few tail words: 8, 5, 30 and 12 of them for the four backgrounds. `indexOK` checks the
  word of each of the `P L` alignments against a table, and `censusOK R W` runs `breakRun R` on every head below
  `2 ^ 12` with the tail word `W`, one kernel computation per word, with `R = 17` rounds (the odd steps up to 33).
* **The theorem.** `not_inK_of_tables` reduces the alignment modulo `(P, L)`, reads the head off `u`, and turns a
  break of the truncation into a break of `u`.

The natural-language argument is `NoKTails.md`, beside this file.
-/

@[expose] public section

-- Sequential elaboration: the kernel checks would otherwise run in parallel and stack their memory.
set_option Elab.async false

namespace Rule30Open

/-! ### Backgrounds on a ring -/

/-- Cell `j` of state `a` of the background with the states `st` on a ring of `L` cells, both read cyclically. -/
def ringCell (st : List Nat) (L a j : Nat) : Bool := (st.getD (a % st.length) 0).testBit (j % L)

/-- The check that each state of `st` steps to the next under the held map on the ring of `L` cells, and the last to
the first: cell `j` of state `a + 1` is cell `j + 1` xor (cell `j` or cell `j - 1`) of state `a`, with `j - 1` read as
`j + (L - 1)`. -/
def ringStepOK (st : List Nat) (L : Nat) : Bool :=
  allBelow (fun a => allBelow (fun j => ringCell st L (a + 1) j ==
    xor (ringCell st L a (j + 1)) (ringCell st L a j || ringCell st L a (j + (L - 1)))) L) st.length

theorem ringCell_congr (st : List Nat) (L : Nat) {a a' j j' : Nat} (ha : a % st.length = a' % st.length)
    (hj : j % L = j' % L) : ringCell st L a j = ringCell st L a' j' := by
  unfold ringCell
  rw [ha, hj]

/-- **A checked background is a cycle of the held map on the ring**, at every phase and cell. -/
theorem ringCell_step (st : List Nat) (L : Nat) (hL : 0 < L) (hP : 0 < st.length) (h : ringStepOK st L = true)
    (a j : Nat) : ringCell st L (a + 1) j =
      xor (ringCell st L a (j + 1)) (ringCell st L a j || ringCell st L a (j + (L - 1))) := by
  have key : ringCell st L (a % st.length + 1) (j % L) =
      xor (ringCell st L (a % st.length) (j % L + 1))
        (ringCell st L (a % st.length) (j % L) || ringCell st L (a % st.length) (j % L + (L - 1))) :=
    beq_iff_eq.mp (allBelow_spec _ _ (allBelow_spec _ _ h (a % st.length) (Nat.mod_lt _ hP)) (j % L)
      (Nat.mod_lt _ hL))
  have e1 := ringCell_congr st L (Nat.mod_add_mod a st.length 1).symm (Nat.mod_mod j L).symm
  have e2 := ringCell_congr st L (Nat.mod_mod a st.length).symm (Nat.mod_add_mod j L 1).symm
  have e3 := ringCell_congr st L (Nat.mod_mod a st.length).symm (Nat.mod_mod j L).symm
  have e4 := ringCell_congr st L (Nat.mod_mod a st.length).symm (Nat.mod_add_mod j L (L - 1)).symm
  rw [e1, e2, e3, e4]
  exact key

/-! ### A finite truncation decides the first odd steps -/

private theorem nk_xor_cancel (a b c : Bool) (h : xor a c = xor b c) : a = b := by
  revert a b c; decide

/-- **The cell next to the column at step `t` reads only the cells `0, …, t`**: two halves that agree there have the
same `column` at step `t`. -/
theorem column_eq_of_agree (t : Nat) (u v : Nat → Bool) (h : ∀ i, i ≤ t → u i = v i) : column u t = column v t := by
  have key := column_triangular t u v (fun i hi => h i (by omega))
  rw [h t (Nat.le_refl t)] at key
  exact nk_xor_cancel _ _ _ key

/-- The held map with the raw operations, which the kernel evaluates on numbers. -/
def heldRaw (n : Nat) : Nat := Nat.xor (Nat.shiftRight n 1) (Nat.lor n (Nat.shiftLeft n 1))

theorem heldRaw_eq (n : Nat) : heldRaw n = heldNat n := rfl

theorem repeat_succ_nk (f : Nat → Nat) (n a : Nat) : Nat.repeat f (n + 1) a = f (Nat.repeat f n a) := rfl

/-- The checker: `R` rounds of two steps of the held map from `n`, succeeding when bit 0 is 0 after the first step of a
round. -/
def breakRun (R : Nat) (n : Nat) : Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun _ => false)
    (fun _ ih m => letN (heldRaw m) fun n1 => Nat.beq (Nat.mod n1 2) 0 || letN (heldRaw n1) fun n2 => ih n2) R n

theorem breakRun_succ (R n : Nat) :
    breakRun (R + 1) n =
      letN (heldRaw n) fun n1 => Nat.beq (Nat.mod n1 2) 0 || letN (heldRaw n1) fun n2 => breakRun R n2 := rfl

/-- **The checker is sound**: from `n = heldNat^(2 k) N`, a run that succeeds finds an odd step `2 s + 1` with
`k ≤ s < k + R` at which `heldNat^(2 s + 1) N` is even. -/
theorem breakRun_sound (N : Nat) : ∀ R n k, n = Nat.repeat heldNat (2 * k) N → breakRun R n = true →
    ∃ s, s < k + R ∧ Nat.repeat heldNat (2 * s + 1) N % 2 = 0 := by
  intro R
  induction R with
  | zero => intro n k _ h; exact absurd h Bool.false_ne_true
  | succ R ih =>
    intro n k hn h
    subst hn
    rw [breakRun_succ, letN_eq, letN_eq, Bool.or_eq_true] at h
    rcases h with h | h
    · have h1 : heldRaw (Nat.repeat heldNat (2 * k) N) % 2 = 0 := Nat.eq_of_beq_eq_true h
      refine ⟨k, by omega, ?_⟩
      rw [repeat_succ_nk]
      rw [heldRaw_eq] at h1
      exact h1
    · obtain ⟨s, hs, hz⟩ := ih (heldRaw (heldRaw (Nat.repeat heldNat (2 * k) N))) (k + 1)
        (by rw [heldRaw_eq, heldRaw_eq, show 2 * (k + 1) = 2 * k + 1 + 1 by omega, repeat_succ_nk, repeat_succ_nk]) h
      exact ⟨s, by omega, hz⟩

/-- From the start: a run of `R` rounds from `N` that succeeds finds an odd step `2 s + 1 < 2 R` at which
`heldNat^(2 s + 1) N` is even. -/
theorem breakRun_start (N R : Nat) (h : breakRun R N = true) :
    ∃ s, s < R ∧ Nat.repeat heldNat (2 * s + 1) N % 2 = 0 := by
  obtain ⟨s, hs, hz⟩ := breakRun_sound N R N 0 rfl h
  exact ⟨s, by omega, hz⟩

/-! ### The tables -/

/-- The cells `12, …, 63` of the background at the alignment `(a, o)`, in place: bit `j` is the cell `j`. -/
def tailWord (st : List Nat) (L a o : Nat) : Nat := natOf (fun j => decide (12 ≤ j) && ringCell st L a (j + o)) 64

/-- The check of the tables: at each alignment `(a, o)` with `a < P` and `o < L`, entry `L a + o` of `idx` is below
`k`, and the tail word there is the word of `ws` at that entry. -/
def indexOK (st : List Nat) (L P k : Nat) (ws idx : List Nat) : Bool :=
  allBelow (fun a => allBelow (fun o => Nat.blt (idx.getD (L * a + o) 0) k &&
    Nat.beq (tailWord st L a o) (ws.getD (idx.getD (L * a + o) 0) 0)) L) P

/-- Every head below `2 ^ 12` with the tail word `W` breaks `K` within `R` rounds, as one kernel computation. -/
def censusOK (R W : Nat) : Bool := allBelow (fun h => breakRun R (Nat.lor h W)) 4096

/-- **The tables exclude the background**: if the tables of the states `st` pass `indexOK` and every word of `ws`
passes `censusOK` with `R` rounds, `2 R ≤ 64`, then no point of `K` has the background from a cell `p ≤ 12` on, at any
alignment `(a, o)`. -/
theorem not_inK_of_tables (st : List Nat) (L P R : Nat) (ws idx : List Nat) (k : Nat) (hR : 2 * R ≤ 64)
    (hP : st.length = P) (hP0 : 0 < P) (hL0 : 0 < L) (hidx : indexOK st L P k ws idx = true)
    (hw : ∀ i, i < k → censusOK R (ws.getD i 0) = true) (u : Nat → Bool) (a o p : Nat) (hp : p ≤ 12)
    (hu : ∀ j, p ≤ j → u j = ringCell st L a (j + o)) : ¬ InK u := by
  intro hK
  -- the alignment, reduced modulo `(P, L)`
  have hu' : ∀ j, p ≤ j → u j = ringCell st L (a % P) (j + o % L) := by
    intro j hj
    rw [hu j hj]
    unfold ringCell
    rw [hP, Nat.mod_mod, Nat.add_mod_mod]
  have ha : a % P < P := Nat.mod_lt _ hP0
  have ho : o % L < L := Nat.mod_lt _ hL0
  -- its tail word passes the census
  have hi : (Nat.blt (idx.getD (L * (a % P) + o % L) 0) k &&
      Nat.beq (tailWord st L (a % P) (o % L)) (ws.getD (idx.getD (L * (a % P) + o % L) 0) 0)) = true :=
    allBelow_spec _ _ (allBelow_spec _ _ hidx (a % P) ha) (o % L) ho
  obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hi
  have hk : idx.getD (L * (a % P) + o % L) 0 < k := Nat.le_of_ble_eq_true h1
  have hword : tailWord st L (a % P) (o % L) = ws.getD (idx.getD (L * (a % P) + o % L) 0) 0 :=
    Nat.eq_of_beq_eq_true h2
  have hc := hw _ hk
  rw [← hword] at hc
  -- the number holding the cells `0, …, 63` of `u`
  have hN : ∀ i, i < 64 → (natOf u 12 ||| tailWord st L (a % P) (o % L)).testBit i = u i := by
    intro i hi64
    unfold tailWord
    rw [Nat.testBit_or, natOf_testBit, natOf_testBit]
    by_cases h12 : i < 12
    · simp [h12, hi64, show ¬ 12 ≤ i by omega]
    · rw [hu' i (by omega)]
      simp [h12, hi64, show 12 ≤ i by omega]
  have hb : breakRun R (natOf u 12 ||| tailWord st L (a % P) (o % L)) = true :=
    allBelow_spec _ _ hc (natOf u 12) (Nat.lt_of_lt_of_le (natOf_lt u 12) (by decide))
  obtain ⟨s, hs, hz⟩ := breakRun_start _ R hb
  -- the break of the truncation is a break of `u`
  have hcol := heldNat_repeat_testBit (natOf u 12 ||| tailWord st L (a % P) (o % L)) (2 * s + 1) 0
  rw [Nat.testBit_zero, hz] at hcol
  have hagree := column_eq_of_agree (2 * s + 1) u
    (fun i => (natOf u 12 ||| tailWord st L (a % P) (o % L)).testBit i) (fun i hi => (hN i (by omega)).symm)
  have hone : heldOrbit (fun i => (natOf u 12 ||| tailWord st L (a % P) (o % L)).testBit i) (2 * s + 1) 0 = true :=
    hagree.symm.trans (hK s)
  rw [hone] at hcol
  exact absurd hcol (by decide)

/-! ### The background `1000`: `L = 4`, `P = 8` -/

/-- The 8 states of the background `1000` on a ring of 4 cells, bit `j` the ring cell `j`. -/
def bgStates48 : List Nat := [1, 11, 2, 7, 4, 14, 8, 13]

theorem bgStates48_cycle : ringStepOK bgStates48 4 = true := by
  decide +kernel

/-- The background `1000` is a cycle of the held map on the ring of 4 cells. -/
theorem bgStep48 (a j : Nat) : ringCell bgStates48 4 (a + 1) j =
    xor (ringCell bgStates48 4 a (j + 1)) (ringCell bgStates48 4 a j || ringCell bgStates48 4 a (j + 3)) :=
  ringCell_step bgStates48 4 (by decide) (by decide) bgStates48_cycle a j

/-- The 8 distinct tail words of the background, cells 12 to 63 in place. -/
def bgWords48 : List Nat := [1229782938247303168, 9838263505978425344, 4919131752989212672, 2459565876494606336, 13527612320720334848, 15987178197214941184, 17216961135462244352, 8608480567731122176]

/-- Entry `4 a + o`: the index in `bgWords48` of the tail word at the alignment `(a, o)`. -/
def bgIndex48 : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 3, 0, 1, 2, 7, 4, 5, 6, 2, 3, 0, 1, 6, 7, 4, 5, 1, 2, 3, 0, 5, 6, 7, 4]

theorem bgIndex48_ok : indexOK bgStates48 4 8 8 bgWords48 bgIndex48 = true := by
  decide +kernel

theorem kcensus48_0 : censusOK 17 (bgWords48.getD 0 0) = true := by
  decide +kernel

theorem kcensus48_1 : censusOK 17 (bgWords48.getD 1 0) = true := by
  decide +kernel

theorem kcensus48_2 : censusOK 17 (bgWords48.getD 2 0) = true := by
  decide +kernel

theorem kcensus48_3 : censusOK 17 (bgWords48.getD 3 0) = true := by
  decide +kernel

theorem kcensus48_4 : censusOK 17 (bgWords48.getD 4 0) = true := by
  decide +kernel

theorem kcensus48_5 : censusOK 17 (bgWords48.getD 5 0) = true := by
  decide +kernel

theorem kcensus48_6 : censusOK 17 (bgWords48.getD 6 0) = true := by
  decide +kernel

theorem kcensus48_7 : censusOK 17 (bgWords48.getD 7 0) = true := by
  decide +kernel

theorem kcensus48 (i : Nat) (hi : i < 8) : censusOK 17 (bgWords48.getD i 0) = true :=
  match i, hi with
  | 0, _ => kcensus48_0
  | 1, _ => kcensus48_1
  | 2, _ => kcensus48_2
  | 3, _ => kcensus48_3
  | 4, _ => kcensus48_4
  | 5, _ => kcensus48_5
  | 6, _ => kcensus48_6
  | 7, _ => kcensus48_7
  | i + 8, hi => absurd hi (by omega)

/-- **No point of `K` has the background `1000` from a cell `p ≤ 12` on**, at any alignment `(a, o)`. -/
theorem no_k_tail_48 (u : Nat → Bool) (a o p : Nat) (hp : p ≤ 12)
    (hu : ∀ j, p ≤ j → u j = ringCell bgStates48 4 a (j + o)) : ¬ InK u :=
  not_inK_of_tables bgStates48 4 8 17 bgWords48 bgIndex48 8 (by decide) (by decide)
    (by decide) (by decide) bgIndex48_ok kcensus48 u a o p hp hu

/-! ### The background `11100`: `L = 5`, `P = 5` -/

/-- The 5 states of the background `11100` on a ring of 5 cells, bit `j` the ring cell `j`. -/
def bgStates55 : List Nat := [7, 28, 19, 14, 25]

theorem bgStates55_cycle : ringStepOK bgStates55 5 = true := by
  decide +kernel

/-- The background `11100` is a cycle of the held map on the ring of 5 cells. -/
theorem bgStep55 (a j : Nat) : ringCell bgStates55 5 (a + 1) j =
    xor (ringCell bgStates55 5 a (j + 1)) (ringCell bgStates55 5 a j || ringCell bgStates55 5 a (j + 4)) :=
  ringCell_step bgStates55 5 (by decide) (by decide) bgStates55_cycle a j

/-- The 5 distinct tail words of the background, cells 12 to 63 in place. -/
def bgWords55 : List Nat := [8330787646191407104, 4165393823095701504, 11306068948402626560, 14876406511056089088, 16661575292382818304]

/-- Entry `5 a + o`: the index in `bgWords55` of the tail word at the alignment `(a, o)`. -/
def bgIndex55 : List Nat := [0, 1, 2, 3, 4, 3, 4, 0, 1, 2, 1, 2, 3, 4, 0, 4, 0, 1, 2, 3, 2, 3, 4, 0, 1]

theorem bgIndex55_ok : indexOK bgStates55 5 5 5 bgWords55 bgIndex55 = true := by
  decide +kernel

theorem kcensus55_0 : censusOK 17 (bgWords55.getD 0 0) = true := by
  decide +kernel

theorem kcensus55_1 : censusOK 17 (bgWords55.getD 1 0) = true := by
  decide +kernel

theorem kcensus55_2 : censusOK 17 (bgWords55.getD 2 0) = true := by
  decide +kernel

theorem kcensus55_3 : censusOK 17 (bgWords55.getD 3 0) = true := by
  decide +kernel

theorem kcensus55_4 : censusOK 17 (bgWords55.getD 4 0) = true := by
  decide +kernel

theorem kcensus55 (i : Nat) (hi : i < 5) : censusOK 17 (bgWords55.getD i 0) = true :=
  match i, hi with
  | 0, _ => kcensus55_0
  | 1, _ => kcensus55_1
  | 2, _ => kcensus55_2
  | 3, _ => kcensus55_3
  | 4, _ => kcensus55_4
  | i + 5, hi => absurd hi (by omega)

/-- **No point of `K` has the background `11100` from a cell `p ≤ 12` on**, at any alignment `(a, o)`. -/
theorem no_k_tail_55 (u : Nat → Bool) (a o p : Nat) (hp : p ≤ 12)
    (hu : ∀ j, p ≤ j → u j = ringCell bgStates55 5 a (j + o)) : ¬ InK u :=
  not_inK_of_tables bgStates55 5 5 17 bgWords55 bgIndex55 5 (by decide) (by decide)
    (by decide) (by decide) bgIndex55_ok kcensus55 u a o p hp hu

/-! ### The background `1110100000`: `L = 10`, `P = 15` -/

/-- The 15 states of the background `1110100000` on a ring of 10 cells, bit `j` the ring cell `j`. -/
def bgStates1015 : List Nat := [23, 564, 871, 92, 210, 415, 368, 840, 637, 449, 291, 502, 773, 141, 985]

theorem bgStates1015_cycle : ringStepOK bgStates1015 10 = true := by
  decide +kernel

/-- The background `1110100000` is a cycle of the held map on the ring of 10 cells. -/
theorem bgStep1015 (a j : Nat) : ringCell bgStates1015 10 (a + 1) j =
    xor (ringCell bgStates1015 10 a (j + 1)) (ringCell bgStates1015 10 a j || ringCell bgStates1015 10 a (j + 9)) :=
  ringCell_step bgStates1015 10 (by decide) (by decide) bgStates1015_cycle a j

/-- The 30 distinct tail words of the background, cells 12 to 63 in place. -/
def bgWords1015 : List Nat := [8096371543592947712, 13271557808651247616, 6635778904325623808, 3317889452162809856, 1658944726081404928, 829472363040702464, 414736181520351232, 9430740127614951424, 13938742100662251520, 16192743087185899520, 5247314296627056640, 11847029185168302080, 15146886629438926848, 7573443314719461376, 3786721657359728640, 1893360828679864320, 10170052451194707968, 5085026225597353984, 2542513112798674944, 10494628593254113280, 9052067961878974464, 4526033980939485184, 11486389027324518400, 14966566550517035008, 7483283275258515456, 12965013674484031488, 15705878874096791552, 17076311473903169536, 17761527773806358528, 18104135923757953024]

/-- Entry `10 a + o`: the index in `bgWords1015` of the tail word at the alignment `(a, o)`. -/
def bgIndex1015 : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 8, 9, 0, 1, 2, 3, 4, 5, 6, 7, 18, 19, 10, 11, 12, 13, 14, 15, 16, 17, 28, 29, 20, 21, 22, 23, 24, 25, 26, 27, 6, 7, 8, 9, 0, 1, 2, 3, 4, 5, 16, 17, 18, 19, 10, 11, 12, 13, 14, 15, 26, 27, 28, 29, 20, 21, 22, 23, 24, 25, 4, 5, 6, 7, 8, 9, 0, 1, 2, 3, 14, 15, 16, 17, 18, 19, 10, 11, 12, 13, 24, 25, 26, 27, 28, 29, 20, 21, 22, 23, 2, 3, 4, 5, 6, 7, 8, 9, 0, 1, 12, 13, 14, 15, 16, 17, 18, 19, 10, 11, 22, 23, 24, 25, 26, 27, 28, 29, 20, 21]

theorem bgIndex1015_ok : indexOK bgStates1015 10 15 30 bgWords1015 bgIndex1015 = true := by
  decide +kernel

theorem kcensus1015_0 : censusOK 17 (bgWords1015.getD 0 0) = true := by
  decide +kernel

theorem kcensus1015_1 : censusOK 17 (bgWords1015.getD 1 0) = true := by
  decide +kernel

theorem kcensus1015_2 : censusOK 17 (bgWords1015.getD 2 0) = true := by
  decide +kernel

theorem kcensus1015_3 : censusOK 17 (bgWords1015.getD 3 0) = true := by
  decide +kernel

theorem kcensus1015_4 : censusOK 17 (bgWords1015.getD 4 0) = true := by
  decide +kernel

theorem kcensus1015_5 : censusOK 17 (bgWords1015.getD 5 0) = true := by
  decide +kernel

theorem kcensus1015_6 : censusOK 17 (bgWords1015.getD 6 0) = true := by
  decide +kernel

theorem kcensus1015_7 : censusOK 17 (bgWords1015.getD 7 0) = true := by
  decide +kernel

theorem kcensus1015_8 : censusOK 17 (bgWords1015.getD 8 0) = true := by
  decide +kernel

theorem kcensus1015_9 : censusOK 17 (bgWords1015.getD 9 0) = true := by
  decide +kernel

theorem kcensus1015_10 : censusOK 17 (bgWords1015.getD 10 0) = true := by
  decide +kernel

theorem kcensus1015_11 : censusOK 17 (bgWords1015.getD 11 0) = true := by
  decide +kernel

theorem kcensus1015_12 : censusOK 17 (bgWords1015.getD 12 0) = true := by
  decide +kernel

theorem kcensus1015_13 : censusOK 17 (bgWords1015.getD 13 0) = true := by
  decide +kernel

theorem kcensus1015_14 : censusOK 17 (bgWords1015.getD 14 0) = true := by
  decide +kernel

theorem kcensus1015_15 : censusOK 17 (bgWords1015.getD 15 0) = true := by
  decide +kernel

theorem kcensus1015_16 : censusOK 17 (bgWords1015.getD 16 0) = true := by
  decide +kernel

theorem kcensus1015_17 : censusOK 17 (bgWords1015.getD 17 0) = true := by
  decide +kernel

theorem kcensus1015_18 : censusOK 17 (bgWords1015.getD 18 0) = true := by
  decide +kernel

theorem kcensus1015_19 : censusOK 17 (bgWords1015.getD 19 0) = true := by
  decide +kernel

theorem kcensus1015_20 : censusOK 17 (bgWords1015.getD 20 0) = true := by
  decide +kernel

theorem kcensus1015_21 : censusOK 17 (bgWords1015.getD 21 0) = true := by
  decide +kernel

theorem kcensus1015_22 : censusOK 17 (bgWords1015.getD 22 0) = true := by
  decide +kernel

theorem kcensus1015_23 : censusOK 17 (bgWords1015.getD 23 0) = true := by
  decide +kernel

theorem kcensus1015_24 : censusOK 17 (bgWords1015.getD 24 0) = true := by
  decide +kernel

theorem kcensus1015_25 : censusOK 17 (bgWords1015.getD 25 0) = true := by
  decide +kernel

theorem kcensus1015_26 : censusOK 17 (bgWords1015.getD 26 0) = true := by
  decide +kernel

theorem kcensus1015_27 : censusOK 17 (bgWords1015.getD 27 0) = true := by
  decide +kernel

theorem kcensus1015_28 : censusOK 17 (bgWords1015.getD 28 0) = true := by
  decide +kernel

theorem kcensus1015_29 : censusOK 17 (bgWords1015.getD 29 0) = true := by
  decide +kernel

theorem kcensus1015 (i : Nat) (hi : i < 30) : censusOK 17 (bgWords1015.getD i 0) = true :=
  match i, hi with
  | 0, _ => kcensus1015_0
  | 1, _ => kcensus1015_1
  | 2, _ => kcensus1015_2
  | 3, _ => kcensus1015_3
  | 4, _ => kcensus1015_4
  | 5, _ => kcensus1015_5
  | 6, _ => kcensus1015_6
  | 7, _ => kcensus1015_7
  | 8, _ => kcensus1015_8
  | 9, _ => kcensus1015_9
  | 10, _ => kcensus1015_10
  | 11, _ => kcensus1015_11
  | 12, _ => kcensus1015_12
  | 13, _ => kcensus1015_13
  | 14, _ => kcensus1015_14
  | 15, _ => kcensus1015_15
  | 16, _ => kcensus1015_16
  | 17, _ => kcensus1015_17
  | 18, _ => kcensus1015_18
  | 19, _ => kcensus1015_19
  | 20, _ => kcensus1015_20
  | 21, _ => kcensus1015_21
  | 22, _ => kcensus1015_22
  | 23, _ => kcensus1015_23
  | 24, _ => kcensus1015_24
  | 25, _ => kcensus1015_25
  | 26, _ => kcensus1015_26
  | 27, _ => kcensus1015_27
  | 28, _ => kcensus1015_28
  | 29, _ => kcensus1015_29
  | i + 30, hi => absurd hi (by omega)

/-- **No point of `K` has the background `1110100000` from a cell `p ≤ 12` on**, at any alignment `(a, o)`. -/
theorem no_k_tail_1015 (u : Nat → Bool) (a o p : Nat) (hp : p ≤ 12)
    (hu : ∀ j, p ≤ j → u j = ringCell bgStates1015 10 a (j + o)) : ¬ InK u :=
  not_inK_of_tables bgStates1015 10 15 17 bgWords1015 bgIndex1015 30 (by decide) (by decide)
    (by decide) (by decide) bgIndex1015_ok kcensus1015 u a o p hp hu

/-! ### The background `111110010000`: `L = 12`, `P = 3` -/

/-- The 3 states of the background `111110010000` on a ring of 12 cells, bit `j` the ring cell `j`. -/
def bgStates123 : List Nat := [159, 2544, 3849]

theorem bgStates123_cycle : ringStepOK bgStates123 12 = true := by
  decide +kernel

/-- The background `111110010000` is a cycle of the held map on the ring of 12 cells. -/
theorem bgStep123 (a j : Nat) : ringCell bgStates123 12 (a + 1) j =
    xor (ringCell bgStates123 12 a (j + 1)) (ringCell bgStates123 12 a j || ringCell bgStates123 12 a (j + 11)) :=
  ringCell_step bgStates123 12 (by decide) (by decide) bgStates123_cycle a j

/-- The 12 distinct tail words of the background, cells 12 to 63 in place. -/
def bgWords123 : List Nat := [17338588019464728576, 17892666046587138048, 8946333023293566976, 4473166511646781440, 11459955292678164480, 5729977646339080192, 2864988823169540096, 1432494411584770048, 716247205792382976, 9581495639750967296, 14014119856730259456, 16230431965219905536]

/-- Entry `12 a + o`: the index in `bgWords123` of the tail word at the alignment `(a, o)`. -/
def bgIndex123 : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7, 4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3]

theorem bgIndex123_ok : indexOK bgStates123 12 3 12 bgWords123 bgIndex123 = true := by
  decide +kernel

theorem kcensus123_0 : censusOK 17 (bgWords123.getD 0 0) = true := by
  decide +kernel

theorem kcensus123_1 : censusOK 17 (bgWords123.getD 1 0) = true := by
  decide +kernel

theorem kcensus123_2 : censusOK 17 (bgWords123.getD 2 0) = true := by
  decide +kernel

theorem kcensus123_3 : censusOK 17 (bgWords123.getD 3 0) = true := by
  decide +kernel

theorem kcensus123_4 : censusOK 17 (bgWords123.getD 4 0) = true := by
  decide +kernel

theorem kcensus123_5 : censusOK 17 (bgWords123.getD 5 0) = true := by
  decide +kernel

theorem kcensus123_6 : censusOK 17 (bgWords123.getD 6 0) = true := by
  decide +kernel

theorem kcensus123_7 : censusOK 17 (bgWords123.getD 7 0) = true := by
  decide +kernel

theorem kcensus123_8 : censusOK 17 (bgWords123.getD 8 0) = true := by
  decide +kernel

theorem kcensus123_9 : censusOK 17 (bgWords123.getD 9 0) = true := by
  decide +kernel

theorem kcensus123_10 : censusOK 17 (bgWords123.getD 10 0) = true := by
  decide +kernel

theorem kcensus123_11 : censusOK 17 (bgWords123.getD 11 0) = true := by
  decide +kernel

theorem kcensus123 (i : Nat) (hi : i < 12) : censusOK 17 (bgWords123.getD i 0) = true :=
  match i, hi with
  | 0, _ => kcensus123_0
  | 1, _ => kcensus123_1
  | 2, _ => kcensus123_2
  | 3, _ => kcensus123_3
  | 4, _ => kcensus123_4
  | 5, _ => kcensus123_5
  | 6, _ => kcensus123_6
  | 7, _ => kcensus123_7
  | 8, _ => kcensus123_8
  | 9, _ => kcensus123_9
  | 10, _ => kcensus123_10
  | 11, _ => kcensus123_11
  | i + 12, hi => absurd hi (by omega)

/-- **No point of `K` has the background `111110010000` from a cell `p ≤ 12` on**, at any alignment `(a, o)`. -/
theorem no_k_tail_123 (u : Nat → Bool) (a o p : Nat) (hp : p ≤ 12)
    (hu : ∀ j, p ≤ j → u j = ringCell bgStates123 12 a (j + o)) : ¬ InK u :=
  not_inK_of_tables bgStates123 12 3 17 bgWords123 bgIndex123 12 (by decide) (by decide)
    (by decide) (by decide) bgIndex123_ok kcensus123 u a o p hp hu

end Rule30Open
