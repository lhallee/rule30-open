module

public import Rule30Open.Complexity.ConeScreening

/-!
# Reading the cone from the left: the cells `-t .. -3` are pairwise distinguishable for `t ≤ 17`, and not at `t = 18`

The center after `t` steps is a function of the cells `-t .. t` of a row (`ConeScreening`). Split the row at cell `-2`:
the *prefix* is the cells `-t .. -3`, the *completion* everything from `-2` on. For `3 ≤ t ≤ 17`, any two rows that
differ somewhere on their prefixes have a common completion on which their centers differ (`left_cut`), and so do two
rows that differ left of any cut `a ≤ -2` (`left_cut_at`). So every way to compute the center through a set of states at
the cut, a state from the cells left of the cut and the center from that state and the cells from the cut on, has at
least `2 ^ (t + a)` states (`left_cut_factor`, `left_cut_width`): the width of an ordered decision diagram that reads
the row from the left, at the level of its first `t + a` cells, and the number of messages of a one-way protocol across
the cut.

For each `t` the kernel checks, by `decide +kernel`, that a list of at most 32 completions splits the `2 ^ (t - 2)`
prefixes into single prefixes (`cutCheck`). The prefixes are the bits of numbers (`sliceStep` runs Rule 30 on all of
them at once, bit `P` of each number belonging to prefix `P`), a class of prefixes is a mask, and `refineMasks` splits
every class by the center at the first completion, each part by the second, and so on, dropping the parts of at most one
prefix, and ends with no part left. The completions come from the rows with any cells `-2, -1` and at most one black
cell in the right half (`t ≤ 12`), or at most two (`13 ≤ t ≤ 17`).

The statement fails at `t = 18` (`left_cut_fails_18`): the odd stripe ending black at `-3` makes the center white and
the even stripe ending black at `-4` makes it black, for every completion (`stripe_three_18`, `stripe_four_18`, checked
over all `2 ^ 21` completions at once with the completions sliced, `completionCenters`).
-/

@[expose] public section

namespace Rule30Open

/-- The row equal to `x` left of cell `a` and to `z` from cell `a` on. -/
def spliceAt (a : Int) (x z : Int → Bool) : Int → Bool := fun i => if i < a then x i else z i

/-- The center after `t` steps of the row whose cells `-t .. -3` are the bits of `P` (bit `k` is cell `-t + k`) and
whose cells from `-2` on are the bits of `r` (bit `k` is cell `-2 + k`). -/
def cutCenter (t P r : Nat) : Bool := (nevo (2 ^ (t - 2) * r + P) t).testBit 0

/-! ## Rows of numbers: every prefix at once

Bit `P` of the number in place `k` of a sliced row is cell `k` of the row of prefix `P`. Rule 30 acts on the sliced
row by the bitwise formula of `nstep` (`sliceStep`), so bit `P` of the sliced center is the center for prefix `P`
(`testBit_sliceCenter`). -/

/-- Entry `k` of a list, and `0` past its end. -/
def nth0 : List Nat → Nat → Nat
  | [], _ => 0
  | a :: _, 0 => a
  | _ :: l, k + 1 => nth0 l k

/-- One step on a sliced row: entry `k` becomes entry `k` xor (entry `k + 1` or entry `k + 2`), the entries past the
end read as `0`. -/
def sliceStep : List Nat → List Nat
  | [] => []
  | a :: tl => (a ^^^ (nth0 tl 0 ||| nth0 tl 1)) :: sliceStep tl

def sliceEvo (l : List Nat) : Nat → List Nat
  | 0 => l
  | s + 1 => sliceStep (sliceEvo l s)

theorem nth0_sliceStep (l : List Nat) :
    ∀ k, nth0 (sliceStep l) k = nth0 l k ^^^ (nth0 l (k + 1) ||| nth0 l (k + 2)) := by
  induction l with
  | nil => intro k; simp [sliceStep, nth0]
  | cons a tl ih =>
    intro k
    cases k with
    | zero => simp [sliceStep, nth0]
    | succ k =>
      simp only [sliceStep, nth0]
      exact ih k

/-- Bit `P` of the sliced evolution is the evolution of the row whose bits are the bits `P` of the sliced row. -/
theorem testBit_sliceEvo (l : List Nat) (R P : Nat) (h : ∀ k, (nth0 l k).testBit P = R.testBit k) :
    ∀ s k, (nth0 (sliceEvo l s) k).testBit P = (nevo R s).testBit k := by
  intro s
  induction s with
  | zero => exact h
  | succ s ih =>
    intro k
    simp only [sliceEvo, nevo, nstep]
    rw [nth0_sliceStep, Nat.testBit_xor, Nat.testBit_or, Nat.testBit_xor, Nat.testBit_or, Nat.testBit_shiftRight,
      Nat.testBit_shiftRight, ih k, ih (k + 1), ih (k + 2), Nat.add_comm 1 k, Nat.add_comm 2 k]

/-- The numbers `f 0, ..., f (n - 1)`. -/
def tabulate (f : Nat → Nat) : Nat → List Nat
  | 0 => []
  | n + 1 => f 0 :: tabulate (fun k => f (k + 1)) n

theorem nth0_tabulate (n : Nat) : ∀ (f : Nat → Nat) (k : Nat), nth0 (tabulate f n) k = if k < n then f k else 0 := by
  induction n with
  | zero => intro f k; simp [tabulate, nth0]
  | succ n ih =>
    intro f k
    cases k with
    | zero => simp [tabulate, nth0]
    | succ k =>
      simp only [tabulate, nth0]
      rw [ih]
      by_cases hk : k < n
      · rw [ite_eq_left hk, ite_eq_left (by omega)]
      · rw [ite_eq_right hk, ite_eq_right (by omega)]

/-- The prefix cell `i` as a number over the prefixes `P < 2 ^ n`: bit `P` is bit `i` of `P`. -/
def cellPattern (i : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => cellPattern i n + 2 ^ (2 ^ n) * (bif i == n then 2 ^ (2 ^ n) - 1 else cellPattern i n)

theorem testBit_cellPattern (i n : Nat) :
    ∀ P, (cellPattern i n).testBit P = (decide (P < 2 ^ n) && P.testBit i) := by
  induction n with
  | zero =>
    intro P
    simp only [cellPattern, Nat.zero_testBit, Nat.pow_zero]
    cases P with
    | zero => simp
    | succ P => simp
  | succ n ih =>
    intro P
    have hlt : cellPattern i n < 2 ^ (2 ^ n) := by
      apply Nat.lt_pow_two_of_testBit
      intro j hj
      rw [ih]
      simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
      left
      omega
    have hpow : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by rw [Nat.pow_succ]; omega
    simp only [cellPattern]
    rw [Nat.add_comm, Nat.testBit_two_pow_mul_add _ hlt, ih]
    by_cases hP : P < 2 ^ n
    · rw [ite_eq_left hP]
      simp [hP, show P < 2 ^ (n + 1) by omega]
    · rw [ite_eq_right hP]
      by_cases hi : i = n
      · subst hi
        simp only [beq_self_eq_true, Bool.cond_true, Nat.testBit_two_pow_sub_one]
        by_cases h2 : P < 2 ^ (i + 1)
        · rw [Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt (by omega) h2]
          simp [h2]
          omega
        · simp [h2]
          omega
      · have hb : (i == n) = false := by simp [hi]
        rw [hb, Bool.cond_false, ih]
        by_cases h2 : P < 2 ^ (n + 1)
        · have e : P = 2 ^ n * 1 + (P - 2 ^ n) := by omega
          have hsmall : P - 2 ^ n < 2 ^ n := by omega
          have hbit : P.testBit i = (P - 2 ^ n).testBit i := by
            conv => lhs; rw [e]
            rw [Nat.testBit_two_pow_mul_add _ hsmall]
            by_cases hin : i < n
            · rw [ite_eq_left hin]
            · rw [ite_eq_right hin]
              have hni : n + 1 ≤ i := by omega
              have hpow : 2 ^ n ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
              have h0 : (P - 2 ^ n).testBit i = false := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hsmall hpow)
              have h1 : (1 : Nat).testBit (i - n) = false := by
                rw [show i - n = (i - n - 1) + 1 by omega, Nat.testBit_succ]
                simp
              rw [h0, h1]
          simp [hsmall, h2, hbit]
        · simp [h2]
          omega

/-! ## Splitting classes of prefixes, as masks -/

/-- `u` has at most one bit set, tested as `u &&& (u - 1) = 0`. -/
def lowOne (u : Nat) : Bool := u &&& (u - 1) == 0

theorem testBit_and_pred (u P Q : Nat) (hPQ : P < Q) (hP : u.testBit P = true) (hQ : u.testBit Q = true) :
    (u &&& (u - 1)).testBit Q = true := by
  have hmod : u % 2 ^ Q < 2 ^ Q := Nat.mod_lt _ (Nat.two_pow_pos Q)
  have hdm : 2 ^ Q * (u / 2 ^ Q) + u % 2 ^ Q = u := Nat.div_add_mod u (2 ^ Q)
  have hb : (u % 2 ^ Q).testBit P = true := by
    rw [← hdm, Nat.testBit_two_pow_mul_add _ hmod, ite_eq_left hPQ] at hP
    exact hP
  have hpos : u % 2 ^ Q ≠ 0 := by
    intro h0
    rw [h0, Nat.zero_testBit] at hb
    cases hb
  have ha : (u / 2 ^ Q).testBit 0 = true := by
    rw [← hdm, Nat.testBit_two_pow_mul_add _ hmod, ite_eq_right (by omega), Nat.sub_self] at hQ
    exact hQ
  have hpred : u - 1 = 2 ^ Q * (u / 2 ^ Q) + (u % 2 ^ Q - 1) := by omega
  rw [Nat.testBit_and, hpred, Nat.testBit_two_pow_mul_add _ (by omega), ite_eq_right (by omega), Nat.sub_self, ha,
    hQ]
  rfl

theorem eq_of_lowOne (u P Q : Nat) (h : lowOne u = true) (hP : u.testBit P = true) (hQ : u.testBit Q = true) :
    P = Q := by
  have h0 : u &&& (u - 1) = 0 := by simpa [lowOne] using h
  rcases Nat.lt_trichotomy P Q with hlt | heq | hgt
  · have := testBit_and_pred u P Q hlt hP hQ
    rw [h0, Nat.zero_testBit] at this
    cases this
  · exact heq
  · have := testBit_and_pred u Q P hgt hQ hP
    rw [h0, Nat.zero_testBit] at this
    cases this

/-- Put the mask `u` in front of `rest` unless it has at most one bit. -/
def keepMask (u : Nat) (rest : List Nat) : List Nat := bif lowOne u then rest else u :: rest

/-- Split every mask by the column `C`, the part inside `C` and the part outside, keeping the parts of at least two
bits. -/
def splitMasks (C : Nat) : List Nat → List Nat
  | [] => []
  | m :: ms => keepMask (m &&& C) (keepMask (m ^^^ (m &&& C)) (splitMasks C ms))

/-- Split by the column of every completion of the list in turn; true when no mask of two or more bits is left. -/
def refineMasks (col : Nat → Nat) : List Nat → List Nat → Bool
  | [], [] => true
  | [], _ :: _ => false
  | r :: rs, ms => refineMasks col rs (splitMasks (col r) ms)

/-- Every two distinct bits of the mask `m` differ in the column of some completion of `rs`. -/
def MaskSeparates (col : Nat → Nat) (rs : List Nat) (m : Nat) : Prop :=
  ∀ P Q, m.testBit P = true → m.testBit Q = true → P ≠ Q → ∃ r, r ∈ rs ∧ (col r).testBit P ≠ (col r).testBit Q

theorem mem_keepMask (u : Nat) (rest : List Nat) (h : lowOne u = false) : u ∈ keepMask u rest := by
  simp [keepMask, h]

theorem mem_keepMask_of_mem (u w : Nat) (rest : List Nat) (h : w ∈ rest) : w ∈ keepMask u rest := by
  unfold keepMask
  cases lowOne u
  · exact List.mem_cons_of_mem u h
  · exact h

theorem mem_splitMasks (C : Nat) (ms : List Nat) :
    ∀ m, m ∈ ms → ∀ w, (w = m &&& C ∨ w = m ^^^ (m &&& C)) → lowOne w = false → w ∈ splitMasks C ms := by
  induction ms with
  | nil => intro m hm; cases hm
  | cons m0 ms ih =>
    intro m hm w hw hb
    simp only [splitMasks]
    rcases List.mem_cons.mp hm with rfl | hm
    · rcases hw with rfl | rfl
      · exact mem_keepMask _ _ hb
      · exact mem_keepMask_of_mem _ _ _ (mem_keepMask _ _ hb)
    · exact mem_keepMask_of_mem _ _ _ (mem_keepMask_of_mem _ _ _ (ih m hm w hw hb))

/-- **Soundness of the split.** If `refineMasks` accepts, every mask it started from is separated. -/
theorem separates_of_refineMasks (col : Nat → Nat) (rs : List Nat) :
    ∀ ms : List Nat, refineMasks col rs ms = true → ∀ m, m ∈ ms → MaskSeparates col rs m := by
  induction rs with
  | nil =>
    intro ms h m hm
    match ms, h, hm with
    | [], _, hm => cases hm
  | cons r rs ih =>
    intro ms h m hm P Q hP hQ hne
    have hrest := ih (splitMasks (col r) ms) h
    by_cases hd : (col r).testBit P = (col r).testBit Q
    · have side : ∃ w, (w = m &&& col r ∨ w = m ^^^ (m &&& col r)) ∧ w.testBit P = true ∧ w.testBit Q = true := by
        cases hc : (col r).testBit P
        · refine ⟨m ^^^ (m &&& col r), Or.inr rfl, ?_, ?_⟩
          · simp [hP, hc]
          · simp [hQ, ← hd, hc]
        · refine ⟨m &&& col r, Or.inl rfl, ?_, ?_⟩
          · simp [hP, hc]
          · simp [hQ, ← hd, hc]
      obtain ⟨w, hw, hPw, hQw⟩ := side
      have hb : lowOne w = false := by
        cases hl : lowOne w
        · rfl
        · exact absurd (eq_of_lowOne w P Q hl hPw hQw) hne
      obtain ⟨r', hr', hne'⟩ := hrest w (mem_splitMasks (col r) ms m hm w hw hb) P Q hPw hQw hne
      exact ⟨r', List.mem_cons_of_mem r hr', hne'⟩
    · exact ⟨r, List.mem_cons_self, hd⟩

/-! ## The sliced center -/

/-- Place `k` of the sliced row at `t` with completion `r`: a prefix cell pattern for `k < t - 2`, else all ones or
all zeros by bit `k - (t - 2)` of `r`. -/
def rowCell (t r k : Nat) : Nat :=
  if k < t - 2 then cellPattern k (t - 2) else bif r.testBit (k - (t - 2)) then 2 ^ (2 ^ (t - 2)) - 1 else 0

/-- The centers after `t` steps for completion `r`, as a number: bit `P` is `cutCenter t P r`. -/
def sliceCenter (t r : Nat) : Nat := nth0 (sliceEvo (tabulate (rowCell t r) (2 * t + 1)) t) 0

theorem testBit_sliceCenter (t r P : Nat) (ht : 2 ≤ t) (hP : P < 2 ^ (t - 2)) (hr : r < 2 ^ (t + 3)) :
    (sliceCenter t r).testBit P = cutCenter t P r := by
  unfold sliceCenter cutCenter
  apply testBit_sliceEvo
  intro k
  rw [nth0_tabulate, Nat.testBit_two_pow_mul_add _ hP]
  by_cases hk : k < 2 * t + 1
  · rw [ite_eq_left hk]
    unfold rowCell
    by_cases hk2 : k < t - 2
    · rw [ite_eq_left hk2, ite_eq_left hk2, testBit_cellPattern]
      simp [hP]
    · rw [ite_eq_right hk2, ite_eq_right hk2]
      cases r.testBit (k - (t - 2)) <;> simp [Nat.testBit_two_pow_sub_one, hP]
  · rw [ite_eq_right hk, ite_eq_right (by omega), Nat.zero_testBit]
    exact (Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hr (Nat.pow_le_pow_right (by omega) (by omega)))).symm

/-- The check at `t`: every completion of `rs` lies in `2 ^ (t + 3)`, and their columns split the mask of all
`2 ^ (t - 2)` prefixes into masks of at most one prefix. -/
def cutCheck (t : Nat) (rs : List Nat) : Bool :=
  rs.all (fun r => decide (r < 2 ^ (t + 3))) && refineMasks (sliceCenter t) rs [2 ^ (2 ^ (t - 2)) - 1]

/-! ## From the numbers to rows -/

/-- The center of a spliced row is `cutCenter` of its prefix, read as a number, and the completion's number. -/
theorem evo_splice_cut (t : Nat) (ht : 2 ≤ t) (x : Int → Bool) (r : Nat) :
    evo (spliceAt (-2) x (rowN r (-2))) t 0 = cutCenter t (enc (fun k => x ((k : Int) - t)) (t - 2)) r := by
  have hP := enc_lt (t - 2) (fun k => x ((k : Int) - t))
  have hloc : evo (spliceAt (-2) x (rowN r (-2))) t 0 =
      evo (rowN (2 ^ (t - 2) * r + enc (fun k => x ((k : Int) - t)) (t - 2)) (-(t : Int))) t 0 := by
    apply evo_local
    intro i h1 h2
    simp only [spliceAt, rowN]
    rw [ite_eq_left (show -(t : Int) ≤ i by omega), Nat.testBit_two_pow_mul_add _ hP]
    by_cases hi : i < -2
    · rw [ite_eq_left hi, ite_eq_left (show (i - -(t : Int)).toNat < t - 2 by omega), testBit_enc _ _ _ (by omega)]
      congr 1
      omega
    · rw [ite_eq_right hi, ite_eq_left (show (-2 : Int) ≤ i by omega),
        ite_eq_right (show ¬ (i - -(t : Int)).toNat < t - 2 by omega)]
      congr 1
      omega
  rw [hloc, evo_rowN _ _ _ 0 (by omega)]
  simp only [rowN, cutCenter]
  rw [ite_eq_left (by omega), show (0 - (-(t : Int) + (t : Int))).toNat = 0 by omega]

/-- A passing `cutCheck` at `t` separates every two rows that differ on cells `-t .. -3`. -/
theorem left_cut_of_check (t : Nat) (ht : 3 ≤ t) (rs : List Nat) (hc : cutCheck t rs = true)
    (x y : Int → Bool) (i : Int) (hi1 : -(t : Int) ≤ i) (hi2 : i ≤ -3) (hne : x i ≠ y i) :
    ∃ z : Int → Bool, evo (spliceAt (-2) x z) t 0 ≠ evo (spliceAt (-2) y z) t 0 := by
  simp only [cutCheck, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hc
  obtain ⟨hall, hc⟩ := hc
  let P := enc (fun k => x ((k : Int) - t)) (t - 2)
  let Q := enc (fun k => y ((k : Int) - t)) (t - 2)
  have hPlt : P < 2 ^ (t - 2) := enc_lt _ _
  have hQlt : Q < 2 ^ (t - 2) := enc_lt _ _
  have hPQ : P ≠ Q := by
    intro h
    apply hne
    have hx := testBit_enc (t - 2) (fun k => x ((k : Int) - t)) (i + t).toNat (by omega)
    have hy := testBit_enc (t - 2) (fun k => y ((k : Int) - t)) (i + t).toNat (by omega)
    have e : (((i + t).toNat : Nat) : Int) - t = i := by omega
    simp only [e] at hx hy
    rw [← hx, ← hy]
    exact congrArg (fun n => n.testBit (i + t).toNat) h
  have hall' : ∀ m, m < 2 ^ (t - 2) → (2 ^ (2 ^ (t - 2)) - 1).testBit m = true := by
    intro m hm
    simp [Nat.testBit_two_pow_sub_one, hm]
  obtain ⟨r, hr, hne'⟩ := separates_of_refineMasks _ rs _ hc _ List.mem_cons_self P Q
    (hall' P hPlt) (hall' Q hQlt) hPQ
  refine ⟨rowN r (-2), ?_⟩
  rw [evo_splice_cut t (by omega), evo_splice_cut t (by omega)]
  rw [testBit_sliceCenter t r P (by omega) hPlt (hall r hr), testBit_sliceCenter t r Q (by omega) hQlt (hall r hr)]
    at hne'
  exact hne'

/-! ## The certificates -/

/-- The 1 completions for `t = 3`, from the family with at most 1 black cell in the right half. -/
def cutCert3 : List Nat := [0]

theorem cutCert3_check : cutCheck 3 cutCert3 = true := by
  decide +kernel

/-- The 2 completions for `t = 4`, from the family with at most 1 black cell in the right half. -/
def cutCert4 : List Nat := [0, 16]

theorem cutCert4_check : cutCheck 4 cutCert4 = true := by
  decide +kernel

/-- The 3 completions for `t = 5`, from the family with at most 1 black cell in the right half. -/
def cutCert5 : List Nat := [0, 2, 16]

theorem cutCert5_check : cutCheck 5 cutCert5 = true := by
  decide +kernel

/-- The 4 completions for `t = 6`, from the family with at most 1 black cell in the right half. -/
def cutCert6 : List Nat := [0, 1, 4, 33]

theorem cutCert6_check : cutCheck 6 cutCert6 = true := by
  decide +kernel

/-- The 6 completions for `t = 7`, from the family with at most 1 black cell in the right half. -/
def cutCert7 : List Nat := [0, 3, 18, 4, 9, 16]

theorem cutCert7_check : cutCheck 7 cutCert7 = true := by
  decide +kernel

/-- The 8 completions for `t = 8`, from the family with at most 1 black cell in the right half. -/
def cutCert8 : List Nat := [0, 1, 7, 16, 4, 64, 131, 2]

theorem cutCert8_check : cutCheck 8 cutCert8 = true := by
  decide +kernel

/-- The 10 completions for `t = 9`, from the family with at most 1 black cell in the right half. -/
def cutCert9 : List Nat := [0, 7, 9, 8, 65, 66, 64, 32, 3, 514]

theorem cutCert9_check : cutCheck 9 cutCert9 = true := by
  decide +kernel

/-- The 13 completions for `t = 10`, from the family with at most 1 black cell in the right half. -/
def cutCert10 : List Nat := [0, 33, 67, 7, 256, 17, 64, 2, 8, 3, 16, 66, 19]

theorem cutCert10_check : cutCheck 10 cutCert10 = true := by
  decide +kernel

/-- The 14 completions for `t = 11`, from the family with at most 1 black cell in the right half. -/
def cutCert11 : List Nat := [0, 129, 9, 19, 64, 4, 16, 8, 7, 1027, 131, 3, 67, 32]

theorem cutCert11_check : cutCheck 11 cutCert11 = true := by
  decide +kernel

/-- The 19 completions for `t = 12`, from the family with at most 1 black cell in the right half. -/
def cutCert12 : List Nat := [0, 7, 19, 64, 16, 4, 67, 259, 66, 33, 32, 8, 3, 514, 2, 129, 34, 258, 131]

theorem cutCert12_check : cutCheck 12 cutCert12 = true := by
  decide +kernel

/-- The 18 completions for `t = 13`, from the family with at most 2 black cells in the right half. -/
def cutCert13 : List Nat := [0, 519, 14, 1091, 516, 39, 66, 15, 2051, 16393, 264, 134, 529, 7, 16, 36, 1026, 144]

theorem cutCert13_check : cutCheck 13 cutCert13 = true := by
  decide +kernel

/-- The 22 completions for `t = 14`, from the family with at most 2 black cells in the right half. -/
def cutCert14 : List Nat := [0, 132, 7, 8225, 134, 15, 528, 67, 264, 34, 259, 68, 19, 529, 139, 16388, 133, 36, 3, 2, 16, 8]

theorem cutCert14_check : cutCheck 14 cutCert14 = true := by
  decide +kernel

/-- The 24 completions for `t = 15`, from the family with at most 2 black cells in the right half. -/
def cutCert15 : List Nat := [0, 1027, 71, 32772, 16450, 1057, 16392, 34, 39, 15, 531, 1031, 14, 8208, 132, 136, 130, 16389, 288, 4115, 18, 262, 4103, 36]

theorem cutCert15_check : cutCheck 15 cutCert15 = true := by
  decide +kernel

/-- The 26 completions for `t = 16`, from the family with at most 2 black cells in the right half. -/
def cutCert16 : List Nat := [0, 132, 2114, 2059, 33, 264, 4355, 39, 2057, 529, 68, 290, 16392, 8211, 135, 1026, 18, 3, 36, 14, 2064, 265, 8196, 72, 16419, 2]

theorem cutCert16_check : cutCheck 16 cutCert16 = true := by
  decide +kernel

/-- The 32 completions for `t = 17`, from the family with at most 2 black cells in the right half. -/
def cutCert17 : List Nat := [0, 75, 33, 2052, 34, 37, 134, 264, 528, 15, 2059, 1155, 14, 132, 19, 136, 2065, 1088, 265, 2, 8199, 517, 32772, 135, 262, 69, 65, 36, 32775, 1026, 8, 4115]

theorem cutCert17_check : cutCheck 17 cutCert17 = true := by
  decide +kernel

/-- The certificate for `t`, empty outside the range checked. -/
def cutCertList : Nat → List Nat
  | 3 => cutCert3
  | 4 => cutCert4
  | 5 => cutCert5
  | 6 => cutCert6
  | 7 => cutCert7
  | 8 => cutCert8
  | 9 => cutCert9
  | 10 => cutCert10
  | 11 => cutCert11
  | 12 => cutCert12
  | 13 => cutCert13
  | 14 => cutCert14
  | 15 => cutCert15
  | 16 => cutCert16
  | 17 => cutCert17
  | _ => []

/-! ## The cut fails at `t = 18`: two stripes fix the center

With the prefix fixed and the completions sliced, bit `r` of `completionCenters t P` is the center for the completion
`r` (`testBit_completionCenters`). At `t = 18` the odd stripe ending black at `-3` makes the center white for all
`2 ^ 21` completions, and the even stripe ending black at `-4` makes it black, whatever cell `-3` is
(`stripe_three_18`, `stripe_four_18`); with `flip_center` the odd stripe and the even stripe flipped at `-18` are two
prefixes that no completion separates (`left_cut_fails_18`). -/

/-- Place `k` of the row sliced over the completions: all ones or all zeros by bit `k` of the prefix `P` for
`k < t - 2`, else the pattern of completion cell `k - (t - 2)`. -/
def rowCellC (t P k : Nat) : Nat :=
  if k < t - 2 then (bif P.testBit k then 2 ^ (2 ^ (t + 3)) - 1 else 0) else cellPattern (k - (t - 2)) (t + 3)

/-- The centers after `t` steps for the prefix `P`, as a number: bit `r` is `cutCenter t P r`. -/
def completionCenters (t P : Nat) : Nat := nth0 (sliceEvo (tabulate (rowCellC t P) (2 * t + 1)) t) 0

theorem testBit_completionCenters (t P r : Nat) (ht : 2 ≤ t) (hP : P < 2 ^ (t - 2)) (hr : r < 2 ^ (t + 3)) :
    (completionCenters t P).testBit r = cutCenter t P r := by
  unfold completionCenters cutCenter
  apply testBit_sliceEvo
  intro k
  rw [nth0_tabulate, Nat.testBit_two_pow_mul_add _ hP]
  by_cases hk : k < 2 * t + 1
  · rw [ite_eq_left hk]
    unfold rowCellC
    by_cases hk2 : k < t - 2
    · rw [ite_eq_left hk2, ite_eq_left hk2]
      cases P.testBit k <;> simp [Nat.testBit_two_pow_sub_one, hr]
    · rw [ite_eq_right hk2, ite_eq_right hk2, testBit_cellPattern]
      simp [hr]
  · rw [ite_eq_right hk, ite_eq_right (by omega), Nat.zero_testBit]
    exact (Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hr (Nat.pow_le_pow_right (by omega) (by omega)))).symm

/-- The center of any row through its prefix and the number of its cells `-2 .. t`. -/
theorem center_of_prefix (t : Nat) (ht : 2 ≤ t) (x : Int → Bool) :
    evo x t 0 = cutCenter t (enc (fun k => x ((k : Int) - t)) (t - 2)) (enc (fun k => x ((k : Int) - 2)) (t + 3)) := by
  rw [← evo_splice_cut t ht x]
  apply evo_local
  intro i h1 h2
  simp only [spliceAt, rowN]
  by_cases hi : i < -2
  · rw [ite_eq_left hi]
  · rw [ite_eq_right hi, ite_eq_left (show (-2 : Int) ≤ i by omega), testBit_enc _ _ _ (by omega)]
    congr 1
    omega

/-- A prefix whose centers are all `v` fixes the center of every row that carries it. -/
theorem center_of_completionCenters (t : Nat) (ht : 2 ≤ t) (x : Int → Bool) (P : Nat) (v : Bool)
    (hP : enc (fun k => x ((k : Int) - t)) (t - 2) = P)
    (hc : completionCenters t P = bif v then 2 ^ (2 ^ (t + 3)) - 1 else 0) : evo x t 0 = v := by
  rw [center_of_prefix t ht x, hP]
  have hPlt : P < 2 ^ (t - 2) := by rw [← hP]; exact enc_lt _ _
  have hr := enc_lt (t + 3) (fun k => x ((k : Int) - 2))
  rw [← testBit_completionCenters t P _ ht hPlt hr, hc]
  cases v <;> simp [Nat.testBit_two_pow_sub_one, hr]

theorem stripe_three_check : completionCenters 18 43690 = 0 := by
  decide +kernel

theorem stripe_four_check : completionCenters 18 21845 = bif true then 2 ^ (2 ^ (18 + 3)) - 1 else 0 := by
  decide +kernel

theorem stripe_four_check' : completionCenters 18 54613 = bif true then 2 ^ (2 ^ (18 + 3)) - 1 else 0 := by
  decide +kernel

/-- **The odd stripe to `-3`.** If `x (-j) = (j odd)` for `3 ≤ j ≤ 18`, the center after 18 steps is white, whatever
the cells `-2, -1, 0, ...` are. -/
theorem stripe_three_18 (x : Int → Bool) (h : ∀ j : Int, 3 ≤ j → j ≤ 18 → x (-j) = odd j) : evo x 18 0 = false := by
  refine center_of_completionCenters 18 (by omega) x 43690 false ?_ stripe_three_check
  have : enc (fun k => x ((k : Int) - ((18 : Nat) : Int))) (18 - 2) = enc (fun k => odd ((18 : Int) - k)) 16 := by
    apply enc_congr
    intro k hk
    have := h ((18 : Int) - k) (by omega) (by omega)
    rw [show -((18 : Int) - k) = (k : Int) - ((18 : Nat) : Int) by omega] at this
    exact this
  rw [this]
  decide +kernel

/-- **The even stripe to `-4`.** If `x (-j) = (j even)` for `4 ≤ j ≤ 18`, the center after 18 steps is black, whatever
the cells `-3, -2, -1, 0, ...` are. -/
theorem stripe_four_18 (x : Int → Bool) (h : ∀ j : Int, 4 ≤ j → j ≤ 18 → x (-j) = even j) : evo x 18 0 = true := by
  have e : enc (fun k => x ((k : Int) - ((18 : Nat) : Int))) (18 - 2) =
      enc (fun k => if k = 15 then x (-3) else even ((18 : Int) - k)) 16 := by
    apply enc_congr
    intro k hk
    by_cases h15 : k = 15
    · subst h15
      simp
    · rw [ite_eq_right h15]
      have := h ((18 : Int) - k) (by omega) (by omega)
      rw [show -((18 : Int) - k) = (k : Int) - ((18 : Nat) : Int) by omega] at this
      exact this
  cases h3 : x (-3)
  · refine center_of_completionCenters 18 (by omega) x 21845 true ?_ stripe_four_check
    rw [e, h3]
    decide +kernel
  · refine center_of_completionCenters 18 (by omega) x 54613 true ?_ stripe_four_check'
    rw [e, h3]
    decide +kernel

/-- **The left cut fails at `t = 18`.** Two rows that differ at cell `-4` give the same center after 18 steps for every
completion from cell `-2` on: the odd stripe to `-3`, and the even stripe to `-4` with cell `-18` flipped. -/
theorem left_cut_fails_18 : ∃ x y : Int → Bool, x (-4) ≠ y (-4) ∧
    ∀ z : Int → Bool, evo (spliceAt (-2) x z) 18 0 = evo (spliceAt (-2) y z) 18 0 := by
  refine ⟨fun i => odd (-i), flipAt (fun i => even (-i)) (-18), by decide, ?_⟩
  intro z
  have hx := stripe_three_18 (spliceAt (-2) (fun i => odd (-i)) z) (fun j h1 h2 => by
    simp only [spliceAt]
    rw [ite_eq_left (by omega), Int.neg_neg])
  have hy := flip_center (spliceAt (-2) (fun i => even (-i)) z) 18
  have hs : flipAt (spliceAt (-2) (fun i => even (-i)) z) (-18) =
      spliceAt (-2) (flipAt (fun i => even (-i)) (-18)) z := by
    funext i
    simp only [flipAt, spliceAt]
    by_cases hi : i = -18
    · subst hi; simp
    · rw [ite_eq_right hi]
      by_cases h2 : i < -2
      · rw [ite_eq_left h2, ite_eq_left h2, ite_eq_right hi]
      · rw [ite_eq_right h2, ite_eq_right h2]
  have h4 := stripe_four_18 (spliceAt (-2) (fun i => even (-i)) z) (fun j h1 h2 => by
    simp only [spliceAt]
    rw [ite_eq_left (by omega), Int.neg_neg])
  have hy' : evo (flipAt (spliceAt (-2) (fun i => even (-i)) z) (-18)) 18 0 =
      !evo (spliceAt (-2) (fun i => even (-i)) z) 18 0 := hy
  rw [← hs, hy', h4, hx]
  rfl

/-! ## Every cut, and the width -/

/-- **The left cut** (`3 ≤ t ≤ 17`). Two rows that differ somewhere on cells `-t .. -3` have a common completion
from cell `-2` on that gives them different centers after `t` steps. -/
theorem left_cut (t : Nat) (h3 : 3 ≤ t) (hT : t ≤ 17) (x y : Int → Bool) (i : Int) (hi1 : -(t : Int) ≤ i)
    (hi2 : i ≤ -3) (hne : x i ≠ y i) :
    ∃ z : Int → Bool, evo (spliceAt (-2) x z) t 0 ≠ evo (spliceAt (-2) y z) t 0 := by
  have hc : cutCheck t (cutCertList t) = true := by
    rcases (show t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 ∨ t = 8 ∨ t = 9 ∨ t = 10 ∨ t = 11 ∨ t = 12 ∨ t = 13 ∨ t = 14 ∨ t = 15 ∨ t = 16 ∨ t = 17 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact cutCert3_check
    · exact cutCert4_check
    · exact cutCert5_check
    · exact cutCert6_check
    · exact cutCert7_check
    · exact cutCert8_check
    · exact cutCert9_check
    · exact cutCert10_check
    · exact cutCert11_check
    · exact cutCert12_check
    · exact cutCert13_check
    · exact cutCert14_check
    · exact cutCert15_check
    · exact cutCert16_check
    · exact cutCert17_check
  exact left_cut_of_check t h3 (cutCertList t) hc x y i hi1 hi2 hne

/-- **Every cut left of `-2`** (`3 ≤ t ≤ 17`, `-t < a ≤ -2`). Two rows that differ somewhere on cells `-t .. a - 1`
have a common completion from cell `a` on that gives them different centers after `t` steps. -/
theorem left_cut_at (t : Nat) (h3 : 3 ≤ t) (hT : t ≤ 17) (a : Int) (ha : a ≤ -2) (x y : Int → Bool) (i : Int)
    (hi1 : -(t : Int) ≤ i) (hi2 : i < a) (hne : x i ≠ y i) :
    ∃ z : Int → Bool, evo (spliceAt a x z) t 0 ≠ evo (spliceAt a y z) t 0 := by
  obtain ⟨z, hz⟩ := left_cut t h3 hT x (spliceAt a y x) i hi1 (by omega) (by simp [spliceAt, hi2, hne])
  refine ⟨spliceAt (-2) x z, ?_⟩
  have ex : spliceAt a x (spliceAt (-2) x z) = spliceAt (-2) x z := by
    funext j
    simp only [spliceAt]
    by_cases h1 : j < a
    · rw [ite_eq_left h1, ite_eq_left (by omega)]
    · rw [ite_eq_right h1]
  have ey : spliceAt a y (spliceAt (-2) x z) = spliceAt (-2) (spliceAt a y x) z := by
    funext j
    simp only [spliceAt]
    by_cases h1 : j < a
    · rw [ite_eq_left h1, ite_eq_left (by omega), ite_eq_left h1]
    · rw [ite_eq_right h1]
      by_cases h2 : j < -2
      · rw [ite_eq_left h2, ite_eq_left h2, ite_eq_right h1]
      · rw [ite_eq_right h2, ite_eq_right h2]
  rw [ex, ey]
  exact hz

/-- **States at a cut.** If the center after `t` steps is computed as `G (F x) z` from a state `F x` of the cells left
of `a` and the cells `z` from `a` on, then rows with the same state agree on cells `-t .. a - 1`. -/
theorem left_cut_factor (t : Nat) (h3 : 3 ≤ t) (hT : t ≤ 17) (a : Int) (ha : a ≤ -2) {S : Type}
    (F : (Int → Bool) → S) (G : S → (Int → Bool) → Bool)
    (hFG : ∀ x z : Int → Bool, evo (spliceAt a x z) t 0 = G (F x) z)
    (x y : Int → Bool) (hxy : F x = F y) : ∀ i : Int, -(t : Int) ≤ i → i < a → x i = y i := by
  intro i hi1 hi2
  apply Classical.byContradiction
  intro hne
  obtain ⟨z, hz⟩ := left_cut_at t h3 hT a ha x y i hi1 hi2 hne
  rw [hFG, hFG, hxy] at hz
  exact hz rfl

/-- **The width at a cut** (`3 ≤ t ≤ 17`, `0 ≤ k ≤ t - 2`). Every such factorization at the cut after the `k`
leftmost cells of the cone has at least `2 ^ k` states: the rows with the bits of `P < 2 ^ k` on cells `-t .. -t + k - 1`
have pairwise different states. -/
theorem left_cut_width (t k : Nat) (h3 : 3 ≤ t) (hT : t ≤ 17) (hk : k + 2 ≤ t) {S : Type}
    (F : (Int → Bool) → S) (G : S → (Int → Bool) → Bool)
    (hFG : ∀ x z : Int → Bool, evo (spliceAt (-(t : Int) + k) x z) t 0 = G (F x) z) :
    ∀ P Q : Nat, P < 2 ^ k → Q < 2 ^ k → F (rowN P (-(t : Int))) = F (rowN Q (-(t : Int))) → P = Q := by
  intro P Q hP hQ hPQ
  have hagree := left_cut_factor t h3 hT (-(t : Int) + k) (by omega) F G hFG _ _ hPQ
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < k
  · have := hagree (-(t : Int) + j) (by omega) (by omega)
    simp only [rowN] at this
    rw [ite_eq_left (by omega), ite_eq_left (by omega), show (-(t : Int) + j - -(t : Int)).toNat = j by omega] at this
    exact this
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hP (Nat.pow_le_pow_right (by omega) (by omega))),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hQ (Nat.pow_le_pow_right (by omega) (by omega)))]

end Rule30Open
