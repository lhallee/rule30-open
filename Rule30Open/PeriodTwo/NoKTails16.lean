module

public import Rule30Open.PeriodTwo.NoKTails

/-!
# No head of up to 16 cells on a background of the tail census besides the stripes and the ether is in `K`

A background is a cycle of `P` states of the held map on a ring of `L` cells (`ringCell`, a cycle by `ringCell_step`
of `NoKTails`), laid on the cells `j ≥ 0` of a half at an alignment `(a, o)`: cell `j` is ring cell `j + o` of state
`a`. For each of the 12 backgrounds of the tail census reached by a periodic tail of up to 12 cells, other than the
stripes and the ether (the vacuum and 11 backgrounds that carry fronts), no point of `K` (`InK`) has the background from
a cell `p ≤ 16` on, at any alignment (`no_k_tail16_L1P1` to `no_k_tail16_L12P102`).

* **The tree of `K`.** Bit 0 of `heldOrbit u d` is `u d` xor a function of the cells below `d`
  (`column_triangular`), so at an odd step `d` exactly one value of cell `d` keeps it odd, whatever the cells above `d`
  are. `treeRun R 16 0 W` walks the heads of 16 cells under the tail word `W`: both values at an even cell, the one
  value at an odd cell `d` that makes bit 0 of `heldNat^d` odd (`colRaw`), and at each of the 2^8 leaves the checker
  `breakRun R` of `NoKTails`, which must find an odd step `2 s + 1 < 2 R` at which bit 0 is 0. A head off the tree
  breaks `K` at the odd cell where it leaves it, so the walk is sound for every head (`treeWith_sound`,
  `treeRun_sound`).
* **Tables.** The alignments share 1,151 distinct tail words over the 12 backgrounds, kept in chunks of at most 32.
  `tabOK` checks, by the recursors of the lists, that the entry of each alignment names a word that holds the
  background on the cells `16, …, 63` and 0 below (`tailEntryOK`, `wordOK`), and `wordsOK` runs the tree on every word of
  a chunk as one kernel computation, with `R = 24` rounds (the odd steps up to 47).
* **The theorem.** `not_inK_of_tree` reduces the alignment modulo `(P, L)`, finds its word, and applies the tree to the
  number that holds the background on the cells `16, …, 63` and 0 below.

The natural-language argument is `NoKTails16.md`, beside this file.
-/

@[expose] public section

-- Sequential elaboration: the kernel checks would otherwise run in parallel and stack their memory.
set_option Elab.async false

namespace Rule30Open

/-! ### The forced cells of `K` -/

/-- Bit 0 of `heldNat^d n`, with the raw operations: each step evaluated once by the kernel. -/
def colRaw (d : Nat) : Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun m => Nat.beq (Nat.mod m 2) 1) (fun _ ih m => letN (heldRaw m) ih) d

theorem repeat_shift_nk (f : Nat → Nat) : ∀ n a, Nat.repeat f n (f a) = Nat.repeat f (n + 1) a := by
  intro n
  induction n with
  | zero => intro a; rfl
  | succ n ih => intro a; show f (Nat.repeat f n (f a)) = f (Nat.repeat f (n + 1) a); rw [ih]

theorem colRaw_eq : ∀ d n, colRaw d n = (Nat.repeat heldNat d n).testBit 0 := by
  intro d
  induction d with
  | zero =>
    intro n
    show Nat.beq (n % 2) 1 = n.testBit 0
    rw [Nat.testBit_zero]
    rcases Nat.mod_two_eq_zero_or_one n with h | h <;> rw [h] <;> rfl
  | succ d ih =>
    intro n
    show letN (heldRaw n) (colRaw d) = _
    rw [letN_eq, ih, heldRaw_eq, repeat_shift_nk]

/-- The tree of the heads of `K` with the leaf test `leaf`: from cell `d` with `m` cells of the head left, the cells
`d, …` of `n` still 0 below the tail. At an even cell both values are tried; at an odd cell `d` only the value that
makes bit 0 of `heldNat^d` odd, since the other breaks `K` at step `d`. With no cell left, `leaf` must accept the
number. -/
def treeWith (leaf : Nat → Bool) (m : Nat) : Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ n => leaf n)
    (fun _ ih d n => cond (Nat.beq (Nat.mod d 2) 0)
      (ih (Nat.add d 1) n && ih (Nat.add d 1) (Nat.lor n (Nat.pow 2 d)))
      (cond (colRaw d n) (ih (Nat.add d 1) n) (ih (Nat.add d 1) (Nat.lor n (Nat.pow 2 d))))) m

theorem treeWith_succ (leaf : Nat → Bool) (m d n : Nat) : treeWith leaf (m + 1) d n =
    cond (Nat.beq (d % 2) 0) (treeWith leaf m (d + 1) n && treeWith leaf m (d + 1) (n ||| 2 ^ d))
      (cond (colRaw d n) (treeWith leaf m (d + 1) n) (treeWith leaf m (d + 1) (n ||| 2 ^ d))) := rfl

/-- The tree with `breakRun R` at the leaves: every leaf must break `K` within `R` rounds. -/
def treeRun (R m : Nat) : Nat → Nat → Bool := treeWith (breakRun R) m

/-- A run of `breakRun` on a number that holds the cells `0, …, 63` of `u` breaks `u`. -/
theorem not_inK_of_breakRun (R N : Nat) (hR : 2 * R ≤ 64) (u : Nat → Bool)
    (hN : ∀ i, i < 64 → N.testBit i = u i) (hb : breakRun R N = true) : ¬ InK u := by
  intro hK
  obtain ⟨s, hs, hz⟩ := breakRun_start N R hb
  have hcol := heldNat_repeat_testBit N (2 * s + 1) 0
  rw [Nat.testBit_zero, hz] at hcol
  have hagree := column_eq_of_agree (2 * s + 1) u (fun i => N.testBit i) (fun i hi => (hN i (by omega)).symm)
  have hone : heldOrbit (fun i => N.testBit i) (2 * s + 1) 0 = true := hagree.symm.trans (hK s)
  rw [hone] at hcol
  exact absurd hcol (by decide)

theorem testBit_lor_two_pow (n d i : Nat) : (n ||| 2 ^ d).testBit i = (n.testBit i || decide (d = i)) := by
  rw [Nat.testBit_or, Nat.testBit_two_pow]

private theorem flip_alg (a b c : Bool) (h : xor a false = xor c true) (ha : a = false) : c = true := by
  revert a b c; decide

private theorem break_alg (x y z : Bool) (h : xor x y = xor true z) (hyz : y ≠ z) : x = false := by
  revert x y z; decide

/-- **The tree is sound**: let `Q` hold for every point of `K` that agrees on the cells `0, …, 63` with a number that
`leaf` accepts. If `treeWith leaf m d n` succeeds, with `d + m = H ≤ 64`, `n` equal to `u` on the cells below `d`
and on the cells `H, …, 63`, and 0 on the cells `d, …, H - 1`, then `Q` holds if `u` is in `K`. -/
theorem treeWith_sound (leaf : Nat → Bool) (H : Nat) (hH : H ≤ 64) (u : Nat → Bool) (Q : Prop)
    (hleaf : ∀ n, leaf n = true → (∀ i, i < 64 → n.testBit i = u i) → InK u → Q) : ∀ m d n, d + m = H →
    treeWith leaf m d n = true → (∀ i, i < 64 → (i < d ∨ H ≤ i) → n.testBit i = u i) →
    (∀ i, d ≤ i → i < H → n.testBit i = false) → InK u → Q := by
  intro m
  induction m with
  | zero =>
    intro d n hd h hag _
    exact hleaf n h (fun i hi => hag i hi (by omega))
  | succ m ih =>
    intro d n hd h hag hz
    rw [treeWith_succ] at h
    have hset : ∀ i, (n ||| 2 ^ d).testBit i = (n.testBit i || decide (d = i)) := testBit_lor_two_pow n d
    have hd' : d + 1 + m = H := by omega
    -- the step from a value `n'` of cell `d` that differs from `n` at `d` at most
    have step : ∀ n', (∀ i, i ≠ d → n'.testBit i = n.testBit i) → u d = n'.testBit d →
        treeWith leaf m (d + 1) n' = true → InK u → Q := by
      intro n' hsame hud hrun
      refine ih (d + 1) n' hd' hrun (fun i hi hor => ?_) (fun i h1 h2 => ?_)
      · rcases hor with hor | hor
        · rcases Nat.lt_succ_iff_lt_or_eq.mp hor with hor | rfl
          · rw [hsame i (by omega)]; exact hag i hi (Or.inl hor)
          · exact hud.symm
        · rw [hsame i (by omega)]; exact hag i hi (Or.inr hor)
      · rw [hsame i (by omega)]; exact hz i (by omega) h2
    have same_keep : ∀ i, i ≠ d → n.testBit i = n.testBit i := fun _ _ => rfl
    have same_set : ∀ i, i ≠ d → (n ||| 2 ^ d).testBit i = n.testBit i := by
      intro i hi; rw [hset]; simp [show d ≠ i from fun e => hi e.symm]
    have hn_d : n.testBit d = false := hz d (Nat.le_refl d) (by omega)
    have hset_d : (n ||| 2 ^ d).testBit d = true := by rw [hset]; simp
    by_cases he : d % 2 = 0
    · rw [show Nat.beq (d % 2) 0 = true from Nat.beq_eq_true_eq _ _ ▸ he, Bool.cond_true,
        Bool.and_eq_true_iff] at h
      cases hu : u d with
      | false => exact step n same_keep (hu.trans hn_d.symm) h.1
      | true => exact step (n ||| 2 ^ d) same_set (hu.trans hset_d.symm) h.2
    · rw [show Nat.beq (d % 2) 0 = false from by
        cases hb : Nat.beq (d % 2) 0
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true hb) he, Bool.cond_false] at h
      have hodd : d % 2 = 1 := by omega
      -- a value `n'` of cell `d` whose bit 0 at step `d` is odd: `u` either takes it or breaks `K` at step `d`
      have odd_step : ∀ n', (∀ i, i ≠ d → n'.testBit i = n.testBit i) →
          (Nat.repeat heldNat d n').testBit 0 = true → treeWith leaf m (d + 1) n' = true → InK u → Q := by
        intro n' hsame hcol hrun hK
        by_cases hud : u d = n'.testBit d
        · exact step n' hsame hud hrun hK
        · have key := column_triangular d u (fun i => n'.testBit i) (fun i hi => by
            show u i = n'.testBit i
            rw [hsame i (by omega)]; exact (hag i (by omega) (Or.inl hi)).symm)
          have hc : column (fun i => n'.testBit i) d = true := by
            unfold column; rw [← heldNat_repeat_testBit]; exact hcol
          rw [hc] at key
          have h0 := break_alg _ _ _ key hud
          have h1 := hK (d / 2)
          rw [show 2 * (d / 2) + 1 = d by omega] at h1
          unfold column at h0
          rw [h0] at h1
          exact absurd h1 (by decide)
      cases hc : colRaw d n with
      | true =>
        rw [hc, Bool.cond_true] at h
        rw [colRaw_eq] at hc
        exact odd_step n same_keep hc h
      | false =>
        rw [hc, Bool.cond_false] at h
        rw [colRaw_eq] at hc
        have hmod : n % 2 ^ d = (n ||| 2 ^ d) % 2 ^ d := by
          apply Nat.eq_of_testBit_eq
          intro i
          rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow, hset]
          by_cases hi : i < d
          · simp [hi, show d ≠ i by omega]
          · simp [hi]
        have hflip := heldNat_triangular d n (n ||| 2 ^ d) hmod
        rw [hn_d, hc, hset_d] at hflip
        exact odd_step (n ||| 2 ^ d) same_set (flip_alg _ false _ hflip rfl) h

/-- **The tree with `breakRun` at the leaves is sound**: if `treeRun R m d n` succeeds, with `2 R ≤ 64`, `d + m = 16`,
`n` equal to `u` on the cells below `d` and on the cells `16, …, 63`, and 0 on the cells `d, …, 15`, then `u` is not
in `K`. -/
theorem treeRun_sound (R : Nat) (hR : 2 * R ≤ 64) (u : Nat → Bool) (m d n : Nat) (hd : d + m = 16)
    (h : treeRun R m d n = true) (hag : ∀ i, i < 64 → (i < d ∨ 16 ≤ i) → n.testBit i = u i)
    (hz : ∀ i, d ≤ i → i < 16 → n.testBit i = false) : ¬ InK u :=
  treeWith_sound (breakRun R) 16 (by decide) u False (fun n hb hn hK => not_inK_of_breakRun R n hR u hn hb hK)
    m d n hd h hag hz

/-! ### The tables -/

/-- The check of one tail word `W` against the state `s` of a background on a ring of `L` cells, read from cell `o`:
the cells `0, …, 15` of `W` are 0, and cell `16 + i` of `W` is ring cell `16 + i + o` of `s`, for `i < 48`. -/
def wordOK (s L o W : Nat) : Bool :=
  Nat.beq (Nat.mod W 65536) 0 &&
    allBelow (fun i => Bool.beq (Nat.testBit W (Nat.add i 16))
      (Nat.testBit s (Nat.mod (Nat.add (Nat.add i 16) o) L))) 48

private theorem beq_alg (x y : Bool) (h : Bool.beq x y = true) : x = y := by
  revert x y; decide

theorem wordOK_spec (s L o W : Nat) (h : wordOK s L o W = true) :
    (∀ i, i < 16 → W.testBit i = false) ∧
      ∀ j, 16 ≤ j → j < 64 → W.testBit j = s.testBit ((j + o) % L) := by
  unfold wordOK at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h0, h1⟩ := h
  refine ⟨fun i hi => ?_, fun j hj1 hj2 => ?_⟩
  · have hz : W % 2 ^ 16 = 0 := Nat.eq_of_beq_eq_true h0
    have := Nat.testBit_mod_two_pow W 16 i
    rw [hz, Nat.zero_testBit, decide_eq_true hi, Bool.true_and] at this
    exact this.symm
  · have := beq_alg _ _ (allBelow_spec _ _ h1 (j - 16) (by omega))
    simp only [Nat.add_eq, show j - 16 + 16 = j by omega] at this
    exact this

/-- The words of a background are kept in chunks of at most 32: entry `e` is word `e % 32` of chunk `e / 32`. The
check of the entry `e` at the offset `o` of the state `s`: the chunk is one of the `nc` checked, the word exists, and it
holds the background (`wordOK`). -/
def tailEntryOK (s L nc : Nat) (ws : List (List Nat)) (o e : Nat) : Bool :=
  Nat.blt (e / 32) nc && Nat.blt (e % 32) (ws.getD (e / 32) []).length &&
    wordOK s L o ((ws.getD (e / 32) []).getD (e % 32) 0)

/-- The check of a row of entries, the offsets `o, o + 1, …`, by the recursor of the list. -/
noncomputable def rowOK (s L nc : Nat) (ws : List (List Nat)) (row : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun e _ ih o => tailEntryOK s L nc ws o e && ih (Nat.add o 1)) row

/-- The check of the tables: row `a` of `rows` has `L` entries, and entry `o` of it passes `tailEntryOK` against state `a`
of `st` at the offset `o`, by the recursor of the list of states. -/
noncomputable def tabOK (L nc : Nat) (ws : List (List Nat)) (st : List Nat) : List (List Nat) → Bool :=
  List.rec (motive := fun _ => List (List Nat) → Bool) (fun _ => true)
    (fun s _ ih rows => List.rec (motive := fun _ => Bool) false
      (fun row rest _ => Nat.beq row.length L && rowOK s L nc ws row 0 && ih rest) rows) st

theorem rowOK_spec (s L nc : Nat) (ws : List (List Nat)) :
    ∀ (row : List Nat) (o0 : Nat), rowOK s L nc ws row o0 = true →
      ∀ i, i < row.length → tailEntryOK s L nc ws (o0 + i) (row.getD i 0) = true := by
  intro row
  induction row with
  | nil => intro _ _ i hi; exact absurd hi (Nat.not_lt_zero i)
  | cons e es ih =>
    intro o0 h i hi
    have h' : (tailEntryOK s L nc ws o0 e && rowOK s L nc ws es (o0 + 1)) = true := h
    rw [Bool.and_eq_true] at h'
    cases i with
    | zero => rw [Nat.add_zero]; exact h'.1
    | succ i =>
      have := ih (o0 + 1) h'.2 i (by simp at hi; omega)
      rw [show o0 + (i + 1) = o0 + 1 + i by omega]
      exact this

theorem tabOK_spec (L nc : Nat) (ws : List (List Nat)) : ∀ (st : List Nat) (rows : List (List Nat)),
    tabOK L nc ws st rows = true → ∀ a, a < st.length → ∀ o, o < L →
      tailEntryOK (st.getD a 0) L nc ws o ((rows.getD a []).getD o 0) = true := by
  intro st
  induction st with
  | nil => intro _ _ a ha; exact absurd ha (Nat.not_lt_zero a)
  | cons s ss ih =>
    intro rows h a ha o ho
    cases rows with
    | nil => exact absurd h Bool.false_ne_true
    | cons row rest =>
      have h' : (Nat.beq row.length L && rowOK s L nc ws row 0 && tabOK L nc ws ss rest) = true := h
      simp only [Bool.and_eq_true] at h'
      obtain ⟨⟨hlen, hrow⟩, htl⟩ := h'
      cases a with
      | zero =>
        have hl : row.length = L := Nat.eq_of_beq_eq_true hlen
        have := rowOK_spec s L nc ws row 0 hrow o (by omega)
        rw [Nat.zero_add] at this
        exact this
      | succ a => exact ih rest htl a (by simp at ha; omega) o ho

/-- The tree of every word of the chunk `cw` succeeds with `R` rounds at its leaves, as one kernel computation. -/
def wordsOK (R : Nat) (cw : List Nat) : Bool := allBelow (fun i => treeRun R 16 0 (cw.getD i 0)) cw.length

/-- **The tables exclude the background**: if the tables of the states `st` pass `tabOK` and every chunk of words passes
`wordsOK` with `R` rounds, `2 R ≤ 64`, then no point of `K` has the background from a cell `p ≤ 16` on, at any
alignment `(a, o)`. -/
theorem not_inK_of_tree (st : List Nat) (L P R : Nat) (ws : List (List Nat)) (rows : List (List Nat)) (nc : Nat)
    (hR : 2 * R ≤ 64) (hP : st.length = P) (hP0 : 0 < P) (hL0 : 0 < L) (htab : tabOK L nc ws st rows = true)
    (hw : ∀ c, c < nc → wordsOK R (ws.getD c []) = true)
    (u : Nat → Bool) (a o p : Nat) (hp : p ≤ 16)
    (hu : ∀ j, p ≤ j → u j = ringCell st L a (j + o)) : ¬ InK u := by
  have ha : a % P < P := Nat.mod_lt _ hP0
  have ho : o % L < L := Nat.mod_lt _ hL0
  -- the alignment, reduced modulo `(P, L)`
  have hu' : ∀ j, p ≤ j → u j = (st.getD (a % P) 0).testBit ((j + o % L) % L) := by
    intro j hj
    rw [hu j hj]
    unfold ringCell
    rw [hP, Nat.add_mod_mod]
  -- its entry and its word
  have he := tabOK_spec L nc ws st rows htab (a % P) (by omega) (o % L) ho
  unfold tailEntryOK at he
  simp only [Bool.and_eq_true] at he
  obtain ⟨⟨hc, hpos⟩, hword⟩ := he
  obtain ⟨hlow, hhigh⟩ := wordOK_spec _ _ _ _ hword
  have ht := allBelow_spec _ _ (hw _ (Nat.le_of_ble_eq_true hc)) _ (Nat.le_of_ble_eq_true hpos)
  refine treeRun_sound R hR u 16 0 _ rfl ht (fun i hi hor => ?_) (fun i _ hi => hlow i hi)
  rcases hor with hor | hor
  · omega
  · rw [hhigh i hor hi, hu' i (by omega)]

/-! ### The background `0`: `L = 1`, `P = 1` -/

/-- The 1 states of the background `0` on a ring of 1 cells, bit `j` the ring cell `j`. -/
def statesL1P1 : List Nat := [0]

theorem statesL1P1_cycle : ringStepOK statesL1P1 1 = true := by
  decide +kernel

/-- Chunk 0 of the 1 distinct tail words of the background, cells 16 to 63 in place. -/
def wordsL1P1_0 : List Nat := [0]

/-- The chunks of tail words. -/
def wordsL1P1 : List (List Nat) := [wordsL1P1_0]

/-- Row `a`, entry `o`: the index of the tail word at the alignment `(a, o)`. -/
def rowsL1P1 : List (List Nat) := [[0]]

theorem tablesL1P1_ok : tabOK 1 1 wordsL1P1 statesL1P1 rowsL1P1 = true := by
  decide +kernel

theorem ktreeL1P1_0 : wordsOK 24 wordsL1P1_0 = true := by
  decide +kernel

theorem ktreeL1P1 (c : Nat) (hc : c < 1) : wordsOK 24 (wordsL1P1.getD c []) = true :=
  match c, hc with
  | 0, _ => ktreeL1P1_0
  | c + 1, hc => absurd hc (by omega)

/-- **No point of `K` has the background `0` from a cell `p ≤ 16` on**, at any alignment `(a, o)`. -/
theorem no_k_tail16_L1P1 (u : Nat → Bool) (a o p : Nat) (hp : p ≤ 16)
    (hu : ∀ j, p ≤ j → u j = ringCell statesL1P1 1 a (j + o)) : ¬ InK u :=
  not_inK_of_tree statesL1P1 1 1 24 wordsL1P1 rowsL1P1 1 (by decide) (by decide +kernel)
    (by decide) (by decide) tablesL1P1_ok ktreeL1P1 u a o p hp hu

/-! ### The background `1000`: `L = 4`, `P = 8` -/

/-- The 8 states of the background `1000` on a ring of 4 cells, bit `j` the ring cell `j`. -/
def statesL4P8 : List Nat := [1, 11, 2, 7, 4, 14, 8, 13]

theorem statesL4P8_cycle : ringStepOK statesL4P8 4 = true := by
  decide +kernel

/-- Chunk 0 of the 8 distinct tail words of the background, cells 16 to 63 in place. -/
def wordsL4P8_0 : List Nat := [1229782938247299072, 9838263505978392576, 4919131752989196288, 2459565876494598144, 13527612320720289792, 15987178197214887936, 17216961135462187008, 8608480567731093504]

/-- The chunks of tail words. -/
def wordsL4P8 : List (List Nat) := [wordsL4P8_0]

/-- Row `a`, entry `o`: the index of the tail word at the alignment `(a, o)`. -/
def rowsL4P8 : List (List Nat) := [[0, 1, 2, 3], [4, 5, 6, 7], [3, 0, 1, 2], [7, 4, 5, 6], [2, 3, 0, 1], [6, 7, 4, 5], [1, 2, 3, 0], [5, 6, 7, 4]]

theorem tablesL4P8_ok : tabOK 4 1 wordsL4P8 statesL4P8 rowsL4P8 = true := by
  decide +kernel

theorem ktreeL4P8_0 : wordsOK 24 wordsL4P8_0 = true := by
  decide +kernel

theorem ktreeL4P8 (c : Nat) (hc : c < 1) : wordsOK 24 (wordsL4P8.getD c []) = true :=
  match c, hc with
  | 0, _ => ktreeL4P8_0
  | c + 1, hc => absurd hc (by omega)

/-- **No point of `K` has the background `1000` from a cell `p ≤ 16` on**, at any alignment `(a, o)`. -/
theorem no_k_tail16_L4P8 (u : Nat → Bool) (a o p : Nat) (hp : p ≤ 16)
    (hu : ∀ j, p ≤ j → u j = ringCell statesL4P8 4 a (j + o)) : ¬ InK u :=
  not_inK_of_tree statesL4P8 4 8 24 wordsL4P8 rowsL4P8 1 (by decide) (by decide +kernel)
    (by decide) (by decide) tablesL4P8_ok ktreeL4P8 u a o p hp hu

/-! ### The background `11100`: `L = 5`, `P = 5` -/

/-- The 5 states of the background `11100` on a ring of 5 cells, bit `j` the ring cell `j`. -/
def statesL5P5 : List Nat := [7, 28, 19, 14, 25]

theorem statesL5P5_cycle : ringStepOK statesL5P5 5 = true := by
  decide +kernel

/-- Chunk 0 of the 5 distinct tail words of the background, cells 16 to 63 in place. -/
def wordsL5P5_0 : List Nat := [8330787646191370240, 4165393823095652352, 11306068948402569216, 14876406511056060416, 16661575292382806016]

/-- The chunks of tail words. -/
def wordsL5P5 : List (List Nat) := [wordsL5P5_0]

/-- Row `a`, entry `o`: the index of the tail word at the alignment `(a, o)`. -/
def rowsL5P5 : List (List Nat) := [[0, 1, 2, 3, 4], [3, 4, 0, 1, 2], [1, 2, 3, 4, 0], [4, 0, 1, 2, 3], [2, 3, 4, 0, 1]]

theorem tablesL5P5_ok : tabOK 5 1 wordsL5P5 statesL5P5 rowsL5P5 = true := by
  decide +kernel

theorem ktreeL5P5_0 : wordsOK 24 wordsL5P5_0 = true := by
  decide +kernel

theorem ktreeL5P5 (c : Nat) (hc : c < 1) : wordsOK 24 (wordsL5P5.getD c []) = true :=
  match c, hc with
  | 0, _ => ktreeL5P5_0
  | c + 1, hc => absurd hc (by omega)

/-- **No point of `K` has the background `11100` from a cell `p ≤ 16` on**, at any alignment `(a, o)`. -/
theorem no_k_tail16_L5P5 (u : Nat → Bool) (a o p : Nat) (hp : p ≤ 16)
    (hu : ∀ j, p ≤ j → u j = ringCell statesL5P5 5 a (j + o)) : ¬ InK u :=
  not_inK_of_tree statesL5P5 5 5 24 wordsL5P5 rowsL5P5 1 (by decide) (by decide +kernel)
    (by decide) (by decide) tablesL5P5_ok ktreeL5P5 u a o p hp hu

/-! ### The background `1010000`: `L = 7`, `P = 63` -/

/-- The 63 states of the background `1010000` on a ring of 7 cells, bit `j` the ring cell `j`. -/
def statesL7P63 : List Nat := [5, 77, 57, 39, 60, 98, 86, 84, 87, 20, 54, 101, 29, 113, 11, 90, 82, 94, 80, 89, 23, 116, 71, 44, 106, 74, 122, 66, 102, 92, 83, 30, 49, 43, 42, 107, 10, 27, 114, 78, 120, 69, 45, 41, 47, 40, 108, 75, 58, 99, 22, 53, 37, 61, 33, 51, 46, 105, 15, 88, 85, 21, 117]

theorem statesL7P63_cycle : ringStepOK statesL7P63 7 = true := by
  decide +kernel

/-- Chunk 0 of the 63 distinct tail words of the background, cells 16 to 63 in place. -/
def wordsL7P63_0 : List Nat := [9586496920195497984, 4793248460097716224, 11619996266903633920, 5809998133451816960, 2904999066725908480, 1452499533362954240, 726249766681444352, 14815495240302133248, 7407747620151033856, 12927245846930259968, 15686994960319905792, 7843497480159952896, 3921748740079943680, 11184246406894714880, 13362995706939179008, 6681497853469589504, 3340748926734761984, 10893746500222124032, 14670245286965805056, 16558494680337678336, 8279247340168806400, 12055746126912487424, 15251245100310986752, 16848994587010269184, 8424497293505134592, 4212248646752534528, 11329496360231043072, 5664748180115488768, 4357498600088862720, 2178749300044398592, 10312746686876942336, 14379745380293214208]

/-- Chunk 1 of the 63 distinct tail words of the background, cells 16 to 63 in place. -/
def wordsL7P63_1 : List Nat := [16413244727001350144, 17429994400355450880, 8714997200177725440, 7117247713478443008, 12781995893593997312, 6390997946796998656, 3195498973398499328, 1597749486699216896, 10022246780204351488, 14234495426956951552, 6245747993460670464, 12346246033585078272, 15396495053647314944, 7698247526823624704, 13072495800266588160, 6536247900133261312, 12491495986921406464, 6100498040124407808, 3050249020062171136, 10748496546885861376, 5374248273442897920, 11910496173576224768, 5955248086788079616, 12200996080248815616, 15541745006983577600, 16994244540346531840, 17720494307028041728, 8860247153513988096, 13653495613611769856, 6826747806805852160, 12636745940257669120]

/-- The chunks of tail words. -/
def wordsL7P63 : List (List Nat) := [wordsL7P63_0, wordsL7P63_1]

/-- Row `a`, entry `o`: the index of the tail word at the alignment `(a, o)`. -/
def rowsL7P63 : List (List Nat) := [[0, 1, 2, 3, 4, 5, 6], [7, 8, 9, 10, 11, 12, 13], [14, 15, 16, 17, 18, 19, 20], [21, 22, 23, 24, 25, 26, 27], [28, 29, 30, 31, 32, 33, 34], [35, 36, 37, 38, 39, 40, 41], [42, 43, 44, 45, 46, 47, 48], [49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62], [5, 6, 0, 1, 2, 3, 4], [12, 13, 7, 8, 9, 10, 11], [19, 20, 14, 15, 16, 17, 18], [26, 27, 21, 22, 23, 24, 25], [33, 34, 28, 29, 30, 31, 32], [40, 41, 35, 36, 37, 38, 39], [47, 48, 42, 43, 44, 45, 46], [54, 55, 49, 50, 51, 52, 53], [61, 62, 56, 57, 58, 59, 60], [3, 4, 5, 6, 0, 1, 2], [10, 11, 12, 13, 7, 8, 9], [17, 18, 19, 20, 14, 15, 16], [24, 25, 26, 27, 21, 22, 23], [31, 32, 33, 34, 28, 29, 30], [38, 39, 40, 41, 35, 36, 37], [45, 46, 47, 48, 42, 43, 44], [52, 53, 54, 55, 49, 50, 51], [59, 60, 61, 62, 56, 57, 58], [1, 2, 3, 4, 5, 6, 0], [8, 9, 10, 11, 12, 13, 7], [15, 16, 17, 18, 19, 20, 14], [22, 23, 24, 25, 26, 27, 21], [29, 30, 31, 32, 33, 34, 28], [36, 37, 38, 39, 40, 41, 35], [43, 44, 45, 46, 47, 48, 42], [50, 51, 52, 53, 54, 55, 49], [57, 58, 59, 60, 61, 62, 56], [6, 0, 1, 2, 3, 4, 5], [13, 7, 8, 9, 10, 11, 12], [20, 14, 15, 16, 17, 18, 19], [27, 21, 22, 23, 24, 25, 26], [34, 28, 29, 30, 31, 32, 33], [41, 35, 36, 37, 38, 39, 40], [48, 42, 43, 44, 45, 46, 47], [55, 49, 50, 51, 52, 53, 54], [62, 56, 57, 58, 59, 60, 61], [4, 5, 6, 0, 1, 2, 3], [11, 12, 13, 7, 8, 9, 10], [18, 19, 20, 14, 15, 16, 17], [25, 26, 27, 21, 22, 23, 24], [32, 33, 34, 28, 29, 30, 31], [39, 40, 41, 35, 36, 37, 38], [46, 47, 48, 42, 43, 44, 45], [53, 54, 55, 49, 50, 51, 52], [60, 61, 62, 56, 57, 58, 59], [2, 3, 4, 5, 6, 0, 1], [9, 10, 11, 12, 13, 7, 8], [16, 17, 18, 19, 20, 14, 15], [23, 24, 25, 26, 27, 21, 22], [30, 31, 32, 33, 34, 28, 29], [37, 38, 39, 40, 41, 35, 36], [44, 45, 46, 47, 48, 42, 43], [51, 52, 53, 54, 55, 49, 50], [58, 59, 60, 61, 62, 56, 57]]

theorem tablesL7P63_ok : tabOK 7 2 wordsL7P63 statesL7P63 rowsL7P63 = true := by
  decide +kernel

theorem ktreeL7P63_0 : wordsOK 24 wordsL7P63_0 = true := by
  decide +kernel

theorem ktreeL7P63_1 : wordsOK 24 wordsL7P63_1 = true := by
  decide +kernel

theorem ktreeL7P63 (c : Nat) (hc : c < 2) : wordsOK 24 (wordsL7P63.getD c []) = true :=
  match c, hc with
  | 0, _ => ktreeL7P63_0
  | 1, _ => ktreeL7P63_1
  | c + 2, hc => absurd hc (by omega)

/-- **No point of `K` has the background `1010000` from a cell `p ≤ 16` on**, at any alignment `(a, o)`. -/
theorem no_k_tail16_L7P63 (u : Nat → Bool) (a o p : Nat) (hp : p ≤ 16)
    (hu : ∀ j, p ≤ j → u j = ringCell statesL7P63 7 a (j + o)) : ¬ InK u :=
  not_inK_of_tree statesL7P63 7 63 24 wordsL7P63 rowsL7P63 2 (by decide) (by decide +kernel)
    (by decide) (by decide) tablesL7P63_ok ktreeL7P63 u a o p hp hu

/-! ### The background `11100000`: `L = 8`, `P = 40` -/

/-- The 40 states of the background `11100000` on a ring of 8 cells, bit `j` the ring cell `j`. -/
def statesL8P40 : List Nat := [7, 140, 219, 18, 63, 224, 145, 123, 66, 231, 28, 50, 111, 72, 252, 131, 70, 237, 9, 159, 112, 200, 189, 33, 243, 14, 25, 183, 36, 126, 193, 35, 246, 132, 207, 56, 100, 222, 144, 249]

theorem statesL8P40_cycle : ringStepOK statesL8P40 8 = true := by
  decide +kernel

/-- Chunk 0 of the 40 distinct tail words of the background, cells 16 to 63 in place. -/
def wordsL8P40_0 : List Nat := [506381209866534912, 9476562641788010496, 13961653357748748288, 16204198715729117184, 8102099357864558592, 4051049678932279296, 2025524839466139648, 1012762419733069824, 10127624197330698240, 5063812098665349120, 2531906049332674560, 10489325061521080320, 14468034567615283200, 7234017283807641600, 3617008641903820800, 1808504320951910400, 15842497851538735104, 17144620962624110592, 17795682518166798336, 8897841259083399168, 13672292666396442624, 16059518370052964352, 8029759185026482176, 13238251629367984128, 1302123111085375488, 651061555542687744, 9548902814626086912, 4774451407313043456, 2387225703656521728, 10416984888683003904, 5208492444341501952, 2604246222170750976]

/-- Chunk 1 of the 40 distinct tail words of the background, cells 16 to 63 in place. -/
def wordsL8P40_1 : List Nat := [4557430888798814208, 11502087481254150144, 14974415777481818112, 16710579925595652096, 17578661999652569088, 18012703036681027584, 18229723555195256832, 9114861777597628416]

/-- The chunks of tail words. -/
def wordsL8P40 : List (List Nat) := [wordsL8P40_0, wordsL8P40_1]

/-- Row `a`, entry `o`: the index of the tail word at the alignment `(a, o)`. -/
def rowsL8P40 : List (List Nat) := [[0, 1, 2, 3, 4, 5, 6, 7], [8, 9, 10, 11, 12, 13, 14, 15], [16, 17, 18, 19, 20, 21, 22, 23], [24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [3, 4, 5, 6, 7, 0, 1, 2], [11, 12, 13, 14, 15, 8, 9, 10], [19, 20, 21, 22, 23, 16, 17, 18], [27, 28, 29, 30, 31, 24, 25, 26], [35, 36, 37, 38, 39, 32, 33, 34], [6, 7, 0, 1, 2, 3, 4, 5], [14, 15, 8, 9, 10, 11, 12, 13], [22, 23, 16, 17, 18, 19, 20, 21], [30, 31, 24, 25, 26, 27, 28, 29], [38, 39, 32, 33, 34, 35, 36, 37], [1, 2, 3, 4, 5, 6, 7, 0], [9, 10, 11, 12, 13, 14, 15, 8], [17, 18, 19, 20, 21, 22, 23, 16], [25, 26, 27, 28, 29, 30, 31, 24], [33, 34, 35, 36, 37, 38, 39, 32], [4, 5, 6, 7, 0, 1, 2, 3], [12, 13, 14, 15, 8, 9, 10, 11], [20, 21, 22, 23, 16, 17, 18, 19], [28, 29, 30, 31, 24, 25, 26, 27], [36, 37, 38, 39, 32, 33, 34, 35], [7, 0, 1, 2, 3, 4, 5, 6], [15, 8, 9, 10, 11, 12, 13, 14], [23, 16, 17, 18, 19, 20, 21, 22], [31, 24, 25, 26, 27, 28, 29, 30], [39, 32, 33, 34, 35, 36, 37, 38], [2, 3, 4, 5, 6, 7, 0, 1], [10, 11, 12, 13, 14, 15, 8, 9], [18, 19, 20, 21, 22, 23, 16, 17], [26, 27, 28, 29, 30, 31, 24, 25], [34, 35, 36, 37, 38, 39, 32, 33], [5, 6, 7, 0, 1, 2, 3, 4], [13, 14, 15, 8, 9, 10, 11, 12], [21, 22, 23, 16, 17, 18, 19, 20], [29, 30, 31, 24, 25, 26, 27, 28], [37, 38, 39, 32, 33, 34, 35, 36]]

theorem tablesL8P40_ok : tabOK 8 2 wordsL8P40 statesL8P40 rowsL8P40 = true := by
  decide +kernel

theorem ktreeL8P40_0 : wordsOK 24 wordsL8P40_0 = true := by
  decide +kernel

theorem ktreeL8P40_1 : wordsOK 24 wordsL8P40_1 = true := by
  decide +kernel

theorem ktreeL8P40 (c : Nat) (hc : c < 2) : wordsOK 24 (wordsL8P40.getD c []) = true :=
  match c, hc with
  | 0, _ => ktreeL8P40_0
  | 1, _ => ktreeL8P40_1
  | c + 2, hc => absurd hc (by omega)

/-- **No point of `K` has the background `11100000` from a cell `p ≤ 16` on**, at any alignment `(a, o)`. -/
theorem no_k_tail16_L8P40 (u : Nat → Bool) (a o p : Nat) (hp : p ≤ 16)
    (hu : ∀ j, p ≤ j → u j = ringCell statesL8P40 8 a (j + o)) : ¬ InK u :=
  not_inK_of_tree statesL8P40 8 40 24 wordsL8P40 rowsL8P40 2 (by decide) (by decide +kernel)
    (by decide) (by decide) tablesL8P40_ok ktreeL8P40 u a o p hp hu

/-! ### The background `111000000`: `L = 9`, `P = 72` -/

/-- The 72 states of the background `111000000` on a ring of 9 cells, bit `j` the ring cell `j`. -/
def statesL9P72 : List Nat := [7, 268, 411, 114, 207, 184, 420, 319, 224, 400, 377, 71, 492, 267, 154, 499, 14, 25, 311, 228, 414, 368, 329, 127, 448, 289, 243, 142, 473, 23, 308, 487, 28, 50, 111, 456, 317, 225, 147, 254, 385, 67, 486, 284, 435, 46, 105, 463, 56, 100, 222, 401, 123, 450, 294, 508, 259, 134, 461, 57, 359, 92, 210, 415, 112, 200, 444, 291, 246, 389, 77, 505]

theorem statesL9P72_cycle : ringStepOK statesL9P72 9 = true := by
  decide +kernel

/-- Chunk 0 of the 72 distinct tail words of the background, cells 16 to 63 in place. -/
def wordsL9P72_0 : List Nat := [9349719599003467776, 13898231836356509696, 16172487955033030656, 8086243977516482560, 4043121988758208512, 2021560994379071488, 1010780497189535744, 505390248594767872, 252695124297383936, 4837306665121480704, 2418653332560740352, 10432698703135113216, 14439721388422332416, 7219860694211166208, 3609930347105550336, 1804965173552742400, 902482586776371200, 9674613330242961408, 16641778900156743680, 17544261486933114880, 8772130743466524672, 13609437408588005376, 16028090741148745728, 8014045370574372864, 4007022685287153664, 11226883379498319872, 14836813726603935744, 2057660297850126336, 10252202185779838976, 5126101092889919488, 2563050546444959744, 10504897310077222912]

/-- Chunk 1 of the 72 distinct tail words of the background, cells 16 to 63 in place. -/
def wordsL9P72_1 : List Nat := [14475820691893387264, 16461282382801469440, 8230641191400701952, 4115320595700318208, 12959649946109018112, 15703197009909252096, 17074970541809401856, 17760857307759443968, 8880428653879689216, 4440214326939811840, 11443479200324648960, 14945111637017100288, 7472555818508550144, 3321135919337111552, 1660567959668523008, 830283979834261504, 9638514026771906560, 14042629050240729088, 16244686561975140352, 8122343280987537408, 13284543677348511744, 6642271838674223104, 7580853728921714688, 3790426864460824576, 11118585469085155328, 5559292734542577664, 2779646367271288832, 10613195220490387456, 5306597610245193728, 11876670841977372672, 15161707457843429376, 14981210940488155136]

/-- Chunk 2 of the 72 distinct tail words of the background, cells 16 to 63 in place. -/
def wordsL9P72_2 : List Nat := [16713977507098853376, 17580360790404169728, 18013552432056827904, 18230148252883156992, 18338446163296321536, 9169223081648128000, 4584611540824031232, 11515677807266758656]

/-- The chunks of tail words. -/
def wordsL9P72 : List (List Nat) := [wordsL9P72_0, wordsL9P72_1, wordsL9P72_2]

/-- Row `a`, entry `o`: the index of the tail word at the alignment `(a, o)`. -/
def rowsL9P72 : List (List Nat) := [[0, 1, 2, 3, 4, 5, 6, 7, 8], [9, 10, 11, 12, 13, 14, 15, 16, 17], [18, 19, 20, 21, 22, 23, 24, 25, 26], [27, 28, 29, 30, 31, 32, 33, 34, 35], [36, 37, 38, 39, 40, 41, 42, 43, 44], [45, 46, 47, 48, 49, 50, 51, 52, 53], [54, 55, 56, 57, 58, 59, 60, 61, 62], [63, 64, 65, 66, 67, 68, 69, 70, 71], [4, 5, 6, 7, 8, 0, 1, 2, 3], [13, 14, 15, 16, 17, 9, 10, 11, 12], [22, 23, 24, 25, 26, 18, 19, 20, 21], [31, 32, 33, 34, 35, 27, 28, 29, 30], [40, 41, 42, 43, 44, 36, 37, 38, 39], [49, 50, 51, 52, 53, 45, 46, 47, 48], [58, 59, 60, 61, 62, 54, 55, 56, 57], [67, 68, 69, 70, 71, 63, 64, 65, 66], [8, 0, 1, 2, 3, 4, 5, 6, 7], [17, 9, 10, 11, 12, 13, 14, 15, 16], [26, 18, 19, 20, 21, 22, 23, 24, 25], [35, 27, 28, 29, 30, 31, 32, 33, 34], [44, 36, 37, 38, 39, 40, 41, 42, 43], [53, 45, 46, 47, 48, 49, 50, 51, 52], [62, 54, 55, 56, 57, 58, 59, 60, 61], [71, 63, 64, 65, 66, 67, 68, 69, 70], [3, 4, 5, 6, 7, 8, 0, 1, 2], [12, 13, 14, 15, 16, 17, 9, 10, 11], [21, 22, 23, 24, 25, 26, 18, 19, 20], [30, 31, 32, 33, 34, 35, 27, 28, 29], [39, 40, 41, 42, 43, 44, 36, 37, 38], [48, 49, 50, 51, 52, 53, 45, 46, 47], [57, 58, 59, 60, 61, 62, 54, 55, 56], [66, 67, 68, 69, 70, 71, 63, 64, 65], [7, 8, 0, 1, 2, 3, 4, 5, 6], [16, 17, 9, 10, 11, 12, 13, 14, 15], [25, 26, 18, 19, 20, 21, 22, 23, 24], [34, 35, 27, 28, 29, 30, 31, 32, 33], [43, 44, 36, 37, 38, 39, 40, 41, 42], [52, 53, 45, 46, 47, 48, 49, 50, 51], [61, 62, 54, 55, 56, 57, 58, 59, 60], [70, 71, 63, 64, 65, 66, 67, 68, 69], [2, 3, 4, 5, 6, 7, 8, 0, 1], [11, 12, 13, 14, 15, 16, 17, 9, 10], [20, 21, 22, 23, 24, 25, 26, 18, 19], [29, 30, 31, 32, 33, 34, 35, 27, 28], [38, 39, 40, 41, 42, 43, 44, 36, 37], [47, 48, 49, 50, 51, 52, 53, 45, 46], [56, 57, 58, 59, 60, 61, 62, 54, 55], [65, 66, 67, 68, 69, 70, 71, 63, 64], [6, 7, 8, 0, 1, 2, 3, 4, 5], [15, 16, 17, 9, 10, 11, 12, 13, 14], [24, 25, 26, 18, 19, 20, 21, 22, 23], [33, 34, 35, 27, 28, 29, 30, 31, 32], [42, 43, 44, 36, 37, 38, 39, 40, 41], [51, 52, 53, 45, 46, 47, 48, 49, 50], [60, 61, 62, 54, 55, 56, 57, 58, 59], [69, 70, 71, 63, 64, 65, 66, 67, 68], [1, 2, 3, 4, 5, 6, 7, 8, 0], [10, 11, 12, 13, 14, 15, 16, 17, 9], [19, 20, 21, 22, 23, 24, 25, 26, 18], [28, 29, 30, 31, 32, 33, 34, 35, 27], [37, 38, 39, 40, 41, 42, 43, 44, 36], [46, 47, 48, 49, 50, 51, 52, 53, 45], [55, 56, 57, 58, 59, 60, 61, 62, 54], [64, 65, 66, 67, 68, 69, 70, 71, 63], [5, 6, 7, 8, 0, 1, 2, 3, 4], [14, 15, 16, 17, 9, 10, 11, 12, 13], [23, 24, 25, 26, 18, 19, 20, 21, 22], [32, 33, 34, 35, 27, 28, 29, 30, 31], [41, 42, 43, 44, 36, 37, 38, 39, 40], [50, 51, 52, 53, 45, 46, 47, 48, 49], [59, 60, 61, 62, 54, 55, 56, 57, 58], [68, 69, 70, 71, 63, 64, 65, 66, 67]]

theorem tablesL9P72_ok : tabOK 9 3 wordsL9P72 statesL9P72 rowsL9P72 = true := by
  decide +kernel

theorem ktreeL9P72_0 : wordsOK 24 wordsL9P72_0 = true := by
  decide +kernel

theorem ktreeL9P72_1 : wordsOK 24 wordsL9P72_1 = true := by
  decide +kernel

theorem ktreeL9P72_2 : wordsOK 24 wordsL9P72_2 = true := by
  decide +kernel

theorem ktreeL9P72 (c : Nat) (hc : c < 3) : wordsOK 24 (wordsL9P72.getD c []) = true :=
  match c, hc with
  | 0, _ => ktreeL9P72_0
  | 1, _ => ktreeL9P72_1
  | 2, _ => ktreeL9P72_2
  | c + 3, hc => absurd hc (by omega)

/-- **No point of `K` has the background `111000000` from a cell `p ≤ 16` on**, at any alignment `(a, o)`. -/
theorem no_k_tail16_L9P72 (u : Nat → Bool) (a o p : Nat) (hp : p ≤ 16)
    (hu : ∀ j, p ≤ j → u j = ringCell statesL9P72 9 a (j + o)) : ¬ InK u :=
  not_inK_of_tree statesL9P72 9 72 24 wordsL9P72 rowsL9P72 3 (by decide) (by decide +kernel)
    (by decide) (by decide) tablesL9P72_ok ktreeL9P72 u a o p hp hu

/-! ### The background `100100000`: `L = 9`, `P = 171` -/

/-- The 171 states of the background `100100000` on a ring of 9 cells, bit `j` the ring cell `j`. -/
def statesL9P171 : List Nat := [9, 287, 176, 424, 301, 233, 143, 216, 404, 375, 68, 238, 393, 95, 464, 281, 183, 164, 446, 288, 497, 11, 282, 434, 302, 488, 269, 153, 247, 132, 462, 312, 485, 29, 305, 235, 138, 475, 18, 63, 352, 337, 91, 466, 286, 432, 297, 239, 136, 476, 275, 190, 417, 51, 366, 328, 381, 65, 483, 22, 53, 357, 93, 465, 27, 306, 494, 264, 413, 113, 459, 58, 99, 470, 276, 439, 36, 126, 193, 163, 182, 421, 61, 353, 83, 478, 272, 441, 39, 380, 323, 102, 221, 145, 251, 130, 455, 44, 106, 203, 186, 419, 54, 101, 477, 17, 315, 226, 407, 116, 198, 429, 41, 367, 72, 252, 386, 326, 364, 331, 122, 195, 166, 445, 33, 371, 78, 249, 135, 204, 442, 290, 502, 260, 399, 88, 212, 406, 372, 327, 108, 202, 443, 34, 119, 452, 303, 232, 396, 347, 82, 223, 144, 504, 261, 141, 217, 151, 244, 390, 332, 379, 66, 231, 156, 498, 270, 408, 373, 69, 493]

theorem statesL9P171_cycle : ringStepOK statesL9P171 9 = true := by
  decide +kernel

/-- Chunk 0 of the 171 distinct tail words of the background, cells 16 to 63 in place. -/
def wordsL9P171_0 : List Nat := [9385818902474522624, 4692909451237261312, 2346454725618630656, 10396599399664058368, 5198299699832029184, 2599149849916014592, 1299574924957974528, 649787462478987264, 324893731239493632, 14403622084951277568, 16425183079330414592, 17435963576519950336, 17941353825114718208, 18194048949412102144, 9097024474706018304, 4548512237352976384, 2274256118676455424, 10360500096193003520, 3176738705452892160, 1588369352726413312, 794184676363206656, 397092338181603328, 9421918205945577472, 13934331139827564544, 6967165569913782272, 12706954821811634176, 6353477410905784320, 7653052335863824384, 3826526167931879424, 1913263083965906944, 10180003578837729280, 5090001789418864640]

/-- Chunk 1 of the 171 distinct tail words of the background, cells 16 to 63 in place. -/
def wordsL9P171_1 : List Nat := [11768372931564208128, 5884186465782071296, 12165465269745811456, 15306104671727648768, 14656317209248661504, 7328158604624330752, 12887451339166908416, 15667097706438197248, 7833548853219098624, 13140146463464292352, 6570073231732113408, 3285036615866056704, 10865890344787771392, 13428940891232731136, 6714470445616332800, 3357235222808166400, 10901989648258826240, 5450994824129413120, 11948869448919482368, 15197806761314484224, 16822275417512017920, 8411137708755976192, 11804472235035262976, 15125608154372374528, 16786176114040963072, 17616460093875224576, 8808230046937579520, 4404115023468756992, 2202057511734345728, 10324400792721948672, 5162200396360974336, 3898724774873989120]

/-- Chunk 2 of the 171 distinct tail words of the background, cells 16 to 63 in place. -/
def wordsL9P171_2 : List Nat := [1949362387436961792, 974681193718480896, 9710712633714016256, 14078728353711783936, 7039364176855891968, 12743054125282689024, 15594899099496087552, 7797449549748043776, 7292059301153275904, 3646029650576605184, 11046386862143045632, 5523193431071522816, 11984968752390537216, 5992484376195235840, 2996242188097617920, 10721493130903552000, 14584118602306551808, 15991991437677690880, 17219367755693621248, 17833055914701553664, 8916527957350744064, 13681636015530115072, 16064190044619800576, 17255467059164676096, 8627733529582305280, 13537238801645895680, 1227376318015864832, 613688159007932416, 9530216116358742016, 4765108058179371008, 2382554029089685504, 1191277014544809984]

/-- Chunk 3 of the 171 distinct tail words of the background, cells 16 to 63 in place. -/
def wordsL9P171_3 : List Nat := [9819010544127180800, 4909505272063590400, 2454752636031795200, 4295817113055592448, 11371280593382539264, 14909012333546045440, 16677878203627798528, 8338939101813866496, 13392841587761676288, 15919792830735581184, 17183268452222566400, 8591634226111250432, 16316885168917250048, 8158442584458592256, 4079221292229263360, 11262982682969374720, 5631491341484687360, 2815745670742343680, 1407872835371139072, 9927308454540345344, 14187026264124948480, 10938088951729881088, 14692416512719716352, 16569580293214633984, 17508162183462060032, 17977453128585773056, 8988726564292853760, 13717735319001169920, 6858867659500552192, 3429433829750276096, 8375038405284921344, 4187519202642427904]

/-- Chunk 4 of the 171 distinct tail words of the background, cells 16 to 63 in place. -/
def wordsL9P171_4 : List Nat := [2093759601321181184, 1046879800660590592, 9746811937185071104, 4873405968592535552, 11660075021151043584, 15053409547430264832, 16750076810569908224, 14295324174538113024, 7147662087269056512, 3573831043634495488, 11010287558671990784, 14728515816190771200, 7364257908095385600, 3682128954047660032, 1841064477023797248, 10143904275366674432, 12526458304456359936, 15486601189082923008, 16966672631396237312, 8483336315698085888, 13465040194703785984, 15955892134206636032, 7977946067103318016, 13212345070406402048, 6606172535203168256, 2960142884626563072, 1480071442313248768, 9963407758011400192, 4981703879005700096, 2490851939502850048, 10468798006606168064, 5234399003303084032]

/-- Chunk 5 of the 171 distinct tail words of the background, cells 16 to 63 in place. -/
def wordsL9P171_5 : List Nat := [11840571538506317824, 5920285769253126144, 8050144674045427712, 13248444373877456896, 15847594223793471488, 17147169148751511552, 17796956611230498816, 18121850342469992448, 9060925171234963456, 13753834622472224768, 16100289348090855424]

/-- The chunks of tail words. -/
def wordsL9P171 : List (List Nat) := [wordsL9P171_0, wordsL9P171_1, wordsL9P171_2, wordsL9P171_3, wordsL9P171_4, wordsL9P171_5]

/-- Row `a`, entry `o`: the index of the tail word at the alignment `(a, o)`. -/
def rowsL9P171 : List (List Nat) := [[0, 1, 2, 3, 4, 5, 6, 7, 8], [9, 10, 11, 12, 13, 14, 15, 16, 17], [18, 19, 20, 21, 22, 23, 24, 25, 26], [27, 28, 29, 30, 31, 32, 33, 34, 35], [36, 37, 38, 39, 40, 41, 42, 43, 44], [45, 46, 47, 48, 49, 50, 51, 52, 53], [54, 55, 56, 57, 58, 59, 60, 61, 62], [63, 64, 65, 66, 67, 68, 69, 70, 71], [72, 73, 74, 75, 76, 77, 78, 79, 80], [81, 82, 83, 84, 85, 86, 87, 88, 89], [90, 91, 92, 93, 94, 95, 96, 97, 98], [99, 100, 101, 102, 103, 104, 105, 106, 107], [108, 109, 110, 111, 112, 113, 114, 115, 116], [117, 118, 119, 120, 121, 122, 123, 124, 125], [126, 127, 128, 129, 130, 131, 132, 133, 134], [135, 136, 137, 138, 139, 140, 141, 142, 143], [144, 145, 146, 147, 148, 149, 150, 151, 152], [153, 154, 155, 156, 157, 158, 159, 160, 161], [162, 163, 164, 165, 166, 167, 168, 169, 170], [4, 5, 6, 7, 8, 0, 1, 2, 3], [13, 14, 15, 16, 17, 9, 10, 11, 12], [22, 23, 24, 25, 26, 18, 19, 20, 21], [31, 32, 33, 34, 35, 27, 28, 29, 30], [40, 41, 42, 43, 44, 36, 37, 38, 39], [49, 50, 51, 52, 53, 45, 46, 47, 48], [58, 59, 60, 61, 62, 54, 55, 56, 57], [67, 68, 69, 70, 71, 63, 64, 65, 66], [76, 77, 78, 79, 80, 72, 73, 74, 75], [85, 86, 87, 88, 89, 81, 82, 83, 84], [94, 95, 96, 97, 98, 90, 91, 92, 93], [103, 104, 105, 106, 107, 99, 100, 101, 102], [112, 113, 114, 115, 116, 108, 109, 110, 111], [121, 122, 123, 124, 125, 117, 118, 119, 120], [130, 131, 132, 133, 134, 126, 127, 128, 129], [139, 140, 141, 142, 143, 135, 136, 137, 138], [148, 149, 150, 151, 152, 144, 145, 146, 147], [157, 158, 159, 160, 161, 153, 154, 155, 156], [166, 167, 168, 169, 170, 162, 163, 164, 165], [8, 0, 1, 2, 3, 4, 5, 6, 7], [17, 9, 10, 11, 12, 13, 14, 15, 16], [26, 18, 19, 20, 21, 22, 23, 24, 25], [35, 27, 28, 29, 30, 31, 32, 33, 34], [44, 36, 37, 38, 39, 40, 41, 42, 43], [53, 45, 46, 47, 48, 49, 50, 51, 52], [62, 54, 55, 56, 57, 58, 59, 60, 61], [71, 63, 64, 65, 66, 67, 68, 69, 70], [80, 72, 73, 74, 75, 76, 77, 78, 79], [89, 81, 82, 83, 84, 85, 86, 87, 88], [98, 90, 91, 92, 93, 94, 95, 96, 97], [107, 99, 100, 101, 102, 103, 104, 105, 106], [116, 108, 109, 110, 111, 112, 113, 114, 115], [125, 117, 118, 119, 120, 121, 122, 123, 124], [134, 126, 127, 128, 129, 130, 131, 132, 133], [143, 135, 136, 137, 138, 139, 140, 141, 142], [152, 144, 145, 146, 147, 148, 149, 150, 151], [161, 153, 154, 155, 156, 157, 158, 159, 160], [170, 162, 163, 164, 165, 166, 167, 168, 169], [3, 4, 5, 6, 7, 8, 0, 1, 2], [12, 13, 14, 15, 16, 17, 9, 10, 11], [21, 22, 23, 24, 25, 26, 18, 19, 20], [30, 31, 32, 33, 34, 35, 27, 28, 29], [39, 40, 41, 42, 43, 44, 36, 37, 38], [48, 49, 50, 51, 52, 53, 45, 46, 47], [57, 58, 59, 60, 61, 62, 54, 55, 56], [66, 67, 68, 69, 70, 71, 63, 64, 65], [75, 76, 77, 78, 79, 80, 72, 73, 74], [84, 85, 86, 87, 88, 89, 81, 82, 83], [93, 94, 95, 96, 97, 98, 90, 91, 92], [102, 103, 104, 105, 106, 107, 99, 100, 101], [111, 112, 113, 114, 115, 116, 108, 109, 110], [120, 121, 122, 123, 124, 125, 117, 118, 119], [129, 130, 131, 132, 133, 134, 126, 127, 128], [138, 139, 140, 141, 142, 143, 135, 136, 137], [147, 148, 149, 150, 151, 152, 144, 145, 146], [156, 157, 158, 159, 160, 161, 153, 154, 155], [165, 166, 167, 168, 169, 170, 162, 163, 164], [7, 8, 0, 1, 2, 3, 4, 5, 6], [16, 17, 9, 10, 11, 12, 13, 14, 15], [25, 26, 18, 19, 20, 21, 22, 23, 24], [34, 35, 27, 28, 29, 30, 31, 32, 33], [43, 44, 36, 37, 38, 39, 40, 41, 42], [52, 53, 45, 46, 47, 48, 49, 50, 51], [61, 62, 54, 55, 56, 57, 58, 59, 60], [70, 71, 63, 64, 65, 66, 67, 68, 69], [79, 80, 72, 73, 74, 75, 76, 77, 78], [88, 89, 81, 82, 83, 84, 85, 86, 87], [97, 98, 90, 91, 92, 93, 94, 95, 96], [106, 107, 99, 100, 101, 102, 103, 104, 105], [115, 116, 108, 109, 110, 111, 112, 113, 114], [124, 125, 117, 118, 119, 120, 121, 122, 123], [133, 134, 126, 127, 128, 129, 130, 131, 132], [142, 143, 135, 136, 137, 138, 139, 140, 141], [151, 152, 144, 145, 146, 147, 148, 149, 150], [160, 161, 153, 154, 155, 156, 157, 158, 159], [169, 170, 162, 163, 164, 165, 166, 167, 168], [2, 3, 4, 5, 6, 7, 8, 0, 1], [11, 12, 13, 14, 15, 16, 17, 9, 10], [20, 21, 22, 23, 24, 25, 26, 18, 19], [29, 30, 31, 32, 33, 34, 35, 27, 28], [38, 39, 40, 41, 42, 43, 44, 36, 37], [47, 48, 49, 50, 51, 52, 53, 45, 46], [56, 57, 58, 59, 60, 61, 62, 54, 55], [65, 66, 67, 68, 69, 70, 71, 63, 64], [74, 75, 76, 77, 78, 79, 80, 72, 73], [83, 84, 85, 86, 87, 88, 89, 81, 82], [92, 93, 94, 95, 96, 97, 98, 90, 91], [101, 102, 103, 104, 105, 106, 107, 99, 100], [110, 111, 112, 113, 114, 115, 116, 108, 109], [119, 120, 121, 122, 123, 124, 125, 117, 118], [128, 129, 130, 131, 132, 133, 134, 126, 127], [137, 138, 139, 140, 141, 142, 143, 135, 136], [146, 147, 148, 149, 150, 151, 152, 144, 145], [155, 156, 157, 158, 159, 160, 161, 153, 154], [164, 165, 166, 167, 168, 169, 170, 162, 163], [6, 7, 8, 0, 1, 2, 3, 4, 5], [15, 16, 17, 9, 10, 11, 12, 13, 14], [24, 25, 26, 18, 19, 20, 21, 22, 23], [33, 34, 35, 27, 28, 29, 30, 31, 32], [42, 43, 44, 36, 37, 38, 39, 40, 41], [51, 52, 53, 45, 46, 47, 48, 49, 50], [60, 61, 62, 54, 55, 56, 57, 58, 59], [69, 70, 71, 63, 64, 65, 66, 67, 68], [78, 79, 80, 72, 73, 74, 75, 76, 77], [87, 88, 89, 81, 82, 83, 84, 85, 86], [96, 97, 98, 90, 91, 92, 93, 94, 95], [105, 106, 107, 99, 100, 101, 102, 103, 104], [114, 115, 116, 108, 109, 110, 111, 112, 113], [123, 124, 125, 117, 118, 119, 120, 121, 122], [132, 133, 134, 126, 127, 128, 129, 130, 131], [141, 142, 143, 135, 136, 137, 138, 139, 140], [150, 151, 152, 144, 145, 146, 147, 148, 149], [159, 160, 161, 153, 154, 155, 156, 157, 158], [168, 169, 170, 162, 163, 164, 165, 166, 167], [1, 2, 3, 4, 5, 6, 7, 8, 0], [10, 11, 12, 13, 14, 15, 16, 17, 9], [19, 20, 21, 22, 23, 24, 25, 26, 18], [28, 29, 30, 31, 32, 33, 34, 35, 27], [37, 38, 39, 40, 41, 42, 43, 44, 36], [46, 47, 48, 49, 50, 51, 52, 53, 45], [55, 56, 57, 58, 59, 60, 61, 62, 54], [64, 65, 66, 67, 68, 69, 70, 71, 63], [73, 74, 75, 76, 77, 78, 79, 80, 72], [82, 83, 84, 85, 86, 87, 88, 89, 81], [91, 92, 93, 94, 95, 96, 97, 98, 90], [100, 101, 102, 103, 104, 105, 106, 107, 99], [109, 110, 111, 112, 113, 114, 115, 116, 108], [118, 119, 120, 121, 122, 123, 124, 125, 117], [127, 128, 129, 130, 131, 132, 133, 134, 126], [136, 137, 138, 139, 140, 141, 142, 143, 135], [145, 146, 147, 148, 149, 150, 151, 152, 144], [154, 155, 156, 157, 158, 159, 160, 161, 153], [163, 164, 165, 166, 167, 168, 169, 170, 162], [5, 6, 7, 8, 0, 1, 2, 3, 4], [14, 15, 16, 17, 9, 10, 11, 12, 13], [23, 24, 25, 26, 18, 19, 20, 21, 22], [32, 33, 34, 35, 27, 28, 29, 30, 31], [41, 42, 43, 44, 36, 37, 38, 39, 40], [50, 51, 52, 53, 45, 46, 47, 48, 49], [59, 60, 61, 62, 54, 55, 56, 57, 58], [68, 69, 70, 71, 63, 64, 65, 66, 67], [77, 78, 79, 80, 72, 73, 74, 75, 76], [86, 87, 88, 89, 81, 82, 83, 84, 85], [95, 96, 97, 98, 90, 91, 92, 93, 94], [104, 105, 106, 107, 99, 100, 101, 102, 103], [113, 114, 115, 116, 108, 109, 110, 111, 112], [122, 123, 124, 125, 117, 118, 119, 120, 121], [131, 132, 133, 134, 126, 127, 128, 129, 130], [140, 141, 142, 143, 135, 136, 137, 138, 139], [149, 150, 151, 152, 144, 145, 146, 147, 148], [158, 159, 160, 161, 153, 154, 155, 156, 157], [167, 168, 169, 170, 162, 163, 164, 165, 166]]

theorem tablesL9P171_ok : tabOK 9 6 wordsL9P171 statesL9P171 rowsL9P171 = true := by
  decide +kernel

theorem ktreeL9P171_0 : wordsOK 24 wordsL9P171_0 = true := by
  decide +kernel

theorem ktreeL9P171_1 : wordsOK 24 wordsL9P171_1 = true := by
  decide +kernel

theorem ktreeL9P171_2 : wordsOK 24 wordsL9P171_2 = true := by
  decide +kernel

theorem ktreeL9P171_3 : wordsOK 24 wordsL9P171_3 = true := by
  decide +kernel

theorem ktreeL9P171_4 : wordsOK 24 wordsL9P171_4 = true := by
  decide +kernel

theorem ktreeL9P171_5 : wordsOK 24 wordsL9P171_5 = true := by
  decide +kernel

theorem ktreeL9P171 (c : Nat) (hc : c < 6) : wordsOK 24 (wordsL9P171.getD c []) = true :=
  match c, hc with
  | 0, _ => ktreeL9P171_0
  | 1, _ => ktreeL9P171_1
  | 2, _ => ktreeL9P171_2
  | 3, _ => ktreeL9P171_3
  | 4, _ => ktreeL9P171_4
  | 5, _ => ktreeL9P171_5
  | c + 6, hc => absurd hc (by omega)

/-- **No point of `K` has the background `100100000` from a cell `p ≤ 16` on**, at any alignment `(a, o)`. -/
theorem no_k_tail16_L9P171 (u : Nat → Bool) (a o p : Nat) (hp : p ≤ 16)
    (hu : ∀ j, p ≤ j → u j = ringCell statesL9P171 9 a (j + o)) : ¬ InK u :=
  not_inK_of_tree statesL9P171 9 171 24 wordsL9P171 rowsL9P171 6 (by decide) (by decide +kernel)
    (by decide) (by decide) tablesL9P171_ok ktreeL9P171 u a o p hp hu

/-! ### The background `1110100000`: `L = 10`, `P = 15` -/

/-- The 15 states of the background `1110100000` on a ring of 10 cells, bit `j` the ring cell `j`. -/
def statesL10P15 : List Nat := [23, 564, 871, 92, 210, 415, 368, 840, 637, 449, 291, 502, 773, 141, 985]

theorem statesL10P15_cycle : ringStepOK statesL10P15 10 = true := by
  decide +kernel

/-- Chunk 0 of the 30 distinct tail words of the background, cells 16 to 63 in place. -/
def wordsL10P15_0 : List Nat := [8096371543592927232, 13271557808651239424, 6635778904325619712, 3317889452162809856, 1658944726081404928, 829472363040669696, 414736181520302080, 9430740127614894080, 13938742100662222848, 16192743087185854464, 5247314296627003392, 11847029185168277504, 15146886629438914560, 7573443314719457280, 3786721657359695872, 1893360828679847936, 10170052451194699776, 5085026225597317120, 2542513112798658560, 10494628593254072320, 9052067961878937600, 4526033980939436032, 11486389027324493824, 14966566550516989952, 7483283275258462208, 12965013674483974144, 15705878874096730112, 17076311473903108096, 17761527773806329856, 18104135923757940736]

/-- The chunks of tail words. -/
def wordsL10P15 : List (List Nat) := [wordsL10P15_0]

/-- Row `a`, entry `o`: the index of the tail word at the alignment `(a, o)`. -/
def rowsL10P15 : List (List Nat) := [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9], [10, 11, 12, 13, 14, 15, 16, 17, 18, 19], [20, 21, 22, 23, 24, 25, 26, 27, 28, 29], [8, 9, 0, 1, 2, 3, 4, 5, 6, 7], [18, 19, 10, 11, 12, 13, 14, 15, 16, 17], [28, 29, 20, 21, 22, 23, 24, 25, 26, 27], [6, 7, 8, 9, 0, 1, 2, 3, 4, 5], [16, 17, 18, 19, 10, 11, 12, 13, 14, 15], [26, 27, 28, 29, 20, 21, 22, 23, 24, 25], [4, 5, 6, 7, 8, 9, 0, 1, 2, 3], [14, 15, 16, 17, 18, 19, 10, 11, 12, 13], [24, 25, 26, 27, 28, 29, 20, 21, 22, 23], [2, 3, 4, 5, 6, 7, 8, 9, 0, 1], [12, 13, 14, 15, 16, 17, 18, 19, 10, 11], [22, 23, 24, 25, 26, 27, 28, 29, 20, 21]]

theorem tablesL10P15_ok : tabOK 10 1 wordsL10P15 statesL10P15 rowsL10P15 = true := by
  decide +kernel

theorem ktreeL10P15_0 : wordsOK 24 wordsL10P15_0 = true := by
  decide +kernel

theorem ktreeL10P15 (c : Nat) (hc : c < 1) : wordsOK 24 (wordsL10P15.getD c []) = true :=
  match c, hc with
  | 0, _ => ktreeL10P15_0
  | c + 1, hc => absurd hc (by omega)

/-- **No point of `K` has the background `1110100000` from a cell `p ≤ 16` on**, at any alignment `(a, o)`. -/
theorem no_k_tail16_L10P15 (u : Nat → Bool) (a o p : Nat) (hp : p ≤ 16)
    (hu : ∀ j, p ≤ j → u j = ringCell statesL10P15 10 a (j + o)) : ¬ InK u :=
  not_inK_of_tree statesL10P15 10 15 24 wordsL10P15 rowsL10P15 1 (by decide) (by decide +kernel)
    (by decide) (by decide) tablesL10P15_ok ktreeL10P15 u a o p hp hu

/-! ### The background `10010100000`: `L = 11`, `P = 17` -/

/-- The 17 states of the background `10010100000` on a ring of 11 cells, bit `j` the ring cell `j`. -/
def statesL11P17 : List Nat := [41, 1135, 712, 1724, 1187, 950, 1573, 381, 1857, 99, 1238, 1940, 1143, 708, 1710, 1192, 1965]

theorem statesL11P17_cycle : ringStepOK statesL11P17 11 = true := by
  decide +kernel

/-- Chunk 0 of the 187 distinct tail words of the background, cells 16 to 63 in place. -/
def wordsL11P17_0 : List Nat := [1477902309764694016, 738951154882314240, 369475577441157120, 9408109825575354368, 4704054912787677184, 2352027456393838592, 10399385765051695104, 5199692882525814784, 11823218478117683200, 5911609239058841600, 2955804619529388032, 4019173354604003328, 2009586677301968896, 10228165375505727488, 14337454724607639552, 16392099399158595584, 17419421736434073600, 17933082905071779840, 8966541452535857152, 13706642763122671616, 16076693418416078848, 8038346709208006656, 7218291159277633536, 12832517616493592576, 6416258808246763520, 3208129404123348992, 1604064702061674496, 802032351030804480, 9624388212370178048, 4812194106185089024, 2406097053092544512, 10426420563401048064]

/-- Chunk 1 of the 187 distinct tail words of the background, cells 16 to 63 in place. -/
def wordsL11P17_1 : List Nat := [14436582318555267072, 6803757584587489280, 12625250829148487680, 15535997451429019648, 7767998725714477056, 3883999362857238528, 11165371718283362304, 14806057895996424192, 16626400984852987904, 17536572529281269760, 8768286264640602112, 13607515169175044096, 5893586040159272960, 2946793020079603712, 10696768546894577664, 14571756310302031872, 16509250192005791744, 8254625096002895872, 4127312548001415168, 2063656274000674816, 10255200173855080448, 5127600086927540224, 11787172080318545920, 15797333835472764928, 17122038954591125504, 8561019477295562752, 4280509738647748608, 11363626906178617344, 14905185489944051712, 7452592744972025856, 12949668409340788736, 15698206241525137408]

/-- Chunk 2 of the 187 distinct tail words of the background, cells 16 to 63 in place. -/
def wordsL11P17_2 : List Nat := [7849103120762535936, 13147923597236043776, 1360751516917497856, 9903747795313491968, 14175245934511521792, 16310995004110536704, 8155497502055268352, 13301120787882377216, 6650560393941155840, 3325280196970545152, 10886012135340048384, 5443006067669991424, 2721503033834995712, 13733677561472024576, 6866838780735979520, 3433419390367956992, 10940081732038754304, 5470040866019344384, 11958392469864448000, 15202568271786999808, 16824656172748242944, 17635700123228897280, 18041222098469191680, 9020611049234563072, 11597928491873075200, 15022336282791313408, 16734540178250399744, 17590642125979975680, 8795321062989955072, 4397660531494944768, 2198830265747439616, 1099415132873687040]

/-- Chunk 3 of the 187 distinct tail words of the background, cells 16 to 63 in place. -/
def wordsL11P17_3 : List Nat := [549707566436843520, 9498225820073197568, 4749112910036598784, 3568593382114787328, 1784296691057360896, 892148345528647680, 9669446209619099648, 14058095141664325632, 7029047570832162816, 3514523785416081408, 1757261892708007936, 10102002983208747008, 14274373528459149312, 7137186764229574656, 7731952327915339776, 3865976163957669888, 11156360118833577984, 5578180059416756224, 12012462066563153920, 15229603070136352768, 7614801535068143616, 13030772804388847616, 6515386402194391040, 12481065237951938560, 15463904655830745088, 14589779509201600512, 16518261791455576064, 17482502932582563840, 8741251466291249152, 4370625733145591808, 11408684903427538944, 5704342451713736704]

/-- Chunk 4 of the 187 distinct tail words of the background, cells 16 to 63 in place. -/
def wordsL11P17_4 : List Nat := [12075543262711644160, 6037771631355822080, 3018885815677878272, 10732814944693714944, 4307544536997101568, 2153772268498518016, 10300258171104002048, 14373501122406776832, 16410122598058164224, 17428433335883857920, 8714216667941896192, 13580480370825691136, 16013612222267588608, 17230178147988537344, 8615089073994268672, 7074105568081084416, 12760424820895318016, 6380212410447626240, 3190106205223780352, 1595053102611890176, 10020898588160688128, 5010449294080344064, 2505224647040172032, 1252612323520086016, 9849678198614786048, 14148211136162168832, 6299108015399567360, 12372926044554526720, 15409835059132039168, 7704917529565986816, 13075830801637769216, 15761287437673627648]

/-- Chunk 5 of the 187 distinct tail words of the background, cells 16 to 63 in place. -/
def wordsL11P17_5 : List Nat := [17104015755691556864, 8552007877845778432, 13499375975777632256, 6749687987888783360, 12598216030799134720, 6073818029154959360, 3036909014577446912, 10741826544143499264, 5370913272071716864, 2685456636035858432, 1342728318017929216, 9894736195863707648, 4947368097931853824, 11697056085820702720, 5848528042910351360, 12147636058309918720, 15490939454180098048, 16968841763944792064, 17707792918827171840, 18077268496268328960, 9038634248134131712, 13742689160921808896, 16094716617315647488, 8047358308657790976, 13247051191183671296, 6623525595591802880, 12535134834650644480]

/-- The chunks of tail words. -/
def wordsL11P17 : List (List Nat) := [wordsL11P17_0, wordsL11P17_1, wordsL11P17_2, wordsL11P17_3, wordsL11P17_4, wordsL11P17_5]

/-- Row `a`, entry `o`: the index of the tail word at the alignment `(a, o)`. -/
def rowsL11P17 : List (List Nat) := [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10], [11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21], [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32], [33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43], [44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54], [55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65], [66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76], [77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87], [88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98], [99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109], [110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120], [121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131], [132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142], [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153], [154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164], [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175], [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186]]

theorem tablesL11P17_ok : tabOK 11 6 wordsL11P17 statesL11P17 rowsL11P17 = true := by
  decide +kernel

theorem ktreeL11P17_0 : wordsOK 24 wordsL11P17_0 = true := by
  decide +kernel

theorem ktreeL11P17_1 : wordsOK 24 wordsL11P17_1 = true := by
  decide +kernel

theorem ktreeL11P17_2 : wordsOK 24 wordsL11P17_2 = true := by
  decide +kernel

theorem ktreeL11P17_3 : wordsOK 24 wordsL11P17_3 = true := by
  decide +kernel

theorem ktreeL11P17_4 : wordsOK 24 wordsL11P17_4 = true := by
  decide +kernel

theorem ktreeL11P17_5 : wordsOK 24 wordsL11P17_5 = true := by
  decide +kernel

theorem ktreeL11P17 (c : Nat) (hc : c < 6) : wordsOK 24 (wordsL11P17.getD c []) = true :=
  match c, hc with
  | 0, _ => ktreeL11P17_0
  | 1, _ => ktreeL11P17_1
  | 2, _ => ktreeL11P17_2
  | 3, _ => ktreeL11P17_3
  | 4, _ => ktreeL11P17_4
  | 5, _ => ktreeL11P17_5
  | c + 6, hc => absurd hc (by omega)

/-- **No point of `K` has the background `10010100000` from a cell `p ≤ 16` on**, at any alignment `(a, o)`. -/
theorem no_k_tail16_L11P17 (u : Nat → Bool) (a o p : Nat) (hp : p ≤ 16)
    (hu : ∀ j, p ≤ j → u j = ringCell statesL11P17 11 a (j + o)) : ¬ InK u :=
  not_inK_of_tree statesL11P17 11 17 24 wordsL11P17 rowsL11P17 6 (by decide) (by decide +kernel)
    (by decide) (by decide) tablesL11P17_ok ktreeL11P17 u a o p hp hu

/-! ### The background `10100000000`: `L = 11`, `P = 154` -/

/-- The 154 states of the background `10100000000` on a ring of 11 cells, bit `j` the ring cell `j`. -/
def statesL11P154 : List Nat := [5, 1037, 537, 823, 740, 1694, 1264, 1929, 95, 1232, 1945, 119, 1220, 1967, 40, 108, 202, 443, 1826, 1270, 1924, 1103, 760, 1668, 1231, 952, 1572, 1407, 320, 864, 1616, 1497, 279, 1972, 1063, 636, 1986, 1062, 1660, 1475, 294, 1021, 513, 771, 646, 1741, 185, 1447, 316, 994, 1559, 308, 998, 1565, 305, 2027, 10, 27, 1074, 1646, 1480, 1341, 481, 1811, 190, 417, 1843, 238, 393, 1887, 80, 216, 404, 886, 1605, 493, 1801, 159, 1520, 1289, 415, 1904, 1097, 767, 640, 1728, 1185, 947, 558, 1897, 79, 1272, 1925, 77, 1273, 903, 588, 2042, 1026, 1542, 1292, 1435, 370, 847, 632, 1988, 1071, 616, 1996, 1083, 610, 2007, 20, 54, 101, 1245, 913, 635, 962, 1575, 380, 834, 1639, 476, 786, 1727, 160, 432, 808, 1772, 1163, 986, 1555, 318, 993, 531, 830, 1761, 147, 1534, 1280, 1409, 323, 1894, 1116, 1747, 158, 497, 1803, 154, 499, 1806, 1176, 2037]

theorem statesL11P154_cycle : ringStepOK statesL11P154 11 = true := by
  decide +kernel

/-- Chunk 0 of the 154 distinct tail words of the background, cells 16 to 63 in place. -/
def wordsL11P154_0 : List Nat := [180231988995686400, 90115994497843200, 45057997248921600, 9245901035479236608, 4622950517739618304, 11534847295724584960, 5767423647862292480, 2883711823931113472, 1441855911965556736, 720927955982745600, 360463977991372800, 486626370288353280, 243313185144176640, 9345028629426864128, 13895886351568207872, 6947943175784103936, 12697343624746827776, 15572043849228156928, 7786021924614045696, 3893010962307022848, 1946505481153478656, 973252740576706560, 910171544428216320, 9678457809068883968, 4839228904534441984, 11642986489121996800, 5821493244560998400, 2910746622280466432, 10678745347995009024, 14562744710852247552, 7281372355426123776, 3640686177713061888]

/-- Chunk 1 of the 154 distinct tail words of the background, cells 16 to 63 in place. -/
def wordsL11P154_1 : List Nat := [1820343088856498176, 11219441314982068224, 14833092694345777152, 7416546347172888576, 12931645210441220096, 15689194642075353088, 17067969357892419584, 8533984678946209792, 13490364376327847936, 15968554225018667008, 7984277112509300736, 3992138556254650368, 8227590297653542912, 13337167185681514496, 6668583592840724480, 3334291796420329472, 1667145898210164736, 10056944985959825408, 5028472492979912704, 2514236246489956352, 10480490160099753984, 14463617116904620032, 16455180595307085824, 5722365650613305344, 12084554862161428480, 15265649467935490048, 7632824733967712256, 13039784403838631936, 15743264238774059008, 17095004156241772544, 17770874114975662080, 8885437057487798272]

/-- Chunk 2 of the 154 distinct tail words of the background, cells 16 to 63 in place. -/
def wordsL11P154_2 : List Nat := [4442718528743866368, 11444731301226676224, 8669158670692974592, 4334579335346454528, 11390661704527970304, 5695330852263952384, 2847665426131976192, 1423832713065988096, 711916356532961280, 9579330215121256448, 14013037144415404032, 16229890609062477824, 17338317341386014720, 14193269133411090432, 16320006603560321024, 17383375338634936320, 17915059706172211200, 8957529853086072832, 4478764926543003648, 11462754500126244864, 5731377250063089664, 2865688625031544832, 1432844312515772416, 9939794193112629248, 3424407790918172672, 1712203895459086336, 856101947729510400, 9651423010719531008, 14049083542214541312, 16247913807962046464, 17347328940835799040, 17897036507272642560]

/-- Chunk 3 of the 154 distinct tail words of the background, cells 16 to 63 in place. -/
def wordsL11P154_3 : List Nat := [8948518253636288512, 13697631163672887296, 6848815581836410880, 7515673941120516096, 3757836970560258048, 11102290522134872064, 5551145261067403264, 2775572630533701632, 1387786315266850816, 693893157633392640, 9570318615671472128, 4785159307835736064, 11615951690772643840, 15031347882241097728, 14770011498197286912, 16608377785953419264, 17527560929831485440, 17987152501770485760, 8993576250885210112, 4496788125442572288, 11471766099576029184, 14959255086642757632, 7479627543321378816, 3739813771660689408, 11093278922685087744, 4289521338097532928, 2144760669048733696, 1072380334524334080, 9759562204116942848, 14103153138913247232, 16274948606311399424, 8137474303155699712]

/-- Chunk 4 of the 154 distinct tail words of the background, cells 16 to 63 in place. -/
def wordsL11P154_4 : List Nat := [13292109188432592896, 15869426631071039488, 17158085352390262784, 8579042676195131392, 7083117167530868736, 3541558583765434368, 10994151328737460224, 5497075664368697344, 2748537832184348672, 10597640952946950144, 5298820476473442304, 2649410238236721152, 1324705119118360576, 9885724596413923328, 14166234335061737472, 15563032249778372608, 17004888161743929344, 17725816117726740480, 18086280095718113280, 18266512084713799680, 18356628079211642880, 18401686076460564480, 9200843038230249472, 13823793555969867776, 6911896777984901120, 12679320425847193600]

/-- The chunks of tail words. -/
def wordsL11P154 : List (List Nat) := [wordsL11P154_0, wordsL11P154_1, wordsL11P154_2, wordsL11P154_3, wordsL11P154_4]

/-- Row `a`, entry `o`: the index of the tail word at the alignment `(a, o)`. -/
def rowsL11P154 : List (List Nat) := [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10], [11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21], [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32], [33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43], [44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54], [55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65], [66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76], [77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87], [88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98], [99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109], [110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120], [121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131], [132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142], [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153], [8, 9, 10, 0, 1, 2, 3, 4, 5, 6, 7], [19, 20, 21, 11, 12, 13, 14, 15, 16, 17, 18], [30, 31, 32, 22, 23, 24, 25, 26, 27, 28, 29], [41, 42, 43, 33, 34, 35, 36, 37, 38, 39, 40], [52, 53, 54, 44, 45, 46, 47, 48, 49, 50, 51], [63, 64, 65, 55, 56, 57, 58, 59, 60, 61, 62], [74, 75, 76, 66, 67, 68, 69, 70, 71, 72, 73], [85, 86, 87, 77, 78, 79, 80, 81, 82, 83, 84], [96, 97, 98, 88, 89, 90, 91, 92, 93, 94, 95], [107, 108, 109, 99, 100, 101, 102, 103, 104, 105, 106], [118, 119, 120, 110, 111, 112, 113, 114, 115, 116, 117], [129, 130, 131, 121, 122, 123, 124, 125, 126, 127, 128], [140, 141, 142, 132, 133, 134, 135, 136, 137, 138, 139], [151, 152, 153, 143, 144, 145, 146, 147, 148, 149, 150], [5, 6, 7, 8, 9, 10, 0, 1, 2, 3, 4], [16, 17, 18, 19, 20, 21, 11, 12, 13, 14, 15], [27, 28, 29, 30, 31, 32, 22, 23, 24, 25, 26], [38, 39, 40, 41, 42, 43, 33, 34, 35, 36, 37], [49, 50, 51, 52, 53, 54, 44, 45, 46, 47, 48], [60, 61, 62, 63, 64, 65, 55, 56, 57, 58, 59], [71, 72, 73, 74, 75, 76, 66, 67, 68, 69, 70], [82, 83, 84, 85, 86, 87, 77, 78, 79, 80, 81], [93, 94, 95, 96, 97, 98, 88, 89, 90, 91, 92], [104, 105, 106, 107, 108, 109, 99, 100, 101, 102, 103], [115, 116, 117, 118, 119, 120, 110, 111, 112, 113, 114], [126, 127, 128, 129, 130, 131, 121, 122, 123, 124, 125], [137, 138, 139, 140, 141, 142, 132, 133, 134, 135, 136], [148, 149, 150, 151, 152, 153, 143, 144, 145, 146, 147], [2, 3, 4, 5, 6, 7, 8, 9, 10, 0, 1], [13, 14, 15, 16, 17, 18, 19, 20, 21, 11, 12], [24, 25, 26, 27, 28, 29, 30, 31, 32, 22, 23], [35, 36, 37, 38, 39, 40, 41, 42, 43, 33, 34], [46, 47, 48, 49, 50, 51, 52, 53, 54, 44, 45], [57, 58, 59, 60, 61, 62, 63, 64, 65, 55, 56], [68, 69, 70, 71, 72, 73, 74, 75, 76, 66, 67], [79, 80, 81, 82, 83, 84, 85, 86, 87, 77, 78], [90, 91, 92, 93, 94, 95, 96, 97, 98, 88, 89], [101, 102, 103, 104, 105, 106, 107, 108, 109, 99, 100], [112, 113, 114, 115, 116, 117, 118, 119, 120, 110, 111], [123, 124, 125, 126, 127, 128, 129, 130, 131, 121, 122], [134, 135, 136, 137, 138, 139, 140, 141, 142, 132, 133], [145, 146, 147, 148, 149, 150, 151, 152, 153, 143, 144], [10, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9], [21, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20], [32, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], [43, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42], [54, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53], [65, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64], [76, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75], [87, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86], [98, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97], [109, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108], [120, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119], [131, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130], [142, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141], [153, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152], [7, 8, 9, 10, 0, 1, 2, 3, 4, 5, 6], [18, 19, 20, 21, 11, 12, 13, 14, 15, 16, 17], [29, 30, 31, 32, 22, 23, 24, 25, 26, 27, 28], [40, 41, 42, 43, 33, 34, 35, 36, 37, 38, 39], [51, 52, 53, 54, 44, 45, 46, 47, 48, 49, 50], [62, 63, 64, 65, 55, 56, 57, 58, 59, 60, 61], [73, 74, 75, 76, 66, 67, 68, 69, 70, 71, 72], [84, 85, 86, 87, 77, 78, 79, 80, 81, 82, 83], [95, 96, 97, 98, 88, 89, 90, 91, 92, 93, 94], [106, 107, 108, 109, 99, 100, 101, 102, 103, 104, 105], [117, 118, 119, 120, 110, 111, 112, 113, 114, 115, 116], [128, 129, 130, 131, 121, 122, 123, 124, 125, 126, 127], [139, 140, 141, 142, 132, 133, 134, 135, 136, 137, 138], [150, 151, 152, 153, 143, 144, 145, 146, 147, 148, 149], [4, 5, 6, 7, 8, 9, 10, 0, 1, 2, 3], [15, 16, 17, 18, 19, 20, 21, 11, 12, 13, 14], [26, 27, 28, 29, 30, 31, 32, 22, 23, 24, 25], [37, 38, 39, 40, 41, 42, 43, 33, 34, 35, 36], [48, 49, 50, 51, 52, 53, 54, 44, 45, 46, 47], [59, 60, 61, 62, 63, 64, 65, 55, 56, 57, 58], [70, 71, 72, 73, 74, 75, 76, 66, 67, 68, 69], [81, 82, 83, 84, 85, 86, 87, 77, 78, 79, 80], [92, 93, 94, 95, 96, 97, 98, 88, 89, 90, 91], [103, 104, 105, 106, 107, 108, 109, 99, 100, 101, 102], [114, 115, 116, 117, 118, 119, 120, 110, 111, 112, 113], [125, 126, 127, 128, 129, 130, 131, 121, 122, 123, 124], [136, 137, 138, 139, 140, 141, 142, 132, 133, 134, 135], [147, 148, 149, 150, 151, 152, 153, 143, 144, 145, 146], [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0], [12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 11], [23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 22], [34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 33], [45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 44], [56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 55], [67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 66], [78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 77], [89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 88], [100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 99], [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 110], [122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 121], [133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 132], [144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 143], [9, 10, 0, 1, 2, 3, 4, 5, 6, 7, 8], [20, 21, 11, 12, 13, 14, 15, 16, 17, 18, 19], [31, 32, 22, 23, 24, 25, 26, 27, 28, 29, 30], [42, 43, 33, 34, 35, 36, 37, 38, 39, 40, 41], [53, 54, 44, 45, 46, 47, 48, 49, 50, 51, 52], [64, 65, 55, 56, 57, 58, 59, 60, 61, 62, 63], [75, 76, 66, 67, 68, 69, 70, 71, 72, 73, 74], [86, 87, 77, 78, 79, 80, 81, 82, 83, 84, 85], [97, 98, 88, 89, 90, 91, 92, 93, 94, 95, 96], [108, 109, 99, 100, 101, 102, 103, 104, 105, 106, 107], [119, 120, 110, 111, 112, 113, 114, 115, 116, 117, 118], [130, 131, 121, 122, 123, 124, 125, 126, 127, 128, 129], [141, 142, 132, 133, 134, 135, 136, 137, 138, 139, 140], [152, 153, 143, 144, 145, 146, 147, 148, 149, 150, 151], [6, 7, 8, 9, 10, 0, 1, 2, 3, 4, 5], [17, 18, 19, 20, 21, 11, 12, 13, 14, 15, 16], [28, 29, 30, 31, 32, 22, 23, 24, 25, 26, 27], [39, 40, 41, 42, 43, 33, 34, 35, 36, 37, 38], [50, 51, 52, 53, 54, 44, 45, 46, 47, 48, 49], [61, 62, 63, 64, 65, 55, 56, 57, 58, 59, 60], [72, 73, 74, 75, 76, 66, 67, 68, 69, 70, 71], [83, 84, 85, 86, 87, 77, 78, 79, 80, 81, 82], [94, 95, 96, 97, 98, 88, 89, 90, 91, 92, 93], [105, 106, 107, 108, 109, 99, 100, 101, 102, 103, 104], [116, 117, 118, 119, 120, 110, 111, 112, 113, 114, 115], [127, 128, 129, 130, 131, 121, 122, 123, 124, 125, 126], [138, 139, 140, 141, 142, 132, 133, 134, 135, 136, 137], [149, 150, 151, 152, 153, 143, 144, 145, 146, 147, 148], [3, 4, 5, 6, 7, 8, 9, 10, 0, 1, 2], [14, 15, 16, 17, 18, 19, 20, 21, 11, 12, 13], [25, 26, 27, 28, 29, 30, 31, 32, 22, 23, 24], [36, 37, 38, 39, 40, 41, 42, 43, 33, 34, 35], [47, 48, 49, 50, 51, 52, 53, 54, 44, 45, 46], [58, 59, 60, 61, 62, 63, 64, 65, 55, 56, 57], [69, 70, 71, 72, 73, 74, 75, 76, 66, 67, 68], [80, 81, 82, 83, 84, 85, 86, 87, 77, 78, 79], [91, 92, 93, 94, 95, 96, 97, 98, 88, 89, 90], [102, 103, 104, 105, 106, 107, 108, 109, 99, 100, 101], [113, 114, 115, 116, 117, 118, 119, 120, 110, 111, 112], [124, 125, 126, 127, 128, 129, 130, 131, 121, 122, 123], [135, 136, 137, 138, 139, 140, 141, 142, 132, 133, 134], [146, 147, 148, 149, 150, 151, 152, 153, 143, 144, 145]]

theorem tablesL11P154_ok : tabOK 11 5 wordsL11P154 statesL11P154 rowsL11P154 = true := by
  decide +kernel

theorem ktreeL11P154_0 : wordsOK 24 wordsL11P154_0 = true := by
  decide +kernel

theorem ktreeL11P154_1 : wordsOK 24 wordsL11P154_1 = true := by
  decide +kernel

theorem ktreeL11P154_2 : wordsOK 24 wordsL11P154_2 = true := by
  decide +kernel

theorem ktreeL11P154_3 : wordsOK 24 wordsL11P154_3 = true := by
  decide +kernel

theorem ktreeL11P154_4 : wordsOK 24 wordsL11P154_4 = true := by
  decide +kernel

theorem ktreeL11P154 (c : Nat) (hc : c < 5) : wordsOK 24 (wordsL11P154.getD c []) = true :=
  match c, hc with
  | 0, _ => ktreeL11P154_0
  | 1, _ => ktreeL11P154_1
  | 2, _ => ktreeL11P154_2
  | 3, _ => ktreeL11P154_3
  | 4, _ => ktreeL11P154_4
  | c + 5, hc => absurd hc (by omega)

/-- **No point of `K` has the background `10100000000` from a cell `p ≤ 16` on**, at any alignment `(a, o)`. -/
theorem no_k_tail16_L11P154 (u : Nat → Bool) (a o p : Nat) (hp : p ≤ 16)
    (hu : ∀ j, p ≤ j → u j = ringCell statesL11P154 11 a (j + o)) : ¬ InK u :=
  not_inK_of_tree statesL11P154 11 154 24 wordsL11P154 rowsL11P154 5 (by decide) (by decide +kernel)
    (by decide) (by decide) tablesL11P154_ok ktreeL11P154 u a o p hp hu

/-! ### The background `111110010000`: `L = 12`, `P = 3` -/

/-- The 3 states of the background `111110010000` on a ring of 12 cells, bit `j` the ring cell `j`. -/
def statesL12P3 : List Nat := [159, 2544, 3849]

theorem statesL12P3_cycle : ringStepOK statesL12P3 12 = true := by
  decide +kernel

/-- Chunk 0 of the 12 distinct tail words of the background, cells 16 to 63 in place. -/
def wordsL12P3_0 : List Nat := [17338588019464667136, 17892666046587076608, 8946333023293538304, 4473166511646769152, 11459955292678127616, 5729977646339063808, 2864988823169531904, 1432494411584765952, 716247205792382976, 9581495639750934528, 14014119856730210304, 16230431965219848192]

/-- The chunks of tail words. -/
def wordsL12P3 : List (List Nat) := [wordsL12P3_0]

/-- Row `a`, entry `o`: the index of the tail word at the alignment `(a, o)`. -/
def rowsL12P3 : List (List Nat) := [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], [8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7], [4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3]]

theorem tablesL12P3_ok : tabOK 12 1 wordsL12P3 statesL12P3 rowsL12P3 = true := by
  decide +kernel

theorem ktreeL12P3_0 : wordsOK 24 wordsL12P3_0 = true := by
  decide +kernel

theorem ktreeL12P3 (c : Nat) (hc : c < 1) : wordsOK 24 (wordsL12P3.getD c []) = true :=
  match c, hc with
  | 0, _ => ktreeL12P3_0
  | c + 1, hc => absurd hc (by omega)

/-- **No point of `K` has the background `111110010000` from a cell `p ≤ 16` on**, at any alignment `(a, o)`. -/
theorem no_k_tail16_L12P3 (u : Nat → Bool) (a o p : Nat) (hp : p ≤ 16)
    (hu : ∀ j, p ≤ j → u j = ringCell statesL12P3 12 a (j + o)) : ¬ InK u :=
  not_inK_of_tree statesL12P3 12 3 24 wordsL12P3 rowsL12P3 1 (by decide) (by decide +kernel)
    (by decide) (by decide) tablesL12P3_ok ktreeL12P3 u a o p hp hu

/-! ### The background `100100000000`: `L = 12`, `P = 102` -/

/-- The 102 states of the background `100100000000` on a ring of 12 cells, bit `j` the ring cell `j`. -/
def statesL12P102 : List Nat := [9, 2079, 1072, 3688, 2509, 1849, 1255, 1948, 3186, 2766, 2744, 2725, 701, 3745, 179, 2478, 3880, 2285, 1417, 1375, 1360, 3416, 2389, 1877, 1109, 1749, 1173, 2037, 1029, 1549, 1305, 1463, 1316, 3582, 2304, 3969, 67, 2278, 3484, 2419, 1870, 3193, 711, 3756, 2219, 1450, 3371, 490, 779, 3738, 2290, 3470, 2392, 3925, 85, 2261, 1429, 1397, 1349, 1389, 1353, 1407, 1344, 3424, 2385, 1883, 1106, 3807, 144, 504, 772, 1678, 3289, 919, 3700, 2503, 1836, 3306, 2954, 2650, 3026, 2590, 2864, 2793, 655, 3800, 2197, 1525, 1285, 1421, 1369, 1367, 1364, 3414, 2388, 3927, 84, 214, 405, 2933, 581, 4077]

theorem statesL12P102_cycle : ringStepOK statesL12P102 12 = true := by
  decide +kernel

/-- Chunk 0 of the 408 distinct tail words of the background, cells 16 to 63 in place. -/
def wordsL12P102_0 : List Nat := [10378827434878304256, 5189413717439152128, 2594706858719576064, 1297353429359788032, 648676714679894016, 324338357339947008, 162169178669973504, 81084589334986752, 40542294667493376, 9243643184188489728, 4621821592094244864, 2310910796047122432, 17879151948364578816, 18162948011037032448, 9081474005518516224, 4540737002759258112, 2270368501379629056, 1135184250689814528, 567592125344907264, 283796062672453632, 9365270068190969856, 13906007070950227968, 16176375572329857024, 17311559823019671552, 301814860302450688, 9374279467005968384, 13910511770357727232, 6955255885178863616, 3477627942589431808, 1738813971294715904, 869406985647357952, 9658075529678422016]

/-- Chunk 1 of the 408 distinct tail words of the background, cells 16 to 63 in place. -/
def wordsL12P102_1 : List Nat := [4829037764839211008, 2414518882419605504, 1207259441209802752, 603629720604901376, 10261705250283323392, 5130852625141661696, 11788798349425573888, 15117771211567529984, 7558885605783764992, 3779442802891882496, 11113093438300684288, 14779918756005085184, 16613331414857285632, 8306665707428642816, 4153332853714321408, 2076666426857160704, 15694372735727435776, 7847186367863717888, 3923593183931858944, 11185168628820672512, 14815956351265079296, 16631350212487282688, 8315675106243641344, 4157837553121820672, 11302290813415653376, 14874517443562569728, 7437258721781284864, 12942001397745385472, 10896867866740719616, 14671805970225102848, 16559275021967294464, 8279637510983647232]

/-- Chunk 2 of the 408 distinct tail words of the background, cells 16 to 63 in place. -/
def wordsL12P102_2 : List Nat := [4139818755491823616, 11293281414600654848, 14870012744155070464, 16658378408932278272, 8329189204466139136, 13387966639087812608, 6693983319543906304, 3346991659771953152, 8423787892023623680, 4211893946011811840, 11329319009860648960, 14888031541785067520, 16667387807747276800, 8333693903873638400, 4166846951936819200, 11306795512823152640, 5653397756411576320, 12050070915060531200, 15248407494385008640, 16847575784047247360, 14383505208145149952, 16415124640927318016, 8207562320463659008, 4103781160231829504, 11275262616970657792, 14861003345340071936, 16653873709524779008, 17550308891617132544, 8775154445808566272, 4387577222904283136, 2193788611452141568, 10320266342580813824]

/-- Chunk 3 of the 408 distinct tail words of the background, cells 16 to 63 in place. -/
def wordsL12P102_3 : List Nat := [3202841278731976704, 10824792676220731392, 14635768374965108736, 16541256224337297408, 8270628112168648704, 4135314056084324352, 2067657028042162176, 10257200550875824128, 14351972312292655104, 7175986156146327552, 12811365114927906816, 6405682557463953408, 16919650974567235584, 8459825487283617792, 4229912743641808896, 11338328408675647488, 14892536241192566784, 7446268120596283392, 12946506097152884736, 6473253048576442368, 12459998561142964224, 6229999280571482112, 12338371677140484096, 15392557875424985088, 9995927985240866816, 14221336029475176448, 16334040051592331264, 8167020025796165632, 13306882049752825856, 6653441024876412928, 12550092549292949504, 6275046274646474752]

/-- Chunk 4 of the 408 distinct tail words of the background, cells 16 to 63 in place. -/
def wordsL12P102_4 : List Nat := [12360895174177980416, 6180447587088990208, 3090223793544495104, 1545111896772247552, 6531814140873932800, 3265907070436966400, 10856325572073226240, 5428162786036613120, 11937453429873049600, 5968726714936524800, 12207735394323005440, 6103867697161502720, 12275305885435494400, 15361024979572490240, 7680512489786245120, 13063628281747865600, 15185341702680018944, 16816042888194752512, 17631393480952119296, 8815696740476059648, 13631220407092772864, 6815610203546386432, 12631177138627936256, 6315588569313968128, 3157794284656984064, 10802269179183235072, 5401134589591617536, 11923939331650551808, 2207302709674639360, 1103651354837319680, 9775197714273402880, 4887598857136701440]

/-- Chunk 5 of the 408 distinct tail words of the background, cells 16 to 63 in place. -/
def wordsL12P102_5 : List Nat := [11667171465423093760, 5833585732711546880, 12140164903210516480, 15293454488460001280, 16870099281084743680, 17658421677397114880, 8829210838698557440, 4414605419349278720, 3509160838441926656, 10977952456075706368, 14712348264892596224, 7356174132446298112, 12901459103077892096, 6450729551538946048, 3225364775769473024, 1612682387884736512, 806341193942368256, 9626542633825927168, 14036643353767706624, 7018321676883853312, 16838566385232248832, 8419283192616124416, 13433013633162805248, 6716506816581402624, 12581625445145444352, 15514184759427465216, 7757092379713732608, 3878546189856866304, 11162645131783176192, 5581322565891588096, 12014033319800537088, 15230388696755011584]

/-- Chunk 6 of the 408 distinct tail words of the background, cells 16 to 63 in place. -/
def wordsL12P102_6 : List Nat := [10315761643173314560, 5157880821586657280, 11802312447648071680, 5901156223824035840, 2950578111912017920, 10698661092810752000, 14572702583260119040, 16509723328484802560, 17478233701097144320, 8739116850548572160, 4369558425274286080, 2184779212637143040, 15631306944022446080, 7815653472011223040, 13131198772860354560, 15788971423284920320, 17117857748497203200, 8558928874248601600, 4279464437124300800, 2139732218562150400, 10293238146135818240, 14369991109922652160, 7184995554961326080, 12815869814335406080, 10775240982738239488, 5387620491369119744, 2693810245684559872, 1346905122842279936, 9896824598275883008, 14171784335992684544, 7085892167996342272, 12766318120852914176]

/-- Chunk 7 of the 408 distinct tail words of the background, cells 16 to 63 in place. -/
def wordsL12P102_7 : List Nat := [6383159060426457088, 12414951567067971584, 6207475783533985792, 3103737891766992896, 17680945174434611200, 18063844624072048640, 9031922312036024320, 13739333192872755200, 6869666596436377600, 12658205335072931840, 6329102667536465920, 12387923370622976000, 6193961685311488000, 12320352879510487040, 15383548476609986560, 16915146275159736320, 382899449637437440, 9414821761673461760, 4707410880836730880, 11577077477273108480, 5788538738636554240, 12117641406173020160, 6058820703086510080, 12252782388397998080, 6126391194198999040, 3063195597099499520, 1531597798549749760, 765798899274874880, 10185125360355835904, 14315934717032660992, 7157967358516330496, 12802355716112908288]

/-- Chunk 8 of the 408 distinct tail words of the background, cells 16 to 63 in place. -/
def wordsL12P102_8 : List Nat := [6401177858056454144, 12423960965882970112, 6211980482941485056, 12329362278325485568, 15388053176017485824, 7694026588008742912, 3847013294004371456, 1923506647002185728, 6437215453316448256, 12441979763512967168, 6220989881756483584, 12333866977732984832, 6166933488866492416, 12306838781287989248, 6153419390643994624, 3076709695321997312, 10761726884515741696, 14604235479112613888, 7302117739556306944, 12874430906632896512, 6293065072276471808, 12369904572992978944, 6184952286496489472, 12315848180102987776, 6157924090051493888, 12302334081880489984, 15374539077794988032, 16910641575752237056, 8455320787876118528, 13451032430792802304, 6725516215396401152, 12586130144552943616]

/-- Chunk 9 of the 408 distinct tail words of the background, cells 16 to 63 in place. -/
def wordsL12P102_9 : List Nat := [6076839500716507136, 12261791787212996608, 6130895893606498304, 12288819983657992192, 6144409991828996096, 3072204995914498048, 1536102497957249024, 9991423285833367552, 4995711642916683776, 11721227858313084928, 5860613929156542464, 12153679001433014272, 6257027477016477696, 12351885775362981888, 6175942887681490944, 12311343480695488512, 15379043777202487296, 7689521888601243648, 13068132981155364864, 15757438527432425472, 7878719263716212736, 13162731668712849408, 6581365834356424704, 12514054954032955392, 6094858298346504192, 12270801186027995136, 6135400593013997568, 3067700296506998784, 10757222185108242432, 5378611092554121216, 2689305546277060608, 10568024809993273344]

/-- Chunk 10 of the 408 distinct tail words of the background, cells 16 to 63 in place. -/
def wordsL12P102_10 : List Nat := [5284012404996636672, 11865378239353061376, 5932689119676530688, 12189716596693008384, 6338112066351464448, 12392428070030475264, 15419586071869980672, 16933165072789733376, 17689954573249609728, 18068349323479547904, 18257546698594516992, 18352145386152001536, 9176072693076000768, 13811408383392743424, 6905704191696371712, 12676224132702928896, 6054316003679010816, 3027158001839505408, 1513579000919752704, 756789500459876352, 378394750229938176, 189197375114969088, 94598687557484544, 9270671380633485312, 4635335690316742656, 11541039882013114368, 5770519941006557184, 12108632007358021632, 15424090771277479936, 7712045385638739968, 3856022692819369984, 1928011346409684992]

/-- Chunk 11 of the 408 distinct tail words of the background, cells 16 to 63 in place. -/
def wordsL12P102_11 : List Nat := [964005673204842496, 482002836602421248, 9464373455155953664, 13955558764432719872, 6977779382216359936, 12712261727962923008, 6356130863981461504, 12401437468845473792, 10743708086885744640, 14595226080297615360, 7297613040148807680, 3648806520074403840, 1824403260037201920, 10135573666873344000, 5067786833436672000, 11757265453573079040, 5878632726786539520, 12162688400248012800, 6081344200124006400, 3040672100062003200, 8482348984321114112, 13464546529015300096, 15955645301362393088, 7977822650681196544, 13212283362195341312, 15829513717952413696, 7914756858976206848, 13180750466342846464, 6590375233171423232, 12518559653440454656, 15482651863574970368, 16964697968642228224]

/-- Chunk 12 of the 408 distinct tail words of the background, cells 16 to 63 in place. -/
def wordsL12P102_12 : List Nat := [4982197544694185984, 2491098772347092992, 10468921423028289536, 5234460711514144768, 2617230355757072384, 10531987214733279232, 5265993607366639616, 11856368840538062848, 5928184420269031424, 2964092210134515712, 1482046105067257856, 9964395089388371968, 17149390644349698048, 17798067359029592064, 18122405716369539072, 18284574895039512576, 18365659484374499328, 18406201779041992704, 9203100889520996352, 13824922481615241216, 16135833277662363648, 8067916638831181824, 13257330356270333952, 15852037214989910016]

/-- The chunks of tail words. -/
def wordsL12P102 : List (List Nat) := [wordsL12P102_0, wordsL12P102_1, wordsL12P102_2, wordsL12P102_3, wordsL12P102_4, wordsL12P102_5, wordsL12P102_6, wordsL12P102_7, wordsL12P102_8, wordsL12P102_9, wordsL12P102_10, wordsL12P102_11, wordsL12P102_12]

/-- Row `a`, entry `o`: the index of the tail word at the alignment `(a, o)`. -/
def rowsL12P102 : List (List Nat) := [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], [12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23], [24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35], [36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59], [60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71], [72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83], [84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95], [96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107], [108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119], [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131], [132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143], [144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155], [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167], [168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179], [180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191], [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203], [204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215], [216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227], [228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239], [240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251], [252, 253, 254, 255, 256, 257, 258, 259, 260, 261, 262, 263], [264, 265, 266, 267, 268, 269, 270, 271, 272, 273, 274, 275], [276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287], [288, 289, 290, 291, 292, 293, 294, 295, 296, 297, 298, 299], [300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 310, 311], [312, 313, 314, 315, 316, 317, 318, 319, 320, 321, 322, 323], [324, 325, 326, 327, 328, 329, 330, 331, 332, 333, 334, 335], [336, 337, 338, 339, 340, 341, 342, 343, 344, 345, 346, 347], [348, 349, 350, 351, 352, 353, 354, 355, 356, 357, 358, 359], [360, 361, 362, 363, 364, 365, 366, 367, 368, 369, 370, 371], [372, 373, 374, 375, 376, 377, 378, 379, 380, 381, 382, 383], [384, 385, 386, 387, 388, 389, 390, 391, 392, 393, 394, 395], [396, 397, 398, 399, 400, 401, 402, 403, 404, 405, 406, 407], [4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3], [16, 17, 18, 19, 20, 21, 22, 23, 12, 13, 14, 15], [28, 29, 30, 31, 32, 33, 34, 35, 24, 25, 26, 27], [40, 41, 42, 43, 44, 45, 46, 47, 36, 37, 38, 39], [52, 53, 54, 55, 56, 57, 58, 59, 48, 49, 50, 51], [64, 65, 66, 67, 68, 69, 70, 71, 60, 61, 62, 63], [76, 77, 78, 79, 80, 81, 82, 83, 72, 73, 74, 75], [88, 89, 90, 91, 92, 93, 94, 95, 84, 85, 86, 87], [100, 101, 102, 103, 104, 105, 106, 107, 96, 97, 98, 99], [112, 113, 114, 115, 116, 117, 118, 119, 108, 109, 110, 111], [124, 125, 126, 127, 128, 129, 130, 131, 120, 121, 122, 123], [136, 137, 138, 139, 140, 141, 142, 143, 132, 133, 134, 135], [148, 149, 150, 151, 152, 153, 154, 155, 144, 145, 146, 147], [160, 161, 162, 163, 164, 165, 166, 167, 156, 157, 158, 159], [172, 173, 174, 175, 176, 177, 178, 179, 168, 169, 170, 171], [184, 185, 186, 187, 188, 189, 190, 191, 180, 181, 182, 183], [196, 197, 198, 199, 200, 201, 202, 203, 192, 193, 194, 195], [208, 209, 210, 211, 212, 213, 214, 215, 204, 205, 206, 207], [220, 221, 222, 223, 224, 225, 226, 227, 216, 217, 218, 219], [232, 233, 234, 235, 236, 237, 238, 239, 228, 229, 230, 231], [244, 245, 246, 247, 248, 249, 250, 251, 240, 241, 242, 243], [256, 257, 258, 259, 260, 261, 262, 263, 252, 253, 254, 255], [268, 269, 270, 271, 272, 273, 274, 275, 264, 265, 266, 267], [280, 281, 282, 283, 284, 285, 286, 287, 276, 277, 278, 279], [292, 293, 294, 295, 296, 297, 298, 299, 288, 289, 290, 291], [304, 305, 306, 307, 308, 309, 310, 311, 300, 301, 302, 303], [316, 317, 318, 319, 320, 321, 322, 323, 312, 313, 314, 315], [328, 329, 330, 331, 332, 333, 334, 335, 324, 325, 326, 327], [340, 341, 342, 343, 344, 345, 346, 347, 336, 337, 338, 339], [352, 353, 354, 355, 356, 357, 358, 359, 348, 349, 350, 351], [364, 365, 366, 367, 368, 369, 370, 371, 360, 361, 362, 363], [376, 377, 378, 379, 380, 381, 382, 383, 372, 373, 374, 375], [388, 389, 390, 391, 392, 393, 394, 395, 384, 385, 386, 387], [400, 401, 402, 403, 404, 405, 406, 407, 396, 397, 398, 399], [8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7], [20, 21, 22, 23, 12, 13, 14, 15, 16, 17, 18, 19], [32, 33, 34, 35, 24, 25, 26, 27, 28, 29, 30, 31], [44, 45, 46, 47, 36, 37, 38, 39, 40, 41, 42, 43], [56, 57, 58, 59, 48, 49, 50, 51, 52, 53, 54, 55], [68, 69, 70, 71, 60, 61, 62, 63, 64, 65, 66, 67], [80, 81, 82, 83, 72, 73, 74, 75, 76, 77, 78, 79], [92, 93, 94, 95, 84, 85, 86, 87, 88, 89, 90, 91], [104, 105, 106, 107, 96, 97, 98, 99, 100, 101, 102, 103], [116, 117, 118, 119, 108, 109, 110, 111, 112, 113, 114, 115], [128, 129, 130, 131, 120, 121, 122, 123, 124, 125, 126, 127], [140, 141, 142, 143, 132, 133, 134, 135, 136, 137, 138, 139], [152, 153, 154, 155, 144, 145, 146, 147, 148, 149, 150, 151], [164, 165, 166, 167, 156, 157, 158, 159, 160, 161, 162, 163], [176, 177, 178, 179, 168, 169, 170, 171, 172, 173, 174, 175], [188, 189, 190, 191, 180, 181, 182, 183, 184, 185, 186, 187], [200, 201, 202, 203, 192, 193, 194, 195, 196, 197, 198, 199], [212, 213, 214, 215, 204, 205, 206, 207, 208, 209, 210, 211], [224, 225, 226, 227, 216, 217, 218, 219, 220, 221, 222, 223], [236, 237, 238, 239, 228, 229, 230, 231, 232, 233, 234, 235], [248, 249, 250, 251, 240, 241, 242, 243, 244, 245, 246, 247], [260, 261, 262, 263, 252, 253, 254, 255, 256, 257, 258, 259], [272, 273, 274, 275, 264, 265, 266, 267, 268, 269, 270, 271], [284, 285, 286, 287, 276, 277, 278, 279, 280, 281, 282, 283], [296, 297, 298, 299, 288, 289, 290, 291, 292, 293, 294, 295], [308, 309, 310, 311, 300, 301, 302, 303, 304, 305, 306, 307], [320, 321, 322, 323, 312, 313, 314, 315, 316, 317, 318, 319], [332, 333, 334, 335, 324, 325, 326, 327, 328, 329, 330, 331], [344, 345, 346, 347, 336, 337, 338, 339, 340, 341, 342, 343], [356, 357, 358, 359, 348, 349, 350, 351, 352, 353, 354, 355], [368, 369, 370, 371, 360, 361, 362, 363, 364, 365, 366, 367], [380, 381, 382, 383, 372, 373, 374, 375, 376, 377, 378, 379], [392, 393, 394, 395, 384, 385, 386, 387, 388, 389, 390, 391], [404, 405, 406, 407, 396, 397, 398, 399, 400, 401, 402, 403]]

theorem tablesL12P102_ok : tabOK 12 13 wordsL12P102 statesL12P102 rowsL12P102 = true := by
  decide +kernel

theorem ktreeL12P102_0 : wordsOK 24 wordsL12P102_0 = true := by
  decide +kernel

theorem ktreeL12P102_1 : wordsOK 24 wordsL12P102_1 = true := by
  decide +kernel

theorem ktreeL12P102_2 : wordsOK 24 wordsL12P102_2 = true := by
  decide +kernel

theorem ktreeL12P102_3 : wordsOK 24 wordsL12P102_3 = true := by
  decide +kernel

theorem ktreeL12P102_4 : wordsOK 24 wordsL12P102_4 = true := by
  decide +kernel

theorem ktreeL12P102_5 : wordsOK 24 wordsL12P102_5 = true := by
  decide +kernel

theorem ktreeL12P102_6 : wordsOK 24 wordsL12P102_6 = true := by
  decide +kernel

theorem ktreeL12P102_7 : wordsOK 24 wordsL12P102_7 = true := by
  decide +kernel

theorem ktreeL12P102_8 : wordsOK 24 wordsL12P102_8 = true := by
  decide +kernel

theorem ktreeL12P102_9 : wordsOK 24 wordsL12P102_9 = true := by
  decide +kernel

theorem ktreeL12P102_10 : wordsOK 24 wordsL12P102_10 = true := by
  decide +kernel

theorem ktreeL12P102_11 : wordsOK 24 wordsL12P102_11 = true := by
  decide +kernel

theorem ktreeL12P102_12 : wordsOK 24 wordsL12P102_12 = true := by
  decide +kernel

theorem ktreeL12P102 (c : Nat) (hc : c < 13) : wordsOK 24 (wordsL12P102.getD c []) = true :=
  match c, hc with
  | 0, _ => ktreeL12P102_0
  | 1, _ => ktreeL12P102_1
  | 2, _ => ktreeL12P102_2
  | 3, _ => ktreeL12P102_3
  | 4, _ => ktreeL12P102_4
  | 5, _ => ktreeL12P102_5
  | 6, _ => ktreeL12P102_6
  | 7, _ => ktreeL12P102_7
  | 8, _ => ktreeL12P102_8
  | 9, _ => ktreeL12P102_9
  | 10, _ => ktreeL12P102_10
  | 11, _ => ktreeL12P102_11
  | 12, _ => ktreeL12P102_12
  | c + 13, hc => absurd hc (by omega)

/-- **No point of `K` has the background `100100000000` from a cell `p ≤ 16` on**, at any alignment `(a, o)`. -/
theorem no_k_tail16_L12P102 (u : Nat → Bool) (a o p : Nat) (hp : p ≤ 16)
    (hu : ∀ j, p ≤ j → u j = ringCell statesL12P102 12 a (j + o)) : ¬ InK u :=
  not_inK_of_tree statesL12P102 12 102 24 wordsL12P102 rowsL12P102 13 (by decide) (by decide +kernel)
    (by decide) (by decide) tablesL12P102_ok ktreeL12P102 u a o p hp hu

end Rule30Open
