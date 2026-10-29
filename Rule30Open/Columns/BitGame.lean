module

public import Rule30Open.Columns.GameBlocks
public import Ruliology.CellularAutomata.Rule30ZeroBoundaryLanes

/-!
# The finite game decided in the kernel, without a certificate

[The finite game](FiniteGame.md) keeps the cells `k + 1, …, k + K` right of a column that repeats a block, with the
cell beyond them free at each step, and excludes the block when, along every play, the column left of `k` ends up
repeating. `GameMask` checks a stored certificate node by node. Here the kernel decides the same kind of question
from the block alone, on truth tables: a set of nodes is one number with one bit per node, the nodes of all phases
side by side, and one step of the game acts on all of them at once through a few dozen shifts and masks.

* **Image and preimage** (`post`, `pre`, `post_sound`, `pre_sound`). With the column cell and the free cell added to the
  index, one step is a bijection on `K + 2` index bits, a product of `K` flips of one index bit by two others (Rule 30
  is permutive in its left cell). Composing a truth table with such a flip is a delta swap (`ds`), so the image of a
  set is `K` delta swaps, two projections and `K` swaps that rotate the index bits back.
* **The decision** (`gameCheck`). After `D` steps every play lies in the image of everything `D` times over. At each
  phase, split that set by the value of the column left of `k`; keep only the nodes of each value that can reach and be
  reached from nodes of the other value, and repeat. If one side empties, no play visits both values at that phase
  forever, so the column left of `k` is eventually constant there (`refine_sound`).
* `bitGame_column`: no column of the orbit of a row with a leftmost 1 repeats a block for which `gameCheck` succeeds,
  from any time on and in any rotation.

The natural-language argument is `BitGame.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

open Ruliology.CellularAutomata

namespace BitGame

/-! ### Delta swaps -/

/-- The delta swap: the bit at each position `g` of `M` trades places with the bit at `g + d`. -/
def ds (T M d : Nat) : Nat :=
  Nat.xor (Nat.xor T (Nat.land (Nat.xor (Nat.shiftRight T d) T) M))
    (Nat.shiftLeft (Nat.land (Nat.xor (Nat.shiftRight T d) T) M) d)

/-- **The delta swap**, when no two positions of `M` are `d` apart. -/
theorem ds_spec (T M d g : Nat) (hM : ∀ g, M.testBit g = true → d ≤ g → M.testBit (g - d) = false) :
    (ds T M d).testBit g = if M.testBit g then T.testBit (g + d)
      else if d ≤ g ∧ M.testBit (g - d) = true then T.testBit (g - d) else T.testBit g := by
  show (T ^^^ (((T >>> d) ^^^ T) &&& M) ^^^ ((((T >>> d) ^^^ T) &&& M) <<< d)).testBit g = _
  simp only [Nat.testBit_xor, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_shiftLeft]
  by_cases hg : M.testBit g = true
  · have e : (decide (g ≥ d) && ((T.testBit (d + (g - d)) ^^ T.testBit (g - d)) && M.testBit (g - d))) = false := by
      by_cases hd : d ≤ g
      · rw [hM g hg hd]; simp
      · simp [hd]
    rw [e, hg, Nat.add_comm d g]
    simp only [Bool.and_true, Bool.xor_false, ite_true]
    cases T.testBit g <;> cases T.testBit (g + d) <;> rfl
  · have hg' : M.testBit g = false := by simpa using hg
    rw [hg']
    simp only [Bool.and_false, Bool.xor_false, Bool.false_eq_true, ite_false]
    by_cases hd : d ≤ g
    · rw [show d + (g - d) = g by omega]
      cases hm : M.testBit (g - d)
      · simp
      · simp [hd]
    · simp [hd]

/-! ### Patterns -/

/-- `n` copies of the `B`-bit number `X`, side by side. -/
def rep (B X : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => Nat.lor (rep B X n) (Nat.shiftLeft X (Nat.mul n B))

theorem rep_testBit (B X : Nat) (hX : X < 2 ^ B) :
    ∀ n g, (rep B X n).testBit g = (decide (g < n * B) && X.testBit (g % B)) := by
  intro n
  induction n with
  | zero => intro g; simp [rep]
  | succ n ih =>
    intro g
    show (rep B X n ||| (X <<< (n * B))).testBit g = _
    rw [Nat.testBit_or, ih, Nat.testBit_shiftLeft]
    by_cases h1 : g < n * B
    · have : ¬ g ≥ n * B := by omega
      simp [h1, this, show g < (n + 1) * B by rw [Nat.succ_mul]; omega]
    · by_cases h2 : g < (n + 1) * B
      · have hm : g % B = g - n * B := by
          have hB : 0 < B := by rw [Nat.succ_mul] at h2; omega
          rw [show g = g - n * B + n * B by omega, Nat.add_mul_mod_self_right,
            Nat.mod_eq_of_lt (by rw [Nat.succ_mul] at h2; omega)]
          omega
        simp [h1, h2, show g ≥ n * B by omega, hm]
      · have hlt : X.testBit (g - n * B) = false :=
          Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hX (Nat.pow_le_pow_right (by decide) (by
            rw [Nat.succ_mul] at h2; omega)))
        simp [h1, h2, hlt]

/-- Bit `q` of the kit's lane pattern `pat n s` is bit `s` of `q`, below `2 ^ n`. -/
theorem pat_testBit (n s q : Nat) (hs : s < n) :
    (Rule30ZeroBoundaryLanes.pat n s).testBit q = (decide (q < 2 ^ n) && q.testBit s) := by
  have base : ∀ q, (Nat.shiftLeft (Nat.sub (Nat.pow 2 (Nat.pow 2 s)) 1) (Nat.pow 2 s)).testBit q =
      (decide (q < 2 ^ (s + 1)) && q.testBit s) := by
    intro q
    show ((2 ^ 2 ^ s - 1) <<< 2 ^ s).testBit q = _
    rw [Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
    have h2 : 2 ^ (s + 1) = 2 ^ s + 2 ^ s := by rw [Nat.pow_succ]; omega
    by_cases hq : q < 2 ^ (s + 1)
    · rw [Rule30ZeroBoundaryLanes.testBit_low_block s q hq]
      by_cases h : 2 ^ s ≤ q
      · simp [h, hq, show q - 2 ^ s < 2 ^ s by omega]
      · simp [h, hq]
    · simp [hq, show ¬ q - 2 ^ s < 2 ^ s by omega]
  have := Rule30ZeroBoundaryLanes.dbl_spec s (n - (s + 1)) _ (s + 1) (by omega) base q
  unfold Rule30ZeroBoundaryLanes.pat
  rw [show Nat.pow 2 (s + 1) = 2 ^ (s + 1) from rfl, this, show s + 1 + (n - (s + 1)) = n by omega]

theorem pat_lt (n s : Nat) (hs : s < n) : Rule30ZeroBoundaryLanes.pat n s < 2 ^ 2 ^ n :=
  Nat.lt_pow_two_of_testBit _ fun i hi => by
    rw [pat_testBit n s i hs, decide_eq_false (by omega), Bool.false_and]

/-! ### One index bit, flipped -/

theorem testBit_xor_two_pow (g t j : Nat) : (g ^^^ 2 ^ t).testBit j = (g.testBit j ^^ decide (t = j)) := by
  rw [Nat.testBit_xor, Nat.testBit_two_pow]

theorem xor_two_pow_of_false {g t : Nat} (h : g.testBit t = false) : g ^^^ 2 ^ t = g + 2 ^ t := by
  have hm : g % 2 ^ (t + 1) < 2 ^ t := by
    refine Classical.byContradiction fun hc => ?_
    have := Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt (Nat.le_of_not_lt hc) (Nat.mod_lt _ (Nat.two_pow_pos _))
    rw [Nat.testBit_mod_two_pow, decide_eq_true (Nat.lt_succ_self t), Bool.true_and, h] at this
    exact Bool.noConfusion this
  have h2 : 2 ^ (t + 1) = 2 * 2 ^ t := by rw [Nat.pow_succ]; omega
  have hsplit : g + 2 ^ t = 2 ^ (t + 1) * (g / 2 ^ (t + 1)) + (2 ^ t + g % 2 ^ (t + 1)) := by
    have := Nat.div_add_mod g (2 ^ (t + 1)); omega
  have hsplit' : g = 2 ^ (t + 1) * (g / 2 ^ (t + 1)) + g % 2 ^ (t + 1) := (Nat.div_add_mod g _).symm
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_xor_two_pow, hsplit, Nat.testBit_two_pow_mul_add _ (by omega)]
  conv => lhs; rw [hsplit', Nat.testBit_two_pow_mul_add _ (Nat.mod_lt _ (Nat.two_pow_pos _))]
  by_cases hj : j < t + 1
  · rw [ite_eq_left hj, ite_eq_left hj]
    by_cases hjt : j = t
    · subst hjt
      rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hm]
      simp
    · rw [Nat.testBit_two_pow_add_gt (by omega), decide_eq_false (Ne.symm hjt), Bool.xor_false]
  · rw [ite_eq_right hj, ite_eq_right hj, decide_eq_false (by omega), Bool.xor_false]

theorem xor_two_pow_of_true {g t : Nat} (h : g.testBit t = true) : g ^^^ 2 ^ t = g - 2 ^ t := by
  have hle : 2 ^ t ≤ g := Nat.ge_two_pow_of_testBit h
  have hm : 2 ^ t ≤ g % 2 ^ (t + 1) := by
    refine Classical.byContradiction fun hc => ?_
    have := Nat.testBit_lt_two_pow (Nat.lt_of_not_le hc)
    rw [Nat.testBit_mod_two_pow, decide_eq_true (Nat.lt_succ_self t), Bool.true_and, h] at this
    exact Bool.noConfusion this
  have h2 : 2 ^ (t + 1) = 2 * 2 ^ t := by rw [Nat.pow_succ]; omega
  have hlt : g % 2 ^ (t + 1) < 2 ^ (t + 1) := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hsplit : g - 2 ^ t = 2 ^ (t + 1) * (g / 2 ^ (t + 1)) + (g % 2 ^ (t + 1) - 2 ^ t) := by
    have := Nat.div_add_mod g (2 ^ (t + 1)); omega
  have hf : (g - 2 ^ t).testBit t = false := by
    rw [hsplit, Nat.testBit_two_pow_mul_add _ (by omega), ite_eq_left (Nat.lt_succ_self t)]
    exact Nat.testBit_lt_two_pow (by omega)
  have e := xor_two_pow_of_false hf
  rw [show g - 2 ^ t + 2 ^ t = g by omega] at e
  calc g ^^^ 2 ^ t = ((g - 2 ^ t) ^^^ 2 ^ t) ^^^ 2 ^ t := by rw [e]
    _ = g - 2 ^ t := by rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

/-- Below a position whose bit `t` is clear, by `2 ^ t`, bit `t` is set: the borrow. -/
theorem testBit_sub_two_pow_of_false {g t : Nat} (h : g.testBit t = false) (hle : 2 ^ t ≤ g) :
    (g - 2 ^ t).testBit t = true := by
  cases h' : (g - 2 ^ t).testBit t
  · have e := xor_two_pow_of_false h'
    rw [show g - 2 ^ t + 2 ^ t = g by omega] at e
    have := congrArg (fun x => x.testBit t) e
    simp only [testBit_xor_two_pow, h', h] at this
    simp at this
  · rfl

theorem xor_two_pow_lt {g t n : Nat} (ht : t < n) (P : Nat) (hg : g < P * 2 ^ n) : g ^^^ 2 ^ t < P * 2 ^ n := by
  cases hb : g.testBit t
  · rw [xor_two_pow_of_false hb]
    have hlow : g % 2 ^ n ^^^ 2 ^ t < 2 ^ n :=
      Nat.xor_lt_two_pow (Nat.mod_lt _ (Nat.two_pow_pos _)) (Nat.pow_lt_pow_right (by decide) ht)
    have hb' : (g % 2 ^ n).testBit t = false := by rw [Nat.testBit_mod_two_pow, hb, Bool.and_false]
    rw [xor_two_pow_of_false hb'] at hlow
    have hdm := Nat.div_add_mod g (2 ^ n)
    have hq : g / 2 ^ n + 1 ≤ P := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hg)
    have hmul : 2 ^ n * (g / 2 ^ n + 1) ≤ 2 ^ n * P := Nat.mul_le_mul_left _ hq
    rw [Nat.mul_succ] at hmul
    rw [Nat.mul_comm P]
    omega
  · have hp := Nat.two_pow_pos t
    rw [xor_two_pow_of_true hb]; omega

/-! ### Tables of `P` blocks -/

/-- Every position of `P` blocks of `2 ^ (K + 2)` bits. -/
def full (P K : Nat) : Nat := Nat.sub (Nat.pow 2 (Nat.mul P (Nat.pow 2 (K + 2)))) 1

theorem full_testBit (P K g : Nat) : (full P K).testBit g = decide (g < P * 2 ^ (K + 2)) := by
  show (2 ^ (P * 2 ^ (K + 2)) - 1).testBit g = _
  rw [Nat.testBit_two_pow_sub_one]

/-- Bit `s` of the index, in every block. -/
def ip (P K s : Nat) : Nat := rep (Nat.pow 2 (K + 2)) (Rule30ZeroBoundaryLanes.pat (K + 2) s) P

theorem ip_testBit (P K s g : Nat) (hs : s < K + 2) :
    (ip P K s).testBit g = (decide (g < P * 2 ^ (K + 2)) && g.testBit s) := by
  unfold ip
  rw [show Nat.pow 2 (K + 2) = 2 ^ (K + 2) from rfl, rep_testBit _ _ (pat_lt _ _ hs), pat_testBit _ _ _ hs,
    Nat.testBit_mod_two_pow, decide_eq_true (Nat.mod_lt _ (Nat.two_pow_pos _)), decide_eq_true hs]
  simp

/-- Bit `s` of the index clear, in every block. -/
def nip (P K s : Nat) : Nat := Nat.xor (full P K) (ip P K s)

theorem nip_testBit (P K s g : Nat) (hs : s < K + 2) :
    (nip P K s).testBit g = (decide (g < P * 2 ^ (K + 2)) && !g.testBit s) := by
  show (full P K ^^^ ip P K s).testBit g = _
  rw [Nat.testBit_xor, full_testBit, ip_testBit _ _ _ _ hs]
  cases decide (g < P * 2 ^ (K + 2)) <;> cases g.testBit s <;> rfl

/-- The positions whose index has bit `t` clear and bit `a` or bit `b` set. -/
def flipMask (P K t a b : Nat) : Nat := Nat.land (nip P K t) (Nat.lor (ip P K a) (ip P K b))

theorem flipMask_testBit (P K t a b g : Nat) (ht : t < K + 2) (ha : a < K + 2) (hb : b < K + 2) :
    (flipMask P K t a b).testBit g =
      (decide (g < P * 2 ^ (K + 2)) && !g.testBit t && (g.testBit a || g.testBit b)) := by
  show (nip P K t &&& (ip P K a ||| ip P K b)).testBit g = _
  rw [Nat.testBit_and, Nat.testBit_or, nip_testBit _ _ _ _ ht, ip_testBit _ _ _ _ ha, ip_testBit _ _ _ _ hb]
  cases decide (g < P * 2 ^ (K + 2)) <;> cases g.testBit t <;> cases g.testBit a <;> cases g.testBit b <;> rfl

/-- The index flip: bit `t` of the index changes when bit `a` or bit `b` is set. -/
def flipIdx (t a b g : Nat) : Nat := if (g.testBit a || g.testBit b) = true then g ^^^ 2 ^ t else g

theorem flipIdx_testBit (t a b g j : Nat) :
    (flipIdx t a b g).testBit j = (g.testBit j ^^ (decide (t = j) && (g.testBit a || g.testBit b))) := by
  unfold flipIdx
  cases h : (g.testBit a || g.testBit b)
  · simp
  · simp [Nat.testBit_two_pow]

theorem flipIdx_lt {P K t a b g : Nat} (ht : t < K + 2) (hg : g < P * 2 ^ (K + 2)) :
    flipIdx t a b g < P * 2 ^ (K + 2) := by
  unfold flipIdx
  split
  · exact xor_two_pow_lt ht P hg
  · exact hg

/-- **A flip, on tables**: composing a table with an index flip is a delta swap. -/
theorem dsFlip_spec (P K t a b T g : Nat) (ht : t < K + 2) (ha : a < K + 2) (hb : b < K + 2) (hta : t ≠ a)
    (htb : t ≠ b) (hg : g < P * 2 ^ (K + 2)) :
    (ds T (flipMask P K t a b) (2 ^ t)).testBit g = T.testBit (flipIdx t a b g) := by
  have hM : ∀ g, (flipMask P K t a b).testBit g = true → 2 ^ t ≤ g →
      (flipMask P K t a b).testBit (g - 2 ^ t) = false := by
    intro g hg1 hle
    rw [flipMask_testBit _ _ _ _ _ _ ht ha hb] at hg1 ⊢
    have h0 : g.testBit t = false := by
      cases h : g.testBit t
      · rfl
      · rw [h] at hg1; simp at hg1
    rw [testBit_sub_two_pow_of_false h0 hle]
    simp
  rw [ds_spec _ _ _ _ hM]
  simp only [flipMask_testBit _ _ _ _ _ _ ht ha hb]
  unfold flipIdx
  have hga : ∀ x : Nat, x.testBit t = true → (x - 2 ^ t).testBit a = x.testBit a := fun x hx => by
    rw [← xor_two_pow_of_true hx, testBit_xor_two_pow, decide_eq_false hta, Bool.xor_false]
  have hgb : ∀ x : Nat, x.testBit t = true → (x - 2 ^ t).testBit b = x.testBit b := fun x hx => by
    rw [← xor_two_pow_of_true hx, testBit_xor_two_pow, decide_eq_false htb, Bool.xor_false]
  cases h0 : g.testBit t
  · -- bit `t` clear: the position moves up when the condition holds
    have hgt : decide (g < P * 2 ^ (K + 2)) = true := decide_eq_true hg
    cases hc : (g.testBit a || g.testBit b)
    · have hsecond : ¬ (2 ^ t ≤ g ∧ (decide (g - 2 ^ t < P * 2 ^ (K + 2)) && !(g - 2 ^ t).testBit t &&
          ((g - 2 ^ t).testBit a || (g - 2 ^ t).testBit b)) = true) := by
        rintro ⟨hle, h2⟩
        rw [testBit_sub_two_pow_of_false h0 hle] at h2
        simp at h2
      simp only [hgt, Bool.not_false, Bool.true_and, Bool.false_eq_true, ite_false]
      rw [ite_eq_right hsecond]
    · simp only [hgt, Bool.not_false, Bool.true_and, ite_true]
      rw [xor_two_pow_of_false h0]
  · -- bit `t` set: the position moves down when the condition holds
    have hle : 2 ^ t ≤ g := Nat.ge_two_pow_of_testBit h0
    have hlow : (g - 2 ^ t).testBit t = false := by
      rw [← xor_two_pow_of_true h0, testBit_xor_two_pow, h0]; simp
    have hlt : decide (g - 2 ^ t < P * 2 ^ (K + 2)) = true := decide_eq_true (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hg)
    simp only [Bool.not_true, Bool.and_false, Bool.false_and, Bool.false_eq_true, ite_false, hlow, hlt,
      Bool.not_false, Bool.true_and, hga g h0, hgb g h0]
    cases hc : (g.testBit a || g.testBit b)
    · simp
    · simp [hle, xor_two_pow_of_true h0]

/-! ### Lists of flips -/

/-- A flip `(t, a, b)` is valid at width `K` when its three index bits are below `K + 2` and `t` is neither of the
others. -/
def ValidFlip (K : Nat) (f : Nat × Nat × Nat) : Prop :=
  f.1 < K + 2 ∧ f.2.1 < K + 2 ∧ f.2.2 < K + 2 ∧ f.1 ≠ f.2.1 ∧ f.1 ≠ f.2.2

/-- The table composed with the flips of a list, the first one innermost: `T ∘ f₁ ∘ f₂ ∘ ⋯`. -/
def applyFlips (P K : Nat) (T : Nat) : List (Nat × Nat × Nat) → Nat
  | [] => T
  | f :: rest => applyFlips P K (ds T (flipMask P K f.1 f.2.1 f.2.2) (2 ^ f.1)) rest

/-- The index map of a list of flips: `f₁ (f₂ (⋯ g))`. -/
def idxFlips : List (Nat × Nat × Nat) → Nat → Nat
  | [], g => g
  | f :: rest, g => flipIdx f.1 f.2.1 f.2.2 (idxFlips rest g)

theorem idxFlips_lt {P K : Nat} : ∀ (fs : List (Nat × Nat × Nat)), (∀ f ∈ fs, ValidFlip K f) →
    ∀ g, g < P * 2 ^ (K + 2) → idxFlips fs g < P * 2 ^ (K + 2)
  | [], _, _, hg => hg
  | f :: rest, hv, g, hg => flipIdx_lt (hv f (List.mem_cons_self ..)).1
      (idxFlips_lt rest (fun f' hf' => hv f' (List.mem_cons_of_mem _ hf')) g hg)

theorem applyFlips_spec (P K : Nat) : ∀ (fs : List (Nat × Nat × Nat)) (T : Nat), (∀ f ∈ fs, ValidFlip K f) →
    ∀ g, g < P * 2 ^ (K + 2) → (applyFlips P K T fs).testBit g = T.testBit (idxFlips fs g)
  | [], _, _, _, _ => rfl
  | f :: rest, T, hv, g, hg => by
    have hf := hv f (List.mem_cons_self ..)
    have hrest : ∀ f' ∈ rest, ValidFlip K f' := fun f' hf' => hv f' (List.mem_cons_of_mem _ hf')
    show (applyFlips P K (ds T (flipMask P K f.1 f.2.1 f.2.2) (2 ^ f.1)) rest).testBit g = _
    rw [applyFlips_spec P K rest _ hrest g hg,
      dsFlip_spec P K _ _ _ T _ hf.1 hf.2.1 hf.2.2.1 hf.2.2.2.1 hf.2.2.2.2 (idxFlips_lt rest hrest g hg)]
    rfl

/-! ### Projections, the canonical form and the blocks -/

/-- The table made symmetric in index bit `p`: the OR over its two values. -/
def proj (P K T p : Nat) : Nat :=
  Nat.lor (Nat.lor T (Nat.land (Nat.shiftRight T (2 ^ p)) (nip P K p)))
    (Nat.shiftLeft (Nat.land T (nip P K p)) (2 ^ p))

theorem proj_testBit (P K T p g : Nat) (hp : p < K + 2) (hg : g < P * 2 ^ (K + 2)) :
    (proj P K T p).testBit g = (T.testBit g || T.testBit (g ^^^ 2 ^ p)) := by
  show ((T ||| ((T >>> 2 ^ p) &&& nip P K p)) ||| ((T &&& nip P K p) <<< 2 ^ p)).testBit g = _
  simp only [Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_shiftLeft,
    nip_testBit _ _ _ _ hp]
  cases h0 : g.testBit p
  · have hge : ¬ (2 ^ p ≤ g ∧ (g - 2 ^ p).testBit p = false) := fun ⟨hle, hf⟩ => by
      rw [testBit_sub_two_pow_of_false h0 hle] at hf; exact Bool.noConfusion hf
    rw [xor_two_pow_of_false h0, Nat.add_comm (2 ^ p) g]
    by_cases hle : 2 ^ p ≤ g
    · have hb : (g - 2 ^ p).testBit p = true := testBit_sub_two_pow_of_false h0 hle
      simp [hg, hb]
    · simp [hg, show ¬ g ≥ 2 ^ p by omega]
  · have hle : 2 ^ p ≤ g := Nat.ge_two_pow_of_testBit h0
    have hlow : (g - 2 ^ p).testBit p = false := by
      rw [← xor_two_pow_of_true h0, testBit_xor_two_pow, h0]; simp
    rw [xor_two_pow_of_true h0, show 2 ^ p + g = g + 2 ^ p by omega]
    simp [hle, hlow, Nat.lt_of_le_of_lt (Nat.sub_le g (2 ^ p)) hg]

/-- The slice of each block with index bits `K` and `K + 1` clear, copied to the other three slices. -/
def canon (P K T : Nat) : Nat := proj P K (proj P K (Nat.land (Nat.land T (nip P K K)) (nip P K (K + 1))) K) (K + 1)

/-- Index bit `p` cleared. -/
def clr (p g : Nat) : Nat := if g.testBit p = true then g ^^^ 2 ^ p else g

theorem clr_testBit (p g j : Nat) : (clr p g).testBit j = (g.testBit j && !decide (p = j)) := by
  unfold clr
  cases h : g.testBit p
  · simp only [Bool.false_eq_true, ite_false]
    by_cases hj : p = j
    · subst hj; simp [h]
    · simp [hj]
  · simp only [ite_true, testBit_xor_two_pow]
    by_cases hj : p = j
    · subst hj; simp [h]
    · simp [hj]

theorem clr_lt {P K p g : Nat} (hp : p < K + 2) (hg : g < P * 2 ^ (K + 2)) : clr p g < P * 2 ^ (K + 2) := by
  unfold clr
  split
  · exact xor_two_pow_lt hp P hg
  · exact hg

/-- Projecting a table that lives where index bit `p` is clear reads it with bit `p` cleared. -/
theorem proj_clear (P K X p g : Nat) (hp : p < K + 2) (hg : g < P * 2 ^ (K + 2))
    (hX : ∀ h, h < P * 2 ^ (K + 2) → X.testBit h = true → h.testBit p = false) :
    (proj P K X p).testBit g = X.testBit (clr p g) := by
  rw [proj_testBit _ _ _ _ _ hp hg]
  unfold clr
  cases h0 : g.testBit p
  · have : X.testBit (g ^^^ 2 ^ p) = false := by
      cases hx : X.testBit (g ^^^ 2 ^ p)
      · rfl
      · have := hX _ (xor_two_pow_lt hp P hg) hx
        rw [testBit_xor_two_pow, h0] at this
        simp at this
    simp [this]
  · have : X.testBit g = false := by
      cases hx : X.testBit g
      · rfl
      · have := hX _ hg hx; rw [h0] at this; exact absurd this (by decide)
    simp [this]

theorem clr_self (p g : Nat) : (clr p g).testBit p = false := by
  rw [clr_testBit]; simp

theorem clr_other {p q g : Nat} (h : p ≠ q) : (clr p g).testBit q = g.testBit q := by
  rw [clr_testBit, decide_eq_false h, Bool.not_false, Bool.and_true]

theorem canon_testBit (P K T g : Nat) (hg : g < P * 2 ^ (K + 2)) :
    (canon P K T).testBit g = T.testBit (clr K (clr (K + 1) g)) := by
  have hK : K < K + 2 := by omega
  have hK1 : K + 1 < K + 2 := by omega
  have hne : K ≠ K + 1 := by omega
  let X0 := Nat.land (Nat.land T (nip P K K)) (nip P K (K + 1))
  have hX0 : ∀ h, h < P * 2 ^ (K + 2) → X0.testBit h = (T.testBit h && !h.testBit K && !h.testBit (K + 1)) :=
    fun h hh => by
      show (T &&& nip P K K &&& nip P K (K + 1)).testBit h = _
      rw [Nat.testBit_and, Nat.testBit_and, nip_testBit _ _ _ _ hK, nip_testBit _ _ _ _ hK1, decide_eq_true hh]
      cases T.testBit h <;> cases h.testBit K <;> cases h.testBit (K + 1) <;> rfl
  have s1 : ∀ h, h < P * 2 ^ (K + 2) → X0.testBit h = true → h.testBit K = false := fun h hh hx => by
    rw [hX0 h hh] at hx
    cases hk : h.testBit K
    · rfl
    · rw [hk] at hx; simp at hx
  have hX1 : ∀ h, h < P * 2 ^ (K + 2) → (proj P K X0 K).testBit h = X0.testBit (clr K h) := fun h hh =>
    proj_clear _ _ _ _ _ hK hh s1
  have s2 : ∀ h, h < P * 2 ^ (K + 2) → (proj P K X0 K).testBit h = true → h.testBit (K + 1) = false :=
    fun h hh hx => by
      rw [hX1 h hh, hX0 _ (clr_lt hK hh), clr_other hne] at hx
      cases hk : h.testBit (K + 1)
      · rfl
      · rw [hk] at hx; simp at hx
  show (proj P K (proj P K X0 K) (K + 1)).testBit g = _
  rw [proj_clear _ _ _ _ _ hK1 hg s2, hX1 _ (clr_lt hK1 hg), hX0 _ (clr_lt hK (clr_lt hK1 hg)), clr_self,
    clr_other hne, clr_self]
  simp

/-- Block `φ` moves to block `φ + 1`, the last one to the first. -/
def shiftUp (P K T : Nat) : Nat :=
  Nat.lor (Nat.land (Nat.shiftLeft (Nat.land T (full P K)) (2 ^ (K + 2))) (full P K))
    (Nat.shiftRight (Nat.land T (full P K)) (Nat.mul (P - 1) (2 ^ (K + 2))))

/-- Block `φ + 1` moves to block `φ`, the first one to the last. -/
def shiftDown (P K T : Nat) : Nat :=
  Nat.lor (Nat.shiftRight (Nat.land T (full P K)) (2 ^ (K + 2)))
    (Nat.land (Nat.shiftLeft (Nat.land T (full P K)) (Nat.mul (P - 1) (2 ^ (K + 2)))) (full P K))

theorem pred_mul_add (P B : Nat) (hP : 0 < P) : (P - 1) * B + B = P * B := by
  rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hP]

theorem shiftUp_testBit (P K T g : Nat) (hP : 0 < P) (hg : g < P * 2 ^ (K + 2)) :
    (shiftUp P K T).testBit g =
      if g < 2 ^ (K + 2) then T.testBit (g + (P - 1) * 2 ^ (K + 2)) else T.testBit (g - 2 ^ (K + 2)) := by
  have h := pred_mul_add P (2 ^ (K + 2)) hP
  have hB := Nat.two_pow_pos (K + 2)
  show ((((T &&& full P K) <<< 2 ^ (K + 2)) &&& full P K) ||| ((T &&& full P K) >>> ((P - 1) * 2 ^ (K + 2)))).testBit
    g = _
  simp only [Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftRight, full_testBit,
    decide_eq_true hg, Bool.and_true]
  by_cases hb : g < 2 ^ (K + 2)
  · rw [ite_eq_left hb, decide_eq_false (show ¬ g ≥ 2 ^ (K + 2) by omega), Bool.false_and, Bool.false_or,
      Nat.add_comm ((P - 1) * 2 ^ (K + 2)) g, decide_eq_true (show g + (P - 1) * 2 ^ (K + 2) < P * 2 ^ (K + 2) by
        omega), Bool.and_true]
  · rw [ite_eq_right hb, decide_eq_true (show g ≥ 2 ^ (K + 2) by omega), Bool.true_and,
      decide_eq_true (show g - 2 ^ (K + 2) < P * 2 ^ (K + 2) by omega), Bool.and_true,
      Nat.add_comm ((P - 1) * 2 ^ (K + 2)) g, decide_eq_false (show ¬ g + (P - 1) * 2 ^ (K + 2) < P * 2 ^ (K + 2) by
        omega), Bool.and_false, Bool.or_false]

theorem shiftDown_testBit (P K T g : Nat) (hP : 0 < P) (hg : g < P * 2 ^ (K + 2)) :
    (shiftDown P K T).testBit g =
      if g < (P - 1) * 2 ^ (K + 2) then T.testBit (g + 2 ^ (K + 2)) else T.testBit (g - (P - 1) * 2 ^ (K + 2)) := by
  have h := pred_mul_add P (2 ^ (K + 2)) hP
  have hB := Nat.two_pow_pos (K + 2)
  show (((T &&& full P K) >>> 2 ^ (K + 2)) ||| (((T &&& full P K) <<< ((P - 1) * 2 ^ (K + 2))) &&& full P K)).testBit
    g = _
  simp only [Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftRight, full_testBit,
    decide_eq_true hg, Bool.and_true]
  by_cases hb : g < (P - 1) * 2 ^ (K + 2)
  · rw [ite_eq_left hb, decide_eq_false (show ¬ g ≥ (P - 1) * 2 ^ (K + 2) by omega), Bool.false_and, Bool.or_false,
      Nat.add_comm (2 ^ (K + 2)) g, decide_eq_true (show g + 2 ^ (K + 2) < P * 2 ^ (K + 2) by omega), Bool.and_true]
  · rw [ite_eq_right hb, decide_eq_true (show g ≥ (P - 1) * 2 ^ (K + 2) by omega), Bool.true_and,
      decide_eq_true (show g - (P - 1) * 2 ^ (K + 2) < P * 2 ^ (K + 2) by omega), Bool.and_true,
      Nat.add_comm (2 ^ (K + 2)) g, decide_eq_false (show ¬ g + 2 ^ (K + 2) < P * 2 ^ (K + 2) by omega),
      Bool.and_false, Bool.false_or]

/-! ### Blocks chosen by a predicate -/

/-- The blocks `φ < n` with `f φ`, all their bits set. -/
def blockSel (K : Nat) (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => Nat.lor (blockSel K f n)
      (cond (f n) (Nat.shiftLeft (Nat.sub (Nat.pow 2 (Nat.pow 2 (K + 2))) 1) (Nat.mul n (Nat.pow 2 (K + 2)))) 0)

theorem blockSel_testBit (K : Nat) (f : Nat → Bool) :
    ∀ n g, (blockSel K f n).testBit g = (decide (g < n * 2 ^ (K + 2)) && f (g / 2 ^ (K + 2))) := by
  intro n
  induction n with
  | zero => intro g; simp [blockSel]
  | succ n ih =>
    intro g
    have hB := Nat.two_pow_pos (K + 2)
    show (blockSel K f n ||| cond (f n) ((2 ^ 2 ^ (K + 2) - 1) <<< (n * 2 ^ (K + 2))) 0).testBit g = _
    rw [Nat.testBit_or, ih]
    by_cases h1 : g < n * 2 ^ (K + 2)
    · have h2 : g < (n + 1) * 2 ^ (K + 2) := by rw [Nat.succ_mul]; omega
      cases hf : f n
      · simp [h1, h2]
      · simp only [h1, h2, decide_true, Bool.true_and, Bool.cond_true, Nat.testBit_shiftLeft,
          Nat.testBit_two_pow_sub_one]
        simp [show ¬ g ≥ n * 2 ^ (K + 2) by omega]
    · have hq : n * 2 ^ (K + 2) ≤ g := by omega
      by_cases h2 : g < (n + 1) * 2 ^ (K + 2)
      · have hdiv : g / 2 ^ (K + 2) = n := by
          apply Nat.div_eq_of_lt_le
          · exact hq
          · exact h2
        cases hf : f n
        · simp [h1, h2, hdiv, hf]
        · have : g - n * 2 ^ (K + 2) < 2 ^ (K + 2) := by rw [Nat.succ_mul] at h2; omega
          simp [h1, h2, hdiv, hf, hq, this]
      · cases hf : f n
        · simp [h1, h2]
        · have : ¬ g - n * 2 ^ (K + 2) < 2 ^ (K + 2) := by rw [Nat.succ_mul] at h2; omega
          simp [h1, h2, hq, this]

/-! ### The game of a block -/

/-- Phase `φ` of the block: the column reads `bit b φ`. -/
def col (b : List Bool) (φ : Nat) : Bool := bit b (φ % b.length)

/-- Index bit `K` equals the column at the block's phase. -/
def colMask (b : List Bool) (K : Nat) : Nat :=
  Nat.lor (Nat.land (ip b.length K K) (blockSel K (col b) b.length))
    (Nat.land (nip b.length K K) (Nat.xor (full b.length K) (blockSel K (col b) b.length)))

theorem colMask_testBit (b : List Bool) (K g : Nat) (hg : g < b.length * 2 ^ (K + 2)) :
    (colMask b K).testBit g = (g.testBit K == col b (g / 2 ^ (K + 2))) := by
  have hK : K < K + 2 := by omega
  show ((ip b.length K K &&& blockSel K (col b) b.length) |||
    (nip b.length K K &&& (full b.length K ^^^ blockSel K (col b) b.length))).testBit g = _
  rw [Nat.testBit_or, Nat.testBit_and, Nat.testBit_and, Nat.testBit_xor, ip_testBit _ _ _ _ hK,
    nip_testBit _ _ _ _ hK, full_testBit, blockSel_testBit, decide_eq_true hg]
  cases g.testBit K <;> cases col b (g / 2 ^ (K + 2)) <;> rfl

/-- The column left of `k` at a node: the next column cell xor (this one or the first cell). -/
def value (b : List Bool) (φ r : Nat) : Bool := xor (col b (φ + 1)) (col b φ || r.testBit 0)

/-- The nodes where the column left of `k` reads 1. -/
def valMask (b : List Bool) (K : Nat) : Nat :=
  let S := blockSel K (col b) b.length
  let S' := blockSel K (fun φ => col b (φ + 1)) b.length
  let F := full b.length K
  Nat.lor (Nat.land S (Nat.xor F S'))
    (Nat.land (Nat.xor F S) (Nat.lor (Nat.land (ip b.length K 0) (Nat.xor F S')) (Nat.land (nip b.length K 0) S')))

theorem valMask_testBit (b : List Bool) (K g : Nat) (hg : g < b.length * 2 ^ (K + 2)) :
    (valMask b K).testBit g = value b (g / 2 ^ (K + 2)) g := by
  have h0 : 0 < K + 2 := by omega
  show ((blockSel K (col b) b.length &&& (full b.length K ^^^ blockSel K (fun φ => col b (φ + 1)) b.length)) |||
    ((full b.length K ^^^ blockSel K (col b) b.length) &&& ((ip b.length K 0 &&&
      (full b.length K ^^^ blockSel K (fun φ => col b (φ + 1)) b.length)) |||
      (nip b.length K 0 &&& blockSel K (fun φ => col b (φ + 1)) b.length)))).testBit g = _
  simp only [Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor, ip_testBit _ _ _ _ h0, nip_testBit _ _ _ _ h0,
    full_testBit, blockSel_testBit, decide_eq_true hg, Bool.true_and]
  unfold value
  cases col b (g / 2 ^ (K + 2)) <;> cases col b (g / 2 ^ (K + 2) + 1) <;> cases g.testBit 0 <;> rfl

/-! ### One step of the game as index flips -/

/-- Flip `j` of a step: index bit `j - 1` (bit `K`, the column, for `j = 0`) changes when bit `j` or bit `j + 1`
(bit `K + 1`, the free cell, for `j + 1 = K`) is set. -/
def phiF (K j : Nat) : Nat × Nat × Nat := (if j = 0 then K else j - 1, j, if j + 1 = K then K + 1 else j + 1)

/-- Flips `j, j + 1, …, j + n - 1` of a step. -/
def phis (K : Nat) : Nat → Nat → List (Nat × Nat × Nat)
  | _, 0 => []
  | j, n + 1 => phiF K j :: phis K (j + 1) n

theorem idxFlips_append : ∀ (l₁ l₂ : List (Nat × Nat × Nat)) (g : Nat),
    idxFlips (l₁ ++ l₂) g = idxFlips l₁ (idxFlips l₂ g)
  | [], _, _ => rfl
  | f :: rest, l₂, g => by
    show flipIdx f.1 f.2.1 f.2.2 (idxFlips (rest ++ l₂) g) = flipIdx f.1 f.2.1 f.2.2 (idxFlips rest (idxFlips l₂ g))
    rw [idxFlips_append rest l₂ g]

theorem flipIdx_invol {t a b : Nat} (hta : t ≠ a) (htb : t ≠ b) (g : Nat) : flipIdx t a b (flipIdx t a b g) = g := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [flipIdx_testBit, flipIdx_testBit, flipIdx_testBit, flipIdx_testBit,
    show (decide (t = a)) = false from decide_eq_false hta, show (decide (t = b)) = false from decide_eq_false htb]
  simp only [Bool.false_and, Bool.xor_false]
  cases g.testBit j <;> cases decide (t = j) <;> cases g.testBit a <;> cases g.testBit b <;> rfl

/-- **A list of flips, then the same flips in reverse, is the identity.** -/
theorem idxFlips_reverse_cancel {K : Nat} : ∀ (l : List (Nat × Nat × Nat)), (∀ f ∈ l, ValidFlip K f) →
    ∀ g, idxFlips l.reverse (idxFlips l g) = g
  | [], _, _ => rfl
  | f :: rest, hv, g => by
    have hf := hv f (List.mem_cons_self ..)
    rw [List.reverse_cons, idxFlips_append]
    show idxFlips rest.reverse (flipIdx f.1 f.2.1 f.2.2 (flipIdx f.1 f.2.1 f.2.2 (idxFlips rest g))) = g
    rw [flipIdx_invol hf.2.2.2.1 hf.2.2.2.2]
    exact idxFlips_reverse_cancel rest (fun f' hf' => hv f' (List.mem_cons_of_mem _ hf')) g

/-! ### Swaps of adjacent index bits -/

/-- The positions whose index has bit `i` set and bit `i + 1` clear. -/
def swapMask (P K i : Nat) : Nat := Nat.land (ip P K i) (nip P K (i + 1))

/-- Index bits `i` and `i + 1` exchanged. -/
def swapIdx (i g : Nat) : Nat :=
  if (g.testBit i != g.testBit (i + 1)) = true then g ^^^ 2 ^ i ^^^ 2 ^ (i + 1) else g

theorem swapIdx_testBit (i g j : Nat) : (swapIdx i g).testBit j =
    if j = i then g.testBit (i + 1) else if j = i + 1 then g.testBit i else g.testBit j := by
  unfold swapIdx
  have h1 : i ≠ i + 1 := by omega
  cases hb : (g.testBit i != g.testBit (i + 1))
  · simp only [Bool.false_eq_true, ite_false]
    have e : g.testBit i = g.testBit (i + 1) := by
      revert hb; cases g.testBit i <;> cases g.testBit (i + 1) <;> simp
    by_cases hj : j = i
    · subst hj; simp [e]
    · by_cases hj1 : j = i + 1
      · subst hj1; simp [e]
      · simp [hj, hj1]
  · simp only [ite_true, testBit_xor_two_pow]
    have e : g.testBit i = !g.testBit (i + 1) := by
      revert hb; cases g.testBit i <;> cases g.testBit (i + 1) <;> simp
    by_cases hj : j = i
    · subst hj; simp [e]
    · by_cases hj1 : j = i + 1
      · subst hj1; simp [e]
      · simp [hj, hj1, Ne.symm hj, Ne.symm hj1]

theorem swapIdx_invol (i g : Nat) : swapIdx i (swapIdx i g) = g := by
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [swapIdx_testBit]
  by_cases hj : j = i
  · subst hj; simp
  · by_cases hj1 : j = i + 1
    · subst hj1; simp
    · simp [hj, hj1]

/-- Adding `2 ^ i` where bit `i` is set and bit `i + 1` clear carries into bit `i + 1`. -/
theorem add_two_pow_carry {g i : Nat} (h1 : g.testBit i = true) (h2 : g.testBit (i + 1) = false) :
    g + 2 ^ i = g ^^^ 2 ^ i ^^^ 2 ^ (i + 1) := by
  have hle := Nat.ge_two_pow_of_testBit h1
  have e1 := xor_two_pow_of_true h1
  have h3 : (g ^^^ 2 ^ i).testBit (i + 1) = false := by
    rw [testBit_xor_two_pow, h2, decide_eq_false (show i ≠ i + 1 by omega)]; rfl
  rw [xor_two_pow_of_false h3, e1, Nat.pow_succ]
  omega

theorem swapIdx_lt {P K i g : Nat} (hi : i + 1 < K + 2) (hg : g < P * 2 ^ (K + 2)) : swapIdx i g < P * 2 ^ (K + 2) := by
  unfold swapIdx
  split
  · exact xor_two_pow_lt hi P (xor_two_pow_lt (by omega) P hg)
  · exact hg

/-- **A swap, on tables**: composing a table with the exchange of index bits `i` and `i + 1` is a delta swap. -/
theorem dsSwap_spec (P K i T g : Nat) (hi : i + 1 < K + 2) (hg : g < P * 2 ^ (K + 2)) :
    (ds T (swapMask P K i) (2 ^ i)).testBit g = T.testBit (swapIdx i g) := by
  have hi0 : i < K + 2 := by omega
  have hM : ∀ h, h < P * 2 ^ (K + 2) → (swapMask P K i).testBit h = (h.testBit i && !h.testBit (i + 1)) := fun h hh => by
    show (ip P K i &&& nip P K (i + 1)).testBit h = _
    rw [Nat.testBit_and, ip_testBit _ _ _ _ hi0, nip_testBit _ _ _ _ hi, decide_eq_true hh]
    cases h.testBit i <;> cases h.testBit (i + 1) <;> rfl
  have hMout : ∀ h, ¬ h < P * 2 ^ (K + 2) → (swapMask P K i).testBit h = false := fun h hh => by
    show (ip P K i &&& nip P K (i + 1)).testBit h = _
    rw [Nat.testBit_and, ip_testBit _ _ _ _ hi0, decide_eq_false hh]; rfl
  have hMg : ∀ h, (swapMask P K i).testBit h = true → h.testBit i = true := fun h hm => by
    by_cases hh : h < P * 2 ^ (K + 2)
    · rw [hM h hh] at hm; revert hm; cases h.testBit i <;> simp
    · rw [hMout h hh] at hm; exact absurd hm (by decide)
  have hsub : ∀ h, h.testBit i = true → (h - 2 ^ i).testBit i = false := fun h hh => by
    rw [← xor_two_pow_of_true hh, testBit_xor_two_pow, hh]; simp
  rw [ds_spec _ _ _ _ (fun h hm _ => by
    cases e : (swapMask P K i).testBit (h - 2 ^ i)
    · rfl
    · exact absurd (hsub h (hMg h hm)) (by rw [hMg _ e]; decide))]
  unfold swapIdx
  rw [hM g hg]
  cases b1 : g.testBit i <;> cases b2 : g.testBit (i + 1)
  · -- both clear: below `g` by `2 ^ i` both are set, so nothing moves
    have : ¬ (2 ^ i ≤ g ∧ (swapMask P K i).testBit (g - 2 ^ i) = true) := fun ⟨hle, hm⟩ => by
      have hgi := testBit_sub_two_pow_of_false b1 hle
      have hlt : g - 2 ^ i < P * 2 ^ (K + 2) := Nat.lt_of_le_of_lt (Nat.sub_le _ _) hg
      rw [hM _ hlt, hgi] at hm
      have h0 : (g - 2 ^ i).testBit (i + 1) = false := by simpa using hm
      have := add_two_pow_carry hgi h0
      rw [show g - 2 ^ i + 2 ^ i = g by omega] at this
      have := congrArg (fun x => x.testBit (i + 1)) this
      simp only [testBit_xor_two_pow, h0, b2] at this
      simp at this
    simp [this]
  · -- bit `i + 1` set, bit `i` clear: the entry comes from below
    have hle : 2 ^ (i + 1) ≤ g := Nat.ge_two_pow_of_testBit b2
    have e : g - 2 ^ i = g ^^^ 2 ^ i ^^^ 2 ^ (i + 1) := by
      have hx : (g ^^^ 2 ^ (i + 1)).testBit i = false := by
        rw [testBit_xor_two_pow, b1, decide_eq_false (show i + 1 ≠ i by omega)]; rfl
      rw [Nat.xor_assoc, Nat.xor_comm (2 ^ i), ← Nat.xor_assoc, xor_two_pow_of_false hx, xor_two_pow_of_true b2,
        Nat.pow_succ]
      rw [Nat.pow_succ] at hle
      omega
    have hlt : g - 2 ^ i < P * 2 ^ (K + 2) := Nat.lt_of_le_of_lt (Nat.sub_le _ _) hg
    have hm : (swapMask P K i).testBit (g - 2 ^ i) = true := by
      rw [hM _ hlt, e, testBit_xor_two_pow, testBit_xor_two_pow, testBit_xor_two_pow, testBit_xor_two_pow, b1, b2,
        decide_eq_false (show i + 1 ≠ i by omega), decide_eq_false (show i ≠ i + 1 by omega)]
      simp
    have hle' : 2 ^ i ≤ g := Nat.le_trans (Nat.pow_le_pow_right (by decide) (by omega)) hle
    rw [ite_eq_right (by decide : ¬ ((false && !true) = true)), ite_eq_left ⟨hle', hm⟩,
      ite_eq_left (by decide : (false != true) = true), e]
  · -- bit `i` set, bit `i + 1` clear: the entry comes from above
    simp [add_two_pow_carry b1 b2]
  · -- both set: nothing moves
    have : ¬ (2 ^ i ≤ g ∧ (swapMask P K i).testBit (g - 2 ^ i) = true) := fun ⟨_, hm⟩ => by
      have h1 := hMg _ hm
      rw [hsub g b1] at h1
      exact Bool.noConfusion h1
    simp [this]

/-- The table composed with the swaps of a list, the first one innermost. -/
def applySwaps (P K : Nat) (T : Nat) : List Nat → Nat
  | [] => T
  | i :: rest => applySwaps P K (ds T (swapMask P K i) (2 ^ i)) rest

/-- The index map of a list of swaps: `τ_{i₁} (τ_{i₂} (⋯ g))`. -/
def idxSwaps : List Nat → Nat → Nat
  | [], g => g
  | i :: rest, g => swapIdx i (idxSwaps rest g)

theorem idxSwaps_lt {P K : Nat} : ∀ (l : List Nat), (∀ i ∈ l, i + 1 < K + 2) →
    ∀ g, g < P * 2 ^ (K + 2) → idxSwaps l g < P * 2 ^ (K + 2)
  | [], _, _, hg => hg
  | i :: rest, hv, g, hg => swapIdx_lt (hv i (List.mem_cons_self ..))
      (idxSwaps_lt rest (fun i' hi' => hv i' (List.mem_cons_of_mem _ hi')) g hg)

theorem applySwaps_spec (P K : Nat) : ∀ (l : List Nat) (T : Nat), (∀ i ∈ l, i + 1 < K + 2) →
    ∀ g, g < P * 2 ^ (K + 2) → (applySwaps P K T l).testBit g = T.testBit (idxSwaps l g)
  | [], _, _, _, _ => rfl
  | i :: rest, T, hv, g, hg => by
    have hrest : ∀ i' ∈ rest, i' + 1 < K + 2 := fun i' hi' => hv i' (List.mem_cons_of_mem _ hi')
    show (applySwaps P K (ds T (swapMask P K i) (2 ^ i)) rest).testBit g = _
    rw [applySwaps_spec P K rest _ hrest g hg, dsSwap_spec P K i T _ (hv i (List.mem_cons_self ..))
      (idxSwaps_lt rest hrest g hg)]
    rfl

theorem idxSwaps_append : ∀ (l₁ l₂ : List Nat) (g : Nat), idxSwaps (l₁ ++ l₂) g = idxSwaps l₁ (idxSwaps l₂ g)
  | [], _, _ => rfl
  | i :: rest, l₂, g => by
    show swapIdx i (idxSwaps (rest ++ l₂) g) = swapIdx i (idxSwaps rest (idxSwaps l₂ g))
    rw [idxSwaps_append rest l₂ g]

theorem idxSwaps_reverse_cancel : ∀ (l : List Nat) (g : Nat), idxSwaps l.reverse (idxSwaps l g) = g
  | [], _ => rfl
  | i :: rest, g => by
    rw [List.reverse_cons, idxSwaps_append]
    show idxSwaps rest.reverse (swapIdx i (swapIdx i (idxSwaps rest g))) = g
    rw [swapIdx_invol]
    exact idxSwaps_reverse_cancel rest g

/-- The swaps `m - 1, …, 0`: they move index bit `0` up to bit `m` and bits `1, …, m` down by one. -/
def rotDown : Nat → List Nat
  | 0 => []
  | m + 1 => m :: rotDown m

theorem rotDown_valid {K : Nat} : ∀ m, m < K + 2 → ∀ i ∈ rotDown m, i + 1 < K + 2
  | 0, _, i, hi => absurd hi (List.not_mem_nil)
  | m + 1, hm, i, hi => by
    rcases List.mem_cons.mp hi with rfl | h
    · omega
    · exact rotDown_valid m (by omega) i h

/-- **The rotation**: after the swaps `m - 1, …, 0`, bit `j < m` holds old bit `j + 1` and bit `m` old bit `0`. -/
theorem rotDown_testBit : ∀ (m g j : Nat), (idxSwaps (rotDown m) g).testBit j =
    if j < m then g.testBit (j + 1) else if j = m then g.testBit 0 else g.testBit j
  | 0, g, j => by
    show g.testBit j = _
    by_cases hj : j = 0
    · subst hj; simp
    · simp [hj]
  | m + 1, g, j => by
    show (swapIdx m (idxSwaps (rotDown m) g)).testBit j = _
    rw [swapIdx_testBit, rotDown_testBit m g (m + 1), rotDown_testBit m g m, rotDown_testBit m g j]
    by_cases h1 : j = m
    · subst h1
      simp [show ¬ j + 1 < j by omega]
    · by_cases h2 : j = m + 1
      · subst h2
        simp
      · by_cases h4 : j < m
        · simp [h1, h2, h4, show j < m + 1 by omega]
        · simp [h1, h2, h4, show ¬ j < m + 1 by omega]

theorem phiF_valid {K j : Nat} (hK : 1 ≤ K) (hj : j < K) : ValidFlip K (phiF K j) := by
  unfold phiF ValidFlip
  by_cases h0 : j = 0
  · subst h0
    by_cases h1 : 0 + 1 = K
    · simp [h1]; omega
    · simp [h1]; omega
  · by_cases h1 : j + 1 = K
    · simp [h0, h1]; omega
    · simp [h0, h1]; omega

theorem phis_valid {K : Nat} (hK : 1 ≤ K) : ∀ n j, j + n ≤ K → ∀ f ∈ phis K j n, ValidFlip K f
  | 0, _, _, f, hf => absurd hf (List.not_mem_nil)
  | n + 1, j, hjn, f, hf => by
    rcases List.mem_cons.mp hf with rfl | h
    · exact phiF_valid hK (by omega)
    · exact phis_valid hK n (j + 1) (by omega) f h

/-- The cell `i` of the next step, beside a column reading `c` and with the free cell `u`. -/
def nextCell (K : Nat) (r : Nat → Bool) (c u : Bool) (i : Nat) : Bool :=
  xor (if i = 0 then c else r (i - 1)) (r i || (if i + 1 = K then u else r (i + 1)))

/-- **The step undone, flip by flip.** Start from an index holding the next cells `y₁, …, y_{K-1}` at bits
`0, …, K - 2`, the last cell `r_{K-1}` at bit `K - 1`, `y₀` at bit `K` and the free cell at bit `K + 1`. The flips
`K - 1` down to `j` turn bits `j - 1, …, K - 2` back into the cells, and flip `0` turns bit `K` back into the
column. -/
theorem phis_undo (K : Nat) (hK : 1 ≤ K) (r : Nat → Bool) (c u : Bool) (h : Nat)
    (h1 : ∀ i, i + 1 < K → h.testBit i = nextCell K r c u (i + 1)) (h2 : h.testBit (K - 1) = r (K - 1))
    (h3 : h.testBit K = nextCell K r c u 0) (h4 : h.testBit (K + 1) = u) :
    ∀ n j, j + n = K → ∀ i, (idxFlips (phis K j n) h).testBit i =
      if i < K then (if j ≤ i + 1 then r i else nextCell K r c u (i + 1))
      else if i = K then (if j = 0 then c else nextCell K r c u 0) else h.testBit i := by
  intro n
  induction n with
  | zero =>
    intro j hj i
    have hjK : j = K := by omega
    subst hjK
    show h.testBit i = _
    by_cases hi : i < j
    · rw [ite_eq_left hi]
      by_cases hl : j ≤ i + 1
      · rw [ite_eq_left hl, show i = j - 1 by omega]; exact h2
      · rw [ite_eq_right hl]; exact h1 i (by omega)
    · rw [ite_eq_right hi]
      by_cases hk : i = j
      · rw [ite_eq_left hk, ite_eq_right (show ¬ j = 0 by omega), hk]; exact h3
      · rw [ite_eq_right hk]
  | succ n ih =>
    intro j hj i
    show (flipIdx (phiF K j).1 (phiF K j).2.1 (phiF K j).2.2 (idxFlips (phis K (j + 1) n) h)).testBit i = _
    rw [flipIdx_testBit]
    have ihj := ih (j + 1) (by omega)
    -- the two condition bits are the cells `j` and `j + 1` (the free cell for `j + 1 = K`)
    have ca : (idxFlips (phis K (j + 1) n) h).testBit (phiF K j).2.1 = r j := by
      show (idxFlips (phis K (j + 1) n) h).testBit j = r j
      rw [ihj, ite_eq_left (show j < K by omega), ite_eq_left (show j + 1 ≤ j + 1 by omega)]
    have cb : (idxFlips (phis K (j + 1) n) h).testBit (phiF K j).2.2 = (if j + 1 = K then u else r (j + 1)) := by
      by_cases hjK : j + 1 = K
      · have e : (phiF K j).2.2 = K + 1 := by simp [phiF, hjK]
        rw [e, ihj, ite_eq_right (show ¬ K + 1 < K by omega), ite_eq_right (show ¬ K + 1 = K by omega), h4,
          ite_eq_left hjK]
      · have e : (phiF K j).2.2 = j + 1 := by simp [phiF, hjK]
        rw [e, ihj, ite_eq_left (show j + 1 < K by omega), ite_eq_left (show j + 1 ≤ j + 1 + 1 by omega),
          ite_eq_right hjK]
    rw [ca, cb, ihj]
    have hy : ∀ m, m < K → xor (nextCell K r c u m) (r m || (if m + 1 = K then u else r (m + 1))) =
        (if m = 0 then c else r (m - 1)) := fun m _ => by
      unfold nextCell
      cases (if m = 0 then c else r (m - 1)) <;> cases (r m || (if m + 1 = K then u else r (m + 1))) <;> rfl
    by_cases hj0 : j = 0
    · subst hj0
      -- flip `0` targets bit `K`
      have ht : (phiF K 0).1 = K := by simp [phiF]
      rw [ht]
      by_cases hiK : i = K
      · subst hiK
        rw [ite_eq_right (Nat.lt_irrefl _), ite_eq_left rfl, ite_eq_right (show ¬ 0 + 1 = 0 by omega),
          ite_eq_right (Nat.lt_irrefl _), ite_eq_left rfl, ite_eq_left rfl, decide_eq_true rfl, Bool.true_and,
          hy 0 (by omega)]
        simp
      · rw [decide_eq_false (Ne.symm hiK), Bool.false_and, Bool.xor_false]
        by_cases hi : i < K
        · rw [ite_eq_left hi, ite_eq_left hi, ite_eq_left (show 0 + 1 ≤ i + 1 by omega),
            ite_eq_left (show 0 ≤ i + 1 by omega)]
        · rw [ite_eq_right hi, ite_eq_right hi, ite_eq_right hiK, ite_eq_right hiK]
    · have ht : (phiF K j).1 = j - 1 := by simp [phiF, hj0]
      rw [ht]
      by_cases hit : i = j - 1
      · subst hit
        rw [decide_eq_true rfl, Bool.true_and, ite_eq_left (show j - 1 < K by omega),
          ite_eq_right (show ¬ j + 1 ≤ j - 1 + 1 by omega), ite_eq_left (show j - 1 < K by omega),
          ite_eq_left (show j ≤ j - 1 + 1 by omega), show j - 1 + 1 = j by omega, hy j (by omega),
          ite_eq_right hj0]
      · rw [decide_eq_false (Ne.symm hit), Bool.false_and, Bool.xor_false]
        by_cases hi : i < K
        · rw [ite_eq_left hi, ite_eq_left hi]
          by_cases hl : j + 1 ≤ i + 1
          · rw [ite_eq_left hl, ite_eq_left (show j ≤ i + 1 by omega)]
          · rw [ite_eq_right hl, ite_eq_right (show ¬ j ≤ i + 1 by omega)]
        · rw [ite_eq_right hi, ite_eq_right hi]
          by_cases hiK : i = K
          · rw [ite_eq_left hiK, ite_eq_left hiK, ite_eq_right (show ¬ j + 1 = 0 by omega), ite_eq_right hj0]
          · rw [ite_eq_right hiK, ite_eq_right hiK]

/-! ### Image and preimage -/

/-- The image of a set of nodes under one step, for both free cells. Index bit `K` takes the column and bit `K + 1`
the free cell, the flips make the step a bijection of the index, the projections forget the last cell and the free
cell, the rotation puts the new cells back at bits `0, …, K - 1`, and the blocks move to the next phase. -/
def post (b : List Bool) (K X : Nat) : Nat :=
  canon b.length K (shiftUp b.length K (applySwaps b.length K
    (proj b.length K (proj b.length K (applyFlips b.length K (Nat.land (canon b.length K X) (colMask b K))
      (phis K 0 K)) (K - 1)) (K + 1)) (rotDown K)))

/-- The preimage of a set of nodes: the nodes with a move into it, for some free cell. -/
def pre (b : List Bool) (K Y : Nat) : Nat :=
  canon b.length K (proj b.length K (proj b.length K (Nat.land (applyFlips b.length K
    (applySwaps b.length K (shiftDown b.length K (canon b.length K Y)) (rotDown K).reverse) (phis K 0 K).reverse)
      (colMask b K)) (K + 1)) K)

/-- Bits of a position in block `φ`. -/
theorem testBit_blk (φ x i K : Nat) (hx : x < 2 ^ (K + 2)) :
    (φ * 2 ^ (K + 2) + x).testBit i = if i < K + 2 then x.testBit i else φ.testBit (i - (K + 2)) := by
  rw [Nat.mul_comm, Nat.testBit_two_pow_mul_add _ hx]

theorem clr_of_false {p g : Nat} (h : g.testBit p = false) : clr p g = g := by
  unfold clr; rw [h]; rfl

theorem blk_lt {P φ x K : Nat} (hφ : φ < P) (hx : x < 2 ^ (K + 2)) : φ * 2 ^ (K + 2) + x < P * 2 ^ (K + 2) := by
  have : (φ + 1) * 2 ^ (K + 2) ≤ P * 2 ^ (K + 2) := Nat.mul_le_mul_right _ hφ
  rw [Nat.succ_mul] at this
  omega

/-- A number with the bits of block `φ` above `K + 2` is in block `φ`. -/
theorem eq_blk {z φ K : Nat} (h : ∀ i, K + 2 ≤ i → z.testBit i = φ.testBit (i - (K + 2))) :
    z = φ * 2 ^ (K + 2) + z % 2 ^ (K + 2) := by
  have hd : z / 2 ^ (K + 2) = φ := Nat.eq_of_testBit_eq fun j => by
    rw [Nat.testBit_div_two_pow, h _ (by omega), show j + (K + 2) - (K + 2) = j by omega]
  have := Nat.div_add_mod z (2 ^ (K + 2))
  rw [hd] at this
  rw [Nat.mul_comm]
  omega

theorem lt_pow_of_mod {x K : Nat} : x % 2 ^ (K + 2) < 2 ^ (K + 2) := Nat.mod_lt _ (Nat.two_pow_pos _)

/-- The bits of the kit's step are those of `nextCell`. -/
theorem move_testBit (K : Nat) (c u : Bool) (r : Nat) (hr : r < 2 ^ K) (i : Nat) (hi : i < K) :
    (GameMask.move K c u r).testBit i = nextCell K r.testBit c u i := by
  rw [GameMask.move_eq, Rule30StripCertificates.testBit_stripStep K c u r hr i hi]
  unfold Rule30Jen.rule nextCell
  rfl

/-- Index bit `p` flipped when `v` holds. -/
def fl (p : Nat) (v : Bool) (g : Nat) : Nat := if v = true then g ^^^ 2 ^ p else g

theorem fl_testBit (p : Nat) (v : Bool) (g j : Nat) : (fl p v g).testBit j = (g.testBit j ^^ (v && decide (p = j))) := by
  unfold fl; cases v <;> simp [Nat.testBit_two_pow]

theorem fl_false (p g : Nat) : fl p false g = g := rfl

theorem fl_true (p g : Nat) : fl p true g = g ^^^ 2 ^ p := rfl

theorem fl_lt {P K p g : Nat} (v : Bool) (hp : p < K + 2) (hg : g < P * 2 ^ (K + 2)) : fl p v g < P * 2 ^ (K + 2) := by
  unfold fl; cases v
  · exact hg
  · exact xor_two_pow_lt hp P hg

/-- The block of a position, from its bits above `K + 2`. -/
theorem div_of_bits {z φ K : Nat} (h : ∀ i, K + 2 ≤ i → z.testBit i = φ.testBit (i - (K + 2))) :
    z / 2 ^ (K + 2) = φ :=
  Nat.eq_of_testBit_eq fun j => by
    rw [Nat.testBit_div_two_pow, h _ (by omega), show j + (K + 2) - (K + 2) = j by omega]

/-- The real step at a position of block `φ`: the next cells, as a number below `2 ^ K`. -/
theorem move_lt (K : Nat) (c u : Bool) (r : Nat) : GameMask.move K c u r < 2 ^ K := by
  rw [GameMask.move_eq]; exact Rule30StripCertificates.stripStep_lt _ _ _ _

/-- **The image contains every move.** -/
theorem post_sound (b : List Bool) (K : Nat) (hK : 1 ≤ K) (X φ r : Nat) (u : Bool) (hφ : φ < b.length)
    (hr : r < 2 ^ K) (hX : X.testBit (φ * 2 ^ (K + 2) + r) = true) :
    (post b K X).testBit ((φ + 1) % b.length * 2 ^ (K + 2) + GameMask.move K (col b φ) u r) = true := by
  have hP : 0 < b.length := by omega
  have hB := Nat.two_pow_pos (K + 2)
  have hKB : 2 ^ K ≤ 2 ^ (K + 2) := Nat.pow_le_pow_right (by decide) (by omega)
  have hy := move_lt K (col b φ) u r
  have hyB : GameMask.move K (col b φ) u r < 2 ^ (K + 2) := by omega
  have hrB : r < 2 ^ (K + 2) := by omega
  have hyK : ∀ i, K ≤ i → (GameMask.move K (col b φ) u r).testBit i = false := fun i hi =>
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hy (Nat.pow_le_pow_right (by decide) hi))
  have hrK : ∀ i, K ≤ i → r.testBit i = false := fun i hi =>
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hr (Nat.pow_le_pow_right (by decide) hi))
  -- the tables of the step
  let S := Nat.land (canon b.length K X) (colMask b K)
  let W := applyFlips b.length K S (phis K 0 K)
  let Q := proj b.length K (proj b.length K W (K - 1)) (K + 1)
  let Z := applySwaps b.length K Q (rotDown K)
  show (canon b.length K (shiftUp b.length K Z)).testBit _ = true
  -- 1. the canonical form reads the target itself
  have hg := blk_lt (Nat.mod_lt (φ + 1) hP) hyB
  have hgK : ((φ + 1) % b.length * 2 ^ (K + 2) + GameMask.move K (col b φ) u r).testBit K = false := by
    rw [testBit_blk _ _ _ _ hyB, ite_eq_left (by omega)]; exact hyK K (Nat.le_refl _)
  have hgK1 : ((φ + 1) % b.length * 2 ^ (K + 2) + GameMask.move K (col b φ) u r).testBit (K + 1) = false := by
    rw [testBit_blk _ _ _ _ hyB, ite_eq_left (by omega)]; exact hyK (K + 1) (by omega)
  rw [canon_testBit _ _ _ _ hg, clr_of_false hgK1, clr_of_false hgK, shiftUp_testBit _ _ _ _ hP hg]
  -- 2. block `φ + 1` came from block `φ`
  have hZ : ∀ v, v = φ * 2 ^ (K + 2) + GameMask.move K (col b φ) u r → Z.testBit v = true → (if
      (φ + 1) % b.length * 2 ^ (K + 2) + GameMask.move K (col b φ) u r < 2 ^ (K + 2) then
      Z.testBit ((φ + 1) % b.length * 2 ^ (K + 2) + GameMask.move K (col b φ) u r + (b.length - 1) * 2 ^ (K + 2))
      else Z.testBit ((φ + 1) % b.length * 2 ^ (K + 2) + GameMask.move K (col b φ) u r - 2 ^ (K + 2))) = true := by
    intro v hv hZv
    by_cases hlast : φ + 1 = b.length
    · rw [hlast, Nat.mod_self, Nat.zero_mul, Nat.zero_add, ite_eq_left hyB,
        show b.length - 1 = φ by omega, Nat.add_comm, ← hv]
      exact hZv
    · rw [Nat.mod_eq_of_lt (show φ + 1 < b.length by omega), Nat.succ_mul,
        ite_eq_right (show ¬ φ * 2 ^ (K + 2) + 2 ^ (K + 2) + GameMask.move K (col b φ) u r < 2 ^ (K + 2) by omega),
        show φ * 2 ^ (K + 2) + 2 ^ (K + 2) + GameMask.move K (col b φ) u r - 2 ^ (K + 2) = v by omega]
      exact hZv
  apply hZ _ rfl
  -- 3. the rotation
  have hvB := blk_lt hφ hyB
  rw [applySwaps_spec _ _ _ _ (rotDown_valid K (by omega)) _ hvB]
  have hsB := idxSwaps_lt (P := b.length) (K := K) (rotDown K) (rotDown_valid K (by omega)) _ hvB
  -- the rotated index: bit `j < K` holds bit `j + 1` of the target, bit `K` its bit `0`
  have hs : ∀ j, (idxSwaps (rotDown K) (φ * 2 ^ (K + 2) + GameMask.move K (col b φ) u r)).testBit j =
      if j < K then (GameMask.move K (col b φ) u r).testBit (j + 1)
      else if j = K then (GameMask.move K (col b φ) u r).testBit 0
      else (φ * 2 ^ (K + 2) + GameMask.move K (col b φ) u r).testBit j := fun j => by
    rw [rotDown_testBit]
    by_cases h1 : j < K
    · rw [ite_eq_left h1, ite_eq_left h1, testBit_blk _ _ _ _ hyB, ite_eq_left (by omega)]
    · rw [ite_eq_right h1, ite_eq_right h1]
      by_cases h2 : j = K
      · rw [ite_eq_left h2, ite_eq_left h2, testBit_blk _ _ _ _ hyB, ite_eq_left (by omega)]
      · rw [ite_eq_right h2, ite_eq_right h2]
  -- 4. the projections: the index with the last cell and the free cell put back
  obtain ⟨s, hsdef⟩ : ∃ s, s = idxSwaps (rotDown K) (φ * 2 ^ (K + 2) + GameMask.move K (col b φ) u r) := ⟨_, rfl⟩
  rw [← hsdef] at hsB hs ⊢
  obtain ⟨h', hh'def⟩ : ∃ h', h' = fl (K - 1) (r.testBit (K - 1)) (fl (K + 1) u s) := ⟨_, rfl⟩
  have hh'B : h' < b.length * 2 ^ (K + 2) := hh'def ▸ fl_lt _ (by omega) (fl_lt _ (by omega) hsB)
  suffices hW : W.testBit h' = true by
    show (proj b.length K (proj b.length K W (K - 1)) (K + 1)).testBit s = true
    rw [proj_testBit _ _ _ _ _ (by omega) hsB]
    have hs1 := fl_lt (K := K) (P := b.length) u (show K + 1 < K + 2 by omega) hsB
    have key : (proj b.length K W (K - 1)).testBit (fl (K + 1) u s) = true := by
      rw [proj_testBit _ _ _ _ _ (by omega) hs1]
      rw [hh'def] at hW
      cases hrk : r.testBit (K - 1)
      · rw [hrk, fl_false] at hW; rw [hW, Bool.true_or]
      · rw [hrk, fl_true] at hW; rw [hW, Bool.or_true]
    cases u
    · rw [fl_false] at key; rw [key, Bool.true_or]
    · rw [fl_true] at key; rw [key, Bool.or_true]
  -- 5. the flips undo the step
  rw [applyFlips_spec _ _ _ _ (phis_valid hK K 0 (by omega)) _ hh'B]
  have hbits := phis_undo K hK r.testBit (col b φ) u h'
    (fun i hi => by
      rw [hh'def, fl_testBit, fl_testBit, hs, decide_eq_false (show K + 1 ≠ i by omega),
        decide_eq_false (show K - 1 ≠ i by omega), ite_eq_left (show i < K by omega), move_testBit _ _ _ _ hr _ hi]
      simp)
    (by
      rw [hh'def, fl_testBit, fl_testBit, hs, decide_eq_false (show K + 1 ≠ K - 1 by omega), ite_eq_left (show K - 1 < K by omega),
        show K - 1 + 1 = K by omega, hyK K (Nat.le_refl _)]
      simp)
    (by
      rw [hh'def, fl_testBit, fl_testBit, hs, decide_eq_false (show K + 1 ≠ K by omega), decide_eq_false (show K - 1 ≠ K by omega),
        ite_eq_right (Nat.lt_irrefl K), ite_eq_left rfl, move_testBit _ _ _ _ hr _ (by omega)]
      simp)
    (by
      rw [hh'def, fl_testBit, fl_testBit, hs, decide_eq_false (show K - 1 ≠ K + 1 by omega), ite_eq_right (show ¬ K + 1 < K by omega),
        ite_eq_right (show K + 1 ≠ K by omega), testBit_blk _ _ _ _ hyB, ite_eq_left (show K + 1 < K + 2 by omega),
        hyK (K + 1) (by omega)]
      simp)
    K 0 (by omega)
  -- 6. the start: the cells `r`, the column, and block `φ`
  have hz0B := idxFlips_lt (P := b.length) (K := K) (phis K 0 K) (phis_valid hK K 0 (by omega)) _ hh'B
  have hhigh : ∀ i, K + 2 ≤ i → (idxFlips (phis K 0 K) h').testBit i = φ.testBit (i - (K + 2)) := fun i hi => by
    rw [hbits, ite_eq_right (show ¬ i < K by omega), ite_eq_right (show i ≠ K by omega)]
    rw [hh'def, fl_testBit, fl_testBit, hs, decide_eq_false (show K + 1 ≠ i by omega), decide_eq_false (show K - 1 ≠ i by omega),
      ite_eq_right (show ¬ i < K by omega), ite_eq_right (show i ≠ K by omega), testBit_blk _ _ _ _ hyB,
      ite_eq_right (show ¬ i < K + 2 by omega)]
    simp
  show (canon b.length K X &&& colMask b K).testBit (idxFlips (phis K 0 K) h') = true
  rw [Nat.testBit_and, canon_testBit _ _ _ _ hz0B, colMask_testBit _ _ _ hz0B, div_of_bits hhigh, hbits]
  rw [ite_eq_right (Nat.lt_irrefl K), ite_eq_left rfl, ite_eq_left rfl, beq_self_eq_true, Bool.and_true]
  -- the cleared index is the start node
  have hstart : clr K (clr (K + 1) (idxFlips (phis K 0 K) h')) = φ * 2 ^ (K + 2) + r := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [clr_testBit, clr_testBit, testBit_blk _ _ _ _ hrB]
    by_cases hi : i < K
    · rw [hbits, ite_eq_left hi, ite_eq_left (show 0 ≤ i + 1 by omega), ite_eq_left (show i < K + 2 by omega),
        decide_eq_false (show K + 1 ≠ i by omega), decide_eq_false (show K ≠ i by omega)]
      simp
    · by_cases hiK : i = K
      · subst hiK; simp [hrK i (Nat.le_refl _)]
      · by_cases hiK1 : i = K + 1
        · subst hiK1; simp [hrK (K + 1) (by omega)]
        · rw [hhigh i (by omega), ite_eq_right (show ¬ i < K + 2 by omega), decide_eq_false (Ne.symm hiK1),
            decide_eq_false (Ne.symm hiK)]
          simp
  rw [hstart]
  exact hX

/-- The rotated index of a move, with the last cell at bit `K - 1` and the free cell at bit `K + 1`, is the rotation
of the move with those two cells at bits `K` and `K + 1`. -/
theorem rot_move (K : Nat) (hK : 1 ≤ K) (φ r : Nat) (c u : Bool) :
    fl (K - 1) (r.testBit (K - 1)) (fl (K + 1) u (idxSwaps (rotDown K) (φ * 2 ^ (K + 2) + GameMask.move K c u r))) =
      idxSwaps (rotDown K) (fl (K + 1) u (fl K (r.testBit (K - 1)) (φ * 2 ^ (K + 2) + GameMask.move K c u r))) := by
  have hy := move_lt K c u r
  have hyB : GameMask.move K c u r < 2 ^ (K + 2) :=
    Nat.lt_of_lt_of_le hy (Nat.pow_le_pow_right (by decide) (by omega))
  have hyK : ∀ i, K ≤ i → (GameMask.move K c u r).testBit i = false := fun i hi =>
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hy (Nat.pow_le_pow_right (by decide) hi))
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [fl_testBit, rotDown_testBit, testBit_blk _ _ _ _ hyB]
  rcases Nat.lt_or_ge j (K - 1) with h | h
  · have e1 : K - 1 ≠ j := by omega
    have e2 : K + 1 ≠ j := by omega
    have e3 : K ≠ j + 1 := by omega
    have e5 : K ≠ j := by omega
    simp [show j < K by omega, show j + 1 < K + 2 by omega, e1, e2, e3, e5]
  · rcases Nat.lt_or_ge j K with h' | h'
    · have hj : j = K - 1 := by omega
      subst hj
      have e2 : K + 1 ≠ K - 1 := by omega
      simp [show K - 1 < K by omega, show K - 1 + 1 = K by omega, e2, hyK K (Nat.le_refl _)]
    · rcases Nat.lt_or_ge K j with h'' | h''
      · have e1 : K - 1 ≠ j := by omega
        have e5 : K ≠ j := by omega
        simp [show ¬ j < K by omega, show j ≠ K by omega, e1, e5]
      · have hj : j = K := by omega
        subst hj
        have e1 : j - 1 ≠ j := by omega
        have e3 : j ≠ 0 := by omega
        simp [e1, e3, show (0 : Nat) < j + 2 by omega]

/-- **Undoing the step**: the flips take the rotated move back to the start, with the column at bit `K` and the free
cell at bit `K + 1`. -/
theorem undo_move (K : Nat) (hK : 1 ≤ K) (φ r : Nat) (c u : Bool) (hr : r < 2 ^ K) :
    idxFlips (phis K 0 K) (fl (K - 1) (r.testBit (K - 1)) (fl (K + 1) u
      (idxSwaps (rotDown K) (φ * 2 ^ (K + 2) + GameMask.move K c u r)))) =
      fl (K + 1) u (fl K c (φ * 2 ^ (K + 2) + r)) := by
  have hy := move_lt K c u r
  have hyB : GameMask.move K c u r < 2 ^ (K + 2) :=
    Nat.lt_of_lt_of_le hy (Nat.pow_le_pow_right (by decide) (by omega))
  have hrB : r < 2 ^ (K + 2) := Nat.lt_of_lt_of_le hr (Nat.pow_le_pow_right (by decide) (by omega))
  have hyK : ∀ i, K ≤ i → (GameMask.move K c u r).testBit i = false := fun i hi =>
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hy (Nat.pow_le_pow_right (by decide) hi))
  have hrK : ∀ i, K ≤ i → r.testBit i = false := fun i hi =>
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hr (Nat.pow_le_pow_right (by decide) hi))
  -- the start index of `phis_undo`
  have hbits := phis_undo K hK r.testBit c u
    (fl (K - 1) (r.testBit (K - 1)) (fl (K + 1) u (idxSwaps (rotDown K) (φ * 2 ^ (K + 2) + GameMask.move K c u r))))
    (fun i hi => by
      simp only [fl_testBit, rotDown_testBit, testBit_blk _ _ _ _ hyB]
      have e1 : K - 1 ≠ i := by omega
      have e2 : K + 1 ≠ i := by omega
      simp [e1, e2, show i < K by omega, show i + 1 < K + 2 by omega, move_testBit _ _ _ _ hr _ hi])
    (by
      simp only [fl_testBit, rotDown_testBit, testBit_blk _ _ _ _ hyB]
      have e2 : K + 1 ≠ K - 1 := by omega
      simp [e2, show K - 1 < K by omega, show K - 1 + 1 = K by omega, hyK K (Nat.le_refl _)])
    (by
      simp only [fl_testBit, rotDown_testBit, testBit_blk _ _ _ _ hyB]
      have e1 : K - 1 ≠ K := by omega
      simp [e1, move_testBit _ _ _ _ hr _ (show 0 < K by omega)])
    (by
      simp only [fl_testBit, rotDown_testBit, testBit_blk _ _ _ _ hyB]
      have e1 : K - 1 ≠ K + 1 := by omega
      simp [e1, show ¬ K + 1 < K by omega, show K + 1 < K + 2 by omega, hyK (K + 1) (by omega)])
    K 0 (by omega)
  apply Nat.eq_of_testBit_eq
  intro i
  rw [hbits]
  simp only [fl_testBit, rotDown_testBit, testBit_blk _ _ _ _ hyB, testBit_blk _ _ _ _ hrB]
  rcases Nat.lt_or_ge i K with h | h
  · have e1 : K ≠ i := by omega
    have e2 : K + 1 ≠ i := by omega
    simp [h, e1, e2, show i < K + 2 by omega]
  · rcases Nat.lt_or_ge K i with h' | h'
    · rcases Nat.lt_or_ge (K + 1) i with h'' | h''
      · have e1 : K - 1 ≠ i := by omega
        have e2 : K + 1 ≠ i := by omega
        have e3 : K ≠ i := by omega
        simp [show ¬ i < K by omega, show i ≠ K by omega, e1, e2, e3, show ¬ i < K + 2 by omega]
      · have hi : i = K + 1 := by omega
        subst hi
        have e1 : K - 1 ≠ K + 1 := by omega
        simp [e1, show ¬ K + 1 < K by omega, show K + 1 < K + 2 by omega, hyK (K + 1) (by omega),
          hrK (K + 1) (by omega)]
    · have hi : i = K := by omega
      subst hi
      simp [show i < i + 2 by omega, hrK i (Nat.le_refl _)]

theorem fl_blk {p K : Nat} (v : Bool) (φ x : Nat) (hp : p < K + 2) (hx : x < 2 ^ (K + 2)) :
    fl p v (φ * 2 ^ (K + 2) + x) = φ * 2 ^ (K + 2) + fl p v x := by
  have hfx : fl p v x < 2 ^ (K + 2) := by
    have := fl_lt (P := 1) (K := K) v hp (by rw [Nat.one_mul]; exact hx)
    rwa [Nat.one_mul] at this
  apply Nat.eq_of_testBit_eq
  intro i
  rw [fl_testBit, testBit_blk _ _ _ _ hx, testBit_blk _ _ _ _ hfx, fl_testBit]
  by_cases hi : i < K + 2
  · rw [ite_eq_left hi, ite_eq_left hi]
  · rw [ite_eq_right hi, ite_eq_right hi, decide_eq_false (show p ≠ i by omega)]
    simp

theorem fl_lt_blk {p K : Nat} (v : Bool) (x : Nat) (hp : p < K + 2) (hx : x < 2 ^ (K + 2)) :
    fl p v x < 2 ^ (K + 2) := by
  have := fl_lt (P := 1) (K := K) v hp (by rw [Nat.one_mul]; exact hx)
  rwa [Nat.one_mul] at this

theorem valid_reverse {K : Nat} {l : List (Nat × Nat × Nat)} (h : ∀ f ∈ l, ValidFlip K f) :
    ∀ f ∈ l.reverse, ValidFlip K f := fun f hf => h f (List.mem_reverse.mp hf)

/-- **The preimage contains every node with a move into the set.** -/
theorem pre_sound (b : List Bool) (K : Nat) (hK : 1 ≤ K) (Y φ r : Nat) (u : Bool) (hφ : φ < b.length)
    (hr : r < 2 ^ K) (hY : Y.testBit ((φ + 1) % b.length * 2 ^ (K + 2) + GameMask.move K (col b φ) u r) = true) :
    (pre b K Y).testBit (φ * 2 ^ (K + 2) + r) = true := by
  have hP : 0 < b.length := by omega
  have hB := Nat.two_pow_pos (K + 2)
  have hKB : 2 ^ K ≤ 2 ^ (K + 2) := Nat.pow_le_pow_right (by decide) (by omega)
  have hy := move_lt K (col b φ) u r
  have hyB : GameMask.move K (col b φ) u r < 2 ^ (K + 2) := by omega
  have hrB : r < 2 ^ (K + 2) := by omega
  have hyK : ∀ i, K ≤ i → (GameMask.move K (col b φ) u r).testBit i = false := fun i hi =>
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hy (Nat.pow_le_pow_right (by decide) hi))
  have hrK : ∀ i, K ≤ i → r.testBit i = false := fun i hi =>
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hr (Nat.pow_le_pow_right (by decide) hi))
  have hgB := blk_lt hφ hrB
  have hK0 : K < K + 2 := by omega
  have hK1 : K + 1 < K + 2 := by omega
  -- 1. the canonical form reads the start itself
  have hgK : (φ * 2 ^ (K + 2) + r).testBit K = false := by
    rw [testBit_blk _ _ _ _ hrB, ite_eq_left hK0]; exact hrK K (Nat.le_refl _)
  have hgK1 : (φ * 2 ^ (K + 2) + r).testBit (K + 1) = false := by
    rw [testBit_blk _ _ _ _ hrB, ite_eq_left hK1]; exact hrK (K + 1) (by omega)
  let V := applyFlips b.length K (applySwaps b.length K (shiftDown b.length K (canon b.length K Y)) (rotDown K).reverse)
    (phis K 0 K).reverse
  show (canon b.length K (proj b.length K (proj b.length K (Nat.land V (colMask b K)) (K + 1)) K)).testBit _ = true
  rw [canon_testBit _ _ _ _ hgB, clr_of_false hgK1, clr_of_false hgK]
  -- 2. the projections: put the column at bit `K` and the free cell at bit `K + 1`
  have hz1B : fl K (col b φ) (φ * 2 ^ (K + 2) + r) < b.length * 2 ^ (K + 2) := fl_lt _ hK0 hgB
  have hz0B : fl (K + 1) u (fl K (col b φ) (φ * 2 ^ (K + 2) + r)) < b.length * 2 ^ (K + 2) := fl_lt _ hK1 hz1B
  suffices hM : (Nat.land V (colMask b K)).testBit (fl (K + 1) u (fl K (col b φ) (φ * 2 ^ (K + 2) + r))) = true by
    rw [proj_testBit _ _ _ _ _ hK0 hgB]
    have key : (proj b.length K (Nat.land V (colMask b K)) (K + 1)).testBit (fl K (col b φ) (φ * 2 ^ (K + 2) + r))
        = true := by
      rw [proj_testBit _ _ _ _ _ hK1 hz1B]
      cases u
      · rw [fl_false] at hM; rw [hM, Bool.true_or]
      · rw [fl_true] at hM; rw [hM, Bool.or_true]
    cases hc : col b φ
    · rw [hc, fl_false] at key; rw [key, Bool.true_or]
    · rw [hc, fl_true] at key; rw [key, Bool.or_true]
  -- 3. the column check: bit `K` is the column of block `φ`
  have hz0 : fl (K + 1) u (fl K (col b φ) (φ * 2 ^ (K + 2) + r)) =
      φ * 2 ^ (K + 2) + fl (K + 1) u (fl K (col b φ) r) := by
    rw [fl_blk _ _ _ hK0 hrB, fl_blk _ _ _ hK1 (fl_lt_blk _ _ hK0 hrB)]
  have hlowB : fl (K + 1) u (fl K (col b φ) r) < 2 ^ (K + 2) := fl_lt_blk _ _ hK1 (fl_lt_blk _ _ hK0 hrB)
  show (V &&& colMask b K).testBit _ = true
  rw [Nat.testBit_and, colMask_testBit _ _ _ hz0B]
  have hcol : ((fl (K + 1) u (fl K (col b φ) (φ * 2 ^ (K + 2) + r))).testBit K ==
      col b (fl (K + 1) u (fl K (col b φ) (φ * 2 ^ (K + 2) + r)) / 2 ^ (K + 2))) = true := by
    rw [hz0, Nat.mul_comm, Nat.mul_add_div hB, Nat.div_eq_of_lt hlowB, Nat.add_zero, ← Nat.mul_comm,
      testBit_blk _ _ _ _ hlowB, ite_eq_left hK0, fl_testBit, fl_testBit, decide_eq_false (show K + 1 ≠ K by omega),
      decide_eq_true rfl, hrK K (Nat.le_refl _)]
    simp
  rw [hcol, Bool.and_true]
  -- 4. undo the flips: the rotated move
  rw [applyFlips_spec _ _ _ _ (valid_reverse (phis_valid hK K 0 (by omega))) _ hz0B,
    ← undo_move K hK φ r (col b φ) u hr, idxFlips_reverse_cancel _ (phis_valid hK K 0 (by omega))]
  have hvB := blk_lt hφ hyB
  have hh'B : fl (K - 1) (r.testBit (K - 1)) (fl (K + 1) u (idxSwaps (rotDown K)
      (φ * 2 ^ (K + 2) + GameMask.move K (col b φ) u r))) < b.length * 2 ^ (K + 2) :=
    fl_lt _ (by omega) (fl_lt _ hK1 (idxSwaps_lt _ (rotDown_valid K (by omega)) _ hvB))
  rw [applySwaps_spec _ _ _ _ (fun i hi => rotDown_valid K (by omega) i (List.mem_reverse.mp hi)) _ hh'B, rot_move K hK,
    idxSwaps_reverse_cancel]
  -- 5. block `φ` reads block `φ + 1` of the canonical `Y`
  have hw : fl (K + 1) u (fl K (r.testBit (K - 1)) (φ * 2 ^ (K + 2) + GameMask.move K (col b φ) u r)) =
      φ * 2 ^ (K + 2) + fl (K + 1) u (fl K (r.testBit (K - 1)) (GameMask.move K (col b φ) u r)) := by
    rw [fl_blk _ _ _ hK0 hyB, fl_blk _ _ _ hK1 (fl_lt_blk _ _ hK0 hyB)]
  have hw'B : fl (K + 1) u (fl K (r.testBit (K - 1)) (GameMask.move K (col b φ) u r)) < 2 ^ (K + 2) :=
    fl_lt_blk _ _ hK1 (fl_lt_blk _ _ hK0 hyB)
  rw [hw, shiftDown_testBit _ _ _ _ hP (blk_lt hφ hw'B)]
  -- clearing bits `K` and `K + 1` of the low part leaves the move
  have hclr : ∀ q, q < b.length → clr K (clr (K + 1) (q * 2 ^ (K + 2) +
      fl (K + 1) u (fl K (r.testBit (K - 1)) (GameMask.move K (col b φ) u r)))) =
      q * 2 ^ (K + 2) + GameMask.move K (col b φ) u r := fun q _ => by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [clr_testBit, clr_testBit, testBit_blk _ _ _ _ hw'B, testBit_blk _ _ _ _ hyB]
    by_cases hi : i < K + 2
    · rw [ite_eq_left hi, ite_eq_left hi, fl_testBit, fl_testBit]
      by_cases hiK : i = K
      · subst hiK; simp [hyK i (Nat.le_refl _)]
      · by_cases hiK1 : i = K + 1
        · subst hiK1; simp [hyK (K + 1) (by omega)]
        · simp [Ne.symm hiK, Ne.symm hiK1]
    · rw [ite_eq_right hi, ite_eq_right hi, decide_eq_false (show K ≠ i by omega),
        decide_eq_false (show K + 1 ≠ i by omega)]
      simp
  by_cases hlast : φ + 1 = b.length
  · rw [ite_eq_right (show ¬ φ * 2 ^ (K + 2) + _ < (b.length - 1) * 2 ^ (K + 2) by
        rw [show b.length - 1 = φ by omega]; omega),
      show φ * 2 ^ (K + 2) + fl (K + 1) u (fl K (r.testBit (K - 1)) (GameMask.move K (col b φ) u r)) -
        (b.length - 1) * 2 ^ (K + 2) = 0 * 2 ^ (K + 2) + fl (K + 1) u (fl K (r.testBit (K - 1))
          (GameMask.move K (col b φ) u r)) by rw [show b.length - 1 = φ by omega]; omega,
      canon_testBit _ _ _ _ (blk_lt hP hw'B), hclr 0 hP]
    rw [hlast, Nat.mod_self] at hY
    exact hY
  · have hlt : φ + 1 < b.length := by omega
    have h1 : φ * 2 ^ (K + 2) + fl (K + 1) u (fl K (r.testBit (K - 1)) (GameMask.move K (col b φ) u r)) <
        (b.length - 1) * 2 ^ (K + 2) := by
      have : (φ + 1) * 2 ^ (K + 2) ≤ (b.length - 1) * 2 ^ (K + 2) := Nat.mul_le_mul_right _ (by omega)
      rw [Nat.succ_mul] at this
      omega
    rw [ite_eq_left h1, show φ * 2 ^ (K + 2) + fl (K + 1) u (fl K (r.testBit (K - 1)) (GameMask.move K (col b φ) u r)) +
        2 ^ (K + 2) = (φ + 1) * 2 ^ (K + 2) + fl (K + 1) u (fl K (r.testBit (K - 1))
          (GameMask.move K (col b φ) u r)) by rw [Nat.succ_mul]; omega,
      canon_testBit _ _ _ _ (blk_lt hlt hw'B), hclr (φ + 1) hlt]
    rw [Nat.mod_eq_of_lt hlt] at hY
    exact hY

/-! ### The decision -/

/-- `n` images of every node. -/
def reach (b : List Bool) (K : Nat) : Nat → Nat
  | 0 => full b.length K
  | n + 1 => post b K (reach b K n)

/-- Block `φ` of a table, as a table of one block. -/
def getBlock (K X φ : Nat) : Nat :=
  Nat.land (Nat.shiftRight X (Nat.mul φ (2 ^ (K + 2)))) (Nat.sub (2 ^ (2 ^ (K + 2))) 1)

/-- Tables of one block, side by side. -/
def packList (K : Nat) : List Nat → Nat
  | [] => 0
  | x :: rest => Nat.lor x (Nat.shiftLeft (packList K rest) (2 ^ (K + 2)))

/-- A forward search from a frontier at phase `ψ`, one phase per step, with the game of one block at each phase:
the sets found so far, phase by phase. Only the check of its result matters. -/
def bfsF (b : List Bool) (K : Nat) : Nat → List Nat → Nat → Nat → List Nat
  | 0, C, _, _ => C
  | n + 1, C, ψ, front =>
    let ψ' := (ψ + 1) % b.length
    let old := C.getD ψ' 0
    let new := Nat.land (post [col b ψ] K front) (Nat.xor (full 1 K) old)
    cond (Nat.beq new 0) C (bfsF b K n (C.set ψ' (Nat.lor old new)) ψ' new)

/-- The same backward, with the preimage. -/
def bfsB (b : List Bool) (K : Nat) : Nat → List Nat → Nat → Nat → List Nat
  | 0, C, _, _ => C
  | n + 1, C, ψ, front =>
    let ψ' := (ψ + b.length - 1) % b.length
    let old := C.getD ψ' 0
    let new := Nat.land (pre [col b ψ'] K front) (Nat.xor (full 1 K) old)
    cond (Nat.beq new 0) C (bfsB b K n (C.set ψ' (Nat.lor old new)) ψ' new)

/-- The nodes reachable from the nodes of `A` at phase `φ`, by the search. -/
def fwdClose (b : List Bool) (K fuel A φ : Nat) : Nat :=
  packList K (bfsF b K fuel (List.replicate b.length 0) φ (getBlock K A φ))

/-- The nodes that reach the nodes of `A` at phase `φ`, by the search. -/
def bwdClose (b : List Bool) (K fuel A φ : Nat) : Nat :=
  packList K (bfsB b K fuel (List.replicate b.length 0) φ (getBlock K A φ))

/-- `F` holds its own image. -/
def closedF (b : List Bool) (K F : Nat) : Bool := Nat.beq (Nat.lor F (post b K F)) F

/-- `G` holds its own preimage. -/
def closedB (b : List Bool) (K G : Nat) : Bool := Nat.beq (Nat.lor G (pre b K G)) G

/-- `F` holds the image of `A`, and its own. -/
def fwdOk (b : List Bool) (K A F : Nat) : Bool := Nat.beq (Nat.lor F (post b K A)) F && closedF b K F

/-- `G` holds the preimage of `A`, and its own. -/
def bwdOk (b : List Bool) (K A G : Nat) : Bool := Nat.beq (Nat.lor G (pre b K A)) G && closedB b K G

/-- The refinement at phase `φ`: `A` and `B` are the nodes of the two values. Keep the nodes of each value that the
other value's nodes reach and that reach them, until one side is empty. -/
def refine (b : List Bool) (K fuel φ : Nat) : Nat → Nat → Nat → Bool
  | 0, A, B => Nat.beq A 0 || Nat.beq B 0
  | n + 1, A, B =>
    Nat.beq A 0 || Nat.beq B 0 ||
      (let FA := fwdClose b K fuel A φ
       let FB := fwdClose b K fuel B φ
       let GA := bwdClose b K fuel A φ
       let GB := bwdClose b K fuel B φ
       fwdOk b K A FA && fwdOk b K B FB && bwdOk b K A GA && bwdOk b K B GB &&
         refine b K fuel φ n (Nat.land A (Nat.land FB GB)) (Nat.land B (Nat.land FA GA)))

/-- **The check.** After `D` images of everything, at each phase, the refinement empties one value's nodes within
`rounds` rounds, with closures of at most `fuel` steps. -/
def gameCheck (b : List Bool) (K D rounds fuel : Nat) : Bool :=
  Nat.ble 1 K && Nat.ble 1 b.length &&
    (List.range b.length).all fun φ =>
      let m := Nat.land (reach b K D) (blockSel K (fun ψ => Nat.beq ψ φ) b.length)
      refine b K fuel φ rounds (Nat.land m (Nat.xor (full b.length K) (valMask b K))) (Nat.land m (valMask b K))

/-! ### Closures -/

theorem fwdOk_spec {b : List Bool} {K A F : Nat} (h : fwdOk b K A F = true) :
    (∀ g, (post b K A).testBit g = true → F.testBit g = true) ∧ closedF b K F = true := by
  unfold fwdOk at h
  rw [Bool.and_eq_true] at h
  refine ⟨fun g hg => ?_, h.2⟩
  have e : F ||| post b K A = F := Nat.eq_of_beq_eq_true h.1
  rw [← e, Nat.testBit_or, hg, Bool.or_true]

theorem bwdOk_spec {b : List Bool} {K A G : Nat} (h : bwdOk b K A G = true) :
    (∀ g, (pre b K A).testBit g = true → G.testBit g = true) ∧ closedB b K G = true := by
  unfold bwdOk at h
  rw [Bool.and_eq_true] at h
  refine ⟨fun g hg => ?_, h.2⟩
  have e : G ||| pre b K A = G := Nat.eq_of_beq_eq_true h.1
  rw [← e, Nat.testBit_or, hg, Bool.or_true]

theorem closedF_spec {b : List Bool} {K F : Nat} (h : closedF b K F = true) (g : Nat) (hg : (post b K F).testBit g = true) :
    F.testBit g = true := by
  have e : F ||| post b K F = F := Nat.eq_of_beq_eq_true h
  rw [← e, Nat.testBit_or, hg, Bool.or_true]

theorem closedB_spec {b : List Bool} {K G : Nat} (h : closedB b K G = true) (g : Nat) (hg : (pre b K G).testBit g = true) :
    G.testBit g = true := by
  have e : G ||| pre b K G = G := Nat.eq_of_beq_eq_true h
  rw [← e, Nat.testBit_or, hg, Bool.or_true]

/-! ### The real row as a play -/

/-- The node of the real row at time `t`: the block of its phase and the cells `k + 1, …, k + K`. -/
def pos (init : Int → Bool) (b : List Bool) (K : Nat) (k : Int) (shift t : Nat) : Nat :=
  (t + shift) % b.length * 2 ^ (K + 2) + codeFrom init t (k + 1) K

/-- **A play follows the moves.** If column `k` repeats `b` from time `T`, the node at time `t + 1` is a move of the
node at time `t`, so it is in the image of any set that holds the node at `t`, and the node at `t` is in the
preimage of any set that holds the node at `t + 1`. -/
theorem play_step (init : Int → Bool) (b : List Bool) (K : Nat) (hK : 1 ≤ K) (k : Int) (T shift : Nat)
    (hP : 0 < b.length) (h : ∀ t : Nat, T ≤ t → evolve init t k = col b (t + shift)) (t : Nat) (ht : T ≤ t) :
    (∀ X, X.testBit (pos init b K k shift t) = true → (post b K X).testBit (pos init b K k shift (t + 1)) = true) ∧
    (∀ Y, Y.testBit (pos init b K k shift (t + 1)) = true → (pre b K Y).testBit (pos init b K k shift t) = true) := by
  have hφ : (t + shift) % b.length < b.length := Nat.mod_lt _ hP
  have hc : col b ((t + shift) % b.length) = evolve init t k := by
    rw [h t ht]; unfold col; rw [Nat.mod_mod]
  have hcode : codeFrom init (t + 1) (k + 1) K =
      GameMask.move K (col b ((t + shift) % b.length)) (evolve init t (k + 1 + K)) (codeFrom init t (k + 1) K) := by
    rw [codeFrom_succ, GameMask.move_eq, show k + 1 - 1 = k by omega, hc]
  have hph : (t + 1 + shift) % b.length = ((t + shift) % b.length + 1) % b.length := by
    rw [mod_succ_mod, show t + 1 + shift = t + shift + 1 by omega]
  have hr := codeFrom_lt init t K (k + 1)
  refine ⟨fun X hX => ?_, fun Y hY => ?_⟩
  · have := post_sound b K hK X _ _ (evolve init t (k + 1 + K)) hφ hr hX
    unfold pos
    rw [hph, hcode]
    exact this
  · unfold pos at hY
    rw [hph, hcode] at hY
    exact pre_sound b K hK Y _ _ _ hφ hr hY

theorem pos_lt (init : Int → Bool) (b : List Bool) (K : Nat) (k : Int) (shift t : Nat) (hP : 0 < b.length) :
    pos init b K k shift t < b.length * 2 ^ (K + 2) :=
  blk_lt (Nat.mod_lt _ hP) (Nat.lt_of_lt_of_le (codeFrom_lt init t K (k + 1)) (Nat.pow_le_pow_right (by decide)
    (by omega)))

/-- **After `n` steps the play is in `n` images of everything.** -/
theorem play_reach (init : Int → Bool) (b : List Bool) (K : Nat) (hK : 1 ≤ K) (k : Int) (T shift : Nat)
    (hP : 0 < b.length) (h : ∀ t : Nat, T ≤ t → evolve init t k = col b (t + shift)) :
    ∀ n t, T + n ≤ t → (reach b K n).testBit (pos init b K k shift t) = true := by
  intro n
  induction n with
  | zero =>
    intro t _
    show (full b.length K).testBit _ = true
    rw [full_testBit]; exact decide_eq_true (pos_lt init b K k shift t hP)
  | succ n ih =>
    intro t ht
    obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    exact (play_step init b K hK k T shift hP h t' (by omega)).1 _ (ih t' (by omega))

/-- **A closed forward set holds the play after any visit to its seed.** -/
theorem play_fwd (init : Int → Bool) (b : List Bool) (K : Nat) (hK : 1 ≤ K) (k : Int) (T shift : Nat)
    (hP : 0 < b.length) (h : ∀ t : Nat, T ≤ t → evolve init t k = col b (t + shift)) (C F : Nat)
    (hseed : ∀ g, (post b K C).testBit g = true → F.testBit g = true) (hclosed : closedF b K F = true)
    (t1 : Nat) (ht1 : T ≤ t1) (hC : C.testBit (pos init b K k shift t1) = true) :
    ∀ n, F.testBit (pos init b K k shift (t1 + 1 + n)) = true := by
  intro n
  induction n with
  | zero => exact hseed _ ((play_step init b K hK k T shift hP h t1 ht1).1 C hC)
  | succ n ih =>
    rw [show t1 + 1 + (n + 1) = t1 + 1 + n + 1 by omega]
    exact closedF_spec hclosed _ ((play_step init b K hK k T shift hP h _ (by omega)).1 F ih)

/-- **A closed backward set holds the play before any visit to its seed.** -/
theorem play_bwd (init : Int → Bool) (b : List Bool) (K : Nat) (hK : 1 ≤ K) (k : Int) (T shift : Nat)
    (hP : 0 < b.length) (h : ∀ t : Nat, T ≤ t → evolve init t k = col b (t + shift)) (C G : Nat)
    (hseed : ∀ g, (pre b K C).testBit g = true → G.testBit g = true) (hclosed : closedB b K G = true)
    (t2 : Nat) (hC : C.testBit (pos init b K k shift t2) = true) :
    ∀ t1, T ≤ t1 → t1 < t2 → G.testBit (pos init b K k shift t1) = true := by
  intro t1 ht1 hlt
  obtain ⟨n, rfl⟩ : ∃ n, t2 = t1 + 1 + n := ⟨t2 - t1 - 1, by omega⟩
  induction n generalizing t1 with
  | zero => exact hseed _ ((play_step init b K hK k T shift hP h t1 ht1).2 C hC)
  | succ n ih =>
    have := ih (t1 + 1) (by omega) (by rw [show t1 + 1 + 1 + n = t1 + 1 + (n + 1) by omega]; exact hC) (by omega)
    exact closedB_spec hclosed _ ((play_step init b K hK k T shift hP h t1 ht1).2 G this)

/-- **The refinement keeps two nodes that the play visits again and again.** If the play passes `ga` and then `gb`
after any time, and `gb` and then `ga`, both stay through every round, so the refinement cannot empty a side. -/
theorem refine_sound (init : Int → Bool) (b : List Bool) (K : Nat) (hK : 1 ≤ K) (k : Int) (T shift : Nat)
    (hP : 0 < b.length) (h : ∀ t : Nat, T ≤ t → evolve init t k = col b (t + shift)) (fuel φ ga gb : Nat)
    (hab : ∀ N, ∃ t1 t2, N ≤ t1 ∧ t1 < t2 ∧ pos init b K k shift t1 = ga ∧ pos init b K k shift t2 = gb)
    (hba : ∀ N, ∃ t1 t2, N ≤ t1 ∧ t1 < t2 ∧ pos init b K k shift t1 = gb ∧ pos init b K k shift t2 = ga) :
    ∀ n A B, A.testBit ga = true → B.testBit gb = true → refine b K fuel φ n A B = false := by
  have hzero : ∀ X g, X.testBit g = true → Nat.beq X 0 = false := fun X g hX => by
    cases e : Nat.beq X 0
    · rfl
    · rw [Nat.eq_of_beq_eq_true e, Nat.zero_testBit] at hX; exact absurd hX (by decide)
  -- a set reached from `C` and closed holds every later visit; one reaching `C` and closed, every earlier one
  have fwdHolds : ∀ (C F : Nat), fwdOk b K C F = true → ∀ gc gd,
      (∀ N, ∃ t1 t2, N ≤ t1 ∧ t1 < t2 ∧ pos init b K k shift t1 = gc ∧ pos init b K k shift t2 = gd) →
      C.testBit gc = true → F.testBit gd = true := fun C F hok gc gd hvis hC => by
    obtain ⟨hseed, hclosed⟩ := fwdOk_spec hok
    obtain ⟨t1, t2, ht1, hlt, e1, e2⟩ := hvis T
    have := play_fwd init b K hK k T shift hP h C F hseed hclosed t1 ht1 (e1 ▸ hC) (t2 - t1 - 1)
    rwa [show t1 + 1 + (t2 - t1 - 1) = t2 by omega, e2] at this
  have bwdHolds : ∀ (C G : Nat), bwdOk b K C G = true → ∀ gc gd,
      (∀ N, ∃ t1 t2, N ≤ t1 ∧ t1 < t2 ∧ pos init b K k shift t1 = gd ∧ pos init b K k shift t2 = gc) →
      C.testBit gc = true → G.testBit gd = true := fun C G hok gc gd hvis hC => by
    obtain ⟨hseed, hclosed⟩ := bwdOk_spec hok
    obtain ⟨t1, t2, ht1, hlt, e1, e2⟩ := hvis T
    have := play_bwd init b K hK k T shift hP h C G hseed hclosed t2 (e2 ▸ hC) t1 ht1 hlt
    rwa [e1] at this
  intro n
  induction n with
  | zero =>
    intro A B hA hB
    show (Nat.beq A 0 || Nat.beq B 0) = false
    rw [hzero A ga hA, hzero B gb hB]; rfl
  | succ n ih =>
    intro A B hA hB
    show (Nat.beq A 0 || Nat.beq B 0 || (fwdOk b K A (fwdClose b K fuel A φ) && fwdOk b K B (fwdClose b K fuel B φ) &&
      bwdOk b K A (bwdClose b K fuel A φ) && bwdOk b K B (bwdClose b K fuel B φ) &&
      refine b K fuel φ n (Nat.land A (Nat.land (fwdClose b K fuel B φ) (bwdClose b K fuel B φ)))
        (Nat.land B (Nat.land (fwdClose b K fuel A φ) (bwdClose b K fuel A φ))))) = false
    rw [hzero A ga hA, hzero B gb hB, Bool.false_or, Bool.false_or]
    cases cFA : fwdOk b K A (fwdClose b K fuel A φ) <;>
      cases cFB : fwdOk b K B (fwdClose b K fuel B φ) <;>
      cases cGA : bwdOk b K A (bwdClose b K fuel A φ) <;>
      cases cGB : bwdOk b K B (bwdClose b K fuel B φ) <;> simp only [Bool.false_and, Bool.and_false,
        Bool.true_and]
    -- every closure passed its checks: the two nodes survive the round
    apply ih
    · show (A &&& ((fwdClose b K fuel B φ) &&& (bwdClose b K fuel B φ))).testBit ga = true
      rw [Nat.testBit_and, Nat.testBit_and, hA, fwdHolds B _ cFB gb ga hba hB, bwdHolds B _ cGB gb ga hab hB]
      rfl
    · show (B &&& ((fwdClose b K fuel A φ) &&& (bwdClose b K fuel A φ))).testBit gb = true
      rw [Nat.testBit_and, Nat.testBit_and, hB, fwdHolds A _ cFA ga gb hab hA, bwdHolds A _ cGA ga gb hba hA]
      rfl

/-! ### The column left of `k` repeats -/

/-- **Pigeonhole.** If times with property `Q` and a value of `f` below `M` keep coming, one value keeps coming. -/
theorem pigeonhole (Q : Nat → Prop) (f : Nat → Nat) :
    ∀ M, (∀ N, ∃ t, N ≤ t ∧ Q t ∧ f t < M) → ∃ v, v < M ∧ ∀ N, ∃ t, N ≤ t ∧ Q t ∧ f t = v := by
  intro M
  induction M with
  | zero => intro h; obtain ⟨t, -, -, h0⟩ := h 0; exact absurd h0 (Nat.not_lt_zero _)
  | succ M ih =>
    intro h
    by_cases hM : ∀ N, ∃ t, N ≤ t ∧ Q t ∧ f t = M
    · exact ⟨M, Nat.lt_succ_self M, hM⟩
    · have hfin : ∃ N0, ∀ t, N0 ≤ t → Q t → f t ≠ M := by
        refine Classical.byContradiction fun hc => hM fun N => ?_
        refine Classical.byContradiction fun hn => hc ⟨N, fun t ht hq hf => hn ⟨t, ht, hq, hf⟩⟩
      obtain ⟨N0, hN0⟩ := hfin
      obtain ⟨v, hv, hrec⟩ := ih fun N => by
        obtain ⟨t, ht, hq, hf⟩ := h (N + N0)
        exact ⟨t, by omega, hq, by have := hN0 t (by omega) hq; omega⟩
      exact ⟨v, by omega, hrec⟩

/-- A bound for each of finitely many phases gives one bound for all. -/
theorem common_bound (R : Nat → Nat → Prop) (hmono : ∀ φ N N', N ≤ N' → R φ N → R φ N') :
    ∀ P, (∀ φ, φ < P → ∃ N, R φ N) → ∃ N, ∀ φ, φ < P → R φ N := by
  intro P
  induction P with
  | zero => intro _; exact ⟨0, fun φ hφ => absurd hφ (Nat.not_lt_zero _)⟩
  | succ P ih =>
    intro h
    obtain ⟨N1, h1⟩ := ih fun φ hφ => h φ (by omega)
    obtain ⟨N2, h2⟩ := h P (Nat.lt_succ_self P)
    refine ⟨N1 + N2, fun φ hφ => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hφ with hlt | heq
    · exact hmono φ N1 _ (by omega) (h1 φ hlt)
    · exact heq ▸ hmono P N2 _ (by omega) h2

theorem testBit_zero_blk (φ r K : Nat) : (φ * 2 ^ (K + 2) + r).testBit 0 = r.testBit 0 := by
  rw [Nat.testBit_zero, Nat.testBit_zero, Nat.add_mod, Nat.mul_mod, show 2 ^ (K + 2) % 2 = 0 by
    rw [Nat.pow_succ, Nat.mul_mod_left]]
  simp

end BitGame

open BitGame

/-- **No column repeats a block that the check decides**, in the orbit of a row with a leftmost 1, from any time on and
in any rotation. -/
theorem bitGame_column (init : Int → Bool) (m : Int) (hm : init m = true) (hz : ∀ x : Int, x < m → init x = false)
    (b : List Bool) (K D rounds fuel : Nat) (hc : gameCheck b K D rounds fuel = true) (k : Int) (T shift : Nat)
    (h : ∀ t : Nat, T ≤ t → evolve init t k = col b (t + shift)) : False := by
  unfold gameCheck at hc
  simp only [Bool.and_eq_true, Nat.ble_eq, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨hK, hP⟩, hall⟩ := hc
  have hB := Nat.two_pow_pos (K + 2)
  have hKB : 2 ^ K < 2 ^ (K + 2) := Nat.pow_lt_pow_right (by decide) (by omega)
  let phase : Nat → Nat := fun t => (t + shift) % b.length
  let code : Nat → Nat := fun t => codeFrom init t (k + 1) K
  have hcode : ∀ t, code t < 2 ^ K := fun t => codeFrom_lt init t K (k + 1)
  have hpos : ∀ t, pos init b K k shift t = phase t * 2 ^ (K + 2) + code t := fun t => rfl
  -- the column left of `k` is the value of the node
  have hleft : ∀ t, T ≤ t → evolve init t (k - 1) = value b (phase t) (code t) := fun t ht => by
    rw [left_cell init t k, h (t + 1) (by omega), h t ht]
    unfold value col
    have e1 : (t + 1 + shift) % b.length = (phase t + 1) % b.length := by
      show _ = ((t + shift) % b.length + 1) % b.length
      rw [mod_succ_mod, show t + 1 + shift = t + shift + 1 by omega]
    have e2 : (t + shift) % b.length = phase t % b.length := by
      show _ = (t + shift) % b.length % b.length; rw [Nat.mod_mod]
    rw [e1, e2, testBit_codeFrom, decide_eq_true (by omega), Bool.true_and, show k + 1 + ((0 : Nat) : Int) = k + 1 by
      omega]
  -- at each phase the value is eventually constant
  have hconst : ∀ φ, φ < b.length → ∃ N, ∀ t1 t2, N ≤ t1 → N ≤ t2 → phase t1 = φ → phase t2 = φ →
      value b φ (code t1) = value b φ (code t2) := by
    intro φ hφ
    refine Classical.byContradiction fun hno => ?_
    -- otherwise both values recur at phase `φ`
    have hrec : ∀ v : Bool, ∀ N, ∃ t, N ≤ t ∧ phase t = φ ∧ value b φ (code t) = v := by
      intro v N
      refine Classical.byContradiction fun hn => hno ⟨N + T + D + 1, fun t1 t2 h1 h2 e1 e2 => ?_⟩
      have a1 : value b φ (code t1) = !v := by
        cases hv : value b φ (code t1)
        · cases v
          · exact absurd ⟨t1, by omega, e1, hv⟩ hn
          · rfl
        · cases v
          · rfl
          · exact absurd ⟨t1, by omega, e1, hv⟩ hn
      have a2 : value b φ (code t2) = !v := by
        cases hv : value b φ (code t2)
        · cases v
          · exact absurd ⟨t2, by omega, e2, hv⟩ hn
          · rfl
        · cases v
          · rfl
          · exact absurd ⟨t2, by omega, e2, hv⟩ hn
      rw [a1, a2]
    -- a node of each value is visited again and again
    have hvisit : ∀ v : Bool, ∃ r, r < 2 ^ K ∧ value b φ r = v ∧ ∀ N, ∃ t, N ≤ t ∧ phase t = φ ∧ code t = r := by
      intro v
      obtain ⟨r, hr, hr'⟩ := pigeonhole (fun t => phase t = φ ∧ value b φ (code t) = v) code (2 ^ K)
        (fun N => by obtain ⟨t, ht, e, ev⟩ := hrec v N; exact ⟨t, ht, ⟨e, ev⟩, hcode t⟩)
      refine ⟨r, hr, ?_, fun N => ?_⟩
      · obtain ⟨t, -, ⟨-, ev⟩, ec⟩ := hr' 0
        rw [← ec]; exact ev
      · obtain ⟨t, ht, ⟨e, -⟩, ec⟩ := hr' N
        exact ⟨t, ht, e, ec⟩
    obtain ⟨ra, hra, va, visA⟩ := hvisit false
    obtain ⟨rb, hrb, vb, visB⟩ := hvisit true
    have hraB : ra < 2 ^ (K + 2) := by omega
    have hrbB : rb < 2 ^ (K + 2) := by omega
    -- visits as positions, in either order
    have order : ∀ r r', (∀ N, ∃ t, N ≤ t ∧ phase t = φ ∧ code t = r) → (∀ N, ∃ t, N ≤ t ∧ phase t = φ ∧ code t = r') →
        ∀ N, ∃ t1 t2, N ≤ t1 ∧ t1 < t2 ∧ pos init b K k shift t1 = φ * 2 ^ (K + 2) + r ∧
          pos init b K k shift t2 = φ * 2 ^ (K + 2) + r' := fun r r' hr hr' N => by
      obtain ⟨t1, ht1, e1, c1⟩ := hr N
      obtain ⟨t2, ht2, e2, c2⟩ := hr' (t1 + 1)
      exact ⟨t1, t2, ht1, by omega, by rw [hpos, e1, c1], by rw [hpos, e2, c2]⟩
    have hrefine := refine_sound init b K hK k T shift hP h fuel φ _ _ (order ra rb visA visB)
      (order rb ra visB visA) rounds
    -- the two nodes start in their sides
    obtain ⟨tA, htA, eA, cA⟩ := visA (T + D)
    obtain ⟨tB, htB, eB, cB⟩ := visB (T + D)
    have hJA := play_reach init b K hK k T shift hP h D tA htA
    have hJB := play_reach init b K hK k T shift hP h D tB htB
    rw [hpos, eA, cA] at hJA
    rw [hpos, eB, cB] at hJB
    have hgA := blk_lt hφ hraB
    have hgB := blk_lt hφ hrbB
    have hdivA : (φ * 2 ^ (K + 2) + ra) / 2 ^ (K + 2) = φ := by
      rw [Nat.mul_comm, Nat.mul_add_div hB, Nat.div_eq_of_lt hraB, Nat.add_zero]
    have hdivB : (φ * 2 ^ (K + 2) + rb) / 2 ^ (K + 2) = φ := by
      rw [Nat.mul_comm, Nat.mul_add_div hB, Nat.div_eq_of_lt hrbB, Nat.add_zero]
    have hvalA : value b φ (φ * 2 ^ (K + 2) + ra) = value b φ ra := by
      unfold value; rw [testBit_zero_blk]
    have hvalB : value b φ (φ * 2 ^ (K + 2) + rb) = value b φ rb := by
      unfold value; rw [testBit_zero_blk]
    have hfalse := hrefine
      (Nat.land (Nat.land (reach b K D) (blockSel K (fun ψ => Nat.beq ψ φ) b.length))
        (Nat.xor (full b.length K) (valMask b K)))
      (Nat.land (Nat.land (reach b K D) (blockSel K (fun ψ => Nat.beq ψ φ) b.length)) (valMask b K))
      (by
        show ((reach b K D &&& blockSel K (fun ψ => Nat.beq ψ φ) b.length) &&& (full b.length K ^^^ valMask b K)).testBit
          _ = true
        rw [Nat.testBit_and, Nat.testBit_and, Nat.testBit_xor, hJA, blockSel_testBit, full_testBit,
          valMask_testBit _ _ _ hgA, hdivA, hvalA, va, decide_eq_true hgA]
        simp)
      (by
        show ((reach b K D &&& blockSel K (fun ψ => Nat.beq ψ φ) b.length) &&& valMask b K).testBit _ = true
        rw [Nat.testBit_and, Nat.testBit_and, hJB, blockSel_testBit, valMask_testBit _ _ _ hgB, hdivB, hvalB, vb,
          decide_eq_true hgB]
        simp)
    rw [hall φ hφ] at hfalse
    exact Bool.noConfusion hfalse
  -- one bound for every phase
  obtain ⟨N, hN⟩ := common_bound (fun φ N => ∀ t1 t2, N ≤ t1 → N ≤ t2 → phase t1 = φ → phase t2 = φ →
      value b φ (code t1) = value b φ (code t2))
    (fun φ N N' hle hR t1 t2 h1 h2 => hR t1 t2 (by omega) (by omega)) b.length hconst
  have hphase : ∀ t, phase (t + b.length) = phase t := fun t => by
    show (t + b.length + shift) % b.length = (t + shift) % b.length
    rw [show t + b.length + shift = t + shift + b.length by omega, Nat.add_mod_right]
  exact adjacent_columns init m hm hz (k - 1) (N + T) b.length hP
    (fun t ht => by
      rw [hleft (t + b.length) (by omega), hleft t (by omega), hphase t]
      exact hN (phase t) (Nat.mod_lt _ hP) _ _ (by omega) (by omega) (hphase t) rfl)
    (fun t ht => by
      rw [show k - 1 + 1 = k by omega, h (t + b.length) (by omega), h t (by omega)]
      unfold col
      rw [show t + b.length + shift = t + shift + b.length by omega, Nat.add_mod_right])

/-! ### The center column -/

/-- **The center column does not repeat a block that the check decides**, from any time on and in any phase. -/
theorem center_not_bitGame (b : List Bool) (K D rounds fuel : Nat) (hc : gameCheck b K D rounds fuel = true)
    (T shift : Nat) (h : ∀ t : Nat, T ≤ t → Rule30Prize.center t = b.getD ((t + shift) % b.length) false) : False :=
  bitGame_column single 0 rfl (fun x hx => decide_eq_false (by omega)) b K D rounds fuel hc 0 T shift fun t ht => by
    rw [evolve_single_center, h t ht]
    unfold col
    rw [bit_eq_getD]

/-- The same in the kit's form `Rule30StripCertificates.EventuallyWord`, which composes with its
`problem1_iff_no_word`. -/
theorem bitGame_not_eventuallyWord (b : List Bool) (K D rounds fuel : Nat) (hc : gameCheck b K D rounds fuel = true) :
    ¬ Rule30StripCertificates.EventuallyWord b := by
  have hP : 0 < b.length := by
    unfold gameCheck at hc
    simp only [Bool.and_eq_true, Nat.ble_eq] at hc
    exact hc.1.2
  rintro ⟨T, hT⟩
  refine center_not_bitGame b K D rounds fuel hc T (b.length * T - T) fun t ht => ?_
  rw [← evolve_single_center, evolve_single_eq_cell]
  show Rule30Jen.cell t 0 = _
  have hLT : T ≤ b.length * T := Nat.le_mul_of_pos_left T hP
  rw [hT t ht, show t + (b.length * T - T) = t - T + b.length * T by omega, Nat.add_mul_mod_self_left]

/-! ### The seven blocks the certificates left out -/

/-- The blocks of period at most 16 that the game excludes and that `GameBlocks`, `GameBlocksLong` and the kit leave
out, each as its least rotation `wordOf n bits`, with the width `K`, the steps `D`, the rounds and the search fuel of
its check. -/
def restBlocks : List ((Nat × Nat) × (Nat × Nat × Nat × Nat)) := [
    ((14, 0b00000001001111), (13, 127, 4, 300)), ((14, 0b00000000010001), (14, 89, 4, 300)),
    ((15, 0b000000000101101), (14, 75, 5, 300)), ((15, 0b000001011111011), (14, 114, 4, 300)),
    ((16, 0b0000001011111011), (12, 110, 4, 300)), ((16, 0b0000101111111011), (13, 142, 4, 300)),
    ((16, 0b0001011111111001), (14, 95, 5, 300))]

set_option Elab.async false

set_option maxHeartbeats 0 in
theorem check_00000001001111 : gameCheck (Rule30StripCertificateTable.wordOf 14 0b00000001001111) 13 127 4 300 = true :=
  by decide +kernel

set_option maxHeartbeats 0 in
theorem check_00000000010001 : gameCheck (Rule30StripCertificateTable.wordOf 14 0b00000000010001) 14 89 4 300 = true :=
  by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000000000101101 :
    gameCheck (Rule30StripCertificateTable.wordOf 15 0b000000000101101) 14 75 5 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_000001011111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 15 0b000001011111011) 14 114 4 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000001011111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 16 0b0000001011111011) 12 110 4 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0000101111111011 :
    gameCheck (Rule30StripCertificateTable.wordOf 16 0b0000101111111011) 13 142 4 300 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_0001011111111001 :
    gameCheck (Rule30StripCertificateTable.wordOf 16 0b0001011111111001) 14 95 5 300 = true := by decide +kernel

theorem restBlocks_check : ∀ e ∈ restBlocks,
    gameCheck (Rule30StripCertificateTable.wordOf e.1.1 e.1.2) e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2 = true := by
  intro e he
  simp only [restBlocks, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact check_00000001001111
  · exact check_00000000010001
  · exact check_000000000101101
  · exact check_000001011111011
  · exact check_0000001011111011
  · exact check_0000101111111011
  · exact check_0001011111111001

/-- **The seven blocks**: for each entry of `restBlocks`, the center column is not, from any time `T` on, the block
`wordOf n bits`, read from any phase. -/
theorem center_not_restBlocks (e : (Nat × Nat) × (Nat × Nat × Nat × Nat)) (he : e ∈ restBlocks) (T shift : Nat)
    (h : ∀ t : Nat, T ≤ t → Rule30Prize.center t =
      (Rule30StripCertificateTable.wordOf e.1.1 e.1.2).getD ((t + shift) % e.1.1) false) : False :=
  center_not_bitGame _ _ _ _ _ (restBlocks_check e he) T shift fun t ht => by
    rw [h t ht, Rule30StripCertificateTable.wordOf_length]

/-- The same in the kit's form: none of the seven blocks is an `EventuallyWord` of the center column. -/
theorem not_eventually_restBlocks (e : (Nat × Nat) × (Nat × Nat × Nat × Nat)) (he : e ∈ restBlocks) :
    ¬ Rule30StripCertificates.EventuallyWord (Rule30StripCertificateTable.wordOf e.1.1 e.1.2) :=
  bitGame_not_eventuallyWord _ _ _ _ _ (restBlocks_check e he)

end Rule30Open
