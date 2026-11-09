module

public import Rule30Open.Foundations.Evolve

/-!
# Right-moving light-like periodic sets of Rule 30 with positive entropy

`Σ_p` is the set of rows `x` with `F^p x = σ^{-p} x`: after `p` steps the row is itself moved `p` cells to the
right (`LightLike p x`). Rule 30 is left-permutive, so `F^p(x)_i = x_{i-p} xor g_p(x_{i-p+1}, …, x_{i+p})`, and
`Σ_p` is the subshift of finite type on which `g_p` vanishes on every window of `2p` cells. The left-moving sets
`F^p x = σ^p x`, and every velocity slower than light, hold only finitely many rows: a cell is fixed by the `2p`
cells on one side of it. At the speed of light to the right this fails, and `Σ_p` can have positive entropy.

* `blocks L X Y s`: the row whose block `q`, on the cells `L q, …, L q + L - 1`, is the word `X` if `s q` and `Y`
  if not.
* `lightLike_blocks`: if `p ≤ L` and the finite check `checkG p L X Y` passes, **every `blocks L X Y s` satisfies
  `F^p x = σ^{-p} x`.** A cell after `p` steps reads the `2p + 1` cells around it (`iterate_getD`), which lie in
  three consecutive blocks, and `checkG` runs the `8` triples of blocks.
* `blocks_window_determines`: if `X` and `Y` differ at a cell, the cells `0, …, L n - 1` of `blocks L X Y s`
  determine `s 0, …, s (n - 1)`. So at least `2^n` words of length `L n` occur in rows of `Σ_p`: `Σ_p` has
  topological entropy at least `(log 2) / L`.
* `sigma12_entropy`, `sigma15_entropy`, `sigma17_entropy`: the three instances, `p = 12` with `L = 34`, `p = 15`
  with `L = 31` and `p = 17` with `L = 26`. For `p = 12` the blocks are `X = a b` and `Y = b a` with
  `a = 11110010011110111100` and `b = 11110010011110`. The checks run in the kernel (`decide +kernel`).

So Rule 30 has, at the speed of light to the right, the patterns that the kit's `PeriodicPoints` excludes at every
velocity in `[-1, 1)`: uncountably many rows that come back after `p` steps moved `p` cells to the right.
The natural-language argument is `LightLikeEntropy.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open
namespace LightLikeEntropy

/-- `x` comes back after `p` steps moved `p` cells to the right: `F^p x = σ^{-p} x`. -/
def LightLike (p : Nat) (x : Int → Bool) : Prop := ∀ i : Int, evolve x p i = x (i - p)

/-! ### Rule 30 on a finite word -/

/-- One step of Rule 30 on a word: cells `0, …, m + 1` give the cells `1, …, m` one step later. -/
def stepW : List Bool → List Bool
  | a :: b :: c :: rest => rule30 a b c :: stepW (b :: c :: rest)
  | _ => []

theorem stepW_length : ∀ w : List Bool, (stepW w).length = w.length - 2
  | _ :: b :: c :: rest => by
    simp only [stepW, List.length_cons]
    rw [stepW_length (b :: c :: rest)]
    simp only [List.length_cons]
    omega
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl

theorem stepW_getD : ∀ (w : List Bool) (j : Nat), j + 2 < w.length →
    (stepW w).getD j false = rule30 (w.getD j false) (w.getD (j + 1) false) (w.getD (j + 2) false)
  | _ :: _ :: _ :: _, 0, _ => rfl
  | _ :: b :: c :: rest, j + 1, h => by
    have h' : j + 2 < (b :: c :: rest).length := by
      simp only [List.length_cons] at h ⊢
      omega
    exact stepW_getD (b :: c :: rest) j h'
  | [], _, h => by simp only [List.length_nil] at h; omega
  | [_], _, h => by simp only [List.length_cons, List.length_nil] at h; omega
  | [_, _], _, h => by simp only [List.length_cons, List.length_nil] at h; omega

/-- `t` steps of `stepW`. -/
def iter : Nat → List Bool → List Bool
  | 0, w => w
  | t + 1, w => stepW (iter t w)

theorem iter_length (w : List Bool) : ∀ t : Nat, (iter t w).length = w.length - 2 * t
  | 0 => by simp [iter]
  | t + 1 => by
    rw [iter, stepW_length, iter_length w t]
    omega

theorem getD_append_left (l₁ l₂ : List Bool) (i : Nat) (h : i < l₁.length) :
    (l₁ ++ l₂).getD i false = l₁.getD i false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_right (l₁ l₂ : List Bool) (i : Nat) (h : l₁.length ≤ i) :
    (l₁ ++ l₂).getD i false = l₂.getD (i - l₁.length) false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_right h]

/-- **Light cone on a word.** If the word `w` holds the cells `a, …, a + |w| - 1` of `init`, then `t` steps of
`stepW` hold the cells `a + t, …, a + |w| - 1 - t` at time `t`. -/
theorem iterate_getD (init : Int → Bool) (a : Int) (w : List Bool)
    (hw : ∀ j : Nat, j < w.length → w.getD j false = init (a + j)) :
    ∀ t j : Nat, j + 2 * t < w.length → (iter t w).getD j false = evolve init t (a + t + j)
  | 0, j, hj => by
    simp only [iter]
    rw [hw j (by omega)]
    show init (a + j) = init (a + ((0 : Nat) : Int) + j)
    congr 1
    omega
  | t + 1, j, hj => by
    rw [iter, stepW_getD _ j (by rw [iter_length]; omega),
      iterate_getD init a w hw t j (by omega), iterate_getD init a w hw t (j + 1) (by omega),
      iterate_getD init a w hw t (j + 2) (by omega)]
    show _ = rule30 (evolve init t (a + ((t + 1 : Nat) : Int) + j - 1))
      (evolve init t (a + ((t + 1 : Nat) : Int) + j)) (evolve init t (a + ((t + 1 : Nat) : Int) + j + 1))
    rw [show a + ((t + 1 : Nat) : Int) + j + 1 = a + t + ((j + 2 : Nat) : Int) by omega,
      show a + ((t + 1 : Nat) : Int) + j - 1 = a + t + j by omega,
      show a + ((t + 1 : Nat) : Int) + j = a + t + ((j + 1 : Nat) : Int) by omega]

/-! ### Rows made of two blocks -/

/-- The block chosen by a bit. -/
def pick (X Y : List Bool) (b : Bool) : List Bool := if b then X else Y

/-- The row whose block `q`, on the cells `L q, …, L q + L - 1`, is `X` if `s q` and `Y` otherwise. -/
def blocks (L : Nat) (X Y : List Bool) (s : Int → Bool) (i : Int) : Bool :=
  (pick X Y (s (i / L))).getD (i % L).toNat false

theorem divmod (L : Nat) (hL : 0 < L) (m : Int) (j : Nat) (hj : j < L) :
    ((L : Int) * m + j) / L = m ∧ (((L : Int) * m + j) % L).toNat = j := by
  have hL' : (L : Int) ≠ 0 := by omega
  constructor
  · rw [Int.add_comm, Int.add_mul_ediv_left _ _ hL', Int.ediv_eq_zero_of_lt (by omega) (by omega)]
    omega
  · rw [Int.add_comm, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by omega) (by omega)]
    rfl

theorem blocks_eq (L : Nat) (hL : 0 < L) (X Y : List Bool) (s : Int → Bool) (m : Int) (j : Nat) (hj : j < L) :
    blocks L X Y s ((L : Int) * m + j) = (pick X Y (s m)).getD j false := by
  obtain ⟨h1, h2⟩ := divmod L hL m j hj
  simp only [blocks, h1, h2]

theorem pick_length (L : Nat) (X Y : List Bool) (hX : X.length = L) (hY : Y.length = L) (b : Bool) :
    (pick X Y b).length = L := by
  cases b
  · exact hY
  · exact hX

/-- Three consecutive blocks. -/
def window3 (X Y : List Bool) (b1 b2 b3 : Bool) : List Bool := pick X Y b1 ++ pick X Y b2 ++ pick X Y b3

/-- The blocks `q - 1`, `q`, `q + 1` hold the cells `L (q - 1), …, L (q - 1) + 3 L - 1`. -/
theorem window3_spec (L : Nat) (hL : 0 < L) (X Y : List Bool) (hX : X.length = L) (hY : Y.length = L)
    (s : Int → Bool) (q : Int) (j : Nat) (hj : j < 3 * L) :
    (window3 X Y (s (q - 1)) (s q) (s (q + 1))).getD j false = blocks L X Y s ((L : Int) * (q - 1) + j) := by
  have hp := pick_length L X Y hX hY
  have e : (L : Int) * (q - 1) = (L : Int) * q - L := by rw [Int.mul_sub, Int.mul_one]
  have e2 : (L : Int) * (q + 1) = (L : Int) * q + L := by rw [Int.mul_add, Int.mul_one]
  simp only [window3]
  by_cases h1 : j < L
  · rw [getD_append_left _ _ _ (by simp only [List.length_append, hp]; omega),
      getD_append_left _ _ _ (by simp only [hp]; omega), blocks_eq L hL X Y s (q - 1) j h1]
  · by_cases h2 : j < 2 * L
    · rw [getD_append_left _ _ _ (by simp only [List.length_append, hp]; omega),
        getD_append_right _ _ _ (by simp only [hp]; omega), hp,
        show (L : Int) * (q - 1) + (j : Int) = (L : Int) * q + ((j - L : Nat) : Int) by omega,
        blocks_eq L hL X Y s q (j - L) (by omega)]
    · rw [getD_append_right _ _ _ (by simp only [List.length_append, hp]; omega),
        show (L : Int) * (q - 1) + (j : Int) = (L : Int) * (q + 1) + ((j - 2 * L : Nat) : Int) by omega,
        blocks_eq L hL X Y s (q + 1) (j - 2 * L) (by omega)]
      simp only [List.length_append, hp]
      congr 1
      omega

/-- The finite check: in every triple of blocks, `p` steps move each cell of the middle block `p` cells to the
right (the cells `L - p, …, 2 L - p - 1` of the triple after `p` steps equal the same cells before). -/
def checkG (p L : Nat) (X Y : List Bool) : Bool :=
  [true, false].all fun b1 => [true, false].all fun b2 => [true, false].all fun b3 =>
    (List.range L).all fun r =>
      (iter p (window3 X Y b1 b2 b3)).getD (r + (L - p)) false == (window3 X Y b1 b2 b3).getD (r + (L - p)) false

theorem checkG_spec (p L : Nat) (X Y : List Bool) (hc : checkG p L X Y = true) (b1 b2 b3 : Bool) (r : Nat)
    (hr : r < L) :
    (iter p (window3 X Y b1 b2 b3)).getD (r + (L - p)) false = (window3 X Y b1 b2 b3).getD (r + (L - p)) false := by
  simp only [checkG, List.all_eq_true, List.mem_range, beq_iff_eq] at hc
  have hb : ∀ b : Bool, b ∈ [true, false] := fun b => by cases b <;> simp
  exact hc b1 (hb b1) b2 (hb b2) b3 (hb b3) r hr

end LightLikeEntropy

/-- **Rows of blocks lie in `Σ_p`.** If `p ≤ L` and the check passes, every row `blocks L X Y s` satisfies
`F^p x = σ^{-p} x`. -/
theorem LightLikeEntropy.lightLike_blocks (p L : Nat) (X Y : List Bool) (hX : X.length = L) (hY : Y.length = L) (hpL : p ≤ L)
    (hL : 0 < L) (hc : checkG p L X Y = true) (s : Int → Bool) : LightLike p (blocks L X Y s) := by
  intro i
  have hdec := Int.emod_add_ediv_mul i L
  have h0 : 0 ≤ i % (L : Int) := Int.emod_nonneg i (by omega)
  have h1 : i % (L : Int) < L := Int.emod_lt_of_pos i (by omega)
  obtain ⟨r, hr⟩ : ∃ r : Nat, i % (L : Int) = r := ⟨(i % (L : Int)).toNat, by omega⟩
  generalize i / (L : Int) = q at hdec
  rw [Int.mul_comm] at hdec
  have e : (L : Int) * (q - 1) = (L : Int) * q - L := by rw [Int.mul_sub, Int.mul_one]
  have hw3 := pick_length L X Y hX hY
  have hlen : (window3 X Y (s (q - 1)) (s q) (s (q + 1))).length = 3 * L := by
    simp only [window3, List.length_append, hw3]
    omega
  have key := iterate_getD (blocks L X Y s) ((L : Int) * (q - 1)) (window3 X Y (s (q - 1)) (s q) (s (q + 1)))
    (fun j hj => window3_spec L hL X Y hX hY s q j (by omega)) p (r + (L - p)) (by omega)
  rw [show (L : Int) * (q - 1) + (p : Int) + ((r + (L - p) : Nat) : Int) = i by omega] at key
  rw [← key, checkG_spec p L X Y hc _ _ _ r (by omega),
    window3_spec L hL X Y hX hY s q (r + (L - p)) (by omega),
    show (L : Int) * (q - 1) + ((r + (L - p) : Nat) : Int) = i - (p : Int) by omega]

namespace LightLikeEntropy

/-- If `X` and `Y` differ at the cell `r0`, block `q` of `blocks L X Y s` determines `s q`. -/
theorem blocks_determines (L : Nat) (hL : 0 < L) (X Y : List Bool) (r0 : Nat) (hr0 : r0 < L)
    (hXY : X.getD r0 false ≠ Y.getD r0 false) (s s' : Int → Bool) (q : Int)
    (h : blocks L X Y s ((L : Int) * q + r0) = blocks L X Y s' ((L : Int) * q + r0)) : s q = s' q := by
  rw [blocks_eq L hL X Y s q r0 hr0, blocks_eq L hL X Y s' q r0 hr0] at h
  revert h
  cases s q <;> cases s' q <;> intro h
  · rfl
  · exact absurd h.symm hXY
  · exact absurd h hXY
  · rfl

end LightLikeEntropy

/-- **Positive entropy.** The cells `0, …, L n - 1` of `blocks L X Y s` determine `s 0, …, s (n - 1)`. -/
theorem LightLikeEntropy.blocks_window_determines (L : Nat) (hL : 0 < L) (X Y : List Bool) (r0 : Nat) (hr0 : r0 < L)
    (hXY : X.getD r0 false ≠ Y.getD r0 false) (s s' : Int → Bool) (n : Nat)
    (h : ∀ j : Nat, j < L * n → blocks L X Y s j = blocks L X Y s' j) (q : Nat) (hq : q < n) : s q = s' q := by
  have hlt : L * q + r0 < L * n :=
    Nat.lt_of_lt_of_le (Nat.add_lt_add_left hr0 _) (by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left L hq)
  have := h (L * q + r0) hlt
  rw [show ((L * q + r0 : Nat) : Int) = (L : Int) * (q : Int) + (r0 : Int) by
    rw [Int.natCast_add, Int.natCast_mul]] at this
  exact blocks_determines L hL X Y r0 hr0 hXY s s' q this

namespace LightLikeEntropy

/-! ### Three instances -/

/-- First block for `p = 12`. -/
def x12 : List Bool :=
  [true, true, true, true, false, false, true, false, false, true, true, true, true, false, true, true, true, true,
    false, false, true, true, true, true, false, false, true, false, false, true, true, true, true, false]

/-- Second block for `p = 12`. -/
def y12 : List Bool :=
  [true, true, true, true, false, false, true, false, false, true, true, true, true, false, true, true, true, true,
    false, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false]

theorem check12 : checkG 12 34 x12 y12 = true := by decide +kernel

end LightLikeEntropy

/-- **`Σ_12` has positive entropy**: every row of blocks `x12`, `y12` (of 34 cells) satisfies
`F^12 x = σ^{-12} x`, and its cells `0, …, 34 n - 1` determine the `n` bits that choose its first `n` blocks. -/
theorem LightLikeEntropy.sigma12_entropy :
    (∀ s : Int → Bool, LightLike 12 (blocks 34 x12 y12 s)) ∧
    ∀ (s s' : Int → Bool) (n : Nat), (∀ j : Nat, j < 34 * n → blocks 34 x12 y12 s j = blocks 34 x12 y12 s' j) →
      ∀ q : Nat, q < n → s q = s' q :=
  ⟨lightLike_blocks 12 34 x12 y12 rfl rfl (by decide) (by decide) check12,
    fun s s' n h q hq => blocks_window_determines 34 (by decide) x12 y12 21 (by decide) (by decide) s s' n h q hq⟩

namespace LightLikeEntropy

/-- First block for `p = 15`. -/
def x15 : List Bool :=
  [false, true, true, true, true, true, true, true, false, true, false, false, true, true, false, false, false, true,
    false, false, false, false, false, false, true, false, false, true, true, false, true]

/-- Second block for `p = 15`. -/
def y15 : List Bool :=
  [false, true, true, true, true, true, true, true, false, true, false, false, true, false, true, true, false, false,
    false, true, false, false, false, true, true, false, true, false, false, true, true]

theorem check15 : checkG 15 31 x15 y15 = true := by decide +kernel

end LightLikeEntropy

/-- **`Σ_15` has positive entropy**: every row of blocks `x15`, `y15` (of 31 cells) satisfies
`F^15 x = σ^{-15} x`, and its cells `0, …, 31 n - 1` determine the `n` bits that choose its first `n` blocks. -/
theorem LightLikeEntropy.sigma15_entropy :
    (∀ s : Int → Bool, LightLike 15 (blocks 31 x15 y15 s)) ∧
    ∀ (s s' : Int → Bool) (n : Nat), (∀ j : Nat, j < 31 * n → blocks 31 x15 y15 s j = blocks 31 x15 y15 s' j) →
      ∀ q : Nat, q < n → s q = s' q :=
  ⟨lightLike_blocks 15 31 x15 y15 rfl rfl (by decide) (by decide) check15,
    fun s s' n h q hq => blocks_window_determines 31 (by decide) x15 y15 13 (by decide) (by decide) s s' n h q hq⟩

namespace LightLikeEntropy

/-- First block for `p = 17`. -/
def x17 : List Bool :=
  [false, true, true, false, false, false, true, true, false, false, false, true, false, false, false, false, true,
    false, false, false, true, true, true, false, false, false]

/-- Second block for `p = 17`. -/
def y17 : List Bool :=
  [false, true, true, false, false, false, true, true, false, false, false, true, false, false, false, false, true,
    false, false, false, true, true, true, false, true, false]

theorem check17 : checkG 17 26 x17 y17 = true := by decide +kernel

end LightLikeEntropy

/-- **`Σ_17` has positive entropy**: every row of blocks `x17`, `y17` (of 26 cells) satisfies
`F^17 x = σ^{-17} x`, and its cells `0, …, 26 n - 1` determine the `n` bits that choose its first `n` blocks. -/
theorem LightLikeEntropy.sigma17_entropy :
    (∀ s : Int → Bool, LightLike 17 (blocks 26 x17 y17 s)) ∧
    ∀ (s s' : Int → Bool) (n : Nat), (∀ j : Nat, j < 26 * n → blocks 26 x17 y17 s j = blocks 26 x17 y17 s' j) →
      ∀ q : Nat, q < n → s q = s' q :=
  ⟨lightLike_blocks 17 26 x17 y17 rfl rfl (by decide) (by decide) check17,
    fun s s' n h q hq => blocks_window_determines 26 (by decide) x17 y17 24 (by decide) (by decide) s s' n h q hq⟩

end Rule30Open
