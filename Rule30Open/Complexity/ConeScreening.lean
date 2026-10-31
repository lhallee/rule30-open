module

/-!
# An alternating left half fixes the center cell

A row is `Int → Bool`, and one step of Rule 30 is `x' j = x (j - 1) xor (x j || x (j + 1))`. If the cells left of the
center alternate with the odd cells black, `x (-j) = (j odd)` for `1 ≤ j ≤ t`, the center after `t ≥ 9` steps is white
whatever the rest of the row is (`screening_odd`); with the even cells black it is black for `t ≥ 8`
(`screening_even`). The alternating stretch is fixed by every step whatever lies right of its black end (`stripe`),
and next to that wall the pair of cells `(a, b)` follows `a' = !(a || b)`, so the white pair at time `s + 2` forces the
white pair at time `s` (`pair_back`). The base cases `t = 9, 10` (odd) and `t = 8, 9` (even) are checked over every
right half by `decide` on rows encoded as natural numbers (`base_of_check`), and `evo_local` carries them to any row.
-/

@[expose] public section

namespace Rule30Open


def coneStep (x : Int → Bool) : Int → Bool := fun j => xor (x (j - 1)) (x j || x (j + 1))

def evo (x : Int → Bool) : Nat → Int → Bool
  | 0 => x
  | s + 1 => coneStep (evo x s)

/-- A cell after `s` steps depends only on the `2s + 1` cells of its cone. -/
theorem evo_local (x y : Int → Bool) (s : Nat) (j : Int)
    (h : ∀ i : Int, j - s ≤ i → i ≤ j + s → x i = y i) : evo x s j = evo y s j := by
  induction s generalizing j with
  | zero => exact h j (by omega) (by omega)
  | succ s ih =>
    simp only [evo, coneStep]
    rw [ih (j - 1) (fun i h1 h2 => h i (by omega) (by omega)),
      ih j (fun i h1 h2 => h i (by omega) (by omega)),
      ih (j + 1) (fun i h1 h2 => h i (by omega) (by omega))]

/-! ## The stripe and the pair beside the wall -/

def odd (j : Int) : Bool := decide (j % 2 = 1)

/-- The stripe lemma: the alternating stretch left of the wall at `-1` is fixed by one step on its interior, whatever
lies right of the wall. -/
theorem stripe_step (x : Int → Bool) (n : Nat)
    (h : ∀ j : Int, 1 ≤ j → j ≤ n + 1 → x (-j) = odd j) :
    ∀ j : Int, 1 ≤ j → j ≤ n → coneStep x (-j) = odd j := by
  intro j h1 h2
  simp only [coneStep]
  have e1 : -j - 1 = -(j + 1) := by omega
  rw [e1, h (j + 1) (by omega) (by omega), h j h1 (by omega)]
  by_cases hj : j = 1
  · subst hj
    have hw := h 1 (by omega) (by omega)
    simp [odd] at hw ⊢
  · have e2 : -j + 1 = -(j - 1) := by omega
    rw [e2, h (j - 1) (by omega) (by omega)]
    rcases (show j % 2 = 0 ∨ j % 2 = 1 by omega) with hm | hm
    · have : (j + 1) % 2 = 1 := by omega
      have : (j - 1) % 2 = 1 := by omega
      simp [odd, *]
    · have : (j + 1) % 2 = 0 := by omega
      simp [odd, *]

/-- The stretch stays inside the cone: after `s ≤ t` steps, cells `-1 .. -(t - s)` still alternate. -/
theorem stripe (x : Int → Bool) (t : Nat)
    (h : ∀ j : Int, 1 ≤ j → j ≤ t → x (-j) = odd j) :
    ∀ s : Nat, s ≤ t → ∀ j : Int, 1 ≤ j → j ≤ (t - s : Nat) → evo x s (-j) = odd j := by
  intro s
  induction s with
  | zero => intro _ j h1 h2; exact h j h1 (by omega)
  | succ s ih =>
    intro hs j h1 h2
    exact stripe_step (evo x s) (t - (s + 1)) (fun i a b => ih (by omega) i a (by omega)) j h1 (by omega)

/-- The wall: cell `-1` is black at every time `s < t`. -/
theorem wall_black (x : Int → Bool) (t : Nat)
    (h : ∀ j : Int, 1 ≤ j → j ≤ t → x (-j) = odd j) (s : Nat) (hs : s < t) : evo x s (-1) = true := by
  have := stripe x t h s (by omega) 1 (by omega) (by omega)
  simpa [odd] using this

/-- The pair `(a, b) = (cell 0, cell 1)` beside the wall: `a' = NOR(a, b)`. -/
theorem pair_a (x : Int → Bool) (s : Nat) (hw : evo x s (-1) = true) :
    evo x (s + 1) 0 = !(evo x s 0 || evo x s 1) := by
  simp only [evo, coneStep]
  have : (0 : Int) - 1 = -1 := by omega
  rw [this, hw]
  simp

/-- `b' = a xor (b || e)`, with `e` the cell at 2. -/
theorem pair_b (x : Int → Bool) (s : Nat) :
    evo x (s + 1) 1 = xor (evo x s 0) (evo x s 1 || evo x s 2) := by
  simp only [evo, coneStep]
  rfl

/-- Lemma A: a pair `(false, false)` at `s + 2` forces `(false, false)` at `s`, when the wall is black at `s` and
`s + 1`. -/
theorem pair_back (x : Int → Bool) (s : Nat) (h0 : evo x s (-1) = true) (h1 : evo x (s + 1) (-1) = true)
    (ha : evo x (s + 2) 0 = false) (hb : evo x (s + 2) 1 = false) :
    evo x s 0 = false ∧ evo x s 1 = false := by
  have a2 := pair_a x (s + 1) h1
  have b2 := pair_b x (s + 1)
  have a1 := pair_a x s h0
  rw [ha] at a2
  rw [hb] at b2
  revert a2 b2 a1
  generalize evo x (s + 1) 0 = a1v
  generalize evo x (s + 1) 1 = b1v
  generalize evo x (s + 1) 2 = e1v
  generalize evo x s 0 = a0
  generalize evo x s 1 = b0
  cases a1v <;> cases b1v <;> cases e1v <;> cases a0 <;> cases b0 <;> simp

/-! ## Rows encoded as numbers, for the kernel check of the base -/

/-- The row with cell `o + k` equal to bit `k` of `r`, and white left of `o`. -/
def rowN (r : Nat) (o : Int) : Int → Bool := fun i => if o ≤ i then r.testBit (i - o).toNat else false

/-- One step on the number: bit `k` becomes bit `k` xor (bit `k + 1` or bit `k + 2`); the row moves one cell right. -/
def nstep (r : Nat) : Nat := r ^^^ ((r >>> 1) ||| (r >>> 2))

theorem step_rowN (r : Nat) (o i : Int) (hi : o + 1 ≤ i) : coneStep (rowN r o) i = rowN (nstep r) (o + 1) i := by
  simp only [coneStep, rowN, nstep]
  rw [ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_left (by omega)]
  simp only [Nat.testBit_xor, Nat.testBit_or, Nat.testBit_shiftRight]
  have e1 : (i - 1 - o).toNat = (i - (o + 1)).toNat := by omega
  have e2 : (i - o).toNat = 1 + (i - (o + 1)).toNat := by omega
  have e3 : (i + 1 - o).toNat = 2 + (i - (o + 1)).toNat := by omega
  rw [e1, e2, e3]

def nevo (r : Nat) : Nat → Nat
  | 0 => r
  | s + 1 => nstep (nevo r s)

theorem evo_rowN (r : Nat) (o : Int) (s : Nat) :
    ∀ i : Int, o + s ≤ i → evo (rowN r o) s i = rowN (nevo r s) (o + s) i := by
  induction s with
  | zero => intro i _; simp [evo, nevo]
  | succ s ih =>
    intro i hi
    simp only [evo, nevo]
    have : coneStep (evo (rowN r o) s) i = coneStep (rowN (nevo r s) (o + s)) i := by
      simp only [coneStep]
      rw [ih (i - 1) (by omega), ih i (by omega), ih (i + 1) (by omega)]
    rw [this, step_rowN _ _ _ (by omega)]
    congr 1
    push_cast
    omega

/-- Bits of a Bool function, bit 0 first. -/
def enc (g : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => 2 * enc (fun k => g (k + 1)) n + (if g 0 then 1 else 0)

theorem testBit_enc (n : Nat) : ∀ (g : Nat → Bool) (k : Nat), k < n → (enc g n).testBit k = g k := by
  induction n with
  | zero => intro g k hk; omega
  | succ n ih =>
    intro g k hk
    cases k with
    | zero =>
      simp only [enc, Nat.testBit_zero]
      cases g 0 <;> simp <;> omega
    | succ k =>
      rw [Nat.testBit_succ]
      have : (2 * enc (fun k => g (k + 1)) n + (if g 0 then 1 else 0)) / 2 = enc (fun k => g (k + 1)) n := by
        cases g 0 <;> simp <;> omega
      simp only [enc]
      rw [this, ih _ k (by omega)]

theorem enc_lt (n : Nat) : ∀ g : Nat → Bool, enc g n < 2 ^ n := by
  induction n with
  | zero => intro g; simp [enc]
  | succ n ih =>
    intro g
    have := ih (fun k => g (k + 1))
    simp only [enc, Nat.pow_succ]
    cases g 0 <;> simp <;> omega

/-! ## The two base checks, by the kernel over every right half -/

/-- `t = 9`: left cells `-9 .. -1` are bits `0 .. 8` of `341` (odd pattern), right cells `0 .. 9` are `r < 2^10`. -/
def allIn (f : Nat → Bool) (lo : Nat) : Nat → Bool
  | 0 => f lo
  | k + 1 => allIn f lo k && allIn f (lo + 2 ^ k) k

theorem allIn_spec (f : Nat → Bool) (k : Nat) :
    ∀ lo : Nat, allIn f lo k = true → ∀ r : Nat, lo ≤ r → r < lo + 2 ^ k → f r = true := by
  induction k with
  | zero => intro lo h r h1 h2; simp at h2; have : r = lo := by omega
            subst this; exact h
  | succ k ih =>
    intro lo h r h1 h2
    simp only [allIn, Bool.and_eq_true] at h
    rw [Nat.pow_succ] at h2
    by_cases hr : r < lo + 2 ^ k
    · exact ih lo h.1 r h1 hr
    · exact ih (lo + 2 ^ k) h.2 r (by omega) (by omega)

def f9 (r : Nat) : Bool := !(nevo (341 + 512 * r) 9).testBit 0
def f10 (r : Nat) : Bool := !(nevo (682 + 1024 * r) 10).testBit 0

theorem base9_all : allIn f9 0 10 = true := by decide

theorem base9_check : ∀ r : Nat, r < 1024 → (nevo (341 + 512 * r) 9).testBit 0 = false := by
  intro r hr
  have := allIn_spec f9 10 0 base9_all r (by omega) (by simpa using hr)
  simpa [f9] using this

/-- `t = 10`: left cells `-10 .. -1` are bits `0 .. 9` of `682`, right cells `0 .. 10` are `r < 2^11`. -/
theorem base10_all : allIn f10 0 11 = true := by decide

theorem base10_check : ∀ r : Nat, r < 2048 → (nevo (682 + 1024 * r) 10).testBit 0 = false := by
  intro r hr
  have := allIn_spec f10 11 0 base10_all r (by omega) (by simpa using hr)
  simpa [f10] using this

/-! ## From the checks to every row -/

theorem enc_congr (n : Nat) : ∀ g h : Nat → Bool, (∀ k, k < n → g k = h k) → enc g n = enc h n := by
  induction n with
  | zero => intro g h _; rfl
  | succ n ih =>
    intro g h hgh
    simp only [enc]
    rw [ih (fun k => g (k + 1)) (fun k => h (k + 1)) (fun k hk => hgh (k + 1) (by omega)), hgh 0 (by omega)]

theorem enc_add (m : Nat) : ∀ (g : Nat → Bool) (n : Nat),
    enc g (m + n) = enc g m + 2 ^ m * enc (fun k => g (k + m)) n := by
  induction m with
  | zero => intro g n; simp [enc]
  | succ m ih =>
    intro g n
    rw [show m + 1 + n = (m + n) + 1 by omega]
    simp only [enc]
    rw [ih (fun k => g (k + 1)) n, Nat.pow_succ]
    have : (fun k => g (k + m + 1)) = (fun k => g (k + (m + 1))) := by
      funext k; congr 1
    rw [this]
    generalize enc (fun k => g (k + 1)) m = A
    generalize enc (fun k => g (k + (m + 1))) n = B
    generalize 2 ^ m = C
    rw [Nat.mul_add, Nat.mul_comm 2 (C * B), Nat.mul_assoc C 2 B, Nat.mul_comm 2 B, ← Nat.mul_assoc]
    cases g 0 <;> simp <;> omega

/-- A base check over all `2^(n+1)` right halves gives `c_n = v` for every row whose left half `-n .. -1` follows
`pat`. -/
theorem base_of_check (pat : Int → Bool) (v : Bool) (n P : Nat)
    (hP : enc (fun k => pat ((n : Int) - k)) n = P)
    (hc : ∀ r : Nat, r < 2 ^ (n + 1) → (nevo (P + 2 ^ n * r) n).testBit 0 = v)
    (x : Int → Bool) (h : ∀ j : Int, 1 ≤ j → j ≤ n → x (-j) = pat j) : evo x n 0 = v := by
  let g : Nat → Bool := fun k => x ((k : Int) - n)
  have hR : enc g (n + (n + 1)) = P + 2 ^ n * enc (fun k => g (k + n)) (n + 1) := by
    rw [enc_add, ← hP]
    congr 1
    apply enc_congr
    intro k hk
    simp only [g]
    have := h ((n : Int) - k) (by omega) (by omega)
    rw [show -((n : Int) - k) = (k : Int) - n by omega] at this
    exact this
  have hloc : evo x n 0 = evo (rowN (enc g (n + (n + 1))) (-(n : Int))) n 0 := by
    apply evo_local
    intro i h1 h2
    simp only [rowN]
    rw [ite_eq_left (by omega), testBit_enc _ g _ (by omega)]
    simp only [g]
    congr 1
    omega
  rw [hloc, evo_rowN _ _ _ 0 (by omega), hR]
  simp only [rowN]
  rw [ite_eq_left (by omega)]
  rw [show (0 - (-(n : Int) + n)).toNat = 0 by omega]
  exact hc _ (enc_lt _ _)

theorem base9 (x : Int → Bool) (h : ∀ j : Int, 1 ≤ j → j ≤ 9 → x (-j) = odd j) : evo x 9 0 = false :=
  base_of_check odd false 9 341 (by decide) (fun r hr => base9_check r (by simpa using hr)) x (by simpa using h)

theorem base10 (x : Int → Bool) (h : ∀ j : Int, 1 ≤ j → j ≤ 10 → x (-j) = odd j) : evo x 10 0 = false :=
  base_of_check odd false 10 682 (by decide) (fun r hr => base10_check r (by simpa using hr)) x (by simpa using h)

/-- **Screening, odd pattern.** If `x (-j) = (j odd)` for `1 ≤ j ≤ t` and `t ≥ 9`, then the cell at column 0 after
`t` steps is false, whatever the rest of the row is. -/
theorem screening_odd (x : Int → Bool) (t : Nat) (ht : 9 ≤ t)
    (h : ∀ j : Int, 1 ≤ j → j ≤ t → x (-j) = odd j) : evo x t 0 = false := by
  by_cases h9 : t = 9
  · subst h9; exact base9 x h
  have c9 := base9 x (fun j h1 h2 => h j h1 (by omega))
  have c10 := base10 x (fun j h1 h2 => h j h1 (by omega))
  -- No pair (false, false) at any time 8 ≤ s < t.
  have key : ∀ s : Nat, 8 ≤ s → s < t → ¬ (evo x s 0 = false ∧ evo x s 1 = false) := by
    intro s
    induction s using Nat.strongRecOn with
    | _ s ih =>
      intro hs1 hs2 hp
      by_cases e8 : s = 8
      · subst e8
        have := pair_a x 8 (wall_black x t h 8 (by omega))
        rw [hp.1, hp.2, c9] at this; simp at this
      by_cases e9 : s = 9
      · subst e9
        have := pair_a x 9 (wall_black x t h 9 (by omega))
        rw [hp.1, hp.2, c10] at this; simp at this
      obtain ⟨u, rfl⟩ : ∃ u, s = u + 2 := ⟨s - 2, by omega⟩
      have := pair_back x u (wall_black x t h u (by omega)) (wall_black x t h (u + 1) (by omega)) hp.1 hp.2
      exact ih u (by omega) (by omega) (by omega) this
  obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
  rw [pair_a x u (wall_black x (u + 1) h u (by omega))]
  have := key u (by omega) (by omega)
  revert this
  cases evo x u 0 <;> cases evo x u 1 <;> simp

/-! ## The even pattern -/

def even (j : Int) : Bool := decide (j % 2 = 0)

def g8 (r : Nat) : Bool := (nevo (85 + 256 * r) 8).testBit 0
def g9 (r : Nat) : Bool := (nevo (170 + 512 * r) 9).testBit 0

theorem ebase8_all : allIn g8 0 9 = true := by decide
theorem ebase9_all : allIn g9 0 10 = true := by decide

theorem ebase8 (x : Int → Bool) (h : ∀ j : Int, 1 ≤ j → j ≤ 8 → x (-j) = even j) : evo x 8 0 = true :=
  base_of_check even true 8 85 (by decide)
    (fun r hr => allIn_spec g8 9 0 ebase8_all r (by omega) (by simpa using hr)) x (by simpa using h)

theorem ebase9 (x : Int → Bool) (h : ∀ j : Int, 1 ≤ j → j ≤ 9 → x (-j) = even j) : evo x 9 0 = true :=
  base_of_check even true 9 170 (by decide)
    (fun r hr => allIn_spec g9 10 0 ebase9_all r (by omega) (by simpa using hr)) x (by simpa using h)

/-- Evolution commutes with translation. -/
theorem evo_shift (x : Int → Bool) (s : Nat) : ∀ j : Int, evo (fun i => x (i - 1)) s j = evo x s (j - 1) := by
  induction s with
  | zero => intro j; rfl
  | succ s ih =>
    intro j
    simp only [evo, coneStep]
    rw [ih (j - 1), ih j, ih (j + 1), show j - 1 + 1 = j by omega, show j + 1 - 1 = j by omega]

/-- **Screening, even pattern.** If `x (-j) = (j even)` for `1 ≤ j ≤ t` and `t ≥ 8`, then the cell at column 0 after
`t` steps is true, whatever the rest of the row is. -/
theorem screening_even (x : Int → Bool) (t : Nat) (ht : 8 ≤ t)
    (h : ∀ j : Int, 1 ≤ j → j ≤ t → x (-j) = even j) : evo x t 0 = true := by
  by_cases h8 : t = 8
  · subst h8; exact ebase8 x h
  by_cases h9 : t = 9
  · subst h9; exact ebase9 x h
  have c8 := ebase8 x (fun j h1 h2 => h j h1 (by omega))
  have c9 := ebase9 x (fun j h1 h2 => h j h1 (by omega))
  -- The translated row has the odd pattern on `-1 .. -(t - 1)`.
  let y : Int → Bool := fun i => x (i - 1)
  have hy : ∀ j : Int, 1 ≤ j → j ≤ (t - 1 : Nat) → y (-j) = odd j := by
    intro j h1 h2
    simp only [y]
    rw [show -j - 1 = -(j + 1) by omega, h (j + 1) (by omega) (by omega)]
    simp only [even, odd]
    rcases (show j % 2 = 0 ∨ j % 2 = 1 by omega) with hm | hm
    · have : (j + 1) % 2 = 1 := by omega
      simp [hm, this]
    · have : (j + 1) % 2 = 0 := by omega
      simp [hm, this]
  have hb : ∀ s : Nat, evo x s 0 = evo y s 1 := by
    intro s; rw [evo_shift]; rfl
  have b8 : evo y 8 1 = true := by rw [← hb]; exact c8
  have b9 : evo y 9 1 = true := by rw [← hb]; exact c9
  have W := wall_black y (t - 1) hy
  have key : ∀ s : Nat, 7 ≤ s → s ≤ t - 1 → ¬ (evo y s 0 = false ∧ evo y s 1 = false) := by
    intro s
    induction s using Nat.strongRecOn with
    | _ s ih =>
      intro hs1 hs2 hp
      by_cases e7 : s = 7
      · subst e7
        have a8 := pair_a y 7 (W 7 (by omega))
        have bb8 := pair_b y 7
        have a9 := pair_a y 8 (W 8 (by omega))
        have bb9 := pair_b y 8
        rw [hp.1, hp.2] at a8 bb8
        rw [b8] at bb8 a9
        rw [b9] at bb9
        revert a8 bb8 a9 bb9
        cases evo y 8 0 <;> cases evo y 7 2 <;> cases evo y 9 0 <;> cases evo y 8 2 <;> simp [b8]
      by_cases e8 : s = 8
      · subst e8; rw [b8] at hp; simp at hp
      by_cases e9 : s = 9
      · subst e9; rw [b9] at hp; simp at hp
      obtain ⟨u, rfl⟩ : ∃ u, s = u + 2 := ⟨s - 2, by omega⟩
      have := pair_back y u (W u (by omega)) (W (u + 1) (by omega)) hp.1 hp.2
      exact ih u (by omega) (by omega) (by omega) this
  obtain ⟨u, rfl⟩ : ∃ u, t = u + 2 := ⟨t - 2, by omega⟩
  rw [hb, pair_b y (u + 1), pair_a y u (W u (by omega))]
  have k0 := key u (by omega) (by omega)
  have k1 := key (u + 1) (by omega) (by omega)
  rw [pair_a y u (W u (by omega))] at k1
  revert k0 k1
  cases evo y u 0 <;> cases evo y u 1 <;> cases evo y (u + 1) 1 <;> cases evo y (u + 1) 2 <;> simp

/-! ## The leftmost cell of the cone enters the center linearly -/

/-- The row `x` with cell `a` flipped. -/
def flipAt (x : Int → Bool) (a : Int) : Int → Bool := fun i => if i = a then !x i else x i

/-- The row `x` with cell `a` set to `v`. -/
def setAt (x : Int → Bool) (a : Int) (v : Bool) : Int → Bool := fun i => if i = a then v else x i

/-- Rows that agree right of `a`: the front cell `a + s` after `s` steps differs by `x a xor y a`. -/
theorem front_xor (x y : Int → Bool) (a : Int) (hagree : ∀ i : Int, a < i → x i = y i) (s : Nat) :
    evo y s (a + s) = xor (xor (x a) (y a)) (evo x s (a + s)) := by
  induction s with
  | zero =>
    have e : a + ((0 : Nat) : Int) = a := by omega
    simp only [evo]
    rw [e]
    generalize x a = p
    generalize y a = q
    cases p <;> cases q <;> rfl
  | succ s ih =>
    have e0 : a + ((s + 1 : Nat) : Int) - 1 = a + s := by push_cast; omega
    have r1 : evo x s (a + ((s + 1 : Nat) : Int)) = evo y s (a + ((s + 1 : Nat) : Int)) :=
      evo_local x y s _ (fun i h1 _ => hagree i (by push_cast at h1; omega))
    have r2 : evo x s (a + ((s + 1 : Nat) : Int) + 1) = evo y s (a + ((s + 1 : Nat) : Int) + 1) :=
      evo_local x y s _ (fun i h1 _ => hagree i (by push_cast at h1; omega))
    simp only [evo, coneStep]
    rw [e0, ih, r1, r2]
    generalize xor (x a) (y a) = d
    generalize evo x s (a + s) = u
    cases d <;> cases u <;> simp

/-- Flipping cell `-t` flips the center after `t` steps. -/
theorem flip_center (x : Int → Bool) (t : Nat) : evo (flipAt x (-t)) t 0 = !(evo x t 0) := by
  have h := front_xor x (flipAt x (-t)) (-t) (fun i hi => by simp [flipAt]; omega) t
  have e : -(t : Int) + (t : Int) = 0 := by omega
  rw [e] at h
  rw [h]
  simp [flipAt]

/-- The center after `t` steps is `x (-t) xor g`, with `g` the center for the row with cell `-t` white, a function
of the cells `-t + 1 .. t`. -/
theorem center_decomp (x : Int → Bool) (t : Nat) :
    evo x t 0 = xor (x (-t)) (evo (setAt x (-t) false) t 0) := by
  have h := front_xor (setAt x (-t) false) x (-t) (fun i hi => by simp [setAt]; omega) t
  have e : -(t : Int) + (t : Int) = 0 := by omega
  rw [e] at h
  rw [h]
  simp [setAt]

/-- `g` depends only on the cells `-t + 1 .. t`. -/
theorem decomp_local (x y : Int → Bool) (t : Nat)
    (h : ∀ i : Int, -(t : Int) < i → i ≤ t → x i = y i) :
    evo (setAt x (-t) false) t 0 = evo (setAt y (-t) false) t 0 :=
  evo_local _ _ t 0 (fun i h1 h2 => by
    simp only [setAt]
    by_cases hi : i = -(t : Int)
    · simp [hi]
    · simp only [hi, ite_false]; exact h i (by omega) (by omega))

/-- The odd word with cell `-t` flipped makes the center black for `t ≥ 9`. -/
theorem flip_odd (x : Int → Bool) (t : Nat) (ht : 9 ≤ t)
    (h : ∀ j : Int, 1 ≤ j → j ≤ t → x (-j) = odd j) : evo (flipAt x (-t)) t 0 = true := by
  rw [flip_center, screening_odd x t ht h]; rfl

/-- The even word with cell `-t` flipped makes the center white for `t ≥ 8`. -/
theorem flip_even (x : Int → Bool) (t : Nat) (ht : 8 ≤ t)
    (h : ∀ j : Int, 1 ≤ j → j ≤ t → x (-j) = even j) : evo (flipAt x (-t)) t 0 = false := by
  rw [flip_center, screening_even x t ht h]; rfl

/-- For `t ≥ 9`, rows `x` and `y` carrying any two of the four left words (odd, even, odd flipped at `-t`, even
flipped at `-t`) on cells `-1 .. -t`, with arbitrary right halves, have the same center exactly when the words fall
in the same class {odd, even flipped} or {even, odd flipped}: here, odd and even flipped give white, even and odd
flipped give black, whatever the rest of the row. -/
theorem four_words (x : Int → Bool) (t : Nat) (ht : 9 ≤ t) :
    ((∀ j : Int, 1 ≤ j → j ≤ t → x (-j) = odd j) → evo x t 0 = false ∧ evo (flipAt x (-t)) t 0 = true) ∧
    ((∀ j : Int, 1 ≤ j → j ≤ t → x (-j) = even j) → evo x t 0 = true ∧ evo (flipAt x (-t)) t 0 = false) :=
  ⟨fun h => ⟨screening_odd x t ht h, flip_odd x t ht h⟩,
   fun h => ⟨screening_even x t (by omega) h, flip_even x t (by omega) h⟩⟩

end Rule30Open
