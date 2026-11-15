module

public import Rule30Open.PeriodTwo.HeldColumn

/-!
# No iterate of the held map is affine on a residue class

`heldNat U = (U >>> 1) ^^^ (U ||| (U <<< 1))` is the held map of `HeldColumn`. Far from cell 0 it acts as
`edgeless x = x ^^^ ((x <<< 1) ||| (x <<< 2))`, and two pieces of a number separated by a gap evolve apart:
`heldNat_split` and `heldNat_repeat_split`. The top two bits of `edgeless x` are both 1 (`edgeless_top`), so
`edgeless^n 3 < 3 * edgeless^n 1` (`edgeless_three_lt`). Hence on every class `a + 2^k ℤ`, the two numbers
`a + 2^m` and `a + 3 * 2^m` have images whose differences from the image of `a` are not in the ratio 1 to 3
(`heldNat_not_affine`), which an affine map on the class would need.

The natural-language argument is `HeldSimilarity.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

/-- The held map far from cell 0. -/
def edgeless (x : Nat) : Nat := x ^^^ ((x <<< 1) ||| (x <<< 2))

theorem heldNat_split (A y p q : Nat) (hA : A < 2 ^ p) (hpq : p + 2 ≤ q) :
    heldNat (2 ^ q * y + A) = 2 ^ (q - 1) * edgeless y + heldNat A ∧ heldNat A < 2 ^ (p + 1) := by
  have hAz : ∀ i, p ≤ i → A.testBit i = false := fun i hi =>
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hA (Nat.pow_le_pow_right (by omega) hi))
  have hX : ∀ i, (2 ^ q * y + A).testBit i = if i < q then A.testBit i else y.testBit (i - q) := fun i =>
    Nat.testBit_two_pow_mul_add y (Nat.lt_of_lt_of_le hA (Nat.pow_le_pow_right (by omega) (by omega))) i
  have hHz : ∀ i, p + 1 ≤ i → (heldNat A).testBit i = false := by
    intro i hi
    unfold heldNat
    simp only [Nat.testBit_xor, Nat.testBit_or, Nat.testBit_shiftRight, Nat.testBit_shiftLeft,
      hAz i (by omega), hAz (1 + i) (by omega), hAz (i - 1) (by omega)]
    simp
  have hHlt : heldNat A < 2 ^ (p + 1) := Nat.lt_pow_two_of_testBit _ hHz
  refine ⟨?_, hHlt⟩
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  have hHlt' : heldNat A < 2 ^ r := Nat.lt_of_lt_of_le hHlt (Nat.pow_le_pow_right (by omega) (by omega))
  apply Nat.eq_of_testBit_eq
  intro j
  rw [show r + 1 - 1 = r by omega, Nat.testBit_two_pow_mul_add _ hHlt']
  unfold heldNat edgeless
  simp only [Nat.testBit_xor, Nat.testBit_or, Nat.testBit_shiftRight, Nat.testBit_shiftLeft, hX]
  by_cases hj : j < r
  · simp only [hj, ite_true]
    have h1 : 1 + j < r + 1 := by omega
    have h2 : j < r + 1 := by omega
    have h3 : j - 1 < r + 1 := by omega
    simp [h1, h2, h3]
  · simp only [hj, ite_false]
    have h1 : ¬ (1 + j < r + 1) := by omega
    simp only [h1, ite_false, show 1 + j - (r + 1) = j - r by omega]
    by_cases hj2 : j = r
    · subst hj2
      have h2 : j < j + 1 := by omega
      simp only [h2, ite_true, hAz j (by omega), Nat.sub_self]
      by_cases hj0 : j = 0
      · subst hj0; simp
      · have h3 : j - 1 < j + 1 := by omega
        simp [h3, hAz (j - 1) (by omega)]
    · have h2 : ¬ (j < r + 1) := by omega
      simp only [h2, ite_false]
      by_cases hj3 : j = r + 1
      · subst hj3
        have h3 : r + 1 - 1 < r + 1 := by omega
        simp only [h3, ite_true, hAz (r + 1 - 1) (by omega), show r + 1 - (r + 1) = 0 by omega,
          show r + 1 - r = 1 by omega]
        simp
      · have h3 : ¬ (j - 1 < r + 1) := by omega
        simp only [h3, ite_false, show j - (r + 1) = j - r - 1 by omega,
          show j - 1 - (r + 1) = j - r - 2 by omega]
        have h4 : 1 ≤ j - r := by omega
        have h5 : 2 ≤ j - r := by omega
        simp [h4, h5, show j ≥ 1 by omega]

theorem heldNat_repeat_split : ∀ n (A y p q : Nat), A < 2 ^ p → p + 2 * n ≤ q →
    Nat.repeat heldNat n (2 ^ q * y + A) = 2 ^ (q - n) * Nat.repeat edgeless n y + Nat.repeat heldNat n A ∧
      Nat.repeat heldNat n A < 2 ^ (p + n) := by
  intro n
  induction n with
  | zero => intro A y p q hA _; exact ⟨by simp [Nat.repeat], by simpa [Nat.repeat] using hA⟩
  | succ n ih =>
    intro A y p q hA hpq
    obtain ⟨h1, h2⟩ := ih A y p q hA (by omega)
    obtain ⟨h3, h4⟩ := heldNat_split (Nat.repeat heldNat n A) (Nat.repeat edgeless n y) (p + n) (q - n) h2
      (by omega)
    have e1 : Nat.repeat heldNat (n + 1) (2 ^ q * y + A) = heldNat (Nat.repeat heldNat n (2 ^ q * y + A)) := rfl
    have e2 : Nat.repeat heldNat (n + 1) A = heldNat (Nat.repeat heldNat n A) := rfl
    have e3 : Nat.repeat edgeless (n + 1) y = edgeless (Nat.repeat edgeless n y) := rfl
    refine ⟨?_, ?_⟩
    · rw [e1, e2, e3, h1, h3, show q - n - 1 = q - (n + 1) by omega]
    · rw [e2, show p + (n + 1) = p + n + 1 by omega]; exact h4

/-- `x` has its last 1 at bit `p`. -/
def heldTopAt (x p : Nat) : Prop := x.testBit p = true ∧ ∀ i, p < i → x.testBit i = false

theorem edgeless_top (x p : Nat) (h : heldTopAt x p) :
    heldTopAt (edgeless x) (p + 2) ∧ (edgeless x).testBit (p + 1) = true := by
  obtain ⟨h1, h2⟩ := h
  unfold edgeless
  refine ⟨⟨?_, fun i hi => ?_⟩, ?_⟩
  · simp only [Nat.testBit_xor, Nat.testBit_or, Nat.testBit_shiftLeft, h2 (p + 2) (by omega),
      show p + 2 - 1 = p + 1 by omega, show p + 2 - 2 = p by omega, h1]
    simp
  · simp only [Nat.testBit_xor, Nat.testBit_or, Nat.testBit_shiftLeft, h2 i (by omega),
      h2 (i - 1) (by omega), h2 (i - 2) (by omega)]
    simp
  · simp only [Nat.testBit_xor, Nat.testBit_or, Nat.testBit_shiftLeft, h2 (p + 1) (by omega),
      show p + 1 - 1 = p by omega, h1]
    simp

theorem heldTopAt.lt {x p : Nat} (h : heldTopAt x p) : x < 2 ^ (p + 1) :=
  Nat.lt_pow_two_of_testBit _ fun i hi => h.2 i (by omega)

/-- A number whose bits `p + 1` and `p` are 1 is at least `3 * 2 ^ p`. -/
theorem three_le_of_testBit (x p : Nat) (h1 : x.testBit (p + 1) = true) (h0 : x.testBit p = true) :
    3 * 2 ^ p ≤ x := by
  have hd : (x / 2 ^ p).testBit 1 = true ∧ (x / 2 ^ p).testBit 0 = true := by
    rw [← Nat.shiftRight_eq_div_pow, Nat.testBit_shiftRight, Nat.testBit_shiftRight]
    exact ⟨by simpa [Nat.add_comm] using h1, by simpa using h0⟩
  have hge : 2 ≤ x / 2 ^ p := by
    have := Nat.ge_two_pow_of_testBit hd.1
    simpa using this
  have hodd : (x / 2 ^ p) % 2 = 1 := by
    rw [Nat.mod_two_eq_one_iff_testBit_zero]; exact hd.2
  have h3 : 3 ≤ x / 2 ^ p := by omega
  have := Nat.div_mul_le_self x (2 ^ p)
  have h4 : 3 * 2 ^ p ≤ x / 2 ^ p * 2 ^ p := Nat.mul_le_mul_right _ h3
  omega

theorem edgeless_repeat_top : ∀ n (x p : Nat), heldTopAt x p → heldTopAt (Nat.repeat edgeless n x) (p + 2 * n) := by
  intro n
  induction n with
  | zero => intro x p h; simpa [Nat.repeat] using h
  | succ n ih =>
    intro x p h
    have := (edgeless_top _ _ (ih x p h)).1
    simpa [Nat.repeat, show p + 2 * n + 2 = p + 2 * (n + 1) by omega] using this

theorem edgeless_three_lt (n : Nat) (hn : 1 ≤ n) :
    Nat.repeat edgeless n 3 < 3 * Nat.repeat edgeless n 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have t1 : heldTopAt 1 0 := ⟨by decide, fun i hi => by
    rw [Nat.testBit_lt_two_pow]; exact Nat.lt_of_lt_of_le (by decide) (Nat.pow_le_pow_right (by omega) hi)⟩
  have t3 : heldTopAt 3 1 := ⟨by decide, fun i hi => by
    rw [Nat.testBit_lt_two_pow]; exact Nat.lt_of_lt_of_le (by decide) (Nat.pow_le_pow_right (by omega) hi)⟩
  have hm1 := edgeless_top _ _ (edgeless_repeat_top m 1 0 t1)
  have hlow := three_le_of_testBit (Nat.repeat edgeless (m + 1) 1) (0 + 2 * m + 1)
    (by simpa [Nat.repeat] using hm1.1.1) (by simpa [Nat.repeat] using hm1.2)
  have hhigh := (edgeless_repeat_top (m + 1) 3 1 t3).lt
  have e : 2 ^ (1 + 2 * (m + 1) + 1) = 8 * 2 ^ (0 + 2 * m + 1) := by
    rw [show 1 + 2 * (m + 1) + 1 = (0 + 2 * m + 1) + 3 by omega, Nat.pow_add]; omega
  omega

/-- **No iterate of the held map is affine on a class.** On the class of `a` modulo `2 ^ k`, with
`m = k + 2 n + 3`, the images of `a + 2 ^ m` and `a + 3 * 2 ^ m` differ from the image of `a` by amounts not in the
ratio 1 to 3. -/
theorem heldNat_not_affine (n k a : Nat) (hn : 1 ≤ n) (ha : a < 2 ^ k) :
    (((Nat.repeat heldNat n (2 ^ (k + 2 * n + 3) * 3 + a) : Nat) : Int) - ((Nat.repeat heldNat n a : Nat) : Int)) ≠
      3 * (((Nat.repeat heldNat n (2 ^ (k + 2 * n + 3) * 1 + a) : Nat) : Int) -
        ((Nat.repeat heldNat n a : Nat) : Int)) := by
  have h3 := (heldNat_repeat_split n a 3 k (k + 2 * n + 3) ha (by omega)).1
  have h1 := (heldNat_repeat_split n a 1 k (k + 2 * n + 3) ha (by omega)).1
  rw [h3, h1]
  have hlt := edgeless_three_lt n hn
  have hpos : 0 < 2 ^ (k + 2 * n + 3 - n) := Nat.two_pow_pos _
  intro h
  have h' : (2 ^ (k + 2 * n + 3 - n) * Nat.repeat edgeless n 3 : Int) =
      3 * (2 ^ (k + 2 * n + 3 - n) * Nat.repeat edgeless n 1 : Int) := by push_cast at h ⊢; omega
  have h'' : 2 ^ (k + 2 * n + 3 - n) * Nat.repeat edgeless n 3 =
      2 ^ (k + 2 * n + 3 - n) * (3 * Nat.repeat edgeless n 1) := by
    have := h'; rw [← Int.mul_assoc, Int.mul_comm 3, Int.mul_assoc] at this; exact_mod_cast this
  have := Nat.eq_of_mul_eq_mul_left hpos h''
  omega

end Rule30Open
