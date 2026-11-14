module

public import Rule30Open.PeriodTwo.ShiftModel

/-!
# The held map is a similarity of ratio 2^n on each class modulo 2^n

For numbers `U ≡ V (mod 2^n)` and `m ≥ n`, the images under `n` steps of the held map `heldNat` are congruent modulo
`2^(m - n)` exactly when `U ≡ V (mod 2^m)` (`heldNat_repeat_mod_iff`): in 2-adic terms, `H^n` multiplies distances
by exactly `2^n` on each class modulo `2^n`. Every residue modulo `2^(m - n)` is the image of a number in every class
modulo `2^n` (`heldNat_repeat_onto`). Both follow from the triangular form `heldOrbit_triangular` of `ShiftModel`.

The natural-language argument is `HeldClasses.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

theorem mod_two_pow_eq_iff (x y m : Nat) : x % 2 ^ m = y % 2 ^ m ↔ ∀ i, i < m → x.testBit i = y.testBit i := by
  constructor
  · intro h i hi
    have := congrArg (fun z => z.testBit i) h
    simpa [Nat.testBit_mod_two_pow, hi] using this
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_mod_two_pow]
    by_cases hi : i < m
    · simp [hi, h i hi]
    · simp [hi]

/-- On bit sequences that agree below `n`: the orbits after `n` steps agree below `k` exactly when the sequences
agree below `k + n`. -/
theorem heldOrbit_agree_iff (u v : Nat → Bool) (n : Nat) (h : ∀ i, i < n → u i = v i) :
    ∀ k, (∀ j, j < k → heldOrbit u n j = heldOrbit v n j) ↔ (∀ i, i < k + n → u i = v i) := by
  intro k
  induction k with
  | zero => exact ⟨fun _ => by simpa using h, fun _ j hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ k ih =>
    constructor
    · intro hk
      have hlow : ∀ i, i < k + n → u i = v i := ih.1 fun j hj => hk j (by omega)
      have tri := heldOrbit_triangular n k u v hlow
      rw [hk k (by omega)] at tri
      have hb : u (k + n) = v (k + n) := by
        revert tri
        cases heldOrbit v n k <;> cases u (k + n) <;> cases v (k + n) <;> simp
      intro i hi
      by_cases hik : i < k + n
      · exact hlow i hik
      · rw [show i = k + n by omega]; exact hb
    · intro hk
      have hlow : ∀ i, i < k + n → u i = v i := fun i hi => hk i (by omega)
      have tri := heldOrbit_triangular n k u v hlow
      rw [hk (k + n) (by omega)] at tri
      have hb : heldOrbit u n k = heldOrbit v n k := by
        revert tri
        cases heldOrbit u n k <;> cases heldOrbit v n k <;> cases v (k + n) <;> simp
      intro j hj
      by_cases hjk : j < k
      · exact ih.2 hlow j hjk
      · rw [show j = k by omega]; exact hb

/-- **Similarity on classes.** For `U ≡ V (mod 2^n)` and `m ≥ n`, `H^n U ≡ H^n V (mod 2^(m - n))` exactly when
`U ≡ V (mod 2^m)`. -/
theorem heldNat_repeat_mod_iff (n m U V : Nat) (hnm : n ≤ m) (h : U % 2 ^ n = V % 2 ^ n) :
    Nat.repeat heldNat n U % 2 ^ (m - n) = Nat.repeat heldNat n V % 2 ^ (m - n) ↔ U % 2 ^ m = V % 2 ^ m := by
  rw [mod_two_pow_eq_iff, mod_two_pow_eq_iff]
  simp only [heldNat_repeat_testBit]
  rw [mod_two_pow_eq_iff] at h
  rw [heldOrbit_agree_iff _ _ n h (m - n), show m - n + n = m by omega]

/-- Flipping bit `n + k` of a number with `n` steps to go flips bit `k` of its image and keeps the bits below. -/
theorem heldNat_repeat_flip (n k U : Nat) :
    (∀ j, j < k → (Nat.repeat heldNat n (U ^^^ 2 ^ (k + n))).testBit j = (Nat.repeat heldNat n U).testBit j) ∧
      (Nat.repeat heldNat n (U ^^^ 2 ^ (k + n))).testBit k = !(Nat.repeat heldNat n U).testBit k := by
  have hbit : ∀ i, (U ^^^ 2 ^ (k + n)).testBit i = (U.testBit i ^^ decide (k + n = i)) := by
    intro i; simp [Nat.testBit_xor, Nat.testBit_two_pow]
  have hlow : ∀ i, i < k + n → (U ^^^ 2 ^ (k + n)).testBit i = U.testBit i := by
    intro i hi; rw [hbit]; simp [show k + n ≠ i by omega]
  have hn : ∀ i, i < n → (U ^^^ 2 ^ (k + n)).testBit i = U.testBit i := fun i hi => hlow i (by omega)
  simp only [heldNat_repeat_testBit]
  refine ⟨(heldOrbit_agree_iff _ _ n hn k).2 fun i hi => hlow i (by omega), ?_⟩
  have tri := heldOrbit_triangular n k (fun i => (U ^^^ 2 ^ (k + n)).testBit i) (fun i => U.testBit i) hlow
  have hk' : (U ^^^ 2 ^ (k + n)).testBit (k + n) = !U.testBit (k + n) := by rw [hbit]; simp
  rw [hk'] at tri
  revert tri
  generalize heldOrbit (fun i => (U ^^^ 2 ^ (k + n)).testBit i) n k = x
  generalize heldOrbit (fun i => U.testBit i) n k = y
  cases x <;> cases y <;> cases U.testBit (k + n) <;> simp

/-- **Onto.** Every residue `W` modulo `2^k` is the image under `H^n` of a number in the class of `a` modulo `2^n`. -/
theorem heldNat_repeat_onto (n a W : Nat) :
    ∀ k, ∃ U, U % 2 ^ n = a % 2 ^ n ∧ Nat.repeat heldNat n U % 2 ^ k = W % 2 ^ k := by
  intro k
  induction k with
  | zero => exact ⟨a, rfl, by simp [Nat.pow_zero, Nat.mod_one]⟩
  | succ k ih =>
    obtain ⟨U, hU, hW⟩ := ih
    rw [mod_two_pow_eq_iff] at hW
    by_cases hk : (Nat.repeat heldNat n U).testBit k = W.testBit k
    · refine ⟨U, hU, (mod_two_pow_eq_iff _ _ _).2 fun j hj => ?_⟩
      by_cases hjk : j < k
      · exact hW j hjk
      · rw [show j = k by omega]; exact hk
    · obtain ⟨hl, hf⟩ := heldNat_repeat_flip n k U
      refine ⟨U ^^^ 2 ^ (k + n), ?_, (mod_two_pow_eq_iff _ _ _).2 fun j hj => ?_⟩
      · rw [mod_two_pow_eq_iff] at hU ⊢
        intro i hi
        rw [← hU i hi]
        simp [Nat.testBit_xor, show k + n ≠ i by omega]
      · by_cases hjk : j < k
        · rw [hl j hjk]; exact hW j hjk
        · rw [show j = k by omega, hf]
          revert hk
          cases (Nat.repeat heldNat n U).testBit k <;> cases W.testBit k <;> simp

end Rule30Open
