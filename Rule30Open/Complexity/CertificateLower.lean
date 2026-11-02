module

public import Rule30Open.Complexity.MinCertificate
public import Rule30Open.Complexity.SecondCells

/-!
# The combs that every constant subcube of the center meets

Write `c_t(x) = evo x t 0` for the center after `t` steps from a row `x`, and call a partial row `ρ` a constant
subcube when `CenterConstOn ρ t` (MinCertificate): the center is the same on every row that agrees with `ρ` on its
fixed cells. MinCertificate shows that every such `ρ` fixes the cell `-t` (`constOn_fixes_left`) and that `t - 1`
fixed cells suffice for `t ≥ 9`. This module proves, for every `t`, which further cells near the left edge a constant
subcube must fix.

The comb `B_j(t)` is the set of cells `-t + 1, -t + 3, ..., -t + 2j + 1` and `-t + 2j + 2`.

* `combPar_zero`, `combPar_step`, `combPar_front`: the derivative of `c_t` along cell `-t + 1` is `combPar t 0`, the
  derivative of `combPar t j` along cell `-t + 2j + 3` is `combPar t (j + 1)`, and its derivative along cell
  `-t + 2j + 2` is the constant `pasc t (j + 1)`, the parity of the binomial coefficient `C(t, j + 1)`. Here
  `combPar t j x` is the xor over `q < t` of the negated cells `(q, -t + 2j + 2 + q)` weighted by `C(t - 1 - q, j)`
  mod 2. So the mixed derivative of `c_t` over the comb `B_j(t)` is the constant `C(t, j + 1)` mod 2 on every row.
* `constOn_hits_comb`: when `C(t, j + 1)` is odd, every constant subcube fixes a cell of `B_j(t)`.
* `constOn_odd`: for odd `t` it fixes `-t + 1` or `-t + 2` (`j = 0`); `constOn_two_mod_four`: for `t ≡ 2, 3 mod 4` it
  fixes one of `-t + 1`, `-t + 3`, `-t + 4` (`j = 1`).

The proofs follow the difference that a flip starts along the left edge of the cone: SecondCells' `flip_second_cell`
for the cells one left of its front, and ConeScreening's `front_xor` for the front itself. The sums are exchanged by
`fsum_pasc_exchange`, the hockey-stick identity of Pascal's triangle mod 2.

These blocks give no lower bound on the least certificate beyond two cells: they all contain `-t + 1`. The natural
language argument, with the computations that bound what this algebraic route can give, is `CertificateLower.md`,
beside this file.
-/

@[expose] public section

namespace Rule30Open

/-! ## Xor sums -/

/-- The xor of `f 0, ..., f (n - 1)`, peeled from the front. -/
def fsum : Nat → (Nat → Bool) → Bool
  | 0, _ => false
  | n + 1, f => xor (f 0) (fsum n (fun q => f (q + 1)))

theorem fsum_succ_last : ∀ (n : Nat) (f : Nat → Bool), fsum (n + 1) f = xor (fsum n f) (f n)
  | 0, f => by simp [fsum]
  | n + 1, f => by
    show xor (f 0) (fsum (n + 1) (fun q => f (q + 1))) = xor (xor (f 0) (fsum n (fun q => f (q + 1)))) (f (n + 1))
    rw [fsum_succ_last n]
    rw [Bool.xor_assoc]

theorem fsum_congr : ∀ (n : Nat) (f g : Nat → Bool), (∀ q, q < n → f q = g q) → fsum n f = fsum n g
  | 0, _, _, _ => rfl
  | n + 1, f, g, h => by
    show xor (f 0) (fsum n (fun q => f (q + 1))) = xor (g 0) (fsum n (fun q => g (q + 1)))
    rw [h 0 (by omega), fsum_congr n _ _ (fun q hq => h (q + 1) (by omega))]

theorem fsum_xor : ∀ (n : Nat) (f g : Nat → Bool),
    fsum n (fun q => xor (f q) (g q)) = xor (fsum n f) (fsum n g)
  | 0, _, _ => rfl
  | n + 1, f, g => by
    show xor (xor (f 0) (g 0)) (fsum n (fun q => xor (f (q + 1)) (g (q + 1)))) =
      xor (xor (f 0) (fsum n (fun q => f (q + 1)))) (xor (g 0) (fsum n (fun q => g (q + 1))))
    rw [fsum_xor n]
    generalize f 0 = a
    generalize g 0 = b
    generalize fsum n (fun q => f (q + 1)) = c
    generalize fsum n (fun q => g (q + 1)) = d
    revert a b c d
    decide

theorem fsum_and_left : ∀ (n : Nat) (c : Bool) (f : Nat → Bool), fsum n (fun q => c && f q) = (c && fsum n f)
  | 0, c, _ => by cases c <;> rfl
  | n + 1, c, f => by
    show xor (c && f 0) (fsum n (fun q => c && f (q + 1))) = (c && xor (f 0) (fsum n (fun q => f (q + 1))))
    rw [fsum_and_left n]
    cases c <;> simp

/-- SecondCells' `diagPar` as an xor sum. -/
theorem diagPar_eq_fsum (x : Int → Bool) (a : Int) : ∀ s : Nat,
    diagPar x a s = fsum s (fun r => !evo x r (a + 1 + r))
  | 0 => rfl
  | s + 1 => by
    rw [fsum_succ_last, ← diagPar_eq_fsum x a s]
    rfl

/-! ## Pascal's triangle mod 2 -/

/-- `pasc n k` is the parity of the binomial coefficient `C(n, k)`, by Pascal's rule. -/
def pasc : Nat → Nat → Bool
  | _, 0 => true
  | 0, _ + 1 => false
  | n + 1, k + 1 => xor (pasc n k) (pasc n (k + 1))

theorem pasc_zero (n : Nat) : pasc n 0 = true := by cases n <;> rfl

/-- The hockey-stick identity mod 2: `C(n - 1, j) + ... + C(0, j) = C(n, j + 1)`. -/
theorem fsum_pasc (j : Nat) : ∀ n : Nat, fsum n (fun q => pasc (n - 1 - q) j) = pasc n (j + 1)
  | 0 => rfl
  | n + 1 => by
    show xor (pasc (n + 1 - 1 - 0) j) (fsum n (fun q => pasc (n + 1 - 1 - (q + 1)) j)) = pasc (n + 1) (j + 1)
    rw [fsum_congr n _ (fun q => pasc (n - 1 - q) j) (fun q _ => by congr 1; omega), fsum_pasc j n]
    have e : n + 1 - 1 - 0 = n := by omega
    rw [e]
    rfl

/-- **The exchange of the two sums.** Weighting the prefix xors of `y` by the column `j` of Pascal's triangle mod 2
is weighting `y` itself by the column `j + 1`. -/
theorem fsum_pasc_exchange (j : Nat) : ∀ (n : Nat) (y : Nat → Bool),
    fsum n (fun q => pasc (n - 1 - q) j && fsum q y) = fsum n (fun r => pasc (n - 1 - r) (j + 1) && y r)
  | 0, _ => rfl
  | n + 1, y => by
    show xor (pasc (n + 1 - 1 - 0) j && fsum 0 y) (fsum n (fun q => pasc (n + 1 - 1 - (q + 1)) j && fsum (q + 1) y)) =
      xor (pasc (n + 1 - 1 - 0) (j + 1) && y 0) (fsum n (fun r => pasc (n + 1 - 1 - (r + 1)) (j + 1) && y (r + 1)))
    have e : n + 1 - 1 - 0 = n := by omega
    rw [e]
    rw [fsum_congr n (fun q => pasc (n + 1 - 1 - (q + 1)) j && fsum (q + 1) y)
      (fun q => xor (y 0 && pasc (n - 1 - q) j) (pasc (n - 1 - q) j && fsum q (fun r => y (r + 1))))
      (fun q _ => by
        have e2 : n + 1 - 1 - (q + 1) = n - 1 - q := by omega
        rw [e2]
        show (pasc (n - 1 - q) j && xor (y 0) (fsum q (fun r => y (r + 1)))) = _
        generalize pasc (n - 1 - q) j = p
        generalize y 0 = a
        generalize fsum q (fun r => y (r + 1)) = b
        revert p a b
        decide)]
    rw [fsum_congr n (fun r => pasc (n + 1 - 1 - (r + 1)) (j + 1) && y (r + 1))
      (fun r => pasc (n - 1 - r) (j + 1) && y (r + 1)) (fun r _ => by congr 2; omega)]
    rw [fsum_xor, fsum_and_left, fsum_pasc j n, fsum_pasc_exchange j n (fun r => y (r + 1))]
    rw [show fsum 0 y = false from rfl]
    generalize fsum n (fun r => pasc (n - 1 - r) (j + 1) && y (r + 1)) = d
    generalize pasc n (j + 1) = p
    generalize pasc n j = p'
    generalize y 0 = a
    revert d p p' a
    decide

/-! ## The derivatives along the comb -/

/-- The xor over `q < t` of the negated cells `(q, -t + 2j + 2 + q)`, each weighted by `C(t - 1 - q, j)` mod 2. -/
def combPar (t j : Nat) (x : Int → Bool) : Bool :=
  fsum t (fun q => pasc (t - 1 - q) j && !evo x q (-(t : Int) + 2 + 2 * (j : Int) + q))

/-- The derivative of the center along cell `-t + 1` is `combPar t 0`. -/
theorem combPar_zero (t : Nat) (x : Int → Bool) : combPar t 0 x = diagPar x (-(t : Int) + 1) t := by
  rw [diagPar_eq_fsum]
  unfold combPar
  apply fsum_congr
  intro q _
  have e : -(t : Int) + 2 + 2 * ((0 : Nat) : Int) + q = -(t : Int) + 1 + 1 + q := by omega
  rw [e, pasc_zero]
  rfl

/-- **The front of the comb.** Flipping cell `-t + 2j + 2` changes `combPar t j` by `C(t, j + 1)` mod 2, on every
row. -/
theorem combPar_front (t j : Nat) (x : Int → Bool) :
    combPar t j (flipAt x (-(t : Int) + 2 + 2 * (j : Int))) = xor (combPar t j x) (pasc t (j + 1)) := by
  unfold combPar
  rw [← fsum_pasc j t, ← fsum_xor]
  apply fsum_congr
  intro q _
  have hf := front_xor x (flipAt x (-(t : Int) + 2 + 2 * (j : Int))) (-(t : Int) + 2 + 2 * (j : Int))
    (fun i hi => (flipAt_of_ne x (by omega)).symm) q
  have hfa : flipAt x (-(t : Int) + 2 + 2 * (j : Int)) (-(t : Int) + 2 + 2 * (j : Int)) =
      !x (-(t : Int) + 2 + 2 * (j : Int)) := by simp [flipAt]
  rw [hf, hfa]
  generalize pasc (t - 1 - q) j = p
  generalize evo x q (-(t : Int) + 2 + 2 * (j : Int) + q) = e
  generalize x (-(t : Int) + 2 + 2 * (j : Int)) = c
  revert p e c
  decide

/-- **One tooth further.** Flipping cell `-t + 2j + 3` changes `combPar t j` by `combPar t (j + 1)`, on every row. -/
theorem combPar_step (t j : Nat) (x : Int → Bool) :
    combPar t j (flipAt x (-(t : Int) + 3 + 2 * (j : Int))) = xor (combPar t j x) (combPar t (j + 1) x) := by
  have key : combPar t (j + 1) x =
      fsum t (fun q => pasc (t - 1 - q) j && diagPar x (-(t : Int) + 3 + 2 * (j : Int)) q) := by
    rw [fsum_congr t _ (fun q => pasc (t - 1 - q) j &&
      fsum q (fun r => !evo x r (-(t : Int) + 3 + 2 * (j : Int) + 1 + r))) (fun q _ => by rw [diagPar_eq_fsum])]
    rw [fsum_pasc_exchange]
    unfold combPar
    apply fsum_congr
    intro r _
    have e : -(t : Int) + 2 + 2 * ((j + 1 : Nat) : Int) + r = -(t : Int) + 3 + 2 * (j : Int) + 1 + r := by
      push_cast; omega
    rw [e]
  rw [key]
  unfold combPar
  rw [← fsum_xor]
  apply fsum_congr
  intro q _
  have hs := flip_second_cell x (-(t : Int) + 3 + 2 * (j : Int)) q
  have e : -(t : Int) + 3 + 2 * (j : Int) - 1 + q = -(t : Int) + 2 + 2 * (j : Int) + q := by omega
  rw [e] at hs
  rw [hs]
  generalize pasc (t - 1 - q) j = p
  generalize evo x q (-(t : Int) + 2 + 2 * (j : Int) + q) = a
  generalize diagPar x (-(t : Int) + 3 + 2 * (j : Int)) q = d
  revert p a d
  decide

/-! ## Constant subcubes meet every comb with an odd binomial -/

/-- Flipping a free cell commutes with filling in the fixed cells. -/
theorem fillRow_flipAt_none (ρ : Int → Option Bool) (u : Int) (hu : ρ u = none) (x : Int → Bool) :
    fillRow ρ (flipAt x u) = flipAt (fillRow ρ x) u := by
  funext i
  by_cases hi : i = u
  · subst hi; simp [fillRow, flipAt, hu]
  · simp only [fillRow, flipAt, hi, ite_false]

/-- **Every constant subcube meets the comb `B_j(t)` when `C(t, j + 1)` is odd.** If the cells `-t + 1 + 2i`
(`i ≤ j`) and `-t + 2j + 2` were all free, the mixed derivative of the center over them would vanish on the subcube,
and it is `C(t, j + 1)` mod 2. -/
theorem constOn_hits_comb (ρ : Int → Option Bool) (t j : Nat) (h : CenterConstOn ρ t)
    (hodd : pasc t (j + 1) = true)
    (hfree : ∀ i : Nat, i ≤ j → ρ (-(t : Int) + 1 + 2 * (i : Int)) = none)
    (hlast : ρ (-(t : Int) + 2 + 2 * (j : Int)) = none) : False := by
  have zero : ∀ x, combPar t 0 (fillRow ρ x) = false := by
    intro x
    rw [combPar_zero]
    have hu : ρ (-(t : Int) + 1) = none := by simpa using hfree 0 (Nat.zero_le _)
    have hc := h (flipAt x (-(t : Int) + 1)) x
    rw [fillRow_flipAt_none ρ _ hu, center_flip_second] at hc
    revert hc
    generalize evo (fillRow ρ x) t 0 = c
    generalize diagPar (fillRow ρ x) (-(t : Int) + 1) t = d
    revert c d
    decide
  have teeth : ∀ i : Nat, i ≤ j → ∀ x, combPar t i (fillRow ρ x) = false := by
    intro i
    induction i with
    | zero => intro _; exact zero
    | succ i ih =>
      intro hi x
      have hu : ρ (-(t : Int) + 3 + 2 * (i : Int)) = none := by
        have e : -(t : Int) + 3 + 2 * (i : Int) = -(t : Int) + 1 + 2 * ((i + 1 : Nat) : Int) := by push_cast; omega
        rw [e]; exact hfree (i + 1) hi
      have hb := combPar_step t i (fillRow ρ x)
      rw [← fillRow_flipAt_none ρ _ hu, ih (by omega), ih (by omega)] at hb
      revert hb
      generalize combPar t (i + 1) (fillRow ρ x) = d
      revert d
      decide
  have fin := combPar_front t j (fillRow ρ (fun _ => false))
  rw [← fillRow_flipAt_none ρ _ hlast, teeth j (Nat.le_refl j), teeth j (Nat.le_refl j), hodd] at fin
  exact absurd fin (by decide)

theorem pasc_one : ∀ n : Nat, pasc n 1 = decide (n % 2 = 1)
  | 0 => rfl
  | n + 1 => by
    show xor (pasc n 0) (pasc n 1) = decide ((n + 1) % 2 = 1)
    rw [pasc_zero, pasc_one n, odd_succ]
    cases decide (n % 2 = 1) <;> rfl

theorem pasc_two : ∀ n : Nat, pasc n 2 = decide (n / 2 % 2 = 1)
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
    show xor (pasc (n + 1) 1) (xor (pasc n 1) (pasc n 2)) = decide ((n + 2) / 2 % 2 = 1)
    rw [pasc_one, pasc_one, pasc_two n, odd_succ]
    have e : (n + 2) / 2 = n / 2 + 1 := by omega
    rw [e, odd_succ]
    generalize decide (n % 2 = 1) = a
    generalize decide (n / 2 % 2 = 1) = b
    revert a b
    decide

/-- **Odd `t`: a constant subcube fixes cell `-t + 1` or cell `-t + 2`** (the comb `B_0(t)`, `C(t, 1) = t`). With
`constOn_fixes_left`, it fixes at least two of the three leftmost cells of the cone. -/
theorem constOn_odd (ρ : Int → Option Bool) (t : Nat) (h : CenterConstOn ρ t) (ht : t % 2 = 1) :
    ρ (-(t : Int) + 1) ≠ none ∨ ρ (-(t : Int) + 2) ≠ none := by
  by_cases h1 : ρ (-(t : Int) + 1) = none
  · by_cases h2 : ρ (-(t : Int) + 2) = none
    · refine (constOn_hits_comb ρ t 0 h (by rw [pasc_one]; simp [ht]) (fun i hi => ?_) (by simpa using h2)).elim
      have : i = 0 := by omega
      subst this
      simpa using h1
    · exact Or.inr h2
  · exact Or.inl h1

/-- **`t ≡ 2, 3 mod 4`: a constant subcube fixes one of the cells `-t + 1`, `-t + 3`, `-t + 4`** (the comb `B_1(t)`,
`C(t, 2) = t (t - 1) / 2`). -/
theorem constOn_two_mod_four (ρ : Int → Option Bool) (t : Nat) (h : CenterConstOn ρ t)
    (ht : t % 4 = 2 ∨ t % 4 = 3) :
    ρ (-(t : Int) + 1) ≠ none ∨ ρ (-(t : Int) + 3) ≠ none ∨ ρ (-(t : Int) + 4) ≠ none := by
  have hp : pasc t 2 = true := by
    rw [pasc_two]
    have : t / 2 % 2 = 1 := by omega
    simp [this]
  by_cases h1 : ρ (-(t : Int) + 1) = none
  · by_cases h3 : ρ (-(t : Int) + 3) = none
    · by_cases h4 : ρ (-(t : Int) + 4) = none
      · refine (constOn_hits_comb ρ t 1 h hp (fun i hi => ?_) ?_).elim
        · rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
          · simpa using h1
          · have e : -(t : Int) + 1 + 2 * ((1 : Nat) : Int) = -(t : Int) + 3 := by omega
            rw [e]; exact h3
        · have e : -(t : Int) + 2 + 2 * ((1 : Nat) : Int) = -(t : Int) + 4 := by omega
          rw [e]; exact h4
      · exact Or.inr (Or.inr h4)
    · exact Or.inr (Or.inl h3)
  · exact Or.inl h1

end Rule30Open
