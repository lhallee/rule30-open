module

public import Rule30Open.Complexity.LeftCut

/-!
# The left cut through the T-function: windowed rows, the window at `2 ^ j` steps, and rank against width

Split the row after its `a` leftmost cone cells. On the rows that are white right of cell `-t + D - 1`, the center
after `t` steps is bit `D - 1` of `Φ^t(N)`, with `Φ(x) = x xor (2x or 4x)` the kit's T-function
(`Rule30Equivalents.TFunction.Phi`, here `tPhi`, written with shifts) and `N` the cells `-t .. -t + D - 1` read with
cell `-t` as the top bit (`window_center`). The proof runs the repository's number evolution `nevo` backwards on `D`
bits (`tPhiIter_rev`).

`Φ^(2^j)` is the identity on the lowest `j + 1` bits (`tPhiIter_two_pow`, the kit's `orbit_two_pow_mod`, proved here
again since this library does not depend on the kit's equivalent forms): bit `n` of `Φ^L(x)` is `x_n` plus the parity
of a function of the lower bits along the orbit (`testBit_tPhiIter`), and going twice around a cycle of the lower bits
adds that parity twice. So on every row white right of cell `-2^j + j` the center after `2^j` steps is the cell
`-2^j` (`center_two_pow`): every left cut matrix restricted to such rows has rank 1, and a lower bound for the rank of
the cut that holds for every `t` cannot use right settings of a fixed width.

`width_of_independent` is the step from rank to width, in the conventions of `left_cut_factor`: left settings whose
rows are independent over GF(2) (every nonempty set of them has a completion on which an odd number of their centers
is black) have pairwise different states in every factorization of the center through the cut.

The natural-language argument is `LeftCutRank.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

/-! ## The T-function -/

/-- The kit's `Φ(x) = x xor (2x or 4x)`, one step of Rule 30 on a row written as a binary number with its leftmost
cell as the top bit. -/
def tPhi (x : Nat) : Nat := x ^^^ ((x <<< 1) ||| (x <<< 2))

/-- `Φ` applied `s` times. -/
def tPhiIter : Nat → Nat → Nat
  | 0, x => x
  | s + 1, x => tPhi (tPhiIter s x)

/-- The part of bit `j` of `Φ x` that comes from the bits below `j`: `x_{j-1} or x_{j-2}`. -/
def tLow (x j : Nat) : Bool := (decide (1 ≤ j) && x.testBit (j - 1)) || (decide (2 ≤ j) && x.testBit (j - 2))

theorem testBit_tPhi (x j : Nat) : (tPhi x).testBit j = xor (x.testBit j) (tLow x j) := by
  simp only [tPhi, tLow, Nat.testBit_xor, Nat.testBit_or, Nat.testBit_shiftLeft]

theorem tPhiIter_add (L x : Nat) : ∀ s, tPhiIter (s + L) x = tPhiIter s (tPhiIter L x)
  | 0 => by rw [Nat.zero_add]; rfl
  | s + 1 => by
    rw [show s + 1 + L = (s + L) + 1 by omega]
    simp only [tPhiIter]
    rw [tPhiIter_add L x s]

/-! ## Windowed rows -/

/-- Bit `j < D` of `Φ^s(N)` is bit `D - 1 - j` of `nevo R s`, when `R` has no bit from `D` on and `N` is `R` read
backwards on `D` bits; `nevo R s` keeps no bit from `D` on. -/
theorem tPhiIter_rev (D R N : Nat) (hR : ∀ k, D ≤ k → R.testBit k = false)
    (hN : ∀ j, j < D → N.testBit j = R.testBit (D - 1 - j)) :
    ∀ s, (∀ k, D ≤ k → (nevo R s).testBit k = false) ∧
      ∀ j, j < D → (tPhiIter s N).testBit j = (nevo R s).testBit (D - 1 - j) := by
  intro s
  induction s with
  | zero => exact ⟨hR, hN⟩
  | succ s ih =>
    obtain ⟨h1, h2⟩ := ih
    constructor
    · intro k hk
      simp only [nevo, nstep, Nat.testBit_xor, Nat.testBit_or, Nat.testBit_shiftRight]
      rw [h1 k hk, h1 (1 + k) (by omega), h1 (2 + k) (by omega)]
      rfl
    · intro j hj
      simp only [tPhiIter, nevo, nstep]
      rw [testBit_tPhi, Nat.testBit_xor, Nat.testBit_or, Nat.testBit_shiftRight, Nat.testBit_shiftRight, h2 j hj]
      congr 1
      simp only [tLow]
      match j, hj with
      | 0, _ =>
        rw [h1 (1 + (D - 1 - 0)) (by omega), h1 (2 + (D - 1 - 0)) (by omega)]
        rfl
      | 1, _ =>
        rw [h2 0 (by omega), h1 (2 + (D - 1 - 1)) (by omega), show 1 + (D - 1 - 1) = D - 1 - 0 by omega]
        simp
      | j + 2, hj =>
        rw [h2 (j + 2 - 1) (by omega), h2 (j + 2 - 2) (by omega), show 1 + (D - 1 - (j + 2)) = D - 1 - (j + 2 - 1) by omega,
          show 2 + (D - 1 - (j + 2)) = D - 1 - (j + 2 - 2) by omega]
        simp

/-- The cells `-t .. -t + D - 1` of `x` as a number, cell `-t` the top bit `D - 1`. -/
def windowNum (x : Int → Bool) (t D : Nat) : Nat := enc (fun k => x (-(t : Int) + ((D - 1 - k : Nat) : Int))) D

/-- **The center of a windowed row is the top bit of `Φ^t`.** On a row white right of cell `-t + D - 1`, the center
after `t` steps is bit `D - 1` of `Φ^t(N)`, `N` the cells `-t .. -t + D - 1` with cell `-t` on top. -/
theorem window_center (x : Int → Bool) (t D : Nat) (hD : 1 ≤ D)
    (hw : ∀ i : Int, -(t : Int) + D ≤ i → x i = false) :
    evo x t 0 = (tPhiIter t (windowNum x t D)).testBit (D - 1) := by
  have hR : ∀ k, D ≤ k → (enc (fun k => x ((k : Int) - t)) D).testBit k = false := fun k hk =>
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (enc_lt D _) (Nat.pow_le_pow_right (by omega) hk))
  have hloc : evo x t 0 = evo (rowN (enc (fun k => x ((k : Int) - t)) D) (-(t : Int))) t 0 := by
    apply evo_local
    intro i h1 h2
    simp only [rowN]
    rw [ite_eq_left (by omega)]
    by_cases hi : i < -(t : Int) + D
    · rw [testBit_enc _ _ _ (by omega)]
      congr 1
      omega
    · rw [hw i (by omega), hR _ (by omega)]
  rw [hloc, evo_rowN _ _ _ 0 (by omega)]
  simp only [rowN]
  rw [ite_eq_left (by omega), show (0 - (-(t : Int) + (t : Int))).toNat = 0 by omega]
  have hN : ∀ j, j < D → (windowNum x t D).testBit j = (enc (fun k => x ((k : Int) - t)) D).testBit (D - 1 - j) := by
    intro j hj
    simp only [windowNum]
    rw [testBit_enc _ _ _ hj, testBit_enc _ _ _ (by omega)]
    congr 1
    omega
  rw [(tPhiIter_rev D _ _ hR hN t).2 (D - 1) (by omega), show D - 1 - (D - 1) = 0 by omega]

/-! ## `Φ^(2^j)` on the lowest `j + 1` bits -/

/-- `x` and `y` agree on their lowest `n` bits. -/
def BitsAgree (n x y : Nat) : Prop := ∀ i, i < n → x.testBit i = y.testBit i

theorem bitsAgree_tPhi {n x y : Nat} (h : BitsAgree n x y) : BitsAgree n (tPhi x) (tPhi y) := by
  intro i hi
  rw [testBit_tPhi, testBit_tPhi, h i hi]
  simp only [tLow]
  rw [h (i - 1) (by omega), h (i - 2) (by omega)]

theorem bitsAgree_iter {n x y : Nat} (h : BitsAgree n x y) : ∀ s, BitsAgree n (tPhiIter s x) (tPhiIter s y)
  | 0 => h
  | s + 1 => bitsAgree_tPhi (bitsAgree_iter h s)

theorem tLow_congr {n x y : Nat} (h : BitsAgree n x y) : tLow x n = tLow y n := by
  simp only [tLow]
  match n, h with
  | 0, _ => rfl
  | 1, h => rw [h 0 (by omega)]
  | n + 2, h => rw [h (n + 2 - 1) (by omega), h (n + 2 - 2) (by omega)]

/-- The parity of `tLow · n` along the first `L` points of the orbit of `x`. -/
def tLowPar (n x : Nat) : Nat → Bool
  | 0 => false
  | L + 1 => xor (tLowPar n x L) (tLow (tPhiIter L x) n)

/-- **Bit `n` of `Φ^L(x)` is `x_n` plus the parity of `tLow · n` along the orbit** (the kit's `testBit_iterate`). -/
theorem testBit_tPhiIter (n x : Nat) : ∀ L, (tPhiIter L x).testBit n = xor (x.testBit n) (tLowPar n x L)
  | 0 => by simp [tPhiIter, tLowPar]
  | L + 1 => by
    simp only [tPhiIter, tLowPar]
    rw [testBit_tPhi, testBit_tPhiIter n x L, Bool.xor_assoc]

/-- Along a cycle of the lowest `n` bits, the parities of consecutive stretches add. -/
theorem tLowPar_add {n x L : Nat} (hL : BitsAgree n (tPhiIter L x) x) :
    ∀ M, tLowPar n x (M + L) = xor (tLowPar n x L) (tLowPar n x M)
  | 0 => by simp [tLowPar]
  | M + 1 => by
    rw [show M + 1 + L = (M + L) + 1 by omega]
    simp only [tLowPar]
    rw [tLowPar_add hL M, tPhiIter_add L x M, tLow_congr (bitsAgree_iter hL M), Bool.xor_assoc]

/-- **`Φ^(2^j)` fixes the lowest `j + 1` bits** (the kit's `orbit_two_pow_mod`). -/
theorem tPhiIter_two_pow : ∀ j x, BitsAgree (j + 1) (tPhiIter (2 ^ j) x) x
  | 0, x => by
    intro i hi
    have : i = 0 := by omega
    subst this
    simp only [Nat.pow_zero, tPhiIter]
    rw [testBit_tPhi]
    simp [tLow]
  | j + 1, x => by
    have ih := tPhiIter_two_pow j
    have hsplit : tPhiIter (2 ^ (j + 1)) x = tPhiIter (2 ^ j) (tPhiIter (2 ^ j) x) := by
      rw [Nat.pow_succ, Nat.mul_two, tPhiIter_add]
    intro i hi
    by_cases hij : i < j + 1
    · rw [hsplit, ih _ i hij, ih x i hij]
    · have hi' : i = j + 1 := by omega
      subst hi'
      rw [testBit_tPhiIter, Nat.pow_succ, Nat.mul_two, tLowPar_add (ih x) (2 ^ j)]
      simp

/-- **After `2^j` steps, a row white right of cell `-2^j + j` has the center of its cell `-2^j`.** So at the left cut
after `a ≤ j + 1` cells, the right settings white from cell `-2^j + j + 1` on leave a matrix of rank 1. -/
theorem center_two_pow (j : Nat) (x : Int → Bool)
    (hw : ∀ i : Int, -((2 ^ j : Nat) : Int) + (j : Int) < i → x i = false) :
    evo x (2 ^ j) 0 = x (-((2 ^ j : Nat) : Int)) := by
  rw [window_center x (2 ^ j) (j + 1) (by omega) (fun i hi => hw i (by omega)),
    show j + 1 - 1 = j by omega, tPhiIter_two_pow j _ j (by omega)]
  simp only [windowNum]
  rw [testBit_enc _ _ _ (by omega)]
  congr 1
  omega

/-! ## Rank against width -/

/-- The parity of `p 0, ..., p (m - 1)`. -/
def parityUpTo (p : Nat → Bool) : Nat → Bool
  | 0 => false
  | m + 1 => xor (parityUpTo p m) (p m)

theorem parity_pair (v : Nat → Bool) (i j : Nat) (hij : i ≠ j) : ∀ m,
    parityUpTo (fun k => (k == i || k == j) && v k) m = xor (decide (i < m) && v i) (decide (j < m) && v j) := by
  intro m
  induction m with
  | zero => simp [parityUpTo]
  | succ m ih =>
    simp only [parityUpTo]
    rw [ih]
    by_cases hi : m = i
    · subst hi
      have hj : (m == j) = false := by simp [hij]
      have e1 : decide (m < m + 1) = true := by simp
      have e2 : decide (m < m) = false := by simp
      have e3 : decide (j < m + 1) = decide (j < m) := by
        apply decide_eq_decide.mpr
        omega
      simp only [beq_self_eq_true, hj, Bool.true_or, Bool.true_and, e1, e2, e3, Bool.false_and]
      cases v m <;> cases decide (j < m) <;> cases v j <;> rfl
    · by_cases hj : m = j
      · subst hj
        have hi' : (m == i) = false := by simp [hi]
        have e1 : decide (m < m + 1) = true := by simp
        have e2 : decide (m < m) = false := by simp
        have e3 : decide (i < m + 1) = decide (i < m) := by
          apply decide_eq_decide.mpr
          omega
        simp only [beq_self_eq_true, hi', Bool.or_true, Bool.true_and, e1, e2, e3, Bool.false_and]
        cases v m <;> cases decide (i < m) <;> cases v i <;> rfl
      · have hi' : (m == i) = false := by simp [hi]
        have hj' : (m == j) = false := by simp [hj]
        have e3 : decide (i < m + 1) = decide (i < m) := by
          apply decide_eq_decide.mpr
          omega
        have e4 : decide (j < m + 1) = decide (j < m) := by
          apply decide_eq_decide.mpr
          omega
        simp only [hi', hj', Bool.false_or, Bool.false_and, Bool.xor_false, e3, e4]

/-- **Independent rows have different states.** If the center factors through a set `S` at the cut `a`
(`left_cut_factor`) and the left settings `rows 0, ..., rows (m - 1)` are independent over GF(2) (every nonempty set
of them has a completion on which an odd number of their centers is black), then they have pairwise different states,
so `S` has at least `m` elements: the GF(2) rank of the cut is at most the width of every ordered decision diagram
that reads the row from the left, at that level. -/
theorem width_of_independent (t : Nat) (a : Int) {S : Type} (F : (Int → Bool) → S) (G : S → (Int → Bool) → Bool)
    (hFG : ∀ x z, evo (spliceAt a x z) t 0 = G (F x) z) (m : Nat) (rows : Nat → Int → Bool)
    (hind : ∀ c : Nat → Bool, (∃ i, i < m ∧ c i = true) →
      ∃ z, parityUpTo (fun k => c k && evo (spliceAt a (rows k) z) t 0) m = true) :
    ∀ i j, i < m → j < m → F (rows i) = F (rows j) → i = j := by
  intro i j hi hj hF
  apply Classical.byContradiction
  intro hij
  obtain ⟨z, hz⟩ := hind (fun k => k == i || k == j) ⟨i, hi, by simp⟩
  have e : (fun k => (k == i || k == j) && evo (spliceAt a (rows k) z) t 0) =
      (fun k => (k == i || k == j) && G (F (rows k)) z) := by
    funext k
    rw [hFG]
  rw [e, parity_pair _ i j hij m] at hz
  simp only [decide_eq_true hi, decide_eq_true hj, Bool.true_and, hF, Bool.xor_self] at hz
  exact Bool.false_ne_true hz

end Rule30Open
