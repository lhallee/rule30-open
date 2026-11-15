module

/-!
# The odd edge codes of period dividing 4 are the rain pair

In the frame of its right edge, one step of rule 30 acts on the edge code `c` of a row (bit `k` is the cell `k` places
left of the edge cell) by `T c 0 = c 0`, `T c 1 = c 1 ⊕ c 0`, `T c (k + 2) = c (k + 2) ⊕ (c (k + 1) ∨ c k)`: the
2-adic map `Φ(y) = y ⊕ (2y ∨ 4y)` (the kit's `Rule30FrozenRuler.T`, restated here so that the module needs only core
Lean).

* `period_four_iff`: **an edge code with bit `0` black satisfies `T⁴ c = c` exactly when it is `rainA = 1 0 1 0 …`
  (`-1/3`) or `rainB = 1 1 0 1 0 …` (`1/3`).** The kit's `Rule30EdgeStaircases.period_two_iff` is the same with `T²`.
  On paper (even codes by `Φ(2z) = 2Φ(z)`, rows by the edge-frame translation) it follows that a row with a white
  right half that comes back after 4 steps moved 4 cells to the right is white or a rain row, which comes back after 2.

The proof follows the columns `b_k(i) = Tⁱ c k`, `i ∈ ℤ/4`. Write `Alt k` when column `k` alternates in `i`.
* `alt_of_or`: if columns `k` and `k + 1` alternate and are complementary, column `k + 2` alternates (its input
  `b_{k+1} ∨ b_k` is black at every step).
* `dead_core`, `not_equal_alt`: if columns `k` and `k + 1` alternate and are equal, column `k + 2` exists but column
  `k + 3` would need an input with three black cells in four steps, an odd number: impossible.
* `main`: so from bit `1` on every column alternates and each is the complement of the one before.
-/

@[expose] public section

namespace Rule30Open.Frames.EdgePeriodFour

/-- One step of rule 30 read from a right edge that advances one cell per step. -/
def T (c : Nat → Bool) : Nat → Bool
  | 0 => c 0
  | 1 => xor (c 1) (c 0)
  | k + 2 => xor (c (k + 2)) (c (k + 1) || c k)

/-- `1 0 1 0 …`: the 2-adic number `-1/3`. -/
def rainA : Nat → Bool := fun k => k % 2 == 0

/-- `1 1 0 1 0 …`: the 2-adic number `1/3`. -/
def rainB : Nat → Bool := fun k => k == 0 || k % 2 == 1

theorem T_rainA : T rainA = rainB := by
  funext k
  match k with
  | 0 => rfl
  | 1 => rfl
  | j + 2 =>
    simp only [T, rainA, rainB]
    rcases Nat.mod_two_eq_zero_or_one j with h | h
    · have h1 : (j + 1) % 2 = 1 := by omega
      have h2 : (j + 2) % 2 = 0 := by omega
      simp [h, h1, h2]
    · have h1 : (j + 1) % 2 = 0 := by omega
      have h2 : (j + 2) % 2 = 1 := by omega
      simp [h, h1, h2]

theorem T_rainB : T rainB = rainA := by
  funext k
  match k with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | j + 3 =>
    show xor (rainB (j + 3)) (rainB (j + 2) || rainB (j + 1)) = rainA (j + 3)
    simp only [rainA, rainB]
    rcases Nat.mod_two_eq_zero_or_one j with h | h
    · have h1 : (j + 1) % 2 = 1 := by omega
      have h2 : (j + 2) % 2 = 0 := by omega
      have h3 : (j + 3) % 2 = 1 := by omega
      simp [h1, h2, h3]
    · have h1 : (j + 1) % 2 = 0 := by omega
      have h2 : (j + 2) % 2 = 1 := by omega
      have h3 : (j + 3) % 2 = 0 := by omega
      simp [h1, h2, h3]

/-- The Boolean core of a dead branch: columns `k` and `k + 1` both equal to the alternating column `a, ¬a, a, ¬a`
give column `k + 2` (`x`) and then no column `k + 3` (`y`) closes up around the four steps. -/
theorem dead_core (a x0 x1 x2 x3 y0 y1 y2 y3 : Bool)
    (h1 : x1 = xor x0 a) (h2 : x2 = xor x1 (!a)) (h3 : x3 = xor x2 a) (h4 : x0 = xor x3 (!a))
    (g1 : y1 = xor y0 (x0 || a)) (g2 : y2 = xor y1 (x1 || !a)) (g3 : y3 = xor y2 (x2 || a))
    (g4 : y0 = xor y3 (x3 || !a)) : False := by
  subst h1 h2 h3 g1 g2 g3
  revert h4 g4
  cases a <;> cases x0 <;> cases y0 <;> decide

/-- **The odd edge codes of period dividing 4.** -/
theorem period_four_iff (c : Nat → Bool) (h0 : c 0 = true) :
    T (T (T (T c))) = c ↔ (c = rainA ∨ c = rainB) := by
  constructor
  · intro h4
    let c1 := T c
    let c2 := T c1
    let c3 := T c2
    have r0 : ∀ k, c1 (k + 2) = xor (c (k + 2)) (c (k + 1) || c k) := fun k => rfl
    have r1 : ∀ k, c2 (k + 2) = xor (c1 (k + 2)) (c1 (k + 1) || c1 k) := fun k => rfl
    have r2 : ∀ k, c3 (k + 2) = xor (c2 (k + 2)) (c2 (k + 1) || c2 k) := fun k => rfl
    have r3 : ∀ k, c (k + 2) = xor (c3 (k + 2)) (c3 (k + 1) || c3 k) := fun k =>
      (congrFun h4 (k + 2)).symm
    -- column k alternates
    let Alt : Nat → Prop := fun k => c1 k = !c k ∧ c2 k = c k ∧ c3 k = !c k
    have z1 : c1 0 = true := h0
    have z2 : c2 0 = true := z1
    have z3 : c3 0 = true := z2
    have alt1 : Alt 1 := by
      have e1 : c1 1 = xor (c 1) (c 0) := rfl
      have e2 : c2 1 = xor (c1 1) (c1 0) := rfl
      have e3 : c3 1 = xor (c2 1) (c2 0) := rfl
      refine ⟨?_, ?_, ?_⟩
      · rw [e1, h0]; cases c 1 <;> rfl
      · rw [e2, z1, e1, h0]; cases c 1 <;> rfl
      · rw [e3, z2, e2, z1, e1, h0]; cases c 1 <;> rfl
    -- complementary alternating columns k, k + 1 give an alternating column k + 2
    have alt_of_or : ∀ k, (c (k + 1) || c k) = true → (c1 (k + 1) || c1 k) = true →
        (c2 (k + 1) || c2 k) = true → Alt (k + 2) := by
      intro k a0 a1 a2
      have e0 := r0 k; have e1 := r1 k; have e2 := r2 k
      rw [a0] at e0; rw [a1] at e1; rw [a2] at e2
      refine ⟨?_, ?_, ?_⟩
      · rw [e0]; cases c (k + 2) <;> simp
      · rw [e1, e0]; cases c (k + 2) <;> simp
      · rw [e2, e1, e0]; cases c (k + 2) <;> simp
    -- equal alternating columns k, k + 1 are a dead branch
    have not_equal_alt : ∀ k, Alt k → Alt (k + 1) → c (k + 1) = c k → False := by
      intro k ak ak1 heq
      obtain ⟨p1, p2, p3⟩ := ak
      obtain ⟨q1, q2, q3⟩ := ak1
      have s0 := r0 k; have s1 := r1 k; have s2 := r2 k; have s3 := r3 k
      have t0 : c1 (k + 3) = xor (c (k + 3)) (c (k + 2) || c (k + 1)) := r0 (k + 1)
      have t1 : c2 (k + 3) = xor (c1 (k + 3)) (c1 (k + 2) || c1 (k + 1)) := r1 (k + 1)
      have t2 : c3 (k + 3) = xor (c2 (k + 3)) (c2 (k + 2) || c2 (k + 1)) := r2 (k + 1)
      have t3 : c (k + 3) = xor (c3 (k + 3)) (c3 (k + 2) || c3 (k + 1)) := r3 (k + 1)
      simp only [q1, q2, q3, p1, p2, p3, heq, Bool.or_self] at s0 s1 s2 s3 t0 t1 t2 t3
      exact dead_core (c k) (c (k + 2)) (c1 (k + 2)) (c2 (k + 2)) (c3 (k + 2))
        (c (k + 3)) (c1 (k + 3)) (c2 (k + 3)) (c3 (k + 3))
        s0 s1 s2 s3 t0 t1 t2 t3
    have or_of_ne : ∀ k, Alt k → c (k + 1) = !c k → Alt (k + 1) →
        (c (k + 1) || c k) = true ∧ (c1 (k + 1) || c1 k) = true ∧ (c2 (k + 1) || c2 k) = true := by
      intro k ak hne ak1
      obtain ⟨p1, p2, _⟩ := ak
      obtain ⟨q1, q2, _⟩ := ak1
      rw [q1, p1, q2, p2, hne]
      cases c k <;> simp
    -- from bit 1 on: alternating columns, each the complement of the one before
    have main : ∀ n, Alt (n + 1) ∧ Alt (n + 2) ∧ c (n + 2) = !c (n + 1) := by
      intro n
      induction n with
      | zero =>
        have a2 : Alt 2 := by
          have e0 := r0 0; have e1 := r1 0; have e2 := r2 0
          rw [h0, Bool.or_true] at e0; rw [z1, Bool.or_true] at e1; rw [z2, Bool.or_true] at e2
          refine ⟨?_, ?_, ?_⟩
          · rw [e0]; cases c 2 <;> simp
          · rw [e1, e0]; cases c 2 <;> simp
          · rw [e2, e1, e0]; cases c 2 <;> simp
        refine ⟨alt1, a2, ?_⟩
        cases hc : c 2 <;> cases hc1 : c 1
        · exact absurd (hc.trans hc1.symm) (fun h => not_equal_alt 1 alt1 a2 h)
        · rfl
        · rfl
        · exact absurd (hc.trans hc1.symm) (fun h => not_equal_alt 1 alt1 a2 h)
      | succ m ih =>
        obtain ⟨am, am1, hne⟩ := ih
        obtain ⟨o0, o1, o2⟩ := or_of_ne (m + 1) am hne am1
        have a3 : Alt (m + 3) := alt_of_or (m + 1) o0 o1 o2
        refine ⟨am1, a3, ?_⟩
        cases hc : c (m + 3) <;> cases hc1 : c (m + 2)
        · exact absurd (hc.trans hc1.symm) (fun h => not_equal_alt (m + 2) am1 a3 h)
        · rfl
        · rfl
        · exact absurd (hc.trans hc1.symm) (fun h => not_equal_alt (m + 2) am1 a3 h)
    have alt : ∀ n, c (n + 1) = (if n % 2 = 0 then c 1 else !c 1) := by
      intro n
      induction n with
      | zero => simp
      | succ m ih =>
        have hm := (main m).2.2
        rw [show m + 1 + 1 = m + 2 by omega, hm, ih]
        rcases Nat.mod_two_eq_zero_or_one m with h | h
        · have h' : (m + 1) % 2 = 1 := by omega
          simp [h, h']
        · have h' : (m + 1) % 2 = 0 := by omega
          simp [h, h']
    cases h1 : c 1
    · left; funext k
      match k with
      | 0 => simp [rainA, h0]
      | n + 1 =>
        rw [alt n, h1]
        simp only [rainA]
        split <;> rename_i hn <;> simp <;> omega
    · right; funext k
      match k with
      | 0 => simp [rainB, h0]
      | n + 1 =>
        rw [alt n, h1]
        simp only [rainB]
        split <;> rename_i hn <;> simp <;> omega
  · rintro (rfl | rfl)
    · rw [T_rainA, T_rainB, T_rainA, T_rainB]
    · rw [T_rainB, T_rainA, T_rainB, T_rainA]

end Rule30Open.Frames.EdgePeriodFour
