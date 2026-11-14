module

public import Rule30Open.Frames.EdgePeriodFour

/-!
# The odd edge codes of period dividing 8 are the rain pair

On the definitions of `EdgePeriodFour` (`T`, the edge map of rule 30, that is the 2-adic map `Φ(y) = y ⊕ (2y ∨ 4y)`,
and the rain codes `rainA = -1/3`, `rainB = 1/3`):

* `period_eight_iff`: **an edge code with bit `0` black satisfies `T⁸ c = c` exactly when it is `rainA` or `rainB`.**

The proof is the one of `EdgePeriodFour.period_four_iff` with columns of length 8. Write `b_k(i) = Tⁱ c k`,
`i ∈ ℤ/8`. From bit `1` on, as long as columns `k` and `k + 1` alternate and are complementary, column `k + 2`
alternates (`alt_of_or`); the other choice makes columns `k + 1` and `k + 2` equal and alternating, the branch state
`(P, P)`, and `dead_core` shows that no four further columns close up around the cycle from it: a finite check, by
`decide`, of the 32 values of the phase and of the first bits of the four columns, the other bits being forced.
-/

@[expose] public section

namespace Rule30Open.Frames.EdgePeriodEight

open Rule30Open.Frames.EdgePeriodFour

/-- The branch state `(P, P)`, `P` alternating with phase `a`, has no walk of four edges in the column graph of
period 8: the columns `x, y, z, q` after it cannot all close up around the cycle. -/
theorem dead_core (a x0 x1 x2 x3 x4 x5 x6 x7 y0 y1 y2 y3 y4 y5 y6 y7 z0 z1 z2 z3 z4 z5 z6 z7 q0 q1 q2 q3 q4 q5 q6 q7 : Bool)
    (hx0 : x1 = xor x0 a)
    (hx1 : x2 = xor x1 (!a))
    (hx2 : x3 = xor x2 a)
    (hx3 : x4 = xor x3 (!a))
    (hx4 : x5 = xor x4 a)
    (hx5 : x6 = xor x5 (!a))
    (hx6 : x7 = xor x6 a)
    (hx7 : x0 = xor x7 (!a))
    (hy0 : y1 = xor y0 (x0 || a))
    (hy1 : y2 = xor y1 (x1 || (!a)))
    (hy2 : y3 = xor y2 (x2 || a))
    (hy3 : y4 = xor y3 (x3 || (!a)))
    (hy4 : y5 = xor y4 (x4 || a))
    (hy5 : y6 = xor y5 (x5 || (!a)))
    (hy6 : y7 = xor y6 (x6 || a))
    (hy7 : y0 = xor y7 (x7 || (!a)))
    (hz0 : z1 = xor z0 (y0 || x0))
    (hz1 : z2 = xor z1 (y1 || x1))
    (hz2 : z3 = xor z2 (y2 || x2))
    (hz3 : z4 = xor z3 (y3 || x3))
    (hz4 : z5 = xor z4 (y4 || x4))
    (hz5 : z6 = xor z5 (y5 || x5))
    (hz6 : z7 = xor z6 (y6 || x6))
    (hz7 : z0 = xor z7 (y7 || x7))
    (hq0 : q1 = xor q0 (z0 || y0))
    (hq1 : q2 = xor q1 (z1 || y1))
    (hq2 : q3 = xor q2 (z2 || y2))
    (hq3 : q4 = xor q3 (z3 || y3))
    (hq4 : q5 = xor q4 (z4 || y4))
    (hq5 : q6 = xor q5 (z5 || y5))
    (hq6 : q7 = xor q6 (z6 || y6))
    (hq7 : q0 = xor q7 (z7 || y7))
    : False := by
  subst hx0 hx1 hx2 hx3 hx4 hx5 hx6 hy0 hy1 hy2 hy3 hy4 hy5 hy6 hz0 hz1 hz2 hz3 hz4 hz5 hz6 hq0 hq1 hq2 hq3 hq4 hq5 hq6
  revert hx7 hy7 hz7 hq7
  cases a <;> cases x0 <;> cases y0 <;> cases z0 <;> cases q0 <;> decide

/-- **The odd edge codes of period dividing 8.** -/
theorem period_eight_iff (c : Nat → Bool) (h0 : c 0 = true) :
    T (T (T (T (T (T (T (T c))))))) = c ↔ (c = rainA ∨ c = rainB) := by
  constructor
  · intro h8
    let c1 := T c
    let c2 := T c1
    let c3 := T c2
    let c4 := T c3
    let c5 := T c4
    let c6 := T c5
    let c7 := T c6
    have r0 : ∀ k, c1 (k + 2) = xor (c (k + 2)) (c (k + 1) || c k) := fun k => rfl
    have r1 : ∀ k, c2 (k + 2) = xor (c1 (k + 2)) (c1 (k + 1) || c1 k) := fun k => rfl
    have r2 : ∀ k, c3 (k + 2) = xor (c2 (k + 2)) (c2 (k + 1) || c2 k) := fun k => rfl
    have r3 : ∀ k, c4 (k + 2) = xor (c3 (k + 2)) (c3 (k + 1) || c3 k) := fun k => rfl
    have r4 : ∀ k, c5 (k + 2) = xor (c4 (k + 2)) (c4 (k + 1) || c4 k) := fun k => rfl
    have r5 : ∀ k, c6 (k + 2) = xor (c5 (k + 2)) (c5 (k + 1) || c5 k) := fun k => rfl
    have r6 : ∀ k, c7 (k + 2) = xor (c6 (k + 2)) (c6 (k + 1) || c6 k) := fun k => rfl
    have r7 : ∀ k, c (k + 2) = xor (c7 (k + 2)) (c7 (k + 1) || c7 k) := fun k =>
      (congrFun h8 (k + 2)).symm
    let Alt : Nat → Prop := fun k => c1 k = !c k ∧ c2 k = c k ∧ c3 k = !c k ∧ c4 k = c k ∧ c5 k = !c k ∧ c6 k = c k ∧ c7 k = !c k
    have z1 : c1 0 = true := h0
    have z2 : c2 0 = true := z1
    have z3 : c3 0 = true := z2
    have z4 : c4 0 = true := z3
    have z5 : c5 0 = true := z4
    have z6 : c6 0 = true := z5
    have z7 : c7 0 = true := z6
    have alt1 : Alt 1 := by
      have e1 : c1 1 = xor (c 1) (c 0) := rfl
      have e2 : c2 1 = xor (c1 1) (c1 0) := rfl
      have e3 : c3 1 = xor (c2 1) (c2 0) := rfl
      have e4 : c4 1 = xor (c3 1) (c3 0) := rfl
      have e5 : c5 1 = xor (c4 1) (c4 0) := rfl
      have e6 : c6 1 = xor (c5 1) (c5 0) := rfl
      have e7 : c7 1 = xor (c6 1) (c6 0) := rfl
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [e1, h0]; cases c 1 <;> rfl
      · rw [e2, z1, e1, h0]; cases c 1 <;> rfl
      · rw [e3, z2, e2, z1, e1, h0]; cases c 1 <;> rfl
      · rw [e4, z3, e3, z2, e2, z1, e1, h0]; cases c 1 <;> rfl
      · rw [e5, z4, e4, z3, e3, z2, e2, z1, e1, h0]; cases c 1 <;> rfl
      · rw [e6, z5, e5, z4, e4, z3, e3, z2, e2, z1, e1, h0]; cases c 1 <;> rfl
      · rw [e7, z6, e6, z5, e5, z4, e4, z3, e3, z2, e2, z1, e1, h0]; cases c 1 <;> rfl
    have alt_of_or : ∀ k, (c (k + 1) || c k) = true → (c1 (k + 1) || c1 k) = true → (c2 (k + 1) || c2 k) = true → (c3 (k + 1) || c3 k) = true → (c4 (k + 1) || c4 k) = true → (c5 (k + 1) || c5 k) = true → (c6 (k + 1) || c6 k) = true → Alt (k + 2) := by
      intro k o0 o1 o2 o3 o4 o5 o6
      have e0 := r0 k
      have e1 := r1 k
      have e2 := r2 k
      have e3 := r3 k
      have e4 := r4 k
      have e5 := r5 k
      have e6 := r6 k
      rw [o0] at e0; rw [o1] at e1; rw [o2] at e2; rw [o3] at e3; rw [o4] at e4; rw [o5] at e5; rw [o6] at e6
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [e0]; cases c (k + 2) <;> rfl
      · rw [e1, e0]; cases c (k + 2) <;> rfl
      · rw [e2, e1, e0]; cases c (k + 2) <;> rfl
      · rw [e3, e2, e1, e0]; cases c (k + 2) <;> rfl
      · rw [e4, e3, e2, e1, e0]; cases c (k + 2) <;> rfl
      · rw [e5, e4, e3, e2, e1, e0]; cases c (k + 2) <;> rfl
      · rw [e6, e5, e4, e3, e2, e1, e0]; cases c (k + 2) <;> rfl
    have not_equal_alt : ∀ k, Alt k → Alt (k + 1) → c (k + 1) = c k → False := by
      intro k ak ak1 heq
      obtain ⟨p1, p2, p3, p4, p5, p6, p7⟩ := ak
      obtain ⟨p'1, p'2, p'3, p'4, p'5, p'6, p'7⟩ := ak1
      have s0_0 : c1 (k + 2) = xor (c (k + 2)) (c (k + 1) || c k) := r0 k
      have s0_1 : c2 (k + 2) = xor (c1 (k + 2)) (c1 (k + 1) || c1 k) := r1 k
      have s0_2 : c3 (k + 2) = xor (c2 (k + 2)) (c2 (k + 1) || c2 k) := r2 k
      have s0_3 : c4 (k + 2) = xor (c3 (k + 2)) (c3 (k + 1) || c3 k) := r3 k
      have s0_4 : c5 (k + 2) = xor (c4 (k + 2)) (c4 (k + 1) || c4 k) := r4 k
      have s0_5 : c6 (k + 2) = xor (c5 (k + 2)) (c5 (k + 1) || c5 k) := r5 k
      have s0_6 : c7 (k + 2) = xor (c6 (k + 2)) (c6 (k + 1) || c6 k) := r6 k
      have s0_7 : c (k + 2) = xor (c7 (k + 2)) (c7 (k + 1) || c7 k) := r7 k
      have s1_0 : c1 (k + 3) = xor (c (k + 3)) (c (k + 2) || c (k + 1)) := r0 (k + 1)
      have s1_1 : c2 (k + 3) = xor (c1 (k + 3)) (c1 (k + 2) || c1 (k + 1)) := r1 (k + 1)
      have s1_2 : c3 (k + 3) = xor (c2 (k + 3)) (c2 (k + 2) || c2 (k + 1)) := r2 (k + 1)
      have s1_3 : c4 (k + 3) = xor (c3 (k + 3)) (c3 (k + 2) || c3 (k + 1)) := r3 (k + 1)
      have s1_4 : c5 (k + 3) = xor (c4 (k + 3)) (c4 (k + 2) || c4 (k + 1)) := r4 (k + 1)
      have s1_5 : c6 (k + 3) = xor (c5 (k + 3)) (c5 (k + 2) || c5 (k + 1)) := r5 (k + 1)
      have s1_6 : c7 (k + 3) = xor (c6 (k + 3)) (c6 (k + 2) || c6 (k + 1)) := r6 (k + 1)
      have s1_7 : c (k + 3) = xor (c7 (k + 3)) (c7 (k + 2) || c7 (k + 1)) := r7 (k + 1)
      have s2_0 : c1 (k + 4) = xor (c (k + 4)) (c (k + 3) || c (k + 2)) := r0 (k + 2)
      have s2_1 : c2 (k + 4) = xor (c1 (k + 4)) (c1 (k + 3) || c1 (k + 2)) := r1 (k + 2)
      have s2_2 : c3 (k + 4) = xor (c2 (k + 4)) (c2 (k + 3) || c2 (k + 2)) := r2 (k + 2)
      have s2_3 : c4 (k + 4) = xor (c3 (k + 4)) (c3 (k + 3) || c3 (k + 2)) := r3 (k + 2)
      have s2_4 : c5 (k + 4) = xor (c4 (k + 4)) (c4 (k + 3) || c4 (k + 2)) := r4 (k + 2)
      have s2_5 : c6 (k + 4) = xor (c5 (k + 4)) (c5 (k + 3) || c5 (k + 2)) := r5 (k + 2)
      have s2_6 : c7 (k + 4) = xor (c6 (k + 4)) (c6 (k + 3) || c6 (k + 2)) := r6 (k + 2)
      have s2_7 : c (k + 4) = xor (c7 (k + 4)) (c7 (k + 3) || c7 (k + 2)) := r7 (k + 2)
      have s3_0 : c1 (k + 5) = xor (c (k + 5)) (c (k + 4) || c (k + 3)) := r0 (k + 3)
      have s3_1 : c2 (k + 5) = xor (c1 (k + 5)) (c1 (k + 4) || c1 (k + 3)) := r1 (k + 3)
      have s3_2 : c3 (k + 5) = xor (c2 (k + 5)) (c2 (k + 4) || c2 (k + 3)) := r2 (k + 3)
      have s3_3 : c4 (k + 5) = xor (c3 (k + 5)) (c3 (k + 4) || c3 (k + 3)) := r3 (k + 3)
      have s3_4 : c5 (k + 5) = xor (c4 (k + 5)) (c4 (k + 4) || c4 (k + 3)) := r4 (k + 3)
      have s3_5 : c6 (k + 5) = xor (c5 (k + 5)) (c5 (k + 4) || c5 (k + 3)) := r5 (k + 3)
      have s3_6 : c7 (k + 5) = xor (c6 (k + 5)) (c6 (k + 4) || c6 (k + 3)) := r6 (k + 3)
      have s3_7 : c (k + 5) = xor (c7 (k + 5)) (c7 (k + 4) || c7 (k + 3)) := r7 (k + 3)
      simp only [p1, p2, p3, p4, p5, p6, p7, p'1, p'2, p'3, p'4, p'5, p'6, p'7, heq, Bool.or_self] at s0_0 s0_1 s0_2 s0_3 s0_4 s0_5 s0_6 s0_7 s1_0 s1_1 s1_2 s1_3 s1_4 s1_5 s1_6 s1_7 s2_0 s2_1 s2_2 s2_3 s2_4 s2_5 s2_6 s2_7 s3_0 s3_1 s3_2 s3_3 s3_4 s3_5 s3_6 s3_7
      exact dead_core (c k) (c (k + 2)) (c1 (k + 2)) (c2 (k + 2)) (c3 (k + 2)) (c4 (k + 2)) (c5 (k + 2)) (c6 (k + 2)) (c7 (k + 2)) (c (k + 3)) (c1 (k + 3)) (c2 (k + 3)) (c3 (k + 3)) (c4 (k + 3)) (c5 (k + 3)) (c6 (k + 3)) (c7 (k + 3)) (c (k + 4)) (c1 (k + 4)) (c2 (k + 4)) (c3 (k + 4)) (c4 (k + 4)) (c5 (k + 4)) (c6 (k + 4)) (c7 (k + 4)) (c (k + 5)) (c1 (k + 5)) (c2 (k + 5)) (c3 (k + 5)) (c4 (k + 5)) (c5 (k + 5)) (c6 (k + 5)) (c7 (k + 5))
        s0_0 s0_1 s0_2 s0_3 s0_4 s0_5 s0_6 s0_7 s1_0 s1_1 s1_2 s1_3 s1_4 s1_5 s1_6 s1_7 s2_0 s2_1 s2_2 s2_3 s2_4 s2_5 s2_6 s2_7 s3_0 s3_1 s3_2 s3_3 s3_4 s3_5 s3_6 s3_7
    have or_of_ne : ∀ k, Alt k → c (k + 1) = !c k → Alt (k + 1) →
        (c (k + 1) || c k) = true ∧ (c1 (k + 1) || c1 k) = true ∧ (c2 (k + 1) || c2 k) = true ∧ (c3 (k + 1) || c3 k) = true ∧ (c4 (k + 1) || c4 k) = true ∧ (c5 (k + 1) || c5 k) = true ∧ (c6 (k + 1) || c6 k) = true := by
      intro k ak hne ak1
      obtain ⟨p1, p2, p3, p4, p5, p6, p7⟩ := ak
      obtain ⟨p'1, p'2, p'3, p'4, p'5, p'6, p'7⟩ := ak1
      rw [p'1, p1, p'2, p2, p'3, p3, p'4, p4, p'5, p5, p'6, p6, hne]
      cases c k <;> decide
    have main : ∀ n, Alt (n + 1) ∧ Alt (n + 2) ∧ c (n + 2) = !c (n + 1) := by
      intro n
      induction n with
      | zero =>
        have a2 : Alt 2 := by
          have hh : (c 1 || c 0) = true := by rw [h0, Bool.or_true]
          exact alt_of_or 0 hh (by rw [z1, Bool.or_true]) (by rw [z2, Bool.or_true]) (by rw [z3, Bool.or_true]) (by rw [z4, Bool.or_true]) (by rw [z5, Bool.or_true]) (by rw [z6, Bool.or_true])
        refine ⟨alt1, a2, ?_⟩
        cases hc : c 2 <;> cases hc1 : c 1
        · exact absurd (hc.trans hc1.symm) (fun h => not_equal_alt 1 alt1 a2 h)
        · rfl
        · rfl
        · exact absurd (hc.trans hc1.symm) (fun h => not_equal_alt 1 alt1 a2 h)
      | succ m ih =>
        obtain ⟨am, am1, hne⟩ := ih
        obtain ⟨o0, o1, o2, o3, o4, o5, o6⟩ := or_of_ne (m + 1) am hne am1
        have a3 : Alt (m + 3) := alt_of_or (m + 1) o0 o1 o2 o3 o4 o5 o6
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
  · intro h
    have h4 : T (T (T (T c))) = c := by
      rcases h with rfl | rfl
      · rw [T_rainA, T_rainB, T_rainA, T_rainB]
      · rw [T_rainB, T_rainA, T_rainB, T_rainA]
    rw [h4, h4]

end Rule30Open.Frames.EdgePeriodEight
