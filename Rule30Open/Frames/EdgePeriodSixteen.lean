module

public import Rule30Open.Frames.EdgePeriodFour

/-!
# The odd edge codes of period dividing 16 are the rain pair

On the definitions of `EdgePeriodFour` (`T`, the edge map of rule 30, that is the 2-adic map `Φ(y) = y ⊕ (2y ∨ 4y)`,
and the rain codes `rainA = -1/3`, `rainB = 1/3`):

* `period_sixteen_iff`: **an edge code with bit `0` black satisfies `T¹⁶ c = c` exactly when it is `rainA` or `rainB`.**

The proof is the one of `EdgePeriodFour.period_four_iff` with columns of length 16. Write `b_k(i) = Tⁱ c k`,
`i ∈ ℤ/16`. From bit `1` on, as long as columns `k` and `k + 1` alternate and are complementary, column `k + 2`
alternates (`alt_of_or`); the other choice makes columns `k + 1` and `k + 2` equal and alternating, the branch state
`(P, P)`, and `dead_core` shows that no five further columns close up around the cycle from it: a finite check, by
`decide`, of the 64 values of the phase and of the first bits of the five columns, the other bits being forced.
-/

@[expose] public section

namespace Rule30Open.Frames.EdgePeriodSixteen

open Rule30Open.Frames.EdgePeriodFour

/-- The branch state `(P, P)`, `P` alternating with phase `a`, has no walk of five edges in the column graph of
period 16: the columns `x, y, z, q, r` after it cannot all close up around the cycle. -/
theorem dead_core (a x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : Bool)
    (hx0 : x1 = xor x0 a)
    (hx1 : x2 = xor x1 (!a))
    (hx2 : x3 = xor x2 a)
    (hx3 : x4 = xor x3 (!a))
    (hx4 : x5 = xor x4 a)
    (hx5 : x6 = xor x5 (!a))
    (hx6 : x7 = xor x6 a)
    (hx7 : x8 = xor x7 (!a))
    (hx8 : x9 = xor x8 a)
    (hx9 : x10 = xor x9 (!a))
    (hx10 : x11 = xor x10 a)
    (hx11 : x12 = xor x11 (!a))
    (hx12 : x13 = xor x12 a)
    (hx13 : x14 = xor x13 (!a))
    (hx14 : x15 = xor x14 a)
    (hx15 : x0 = xor x15 (!a))
    (hy0 : y1 = xor y0 (x0 || a))
    (hy1 : y2 = xor y1 (x1 || (!a)))
    (hy2 : y3 = xor y2 (x2 || a))
    (hy3 : y4 = xor y3 (x3 || (!a)))
    (hy4 : y5 = xor y4 (x4 || a))
    (hy5 : y6 = xor y5 (x5 || (!a)))
    (hy6 : y7 = xor y6 (x6 || a))
    (hy7 : y8 = xor y7 (x7 || (!a)))
    (hy8 : y9 = xor y8 (x8 || a))
    (hy9 : y10 = xor y9 (x9 || (!a)))
    (hy10 : y11 = xor y10 (x10 || a))
    (hy11 : y12 = xor y11 (x11 || (!a)))
    (hy12 : y13 = xor y12 (x12 || a))
    (hy13 : y14 = xor y13 (x13 || (!a)))
    (hy14 : y15 = xor y14 (x14 || a))
    (hy15 : y0 = xor y15 (x15 || (!a)))
    (hz0 : z1 = xor z0 (y0 || x0))
    (hz1 : z2 = xor z1 (y1 || x1))
    (hz2 : z3 = xor z2 (y2 || x2))
    (hz3 : z4 = xor z3 (y3 || x3))
    (hz4 : z5 = xor z4 (y4 || x4))
    (hz5 : z6 = xor z5 (y5 || x5))
    (hz6 : z7 = xor z6 (y6 || x6))
    (hz7 : z8 = xor z7 (y7 || x7))
    (hz8 : z9 = xor z8 (y8 || x8))
    (hz9 : z10 = xor z9 (y9 || x9))
    (hz10 : z11 = xor z10 (y10 || x10))
    (hz11 : z12 = xor z11 (y11 || x11))
    (hz12 : z13 = xor z12 (y12 || x12))
    (hz13 : z14 = xor z13 (y13 || x13))
    (hz14 : z15 = xor z14 (y14 || x14))
    (hz15 : z0 = xor z15 (y15 || x15))
    (hq0 : q1 = xor q0 (z0 || y0))
    (hq1 : q2 = xor q1 (z1 || y1))
    (hq2 : q3 = xor q2 (z2 || y2))
    (hq3 : q4 = xor q3 (z3 || y3))
    (hq4 : q5 = xor q4 (z4 || y4))
    (hq5 : q6 = xor q5 (z5 || y5))
    (hq6 : q7 = xor q6 (z6 || y6))
    (hq7 : q8 = xor q7 (z7 || y7))
    (hq8 : q9 = xor q8 (z8 || y8))
    (hq9 : q10 = xor q9 (z9 || y9))
    (hq10 : q11 = xor q10 (z10 || y10))
    (hq11 : q12 = xor q11 (z11 || y11))
    (hq12 : q13 = xor q12 (z12 || y12))
    (hq13 : q14 = xor q13 (z13 || y13))
    (hq14 : q15 = xor q14 (z14 || y14))
    (hq15 : q0 = xor q15 (z15 || y15))
    (hr0 : r1 = xor r0 (q0 || z0))
    (hr1 : r2 = xor r1 (q1 || z1))
    (hr2 : r3 = xor r2 (q2 || z2))
    (hr3 : r4 = xor r3 (q3 || z3))
    (hr4 : r5 = xor r4 (q4 || z4))
    (hr5 : r6 = xor r5 (q5 || z5))
    (hr6 : r7 = xor r6 (q6 || z6))
    (hr7 : r8 = xor r7 (q7 || z7))
    (hr8 : r9 = xor r8 (q8 || z8))
    (hr9 : r10 = xor r9 (q9 || z9))
    (hr10 : r11 = xor r10 (q10 || z10))
    (hr11 : r12 = xor r11 (q11 || z11))
    (hr12 : r13 = xor r12 (q12 || z12))
    (hr13 : r14 = xor r13 (q13 || z13))
    (hr14 : r15 = xor r14 (q14 || z14))
    (hr15 : r0 = xor r15 (q15 || z15))
    : False := by
  subst hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hy0 hy1 hy2 hy3 hy4 hy5 hy6 hy7 hy8 hy9 hy10 hy11 hy12 hy13 hy14 hz0 hz1 hz2 hz3 hz4 hz5 hz6 hz7 hz8 hz9 hz10 hz11 hz12 hz13 hz14 hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hq10 hq11 hq12 hq13 hq14 hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr7 hr8 hr9 hr10 hr11 hr12 hr13 hr14
  revert hx15 hy15 hz15 hq15 hr15
  cases a <;> cases x0 <;> cases y0 <;> cases z0 <;> cases q0 <;> cases r0 <;> decide

/-- **The odd edge codes of period dividing 16.** -/
theorem period_sixteen_iff (c : Nat → Bool) (h0 : c 0 = true) :
    T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T c))))))))))))))) = c ↔ (c = rainA ∨ c = rainB) := by
  constructor
  · intro h8
    let c1 := T c
    let c2 := T c1
    let c3 := T c2
    let c4 := T c3
    let c5 := T c4
    let c6 := T c5
    let c7 := T c6
    let c8 := T c7
    let c9 := T c8
    let c10 := T c9
    let c11 := T c10
    let c12 := T c11
    let c13 := T c12
    let c14 := T c13
    let c15 := T c14
    have r0 : ∀ k, c1 (k + 2) = xor (c (k + 2)) (c (k + 1) || c k) := fun k => rfl
    have r1 : ∀ k, c2 (k + 2) = xor (c1 (k + 2)) (c1 (k + 1) || c1 k) := fun k => rfl
    have r2 : ∀ k, c3 (k + 2) = xor (c2 (k + 2)) (c2 (k + 1) || c2 k) := fun k => rfl
    have r3 : ∀ k, c4 (k + 2) = xor (c3 (k + 2)) (c3 (k + 1) || c3 k) := fun k => rfl
    have r4 : ∀ k, c5 (k + 2) = xor (c4 (k + 2)) (c4 (k + 1) || c4 k) := fun k => rfl
    have r5 : ∀ k, c6 (k + 2) = xor (c5 (k + 2)) (c5 (k + 1) || c5 k) := fun k => rfl
    have r6 : ∀ k, c7 (k + 2) = xor (c6 (k + 2)) (c6 (k + 1) || c6 k) := fun k => rfl
    have r7 : ∀ k, c8 (k + 2) = xor (c7 (k + 2)) (c7 (k + 1) || c7 k) := fun k => rfl
    have r8 : ∀ k, c9 (k + 2) = xor (c8 (k + 2)) (c8 (k + 1) || c8 k) := fun k => rfl
    have r9 : ∀ k, c10 (k + 2) = xor (c9 (k + 2)) (c9 (k + 1) || c9 k) := fun k => rfl
    have r10 : ∀ k, c11 (k + 2) = xor (c10 (k + 2)) (c10 (k + 1) || c10 k) := fun k => rfl
    have r11 : ∀ k, c12 (k + 2) = xor (c11 (k + 2)) (c11 (k + 1) || c11 k) := fun k => rfl
    have r12 : ∀ k, c13 (k + 2) = xor (c12 (k + 2)) (c12 (k + 1) || c12 k) := fun k => rfl
    have r13 : ∀ k, c14 (k + 2) = xor (c13 (k + 2)) (c13 (k + 1) || c13 k) := fun k => rfl
    have r14 : ∀ k, c15 (k + 2) = xor (c14 (k + 2)) (c14 (k + 1) || c14 k) := fun k => rfl
    have r15 : ∀ k, c (k + 2) = xor (c15 (k + 2)) (c15 (k + 1) || c15 k) := fun k =>
      (congrFun h8 (k + 2)).symm
    let Alt : Nat → Prop := fun k => c1 k = !c k ∧ c2 k = c k ∧ c3 k = !c k ∧ c4 k = c k ∧ c5 k = !c k ∧ c6 k = c k ∧ c7 k = !c k ∧ c8 k = c k ∧ c9 k = !c k ∧ c10 k = c k ∧ c11 k = !c k ∧ c12 k = c k ∧ c13 k = !c k ∧ c14 k = c k ∧ c15 k = !c k
    have z1 : c1 0 = true := h0
    have z2 : c2 0 = true := z1
    have z3 : c3 0 = true := z2
    have z4 : c4 0 = true := z3
    have z5 : c5 0 = true := z4
    have z6 : c6 0 = true := z5
    have z7 : c7 0 = true := z6
    have z8 : c8 0 = true := z7
    have z9 : c9 0 = true := z8
    have z10 : c10 0 = true := z9
    have z11 : c11 0 = true := z10
    have z12 : c12 0 = true := z11
    have z13 : c13 0 = true := z12
    have z14 : c14 0 = true := z13
    have z15 : c15 0 = true := z14
    have alt1 : Alt 1 := by
      have e1 : c1 1 = xor (c 1) (c 0) := rfl
      have e2 : c2 1 = xor (c1 1) (c1 0) := rfl
      have e3 : c3 1 = xor (c2 1) (c2 0) := rfl
      have e4 : c4 1 = xor (c3 1) (c3 0) := rfl
      have e5 : c5 1 = xor (c4 1) (c4 0) := rfl
      have e6 : c6 1 = xor (c5 1) (c5 0) := rfl
      have e7 : c7 1 = xor (c6 1) (c6 0) := rfl
      have e8 : c8 1 = xor (c7 1) (c7 0) := rfl
      have e9 : c9 1 = xor (c8 1) (c8 0) := rfl
      have e10 : c10 1 = xor (c9 1) (c9 0) := rfl
      have e11 : c11 1 = xor (c10 1) (c10 0) := rfl
      have e12 : c12 1 = xor (c11 1) (c11 0) := rfl
      have e13 : c13 1 = xor (c12 1) (c12 0) := rfl
      have e14 : c14 1 = xor (c13 1) (c13 0) := rfl
      have e15 : c15 1 = xor (c14 1) (c14 0) := rfl
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [e1, h0]; cases c 1 <;> rfl
      · rw [e2, z1, e1, h0]; cases c 1 <;> rfl
      · rw [e3, z2, e2, z1, e1, h0]; cases c 1 <;> rfl
      · rw [e4, z3, e3, z2, e2, z1, e1, h0]; cases c 1 <;> rfl
      · rw [e5, z4, e4, z3, e3, z2, e2, z1, e1, h0]; cases c 1 <;> rfl
      · rw [e6, z5, e5, z4, e4, z3, e3, z2, e2, z1, e1, h0]; cases c 1 <;> rfl
      · rw [e7, z6, e6, z5, e5, z4, e4, z3, e3, z2, e2, z1, e1, h0]; cases c 1 <;> rfl
      · rw [e8, z7, e7, z6, e6, z5, e5, z4, e4, z3, e3, z2, e2, z1, e1, h0]; cases c 1 <;> rfl
      · rw [e9, z8, e8, z7, e7, z6, e6, z5, e5, z4, e4, z3, e3, z2, e2, z1, e1, h0]; cases c 1 <;> rfl
      · rw [e10, z9, e9, z8, e8, z7, e7, z6, e6, z5, e5, z4, e4, z3, e3, z2, e2, z1, e1, h0]; cases c 1 <;> rfl
      · rw [e11, z10, e10, z9, e9, z8, e8, z7, e7, z6, e6, z5, e5, z4, e4, z3, e3, z2, e2, z1, e1, h0]; cases c 1 <;> rfl
      · rw [e12, z11, e11, z10, e10, z9, e9, z8, e8, z7, e7, z6, e6, z5, e5, z4, e4, z3, e3, z2, e2, z1, e1, h0]; cases c 1 <;> rfl
      · rw [e13, z12, e12, z11, e11, z10, e10, z9, e9, z8, e8, z7, e7, z6, e6, z5, e5, z4, e4, z3, e3, z2, e2, z1, e1, h0]; cases c 1 <;> rfl
      · rw [e14, z13, e13, z12, e12, z11, e11, z10, e10, z9, e9, z8, e8, z7, e7, z6, e6, z5, e5, z4, e4, z3, e3, z2, e2, z1, e1, h0]; cases c 1 <;> rfl
      · rw [e15, z14, e14, z13, e13, z12, e12, z11, e11, z10, e10, z9, e9, z8, e8, z7, e7, z6, e6, z5, e5, z4, e4, z3, e3, z2, e2, z1, e1, h0]; cases c 1 <;> rfl
    have alt_of_or : ∀ k, (c (k + 1) || c k) = true → (c1 (k + 1) || c1 k) = true → (c2 (k + 1) || c2 k) = true → (c3 (k + 1) || c3 k) = true → (c4 (k + 1) || c4 k) = true → (c5 (k + 1) || c5 k) = true → (c6 (k + 1) || c6 k) = true → (c7 (k + 1) || c7 k) = true → (c8 (k + 1) || c8 k) = true → (c9 (k + 1) || c9 k) = true → (c10 (k + 1) || c10 k) = true → (c11 (k + 1) || c11 k) = true → (c12 (k + 1) || c12 k) = true → (c13 (k + 1) || c13 k) = true → (c14 (k + 1) || c14 k) = true → Alt (k + 2) := by
      intro k o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 o11 o12 o13 o14
      have e0 := r0 k
      have e1 := r1 k
      have e2 := r2 k
      have e3 := r3 k
      have e4 := r4 k
      have e5 := r5 k
      have e6 := r6 k
      have e7 := r7 k
      have e8 := r8 k
      have e9 := r9 k
      have e10 := r10 k
      have e11 := r11 k
      have e12 := r12 k
      have e13 := r13 k
      have e14 := r14 k
      rw [o0] at e0; rw [o1] at e1; rw [o2] at e2; rw [o3] at e3; rw [o4] at e4; rw [o5] at e5; rw [o6] at e6; rw [o7] at e7; rw [o8] at e8; rw [o9] at e9; rw [o10] at e10; rw [o11] at e11; rw [o12] at e12; rw [o13] at e13; rw [o14] at e14
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [e0]; cases c (k + 2) <;> rfl
      · rw [e1, e0]; cases c (k + 2) <;> rfl
      · rw [e2, e1, e0]; cases c (k + 2) <;> rfl
      · rw [e3, e2, e1, e0]; cases c (k + 2) <;> rfl
      · rw [e4, e3, e2, e1, e0]; cases c (k + 2) <;> rfl
      · rw [e5, e4, e3, e2, e1, e0]; cases c (k + 2) <;> rfl
      · rw [e6, e5, e4, e3, e2, e1, e0]; cases c (k + 2) <;> rfl
      · rw [e7, e6, e5, e4, e3, e2, e1, e0]; cases c (k + 2) <;> rfl
      · rw [e8, e7, e6, e5, e4, e3, e2, e1, e0]; cases c (k + 2) <;> rfl
      · rw [e9, e8, e7, e6, e5, e4, e3, e2, e1, e0]; cases c (k + 2) <;> rfl
      · rw [e10, e9, e8, e7, e6, e5, e4, e3, e2, e1, e0]; cases c (k + 2) <;> rfl
      · rw [e11, e10, e9, e8, e7, e6, e5, e4, e3, e2, e1, e0]; cases c (k + 2) <;> rfl
      · rw [e12, e11, e10, e9, e8, e7, e6, e5, e4, e3, e2, e1, e0]; cases c (k + 2) <;> rfl
      · rw [e13, e12, e11, e10, e9, e8, e7, e6, e5, e4, e3, e2, e1, e0]; cases c (k + 2) <;> rfl
      · rw [e14, e13, e12, e11, e10, e9, e8, e7, e6, e5, e4, e3, e2, e1, e0]; cases c (k + 2) <;> rfl
    have not_equal_alt : ∀ k, Alt k → Alt (k + 1) → c (k + 1) = c k → False := by
      intro k ak ak1 heq
      obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15⟩ := ak
      obtain ⟨p'1, p'2, p'3, p'4, p'5, p'6, p'7, p'8, p'9, p'10, p'11, p'12, p'13, p'14, p'15⟩ := ak1
      have s0_0 : c1 (k + 2) = xor (c (k + 2)) (c (k + 1) || c k) := r0 k
      have s0_1 : c2 (k + 2) = xor (c1 (k + 2)) (c1 (k + 1) || c1 k) := r1 k
      have s0_2 : c3 (k + 2) = xor (c2 (k + 2)) (c2 (k + 1) || c2 k) := r2 k
      have s0_3 : c4 (k + 2) = xor (c3 (k + 2)) (c3 (k + 1) || c3 k) := r3 k
      have s0_4 : c5 (k + 2) = xor (c4 (k + 2)) (c4 (k + 1) || c4 k) := r4 k
      have s0_5 : c6 (k + 2) = xor (c5 (k + 2)) (c5 (k + 1) || c5 k) := r5 k
      have s0_6 : c7 (k + 2) = xor (c6 (k + 2)) (c6 (k + 1) || c6 k) := r6 k
      have s0_7 : c8 (k + 2) = xor (c7 (k + 2)) (c7 (k + 1) || c7 k) := r7 k
      have s0_8 : c9 (k + 2) = xor (c8 (k + 2)) (c8 (k + 1) || c8 k) := r8 k
      have s0_9 : c10 (k + 2) = xor (c9 (k + 2)) (c9 (k + 1) || c9 k) := r9 k
      have s0_10 : c11 (k + 2) = xor (c10 (k + 2)) (c10 (k + 1) || c10 k) := r10 k
      have s0_11 : c12 (k + 2) = xor (c11 (k + 2)) (c11 (k + 1) || c11 k) := r11 k
      have s0_12 : c13 (k + 2) = xor (c12 (k + 2)) (c12 (k + 1) || c12 k) := r12 k
      have s0_13 : c14 (k + 2) = xor (c13 (k + 2)) (c13 (k + 1) || c13 k) := r13 k
      have s0_14 : c15 (k + 2) = xor (c14 (k + 2)) (c14 (k + 1) || c14 k) := r14 k
      have s0_15 : c (k + 2) = xor (c15 (k + 2)) (c15 (k + 1) || c15 k) := r15 k
      have s1_0 : c1 (k + 3) = xor (c (k + 3)) (c (k + 2) || c (k + 1)) := r0 (k + 1)
      have s1_1 : c2 (k + 3) = xor (c1 (k + 3)) (c1 (k + 2) || c1 (k + 1)) := r1 (k + 1)
      have s1_2 : c3 (k + 3) = xor (c2 (k + 3)) (c2 (k + 2) || c2 (k + 1)) := r2 (k + 1)
      have s1_3 : c4 (k + 3) = xor (c3 (k + 3)) (c3 (k + 2) || c3 (k + 1)) := r3 (k + 1)
      have s1_4 : c5 (k + 3) = xor (c4 (k + 3)) (c4 (k + 2) || c4 (k + 1)) := r4 (k + 1)
      have s1_5 : c6 (k + 3) = xor (c5 (k + 3)) (c5 (k + 2) || c5 (k + 1)) := r5 (k + 1)
      have s1_6 : c7 (k + 3) = xor (c6 (k + 3)) (c6 (k + 2) || c6 (k + 1)) := r6 (k + 1)
      have s1_7 : c8 (k + 3) = xor (c7 (k + 3)) (c7 (k + 2) || c7 (k + 1)) := r7 (k + 1)
      have s1_8 : c9 (k + 3) = xor (c8 (k + 3)) (c8 (k + 2) || c8 (k + 1)) := r8 (k + 1)
      have s1_9 : c10 (k + 3) = xor (c9 (k + 3)) (c9 (k + 2) || c9 (k + 1)) := r9 (k + 1)
      have s1_10 : c11 (k + 3) = xor (c10 (k + 3)) (c10 (k + 2) || c10 (k + 1)) := r10 (k + 1)
      have s1_11 : c12 (k + 3) = xor (c11 (k + 3)) (c11 (k + 2) || c11 (k + 1)) := r11 (k + 1)
      have s1_12 : c13 (k + 3) = xor (c12 (k + 3)) (c12 (k + 2) || c12 (k + 1)) := r12 (k + 1)
      have s1_13 : c14 (k + 3) = xor (c13 (k + 3)) (c13 (k + 2) || c13 (k + 1)) := r13 (k + 1)
      have s1_14 : c15 (k + 3) = xor (c14 (k + 3)) (c14 (k + 2) || c14 (k + 1)) := r14 (k + 1)
      have s1_15 : c (k + 3) = xor (c15 (k + 3)) (c15 (k + 2) || c15 (k + 1)) := r15 (k + 1)
      have s2_0 : c1 (k + 4) = xor (c (k + 4)) (c (k + 3) || c (k + 2)) := r0 (k + 2)
      have s2_1 : c2 (k + 4) = xor (c1 (k + 4)) (c1 (k + 3) || c1 (k + 2)) := r1 (k + 2)
      have s2_2 : c3 (k + 4) = xor (c2 (k + 4)) (c2 (k + 3) || c2 (k + 2)) := r2 (k + 2)
      have s2_3 : c4 (k + 4) = xor (c3 (k + 4)) (c3 (k + 3) || c3 (k + 2)) := r3 (k + 2)
      have s2_4 : c5 (k + 4) = xor (c4 (k + 4)) (c4 (k + 3) || c4 (k + 2)) := r4 (k + 2)
      have s2_5 : c6 (k + 4) = xor (c5 (k + 4)) (c5 (k + 3) || c5 (k + 2)) := r5 (k + 2)
      have s2_6 : c7 (k + 4) = xor (c6 (k + 4)) (c6 (k + 3) || c6 (k + 2)) := r6 (k + 2)
      have s2_7 : c8 (k + 4) = xor (c7 (k + 4)) (c7 (k + 3) || c7 (k + 2)) := r7 (k + 2)
      have s2_8 : c9 (k + 4) = xor (c8 (k + 4)) (c8 (k + 3) || c8 (k + 2)) := r8 (k + 2)
      have s2_9 : c10 (k + 4) = xor (c9 (k + 4)) (c9 (k + 3) || c9 (k + 2)) := r9 (k + 2)
      have s2_10 : c11 (k + 4) = xor (c10 (k + 4)) (c10 (k + 3) || c10 (k + 2)) := r10 (k + 2)
      have s2_11 : c12 (k + 4) = xor (c11 (k + 4)) (c11 (k + 3) || c11 (k + 2)) := r11 (k + 2)
      have s2_12 : c13 (k + 4) = xor (c12 (k + 4)) (c12 (k + 3) || c12 (k + 2)) := r12 (k + 2)
      have s2_13 : c14 (k + 4) = xor (c13 (k + 4)) (c13 (k + 3) || c13 (k + 2)) := r13 (k + 2)
      have s2_14 : c15 (k + 4) = xor (c14 (k + 4)) (c14 (k + 3) || c14 (k + 2)) := r14 (k + 2)
      have s2_15 : c (k + 4) = xor (c15 (k + 4)) (c15 (k + 3) || c15 (k + 2)) := r15 (k + 2)
      have s3_0 : c1 (k + 5) = xor (c (k + 5)) (c (k + 4) || c (k + 3)) := r0 (k + 3)
      have s3_1 : c2 (k + 5) = xor (c1 (k + 5)) (c1 (k + 4) || c1 (k + 3)) := r1 (k + 3)
      have s3_2 : c3 (k + 5) = xor (c2 (k + 5)) (c2 (k + 4) || c2 (k + 3)) := r2 (k + 3)
      have s3_3 : c4 (k + 5) = xor (c3 (k + 5)) (c3 (k + 4) || c3 (k + 3)) := r3 (k + 3)
      have s3_4 : c5 (k + 5) = xor (c4 (k + 5)) (c4 (k + 4) || c4 (k + 3)) := r4 (k + 3)
      have s3_5 : c6 (k + 5) = xor (c5 (k + 5)) (c5 (k + 4) || c5 (k + 3)) := r5 (k + 3)
      have s3_6 : c7 (k + 5) = xor (c6 (k + 5)) (c6 (k + 4) || c6 (k + 3)) := r6 (k + 3)
      have s3_7 : c8 (k + 5) = xor (c7 (k + 5)) (c7 (k + 4) || c7 (k + 3)) := r7 (k + 3)
      have s3_8 : c9 (k + 5) = xor (c8 (k + 5)) (c8 (k + 4) || c8 (k + 3)) := r8 (k + 3)
      have s3_9 : c10 (k + 5) = xor (c9 (k + 5)) (c9 (k + 4) || c9 (k + 3)) := r9 (k + 3)
      have s3_10 : c11 (k + 5) = xor (c10 (k + 5)) (c10 (k + 4) || c10 (k + 3)) := r10 (k + 3)
      have s3_11 : c12 (k + 5) = xor (c11 (k + 5)) (c11 (k + 4) || c11 (k + 3)) := r11 (k + 3)
      have s3_12 : c13 (k + 5) = xor (c12 (k + 5)) (c12 (k + 4) || c12 (k + 3)) := r12 (k + 3)
      have s3_13 : c14 (k + 5) = xor (c13 (k + 5)) (c13 (k + 4) || c13 (k + 3)) := r13 (k + 3)
      have s3_14 : c15 (k + 5) = xor (c14 (k + 5)) (c14 (k + 4) || c14 (k + 3)) := r14 (k + 3)
      have s3_15 : c (k + 5) = xor (c15 (k + 5)) (c15 (k + 4) || c15 (k + 3)) := r15 (k + 3)
      have s4_0 : c1 (k + 6) = xor (c (k + 6)) (c (k + 5) || c (k + 4)) := r0 (k + 4)
      have s4_1 : c2 (k + 6) = xor (c1 (k + 6)) (c1 (k + 5) || c1 (k + 4)) := r1 (k + 4)
      have s4_2 : c3 (k + 6) = xor (c2 (k + 6)) (c2 (k + 5) || c2 (k + 4)) := r2 (k + 4)
      have s4_3 : c4 (k + 6) = xor (c3 (k + 6)) (c3 (k + 5) || c3 (k + 4)) := r3 (k + 4)
      have s4_4 : c5 (k + 6) = xor (c4 (k + 6)) (c4 (k + 5) || c4 (k + 4)) := r4 (k + 4)
      have s4_5 : c6 (k + 6) = xor (c5 (k + 6)) (c5 (k + 5) || c5 (k + 4)) := r5 (k + 4)
      have s4_6 : c7 (k + 6) = xor (c6 (k + 6)) (c6 (k + 5) || c6 (k + 4)) := r6 (k + 4)
      have s4_7 : c8 (k + 6) = xor (c7 (k + 6)) (c7 (k + 5) || c7 (k + 4)) := r7 (k + 4)
      have s4_8 : c9 (k + 6) = xor (c8 (k + 6)) (c8 (k + 5) || c8 (k + 4)) := r8 (k + 4)
      have s4_9 : c10 (k + 6) = xor (c9 (k + 6)) (c9 (k + 5) || c9 (k + 4)) := r9 (k + 4)
      have s4_10 : c11 (k + 6) = xor (c10 (k + 6)) (c10 (k + 5) || c10 (k + 4)) := r10 (k + 4)
      have s4_11 : c12 (k + 6) = xor (c11 (k + 6)) (c11 (k + 5) || c11 (k + 4)) := r11 (k + 4)
      have s4_12 : c13 (k + 6) = xor (c12 (k + 6)) (c12 (k + 5) || c12 (k + 4)) := r12 (k + 4)
      have s4_13 : c14 (k + 6) = xor (c13 (k + 6)) (c13 (k + 5) || c13 (k + 4)) := r13 (k + 4)
      have s4_14 : c15 (k + 6) = xor (c14 (k + 6)) (c14 (k + 5) || c14 (k + 4)) := r14 (k + 4)
      have s4_15 : c (k + 6) = xor (c15 (k + 6)) (c15 (k + 5) || c15 (k + 4)) := r15 (k + 4)
      simp only [p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p'1, p'2, p'3, p'4, p'5, p'6, p'7, p'8, p'9, p'10, p'11, p'12, p'13, p'14, p'15, heq, Bool.or_self] at s0_0 s0_1 s0_2 s0_3 s0_4 s0_5 s0_6 s0_7 s0_8 s0_9 s0_10 s0_11 s0_12 s0_13 s0_14 s0_15 s1_0 s1_1 s1_2 s1_3 s1_4 s1_5 s1_6 s1_7 s1_8 s1_9 s1_10 s1_11 s1_12 s1_13 s1_14 s1_15 s2_0 s2_1 s2_2 s2_3 s2_4 s2_5 s2_6 s2_7 s2_8 s2_9 s2_10 s2_11 s2_12 s2_13 s2_14 s2_15 s3_0 s3_1 s3_2 s3_3 s3_4 s3_5 s3_6 s3_7 s3_8 s3_9 s3_10 s3_11 s3_12 s3_13 s3_14 s3_15 s4_0 s4_1 s4_2 s4_3 s4_4 s4_5 s4_6 s4_7 s4_8 s4_9 s4_10 s4_11 s4_12 s4_13 s4_14 s4_15
      exact dead_core (c k) (c (k + 2)) (c1 (k + 2)) (c2 (k + 2)) (c3 (k + 2)) (c4 (k + 2)) (c5 (k + 2)) (c6 (k + 2)) (c7 (k + 2)) (c8 (k + 2)) (c9 (k + 2)) (c10 (k + 2)) (c11 (k + 2)) (c12 (k + 2)) (c13 (k + 2)) (c14 (k + 2)) (c15 (k + 2)) (c (k + 3)) (c1 (k + 3)) (c2 (k + 3)) (c3 (k + 3)) (c4 (k + 3)) (c5 (k + 3)) (c6 (k + 3)) (c7 (k + 3)) (c8 (k + 3)) (c9 (k + 3)) (c10 (k + 3)) (c11 (k + 3)) (c12 (k + 3)) (c13 (k + 3)) (c14 (k + 3)) (c15 (k + 3)) (c (k + 4)) (c1 (k + 4)) (c2 (k + 4)) (c3 (k + 4)) (c4 (k + 4)) (c5 (k + 4)) (c6 (k + 4)) (c7 (k + 4)) (c8 (k + 4)) (c9 (k + 4)) (c10 (k + 4)) (c11 (k + 4)) (c12 (k + 4)) (c13 (k + 4)) (c14 (k + 4)) (c15 (k + 4)) (c (k + 5)) (c1 (k + 5)) (c2 (k + 5)) (c3 (k + 5)) (c4 (k + 5)) (c5 (k + 5)) (c6 (k + 5)) (c7 (k + 5)) (c8 (k + 5)) (c9 (k + 5)) (c10 (k + 5)) (c11 (k + 5)) (c12 (k + 5)) (c13 (k + 5)) (c14 (k + 5)) (c15 (k + 5)) (c (k + 6)) (c1 (k + 6)) (c2 (k + 6)) (c3 (k + 6)) (c4 (k + 6)) (c5 (k + 6)) (c6 (k + 6)) (c7 (k + 6)) (c8 (k + 6)) (c9 (k + 6)) (c10 (k + 6)) (c11 (k + 6)) (c12 (k + 6)) (c13 (k + 6)) (c14 (k + 6)) (c15 (k + 6))
        s0_0 s0_1 s0_2 s0_3 s0_4 s0_5 s0_6 s0_7 s0_8 s0_9 s0_10 s0_11 s0_12 s0_13 s0_14 s0_15 s1_0 s1_1 s1_2 s1_3 s1_4 s1_5 s1_6 s1_7 s1_8 s1_9 s1_10 s1_11 s1_12 s1_13 s1_14 s1_15 s2_0 s2_1 s2_2 s2_3 s2_4 s2_5 s2_6 s2_7 s2_8 s2_9 s2_10 s2_11 s2_12 s2_13 s2_14 s2_15 s3_0 s3_1 s3_2 s3_3 s3_4 s3_5 s3_6 s3_7 s3_8 s3_9 s3_10 s3_11 s3_12 s3_13 s3_14 s3_15 s4_0 s4_1 s4_2 s4_3 s4_4 s4_5 s4_6 s4_7 s4_8 s4_9 s4_10 s4_11 s4_12 s4_13 s4_14 s4_15
    have or_of_ne : ∀ k, Alt k → c (k + 1) = !c k → Alt (k + 1) →
        (c (k + 1) || c k) = true ∧ (c1 (k + 1) || c1 k) = true ∧ (c2 (k + 1) || c2 k) = true ∧ (c3 (k + 1) || c3 k) = true ∧ (c4 (k + 1) || c4 k) = true ∧ (c5 (k + 1) || c5 k) = true ∧ (c6 (k + 1) || c6 k) = true ∧ (c7 (k + 1) || c7 k) = true ∧ (c8 (k + 1) || c8 k) = true ∧ (c9 (k + 1) || c9 k) = true ∧ (c10 (k + 1) || c10 k) = true ∧ (c11 (k + 1) || c11 k) = true ∧ (c12 (k + 1) || c12 k) = true ∧ (c13 (k + 1) || c13 k) = true ∧ (c14 (k + 1) || c14 k) = true := by
      intro k ak hne ak1
      obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15⟩ := ak
      obtain ⟨p'1, p'2, p'3, p'4, p'5, p'6, p'7, p'8, p'9, p'10, p'11, p'12, p'13, p'14, p'15⟩ := ak1
      rw [p'1, p1, p'2, p2, p'3, p3, p'4, p4, p'5, p5, p'6, p6, p'7, p7, p'8, p8, p'9, p9, p'10, p10, p'11, p11, p'12, p12, p'13, p13, p'14, p14, hne]
      cases c k <;> decide
    have main : ∀ n, Alt (n + 1) ∧ Alt (n + 2) ∧ c (n + 2) = !c (n + 1) := by
      intro n
      induction n with
      | zero =>
        have a2 : Alt 2 := by
          have hh : (c 1 || c 0) = true := by rw [h0, Bool.or_true]
          exact alt_of_or 0 hh (by rw [z1, Bool.or_true]) (by rw [z2, Bool.or_true]) (by rw [z3, Bool.or_true]) (by rw [z4, Bool.or_true]) (by rw [z5, Bool.or_true]) (by rw [z6, Bool.or_true]) (by rw [z7, Bool.or_true]) (by rw [z8, Bool.or_true]) (by rw [z9, Bool.or_true]) (by rw [z10, Bool.or_true]) (by rw [z11, Bool.or_true]) (by rw [z12, Bool.or_true]) (by rw [z13, Bool.or_true]) (by rw [z14, Bool.or_true])
        refine ⟨alt1, a2, ?_⟩
        cases hc : c 2 <;> cases hc1 : c 1
        · exact absurd (hc.trans hc1.symm) (fun h => not_equal_alt 1 alt1 a2 h)
        · rfl
        · rfl
        · exact absurd (hc.trans hc1.symm) (fun h => not_equal_alt 1 alt1 a2 h)
      | succ m ih =>
        obtain ⟨am, am1, hne⟩ := ih
        obtain ⟨o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13, o14⟩ := or_of_ne (m + 1) am hne am1
        have a3 : Alt (m + 3) := alt_of_or (m + 1) o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 o11 o12 o13 o14
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
    rw [h4, h4, h4, h4]

end Rule30Open.Frames.EdgePeriodSixteen
