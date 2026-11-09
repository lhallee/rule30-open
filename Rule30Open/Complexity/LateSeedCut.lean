module

public import Rule30Open.Complexity.LeftCut
public import Rule30Open.Foundations.Evolve

/-!
# Reading the cone from the left, for every `t`: late seeds separate the `a` leftmost cells

Split the cone of the center after `t` steps after its `a` leftmost cells `-t .. -t + a - 1`. For `2 ≤ a ≤ 10` and every
`t` from a threshold on (`lateStart a`: `3, 4, 6, 7, 10, 12, 14, 17, 17`), any two rows that differ on these cells have
a common completion that gives them different centers (`late_seed_cut`), and the completion can be taken white, or white
except one black cell at `t - (a % 2) - 2R - d` with `R ≤ lateR a` (`0, 1, 3, 4, 7, 7, 8, 11, 14`) and `d ≤ 1`. So every
way to compute the center through states at the cut after the `a` leftmost cells has at least `2 ^ a` states, for every
`t ≥ lateStart a` (`late_seed_width`): ordered decision diagrams that read the row from the left have width `2 ^ a` at
level `a`, at every such `t`. `LeftCut` has this for `t ≤ 17` only.

The proof is a reduction of all `t` to finitely many kernel checks.

* **The cut in the number frame.** The row is the number `2 ^ a r + P` (`P` the `a` left cells, `r` the completion)
  and the center is bit 0 of `nevo` after `t` steps (`lateCen`, `evolve_splice_late`). The `a` low bits evolve by
  `aliceStep`, driven only by the completion's own evolution, through its two lowest bits (`nevo_mod`,
  `nevo_shiftRight`).
* **The horizon.** Bit 0 after `n` more steps reads only bits `0 .. 2n` (`nevo_local`), so with `n = ⌈a/2⌉ - 1` the
  center is a fixed function of the `a` low bits at time `t - n` (`lateCen_eq`).
* **Late seeds read the left edge.** A single black cell evolves as the left-edge frame `edgeFrame` shifted
  (`nevo_two_pow`), so its two cells next to the cut at time `i` are two bits of `edgeFrame i`, at depth at most
  `2R + 2` while it matters. The low `J` bits of `edgeFrame` are eventually periodic, from one kernel check
  (`edgeFrame_periodic`).
* **The shift.** Hence moving `t` to `t + p` and the seed `2p` cells right changes the center only by running the `a`
  left cells `p` steps first (`lateCen_shift`), and `nevo · p` is injective on `a`-bit numbers (`nevo_inj`). So
  separation at `t` gives separation at `t + p` (`lateSep_step`), and the checks at `lateStart a ≤ t < t0 + p` give
  every `t` (`lateSep_all`).
* **The checks** run the `a` left cells for all `2 ^ a` settings at once, as in `LeftCut`, with the completion as one
  number (`packRun`, `lateCol`), and split the settings by the probes (`lateCheck`, by `decide +kernel`).

The natural-language argument is `LateSeedCut.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

/-! ## Facts about the number evolution -/

theorem testBit_nstep (r j : Nat) :
    (nstep r).testBit j = xor (r.testBit j) (r.testBit (j + 1) || r.testBit (j + 2)) := by
  simp only [nstep, Nat.testBit_xor, Nat.testBit_or, Nat.testBit_shiftRight]
  rw [Nat.add_comm 1 j, Nat.add_comm 2 j]

theorem nevo_add (r s : Nat) : ∀ n, nevo r (s + n) = nevo (nevo r s) n
  | 0 => rfl
  | n + 1 => by
    show nstep (nevo r (s + n)) = nstep (nevo (nevo r s) n)
    rw [nevo_add r s n]

theorem nevo_succ' (M s : Nat) : nstep (nevo M s) = nevo (nstep M) s := by
  have h := nevo_add M 1 s
  rw [Nat.add_comm] at h
  exact h

/-- **Locality.** Bit `j` of `nevo M n` reads only the bits `j .. j + 2n` of `M`. -/
theorem nevo_local (n : Nat) : ∀ (M M' K : Nat), (∀ i, i < K + 2 * n → M.testBit i = M'.testBit i) →
    ∀ j, j < K → (nevo M n).testBit j = (nevo M' n).testBit j := by
  induction n with
  | zero => intro M M' K h j hj; exact h j (by omega)
  | succ n ih =>
    intro M M' K h j hj
    have h' := ih M M' (K + 2) (fun i hi => h i (by omega))
    show (nstep (nevo M n)).testBit j = (nstep (nevo M' n)).testBit j
    rw [testBit_nstep, testBit_nstep, h' j (by omega), h' (j + 1) (by omega), h' (j + 2) (by omega)]

theorem nstep_shiftRight (a M : Nat) : nstep M >>> a = nstep (M >>> a) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_shiftRight, testBit_nstep, testBit_nstep, Nat.testBit_shiftRight, Nat.testBit_shiftRight,
    Nat.testBit_shiftRight, Nat.add_assoc, Nat.add_assoc]

/-- The cells from the cut on evolve on their own. -/
theorem nevo_shiftRight (a M : Nat) : ∀ s, nevo M s >>> a = nevo (M >>> a) s
  | 0 => rfl
  | s + 1 => by
    show nstep (nevo M s) >>> a = nstep (nevo (M >>> a) s)
    rw [nstep_shiftRight, nevo_shiftRight a M s]

theorem testBit_of_lt (x a i : Nat) (hx : x < 2 ^ a) (hi : a ≤ i) : x.testBit i = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) hi))

theorem nstep_lt (a x : Nat) (hx : x < 2 ^ a) : nstep x < 2 ^ a := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [testBit_nstep, testBit_of_lt x a i hx hi, testBit_of_lt x a (i + 1) hx (by omega),
    testBit_of_lt x a (i + 2) hx (by omega)]
  rfl

theorem nevo_lt (a x : Nat) (hx : x < 2 ^ a) : ∀ s, nevo x s < 2 ^ a
  | 0 => hx
  | s + 1 => nstep_lt a _ (nevo_lt a x hx s)

/-- `nstep` is injective on `a`-bit numbers: bit `j` of `nstep P` is bit `j` of `P` changed by the bits above it. -/
theorem nstep_inj (a P Q : Nat) (hP : P < 2 ^ a) (hQ : Q < 2 ^ a) (h : nstep P = nstep Q) : P = Q := by
  have key : ∀ k, ∀ j, a ≤ j + k → P.testBit j = Q.testBit j := by
    intro k
    induction k with
    | zero =>
      intro j hj
      rw [testBit_of_lt P a j hP (by omega), testBit_of_lt Q a j hQ (by omega)]
    | succ k ih =>
      intro j hj
      have e := congrArg (fun n => n.testBit j) h
      simp only [testBit_nstep] at e
      rw [ih (j + 1) (by omega), ih (j + 2) (by omega)] at e
      revert e
      generalize (Q.testBit (j + 1) || Q.testBit (j + 2)) = X
      generalize P.testBit j = u
      generalize Q.testBit j = v
      cases u <;> cases v <;> cases X <;> simp
  exact Nat.eq_of_testBit_eq (fun j => key a j (by omega))

theorem nevo_inj (a P Q : Nat) (hP : P < 2 ^ a) (hQ : Q < 2 ^ a) : ∀ s, nevo P s = nevo Q s → P = Q
  | 0, h => h
  | s + 1, h => nevo_inj a P Q hP hQ s (nstep_inj a _ _ (nevo_lt a P hP s) (nevo_lt a Q hQ s) h)

/-! ## The cut: the `a` left cells driven by the completion -/

/-- One step of the `a` left cells (the low bits `x`) when the two cells right of the cut are the bits of `e`. -/
def aliceStep (a x e : Nat) : Nat := nstep (2 ^ a * e + x) % 2 ^ a

/-- The `a` left cells after `s` steps, driven by the pairs `e 0, e 1, ...`. -/
def aliceRun (a : Nat) (e : Nat → Nat) (x : Nat) : Nat → Nat
  | 0 => x
  | s + 1 => aliceStep a (aliceRun a e x s) (e s)

theorem nstep_mod (a N : Nat) : nstep N % 2 ^ a = aliceStep a (N % 2 ^ a) (N >>> a % 4) := by
  unfold aliceStep
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
  by_cases hj : j < a
  · have hlt : N % 2 ^ a < 2 ^ a := Nat.mod_lt _ (Nat.two_pow_pos a)
    have hb : ∀ i, i < a + 2 → (2 ^ a * (N >>> a % 4) + N % 2 ^ a).testBit i = N.testBit i := by
      intro i hi
      rw [Nat.testBit_two_pow_mul_add _ hlt]
      by_cases hia : i < a
      · rw [ite_eq_left hia, Nat.testBit_mod_two_pow]
        simp [hia]
      · rw [ite_eq_right hia, show (4 : Nat) = 2 ^ 2 from rfl, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight,
          show a + (i - a) = i by omega]
        simp [show i - a < 2 by omega]
    rw [testBit_nstep, testBit_nstep, hb j (by omega), hb (j + 1) (by omega), hb (j + 2) (by omega)]
  · simp [hj]

/-- **The cut.** The `a` low bits of the evolution are the left cells driven by the completion's two lowest bits. -/
theorem nevo_mod (a M : Nat) :
    ∀ s, nevo M s % 2 ^ a = aliceRun a (fun i => nevo (M >>> a) i % 4) (M % 2 ^ a) s
  | 0 => rfl
  | s + 1 => by
    show nstep (nevo M s) % 2 ^ a = aliceStep a (aliceRun a _ (M % 2 ^ a) s) (nevo (M >>> a) s % 4)
    rw [nstep_mod, nevo_mod a M s, nevo_shiftRight]

theorem aliceRun_add (a : Nat) (e : Nat → Nat) (x p : Nat) :
    ∀ s, aliceRun a e x (s + p) = aliceRun a (fun i => e (i + p)) (aliceRun a e x p) s
  | 0 => by rw [Nat.zero_add]; rfl
  | s + 1 => by
    rw [show s + 1 + p = (s + p) + 1 by omega]
    show aliceStep a (aliceRun a e x (s + p)) (e (s + p)) = aliceStep a (aliceRun a _ _ s) (e (s + p))
    rw [aliceRun_add a e x p s]

theorem aliceRun_congr (a : Nat) (e e' : Nat → Nat) (x : Nat) :
    ∀ s, (∀ i, i < s → e i = e' i) → aliceRun a e x s = aliceRun a e' x s
  | 0, _ => rfl
  | s + 1, h => by
    show aliceStep a (aliceRun a e x s) (e s) = aliceStep a (aliceRun a e' x s) (e' s)
    rw [aliceRun_congr a e e' x s (fun i hi => h i (by omega)), h s (by omega)]

/-- With white cells right of the cut, the left cells evolve as a row of their own. -/
theorem aliceRun_white (a : Nat) (e : Nat → Nat) (x : Nat) (hx : x < 2 ^ a) :
    ∀ s, (∀ i, i < s → e i = 0) → aliceRun a e x s = nevo x s
  | 0, _ => rfl
  | s + 1, h => by
    show aliceStep a (aliceRun a e x s) (e s) = nstep (nevo x s)
    rw [aliceRun_white a e x hx s (fun i hi => h i (by omega)), h s (by omega)]
    unfold aliceStep
    rw [Nat.mul_zero, Nat.zero_add]
    exact Nat.mod_eq_of_lt (nstep_lt a _ (nevo_lt a x hx s))

/-- The center after `t` steps of the row with the bits of `P` on the cells `-t .. -t + a - 1` and the bits of `r`
from cell `-t + a` on. -/
def lateCen (a t r P : Nat) : Bool := (nevo (2 ^ a * r + P) t).testBit 0

/-- **The horizon.** With `2n + 1 ≤ a`, the center after `T + n` steps is bit 0 after `n` further steps of the left
cells at time `T`, whatever the completion does after `T`. -/
theorem lateCen_eq (a T n r P : Nat) (hP : P < 2 ^ a) (hn : 2 * n + 1 ≤ a) :
    lateCen a (T + n) r P = (nevo (aliceRun a (fun i => nevo r i % 4) P T) n).testBit 0 := by
  unfold lateCen
  rw [nevo_add]
  have hM : (2 ^ a * r + P) >>> a = r := by
    rw [Nat.shiftRight_eq_div_pow, Nat.mul_add_div (Nat.two_pow_pos a), Nat.div_eq_of_lt hP, Nat.add_zero]
  have hm : (2 ^ a * r + P) % 2 ^ a = P := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hP]
  rw [nevo_local n (nevo (2 ^ a * r + P) T) (nevo (2 ^ a * r + P) T % 2 ^ a) 1 ?_ 0 (by omega)]
  · rw [nevo_mod, hM, hm]
  · intro i hi
    rw [Nat.testBit_mod_two_pow]
    simp [show i < a by omega]

/-! ## The single black cell read from its left edge -/

/-- One step of a row read from its left edge, bit `j` the cell `j` places right of the edge:
`Z ↦ 4Z xor (2Z or Z)`. -/
def edgeFrameStep (Z : Nat) : Nat := (Z <<< 2) ^^^ ((Z <<< 1) ||| Z)

/-- The single black cell after `s` steps, read from its left edge. -/
def edgeFrame : Nat → Nat
  | 0 => 1
  | s + 1 => edgeFrameStep (edgeFrame s)

theorem testBit_edgeFrameStep (Z m : Nat) : (edgeFrameStep Z).testBit m =
    xor (decide (2 ≤ m) && Z.testBit (m - 2)) ((decide (1 ≤ m) && Z.testBit (m - 1)) || Z.testBit m) := by
  simp only [edgeFrameStep, Nat.testBit_xor, Nat.testBit_or, Nat.testBit_shiftLeft, ge_iff_le]

/-- **A black cell is the left-edge frame, shifted.** The cell `mu` black and the others white, after `s` steps, is
`edgeFrame s` placed `mu - 2s` cells right. -/
theorem nevo_two_pow (mu : Nat) : ∀ s, nevo (2 ^ mu) s = (edgeFrame s <<< mu) >>> (2 * s)
  | 0 => by simp [nevo, edgeFrame, Nat.shiftLeft_eq]
  | s + 1 => by
    apply Nat.eq_of_testBit_eq
    intro k
    show (nstep (nevo (2 ^ mu) s)).testBit k = _
    rw [testBit_nstep, nevo_two_pow mu s]
    simp only [Nat.testBit_shiftRight, Nat.testBit_shiftLeft, edgeFrame, testBit_edgeFrameStep, ge_iff_le]
    generalize edgeFrame s = Z
    by_cases h1 : mu ≤ 2 * s + k
    · rw [decide_eq_true h1, decide_eq_true (show mu ≤ 2 * s + (k + 1) by omega),
        decide_eq_true (show mu ≤ 2 * s + (k + 2) by omega), decide_eq_true (show mu ≤ 2 * (s + 1) + k by omega),
        decide_eq_true (show 2 ≤ 2 * (s + 1) + k - mu by omega),
        decide_eq_true (show 1 ≤ 2 * (s + 1) + k - mu by omega),
        show 2 * (s + 1) + k - mu - 2 = 2 * s + k - mu by omega,
        show 2 * (s + 1) + k - mu - 1 = 2 * s + (k + 1) - mu by omega,
        show 2 * (s + 1) + k - mu = 2 * s + (k + 2) - mu by omega]
      simp
    · rw [decide_eq_false h1]
      by_cases h2 : mu = 2 * s + k + 1
      · subst h2
        rw [decide_eq_true (show 2 * s + k + 1 ≤ 2 * s + (k + 1) by omega),
          decide_eq_true (show 2 * s + k + 1 ≤ 2 * s + (k + 2) by omega),
          decide_eq_true (show 2 * s + k + 1 ≤ 2 * (s + 1) + k by omega),
          show 2 * (s + 1) + k - (2 * s + k + 1) = 1 by omega, show 2 * s + (k + 1) - (2 * s + k + 1) = 0 by omega,
          show 2 * s + (k + 2) - (2 * s + k + 1) = 1 by omega]
        simp
      · by_cases h3 : mu = 2 * s + k + 2
        · subst h3
          rw [decide_eq_false (show ¬ 2 * s + k + 2 ≤ 2 * s + (k + 1) by omega),
            decide_eq_true (show 2 * s + k + 2 ≤ 2 * s + (k + 2) by omega),
            decide_eq_true (show 2 * s + k + 2 ≤ 2 * (s + 1) + k by omega),
            show 2 * (s + 1) + k - (2 * s + k + 2) = 0 by omega, show 2 * s + (k + 2) - (2 * s + k + 2) = 0 by omega]
          simp
        · rw [decide_eq_false (show ¬ mu ≤ 2 * s + (k + 1) by omega),
            decide_eq_false (show ¬ mu ≤ 2 * s + (k + 2) by omega),
            decide_eq_false (show ¬ mu ≤ 2 * (s + 1) + k by omega)]
          simp

theorem edgeFrameStep_mod (J Z : Nat) : edgeFrameStep Z % 2 ^ J = edgeFrameStep (Z % 2 ^ J) % 2 ^ J := by
  apply Nat.eq_of_testBit_eq
  intro m
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
  by_cases hm : m < J
  · simp only [hm, decide_true, Bool.true_and, testBit_edgeFrameStep, Nat.testBit_mod_two_pow]
    simp [show m - 2 < J by omega, show m - 1 < J by omega]
  · simp [hm]

/-- **Eventual periodicity of the left edge.** The low `J` bits of `edgeFrame` follow a map of their own, so one
repetition gives a period from there on. -/
theorem edgeFrame_periodic (J p s0 : Nat) (h : edgeFrame (s0 + p) % 2 ^ J = edgeFrame s0 % 2 ^ J) :
    ∀ s, s0 ≤ s → edgeFrame (s + p) % 2 ^ J = edgeFrame s % 2 ^ J := by
  have key : ∀ k, edgeFrame (s0 + k + p) % 2 ^ J = edgeFrame (s0 + k) % 2 ^ J := by
    intro k
    induction k with
    | zero => exact h
    | succ k ih =>
      rw [show s0 + (k + 1) + p = (s0 + k + p) + 1 by omega, show s0 + (k + 1) = (s0 + k) + 1 by omega]
      show edgeFrameStep (edgeFrame (s0 + k + p)) % 2 ^ J = edgeFrameStep (edgeFrame (s0 + k)) % 2 ^ J
      rw [edgeFrameStep_mod, ih, ← edgeFrameStep_mod]
  intro s hs
  have := key (s - s0)
  rwa [show s0 + (s - s0) = s by omega] at this

/-! ## Late seeds: the letters and the shift -/

/-- Before the black cell's left edge reaches the cut diagonal, the two cells next to the cut are white. -/
theorem seed_letter_zero (mu i : Nat) (h : 2 * i + 2 ≤ mu) : nevo (2 ^ mu) i % 4 = 0 := by
  rw [nevo_two_pow]
  apply Nat.eq_of_testBit_eq
  intro k
  rw [show (4 : Nat) = 2 ^ 2 from rfl, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, Nat.testBit_shiftLeft,
    Nat.zero_testBit]
  by_cases hk : k < 2
  · rw [decide_eq_false (show ¬ 2 * i + k ≥ mu by omega)]
    simp
  · simp [hk]

/-- **The letters repeat.** If the low `J` bits of the left edge repeat with period `p` from `s0` on, the seed `2p`
cells further right shows, `p` steps later, the same two cells next to the cut, as long as they are read at depth
below `J` and from time `s0` on. -/
theorem seed_letter_shift (J p s0 mu i : Nat)
    (hper : ∀ s, s0 ≤ s → edgeFrame (s + p) % 2 ^ J = edgeFrame s % 2 ^ J)
    (h : 2 * i + 2 ≤ mu ∨ (s0 ≤ i ∧ 2 * i + 2 ≤ mu + J)) :
    nevo (2 ^ (mu + 2 * p)) (i + p) % 4 = nevo (2 ^ mu) i % 4 := by
  rcases h with h | ⟨h1, h2⟩
  · rw [seed_letter_zero mu i h, seed_letter_zero _ _ (by omega)]
  · rw [nevo_two_pow, nevo_two_pow]
    apply Nat.eq_of_testBit_eq
    intro k
    rw [show (4 : Nat) = 2 ^ 2 from rfl, Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight,
      Nat.testBit_shiftRight, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft]
    by_cases hk : k < 2
    · by_cases hmu : mu ≤ 2 * i + k
      · have hp := congrArg (fun n => n.testBit (2 * i + k - mu)) (hper i h1)
        simp only [Nat.testBit_mod_two_pow] at hp
        rw [decide_eq_true (show 2 * i + k - mu < J by omega), Bool.true_and, Bool.true_and] at hp
        rw [decide_eq_true (show 2 * (i + p) + k ≥ mu + 2 * p by omega), decide_eq_true (show 2 * i + k ≥ mu by omega),
          show 2 * (i + p) + k - (mu + 2 * p) = 2 * i + k - mu by omega, hp]
      · rw [decide_eq_false (show ¬ 2 * (i + p) + k ≥ mu + 2 * p by omega),
          decide_eq_false (show ¬ 2 * i + k ≥ mu by omega)]
        simp
    · simp [hk]

/-- The seed of a late probe: `R` places and the parity `d` before the last useful time `t - ⌈a/2⌉`. -/
def seedPos (a t R d : Nat) : Nat := 2 * (t - (a + 1) / 2 - R) - d

/-- **The shift.** From `t0 = s0 + R + 1 + ⌈a/2⌉` on, the center at `t + p` with the late seed `(R, d)` is the
center at `t` with the same seed, for the left cells run `p` steps first. -/
theorem lateCen_shift (a J p s0 R d t P : Nat)
    (hper : ∀ s, s0 ≤ s → edgeFrame (s + p) % 2 ^ J = edgeFrame s % 2 ^ J)
    (hJ : 2 * R + 3 ≤ J) (hd : d ≤ 1) (ht : s0 + R + 1 + (a + 1) / 2 ≤ t) (hP : P < 2 ^ a) (ha : 1 ≤ a) :
    lateCen a (t + p) (2 ^ seedPos a (t + p) R d) P = lateCen a t (2 ^ seedPos a t R d) (nevo P p) := by
  obtain ⟨n, hn_def⟩ : ∃ n, n = (a + 1) / 2 - 1 := ⟨_, rfl⟩
  obtain ⟨T, hT_def⟩ : ∃ T, T = t - n := ⟨_, rfl⟩
  have hn : 2 * n + 1 ≤ a := by omega
  have hmu : seedPos a (t + p) R d = seedPos a t R d + 2 * p := by unfold seedPos; omega
  have e1 : lateCen a (t + p) (2 ^ (seedPos a t R d + 2 * p)) P =
      lateCen a ((T + p) + n) (2 ^ (seedPos a t R d + 2 * p)) P := by
    rw [show (T + p) + n = t + p by omega]
  have e2 : lateCen a t (2 ^ seedPos a t R d) (nevo P p) = lateCen a (T + n) (2 ^ seedPos a t R d) (nevo P p) := by
    rw [show T + n = t by omega]
  have hrun : aliceRun a (fun i => nevo (2 ^ (seedPos a t R d + 2 * p)) i % 4) P (T + p) =
      aliceRun a (fun i => nevo (2 ^ seedPos a t R d) i % 4) (nevo P p) T := by
    rw [aliceRun_add, aliceRun_white a _ P hP p (fun i hi => seed_letter_zero _ _ (by omega))]
    apply aliceRun_congr
    intro i hi
    apply seed_letter_shift J p s0 _ i hper
    unfold seedPos
    omega
  rw [hmu, e1, e2, lateCen_eq a _ _ _ P hP hn, lateCen_eq a _ _ _ _ (nevo_lt a P hP p) hn, hrun]

/-! ## Separation, and the step from `t` to `t + p` -/

/-- The probes at `t`: the white completion and the late seeds `(R, d)` with `R ≤ Rmax`, `d ≤ 1`, inside the cone. -/
def LateProbe (a Rmax t r : Nat) : Prop :=
  r = 0 ∨ ∃ R d, R ≤ Rmax ∧ d ≤ 1 ∧ R + d + (a + 1) / 2 ≤ t ∧ r = 2 ^ seedPos a t R d

/-- Every two settings of the `a` left cells give different centers at some probe. -/
def LateSep (a Rmax t : Nat) : Prop :=
  ∀ P Q, P < 2 ^ a → Q < 2 ^ a → P ≠ Q → ∃ r, LateProbe a Rmax t r ∧ lateCen a t r P ≠ lateCen a t r Q

theorem lateCen_white (a t p P : Nat) : lateCen a (t + p) 0 P = lateCen a t 0 (nevo P p) := by
  unfold lateCen
  simp only [Nat.mul_zero, Nat.zero_add]
  rw [Nat.add_comm t p, nevo_add]

/-- **The step.** Separation at `t ≥ t0` gives separation at `t + p`. -/
theorem lateSep_step (a J p s0 Rmax t : Nat)
    (hper : ∀ s, s0 ≤ s → edgeFrame (s + p) % 2 ^ J = edgeFrame s % 2 ^ J)
    (hJ : 2 * Rmax + 3 ≤ J) (ht : s0 + Rmax + 1 + (a + 1) / 2 ≤ t) (ha : 1 ≤ a)
    (h : LateSep a Rmax t) : LateSep a Rmax (t + p) := by
  intro P Q hP hQ hne
  have hne' : nevo P p ≠ nevo Q p := fun e => hne (nevo_inj a P Q hP hQ p e)
  obtain ⟨r, hr, hsep⟩ := h _ _ (nevo_lt a P hP p) (nevo_lt a Q hQ p) hne'
  rcases hr with rfl | ⟨R, d, hR, hd, hRt, rfl⟩
  · refine ⟨0, Or.inl rfl, ?_⟩
    rw [lateCen_white, lateCen_white]
    exact hsep
  · refine ⟨2 ^ seedPos a (t + p) R d, Or.inr ⟨R, d, hR, hd, by omega, rfl⟩, ?_⟩
    rw [lateCen_shift a J p s0 R d t P hper (by omega) hd (by omega) hP ha,
      lateCen_shift a J p s0 R d t Q hper (by omega) hd (by omega) hQ ha]
    exact hsep

/-! ## The check at one `t`: all settings at once

The `2 ^ a` settings of the left cells are run at once in one number of `a` blocks of `2 ^ a` bits: bit `P` of block
`k` is cell `-t + k` of the setting `P`. The completion is the same for all settings and runs as one number; its two
lowest bits enter as two more blocks of all ones or all zeros (`bobPack`), and one step is `nstep` with blocks for bits
(`packStep`). -/

/-- Blocks `a` and `a + 1`: all ones or all zeros by bits 0 and 1 of the completion `r`. -/
def bobPack (a r : Nat) : Nat :=
  2 ^ (2 ^ a) * (bif r.testBit 1 then 2 ^ (2 ^ a) - 1 else 0) + (bif r.testBit 0 then 2 ^ (2 ^ a) - 1 else 0)

/-- Block `k` becomes block `k` xor (block `k + 1` or block `k + 2`), and the `a` low blocks are kept. -/
def packStepY (a Y : Nat) : Nat := (Y ^^^ ((Y >>> 2 ^ a) ||| (Y >>> (2 * 2 ^ a)))) % 2 ^ (a * 2 ^ a)

/-- One step of the left cells of every setting, with the completion `r`. -/
def packStep (a X r : Nat) : Nat := packStepY a (2 ^ (a * 2 ^ a) * bobPack a r + X)

/-- `s` steps of the left cells of every setting and of the completion. -/
def packRun (a : Nat) : Nat → Nat → Nat → Nat
  | 0, X, _ => X
  | s + 1, X, r => packRun a s (packStep a X r) (nstep r)

/-- Blocks `0 .. k - 1` of the settings: bit `P` of block `j` is bit `j` of `P`. -/
def packInit (a : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => 2 ^ (k * 2 ^ a) * cellPattern k a + packInit a k

/-- The centers after `t` steps for the completion `r`, as a number: bit `P` is `lateCen a t r P`. -/
def lateCol (a t r : Nat) : Nat := packRun a t (packInit a a) r % 2 ^ (2 ^ a)

theorem testBit_bobPack (a r P : Nat) (hP : P < 2 ^ a) :
    (bobPack a r).testBit P = r.testBit 0 ∧ (bobPack a r).testBit (2 ^ a + P) = r.testBit 1 := by
  have hlt : (bif r.testBit 0 then 2 ^ (2 ^ a) - 1 else 0) < 2 ^ (2 ^ a) := by
    cases r.testBit 0
    · exact Nat.two_pow_pos _
    · exact Nat.sub_lt (Nat.two_pow_pos _) (by decide)
  unfold bobPack
  rw [Nat.testBit_two_pow_mul_add _ hlt, Nat.testBit_two_pow_mul_add _ hlt, ite_eq_left hP,
    ite_eq_right (show ¬ 2 ^ a + P < 2 ^ a by omega), show 2 ^ a + P - 2 ^ a = P by omega]
  constructor
  · cases r.testBit 0 <;> simp [Nat.testBit_two_pow_sub_one, hP]
  · cases r.testBit 1 <;> simp [Nat.testBit_two_pow_sub_one, hP]

theorem block_lt (a k P : Nat) (hk : k < a) (hP : P < 2 ^ a) : k * 2 ^ a + P < a * 2 ^ a := by
  have h1 : (k + 1) * 2 ^ a ≤ a * 2 ^ a := Nat.mul_le_mul_right _ hk
  rw [Nat.succ_mul] at h1
  omega

theorem packRun_testBit (a P : Nat) (hP : P < 2 ^ a) : ∀ s (X r M : Nat), X < 2 ^ (a * 2 ^ a) →
    (∀ k, k < a → X.testBit (k * 2 ^ a + P) = M.testBit k) → M >>> a = r →
    ∀ k, k < a → (packRun a s X r).testBit (k * 2 ^ a + P) = (nevo M s).testBit k := by
  intro s
  induction s with
  | zero => intro X r M _ hX _; exact hX
  | succ s ih =>
    intro X r M hXlt hX hr
    show ∀ k, k < a → (packRun a s (packStep a X r) (nstep r)).testBit (k * 2 ^ a + P) =
      (nstep (nevo M s)).testBit k
    rw [nevo_succ']
    apply ih (packStep a X r) (nstep r) (nstep M)
    · exact Nat.mod_lt _ (Nat.two_pow_pos _)
    · intro k hk
      have hY : ∀ j, j < a + 2 →
          (2 ^ (a * 2 ^ a) * bobPack a r + X).testBit (j * 2 ^ a + P) = M.testBit j := by
        intro j hj
        rw [Nat.testBit_two_pow_mul_add _ hXlt]
        by_cases hja : j < a
        · rw [ite_eq_left (block_lt a j P hja hP), hX j hja]
        · rw [ite_eq_right (show ¬ j * 2 ^ a + P < a * 2 ^ a by
              have : a * 2 ^ a ≤ j * 2 ^ a := Nat.mul_le_mul_right _ (by omega)
              omega)]
          have hbit : M.testBit j = r.testBit (j - a) := by
            rw [← hr, Nat.testBit_shiftRight, show a + (j - a) = j by omega]
          rw [hbit]
          rcases (show j = a ∨ j = a + 1 by omega) with rfl | rfl
          · rw [show j * 2 ^ j + P - j * 2 ^ j = P by omega, Nat.sub_self]
            exact (testBit_bobPack j r P hP).1
          · rw [show (a + 1) * 2 ^ a + P - a * 2 ^ a = 2 ^ a + P by rw [Nat.succ_mul]; omega,
              show a + 1 - a = 1 by omega]
            exact (testBit_bobPack a r P hP).2
      unfold packStep packStepY
      rw [Nat.testBit_mod_two_pow, decide_eq_true (block_lt a k P hk hP), Bool.true_and, Nat.testBit_xor,
        Nat.testBit_or, Nat.testBit_shiftRight, Nat.testBit_shiftRight,
        show 2 ^ a + (k * 2 ^ a + P) = (k + 1) * 2 ^ a + P by rw [Nat.succ_mul]; omega,
        show 2 * 2 ^ a + (k * 2 ^ a + P) = (k + 2) * 2 ^ a + P by rw [Nat.add_mul]; omega,
        hY k (by omega), hY (k + 1) (by omega), hY (k + 2) (by omega), testBit_nstep]
    · rw [← hr]
      exact nstep_shiftRight a M

theorem cellPattern_lt (k a : Nat) : cellPattern k a < 2 ^ (2 ^ a) := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [testBit_cellPattern]
  simp [show ¬ i < 2 ^ a by omega]

theorem packInit_spec (a P : Nat) (hP : P < 2 ^ a) : ∀ k, packInit a k < 2 ^ (k * 2 ^ a) ∧
    ∀ j, j < k → (packInit a k).testBit (j * 2 ^ a + P) = P.testBit j := by
  intro k
  induction k with
  | zero => exact ⟨by simp [packInit], fun j hj => absurd hj (by omega)⟩
  | succ k ih =>
    obtain ⟨hlt, hbits⟩ := ih
    refine ⟨?_, ?_⟩
    · apply Nat.lt_pow_two_of_testBit
      intro i hi
      have hk : k * 2 ^ a + 2 ^ a ≤ i := by rw [Nat.succ_mul] at hi; omega
      simp only [packInit]
      rw [Nat.testBit_two_pow_mul_add _ hlt, ite_eq_right (by omega)]
      exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (cellPattern_lt k a) (Nat.pow_le_pow_right (by decide)
        (by omega)))
    · intro j hj
      simp only [packInit]
      rw [Nat.testBit_two_pow_mul_add _ hlt]
      by_cases hjk : j < k
      · rw [ite_eq_left (show j * 2 ^ a + P < k * 2 ^ a by
          have : (j + 1) * 2 ^ a ≤ k * 2 ^ a := Nat.mul_le_mul_right _ hjk
          rw [Nat.succ_mul] at this
          omega), hbits j hjk]
      · have hjk' : j = k := by omega
        subst hjk'
        rw [ite_eq_right (by omega), show j * 2 ^ a + P - j * 2 ^ a = P by omega, testBit_cellPattern]
        simp [hP]

theorem lateCol_testBit (a t r P : Nat) (ha : 1 ≤ a) (hP : P < 2 ^ a) :
    (lateCol a t r).testBit P = lateCen a t r P := by
  unfold lateCol lateCen
  rw [Nat.testBit_mod_two_pow, decide_eq_true hP, Bool.true_and]
  obtain ⟨hlt, hbits⟩ := packInit_spec a P hP a
  have h := packRun_testBit a P hP t (packInit a a) r (2 ^ a * r + P) hlt ?_ ?_
  · have := h 0 (by omega)
    rwa [Nat.zero_mul, Nat.zero_add] at this
  · intro k hk
    rw [hbits k hk, Nat.testBit_two_pow_mul_add _ hP, ite_eq_left hk]
  · rw [Nat.shiftRight_eq_div_pow, Nat.mul_add_div (Nat.two_pow_pos a), Nat.div_eq_of_lt hP, Nat.add_zero]

/-- The probes at `t` as completion numbers: white, then the seeds `(R, d)` inside the cone. -/
def lateProbes (a t Rmax : Nat) : List Nat :=
  0 :: (List.range (Rmax + 1)).flatMap (fun R => (List.range 2).filterMap
    (fun d => if R + d + (a + 1) / 2 ≤ t then some (2 ^ seedPos a t R d) else none))

theorem mem_lateProbes (a t Rmax r : Nat) (h : r ∈ lateProbes a t Rmax) : LateProbe a Rmax t r := by
  simp only [lateProbes, List.mem_cons, List.mem_flatMap, List.mem_range, List.mem_filterMap] at h
  rcases h with rfl | ⟨R, hR, d, hd, h⟩
  · exact Or.inl rfl
  · by_cases hc : R + d + (a + 1) / 2 ≤ t
    · rw [ite_eq_left hc] at h
      exact Or.inr ⟨R, d, by omega, by omega, hc, (Option.some.inj h).symm⟩
    · rw [ite_eq_right hc] at h
      cases h

theorem nevo_zero : ∀ s, nevo 0 s = 0
  | 0 => rfl
  | s + 1 => by
    show nstep (nevo 0 s) = 0
    rw [nevo_zero s]
    rfl

/-- While the two cells next to the cut stay white, the row splits into the left cells and the completion, each run
on its own. -/
theorem nevo_split_white (a r P k : Nat) (hP : P < 2 ^ a) (h : ∀ i, i < k → nevo r i % 4 = 0) :
    nevo (2 ^ a * r + P) k = 2 ^ a * nevo r k + nevo P k := by
  have hM : (2 ^ a * r + P) >>> a = r := by
    rw [Nat.shiftRight_eq_div_pow, Nat.mul_add_div (Nat.two_pow_pos a), Nat.div_eq_of_lt hP, Nat.add_zero]
  have hm : (2 ^ a * r + P) % 2 ^ a = P := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hP]
  have hmod := nevo_mod a (2 ^ a * r + P) k
  have hshift := nevo_shiftRight a (2 ^ a * r + P) k
  rw [hM, hm, aliceRun_white a _ P hP k h] at hmod
  rw [hM] at hshift
  rw [← Nat.div_add_mod (nevo (2 ^ a * r + P) k) (2 ^ a), ← Nat.shiftRight_eq_div_pow, hshift, hmod]

/-- The center through the white stretch: the left cells run `k` steps on their own first. -/
theorem lateCen_suffix (a k m r P : Nat) (hP : P < 2 ^ a) (h : ∀ i, i < k → nevo r i % 4 = 0) :
    lateCen a (k + m) r P = lateCen a m (nevo r k) (nevo P k) := by
  unfold lateCen
  rw [nevo_add, nevo_split_white a r P k hP h]

/-- The steps the check runs: all `t` steps for small `t`, else the last `⌈a/2⌉ + Rmax + 1`. -/
def lateSteps (a t Rmax : Nat) : Nat := min t ((a + 1) / 2 + Rmax + 1)

theorem lateSteps_le (a t Rmax : Nat) : lateSteps a t Rmax ≤ t := Nat.min_le_left _ _

/-- Every probe keeps the two cells next to the cut white before the last `lateSteps` steps. -/
theorem probe_letters_zero (a t Rmax r : Nat) (hr : LateProbe a Rmax t r) :
    ∀ i, i < t - lateSteps a t Rmax → nevo r i % 4 = 0 := by
  rcases hr with rfl | ⟨R, d, hR, hd, hRt, rfl⟩
  · intro i _
    rw [nevo_zero]
  · intro i hi
    apply seed_letter_zero
    have h1 : lateSteps a t Rmax = min t ((a + 1) / 2 + Rmax + 1) := rfl
    rw [Nat.min_def] at h1
    unfold seedPos
    split at h1 <;> omega

/-- **The check at `t`.** Write `m = lateSteps a t Rmax` and `v = nevo P (t - m)`, the left cells after the white
stretch. The probes, each run the last `m` steps from every `v` with the completion it has reached at `t - m`, split
the `2 ^ a` values of `v` into single values. -/
def lateCheck (a t Rmax : Nat) : Bool :=
  refineMasks (fun r => lateCol a (lateSteps a t Rmax) (nevo r (t - lateSteps a t Rmax))) (lateProbes a t Rmax)
    [2 ^ (2 ^ a) - 1]

theorem lateSep_of_check (a t Rmax : Nat) (ha : 1 ≤ a) (h : lateCheck a t Rmax = true) : LateSep a Rmax t := by
  intro P Q hP hQ hne
  have hall : ∀ m, m < 2 ^ a → (2 ^ (2 ^ a) - 1).testBit m = true := by
    intro m hm
    simp [Nat.testBit_two_pow_sub_one, hm]
  obtain ⟨m, hm⟩ : ∃ m, m = lateSteps a t Rmax := ⟨_, rfl⟩
  obtain ⟨k, hk⟩ : ∃ k, k = t - m := ⟨_, rfl⟩
  have hkm : t = k + m := by have := lateSteps_le a t Rmax; omega
  have hne' : nevo P k ≠ nevo Q k := fun e => hne (nevo_inj a P Q hP hQ k e)
  have hPk := nevo_lt a P hP k
  have hQk := nevo_lt a Q hQ k
  unfold lateCheck at h
  rw [← hm, ← hk] at h
  obtain ⟨r, hr, hsep⟩ := separates_of_refineMasks _ _ _ h _ List.mem_cons_self (nevo P k) (nevo Q k)
    (hall _ hPk) (hall _ hQk) hne'
  have hprobe := mem_lateProbes a t Rmax r hr
  have hzero := probe_letters_zero a t Rmax r hprobe
  rw [← hm, ← hk] at hzero
  refine ⟨r, hprobe, ?_⟩
  rw [hkm, lateCen_suffix a k m r P hP hzero, lateCen_suffix a k m r Q hQ hzero,
    ← lateCol_testBit a m (nevo r k) _ ha hPk, ← lateCol_testBit a m (nevo r k) _ ha hQk]
  exact hsep

/-- **Every `t` from finitely many checks.** If the low `J ≥ 2 Rmax + 3` bits of the left edge repeat with period
`p` from `s0` on, and the checks pass for `tA ≤ t < t0 + p` with `t0 = s0 + Rmax + 1 + ⌈a/2⌉`, separation holds at
every `t ≥ tA`. -/
theorem lateSep_all (a Rmax J p s0 tA : Nat) (ha : 1 ≤ a) (hp : 0 < p)
    (hper : edgeFrame (s0 + p) % 2 ^ J = edgeFrame s0 % 2 ^ J) (hJ : 2 * Rmax + 3 ≤ J)
    (hA : tA ≤ s0 + Rmax + 1 + (a + 1) / 2)
    (hchk : ∀ t, tA ≤ t → t < s0 + Rmax + 1 + (a + 1) / 2 + p → lateCheck a t Rmax = true) :
    ∀ t, tA ≤ t → LateSep a Rmax t := by
  have hper' := edgeFrame_periodic J p s0 hper
  have key : ∀ m t, tA ≤ t → t < s0 + Rmax + 1 + (a + 1) / 2 + p + m → LateSep a Rmax t := by
    intro m
    induction m with
    | zero => intro t h1 h2; exact lateSep_of_check a t Rmax ha (hchk t h1 (by omega))
    | succ m ih =>
      intro t h1 h2
      by_cases hlt : t < s0 + Rmax + 1 + (a + 1) / 2 + p + m
      · exact ih t h1 hlt
      · have e : t = (t - p) + p := by omega
        rw [e]
        exact lateSep_step a J p s0 Rmax (t - p) hper' hJ (by omega) ha (ih (t - p) (by omega) (by omega))
  intro t ht
  exact key t t ht (by omega)

theorem checks_of_all (a R tA n : Nat) (h : (List.range' tA n).all (fun t => lateCheck a t R) = true) :
    ∀ t, tA ≤ t → t < tA + n → lateCheck a t R = true := by
  intro t h1 h2
  rw [List.all_eq_true] at h
  exact h t (List.mem_range'.mpr ⟨t - tA, by omega, by omega⟩)

/-! ## The checks for `2 ≤ a ≤ 10`

For each `a`: the low `J = 2 R + 3` bits of the left edge repeat with period `p` from `s0` on (one kernel check), and
`lateCheck` passes at every `t` from `lateStart a` to `t0 + p - 1`, `t0 = s0 + R + 1 + ⌈a/2⌉`. -/

theorem edge_period_3 : edgeFrame (2 + 1) % 2 ^ 3 = edgeFrame 2 % 2 ^ 3 := by decide +kernel

theorem edge_period_5 : edgeFrame (2 + 2) % 2 ^ 5 = edgeFrame 2 % 2 ^ 5 := by decide +kernel

theorem edge_period_9 : edgeFrame (2 + 4) % 2 ^ 9 = edgeFrame 2 % 2 ^ 9 := by decide +kernel

theorem edge_period_11 : edgeFrame (6 + 4) % 2 ^ 11 = edgeFrame 6 % 2 ^ 11 := by decide +kernel

theorem edge_period_17 : edgeFrame (16 + 4) % 2 ^ 17 = edgeFrame 16 % 2 ^ 17 := by decide +kernel

theorem edge_period_19 : edgeFrame (20 + 4) % 2 ^ 19 = edgeFrame 20 % 2 ^ 19 := by decide +kernel

theorem edge_period_25 : edgeFrame (27 + 4) % 2 ^ 25 = edgeFrame 27 % 2 ^ 25 := by decide +kernel

theorem edge_period_31 : edgeFrame (33 + 8) % 2 ^ 31 = edgeFrame 33 % 2 ^ 31 := by decide +kernel

theorem late_checks_2 : (List.range' 3 2).all (fun t => lateCheck 2 t 0) = true := by
  decide +kernel

theorem lateSep_2 : ∀ t, 3 ≤ t → LateSep 2 0 t :=
  lateSep_all 2 0 3 1 2 3 (by decide) (by decide) edge_period_3 (by decide) (by decide)
    (fun t h1 h2 => checks_of_all 2 0 3 2 late_checks_2 t h1 (by omega))

theorem late_checks_3 : (List.range' 4 4).all (fun t => lateCheck 3 t 1) = true := by
  decide +kernel

theorem lateSep_3 : ∀ t, 4 ≤ t → LateSep 3 1 t :=
  lateSep_all 3 1 5 2 2 4 (by decide) (by decide) edge_period_5 (by decide) (by decide)
    (fun t h1 h2 => checks_of_all 3 1 4 4 late_checks_3 t h1 (by omega))

theorem late_checks_4 : (List.range' 6 6).all (fun t => lateCheck 4 t 3) = true := by
  decide +kernel

theorem lateSep_4 : ∀ t, 6 ≤ t → LateSep 4 3 t :=
  lateSep_all 4 3 9 4 2 6 (by decide) (by decide) edge_period_9 (by decide) (by decide)
    (fun t h1 h2 => checks_of_all 4 3 6 6 late_checks_4 t h1 (by omega))

theorem late_checks_5 : (List.range' 7 11).all (fun t => lateCheck 5 t 4) = true := by
  decide +kernel

theorem lateSep_5 : ∀ t, 7 ≤ t → LateSep 5 4 t :=
  lateSep_all 5 4 11 4 6 7 (by decide) (by decide) edge_period_11 (by decide) (by decide)
    (fun t h1 h2 => checks_of_all 5 4 7 11 late_checks_5 t h1 (by omega))

theorem late_checks_6 : (List.range' 10 21).all (fun t => lateCheck 6 t 7) = true := by
  decide +kernel

theorem lateSep_6 : ∀ t, 10 ≤ t → LateSep 6 7 t :=
  lateSep_all 6 7 17 4 16 10 (by decide) (by decide) edge_period_17 (by decide) (by decide)
    (fun t h1 h2 => checks_of_all 6 7 10 21 late_checks_6 t h1 (by omega))

theorem late_checks_7 : (List.range' 12 20).all (fun t => lateCheck 7 t 7) = true := by
  decide +kernel

theorem lateSep_7 : ∀ t, 12 ≤ t → LateSep 7 7 t :=
  lateSep_all 7 7 17 4 16 12 (by decide) (by decide) edge_period_17 (by decide) (by decide)
    (fun t h1 h2 => checks_of_all 7 7 12 20 late_checks_7 t h1 (by omega))

theorem late_checks_8 : (List.range' 14 23).all (fun t => lateCheck 8 t 8) = true := by
  decide +kernel

theorem lateSep_8 : ∀ t, 14 ≤ t → LateSep 8 8 t :=
  lateSep_all 8 8 19 4 20 14 (by decide) (by decide) edge_period_19 (by decide) (by decide)
    (fun t h1 h2 => checks_of_all 8 8 14 23 late_checks_8 t h1 (by omega))

theorem late_checks_9 : (List.range' 17 31).all (fun t => lateCheck 9 t 11) = true := by
  decide +kernel

theorem lateSep_9 : ∀ t, 17 ≤ t → LateSep 9 11 t :=
  lateSep_all 9 11 25 4 27 17 (by decide) (by decide) edge_period_25 (by decide) (by decide)
    (fun t h1 h2 => checks_of_all 9 11 17 31 late_checks_9 t h1 (by omega))

theorem late_checks_10 : (List.range' 17 44).all (fun t => lateCheck 10 t 14) = true := by
  decide +kernel

theorem lateSep_10 : ∀ t, 17 ≤ t → LateSep 10 14 t :=
  lateSep_all 10 14 31 8 33 17 (by decide) (by decide) edge_period_31 (by decide) (by decide)
    (fun t h1 h2 => checks_of_all 10 14 17 44 late_checks_10 t h1 (by omega))

/-- The first `t` of the theorem for `a` cells: `3, 4, 6, 7, 10, 12, 14, 17, 17` for `a = 2 .. 10`. The probes fail
at `t = a + 1 .. lateStart a - 1`, except at `a = 7, t = 10`. -/
def lateStart : Nat → Nat
  | 2 => 3 | 3 => 4 | 4 => 6 | 5 => 7 | 6 => 10 | 7 => 12 | 8 => 14 | 9 => 17 | 10 => 17 | _ => 0

/-- The largest `R` of the probes: `0, 1, 3, 4, 7, 7, 8, 11, 14` for `a = 2 .. 10`. -/
def lateR : Nat → Nat
  | 2 => 0 | 3 => 1 | 4 => 3 | 5 => 4 | 6 => 7 | 7 => 7 | 8 => 8 | 9 => 11 | 10 => 14 | _ => 0

theorem lateSep_le (a t : Nat) (ha : 2 ≤ a) (ha' : a ≤ 10) (ht : lateStart a ≤ t) : LateSep a (lateR a) t := by
  rcases (show a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨ a = 6 ∨ a = 7 ∨ a = 8 ∨ a = 9 ∨ a = 10 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lateSep_2 t ht
  · exact lateSep_3 t ht
  · exact lateSep_4 t ht
  · exact lateSep_5 t ht
  · exact lateSep_6 t ht
  · exact lateSep_7 t ht
  · exact lateSep_8 t ht
  · exact lateSep_9 t ht
  · exact lateSep_10 t ht

/-! ## From numbers to rows -/

theorem evolve_eq_evo (x : Int → Bool) : ∀ t, evolve x t = evo x t
  | 0 => rfl
  | t + 1 => by
    funext j
    show rule30 (evolve x t (j - 1)) (evolve x t j) (evolve x t (j + 1)) = coneStep (evo x t) j
    rw [evolve_eq_evo x t]
    rfl

/-- The center of a spliced row is `lateCen` of its `a` left cells, read as a number, and of a number `r` that
carries the completion on the cone. -/
theorem evolve_splice_late (a t r : Nat) (x z : Int → Bool)
    (hz : ∀ i : Int, -(t : Int) + a ≤ i → i ≤ t → z i = r.testBit (i + t - a).toNat) :
    evolve (spliceAt (-(t : Int) + a) x z) t 0 = lateCen a t r (enc (fun k => x ((k : Int) - t)) a) := by
  rw [evolve_eq_evo]
  have hP := enc_lt a (fun k => x ((k : Int) - t))
  have hloc : evo (spliceAt (-(t : Int) + a) x z) t 0 =
      evo (rowN (2 ^ a * r + enc (fun k => x ((k : Int) - t)) a) (-(t : Int))) t 0 := by
    apply evo_local
    intro i h1 h2
    simp only [spliceAt, rowN]
    rw [ite_eq_left (show -(t : Int) ≤ i by omega), Nat.testBit_two_pow_mul_add _ hP]
    by_cases hi : i < -(t : Int) + a
    · rw [ite_eq_left hi, ite_eq_left (show (i - -(t : Int)).toNat < a by omega), testBit_enc _ _ _ (by omega)]
      congr 1
      omega
    · rw [ite_eq_right hi, ite_eq_right (show ¬ (i - -(t : Int)).toNat < a by omega), hz i (by omega) (by omega)]
      congr 1
      omega
  rw [hloc, evo_rowN _ _ _ 0 (by omega)]
  simp only [rowN, lateCen]
  rw [ite_eq_left (by omega), show (0 - (-(t : Int) + (t : Int))).toNat = 0 by omega]

/-- **Separation on rows.** If `t` is separated with seeds up to `Rmax`, two rows that differ somewhere on the cells
`-t .. -t + a - 1` have different centers after `t` steps for the white completion from `-t + a` on, or for the
completion white except one black cell at `t - (a % 2) - 2R - d` with `R ≤ Rmax`, `d ≤ 1` and
`R + d + ⌈a/2⌉ ≤ t`. -/
theorem late_seed_cut_of_sep (a Rmax t : Nat) (hsep : LateSep a Rmax t) (x y : Int → Bool) (i : Int)
    (hi1 : -(t : Int) ≤ i) (hi2 : i < -(t : Int) + a) (hne : x i ≠ y i) :
    evolve (spliceAt (-(t : Int) + a) x (fun _ => false)) t 0 ≠
        evolve (spliceAt (-(t : Int) + a) y (fun _ => false)) t 0 ∨
      ∃ R d : Nat, R ≤ Rmax ∧ d ≤ 1 ∧ R + d + (a + 1) / 2 ≤ t ∧
        evolve (spliceAt (-(t : Int) + a) x (fun j => single (j - ((t : Int) - (a % 2 : Nat) - 2 * R - d)))) t 0 ≠
        evolve (spliceAt (-(t : Int) + a) y (fun j => single (j - ((t : Int) - (a % 2 : Nat) - 2 * R - d)))) t 0 := by
  have hPQ : enc (fun k => x ((k : Int) - t)) a ≠ enc (fun k => y ((k : Int) - t)) a := by
    intro h
    apply hne
    have hx := testBit_enc a (fun k => x ((k : Int) - t)) (i + t).toNat (by omega)
    have hy := testBit_enc a (fun k => y ((k : Int) - t)) (i + t).toNat (by omega)
    have e : (((i + t).toNat : Nat) : Int) - t = i := by omega
    simp only [e] at hx hy
    rw [← hx, ← hy]
    exact congrArg (fun n => n.testBit (i + t).toNat) h
  obtain ⟨r, hr, hne'⟩ := hsep _ _ (enc_lt a _) (enc_lt a _) hPQ
  rcases hr with rfl | ⟨R, d, hR, hd, hRt, rfl⟩
  · left
    have hz : ∀ i : Int, -(t : Int) + a ≤ i → i ≤ t → (fun _ => false) i = (0 : Nat).testBit (i + t - a).toNat :=
      fun i _ _ => (Nat.zero_testBit _).symm
    rw [evolve_splice_late a t 0 x _ hz, evolve_splice_late a t 0 y _ hz]
    exact hne'
  · right
    refine ⟨R, d, hR, hd, hRt, ?_⟩
    have hz : ∀ i : Int, -(t : Int) + a ≤ i → i ≤ t →
        (fun j => single (j - ((t : Int) - (a % 2 : Nat) - 2 * R - d))) i =
          (2 ^ seedPos a t R d).testBit (i + t - a).toNat := by
      intro i h1 h2
      simp only [single, Nat.testBit_two_pow, seedPos]
      rw [decide_eq_decide]
      omega
    rw [evolve_splice_late a t _ x _ hz, evolve_splice_late a t _ y _ hz]
    exact hne'

/-- **States at the cut, from separation.** If the center after `t` steps is computed as `G (F x) z` from a state
`F x` of the cells left of `-t + a` and the cells `z` from `-t + a` on, rows with the same state agree on the cells
`-t .. -t + a - 1`. -/
theorem late_seed_factor_of_sep (a Rmax t : Nat) (hsep : LateSep a Rmax t) {S : Type}
    (F : (Int → Bool) → S) (G : S → (Int → Bool) → Bool)
    (hFG : ∀ x z : Int → Bool, evolve (spliceAt (-(t : Int) + a) x z) t 0 = G (F x) z)
    (x y : Int → Bool) (hxy : F x = F y) : ∀ i : Int, -(t : Int) ≤ i → i < -(t : Int) + a → x i = y i := by
  intro i hi1 hi2
  apply Classical.byContradiction
  intro hne
  rcases late_seed_cut_of_sep a Rmax t hsep x y i hi1 hi2 hne with h | ⟨R, d, _, _, _, h⟩
  · rw [hFG, hFG, hxy] at h
    exact h rfl
  · rw [hFG, hFG, hxy] at h
    exact h rfl

/-- **The width at the cut, from separation.** Every factorization at the cut after the `a` leftmost cells of the cone
has at least `2 ^ a` states: the rows with the bits of `P < 2 ^ a` on the cells `-t .. -t + a - 1` have pairwise
different states. -/
theorem late_seed_width_of_sep (a Rmax t : Nat) (hsep : LateSep a Rmax t) {S : Type}
    (F : (Int → Bool) → S) (G : S → (Int → Bool) → Bool)
    (hFG : ∀ x z : Int → Bool, evolve (spliceAt (-(t : Int) + a) x z) t 0 = G (F x) z) :
    ∀ P Q : Nat, P < 2 ^ a → Q < 2 ^ a → F (rowN P (-(t : Int))) = F (rowN Q (-(t : Int))) → P = Q := by
  intro P Q hP hQ hPQ
  have hagree := late_seed_factor_of_sep a Rmax t hsep F G hFG _ _ hPQ
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < a
  · have := hagree (-(t : Int) + j) (by omega) (by omega)
    simp only [rowN] at this
    rw [ite_eq_left (by omega), ite_eq_left (by omega), show (-(t : Int) + j - -(t : Int)).toNat = j by omega] at this
    exact this
  · rw [testBit_of_lt P a j hP (by omega), testBit_of_lt Q a j hQ (by omega)]

/-- **Late seeds separate the `a` leftmost cells of the cone, for every `t ≥ lateStart a`** (`2 ≤ a ≤ 10`). Two rows
that differ somewhere on the cells `-t .. -t + a - 1` have different centers after `t` steps for the completion from
`-t + a` on that is white, or white except one black cell at `t - (a % 2) - 2R - d` with `R ≤ lateR a`, `d ≤ 1`, a
cell of the cone right of the cut. -/
theorem late_seed_cut (a t : Nat) (ha : 2 ≤ a) (ha' : a ≤ 10) (ht : lateStart a ≤ t) (x y : Int → Bool) (i : Int)
    (hi1 : -(t : Int) ≤ i) (hi2 : i < -(t : Int) + a) (hne : x i ≠ y i) :
    evolve (spliceAt (-(t : Int) + a) x (fun _ => false)) t 0 ≠
        evolve (spliceAt (-(t : Int) + a) y (fun _ => false)) t 0 ∨
      ∃ R d : Nat, R ≤ lateR a ∧ d ≤ 1 ∧ R + d + (a + 1) / 2 ≤ t ∧
        evolve (spliceAt (-(t : Int) + a) x (fun j => single (j - ((t : Int) - (a % 2 : Nat) - 2 * R - d)))) t 0 ≠
        evolve (spliceAt (-(t : Int) + a) y (fun j => single (j - ((t : Int) - (a % 2 : Nat) - 2 * R - d)))) t 0 :=
  late_seed_cut_of_sep a (lateR a) t (lateSep_le a t ha ha' ht) x y i hi1 hi2 hne

/-- **States at the cut** (`2 ≤ a ≤ 10`, `t ≥ lateStart a`). -/
theorem late_seed_factor (a t : Nat) (ha : 2 ≤ a) (ha' : a ≤ 10) (ht : lateStart a ≤ t) {S : Type}
    (F : (Int → Bool) → S) (G : S → (Int → Bool) → Bool)
    (hFG : ∀ x z : Int → Bool, evolve (spliceAt (-(t : Int) + a) x z) t 0 = G (F x) z)
    (x y : Int → Bool) (hxy : F x = F y) : ∀ i : Int, -(t : Int) ≤ i → i < -(t : Int) + a → x i = y i :=
  late_seed_factor_of_sep a (lateR a) t (lateSep_le a t ha ha' ht) F G hFG x y hxy

/-- **The width at the cut, for every `t ≥ lateStart a`** (`2 ≤ a ≤ 10`). Every factorization of the center after `t`
steps through states at the cut after the `a` leftmost cells of the cone has at least `2 ^ a` states. So an ordered
binary decision diagram that reads the row from the left and computes the center after `t` steps has at least `2 ^ a`
nodes at level `a`. -/
theorem late_seed_width (a t : Nat) (ha : 2 ≤ a) (ha' : a ≤ 10) (ht : lateStart a ≤ t) {S : Type}
    (F : (Int → Bool) → S) (G : S → (Int → Bool) → Bool)
    (hFG : ∀ x z : Int → Bool, evolve (spliceAt (-(t : Int) + a) x z) t 0 = G (F x) z) :
    ∀ P Q : Nat, P < 2 ^ a → Q < 2 ^ a → F (rowN P (-(t : Int))) = F (rowN Q (-(t : Int))) → P = Q :=
  late_seed_width_of_sep a (lateR a) t (lateSep_le a t ha ha' ht) F G hFG

theorem lateStart_le (a : Nat) (ha : 2 ≤ a) (ha' : a ≤ 10) : lateStart a ≤ 17 := by
  rcases (show a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨ a = 6 ∨ a = 7 ∨ a = 8 ∨ a = 9 ∨ a = 10 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- **The cut after `a ≤ 10` cells, for every `t ≥ a + 2`.** Two rows that differ somewhere on the cells
`-t .. -t + a - 1` have a common completion from `-t + a` on that gives them different centers after `t` steps:
`LeftCut` for `t ≤ 17`, the late seeds from `lateStart a ≤ 17` on. -/
theorem left_cut_every (a t : Nat) (ha : 2 ≤ a) (ha' : a ≤ 10) (ht : a + 2 ≤ t) (x y : Int → Bool) (i : Int)
    (hi1 : -(t : Int) ≤ i) (hi2 : i < -(t : Int) + a) (hne : x i ≠ y i) :
    ∃ z : Int → Bool, evolve (spliceAt (-(t : Int) + a) x z) t 0 ≠ evolve (spliceAt (-(t : Int) + a) y z) t 0 := by
  by_cases h17 : t ≤ 17
  · obtain ⟨z, hz⟩ := left_cut_at t (by omega) h17 (-(t : Int) + a) (by omega) x y i hi1 hi2 hne
    exact ⟨z, by rw [evolve_eq_evo, evolve_eq_evo]; exact hz⟩
  · have hs := lateStart_le a ha ha'
    rcases late_seed_cut a t ha ha' (by omega) x y i hi1 hi2 hne with h | ⟨R, d, _, _, _, h⟩
    · exact ⟨_, h⟩
    · exact ⟨_, h⟩

/-- **The width at the cut after `a ≤ 10` cells, for every `t ≥ a + 2`.** Every factorization of the center after `t`
steps through states at the cut after the `a` leftmost cells has at least `2 ^ a` states. -/
theorem left_cut_width_every (a t : Nat) (ha : 2 ≤ a) (ha' : a ≤ 10) (ht : a + 2 ≤ t) {S : Type}
    (F : (Int → Bool) → S) (G : S → (Int → Bool) → Bool)
    (hFG : ∀ x z : Int → Bool, evolve (spliceAt (-(t : Int) + a) x z) t 0 = G (F x) z) :
    ∀ P Q : Nat, P < 2 ^ a → Q < 2 ^ a → F (rowN P (-(t : Int))) = F (rowN Q (-(t : Int))) → P = Q := by
  intro P Q hP hQ hPQ
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < a
  · apply Classical.byContradiction
    intro hne
    have hne' : rowN P (-(t : Int)) (-(t : Int) + j) ≠ rowN Q (-(t : Int)) (-(t : Int) + j) := by
      simp only [rowN]
      rw [ite_eq_left (by omega), ite_eq_left (by omega), show (-(t : Int) + j - -(t : Int)).toNat = j by omega]
      exact hne
    obtain ⟨z, hz⟩ := left_cut_every a t ha ha' ht _ _ (-(t : Int) + j) (by omega) (by omega) hne'
    rw [hFG, hFG, hPQ] at hz
    exact hz rfl
  · rw [testBit_of_lt P a j hP (by omega), testBit_of_lt Q a j hQ (by omega)]

end Rule30Open
