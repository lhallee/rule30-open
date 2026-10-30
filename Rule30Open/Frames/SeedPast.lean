module

public import Rule30Open.Foundations.Official

/-!
# Every row of the single cell's past is eventually periodic

Read a row leftward from a frame that moves one cell right per step: bit `j` of `y` is the cell `j` places left of the
frame. One step of Rule 30 is then `phiF`, bit `j` of which is `y j` XOR (`y (j - 1)` OR `y (j - 2)`), for every row
white right of the frame (`frame_step`). `phiF` is a bijection of the sequences of bits: `phiInv` inverts it bit by bit
(`phiF_phiInv`, `phiInv_phiF`). So the single cell has exactly one row `k` steps back in this frame, `rho k`
(`past_unique`).

Inverting runs a transducer whose state is the last two output bits, so it carries an eventually periodic sequence to
an eventually periodic one (`phiInv_evPer`): after the input's preperiod, among the states at five consecutive starts of
a period two agree. Hence every `rho k` is eventually periodic (`rho_evPer`), and so is every row, white right of some
cell, that Rule 30 takes to a single black cell (`past_evPer`).

The natural-language argument is `SeedPast.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

/-- One step of Rule 30 in the frame: bit `j` reads bits `j`, `j - 1` and `j - 2`, white below 0. -/
def phiF (y : Nat → Bool) : Nat → Bool
  | 0 => y 0
  | 1 => xor (y 1) (y 0)
  | j + 2 => xor (y (j + 2)) (y (j + 1) || y j)

/-- The state of the inverting transducer before bit `j`: the output bits `j - 1` and `j - 2`, white below 0. -/
def invState (y : Nat → Bool) : Nat → Bool × Bool
  | 0 => (false, false)
  | j + 1 => (xor (y j) ((invState y j).1 || (invState y j).2), (invState y j).1)

/-- The inverse of `phiF`, bit by bit: output bit `j` is `y j` XOR (output `j - 1` OR output `j - 2`). -/
def phiInv (y : Nat → Bool) (j : Nat) : Bool := xor (y j) ((invState y j).1 || (invState y j).2)

theorem invState_succ (y : Nat → Bool) (j : Nat) : invState y (j + 1) = (phiInv y j, (invState y j).1) := rfl

theorem phiF_phiInv (y : Nat → Bool) : phiF (phiInv y) = y := by
  funext j
  match j with
  | 0 => show xor (y 0) (false || false) = y 0; cases y 0 <;> rfl
  | 1 =>
    show xor (xor (y 1) ((invState y 1).1 || (invState y 1).2)) (phiInv y 0) = y 1
    rw [invState_succ]
    show xor (xor (y 1) (phiInv y 0 || false)) (phiInv y 0) = y 1
    cases y 1 <;> cases phiInv y 0 <;> rfl
  | j + 2 =>
    show xor (phiInv y (j + 2)) (phiInv y (j + 1) || phiInv y j) = y (j + 2)
    have h2 : invState y (j + 2) = (phiInv y (j + 1), phiInv y j) := by
      rw [invState_succ, invState_succ]
    have e : phiInv y (j + 2) = xor (y (j + 2)) (phiInv y (j + 1) || phiInv y j) := by
      show xor (y (j + 2)) ((invState y (j + 2)).1 || (invState y (j + 2)).2) = _
      rw [h2]
    rw [e]
    generalize y (j + 2) = a
    generalize (phiInv y (j + 1) || phiInv y j) = b
    cases a <;> cases b <;> rfl

/-- Reading `phiF y` back, the transducer's state before bit `j` is `y (j - 1)`, `y (j - 2)`. -/
theorem invState_phiF (y : Nat → Bool) : ∀ j, invState (phiF y) j =
    (if j = 0 then false else y (j - 1), if j ≤ 1 then false else y (j - 2))
  | 0 => rfl
  | 1 => by
    show (xor (phiF y 0) (false || false), false) = _
    show (xor (y 0) (false || false), false) = _
    cases y 0 <;> rfl
  | j + 2 => by
    rw [invState_succ, invState_phiF y (j + 1)]
    unfold phiInv
    rw [invState_phiF y (j + 1)]
    simp only [Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel]
    match j with
    | 0 =>
      show (xor (xor (y 1) (y 0)) (y 0 || false), y 0) = (y 1, y 0)
      cases y 0 <;> cases y 1 <;> rfl
    | j + 1 =>
      show (xor (xor (y (j + 2)) (y (j + 1) || y j)) (y (j + 1) || y j), y (j + 1)) = (y (j + 2), y (j + 1))
      generalize y (j + 2) = a
      generalize (y (j + 1) || y j) = b
      cases a <;> cases b <;> rfl

theorem phiInv_phiF (y : Nat → Bool) : phiInv (phiF y) = y := by
  funext j
  unfold phiInv
  rw [invState_phiF]
  match j with
  | 0 => show xor (y 0) (false || false) = y 0; cases y 0 <;> rfl
  | 1 =>
    show xor (xor (y 1) (y 0)) (y 0 || false) = y 1
    cases y 0 <;> cases y 1 <;> rfl
  | j + 2 =>
    show xor (xor (y (j + 2)) (y (j + 1) || y j)) (y (j + 1) || y j) = y (j + 2)
    generalize y (j + 2) = a
    generalize (y (j + 1) || y j) = b
    cases a <;> cases b <;> rfl

/-- A sequence of bits that repeats with period `p > 0` from bit `N` on: in the frame, a row periodic far to the left. -/
def EvPer (y : Nat → Bool) : Prop := ∃ N p, 0 < p ∧ ∀ j, N ≤ j → y (j + p) = y j

theorem evPer_mul {y : Nat → Bool} {N p : Nat} (h : ∀ j, N ≤ j → y (j + p) = y j) :
    ∀ m j, N ≤ j → y (j + m * p) = y j
  | 0, j, _ => by rw [Nat.zero_mul, Nat.add_zero]
  | m + 1, j, hj => by
    rw [show j + (m + 1) * p = (j + m * p) + p by rw [Nat.succ_mul]; omega, h _ (by omega), evPer_mul h m j hj]

/-- Two states of the transducer that agree at bits `a` and `a + q`, past the input's preperiod and with `q` a
period of the input, agree at every later pair of bits `q` apart. -/
theorem invState_shift {y : Nat → Bool} {N q a : Nat} (hy : ∀ j, N ≤ j → y (j + q) = y j) (ha : N ≤ a)
    (hs : invState y (a + q) = invState y a) : ∀ i, invState y (a + i + q) = invState y (a + i)
  | 0 => by rw [Nat.add_zero]; exact hs
  | i + 1 => by
    rw [show a + (i + 1) + q = (a + i + q) + 1 by omega, show a + (i + 1) = (a + i) + 1 by omega, invState_succ,
      invState_succ]
    unfold phiInv
    rw [invState_shift hy ha hs i, hy (a + i) (by omega)]

/-- Five values of a set of four: two of them agree. -/
theorem pigeon (s : Nat → Bool × Bool) : ∃ a b, a < b ∧ b ≤ 4 ∧ s a = s b := by
  obtain ⟨x0, y0⟩ := s 0
  have h : ∀ (a0 b0 a1 b1 a2 b2 a3 b3 a4 b4 : Bool),
      (a0, b0) = (a1, b1) ∨ (a0, b0) = (a2, b2) ∨ (a0, b0) = (a3, b3) ∨ (a0, b0) = (a4, b4) ∨
      (a1, b1) = (a2, b2) ∨ (a1, b1) = (a3, b3) ∨ (a1, b1) = (a4, b4) ∨ (a2, b2) = (a3, b3) ∨
      (a2, b2) = (a4, b4) ∨ (a3, b3) = (a4, b4) := by decide
  rcases h (s 0).1 (s 0).2 (s 1).1 (s 1).2 (s 2).1 (s 2).2 (s 3).1 (s 3).2 (s 4).1 (s 4).2 with
    h | h | h | h | h | h | h | h | h | h
  · exact ⟨0, 1, by omega, by omega, h⟩
  · exact ⟨0, 2, by omega, by omega, h⟩
  · exact ⟨0, 3, by omega, by omega, h⟩
  · exact ⟨0, 4, by omega, by omega, h⟩
  · exact ⟨1, 2, by omega, by omega, h⟩
  · exact ⟨1, 3, by omega, by omega, h⟩
  · exact ⟨1, 4, by omega, by omega, h⟩
  · exact ⟨2, 3, by omega, by omega, h⟩
  · exact ⟨2, 4, by omega, by omega, h⟩
  · exact ⟨3, 4, by omega, by omega, h⟩

/-- **Inverting keeps eventual periodicity**: if `y` repeats with period `p` from bit `N`, the transducer's states at
two of the bits `N, N + p, ..., N + 4p` agree, and from the first of them `phiInv y` repeats with their distance. -/
theorem phiInv_evPer {y : Nat → Bool} (hy : EvPer y) : EvPer (phiInv y) := by
  obtain ⟨N, p, hp, hper⟩ := hy
  obtain ⟨a, b, hab, -, hs⟩ := pigeon (fun i => invState y (N + i * p))
  have hq : ∀ j, N ≤ j → y (j + (b - a) * p) = y j := fun j hj => evPer_mul hper (b - a) j hj
  have hs' : invState y (N + a * p + (b - a) * p) = invState y (N + a * p) := by
    rw [show N + a * p + (b - a) * p = N + b * p by
      rw [Nat.add_assoc, ← Nat.add_mul, Nat.add_sub_cancel' (Nat.le_of_lt hab)]]
    exact hs.symm
  refine ⟨N + a * p, (b - a) * p, Nat.mul_pos (by omega) hp, fun j hj => ?_⟩
  have e := invState_shift hq (Nat.le_add_right N (a * p)) hs' (j - (N + a * p))
  rw [show N + a * p + (j - (N + a * p)) = j by omega] at e
  unfold phiInv
  rw [e, hq j (by omega)]

/-- The single cell in the frame. -/
def seedBits (j : Nat) : Bool := decide (j = 0)

/-- The row `k` steps before the single cell, in the frame. -/
def rho : Nat → Nat → Bool
  | 0 => seedBits
  | k + 1 => phiInv (rho k)

/-- `k` steps of `phiF`. -/
def phiIter : Nat → (Nat → Bool) → Nat → Bool
  | 0, y => y
  | k + 1, y => phiIter k (phiF y)

theorem phiIter_rho : ∀ k, phiIter k (rho k) = seedBits
  | 0 => rfl
  | k + 1 => by
    show phiIter k (phiF (phiInv (rho k))) = seedBits
    rw [phiF_phiInv, phiIter_rho k]

/-- **The single cell has one past at each depth**: the only row that `phiF` takes to the single cell in `k` steps is
`rho k`. -/
theorem past_unique (k : Nat) (y : Nat → Bool) (h : phiIter k y = seedBits) : y = rho k := by
  induction k generalizing y with
  | zero => exact h
  | succ k ih =>
    have e := ih (phiF y) h
    show y = phiInv (rho k)
    rw [← e, phiInv_phiF]

/-- **Every row of the single cell's past is eventually periodic.** -/
theorem rho_evPer : ∀ k, EvPer (rho k)
  | 0 => ⟨1, 1, by omega, fun j hj => by
      show decide (j + 1 = 0) = decide (j = 0)
      rw [decide_eq_false (by omega), decide_eq_false (by omega)]⟩
  | k + 1 => phiInv_evPer (rho_evPer k)

/-- The frame of a row at time `t`: bit `j` is the cell `j` places left of cell `m + t`. -/
def frame (init : Int → Bool) (m : Int) (t : Nat) (j : Nat) : Bool := evolve init t (m + t - j)

/-- A row white right of cell `m` stays white right of `m + t` at time `t`. -/
theorem right_white (init : Int → Bool) (m : Int) (hm : ∀ x : Int, m < x → init x = false) :
    ∀ t : Nat, ∀ x : Int, m + t < x → evolve init t x = false
  | 0, x, hx => hm x (by omega)
  | t + 1, x, hx => by
    show rule30 (evolve init t (x - 1)) (evolve init t x) (evolve init t (x + 1)) = false
    rw [right_white init m hm t (x - 1) (by omega), right_white init m hm t x (by omega),
      right_white init m hm t (x + 1) (by omega)]
    rfl

/-- **One step of Rule 30 is `phiF` in the frame**, for a row white right of cell `m`. -/
theorem frame_step (init : Int → Bool) (m : Int) (hm : ∀ x : Int, m < x → init x = false) (t : Nat) :
    frame init m (t + 1) = phiF (frame init m t) := by
  have hw := right_white init m hm t
  funext j
  show evolve init (t + 1) (m + ((t + 1 : Nat) : Int) - j) = _
  have e : evolve init (t + 1) (m + ((t + 1 : Nat) : Int) - j) =
      rule30 (evolve init t (m + t - j)) (evolve init t (m + t + 1 - j)) (evolve init t (m + t + 2 - j)) := by
    show rule30 (evolve init t (m + ((t + 1 : Nat) : Int) - j - 1)) (evolve init t (m + ((t + 1 : Nat) : Int) - j))
      (evolve init t (m + ((t + 1 : Nat) : Int) - j + 1)) = _
    rw [show m + ((t + 1 : Nat) : Int) - j + 1 = m + t + 2 - j by omega,
      show m + ((t + 1 : Nat) : Int) - j - 1 = m + t - j by omega,
      show m + ((t + 1 : Nat) : Int) - j = m + t + 1 - j by omega]
  rw [e]
  match j with
  | 0 =>
    show _ = evolve init t (m + t - ((0 : Nat) : Int))
    rw [hw (m + t + 1 - ((0 : Nat) : Int)) (by omega), hw (m + t + 2 - ((0 : Nat) : Int)) (by omega)]
    generalize evolve init t (m + t - ((0 : Nat) : Int)) = a
    cases a <;> rfl
  | 1 =>
    show _ = xor (evolve init t (m + t - ((1 : Nat) : Int))) (evolve init t (m + t - ((0 : Nat) : Int)))
    rw [hw (m + t + 2 - ((1 : Nat) : Int)) (by omega), show m + t + 1 - ((1 : Nat) : Int) = m + t - ((0 : Nat) : Int)
      by omega]
    generalize evolve init t (m + t - ((1 : Nat) : Int)) = a
    generalize evolve init t (m + t - ((0 : Nat) : Int)) = b
    cases a <;> cases b <;> rfl
  | j + 2 =>
    show _ = xor (evolve init t (m + t - ((j + 2 : Nat) : Int)))
      (evolve init t (m + t - ((j + 1 : Nat) : Int)) || evolve init t (m + t - (j : Int)))
    rw [show m + t + 1 - ((j + 2 : Nat) : Int) = m + t - ((j + 1 : Nat) : Int) by omega,
      show m + t + 2 - ((j + 2 : Nat) : Int) = m + t - (j : Int) by omega]
    rfl

theorem frame_iterate (init : Int → Bool) (m : Int) (hm : ∀ x : Int, m < x → init x = false) :
    ∀ k t, frame init m (t + k) = phiIter k (frame init m t)
  | 0, t => rfl
  | k + 1, t => by
    rw [show t + (k + 1) = (t + 1) + k by omega, frame_iterate init m hm k (t + 1), frame_step init m hm t]
    rfl

/-- **A row that Rule 30 takes to a single black cell is eventually periodic to the left**: if a row is white right of
cell `m` and `k` steps later its only black cell is `m + k`, then the row, read leftward from `m`, is `rho k`, which
repeats with some period from some cell on. -/
theorem past_evPer (init : Int → Bool) (m : Int) (hm : ∀ x : Int, m < x → init x = false) (k : Nat)
    (hk : ∀ x : Int, evolve init k x = decide (x = m + k)) :
    (fun j : Nat => init (m - j)) = rho k ∧ EvPer (fun j : Nat => init (m - j)) := by
  have hseed : frame init m k = seedBits := by
    funext j
    show evolve init k (m + k - j) = decide (j = 0)
    rw [hk]
    by_cases hj : j = 0
    · subst hj; simp
    · rw [decide_eq_false (by omega), decide_eq_false hj]
  rw [show k = 0 + k by omega, frame_iterate init m hm k 0] at hseed
  have e := past_unique k _ hseed
  have e' : (fun j : Nat => init (m - j)) = frame init m 0 := by
    funext j
    show init (m - j) = evolve init 0 (m + ((0 : Nat) : Int) - j)
    rw [show m + ((0 : Nat) : Int) - j = m - j by omega]
    rfl
  rw [e', e]
  exact ⟨rfl, rho_evPer k⟩

end Rule30Open
