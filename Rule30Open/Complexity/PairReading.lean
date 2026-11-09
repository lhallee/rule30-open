module

public import Rule30Open.Foundations.Official
public import Rule30Open.Complexity.BinomialDuality
public import Ruliology.CellularAutomata.Rule30Problem3
public import Ruliology.CellularAutomata.Rule30FiniteConfigs

/-!
# Two columns read as one sequence cost every machine more steps than its window has digits, at every scale

The kit's `Rule30Problem3.Machine` reads the binary digits of `n`, least significant first, from cell `0` on. In `a`
steps its head visits only cells below `a`, and for every input `m ≥ 2 ^ (a - 1)` those cells hold the lowest `a`
digits of `m`. So a machine that halts within `a` steps on one input `n ≥ 2 ^ (a - 1)` gives the same answer on every
`m ≥ 2 ^ (a - 1)` congruent to `n` modulo `2 ^ a` (`computes_eq_of_mod`). The kit's main branch proves the same
locality (`Rule30Problem3Bounds.computes_eq_of_mod_two_pow_of_run_le`); the kit's commit pinned here does not have
it, so it is proved again (`step_agree`, `run_agree`, `init_tape_agree`).

* `window_period`: if a machine computes `f` within `T`, and `T n ≤ a` for the `2 ^ a` consecutive inputs `n` of a
  window `[A, A + 2 ^ a)` with `A ≥ 2 ^ (a - 1)`, then `f (m + 2 ^ a) = f m` for every `m ≥ 2 ^ (a - 1)`: the window
  meets every class modulo `2 ^ a`.
* `pairOf_window_time`: let `pairOf init j k` read column `j` of Rule 30 from the row `init` at the even inputs and
  column `k` at the odd ones, `pairOf init j k (2t) = evolve init t j` and `pairOf init j k (2t + 1) = evolve init t k`.
  If `init` has a leftmost black cell and `j ≠ k`, every machine that computes it takes at least `a + 1` steps on some
  input of every window `[A, A + 2 ^ a)` with `a ≥ 1` and `A ≥ 2 ^ (a - 1)`. Otherwise both columns would have period
  `2 ^ (a - 1)` from `2 ^ (a - 1)` on, which the kit's Jen theorem for such rows (`Rule30FiniteConfigs.jen`) excludes.
* `pair_window_time`, `pair_interval_time`: the single black cell, with `pair j k (2t) = cell t j` (`pair_even`,
  `pair_center` for the official center); every interval `[A, 3A)`, `A ≥ 1`, holds an input on which the machine
  takes more steps than `A` has binary digits.
* `column_window_time`: the same window bound for a single column that is not eventually periodic, for every row, and
  `column_window_time_or`: of two different columns of a row with a leftmost black cell, at least one has it
  (`Rule30FiniteConfigs.periodic_column_unique`), so every column but at most one has it.
  `center_window_time_of_problem1`: for the official center column it follows from Problem 1.
* `center_window_time_le_seventeen`: for the official center column and `1 ≤ a ≤ 17` it holds, from
  `center_rung_le_seventeen` (`BinomialDuality`, which excludes the period `2 ^ a` from `2 ^ (a - 1)` with the window
  bound of `WideWindow`). So every machine computing the center column takes more than `a` steps on infinitely many
  inputs for `a ≤ 17`, in Lean at the kit's pinned commit.

For the center column alone the bound at every scale is open: it says that the column has no eventual period `2 ^ a`,
part of Problem 1.

The natural-language argument is `PairReading.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

open Ruliology.CellularAutomata Rule30Problem3 Rule30Jen

/-! ### Locality: in `a` steps a machine reads the lowest `a` digits only -/

/-- Two configurations with the same state and head that agree on the cells below `B`, with the head below `B`, take
the same step: both halt with the same answer, or both continue with the same state and head, the head at most one
cell further right, and tapes that still agree below `B`. -/
theorem step_agree {M : Machine} {c₁ c₂ : Cfg M} {B : Int} (hs : c₁.state = c₂.state)
    (hh : c₁.head = c₂.head) (hB : c₁.head < B) (ht : ∀ i, i < B → c₁.tape i = c₂.tape i) :
    (∃ b, c₁.step = .inl b ∧ c₂.step = .inl b) ∨
      ∃ d₁ d₂, c₁.step = .inr d₁ ∧ c₂.step = .inr d₂ ∧ d₁.state = d₂.state ∧ d₁.head = d₂.head ∧
        d₁.head ≤ c₁.head + 1 ∧ ∀ i, i < B → d₁.tape i = d₂.tape i := by
  have hread : c₁.tape c₁.head = c₂.tape c₂.head := by
    rw [← hh]
    exact ht c₁.head hB
  unfold Cfg.step
  rw [hs, hread]
  cases hδ : M.δ c₂.state (c₂.tape c₂.head) with
  | inl b => exact Or.inl ⟨b, rfl, rfl⟩
  | inr v =>
    obtain ⟨p, a, d⟩ := v
    refine Or.inr ⟨_, _, rfl, rfl, rfl, by rw [hh], ?_, fun i hi => ?_⟩
    · cases d <;> simp only [Move.apply] <;> omega
    · dsimp only
      rw [hh]
      by_cases hih : i = c₂.head
      · simp [hih]
      · simp [hih, ht i hi]

/-- Two runs whose initial tapes agree below `B` agree for `B` steps: both have halted with the same answer, or both
run with the same state and head, the head at most at cell `t`, and tapes that agree below `B`. -/
theorem run_agree {M : Machine} {m n B : Nat}
    (h0 : ∀ i : Int, i < B → (M.init m).tape i = (M.init n).tape i) :
    ∀ t, t ≤ B → (∃ b, M.run m t = .inl b ∧ M.run n t = .inl b) ∨
      ∃ c₁ c₂, M.run m t = .inr c₁ ∧ M.run n t = .inr c₂ ∧ c₁.state = c₂.state ∧
        c₁.head = c₂.head ∧ c₁.head ≤ t ∧ ∀ i : Int, i < B → c₁.tape i = c₂.tape i
  | 0, _ => Or.inr ⟨_, _, rfl, rfl, rfl, rfl, by simp [Machine.init], h0⟩
  | t + 1, ht => by
    rcases run_agree h0 t (by omega) with ⟨b, h1, h2⟩ | ⟨c₁, c₂, h1, h2, hs, hh, hle, hti⟩
    · exact Or.inl ⟨b, by simp [Machine.run, h1], by simp [Machine.run, h2]⟩
    · rcases step_agree hs hh (by omega) hti with ⟨b, e1, e2⟩ |
          ⟨d₁, d₂, e1, e2, hs', hh', hle', ht'⟩
      · exact Or.inl ⟨b, by simp [Machine.run, h1, e1], by simp [Machine.run, h2, e2]⟩
      · exact Or.inr ⟨d₁, d₂, by simp [Machine.run, h1, e1], by simp [Machine.run, h2, e2], hs', hh',
          by omega, ht'⟩

/-- Inputs `m, n ≥ 2 ^ (a - 1)` that agree modulo `2 ^ a` have the same initial tape below cell `a`: blanks left of
cell `0`, and on the cells `0, …, a - 1` the lowest `a` digits, which they share. -/
theorem init_tape_agree (M : Machine) {m n a : Nat} (hm : 2 ^ (a - 1) ≤ m) (hn : 2 ^ (a - 1) ≤ n)
    (hmod : m % 2 ^ a = n % 2 ^ a) : ∀ i : Int, i < a → (M.init m).tape i = (M.init n).tape i := by
  intro i hi
  simp only [Machine.init]
  by_cases h0 : 0 ≤ i
  · have hlt : i.toNat < a := by omega
    have hpow : 2 ^ i.toNat ≤ 2 ^ (a - 1) := Nat.pow_le_pow_right (by decide) (by omega)
    have hbit : m.testBit i.toNat = n.testBit i.toNat := by
      have h1 := Nat.testBit_mod_two_pow m a i.toNat
      have h2 := Nat.testBit_mod_two_pow n a i.toNat
      rw [hmod] at h1
      rw [decide_eq_true hlt, Bool.true_and] at h1 h2
      exact h1.symm.trans h2
    rw [ite_eq_left (And.intro h0 (Nat.le_trans hpow hm)), ite_eq_left (And.intro h0 (Nat.le_trans hpow hn)),
      hbit]
  · rw [ite_eq_right (fun h => h0 h.1), ite_eq_right (fun h => h0 h.1)]

/-- A run that has halted has one answer. -/
theorem run_inl_eq {M : Machine} {n t s : Nat} {b₁ b₂ : Bool} (h₁ : M.run n t = .inl b₁)
    (h₂ : M.run n s = .inl b₂) : b₁ = b₂ := by
  have e₁ := Machine.run_add h₁ s
  have e₂ := Machine.run_add h₂ t
  rw [Nat.add_comm] at e₂
  have := e₁.symm.trans e₂
  injection this

/-- **Locality.** If `M` computes `f` within `T` and `T n ≤ a` for an input `n ≥ 2 ^ (a - 1)`, then `f m = f n` for
every `m ≥ 2 ^ (a - 1)` congruent to `n` modulo `2 ^ a`. -/
theorem computes_eq_of_mod {M : Machine} {f : Nat → Bool} {T : Nat → Nat} (hM : Computes M f T)
    {m n a : Nat} (hm : 2 ^ (a - 1) ≤ m) (hn : 2 ^ (a - 1) ≤ n) (hmod : m % 2 ^ a = n % 2 ^ a)
    (hT : T n ≤ a) : f m = f n := by
  have hrun : M.run n a = .inl (f n) := by
    have := Machine.run_add (hM n) (a - T n)
    rwa [Nat.add_sub_cancel' hT] at this
  rcases run_agree (init_tape_agree M hm hn hmod) a (Nat.le_refl a) with ⟨b, h1, h2⟩ | ⟨_, _, _, h2, _⟩
  · rw [h2] at hrun
    exact (run_inl_eq (hM m) h1).trans (Sum.inl.inj hrun)
  · rw [h2] at hrun
    cases hrun

/-! ### Windows -/

/-- **A fast window forces a period.** If `M` computes `f` within `T` and takes at most `a` steps on each of the
`2 ^ a` inputs of `[A, A + 2 ^ a)`, `A ≥ 2 ^ (a - 1)`, then `f` has period `2 ^ a` from `2 ^ (a - 1)` on. -/
theorem window_period {M : Machine} {f : Nat → Bool} {T : Nat → Nat} (hM : Computes M f T)
    {a A : Nat} (hA : 2 ^ (a - 1) ≤ A) (hwin : ∀ n, A ≤ n → n < A + 2 ^ a → T n ≤ a) :
    ∀ m, 2 ^ (a - 1) ≤ m → f (m + 2 ^ a) = f m := by
  intro m hm
  have hP : 0 < 2 ^ a := Nat.two_pow_pos a
  have hAP : A ≤ 2 ^ a * A := Nat.le_mul_of_pos_left A hP
  -- the input of the window congruent to `m`
  have hlt : (m + 2 ^ a * A - A) % 2 ^ a < 2 ^ a := Nat.mod_lt _ hP
  have hrep : (A + (m + 2 ^ a * A - A) % 2 ^ a) % 2 ^ a = m % 2 ^ a := by
    have h1 := Nat.mod_add_div (m + 2 ^ a * A - A) (2 ^ a)
    have h2 : (A + (m + 2 ^ a * A - A) % 2 ^ a) + 2 ^ a * ((m + 2 ^ a * A - A) / 2 ^ a) =
        m + 2 ^ a * A := by omega
    have h3 := congrArg (· % 2 ^ a) h2
    simp only [Nat.add_mul_mod_self_left] at h3
    exact h3
  have hT := hwin (A + (m + 2 ^ a * A - A) % 2 ^ a) (Nat.le_add_right _ _) (by omega)
  have e1 := computes_eq_of_mod hM hm (by omega) hrep.symm hT
  have e2 := computes_eq_of_mod hM (m := m + 2 ^ a) (by omega) (by omega)
    (by rw [Nat.add_mod_right]; exact hrep.symm) hT
  rw [e2, e1]

/-! ### Two columns as one sequence -/

theorem two_pow_eq_two_mul {a : Nat} (ha : 1 ≤ a) : 2 ^ a = 2 * 2 ^ (a - 1) := by
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  rw [Nat.add_sub_cancel, Nat.pow_succ, Nat.mul_comm]

namespace PairReading

/-- `evolve` is the kit's `Rule30Realization.evol`, so the kit's Jen theorem for every row with a leftmost black cell
applies to it. -/
theorem evolve_evol (init : Int → Bool) : ∀ (t : Nat) (x : Int), evolve init t x = Rule30Realization.evol init t x
  | 0, _ => rfl
  | t + 1, x => by
    show rule30 (evolve init t (x - 1)) (evolve init t x) (evolve init t (x + 1)) =
      Rule30Jen.rule (Rule30Realization.evol init t (x - 1)) (Rule30Realization.evol init t x)
        (Rule30Realization.evol init t (x + 1))
    rw [evolve_evol init t (x - 1), evolve_evol init t x, evolve_evol init t (x + 1)]
    rfl

end PairReading

/-- Columns `j` and `k` of Rule 30 from the row `init`, read as one sequence: column `j` at the even inputs and
column `k` at the odd ones. -/
def pairOf (init : Int → Bool) (j k : Int) (n : Nat) : Bool :=
  if n % 2 = 0 then evolve init (n / 2) j else evolve init (n / 2) k

theorem pairOf_even (init : Int → Bool) (j k : Int) (t : Nat) : pairOf init j k (2 * t) = evolve init t j := by
  simp only [pairOf]
  rw [ite_eq_left (by omega), show 2 * t / 2 = t by omega]

theorem pairOf_odd (init : Int → Bool) (j k : Int) (t : Nat) :
    pairOf init j k (2 * t + 1) = evolve init t k := by
  simp only [pairOf]
  rw [ite_eq_right (by omega), show (2 * t + 1) / 2 = t by omega]

/-- **Two columns cost every machine more than `a` steps on every window of `2 ^ a` inputs above `2 ^ (a - 1)`**,
for every row with a leftmost black cell `lo`. -/
theorem pairOf_window_time {init : Int → Bool} {lo : Int} (hlo : init lo = true)
    (hzero : ∀ p, p < lo → init p = false) {j k : Int} (hjk : j ≠ k) {M : Machine} {T : Nat → Nat}
    (hM : Computes M (pairOf init j k) T) {a A : Nat} (ha : 1 ≤ a) (hA : 2 ^ (a - 1) ≤ A) :
    ∃ n, A ≤ n ∧ n < A + 2 ^ a ∧ a + 1 ≤ T n := by
  refine Classical.byContradiction fun hno => ?_
  have hwin : ∀ n, A ≤ n → n < A + 2 ^ a → T n ≤ a := fun n h1 h2 =>
    Nat.le_of_not_lt fun hlt => hno ⟨n, h1, h2, hlt⟩
  have hper := window_period hM hA hwin
  have h2 : 2 ^ a = 2 * 2 ^ (a - 1) := two_pow_eq_two_mul ha
  have hH : 0 < 2 ^ (a - 1) := Nat.two_pow_pos _
  refine Rule30FiniteConfigs.jen hlo hzero j k hjk ⟨⟨2 ^ (a - 1), 2 ^ (a - 1), hH, fun t ht => ?_⟩,
    ⟨2 ^ (a - 1), 2 ^ (a - 1), hH, fun t ht => ?_⟩⟩
  · have := hper (2 * t) (by omega)
    rw [h2, show 2 * t + 2 * 2 ^ (a - 1) = 2 * (t + 2 ^ (a - 1)) by omega, pairOf_even, pairOf_even,
      PairReading.evolve_evol, PairReading.evolve_evol] at this
    exact this
  · have := hper (2 * t + 1) (by omega)
    rw [h2, show 2 * t + 1 + 2 * 2 ^ (a - 1) = 2 * (t + 2 ^ (a - 1)) + 1 by omega, pairOf_odd,
      pairOf_odd, PairReading.evolve_evol, PairReading.evolve_evol] at this
    exact this

/-- Columns `j` and `k` of the single black cell's pattern, read as one sequence. -/
def pair (j k : Int) : Nat → Bool := pairOf single j k

theorem pair_even (j k : Int) (t : Nat) : pair j k (2 * t) = cell t j := by
  rw [pair, pairOf_even, evolve_single_eq_cell]

theorem pair_odd (j k : Int) (t : Nat) : pair j k (2 * t + 1) = cell t k := by
  rw [pair, pairOf_odd, evolve_single_eq_cell]

/-- The center column and column `k` as one sequence: the even inputs read the official center. -/
theorem pair_center (k : Int) (t : Nat) : pair 0 k (2 * t) = Rule30Prize.center t :=
  pair_even 0 k t

theorem single_leftmost : single 0 = true ∧ ∀ p : Int, p < 0 → single p = false :=
  ⟨rfl, fun p hp => decide_eq_false (by omega)⟩

/-- **The single black cell: two columns cost every machine more than `a` steps on every window of `2 ^ a` inputs
above `2 ^ (a - 1)`.** -/
theorem pair_window_time {j k : Int} (hjk : j ≠ k) {M : Machine} {T : Nat → Nat}
    (hM : Computes M (pair j k) T) {a A : Nat} (ha : 1 ≤ a) (hA : 2 ^ (a - 1) ≤ A) :
    ∃ n, A ≤ n ∧ n < A + 2 ^ a ∧ a + 1 ≤ T n :=
  pairOf_window_time single_leftmost.1 single_leftmost.2 hjk hM ha hA

/-- **Every interval `[A, 3A)` holds an input that costs more steps than `A` has digits** (`Nat.log2 A + 1` of
them). -/
theorem pair_interval_time {j k : Int} (hjk : j ≠ k) {M : Machine} {T : Nat → Nat}
    (hM : Computes M (pair j k) T) {A : Nat} (hA : 1 ≤ A) :
    ∃ n, A ≤ n ∧ n < 3 * A ∧ Nat.log2 A + 2 ≤ T n := by
  have hlow : 2 ^ (Nat.log2 A + 1 - 1) ≤ A := by
    rw [Nat.add_sub_cancel]
    exact Nat.log2_self_le (by omega)
  obtain ⟨n, h1, h2, h3⟩ := pair_window_time hjk hM (Nat.le_add_left 1 _) hlow
  refine ⟨n, h1, ?_, h3⟩
  have h4 : 2 ^ (Nat.log2 A + 1) = 2 * 2 ^ Nat.log2 A := Nat.pow_succ'
  rw [Nat.add_sub_cancel] at hlow
  omega

/-! ### One column -/

/-- **A column that is not eventually periodic costs every machine more than `a` steps on every window of `2 ^ a`
inputs above `2 ^ (a - 1)`**, for every row. -/
theorem column_window_time {init : Int → Bool} {x : Int}
    (hx : ¬ EventuallyPeriodic fun t => evolve init t x) {M : Machine} {T : Nat → Nat}
    (hM : Computes M (fun t => evolve init t x) T) {a A : Nat} (hA : 2 ^ (a - 1) ≤ A) :
    ∃ n, A ≤ n ∧ n < A + 2 ^ a ∧ a + 1 ≤ T n := by
  refine Classical.byContradiction fun hno => ?_
  have hwin : ∀ n, A ≤ n → n < A + 2 ^ a → T n ≤ a := fun n h1 h2 =>
    Nat.le_of_not_lt fun hlt => hno ⟨n, h1, h2, hlt⟩
  exact hx ⟨2 ^ (a - 1), 2 ^ a, Nat.two_pow_pos a, window_period hM hA hwin⟩

/-- The window bound for every machine computing column `x` of Rule 30 from `init`. -/
def WindowBound (init : Int → Bool) (x : Int) : Prop :=
  ∀ (M : Machine) (T : Nat → Nat), Computes M (fun t => evolve init t x) T → ∀ a A, 2 ^ (a - 1) ≤ A →
    ∃ n, A ≤ n ∧ n < A + 2 ^ a ∧ a + 1 ≤ T n

/-- **Of two different columns, at least one has the window bound**, for every row with a leftmost black cell: every
column but at most one has it. -/
theorem column_window_time_or {init : Int → Bool} {lo : Int} (hlo : init lo = true)
    (hzero : ∀ p, p < lo → init p = false) {x y : Int} (hxy : x ≠ y) :
    WindowBound init x ∨ WindowBound init y := by
  have hev : ∀ z, (EventuallyPeriodic fun t => evolve init t z) ↔
      EventuallyPeriodic fun t => Rule30Realization.evol init t z := fun z => by
    simp only [PairReading.evolve_evol]
  by_cases hx : EventuallyPeriodic fun t => evolve init t x
  · refine Or.inr fun M T hM a A hA => column_window_time (fun hy => hxy ?_) hM hA
    exact Rule30FiniteConfigs.periodic_column_unique hlo hzero x y ((hev x).1 hx) ((hev y).1 hy)
  · exact Or.inl fun M T hM a A hA => column_window_time hx hM hA

/-- For the center column the window bound at every scale follows from Problem 1. -/
theorem center_window_time_of_problem1 (h : Rule30Prize.Problem1) {M : Machine} {T : Nat → Nat}
    (hM : Computes M Rule30Prize.center T) {a A : Nat} (hA : 2 ^ (a - 1) ≤ A) :
    ∃ n, A ≤ n ∧ n < A + 2 ^ a ∧ a + 1 ≤ T n := by
  have hc : (fun t => evolve single t 0) = Rule30Prize.center := funext evolve_single_center
  exact column_window_time (init := single) (x := 0) (by rw [hc]; exact h) (by rw [hc]; exact hM) hA

/-- **The center column up to level 17.** For `1 ≤ a ≤ 17`, every machine computing the official center takes more
than `a` steps on some input of every window `[A, A + 2 ^ a)` with `A ≥ 2 ^ (a - 1)`, so on infinitely many inputs:
`window_period` with `center_rung_le_seventeen` (`BinomialDuality`, from the window bound of `WideWindow`). -/
theorem center_window_time_le_seventeen {M : Machine} {T : Nat → Nat} (hM : Computes M Rule30Prize.center T)
    {a A : Nat} (ha : 1 ≤ a) (ha17 : a ≤ 17) (hA : 2 ^ (a - 1) ≤ A) :
    ∃ n, A ≤ n ∧ n < A + 2 ^ a ∧ a + 1 ≤ T n := by
  refine Classical.byContradiction fun hno => ?_
  have hwin : ∀ n, A ≤ n → n < A + 2 ^ a → T n ≤ a := fun n h1 h2 =>
    Nat.le_of_not_lt fun hlt => hno ⟨n, h1, h2, hlt⟩
  have hper := window_period hM hA hwin
  obtain ⟨t, ht, hne⟩ := center_rung_le_seventeen (a - 1) (by omega)
  rw [Nat.sub_add_cancel ha] at hne
  exact hne (hper t ht)

end Rule30Open
