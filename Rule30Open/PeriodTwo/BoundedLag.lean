module

public import Rule30Open.PeriodTwo.ShiftModel

/-!
# The condition of `InK` is invisible at a bounded lag

For every half `Y`, every `s` and `m` and every prescription `P` of the column reads at the times `t < s + m`, some
half `U` has `heldOrbit U s` equal to `Y` on every cell `j ≥ m` and column reads `P t` at those times
(`invisible_at_bounded_lag`). Two steps:

* `complete_window`: the bits of `X` below `m` can be chosen one at a time so that the column reads of `X` at the
  times `t < m` are any prescribed bits, with `X` equal to `Y` from cell `m` on. This is the triangularity of the column
  read (`column_built`).
* `pull_back`: `held` is onto with the cell 0 of the preimage free (`held_preimage`), and cell 0 of a preimage is the
  column read one step earlier; so any `X` is `heldOrbit U s` for some `U` whose column reads at the times `t < s`
  are any prescribed bits.

In particular the condition of `InK` up to time `s + m` restricts nothing about `heldOrbit U s` on the cells `j ≥ m`
(`inK_window_invisible`).

When `Y` is eventually periodic (a 2-adic rational), `U` can be taken eventually periodic
(`invisible_at_bounded_lag_rational`): the window completion changes finitely many cells, and the preimage under
`held` follows the recursion `u (j + 2) = h (j + 1) xor (u (j + 1) or u j)` on pairs of cells, which over a periodic
`h` repeats by pigeonhole (`heldPre_evPeriodic`).
-/

@[expose] public section

namespace Rule30Open

/-- The preimage under `held` with cell 0 equal to `b`, as consecutive pairs of cells. -/
def heldPrePair (h : Nat → Bool) (b : Bool) : Nat → Bool × Bool
  | 0 => (b, xor (h 0) b)
  | j + 1 => ((heldPrePair h b j).2, xor (h (j + 1)) ((heldPrePair h b j).2 || (heldPrePair h b j).1))

/-- The preimage under `held` of `h` with cell 0 equal to `b`. -/
def heldPre (h : Nat → Bool) (b : Bool) (j : Nat) : Bool := (heldPrePair h b j).1

private theorem xor_xor_self (a c : Bool) : xor (xor a c) c = a := by
  revert a c; decide

private theorem col_alg' (x t g : Bool) (h : xor x (xor t g) = g) : x = t := by
  revert x t g; decide

/-- **`held` is onto, with cell 0 of the preimage free**: `heldPre h b` maps to `h` and has cell 0 equal to `b`. -/
theorem held_heldPre (h : Nat → Bool) (b : Bool) : held (heldPre h b) = h ∧ heldPre h b 0 = b := by
  refine ⟨funext fun j => ?_, rfl⟩
  cases j with
  | zero =>
    show xor (xor (h 0) b) b = h 0
    exact xor_xor_self _ _
  | succ j =>
    show xor (xor (h (j + 1)) ((heldPrePair h b j).2 || (heldPrePair h b j).1))
      ((heldPrePair h b j).2 || (heldPrePair h b j).1) = h (j + 1)
    exact xor_xor_self _ _

theorem held_preimage (h : Nat → Bool) (b : Bool) : ∃ u, held u = h ∧ u 0 = b :=
  ⟨heldPre h b, held_heldPre h b⟩

/-- **Pull-back.** Every `X` is `heldOrbit U s` for some `U` whose column reads at the times `t < s` are any
prescribed bits. -/
theorem pull_back : ∀ (s : Nat) (X P : Nat → Bool), ∃ U, heldOrbit U s = X ∧ ∀ t, t < s → column U t = P t := by
  intro s
  induction s with
  | zero => intro X P; exact ⟨X, rfl, fun t ht => absurd ht (Nat.not_lt_zero t)⟩
  | succ s ih =>
    intro X P
    obtain ⟨V, hV, hVP⟩ := ih X (fun t => P (t + 1))
    obtain ⟨U, hU, hU0⟩ := held_preimage V (P 0)
    refine ⟨U, by rw [heldOrbit_succ, hU, hV], fun t ht => ?_⟩
    cases t with
    | zero => exact hU0
    | succ t =>
      show heldOrbit U (t + 1) 0 = P (t + 1)
      rw [heldOrbit_succ, hU]
      exact hVP t (by omega)

/-- **Completion of a window.** For every `Y`, `m` and prescription `Q`, some `X` equals `Y` on the cells `j ≥ m` and
has column reads `Q t` at the times `t < m`. -/
theorem complete_window (Y Q : Nat → Bool) (m : Nat) :
    ∃ X, (∀ j, m ≤ j → X j = Y j) ∧ ∀ t, t < m → column X t = Q t := by
  let c : Nat → (Nat → Bool) → Bool := fun k p => if k < m then xor (Q k) (column p k) else Y k
  refine ⟨built c, fun j hj => ?_, fun t ht => ?_⟩
  · rw [built_eq]
    have : ¬ j < m := by omega
    simp only [c, this, ↓reduceIte]
  · have h := column_built c t
    rw [built_eq] at h
    simp only [c, ht, ↓reduceIte] at h
    exact col_alg' _ _ _ h

/-- **The column reads before time `s + m` are invisible at lag `m`.** For every `Y`, `s`, `m` and every prescription
`P` of the column reads at the times `t < s + m`, some `U` has `heldOrbit U s` equal to `Y` on every cell `j ≥ m`
and meets the prescription. -/
theorem invisible_at_bounded_lag (Y P : Nat → Bool) (s m : Nat) :
    ∃ U, (∀ j, m ≤ j → heldOrbit U s j = Y j) ∧ ∀ t, t < s + m → column U t = P t := by
  obtain ⟨X, hXY, hXQ⟩ := complete_window Y (fun r => P (s + r)) m
  obtain ⟨U, hUX, hUP⟩ := pull_back s X P
  refine ⟨U, fun j hj => by rw [hUX]; exact hXY j hj, fun t ht => ?_⟩
  by_cases hts : t < s
  · exact hUP t hts
  · obtain ⟨r, rfl⟩ : ∃ r, t = s + r := ⟨t - s, by omega⟩
    show heldOrbit U (s + r) 0 = P (s + r)
    rw [← heldOrbit_add, hUX]
    exact hXQ r (by omega)

/-- **The condition of `InK` up to a finite time restricts no window at lag `m`**: for every `Y`, `s` and `m`, some
`U` reads 1 next to the column at every odd time below `s + m` and has `heldOrbit U s` equal to `Y` on every cell
`j ≥ m`. Combined with the identity, the same `Y`-window is also reached with the reads at odd times below `s + m`
set to anything else. -/
theorem inK_window_invisible (Y : Nat → Bool) (s m : Nat) :
    ∃ U, (∀ j, m ≤ j → heldOrbit U s j = Y j) ∧ ∀ k, 2 * k + 1 < s + m → heldOrbit U (2 * k + 1) 0 = true := by
  obtain ⟨U, hY, hP⟩ := invisible_at_bounded_lag Y (fun _ => true) s m
  exact ⟨U, hY, fun k hk => hP (2 * k + 1) hk⟩

/-! ### Rational data give a rational half -/

/-- `u` is eventually periodic: a 2-adic rational. -/
def EvPeriodic (u : Nat → Bool) : Prop := ∃ pre per, 0 < per ∧ ∀ k, pre ≤ k → u (k + per) = u k

theorem evPeriodic_mul (h : Nat → Bool) (pre per : Nat) (hp : ∀ k, pre ≤ k → h (k + per) = h k) :
    ∀ d k, pre ≤ k → h (k + per * d) = h k := by
  intro d
  induction d with
  | zero => intro k _; rfl
  | succ d ih =>
    intro k hk
    rw [show k + per * (d + 1) = k + per * d + per by rw [Nat.mul_succ]; omega, hp _ (by omega), ih k hk]

/-- A sequence equal to an eventually periodic one from some cell on is eventually periodic. -/
theorem evPeriodic_of_eventually_eq (u v : Nat → Bool) (m : Nat) (h : ∀ j, m ≤ j → u j = v j)
    (hv : EvPeriodic v) : EvPeriodic u := by
  obtain ⟨pre, per, hper, hp⟩ := hv
  refine ⟨pre + m, per, hper, fun k hk => ?_⟩
  rw [h k (by omega), h (k + per) (by omega)]
  exact hp k (by omega)

/-- **The preimage of a rational is rational**: `heldPre h b` is eventually periodic when `h` is. -/
theorem heldPre_evPeriodic (h : Nat → Bool) (b : Bool) (hh : EvPeriodic h) : EvPeriodic (heldPre h b) := by
  obtain ⟨pre, per, hper, hp⟩ := hh
  let p := heldPrePair h b
  let a : Nat → List Bool := fun i => [(p (pre + per * i)).1, (p (pre + per * i)).2]
  obtain ⟨i, i', hii, -, he⟩ := Ruliology.CellularAutomata.Rule30Jen.pigeonhole 2 a (fun _ => rfl)
  have he' : p (pre + per * i) = p (pre + per * i + per * (i' - i)) := by
    simp only [a, List.cons.injEq, and_true] at he
    rw [show pre + per * i + per * (i' - i) = pre + per * i' by
      rw [Nat.add_assoc, ← Nat.mul_add, show i + (i' - i) = i' by omega]]
    exact Prod.ext he.1 he.2
  have hm := evPeriodic_mul h pre per hp (i' - i)
  have key : ∀ r, p (pre + per * i + per * (i' - i) + r) = p (pre + per * i + r) := by
    intro r
    induction r with
    | zero => exact he'.symm
    | succ r ih =>
      show heldPrePair h b (pre + per * i + per * (i' - i) + r + 1) = heldPrePair h b (pre + per * i + r + 1)
      show ((p (pre + per * i + per * (i' - i) + r)).2,
          xor (h (pre + per * i + per * (i' - i) + r + 1))
            ((p (pre + per * i + per * (i' - i) + r)).2 || (p (pre + per * i + per * (i' - i) + r)).1)) =
        ((p (pre + per * i + r)).2,
          xor (h (pre + per * i + r + 1)) ((p (pre + per * i + r)).2 || (p (pre + per * i + r)).1))
      rw [ih, show pre + per * i + per * (i' - i) + r + 1 = pre + per * i + r + 1 + per * (i' - i) by omega,
        hm _ (by omega)]
  have hd : 0 < per * (i' - i) := Nat.mul_pos hper (by omega)
  refine ⟨pre + per * i, per * (i' - i), hd, fun k hk => ?_⟩
  obtain ⟨r, rfl⟩ : ∃ r, k = pre + per * i + r := ⟨k - (pre + per * i), by omega⟩
  show (p (pre + per * i + r + per * (i' - i))).1 = (p (pre + per * i + r)).1
  rw [show pre + per * i + r + per * (i' - i) = pre + per * i + per * (i' - i) + r by omega, key]

/-- Pull-back keeping rationality: a rational `X` is `heldOrbit U s` for a rational `U` with any prescribed column
reads at the times `t < s`. -/
theorem pull_back_rational : ∀ (s : Nat) (X P : Nat → Bool), EvPeriodic X →
    ∃ U, EvPeriodic U ∧ heldOrbit U s = X ∧ ∀ t, t < s → column U t = P t := by
  intro s
  induction s with
  | zero => intro X P hX; exact ⟨X, hX, rfl, fun t ht => absurd ht (Nat.not_lt_zero t)⟩
  | succ s ih =>
    intro X P hX
    obtain ⟨V, hVr, hV, hVP⟩ := ih X (fun t => P (t + 1)) hX
    obtain ⟨hU, hU0⟩ := held_heldPre V (P 0)
    refine ⟨heldPre V (P 0), heldPre_evPeriodic V (P 0) hVr, by rw [heldOrbit_succ, hU, hV], fun t ht => ?_⟩
    cases t with
    | zero => exact hU0
    | succ t =>
      show heldOrbit (heldPre V (P 0)) (t + 1) 0 = P (t + 1)
      rw [heldOrbit_succ, hU]
      exact hVP t (by omega)

/-- **The bounded-lag statement with rational data**: when `Y` is eventually periodic, the half `U` of
`invisible_at_bounded_lag` can be taken eventually periodic, a 2-adic rational. -/
theorem invisible_at_bounded_lag_rational (Y P : Nat → Bool) (s m : Nat) (hY : EvPeriodic Y) :
    ∃ U, EvPeriodic U ∧ (∀ j, m ≤ j → heldOrbit U s j = Y j) ∧ ∀ t, t < s + m → column U t = P t := by
  obtain ⟨X, hXY, hXQ⟩ := complete_window Y (fun r => P (s + r)) m
  obtain ⟨U, hUr, hUX, hUP⟩ := pull_back_rational s X P (evPeriodic_of_eventually_eq X Y m hXY hY)
  refine ⟨U, hUr, fun j hj => by rw [hUX]; exact hXY j hj, fun t ht => ?_⟩
  by_cases hts : t < s
  · exact hUP t hts
  · obtain ⟨r, rfl⟩ : ∃ r, t = s + r := ⟨t - s, by omega⟩
    show heldOrbit U (s + r) 0 = P (s + r)
    rw [← heldOrbit_add, hUX]
    exact hXQ r (by omega)

end Rule30Open
