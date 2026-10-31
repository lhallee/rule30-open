module

public import Rule30Open.PeriodTwo.HeldColumn
public import Ruliology.CellularAutomata.Rule30Jen

/-!
# The period-two condition is a full 2-shift

Write `column u n` for the cell next to the held column after `n` steps, bit 0 of `heldOrbit u n`, for a half `u`
given as a sequence of bits (a 2-adic integer). Bit 0 of `heldOrbit u n` is `u n` plus a function of the lower bits
`u 0, ..., u (n - 1)` (`heldOrbit_triangular`; on numbers, `heldNat_triangular`). So the column map `u ↦ column u`
is a bijection of the sequences (`column_bijective`): the bits of `u` are fixed one at a time by the column read.

The period-two condition `InK u`, that the column reads 1 at every odd step, therefore fixes each odd bit of `u`
from the lower ones, and the points of `InK` are the graph of a map from the free even bits
(`inK_unique_of_even`, `inK_exists_of_even`). The itinerary `itinerary u s = column u (2 s)` is a bijection from
`InK` onto all sequences (`itinerary_bijective`), `held ∘ held` maps `InK` into itself and shifts the itinerary
(`inK_held_held`, `itinerary_held_held`), and every point of `InK` has exactly two preimages in `InK` (`held_held_two_to_one`).
So `(InK, held ∘ held)` is the one-sided full 2-shift. Nothing here decides whether a point of `InK` has finitely
many ones.

Two consequences. A point of `InK` whose itinerary is periodic has the cell next to the column periodic in time, every
column left of it then has the same period and follows the sideways recursion `heldOrbit_sideways` on a finite set
of words, so by pigeonhole the point is an eventually periodic sequence, a 2-adic rational
(`eventually_periodic_of_column_periodic`, `inK_periodic_rational`). And the last 1 of a half moves out one cell at
every step (`heldOrbit_topBit`), so a point of `InK` with a periodic itinerary, which is fixed by `held` iterated
`2 n` times (`heldOrbit_fixed_of_periodic`), has infinitely many 1s (`inK_periodic_not_finite`); a point of `InK`
with finitely many 1s, in particular a positive integer that is odd at every odd step of `heldNat`, has an itinerary
that is not eventually periodic (`inK_finite_not_preperiodic`, `positive_integer_not_preperiodic`).

The natural-language argument is `ShiftModel.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

/-- The cell next to the held column after `n` steps, for the half `u`. -/
def column (u : Nat → Bool) (n : Nat) : Bool := heldOrbit u n 0

/-- The period-two condition: the cell next to the column reads 1 at every odd step. -/
def InK (u : Nat → Bool) : Prop := ∀ s, heldOrbit u (2 * s + 1) 0 = true

/-- The itinerary of `u`: the column read at the even steps. -/
def itinerary (u : Nat → Bool) (s : Nat) : Bool := heldOrbit u (2 * s) 0

theorem heldOrbit_succ (u : Nat → Bool) (n : Nat) : heldOrbit u (n + 1) = heldOrbit (held u) n := by
  induction n with
  | zero => rfl
  | succ n ih => show held (heldOrbit u (n + 1)) = held (heldOrbit (held u) n); rw [ih]

theorem heldOrbit_two (u : Nat → Bool) (n : Nat) : heldOrbit (held (held u)) n = heldOrbit u (n + 2) := by
  rw [heldOrbit_succ u (n + 1), heldOrbit_succ (held u) n]

private theorem xor_cancel (a b c d : Bool) (h : xor a b = xor c d) (hb : b = d) : a = c := by
  subst hb; cases a <;> cases b <;> cases c <;> simp_all

private theorem xor_left_cancel (a b d : Bool) (h : xor a b = xor a d) : b = d := by
  revert a b d; decide

private theorem parity (n : Nat) : (∃ s, n = 2 * s) ∨ (∃ s, n = 2 * s + 1) := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · exact Or.inl ⟨n / 2, by omega⟩
  · exact Or.inr ⟨n / 2, by omega⟩

private theorem col_alg (x t g : Bool) (h : xor x (xor t g) = g) : x = t := by
  revert x t g; decide

private theorem odd_alg (x g : Bool) (h : xor x (!g) = g) : x = true := by
  revert x g; decide

private theorem xor_shift (A B C D X : Bool) (h : xor A B = xor C D) :
    xor (xor A X) B = xor (xor C X) D := by
  revert A B C D X; decide

/-- Bit `j` of `heldOrbit u t` is bit `j + t` of `u` plus a function of the bits below it: two halves that agree
below `j + t` have the same `heldOrbit _ t j` plus bit `j + t`. -/
theorem heldOrbit_triangular : ∀ (t j : Nat) (u v : Nat → Bool), (∀ i, i < j + t → u i = v i) →
    xor (heldOrbit u t j) (u (j + t)) = xor (heldOrbit v t j) (v (j + t)) := by
  intro t
  induction t with
  | zero =>
    intro j u v _
    show xor (u j) (u (j + 0)) = xor (v j) (v (j + 0))
    simp
  | succ t ih =>
    intro j u v h
    cases j with
    | zero =>
      have a := ih 1 u v (fun i hi => h i (by omega))
      have b := ih 0 u v (fun i hi => h i (by omega))
      have ht : u t = v t := h t (by omega)
      rw [Nat.zero_add] at b
      rw [Nat.add_comm 1 t] at a
      rw [ht] at b
      have e0 : heldOrbit u t 0 = heldOrbit v t 0 := xor_cancel _ _ _ _ b rfl
      show xor (xor (heldOrbit u t 1) (heldOrbit u t 0)) (u (0 + (t + 1))) =
        xor (xor (heldOrbit v t 1) (heldOrbit v t 0)) (v (0 + (t + 1)))
      rw [e0, Nat.zero_add]
      exact xor_shift _ _ _ _ _ a
    | succ j =>
      have a := ih (j + 2) u v (fun i hi => h i (by omega))
      have b := ih (j + 1) u v (fun i hi => h i (by omega))
      have c := ih j u v (fun i hi => h i (by omega))
      have hb : u (j + 1 + t) = v (j + 1 + t) := h _ (by omega)
      have hc : u (j + t) = v (j + t) := h _ (by omega)
      rw [hb] at b
      rw [hc] at c
      have e1 : heldOrbit u t (j + 1) = heldOrbit v t (j + 1) := xor_cancel _ _ _ _ b rfl
      have e2 : heldOrbit u t j = heldOrbit v t j := xor_cancel _ _ _ _ c rfl
      show xor (xor (heldOrbit u t (j + 2)) (heldOrbit u t (j + 1) || heldOrbit u t j)) (u (j + 1 + (t + 1))) =
        xor (xor (heldOrbit v t (j + 2)) (heldOrbit v t (j + 1) || heldOrbit v t j)) (v (j + 1 + (t + 1)))
      rw [e1, e2, show j + 1 + (t + 1) = j + 2 + t by omega]
      exact xor_shift _ _ _ _ _ a

/-- Bit 0 of `heldOrbit u t` is `u t` plus a function of the lower bits. -/
theorem column_triangular (t : Nat) (u v : Nat → Bool) (h : ∀ i, i < t → u i = v i) :
    xor (column u t) (u t) = xor (column v t) (v t) := by
  have := heldOrbit_triangular t 0 u v (fun i hi => h i (by omega))
  rwa [Nat.zero_add] at this

/-- The column read fixes the half: two halves with the same column are equal. -/
theorem column_injective (u v : Nat → Bool) (h : ∀ n, column u n = column v n) : u = v := by
  funext n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    have := column_triangular n u v ih
    rw [h n] at this
    exact xor_left_cancel _ _ _ this

/-- Build a sequence one bit at a time: bit `k` is `c k` of the prefix below it, the prefix padded with 0. -/
def build (c : Nat → (Nat → Bool) → Bool) : Nat → Nat → Bool
  | 0 => fun _ => false
  | k + 1 => fun i => if i = k then c k (build c k) else build c k i

/-- The sequence whose bit `k` is `c k` of its own prefix. -/
def built (c : Nat → (Nat → Bool) → Bool) (k : Nat) : Bool := build c (k + 1) k

theorem build_zero_ge (c : Nat → (Nat → Bool) → Bool) :
    ∀ k i, k ≤ i → build c k i = false := by
  intro k
  induction k with
  | zero => intro i _; rfl
  | succ k ih =>
    intro i hi
    show (if i = k then c k (build c k) else build c k i) = false
    have hne : i ≠ k := by omega
    simp only [hne, ↓reduceIte]
    exact ih i (by omega)

theorem build_prefix (c : Nat → (Nat → Bool) → Bool) :
    ∀ m i, i < m → build c m i = built c i := by
  intro m
  induction m with
  | zero => intro i hi; omega
  | succ m ih =>
    intro i hi
    by_cases him : i = m
    · subst him; rfl
    · show (if i = m then c m (build c m) else build c m i) = built c i
      simp only [him, ↓reduceIte]
      exact ih i (by omega)

theorem built_eq (c : Nat → (Nat → Bool) → Bool) (k : Nat) : built c k = c k (build c k) := by
  show (if k = k then c k (build c k) else build c k k) = _
  simp only [↓reduceIte]

theorem build_agree (c : Nat → (Nat → Bool) → Bool) (k i : Nat) (hi : i < k) : built c i = build c k i :=
  (build_prefix c k i hi).symm

/-- Whatever bit `k` is set to from the prefix, bit 0 of the orbit at step `k` is that bit plus the prefix's. -/
theorem column_built (c : Nat → (Nat → Bool) → Bool) (k : Nat) :
    xor (column (built c) k) (built c k) = column (build c k) k := by
  have := column_triangular k (built c) (build c k) (fun i hi => build_agree c k i hi)
  rw [this, build_zero_ge c k k (Nat.le_refl k)]
  simp

/-- **The column map is onto.** Every sequence of column reads is realized. -/
theorem column_exists (T : Nat → Bool) : ∃ u, ∀ n, column u n = T n := by
  refine ⟨built (fun k p => xor (T k) (column p k)), fun n => ?_⟩
  have h := column_built (fun k p => xor (T k) (column p k)) n
  rw [built_eq] at h
  exact col_alg _ _ _ h

/-- **The column map is a bijection of bit sequences**: each column read has exactly one half. -/
theorem column_bijective (T : Nat → Bool) : ∃ u, (∀ n, column u n = T n) ∧ ∀ v, (∀ n, column v n = T n) → v = u := by
  obtain ⟨u, hu⟩ := column_exists T
  exact ⟨u, hu, fun v hv => column_injective v u (fun n => by rw [hv n, hu n])⟩

/-! ### The points of `InK` are a graph over the even bits -/

/-- Two points of `InK` that agree on the even bits are equal. -/
theorem inK_unique_of_even (u v : Nat → Bool) (hu : InK u) (hv : InK v) (h : ∀ s, u (2 * s) = v (2 * s)) :
    u = v := by
  funext n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rcases parity n with ⟨s, hs⟩ | ⟨s, hs⟩
    · rw [hs]; exact h s
    · have := column_triangular n u v ih
      have e1 : column u n = true := by rw [hs]; exact hu s
      have e2 : column v n = true := by rw [hs]; exact hv s
      rw [e1, e2] at this
      cases hun : u n <;> cases hvn : v n <;> simp_all

/-- Bit `k` of the point with free even bits `e`: `e (k / 2)` at even `k`, the value that makes the column read 1 at odd `k`. -/
def evenFree (e : Nat → Bool) (k : Nat) (p : Nat → Bool) : Bool := if k % 2 = 0 then e (k / 2) else !(column p k)

/-- Every choice of the even bits extends to a point of `InK`. -/
theorem inK_exists_of_even (e : Nat → Bool) : ∃ u, InK u ∧ ∀ s, u (2 * s) = e s := by
  refine ⟨built (evenFree e), fun s => ?_, fun s => ?_⟩
  · have h := column_built (evenFree e) (2 * s + 1)
    have hodd : (2 * s + 1) % 2 ≠ 0 := by omega
    rw [built_eq, show evenFree e (2 * s + 1) (build (evenFree e) (2 * s + 1)) =
      !(column (build (evenFree e) (2 * s + 1)) (2 * s + 1)) by simp only [evenFree, hodd, ↓reduceIte]] at h
    exact odd_alg _ _ h
  · have hev : (2 * s) % 2 = 0 := by omega
    rw [built_eq]
    simp only [evenFree, hev, ↓reduceIte, show 2 * s / 2 = s by omega]

/-- The even bits of a point of `InK` are free and determine it: `InK` is the graph of a map from the even bits. -/
theorem inK_graph : ∀ e : Nat → Bool, ∃ u, (InK u ∧ ∀ s, u (2 * s) = e s) ∧ ∀ v, (InK v ∧ ∀ s, v (2 * s) = e s) → v = u := by
  intro e
  obtain ⟨u, hu, he⟩ := inK_exists_of_even e
  exact ⟨u, ⟨hu, he⟩, fun v hv => inK_unique_of_even v u hv.1 hu (fun s => by rw [hv.2 s, he s])⟩

/-! ### The itinerary is a bijection onto all sequences -/

theorem itinerary_eq_column (u : Nat → Bool) (s : Nat) : itinerary u s = column u (2 * s) := rfl

/-- Two points of `InK` with the same itinerary are equal. -/
theorem itinerary_injective (u v : Nat → Bool) (hu : InK u) (hv : InK v) (h : itinerary u = itinerary v) :
    u = v := by
  apply column_injective
  intro n
  rcases parity n with ⟨s, hs⟩ | ⟨s, hs⟩
  · rw [hs]; exact congrFun h s
  · rw [hs]; exact (hu s).trans (hv s).symm

/-- Every sequence is the itinerary of a point of `InK`. -/
theorem itinerary_exists (β : Nat → Bool) : ∃ u, InK u ∧ itinerary u = β := by
  obtain ⟨u, hu⟩ := column_exists (fun n => if n % 2 = 1 then true else β (n / 2))
  refine ⟨u, fun s => ?_, funext fun s => ?_⟩
  · have h1 := hu (2 * s + 1)
    have hodd : (2 * s + 1) % 2 = 1 := by omega
    simp only [hodd, ↓reduceIte] at h1
    exact h1
  · have h0 := hu (2 * s)
    have hev : ¬ (2 * s) % 2 = 1 := by omega
    simp only [hev, ↓reduceIte, show 2 * s / 2 = s by omega] at h0
    exact h0

/-- **The itinerary is a bijection from `InK` onto all bit sequences.** -/
theorem itinerary_bijective (β : Nat → Bool) : ∃ u, (InK u ∧ itinerary u = β) ∧ ∀ v, (InK v ∧ itinerary v = β) → v = u := by
  obtain ⟨u, hu, hβ⟩ := itinerary_exists β
  exact ⟨u, ⟨hu, hβ⟩, fun v hv => itinerary_injective v u hv.1 hu (hv.2.trans hβ.symm)⟩

/-! ### `held ∘ held` is the shift -/

/-- `held ∘ held` maps `InK` into itself. -/
theorem inK_held_held (u : Nat → Bool) (hu : InK u) : InK (held (held u)) := fun s => by
  show heldOrbit (held (held u)) (2 * s + 1) 0 = true
  rw [heldOrbit_two]
  have := hu (s + 1)
  rwa [show 2 * (s + 1) + 1 = 2 * s + 1 + 2 by omega] at this

/-- `held ∘ held` shifts the itinerary. -/
theorem itinerary_held_held (u : Nat → Bool) (s : Nat) : itinerary (held (held u)) s = itinerary u (s + 1) := by
  show heldOrbit (held (held u)) (2 * s) 0 = heldOrbit u (2 * (s + 1)) 0
  rw [heldOrbit_two, show 2 * (s + 1) = 2 * s + 2 by omega]

/-- **`held ∘ held` is exactly 2-to-1 from `InK` onto `InK`**: each point `w` of `InK` has two preimages in `InK`, one
for each value of the first reading, and no other. -/
theorem held_held_two_to_one (w : Nat → Bool) (hw : InK w) :
    ∃ u₀ u₁, InK u₀ ∧ InK u₁ ∧ u₀ ≠ u₁ ∧ held (held u₀) = w ∧ held (held u₁) = w ∧
      ∀ u, InK u → held (held u) = w → u = u₀ ∨ u = u₁ := by
  have pre : ∀ b : Bool, ∃ u, InK u ∧ itinerary u = (fun s => match s with | 0 => b | s + 1 => itinerary w s) :=
    fun b => itinerary_exists _
  obtain ⟨u₀, h0, i0⟩ := pre false
  obtain ⟨u₁, h1, i1⟩ := pre true
  have lift : ∀ u b, InK u → itinerary u = (fun s => match s with | 0 => b | s + 1 => itinerary w s) →
      held (held u) = w := fun u b hu hi =>
    itinerary_injective _ _ (inK_held_held u hu) hw (funext fun s => by
      rw [itinerary_held_held, hi])
  refine ⟨u₀, u₁, h0, h1, fun h => ?_, lift u₀ false h0 i0, lift u₁ true h1 i1, fun u hu hw' => ?_⟩
  · have := congrFun i0 0
    rw [h] at this
    have h' := congrFun i1 0
    simp at this h'
    rw [this] at h'
    exact absurd h' (by decide)
  · have tail : ∀ s, itinerary u (s + 1) = itinerary w s := fun s => by
      rw [← itinerary_held_held, hw']
    cases hb : itinerary u 0
    · left
      refine itinerary_injective _ _ hu h0 (funext fun s => ?_)
      cases s with
      | zero => rw [hb, i0]
      | succ s => rw [tail s, i0]
    · right
      refine itinerary_injective _ _ hu h1 (funext fun s => ?_)
      cases s with
      | zero => rw [hb, i1]
      | succ s => rw [tail s, i1]

/-! ### On numbers -/

theorem heldNat_repeat_testBit (U : Nat) : ∀ n j,
    (Nat.repeat heldNat n U).testBit j = heldOrbit (fun i => U.testBit i) n j := by
  intro n
  induction n with
  | zero => intro j; rfl
  | succ n ih =>
    intro j
    show (heldNat (Nat.repeat heldNat n U)).testBit j = held (heldOrbit (fun i => U.testBit i) n) j
    rw [heldNat_testBit]
    exact congrArg (fun v => held v j) (funext ih)

/-- On numbers: the parity of `heldNat^t U` is bit `t` of `U` plus a function of `U mod 2^t`. -/
theorem heldNat_triangular (t U V : Nat) (h : U % 2 ^ t = V % 2 ^ t) :
    xor ((Nat.repeat heldNat t U).testBit 0) (U.testBit t) =
      xor ((Nat.repeat heldNat t V).testBit 0) (V.testBit t) := by
  have key := column_triangular t (fun i => U.testBit i) (fun i => V.testBit i) (fun i hi => by
    have := congrArg (fun x => x.testBit i) h
    simp only [Nat.testBit_mod_two_pow, hi, decide_true, Bool.true_and] at this
    exact this)
  unfold column at key
  rwa [heldNat_repeat_testBit, heldNat_repeat_testBit]

/-! ### Periodic columns give 2-adic rationals -/

theorem heldOrbit_add (u : Nat → Bool) (a n : Nat) : heldOrbit (heldOrbit u a) n = heldOrbit u (a + n) := by
  induction n with
  | zero => rfl
  | succ n ih => show held (heldOrbit (heldOrbit u a) n) = held (heldOrbit u (a + n)); rw [ih]

private theorem sideways_alg (a b c : Bool) : a = xor (xor a (b || c)) (b || c) := by
  revert a b c; decide

/-- The sideways recursion: column `k + 2` of the orbit from columns `k` and `k + 1`, one step apart. -/
theorem heldOrbit_sideways (u : Nat → Bool) (t k : Nat) :
    heldOrbit u t (k + 2) = xor (heldOrbit u (t + 1) (k + 1)) (heldOrbit u t (k + 1) || heldOrbit u t k) := by
  show _ = xor (xor (heldOrbit u t (k + 2)) (heldOrbit u t (k + 1) || heldOrbit u t k)) _
  exact sideways_alg _ _ _

private theorem one_alg (a b : Bool) : a = xor (xor a b) b := by
  revert a b; decide

/-- Column 1 of the orbit from column 0 one step apart. -/
theorem heldOrbit_one (u : Nat → Bool) (t : Nat) :
    heldOrbit u t 1 = xor (heldOrbit u (t + 1) 0) (heldOrbit u t 0) := by
  show _ = xor (xor (heldOrbit u t 1) (heldOrbit u t 0)) _
  exact one_alg _ _

private theorem periodic_mod (f : Nat → Bool) (q : Nat) (h : ∀ t, f (t + q) = f t) (t : Nat) :
    f t = f (t % q) := by
  have key : ∀ n r, f (r + q * n) = f r := by
    intro n
    induction n with
    | zero => intro r; rfl
    | succ n ih =>
      intro r
      rw [show r + q * (n + 1) = r + q * n + q by rw [Nat.mul_succ]; omega, h, ih]
  have := key (t / q) (t % q)
  rwa [Nat.mod_add_div] at this

/-- If column 0 of the orbit has period `q`, so has every column. -/
theorem heldOrbit_columns_periodic (u : Nat → Bool) (q : Nat) (h : ∀ t, heldOrbit u (t + q) 0 = heldOrbit u t 0) :
    ∀ k, (∀ t, heldOrbit u (t + q) k = heldOrbit u t k) ∧
      (∀ t, heldOrbit u (t + q) (k + 1) = heldOrbit u t (k + 1)) := by
  intro k
  induction k with
  | zero =>
    refine ⟨h, fun t => ?_⟩
    rw [heldOrbit_one, heldOrbit_one, show t + q + 1 = t + 1 + q by omega, h (t + 1), h t]
  | succ k ih =>
    refine ⟨ih.2, fun t => ?_⟩
    rw [heldOrbit_sideways, heldOrbit_sideways, show t + q + 1 = t + 1 + q by omega, ih.2 (t + 1), ih.2 t, ih.1 t]

/-- **A temporally periodic column means an eventually periodic half**: if the cell next to the column has a period
in time, the 2-adic integer `u` has an eventually periodic expansion, so it is a rational number. The columns left of
the column have the same period and follow the sideways recursion, which is a map on a finite set of words. -/
theorem eventually_periodic_of_column_periodic (u : Nat → Bool) (q : Nat) (hq : 0 < q)
    (h : ∀ t, heldOrbit u (t + q) 0 = heldOrbit u t 0) :
    ∃ pre per, 0 < per ∧ ∀ k, pre ≤ k → u (k + per) = u k := by
  have per := heldOrbit_columns_periodic u q h
  let a : Nat → List Bool := fun m => (List.range (2 * q)).map fun i =>
    if i < q then heldOrbit u i m else heldOrbit u (i - q) (m + 1)
  obtain ⟨m, n, hmn, -, he⟩ := Ruliology.CellularAutomata.Rule30Jen.pigeonhole (2 * q) a (fun m => by simp [a])
  have key : ∀ i, i < 2 * q → (if i < q then heldOrbit u i m else heldOrbit u (i - q) (m + 1)) =
      (if i < q then heldOrbit u i n else heldOrbit u (i - q) (n + 1)) := by
    intro i hi
    have := congrArg (fun l => l[i]?) he
    simpa [a, hi] using this
  have h0 : ∀ t, heldOrbit u t m = heldOrbit u t n := by
    intro t
    have hr := Nat.mod_lt t hq
    have := key (t % q) (by omega)
    simp only [hr, ↓reduceIte] at this
    rw [periodic_mod (fun t => heldOrbit u t m) q (fun t => (per m).1 t) t,
      periodic_mod (fun t => heldOrbit u t n) q (fun t => (per n).1 t) t]
    exact this
  have h1 : ∀ t, heldOrbit u t (m + 1) = heldOrbit u t (n + 1) := by
    intro t
    have hr := Nat.mod_lt t hq
    have := key (q + t % q) (by omega)
    have hnl : ¬ (q + t % q < q) := by omega
    simp only [hnl, ↓reduceIte, show q + t % q - q = t % q by omega] at this
    rw [periodic_mod (fun t => heldOrbit u t (m + 1)) q (fun t => (per m).2 t) t,
      periodic_mod (fun t => heldOrbit u t (n + 1)) q (fun t => (per n).2 t) t]
    exact this
  have step : ∀ i, (∀ t, heldOrbit u t (m + i) = heldOrbit u t (n + i)) ∧
      (∀ t, heldOrbit u t (m + i + 1) = heldOrbit u t (n + i + 1)) := by
    intro i
    induction i with
    | zero => exact ⟨h0, h1⟩
    | succ i ih =>
      refine ⟨ih.2, fun t => ?_⟩
      have e1 := heldOrbit_sideways u t (m + i)
      have e2 := heldOrbit_sideways u t (n + i)
      rw [show m + (i + 1) + 1 = m + i + 2 by omega, show n + (i + 1) + 1 = n + i + 2 by omega, e1, e2,
        ih.2 (t + 1), ih.2 t, ih.1 t]
  refine ⟨m, n - m, by omega, fun k hk => ?_⟩
  obtain ⟨i, rfl⟩ : ∃ i, k = m + i := ⟨k - m, by omega⟩
  have := (step i).1 0
  show heldOrbit u 0 (m + i + (n - m)) = heldOrbit u 0 (m + i)
  rw [show m + i + (n - m) = n + i by omega]
  exact this.symm

/-- A point of `InK` whose itinerary has period `n` has the cell next to the column periodic with period `2 n`. -/
theorem column_periodic_of_itinerary (u : Nat → Bool) (hu : InK u) (n : Nat)
    (hn : ∀ s, itinerary u (s + n) = itinerary u s) : ∀ t, heldOrbit u (t + 2 * n) 0 = heldOrbit u t 0 := by
  intro t
  rcases parity t with ⟨s, hs⟩ | ⟨s, hs⟩
  · have := hn s
    unfold itinerary at this
    rw [hs, show 2 * s + 2 * n = 2 * (s + n) by omega]
    exact this
  · rw [hs, show 2 * s + 1 + 2 * n = 2 * (s + n) + 1 by omega, hu, hu]

/-- **A point of `InK` with a periodic itinerary is an eventually periodic sequence**: a 2-adic rational. -/
theorem inK_periodic_rational (u : Nat → Bool) (hu : InK u) (n : Nat) (hn0 : 0 < n)
    (hn : ∀ s, itinerary u (s + n) = itinerary u s) :
    ∃ pre per, 0 < per ∧ ∀ k, pre ≤ k → u (k + per) = u k :=
  eventually_periodic_of_column_periodic u (2 * n) (by omega) (column_periodic_of_itinerary u hu n hn)

/-! ### Periodic points have no finite support -/

/-- `u` has its last 1 at `m`. -/
def TopBit (u : Nat → Bool) (m : Nat) : Prop := u m = true ∧ ∀ j, m < j → u j = false

theorem held_topBit (u : Nat → Bool) (m : Nat) (h : TopBit u m) : TopBit (held u) (m + 1) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, fun j hj => ?_⟩
  · show xor (u (m + 2)) (u (m + 1) || u m) = true
    rw [h2 (m + 2) (by omega), h2 (m + 1) (by omega), h1]; rfl
  · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    show xor (u (j' + 2)) (u (j' + 1) || u j') = false
    rw [h2 (j' + 2) (by omega), h2 (j' + 1) (by omega), h2 j' (by omega)]; rfl

/-- The last 1 of a half moves one cell out at every step of `held`. -/
theorem heldOrbit_topBit (u : Nat → Bool) (m : Nat) (h : TopBit u m) : ∀ k, TopBit (heldOrbit u k) (m + k) := by
  intro k
  induction k with
  | zero => exact h
  | succ k ih => exact held_topBit _ _ ih

theorem inK_heldOrbit (u : Nat → Bool) (hu : InK u) (a : Nat) : InK (heldOrbit u (2 * a)) := fun s => by
  show heldOrbit (heldOrbit u (2 * a)) (2 * s + 1) 0 = true
  rw [heldOrbit_add, show 2 * a + (2 * s + 1) = 2 * (s + a) + 1 by omega]
  exact hu (s + a)

theorem itinerary_heldOrbit (u : Nat → Bool) (a s : Nat) :
    itinerary (heldOrbit u (2 * a)) s = itinerary u (s + a) := by
  show heldOrbit (heldOrbit u (2 * a)) (2 * s) 0 = heldOrbit u (2 * (s + a)) 0
  rw [heldOrbit_add, show 2 * a + 2 * s = 2 * (s + a) by omega]

/-- A point of `InK` with a periodic itinerary is fixed by `held` iterated `2 n` times. -/
theorem heldOrbit_fixed_of_periodic (v : Nat → Bool) (hv : InK v) (n : Nat)
    (hn : ∀ s, itinerary v (s + n) = itinerary v s) : heldOrbit v (2 * n) = v := by
  refine itinerary_injective _ _ (inK_heldOrbit v hv n) hv (funext fun s => ?_)
  rw [itinerary_heldOrbit]
  exact hn s

/-- **No point of `InK` with a periodic itinerary has finitely many 1s.** -/
theorem inK_periodic_not_finite (v : Nat → Bool) (hv : InK v) (n : Nat) (hn0 : 0 < n)
    (hn : ∀ s, itinerary v (s + n) = itinerary v s) (m : Nat) (hm : TopBit v m) : False := by
  have fix := heldOrbit_fixed_of_periodic v hv n hn
  have top := (heldOrbit_topBit v m hm (2 * n)).1
  rw [fix] at top
  rw [hm.2 (m + 2 * n) (by omega)] at top
  exact Bool.false_ne_true top

/-- **A point of `InK` with finitely many 1s has an itinerary that is not eventually periodic.** -/
theorem inK_finite_not_preperiodic (u : Nat → Bool) (hu : InK u) (m : Nat) (hm : TopBit u m) :
    ¬ ∃ pre n, 0 < n ∧ ∀ s, pre ≤ s → itinerary u (s + n) = itinerary u s := by
  rintro ⟨pre, n, hn0, hn⟩
  refine inK_periodic_not_finite (heldOrbit u (2 * pre)) (inK_heldOrbit u hu pre) n hn0 (fun s => ?_) (m + 2 * pre)
    (heldOrbit_topBit u m hm (2 * pre))
  rw [itinerary_heldOrbit, itinerary_heldOrbit, show s + n + pre = s + pre + n by omega]
  exact hn (s + pre) (by omega)

/-- **Positive integers.** If `U > 0` is odd at every odd step of `heldNat`, the itinerary of its bits is not
eventually periodic. -/
theorem positive_integer_not_preperiodic (U : Nat) (hU : 0 < U)
    (hK : ∀ s, Nat.repeat heldNat (2 * s + 1) U % 2 = 1) :
    ¬ ∃ pre n, 0 < n ∧ ∀ s, pre ≤ s →
      itinerary (fun i => U.testBit i) (s + n) = itinerary (fun i => U.testBit i) s := by
  refine inK_finite_not_preperiodic (fun i => U.testBit i) (fun s => ?_) U.log2 ⟨?_, fun j hj => ?_⟩
  · have := heldNat_repeat_testBit U (2 * s + 1) 0
    rw [Nat.testBit_zero] at this
    have h2 := hK s
    rw [h2] at this
    simpa using this.symm
  · exact Nat.testBit_log2 (by omega)
  · exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le Nat.lt_log2_self (Nat.pow_le_pow_right (by omega) (by omega)))

end Rule30Open
