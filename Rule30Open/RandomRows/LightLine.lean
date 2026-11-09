module

public import Rule30Open.Foundations.Evolve

/-!
# The light-like map of Rule 30 on half-lines: one preimage after `010`, and right diagonals avoid `00100`

The light-like map is Rule 30 in the frame that moves one cell right per step,
`(G y)_i = y_i xor (y_{i+1} or y_{i+2})` (`light`). It reads only the cell itself and the cells to its
right, so it acts on half-lines `ℕ → Bool`.

* `eq_true_of_window`: if `G y` reads `0 1 0` at `q, q + 1, q + 2`, then `y_q = 1`; with the image
  this fixes `y_{q-1}`, and then every cell left of `q`.
* `eq_of_light_eq_of_window`, `eq_of_light_eq_of_frequently`: **two half-lines with the same image
  agree left of every `010` of the image, so they are equal if the image shows `010` arbitrarily far
  to the right.** Almost every half-line does (Borel's normal number theorem, the kit's
  `RandomConfigurations.ae_isNormal`), so `G` is injective on a set of full measure: the light-like
  map is invertible almost everywhere, and therefore not exact.
* `light_iterate_cell`: the light-like map is Rule 30 read along right diagonals: the cell `j` of
  `G^r u`, for the half-line `u_j = evolve init t (i + j)`, is `evolve init (t + r) (i + r + j)`.
* `lightLine_avoids`, `diag_avoids`: **no right diagonal of any space-time diagram of Rule 30 reads
  `0 0 1 0 0` or `1 1 0 1 1`**: the cells `(t + r, i + r)`, `r = 0, …, 4`, never read `b b ¬b b b`.
  So the light line `t ↦ (G^t y)_0` of every half-line, a sequence of fair coins under the uniform
  measure at each time, is not normal for any half-line, and the words it shows grow more slowly
  than `2^n`.

The natural-language argument is `LightLine.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

/-- The light-like map `G = σF` on half-lines: `(G y)_i = y_i xor (y_{i+1} or y_{i+2})`. -/
def LightLine.light (y : Nat → Bool) : Nat → Bool := fun i => xor (y i) (y (i + 1) || y (i + 2))

/-! ### One preimage after `010` -/

/-- **`010` in the image forces a black cell**: if `G y` reads `0 1 0` at `q, q + 1, q + 2`, then
`y_q = 1`. -/
theorem LightLine.eq_true_of_window {y : Nat → Bool} {q : Nat} (h0 : light y q = false)
    (h1 : light y (q + 1) = true) (h2 : light y (q + 2) = false) : y q = true := by
  simp only [light] at h0 h1 h2
  rw [show q + 1 + 1 = q + 2 by omega, show q + 1 + 2 = q + 3 by omega] at h1
  rw [show q + 2 + 1 = q + 3 by omega, show q + 2 + 2 = q + 4 by omega] at h2
  revert h0 h1 h2
  cases y q <;> cases y (q + 1) <;> cases y (q + 2) <;> cases y (q + 3) <;> cases y (q + 4) <;> decide

/-- Left of two agreeing adjacent cells, two half-lines with the same image agree. -/
theorem LightLine.eq_of_light_eq_down {y y' : Nat → Bool} (h : light y = light y') {k : Nat}
    (hk : y k = y' k) (hk1 : y (k + 1) = y' (k + 1)) : ∀ i, i ≤ k + 1 → y i = y' i := by
  have step : ∀ n : Nat, n ≤ k → y (k - n) = y' (k - n) ∧ y (k - n + 1) = y' (k - n + 1) := by
    intro n
    induction n with
    | zero => intro _; simpa using ⟨hk, hk1⟩
    | succ n ih =>
      intro hn
      have ih' := ih (by omega)
      have e := congrFun h (k - (n + 1))
      simp only [light] at e
      rw [show k - (n + 1) + 1 = k - n by omega, show k - (n + 1) + 2 = k - n + 1 by omega,
        ih'.1, ih'.2] at e
      refine ⟨?_, ?_⟩
      · revert e
        cases y (k - (n + 1)) <;> cases y' (k - (n + 1)) <;> cases y' (k - n) <;>
          cases y' (k - n + 1) <;> decide
      · rw [show k - (n + 1) + 1 = k - n by omega]
        exact ih'.1
  intro i hi
  by_cases hik : i = k + 1
  · subst hik; exact hk1
  · have := (step (k - i) (by omega)).1
    rwa [show k - (k - i) = i by omega] at this

/-- **Two preimages of an image showing `010` at `q` agree on the cells `0, …, q`.** -/
theorem LightLine.eq_of_light_eq_of_window {y y' : Nat → Bool} (h : light y = light y') {q : Nat}
    (h0 : light y q = false) (h1 : light y (q + 1) = true) (h2 : light y (q + 2) = false) :
    ∀ i, i ≤ q → y i = y' i := by
  have hq : y q = true := eq_true_of_window h0 h1 h2
  have hq' : y' q = true := eq_true_of_window (h ▸ h0) (h ▸ h1) (h ▸ h2)
  intro i hi
  cases q with
  | zero =>
    have : i = 0 := by omega
    subst this; rw [hq, hq']
  | succ p =>
    -- the cell `p` is the complement of the image at `p`, in both preimages
    have ep := congrFun h p
    simp only [light] at ep
    have hp : y p = y' p := by
      have e1 : y (p + 1) = true := hq
      have e2 : y' (p + 1) = true := hq'
      rw [e1, e2] at ep
      revert ep
      cases y p <;> cases y' p <;> cases y (p + 2) <;> cases y' (p + 2) <;> decide
    exact eq_of_light_eq_down h hp (by rw [hq, hq']) i (by omega)

/-- **The light-like map is injective on half-lines whose image shows `010` arbitrarily far to the
right.** -/
theorem LightLine.eq_of_light_eq_of_frequently {y y' : Nat → Bool} (h : light y = light y')
    (hf : ∀ n : Nat, ∃ q, n ≤ q ∧ light y q = false ∧ light y (q + 1) = true ∧
      light y (q + 2) = false) : y = y' := by
  funext i
  obtain ⟨q, hq, h0, h1, h2⟩ := hf i
  exact eq_of_light_eq_of_window h h0 h1 h2 i hq

/-! ### Right diagonals of Rule 30 -/

/-- `t` steps of the light-like map. -/
def LightLine.lightIter : Nat → (Nat → Bool) → (Nat → Bool)
  | 0, y => y
  | t + 1, y => light (lightIter t y)

theorem LightLine.lightIter_add (y : Nat → Bool) (t : Nat) : ∀ r : Nat, lightIter (t + r) y = lightIter r (lightIter t y)
  | 0 => rfl
  | r + 1 => by
    show light (lightIter (t + r) y) = light (lightIter r (lightIter t y))
    rw [lightIter_add y t r]

/-- **The light-like map reads Rule 30 along right diagonals**: for the half-line
`u_j = evolve init t (i + j)`, the cell `j` of `G^r u` is `evolve init (t + r) (i + r + j)`. -/
theorem LightLine.lightIter_cell (init : Int → Bool) (t : Nat) (i : Int) :
    ∀ (r j : Nat), lightIter r (fun j : Nat => evolve init t (i + j)) j =
      evolve init (t + r) (i + r + j)
  | 0, j => by simp [lightIter]
  | r + 1, j => by
    show xor (lightIter r _ j) (lightIter r _ (j + 1) || lightIter r _ (j + 2)) = _
    rw [lightIter_cell init t i r j, lightIter_cell init t i r (j + 1),
      lightIter_cell init t i r (j + 2)]
    show _ = rule30 (evolve init (t + r) (i + ((r + 1 : Nat) : Int) + j - 1))
      (evolve init (t + r) (i + ((r + 1 : Nat) : Int) + j))
      (evolve init (t + r) (i + ((r + 1 : Nat) : Int) + j + 1))
    have a : i + ((r + 1 : Nat) : Int) + j - 1 = i + r + j := by omega
    have b : i + ((r + 1 : Nat) : Int) + j = i + r + ((j + 1 : Nat) : Int) := by omega
    have c : i + ((r + 1 : Nat) : Int) + j + 1 = i + r + ((j + 2 : Nat) : Int) := by omega
    rw [a, c, b]
    rfl

/-- The finite core: from any half-line, the cells `0` of `y, G y, …, G^4 y` never read
`b b ¬b b b`. They depend on the cells `0, …, 8` of `y`, and the `1024` cases run in the kernel. -/
theorem LightLine.lightLine_avoids_zero (y : Nat → Bool) (b : Bool) :
    ¬ (y 0 = b ∧ lightIter 1 y 0 = b ∧ lightIter 2 y 0 = !b ∧ lightIter 3 y 0 = b ∧
      lightIter 4 y 0 = b) := by
  simp only [lightIter, light]
  cases b <;> cases y 0 <;> cases y 1 <;> cases y 2 <;> cases y 3 <;> cases y 4 <;> cases y 5 <;>
    cases y 6 <;> cases y 7 <;> cases y 8 <;> decide

/-- **The light line avoids `00100` and `11011`**: for every half-line `y` and time `t`, the cells
`(G^t y)_0, …, (G^{t+4} y)_0` never read `b b ¬b b b`. -/
theorem LightLine.lightLine_avoids (y : Nat → Bool) (t : Nat) (b : Bool) :
    ¬ (lightIter t y 0 = b ∧ lightIter (t + 1) y 0 = b ∧ lightIter (t + 2) y 0 = !b ∧
      lightIter (t + 3) y 0 = b ∧ lightIter (t + 4) y 0 = b) := by
  rw [lightIter_add y t 1, lightIter_add y t 2, lightIter_add y t 3, lightIter_add y t 4]
  exact lightLine_avoids_zero (lightIter t y) b

/-- **No right diagonal of Rule 30 reads `00100` or `11011`**: for every row, time and cell, the
cells `(t + r, i + r)`, `r = 0, …, 4`, never read `b b ¬b b b`. -/
theorem LightLine.diag_avoids (init : Int → Bool) (t : Nat) (i : Int) (b : Bool) :
    ¬ (evolve init t i = b ∧ evolve init (t + 1) (i + 1) = b ∧ evolve init (t + 2) (i + 2) = !b ∧
      evolve init (t + 3) (i + 3) = b ∧ evolve init (t + 4) (i + 4) = b) := by
  have h := lightLine_avoids_zero (fun j : Nat => evolve init t (i + j)) b
  have c : ∀ r : Nat, lightIter r (fun j : Nat => evolve init t (i + j)) 0 =
      evolve init (t + r) (i + r) := fun r => by
    rw [lightIter_cell]; simp
  rw [c 1, c 2, c 3, c 4] at h
  simpa using h

/-- The single seed's right diagonals are no exception. -/
example (t : Nat) (i : Int) : ¬ (evolve single t i = false ∧ evolve single (t + 1) (i + 1) = false ∧
    evolve single (t + 2) (i + 2) = true ∧ evolve single (t + 3) (i + 3) = false ∧
    evolve single (t + 4) (i + 4) = false) := LightLine.diag_avoids single t i false

end Rule30Open
