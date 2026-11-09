module

/-!
# Rule 180 at the speed of light: each light line is constant where the next one is white

Rule 180 is the left-permutive elementary rule `F(x)_i = x_{i-1} xor (x_i and not x_{i+1})`, a sibling of
Rule 30 (`x_{i-1} xor (x_i or x_{i+1})`). Its light-like map on half-lines is
`(H y)_i = y_i xor (y_{i+1} and not y_{i+2})` (`step`), and the light line `j` of a half-line `y` is
`t ↦ (H^t y)_j` (`line y j t`). Line `j` changes between `t` and `t + 1` exactly when lines `j + 1` and
`j + 2` read `1 0` at `t` (`line_succ`).

* `const_on_zeros`: **line `j` takes the same value at any two times at which line `j + 1` is white.**
  By strong induction on the distance `n` of the two times, together with `no_zero_between`: between two
  consecutive white times `a < a + n` of line `j + 1`, line `j + 2` is black at every time strictly between
  `a` and `a + n - 1`.
* `pair_dichotomy`: so on every time interval lines `1` and `2` never read both `1 0` and `0 0`.

On paper this decides the light-like map of Rule 180 under the uniform measure `λ`: with `a_T` the probability
that line `0` is constant up to time `T`, flipping cell `1` exchanges the two halves of `pair_dichotomy`,
whose intersection is `line 2 ≡ 1`, so `2 a_T - a_{T-1}/2 = 1` and `a_T = 2/3 + 4^{-T}/3`. The set of
half-lines whose light line `0` is constant is invariant and has measure `2/3`: **the light-like map of Rule 180
is not ergodic**, although it has the shape of Rule 30's (permutive in its own cell, nonlinear in the two to its
right).

The natural-language argument is `LightLike180.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

/-- The light-like map of Rule 180 on half-lines: `(H y)_i = y_i xor (y_{i+1} and not y_{i+2})`. -/
def LightLike180.step (y : Nat → Bool) : Nat → Bool := fun i => xor (y i) (y (i + 1) && !y (i + 2))

/-- `t` steps of `step`. -/
def LightLike180.iter : Nat → (Nat → Bool) → (Nat → Bool)
  | 0, y => y
  | t + 1, y => step (iter t y)

/-- The light line `j` of `y`: its cell `j` at time `t`. -/
def LightLike180.line (y : Nat → Bool) (j t : Nat) : Bool := iter t y j

/-! A spot check against the rule's code, so a slip in the definition would show: `step` applies
`l xor (c and not r)` to the cell and its two right neighbors, which is Wolfram's code 180
(1 0 1 1 0 1 0 0 on the neighborhoods 111, 110, ..., 000). -/

example : (List.map (fun (v : Bool × Bool × Bool) => xor v.1 (v.2.1 && !v.2.2))
    [(true, true, true), (true, true, false), (true, false, true), (true, false, false),
     (false, true, true), (false, true, false), (false, false, true), (false, false, false)]) =
    [true, false, true, true, false, true, false, false] := by decide

theorem LightLike180.line_succ (y : Nat → Bool) (j t : Nat) :
    line y j (t + 1) = xor (line y j t) (line y (j + 1) t && !line y (j + 2) t) := rfl

/-- Line `j` changes at `t` exactly when lines `j + 1`, `j + 2` read `1 0` at `t`. -/
theorem LightLike180.flip_iff (y : Nat → Bool) (j t : Nat) :
    line y j (t + 1) ≠ line y j t ↔ (line y (j + 1) t = true ∧ line y (j + 2) t = false) := by
  rw [line_succ]
  cases line y j t <;> cases line y (j + 1) t <;> cases line y (j + 2) t <;> decide

/-- A line that does not change on `[a, a + n)` has the same value at `a` and `a + n`. -/
theorem LightLike180.const_of_no_flip (y : Nat → Bool) (j a : Nat) :
    ∀ n : Nat, (∀ s, a ≤ s → s < a + n → line y j (s + 1) = line y j s) → line y j (a + n) = line y j a
  | 0, _ => rfl
  | n + 1, h => by
    rw [show a + (n + 1) = (a + n) + 1 by omega, h (a + n) (by omega) (by omega)]
    exact const_of_no_flip y j a n fun s h1 h2 => h s h1 (by omega)

/-- The statement `P n`: two white times of line `j + 1` at distance `n` give line `j` equal values. -/
def LightLike180.P (y : Nat → Bool) (n : Nat) : Prop :=
  ∀ j a, line y (j + 1) a = false → line y (j + 1) (a + n) = false → line y j (a + n) = line y j a

/-- The statement `Q n`: if line `j + 1` is white at `a` and `a + n` and black in between, line `j + 2` is black
strictly between `a` and `a + n - 1`. -/
def LightLike180.Q (y : Nat → Bool) (n : Nat) : Prop :=
  ∀ j a, line y (j + 1) a = false → line y (j + 1) (a + n) = false →
    (∀ s, a < s → s < a + n → line y (j + 1) s = true) → ∀ s, a < s → s + 1 < a + n → line y (j + 2) s = true

theorem LightLike180.Q_step (y : Nat → Bool) (n : Nat) (hP : ∀ m, m < n → P y m) (hQ : ∀ m, m < n → Q y m) : Q y n := by
  intro j a ha hb hin s hs1 hs2
  -- line `j + 1` changes at `a + n - 1`, so lines `j + 2`, `j + 3` read `1 0` there
  have hn : 2 ≤ n := by omega
  have hb1 : line y (j + 1) (a + n - 1) = true := hin (a + n - 1) (by omega) (by omega)
  have fb := (flip_iff y (j + 1) (a + n - 1)).1 (by
    rw [show a + n - 1 + 1 = a + n by omega, hb, hb1]; decide)
  -- and at `a`
  have fa := (flip_iff y (j + 1) a).1 (by rw [ha, hin (a + 1) (by omega) (by omega)]; decide)
  -- line `j + 1` does not change strictly between `a` and `a + n - 1`
  have noflip : ∀ r, a < r → r + 1 < a + n → ¬ (line y (j + 2) r = true ∧ line y (j + 3) r = false) := by
    intro r h1 h2 hf
    have := (flip_iff y (j + 1) r).2 hf
    rw [hin r h1 (by omega), hin (r + 1) (by omega) (by omega)] at this
    exact this rfl
  -- line `j + 3` is black strictly between `a` and `a + n - 1`: a white time there would carry, by `P`,
  -- the value `1` of line `j + 2` at `a`, and lines `j + 2`, `j + 3` would read `1 0`
  have h3 : ∀ r, a < r → r + 1 < a + n → line y (j + 3) r = true := by
    intro r h1 h2
    cases h : line y (j + 3) r with
    | true => rfl
    | false =>
      exfalso
      have e := hP (r - a) (by omega) (j + 2) a fa.2 (by rw [show a + (r - a) = r by omega]; exact h)
      rw [show a + (r - a) = r by omega, fa.1] at e
      exact noflip r h1 h2 ⟨e, h⟩
  -- line `j + 2` does not change on `[a, a + n - 2)`: at `a` line `j + 3` is white, and inside, by `Q (n - 1)`,
  -- line `j + 4` is black
  have hq : ∀ r, a < r → r + 2 < a + n → line y (j + 4) r = true := by
    intro r h1 h2
    have hb3 : line y (j + 2 + 1) (a + (n - 1)) = false := by
      rw [show a + (n - 1) = a + n - 1 by omega]; exact fb.2
    exact hQ (n - 1) (by omega) (j + 2) a fa.2 hb3 (fun r' h1' h2' => h3 r' h1' (by omega)) r h1 (by omega)
  have nf : ∀ r, a ≤ r → r < a + (s - a) → line y (j + 2) (r + 1) = line y (j + 2) r := by
    intro r h1 h2
    cases Classical.em (line y (j + 2) (r + 1) = line y (j + 2) r) with
    | inl e => exact e
    | inr e =>
      have hf := (flip_iff y (j + 2) r).1 e
      by_cases hr : r = a
      · subst hr; rw [fa.2] at hf; exact absurd hf.1 (by decide)
      · rw [hq r (by omega) (by omega)] at hf; exact absurd hf.2 (by decide)
  have := const_of_no_flip y (j + 2) a (s - a) nf
  rw [show a + (s - a) = s by omega, fa.1] at this
  exact this

theorem LightLike180.P_step (y : Nat → Bool) (n : Nat) (hP : ∀ m, m < n → P y m) (hQ : Q y n) : P y n := by
  intro j a ha hb
  cases Classical.em (∃ s, a < s ∧ s < a + n ∧ line y (j + 1) s = false) with
  | inl hex =>
    obtain ⟨s, h1, h2, hs⟩ := hex
    have e1 := hP (s - a) (by omega) j a ha (by rw [show a + (s - a) = s by omega]; exact hs)
    have e2 := hP (a + n - s) (by omega) j s hs (by rw [show s + (a + n - s) = a + n by omega]; exact hb)
    rw [show a + (s - a) = s by omega] at e1
    rw [show s + (a + n - s) = a + n by omega] at e2
    rw [e2, e1]
  | inr hno =>
    have hin : ∀ s, a < s → s < a + n → line y (j + 1) s = true := by
      intro s h1 h2
      cases h : line y (j + 1) s with
      | true => rfl
      | false => exact absurd ⟨s, h1, h2, h⟩ hno
    apply const_of_no_flip y j a n
    intro r h1 h2
    cases Classical.em (line y j (r + 1) = line y j r) with
    | inl e => exact e
    | inr e =>
      exfalso
      have hf := (flip_iff y j r).1 e
      by_cases hr : r = a
      · subst hr; rw [ha] at hf; exact absurd hf.1 (by decide)
      · by_cases hlast : r + 1 = a + n
        · -- line `j + 1` changes at `r = a + n - 1`, so line `j + 2` is black there
          have fb := (flip_iff y (j + 1) r).1 (by rw [hlast, hb, hin r (by omega) (by omega)]; decide)
          rw [fb.1] at hf; exact absurd hf.2 (by decide)
        · rw [hQ j a ha hb hin r (by omega) (by omega)] at hf; exact absurd hf.2 (by decide)

theorem LightLike180.PQ (y : Nat → Bool) : ∀ n, (∀ m, m ≤ n → P y m) ∧ (∀ m, m ≤ n → Q y m)
  | 0 => by
    refine ⟨fun m hm => ?_, fun m hm => ?_⟩
    · have : m = 0 := by omega
      subst this; intro j a _ _; rfl
    · have : m = 0 := by omega
      subst this; intro j a _ _ _ s h1 h2; omega
  | n + 1 => by
    obtain ⟨ihP, ihQ⟩ := PQ y n
    have hQ : Q y (n + 1) := Q_step y (n + 1) (fun m hm => ihP m (by omega)) (fun m hm => ihQ m (by omega))
    have hP : P y (n + 1) := P_step y (n + 1) (fun m hm => ihP m (by omega)) hQ
    refine ⟨fun m hm => ?_, fun m hm => ?_⟩
    · by_cases h : m = n + 1
      · subst h; exact hP
      · exact ihP m (by omega)
    · by_cases h : m = n + 1
      · subst h; exact hQ
      · exact ihQ m (by omega)

/-- **Each light line of Rule 180 is constant on the white times of the next one.** -/
theorem LightLike180.const_on_zeros (y : Nat → Bool) (j a b : Nat) (hab : a ≤ b) (ha : line y (j + 1) a = false)
    (hb : line y (j + 1) b = false) : line y j a = line y j b := by
  have := (PQ y (b - a)).1 (b - a) (Nat.le_refl _) j a ha (by rw [show a + (b - a) = b by omega]; exact hb)
  rw [show a + (b - a) = b by omega] at this
  exact this.symm

/-- **Between consecutive white times of line `j + 1`, line `j + 2` is black.** -/
theorem LightLike180.no_zero_between (y : Nat → Bool) (j a n : Nat) (ha : line y (j + 1) a = false)
    (hb : line y (j + 1) (a + n) = false) (hin : ∀ s, a < s → s < a + n → line y (j + 1) s = true) :
    ∀ s, a < s → s + 1 < a + n → line y (j + 2) s = true :=
  (PQ y n).2 n (Nat.le_refl _) j a ha hb hin

/-- **On every time interval, lines `j + 1` and `j + 2` never read both `1 0` and `0 0`.** -/
theorem LightLike180.pair_dichotomy (y : Nat → Bool) (j T : Nat) :
    (∀ t, t < T → ¬ (line y (j + 1) t = true ∧ line y (j + 2) t = false)) ∨
      (∀ t, t < T → ¬ (line y (j + 1) t = false ∧ line y (j + 2) t = false)) := by
  cases Classical.em (∃ t, t < T ∧ line y (j + 1) t = true ∧ line y (j + 2) t = false) with
  | inr h => exact Or.inl fun t ht hf => h ⟨t, ht, hf⟩
  | inl h =>
    obtain ⟨t, _, h1, h2⟩ := h
    refine Or.inr fun t' _ hf => ?_
    have := (if hle : t ≤ t' then const_on_zeros y (j + 1) t t' hle h2 hf.2
      else (const_on_zeros y (j + 1) t' t (by omega) hf.2 h2).symm)
    rw [h1, hf.1] at this
    exact absurd this (by decide)

/-- Line `j` is constant up to `T` exactly when lines `j + 1`, `j + 2` never read `1 0` before `T`. -/
theorem LightLike180.line_const_iff (y : Nat → Bool) (j T : Nat) :
    (∀ t, t ≤ T → line y j t = line y j 0) ↔
      ∀ t, t < T → ¬ (line y (j + 1) t = true ∧ line y (j + 2) t = false) := by
  constructor
  · intro h t ht hf
    have := (flip_iff y j t).2 hf
    rw [h (t + 1) (by omega), h t (by omega)] at this
    exact this rfl
  · intro h t ht
    have := const_of_no_flip y j 0 t (fun s _ h2 => by
      cases Classical.em (line y j (s + 1) = line y j s) with
      | inl e => exact e
      | inr e => exact absurd ((flip_iff y j s).1 e) (h s (by omega)))
    rwa [Nat.zero_add] at this

end Rule30Open
