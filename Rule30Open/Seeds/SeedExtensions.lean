module

public import Rule30Open.Foundations.Evolve
public import Rule30Open.Foundations.Official

/-!
# Seeds that keep the center column

For every `k`, the seeds (10)^k 1 (`sigma k`) and (10)^k 11 (`tau k`) give exactly the single seed's
center column (`center_sigma`, `center_tau`): each evolves like the single seed at every cell left of
`t` (`sigma_agrees`, `tau_agrees`), and the rows differ exactly where `sigma_difference` and
`tau_difference` say. The seed 11 is `tau 0` (`eleven`, `center_column`, `difference`).

The proof follows the right edge. Read from cell `t - 2` rightward, with 0s beyond, each row is a
window fixed by the parity of `t`, and one step of the rule takes each window to the other, one cell
further right (`sigma_step`, `sigmaOdd_step`, `tau_step`, `tauOdd_step`, each for every `k`). Every
window starts 0 0 at even `t` and 1 1 at odd `t`, as the single seed's does, so the cells left of
`t - 2` agree for all time (`Windows.agree`).

The natural-language argument is `SeedExtensions.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

open Ruliology.CellularAutomata

/-- The seed 11: 1 at cells 0 and 1. -/
def seed11 (x : Int) : Bool := decide (x = 0 ∨ x = 1)

/-- The seed (10)^k 1, 1 at the even cells 0 to 2k. Read at the offset `x - t`, it is also the row from it at every
even `t`, from cell `t - 2` on. -/
def sigma (k : Nat) (x : Int) : Bool := decide (0 ≤ x ∧ x ≤ 2 * (k : Int) ∧ x % 2 = 0)

/-- The row from `sigma k` at odd `t`, at the offset `o` from `t` (from `o = -2` on): 1 1 0 (1 0)^(k-1) 1 1, or 1 1 1
at k = 0. -/
def sigmaOdd (k : Nat) (o : Int) : Bool :=
  decide (o = -2 ∨ o = -1 ∨ (1 ≤ o ∧ o ≤ 2 * (k : Int) - 1 ∧ o % 2 = 1) ∨ o = 2 * (k : Int))

/-- The seed (10)^k 11, 1 at the even cells 0 to 2k and at 2k + 1; also its row at every even `t`. -/
def tau (k : Nat) (x : Int) : Bool := decide ((0 ≤ x ∧ x ≤ 2 * (k : Int) ∧ x % 2 = 0) ∨ x = 2 * (k : Int) + 1)

/-- The row from `tau k` at odd `t`, at the offset `o` from `t` (from `o = -2` on): 1 1 0 (1 0)^k 1. -/
def tauOdd (k : Nat) (o : Int) : Bool := decide (o = -2 ∨ o = -1 ∨ (1 ≤ o ∧ o ≤ 2 * (k : Int) + 1 ∧ o % 2 = 1))

/-! Spot checks: `sigma 2` and `tau 1` are the seeds 10101 and 1011, and the row from 1011 at t = 3 reads its odd
window 1 1 0 1 0 1 0 from cell t - 2. -/

example : (List.range 7).map (fun i : Nat => sigma 2 ((i : Int) - 1)) =
    [false, true, false, true, false, true, false] := by decide

example : (List.range 6).map (fun i : Nat => tau 1 ((i : Int) - 1)) = [false, true, false, true, true, false] := by
  decide

example : (List.range 7).map (fun i : Nat => evolve (tau 1) 3 ((i : Int) + 1)) =
    [true, true, false, true, false, true, false] := by decide

/-! One step of the rule maps each window to the other, read one cell further right, for every `k`. Each proof
splits on the four cells involved and lets `omega` refute the combinations that cannot occur. -/

theorem sigma_step (k : Nat) (o : Int) (ho : -1 ≤ o) :
    rule30 (sigma k (o - 1)) (sigma k o) (sigma k (o + 1)) = sigmaOdd k (o - 1) := by
  cases h1 : sigma k (o - 1) <;> cases h2 : sigma k o <;> cases h3 : sigma k (o + 1) <;>
    cases h4 : sigmaOdd k (o - 1) <;>
    simp only [sigma, sigmaOdd, decide_eq_true_eq, decide_eq_false_iff_not] at h1 h2 h3 h4 <;>
    first | rfl | omega

theorem sigmaOdd_step (k : Nat) (o : Int) (ho : -1 ≤ o) :
    rule30 (sigmaOdd k (o - 1)) (sigmaOdd k o) (sigmaOdd k (o + 1)) = sigma k (o - 1) := by
  cases h1 : sigmaOdd k (o - 1) <;> cases h2 : sigmaOdd k o <;> cases h3 : sigmaOdd k (o + 1) <;>
    cases h4 : sigma k (o - 1) <;>
    simp only [sigma, sigmaOdd, decide_eq_true_eq, decide_eq_false_iff_not] at h1 h2 h3 h4 <;>
    first | rfl | omega

theorem tau_step (k : Nat) (o : Int) (ho : -1 ≤ o) :
    rule30 (tau k (o - 1)) (tau k o) (tau k (o + 1)) = tauOdd k (o - 1) := by
  cases h1 : tau k (o - 1) <;> cases h2 : tau k o <;> cases h3 : tau k (o + 1) <;>
    cases h4 : tauOdd k (o - 1) <;>
    simp only [tau, tauOdd, decide_eq_true_eq, decide_eq_false_iff_not] at h1 h2 h3 h4 <;>
    first | rfl | omega

theorem tauOdd_step (k : Nat) (o : Int) (ho : -1 ≤ o) :
    rule30 (tauOdd k (o - 1)) (tauOdd k o) (tauOdd k (o + 1)) = tau k (o - 1) := by
  cases h1 : tauOdd k (o - 1) <;> cases h2 : tauOdd k o <;> cases h3 : tauOdd k (o + 1) <;>
    cases h4 : tau k (o - 1) <;>
    simp only [tau, tauOdd, decide_eq_true_eq, decide_eq_false_iff_not] at h1 h2 h3 h4 <;>
    first | rfl | omega

/-- A seed whose rows read the window `W0` from cell `t - 2` at even `t` and `W1` at odd `t` (as functions of the
offset from `t`): the seed itself reads `W0` from cell -2 with 0s left of it, one step takes each window to the
other, and the windows hold the single seed's values at offsets -2 and -1. -/
structure Windows (seed W0 W1 : Int → Bool) : Prop where
  start : ∀ x : Int, -2 ≤ x → seed x = W0 x
  zeros : ∀ x : Int, x < -2 → seed x = false
  step0 : ∀ o : Int, -1 ≤ o → rule30 (W0 (o - 1)) (W0 o) (W0 (o + 1)) = W1 (o - 1)
  step1 : ∀ o : Int, -1 ≤ o → rule30 (W1 (o - 1)) (W1 o) (W1 (o + 1)) = W0 (o - 1)
  low0 : W0 (-2) = false ∧ W0 (-1) = false
  low1 : W1 (-2) = true ∧ W1 (-1) = true

/-- If the row at `t` reads `W` from cell `t - 2`, the row at `t + 1` reads the window a step lemma gives. -/
theorem window_step {init W W' : Int → Bool} {t : Nat}
    (hW : ∀ x : Int, (t : Int) - 2 ≤ x → evolve init t x = W (x - t))
    (hstep : ∀ o : Int, -1 ≤ o → rule30 (W (o - 1)) (W o) (W (o + 1)) = W' (o - 1)) :
    ∀ x : Int, ((t + 1 : Nat) : Int) - 2 ≤ x → evolve init (t + 1) x = W' (x - ((t + 1 : Nat) : Int)) := by
  intro x hx
  have h1 := hW (x - 1) (by omega)
  have h2 := hW x (by omega)
  have h3 := hW (x + 1) (by omega)
  rw [show x - 1 - (t : Int) = x - t - 1 by omega] at h1
  rw [show x + 1 - (t : Int) = x - t + 1 by omega] at h3
  rw [show x - ((t + 1 : Nat) : Int) = x - t - 1 by omega]
  show rule30 (evolve init t (x - 1)) (evolve init t x) (evolve init t (x + 1)) = W' (x - t - 1)
  rw [h1, h2, h3]
  exact hstep (x - t) (by omega)

/-- The rows of a seed with windows: from cell `t - 2` on, `W0` at even `t` and `W1` at odd `t`. -/
theorem Windows.rows {seed W0 W1 : Int → Bool} (h : Windows seed W0 W1) (t : Nat) :
    ∀ x : Int, (t : Int) - 2 ≤ x → evolve seed t x = (if t % 2 = 0 then W0 else W1) (x - t) := by
  induction t with
  | zero =>
    intro x hx
    rw [ite_eq_left (by decide : (0 : Nat) % 2 = 0), show x - ((0 : Nat) : Int) = x by omega]
    exact h.start x (by omega)
  | succ t ih =>
    by_cases hp : t % 2 = 0
    · rw [ite_eq_left hp] at ih
      rw [ite_eq_right (by omega : ¬(t + 1) % 2 = 0)]
      exact window_step ih h.step0
    · rw [ite_eq_right hp] at ih
      rw [ite_eq_left (by omega : (t + 1) % 2 = 0)]
      exact window_step ih h.step1

theorem sigma_windows (k : Nat) : Windows (sigma k) (sigma k) (sigmaOdd k) where
  start _ _ := rfl
  zeros x hx := (decide_eq_false (by omega) : sigma k x = false)
  step0 := sigma_step k
  step1 := sigmaOdd_step k
  low0 := ⟨(decide_eq_false (by omega) : sigma k (-2) = false), (decide_eq_false (by omega) : sigma k (-1) = false)⟩
  low1 := ⟨(decide_eq_true (by omega) : sigmaOdd k (-2) = true), (decide_eq_true (by omega) : sigmaOdd k (-1) = true)⟩

theorem tau_windows (k : Nat) : Windows (tau k) (tau k) (tauOdd k) where
  start _ _ := rfl
  zeros x hx := (decide_eq_false (by omega) : tau k x = false)
  step0 := tau_step k
  step1 := tauOdd_step k
  low0 := ⟨(decide_eq_false (by omega) : tau k (-2) = false), (decide_eq_false (by omega) : tau k (-1) = false)⟩
  low1 := ⟨(decide_eq_true (by omega) : tauOdd k (-2) = true), (decide_eq_true (by omega) : tauOdd k (-1) = true)⟩

/-- The single seed is `sigma 0`. -/
theorem single_eq : single = sigma 0 := by
  funext x
  by_cases hx : x = 0
  · exact (decide_eq_true hx).trans (decide_eq_true (by omega) : sigma 0 x = true).symm
  · exact (decide_eq_false hx).trans (decide_eq_false (by omega) : sigma 0 x = false).symm

/-- The seed 11 is `tau 0`. -/
theorem seed11_eq : seed11 = tau 0 := by
  funext x
  by_cases hx : x = 0 ∨ x = 1
  · exact (decide_eq_true hx).trans (decide_eq_true (by omega) : tau 0 x = true).symm
  · exact (decide_eq_false hx).trans (decide_eq_false (by omega) : tau 0 x = false).symm

theorem single_windows : Windows single (sigma 0) (sigmaOdd 0) where
  start x _ := congrFun single_eq x
  zeros x hx := (decide_eq_false (by omega) : single x = false)
  step0 := sigma_step 0
  step1 := sigmaOdd_step 0
  low0 := (sigma_windows 0).low0
  low1 := (sigma_windows 0).low1

/-- A seed with windows evolves like the single seed at every cell left of `t`: left of `t - 2` by induction, since
those cells see only cells left of `t - 1` a step earlier, and at `t - 2` and `t - 1` because the windows hold the
same values there. -/
theorem Windows.agree {seed W0 W1 : Int → Bool} (h : Windows seed W0 W1) (t : Nat) :
    ∀ x : Int, x < t → evolve seed t x = evolve single t x := by
  have edge : ∀ (t : Nat) (x : Int), (t : Int) - 2 ≤ x → x < t → evolve seed t x = evolve single t x := by
    intro t x h1 h2
    rw [h.rows t x h1, single_windows.rows t x h1]
    by_cases hp : t % 2 = 0
    · simp only [ite_eq_left hp]
      rcases (by omega : x - t = -2 ∨ x - t = -1) with e | e <;> rw [e]
      · rw [h.low0.1, single_windows.low0.1]
      · rw [h.low0.2, single_windows.low0.2]
    · simp only [ite_eq_right hp]
      rcases (by omega : x - t = -2 ∨ x - t = -1) with e | e <;> rw [e]
      · rw [h.low1.1, single_windows.low1.1]
      · rw [h.low1.2, single_windows.low1.2]
  have far : ∀ (t : Nat) (x : Int), x < (t : Int) - 2 → evolve seed t x = evolve single t x := by
    intro t
    induction t with
    | zero =>
      intro x hx
      show seed x = single x
      rw [h.zeros x (by omega), single_windows.zeros x (by omega)]
    | succ t ih =>
      intro x hx
      have below : ∀ y : Int, y < t → evolve seed t y = evolve single t y := fun y hy =>
        if hf : y < (t : Int) - 2 then ih y hf else edge t y (by omega) hy
      show rule30 (evolve seed t (x - 1)) (evolve seed t x) (evolve seed t (x + 1)) =
        rule30 (evolve single t (x - 1)) (evolve single t x) (evolve single t (x + 1))
      rw [below (x - 1) (by omega), below x (by omega), below (x + 1) (by omega)]
  intro x hx
  exact if hf : x < (t : Int) - 2 then far t x hf else edge t x (by omega) hx

/-- A seed with windows differs from the single seed exactly where, from cell `t - 2` on, the windows differ. -/
theorem Windows.difference {seed W0 W1 : Int → Bool} (h : Windows seed W0 W1) (t : Nat) (x : Int) :
    evolve seed t x ≠ evolve single t x ↔ (t : Int) - 2 ≤ x ∧
      (if t % 2 = 0 then W0 else W1) (x - t) ≠ (if t % 2 = 0 then sigma 0 else sigmaOdd 0) (x - t) := by
  by_cases hx : (t : Int) - 2 ≤ x
  · rw [h.rows t x hx, single_windows.rows t x hx]
    exact ⟨fun hne => ⟨hx, hne⟩, fun hc => hc.2⟩
  · rw [h.agree t x (by omega)]
    exact ⟨fun hne => absurd rfl hne, fun hc => absurd hc.1 hx⟩

/-- For every `k`, the seed (10)^k 1 evolves like the single seed at every cell left of `t`. -/
theorem sigma_agrees (k t : Nat) (x : Int) (hx : x < t) : evolve (sigma k) t x = evolve single t x :=
  (sigma_windows k).agree t x hx

/-- For every `k`, the seed (10)^k 11 evolves like the single seed at every cell left of `t`. -/
theorem tau_agrees (k t : Nat) (x : Int) (hx : x < t) : evolve (tau k) t x = evolve single t x :=
  (tau_windows k).agree t x hx

/-- Every seed (10)^k 1 gives the single seed's center column. -/
theorem sigma_center (k t : Nat) : evolve (sigma k) t 0 = evolve single t 0 := by
  cases t with
  | zero => exact (decide_eq_true (by omega) : sigma k 0 = true).trans (decide_eq_true rfl : single 0 = true).symm
  | succ t => exact sigma_agrees k (t + 1) 0 (by omega)

/-- Every seed (10)^k 11 gives the single seed's center column. -/
theorem tau_center (k t : Nat) : evolve (tau k) t 0 = evolve single t 0 := by
  cases t with
  | zero => exact (decide_eq_true (by omega) : tau k 0 = true).trans (decide_eq_true rfl : single 0 = true).symm
  | succ t => exact tau_agrees k (t + 1) 0 (by omega)

/-- The rows from (10)^k 1 and from the single seed differ exactly at these offsets `x - t`: 2, 4, ..., 2k at even
`t`, and 0, the odd ones up to 2k - 1, and 2k at odd `t` when k > 0. -/
theorem sigma_difference (k t : Nat) (x : Int) :
    evolve (sigma k) t x ≠ evolve single t x ↔
      (t % 2 = 0 ∧ 2 ≤ x - t ∧ x - t ≤ 2 * (k : Int) ∧ (x - t) % 2 = 0) ∨
      (t % 2 = 1 ∧ 0 < k ∧
        (x - t = 0 ∨ (1 ≤ x - t ∧ x - t ≤ 2 * (k : Int) - 1 ∧ (x - t) % 2 = 1) ∨ x - t = 2 * (k : Int))) := by
  rw [(sigma_windows k).difference t x]
  by_cases hp : t % 2 = 0
  · simp only [ite_eq_left hp]
    cases h1 : sigma k (x - t) <;> cases h2 : sigma 0 (x - t) <;>
      simp only [sigma, decide_eq_true_eq, decide_eq_false_iff_not] at h1 h2 <;>
      simp only [ne_eq,Bool.false_eq_true, Bool.true_eq_false, not_true_eq_false,
        not_false_eq_true, and_true, and_false] <;>
      constructor <;> intro hc <;> first | exact False.elim hc | omega
  · simp only [ite_eq_right hp]
    cases h1 : sigmaOdd k (x - t) <;> cases h2 : sigmaOdd 0 (x - t) <;>
      simp only [sigmaOdd, decide_eq_true_eq, decide_eq_false_iff_not] at h1 h2 <;>
      simp only [ne_eq,Bool.false_eq_true, Bool.true_eq_false, not_true_eq_false,
        not_false_eq_true, and_true, and_false] <;>
      constructor <;> intro hc <;> first | exact False.elim hc | omega

/-- The rows from (10)^k 11 and from the single seed differ exactly at these offsets `x - t`: 2, 4, ..., 2k and
2k + 1 at even `t`, and 0 and the odd ones up to 2k + 1 at odd `t`. -/
theorem tau_difference (k t : Nat) (x : Int) :
    evolve (tau k) t x ≠ evolve single t x ↔
      (t % 2 = 0 ∧ ((2 ≤ x - t ∧ x - t ≤ 2 * (k : Int) ∧ (x - t) % 2 = 0) ∨ x - t = 2 * (k : Int) + 1)) ∨
      (t % 2 = 1 ∧ (x - t = 0 ∨ (1 ≤ x - t ∧ x - t ≤ 2 * (k : Int) + 1 ∧ (x - t) % 2 = 1))) := by
  rw [(tau_windows k).difference t x]
  by_cases hp : t % 2 = 0
  · simp only [ite_eq_left hp]
    cases h1 : tau k (x - t) <;> cases h2 : sigma 0 (x - t) <;>
      simp only [tau, sigma, decide_eq_true_eq, decide_eq_false_iff_not] at h1 h2 <;>
      simp only [ne_eq,Bool.false_eq_true, Bool.true_eq_false, not_true_eq_false,
        not_false_eq_true, and_true, and_false] <;>
      constructor <;> intro hc <;> first | exact False.elim hc | omega
  · simp only [ite_eq_right hp]
    cases h1 : tauOdd k (x - t) <;> cases h2 : sigmaOdd 0 (x - t) <;>
      simp only [tauOdd, sigmaOdd, decide_eq_true_eq, decide_eq_false_iff_not] at h1 h2 <;>
      simp only [ne_eq,Bool.false_eq_true, Bool.true_eq_false, not_true_eq_false,
        not_false_eq_true, and_true, and_false] <;>
      constructor <;> intro hc <;> first | exact False.elim hc | omega

/-- The 11 lemma: the evolutions from the seeds 1 and 11 agree at every cell left of `t`. -/
theorem eleven (t : Nat) (x : Int) (hx : x < t) : evolve seed11 t x = evolve single t x := by
  rw [seed11_eq]
  exact tau_agrees 0 t x hx

/-- The seeds 1 and 11 give the same center column. -/
theorem center_column (t : Nat) : evolve seed11 t 0 = evolve single t 0 := by
  rw [seed11_eq]
  exact tau_center 0 t

/-- The rows from the seeds 11 and 1 differ exactly at `t + 1`, and at `t` too when `t` is odd. -/
theorem difference (t : Nat) (x : Int) :
    evolve seed11 t x ≠ evolve single t x ↔ x = (t : Int) + 1 ∨ (t % 2 = 1 ∧ x = t) := by
  rw [seed11_eq, tau_difference]
  constructor <;> intro hc <;> omega

/-- Official form: every seed (10)^k 1 has the prize's center column. -/
theorem center_sigma (k t : Nat) : evolve (sigma k) t 0 = Rule30Prize.center t :=
  (sigma_center k t).trans (evolve_single_center t)

/-- Official form: every seed (10)^k 11 has the prize's center column. -/
theorem center_tau (k t : Nat) : evolve (tau k) t 0 = Rule30Prize.center t :=
  (tau_center k t).trans (evolve_single_center t)

end Rule30Open
