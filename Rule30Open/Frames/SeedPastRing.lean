module

public import Rule30Open.Frames.SeedPastPeriods

/-!
# The single cell's past in Rule 30 itself, and the death of its tails on a ring

`SeedPast` and `SeedPastPeriods` work in the moving frame, on sequences of bits. Here the same facts are stated for
`evolve`, Rule 30 on rows indexed by the integers.

* **Exactly one past** (`seedRow_evolve`, `seed_past_iff`). Among rows white right of cell `m`, the ones that Rule 30
  takes in `k` steps to the single black cell at `m + k` are exactly one: `seedRow k m`, which reads `rho k` leftward
  from `m`.
* **The tail dies on its ring in exactly `k` steps** (`rho_tail_dies`). If `rho k` repeats with period `p` from bit
  `N`, wrap that tail on a ring of `p` cells: the `p`-periodic row `tailRing (rho k) N p`, which agrees with the past
  far to the left (`tailRing_left`, `tailRing_periodic`). Rule 30 turns it all white at step `k` and not before, and
  all black at step `k - 1`. A periodic row agrees, far to the left, with the row white right of the frame
  (`evolve_agree`), and the latter reads `phiIter t (rho k) = rho (k - t)` (`frameRow_evolve`); a periodic row is white
  when it is white far to the left (`evolve_periodic`). `rho 1` is all black (`rho_one`), and `rho j` for `j ≥ 1` is
  never white far out (`rho_not_evZero`).

The natural-language argument is `SeedPastRing.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

/-! ### Rows read leftward from a cell -/

/-- The row that reads `y` leftward from cell `m`, bit `j` at cell `m - j`, and is white right of `m`. -/
def frameRow (y : Nat → Bool) (m : Int) (x : Int) : Bool := if x ≤ m then y (m - x).toNat else false

theorem frameRow_white (y : Nat → Bool) (m : Int) : ∀ x : Int, m < x → frameRow y m x = false := by
  intro x hx
  unfold frameRow
  split
  · omega
  · rfl

theorem frameRow_of_le (y : Nat → Bool) (m x : Int) (hx : x ≤ m) : frameRow y m x = y (m - x).toNat := by
  unfold frameRow
  split
  · rfl
  · omega

theorem frame_frameRow (y : Nat → Bool) (m : Int) : frame (frameRow y m) m 0 = y := by
  funext j
  show frameRow y m (m + ((0 : Nat) : Int) - j) = y j
  rw [frameRow_of_le y m _ (by omega), show m - (m + ((0 : Nat) : Int) - j) = (j : Int) by omega, Int.toNat_natCast]

/-- Cell `m + t - j` of the row reading `y` from `m`, at time `t`, is bit `j` of `phiIter t y`. -/
theorem frameRow_evolve (y : Nat → Bool) (m : Int) (t j : Nat) :
    evolve (frameRow y m) t (m + t - j) = phiIter t y j := by
  have e := frame_iterate (frameRow y m) m (frameRow_white y m) t 0
  rw [Nat.zero_add, frame_frameRow] at e
  have e2 := congrFun e j
  exact e2

/-- The row white right of `m` that reads `rho k` leftward from `m`. -/
def seedRow (k : Nat) (m : Int) : Int → Bool := frameRow (rho k) m

/-- **The past exists in Rule 30**: `k` steps take `seedRow k m` to the single black cell at `m + k`. -/
theorem seedRow_evolve (k : Nat) (m : Int) : ∀ x : Int, evolve (seedRow k m) k x = decide (x = m + k) := by
  intro x
  by_cases hx : x ≤ m + k
  · have e := frameRow_evolve (rho k) m k (m + k - x).toNat
    rw [show m + (k : Int) - ((m + k - x).toNat : Nat) = x by omega, phiIter_rho] at e
    show evolve (frameRow (rho k) m) k x = _
    rw [e]
    show decide ((m + k - x).toNat = 0) = _
    by_cases h : x = m + k
    · rw [decide_eq_true h, decide_eq_true (by omega)]
    · rw [decide_eq_false h, decide_eq_false (by omega)]
  · show evolve (frameRow (rho k) m) k x = _
    rw [right_white _ m (frameRow_white (rho k) m) k x (by omega), decide_eq_false (by omega)]

/-- **The single cell has exactly one past at each depth**: a row white right of cell `m` becomes, `k` steps later,
the single black cell at `m + k` if and only if it is `seedRow k m`. -/
theorem seed_past_iff (init : Int → Bool) (m : Int) (hm : ∀ x : Int, m < x → init x = false) (k : Nat) :
    (∀ x : Int, evolve init k x = decide (x = m + k)) ↔ init = seedRow k m := by
  constructor
  · intro hk
    have e := (past_evPer init m hm k hk).1
    funext x
    show init x = frameRow (rho k) m x
    by_cases hx : x ≤ m
    · rw [frameRow_of_le _ m x hx, ← e]
      show init x = init (m - ((m - x).toNat : Nat))
      rw [show m - (((m - x).toNat : Nat) : Int) = x by omega]
    · rw [frameRow_white _ m x (by omega), hm x (by omega)]
  · intro e
    rw [e]
    exact seedRow_evolve k m

/-! ### Periodic rows -/

/-- A row with period `p` keeps it. -/
theorem evolve_periodic (init : Int → Bool) (p : Int) (h : ∀ x, init (x + p) = init x) :
    ∀ t x, evolve init t (x + p) = evolve init t x
  | 0, x => h x
  | t + 1, x => by
    show rule30 (evolve init t (x + p - 1)) (evolve init t (x + p)) (evolve init t (x + p + 1)) =
      rule30 (evolve init t (x - 1)) (evolve init t x) (evolve init t (x + 1))
    rw [show x + p - 1 = (x - 1) + p by omega, show x + p + 1 = (x + 1) + p by omega,
      evolve_periodic init p h t (x - 1), evolve_periodic init p h t x, evolve_periodic init p h t (x + 1)]

theorem evolve_periodic_mul (init : Int → Bool) (p : Int) (h : ∀ x, init (x + p) = init x) (t : Nat) :
    ∀ q : Nat, ∀ x, evolve init t (x + q * p) = evolve init t x
  | 0, x => by rw [Int.natCast_zero, Int.zero_mul, Int.add_zero]
  | q + 1, x => by
    rw [show x + ((q + 1 : Nat) : Int) * p = (x + (q : Int) * p) + p by
      rw [Int.natCast_succ, Int.add_mul, Int.one_mul, Int.add_assoc], evolve_periodic init p h t,
      evolve_periodic_mul init p h t q x]

/-- **The light cone**: two rows that agree left of cell `a` agree left of `a - t` at time `t`. -/
theorem evolve_agree (init init' : Int → Bool) (a : Int) (h : ∀ x, x ≤ a → init x = init' x) :
    ∀ t : Nat, ∀ x, x + t ≤ a → evolve init t x = evolve init' t x
  | 0, x, hx => h x (by omega)
  | t + 1, x, hx => by
    show rule30 (evolve init t (x - 1)) (evolve init t x) (evolve init t (x + 1)) =
      rule30 (evolve init' t (x - 1)) (evolve init' t x) (evolve init' t (x + 1))
    rw [evolve_agree init init' a h t (x - 1) (by omega), evolve_agree init init' a h t x (by omega),
      evolve_agree init init' a h t (x + 1) (by omega)]

/-- The tail of `y` from bit `N`, wrapped on a ring of `p` cells: the `p`-periodic row whose cell `-j` is bit `j` of
`y` for `j ≥ N`, when `y` has period `p` from `N` (`tailRing_left`). -/
def tailRing (y : Nat → Bool) (N p : Nat) (x : Int) : Bool := y (N + ((-x - N) % (p : Int)).toNat)

theorem tailRing_periodic (y : Nat → Bool) (N p : Nat) : ∀ x, tailRing y N p (x + p) = tailRing y N p x := by
  intro x
  unfold tailRing
  rw [show -(x + (p : Int)) - N = (-x - N) + (-1) * (p : Int) by omega, Int.add_mul_emod_self_right]

theorem tailRing_left (y : Nat → Bool) (N p : Nat) (h : ∀ j, N ≤ j → y (j + p) = y j) :
    ∀ j, N ≤ j → tailRing y N p (-(j : Int)) = y j := by
  intro j hj
  unfold tailRing
  rw [show -(-(j : Int)) - N = ((j - N : Nat) : Int) by omega, ← Int.natCast_emod, Int.toNat_natCast]
  have e := evPer_mul h ((j - N) / p) (N + (j - N) % p) (by omega)
  rw [show N + (j - N) % p + (j - N) / p * p = j by
    have := Nat.div_add_mod (j - N) p
    rw [Nat.mul_comm] at this
    omega] at e
  exact e.symm

/-- A row with period `p` from bit `N` and the row white right of the frame that reads it agree at time `t` on the
cells `t - j`, `j ≥ N + 2 t`, of the ring. -/
theorem tailRing_evolve (y : Nat → Bool) (N p : Nat) (h : ∀ j, N ≤ j → y (j + p) = y j) (t j : Nat)
    (hj : N + 2 * t ≤ j) : evolve (tailRing y N p) t ((t : Int) - j) = phiIter t y j := by
  have hag : ∀ x : Int, x ≤ -(N : Int) → tailRing y N p x = frameRow y 0 x := by
    intro x hx
    have e := tailRing_left y N p h (-x).toNat (by omega)
    rw [show -(((-x).toNat : Nat) : Int) = x by omega] at e
    rw [e, frameRow_of_le y 0 x (by omega), show (0 : Int) - x = -x by omega]
  rw [evolve_agree _ _ (-(N : Int)) hag t _ (by omega)]
  have e := frameRow_evolve y 0 t j
  rw [show (0 : Int) + t - j = (t : Int) - j by omega] at e
  exact e

/-- Every cell of a `p`-periodic row at time `t` repeats a cell `t - j` with `j ≥ M`. -/
theorem tailRing_cell (y : Nat → Bool) (N p : Nat) (hp : 0 < p) (t M : Nat) (x : Int) :
    ∃ j, M ≤ j ∧ evolve (tailRing y N p) t x = evolve (tailRing y N p) t ((t : Int) - j) := by
  refine ⟨(t - (x - ((x + M).toNat : Nat) * (p : Int))).toNat, by
    have : (p : Int) ≥ 1 := by omega
    have : ((x + M).toNat : Int) * (p : Int) ≥ ((x + M).toNat : Int) := by
      have := Int.mul_le_mul_of_nonneg_left this (by omega : (0 : Int) ≤ ((x + M).toNat : Int))
      omega
    omega, ?_⟩
  have hle : x - ((x + M).toNat : Nat) * (p : Int) ≤ t := by
    have : ((x + M).toNat : Int) * (p : Int) ≥ 0 := Int.mul_nonneg (by omega) (by omega)
    have : (p : Int) ≥ 1 := by omega
    have : ((x + M).toNat : Int) * (p : Int) ≥ ((x + M).toNat : Int) := by
      have := Int.mul_le_mul_of_nonneg_left this (by omega : (0 : Int) ≤ ((x + M).toNat : Int))
      omega
    omega
  rw [show (t : Int) - (((t - (x - ((x + M).toNat : Nat) * (p : Int))).toNat : Nat) : Int) =
    x - ((x + M).toNat : Nat) * (p : Int) by omega]
  have e := evolve_periodic_mul _ (p : Int) (tailRing_periodic y N p) t (x + M).toNat
    (x - ((x + M).toNat : Nat) * (p : Int))
  rw [Int.sub_add_cancel] at e
  exact e

/-! ### The tail of the single cell's past dies on its ring in exactly `k` steps -/

/-- One step back, the single cell's past is all black: `phiF` takes the all-black row to the single cell. -/
theorem rho_one : rho 1 = fun _ => true := by
  have e : phiF (fun _ => true) = seedBits := by
    funext j
    match j with
    | 0 => rfl
    | 1 => rfl
    | j + 2 => rfl
  show phiInv seedBits = _
  rw [← e, phiInv_phiF]

/-- **The tail of `rho k`, wrapped on a ring, dies in exactly `k` steps**: if `rho k` repeats with period `p` from bit
`N`, the `p`-periodic row of that tail is all white after `k` steps of Rule 30, has a black cell at every earlier step,
and is all black at step `k - 1`. -/
theorem rho_tail_dies (k N p : Nat) (hp : 0 < p) (h : ∀ j, N ≤ j → rho k (j + p) = rho k j) :
    (∀ x, evolve (tailRing (rho k) N p) k x = false) ∧
    (∀ t, t < k → ∃ x, evolve (tailRing (rho k) N p) t x = true) ∧
    (0 < k → ∀ x, evolve (tailRing (rho k) N p) (k - 1) x = true) := by
  refine ⟨fun x => ?_, fun t ht => ?_, fun hk x => ?_⟩
  · obtain ⟨j, hj, e⟩ := tailRing_cell (rho k) N p hp k (N + 2 * k + 1) x
    rw [e, tailRing_evolve (rho k) N p h k j (by omega), phiIter_rho]
    exact decide_eq_false (by omega)
  · have hne := rho_not_evZero (k - t) (by omega)
    have hb : ∃ j, N + 2 * t ≤ j ∧ rho (k - t) j = true := by
      refine Classical.byContradiction fun hn => hne ⟨N + 2 * t, fun j hj => ?_⟩
      cases hr : rho (k - t) j with
      | false => rfl
      | true => exact absurd ⟨j, hj, hr⟩ hn
    obtain ⟨j, hj, hr⟩ := hb
    refine ⟨(t : Int) - j, ?_⟩
    rw [tailRing_evolve (rho k) N p h t j hj, rho_iter t k (by omega)]
    exact hr
  · obtain ⟨j, hj, e⟩ := tailRing_cell (rho k) N p hp (k - 1) (N + 2 * (k - 1)) x
    rw [e, tailRing_evolve (rho k) N p h (k - 1) j hj, rho_iter (k - 1) k (by omega),
      show k - (k - 1) = 1 by omega, rho_one]

/-- **Every tail of the single cell's past dies on a ring**: for every `k` there are `N` and `p > 0` with `rho k`
repeating with period `p` from `N`, and the ring of that tail dies in exactly `k` steps. -/
theorem seed_past_rings (k : Nat) : ∃ N p, 0 < p ∧ (∀ j, N ≤ j → rho k (j + p) = rho k j) ∧
    (∀ x, evolve (tailRing (rho k) N p) k x = false) ∧
    (∀ t, t < k → ∃ x, evolve (tailRing (rho k) N p) t x = true) := by
  obtain ⟨N, p, hp, h⟩ := rho_evPer k
  have d := rho_tail_dies k N p hp h
  exact ⟨N, p, hp, h, d.1, d.2.1⟩

end Rule30Open
