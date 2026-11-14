module

public import Ruliology.CellularAutomata.Rule30FiniteDiagonals

/-!
# Eternal left halves: purely periodic diagonals and a unique past

Read a row that is white left of a cell from that cell rightward: coordinate `d` is the left diagonal `d`. One step of
rule 30 with the frame moved one cell left is the map `leftStep`,
`leftStep(R)_d = R_{d-2} xor (R_{d-1} || R_d)` with `R_{-1} = R_{-2} = false`. Coordinate `d` of the image reads only
coordinates `d - 2, d - 1, d`, so `leftStep` does not increase the 2-adic distance `2^-(first difference)`; it is not
injective (the single cell has no preimage with a black edge cell, `seed_no_preimage`).

An *eternal* orbit is a family of rows `R t`, `t : Int`, with `R (t + 1) = leftStep (R t)` for every integer `t`: a
rule-30 history defined for all times, every row white left of a frame moving left one cell per step.

* `Ld_leftStep`: for every configuration white left of `lo`, the kit's left diagonals
  `Ld x lo d t = evol x t (lo - t + d)` are a forward orbit of `leftStep`.
* `eternal_periodic`: in an eternal orbit every diagonal is purely periodic on all of `Int`, with period dividing
  `2 ^ d`. This is the kit's uniform period (`Rule30FiniteDiagonals.left_recurrence_uniform_period`, from time
  `2 ^ d - 1`) applied from a time `2 ^ d - 1` steps earlier, which always exists in an eternal orbit.
* `eternal_past`: the past is a forward function of the present. Coordinate `d` of `R t` is coordinate `d` of
  `leftStep^(2^d - 1) (R (t + 1))`. So `eternal_agree`: two eternal orbits that agree at one time agree at every time,
  and `leftStep` is injective on the rows of eternal orbits, with an inverse that is continuous coordinate by
  coordinate.
* `eternal_edge`: if some row of an eternal orbit has a black cell at the frame, then at every time diagonal 0 and 1
  are black, diagonal 2 is white and diagonal 3 flips at every step. `seed_not_eternal`: the single black cell is not a
  row of any eternal orbit.

The natural-language argument, with the limit set and the odometer this gives, is `EternalSkeleton.md`, beside this
file.
-/

@[expose] public section

namespace Rule30Open

namespace EternalSkeleton

/-- Rule 30 in the frame of a left edge moving left one cell per step: coordinate `d` is left diagonal `d`. -/
def leftStep (R : Nat → Bool) : Nat → Bool
  | 0 => R 0
  | 1 => (R 0 || R 1)
  | d + 2 => xor (R d) (R (d + 1) || R (d + 2))

/-- The `n`-th iterate of `leftStep`. -/
def iter : Nat → (Nat → Bool) → Nat → Bool
  | 0, R => R
  | n + 1, R => leftStep (iter n R)

/-- An eternal orbit of `leftStep`: rows at every integer time. -/
def Eternal (R : Int → Nat → Bool) : Prop := ∀ t : Int, R (t + 1) = leftStep (R t)

/-- The kit's left diagonals of a configuration white left of `lo` are a forward orbit of `leftStep`. -/
theorem Ld_leftStep {x : Int → Bool} {lo : Int} (hleft : ∀ p, p < lo → x p = false) (t : Nat) :
    (fun d => Ruliology.CellularAutomata.Rule30FiniteDiagonals.Ld x lo d (t + 1)) =
      leftStep (fun d => Ruliology.CellularAutomata.Rule30FiniteDiagonals.Ld x lo d t) := by
  funext d
  match d with
  | 0 => exact Ruliology.CellularAutomata.Rule30FiniteDiagonals.Ld_zero_succ hleft t
  | 1 => exact Ruliology.CellularAutomata.Rule30FiniteDiagonals.Ld_one_succ hleft t
  | j + 2 => exact Ruliology.CellularAutomata.Rule30FiniteDiagonals.Ld_step (x := x) (lo := lo) j t

theorem eternal_iter {R : Int → Nat → Bool} (hR : Eternal R) (t : Int) :
    ∀ n : Nat, R (t + (n : Int)) = iter n (R t)
  | 0 => by simp [iter]
  | n + 1 => by
    rw [show t + ((n + 1 : Nat) : Int) = (t + (n : Int)) + 1 by omega, hR, eternal_iter hR t n]
    rfl

/-- **Every diagonal of an eternal orbit is purely periodic, with period dividing `2 ^ d`.** -/
theorem eternal_periodic {R : Int → Nat → Bool} (hR : Eternal R) (d : Nat) (t : Int) :
    R (t + ((2 ^ d : Nat) : Int)) d = R t d := by
  let s : Nat := 2 ^ d - 1
  let b : Nat → Nat → Bool := fun i n => R (t - (s : Int) + (n : Int)) i
  have hstep : ∀ n : Nat, R (t - (s : Int) + ((n + 1 : Nat) : Int)) =
      leftStep (R (t - (s : Int) + (n : Int))) := by
    intro n
    rw [show t - (s : Int) + ((n + 1 : Nat) : Int) = (t - (s : Int) + (n : Int)) + 1 by omega]
    exact hR _
  have h0 : ∀ n, b 0 (n + 1) = b 0 n := by
    intro n; show R _ 0 = R _ 0; rw [hstep n]; rfl
  have h1 : ∀ n, b 1 (n + 1) = (b 0 n || b 1 n) := by
    intro n; show R _ 1 = _; rw [hstep n]; rfl
  have h2 : ∀ i n, b (i + 2) (n + 1) = xor (b i n) (b (i + 1) n || b (i + 2) n) := by
    intro i n; show R _ (i + 2) = _; rw [hstep n]; rfl
  have hp := Ruliology.CellularAutomata.Rule30FiniteDiagonals.left_recurrence_uniform_period b h0 h1 h2 d s
    (Nat.le_refl _)
  have hpos : 0 < 2 ^ d := Nat.two_pow_pos d
  have e1 : t - (s : Int) + ((s + 2 ^ d : Nat) : Int) = t + ((2 ^ d : Nat) : Int) := by omega
  have e2 : t - (s : Int) + ((s : Nat) : Int) = t := by omega
  have := hp
  simp only [b] at this
  rw [e1, e2] at this
  exact this

/-- **The past is a forward function of the present**: coordinate `d` of `R t` is coordinate `d` of
`leftStep^(2^d - 1) (R (t + 1))`. -/
theorem eternal_past {R : Int → Nat → Bool} (hR : Eternal R) (t : Int) (d : Nat) :
    R t d = iter (2 ^ d - 1) (R (t + 1)) d := by
  have hpos : 0 < 2 ^ d := Nat.two_pow_pos d
  rw [← eternal_periodic hR d t, ← eternal_iter hR (t + 1) (2 ^ d - 1)]
  congr 1
  omega

/-- Two eternal orbits that agree at time `t + 1` agree at time `t`. -/
theorem eternal_unique_past {R R' : Int → Nat → Bool} (hR : Eternal R) (hR' : Eternal R') (t : Int)
    (h : R (t + 1) = R' (t + 1)) : R t = R' t := by
  funext d
  rw [eternal_past hR, eternal_past hR', h]

/-- **Two eternal orbits that agree at one time agree at every time.** -/
theorem eternal_agree {R R' : Int → Nat → Bool} (hR : Eternal R) (hR' : Eternal R') (t₀ : Int)
    (h : R t₀ = R' t₀) (t : Int) : R t = R' t := by
  have fwd : ∀ n : Nat, R (t₀ + n) = R' (t₀ + n) := by
    intro n
    rw [eternal_iter hR, eternal_iter hR', h]
  have bwd : ∀ n : Nat, R (t₀ - n) = R' (t₀ - n) := by
    intro n
    induction n with
    | zero => simpa using h
    | succ n ih =>
      apply eternal_unique_past hR hR'
      rw [show t₀ - ((n + 1 : Nat) : Int) + 1 = t₀ - (n : Int) by omega]
      exact ih
  rcases Int.le_total t₀ t with hle | hle
  · have := fwd (t - t₀).toNat
    rwa [show t₀ + ((t - t₀).toNat : Int) = t by omega] at this
  · have := bwd (t₀ - t).toNat
    rwa [show t₀ - ((t₀ - t).toNat : Int) = t by omega] at this

/-- `leftStep` is injective on rows of eternal orbits. -/
theorem leftStep_injective_on_eternal {R R' : Int → Nat → Bool} (hR : Eternal R) (hR' : Eternal R') (t t' : Int)
    (h : leftStep (R t) = leftStep (R' t')) : R t = R' t' := by
  let Q : Int → Nat → Bool := fun s => R' (s + (t' - t))
  have hQ : Eternal Q := by
    intro s
    show R' (s + 1 + (t' - t)) = leftStep (R' (s + (t' - t)))
    rw [show s + 1 + (t' - t) = s + (t' - t) + 1 by omega]
    exact hR' _
  have h1 : R (t + 1) = Q (t + 1) := by
    show R (t + 1) = R' (t + 1 + (t' - t))
    rw [hR, show t + 1 + (t' - t) = t' + 1 by omega, hR', h]
  have := eternal_unique_past hR hQ t h1
  show R t = R' t'
  rw [this]
  show R' (t + (t' - t)) = R' t'
  rw [show t + (t' - t) = t' by omega]

/-- **The edge of an eternal orbit.** If one row has a black cell at the frame, then at every time diagonals 0 and 1
are black, diagonal 2 is white, and diagonal 3 flips at every step. -/
theorem eternal_edge {R : Int → Nat → Bool} (hR : Eternal R) (t₀ : Int) (h0 : R t₀ 0 = true) :
    ∀ t : Int, R t 0 = true ∧ R t 1 = true ∧ R t 2 = false ∧ R (t + 1) 3 = !R t 3 := by
  -- diagonal 0 has period 1
  have p0 : ∀ t, R (t + 1) 0 = R t 0 := fun t => by
    have := eternal_periodic hR 0 t; simpa using this
  have c0 : ∀ t, R t 0 = true := by
    intro t
    have fwd : ∀ n : Nat, R (t₀ + n) 0 = true := by
      intro n; induction n with
      | zero => simpa using h0
      | succ n ih => rw [show t₀ + ((n + 1 : Nat) : Int) = (t₀ + n) + 1 by omega, p0]; exact ih
    have bwd : ∀ n : Nat, R (t₀ - n) 0 = true := by
      intro n; induction n with
      | zero => simpa using h0
      | succ n ih =>
        rw [← p0, show t₀ - ((n + 1 : Nat) : Int) + 1 = t₀ - n by omega]; exact ih
    rcases Int.le_total t₀ t with hle | hle
    · have := fwd (t - t₀).toNat
      rwa [show t₀ + ((t - t₀).toNat : Int) = t by omega] at this
    · have := bwd (t₀ - t).toNat
      rwa [show t₀ - ((t₀ - t).toNat : Int) = t by omega] at this
  have c1 : ∀ t, R t 1 = true := by
    intro t
    rw [show t = t - 1 + 1 by omega, hR]
    show (R (t - 1) 0 || R (t - 1) 1) = true
    rw [c0]; rfl
  have c2 : ∀ t, R t 2 = false := by
    intro t
    rw [show t = t - 1 + 1 by omega, hR]
    show xor (R (t - 1) 0) (R (t - 1) 1 || R (t - 1) 2) = false
    rw [c0, c1]; rfl
  intro t
  refine ⟨c0 t, c1 t, c2 t, ?_⟩
  rw [hR]
  show xor (R t 1) (R t 2 || R t 3) = !R t 3
  rw [c1, c2]; cases R t 3 <;> rfl

/-- The single black cell, read from its own cell. -/
def seedRow : Nat → Bool := fun d => d == 0

/-- The single cell has no preimage under `leftStep` with a black cell at the frame. -/
theorem seed_no_preimage (R : Nat → Bool) (h : R 0 = true) : leftStep R ≠ seedRow := by
  intro he
  have := congrFun he 1
  simp [leftStep, seedRow, h] at this

/-- **The single cell is not a row of any eternal orbit.** -/
theorem seed_not_eternal {R : Int → Nat → Bool} (hR : Eternal R) (t : Int) : R t ≠ seedRow := by
  intro he
  have h0 : R t 0 = true := by rw [he]; rfl
  have := (eternal_edge hR t h0 t).2.1
  rw [he] at this
  simp [seedRow] at this

end EternalSkeleton

end Rule30Open
