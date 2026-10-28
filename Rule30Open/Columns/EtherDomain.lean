module

public import Rule30Open.Foundations.Official
public import Rule30Open.Columns.KickedForm
public import Rule30Open.PeriodTwo.Domains
public import Ruliology.CellularAutomata.Rule30PeriodFourSkeleton

/-!
# The word 0001 comes down to the period-two map, and the ether is its domain

The word `0001` never has two black cells in a row, so the cells left of a column that repeats it get no
kicks (`left_kicked_zero`): they follow `held`, the map that period 2 comes down to. The kit's skeleton
for `0001` (`Rule30PeriodFourSkeleton.skeleton_0001_explicit`) fixes the cell next to the center at three
of the four phases, white, free, white, black, and its no-repeat check (`no11_0001`) says the free bit is
never black in two periods in a row. So an eventual `0001` in the center column gives a positive integer
whose orbit under `heldNat` is even at the steps `4s` and `4s + 2`, odd at the steps `4s + 3`, and never
odd at two steps `4s + 1` and `4s + 5` (`center_period_four_0001_integer`): the kit's open statement
`C3 0001` as a question about the integer map of period 2.

As for period 2, infinite halves keep the condition. The ether of the kit (`Rule30Ether.ether`), read
leftward from one of its two `0001` columns, is a 4-cycle of `held` whose cell next to the column reads
`0001` (`held_etherLeft`, `ether_fits`), with every free bit white; as a 2-adic number it is `-8/127`.
Domain B of period 2 meets the three fixed phases too, but its free bit is black at every period, which
the no-repeat check forbids (`domainB_repeats`). So the right half's check removes the stripe and leaves
the ether. Near the ether the condition counts down, as near the stripes for period 2: a half that agrees
with it on exactly its `k` lowest bits follows its pattern for exactly `k` steps (`ether_countdown`).

The natural-language argument is `EtherDomain.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

open Ruliology.CellularAutomata

/-- The word 0001 comes down to `held`: if the single seed's center column repeats `0001` from `T` on (black when
`(t - T) % 4 = 3`), then from some step on the cells left of the center are the `held` orbit of a nonzero half that is
0 beyond some cell, whose cell next to the column reads white at the steps `4s` and `4s + 2`, black at the steps
`4s + 3`, and is never black at two steps `4s + 1` and `4s + 5`. -/
theorem period_four_0001_held (T : Nat)
    (h : ∀ t : Nat, T ≤ t → Rule30Prize.center t = decide ((t - T) % 4 = 3)) :
    ∃ u : Nat → Bool, (∃ j, u j = true) ∧ (∃ N, ∀ j, N ≤ j → u j = false) ∧
      ∀ s, heldOrbit u (4 * s) 0 = false ∧ heldOrbit u (4 * s + 2) 0 = false ∧ heldOrbit u (4 * s + 3) 0 = true ∧
        (heldOrbit u (4 * s + 1) 0 = true → heldOrbit u (4 * s + 5) 0 = false) := by
  have hc : ∀ t, T ≤ t → Rule30Jen.cell t 0 = decide ((t - T) % 4 = 3) := h
  obtain ⟨T1, -, hsk⟩ := Rule30PeriodFourSkeleton.skeleton_0001_explicit T hc
  obtain ⟨T2, -, hno⟩ := Rule30PeriodFourSkeleton.no11_0001 T fun t ht => by
    rw [hc t ht, Rule30PeriodFourSkeleton.wAt_0001 _ (Nat.mod_lt _ (by decide))]
  -- a start `S` at phase 0, past both bounds, with the left edge left of the center
  obtain ⟨S, hST, hS1, hS2, hS0, hSφ⟩ : ∃ S, T ≤ S ∧ T1 ≤ S ∧ T2 ≤ S ∧ 1 ≤ S ∧ (S - T) % 4 = 0 :=
    ⟨T + 4 * (T1 + T2 + 1), by omega, by omega, by omega, by omega, by omega⟩
  -- the cells left of the center at step `S + n`, bit `j` for the cell `j + 1` places left of it
  let v : Nat → Nat → Bool := fun n j => leftOf single (S + n) 0 j
  have vcell : ∀ n, v n 0 = Rule30Jen.cell (S + n) (-1) := by
    intro n
    show evolve single (S + n) (0 - 1 - ((0 : Nat) : Int)) = _
    rw [evolve_single_eq_cell, show (0 : Int) - 1 - ((0 : Nat) : Int) = -1 by omega]
  have step : ∀ n, v (n + 1) = held (v n) := by
    intro n
    funext j
    cases j with
    | zero =>
      show leftOf single (S + n + 1) 0 0 = held (leftOf single (S + n) 0) 0
      rw [left_kicked_zero]
      have quiet : (evolve single (S + n) 0 && evolve single (S + n + 1) 0) = false := by
        rw [evolve_single_center, evolve_single_center, h (S + n) (by omega), h (S + n + 1) (by omega)]
        by_cases hx : (S + n - T) % 4 = 3
        · have hy : ¬ (S + n + 1 - T) % 4 = 3 := by omega
          simp [hy]
        · simp [hx]
      rw [quiet, Bool.xor_false]
    | succ j => exact left_kicked_succ single 0 (S + n) j
  have orbit : ∀ n, heldOrbit (v 0) n = v n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => show held (heldOrbit (v 0) n) = v (n + 1); rw [ih, step n]
  have edge := left_edge single 0 rfl (fun x hx => decide_eq_false (by omega)) S
  refine ⟨v 0, ⟨S - 1, ?_⟩, ⟨S, fun j hj => ?_⟩, fun s => ?_⟩
  · show evolve single (S + 0) (0 - 1 - ((S - 1 : Nat) : Int)) = true
    rw [show S + 0 = S by omega, show (0 : Int) - 1 - ((S - 1 : Nat) : Int) = 0 - (S : Int) by omega]
    exact edge.1
  · show evolve single (S + 0) (0 - 1 - (j : Int)) = false
    rw [show S + 0 = S by omega]
    exact edge.2 _ (by omega)
  · rw [orbit, orbit, orbit, orbit, orbit, vcell, vcell, vcell, vcell, vcell]
    refine ⟨((hsk _ (by omega)).1 (by omega)).2.2, ((hsk _ (by omega)).2.2.1 (by omega)).2,
      ((hsk _ (by omega)).2.2.2 (by omega)).2.2, fun h1 => ?_⟩
    have e1 := ((hsk (S + (4 * s + 1)) (by omega)).2.1 (by omega)).2
    have e5 := ((hsk (S + (4 * s + 5)) (by omega)).2.1 (by omega)).2
    rw [e5, show S + (4 * s + 5) = S + (4 * s + 1) + 4 by omega]
    exact hno _ (by omega) (by omega) (by rw [← e1]; exact h1)

/-- Official form, as a question about integers: if the prize's center column repeats `0001` from `T` on, some
positive integer is even at the steps `4s` and `4s + 2` of its orbit under `heldNat`, odd at the steps `4s + 3`, and
never odd at two steps `4s + 1` and `4s + 5`. -/
theorem center_period_four_0001_integer (T : Nat)
    (h : ∀ t : Nat, T ≤ t → Rule30Prize.center t = decide ((t - T) % 4 = 3)) :
    ∃ U : Nat, 0 < U ∧ ∀ s, Nat.repeat heldNat (4 * s) U % 2 = 0 ∧ Nat.repeat heldNat (4 * s + 2) U % 2 = 0 ∧
      Nat.repeat heldNat (4 * s + 3) U % 2 = 1 ∧
      (Nat.repeat heldNat (4 * s + 1) U % 2 = 1 → Nat.repeat heldNat (4 * s + 5) U % 2 = 0) := by
  obtain ⟨u, ⟨j0, hj0⟩, ⟨N, hN⟩, hfit⟩ := period_four_0001_held T h
  have bit : ∀ n, Nat.repeat heldNat n (natOf u N) % 2 = if heldOrbit u n 0 then 1 else 0 := by
    intro n
    have hb := heldNat_repeat u N hN n 0
    rw [Nat.testBit_zero] at hb
    cases hu : heldOrbit u n 0 <;> rw [hu] at hb <;> simp at hb <;> simp [hb]
  refine ⟨natOf u N, ?_, fun s => ?_⟩
  · have hj0N : j0 < N := by
      by_cases hc : j0 < N
      · exact hc
      · rw [hN j0 (by omega)] at hj0; exact absurd hj0 Bool.false_ne_true
    have hbit := natOf_testBit N u j0
    rw [hj0, show decide (j0 < N) = true from decide_eq_true hj0N] at hbit
    exact Nat.pos_of_ne_zero (fun h0 => by rw [h0] at hbit; simp at hbit)
  · obtain ⟨f0, f2, f3, f1⟩ := hfit s
    rw [bit, bit, bit, bit, bit, f0, f2, f3]
    refine ⟨rfl, rfl, rfl, fun h1 => ?_⟩
    cases h5 : heldOrbit u (4 * s + 1) 0
    · rw [h5] at h1; simp at h1
    · rw [f1 h5]; rfl

/-! ### The ether is the domain -/

/-- The kit's ether read leftward from its second `0001` column: bit `j` at phase `φ` is the ether column `j + 1`
places left of it, column `(5 - j) mod 7` of the table `B1 B2 B3 B4 B5 c c`. -/
def etherLeft (φ j : Nat) : Bool := Rule30Ether.ether (5 + 6 * j) φ

theorem etherLeft_congr {φ φ' j j' : Nat} (hφ : φ % 4 = φ' % 4) (hj : j % 7 = j' % 7) :
    etherLeft φ j = etherLeft φ' j' :=
  Rule30Ether.ether_congr (by omega) hφ

theorem held_etherLeft_small : ∀ φ, φ < 4 → ∀ j, j < 8 → held (etherLeft φ) j = etherLeft (φ + 1) j := by decide

/-- The ether's left half is a 4-cycle of `held`: one step of Rule 30 beside a column held at 0 moves it on one phase.
The ether's own column is `0001`, black only where the cell left of it is black, so holding it at 0 changes
nothing. -/
theorem held_etherLeft (φ : Nat) : held (etherLeft φ) = etherLeft (φ + 1) := by
  funext j
  have hφ : φ % 4 < 4 := Nat.mod_lt _ (by decide)
  cases j with
  | zero =>
    have e := held_etherLeft_small (φ % 4) hφ 0 (by decide)
    show xor (etherLeft φ 1) (etherLeft φ 0) = etherLeft (φ + 1) 0
    rw [etherLeft_congr (φ := φ) (φ' := φ % 4) (j := 1) (j' := 1) (by omega) rfl,
      etherLeft_congr (φ := φ) (φ' := φ % 4) (j := 0) (j' := 0) (by omega) rfl,
      etherLeft_congr (φ := φ + 1) (φ' := φ % 4 + 1) (j := 0) (j' := 0) (by omega) rfl]
    exact e
  | succ j =>
    have e := held_etherLeft_small (φ % 4) hφ (j % 7 + 1) (by omega)
    show xor (etherLeft φ (j + 2)) (etherLeft φ (j + 1) || etherLeft φ j) = etherLeft (φ + 1) (j + 1)
    rw [etherLeft_congr (φ := φ) (φ' := φ % 4) (j := j + 2) (j' := j % 7 + 2) (by omega) (by omega),
      etherLeft_congr (φ := φ) (φ' := φ % 4) (j := j + 1) (j' := j % 7 + 1) (by omega) (by omega),
      etherLeft_congr (φ := φ) (φ' := φ % 4) (j := j) (j' := j % 7) (by omega) (by omega),
      etherLeft_congr (φ := φ + 1) (φ' := φ % 4 + 1) (j := j + 1) (j' := j % 7 + 1) (by omega) (by omega)]
    exact e

theorem etherLeft_orbit (φ : Nat) : ∀ n, heldOrbit (etherLeft φ) n = etherLeft (φ + n)
  | 0 => rfl
  | n + 1 => by
    show held (heldOrbit (etherLeft φ) n) = etherLeft (φ + (n + 1))
    rw [etherLeft_orbit φ n, held_etherLeft]
    rfl

/-- Next to the column the ether reads `0001`. -/
theorem etherLeft_zero (n : Nat) : etherLeft n 0 = decide (n % 4 = 3) := by
  rw [etherLeft_congr (φ' := n % 4) (j' := 0) (by omega) rfl]
  have : ∀ ψ, ψ < 4 → etherLeft ψ 0 = decide (ψ % 4 = 3) := by decide
  rw [this _ (Nat.mod_lt _ (by decide)), Nat.mod_mod]

/-- The finiteness in `center_period_four_0001_integer` cannot be dropped: the ether's left half, an infinite half,
keeps the condition forever, with every free bit white. -/
theorem ether_fits (s : Nat) :
    heldOrbit (etherLeft 0) (4 * s) 0 = false ∧ heldOrbit (etherLeft 0) (4 * s + 1) 0 = false ∧
      heldOrbit (etherLeft 0) (4 * s + 2) 0 = false ∧ heldOrbit (etherLeft 0) (4 * s + 3) 0 = true := by
  simp only [etherLeft_orbit, etherLeft_zero]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp <;> omega

/-- The countdown near the ether: a half that agrees with the ether's left half at phase `φ` on exactly its `k` lowest
bits follows the ether's pattern next to the column for exactly `k` steps and leaves it at step `k`. -/
theorem ether_countdown (k : Nat) : ∀ (φ : Nat) (u : Nat → Bool), (∀ j, j < k → u j = etherLeft φ j) →
    u k = !etherLeft φ k →
    (∀ n, n < k → heldOrbit u n 0 = etherLeft (φ + n) 0) ∧ heldOrbit u k 0 = !etherLeft (φ + k) 0 := by
  induction k with
  | zero =>
    intro φ u _ hd
    exact ⟨fun n hn => absurd hn (by omega), by show u 0 = _; rw [hd]; rfl⟩
  | succ k ih =>
    intro φ u hk hd
    obtain ⟨hagree, hnext⟩ := held_disagree u (etherLeft φ) k hk hd
    rw [held_etherLeft] at hagree hnext
    obtain ⟨hlive, hdead⟩ := ih (φ + 1) (held u) hagree hnext
    refine ⟨fun n hn => ?_, ?_⟩
    · cases n with
      | zero => show u 0 = _; rw [hk 0 (by omega)]; rfl
      | succ n =>
        rw [heldOrbit_succ, hlive n (by omega), show φ + 1 + n = φ + (n + 1) by omega]
    · rw [heldOrbit_succ, hdead, show φ + 1 + k = φ + (k + 1) by omega]

/-- A spot check of `ether_countdown` on numbers: the ether's left half at phase 0 is the 2-adic `-8/127`, and
`127 * 1032 + 8 = 2^17`, so `1032` (bits 3 and 10) follows the ether's `0001` for 17 steps and reads 1 at step 17,
where the ether reads 0. -/
theorem ether_countdown_spot :
    (List.range 18).map (fun n => Nat.repeat heldNat n 1032 % 2) =
      [0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1] := by decide

/-- Domain B meets the three fixed phases but not the right half's check: its cell next to the column is black at
every odd step, so the free bit is black at every period. -/
theorem domainB_repeats (s : Nat) :
    heldOrbit domainB (4 * s) 0 = false ∧ heldOrbit domainB (4 * s + 2) 0 = false ∧
      heldOrbit domainB (4 * s + 3) 0 = true ∧ heldOrbit domainB (4 * s + 1) 0 = true ∧
      heldOrbit domainB (4 * s + 5) 0 = true := by
  have even : ∀ m, heldOrbit domainB (2 * m) = domainB := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      show held (held (heldOrbit domainB (2 * m))) = domainB
      rw [ih, held_held_domainB]
  have odd : ∀ m, heldOrbit domainB (2 * m + 1) 0 = true := fun m => by
    show held (heldOrbit domainB (2 * m)) 0 = true
    rw [even]; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [show 4 * s = 2 * (2 * s) by omega, even]; rfl
  · rw [show 4 * s + 2 = 2 * (2 * s + 1) by omega, even]; rfl
  · rw [show 4 * s + 3 = 2 * (2 * s + 1) + 1 by omega]; exact odd _
  · rw [show 4 * s + 1 = 2 * (2 * s) + 1 by omega]; exact odd _
  · rw [show 4 * s + 5 = 2 * (2 * s + 2) + 1 by omega]; exact odd _

end Rule30Open
