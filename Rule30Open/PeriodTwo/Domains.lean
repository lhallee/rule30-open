module

public import Rule30Open.PeriodTwo.HeldColumn

/-!
# The alternating domains and the countdown

Two infinite halves keep the held column's condition forever: the alternating halves 1 0 1 0 ... and
0 1 0 1 ... read from the column, the 2-adic numbers -1/3 and -2/3 (`held_domains_odd`). So a proof that
no finite half keeps the condition must use that the half is finite.

The first domain also times the condition: a half that agrees with it on exactly its `k` lowest bits reads
1 next to the column for exactly `k` steps, then 0 (`held_countdown`). As a number `U`, `k` is the 2-adic
valuation of `3U + 1`. Both domains time it, because the lowest bit at which two halves differ moves one
bit toward the column a step (`held_disagree`): a stretch of the second domain shrinks by two bits every
two steps (`held_agree_stepB`).

The natural-language argument is `Domains.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

/-- Domain A, the cells left of the column reading 1 0 1 0 ..., a fixed point of `held`. -/
def domainA (j : Nat) : Bool := j % 2 == 0

/-- Domain B, the cells left of the column reading 0 1 0 1 ..., a 2-cycle of `held`. -/
def domainB (j : Nat) : Bool := j % 2 == 1

theorem held_domainA : held domainA = domainA := by
  funext j
  cases j with
  | zero => rfl
  | succ j =>
    show xor (domainA (j + 2)) (domainA (j + 1) || domainA j) = domainA (j + 1)
    unfold domainA
    rcases Nat.mod_two_eq_zero_or_one j with h | h
    · rw [show (j + 2) % 2 = 0 by omega, show (j + 1) % 2 = 1 by omega, h]; rfl
    · rw [show (j + 2) % 2 = 1 by omega, show (j + 1) % 2 = 0 by omega, h]; rfl

theorem held_held_domainB : held (held domainB) = domainB := by
  funext j
  match j with
  | 0 => rfl
  | 1 => rfl
  | j + 2 =>
    show xor (held domainB (j + 3)) (held domainB (j + 2) || held domainB (j + 1)) = domainB (j + 2)
    show xor (xor (domainB (j + 4)) (domainB (j + 3) || domainB (j + 2)))
      (xor (domainB (j + 3)) (domainB (j + 2) || domainB (j + 1)) ||
        xor (domainB (j + 2)) (domainB (j + 1) || domainB j)) = domainB (j + 2)
    unfold domainB
    rcases Nat.mod_two_eq_zero_or_one j with h | h
    · rw [show (j + 4) % 2 = 0 by omega, show (j + 3) % 2 = 1 by omega, show (j + 2) % 2 = 0 by omega,
        show (j + 1) % 2 = 1 by omega, h]; rfl
    · rw [show (j + 4) % 2 = 1 by omega, show (j + 3) % 2 = 0 by omega, show (j + 2) % 2 = 1 by omega,
        show (j + 1) % 2 = 0 by omega, h]; rfl

/-- The finiteness in `period_two_held` cannot be dropped: both domains, infinite halves, read 1 next to the held
column at every odd step, so any proof that no finite half does must use that it is finite. -/
theorem held_domains_odd (s : Nat) :
    heldOrbit domainA (2 * s + 1) 0 = true ∧ heldOrbit domainB (2 * s + 1) 0 = true := by
  have hA : ∀ n, heldOrbit domainA n = domainA := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => show held (heldOrbit domainA n) = domainA; rw [ih, held_domainA]
  have hB : ∀ s, heldOrbit domainB (2 * s) = domainB := by
    intro s
    induction s with
    | zero => rfl
    | succ s ih =>
      show held (held (heldOrbit domainB (2 * s))) = domainB
      rw [ih, held_held_domainB]
  refine ⟨by rw [hA]; rfl, ?_⟩
  show held (heldOrbit domainB (2 * s)) 0 = true
  rw [hB]; rfl

/-- One step on from a half that agrees with domain A on its `k + 1` lowest bits and not on the next, the half agrees
on `k` bits and not on the next: the stretch of domain A beside the column shrinks by one bit a step. -/
theorem held_agree_step (u : Nat → Bool) (k : Nat) (hk : ∀ j, j < k + 1 → u j = domainA j)
    (hd : u (k + 1) = !domainA (k + 1)) :
    (∀ j, j < k → held u j = domainA j) ∧ held u k = !domainA k := by
  constructor
  · intro j hj
    rw [← held_domainA]
    cases j with
    | zero => simp only [held, hk 1 (by omega), hk 0 (by omega)]
    | succ j => simp only [held, hk (j + 2) (by omega), hk (j + 1) (by omega), hk j (by omega)]
  · conv => rhs; rw [← held_domainA]
    cases k with
    | zero =>
      simp only [held, hd, hk 0 (by omega)]
      cases domainA 1 <;> cases domainA 0 <;> rfl
    | succ k =>
      simp only [held, hd, hk (k + 1) (by omega), hk k (by omega)]
      cases domainA (k + 2) <;> cases (domainA (k + 1) || domainA k) <;> rfl

/-- The orbit from `held u` is the orbit from `u`, one step on. -/
theorem heldOrbit_succ (u : Nat → Bool) : ∀ n, heldOrbit u (n + 1) = heldOrbit (held u) n
  | 0 => rfl
  | n + 1 => by
    show held (heldOrbit u (n + 1)) = held (heldOrbit (held u) n)
    rw [heldOrbit_succ u n]

/-- The countdown: a half that agrees with domain A on exactly its `k` lowest bits keeps the cell next to the column
at 1 for exactly `k` steps and then reads 0 there. As a number `U`, `k` is the 2-adic valuation of `3U + 1`, since
domain A is `-1/3`; so while a stretch of domain A lasts, the condition holds by itself, and it fails at the stretch's
end when that end falls on an odd step. -/
theorem held_countdown (k : Nat) : ∀ (u : Nat → Bool), (∀ j, j < k → u j = domainA j) → u k = !domainA k →
    (∀ s, s < k → heldOrbit u s 0 = true) ∧ heldOrbit u k 0 = false := by
  induction k with
  | zero =>
    intro u _ hd
    exact ⟨fun s hs => absurd hs (by omega), by show u 0 = false; rw [hd]; rfl⟩
  | succ k ih =>
    intro u hk hd
    obtain ⟨hagree, hnext⟩ := held_agree_step u k hk hd
    obtain ⟨hlive, hdead⟩ := ih (held u) hagree hnext
    refine ⟨fun s hs => ?_, by rw [heldOrbit_succ]; exact hdead⟩
    cases s with
    | zero => show u 0 = true; rw [hk 0 (by omega)]; rfl
    | succ s => rw [heldOrbit_succ]; exact hlive s (by omega)

/-- A spot check of `held_countdown` on numbers: `85` (binary 1010101) agrees with domain A on bits 0 to 7 and not on
bit 8, and `3 * 85 + 1 = 256 = 2^8`, so its orbit is odd at steps 0 to 7 and even at step 8. -/
theorem held_countdown_spot :
    (List.range 9).map (fun n => Nat.repeat heldNat n 85 % 2) = [1, 1, 1, 1, 1, 1, 1, 1, 0] := by decide

/-- The lowest disagreement moves one bit toward the column at every step: halves that agree on their `k + 1`
lowest bits and differ at the next agree on their `k` lowest bits one step later and differ at the next, since the
bit there is the differing bit plus an "or" the two halves share. -/
theorem held_disagree (u v : Nat → Bool) (k : Nat) (hk : ∀ j, j < k + 1 → u j = v j)
    (hd : u (k + 1) = !v (k + 1)) : (∀ j, j < k → held u j = held v j) ∧ held u k = !held v k := by
  constructor
  · intro j hj
    cases j with
    | zero => simp only [held, hk 1 (by omega), hk 0 (by omega)]
    | succ j => simp only [held, hk (j + 2) (by omega), hk (j + 1) (by omega), hk j (by omega)]
  · cases k with
    | zero =>
      simp only [held, hd, hk 0 (by omega)]
      cases v 1 <;> cases v 0 <;> rfl
    | succ k =>
      simp only [held, hd, hk (k + 1) (by omega), hk k (by omega)]
      cases v (k + 2) <;> cases (v (k + 1) || v k) <;> rfl

/-- So a half that agrees with domain B (`-2/3`) on exactly its `m + 2` lowest bits agrees with it on exactly `m`
two steps later: a stretch of B beside the column shrinks by two bits every two steps, as a stretch of A shrinks by
one bit a step (`held_agree_step`). -/
theorem held_agree_stepB (u : Nat → Bool) (m : Nat) (hk : ∀ j, j < m + 2 → u j = domainB j)
    (hd : u (m + 2) = !domainB (m + 2)) :
    (∀ j, j < m → held (held u) j = domainB j) ∧ held (held u) m = !domainB m := by
  obtain ⟨h1, h1d⟩ := held_disagree u domainB (m + 1) hk hd
  obtain ⟨h2, h2d⟩ := held_disagree (held u) (held domainB) m h1 h1d
  rw [held_held_domainB] at h2 h2d
  exact ⟨h2, h2d⟩

end Rule30Open
