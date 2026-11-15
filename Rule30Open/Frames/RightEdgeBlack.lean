module

public import Ruliology.CellularAutomata.Rule30RightPeriods

/-!
# Black cells forced by the doubling right diagonals

`R j t = cell t (t - j)` is the single cell's right diagonal `j`, and `E j = leastExp j` the least `e` with period
`2 ^ e` (the kit's `Rule30RightPeriods`). `cnt f a n` counts the black cells of `f` at times `a, …, a + n - 1`.

* `doubling_black`: if the exponent grows at diagonal `j + 1` (`E (j + 1) = E j + 1`), then over any multiple
  `2 ^ E (j + 1) * m` of its period, from any start, diagonal `j + 1` has exactly `2 ^ E j * m` black cells: half.
  This is the kit's `half_black`, repeated over the periods.
* `leastExp_mono`: `E` is monotone.
* `strip_black`: over one period `L = 2 ^ E N` of the first `N + 1` diagonals, for every `J ≤ N`,
  `L * (2 + E J) ≤ 2 * (black cells of diagonals 0 … J over times 0 … L - 1)`. In particular, for `J = N`,
  the black density of the first `N + 1` right diagonals over their common period is at least `(2 + E N) / (2 (N + 1))`.
* `strip_white`: likewise `L * E J ≤ 2 * (white cells of diagonals 0 … J over times 0 … L - 1)`.

The natural-language argument is `RightEdgeBlack.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

namespace RightEdgeBlack

open Ruliology.CellularAutomata.Rule30Diagonals Ruliology.CellularAutomata.Rule30RightPeriods

/-- Black cells of diagonals `0 … J - 1` over times `0 … L - 1`. -/
def stripBlack (L : Nat) : Nat → Nat
  | 0 => 0
  | J + 1 => stripBlack L J + cnt (R J) 0 L

theorem cnt_le (f : Nat → Bool) (a : Nat) : ∀ n, cnt f a n ≤ n
  | 0 => Nat.le_refl 0
  | n + 1 => by
    have := cnt_le f a n
    show cnt f a n + (if f (a + n) then 1 else 0) ≤ n + 1
    split <;> omega

theorem cnt_true (f : Nat → Bool) (hf : ∀ t, f t = true) (a : Nat) : ∀ n, cnt f a n = n
  | 0 => rfl
  | n + 1 => by
    show cnt f a n + (if f (a + n) then 1 else 0) = n + 1
    rw [cnt_true f hf a n, hf]; rfl

theorem doubling_black_cell {j : Nat} (h : leastExp (j + 1) = leastExp j + 1) :
    R (j + 1) (2 ^ leastExp j) = true := by
  have hs := e_step (leastExp_spec j) (leastExp_spec (j + 1))
  revert hs
  cases R (j + 1) (2 ^ leastExp j) <;> simp <;> omega

/-- **A doubling diagonal is exactly half black over every multiple of its period.** -/
theorem doubling_black {j : Nat} (h : leastExp (j + 1) = leastExp j + 1) (a : Nat) :
    ∀ m, cnt (R (j + 1)) a (2 ^ leastExp (j + 1) * m) = 2 ^ leastExp j * m
  | 0 => by simp [cnt]
  | m + 1 => by
    rw [Nat.mul_succ, cnt_add, doubling_black h a m, h,
      half_black (leastExp_spec j).1 (doubling_black_cell h), Nat.mul_succ]

theorem leastExp_mono {i : Nat} : ∀ j, i ≤ j → leastExp i ≤ leastExp j
  | 0, hij => by rw [show i = 0 by omega]; exact Nat.le_refl _
  | j + 1, hij => by
    rcases Nat.eq_or_lt_of_le hij with rfl | hlt
    · exact Nat.le_refl _
    · exact Nat.le_trans (leastExp_mono j (by omega)) (e_mono (leastExp_spec j) (leastExp_spec (j + 1)))

/-- **Over one period `L = 2 ^ E N`, the doubling diagonals force `L * (2 + E J) ≤ 2 * black`.** -/
theorem strip_black (N : Nat) : ∀ J, J ≤ N →
    2 ^ leastExp N * (2 + leastExp J) ≤ 2 * stripBlack (2 ^ leastExp N) (J + 1)
  | 0, _ => by
    show 2 ^ leastExp N * (2 + leastExp 0) ≤ 2 * (0 + cnt (R 0) 0 (2 ^ leastExp N))
    rw [leastExp_zero, cnt_true (R 0) R_zero]
    omega
  | J + 1, hJ => by
    have ih := strip_black N J (by omega)
    show 2 ^ leastExp N * (2 + leastExp (J + 1)) ≤
      2 * (stripBlack (2 ^ leastExp N) (J + 1) + cnt (R (J + 1)) 0 (2 ^ leastExp N))
    have hs := e_step (leastExp_spec J) (leastExp_spec (J + 1))
    by_cases hd : leastExp (J + 1) = leastExp J + 1
    · have hle : leastExp (J + 1) ≤ leastExp N := leastExp_mono N hJ
      have hL : 2 ^ leastExp N = 2 ^ leastExp (J + 1) * 2 ^ (leastExp N - leastExp (J + 1)) := by
        rw [← Nat.pow_add, show leastExp (J + 1) + (leastExp N - leastExp (J + 1)) = leastExp N by omega]
      have hc := doubling_black hd 0 (2 ^ (leastExp N - leastExp (J + 1)))
      rw [← hL] at hc
      rw [hc]
      have h2 : 2 ^ leastExp N = 2 * (2 ^ leastExp J * 2 ^ (leastExp N - leastExp (J + 1))) := by
        rw [hL, hd, Nat.pow_succ]
        rw [Nat.mul_comm (2 ^ leastExp J) 2, Nat.mul_assoc]
      rw [hd, Nat.mul_add, Nat.mul_add] at *
      have : 2 ^ leastExp N * (leastExp J + 1) = 2 ^ leastExp N * leastExp J + 2 ^ leastExp N := Nat.mul_succ _ _
      omega
    · have he : leastExp (J + 1) = leastExp J := by
        revert hs; split <;> omega
      rw [he]
      omega

/-- White cells of diagonals `0 … J - 1` over times `0 … L - 1`. -/
def stripWhite (L : Nat) : Nat → Nat
  | 0 => 0
  | J + 1 => stripWhite L J + cnt (fun t => !R J t) 0 L

theorem cnt_not (f : Nat → Bool) (a : Nat) : ∀ n, cnt f a n + cnt (fun t => !f t) a n = n
  | 0 => rfl
  | n + 1 => by
    have := cnt_not f a n
    show cnt f a n + (if f (a + n) then 1 else 0) + (cnt (fun t => !f t) a n + (if !f (a + n) then 1 else 0)) = n + 1
    cases f (a + n) <;> simp <;> omega

/-- **Over one period `L = 2 ^ E N`, the doubling diagonals force `L * E J ≤ 2 * white`.** -/
theorem strip_white (N : Nat) : ∀ J, J ≤ N →
    2 ^ leastExp N * leastExp J ≤ 2 * stripWhite (2 ^ leastExp N) (J + 1)
  | 0, _ => by rw [leastExp_zero]; omega
  | J + 1, hJ => by
    have ih := strip_white N J (by omega)
    show 2 ^ leastExp N * leastExp (J + 1) ≤
      2 * (stripWhite (2 ^ leastExp N) (J + 1) + cnt (fun t => !R (J + 1) t) 0 (2 ^ leastExp N))
    have hs := e_step (leastExp_spec J) (leastExp_spec (J + 1))
    by_cases hd : leastExp (J + 1) = leastExp J + 1
    · have hle : leastExp (J + 1) ≤ leastExp N := leastExp_mono N hJ
      have hL : 2 ^ leastExp N = 2 ^ leastExp (J + 1) * 2 ^ (leastExp N - leastExp (J + 1)) := by
        rw [← Nat.pow_add, show leastExp (J + 1) + (leastExp N - leastExp (J + 1)) = leastExp N by omega]
      have hc := doubling_black hd 0 (2 ^ (leastExp N - leastExp (J + 1)))
      rw [← hL] at hc
      have hn := cnt_not (R (J + 1)) 0 (2 ^ leastExp N)
      have h2 : 2 ^ leastExp N = 2 * (2 ^ leastExp J * 2 ^ (leastExp N - leastExp (J + 1))) := by
        rw [hL, hd, Nat.pow_succ]
        rw [Nat.mul_comm (2 ^ leastExp J) 2, Nat.mul_assoc]
      rw [hd]
      have : 2 ^ leastExp N * (leastExp J + 1) = 2 ^ leastExp N * leastExp J + 2 ^ leastExp N := Nat.mul_succ _ _
      omega
    · have he : leastExp (J + 1) = leastExp J := by
        revert hs; split <;> omega
      rw [he]
      omega

end RightEdgeBlack

end Rule30Open
