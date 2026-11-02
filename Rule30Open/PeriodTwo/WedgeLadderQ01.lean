module

public import Rule30Open.PeriodTwo.WedgeLadder
public import Ruliology.CellularAutomata.Rule30PeriodTwo

/-!
# The binary constant-tail separator is the kit's `Q01`, so `BWH` excludes period two of the center column

The kit's `Rule30PeriodTwo.Q01` asks that no start `s` of the zero-driven left half `L (fun _ => false) s` with a
leftmost black cell keep column `-1` black at every even step. For such a start, write `H t p` for the cell at step `t`
and column `p < 0` (column `0` held white), and `zpair s t i` for the pair `(H t i, H t (i - 1))` encoded as a symbol
(`encodePair`, the kit's encoding). The endpoint stream is `zend s j = zpair s (2j + 1) (-1)`, the pair of columns
`-1, -2` at the odd steps.

* `zpair_backward`: rule 30 at columns `i - 1`, `i - 2` is the kit's backward step,
  `phi (zpair t i) (zpair (t + 1) (i - 1)) = zpair t (i - 2)` for `i ≤ 0`.
* If column `-1` is black at every even step: `zend_boundary` (`boundary (zend j) = zpair (2j) (-2)`), the cone chart
  `zcone_chart` (`cone (zend s) n j = zpair (2j + n) (-(n + 2))`), the peel chart `zpeel_chart`
  (`peelPow d (inverse (zend s)) t = zpair t (-(2d + t + 2))`), and `zend_binary`: every symbol of the endpoint is
  binary. The binary property uses column `0` held white at the odd steps and column `-1` black at the even ones, and
  nothing else: no right half and no hard-core property enter.
* `zend_finite_rank`: with a leftmost black cell at `-m`, `peelPow m (inverse (zend s))` is identically `0`.
* `binaryCTS_Q01`: **`BinaryCTS` implies `Q01`.** With `WedgeLadder`: `bwh_Q01` and `weakBWH_Q01`, and through the kit's
  `not_eventually_period_two_of_Q01`, `center_not_eventually_period_two_of_bwh` and
  `center_not_eventually_period_two_of_weakBWH`: the official center column is not eventually of period two.
* `q01_binaryCTS`: **`Q01` implies `BinaryCTS`.** A binary stream whose inverse is constant `c ∈ {2, 3}` from step `N` on
  is the endpoint of a history (`hpair`, `hcell`): column `0` white, column `-1` black at the even steps, the stream at
  the odd steps, the cone inside the light cone and white beyond. The history obeys rule 30 from step `N` on
  (`hcell_rule`): inside the cone by the cone's recursion, on its edge because `phi c c = 0`, beyond it because
  `phi 0 0 = 0`. Its row at step `2N` is a start of `Q01` (`hstart`, `zl_hstart`) whose leftmost black cell is at
  `-(2N + 2)` or `-(2N + 3)`.
* `binaryCTS_iff_Q01`, `q01_iff_horizon`: `Q01` is `BinaryCTS`, and it is `WeakBWH` at every depth with some horizon.
  `q01_constantTailSeparator`: `Q01` implies the kit's `ConstantTailSeparator`.

The chart restates the kit main's `Rule30SEPToPeriodTwo` (`encodePair`, `pair_inverse_table`, `pair_backward`,
`actual_boundary`, `actual_cone_chart`, `actual_peel_chart`, `actual_endpoint_binary`) on the zero-driven left half of
the pinned kit, with time shifted so that the even steps are the black steps of column `-1`. Nothing here proves `BWH`,
`BinaryCTS` or `Q01`.

The natural-language argument is `WedgeLadderQ01.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open
namespace WedgeLadder

open WedgeKit
open Ruliology.CellularAutomata
open Ruliology.CellularAutomata.Rule30DrivenLeft (L L_succ L_col0 edge)

/-! ### The kit's pair encoding (kit main `Rule30SEPToPeriodTwo`, verbatim) -/

def encodePair : Bool → Bool → Sym
  | false,false => 0
  | false,true => 1
  | true,false => 2
  | true,true => 3

theorem pair_inverse_table : ∀ a b c d : Bool,
    phi (encodePair a b)
      (encodePair (xor c (b || a)) (xor d (c || b)))=encodePair c d := by decide

theorem encode_xor_binary : ∀ a b : Bool, xor b a=true → binary (encodePair a b) := by
  unfold binary
  decide

/-! ### The chart of the zero-driven left half -/

/-- The zero-driven left half of the kit's `Q01`. -/
abbrev zl (s : Int → Bool) : Nat → Int → Bool := L (fun _ => false) s

/-- The pair of columns `i, i - 1` at step `t`, as a symbol. -/
def zpair (s : Int → Bool) (t : Nat) (i : Int) : Sym := encodePair (zl s t i) (zl s t (i-1))

/-- The endpoint stream: the pair of columns `-1, -2` at the odd steps. -/
def zend (s : Int → Bool) : Stream := fun j => zpair s (2*j+1) (-1)

theorem zl_succ (s : Int → Bool) (t : Nat) (p : Int) (hp : p < 0) :
    zl s (t+1) p = xor (zl s t (p-1)) (zl s t p || zl s t (p+1)) :=
  L_succ hp

/-- **Rule 30 at columns `i - 1`, `i - 2` is the kit's backward step.** -/
theorem zpair_backward (s : Int → Bool) (t : Nat) (i : Int) (hi : i ≤ 0) :
    phi (zpair s t i) (zpair s (t+1) (i-1)) = zpair s t (i-2) := by
  have e1 := zl_succ s t (i-1) (by omega)
  have e2 := zl_succ s t (i-2) (by omega)
  rw [show i-1-1 = i-2 by omega, show i-1+1 = i by omega] at e1
  rw [show i-2-1 = i-3 by omega, show i-2+1 = i-1 by omega] at e2
  unfold zpair
  rw [show i-1-1 = i-2 by omega, show i-2-1 = i-3 by omega, e1, e2]
  exact pair_inverse_table _ _ _ _

section Chart

variable (s : Int → Bool) (hA : ∀ k, zl s (2*k) (-1) = true)
include hA

/-- **The pin.** The boundary of the endpoint is the pair of columns `-2, -3` at the even steps. -/
theorem zend_boundary (j : Nat) : boundary (zend s j) = zpair s (2*j) (-2) := by
  have h1 := zl_succ s (2*j) (-1) (by omega)
  have h2 := zl_succ s (2*j) (-2) (by omega)
  rw [show (-1 : Int) - 1 = -2 by omega, show (-1 : Int) + 1 = 0 by omega, hA j] at h1
  rw [show (-2 : Int) - 1 = -3 by omega, show (-2 : Int) + 1 = -1 by omega, hA j] at h2
  unfold zend zpair
  rw [show (-1 : Int) - 1 = -2 by omega, show (-2 : Int) - 1 = -3 by omega, h1, h2]
  cases zl s (2*j) (-2) <;> cases zl s (2*j) (-3) <;> rfl

/-- **The endpoint is binary.** -/
theorem zend_binary (j : Nat) : binary (zend s j) := by
  have h := hA (j+1)
  rw [show 2*(j+1) = (2*j+1)+1 by omega, zl_succ s (2*j+1) (-1) (by omega),
    show (-1 : Int) + 1 = 0 by omega, show (-1 : Int) - 1 = -2 by omega] at h
  have h0 : zl s (2*j+1) 0 = false := L_col0 _
  rw [h0, Bool.or_false] at h
  unfold zend zpair
  rw [show (-1 : Int) - 1 = -2 by omega]
  exact encode_xor_binary _ _ h

/-- **The cone chart.** -/
theorem zcone_chart (n : Nat) :
    ∀ j, cone (zend s) n j = zpair s (2*j+n) (-((n+2 : Nat) : Int)) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro j
    match n with
    | 0 =>
      simp only [cone]
      rw [zend_boundary s hA j]
      rfl
    | 1 =>
      simp only [cone]
      rw [zend_boundary s hA (j+1)]
      unfold zend
      have h := zpair_backward s (2*j+1) (-1) (by omega)
      rw [show (-1 : Int) - 1 = -2 by omega, show (-1 : Int) - 2 = -3 by omega,
        show 2*j+1+1 = 2*(j+1) by omega] at h
      rw [h]
      rfl
    | n+2 =>
      simp only [cone]
      rw [ih n (by omega), ih (n+1) (by omega)]
      have h := zpair_backward s (2*(j+1)+n) (-((n+2 : Nat) : Int)) (by omega)
      rw [show 2*(j+1)+n+1 = 2*(j+1)+(n+1) by omega,
        show -((n+2 : Nat) : Int) - 1 = -((n+1+2 : Nat) : Int) by omega,
        show -((n+2 : Nat) : Int) - 2 = -((n+2+2 : Nat) : Int) by omega] at h
      rw [show 2*j+(n+2) = 2*(j+1)+n by omega]
      exact h

/-- **The peel chart.** -/
theorem zpeel_chart (d : Nat) :
    ∀ t, peelPow d (inverse (zend s)) t = zpair s t (-((2*d+t+2 : Nat) : Int)) := by
  induction d with
  | zero =>
    intro t
    show cone (zend s) t 0 = _
    rw [zcone_chart s hA t 0]
    congr 1 <;> omega
  | succ d ih =>
    intro t
    show phi (peelPow d (inverse (zend s)) t) (peelPow d (inverse (zend s)) (t+1)) = _
    rw [ih t, ih (t+1)]
    have h := zpair_backward s t (-((2*d+t+2 : Nat) : Int)) (by omega)
    rw [show -((2*d+t+2 : Nat) : Int) - 1 = -((2*d+(t+1)+2 : Nat) : Int) by omega,
      show -((2*d+t+2 : Nat) : Int) - 2 = -((2*(d+1)+t+2 : Nat) : Int) by omega] at h
    exact h

/-- **Finite peel rank.** With a leftmost black cell at `-m`, the `m`-th peel of the inverse of the endpoint is `0`. -/
theorem zend_finite_rank (m : Nat) (hm : 0 < m) (hs0 : ∀ p : Int, p < -(m : Int) → s p = false)
    (hs1 : s (-(m : Int)) = true) (t : Nat) : peelPow m (inverse (zend s)) t = 0 := by
  rw [zpeel_chart s hA m t]
  have hw : ∀ p : Int, p < -((m+t : Nat) : Int) → zl s t p = false :=
    (edge (c := fun _ => false) hs0 hs1 hm t).1
  unfold zpair
  rw [hw _ (by omega), hw _ (by omega)]
  rfl

end Chart

/-! ### The converse: a history from a binary stream -/

/-- The upper and lower cell of a pair. -/
def hiBit (x : Sym) : Bool := decide (2 ≤ x.val)
def loBit (x : Sym) : Bool := decide (x.val % 2 = 1)

theorem encode_hi_lo : ∀ x : Sym, encodePair (hiBit x) (loBit x) = x := by decide
theorem phi_one_boundary : ∀ x : Sym, phi 1 x = boundary x := by decide
theorem phi_self_tail : ∀ c : Sym, constantTail c → phi c c = 0 := by unfold constantTail; decide
theorem binary_lo_hi : ∀ x : Sym, binary x → xor (loBit x) (hiBit x) = true := by unfold binary; decide

/-- `phi (encodePair a b)` is a bijection, and rule 30 is its inverse. -/
theorem pair_forward : ∀ a b c d x y : Bool,
    phi (encodePair a b) (encodePair x y) = encodePair c d → x = xor c (b || a) ∧ y = xor d (c || b) := by
  decide

/-- The pair of columns `-m`, `-(m + 1)` at step `t` (for `m ≡ t` mod 2) of the history of a stream: column `0` white
over column `-1` black at `m = 0`, the stream at `m = 1`, the cone for `2 ≤ m ≤ t + 2`, white beyond. -/
def hpair (e : Stream) (t m : Nat) : Sym :=
  if m = 0 then 1
  else if m = 1 then e (t/2)
  else if m ≤ t + 2 then cone e (m-2) ((t+2-m)/2)
  else 0

/-- Column `-r` at step `t` of the history. -/
def hcell (e : Stream) (t r : Nat) : Bool :=
  if r = 0 then false
  else if r % 2 = t % 2 then hiBit (hpair e t r)
  else loBit (hpair e t (r-1))

theorem hpair_cells (e : Stream) (t m : Nat) (hm : m % 2 = t % 2) :
    hpair e t m = encodePair (hcell e t m) (hcell e t (m+1)) := by
  by_cases h0 : m = 0
  · subst m
    have : ¬ 1 % 2 = t % 2 := by omega
    simp [hcell, hpair, this]
    rfl
  · have h1 : ¬ (m+1) % 2 = t % 2 := by omega
    simp only [hcell, h0, hm, h1, ite_true, ite_false, Nat.add_sub_cancel, Nat.add_eq_zero_iff]
    exact (encode_hi_lo _).symm

/-- **The history obeys the backward step**, at every step from which the inverse is constant. -/
theorem hpair_rel (e : Stream) (c : Sym) (hc : constantTail c) (N : Nat) (hN : ∀ t, N ≤ t → inverse e t = c)
    (t m : Nat) (ht : N ≤ t) (hm : m % 2 = t % 2) :
    phi (hpair e t m) (hpair e (t+1) (m+1)) = hpair e t (m+2) := by
  by_cases h0 : m = 0
  · subst m
    have h2 : (t+1)/2 = t/2 := by omega
    simp only [hpair, ite_true, Nat.add_eq_zero_iff, h2,
      show (2:Nat) ≤ t + 2 by omega, show (2:Nat) - 2 = 0 by rfl, show t + 2 - 2 = t by omega]
    rw [phi_one_boundary]
    rfl
  by_cases h1 : m = 1
  · subst m
    have h3 : (t+2-3)/2 = t/2 := by omega
    have h4 : (t+1+2-2)/2 = t/2+1 := by omega
    simp only [hpair, show ¬ (1:Nat) = 0 by omega, show ¬ (1+1:Nat) = 0 by omega, show ¬ (1+1:Nat) = 1 by omega,
      show ¬ (1+2:Nat) = 0 by omega, show ¬ (1+2:Nat) = 1 by omega, ite_false, ite_true,
      show 1+1 ≤ t+1+2 by omega, show 1+2 ≤ t+2 by omega, show 1+1-2 = 0 by rfl, show 1+2-2 = 1 by rfl, h3,
      Nat.add_sub_cancel] at *
    rw [h4]
    rfl
  by_cases hle : m ≤ t
  · obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
    obtain ⟨j, hj⟩ : ∃ j, t = 2*j + n + 2 := ⟨(t - n - 2)/2, by omega⟩
    subst t
    simp only [hpair, show ¬ n+2 = 0 by omega, show ¬ n+2 = 1 by omega, show ¬ n+2+1 = 0 by omega,
      show ¬ n+2+1 = 1 by omega, show ¬ n+2+2 = 0 by omega, show ¬ n+2+2 = 1 by omega, ite_false,
      show n+2 ≤ 2*j+n+2+2 by omega, show n+2+1 ≤ 2*j+n+2+1+2 by omega, show n+2+2 ≤ 2*j+n+2+2 by omega,
      ite_true, show n+2-2 = n by omega, show n+2+1-2 = n+1 by omega, show n+2+2-2 = n+2 by omega,
      show (2*j+n+2+2-(n+2))/2 = j+1 by omega, show (2*j+n+2+1+2-(n+2+1))/2 = j+1 by omega,
      show (2*j+n+2+2-(n+2+2))/2 = j by omega]
    rfl
  by_cases heq : m = t + 2
  · subst m
    simp only [hpair, show ¬ t+2 = 0 by omega, show ¬ t+2 = 1 by omega, show ¬ t+2+1 = 0 by omega,
      show ¬ t+2+1 = 1 by omega, show ¬ t+2+2 = 0 by omega, show ¬ t+2+2 = 1 by omega, ite_false,
      show t+2 ≤ t+2 by omega, show t+2+1 ≤ t+1+2 by omega, show ¬ t+2+2 ≤ t+2 by omega, ite_true,
      show t+2-2 = t by omega, show t+2+1-2 = t+1 by omega, show (t+2-(t+2))/2 = 0 by omega,
      show (t+1+2-(t+2+1))/2 = 0 by omega]
    have hc0 : cone e t 0 = c := hN t ht
    have hc1 : cone e (t+1) 0 = c := hN (t+1) (by omega)
    rw [hc0, hc1]
    exact phi_self_tail c hc
  · simp only [hpair, show ¬ m = 0 by omega, show ¬ m = 1 by omega, show ¬ m+1 = 0 by omega,
      show ¬ m+1 = 1 by omega, show ¬ m+2 = 0 by omega, show ¬ m+2 = 1 by omega, ite_false,
      show ¬ m ≤ t+2 by omega, show ¬ m+1 ≤ t+1+2 by omega, show ¬ m+2 ≤ t+2 by omega]
    rfl

/-- **The history obeys rule 30** at every column `-r`, `r ≥ 1`, with column `0` white. -/
theorem hcell_rule (e : Stream) (hb : ∀ i, binary (e i)) (c : Sym) (hc : constantTail c) (N : Nat)
    (hN : ∀ t, N ≤ t → inverse e t = c) (t r : Nat) (ht : N ≤ t) (hr : 1 ≤ r) :
    hcell e (t+1) r = xor (hcell e t (r+1)) (hcell e t r || hcell e t (r-1)) := by
  by_cases hp : r % 2 = (t+1) % 2
  · obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
    have hm : m % 2 = t % 2 := by omega
    have hrel := hpair_rel e c hc N hN t m ht hm
    rw [hpair_cells e t m hm, hpair_cells e (t+1) (m+1) (by omega), hpair_cells e t (m+2) (by omega)] at hrel
    rw [(pair_forward _ _ _ _ _ _ hrel).1, Nat.add_sub_cancel]
  · by_cases h1 : r = 1
    · subst r
      have hmod : t % 2 = 1 := by omega
      have hl : hcell e (t+1) 1 = true := by
        simp [hcell, show ¬ 1 % 2 = (t+1) % 2 by omega, hpair]
        rfl
      have ha : hcell e t 1 = hiBit (e (t/2)) := by
        simp [hcell, show 1 % 2 = t % 2 by omega, hpair]
      have hb2 : hcell e t 2 = loBit (e (t/2)) := by
        simp [hcell, show ¬ 2 % 2 = t % 2 by omega, hpair]
      rw [hl, ha, hb2, show 1 - 1 = 0 by rfl]
      simp only [hcell, ite_true, Bool.or_false]
      exact (binary_lo_hi _ (hb _)).symm
    · obtain ⟨m, rfl⟩ : ∃ m, r = m + 2 := ⟨r - 2, by omega⟩
      have hm : m % 2 = t % 2 := by omega
      have hrel := hpair_rel e c hc N hN t m ht hm
      rw [hpair_cells e t m hm, hpair_cells e (t+1) (m+1) (by omega), hpair_cells e t (m+2) (by omega)] at hrel
      rw [(pair_forward _ _ _ _ _ _ hrel).2, show m+2-1 = m+1 by omega]

theorem hcell_far (e : Stream) (t r : Nat) (hr : t + 4 ≤ r) : hcell e t r = false := by
  unfold hcell
  by_cases ha : r % 2 = t % 2
  · simp [show ¬ r = 0 by omega, ha, hpair, show ¬ r = 1 by omega, show ¬ r ≤ t + 2 by omega]
    rfl
  · simp [show ¬ r = 0 by omega, ha, hpair, show ¬ r - 1 = 0 by omega, show ¬ r - 1 = 1 by omega,
      show ¬ r - 1 ≤ t + 2 by omega]
    rfl

/-- The start of the zero-driven left half read off the history at step `T`. -/
def hstart (e : Stream) (T : Nat) : Int → Bool := fun p => hcell e T (-p).toNat

/-- **The history is the zero-driven left half** from step `T` on. -/
theorem zl_hstart (e : Stream) (hb : ∀ i, binary (e i)) (c : Sym) (hc : constantTail c) (N : Nat)
    (hN : ∀ t, N ≤ t → inverse e t = c) (T : Nat) (hT : N ≤ T) :
    ∀ k : Nat, ∀ p : Int, p < 0 → zl (hstart e T) k p = hcell e (T+k) (-p).toNat := by
  intro k
  induction k with
  | zero => intro p hp; exact Rule30DrivenLeft.L_zero hp
  | succ k ih =>
    intro p hp
    rw [zl_succ _ k p hp, ih (p-1) (by omega), ih p hp]
    have hr : zl (hstart e T) k (p+1) = hcell e (T+k) (-(p+1)).toNat := by
      by_cases hp1 : p + 1 < 0
      · exact ih (p+1) hp1
      · rw [show p + 1 = 0 by omega]
        exact (L_col0 k).trans (by simp [hcell])
    rw [hr, show T + (k+1) = (T+k)+1 by omega,
      hcell_rule e hb c hc N hN (T+k) (-p).toNat (by omega) (by omega),
      show (-(p-1)).toNat = (-p).toNat + 1 by omega, show (-(p+1)).toNat = (-p).toNat - 1 by omega]

/-- **`Q01` implies `BinaryCTS`**: a binary stream whose inverse is eventually constant `2` or `3` is the endpoint of a
start of the zero-driven left half that keeps column `-1` black at every even step. -/
theorem q01_binaryCTS_aux (hQ : Rule30PeriodTwo.Q01) : BinaryCTS := by
  intro c hc e hb ⟨N, hN⟩
  let T := 2 * N
  have hT : N ≤ T := by omega
  have hz := zl_hstart e hb c hc N hN T hT
  have hcol : ∀ k, zl (hstart e T) (2*k) (-1) = true := by
    intro k
    rw [hz (2*k) (-1) (by omega)]
    have hT2 : ¬ 1 = T % 2 := by omega
    simp [hcell, hpair, hT2]
    rfl
  have hinv : hpair e T (T+2) = c := by
    simp only [hpair, show ¬ T+2 = 0 by omega, show ¬ T+2 = 1 by omega, ite_false,
      show T+2 ≤ T+2 by omega, ite_true, show T+2-2 = T by omega, show (T+2-(T+2))/2 = 0 by omega]
    exact hN T hT
  have hhi : hcell e T (T+2) = hiBit c := by
    simp only [hcell, show ¬ T+2 = 0 by omega, show (T+2) % 2 = T % 2 by omega, ite_true, ite_false, hinv]
  have hlo : hcell e T (T+3) = loBit c := by
    simp only [hcell, show ¬ T+3 = 0 by omega, show ¬ (T+3) % 2 = T % 2 by omega, ite_false,
      show T+3-1 = T+2 by omega, hinv]
  have hfar : ∀ p : Int, p < -((T+3 : Nat) : Int) → hstart e T p = false := by
    intro p hp
    exact hcell_far e T _ (by omega)
  rcases hc with rfl | rfl
  · refine hQ (T+2) (hstart e T) (by omega) ?_ ?_ hcol
    · intro p hp
      by_cases hp3 : p = -((T+3 : Nat) : Int)
      · subst p
        show hcell e T _ = false
        rw [show (-(-((T+3 : Nat) : Int))).toNat = T+3 by omega, hlo]
        rfl
      · exact hfar p (by omega)
    · show hcell e T _ = true
      rw [show (-(-((T+2 : Nat) : Int))).toNat = T+2 by omega, hhi]
      rfl
  · refine hQ (T+3) (hstart e T) (by omega) hfar ?_ hcol
    show hcell e T _ = true
    rw [show (-(-((T+3 : Nat) : Int))).toNat = T+3 by omega, hlo]
    rfl

end WedgeLadder

open WedgeKit WedgeLadder
open Ruliology.CellularAutomata

/-- **`BinaryCTS` implies the kit's `Q01`.** -/
theorem binaryCTS_Q01 (h : BinaryCTS) : Rule30PeriodTwo.Q01 := by
  intro m s hm hs0 hs1 hA
  exact binaryCTS_excludes_finite_peel_rank h (zend s) (zend_binary s hA) m 0
    (fun t _ => zend_finite_rank s hA m hm hs0 hs1 t)

/-- **`BWH` implies the kit's `Q01`.** -/
theorem bwh_Q01 (hb : BWH) : Rule30PeriodTwo.Q01 := binaryCTS_Q01 (bwh_binaryCTS hb)

/-- **`WeakBWH` on an infinite set of lengths, with any horizon, implies the kit's `Q01`.** -/
theorem weakBWH_Q01 {S : Nat → Prop} {L : Nat → Nat} (hS : ∀ N, ∃ n, N ≤ n ∧ S n) (h : WeakBWH S L) :
    Rule30PeriodTwo.Q01 :=
  binaryCTS_Q01 (weakBWH_binaryCTS hS h)

/-- **`BWH` alone excludes an eventual period two of the official center column.** -/
theorem center_not_eventually_period_two_of_bwh (hb : BWH) :
    ¬ ∃ T0 : Nat, ∀ t : Nat, T0 ≤ t → Rule30Prize.center (t + 2) = Rule30Prize.center t :=
  Rule30PeriodTwo.not_eventually_period_two_of_Q01 (bwh_Q01 hb)

/-- **`WeakBWH` on an infinite set of lengths, with any horizon, excludes an eventual period two of the official center
column.** -/
theorem center_not_eventually_period_two_of_weakBWH {S : Nat → Prop} {L : Nat → Nat}
    (hS : ∀ N, ∃ n, N ≤ n ∧ S n) (h : WeakBWH S L) :
    ¬ ∃ T0 : Nat, ∀ t : Nat, T0 ≤ t → Rule30Prize.center (t + 2) = Rule30Prize.center t :=
  Rule30PeriodTwo.not_eventually_period_two_of_Q01 (weakBWH_Q01 hS h)

/-- **`Q01` implies `BinaryCTS`.** -/
theorem q01_binaryCTS (hQ : Rule30PeriodTwo.Q01) : BinaryCTS := q01_binaryCTS_aux hQ

/-- **`BinaryCTS` is the kit's `Q01`.** -/
theorem binaryCTS_iff_Q01 : BinaryCTS ↔ Rule30PeriodTwo.Q01 := ⟨binaryCTS_Q01, q01_binaryCTS⟩

/-- **`Q01` is `WeakBWH` at every depth with some horizon.** -/
theorem q01_iff_horizon : Rule30PeriodTwo.Q01 ↔ ∃ L : Nat → Nat, WeakBWH (fun _ => True) L :=
  binaryCTS_iff_Q01.symm.trans binaryCTS_iff_horizon

/-- **`Q01` implies the kit's `ConstantTailSeparator`** (`SEP`). -/
theorem q01_constantTailSeparator (hQ : Rule30PeriodTwo.Q01) : ConstantTailSeparator :=
  binaryCTS_constantTailSeparator (q01_binaryCTS hQ)

end Rule30Open
