module

public import Rule30Open.Foundations.Official
public import Ruliology.CellularAutomata.Rule30WhiteEndNine
public import Ruliology.CellularAutomata.Rule30FiniteStrips

/-!
# Tail families after a white run, with windows of 14 cells and a cycle of the white steps

For a tail `u`, the word `0^q u` repeated is the block of [limit windows](../../findings/columns/limit-windows.md).
Watch the 14 cells right of a column with an arbitrary cell beyond them, as in the kit's `Rule30StripCertificates`;
a set of such windows is a bitmask, and the kit's `Rule30WhiteEndNine.fimage` computes the image of a whole set with
`O(K)` operations on numbers of `2 ^ (K + 1)` bits. The powers of the white relation repeat with period 4, and the
white run is pumped along a residue class modulo 4 (the kit's `Rule30WhitePadding.padding_strip` pumps along a fixed
point of the white steps, which these sets reach only from 21 to 32 white steps).

* `invariant_column`: **soundness of a set chain.** In the orbit of a row with a leftmost 1, a column does not
  eventually repeat `w` if sets `C 0 = all windows, C 1, …, C k` satisfy `C n →w C (n+1)`, `C k →w C k` (one period
  maps into the next set) and every white phase of `w` reads one value of the first cell from `C k`. The column at
  the white phases is then periodic, which masked Jen (`Rule30FiniteMaskedJen.masked_jen`) forbids.
* `cycle_column`: **a residue class at once.** `cycleCert K N d k u` follows `k` periods of `0^N u` from all windows
  and checks, at each set `Y` reached after the white run, that `d` more white steps map `Y` into itself. Then the
  white run of `N + d m` steps lands inside the run of `N` steps for every `m`, and the chain of `0^N u` is a chain for
  `0^(N + d m) u`; with `d = 4` this covers a residue class modulo 4, with `d = 0` the single word `0^N u`.
* `tail_family_column`: a tail with pieces that cover every `q ≥ q0` (`tailCert`).
* `short_tails_column`, `center_short_tails`, `not_eventually_short_tails`: for every tail `u` of one to six cells
  that starts and ends with 1, other than `10101`, and every `q ≥ 22`, no column of the orbit of a row with a leftmost
  1 repeats `0^q u` from any time on, in any phase; `tail_thresholds_column` gives the least `q0` of each tail,
  8 to 22, which are those of `limit_windows.tail_thresholds` at 14 cells. The pinned kit has these families from
  `q = 49`, `69` and `74` for tails of at most four, five and six cells (`Rule30ShortTail`, `Rule30FiveTail`,
  `Rule30SixTailSharpened`), with sharper bounds for `1`, `11` and `10111` (`Rule30PaddedWords`); the argument
  compares the thresholds tail by tail, also with the kit's main branch.

The pieces come from `computations/tail_families.py` (`lean_pieces`). The natural-language argument is
`TailFamilies14.md`, beside this file.
-/

@[expose] public section

-- Sequential elaboration: the kernel checks would otherwise run in parallel and stack their memory.
set_option Elab.async false

namespace Rule30Open
namespace TailFamilies14

open Ruliology.CellularAutomata
open Rule30Realization (evol)
open Rule30StripCertificates (stripStep fullSet)
open Rule30WhiteEndNine (fimage fapply fimage_mem fapply_mono fapply_append SubK subB colC subB_spec colC_spec
  colC_mono testBit_fullSet)

/-- `evolve` is the kit's `evol`. -/
theorem evolve_evol (init : Int → Bool) : ∀ t, evolve init t = evol init t
  | 0 => funext fun _ => rfl
  | t + 1 => funext fun x => by
    show rule30 (evolve init t (x - 1)) (evolve init t x) (evolve init t (x + 1)) =
      Rule30Jen.rule (evol init t (x - 1)) (evol init t x) (evol init t (x + 1))
    rw [evolve_evol init t]
    rfl

/-! ### Sets of windows along a column of any row -/

/-- **Soundness of the bit-parallel sets.** If the window at time `t` is in `S` and column `j` reads `u` from `t` on,
the window at time `t + u.length` is in `fapply K u S`. -/
theorem enc_fapply {x : Int → Bool} {K : Nat} {j : Int} :
    ∀ (u : List Bool) (t r S : Nat), Rule30FiniteStrips.Enc x K t j r → S.testBit r = true →
      (∀ s, s < u.length → evol x (t + s) j = u.getD s false) →
      ∃ r', Rule30FiniteStrips.Enc x K (t + u.length) j r' ∧ (fapply K u S).testBit r' = true
  | [], t, r, S, he, hS, _ => ⟨r, he, hS⟩
  | a :: u, t, r, S, he, hS, hu => by
    have ha : evol x t j = a := by simpa using hu 0 (by simp)
    have he1 := Rule30FiniteStrips.enc_step he
    rw [ha] at he1
    have hS1 : (fimage K a S).testBit (stripStep K a (evol x t (j + 1 + K)) r) = true :=
      fimage_mem he.1 hS _
    obtain ⟨r', he', hS'⟩ := enc_fapply u (t + 1) _ _ he1 hS1 (fun s hs => by
      have := hu (s + 1) (by simp; omega)
      rw [show t + (s + 1) = t + 1 + s by omega] at this
      simpa using this)
    refine ⟨r', ?_, hS'⟩
    rw [show t + (a :: u).length = t + 1 + u.length by simp; omega]
    exact he'

/-- The encoding of a window is unique. -/
theorem enc_unique {x : Int → Bool} {K t : Nat} {j : Int} {r r' : Nat} (h : Rule30FiniteStrips.Enc x K t j r)
    (h' : Rule30FiniteStrips.Enc x K t j r') : r = r' := by
  apply Nat.eq_of_testBit_eq
  intro n
  by_cases hn : n < K
  · rw [h.2 n hn, h'.2 n hn]
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h.1 (Nat.pow_le_pow_right (by omega) (by omega))),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h'.1 (Nat.pow_le_pow_right (by omega) (by omega)))]

/-- Every window of `S` has the same first cell. -/
def known (K S : Nat) : Bool := colC K S false || colC K S true

theorem known_mono {K S S' : Nat} (hsub : SubK K S S') (h : known K S' = true) : known K S = true := by
  unfold known at h ⊢
  rcases Bool.or_eq_true_iff.mp h with h | h
  · rw [colC_mono hsub h]; rfl
  · rw [colC_mono hsub h, Bool.or_true]

/-- **Soundness of a set chain**, for every column of every row with a leftmost 1. -/
theorem invariant_column {x : Int → Bool} {lo : Int} (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (w : List Bool) (hw : 0 < w.length) (K k : Nat) (hK : 1 ≤ K) (C : Nat → Nat)
    (hC0 : C 0 = fullSet K)
    (hstep : ∀ n, n < k → SubK K (fapply K w (C n)) (C (n + 1)))
    (hclose : SubK K (fapply K w (C k)) (C k))
    (hforce : ∀ φ, φ < w.length → w.getD φ false = false → known K (fapply K (w.take φ) (C k)) = true) :
    ¬ Rule30FiniteStrips.EventuallyWord x i w := by
  rintro ⟨T, hT⟩
  have hblock : ∀ m s, s < w.length → evol x (T + m * w.length + s) i = w.getD s false := by
    intro m s hs
    rw [hT _ (by omega), show T + m * w.length + s - T = s + m * w.length by omega,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hs]
  let R : Nat → Nat := fun n => Rule30FiniteStrips.encRow x (T + n * w.length) i K
  have hR : ∀ n, Rule30FiniteStrips.Enc x K (T + n * w.length) i (R n) :=
    fun n => Rule30FiniteStrips.enc_encRow K _ i
  have hmove : ∀ n X, X.testBit (R n) = true → (fapply K w X).testBit (R (n + 1)) = true := by
    intro n X hX
    obtain ⟨r', he', hS'⟩ := enc_fapply w _ (R n) X (hR n) hX (fun s hs => hblock n s hs)
    rw [show T + n * w.length + w.length = T + (n + 1) * w.length by rw [Nat.succ_mul]; omega] at he'
    rw [enc_unique (hR (n + 1)) he']
    exact hS'
  have hwarm : ∀ n, n ≤ k → (C n).testBit (R n) = true := by
    intro n
    induction n with
    | zero =>
      intro _
      rw [hC0, testBit_fullSet]
      exact decide_eq_true (hR 0).1
    | succ n ih => exact fun hn => hstep n (by omega) _ (hR (n + 1)).1 (hmove n _ (ih (by omega)))
  have hinv : ∀ m, (C k).testBit (R (k + m)) = true := by
    intro m
    induction m with
    | zero => exact hwarm k (Nat.le_refl k)
    | succ m ih => exact hclose _ (hR (k + m + 1)).1 (hmove (k + m) _ ih)
  have hval : ∀ m φ, φ < w.length → ∀ b, colC K (fapply K (w.take φ) (C k)) b = true →
      evol x (T + (k + m) * w.length + φ) (i + 1) = b := by
    intro m φ hφ b hb
    obtain ⟨r', he', hS'⟩ := enc_fapply (w.take φ) _ (R (k + m)) (C k) (hR (k + m)) (hinv m) (fun s hs => by
      rw [List.length_take] at hs
      rw [hblock _ s (by omega)]
      simp [List.getD_eq_getElem?_getD, show s < φ by omega])
    rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hφ)] at he'
    have hcell := he'.2 0 (by omega)
    rw [show i + 1 + ((0 : Nat) : Int) = i + 1 by omega] at hcell
    rw [← hcell]
    exact colC_spec hb he'.1 hS'
  have hkey : ∀ m φ, φ < w.length → w.getD φ false = false →
      evol x (T + (k + (m + 1)) * w.length + φ) (i + 1) = evol x (T + (k + m) * w.length + φ) (i + 1) := by
    intro m φ hφ hwφ
    have hk := hforce φ hφ hwφ
    unfold known at hk
    rcases Bool.or_eq_true_iff.mp hk with hb | hb
    · rw [hval (m + 1) φ hφ false hb, hval m φ hφ false hb]
    · rw [hval (m + 1) φ hφ true hb, hval m φ hφ true hb]
  refine Rule30FiniteMaskedJen.masked_jen hlo hzero i (T := T + k * w.length) (P := w.length) hw ?_ ?_
  · intro t ht
    rw [hT t (by omega), hT (t + w.length) (by omega), show t + w.length - T = (t - T) + w.length by omega,
      Nat.add_mod_right]
  · intro t ht hwt
    have hφ : (t - T) % w.length < w.length := Nat.mod_lt _ hw
    have hwφ : w.getD ((t - T) % w.length) false = false := by rw [← hT t (by omega)]; exact hwt
    have hq : k ≤ (t - T) / w.length := (Nat.le_div_iff_mul_le hw).2 (by omega)
    have hd := Nat.div_add_mod (t - T) w.length
    have e1 : T + (k + ((t - T) / w.length - k)) * w.length + (t - T) % w.length = t := by
      rw [show k + ((t - T) / w.length - k) = (t - T) / w.length by omega, Nat.mul_comm]
      omega
    have e2 : T + (k + ((t - T) / w.length - k + 1)) * w.length + (t - T) % w.length = t + w.length := by
      rw [show k + ((t - T) / w.length - k + 1) = (t - T) / w.length + 1 by omega, Nat.succ_mul, Nat.mul_comm]
      omega
    have := hkey ((t - T) / w.length - k) ((t - T) % w.length) hφ hwφ
    rw [e1, e2] at this
    exact this

/-! ### Pumping the white run along a residue class -/

/-- `n` steps beside 0s. -/
def zf (K n S : Nat) : Nat := fapply K (List.replicate n false) S

theorem zf_add (K a b S : Nat) : zf K (a + b) S = zf K b (zf K a S) := by
  unfold zf
  rw [← List.replicate_append_replicate, fapply_append]

/-- If `d` more white steps map the sets after `N` white steps into themselves, so do `d m` more, for every `m`. -/
theorem zf_pump (K N d X : Nat) (h : SubK K (zf K d (zf K N X)) (zf K N X)) :
    ∀ m, SubK K (zf K (N + d * m) X) (zf K N X)
  | 0 => by
    rw [Nat.mul_zero, Nat.add_zero]
    exact Rule30WhiteEndNine.SubK.refl K _
  | m + 1 => by
    rw [Nat.mul_succ, ← Nat.add_assoc, zf_add]
    exact Rule30WhiteEndNine.SubK.trans (fapply_mono K _ (zf_pump K N d X h m)) h

/-- The first cell is known after each of the first `n` white steps from `S`. -/
def whiteKnown (K : Nat) : Nat → Nat → Bool
  | 0, _ => true
  | n + 1, S => known K S && whiteKnown K n (fimage K false S)

theorem whiteKnown_spec (K : Nat) :
    ∀ n S, whiteKnown K n S = true → ∀ j, j < n → known K (zf K j S) = true
  | 0, _, _, j, hj => absurd hj (Nat.not_lt_zero _)
  | n + 1, S, h, j, hj => by
    rw [whiteKnown, Bool.and_eq_true] at h
    cases j with
    | zero => exact h.1
    | succ j =>
      rw [Nat.add_comm, zf_add]
      exact whiteKnown_spec K n _ h.2 j (by omega)

/-- The first cell is known at each white phase of `u` read from `S`. -/
def tailKnown (K : Nat) : List Bool → Nat → Bool
  | [], _ => true
  | a :: u, S => (a || known K S) && tailKnown K u (fimage K a S)

theorem tailKnown_spec (K : Nat) : ∀ (u : List Bool) S, tailKnown K u S = true →
    ∀ ψ, ψ < u.length → u.getD ψ false = false → known K (fapply K (u.take ψ) S) = true
  | [], _, _, ψ, hψ, _ => absurd hψ (by simp)
  | a :: u, S, h, ψ, hψ, hu => by
    rw [tailKnown, Bool.and_eq_true] at h
    cases ψ with
    | zero =>
      have ha : a = false := by simpa using hu
      subst ha
      show known K S = true
      simpa using h.1
    | succ ψ =>
      exact tailKnown_spec K u _ h.2 ψ (by simp at hψ; omega) (by simpa using hu)

/-- One period of `0^N u`. -/
def period (K N : Nat) (u : List Bool) (X : Nat) : Nat := fapply K u (zf K N X)

/-- `n` periods of `0^N u`. -/
def iterP (K N : Nat) (u : List Bool) : Nat → Nat → Nat
  | 0, X => X
  | n + 1, X => iterP K N u n (period K N u X)

theorem iterP_succ (K N : Nat) (u : List Bool) :
    ∀ n X, iterP K N u (n + 1) X = period K N u (iterP K N u n X)
  | 0, _ => rfl
  | n + 1, X => iterP_succ K N u n (period K N u X)

/-- `d` more white steps map `Y` into itself. -/
def stab (K d Y : Nat) : Bool := subB K (zf K d Y) Y

/-- The checks at the last set `X` of the chain, with `Y` the set after its white run. -/
def finalCheck (K N d : Nat) (u : List Bool) (X Y : Nat) : Bool :=
  stab K d Y && subB K (fapply K u Y) X && whiteKnown K (N + d) X && tailKnown K u Y

/-- `n` more periods from `X`, checking `stab` after each white run, then `finalCheck`. -/
def cycleRun (K N d : Nat) (u : List Bool) : Nat → Nat → Bool
  | 0, X => finalCheck K N d u X (zf K N X)
  | n + 1, X =>
    let Y := zf K N X
    stab K d Y && cycleRun K N d u n (fapply K u Y)

/-- **Cycle certificate** for `0^(N + d m) u`, every `m`, at `K` cells after `k` periods. -/
def cycleCert (K N d k : Nat) (u : List Bool) : Bool := cycleRun K N d u k (fullSet K)

theorem cycleRun_spec (K N d : Nat) (u : List Bool) : ∀ n X, cycleRun K N d u n X = true →
    (∀ j, j < n → stab K d (zf K N (iterP K N u j X)) = true) ∧
      finalCheck K N d u (iterP K N u n X) (zf K N (iterP K N u n X)) = true
  | 0, _, h => ⟨fun j hj => absurd hj (Nat.not_lt_zero _), h⟩
  | n + 1, X, h => by
    have h' : stab K d (zf K N X) = true ∧ cycleRun K N d u n (fapply K u (zf K N X)) = true := by
      simpa only [cycleRun, Bool.and_eq_true] using h
    obtain ⟨ih1, ih2⟩ := cycleRun_spec K N d u n (period K N u X) h'.2
    refine ⟨fun j hj => ?_, ih2⟩
    cases j with
    | zero => exact h'.1
    | succ j => exact ih1 j (by omega)

/-- **A residue class at once.** If `cycleCert K N d k u` holds, no column of the orbit of a row with a leftmost 1
repeats `0^(N + d m) u`, for any `m`. -/
theorem cycle_column {x : Int → Bool} {lo : Int} (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (K N d k : Nat) (u : List Bool) (hK : 1 ≤ K) (hu : 0 < u.length)
    (hcert : cycleCert K N d k u = true) (m : Nat) :
    ¬ Rule30FiniteStrips.EventuallyWord x i (List.replicate (N + d * m) false ++ u) := by
  obtain ⟨hstab, hfin⟩ := cycleRun_spec K N d u k (fullSet K) hcert
  unfold finalCheck at hfin
  simp only [Bool.and_eq_true] at hfin
  obtain ⟨⟨⟨hs, hcl⟩, hwk⟩, htk⟩ := hfin
  let C : Nat → Nat := fun n => iterP K N u n (fullSet K)
  have hper : ∀ X, stab K d (zf K N X) = true →
      SubK K (fapply K (List.replicate (N + d * m) false ++ u) X) (period K N u X) := by
    intro X hX
    rw [fapply_append]
    exact fapply_mono K u (zf_pump K N d X (subB_spec hX) m)
  have hpump : SubK K (zf K (N + d * m) (C k)) (zf K N (C k)) := zf_pump K N d _ (subB_spec hs) m
  refine invariant_column hlo hzero i _ (by simp; omega) K k hK C rfl (fun n hn => ?_)
    (Rule30WhiteEndNine.SubK.trans (hper _ hs) (subB_spec hcl)) (fun φ hφ hwφ => ?_)
  · show SubK K _ (iterP K N u (n + 1) (fullSet K))
    rw [iterP_succ]
    exact hper _ (hstab n hn)
  · by_cases hφr : φ < N + d * m
    · have htake : (List.replicate (N + d * m) false ++ u).take φ = List.replicate φ false := by
        rw [List.take_append_of_le_length (by simp; omega), List.take_replicate,
          Nat.min_eq_left (Nat.le_of_lt hφr)]
      rw [htake]
      show known K (zf K φ (C k)) = true
      by_cases hφN : φ < N + d
      · exact whiteKnown_spec K _ _ hwk φ hφN
      · have hd : 0 < d := by
          rcases Nat.eq_zero_or_pos d with h0 | h0
          · subst h0; simp at hφr; omega
          · exact h0
        have he : (φ - N) % d < d := Nat.mod_lt _ hd
        have hdm := Nat.div_add_mod (φ - N) d
        have hφeq : φ = (N + d * ((φ - N) / d)) + (φ - N) % d := by
          generalize d * ((φ - N) / d) = D at hdm ⊢
          omega
        rw [hφeq, zf_add]
        refine known_mono (S' := zf K ((φ - N) % d) (zf K N (C k))) (fapply_mono K _ (zf_pump K N d _ (subB_spec hs) _)) ?_
        rw [← zf_add]
        exact whiteKnown_spec K _ _ hwk _ (by omega)
    · have hlen : φ - (N + d * m) < u.length := by simp at hφ; omega
      have htake : (List.replicate (N + d * m) false ++ u).take φ =
          List.replicate (N + d * m) false ++ u.take (φ - (N + d * m)) := by
        rw [List.take_append]
        simp [List.take_replicate, Nat.min_eq_right (Nat.le_of_not_lt hφr)]
      have hwu : u.getD (φ - (N + d * m)) false = false := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp; omega)] at hwφ
        simpa [List.getD_eq_getElem?_getD] using hwφ
      rw [htake, fapply_append]
      exact known_mono (fapply_mono K _ hpump) (tailKnown_spec K u _ htk _ hlen hwu)

/-! ### Covering every white run from a threshold -/

/-- A piece `(N, d, k)` covers `q` when `q = N + d m` for some `m`. -/
def covers (ps : List (Nat × Nat × Nat)) (q : Nat) : Bool :=
  ps.any fun p => decide (p.1 ≤ q) && (q - p.1) % p.2.1 == 0

/-- A piece of period 4 covers `q`. -/
def covers4 (ps : List (Nat × Nat × Nat)) (q : Nat) : Bool :=
  ps.any fun p => p.2.1 == 4 && decide (p.1 ≤ q) && (q - p.1) % 4 == 0

/-- **Tail certificate**: every piece has a cycle certificate, every `q` in `[q0, B)` is covered, and the four `q` in
`[B, B + 4)` are covered by pieces of period 4. -/
def tailCert (K : Nat) (u : List Bool) (q0 B : Nat) (ps : List (Nat × Nat × Nat)) : Bool :=
  ps.all (fun p => cycleCert K p.1 p.2.1 p.2.2 u) &&
    (List.range B).all (fun q => decide (q < q0) || covers ps q) &&
    (List.range 4).all (fun j => covers4 ps (B + j))

/-- The pieces cover every `q ≥ q0`. -/
theorem tailCert_cover {K : Nat} {u : List Bool} {q0 B : Nat} {ps : List (Nat × Nat × Nat)}
    (h : tailCert K u q0 B ps = true) (q : Nat) (hq : q0 ≤ q) :
    ∃ p ∈ ps, ∃ m, q = p.1 + p.2.1 * m := by
  unfold tailCert at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨_, hlow⟩, hhigh⟩ := h
  by_cases hqB : q < B
  · have hc := hlow q hqB
    rw [show decide (q < q0) = false from decide_eq_false (by omega), Bool.false_or] at hc
    obtain ⟨p, hp, hpc⟩ := List.any_eq_true.mp hc
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hpc
    refine ⟨p, hp, (q - p.1) / p.2.1, ?_⟩
    have := Nat.div_add_mod (q - p.1) p.2.1
    rw [hpc.2] at this
    generalize p.2.1 * ((q - p.1) / p.2.1) = D at this ⊢
    omega
  · have hc := hhigh ((q - B) % 4) (Nat.mod_lt _ (by omega))
    obtain ⟨p, hp, hpc⟩ := List.any_eq_true.mp hc
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hpc
    obtain ⟨⟨h4, hle⟩, hmod⟩ := hpc
    refine ⟨p, hp, (q - p.1) / 4, ?_⟩
    rw [h4]
    omega

/-- **A tail family.** If `tailCert K u q0 B ps` holds, no column of the orbit of a row with a leftmost 1 repeats
`0^q u` for any `q ≥ q0`. -/
theorem tailCert_column {x : Int → Bool} {lo : Int} (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (K : Nat) (u : List Bool) (q0 B : Nat) (ps : List (Nat × Nat × Nat)) (hK : 1 ≤ K)
    (hu : 0 < u.length) (h : tailCert K u q0 B ps = true) (q : Nat) (hq : q0 ≤ q) :
    ¬ Rule30FiniteStrips.EventuallyWord x i (List.replicate q false ++ u) := by
  obtain ⟨p, hp, m, rfl⟩ := tailCert_cover h q hq
  have hall : ps.all (fun p => cycleCert K p.1 p.2.1 p.2.2 u) = true := by
    unfold tailCert at h
    simp only [Bool.and_eq_true] at h
    exact h.1.1
  exact cycle_column hlo hzero i K p.1 p.2.1 p.2.2 u hK hu (List.all_eq_true.mp hall p hp) m

/-! ### The tails of at most six cells at 14 cells

One kernel check per tail: its pieces, from `computations/tail_families.py --lean 6`. -/

/-- `0^q 1` for every `q ≥ 10`. -/
theorem cert_1 : tailCert 14 [true] 10 21
    [(18, 4, 2), (19, 4, 2), (20, 4, 2), (21, 4, 2), (10, 0, 2), (11, 0, 2), (12, 0, 2), (13, 0, 2),
      (14, 0, 2), (15, 0, 2), (16, 0, 2), (17, 0, 2)] = true := by
  decide +kernel

/-- `0^q 11` for every `q ≥ 8`. -/
theorem cert_11 : tailCert 14 [true, true] 8 23
    [(20, 4, 2), (21, 4, 2), (22, 4, 2), (23, 4, 2), (8, 0, 3), (9, 0, 2), (10, 0, 2), (11, 0, 2),
      (12, 0, 2), (13, 0, 2), (14, 0, 2), (15, 0, 2), (16, 0, 2), (17, 0, 2), (18, 0, 2), (19, 0, 2)] = true := by
  decide +kernel

/-- `0^q 101` for every `q ≥ 9`. -/
theorem cert_101 : tailCert 14 [true, false, true] 9 26
    [(25, 4, 2), (26, 4, 2), (23, 4, 2), (24, 4, 2), (9, 0, 3), (10, 0, 3), (11, 0, 2), (12, 0, 2),
      (13, 0, 2), (14, 0, 2), (15, 0, 2), (16, 0, 2), (17, 0, 2), (18, 0, 2), (19, 0, 2), (20, 0, 2),
      (21, 0, 2), (22, 0, 2)] = true := by
  decide +kernel

/-- `0^q 111` for every `q ≥ 18`. -/
theorem cert_111 : tailCert 14 [true, true, true] 18 24
    [(22, 4, 2), (23, 4, 2), (24, 4, 2), (21, 4, 2), (18, 0, 3), (19, 0, 2), (20, 0, 2)] = true := by
  decide +kernel

/-- `0^q 1001` for every `q ≥ 16`. -/
theorem cert_1001 : tailCert 14 [true, false, false, true] 16 27
    [(24, 4, 2), (21, 4, 2), (22, 4, 2), (27, 4, 2), (16, 0, 4), (17, 0, 3), (18, 0, 2), (19, 0, 2),
      (20, 0, 2), (23, 0, 2)] = true := by
  decide +kernel

/-- `0^q 1011` for every `q ≥ 9`. -/
theorem cert_1011 : tailCert 14 [true, false, true, true] 9 20
    [(17, 4, 2), (18, 4, 2), (19, 4, 2), (20, 4, 2), (9, 0, 2), (10, 0, 2), (11, 0, 2), (12, 0, 2),
      (13, 0, 2), (14, 0, 2), (15, 0, 2), (16, 0, 2)] = true := by
  decide +kernel

/-- `0^q 1101` for every `q ≥ 9`. -/
theorem cert_1101 : tailCert 14 [true, true, false, true] 9 26
    [(25, 4, 2), (26, 4, 2), (23, 4, 2), (24, 4, 2), (9, 0, 4), (10, 0, 3), (11, 0, 2), (12, 0, 2),
      (13, 0, 2), (14, 0, 2), (15, 0, 2), (16, 0, 2), (17, 0, 2), (18, 0, 2), (19, 0, 2), (20, 0, 2),
      (21, 0, 2), (22, 0, 2)] = true := by
  decide +kernel

/-- `0^q 1111` for every `q ≥ 9`. -/
theorem cert_1111 : tailCert 14 [true, true, true, true] 9 28
    [(21, 4, 2), (22, 4, 2), (27, 4, 2), (28, 4, 2), (9, 0, 2), (10, 0, 2), (11, 0, 2), (12, 0, 2),
      (13, 0, 2), (14, 0, 2), (15, 0, 2), (16, 0, 2), (17, 0, 2), (18, 0, 2), (19, 0, 2), (20, 0, 2),
      (23, 0, 2), (24, 0, 2)] = true := by
  decide +kernel

/-- `0^q 10001` for every `q ≥ 11`. -/
theorem cert_10001 : tailCert 14 [true, false, false, false, true] 11 23
    [(23, 4, 2), (20, 4, 2), (21, 4, 2), (22, 4, 2), (11, 0, 5), (12, 0, 6), (13, 0, 3), (14, 0, 3),
      (15, 0, 3), (16, 0, 3), (17, 0, 3), (18, 0, 2), (19, 0, 2)] = true := by
  decide +kernel

/-- `0^q 10011` for every `q ≥ 8`. -/
theorem cert_10011 : tailCert 14 [true, false, false, true, true] 8 25
    [(24, 4, 2), (25, 4, 2), (22, 4, 2), (23, 4, 2), (8, 0, 3), (9, 0, 2), (10, 0, 2), (11, 0, 2),
      (12, 0, 2), (13, 0, 2), (14, 0, 2), (15, 0, 2), (16, 0, 2), (17, 0, 2), (18, 0, 2), (19, 0, 2),
      (20, 0, 2), (21, 0, 2)] = true := by
  decide +kernel

/-- `0^q 10111` for every `q ≥ 9`. -/
theorem cert_10111 : tailCert 14 [true, false, true, true, true] 9 25
    [(25, 4, 2), (22, 4, 2), (23, 4, 2), (24, 4, 2), (9, 0, 2), (10, 0, 2), (11, 0, 2), (12, 0, 2),
      (13, 0, 2), (14, 0, 2), (15, 0, 2), (16, 0, 2), (17, 0, 2), (18, 0, 2), (19, 0, 2), (20, 0, 2),
      (21, 0, 2)] = true := by
  decide +kernel

/-- `0^q 11001` for every `q ≥ 18`. -/
theorem cert_11001 : tailCert 14 [true, true, false, false, true] 18 28
    [(26, 4, 2), (27, 4, 2), (28, 4, 2), (25, 4, 2), (18, 0, 2), (19, 0, 2), (20, 0, 2), (21, 0, 2),
      (22, 0, 2), (23, 0, 2), (24, 0, 2)] = true := by
  decide +kernel

/-- `0^q 11011` for every `q ≥ 9`. -/
theorem cert_11011 : tailCert 14 [true, true, false, true, true] 9 26
    [(25, 4, 2), (26, 4, 2), (23, 4, 2), (24, 4, 2), (9, 0, 2), (10, 0, 2), (11, 0, 2), (12, 0, 2),
      (13, 0, 2), (14, 0, 2), (15, 0, 2), (16, 0, 2), (17, 0, 2), (18, 0, 2), (19, 0, 2), (20, 0, 2),
      (21, 0, 2), (22, 0, 2)] = true := by
  decide +kernel

/-- `0^q 11101` for every `q ≥ 10`. -/
theorem cert_11101 : tailCert 14 [true, true, true, false, true] 10 21
    [(18, 4, 2), (19, 4, 2), (20, 4, 2), (21, 4, 2), (10, 0, 3), (11, 0, 2), (12, 0, 2), (13, 0, 2),
      (14, 0, 2), (15, 0, 2), (16, 0, 2), (17, 0, 2)] = true := by
  decide +kernel

/-- `0^q 11111` for every `q ≥ 13`. -/
theorem cert_11111 : tailCert 14 [true, true, true, true, true] 13 19
    [(17, 4, 2), (18, 4, 2), (19, 4, 2), (16, 4, 2), (13, 0, 4), (14, 0, 3), (15, 0, 3)] = true := by
  decide +kernel

/-- `0^q 100001` for every `q ≥ 17`. -/
theorem cert_100001 : tailCert 14 [true, false, false, false, false, true] 17 25
    [(25, 4, 2), (22, 4, 2), (23, 4, 2), (24, 4, 2), (17, 0, 3), (18, 0, 2), (19, 0, 2), (20, 0, 2),
      (21, 0, 2)] = true := by
  decide +kernel

/-- `0^q 100011` for every `q ≥ 14`. -/
theorem cert_100011 : tailCert 14 [true, false, false, false, true, true] 14 21
    [(18, 4, 2), (19, 4, 2), (20, 4, 2), (21, 4, 2), (14, 0, 2), (15, 0, 3), (16, 0, 2), (17, 0, 2)] = true := by
  decide +kernel

/-- `0^q 100101` for every `q ≥ 16`. -/
theorem cert_100101 : tailCert 14 [true, false, false, true, false, true] 16 26
    [(24, 4, 2), (25, 4, 2), (26, 4, 2), (23, 4, 2), (16, 0, 2), (17, 0, 2), (18, 0, 2), (19, 0, 2),
      (20, 0, 2), (21, 0, 2), (22, 0, 2)] = true := by
  decide +kernel

/-- `0^q 100111` for every `q ≥ 18`. -/
theorem cert_100111 : tailCert 14 [true, false, false, true, true, true] 18 25
    [(22, 4, 2), (23, 4, 2), (24, 4, 2), (25, 4, 2), (18, 0, 2), (19, 0, 2), (20, 0, 2), (21, 0, 2)] = true := by
  decide +kernel

/-- `0^q 101001` for every `q ≥ 9`. -/
theorem cert_101001 : tailCert 14 [true, false, true, false, false, true] 9 29
    [(29, 4, 2), (26, 4, 2), (27, 4, 2), (28, 4, 2), (9, 0, 3), (10, 0, 3), (11, 0, 2), (12, 0, 2),
      (13, 0, 2), (14, 0, 2), (15, 0, 2), (16, 0, 2), (17, 0, 2), (18, 0, 2), (19, 0, 2), (20, 0, 2),
      (21, 0, 2), (22, 0, 2), (23, 0, 2), (24, 0, 2), (25, 0, 2)] = true := by
  decide +kernel

/-- `0^q 101011` for every `q ≥ 9`. -/
theorem cert_101011 : tailCert 14 [true, false, true, false, true, true] 9 18
    [(17, 4, 2), (18, 4, 2), (15, 4, 2), (16, 4, 2), (9, 0, 2), (10, 0, 2), (11, 0, 2), (12, 0, 2),
      (13, 0, 2), (14, 0, 2)] = true := by
  decide +kernel

/-- `0^q 101101` for every `q ≥ 16`. -/
theorem cert_101101 : tailCert 14 [true, false, true, true, false, true] 16 21
    [(20, 4, 2), (21, 4, 2), (18, 4, 2), (19, 4, 2), (16, 0, 3), (17, 0, 3)] = true := by
  decide +kernel

/-- `0^q 101111` for every `q ≥ 9`. -/
theorem cert_101111 : tailCert 14 [true, false, true, true, true, true] 9 24
    [(21, 4, 2), (22, 4, 2), (23, 4, 2), (24, 4, 2), (9, 0, 2), (10, 0, 2), (11, 0, 2), (12, 0, 2),
      (13, 0, 2), (14, 0, 2), (15, 0, 2), (16, 0, 2), (17, 0, 2), (18, 0, 2), (19, 0, 2), (20, 0, 2)] = true := by
  decide +kernel

/-- `0^q 110001` for every `q ≥ 15`. -/
theorem cert_110001 : tailCert 14 [true, true, false, false, false, true] 15 26
    [(23, 4, 2), (24, 4, 2), (25, 4, 2), (26, 4, 2), (15, 0, 3), (16, 0, 3), (17, 0, 3), (18, 0, 3),
      (19, 0, 2), (20, 0, 2), (21, 0, 2), (22, 0, 2)] = true := by
  decide +kernel

/-- `0^q 110011` for every `q ≥ 8`. -/
theorem cert_110011 : tailCert 14 [true, true, false, false, true, true] 8 18
    [(16, 4, 2), (17, 4, 2), (18, 4, 2), (15, 4, 2), (8, 0, 2), (9, 0, 2), (10, 0, 2), (11, 0, 2),
      (12, 0, 2), (13, 0, 2), (14, 0, 2)] = true := by
  decide +kernel

/-- `0^q 110101` for every `q ≥ 14`. -/
theorem cert_110101 : tailCert 14 [true, true, false, true, false, true] 14 25
    [(22, 4, 2), (19, 4, 2), (24, 4, 2), (25, 4, 2), (14, 0, 5), (15, 0, 5), (16, 0, 3), (17, 0, 3),
      (18, 0, 2), (20, 0, 2), (21, 0, 2)] = true := by
  decide +kernel

/-- `0^q 110111` for every `q ≥ 10`. -/
theorem cert_110111 : tailCert 14 [true, true, false, true, true, true] 10 26
    [(26, 4, 2), (23, 4, 2), (24, 4, 2), (25, 4, 2), (10, 0, 3), (11, 0, 2), (12, 0, 2), (13, 0, 2),
      (14, 0, 2), (15, 0, 2), (16, 0, 2), (17, 0, 2), (18, 0, 2), (19, 0, 2), (20, 0, 2), (21, 0, 2),
      (22, 0, 2)] = true := by
  decide +kernel

/-- `0^q 111001` for every `q ≥ 16`. -/
theorem cert_111001 : tailCert 14 [true, true, true, false, false, true] 16 25
    [(24, 4, 2), (25, 4, 2), (22, 4, 2), (23, 4, 2), (16, 0, 2), (17, 0, 2), (18, 0, 2), (19, 0, 2),
      (20, 0, 2), (21, 0, 2)] = true := by
  decide +kernel

/-- `0^q 111011` for every `q ≥ 18`. -/
theorem cert_111011 : tailCert 14 [true, true, true, false, true, true] 18 22
    [(22, 4, 2), (19, 4, 2), (20, 4, 2), (21, 4, 2), (18, 0, 2)] = true := by
  decide +kernel

/-- `0^q 111101` for every `q ≥ 22`. -/
theorem cert_111101 : tailCert 14 [true, true, true, true, false, true] 22 27
    [(26, 4, 2), (27, 4, 2), (24, 4, 3), (25, 4, 2), (22, 0, 4), (23, 0, 3)] = true := by
  decide +kernel

/-- `0^q 111111` for every `q ≥ 14`. -/
theorem cert_111111 : tailCert 14 [true, true, true, true, true, true] 14 24
    [(22, 4, 2), (23, 4, 2), (24, 4, 2), (17, 4, 2), (14, 0, 3), (15, 0, 3), (16, 0, 2), (18, 0, 2),
      (19, 0, 2), (20, 0, 2)] = true := by
  decide +kernel

/-- The tails of one to six cells that start and end with 1, other than `10101`, with their thresholds at
14 cells. -/
def thresholds14 : List (List Bool × Nat) := [
  ([true], 10),
  ([true, true], 8),
  ([true, false, true], 9),
  ([true, true, true], 18),
  ([true, false, false, true], 16),
  ([true, false, true, true], 9),
  ([true, true, false, true], 9),
  ([true, true, true, true], 9),
  ([true, false, false, false, true], 11),
  ([true, false, false, true, true], 8),
  ([true, false, true, true, true], 9),
  ([true, true, false, false, true], 18),
  ([true, true, false, true, true], 9),
  ([true, true, true, false, true], 10),
  ([true, true, true, true, true], 13),
  ([true, false, false, false, false, true], 17),
  ([true, false, false, false, true, true], 14),
  ([true, false, false, true, false, true], 16),
  ([true, false, false, true, true, true], 18),
  ([true, false, true, false, false, true], 9),
  ([true, false, true, false, true, true], 9),
  ([true, false, true, true, false, true], 16),
  ([true, false, true, true, true, true], 9),
  ([true, true, false, false, false, true], 15),
  ([true, true, false, false, true, true], 8),
  ([true, true, false, true, false, true], 14),
  ([true, true, false, true, true, true], 10),
  ([true, true, true, false, false, true], 16),
  ([true, true, true, false, true, true], 18),
  ([true, true, true, true, false, true], 22),
  ([true, true, true, true, true, true], 14)]

/-- Each tail of `thresholds14` has a tail certificate from its threshold. -/
theorem thresholds14_cert : ∀ e ∈ thresholds14, ∃ B ps, tailCert 14 e.1 e.2 B ps = true := by
  intro e he
  simp only [thresholds14, List.mem_cons, List.not_mem_nil, or_false] at he
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl := he
  · exact ⟨_, _, cert_1⟩
  · exact ⟨_, _, cert_11⟩
  · exact ⟨_, _, cert_101⟩
  · exact ⟨_, _, cert_111⟩
  · exact ⟨_, _, cert_1001⟩
  · exact ⟨_, _, cert_1011⟩
  · exact ⟨_, _, cert_1101⟩
  · exact ⟨_, _, cert_1111⟩
  · exact ⟨_, _, cert_10001⟩
  · exact ⟨_, _, cert_10011⟩
  · exact ⟨_, _, cert_10111⟩
  · exact ⟨_, _, cert_11001⟩
  · exact ⟨_, _, cert_11011⟩
  · exact ⟨_, _, cert_11101⟩
  · exact ⟨_, _, cert_11111⟩
  · exact ⟨_, _, cert_100001⟩
  · exact ⟨_, _, cert_100011⟩
  · exact ⟨_, _, cert_100101⟩
  · exact ⟨_, _, cert_100111⟩
  · exact ⟨_, _, cert_101001⟩
  · exact ⟨_, _, cert_101011⟩
  · exact ⟨_, _, cert_101101⟩
  · exact ⟨_, _, cert_101111⟩
  · exact ⟨_, _, cert_110001⟩
  · exact ⟨_, _, cert_110011⟩
  · exact ⟨_, _, cert_110101⟩
  · exact ⟨_, _, cert_110111⟩
  · exact ⟨_, _, cert_111001⟩
  · exact ⟨_, _, cert_111011⟩
  · exact ⟨_, _, cert_111101⟩
  · exact ⟨_, _, cert_111111⟩

/-- Every word of at most `n` cells (with repeats). -/
def words : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => [] :: (words n).flatMap fun v => [false :: v, true :: v]

theorem mem_words : ∀ n (u : List Bool), u.length ≤ n → u ∈ words n
  | 0, [], _ => by simp [words]
  | 0, _ :: _, h => by simp at h
  | n + 1, [], _ => by simp [words]
  | n + 1, a :: v, h => by
    simp only [words, List.mem_cons, List.mem_flatMap]
    right
    exact ⟨v, mem_words n v (by simp at h; omega), by cases a <;> simp⟩

/-- Every tail of one to six cells that starts and ends with 1, other than `10101`, is in `thresholds14`, with a
threshold of at most 22. -/
theorem short_in_table : ∀ u ∈ words 6, u.head? = some true → u.getLast? = some true →
    u ≠ [true, false, true, false, true] → ∃ e ∈ thresholds14, e.1 = u ∧ e.2 ≤ 22 := by
  decide +kernel

theorem thresholds14_length : ∀ e ∈ thresholds14, 0 < e.1.length := by
  decide +kernel

/-- A column that reads `w` from time `T` in phase `shift` reads it from a later time in phase 0. -/
theorem shift_word {x : Int → Bool} (i : Int) (w : List Bool) (hw : 0 < w.length) (T shift : Nat)
    (h : ∀ t, T ≤ t → evol x t i = w.getD ((t + shift) % w.length) false) :
    Rule30FiniteStrips.EventuallyWord x i w := by
  refine ⟨T + (w.length - (T + shift) % w.length), fun t ht => ?_⟩
  rw [h t (by omega)]
  congr 1
  have hlt := Nat.mod_lt (T + shift) hw
  have hd := Nat.div_add_mod (T + shift) w.length
  have e : t + shift = (t - (T + (w.length - (T + shift) % w.length))) +
      w.length * ((T + shift) / w.length + 1) := by
    rw [Nat.mul_succ]
    generalize w.length * ((T + shift) / w.length) = D at hd ⊢
    omega
  rw [e, Nat.add_mul_mod_self_left]

/-- The tails of `thresholds14` from their thresholds, for every column of every row with a leftmost 1. -/
theorem table_column {x : Int → Bool} {lo : Int} (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) : ∀ e ∈ thresholds14, ∀ q, e.2 ≤ q →
      ¬ Rule30FiniteStrips.EventuallyWord x i (List.replicate q false ++ e.1) := by
  intro e he q hq
  obtain ⟨B, ps, hc⟩ := thresholds14_cert e he
  exact tailCert_column hlo hzero i 14 e.1 e.2 B ps (by decide) (thresholds14_length e he) hc q hq

/-- Every tail of one to six cells that starts and ends with 1, but `10101`, after a white run of at least 22. -/
theorem short_tails_evol {x : Int → Bool} {lo : Int} (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (u : List Bool) (hlen : u.length ≤ 6) (hhead : u.head? = some true)
    (hlast : u.getLast? = some true) (hne : u ≠ [true, false, true, false, true]) (q : Nat) (hq : 22 ≤ q) :
    ¬ Rule30FiniteStrips.EventuallyWord x i (List.replicate q false ++ u) := by
  obtain ⟨e, he, rfl, h22⟩ := short_in_table u (mem_words 6 u hlen) hhead hlast hne
  exact table_column hlo hzero i e he q (by omega)

end TailFamilies14

open Ruliology.CellularAutomata
open TailFamilies14

/-- **A residue class of white runs at once.** If `cycleCert K N d k u` holds (`K ≥ 1`, `u` nonempty), no column of
the orbit of a row with a leftmost 1 repeats `0^(N + d m) u` from any time on, in any phase, for any `m`. -/
theorem cycle_padding_column (init : Int → Bool) (m0 : Int) (hm : init m0 = true)
    (hz : ∀ x : Int, x < m0 → init x = false) (K N d k : Nat) (u : List Bool) (hK : 1 ≤ K) (hu : 0 < u.length)
    (hcert : cycleCert K N d k u = true) (m : Nat) (col : Int) (T shift : Nat)
    (h : ∀ t : Nat, T ≤ t → evolve init t col = (List.replicate (N + d * m) false ++ u).getD
      ((t + shift) % (List.replicate (N + d * m) false ++ u).length) false) : False :=
  cycle_column hm hz col K N d k u hK hu hcert m
    (shift_word col _ (by simp; omega) T shift fun t ht => by rw [← evolve_evol]; exact h t ht)

/-- **Tail families at 14 cells.** For every tail `u` with threshold `q0` in `thresholds14` (the 31 tails of one to six
cells that start and end with 1, other than `10101`) and every `q ≥ q0`, no column of the orbit of a row with a
leftmost 1 repeats `0^q u` from any time on, in any phase. -/
theorem tail_thresholds_column (init : Int → Bool) (m0 : Int) (hm : init m0 = true)
    (hz : ∀ x : Int, x < m0 → init x = false) (e : List Bool × Nat) (he : e ∈ thresholds14) (q : Nat)
    (hq : e.2 ≤ q) (col : Int) (T shift : Nat)
    (h : ∀ t : Nat, T ≤ t → evolve init t col = (List.replicate q false ++ e.1).getD
      ((t + shift) % (List.replicate q false ++ e.1).length) false) : False :=
  table_column hm hz col e he q hq
    (shift_word col _ (by have := thresholds14_length e he; simp; omega) T shift
      fun t ht => by rw [← evolve_evol]; exact h t ht)

/-- **Every tail of at most six cells but `10101`, after 22 white cells.** For every tail `u` of one to six cells that
starts and ends with 1, other than `10101`, and every `q ≥ 22`, no column of the orbit of a row with a leftmost 1
repeats `0^q u` from any time on, in any phase. -/
theorem short_tails_column (init : Int → Bool) (m0 : Int) (hm : init m0 = true)
    (hz : ∀ x : Int, x < m0 → init x = false) (u : List Bool) (hlen : u.length ≤ 6) (hhead : u.head? = some true)
    (hlast : u.getLast? = some true) (hne : u ≠ [true, false, true, false, true]) (q : Nat) (hq : 22 ≤ q)
    (col : Int) (T shift : Nat)
    (h : ∀ t : Nat, T ≤ t → evolve init t col = (List.replicate q false ++ u).getD
      ((t + shift) % (List.replicate q false ++ u).length) false) : False := by
  have hu : 0 < u.length := by
    cases u with
    | nil => simp at hhead
    | cons _ _ => simp
  exact short_tails_evol hm hz col u hlen hhead hlast hne q hq
    (shift_word col _ (by simp; omega) T shift fun t ht => by rw [← evolve_evol]; exact h t ht)

/-- **The center column**, in the official form: it does not repeat `0^q u` from any time on, in any phase. -/
theorem center_short_tails (u : List Bool) (hlen : u.length ≤ 6) (hhead : u.head? = some true)
    (hlast : u.getLast? = some true) (hne : u ≠ [true, false, true, false, true]) (q : Nat) (hq : 22 ≤ q)
    (T shift : Nat)
    (h : ∀ t : Nat, T ≤ t → Rule30Prize.center t = (List.replicate q false ++ u).getD
      ((t + shift) % (List.replicate q false ++ u).length) false) : False :=
  short_tails_column single 0 rfl (fun x hx => decide_eq_false (by omega)) u hlen hhead hlast hne q hq 0 T shift
    fun t ht => by rw [evolve_single_center, h t ht]

/-- The same in the kit's form: `0^q u` is not an `EventuallyWord` of the center column. -/
theorem not_eventually_short_tails (u : List Bool) (hlen : u.length ≤ 6) (hhead : u.head? = some true)
    (hlast : u.getLast? = some true) (hne : u ≠ [true, false, true, false, true]) (q : Nat) (hq : 22 ≤ q) :
    ¬ Rule30StripCertificates.EventuallyWord (List.replicate q false ++ u) := by
  rintro ⟨T, hT⟩
  refine short_tails_evol (x := single) (lo := 0) rfl (fun x hx => decide_eq_false (by omega)) 0 u hlen hhead
    hlast hne q hq ⟨T, fun t ht => ?_⟩
  rw [← evolve_evol, evolve_single_eq_cell]
  exact hT t ht

end Rule30Open
