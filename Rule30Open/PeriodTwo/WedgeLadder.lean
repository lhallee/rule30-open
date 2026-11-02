module

public import Rule30Open.PeriodTwo.WedgeSmall

/-!
# The wedge ladder: `BWH` and every weak form of it give the binary constant-tail separator

On the kit's streams of four symbols (`Rule30Open.WedgeKit`, restated from the kit's main branch by `WedgeSmall`),
`BinaryCTS` says that no stream whose symbols are all binary (`1` or `2`) has an inverse diagonal that is eventually
constant `c ∈ {2, 3}`. It is the kit's `ConstantTailSeparator` (`SEP`) with the hard-core condition (no `1` after a
`1`) dropped, so it is the stronger of the two. `WeakBWH S L` is `BWH` with the lengths `n ≥ 7` replaced by a set `S` and
the horizon `n + 2` by `L n`: no binary word of length `n + L n` has a constant wedge `c` of length `L n`.

* `bwh_iff_weakBWH`: `BWH` is `WeakBWH` with `S = {n ≥ 7}` and `L n = n + 2`.
* `weakBWH_binaryCTS`: if `S` is infinite, `WeakBWH S L` implies `BinaryCTS`, for every horizon `L`.
  `bwh_binaryCTS`: `BWH` implies `BinaryCTS`. The proof is the kit's rotation (`rotated_iterate`,
  `wedge n (shiftN e n) t = inverse e (t + 2n)`): an eventually constant inverse makes every late shift of `e` a
  witness of every horizon.
* `binaryCTS_constantTailSeparator`, `bwh_constantTailSeparator`: `BinaryCTS`, so `BWH` alone, gives the kit's
  `ConstantTailSeparator`; no `SmallRW` and no `RW` enter.
* `wedge_vacuum`: `phi 0 0 = phi 2 2 = phi 3 3 = 0`, so a constant wedge `c` of length `L` at depth `n` makes
  `peelPow (n + k) (inverse e) t = 0` whenever `1 ≤ k` and `t + k < L`.
* `binaryCTS_excludes_finite_peel_rank`, `binaryCTS_orbit`: the kit's consequences of `ConstantTailSeparator` (no
  finite peel rank, no orbit `liftWord u (const c)`) hold for binary streams under `BinaryCTS`, with the kit's proofs:
  they use only that `2` is binary, never the hard-core condition.
* `binaryCTS_horizon`, `binaryCTS_iff_horizon` (compactness): `BinaryCTS` holds exactly when some horizon works at
  every depth, `∃ L, WeakBWH (fun _ => True) L`. If constant wedges of every horizon exist at a depth `n`, the binary
  tree of their prefixes has an infinite branch (`unbounded_child`, `branch`), and it is a binary stream with a constant
  wedge for ever (`infinite_run_of_unbounded`), which `BinaryCTS` excludes.
* `weakBWH_small`: `WeakBWH` holds for `2 ≤ n ≤ 6` with horizon `L n = 2n`, by kernel-checked searches.

`Rule30Open.PeriodTwo.WedgeLadderQ01` charts the zero-driven left half of the kit's `Q01` into binary streams and proves
`BinaryCTS ↔ Q01`. Nothing here proves `BWH`, `WeakBWH` or `BinaryCTS`.

The natural-language argument is `WedgeLadder.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open
namespace WedgeLadder

open WedgeKit

/-! ### The kit's rotation (kit main `Rule30WedgeBridge`, `Rule30SeparatorBridge`, verbatim) -/

def shift (e : Stream) : Stream := fun t => e (t+1)

theorem cone_shift (e : Stream) (t : Nat) :
    ∀ j, cone (shift e) t j = cone e t (j+1) := by
  induction t using Nat.strongRecOn with
  | ind t ih =>
    intro j
    match t with
    | 0 => rfl
    | 1 => rfl
    | t+2 =>
      simp only [cone]
      rw [ih t (by omega), ih (t+1) (by omega)]

theorem rotated_peel (e : Stream) :
    peel (inverse (shift e)) = fun t => inverse e (t+2) := by
  funext t
  simp only [peel, inverse, cone_shift, cone]

theorem peelPow_translate (n k : Nat) (x : Stream) :
    peelPow n (fun t => x (t+k)) = fun t => peelPow n x (t+k) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext t
    simp only [peelPow, peel, ih]
    congr 2 <;> omega

theorem peelPow_inside (n : Nat) (x : Stream) :
    peelPow n (peel x) = peelPow (n+1) x := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [peelPow] at *; rw [ih]

theorem wedge_shift (n : Nat) (e : Stream) (t : Nat) :
    wedge (n+1) (shift e) t = wedge n e (t+2) := by
  unfold wedge
  rw [← peelPow_inside, rotated_peel, peelPow_translate]

def shiftN (e : Stream) (n : Nat) : Stream := fun t => e (t+n)

theorem shiftN_succ (e : Stream) (n : Nat) :
    shiftN e (n+1) = shift (shiftN e n) := by
  funext t
  simp only [shiftN, shift]
  congr 1 <;> omega

theorem rotated_iterate (e : Stream) (n t : Nat) :
    wedge n (shiftN e n) t = inverse e (t+2*n) := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih =>
    rw [shiftN_succ, wedge_shift, ih]
    congr 1 <;> omega

def HardCore (e : Stream) : Prop :=
  (∀ i, binary (e i)) ∧ ∀ i, ¬(e i=1 ∧ e (i+1)=1)

def EventuallyConstant (x : Stream) (c : Sym) : Prop :=
  ∃ N, ∀ t, N ≤ t → x t = c

def ConstantTailSeparator : Prop :=
  ∀ c, constantTail c → ∀ e, HardCore e → ¬EventuallyConstant (inverse e) c

def prependTwos (e : Stream) (d : Nat) : Stream :=
  fun i => if i<d then 2 else e (i-d)

theorem shift_prepend (e : Stream) (d : Nat) : shiftN (prependTwos e d) d=e := by
  funext t
  have hn : ¬t+d<d := by omega
  simp [shiftN, prependTwos, hn]

def unphi (l a : Sym) : Sym :=
  match l.val, a.val with
  | 0, 0 => 0 | 0, 1 => 1 | 0, 2 => 3 | 0, _ => 2
  | 2, 0 => 2 | 2, 1 => 3 | 2, 2 => 1 | 2, _ => 0
  | _, 0 => 3 | _, 1 => 2 | _, 2 => 1 | _, _ => 0

theorem phi_unphi : ∀ l a : Sym, phi l (unphi l a)=a := by decide
theorem unphi_phi : ∀ l r : Sym, unphi l (phi l r)=r := by decide

def lift (a : Sym) (v : Stream) : Stream
  | 0 => a
  | j+1 => unphi (lift a v j) (v (j+1))

def liftWord : List Sym → Stream → Stream
  | [], v => v
  | a::u, v => liftWord u (lift a v)

theorem peelPow_liftWord (u : List Sym) (v : Stream) :
    peelPow u.length (liftWord u v)=shiftN v u.length := by
  induction u generalizing v with
  | nil => rfl
  | cons a u ih =>
    simp only [List.length_cons, liftWord, peelPow, ih]
    funext t
    change phi (lift a v (t+u.length)) (lift a v ((t+1)+u.length)) =
      v (t+(u.length+1))
    have hindex : (t+1)+u.length=(t+u.length)+1 := by omega
    rw [hindex, lift, phi_unphi]
    congr 1 <;> omega

/-! ### The binary separator and the weak wedge hypothesis -/

/-- **`BinaryCTS`**: no stream of binary symbols has an inverse diagonal that is eventually constant `2` or `3`. The
kit's `ConstantTailSeparator` without the hard-core condition. -/
def BinaryCTS : Prop :=
  ∀ c, constantTail c → ∀ e : Stream, (∀ i, binary (e i)) → ¬EventuallyConstant (inverse e) c

/-- **`WeakBWH S L`**: for every `n ∈ S`, no binary word of length `n + L n` has a constant wedge `c ∈ {2, 3}` of
length `L n` at depth `n`. -/
def WeakBWH (S : Nat → Prop) (L : Nat → Nat) : Prop :=
  ∀ n, S n → ∀ c, constantTail c → ∀ e, BinaryPrefix e (n + L n) → ¬ConstantWedge n (L n) c e

theorem binary_prepend (e : Stream) (d : Nat) (hb : ∀ i, binary (e i)) :
    ∀ i, binary (prependTwos e d i) := by
  intro i
  by_cases hi : i<d
  · simp [prependTwos, hi, binary]
  · simpa [prependTwos, hi] using hb (i-d)

/-! ### The binary analogs of the kit's separator consequences (kit main `Rule30SeparatorEquivalences`) -/

theorem zero_lift_fixed : ∀ a : Sym, unphi (unphi a 0) 0=unphi a 0 := by decide
theorem zero_lift_values : ∀ a : Sym, unphi a 0=0 ∨ constantTail (unphi a 0) := by
  unfold constantTail
  decide
theorem phi_right_zero : ∀ a : Sym, phi a 0=0 → a=0 := by decide

theorem peel_zero_classification (x : Stream) (K : Nat)
    (h : ∀ t, K≤t → peel x t=0) :
    ∃ a, (a=0 ∨ constantTail a) ∧ ∀ t, K+1≤t → x t=a := by
  have nextZero (t : Nat) (ht : K≤t) : x (t+1)=unphi (x t) 0 := by
    calc
      x (t+1)=unphi (x t) (peel x t) := (unphi_phi _ _).symm
      _ = unphi (x t) 0 := by rw [h t ht]
  let a := unphi (x K) 0
  have tail (n : Nat) : x (K+1+n)=a := by
    induction n with
    | zero => exact nextZero K (by omega)
    | succ n ih =>
      have hi : K+1+(n+1)=(K+1+n)+1 := by omega
      rw [hi,nextZero (K+1+n) (by omega),ih]
      exact zero_lift_fixed (x K)
  refine ⟨a,zero_lift_values (x K),?_⟩
  intro t ht
  have heq : K+1+(t-(K+1))=t := by omega
  simpa only [heq] using tail (t-(K+1))

end WedgeLadder

open WedgeKit WedgeLadder

/-- `BWH` is `WeakBWH` on the lengths `n ≥ 7` with the horizon `n + 2`. -/
theorem bwh_iff_weakBWH : BWH ↔ WeakBWH (fun n => 7 ≤ n) (fun n => n + 2) := by
  constructor
  · intro h n hn c hc e hb
    exact h n hn c hc e (by intro i hi; exact hb i (show i < n + (n+2) by omega))
  · intro h n hn c hc e hb
    exact h n hn c hc e (by intro i hi; have hi' : i < n + (n+2) := hi; exact hb i (by omega))

/-- **`WeakBWH` on an infinite set of lengths, with any horizon, implies `BinaryCTS`.** -/
theorem weakBWH_binaryCTS {S : Nat → Prop} {L : Nat → Nat} (hS : ∀ N, ∃ n, N ≤ n ∧ S n) (h : WeakBWH S L) :
    BinaryCTS := by
  intro c hc e hb ⟨N, hN⟩
  obtain ⟨n, hn, hSn⟩ := hS N
  refine h n hSn c hc (shiftN e n) (fun i _ => hb (i+n)) ?_
  intro t _
  rw [rotated_iterate]
  exact hN (t+2*n) (by omega)

/-- **`BWH` implies `BinaryCTS`.** -/
theorem bwh_binaryCTS (hb : BWH) : BinaryCTS :=
  weakBWH_binaryCTS (fun N => ⟨N + 7, by omega, by omega⟩) (bwh_iff_weakBWH.1 hb)

/-- `BinaryCTS` gives the kit's `ConstantTailSeparator`: a hard-core stream is binary. -/
theorem binaryCTS_constantTailSeparator (h : BinaryCTS) : ConstantTailSeparator :=
  fun c hc e hh => h c hc e hh.1

/-- **`BWH` alone gives the kit's `ConstantTailSeparator`**, with no `SmallRW` and no `RW`. -/
theorem bwh_constantTailSeparator (hb : BWH) : ConstantTailSeparator :=
  binaryCTS_constantTailSeparator (bwh_binaryCTS hb)

/-! ### The vacuum under a constant wedge -/

theorem wedge_vacuum_phi : phi 0 0 = 0 ∧ phi 2 2 = 0 ∧ phi 3 3 = 0 := by decide

theorem peelPow_add (n k : Nat) (x : Stream) : peelPow (n+k) x = peelPow k (peelPow n x) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show peel (peelPow (n+k) x) = peel (peelPow k (peelPow n x))
    rw [ih]

theorem peelPow_zeros (k : Nat) : peelPow k (fun _ => (0 : Sym)) = fun _ => 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show peel (peelPow k (fun _ => (0 : Sym))) = _
    rw [ih]
    rfl

/-- **The vacuum.** A constant wedge `c ∈ {2, 3}` of length `L` at depth `n` makes every deeper peel vanish inside the
triangle it spans: `peelPow (n + k) (inverse e) t = 0` for `1 ≤ k` and `t + k < L`. -/
theorem wedge_vacuum (n L k t : Nat) (c : Sym) (e : Stream) (hc : constantTail c) (hw : ConstantWedge n L c e)
    (hk : 1 ≤ k) (ht : t + k < L) : peelPow (n + k) (inverse e) t = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [show n + (k+1) = (n+1) + k by omega, peelPow_add]
  have hz : ∀ i, t ≤ i → i ≤ t + k → peelPow (n+1) (inverse e) i = (fun _ => (0 : Sym)) i := by
    intro i _ hi
    show phi (wedge n e i) (wedge n e (i+1)) = 0
    rw [hw i (by omega), hw (i+1) (by omega)]
    rcases hc with rfl | rfl <;> decide
  rw [peelPow_locality _ _ k t hz, peelPow_zeros]

/-- The vacuum for `BWH`'s horizon: a constant wedge of length `n + 2` forces zeros for `1 ≤ k`, `t + k ≤ n + 1`. -/
theorem wedge_vacuum_bwh (n k t : Nat) (c : Sym) (e : Stream) (hc : constantTail c)
    (hw : ConstantWedge n (n+2) c e) (hk : 1 ≤ k) (ht : t + k ≤ n + 1) : peelPow (n + k) (inverse e) t = 0 :=
  wedge_vacuum n (n+2) k t c e hc hw hk (by omega)

/-! ### The binary separator's consequences -/

/-- Under `BinaryCTS` no peel of the inverse of a binary stream is eventually constant `2` or `3`. -/
theorem binaryCTS_peel (h : BinaryCTS) (c : Sym) (hc : constantTail c) (e : Stream) (hb : ∀ i, binary (e i))
    (d : Nat) : ¬EventuallyConstant (peelPow d (inverse e)) c := by
  intro ⟨N, hN⟩
  apply h c hc (prependTwos e d) (binary_prepend e d hb)
  refine ⟨N + 2*d, ?_⟩
  intro t ht
  have hi := rotated_iterate (prependTwos e d) d (t-2*d)
  rw [shift_prepend, show t-2*d+2*d = t by omega] at hi
  rw [← hi]
  exact hN (t-2*d) (by omega)

/-- **The binary orbit separator.** Under `BinaryCTS`, no binary stream has an inverse of the form
`liftWord u (const c)`. -/
theorem binaryCTS_orbit (h : BinaryCTS) (c : Sym) (hc : constantTail c) (u : List Sym) (e : Stream)
    (hb : ∀ i, binary (e i)) : liftWord u (fun _ => c) ≠ inverse e := by
  intro heq
  apply binaryCTS_peel h c hc e hb u.length
  refine ⟨0, fun t _ => ?_⟩
  rw [← heq, peelPow_liftWord]
  rfl

theorem binaryCTS_peel_zero (h : BinaryCTS) (e : Stream) (hb : ∀ i, binary (e i)) (K : Nat)
    (hp : ∀ t, K≤t → peel (inverse e) t=0) :
    ∀ t, K≤t → inverse e t=0 := by
  obtain ⟨a,ha,he⟩ := peel_zero_classification (inverse e) K hp
  rcases ha with h0 | hc
  · subst a
    intro t ht
    by_cases hkt : t=K
    · subst t
      have h := hp K (by omega)
      change phi (inverse e K) (inverse e (K+1))=0 at h
      rw [he (K+1) (by omega)] at h
      exact phi_right_zero _ h
    · exact he t (by omega)
  · exact False.elim (h a hc e hb ⟨K+1,he⟩)

/-- Under `BinaryCTS` no binary stream has an inverse diagonal that is eventually `0`. -/
theorem binaryCTS_excludes_zero_cut (h : BinaryCTS) :
    ∀ K e, (∀ i, binary (e i)) → (∀ t, K≤t → inverse e t=0) → False := by
  intro K
  induction K using Nat.strongRecOn with
  | ind K ih =>
    intro e hb hz
    by_cases hK : K=0
    · subst K
      have h := hz 0 (by omega)
      rcases hb 0 with he | he <;> simp [inverse,cone,he,boundary] at h
    · have hn : K-2<K := by omega
      apply ih (K-2) hn (shiftN e 1) (fun i => hb (i+1))
      apply binaryCTS_peel_zero h (shiftN e 1) (fun i => hb (i+1)) (K-2)
      intro t ht
      have hs1 : shiftN e 1=shift e := rfl
      rw [hs1,rotated_peel]
      exact hz (t+2) (by omega)

/-- **No finite peel rank.** Under `BinaryCTS` no peel of the inverse of a binary stream is eventually `0`. -/
theorem binaryCTS_excludes_finite_peel_rank (h : BinaryCTS)
    (e : Stream) (hb : ∀ i, binary (e i)) (d K : Nat)
    (hz : ∀ t, K≤t → peelPow d (inverse e) t=0) : False := by
  apply binaryCTS_excludes_zero_cut h (K+2*d) (prependTwos e d) (binary_prepend e d hb)
  intro t ht
  have hi := rotated_iterate (prependTwos e d) d (t-2*d)
  rw [shift_prepend] at hi
  have hindex : t-2*d+2*d=t := by omega
  rw [hindex] at hi
  change peelPow d (inverse e) (t-2*d)=_ at hi
  rw [hz (t-2*d) (by omega)] at hi
  exact hi.symm

/-! ### Compactness: `BinaryCTS` bounds the horizon at every depth -/

namespace WedgeLadder

/-- A word whose extensions carry constant wedges `c` at depth `n` of every horizon. -/
def Unbounded (n : Nat) (c : Sym) (w : List Sym) : Prop :=
  ∀ L, ∃ e : Stream, (∀ i, i < w.length → e i = w.getD i 0) ∧ BinaryPrefix e (n+L) ∧ ConstantWedge n L c e

theorem getD_snoc (w : List Sym) (a : Sym) (i : Nat) (hi : i < w.length + 1) :
    (w ++ [a]).getD i 0 = if i < w.length then w.getD i 0 else a := by
  by_cases h : i < w.length
  · simp [h, List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · have : i = w.length := by omega
    subst this
    simp

/-- One of the two binary children of an unbounded word is unbounded. -/
theorem unbounded_child (n : Nat) (c : Sym) (w : List Sym) (h : Unbounded n c w) :
    Unbounded n c (w ++ [1]) ∨ Unbounded n c (w ++ [2]) := by
  apply Classical.byContradiction
  intro hn
  obtain ⟨h1, h2⟩ := not_or.1 hn
  obtain ⟨L1, hL1⟩ := Classical.not_forall.1 h1
  obtain ⟨L2, hL2⟩ := Classical.not_forall.1 h2
  obtain ⟨e, he, hb, hw⟩ := h (L1 + L2 + w.length + 1)
  have ext : ∀ a : Sym, e w.length = a → ∀ i, i < (w ++ [a]).length → e i = (w ++ [a]).getD i 0 := by
    intro a ha i hi
    simp only [List.length_append, List.length_cons, List.length_nil] at hi
    rw [getD_snoc w a i (by omega)]
    by_cases hlt : i < w.length
    · simp only [hlt, ite_true]; exact he i hlt
    · simp only [hlt, ite_false]; rw [show i = w.length by omega]; exact ha
  rcases hb w.length (by omega) with hx | hx
  · exact hL1 ⟨e, ext 1 hx, fun i hi => hb i (by omega), fun t ht => hw t (by omega)⟩
  · exact hL2 ⟨e, ext 2 hx, fun i hi => hb i (by omega), fun t ht => hw t (by omega)⟩

open Classical in
/-- The branch of unbounded words through the binary tree. -/
noncomputable def branch (n : Nat) (c : Sym) : Nat → List Sym
  | 0 => []
  | k+1 => if Unbounded n c (branch n c k ++ [1]) then branch n c k ++ [1] else branch n c k ++ [2]

theorem branch_length (n : Nat) (c : Sym) : ∀ k, (branch n c k).length = k
  | 0 => rfl
  | k+1 => by
    simp only [branch]
    split <;> simp [branch_length n c k]

theorem branch_unbounded (n : Nat) (c : Sym) (h0 : Unbounded n c []) : ∀ k, Unbounded n c (branch n c k)
  | 0 => h0
  | k+1 => by
    simp only [branch]
    split
    · assumption
    · rcases unbounded_child n c _ (branch_unbounded n c h0 k) with h | h
      · contradiction
      · exact h

theorem branch_succ_getD (n : Nat) (c : Sym) (k i : Nat) (hi : i < k) :
    (branch n c (k+1)).getD i 0 = (branch n c k).getD i 0 := by
  have hl := branch_length n c k
  simp only [branch]
  split <;> rw [getD_snoc _ _ i (by omega)] <;> simp [show i < (branch n c k).length by omega]

theorem branch_getD (n : Nat) (c : Sym) (i : Nat) : ∀ k, i < k → (branch n c k).getD i 0 = (branch n c (i+1)).getD i 0
  | 0, h => absurd h (by omega)
  | k+1, h => by
    by_cases hk : i < k
    · rw [branch_succ_getD n c k i hk, branch_getD n c i k hk]
    · rw [show k = i by omega]

theorem branch_binary (n : Nat) (c : Sym) (i : Nat) : binary ((branch n c (i+1)).getD i 0) := by
  have hl := branch_length n c i
  simp only [branch]
  split <;> rw [getD_snoc _ _ i (by omega)] <;> simp [show ¬ i < (branch n c i).length by omega, binary]

/-- The wedge at `t` reads the stream below `t + n + 1` only. -/
theorem wedge_local (n t : Nat) (e f : Stream) (h : ∀ i, i < t+n+1 → e i = f i) : wedge n e t = wedge n f t :=
  peelPow_locality _ _ n t (fun i _ hi => inverse_prefix e f (t+n+1) h i (by omega))

/-- **Compactness.** If constant wedges `c` of every horizon exist at depth `n`, one binary stream carries a constant
wedge `c` at depth `n` for ever. -/
theorem infinite_run_of_unbounded (n : Nat) (c : Sym) (h0 : Unbounded n c []) :
    ∃ e : Stream, (∀ i, binary (e i)) ∧ ∀ t, wedge n e t = c := by
  refine ⟨fun i => (branch n c (i+1)).getD i 0, fun i => branch_binary n c i, ?_⟩
  intro t
  obtain ⟨f, hf, _, hw⟩ := branch_unbounded n c h0 (t+n+1) (t+1)
  rw [branch_length] at hf
  rw [wedge_local n t _ f (fun i hi => by rw [hf i hi, branch_getD n c i (t+n+1) hi])]
  exact hw t (by omega)

end WedgeLadder

/-- **`BinaryCTS` bounds the horizon at every depth**: for every `n` and `c ∈ {2, 3}` some horizon `L` has no binary
word of length `n + L` with a constant wedge `c` of length `L` at depth `n`. -/
theorem binaryCTS_horizon (h : BinaryCTS) (n : Nat) (c : Sym) (hc : constantTail c) :
    ∃ L, ∀ e, BinaryPrefix e (n+L) → ¬ConstantWedge n L c e := by
  apply Classical.byContradiction
  intro hn
  have h0 : WedgeLadder.Unbounded n c [] := by
    intro L
    apply Classical.byContradiction
    intro hL
    apply hn ⟨L, fun e hb hw => hL ⟨e, fun i hi => absurd hi (by simp), hb, hw⟩⟩
  obtain ⟨e, hb, hw⟩ := WedgeLadder.infinite_run_of_unbounded n c h0
  exact binaryCTS_peel h c hc e hb n ⟨0, fun t _ => hw t⟩

/-- A horizon without witnesses stays without witnesses when it grows. -/
theorem no_run_mono (n L L' : Nat) (c : Sym) (hL : L ≤ L') (h : ∀ e, BinaryPrefix e (n+L) → ¬ConstantWedge n L c e) :
    ∀ e, BinaryPrefix e (n+L') → ¬ConstantWedge n L' c e :=
  fun e hb hw => h e (fun i hi => hb i (by omega)) (fun t ht => hw t (by omega))

/-- **`BinaryCTS` is `WeakBWH` at every depth with some horizon.** -/
theorem binaryCTS_iff_horizon : BinaryCTS ↔ ∃ L : Nat → Nat, WeakBWH (fun _ => True) L := by
  constructor
  · intro h
    refine ⟨fun n => Classical.choose (binaryCTS_horizon h n 2 (Or.inl rfl)) +
      Classical.choose (binaryCTS_horizon h n 3 (Or.inr rfl)), ?_⟩
    intro n _ c hc
    rcases hc with rfl | rfl
    · exact no_run_mono n _ _ 2 (Nat.le_add_right _ _) (Classical.choose_spec (binaryCTS_horizon h n 2 (Or.inl rfl)))
    · exact no_run_mono n _ _ 3 (Nat.le_add_left _ _) (Classical.choose_spec (binaryCTS_horizon h n 3 (Or.inr rfl)))
  · intro ⟨L, hL⟩
    exact weakBWH_binaryCTS (fun N => ⟨N, Nat.le_refl N, trivial⟩) hL

/-! ### Horizon `2n` for the small lengths, by search -/

namespace WedgeLadder

open WedgeSmall

/-- Every condition of a constant wedge `c` of length `L` at depth `n` that reads only the first `w.length` symbols. -/
def horizonTest (n L : Nat) (c : Sym) (w : List Sym) : Bool :=
  (List.range (min (w.length - n) L)).all (fun t => decide ((wedgeL n w).getD t 0 = c))

theorem horizonTest_of_run (n L : Nat) (c : Sym) (e : Stream) (hc : ConstantWedge n L c e) (k : Nat) :
    horizonTest n L c (pre e k) = true := by
  have agree : ∀ j, j < (pre e k).length → e j = (pre e k).getD j 0 := by
    intro j hj; rw [pre_length] at hj; rw [pre_getD e k j hj]
  simp only [horizonTest, List.all_eq_true, List.mem_range, decide_eq_true_eq, pre_length]
  intro t ht
  rw [wedgeL_spec n e (pre e k) agree t (by rw [pre_length]; omega)]
  exact hc t (by omega)

theorem no_run_of_search (n L : Nat) (c : Sym) (hs : wsearch (horizonTest n L c) (n+L) [] = true) :
    ∀ e, BinaryPrefix e (n+L) → ¬ConstantWedge n L c e := by
  intro e hb hw
  exact wsearch_sound (horizonTest n L c) e (n+L) 0 (fun i _ hi => hb i (by omega))
    (fun j _ _ => horizonTest_of_run n L c e hw j) (by simpa [pre] using hs)

/-- The two searches of one length `n`, with horizon `2n`. -/
def horizonSearches (n : Nat) : Bool :=
  [(2 : Sym), 3].all fun c => wsearch (horizonTest n (2*n) c) (n + 2*n) []

theorem horizon_n2 : horizonSearches 2 = true := by decide +kernel
theorem horizon_n3 : horizonSearches 3 = true := by decide +kernel
theorem horizon_n4 : horizonSearches 4 = true := by decide +kernel
theorem horizon_n5 : horizonSearches 5 = true := by decide +kernel
theorem horizon_n6 : horizonSearches 6 = true := by decide +kernel

theorem no_run_of_searches (n : Nat) (h : horizonSearches n = true) (c : Sym) (hc : constantTail c) :
    ∀ e, BinaryPrefix e (n + 2*n) → ¬ConstantWedge n (2*n) c e := by
  apply no_run_of_search
  simp only [horizonSearches, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
  rcases hc with rfl | rfl
  · exact h.1
  · exact h.2

end WedgeLadder

/-- **Horizon `2n` for `2 ≤ n ≤ 6`**: no binary word of length `3n` has a constant wedge `c ∈ {2, 3}` of length `2n`. -/
theorem weakBWH_small : WeakBWH (fun n => 2 ≤ n ∧ n ≤ 6) (fun n => 2*n) := by
  intro n ⟨h2, h6⟩ c hc
  have : n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl
  · exact WedgeLadder.no_run_of_searches 2 WedgeLadder.horizon_n2 c hc
  · exact WedgeLadder.no_run_of_searches 3 WedgeLadder.horizon_n3 c hc
  · exact WedgeLadder.no_run_of_searches 4 WedgeLadder.horizon_n4 c hc
  · exact WedgeLadder.no_run_of_searches 5 WedgeLadder.horizon_n5 c hc
  · exact WedgeLadder.no_run_of_searches 6 WedgeLadder.horizon_n6 c hc

end Rule30Open
