module

/-!
# `SmallRW`: the six small lengths of the rotated wedge hypothesis, and forced runs

The kit's main branch (`Rule30WedgeBridge`, commit cd5466b) states two open hypotheses on streams of four symbols, `BWH`
and `RW`, proves `bwh_implies_rw : BWH → SmallRW → RW`, and leaves `SmallRW`, the case `1 ≤ n < 7` of `RW`, to finite
certificates. `Rule30SEPToPeriodTwo` concludes from `BWH` and `SmallRW` that the official center column is not eventually
of period two. The pinned kit has neither module, so `Rule30Open.WedgeKit` restates the definitions verbatim; they are
definitionally the kit's.

* **`SmallRW` holds** (`wedge_small_rw`). For each of the 36 cases `(n, r, c)` a depth-first search over binary words
  (`wsearch`) checks every prefix of a would-be witness (`rwTest`) and prunes the prefixes that fail; the kernel
  evaluates each search by `decide +kernel` (`small_rw_n1`, …, `small_rw_n6`), and `wsearch_sound` turns a successful
  search into the absence of a witness.
* **A memoized cone.** The kit's `cone` recursion recomputes shared entries, so its unfolding grows like the Fibonacci
  numbers in the length of the word, and `peelPow n` doubles it `n` times. The checker computes the cone of a finite word row by row (`coneHeads`, `inverseL`) and peels lists (`wedgeL`);
  `wedgeL_spec` proves it equal to the kit's `wedge` on every stream that agrees with the word.
* **Forced runs** (`wedge_forced`). `phi a` is a bijection for every `a`, so the newest symbol of a prefix is fixed by
  the earlier ones and one wedge value: if two streams agree below `k ≥ n` and have the same `wedge n · (k - n)`, they
  agree at `k`. So at most one binary symbol continues a constant wedge, and the search for a witness of length `L` with
  `n` free symbols is a search over `2 ^ n` forced runs.

Nothing here proves `BWH` or `RW`, and nothing here bounds the center column of Rule 30.

The natural-language argument is `WedgeSmall.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open
namespace WedgeKit

/-! ### The kit's definitions (kit main `Rule30WedgeBridge`, verbatim) -/

abbrev Sym := Fin 4
abbrev Stream := Nat → Sym

def boundary (q : Sym) : Sym := ⟨3-q.val, by omega⟩

def phi (a b : Sym) : Sym :=
  match a.val, b.val with
  | 0, 0 => 0 | 0, 1 => 1 | 0, 2 => 3 | 0, _ => 2
  | 2, 0 => 3 | 2, 1 => 2 | 2, 2 => 0 | 2, _ => 1
  | _, 0 => 3 | _, 1 => 2 | _, 2 => 1 | _, _ => 0

def cone (e : Stream) : Nat → Nat → Sym
  | 0, j => boundary (e j)
  | 1, j => phi (e j) (boundary (e (j+1)))
  | t+2, j => phi (cone e t (j+1)) (cone e (t+1) (j+1))

def inverse (e : Stream) (t : Nat) : Sym := cone e t 0
def peel (x : Stream) (t : Nat) : Sym := phi (x t) (x (t+1))

def peelPow : Nat → Stream → Stream
  | 0, x => x
  | n+1, x => peel (peelPow n x)

def wedge (n : Nat) (e : Stream) : Stream := peelPow n (inverse e)

def binary (q : Sym) : Prop := q=1 ∨ q=2
def constantTail (q : Sym) : Prop := q=2 ∨ q=3
def BinaryPrefix (e : Stream) (L : Nat) : Prop := ∀ i, i < L → binary (e i)

def ConstantWedge (n L : Nat) (c : Sym) (e : Stream) : Prop :=
  ∀ t, t < L → wedge n e t = c

def HardCoreJunction (n L : Nat) (e : Stream) : Prop :=
  ∀ i, n ≤ i → i < L → ¬(e (i-1)=1 ∧ e i=1)

def RWWitness (n r : Nat) (c : Sym) (e : Stream) : Prop :=
  BinaryPrefix e (2*n+r+2) ∧
  HardCoreJunction n (2*n+r+2) e ∧
  ConstantWedge n (n+r+2) c e ∧
  e (2*n+r-1)=1 ∧ e (2*n+r)=2

def BWH : Prop := ∀ n, 7 ≤ n → ∀ c, constantTail c → ∀ e,
  BinaryPrefix e (2*n+2) → ¬ConstantWedge n (n+2) c e

def SmallRW : Prop := ∀ n, 1 ≤ n → n < 7 → ∀ r, r ≤ 2 → ∀ c,
  constantTail c → ∀ e, ¬RWWitness n r c e

def RW : Prop := ∀ n, 1 ≤ n → ∀ r, r ≤ 2 → ∀ c,
  constantTail c → ∀ e, ¬RWWitness n r c e

theorem cone_locality (e f : Stream) (t : Nat) :
    ∀ j, (∀ i, j ≤ i → i ≤ j+t → e i = f i) → cone e t j = cone f t j := by
  induction t using Nat.strongRecOn with
  | ind t ih =>
    intro j h
    match t with
    | 0 => simp only [cone]; rw [h j (by omega) (by omega)]
    | 1 => simp only [cone]; rw [h j (by omega) (by omega), h (j+1) (by omega) (by omega)]
    | t+2 =>
      simp only [cone]
      rw [ih t (by omega) (j+1) (by intro i hi hj; exact h i (by omega) (by omega)),
          ih (t+1) (by omega) (j+1) (by intro i hi hj; exact h i (by omega) (by omega))]

theorem inverse_prefix (e f : Stream) (L : Nat)
    (h : ∀ i, i < L → e i = f i) :
    ∀ i, i < L → inverse e i = inverse f i := by
  intro i hi
  exact cone_locality e f i 0 (by intro j _ hj; exact h j (by omega))

theorem peelPow_locality (x y : Stream) (n : Nat) :
    ∀ t, (∀ i, t ≤ i → i ≤ t+n → x i = y i) → peelPow n x t = peelPow n y t := by
  induction n with
  | zero => intro t h; exact h t (by omega) (by omega)
  | succ n ih =>
    intro t h
    simp only [peelPow, peel]
    rw [ih t (by intro i hi hj; exact h i hi (by omega)),
        ih (t+1) (by intro i hi hj; exact h i (by omega) (by omega))]

end WedgeKit

open WedgeKit

/-! ### Forced runs -/

namespace WedgeSmall

theorem wedge_phi_cancel : ∀ a b b' : Sym, phi a b = phi a b' → b = b' := by decide

theorem wedge_boundary_cancel : ∀ q q' : Sym, boundary q = boundary q' → q = q' := by decide

/-- The newest symbol of a cone entry is fixed by the entry and the earlier symbols. -/
theorem cone_newest (e f : Stream) (t : Nat) :
    ∀ j, (∀ i, i < j+t → e i = f i) → cone e t j = cone f t j → e (j+t) = f (j+t) := by
  induction t using Nat.strongRecOn with
  | ind t ih =>
    intro j h hc
    match t with
    | 0 => exact wedge_boundary_cancel _ _ hc
    | 1 =>
      simp only [cone] at hc
      rw [h j (by omega)] at hc
      exact wedge_boundary_cancel _ _ (wedge_phi_cancel _ _ _ hc)
    | t+2 =>
      simp only [cone] at hc
      rw [cone_locality e f t (j+1) (by intro i _ hi; exact h i (by omega))] at hc
      have := ih (t+1) (by omega) (j+1) (by intro i hi; exact h i (by omega)) (wedge_phi_cancel _ _ _ hc)
      rwa [show j+1+(t+1) = j+(t+2) by omega] at this

/-- The newest entry of a peeled stream is fixed by the peeled value and the earlier entries. -/
theorem peelPow_newest (x y : Stream) (m : Nat) :
    ∀ t, (∀ i, i < t+m → x i = y i) → peelPow m x t = peelPow m y t → x (t+m) = y (t+m) := by
  induction m with
  | zero => intro t _ hp; simpa [peelPow] using hp
  | succ m ih =>
    intro t h hp
    simp only [peelPow, peel] at hp
    rw [peelPow_locality x y m t (by intro i _ hi; exact h i (by omega))] at hp
    have := ih (t+1) (by intro i hi; exact h i (by omega)) (wedge_phi_cancel _ _ _ hp)
    rwa [show t+1+m = t+(m+1) by omega] at this

end WedgeSmall

open WedgeSmall

/-- **Forced runs.** Two streams that agree below `k ≥ n` and have the same wedge value at `k - n` agree at `k`. -/
theorem wedge_forced (n k : Nat) (e f : Stream) (h : ∀ i, i < k → e i = f i) (hk : n ≤ k)
    (hw : wedge n e (k-n) = wedge n f (k-n)) : e k = f k := by
  have hi := peelPow_newest (inverse e) (inverse f) n (k-n)
    (by intro i hi; exact inverse_prefix e f k h i (by omega)) hw
  rw [show k-n+n = k by omega] at hi
  have := cone_newest e f k 0 (by intro i hi; exact h i (by omega)) hi
  simpa using this

/-- At most one binary symbol continues a constant wedge: a prefix has at most one binary child that keeps it. -/
theorem wedge_one_child (n k : Nat) (c : Sym) (e f : Stream) (h : ∀ i, i < k → e i = f i) (hk : n ≤ k)
    (he : wedge n e (k-n) = c) (hf : wedge n f (k-n) = c) : e k = f k :=
  wedge_forced n k e f h hk (he.trans hf.symm)

/-! ### The memoized cone of a word -/

namespace WedgeSmall

/-- The first entries of the cone rows `t, t+1, …, t+k-1`, from the rows `a` (row `t`) and `b` (row `t+1`). -/
def coneHeads : Nat → List Sym → List Sym → List Sym
  | 0, _, _ => []
  | k+1, a, b => a.headD 0 :: coneHeads k b (List.zipWith phi a.tail b.tail)

def row0 (w : List Sym) : List Sym := w.map boundary
def row1 (w : List Sym) : List Sym := List.zipWith phi w (row0 w).tail

/-- `inverse t` for `t < w.length`, for every stream that starts with `w`. -/
def inverseL (w : List Sym) : List Sym := coneHeads w.length (row0 w) (row1 w)

def peelL (x : List Sym) : List Sym := List.zipWith phi x x.tail

def peelPowL : Nat → List Sym → List Sym
  | 0, x => x
  | n+1, x => peelL (peelPowL n x)

/-- `wedge n e t` for `t + n < w.length`, for every stream `e` that starts with `w`. -/
def wedgeL (n : Nat) (w : List Sym) : List Sym := peelPowL n (inverseL w)

theorem getD_zipWith (f : Sym → Sym → Sym) : ∀ (a b : List Sym) (j : Nat), j < a.length → j < b.length →
    (List.zipWith f a b).getD j 0 = f (a.getD j 0) (b.getD j 0)
  | [], _, _, h, _ => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | _ :: _, _ :: _, 0, _, _ => by simp
  | _ :: a, _ :: b, j+1, h1, h2 => by
    simp only [List.zipWith_cons_cons, List.getD_cons_succ, List.length_cons] at h1 h2 ⊢
    exact getD_zipWith f a b j (by omega) (by omega)

theorem getD_tail (a : List Sym) (j : Nat) : a.tail.getD j 0 = a.getD (j+1) 0 := by
  cases a <;> simp

theorem getD_map_boundary : ∀ (w : List Sym) (j : Nat), j < w.length →
    (w.map boundary).getD j 0 = boundary (w.getD j 0)
  | [], _, h => by simp at h
  | _ :: _, 0, _ => by simp
  | _ :: w, j+1, h => by
    simp only [List.map_cons, List.getD_cons_succ, List.length_cons] at h ⊢
    exact getD_map_boundary w j (by omega)

theorem coneHeads_length : ∀ (k : Nat) (a b : List Sym), (coneHeads k a b).length = k
  | 0, _, _ => rfl
  | k+1, a, b => by simp [coneHeads, coneHeads_length k]

theorem coneHeads_spec (e : Stream) : ∀ (k t : Nat) (a b : List Sym),
    a.length = k → b.length = k - 1 →
    (∀ j, j < k → a.getD j 0 = cone e t j) → (∀ j, j < k - 1 → b.getD j 0 = cone e (t+1) j) →
    ∀ i, i < k → (coneHeads k a b).getD i 0 = cone e (t+i) 0
  | 0, _, _, _, _, _, _, _, i, hi => absurd hi (by omega)
  | k+1, t, a, b, ha, hb, hA, hB, i, hi => by
    match i with
    | 0 =>
      simp only [coneHeads, List.getD_cons_zero, Nat.add_zero]
      rw [← hA 0 (by omega)]
      cases a with
      | nil => simp at ha
      | cons x a => rfl
    | i+1 =>
      simp only [coneHeads, List.getD_cons_succ]
      have hc : ∀ j, j < k - 1 → (List.zipWith phi a.tail b.tail).getD j 0 = cone e (t+1+1) j := by
        intro j hj
        rw [getD_zipWith phi a.tail b.tail j (by simp; omega) (by simp; omega), getD_tail, getD_tail,
          hA (j+1) (by omega), hB (j+1) (by omega)]
        rfl
      have := coneHeads_spec e k (t+1) b (List.zipWith phi a.tail b.tail) (by omega)
        (by simp; omega) (by intro j hj; exact hB j (by omega)) hc i (by omega)
      rwa [show t+1+i = t+(i+1) by omega] at this

/-- The memoized inverse agrees with the kit's `inverse` on every stream that starts with the word. -/
theorem inverseL_spec (e : Stream) (w : List Sym) (hw : ∀ j, j < w.length → e j = w.getD j 0) :
    (inverseL w).length = w.length ∧ ∀ i, i < w.length → (inverseL w).getD i 0 = inverse e i := by
  refine ⟨coneHeads_length _ _ _, ?_⟩
  intro i hi
  have h := coneHeads_spec e w.length 0 (row0 w) (row1 w) (by simp [row0]) (by simp [row1, row0])
    (by
      intro j hj
      simp only [row0, cone]
      rw [getD_map_boundary w j hj, hw j hj])
    (by
      intro j hj
      simp only [row1, row0, cone]
      rw [getD_zipWith phi w _ j (by omega) (by simp; omega), getD_tail, getD_map_boundary w (j+1) (by omega),
        hw j (by omega), hw (j+1) (by omega)])
    i hi
  simpa [inverse, inverseL] using h

theorem peelPowL_spec (y : Stream) : ∀ (n : Nat) (x : List Sym),
    (∀ i, i < x.length → x.getD i 0 = y i) →
    (peelPowL n x).length = x.length - n ∧ ∀ t, t + n < x.length → (peelPowL n x).getD t 0 = peelPow n y t
  | 0, x, hx => ⟨by simp [peelPowL], fun t ht => by simpa [peelPowL, peelPow] using hx t (by omega)⟩
  | n+1, x, hx => by
    obtain ⟨hl, hv⟩ := peelPowL_spec y n x hx
    refine ⟨by simp [peelPowL, peelL, hl]; omega, ?_⟩
    intro t ht
    simp only [peelPowL, peelL, peelPow, peel]
    rw [getD_zipWith phi _ _ t (by omega) (by simp; omega), getD_tail, hv t (by omega), hv (t+1) (by omega)]

/-- **The memoized wedge is the kit's wedge.** -/
theorem wedgeL_spec (n : Nat) (e : Stream) (w : List Sym) (hw : ∀ j, j < w.length → e j = w.getD j 0) :
    ∀ t, t + n < w.length → (wedgeL n w).getD t 0 = wedge n e t := by
  obtain ⟨hl, hv⟩ := inverseL_spec e w hw
  intro t ht
  exact (peelPowL_spec (inverse e) n (inverseL w) (by intro i hi; exact hv i (by omega))).2 t (by omega)

/-! ### The search for a witness -/

/-- The prefix of length `k` of a stream. -/
def pre (e : Stream) (k : Nat) : List Sym := (List.range k).map e

theorem pre_length (e : Stream) (k : Nat) : (pre e k).length = k := by simp [pre]

theorem pre_getD (e : Stream) (k j : Nat) (hj : j < k) : (pre e k).getD j 0 = e j := by
  simp [pre, hj]

theorem pre_succ (e : Stream) (k : Nat) : pre e (k+1) = pre e k ++ [e k] := by
  simp [pre, List.range_succ]

/-- Depth-first search over binary words: `true` when no extension of `w` by `f` binary symbols passes `test` at every
prefix length from `w` on. -/
def wsearch (test : List Sym → Bool) : Nat → List Sym → Bool
  | 0, w => !test w
  | f+1, w => !test w || (wsearch test f (w ++ [1]) && wsearch test f (w ++ [2]))

theorem wsearch_sound (test : List Sym → Bool) (e : Stream) : ∀ (f k : Nat),
    (∀ i, k ≤ i → i < k+f → binary (e i)) → (∀ j, k ≤ j → j ≤ k+f → test (pre e j) = true) →
    wsearch test f (pre e k) = true → False
  | 0, k, _, ht, hs => by
    simp only [wsearch, ht k (by omega) (by omega)] at hs
    exact absurd hs (by decide)
  | f+1, k, hb, ht, hs => by
    simp only [wsearch, ht k (by omega) (by omega), Bool.not_true, Bool.false_or, Bool.and_eq_true] at hs
    have hnext : wsearch test f (pre e (k+1)) = true := by
      rw [pre_succ]
      rcases hb k (by omega) (by omega) with h | h <;> rw [h]
      · exact hs.1
      · exact hs.2
    exact wsearch_sound test e f (k+1) (fun i h1 h2 => hb i (by omega) (by omega))
      (fun j h1 h2 => ht j (by omega) (by omega)) hnext

/-- Every condition of `RWWitness n r c` that reads only the first `w.length` symbols. -/
def rwTest (n r : Nat) (c : Sym) (w : List Sym) : Bool :=
  (List.range w.length).all (fun i => !(decide (n ≤ i) && decide (w.getD (i-1) 0 = 1) && decide (w.getD i 0 = 1))) &&
  (!decide (2*n+r-1 < w.length) || decide (w.getD (2*n+r-1) 0 = 1)) &&
  (!decide (2*n+r < w.length) || decide (w.getD (2*n+r) 0 = 2)) &&
  (List.range (min (w.length - n) (n+r+2))).all (fun t => decide ((wedgeL n w).getD t 0 = c))

theorem rwTest_of_witness (n r : Nat) (c : Sym) (e : Stream) (hw : RWWitness n r c e) (k : Nat)
    (hk : k ≤ 2*n+r+2) : rwTest n r c (pre e k) = true := by
  obtain ⟨_, hh, hc, h1, h2⟩ := hw
  have agree : ∀ j, j < (pre e k).length → e j = (pre e k).getD j 0 := by
    intro j hj; rw [pre_length] at hj; rw [pre_getD e k j hj]
  simp only [rwTest, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, decide_eq_true_eq, pre_length]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · intro i hi
    simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
    by_cases hni : n ≤ i
    · rw [pre_getD e k i hi, pre_getD e k (i-1) (by omega)]
      have := hh i hni (by omega)
      by_cases h' : e (i-1) = 1
      · exact Or.inr (fun h'' => this ⟨h', h''⟩)
      · exact Or.inl (Or.inr h')
    · exact Or.inl (Or.inl hni)
  · by_cases hl : 2*n+r-1 < k
    · exact Or.inr (by rw [pre_getD e k _ hl]; exact h1)
    · exact Or.inl hl
  · by_cases hl : 2*n+r < k
    · exact Or.inr (by rw [pre_getD e k _ hl]; exact h2)
    · exact Or.inl hl
  · intro t ht
    rw [wedgeL_spec n e (pre e k) agree t (by rw [pre_length]; omega)]
    exact hc t (by omega)

/-- A successful search over the binary words of length `2n + r + 2` excludes every `RWWitness n r c`. -/
theorem no_rw_witness_of_search (n r : Nat) (c : Sym) (hs : wsearch (rwTest n r c) (2*n+r+2) [] = true) :
    ∀ e, ¬RWWitness n r c e := by
  intro e hw
  exact wsearch_sound (rwTest n r c) e (2*n+r+2) 0 (fun i _ hi => hw.1 i (by omega))
    (fun j _ hj => rwTest_of_witness n r c e hw j (by omega)) (by simpa [pre] using hs)

/-! ### The 36 searches -/

/-- The 6 searches of one length `n`. -/
def rwSearches (n : Nat) : Bool :=
  [0, 1, 2].all fun r => [(2 : Sym), 3].all fun c => wsearch (rwTest n r c) (2*n+r+2) []

theorem no_rw_of_searches (n : Nat) (h : rwSearches n = true) (r : Nat) (hr : r ≤ 2) (c : Sym)
    (hc : constantTail c) : ∀ e, ¬RWWitness n r c e := by
  apply no_rw_witness_of_search
  simp only [rwSearches, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
  rcases hc with rfl | rfl <;> (have : r = 0 ∨ r = 1 ∨ r = 2 := by omega) <;>
    rcases this with rfl | rfl | rfl <;> simp_all

theorem small_rw_n1 : rwSearches 1 = true := by decide +kernel
theorem small_rw_n2 : rwSearches 2 = true := by decide +kernel
theorem small_rw_n3 : rwSearches 3 = true := by decide +kernel
theorem small_rw_n4 : rwSearches 4 = true := by decide +kernel
theorem small_rw_n5 : rwSearches 5 = true := by decide +kernel
theorem small_rw_n6 : rwSearches 6 = true := by decide +kernel

end WedgeSmall

/-- **`SmallRW` holds**: for `1 ≤ n < 7`, `r ≤ 2` and `c ∈ {2, 3}` no stream is an `RWWitness n r c`. -/
theorem wedge_small_rw : SmallRW := by
  intro n hn1 hn7 r hr c hc
  have : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl
  · exact no_rw_of_searches 1 small_rw_n1 r hr c hc
  · exact no_rw_of_searches 2 small_rw_n2 r hr c hc
  · exact no_rw_of_searches 3 small_rw_n3 r hr c hc
  · exact no_rw_of_searches 4 small_rw_n4 r hr c hc
  · exact no_rw_of_searches 5 small_rw_n5 r hr c hc
  · exact no_rw_of_searches 6 small_rw_n6 r hr c hc

/-- With `SmallRW` proved, `RW` is `BWH`'s consequence on the kit's definitions: `RW` for `n ≥ 7` is all that remains. -/
theorem wedge_rw_of_large (h : ∀ n, 7 ≤ n → ∀ r, r ≤ 2 → ∀ c, constantTail c → ∀ e, ¬RWWitness n r c e) : RW := by
  intro n hn r hr c hc e
  by_cases hs : n < 7
  · exact wedge_small_rw n hn hs r hr c hc e
  · exact h n (by omega) r hr c hc e

end Rule30Open
