module

public import Rule30Open.Foundations.Evolve
public import Ruliology.CellularAutomata.Rule30PredecessorCounts

/-!
# The rows of a ring that one step of Rule 30 does not reach

A row of a ring of `W` cells is a list of `W` cells, cell `W - 1` beside cell `0`; `rows W` lists all `2^W` of them
(`rows_length`), each once (`rows_count`). `ringStep` is one step of Rule 30 on a ring (`ringStep_getD`), `preimages W z`
counts the rows that it maps to `z`, and `missed W` counts the rows with no preimage. With `p_W` the sum of the `W`-th
powers of the three roots of `x^3 - x^2 - 2` (`powerSum`: `p_0 = 3`, `p_1 = p_2 = 1`, `p_(n+3) = p_(n+2) + 2 p_n`),
for every `W ≥ 1`:

* `ring_missed_rows`: `2 * missed W + 2 * [3 ∣ W] = p_W + 1`, so `missed W = (p_W + 1) / 2 - [3 ∣ W]`
  (`ring_missed_rows_div`), and the image has `2^W - missed W` rows (`ring_image_card`);
* `ring_preimages_le_three`: every row has at most three preimages;
* `ring_three_preimages`: one row has three preimages when `3 ∣ W`, and none otherwise;
* `numWithPreds_zero_closed`, `numWithPreds_two_closed`: the same count in the kit's terms. `ringStep` is the kit's
  `Rule30.step` on a cyclic register (`ringStep_eq_step`) and `missed W` is its `Rule30.numWithPreds 0 W`
  (`missed_eq_numWithPreds`), so with the kit's `c_0 = c_2 + 2 [3 ∣ W]` both `c_0` and `c_2` have a closed form.

The proof is a transfer-matrix count, in four steps.

* **Collisions are cyclic words.** Two rows `x ≠ y` with one image differ on every pair of adjacent cells, by left
  permutivity going around the ring. So the ordered pairs `(x, y)` of distinct rows with one image are the words over
  the four letters `(x_i, y_i)` whose cyclic windows of three letters all pass one local test `okP`
  (`pair_collision_iff`, `pairs_eq_trace`). Ordered triples of pairwise distinct rows with one image are the words over
  eight letters that pass `okT`, the test `okP` on each of the three pairs (`triples_eq_trace`).
* **Cyclic words are traces.** For any alphabet and window test, the cyclic words of length `W` number
  `∑_(a, b) walk W a b a b` (`cyc_count`), the trace of the `W`-th power of the transfer matrix on pairs of letters.
* **Traces satisfy recurrences.** `walk (n + k) = walk n * walk k` (`walk_add`), so a linear relation among
  `walk k, ..., walk (k + j)` that holds on every entry, checked by `decide +kernel`, holds for the traces at every
  shift (`trace_rec`). The relations are `M^2 (M - 1)(M^3 - M^2 - 2) = 0` for the 16 states of pairs (`recP`) and
  `M^5 = M^2` for the 64 states of triples (`recT`), so the pair trace is `p_W + 1` (`pairTrace_eq`) and the triple
  trace is `6 [3 ∣ W]` (`tripleTrace_eq`).
* **Counting.** With `c ≤ 3` the number of preimages of a row, `6 [c = 0] + 6 c + c (c - 1) (c - 2) = 6 + 3 c (c - 1)`.
  Summed over all rows, `6 * missed + T = 3 * P` (`six_missed`), with `P = ∑ c (c - 1)` the ordered pairs
  (`pairs_total`) and `T = ∑ c (c - 1) (c - 2)` the ordered triples (`triples_total`).

The natural-language argument is `RingImages.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

namespace RingImages

/-! ### Sums over lists -/

/-- The sum of `f` over the list `l`. -/
def lsum {α : Type} : List α → (α → Nat) → Nat
  | [], _ => 0
  | a :: l, f => f a + lsum l f

/-- `1` when `b` holds, `0` otherwise. -/
def ind (b : Bool) : Nat := if b then 1 else 0

theorem ind_and (a b : Bool) : ind (a && b) = ind a * ind b := by
  cases a <;> cases b <;> rfl

theorem ind_le_one (b : Bool) : ind b ≤ 1 := by
  cases b <;> decide

section Sums

variable {α β : Type}

theorem lsum_append (l m : List α) (f : α → Nat) : lsum (l ++ m) f = lsum l f + lsum m f := by
  induction l with
  | nil => simp [lsum]
  | cons a l ih => simp only [List.cons_append, lsum, ih]; omega

theorem lsum_congr {l : List α} {f g : α → Nat} (h : ∀ a ∈ l, f a = g a) : lsum l f = lsum l g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [lsum]
    rw [h a (by simp), ih fun b hb => h b (by simp [hb])]

theorem lsum_le {l : List α} {f g : α → Nat} (h : ∀ a ∈ l, f a ≤ g a) : lsum l f ≤ lsum l g := by
  induction l with
  | nil => exact Nat.le_refl 0
  | cons a l ih =>
    simp only [lsum]
    have h1 := h a (by simp)
    have h2 := ih fun b hb => h b (by simp [hb])
    omega

theorem lsum_add (l : List α) (f g : α → Nat) : lsum l (fun a => f a + g a) = lsum l f + lsum l g := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [lsum, ih]; omega

theorem lsum_mul (l : List α) (k : Nat) (f : α → Nat) : lsum l (fun a => k * f a) = k * lsum l f := by
  induction l with
  | nil => simp [lsum]
  | cons a l ih => simp only [lsum, ih, Nat.mul_add]

theorem lsum_mul_right (l : List α) (k : Nat) (f : α → Nat) : lsum l (fun a => f a * k) = lsum l f * k := by
  induction l with
  | nil => simp [lsum]
  | cons a l ih => simp only [lsum, ih, Nat.add_mul]

theorem lsum_zero (l : List α) : lsum l (fun _ => 0) = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [lsum, ih]

theorem lsum_eq_zero {l : List α} {f : α → Nat} (h : ∀ a ∈ l, f a = 0) : lsum l f = 0 :=
  (lsum_congr h).trans (lsum_zero l)

theorem lsum_comm (l : List α) (m : List β) (f : α → β → Nat) :
    lsum l (fun a => lsum m (f a)) = lsum m (fun b => lsum l (fun a => f a b)) := by
  induction l with
  | nil => exact (lsum_zero m).symm
  | cons a l ih =>
    simp only [lsum]
    rw [ih]
    exact (lsum_add m (f a) _).symm

theorem lsum_flatMap (l : List α) (g : α → List β) (f : β → Nat) :
    lsum (l.flatMap g) f = lsum l (fun a => lsum (g a) f) := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, lsum_append, ih]; rfl

theorem lsum_map (l : List α) (g : α → β) (f : β → Nat) : lsum (l.map g) f = lsum l (fun a => f (g a)) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, lsum, ih]

theorem countP_eq_lsum (p : α → Bool) (l : List α) : l.countP p = lsum l (fun a => ind (p a)) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.countP_cons, ih]
    simp only [lsum, ind]
    cases p a <;> simp <;> omega

/-- An alphabet lists every letter exactly once. -/
def Complete [DecidableEq α] (alph : List α) : Prop :=
  ∀ x : α, lsum alph (fun a => ind (decide (a = x))) = 1

/-- Summing against the indicator of a letter that occurs once picks out that letter. -/
theorem lsum_pick [DecidableEq α] {l : List α} (x : α) (hx : lsum l (fun a => ind (decide (a = x))) = 1)
    (g : α → Nat) : lsum l (fun a => ind (decide (a = x)) * g a) = g x := by
  have : lsum l (fun a => ind (decide (a = x)) * g a) = lsum l (fun a => ind (decide (a = x)) * g x) :=
    lsum_congr fun a _ => by by_cases h : a = x <;> simp [h, ind]
  rw [this, lsum_mul_right, hx, Nat.one_mul]

theorem lsum_pick_const [DecidableEq α] {l : List α} (x : α) (hx : lsum l (fun a => ind (decide (a = x))) = 1)
    (k : Nat) : lsum l (fun a => ind (decide (a = x)) * k) = k := by
  rw [lsum_mul_right, hx, Nat.one_mul]

end Sums

/-! ### Words over an alphabet -/

section Words

variable {α : Type}

/-- All words of length `n` over the letters of `alph`. -/
def words (alph : List α) : Nat → List (List α)
  | 0 => [[]]
  | n + 1 => alph.flatMap fun a => (words alph n).map (a :: ·)

theorem lsum_words_zero (alph : List α) (f : List α → Nat) : lsum (words alph 0) f = f [] := by
  simp [words, lsum]

theorem lsum_words_succ (alph : List α) (n : Nat) (f : List α → Nat) :
    lsum (words alph (n + 1)) f = lsum alph (fun a => lsum (words alph n) (fun w => f (a :: w))) := by
  rw [words, lsum_flatMap]
  exact lsum_congr fun a _ => lsum_map _ _ _

/-- Summing over the words of length `n + 1` by their last letter. -/
theorem lsum_words_snoc (alph : List α) : ∀ (n : Nat) (f : List α → Nat),
    lsum (words alph (n + 1)) f = lsum (words alph n) (fun v => lsum alph (fun c => f (v ++ [c])))
  | 0, f => by
    rw [lsum_words_succ, lsum_words_zero]
    exact lsum_congr fun a _ => lsum_words_zero alph _
  | n + 1, f => by
    rw [lsum_words_succ alph (n + 1), lsum_words_succ alph n]
    exact lsum_congr fun a _ => lsum_words_snoc alph n _

theorem length_of_mem_words (alph : List α) : ∀ (n : Nat) (w : List α), w ∈ words alph n → w.length = n
  | 0, w, h => by simp [words] at h; simp [h]
  | n + 1, w, h => by
    simp only [words, List.mem_flatMap, List.mem_map] at h
    obtain ⟨a, _, v, hv, rfl⟩ := h
    simp [length_of_mem_words alph n v hv]

/-- Over an alphabet that lists each letter once, each word occurs once among the words of its length. -/
theorem lsum_words_eq [DecidableEq α] {alph : List α} (h : Complete alph) :
    ∀ u : List α, lsum (words alph u.length) (fun w => ind (decide (w = u))) = 1
  | [] => by simp [words, lsum, ind]
  | c :: u => by
    rw [List.length_cons, lsum_words_succ]
    have key : ∀ a, lsum (words alph u.length) (fun w => ind (decide (a :: w = c :: u))) =
        ind (decide (a = c)) := by
      intro a
      by_cases hac : a = c
      · subst hac
        rw [show ind (decide (a = a)) = 1 by simp [ind], ← lsum_words_eq h u]
        exact lsum_congr fun w _ => by simp
      · rw [lsum_eq_zero fun w _ => by simp [hac, ind]]
        simp [hac, ind]
    rw [lsum_congr fun a _ => key a]
    exact h c

end Words

/-! ### Window tests along a word -/

section Chains

variable {C : Type}

/-- Every window of three consecutive letters of `a :: b :: u` passes `ok`. -/
def chainOK (ok : C → C → C → Bool) : C → C → List C → Bool
  | _, _, [] => true
  | a, b, c :: u => ok a b c && chainOK ok b c u

/-- The last two letters of `a :: b :: u`. -/
def endPair : C → C → List C → C × C
  | a, b, [] => (a, b)
  | _, b, c :: u => endPair b c u

/-- The last letter of `b :: u`. -/
def lastOf : C → List C → C
  | b, [] => b
  | _, c :: u => lastOf c u

/-- Every cyclic window of three letters of a word passes `ok`: the windows of `c_(W-1), c_0, ..., c_(W-1), c_0`. -/
def cycOK (ok : C → C → C → Bool) : List C → Bool
  | [] => true
  | b :: v => chainOK ok (lastOf b v) b (v ++ [b])

theorem endPair_snoc (c : C) : ∀ (a b : C) (v : List C), endPair a b (v ++ [c]) = (lastOf b v, c)
  | _, _, [] => rfl
  | _, b, e :: v => endPair_snoc c b e v

theorem lastOf_map {D : Type} (f : C → D) : ∀ (b : C) (v : List C), lastOf (f b) (v.map f) = f (lastOf b v)
  | _, [] => rfl
  | _, e :: v => lastOf_map f e v

theorem chainOK_and (ok ok' : C → C → C → Bool) : ∀ (a b : C) (u : List C),
    chainOK (fun a b c => ok a b c && ok' a b c) a b u = (chainOK ok a b u && chainOK ok' a b u)
  | _, _, [] => rfl
  | a, b, c :: u => by
    simp only [chainOK, chainOK_and ok ok' b c u]
    cases ok a b c <;> cases ok' a b c <;> simp

theorem cycOK_and (ok ok' : C → C → C → Bool) (w : List C) :
    cycOK (fun a b c => ok a b c && ok' a b c) w = (cycOK ok w && cycOK ok' w) := by
  cases w with
  | nil => rfl
  | cons b v => exact chainOK_and ok ok' _ _ _

theorem chainOK_map {D : Type} (ok : D → D → D → Bool) (f : C → D) : ∀ (a b : C) (u : List C),
    chainOK (fun a b c => ok (f a) (f b) (f c)) a b u = chainOK ok (f a) (f b) (u.map f)
  | _, _, [] => rfl
  | a, b, c :: u => by simp only [chainOK, List.map_cons, chainOK_map ok f b c u]

theorem cycOK_map {D : Type} (ok : D → D → D → Bool) (f : C → D) (w : List C) :
    cycOK (fun a b c => ok (f a) (f b) (f c)) w = cycOK ok (w.map f) := by
  cases w with
  | nil => rfl
  | cons b v =>
    simp only [cycOK, List.map_cons, chainOK_map, List.map_append, lastOf_map]
    rfl

end Chains

/-! ### Cyclic words are traces of the transfer matrix -/

section Transfer

variable {C : Type} [DecidableEq C]

/-- The transfer matrix on pairs of letters, raised to the power `n`: the number of words `u` of length `n` such that
`a :: b :: u` passes `ok` on every window and ends with `c, d`. -/
def walk (alph : List C) (ok : C → C → C → Bool) : Nat → C → C → C → C → Nat
  | 0, a, b, c, d => ind (decide ((a, b) = (c, d)))
  | n + 1, a, b, c, d => lsum alph fun e => bif ok a b e then walk alph ok n b e c d else 0

theorem cond_eq_ind_mul (b : Bool) (x : Nat) : (bif b then x else 0) = ind b * x := by
  cases b <;> simp [ind]

theorem walk_succ (alph : List C) (ok : C → C → C → Bool) (n : Nat) (a b c d : C) :
    walk alph ok (n + 1) a b c d = lsum alph fun e => ind (ok a b e) * walk alph ok n b e c d :=
  lsum_congr fun _ _ => cond_eq_ind_mul _ _

/-- The trace of the `n`-th power of the transfer matrix. -/
def trace (alph : List C) (ok : C → C → C → Bool) (n : Nat) : Nat :=
  lsum alph fun a => lsum alph fun b => walk alph ok n a b a b

theorem walk_spec (alph : List C) (ok : C → C → C → Bool) : ∀ (n : Nat) (a b c d : C),
    walk alph ok n a b c d =
      lsum (words alph n) (fun u => ind (chainOK ok a b u && decide (endPair a b u = (c, d))))
  | 0, a, b, c, d => by rw [lsum_words_zero]; rfl
  | n + 1, a, b, c, d => by
    rw [walk_succ, lsum_words_succ]
    refine lsum_congr fun e _ => ?_
    rw [walk_spec alph ok n b e c d, ← lsum_mul]
    exact lsum_congr fun u _ => by simp only [chainOK, endPair, Bool.and_assoc, ind_and] <;> rfl

/-- **Cyclic words are closed walks**: the words of length `n + 1` that pass `ok` on every cyclic window number the
trace of the `(n + 1)`-th power of the transfer matrix. -/
theorem cyc_count {alph : List C} (h : Complete alph) (ok : C → C → C → Bool) (n : Nat) :
    lsum (words alph (n + 1)) (fun w => ind (cycOK ok w)) = trace alph ok (n + 1) := by
  unfold trace
  -- the right side, summed by the last letter
  have hr : ∀ a b, walk alph ok (n + 1) a b a b =
      lsum (words alph n) (fun v => lsum alph (fun c =>
        ind (decide (a = lastOf b v)) * (ind (decide (c = b)) * ind (chainOK ok (lastOf b v) b (v ++ [b]))))) := by
    intro a b
    rw [walk_spec, lsum_words_snoc]
    refine lsum_congr fun v _ => lsum_congr fun c _ => ?_
    rw [endPair_snoc]
    by_cases h1 : a = lastOf b v
    · by_cases h2 : c = b
      · subst h1; subst h2; simp [ind]
      · simp [h2, ind]
    · have : ¬ (lastOf b v, c) = (a, b) := fun e => h1 (congrArg Prod.fst e).symm
      simp [h1, this, ind]
  rw [lsum_congr fun a _ => lsum_congr fun b _ => hr a b, lsum_comm, lsum_words_succ]
  refine lsum_congr fun b _ => ?_
  rw [lsum_comm]
  refine lsum_congr fun v _ => ?_
  have e1 : ∀ a, lsum alph (fun c => ind (decide (a = lastOf b v)) *
      (ind (decide (c = b)) * ind (chainOK ok (lastOf b v) b (v ++ [b])))) =
      ind (decide (a = lastOf b v)) * ind (chainOK ok (lastOf b v) b (v ++ [b])) := by
    intro a
    rw [lsum_mul, lsum_pick_const b (h b)]
  rw [lsum_congr fun a _ => e1 a, lsum_pick_const _ (h _)]
  rfl

/-- **The transfer matrix multiplies**: `walk (n + k) = walk n * walk k`. -/
theorem walk_add {alph : List C} (h : Complete alph) (ok : C → C → C → Bool) (k : Nat) : ∀ (n : Nat) (a b c d : C),
    walk alph ok (n + k) a b c d =
      lsum alph (fun e => lsum alph (fun f => walk alph ok n a b e f * walk alph ok k e f c d))
  | 0, a, b, c, d => by
    rw [Nat.zero_add]
    have e1 : ∀ e, lsum alph (fun f => walk alph ok 0 a b e f * walk alph ok k e f c d) =
        ind (decide (e = a)) * walk alph ok k e b c d := by
      intro e
      have : ∀ f, walk alph ok 0 a b e f * walk alph ok k e f c d =
          ind (decide (e = a)) * (ind (decide (f = b)) * walk alph ok k e f c d) := by
        intro f
        show ind (decide ((a, b) = (e, f))) * _ = _
        by_cases h1 : e = a
        · by_cases h2 : f = b
          · subst h1; subst h2; simp [ind]
          · have : ¬ (a, b) = (e, f) := fun q => h2 (congrArg Prod.snd q).symm
            simp [h2, this, ind]
        · have : ¬ (a, b) = (e, f) := fun q => h1 (congrArg Prod.fst q).symm
          simp [h1, this, ind]
      rw [lsum_congr fun f _ => this f, lsum_mul, lsum_pick b (h b)]
    rw [lsum_congr fun e _ => e1 e, lsum_pick a (h a)]
  | n + 1, a, b, c, d => by
    rw [show n + 1 + k = (n + k) + 1 by omega, walk_succ]
    -- left: ∑_g [ok a b g] ∑_e ∑_f walk n b g e f * walk k e f c d
    have hl : ∀ g, ind (ok a b g) * walk alph ok (n + k) b g c d =
        lsum alph (fun e => lsum alph (fun f =>
          ind (ok a b g) * (walk alph ok n b g e f * walk alph ok k e f c d))) := by
      intro g
      rw [walk_add h ok k n b g c d, ← lsum_mul]
      exact lsum_congr fun e _ => (lsum_mul _ _ _).symm
    rw [lsum_congr fun g _ => hl g, lsum_comm]
    refine lsum_congr fun e _ => ?_
    rw [lsum_comm]
    refine lsum_congr fun f _ => ?_
    rw [walk_succ, ← lsum_mul_right]
    exact lsum_congr fun g _ => (Nat.mul_assoc _ _ _).symm

/-- `α_0 g(k) + α_1 g(k + 1) + ...` for the coefficients `α = [α_0, α_1, ...]`. -/
def comb : List Nat → (Nat → Nat) → Nat → Nat
  | [], _, _ => 0
  | a :: cs, g, k => a * g k + comb cs g (k + 1)

theorem comb_lsum {β : Type} (L : List β) (H : β → Nat) (F : Nat → β → Nat) : ∀ (cs : List Nat) (k : Nat),
    comb cs (fun m => lsum L (fun s => H s * F m s)) k = lsum L (fun s => H s * comb cs (fun m => F m s) k)
  | [], k => (lsum_eq_zero fun s _ => Nat.mul_zero _).symm
  | a :: cs, k => by
    simp only [comb]
    rw [comb_lsum L H F cs (k + 1), ← lsum_mul, ← lsum_add]
    refine lsum_congr fun s _ => ?_
    rw [Nat.mul_add, Nat.mul_left_comm]

theorem comb_lsum_one {β : Type} (L : List β) (F : Nat → β → Nat) (cs : List Nat) (k : Nat) :
    comb cs (fun m => lsum L (fun s => F m s)) k = lsum L (fun s => comb cs (fun m => F m s) k) := by
  have h1 := comb_lsum L (fun _ => 1) F cs k
  simp only [Nat.one_mul] at h1
  exact h1

/-- **A relation among powers holds at every shift.** If `∑ α_i walk (k + i) = ∑ β_i walk (k + i)` on every entry,
then the traces satisfy the same relation from every `n` on. -/
theorem trace_rec {alph : List C} (h : Complete alph) (ok : C → C → C → Bool) (α β : List Nat) (k : Nat)
    (hrec : ∀ e ∈ alph, ∀ f ∈ alph, ∀ c ∈ alph, ∀ d ∈ alph,
      comb α (fun m => walk alph ok m e f c d) k = comb β (fun m => walk alph ok m e f c d) k) (n : Nat) :
    comb α (fun m => trace alph ok (n + m)) k = comb β (fun m => trace alph ok (n + m)) k := by
  have hw : ∀ (γ : List Nat) (a b : C), comb γ (fun m => walk alph ok (n + m) a b a b) k =
      lsum alph (fun e => lsum alph (fun f => walk alph ok n a b e f * comb γ (fun m => walk alph ok m e f a b) k)) := by
    intro γ a b
    have : (fun m => walk alph ok (n + m) a b a b) =
        fun m => lsum alph (fun e => lsum alph (fun f => walk alph ok n a b e f * walk alph ok m e f a b)) :=
      funext fun m => walk_add h ok m n a b a b
    rw [this, comb_lsum_one]
    exact lsum_congr fun e _ => comb_lsum alph _ _ γ k
  have ht : ∀ γ : List Nat, comb γ (fun m => trace alph ok (n + m)) k =
      lsum alph (fun a => lsum alph (fun b => comb γ (fun m => walk alph ok (n + m) a b a b) k)) := by
    intro γ
    unfold trace
    rw [comb_lsum_one]
    exact lsum_congr fun a _ => comb_lsum_one alph _ γ k
  rw [ht, ht]
  refine lsum_congr fun a ha => lsum_congr fun b hb => ?_
  rw [hw, hw]
  exact lsum_congr fun e he => lsum_congr fun f hf => by rw [hrec e he f hf a ha b hb]

end Transfer

/-! ### Rule 30 on a ring -/

/-- The two values of a cell. -/
def boolAlph : List Bool := [false, true]

/-- All `2^W` rows of a ring of `W` cells (`rows_length`), each once (`rows_count`). -/
def rows (W : Nat) : List (List Bool) := words boolAlph W

/-- The letters `(a, b)` with `a` from `A` and `b` from `B`. -/
def pairAlph {α β : Type} (A : List α) (B : List β) : List (α × β) := A.flatMap fun a => B.map fun b => (a, b)

theorem lsum_pairAlph {α β : Type} (A : List α) (B : List β) (f : α × β → Nat) :
    lsum (pairAlph A B) f = lsum A (fun a => lsum B (fun b => f (a, b))) := by
  rw [pairAlph, lsum_flatMap]
  exact lsum_congr fun a _ => lsum_map _ _ _

theorem complete_bool : Complete boolAlph := by
  intro x; cases x <;> decide

theorem rows_count (u : List Bool) : lsum (rows u.length) (fun w => ind (decide (w = u))) = 1 :=
  lsum_words_eq complete_bool u

theorem length_of_mem_rows {W : Nat} {x : List Bool} (h : x ∈ rows W) : x.length = W :=
  length_of_mem_words boolAlph W x h

theorem lsum_const {α : Type} (l : List α) (k : Nat) : lsum l (fun _ => k) = l.length * k := by
  induction l with
  | nil => simp [lsum]
  | cons a l ih => simp only [lsum, ih, List.length_cons, Nat.succ_mul]; omega

theorem length_words {α : Type} (alph : List α) : ∀ n : Nat, (words alph n).length = alph.length ^ n
  | 0 => rfl
  | n + 1 => by
    have h1 := lsum_const (words alph (n + 1)) 1
    rw [lsum_words_succ, lsum_congr fun a _ => lsum_const (words alph n) 1, lsum_const,
      length_words alph n] at h1
    rw [Nat.pow_succ]
    simp only [Nat.mul_one] at h1
    rw [← h1, Nat.mul_comm]

theorem rows_length (W : Nat) : (rows W).length = 2 ^ W := length_words boolAlph W

/-- Rule 30 on the windows of `a :: b :: u`. -/
def stepChain : Bool → Bool → List Bool → List Bool
  | _, _, [] => []
  | a, b, c :: u => rule30 a b c :: stepChain b c u

/-- One step of Rule 30 on a ring: cell `i` of the image is `rule30` of the cells `i - 1`, `i` and `i + 1`, with cell
`W - 1` beside cell `0` (`ringStep_getD`). -/
def ringStep : List Bool → List Bool
  | [] => []
  | b :: v => stepChain (lastOf b v) b (v ++ [b])

/-- The number of preimages of the row `z` among the rows of `W` cells. -/
def preimages (W : Nat) (z : List Bool) : Nat := (rows W).countP fun x => decide (ringStep x = z)

/-- The number of rows of `W` cells with no preimage. -/
def missed (W : Nat) : Nat := (rows W).countP fun z => decide (preimages W z = 0)

/-- `p_W`, the sum of the `W`-th powers of the three roots of `x^3 - x^2 - 2`. -/
def powerSum : Nat → Nat
  | 0 => 3
  | 1 => 1
  | 2 => 1
  | n + 3 => powerSum (n + 2) + 2 * powerSum n

theorem length_stepChain : ∀ (a b : Bool) (u : List Bool), (stepChain a b u).length = u.length
  | _, _, [] => rfl
  | _, b, c :: u => by simp [stepChain, length_stepChain b c u]

theorem length_ringStep (x : List Bool) : (ringStep x).length = x.length := by
  cases x with
  | nil => rfl
  | cons b v => simp [ringStep, length_stepChain]

theorem stepChain_getD : ∀ (a b : Bool) (u : List Bool) (j : Nat), j < u.length →
    (stepChain a b u).getD j false =
      rule30 ((a :: b :: u).getD j false) ((a :: b :: u).getD (j + 1) false) ((a :: b :: u).getD (j + 2) false)
  | _, _, [], j, h => absurd h (by simp)
  | a, b, c :: u, 0, _ => rfl
  | a, b, c :: u, j + 1, h => by
    have := stepChain_getD b c u j (by simp at h; omega)
    simpa [stepChain] using this

theorem lastOf_eq_getD : ∀ (b : Bool) (v : List Bool), lastOf b v = (b :: v).getD v.length false
  | _, [] => rfl
  | _, e :: v => by rw [lastOf, lastOf_eq_getD e v]; simp

theorem getD_app_left {l m : List Bool} {i : Nat} (h : i < l.length) : (l ++ m).getD i false = l.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_app_last (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

/-- `ringStep` is one step of Rule 30 on a ring of `W` cells. -/
theorem ringStep_getD (x : List Bool) (i : Nat) (hi : i < x.length) :
    (ringStep x).getD i false = rule30 (x.getD ((i + x.length - 1) % x.length) false) (x.getD i false)
      (x.getD ((i + 1) % x.length) false) := by
  cases x with
  | nil => simp at hi
  | cons b v =>
    simp only [List.length_cons] at hi ⊢
    rw [ringStep, stepChain_getD _ _ _ _ (by simp; omega)]
    have hmid : (lastOf b v :: b :: (v ++ [b])).getD (i + 1) false = (b :: v).getD i false := by
      have : b :: (v ++ [b]) = (b :: v) ++ [b] := rfl
      rw [List.getD_cons_succ, this, getD_app_left hi]
    rw [hmid]
    congr 1
    · rcases Nat.eq_zero_or_pos i with rfl | hpos
      · rw [show (0 + (v.length + 1) - 1) % (v.length + 1) = v.length by
          rw [Nat.mod_eq_of_lt (by omega)]; omega]
        rw [lastOf_eq_getD]; rfl
      · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
        rw [show (j + 1 + (v.length + 1) - 1) % (v.length + 1) = j by
          rw [show j + 1 + (v.length + 1) - 1 = j + (v.length + 1) by omega, Nat.add_mod_right,
            Nat.mod_eq_of_lt (by omega)]]
        have : b :: (v ++ [b]) = (b :: v) ++ [b] := rfl
        rw [List.getD_cons_succ, this, getD_app_left (by simp; omega)]
    · have : b :: (v ++ [b]) = (b :: v) ++ [b] := rfl
      rw [List.getD_cons_succ, this]
      rcases Nat.lt_or_ge (i + 1) (v.length + 1) with h1 | h1
      · rw [getD_app_left (by simpa using h1), Nat.mod_eq_of_lt h1]
      · have h2 : i + 1 = v.length + 1 := by omega
        rw [h2, Nat.mod_self, show v.length + 1 = (b :: v).length from rfl, getD_app_last]
        rfl

/-! ### Pairs of rows with one image -/

/-- Rule 30 gives the two rows of a pair the same cell over the window `a, b, c`. -/
def okE (a b c : Bool × Bool) : Bool := decide (rule30 a.1 b.1 c.1 = rule30 a.2 b.2 c.2)

/-- The two rows agree on this cell. -/
def diag (p : Bool × Bool) : Bool := decide (p.1 = p.2)

/-- The two rows do not agree on both of the cells `b, c`. -/
def okD (_a b c : Bool × Bool) : Bool := !(diag b && diag c)

/-- The window test for ordered pairs of distinct rows with one image. -/
def okP (a b c : Bool × Bool) : Bool := okE a b c && okD a b c

/-- The four letters of a pair of rows. -/
def alph2 : List (Bool × Bool) := pairAlph boolAlph boolAlph

theorem complete2 : Complete alph2 := by
  intro ⟨a, b⟩; cases a <;> cases b <;> decide

theorem stepChain_pair : ∀ (a b : Bool × Bool) (u : List (Bool × Bool)),
    stepChain a.1 b.1 (u.map Prod.fst) = stepChain a.2 b.2 (u.map Prod.snd) ↔ chainOK okE a b u = true
  | _, _, [] => by simp [stepChain, chainOK]
  | a, b, c :: u => by
    simp only [stepChain, List.map_cons, chainOK, List.cons.injEq, stepChain_pair b c u, Bool.and_eq_true, okE,
      decide_eq_true_eq]

theorem ringStep_pair (b : Bool × Bool) (v : List (Bool × Bool)) :
    ringStep ((b :: v).map Prod.fst) = ringStep ((b :: v).map Prod.snd) ↔
      chainOK okE (lastOf b v) b (v ++ [b]) = true := by
  have h := stepChain_pair (lastOf b v) b (v ++ [b])
  simp only [List.map_append, List.map_cons, List.map_nil] at h
  simp only [List.map_cons, ringStep, lastOf_map]
  exact h

/-- Left permutivity on a pair of rows: rows with one image that agree on `b` and `c` agree on `a`. -/
theorem diag_left {a b c : Bool × Bool} (h : okE a b c = true) (hb : diag b = true) (hc : diag c = true) :
    diag a = true := by
  revert h hb hc
  obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b; obtain ⟨c1, c2⟩ := c
  cases a1 <;> cases a2 <;> cases b1 <;> cases b2 <;> cases c1 <;> cases c2 <;> decide

/-- Agreement on the last two cells of a chain with one image spreads to every cell. -/
theorem diag_back : ∀ (a b : Bool × Bool) (u : List (Bool × Bool)), chainOK okE a b u = true →
    diag (endPair a b u).1 = true → diag (endPair a b u).2 = true →
      diag a = true ∧ diag b = true ∧ ∀ e ∈ u, diag e = true
  | _, _, [], _, h1, h2 => ⟨h1, h2, by simp⟩
  | a, b, c :: u, h, h1, h2 => by
    simp only [chainOK, Bool.and_eq_true] at h
    obtain ⟨hb, hc, hu⟩ := diag_back b c u h.2 h1 h2
    refine ⟨diag_left h.1 hb hc, hb, ?_⟩
    intro e he
    simp only [List.mem_cons] at he
    rcases he with rfl | he
    · exact hc
    · exact hu e he

/-- A chain with one image that fails `okD` somewhere agrees on its first two cells. -/
theorem diag_front : ∀ (a b : Bool × Bool) (u : List (Bool × Bool)), chainOK okE a b u = true →
    chainOK okD a b u = false → diag a = true ∧ diag b = true
  | _, _, [], _, h => by simp [chainOK] at h
  | a, b, c :: u, h, hd => by
    simp only [chainOK, Bool.and_eq_true] at h
    simp only [chainOK, Bool.and_eq_false_iff] at hd
    rcases hd with hd | hd
    · simp only [okD, Bool.not_eq_false', Bool.and_eq_true] at hd
      exact ⟨diag_left h.1 hd.1 hd.2, hd.1⟩
    · have := diag_front b c u h.2 hd
      exact ⟨diag_left h.1 this.1 this.2, this.1⟩

theorem map_fst_eq_snd_iff : ∀ w : List (Bool × Bool), w.map Prod.fst = w.map Prod.snd ↔ ∀ e ∈ w, diag e = true
  | [] => by simp
  | e :: w => by
    simp only [List.map_cons, List.cons.injEq, map_fst_eq_snd_iff w, List.mem_cons, forall_eq_or_imp, diag,
      decide_eq_true_eq]

/-- **Pairs with one image are cyclic words**: a word over the letters `(x_i, y_i)` passes `okP` on every cyclic window
exactly when the rows `x ≠ y` have the same image. -/
theorem pair_collision_iff (b : Bool × Bool) (v : List (Bool × Bool)) :
    cycOK okP (b :: v) = true ↔
      ((b :: v).map Prod.fst ≠ (b :: v).map Prod.snd ∧
        ringStep ((b :: v).map Prod.fst) = ringStep ((b :: v).map Prod.snd)) := by
  have hsplit : cycOK okP (b :: v) =
      (chainOK okE (lastOf b v) b (v ++ [b]) && chainOK okD (lastOf b v) b (v ++ [b])) :=
    chainOK_and okE okD _ _ _
  rw [hsplit, Bool.and_eq_true, ringStep_pair]
  constructor
  · rintro ⟨he, hd⟩
    refine ⟨fun heq => ?_, he⟩
    have hall := (map_fst_eq_snd_iff _).1 heq
    obtain ⟨c, rest, hc, hcr⟩ : ∃ c rest, c ∈ b :: v ∧ v ++ [b] = c :: rest := by
      cases v with
      | nil => exact ⟨b, [], by simp, rfl⟩
      | cons e v => exact ⟨e, v ++ [b], by simp, rfl⟩
    rw [hcr] at hd
    simp [chainOK, okD, hall b (by simp), hall c hc] at hd
  · rintro ⟨hne, he⟩
    refine ⟨he, ?_⟩
    cases hd : chainOK okD (lastOf b v) b (v ++ [b])
    · exfalso
      obtain ⟨h1, h2⟩ := diag_front _ _ _ he hd
      have hend := endPair_snoc b (lastOf b v) b v
      obtain ⟨_, hb, hu⟩ := diag_back _ _ _ he (by rw [hend]; exact h1) (by rw [hend]; exact h2)
      apply hne
      rw [map_fst_eq_snd_iff]
      intro e he'
      simp only [List.mem_cons] at he'
      rcases he' with rfl | he'
      · exact h2
      · exact hu e (by simp [he'])
    · rfl

/-! ### Triples of rows with one image -/

/-- The first and second rows of a triple. -/
def p12 (t : Bool × (Bool × Bool)) : Bool × Bool := (t.1, t.2.1)

/-- The first and third rows of a triple. -/
def p13 (t : Bool × (Bool × Bool)) : Bool × Bool := (t.1, t.2.2)

/-- The second and third rows of a triple. -/
def p23 (t : Bool × (Bool × Bool)) : Bool × Bool := (t.2.1, t.2.2)

/-- The window test for ordered triples of pairwise distinct rows with one image: `okP` on each of the three pairs. -/
def okT (a b c : Bool × (Bool × Bool)) : Bool :=
  okP (p12 a) (p12 b) (p12 c) && (okP (p13 a) (p13 b) (p13 c) && okP (p23 a) (p23 b) (p23 c))

/-- The eight letters of a triple of rows. -/
def alph3 : List (Bool × (Bool × Bool)) := pairAlph boolAlph alph2

theorem complete3 : Complete alph3 := by
  intro ⟨a, b, c⟩; cases a <;> cases b <;> cases c <;> decide

theorem cycOK_okT (w : List (Bool × (Bool × Bool))) :
    cycOK okT w = (cycOK okP (w.map p12) && (cycOK okP (w.map p13) && cycOK okP (w.map p23))) := by
  have h1 := cycOK_and (fun a b c => okP (p12 a) (p12 b) (p12 c))
    (fun a b c => okP (p13 a) (p13 b) (p13 c) && okP (p23 a) (p23 b) (p23 c)) w
  have h2 := cycOK_and (fun a b c => okP (p13 a) (p13 b) (p13 c)) (fun a b c => okP (p23 a) (p23 b) (p23 c)) w
  have e12 : cycOK (fun a b c => okP (p12 a) (p12 b) (p12 c)) w = cycOK okP (w.map p12) := cycOK_map okP p12 w
  have e13 : cycOK (fun a b c => okP (p13 a) (p13 b) (p13 c)) w = cycOK okP (w.map p13) := cycOK_map okP p13 w
  have e23 : cycOK (fun a b c => okP (p23 a) (p23 b) (p23 c)) w = cycOK okP (w.map p23) := cycOK_map okP p23 w
  rw [h2, e12, e13, e23] at h1
  exact h1

/-! ### Summing over pairs and triples of rows -/

/-- Summing over pairs of words is summing over words of pairs. -/
theorem lsum_words_pair {α β : Type} (A : List α) (B : List β) : ∀ (n : Nat) (F : List α → List β → Nat),
    lsum (words A n) (fun x => lsum (words B n) (fun y => F x y)) =
      lsum (words (pairAlph A B) n) (fun w => F (w.map Prod.fst) (w.map Prod.snd))
  | 0, F => by simp [lsum_words_zero]
  | n + 1, F => by
    rw [lsum_words_succ A n, lsum_words_succ (pairAlph A B) n, lsum_pairAlph]
    refine lsum_congr fun a _ => ?_
    rw [lsum_congr fun x _ => lsum_words_succ B n (fun y => F (a :: x) y), lsum_comm]
    exact lsum_congr fun b _ => lsum_words_pair A B n (fun x y => F (a :: x) (b :: y))

/-- `x ≠ y` and the two rows have one image. -/
def pairC (x y : List Bool) : Bool := !decide (x = y) && decide (ringStep x = ringStep y)

/-- `x`, `y`, `u` are pairwise distinct and have one image. -/
def tripC (x y u : List Bool) : Bool := pairC x y && (pairC x u && pairC y u)

theorem pairC_true (x y : List Bool) : pairC x y = true ↔ (x ≠ y ∧ ringStep x = ringStep y) := by
  simp [pairC]

theorem cycOK_okP_eq (b : Bool × Bool) (v : List (Bool × Bool)) :
    cycOK okP (b :: v) = pairC ((b :: v).map Prod.fst) ((b :: v).map Prod.snd) := by
  rw [Bool.eq_iff_iff, pair_collision_iff, pairC_true]

theorem cycOK_okP_eq' (w : List (Bool × Bool)) (hw : w ≠ []) :
    cycOK okP w = pairC (w.map Prod.fst) (w.map Prod.snd) := by
  cases w with
  | nil => exact absurd rfl hw
  | cons b v => exact cycOK_okP_eq b v

/-- The ordered pairs of distinct rows with one image number the trace of the pair transfer matrix. -/
theorem pairs_eq_trace (n : Nat) :
    lsum (rows (n + 1)) (fun x => lsum (rows (n + 1)) (fun y => ind (pairC x y))) = trace alph2 okP (n + 1) := by
  rw [← cyc_count complete2, rows, lsum_words_pair]
  refine lsum_congr fun w hw => ?_
  have hlen := length_of_mem_words _ _ _ hw
  rw [cycOK_okP_eq' w (by intro h; simp [h] at hlen)]

/-- The ordered triples of pairwise distinct rows with one image number the trace of the triple transfer matrix. -/
theorem triples_eq_trace (n : Nat) :
    lsum (rows (n + 1)) (fun x => lsum (rows (n + 1)) (fun y => lsum (rows (n + 1)) (fun u => ind (tripC x y u)))) =
      trace alph3 okT (n + 1) := by
  rw [← cyc_count complete3, rows]
  rw [lsum_congr fun x _ => lsum_words_pair boolAlph boolAlph (n + 1) (fun y u => ind (tripC x y u))]
  rw [show pairAlph boolAlph boolAlph = alph2 from rfl, lsum_words_pair boolAlph alph2 (n + 1),
    show pairAlph boolAlph alph2 = alph3 from rfl]
  refine lsum_congr fun w hw => ?_
  have hlen := length_of_mem_words _ _ _ hw
  have hne : ∀ f : Bool × (Bool × Bool) → Bool × Bool, w.map f ≠ [] := by
    intro f h; rw [List.map_eq_nil_iff] at h; subst h; simp at hlen
  rw [cycOK_okT, cycOK_okP_eq' _ (hne _), cycOK_okP_eq' _ (hne _), cycOK_okP_eq' _ (hne _)]
  simp only [List.map_map]
  rfl

/-! ### The traces -/

theorem recP : ∀ e ∈ alph2, ∀ f ∈ alph2, ∀ c ∈ alph2, ∀ d ∈ alph2,
    comb [2, 0, 1, 0, 1] (fun m => walk alph2 okP m e f c d) 2 = comb [0, 2, 0, 2] (fun m => walk alph2 okP m e f c d) 2 := by
  decide +kernel

theorem recT : ∀ e ∈ alph3, ∀ f ∈ alph3, ∀ c ∈ alph3, ∀ d ∈ alph3,
    comb [0, 0, 0, 1] (fun m => walk alph3 okT m e f c d) 2 = comb [1] (fun m => walk alph3 okT m e f c d) 2 := by
  decide +kernel

/-- **The pair trace**: the ordered pairs of distinct rows of `W` cells with one image number `p_W + 1`. -/
theorem pairTrace_eq : ∀ W : Nat, 1 ≤ W → trace alph2 okP W = powerSum W + 1
  | 0, h => absurd h (by decide)
  | 1, _ => by decide +kernel
  | 2, _ => by decide +kernel
  | 3, _ => by decide +kernel
  | 4, _ => by decide +kernel
  | 5, _ => by decide +kernel
  | n + 6, _ => by
    have r := trace_rec complete2 okP [2, 0, 1, 0, 1] [0, 2, 0, 2] 2 recP n
    simp only [comb, Nat.reduceAdd, Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add] at r
    have h2 := pairTrace_eq (n + 2) (by omega)
    have h3 := pairTrace_eq (n + 3) (by omega)
    have h4 := pairTrace_eq (n + 4) (by omega)
    have h5 := pairTrace_eq (n + 5) (by omega)
    have p6 : powerSum (n + 6) = powerSum (n + 5) + 2 * powerSum (n + 3) := rfl
    have p5 : powerSum (n + 5) = powerSum (n + 4) + 2 * powerSum (n + 2) := rfl
    rw [show n + 2 + 4 = n + 6 by omega] at r
    omega

/-- **The triple trace**: the ordered triples of pairwise distinct rows of `W` cells with one image number `6` when
`3 ∣ W` and `0` otherwise. -/
theorem tripleTrace_eq : ∀ W : Nat, 1 ≤ W → trace alph3 okT W = if W % 3 = 0 then 6 else 0
  | 0, h => absurd h (by decide)
  | 1, _ => by decide +kernel
  | 2, _ => by decide +kernel
  | 3, _ => by decide +kernel
  | 4, _ => by decide +kernel
  | n + 5, _ => by
    have r := trace_rec complete3 okT [0, 0, 0, 1] [1] 2 recT n
    simp only [comb, Nat.reduceAdd, Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add] at r
    have h2 := tripleTrace_eq (n + 2) (by omega)
    rw [show n + 2 + 3 = n + 5 by omega] at r
    rw [r, h2]
    have : (n + 5) % 3 = (n + 2) % 3 := by omega
    rw [this]

/-! ### Counting rows by their numbers of preimages -/

section Counting

variable {W : Nat}

theorem preimages_eq (W : Nat) (z : List Bool) :
    preimages W z = lsum (rows W) (fun x => ind (decide (ringStep x = z))) :=
  countP_eq_lsum _ _

theorem decide_eq_symm {α : Type} [DecidableEq α] (a b : α) : decide (a = b) = decide (b = a) := by
  by_cases h : a = b
  · subst h; rfl
  · simp [h, Ne.symm h]

theorem rows_count' {x : List Bool} (hx : x ∈ rows W) : lsum (rows W) (fun y => ind (decide (y = x))) = 1 := by
  have h := rows_count x
  rwa [length_of_mem_rows hx] at h

/-- Each row has exactly one image among the rows. -/
theorem sum_image_one {x : List Bool} (hx : x ∈ rows W) :
    lsum (rows W) (fun z => ind (decide (ringStep x = z))) = 1 := by
  have h := rows_count (ringStep x)
  rw [length_ringStep, length_of_mem_rows hx] at h
  rw [← h]
  exact lsum_congr fun z _ => by rw [decide_eq_symm]

/-- The preimages of all rows add up to the number of rows. -/
theorem sum_preimages : lsum (rows W) (fun z => preimages W z) = lsum (rows W) (fun _ => 1) := by
  rw [lsum_congr fun z _ => preimages_eq W z, lsum_comm]
  exact lsum_congr fun x hx => sum_image_one hx

/-- The rows other than `x` that map to `z`. -/
theorem count_minus_one (z : List Bool) {x : List Bool} (hx : x ∈ rows W) :
    lsum (rows W) (fun y => ind (!decide (x = y) && decide (ringStep y = z))) + ind (decide (ringStep x = z)) =
      preimages W z := by
  rw [preimages_eq, ← lsum_pick_const x (rows_count' hx) (ind (decide (ringStep x = z))), ← lsum_add]
  refine lsum_congr fun y _ => ?_
  by_cases hy : y = x
  · subst hy; simp [ind]
  · have : ¬ x = y := fun h => hy h.symm
    simp [hy, this, ind]

/-- The rows other than `x` and `y` that map to `z`. -/
theorem count_minus_two (z : List Bool) {x y : List Bool} (hx : x ∈ rows W) (hy : y ∈ rows W) (hxy : x ≠ y) :
    lsum (rows W) (fun u => ind (!decide (x = u) && (!decide (y = u) && decide (ringStep u = z)))) +
      ind (decide (ringStep x = z)) + ind (decide (ringStep y = z)) = preimages W z := by
  rw [preimages_eq, ← lsum_pick_const x (rows_count' hx) (ind (decide (ringStep x = z))),
    ← lsum_pick_const y (rows_count' hy) (ind (decide (ringStep y = z))), ← lsum_add, ← lsum_add]
  refine lsum_congr fun u _ => ?_
  by_cases hux : u = x
  · subst hux
    have : ¬ u = y := hxy
    have : ¬ y = u := fun h => hxy h.symm
    simp [this, hxy, ind]
  · by_cases huy : u = y
    · subst huy
      have : ¬ x = u := hxy
      simp [hux, this, ind]
    · have h1 : ¬ x = u := fun h => hux h.symm
      have h2 : ¬ y = u := fun h => huy h.symm
      simp [hux, huy, h1, h2, ind]

theorem pair_row (z : List Bool) {x : List Bool} (hx : x ∈ rows W) :
    lsum (rows W) (fun y => ind (pairC x y && decide (ringStep x = z))) =
      ind (decide (ringStep x = z)) * (preimages W z - 1) := by
  by_cases hz : ringStep x = z
  · have h := count_minus_one z hx
    rw [show ind (decide (ringStep x = z)) = 1 by simp [hz, ind]] at h ⊢
    rw [Nat.one_mul, ← h, Nat.add_sub_cancel]
    refine lsum_congr fun y _ => ?_
    simp only [pairC, hz, decide_true, Bool.and_true]
    rw [decide_eq_symm z]
  · rw [lsum_eq_zero fun y _ => by simp [hz, ind]]
    simp [hz, ind]

theorem pairs_at (z : List Bool) :
    lsum (rows W) (fun x => lsum (rows W) (fun y => ind (pairC x y && decide (ringStep x = z)))) =
      preimages W z * (preimages W z - 1) := by
  rw [lsum_congr fun x hx => pair_row z hx, lsum_mul_right, ← preimages_eq]

/-- **Ordered pairs**: `∑_z c(z) (c(z) - 1)` counts the ordered pairs of distinct rows with one image. -/
theorem pairs_total :
    lsum (rows W) (fun z => preimages W z * (preimages W z - 1)) =
      lsum (rows W) (fun x => lsum (rows W) (fun y => ind (pairC x y))) := by
  rw [← lsum_congr fun z _ => pairs_at (W := W) z, lsum_comm]
  refine lsum_congr fun x hx => ?_
  rw [lsum_comm]
  refine lsum_congr fun y _ => ?_
  rw [lsum_congr fun z _ => ind_and _ _, lsum_mul, sum_image_one hx, Nat.mul_one]

theorem triple_row (z : List Bool) {x y : List Bool} (hx : x ∈ rows W) (hy : y ∈ rows W) :
    lsum (rows W) (fun u => ind (tripC x y u && decide (ringStep x = z))) =
      ind (pairC x y && decide (ringStep x = z)) * (preimages W z - 2) := by
  by_cases hp : (pairC x y && decide (ringStep x = z)) = true
  · simp only [Bool.and_eq_true, pairC_true, decide_eq_true_eq] at hp
    obtain ⟨⟨hxy, hxy'⟩, hz⟩ := hp
    have h := count_minus_two z hx hy hxy
    have e1 : ind (decide (ringStep x = z)) = 1 := by simp [hz, ind]
    have e2 : ind (decide (ringStep y = z)) = 1 := by simp [← hxy', hz, ind]
    have e3 : ind (pairC x y && decide (ringStep x = z)) = 1 := by
      have : pairC x y = true := (pairC_true x y).2 ⟨hxy, hxy'⟩
      simp [this, hz, ind]
    rw [e1, e2] at h
    rw [e3, Nat.one_mul, ← h, Nat.add_assoc, Nat.add_sub_cancel]
    refine lsum_congr fun u _ => ?_
    have hpxy : pairC x y = true := (pairC_true x y).2 ⟨hxy, hxy'⟩
    have hyz : ringStep y = z := hxy'.symm.trans hz
    unfold tripC
    rw [hpxy]
    unfold pairC
    rw [hz, hyz, decide_eq_symm z (ringStep u)]
    cases decide (x = u) <;> cases decide (y = u) <;> cases decide (ringStep u = z) <;> simp
  · have hp' : (pairC x y && decide (ringStep x = z)) = false := by simpa using hp
    rw [hp', lsum_eq_zero fun u _ => ?_]
    · simp [ind]
    · simp only [tripC] at *
      revert hp'
      cases pairC x y <;> cases decide (ringStep x = z) <;> simp [ind]

theorem triples_at (z : List Bool) :
    lsum (rows W) (fun x => lsum (rows W) (fun y => lsum (rows W) (fun u =>
      ind (tripC x y u && decide (ringStep x = z))))) =
      preimages W z * (preimages W z - 1) * (preimages W z - 2) := by
  rw [lsum_congr fun x hx => lsum_congr fun y hy => triple_row z hx hy]
  rw [lsum_congr fun x _ => lsum_mul_right _ _ _, lsum_mul_right, pairs_at]

/-- **Ordered triples**: `∑_z c(z) (c(z) - 1) (c(z) - 2)` counts the ordered triples of pairwise distinct rows with one
image. -/
theorem triples_total :
    lsum (rows W) (fun z => preimages W z * (preimages W z - 1) * (preimages W z - 2)) =
      lsum (rows W) (fun x => lsum (rows W) (fun y => lsum (rows W) (fun u => ind (tripC x y u)))) := by
  rw [← lsum_congr fun z _ => triples_at (W := W) z, lsum_comm]
  refine lsum_congr fun x hx => ?_
  rw [lsum_comm]
  refine lsum_congr fun y _ => ?_
  rw [lsum_comm]
  refine lsum_congr fun u _ => ?_
  rw [lsum_congr fun z _ => ind_and _ _, lsum_mul, sum_image_one hx, Nat.mul_one]

/-! ### At most three preimages -/

/-- The two cells of a row that meet across the seam of the ring: cell `W - 1` and cell `0`. -/
def seam : List Bool → Bool × Bool
  | [] => (false, false)
  | b :: v => (lastOf b v, b)

theorem stepChain_inj : ∀ (u u' : List Bool) (a b a' b' : Bool), u.length = u'.length →
    stepChain a b u = stepChain a' b' u' → endPair a b u = endPair a' b' u' → a = a' ∧ b = b' ∧ u = u'
  | [], [], _, _, _, _, _, _, he => by
    simp only [endPair, Prod.mk.injEq] at he
    exact ⟨he.1, he.2, rfl⟩
  | [], _ :: _, _, _, _, _, hl, _, _ => by simp at hl
  | _ :: _, [], _, _, _, _, hl, _, _ => by simp at hl
  | c :: u, c' :: u', a, b, a', b', hl, hs, he => by
    simp only [stepChain, List.cons.injEq] at hs
    simp only [endPair] at he
    obtain ⟨hb, hc, hu⟩ := stepChain_inj u u' b c b' c' (by simpa using hl) hs.2 he
    subst hb; subst hc; subst hu
    refine ⟨?_, rfl, rfl⟩
    have h := hs.1
    revert h
    cases a <;> cases a' <;> cases b <;> cases c <;> decide

/-- **Left permutivity around the ring**: two rows with one image that agree across the seam are equal. -/
theorem eq_of_seam {x x' : List Bool} (hl : x.length = x'.length) (hs : ringStep x = ringStep x')
    (hk : seam x = seam x') : x = x' := by
  cases x with
  | nil => cases x' with
    | nil => rfl
    | cons _ _ => simp at hl
  | cons b v => cases x' with
    | nil => simp at hl
    | cons b' v' =>
      simp only [ringStep] at hs
      have he : endPair (lastOf b v) b (v ++ [b]) = endPair (lastOf b' v') b' (v' ++ [b']) := by
        rw [endPair_snoc, endPair_snoc]; exact hk
      obtain ⟨_, hb, hu⟩ := stepChain_inj _ _ _ _ _ _ (by simpa using hl) hs he
      subst hb
      rw [List.append_cancel_right hu]

theorem lsum_le_one_of_unique (q : List Bool → Bool)
    (hq : ∀ x ∈ rows W, ∀ x' ∈ rows W, q x = true → q x' = true → x = x') :
    lsum (rows W) (fun x => ind (q x)) ≤ 1 := by
  by_cases hex : ∃ x0 ∈ rows W, q x0 = true
  · obtain ⟨x0, hx0, hq0⟩ := hex
    calc lsum (rows W) (fun x => ind (q x)) ≤ lsum (rows W) (fun x => ind (decide (x = x0))) :=
          lsum_le fun x hx => by
            cases hqx : q x
            · simp [ind]
            · rw [hq x hx x0 hx0 hqx hq0]; simp [ind]
      _ = 1 := rows_count' hx0
  · have : lsum (rows W) (fun x => ind (q x)) = 0 := lsum_eq_zero fun x hx => by
      cases hqx : q x
      · rfl
      · exact absurd ⟨x, hx, hqx⟩ hex
    omega

theorem ringStep_head (b : Bool) (v : List Bool) : ∃ c rest, ringStep (b :: v) = rule30 (lastOf b v) b c :: rest := by
  cases v with
  | nil => exact ⟨b, [], rfl⟩
  | cons e v => exact ⟨e, _, rfl⟩

/-- **At most three preimages**: on a ring of `W ≥ 1` cells, distinct preimages of a row differ across the seam, and
one of the four values there is impossible: `(0, 1)` when the row is white at cell `0`, `(1, 1)` when it is black. -/
theorem preimages_le_three (hW : 1 ≤ W) (z : List Bool) : preimages W z ≤ 3 := by
  rw [preimages_eq]
  have split : ∀ x, ind (decide (ringStep x = z)) =
      lsum alph2 (fun p => ind (decide (p = seam x) && decide (ringStep x = z))) := by
    intro x
    rw [lsum_congr fun p _ => ind_and _ _]
    exact (lsum_pick_const (seam x) (complete2 (seam x)) _).symm
  rw [lsum_congr fun x _ => split x, lsum_comm]
  have hclass : ∀ p, lsum (rows W) (fun x => ind (decide (p = seam x) && decide (ringStep x = z))) ≤ 1 := by
    intro p
    apply lsum_le_one_of_unique
    intro x hx x' hx' hq hq'
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hq hq'
    exact eq_of_seam (by rw [length_of_mem_rows hx, length_of_mem_rows hx']) (hq.2.trans hq'.2.symm)
      (hq.1.symm.trans hq'.1)
  have hforbid : ∃ p, lsum (rows W) (fun x => ind (decide (p = seam x) && decide (ringStep x = z))) = 0 := by
    cases z with
    | nil =>
      refine ⟨(false, false), lsum_eq_zero fun x hx => ?_⟩
      have : ringStep x ≠ [] := by
        intro h
        have := congrArg List.length h
        rw [length_ringStep, length_of_mem_rows hx] at this
        simp at this; omega
      simp [this, ind]
    | cons h t =>
      refine ⟨(h, true), lsum_eq_zero fun x _ => ?_⟩
      cases x with
      | nil => simp [ringStep, ind]
      | cons b v =>
        obtain ⟨c, rest, hr⟩ := ringStep_head b v
        rw [hr]
        simp only [seam, Prod.mk.injEq]
        by_cases hb : b = true
        · by_cases hl : lastOf b v = h
          · subst hb
            have : rule30 h true c ≠ h := by cases h <;> cases c <;> decide
            simp [hl, this, ind]
          · have : ¬ h = lastOf b v := fun e => hl e.symm
            simp [this, ind]
        · have : ¬ true = b := fun e => hb e.symm
          simp [this, ind]
  have e : alph2 = [(false, false), (false, true), (true, false), (true, true)] := rfl
  obtain ⟨p, hp⟩ := hforbid
  rw [e]
  simp only [lsum]
  have h1 := hclass (false, false)
  have h2 := hclass (false, true)
  have h3 := hclass (true, false)
  have h4 := hclass (true, true)
  obtain ⟨p1, p2⟩ := p
  cases p1 <;> cases p2 <;> omega

/-! ### The count -/

/-- For a number `c ≤ 3` of preimages: `6 [c = 0] + 6 c + c (c - 1) (c - 2) = 6 + 3 c (c - 1)`. -/
theorem small_identity (c : Nat) (hc : c ≤ 3) :
    6 * ind (decide (c = 0)) + 6 * c + c * (c - 1) * (c - 2) = 6 + 3 * (c * (c - 1)) := by
  have : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 := by omega
  rcases this with rfl | rfl | rfl | rfl <;> rfl

theorem missed_eq (W : Nat) : missed W = lsum (rows W) (fun z => ind (decide (preimages W z = 0))) :=
  countP_eq_lsum _ _

/-- **The count**: `6 * missed + T = 3 * P`, with `P` the ordered pairs and `T` the ordered triples of distinct rows
with one image. -/
theorem six_missed (hW : 1 ≤ W) :
    6 * missed W + lsum (rows W) (fun x => lsum (rows W) (fun y => lsum (rows W) (fun u => ind (tripC x y u)))) =
      3 * lsum (rows W) (fun x => lsum (rows W) (fun y => ind (pairC x y))) := by
  have h := lsum_congr (l := rows W) fun z _ => small_identity (preimages W z) (preimages_le_three hW z)
  rw [lsum_add, lsum_add, lsum_add, lsum_mul, lsum_mul, lsum_mul, sum_preimages, ← missed_eq, triples_total,
    pairs_total, lsum_const, lsum_const] at h
  omega

end Counting

end RingImages

/-! ### The headline -/

open RingImages

/-- **The rows a ring step does not reach.** On a ring of `W ≥ 1` cells, the number `m_W` of rows that one step of
Rule 30 does not reach satisfies `2 m_W + 2 [3 ∣ W] = p_W + 1`, with `p_W` the power sums of the roots of
`x^3 - x^2 - 2`. -/
theorem ring_missed_rows (W : Nat) (hW : 1 ≤ W) :
    2 * missed W + 2 * (if W % 3 = 0 then 1 else 0) = powerSum W + 1 := by
  obtain ⟨n, rfl⟩ : ∃ n, W = n + 1 := ⟨W - 1, by omega⟩
  have h := six_missed hW
  rw [triples_eq_trace, pairs_eq_trace, pairTrace_eq _ hW, tripleTrace_eq _ hW] at h
  by_cases h3 : (n + 1) % 3 = 0
  · simp only [h3, ↓reduceIte] at h ⊢; omega
  · simp only [h3, ↓reduceIte] at h ⊢; omega

/-- The same count, as the finding writes it: `m_W = (p_W + 1) / 2 - [3 ∣ W]`. -/
theorem ring_missed_rows_div (W : Nat) (hW : 1 ≤ W) :
    missed W = (powerSum W + 1) / 2 - (if W % 3 = 0 then 1 else 0) := by
  have h := ring_missed_rows W hW
  by_cases h3 : W % 3 = 0
  · simp only [h3, ↓reduceIte] at h ⊢; omega
  · simp only [h3, ↓reduceIte] at h ⊢; omega

/-- **The image of a ring step**: `2^W - m_W` rows are reached. -/
theorem ring_image_card (W : Nat) :
    (rows W).countP (fun z => decide (preimages W z ≠ 0)) + missed W = 2 ^ W := by
  rw [← rows_length, missed, List.length_eq_countP_add_countP (fun z => decide (preimages W z ≠ 0))]
  congr 1
  exact List.countP_congr fun z _ => by simp

/-- **At most three preimages** on a ring of `W ≥ 1` cells. -/
theorem ring_preimages_le_three (W : Nat) (hW : 1 ≤ W) (z : List Bool) : preimages W z ≤ 3 :=
  preimages_le_three hW z

/-- **Three preimages exactly when `3 ∣ W`**: one row has three preimages if `3 ∣ W`, none otherwise. -/
theorem ring_three_preimages (W : Nat) (hW : 1 ≤ W) :
    (rows W).countP (fun z => decide (preimages W z = 3)) = if W % 3 = 0 then 1 else 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, W = n + 1 := ⟨W - 1, by omega⟩
  have ht := triples_total (W := n + 1)
  rw [triples_eq_trace, tripleTrace_eq _ hW] at ht
  have hc : ∀ z, preimages (n + 1) z * (preimages (n + 1) z - 1) * (preimages (n + 1) z - 2) =
      6 * ind (decide (preimages (n + 1) z = 3)) := by
    intro z
    have := preimages_le_three hW z
    have : preimages (n + 1) z = 0 ∨ preimages (n + 1) z = 1 ∨ preimages (n + 1) z = 2 ∨
        preimages (n + 1) z = 3 := by omega
    rcases this with h | h | h | h <;> rw [h] <;> rfl
  rw [lsum_congr fun z _ => hc z, lsum_mul] at ht
  rw [countP_eq_lsum]
  by_cases h3 : (n + 1) % 3 = 0
  · simp only [h3, ↓reduceIte] at ht ⊢; omega
  · simp only [h3, ↓reduceIte] at ht ⊢; omega

/-! ### The kit's registers -/

namespace RingImages

open Ruliology.CellularAutomata

theorem stepChain_eq_lin : ∀ (a b : Bool) (u : List Bool), stepChain a b u = Rule30.lin (a :: b :: u)
  | _, _, [] => rfl
  | a, b, c :: u => by
    rw [stepChain, stepChain_eq_lin b c u]
    rfl

theorem lastOf_eq_getLastD : ∀ (b : Bool) (v : List Bool), lastOf b v = (b :: v).getLastD false
  | _, [] => rfl
  | _, e :: v => by rw [lastOf, lastOf_eq_getLastD e v]; simp [List.getLastD_eq_getLast?]

/-- `ringStep` is the kit's step of Rule 30 on a cyclic register, `Rule30.step`. -/
theorem ringStep_eq_step (x : List Bool) : ringStep x = Rule30.step x := by
  cases x with
  | nil => rfl
  | cons b v =>
    rw [ringStep, stepChain_eq_lin, lastOf_eq_getLastD]
    rfl

/-- Counting over `rows W` is counting over the kit's `regs W`: both list every row of `W` cells once. -/
theorem countP_rows_eq_regs (W : Nat) (q : List Bool → Bool) : (rows W).countP q = (Rule30.regs W).countP q := by
  have hreg : ∀ x : List Bool, x.length = W → lsum (Rule30.regs W) (fun y => ind (decide (y = x))) = 1 := by
    intro x hx
    have h := (Rule30.nodup_regs W).count_of_mem (Rule30.mem_regs.2 hx)
    rw [List.count, countP_eq_lsum] at h
    rw [← h]
    refine lsum_congr fun y _ => ?_
    by_cases e : y = x
    · subst e; simp
    · have hb : (y == x) = false := by simpa using e
      simp [e, hb]
  rw [countP_eq_lsum, countP_eq_lsum]
  calc lsum (rows W) (fun x => ind (q x))
      = lsum (rows W) (fun x => lsum (Rule30.regs W) (fun y => ind (decide (y = x)) * ind (q x))) :=
        lsum_congr fun x hx => by rw [lsum_mul_right, hreg x (length_of_mem_rows hx), Nat.one_mul]
    _ = lsum (rows W) (fun x => lsum (Rule30.regs W) (fun y => ind (decide (x = y)) * ind (q y))) :=
        lsum_congr fun x _ => lsum_congr fun y _ => by
          by_cases e : y = x
          · subst e; rfl
          · simp [e, Ne.symm e, ind]
    _ = lsum (Rule30.regs W) (fun y => ind (q y)) := by
        rw [lsum_comm]
        refine lsum_congr fun y hy => ?_
        have h := rows_count y
        rw [Rule30.mem_regs.1 hy] at h
        rw [lsum_mul_right, h, Nat.one_mul]

/-- `preimages W z` is the kit's `Rule30.predCount z` for a row `z` of `W ≥ 1` cells. -/
theorem preimages_eq_predCount {W : Nat} {z : List Bool} (hz : z.length = W) (hW : 1 ≤ W) :
    preimages W z = Rule30.predCount z := by
  have hne : z ≠ [] := by intro h; subst h; simp at hz; omega
  rw [Rule30.predCount_eq_countP z hne, hz, preimages, countP_rows_eq_regs]
  exact List.countP_congr fun x _ => by rw [ringStep_eq_step]; by_cases e : Rule30.step x = z <;> simp [e]

/-- `missed W` is the kit's `Rule30.numWithPreds 0 W`, the registers of `W` cells with no predecessor. -/
theorem missed_eq_numWithPreds (W : Nat) (hW : 1 ≤ W) : missed W = Rule30.numWithPreds 0 W := by
  rw [missed, countP_rows_eq_regs, Rule30.numWithPreds]
  refine List.countP_congr fun z hz => ?_
  rw [preimages_eq_predCount (Rule30.mem_regs.1 hz) hW]
  by_cases e : Rule30.predCount z = 0 <;> simp [e]

end RingImages

open Ruliology.CellularAutomata in
/-- **The kit's Garden-of-Eden count in closed form**: on a cyclic register of `N ≥ 1` cells, the registers with no
predecessor number `c_0` with `2 c_0 + 2 [3 ∣ N] = p_N + 1`. The kit proves `c_0 = c_2 + 2 [3 ∣ N]`
(`Rule30.numWithPreds_zero`). -/
theorem numWithPreds_zero_closed (N : Nat) (hN : 1 ≤ N) :
    2 * Rule30.numWithPreds 0 N + 2 * (if N % 3 = 0 then 1 else 0) = powerSum N + 1 := by
  rw [← missed_eq_numWithPreds N hN]
  exact ring_missed_rows N hN

open Ruliology.CellularAutomata in
/-- With the kit's `c_0 = c_2 + 2 [3 ∣ N]`: the registers with two predecessors number `c_2` with
`2 c_2 + 6 [3 ∣ N] = p_N + 1`. -/
theorem numWithPreds_two_closed (N : Nat) (hN : 1 ≤ N) :
    2 * Rule30.numWithPreds 2 N + 6 * (if N % 3 = 0 then 1 else 0) = powerSum N + 1 := by
  have h0 := numWithPreds_zero_closed N hN
  have h := Rule30.numWithPreds_zero N hN
  omega

/-! Spot checks: the rows missed by enumerating all rows of small rings (as `computations/ring_images.py` does), and the
power sums. -/

example : [1, 2, 3, 4, 5, 6].map missed = [1, 1, 3, 5, 6, 12] := by decide +kernel

example : (List.range 12).map powerSum = [3, 1, 1, 7, 9, 11, 25, 43, 65, 115, 201, 331] := by decide

example : ringStep [true, false, false, false] = [true, true, false, true] := by decide

end Rule30Open
