module

public import Rule30Open.Complexity.LateSeedCut
public import Rule30Open.Complexity.LeftCutRank

/-!
# The letters a completion feeds to the left cut: two-letter constraints, a Pell bound, and a ceiling on the cut rank

Split the cone of the center after `t` steps after its `a` leftmost cells. The completion (the cells from the cut on)
acts on the `a` left cells only through its *letters* `letter r s = nevo r s % 4`, its two cells next to the cut at
time `s` (`nevo_mod` of `LateSeedCut`), and by the horizon only the letters at times `s < T = t - (⌈a/2⌉ - 1)` reach the
center (`lateCen_eq`).

* `letter_allowed`: two consecutive letters `e = letter r s`, `f = letter r (s + 1)` (bit 0 the cell next to the cut)
  obey `allowedNext e f`: after `0` comes `0, 2` or `3`; after `1` comes `1, 2` or `3`; after `2` comes `1` or `3`; after
  `3` comes `0` or `2`. The cell next to the cut flips when the cell after it is black, and when it flips from white the
  cell after it becomes black.
* `wordList_mem`, `card_words_le`: the words `letter r 0, ..., letter r (T - 1)` lie in a set of at most
  `wordBound T = 4, 10, 24, 58, 140, ...` words, twice the Pell numbers (`wordBound_succ_le`: at most three times more
  per letter).
* `lateCen_word`: the center depends on the completion only through its word of `T` letters.
* `cut_rank_le`: so every family of left settings that is independent over GF(2) across the cut, in the sense of
  `width_of_independent` of `LeftCutRank` (every nonempty subset has a completion with an odd number of black centers),
  has at most `wordBound T` members: the GF(2) rank of the left cut after `a` cells is at most `wordBound T`, for every
  `t`. The proof is a pigeonhole on the parities of subsets, read on the words.
* `cut_rank_lt_rho`: at the cut after `t - 3` cells, for every `t ≥ 24`, fewer than `ρ(t - 3) = 2 + ⌊2^(t-3)/3⌋`
  settings are independent. The left-cut rank finding computed `rank(t, a) = ρ(a)` for `a ≤ t - 3`, `t ≤ 14`, and
  conjectured it for every `t`; this refutes it for every `t ≥ 24`.

The natural-language argument is `LetterWords.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

/-! ## Letters and the two-letter constraints -/

/-- The letter of the completion `r` at time `s`: its two cells next to the cut, bit 0 the one next to it. -/
def letter (r s : Nat) : Nat := nevo r s % 4

theorem mod_four_eq (n : Nat) : n % 4 = (if n.testBit 0 then 1 else 0) + (if n.testBit 1 then 2 else 0) := by
  have h0 : n.testBit 0 = decide (n % 2 = 1) := Nat.testBit_zero n
  have h1 : n.testBit 1 = decide (n / 2 % 2 = 1) := by
    rw [Nat.testBit_succ, Nat.testBit_zero]
  rw [h0, h1]
  by_cases a0 : n % 2 = 1 <;> by_cases a1 : n / 2 % 2 = 1 <;> simp [a0, a1] <;> omega

/-- The letters that may follow a letter. -/
def allowedNext : Nat → Nat → Bool
  | 0, f => f == 0 || f == 2 || f == 3
  | 1, f => f == 1 || f == 2 || f == 3
  | 2, f => f == 1 || f == 3
  | 3, f => f == 0 || f == 2
  | _, _ => false

theorem letter_lt (r s : Nat) : letter r s < 4 := Nat.mod_lt _ (by decide)

/-- **The two-letter constraints.** -/
theorem letter_allowed (r s : Nat) : allowedNext (letter r s) (letter r (s + 1)) = true := by
  unfold letter
  show allowedNext (nevo r s % 4) (nstep (nevo r s) % 4) = true
  generalize nevo r s = M
  rw [mod_four_eq M, mod_four_eq (nstep M), testBit_nstep, testBit_nstep]
  simp only [Nat.reduceAdd]
  generalize M.testBit 0 = b0
  generalize M.testBit 1 = b1
  generalize M.testBit 2 = b2
  generalize M.testBit 3 = b3
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> rfl


/-! ## The words and their number -/

/-- The word of the completion `r`: its letters at times `0, ..., T - 1`. -/
def wordList (r T : Nat) : List Nat := (List.range T).map (letter r)

theorem wordList_succ (r T : Nat) : wordList r (T + 1) = wordList r T ++ [letter r T] := by
  simp [wordList, List.range_succ]

theorem wordList_getD (r T i : Nat) (hi : i < T) : (wordList r T).getD i 0 = letter r i := by
  simp [wordList, List.getD_eq_getElem?_getD, hi]

/-- The last letter of a word (`0` for the empty word). -/
def lastL (w : List Nat) : Nat := w.getLastD 0

theorem lastL_append (w : List Nat) (e : Nat) : lastL (w ++ [e]) = e := by
  simp [lastL]

/-- The words of `T + 1` letters that end in `0` or `1` (`low`) and in `2` or `3` (`high`), built letter by letter
along `allowedNext`: a low word goes on with its own last letter, `2` or `3`; a high word `2` with `1` or `3`, a high word
`3` with `0` or `2`. -/
def wordSets : Nat → List (List Nat) × List (List Nat)
  | 0 => ([[0], [1]], [[2], [3]])
  | T + 1 =>
    ((wordSets T).1.map (fun w => w ++ [lastL w]) ++ (wordSets T).2.map (fun w => w ++ [3 - lastL w]),
      (wordSets T).1.map (fun w => w ++ [2]) ++ (wordSets T).1.map (fun w => w ++ [3]) ++
        (wordSets T).2.map (fun w => w ++ [5 - lastL w]))

/-- The sizes of the two sets: `2, 4, 10, 24, ...` and `2, 6, 14, 34, ...`. -/
def wordCounts : Nat → Nat × Nat
  | 0 => (2, 2)
  | T + 1 => ((wordCounts T).1 + (wordCounts T).2, 2 * (wordCounts T).1 + (wordCounts T).2)

/-- The bound on the number of words of `T` letters: `4, 10, 24, 58, 140, 338, ...`, twice the Pell number
`P(T + 1)`. -/
def wordBound (T : Nat) : Nat := (wordCounts (T - 1)).1 + (wordCounts (T - 1)).2

/-- All words of `T` letters that obey the two-letter constraints. -/
def allowedWords (T : Nat) : List (List Nat) := (wordSets (T - 1)).1 ++ (wordSets (T - 1)).2

theorem wordSets_length (T : Nat) :
    (wordSets T).1.length = (wordCounts T).1 ∧ (wordSets T).2.length = (wordCounts T).2 := by
  induction T with
  | zero => exact ⟨rfl, rfl⟩
  | succ T ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨?_, ?_⟩
    · simp only [wordSets, wordCounts, List.length_append, List.length_map, h1, h2]
    · simp only [wordSets, wordCounts, List.length_append, List.length_map, h1, h2]
      omega

/-- The bound for `T = 1, ..., 8`. -/
theorem wordBound_values : (List.range 8).map (fun T => wordBound (T + 1)) = [4, 10, 24, 58, 140, 338, 816, 1970] := by
  decide

theorem allowedWords_length (T : Nat) : (allowedWords T).length = wordBound T := by
  obtain ⟨h1, h2⟩ := wordSets_length (T - 1)
  simp [allowedWords, wordBound, h1, h2]

theorem wordList_one (r : Nat) : wordList r 1 = [letter r 0] := rfl

/-- The letters that may follow `e`, sorted by where the longer word goes. -/
theorem allowed_cases (e f : Nat) (he : e < 4) (hA : allowedNext e f = true) :
    (e < 2 ∧ (f = e ∨ f = 2 ∨ f = 3)) ∨ (2 ≤ e ∧ (f = 3 - e ∨ f = 5 - e)) := by
  rcases (show e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 by omega) with rfl | rfl | rfl | rfl <;>
    simp [allowedNext] at hA <;> omega

/-- **Every word lies in the sets**, the low one if its last letter is `0` or `1`. -/
theorem wordList_mem (r T : Nat) :
    (letter r T < 2 → wordList r (T + 1) ∈ (wordSets T).1) ∧
      (2 ≤ letter r T → wordList r (T + 1) ∈ (wordSets T).2) := by
  induction T with
  | zero =>
    have h4 := letter_lt r 0
    rw [wordList_one]
    constructor
    · intro h
      rcases (show letter r 0 = 0 ∨ letter r 0 = 1 by omega) with e | e <;> rw [e] <;> decide
    · intro h
      rcases (show letter r 0 = 2 ∨ letter r 0 = 3 by omega) with e | e <;> rw [e] <;> decide
  | succ T ih =>
    obtain ⟨hL, hH⟩ := ih
    have hA := letter_allowed r T
    have h4 := letter_lt r T
    rw [wordList_succ r (T + 1)]
    generalize hw : wordList r (T + 1) = w at hL hH
    have hlast : lastL w = letter r T := by rw [← hw, wordList_succ, lastL_append]
    generalize letter r T = e at hA h4 hL hH hlast
    generalize letter r (T + 1) = f at hA
    simp only [wordSets, List.mem_append]
    rcases allowed_cases e f h4 hA with ⟨he, hf⟩ | ⟨he, hf⟩
    · have hw' := hL he
      rcases hf with rfl | rfl | rfl
      · refine ⟨fun _ => Or.inl ?_, fun h => absurd h (by omega)⟩
        have := List.mem_map_of_mem (f := fun w => w ++ [lastL w]) hw'
        rwa [hlast] at this
      · exact ⟨fun h => absurd h (by omega), fun _ => Or.inl (Or.inl (List.mem_map_of_mem hw'))⟩
      · exact ⟨fun h => absurd h (by omega), fun _ => Or.inl (Or.inr (List.mem_map_of_mem hw'))⟩
    · have hw' := hH he
      rcases hf with rfl | rfl
      · refine ⟨fun _ => Or.inr ?_, fun h => absurd h (by omega)⟩
        have := List.mem_map_of_mem (f := fun w => w ++ [3 - lastL w]) hw'
        rwa [hlast] at this
      · refine ⟨fun h => absurd h (by omega), fun _ => Or.inr ?_⟩
        have := List.mem_map_of_mem (f := fun w => w ++ [5 - lastL w]) hw'
        rwa [hlast] at this

theorem wordList_mem_allowed (r T : Nat) (hT : 1 ≤ T) : wordList r T ∈ allowedWords T := by
  obtain ⟨hL, hH⟩ := wordList_mem r (T - 1)
  rw [show T - 1 + 1 = T by omega] at hL hH
  unfold allowedWords
  rw [List.mem_append]
  by_cases h : letter r (T - 1) < 2
  · exact Or.inl (hL h)
  · exact Or.inr (hH (by omega))

/-! ## The center reads the completion only through its word -/

/-- The center after `T + n` steps of the left cells `P`, driven by the letters of the word `w`. -/
def centerOfWord (a T n : Nat) (w : List Nat) (P : Nat) : Bool :=
  (nevo (aliceRun a (fun i => w.getD i 0) P T) n).testBit 0

/-- **The center through the word.** With `2n + 1 ≤ a`, the center after `T + n` steps depends on the completion `r`
only through its word of `T` letters. -/
theorem lateCen_word (a T n r P : Nat) (hP : P < 2 ^ a) (hn : 2 * n + 1 ≤ a) :
    lateCen a (T + n) r P = centerOfWord a T n (wordList r T) P := by
  rw [lateCen_eq a T n r P hP hn]
  unfold centerOfWord
  rw [aliceRun_congr a (fun i => nevo r i % 4) (fun i => (wordList r T).getD i 0) P T
    (fun i hi => by rw [wordList_getD r T i hi]; rfl)]

/-- The cells of the completion `z` from the cut on, as a number. -/
def coneNum (t a : Nat) (z : Int → Bool) : Nat := enc (fun k => z (-(t : Int) + a + k)) (2 * t + 1 - a)

/-- The center of a spliced row is that of the two numbers. -/
theorem center_splice_eq (t a : Nat) (hat : a ≤ t) (x z : Int → Bool) :
    evo (spliceAt (-(t : Int) + a) x z) t 0 = lateCen a t (coneNum t a z) (enc (fun k => x ((k : Int) - t)) a) := by
  rw [← evolve_eq_evo]
  apply evolve_splice_late
  intro i h1 h2
  unfold coneNum
  rw [testBit_enc _ _ _ (by omega)]
  congr 1
  omega

/-! ## A pigeonhole on the parities of subsets -/

/-- All lists of `m` bits. -/
def allBits : Nat → List (List Bool)
  | 0 => [[]]
  | m + 1 => (allBits m).map (false :: ·) ++ (allBits m).map (true :: ·)

theorem allBits_length (m : Nat) : (allBits m).length = 2 ^ m := by
  induction m with
  | zero => rfl
  | succ m ih => simp [allBits, ih, Nat.pow_succ]; omega

theorem mem_allBits : ∀ (m : Nat) (c : List Bool), c ∈ allBits m ↔ c.length = m
  | 0, c => by cases c <;> simp [allBits]
  | m + 1, [] => by simp [allBits]
  | m + 1, b :: c => by
    have ih := mem_allBits m c
    cases b <;> simp [allBits, ih]

theorem nodup_map_of_inj {α β : Type} (f : α → β) :
    ∀ {l : List α}, l.Nodup → (∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) → (l.map f).Nodup
  | [], _, _ => by simp
  | a :: l, hl, hinj => by
    rw [List.nodup_cons] at hl
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, nodup_map_of_inj f hl.2 (fun x hx y hy h => hinj x (by simp [hx]) y (by simp [hy]) h)⟩
    intro hm
    rw [List.mem_map] at hm
    obtain ⟨b, hb, hfb⟩ := hm
    have := hinj b (by simp [hb]) a (by simp) hfb
    exact hl.1 (this ▸ hb)

theorem allBits_nodup : ∀ m, (allBits m).Nodup
  | 0 => by simp [allBits]
  | m + 1 => by
    have ih := allBits_nodup m
    unfold allBits
    rw [List.nodup_append]
    refine ⟨?_, ?_, ?_⟩
    · exact nodup_map_of_inj _ ih (fun x _ y _ h => (List.cons.inj h).2)
    · exact nodup_map_of_inj _ ih (fun x _ y _ h => (List.cons.inj h).2)
    · intro a ha b hb hab
      simp only [List.mem_map] at ha hb
      obtain ⟨c, _, rfl⟩ := ha
      obtain ⟨d, _, rfl⟩ := hb
      simp at hab

/-- **Pigeonhole.** A map from the lists of `m` bits to the lists of `k < m` bits takes the same value at two
different lists. -/
theorem exists_collision (m k : Nat) (hk : k < m) (f : List Bool → List Bool) (hf : ∀ c, (f c).length = k) :
    ∃ c ∈ allBits m, ∃ c' ∈ allBits m, c ≠ c' ∧ f c = f c' := by
  apply Classical.byContradiction
  intro h
  have hinj : ∀ x ∈ allBits m, ∀ y ∈ allBits m, f x = f y → x = y := by
    intro x hx y hy hxy
    apply Classical.byContradiction
    intro hne
    exact h ⟨x, hx, y, hy, hne, hxy⟩
  have hnd := nodup_map_of_inj f (allBits_nodup m) hinj
  have hsub : (allBits m).map f ⊆ allBits k := by
    intro v hv
    rw [List.mem_map] at hv
    obtain ⟨c, _, rfl⟩ := hv
    exact (mem_allBits k (f c)).2 (hf c)
  have hle := hnd.length_le_of_subset hsub
  rw [List.length_map, allBits_length, allBits_length] at hle
  have : 2 ^ k < 2 ^ m := Nat.pow_lt_pow_right (by decide) hk
  omega

theorem parityUpTo_xor (u v w : Nat → Bool) : ∀ m,
    parityUpTo (fun k => xor (u k) (v k) && w k) m =
      xor (parityUpTo (fun k => u k && w k) m) (parityUpTo (fun k => v k && w k) m)
  | 0 => rfl
  | m + 1 => by
    simp only [parityUpTo]
    rw [parityUpTo_xor u v w m]
    cases u m <;> cases v m <;> cases w m <;>
      cases parityUpTo (fun k => u k && w k) m <;> cases parityUpTo (fun k => v k && w k) m <;> rfl

theorem exists_ne_index (c c' : List Bool) (h1 : c.length = c'.length) (hne : c ≠ c') :
    ∃ i, i < c.length ∧ c.getD i false ≠ c'.getD i false := by
  apply Classical.byContradiction
  intro h
  apply hne
  apply List.ext_getElem h1
  intro i hi hi'
  have := Classical.byContradiction (fun hc : ¬ c.getD i false = c'.getD i false => h ⟨i, hi, hc⟩)
  simpa [List.getD_eq_getElem?_getD, hi, hi'] using this

/-! ## The rank of the left cut is at most the number of words -/

/-- **The ceiling on the cut rank.** Every family of `m` left settings of the `a` leftmost cells (`1 ≤ a ≤ t`) that is
independent over GF(2) across the cut, as in `width_of_independent`, has at most `wordBound T` members, where
`T = t - (⌈a/2⌉ - 1)`: the GF(2) rank of the left cut is at most the number of words of `T` letters that obey the
two-letter constraints. -/
theorem cut_rank_le (t a m : Nat) (ha : 1 ≤ a) (hat : a ≤ t) (rows : Nat → Int → Bool)
    (hind : ∀ c : Nat → Bool, (∃ i, i < m ∧ c i = true) →
      ∃ z, parityUpTo (fun k => c k && evo (spliceAt (-(t : Int) + a) (rows k) z) t 0) m = true) :
    m ≤ wordBound (t - ((a + 1) / 2 - 1)) := by
  obtain ⟨n, hn⟩ : ∃ n, n = (a + 1) / 2 - 1 := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T, T = t - n := ⟨_, rfl⟩
  rw [← hn, ← hT]
  have h2n : 2 * n + 1 ≤ a := by omega
  have htT : t = T + n := by omega
  have hT1 : 1 ≤ T := by omega
  apply Classical.byContradiction
  intro hlt
  have hk : (allowedWords T).length < m := by rw [allowedWords_length]; omega
  let P : Nat → Nat := fun k => enc (fun j => rows k ((j : Int) - t)) a
  have hP : ∀ k, P k < 2 ^ a := fun k => enc_lt a _
  let pv : List Bool → List Bool := fun c =>
    (allowedWords T).map (fun w => parityUpTo (fun k => c.getD k false && centerOfWord a T n w (P k)) m)
  obtain ⟨c, hc, c', hc', hne, heq⟩ :=
    exists_collision m (allowedWords T).length hk pv (fun c => by simp [pv])
  have hlc := (mem_allBits m c).1 hc
  have hlc' := (mem_allBits m c').1 hc'
  obtain ⟨i, hi, hci⟩ := exists_ne_index c c' (by rw [hlc, hlc']) hne
  obtain ⟨z, hz⟩ := hind (fun k => xor (c.getD k false) (c'.getD k false)) ⟨i, by omega, by
    revert hci; cases c.getD i false <;> cases c'.getD i false <;> simp⟩
  have hcenter : ∀ k, evo (spliceAt (-(t : Int) + a) (rows k) z) t 0 =
      centerOfWord a T n (wordList (coneNum t a z) T) (P k) := by
    intro k
    have e := lateCen_word a T n (coneNum t a z) (P k) (hP k) h2n
    rw [← htT] at e
    rw [center_splice_eq t a hat]
    exact e
  have hfun : (fun k => xor (c.getD k false) (c'.getD k false) && evo (spliceAt (-(t : Int) + a) (rows k) z) t 0) =
      (fun k => xor (c.getD k false) (c'.getD k false) &&
        centerOfWord a T n (wordList (coneNum t a z) T) (P k)) := by
    funext k
    rw [hcenter k]
  rw [hfun, parityUpTo_xor] at hz
  have hmem := wordList_mem_allowed (coneNum t a z) T hT1
  have hval := (List.map_inj_left.1 heq) _ hmem
  rw [hval] at hz
  simp at hz

/-! ## The left-cut rank conjecture fails for every `t ≥ 24` -/

/-- `ρ(a) = 2 + ⌊2^a / 3⌋`, the rank of the left cut after `a` cells for `a ≤ t - 3` and `t ≤ 14`. -/
def rhoCut (a : Nat) : Nat := 2 + 2 ^ a / 3

theorem wordBound_succ_le (T : Nat) (hT : 1 ≤ T) : wordBound (T + 1) ≤ 3 * wordBound T := by
  unfold wordBound
  rw [show T + 1 - 1 = (T - 1) + 1 by omega]
  simp only [wordCounts]
  omega

theorem rhoCut_add_two (a : Nat) : 4 * rhoCut a ≤ rhoCut (a + 2) + 6 := by
  unfold rhoCut
  rw [Nat.pow_add]
  omega

/-- The bound beats `ρ(t - 3)` from `t = 24` on. -/
theorem wordBound_lt_rhoCut_step (t : Nat) (ht : 24 ≤ t)
    (h : wordBound (t - ((t - 3 + 1) / 2 - 1)) < rhoCut (t - 3)) :
    wordBound (t + 2 - ((t + 2 - 3 + 1) / 2 - 1)) < rhoCut (t + 2 - 3) := by
  have e1 : t + 2 - ((t + 2 - 3 + 1) / 2 - 1) = (t - ((t - 3 + 1) / 2 - 1)) + 1 := by omega
  have e2 : t + 2 - 3 = (t - 3) + 2 := by omega
  rw [e1, e2]
  have h3 := wordBound_succ_le (t - ((t - 3 + 1) / 2 - 1)) (by omega)
  have h4 := rhoCut_add_two (t - 3)
  have h5 : 6 ≤ rhoCut (t - 3) := by
    unfold rhoCut
    have : 2 ^ 21 ≤ 2 ^ (t - 3) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  omega

/-- The bound beats `ρ(t - 3)` from `t = 24` on. -/
theorem wordBound_lt_rhoCut (t : Nat) (ht : 24 ≤ t) : wordBound (t - ((t - 3 + 1) / 2 - 1)) < rhoCut (t - 3) := by
  have key : ∀ k, wordBound (24 + 2 * k - ((24 + 2 * k - 3 + 1) / 2 - 1)) < rhoCut (24 + 2 * k - 3) ∧
      wordBound (25 + 2 * k - ((25 + 2 * k - 3 + 1) / 2 - 1)) < rhoCut (25 + 2 * k - 3) := by
    intro k
    induction k with
    | zero => exact ⟨by decide, by decide⟩
    | succ k ih =>
      have a1 := wordBound_lt_rhoCut_step (24 + 2 * k) (by omega) ih.1
      have a2 := wordBound_lt_rhoCut_step (25 + 2 * k) (by omega) ih.2
      rw [show 24 + 2 * k + 2 = 24 + 2 * (k + 1) by omega] at a1
      rw [show 25 + 2 * k + 2 = 25 + 2 * (k + 1) by omega] at a2
      exact ⟨a1, a2⟩
  rcases Nat.mod_two_eq_zero_or_one (t - 24) with hk | hk
  · have := (key ((t - 24) / 2)).1
    rwa [show 24 + 2 * ((t - 24) / 2) = t by omega] at this
  · have := (key ((t - 24) / 2)).2
    rwa [show 25 + 2 * ((t - 24) / 2) = t by omega] at this

/-- **The rank conjecture of the left cut fails for every `t ≥ 24`.** At the cut after the `t - 3` leftmost cells,
fewer than `ρ(t - 3) = 2 + ⌊2^(t-3)/3⌋` left settings are independent over GF(2): the rank of the cut is below
`ρ(t - 3)`, which the left-cut rank finding computed for `t ≤ 14` and conjectured for every `t`. -/
theorem cut_rank_lt_rhoCut (t m : Nat) (ht : 24 ≤ t) (rows : Nat → Int → Bool)
    (hind : ∀ c : Nat → Bool, (∃ i, i < m ∧ c i = true) →
      ∃ z, parityUpTo (fun k => c k && evo (spliceAt (-(t : Int) + (t - 3 : Nat)) (rows k) z) t 0) m = true) :
    m < rhoCut (t - 3) :=
  Nat.lt_of_le_of_lt (cut_rank_le t (t - 3) m (by omega) (by omega) rows hind) (wordBound_lt_rhoCut t ht)

end Rule30Open
