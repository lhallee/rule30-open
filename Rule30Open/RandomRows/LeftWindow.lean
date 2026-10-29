module

public import Rule30Open.Foundations.Evolve
public import Rule30Open.Foundations.Official
public import Rule30Open.Foundations.RightHalf

/-!
# A random left window gives a fair center window

Replace the cells `-1, ..., -n` of any row by a word `l` of `n` cells (`setLeft`), and read the center column at
times `n, ..., 1` (`centerWindow`). Over the `2^n` words, every center word comes out exactly once
(`count_centerWindow`, `centerWindow_unique`): with a uniformly random left window, the center cells at times
`1, ..., n` are independent fair coins, whatever the rest of the row holds. The single seed is the all-white window
(`seed_window`), one of the `2^n` equally likely outcomes, and nothing in the count singles it out.

Both counts rest on one fact about the light cone (`cone_left_xor`): the cell at the apex of a cone depends on the
cone's leftmost cell only through an XOR. The same fact bounds partial randomization (`count_adapted`,
`count_periodic`). Set the cells at the depths of a list `S` freely and keep the rest of the row. A condition that fixes
the center at a time in `S` by the center before that time holds for exactly half of the rows, independently of the
conditions at the other times; so a center column that repeats with period `p` from time `T` up to time `M` comes from
at most `2^k` of the `2^|S|` rows, with `k` the number of depths of `S` below `T + p`.

The natural-language argument is `LeftWindow.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

open Ruliology.CellularAutomata

/-! ### The light cone -/

/-- Two rows that agree on the cone of a cell give the same cell. -/
theorem cone_congr {init init' : Int → Bool} : ∀ (t : Nat) (x : Int),
    (∀ y : Int, x - t ≤ y → y ≤ x + t → init y = init' y) → evolve init t x = evolve init' t x
  | 0, x, h => h x (by omega) (by omega)
  | t + 1, x, h => by
    show rule30 (evolve init t (x - 1)) (evolve init t x) (evolve init t (x + 1)) =
      rule30 (evolve init' t (x - 1)) (evolve init' t x) (evolve init' t (x + 1))
    rw [cone_congr t (x - 1) fun y h1 h2 => h y (by omega) (by omega),
      cone_congr t x fun y h1 h2 => h y (by omega) (by omega),
      cone_congr t (x + 1) fun y h1 h2 => h y (by omega) (by omega)]

/-- The leftmost cell of a cone enters the cell at its apex only through an XOR: two rows that agree on the rest of the
cone give cells that differ exactly when the rows differ at the leftmost cell. -/
theorem cone_left_xor {init init' : Int → Bool} : ∀ (t : Nat) (x : Int),
    (∀ y : Int, x - t < y → y ≤ x + t → init y = init' y) →
      evolve init t x = xor (evolve init' t x) (xor (init (x - t)) (init' (x - t)))
  | 0, x, _ => by
    rw [show x - ((0 : Nat) : Int) = x by omega]
    show init x = xor (init' x) (xor (init x) (init' x))
    generalize init x = a
    generalize init' x = b
    cases a <;> cases b <;> rfl
  | t + 1, x, h => by
    have hl := cone_left_xor t (x - 1) fun y h1 h2 => h y (by omega) (by omega)
    have hc := cone_congr t x fun y h1 h2 => h y (by omega) (by omega)
    have hr := cone_congr t (x + 1) fun y h1 h2 => h y (by omega) (by omega)
    show rule30 (evolve init t (x - 1)) (evolve init t x) (evolve init t (x + 1)) =
      xor (rule30 (evolve init' t (x - 1)) (evolve init' t x) (evolve init' t (x + 1)))
        (xor (init (x - ((t + 1 : Nat) : Int))) (init' (x - ((t + 1 : Nat) : Int))))
    rw [hl, hc, hr, show x - 1 - (t : Int) = x - ((t + 1 : Nat) : Int) by omega]
    generalize evolve init' t (x - 1) = a
    generalize evolve init' t x = b
    generalize evolve init' t (x + 1) = c
    generalize init (x - ((t + 1 : Nat) : Int)) = d
    generalize init' (x - ((t + 1 : Nat) : Int)) = e
    cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> rfl

/-! ### Counting over all words -/

/-- Counting over the words `[f a, g a]` counts over `f` and over `g`. -/
theorem countP_pairs {α β : Type} (p : β → Bool) (f g : α → β) : ∀ L : List α,
    (L.flatMap fun a => [f a, g a]).countP p = L.countP (fun a => p (f a)) + L.countP (fun a => p (g a))
  | [] => rfl
  | a :: L => by
    rw [List.flatMap_cons, List.countP_append, countP_pairs p f g L, List.countP_cons, List.countP_cons,
      List.countP_cons, List.countP_cons, List.countP_nil]
    omega

/-- Counting over the words of length `n + 1` splits by the first cell. -/
theorem countP_allLists_succ (n : Nat) (p : List Bool → Bool) :
    (allLists (n + 1)).countP p =
      (allLists n).countP (fun l => p (false :: l)) + (allLists n).countP (fun l => p (true :: l)) :=
  countP_pairs p (fun l => false :: l) (fun l => true :: l) (allLists n)

/-- Two pairs of predicates whose indicators have equal sums at every point have equal sums of counts. -/
theorem countP_add_congr {α : Type} {p q p' q' : α → Bool}
    (h : ∀ a, ((if p a then 1 else 0) + if q a then 1 else 0) = (if p' a then 1 else 0) + if q' a then 1 else 0) :
    ∀ L : List α, L.countP p + L.countP q = L.countP p' + L.countP q'
  | [] => rfl
  | a :: L => by
    rw [List.countP_cons, List.countP_cons, List.countP_cons, List.countP_cons]
    have ha := h a
    have hL := countP_add_congr h L
    omega

/-- Every word appears exactly once among the words of its length. -/
theorem count_allLists_eq : ∀ w : List Bool, (allLists w.length).countP (fun l => decide (l = w)) = 1
  | [] => rfl
  | b :: w => by
    rw [List.length_cons, countP_allLists_succ]
    have ih := count_allLists_eq w
    have hne : ∀ c : Bool, c ≠ b → (allLists w.length).countP (fun l => decide (c :: l = b :: w)) = 0 := by
      intro c hc
      rw [List.countP_eq_zero]
      intro l _ hl
      exact hc (List.cons.inj (of_decide_eq_true hl)).1
    have heq : (allLists w.length).countP (fun l => decide (b :: l = b :: w)) = 1 := by
      rw [← ih]
      exact List.countP_congr fun l _ => by simp
    cases b
    · rw [heq, hne true (by decide)]
    · rw [heq, hne false (by decide)]

/-! ### The left window and the center window -/

/-- The row `init` with the cells left of column 0 replaced by the word `l`, outermost first: `setLeft init (b :: l)`
puts `b` at cell `-(l.length + 1)` and the cells of `l` at cells `-l.length, ..., -1`. -/
def setLeft (init : Int → Bool) : List Bool → Int → Bool
  | [] => init
  | b :: l => fun x => if x = -((l.length + 1 : Nat) : Int) then b else setLeft init l x

/-- The center cells of `setLeft init l` at times `n, n - 1, ..., 1`, with `n` the length of `l`: the latest first, as
the outermost cell comes first in `l`. -/
def centerWindow (init : Int → Bool) (l : List Bool) : List Bool :=
  (List.range l.length).reverse.map fun i => evolve (setLeft init l) (i + 1) 0

/-! Spot checks: the single seed's center column starts 1 1 0 1 (OEIS A051023), so its window of three cells reads
1 0 1, latest first; and the eight left windows of three cells give eight different center windows. -/

example : centerWindow single [false, false, false] = [true, false, true] := by decide

example : ((allLists 3).map (centerWindow single)).Nodup := by decide

theorem setLeft_cons_ne (init : Int → Bool) (b : Bool) (l : List Bool) (x : Int)
    (hx : x ≠ -((l.length + 1 : Nat) : Int)) : setLeft init (b :: l) x = setLeft init l x := by
  show (if x = -((l.length + 1 : Nat) : Int) then b else setLeft init l x) = setLeft init l x
  rw [ite_eq_right hx]

theorem setLeft_cons_eq (init : Int → Bool) (b : Bool) (l : List Bool) :
    setLeft init (b :: l) (-((l.length + 1 : Nat) : Int)) = b := by
  show (if -((l.length + 1 : Nat) : Int) = -((l.length + 1 : Nat) : Int) then b else setLeft init l _) = b
  rw [ite_eq_left rfl]

/-- The outermost cell does not reach the center before time `l.length + 1`, so the center window of `b :: l` is the
center at that time followed by the center window of `l`. -/
theorem centerWindow_cons (init : Int → Bool) (b : Bool) (l : List Bool) :
    centerWindow init (b :: l) = evolve (setLeft init (b :: l)) (l.length + 1) 0 :: centerWindow init l := by
  unfold centerWindow
  rw [List.length_cons, List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
    List.map_cons]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [List.mem_reverse, List.mem_range] at hi
  exact cone_congr (i + 1) 0 fun y h1 _ => setLeft_cons_ne init b l y (by omega)

/-- The outermost cell reaches the center at time `l.length + 1` through an XOR. -/
theorem centerWindow_flip (init : Int → Bool) (l : List Bool) :
    evolve (setLeft init (true :: l)) (l.length + 1) 0 = !evolve (setLeft init (false :: l)) (l.length + 1) 0 := by
  have h := @cone_left_xor (setLeft init (true :: l)) (setLeft init (false :: l)) (l.length + 1) 0
    fun y h1 _ => by
      rw [setLeft_cons_ne init true l y (by omega), setLeft_cons_ne init false l y (by omega)]
  rw [h, show (0 : Int) - ((l.length + 1 : Nat) : Int) = -((l.length + 1 : Nat) : Int) by omega,
    setLeft_cons_eq, setLeft_cons_eq]
  generalize evolve (setLeft init (false :: l)) (l.length + 1) 0 = c
  cases c <;> rfl

/-- **Exact distribution.** For every row and every `n`, the left windows of `n` cells and the center windows they
give are equally distributed: for every predicate `P` on words, as many left windows give a center window with `P`
as there are words with `P`. -/
theorem count_centerWindow (init : Int → Bool) : ∀ (n : Nat) (P : List Bool → Bool),
    (allLists n).countP (fun l => P (centerWindow init l)) = (allLists n).countP P
  | 0, _ => rfl
  | n + 1, P => by
    rw [countP_allLists_succ, countP_allLists_succ, ← count_centerWindow init n fun w => P (false :: w),
      ← count_centerWindow init n fun w => P (true :: w)]
    refine countP_add_congr (fun l => ?_) (allLists n)
    rw [centerWindow_cons, centerWindow_cons, centerWindow_flip]
    generalize evolve (setLeft init (false :: l)) (l.length + 1) 0 = c
    cases c
    · rfl
    · exact Nat.add_comm _ _

/-- **Every center window from exactly one left window.** -/
theorem centerWindow_unique (init : Int → Bool) (w : List Bool) :
    (allLists w.length).countP (fun l => decide (centerWindow init l = w)) = 1 :=
  (count_centerWindow init w.length fun v => decide (v = w)).trans (count_allLists_eq w)

theorem setLeft_white : ∀ n : Nat, setLeft single (List.replicate n false) = single
  | 0 => rfl
  | n + 1 => by
    funext x
    show (if x = -(((List.replicate n false).length + 1 : Nat) : Int) then false
      else setLeft single (List.replicate n false) x) = single x
    rw [setLeft_white n, List.length_replicate]
    by_cases hx : x = -((n + 1 : Nat) : Int)
    · rw [ite_eq_left hx, hx]
      exact (decide_eq_false (by omega)).symm
    · rw [ite_eq_right hx]

/-- **The single seed is the white window**: its center window is the official center column at times `n, ..., 1`. -/
theorem seed_window (n : Nat) :
    centerWindow single (List.replicate n false) = (List.range n).reverse.map fun i => Rule30Prize.center (i + 1) := by
  simp only [centerWindow, setLeft_white, List.length_replicate, evolve_single_center]

/-! ### Partial randomization -/

/-- The row `init` with cell `-s` set to `b`, for the depths `s` of `S` and the values `b` of `a` in turn. -/
def assign (init : Int → Bool) : List Nat → List Bool → Int → Bool
  | s :: S, b :: a => fun x => if x = -(s : Int) then b else assign init S a x
  | _, _ => init

/-- The condition at depth `s` on the center column of `row`: where `Q s` holds, the center at time `s` is `g s` of
the column. -/
def condAt (Q : Nat → Bool) (g : Nat → (Nat → Bool) → Bool) (row : Int → Bool) (s : Nat) : Bool :=
  !Q s || evolve row s 0 == g s fun t => evolve row t 0

/-- Every condition at the depths of `S`. -/
def meets (Q : Nat → Bool) (g : Nat → (Nat → Bool) → Bool) (row : Int → Bool) (S : List Nat) : Bool :=
  S.all (condAt Q g row)

theorem meets_cons (Q : Nat → Bool) (g : Nat → (Nat → Bool) → Bool) (row : Int → Bool) (s : Nat) (S : List Nat) :
    meets Q g row (s :: S) = (condAt Q g row s && meets Q g row S) := rfl

theorem assign_cons_ne (init : Int → Bool) (s : Nat) (b : Bool) (S : List Nat) (a : List Bool) (x : Int)
    (hx : x ≠ -(s : Int)) : assign init (s :: S) (b :: a) x = assign init S a x := by
  show (if x = -(s : Int) then b else assign init S a x) = assign init S a x
  rw [ite_eq_right hx]

theorem assign_cons_eq (init : Int → Bool) (s : Nat) (b : Bool) (S : List Nat) (a : List Bool) :
    assign init (s :: S) (b :: a) (-(s : Int)) = b := by
  show (if -(s : Int) = -(s : Int) then b else assign init S a _) = b
  rw [ite_eq_left rfl]

/-- Before time `s` the center does not see cell `-s`. -/
theorem assign_before (init : Int → Bool) (s : Nat) (b : Bool) (S : List Nat) (a : List Bool) (t : Nat)
    (ht : t < s) : evolve (assign init (s :: S) (b :: a)) t 0 = evolve (assign init S a) t 0 :=
  cone_congr t 0 fun y h1 _ => assign_cons_ne init s b S a y (by omega)

/-- At time `s` the center flips with cell `-s`. -/
theorem assign_flip (init : Int → Bool) (s : Nat) (S : List Nat) (a : List Bool) :
    evolve (assign init (s :: S) (true :: a)) s 0 = !evolve (assign init (s :: S) (false :: a)) s 0 := by
  have h := @cone_left_xor (assign init (s :: S) (true :: a)) (assign init (s :: S) (false :: a)) s 0
    fun y h1 _ => by
      rw [assign_cons_ne init s true S a y (by omega), assign_cons_ne init s false S a y (by omega)]
  rw [h, show (0 : Int) - (s : Int) = -(s : Int) by omega, assign_cons_eq, assign_cons_eq]
  generalize evolve (assign init (s :: S) (false :: a)) s 0 = c
  cases c <;> rfl

theorem all_eq_of_forall {α : Type} {f g : α → Bool} : ∀ L : List α, (∀ x ∈ L, f x = g x) → L.all f = L.all g
  | [], _ => rfl
  | x :: L, h => by
    rw [List.all_cons, List.all_cons, h x (List.mem_cons_self ..),
      all_eq_of_forall L fun y hy => h y (List.mem_cons_of_mem _ hy)]

/-- **Partial randomization.** Free the cells at the depths of `S`, listed deepest first, and keep the rest of the
row `init` (depth `s` is cell `-s`). Let the condition at each depth `s` with `Q s` ask that the center at time `s`
be `g s` of the center column, where `g s` reads the column only before time `s`. Then exactly `2^k` of the `2^|S|`
rows meet every condition, with `k` the number of depths without a condition: each condition holds for half of the
rows, whatever the others ask. -/
theorem count_adapted (init : Int → Bool) (Q : Nat → Bool) (g : Nat → (Nat → Bool) → Bool)
    (hg : ∀ s, Q s = true → ∀ c c' : Nat → Bool, (∀ t, t < s → c t = c' t) → g s c = g s c') :
    ∀ S : List Nat, S.Pairwise (fun a b => b < a) →
      (allLists S.length).countP (fun a => meets Q g (assign init S a) S) = 2 ^ S.countP (fun s => !Q s)
  | [], _ => rfl
  | s :: S, hS => by
    have hlt : ∀ s' ∈ S, s' < s := (List.pairwise_cons.mp hS).1
    have ih := count_adapted init Q g hg S (List.pairwise_cons.mp hS).2
    -- The conditions at the other depths read the center only before time `s`, where cell `-s` is invisible.
    have rest : ∀ (b : Bool) (a : List Bool),
        meets Q g (assign init (s :: S) (b :: a)) S = meets Q g (assign init S a) S := by
      intro b a
      refine all_eq_of_forall S fun s' hs' => ?_
      unfold condAt
      cases hq : Q s'
      · rfl
      · rw [assign_before init s b S a s' (hlt s' hs'),
          hg s' hq (fun t => evolve (assign init (s :: S) (b :: a)) t 0) (fun t => evolve (assign init S a) t 0)
            fun t ht => assign_before init s b S a t (by have := hlt s' hs'; omega)]
    -- The condition at `s` reads the center before `s` alike for both values of cell `-s`, and the center at `s`
    -- flips with the cell, so exactly one value meets it.
    have point : ∀ a : List Bool,
        ((if meets Q g (assign init (s :: S) (false :: a)) (s :: S) then 1 else 0) +
          if meets Q g (assign init (s :: S) (true :: a)) (s :: S) then 1 else 0) =
        (if meets Q g (assign init S a) S then 1 else 0) +
          if (!Q s && meets Q g (assign init S a) S) then 1 else 0 := by
      intro a
      rw [meets_cons, meets_cons, rest false a, rest true a]
      unfold condAt
      rw [assign_flip]
      generalize meets Q g (assign init S a) S = m
      cases hq : Q s
      · cases m <;> rfl
      · rw [hg s hq (fun t => evolve (assign init (s :: S) (true :: a)) t 0)
          (fun t => evolve (assign init (s :: S) (false :: a)) t 0)
          fun t ht => by rw [assign_before init s true S a t ht, assign_before init s false S a t ht]]
        generalize evolve (assign init (s :: S) (false :: a)) s 0 = c
        generalize (g s fun t => evolve (assign init (s :: S) (false :: a)) t 0) = G
        cases c <;> cases G <;> cases m <;> rfl
    rw [List.length_cons, countP_allLists_succ, countP_add_congr point (allLists S.length), List.countP_cons]
    cases Q s
    · show (allLists S.length).countP (fun a => meets Q g (assign init S a) S) +
          (allLists S.length).countP (fun a => meets Q g (assign init S a) S) = 2 ^ (S.countP (fun s => !Q s) + 1)
      rw [ih, Nat.pow_succ]
      omega
    · show (allLists S.length).countP (fun a => meets Q g (assign init S a) S) +
          (allLists S.length).countP (fun _ => false) = 2 ^ (S.countP (fun s => !Q s) + 0)
      rw [ih, List.countP_false]
      rfl

/-- The center column of `row` repeats with period `p` from time `T` up to time `M`. -/
def periodicUpTo (row : Int → Bool) (T p M : Nat) : Bool :=
  (List.range (M + 1)).all fun t => decide (t < T + p) || evolve row t 0 == evolve row (t - p) 0

/-- **A periodic center is rare.** Free the cells at the depths of `S`, listed deepest first and at most `M`. At most
`2^k` of the `2^|S|` rows have a center column that repeats with period `p` from time `T` up to time `M`, with `k`
the number of depths of `S` below `T + p`. -/
theorem count_periodic (init : Int → Bool) (T p M : Nat) (hp : 0 < p) (S : List Nat)
    (hS : S.Pairwise (fun a b => b < a)) (hM : ∀ s ∈ S, s ≤ M) :
    (allLists S.length).countP (fun a => periodicUpTo (assign init S a) T p M) ≤
      2 ^ S.countP (fun s => decide (s < T + p)) := by
  have h := count_adapted init (fun s => decide (T + p ≤ s)) (fun s c => c (s - p))
    (fun s hs c c' hc => hc (s - p) (by have := of_decide_eq_true hs; omega)) S hS
  have e : (S.countP fun s => !decide (T + p ≤ s)) = S.countP fun s => decide (s < T + p) :=
    List.countP_congr fun s _ => by
      rw [Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_iff]
      omega
  rw [← e, ← h]
  refine List.countP_mono_left fun a _ ha => ?_
  unfold meets
  rw [List.all_eq_true]
  intro s hs
  unfold periodicUpTo at ha
  rw [List.all_eq_true] at ha
  have hper := ha s (List.mem_range.mpr (by have := hM s hs; omega))
  show (!decide (T + p ≤ s) || evolve (assign init S a) s 0 == evolve (assign init S a) (s - p) 0) = true
  by_cases hs' : T + p ≤ s
  · have hlt : ¬ s < T + p := by omega
    rw [decide_eq_false hlt, Bool.false_or] at hper
    rw [decide_eq_true hs', Bool.not_true, Bool.false_or]
    exact hper
  · rw [decide_eq_false hs']
    rfl

end Rule30Open
