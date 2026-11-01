module

public import Rule30Open.Complexity.ConeScreening

/-!
# Every query of the leftmost cone cell costs a full level

A decision tree reads the cells of a row one at a time, each choice depending on the answers so far, and answers a
color; its depth is the most cells it reads on one branch. The kit's `QueryComplexity` (in its Mathlib-based
equivalent forms) proves that every tree computing the center after `t ≥ 2` steps has depth at least `2t - 1`, from
the top monomial `x_{-t+2} ⋯ x_t` of the center's GF(2) polynomial, and that `2t + 1` suffice.

The center flips with the leftmost cone cell `x_{-t}` on every row (`flip_center`), and the top monomial avoids that
cell. This module proves, for any function that flips with a cell `u` on every row:

* `depth_restrict_succ_le`: fixing `u` to white in a tree that computes the function, and following the white branch
  at every query of `u` (`restrict`), removes at least one query from every branch: the depth drops by at least one.
* `eval_restrict`: the restricted tree computes the function at the row with cell `u` set white.

For Rule 30 (`center_tree_drop`, `center_tree_lift`): the least depth of a tree for the center after `t` steps is
exactly one more than the least depth of a tree for `g_t = evo (setAt x (-t) false) t 0`, the center with the
leftmost cone cell held white. With the kit's degree theorem for `g_t`, whose top monomial is that of the center, every
tree for the center has depth at least `2t` for `t ≥ 2`.

The natural-language argument is `QueryDepth.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

/-- A decision tree on the cells of a row: a leaf answers, and `query i l r` reads cell `i` and continues with `l` if
it is white, `r` if it is black. The same type as the kit's `QueryComplexity.DecisionTree ℤ`. -/
inductive QTree
  | leaf (b : Bool)
  | query (i : Int) (l r : QTree)

namespace QTree

/-- The answer of a tree on a row. -/
def eval : QTree → (Int → Bool) → Bool
  | leaf b, _ => b
  | query i l r, x => if x i then r.eval x else l.eval x

/-- The most queries on one branch. -/
def depth : QTree → Nat
  | leaf _ => 0
  | query _ l r => max l.depth r.depth + 1

/-- Complement every leaf. -/
def negate : QTree → QTree
  | leaf b => leaf (!b)
  | query i l r => query i l.negate r.negate

/-- Restrict to the cells that `ρ` fixes: a query of a fixed cell follows the fixed branch and disappears, a query of
a free cell stays and fixes it on each branch. -/
def restrict : QTree → (Int → Option Bool) → QTree
  | leaf b, _ => leaf b
  | query i l r, ρ =>
    match ρ i with
    | some false => restrict l ρ
    | some true => restrict r ρ
    | none => query i (restrict l (fun j => if j = i then some false else ρ j))
        (restrict r (fun j => if j = i then some true else ρ j))

end QTree

open QTree

/-- The row `x` with the cells that `ρ` fixes overwritten. -/
def fillRow (ρ : Int → Option Bool) (x : Int → Bool) : Int → Bool := fun i =>
  match ρ i with
  | some b => b
  | none => x i

theorem depth_negate : ∀ T : QTree, T.negate.depth = T.depth
  | leaf _ => rfl
  | query _ l r => by simp only [negate, depth, depth_negate l, depth_negate r]

theorem eval_negate : ∀ (T : QTree) (x : Int → Bool), T.negate.eval x = !(T.eval x)
  | leaf _, _ => rfl
  | query i l r, x => by
    simp only [negate, eval, eval_negate l, eval_negate r]
    cases x i <;> rfl

/-- **The restricted tree computes the tree at the filled row.** -/
theorem eval_restrict : ∀ (T : QTree) (ρ : Int → Option Bool) (x : Int → Bool),
    (T.restrict ρ).eval x = T.eval (fillRow ρ x)
  | leaf _, _, _ => rfl
  | query i l r, ρ, x => by
    simp only [restrict]
    cases hρ : ρ i with
    | some c =>
      have hf : fillRow ρ x i = c := by simp [fillRow, hρ]
      cases c with
      | false => simp only [eval_restrict l, eval, hf]; rfl
      | true => simp only [eval_restrict r, eval, hf]; rfl
    | none =>
      have hf : fillRow ρ x i = x i := by simp [fillRow, hρ]
      have key : ∀ c : Bool, x i = c →
          fillRow (fun j => if j = i then some c else ρ j) x = fillRow ρ x := by
        intro c hc
        funext j
        by_cases hj : j = i
        · subst hj; simp [fillRow, hρ, hc]
        · simp [fillRow, hj]
      simp only [eval, hf]
      cases hx : x i
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rw [eval_restrict l, key false hx]
      · simp only [↓reduceIte]
        rw [eval_restrict r, key true hx]

/-- Restricting never adds a query. -/
theorem depth_restrict_le : ∀ (T : QTree) (ρ : Int → Option Bool), (T.restrict ρ).depth ≤ T.depth
  | leaf _, _ => Nat.le_refl _
  | query i l r, ρ => by
    simp only [restrict, depth]
    cases ρ i with
    | some c =>
      cases c with
      | false => dsimp only; have := depth_restrict_le l ρ; omega
      | true => dsimp only; have := depth_restrict_le r ρ; omega
    | none =>
      simp only [depth]
      have := depth_restrict_le l (fun j => if j = i then some false else ρ j)
      have := depth_restrict_le r (fun j => if j = i then some true else ρ j)
      omega

/-- A row that agrees with `ρ` on every fixed cell other than `u`. -/
def Fits (ρ : Int → Option Bool) (u : Int) (x : Int → Bool) : Prop :=
  ∀ i b, i ≠ u → ρ i = some b → x i = b

/-- **A cell that every branch must read.** If `ρ` fixes `u` to white and the tree flips with `u` on every row that
fits the other fixed cells, then restricting removes a query from every branch: the depth drops by at least one. -/
theorem depth_restrict_succ_le (u : Int) : ∀ (T : QTree) (ρ : Int → Option Bool), ρ u = some false →
    (∀ x, Fits ρ u x → T.eval (setAt x u true) ≠ T.eval (setAt x u false)) →
    (T.restrict ρ).depth + 1 ≤ T.depth
  | leaf b, ρ, _, hflip => by
    exact absurd rfl (hflip (fillRow ρ fun _ => false)
      (fun i c _ hc => by simp [fillRow, hc]))
  | query i l r, ρ, hu, hflip => by
    simp only [restrict, depth]
    cases hρ : ρ i with
    | some c =>
      cases c with
      | false => dsimp only; have := depth_restrict_le l ρ; omega
      | true => dsimp only; have := depth_restrict_le r ρ; omega
    | none =>
      simp only [depth]
      have hiu : i ≠ u := fun h => by subst h; rw [hu] at hρ; cases hρ
      have hside : ∀ (c : Bool) (x : Int → Bool), Fits (fun j => if j = i then some c else ρ j) u x →
            (if c then r else l).eval (setAt x u true) ≠ (if c then r else l).eval (setAt x u false) := by
        intro c x hx
        have hxi : x i = c := hx i c hiu (by simp)
        have hfit : Fits ρ u x := fun j b hj hb => by
          by_cases hji : j = i
          · subst hji; rw [hρ] at hb; cases hb
          · exact hx j b hj (by simp [hji, hb])
        have h := hflip x hfit
        have hs : ∀ v, setAt x u v i = c := fun v => by simp [setAt, hiu, hxi]
        simp only [eval, hs] at h
        cases c <;> simpa using h
      have hl := depth_restrict_succ_le u l (fun j => if j = i then some false else ρ j)
        (by simp [Ne.symm hiu, hu]) (fun x hx => by simpa using hside false x hx)
      have hr := depth_restrict_succ_le u r (fun j => if j = i then some true else ρ j)
        (by simp [Ne.symm hiu, hu]) (fun x hx => by simpa using hside true x hx)
      omega

/-- The restriction that fixes only the cell `u`, to white. -/
def whiteAt (u : Int) : Int → Option Bool := fun j => if j = u then some false else none

theorem fillRow_whiteAt (u : Int) (x : Int → Bool) : fillRow (whiteAt u) x = setAt x u false := by
  funext j
  by_cases hj : j = u <;> simp [fillRow, whiteAt, setAt, hj]

/-- **Dropping a cell that flips the function.** If a function flips with cell `u` on every row, every tree that
computes it gives a tree of smaller depth that computes it with `u` held white. -/
theorem tree_drop_of_flip (f : (Int → Bool) → Bool) (u : Int)
    (hflip : ∀ x, f (setAt x u true) ≠ f (setAt x u false)) (T : QTree) (hT : ∀ x, T.eval x = f x) :
    ∃ T' : QTree, (∀ x, T'.eval x = f (setAt x u false)) ∧ T'.depth + 1 ≤ T.depth :=
  ⟨T.restrict (whiteAt u), fun x => by rw [eval_restrict, hT, fillRow_whiteAt],
    depth_restrict_succ_le u T (whiteAt u) (by simp [whiteAt])
      (fun x _ => by rw [hT, hT]; exact hflip x)⟩

theorem setAt_setAt (x : Int → Bool) (u : Int) (b c : Bool) : setAt (setAt x u b) u c = setAt x u c := by
  funext j
  by_cases hj : j = u <;> simp [setAt, hj]

/-- The center after `t` steps flips with the leftmost cell of its cone, `-t`, on every row. -/
theorem center_flip_setAt (x : Int → Bool) (t : Nat) :
    evo (setAt x (-t) true) t 0 ≠ evo (setAt x (-t) false) t 0 := by
  rw [center_decomp (setAt x (-t) true), center_decomp (setAt x (-t) false), setAt_setAt, setAt_setAt]
  simp [setAt]

/-- **Every tree for the center pays one query for the leftmost cell.** A tree that computes the center after `t`
steps on every row gives a tree of smaller depth that computes it with cell `-t` held white. -/
theorem center_tree_drop (t : Nat) (T : QTree) (hT : ∀ x, T.eval x = evo x t 0) :
    ∃ T' : QTree, (∀ x, T'.eval x = evo (setAt x (-t) false) t 0) ∧ T'.depth + 1 ≤ T.depth :=
  tree_drop_of_flip (fun x => evo x t 0) (-t) (fun x => center_flip_setAt x t) T hT

/-- **And one query suffices.** A tree for the center with cell `-t` held white gives a tree for the center whose
depth is one more: read cell `-t`, then answer the tree's value or its complement. -/
theorem center_tree_lift (t : Nat) (T' : QTree) (hT' : ∀ x, T'.eval x = evo (setAt x (-t) false) t 0) :
    ∃ T : QTree, (∀ x, T.eval x = evo x t 0) ∧ T.depth = T'.depth + 1 :=
  ⟨.query (-t) T' T'.negate, fun x => by
    simp only [eval, eval_negate, hT', center_decomp x t]
    cases x (-t) <;> simp,
   by simp [depth, depth_negate]⟩

end Rule30Open
