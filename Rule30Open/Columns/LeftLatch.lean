module

public import Rule30Open.Columns.KickedForm
public import Rule30Open.Foundations.Official

/-!
# Every eventual period as one statement about the left half

If a column repeats a block `b` from time `T` on, in the orbit of a row with a leftmost 1, the cells left of it
follow `held`, with a kick at each two consecutive 1s of the block (`KickedForm`); they form a finitely supported
half that meets the check at each 1 of the block; and the cell right of the column, which the half shows at each 0 of
the block, latches (`right_shown`, `right_latch`). `LeftLatch b` says that no finitely supported half does all of
this for ever, from any phase of the block. It rules the block out for every such column
(`column_not_eventually_of_leftLatch`), the single seed's center column included (`not_eventually_of_leftLatch`), and
it holds for the black block (`leftLatch_one`). So every eventual period, of every length, comes down to one statement
about the left half.

The natural-language argument is `LeftLatch.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

open Ruliology.CellularAutomata

/-- The block `b`, repeated, at step `t`. -/
def readAt (b : List Bool) (t : Nat) : Bool := b.getD (t % b.length) false

/-- One step of the half left of a column: `held`, with the cell next to the column flipped when `kick` holds. -/
def kickStep (kick : Bool) (u : Nat → Bool) : Nat → Bool
  | 0 => xor (held u 0) kick
  | j + 1 => held u (j + 1)

/-- The half left of a column that repeats `b` from phase `φ`, `t` steps after it is `u`: kicked where the block reads
1 at two steps in a row. -/
def kickOrbit (b : List Bool) (φ : Nat) (u : Nat → Bool) : Nat → Nat → Bool
  | 0 => u
  | t + 1 => kickStep (readAt b (t + φ) && readAt b (t + φ + 1)) (kickOrbit b φ u t)

/-- What a center that repeats `b` asks at step `t` of the half `u` and of the cell `a` right of the center: the check
at a 1 of the block, the cell right of the center shown at a 0, and its latch. -/
def Keeps (b : List Bool) (φ : Nat) (u a : Nat → Bool) (t : Nat) : Prop :=
  (readAt b (t + φ) = true → kickOrbit b φ u t 0 = !readAt b (t + φ + 1)) ∧
  (readAt b (t + φ) = false → a t = xor (readAt b (t + φ + 1)) (kickOrbit b φ u t 0)) ∧
  (a t = true → a (t + 1) = !readAt b (t + φ))

/-- **The left-half statement for the block `b`.** No finitely supported half, beside a center that repeats `b` from
any phase, keeps the conditions at every step with any cell right of the center. -/
def LeftLatch (b : List Bool) : Prop :=
  ∀ φ : Nat, ∀ u : Nat → Bool, (∃ M : Nat, ∀ j, M ≤ j → u j = false) →
    ¬ ∃ a : Nat → Bool, ∀ t, Keeps b φ u a t

/-- While column `k` repeats `b` from time `T`, the half left of it at time `T + t` is the kicked orbit of the half at
time `T`. -/
theorem kickOrbit_eq (init : Int → Bool) (k : Int) (b : List Bool) (T : Nat)
    (hc : ∀ t, evolve init (T + t) k = readAt b (t + T)) :
    ∀ t, kickOrbit b T (leftOf init T k) t = leftOf init (T + t) k := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih =>
    funext j
    cases j with
    | zero =>
      show xor (held (kickOrbit b T (leftOf init T k) t) 0) (readAt b (t + T) && readAt b (t + T + 1)) = _
      rw [ih, show T + (t + 1) = T + t + 1 by omega, left_kicked_zero init k (T + t), hc t,
        show T + t + 1 = T + (t + 1) by omega, hc (t + 1), show t + 1 + T = t + T + 1 by omega]
    | succ j =>
      show held (kickOrbit b T (leftOf init T k) t) (j + 1) = _
      rw [ih, show T + (t + 1) = T + t + 1 by omega, left_kicked_succ init k (T + t) j]

/-- **Every eventual period comes down to the left half.** In the orbit of a row with a leftmost 1, if `LeftLatch b`
holds, no column repeats `b` from any time on. -/
theorem column_not_eventually_of_leftLatch (init : Int → Bool) (m : Int) (hm : init m = true)
    (hz : ∀ x : Int, x < m → init x = false) (k : Int) (b : List Bool) (hb : LeftLatch b) :
    ¬ ∃ T : Nat, ∀ t, T ≤ t → evolve init t k = readAt b t := by
  rintro ⟨T, hT⟩
  have hc : ∀ t, evolve init (T + t) k = readAt b (t + T) := fun t => by
    rw [hT (T + t) (by omega), Nat.add_comm]
  have hk := kickOrbit_eq init k b T hc
  have edge := (left_edge init m hm hz T).2
  refine hb T (leftOf init T k) ⟨(k - m + T).toNat, fun j hj => edge _ (by omega)⟩
    ⟨fun t => evolve init (T + t) (k + 1), fun t => ⟨fun h1 => ?_, fun h0 => ?_, fun ha => ?_⟩⟩
  · rw [hk t, left_kicked_check init k (T + t) (by rw [hc t]; exact h1),
      show T + t + 1 = T + (t + 1) by omega, hc (t + 1), show t + 1 + T = t + T + 1 by omega]
  · have e := right_shown init k (T + t) (by rw [hc t]; exact h0)
    rw [show T + t + 1 = T + (t + 1) by omega, hc (t + 1), show t + 1 + T = t + T + 1 by omega] at e
    rw [hk t]
    show evolve init (T + t) (k + 1) = xor (readAt b (t + T + 1)) (evolve init (T + t) (k - 1 - ((0 : Nat) : Int)))
    rw [show k - 1 - ((0 : Nat) : Int) = k - 1 by omega]
    exact e
  · have e := right_latch init k (T + t) ha
    rw [hc t] at e
    show evolve init (T + (t + 1)) (k + 1) = !readAt b (t + T)
    rw [show T + (t + 1) = T + t + 1 by omega]
    exact e

/-- The official form: if `LeftLatch b` holds, the single seed's center column does not repeat `b` from any time on. -/
theorem not_eventually_of_leftLatch (b : List Bool) (hb : LeftLatch b) :
    ¬ ∃ T : Nat, ∀ t, T ≤ t → Rule30Prize.center t = readAt b t := by
  rintro ⟨T, hT⟩
  refine column_not_eventually_of_leftLatch single 0 rfl (fun x hx => decide_eq_false (by omega)) 0 b hb
    ⟨T, fun t ht => ?_⟩
  rw [evolve_single_center]
  exact hT t ht

/-- **The black block.** The check makes the half alternate at every step, 0 next to the column, and no finitely
supported half does; the kit's `Rule30DrivenLeft.ones_fails`, through the kicked form. -/
theorem leftLatch_one : LeftLatch [true] := by
  rintro φ u ⟨M, hM⟩ ⟨a, ha⟩
  have hr : ∀ t, readAt [true] t = true := fun t => by
    unfold readAt
    rw [show [true].length = 1 from rfl, Nat.mod_one]
    rfl
  have z : ∀ t, kickOrbit [true] φ u t 0 = false := fun t => by rw [(ha t).1 (hr _), hr]; rfl
  have key : ∀ n t, kickOrbit [true] φ u t (2 * n) = false ∧ kickOrbit [true] φ u t (2 * n + 1) = true := by
    intro n
    induction n with
    | zero =>
      intro t
      refine ⟨z t, ?_⟩
      have e : kickOrbit [true] φ u (t + 1) 0 = xor (xor (kickOrbit [true] φ u t 1) (kickOrbit [true] φ u t 0))
          (readAt [true] (t + φ) && readAt [true] (t + φ + 1)) := rfl
      rw [z (t + 1), z t, hr, hr] at e
      revert e
      cases kickOrbit [true] φ u t 1 <;> decide
    | succ n ih =>
      have ev : ∀ t, kickOrbit [true] φ u t (2 * n + 2) = false := by
        intro t
        have e : kickOrbit [true] φ u (t + 1) (2 * n + 1) = xor (kickOrbit [true] φ u t (2 * n + 2))
            (kickOrbit [true] φ u t (2 * n + 1) || kickOrbit [true] φ u t (2 * n)) := rfl
        rw [(ih (t + 1)).2, (ih t).2, (ih t).1] at e
        revert e
        cases kickOrbit [true] φ u t (2 * n + 2) <;> decide
      intro t
      rw [show 2 * (n + 1) = 2 * n + 2 by omega]
      refine ⟨ev t, ?_⟩
      have e : kickOrbit [true] φ u (t + 1) (2 * n + 2) = xor (kickOrbit [true] φ u t (2 * n + 2 + 1))
          (kickOrbit [true] φ u t (2 * n + 2) || kickOrbit [true] φ u t (2 * n + 1)) := rfl
      rw [ev (t + 1), ev t, (ih t).2] at e
      revert e
      cases kickOrbit [true] φ u t (2 * n + 2 + 1) <;> decide
  have h := (key M 0).2
  rw [show kickOrbit [true] φ u 0 = u from rfl, hM (2 * M + 1) (by omega)] at h
  exact Bool.false_ne_true h

end Rule30Open
