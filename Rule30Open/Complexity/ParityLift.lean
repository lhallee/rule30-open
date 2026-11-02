module

public import Rule30Open.Complexity.ConeScreening

/-!
# Odd weight: Walsh coefficients 2 mod 4 and an invertible XOR lift

A Boolean function `g` on the words of length `m` (lists of `Bool`, with sums over the cube `cubeSum`, `cubeXor`)
has *odd weight* when it takes the value true on an odd number of words (`cubeXor m g = true`). Its Walsh
coefficient at `a` is `∑_x (-1)^(g x ⊕ a·x)` (`cubeWalsh`), and its *XOR lift* is the matrix `M x y = g (x ⊕ y)`
over GF(2). For every odd-weight `g`:

* `cubeWalsh_emod_four`: for `m ≥ 2`, every Walsh coefficient is `2` mod `4`, so none is `0`.
* `lift_sq`: `M² = 1` over GF(2): `∑_y g (x ⊕ y) g (y ⊕ z) = [x = z]`. So the XOR lift is invertible,
  `liftApply_liftApply`, `lift_injective`: as a GF(2) linear map on the functions of the cube it is its own inverse,
  hence of full rank `2^m`.
* `walsh_support_of_flip`: if `h` on `m + 2` cells flips with its first cell and `h` with its first two cells white
  has odd weight, `m ≥ 2`, then at least `2^m` Walsh coefficients of `h` are nonzero.

For Rule 30, `coneFn t` is the center after `t` steps as a function of the word `x_{-t}, …, x_t` on its cone. It flips
with its first cell (`coneFn_flip`, from `flip_center`), and the restricted center `x_{-t+2}, …, x_t ↦ coneFn t
(0 :: 0 :: x)` has odd weight for `t ≥ 2`: this is the kit's `AlgebraicDegree.coef_center_top`, the top monomial of
the center, whose coefficient is a sum over exactly these words. The kit's equivalent forms need Mathlib, which this
repository does not build, so the Rule 30 statements take odd weight as a hypothesis (`center_walsh_emod_four`,
`center_lift_sq`, `center_walsh_support`), and `center_odd_small` checks it for `t = 2, 3, 4, 5` by evaluation.

The natural-language argument is `ParityLift.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

/-! ## Sums over the cube of words -/

/-- The sum of `F` over the `2^m` words of length `m`. -/
def cubeSum : Nat → (List Bool → Int) → Int
  | 0, F => F []
  | m + 1, F => cubeSum m (fun x => F (false :: x)) + cubeSum m (fun x => F (true :: x))

/-- The sum over GF(2) (the parity) of `F` over the `2^m` words of length `m`. -/
def cubeXor : Nat → (List Bool → Bool) → Bool
  | 0, F => F []
  | m + 1, F => xor (cubeXor m (fun x => F (false :: x))) (cubeXor m (fun x => F (true :: x)))

/-- The GF(2) inner product of two words. -/
def cubeDot : List Bool → List Bool → Bool
  | a :: as, b :: bs => xor (a && b) (cubeDot as bs)
  | _, _ => false

/-- The cellwise XOR of two words. -/
def wordXor : List Bool → List Bool → List Bool
  | a :: as, b :: bs => xor a b :: wordXor as bs
  | _, _ => []

/-- The Walsh coefficient of `g` at the linear function `x ↦ a · x`. -/
def cubeWalsh (m : Nat) (g : List Bool → Bool) (a : List Bool) : Int :=
  cubeSum m (fun x => if xor (g x) (cubeDot a x) then -1 else 1)

/-- The number of words of length `m` where `P` holds. -/
def cubeCount (m : Nat) (P : List Bool → Bool) : Int := cubeSum m (fun x => if P x then 1 else 0)

theorem cubeSum_congr : ∀ (m : Nat) (F G : List Bool → Int), (∀ x : List Bool, x.length = m → F x = G x) →
    cubeSum m F = cubeSum m G
  | 0, F, G, h => h [] rfl
  | m + 1, F, G, h => by
    simp only [cubeSum]
    rw [cubeSum_congr m (fun x => F (false :: x)) (fun x => G (false :: x)) (fun x hx => h _ (by simp [hx])),
      cubeSum_congr m (fun x => F (true :: x)) (fun x => G (true :: x)) (fun x hx => h _ (by simp [hx]))]

theorem cubeSum_add : ∀ (m : Nat) (F G : List Bool → Int),
    cubeSum m (fun x => F x + G x) = cubeSum m F + cubeSum m G
  | 0, _, _ => rfl
  | m + 1, F, G => by
    simp only [cubeSum]
    rw [cubeSum_add m (fun x => F (false :: x)), cubeSum_add m (fun x => F (true :: x))]
    omega

theorem cubeSum_mul : ∀ (m : Nat) (c : Int) (F : List Bool → Int),
    cubeSum m (fun x => c * F x) = c * cubeSum m F
  | 0, _, _ => rfl
  | m + 1, c, F => by
    simp only [cubeSum]
    rw [cubeSum_mul m c (fun x => F (false :: x)), cubeSum_mul m c (fun x => F (true :: x)), Int.mul_add]

theorem cubeSum_zero : ∀ m : Nat, cubeSum m (fun _ => 0) = 0
  | 0 => rfl
  | m + 1 => by
    simp only [cubeSum]
    rw [cubeSum_zero m]
    rfl

theorem cubeSum_neg : ∀ (m : Nat) (F : List Bool → Int), cubeSum m (fun x => -F x) = -cubeSum m F
  | 0, _ => rfl
  | m + 1, F => by
    simp only [cubeSum]
    rw [cubeSum_neg m (fun x => F (false :: x)), cubeSum_neg m (fun x => F (true :: x))]
    omega

/-- The sign `(-1)^(p ⊕ q)` changes with `q`. -/
theorem sign_xor_not (p q : Bool) : (if xor p (!q) then (-1 : Int) else 1) = -(if xor p q then -1 else 1) := by
  cases p <;> cases q <;> rfl

theorem cubeSum_one : ∀ m : Nat, cubeSum m (fun _ => 1) = 2 ^ m
  | 0 => rfl
  | m + 1 => by
    simp only [cubeSum]
    rw [cubeSum_one m, Int.pow_succ]
    omega

theorem cubeSum_le : ∀ (m : Nat) (F G : List Bool → Int), (∀ x : List Bool, x.length = m → F x ≤ G x) →
    cubeSum m F ≤ cubeSum m G
  | 0, F, G, h => h [] rfl
  | m + 1, F, G, h => by
    simp only [cubeSum]
    have h0 := cubeSum_le m (fun x => F (false :: x)) (fun x => G (false :: x)) (fun x hx => h _ (by simp [hx]))
    have h1 := cubeSum_le m (fun x => F (true :: x)) (fun x => G (true :: x)) (fun x hx => h _ (by simp [hx]))
    omega

theorem emod_two_add (A B : Int) (p q : Bool) (hA : A % 2 = if p then 1 else 0) (hB : B % 2 = if q then 1 else 0) :
    (A + B) % 2 = if xor p q then 1 else 0 := by
  cases p <;> cases q <;> simp at hA hB ⊢ <;> omega

/-- The integer count of `g` has the parity `cubeXor m g`. -/
theorem cubeCount_emod_two : ∀ (m : Nat) (g : List Bool → Bool),
    cubeCount m g % 2 = if cubeXor m g then 1 else 0
  | 0, g => by cases h : g [] <;> simp [cubeCount, cubeSum, cubeXor, h]
  | m + 1, g => by
    have h0 := cubeCount_emod_two m (fun x => g (false :: x))
    have h1 := cubeCount_emod_two m (fun x => g (true :: x))
    simp only [cubeCount] at h0 h1 ⊢
    simp only [cubeSum, cubeXor]
    exact emod_two_add _ _ _ _ h0 h1

/-- A linear function on at least two cells has even weight. -/
theorem cubeCount_dot_even (m : Nat) (a : List Bool) : cubeCount (m + 2) (cubeDot a) % 2 = 0 := by
  cases a with
  | nil =>
    have : cubeCount (m + 2) (cubeDot []) = 0 :=
      Eq.trans (cubeSum_congr _ _ (fun _ => 0) fun x _ => by simp [cubeDot]) (cubeSum_zero _)
    rw [this]; rfl
  | cons a0 a' =>
    rw [cubeCount, show m + 2 = (m + 1) + 1 from rfl, cubeSum]
    cases a0
    · simp only [cubeDot, Bool.false_and, Bool.false_xor]
      omega
    · simp only [cubeDot, Bool.true_and, Bool.false_xor, Bool.true_xor]
      have h := cubeSum_add (m + 1) (fun x => if cubeDot a' x then 1 else 0)
        (fun x => if !cubeDot a' x then 1 else 0)
      rw [← h, cubeSum_congr (m + 1) _ (fun _ => 1) (fun x _ => by cases cubeDot a' x <;> rfl), cubeSum_one,
        Int.pow_succ]
      omega

/-- **Walsh coefficients of an odd-weight function are 2 mod 4.** For `m ≥ 2` and `g` of odd weight on the words of
length `m`, every Walsh coefficient of `g` is `2` mod `4`; in particular none is `0`. -/
theorem cubeWalsh_emod_four (m : Nat) (hm : 2 ≤ m) (g : List Bool → Bool) (hg : cubeXor m g = true)
    (a : List Bool) : cubeWalsh m g a % 4 = 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  have hpt : ∀ x : List Bool, (if xor (g x) (cubeDot a x) then (-1 : Int) else 1) =
      1 + ((-2) * (if g x then 1 else 0) + ((-2) * (if cubeDot a x then 1 else 0) +
        4 * (if g x && cubeDot a x then 1 else 0))) := by
    intro x
    cases g x <;> cases cubeDot a x <;> rfl
  have hW : cubeWalsh (k + 2) g a = 2 ^ (k + 2) - 2 * cubeCount (k + 2) g - 2 * cubeCount (k + 2) (cubeDot a) +
      4 * cubeCount (k + 2) (fun x => g x && cubeDot a x) := by
    rw [cubeWalsh, cubeSum_congr _ _ _ fun x _ => hpt x, cubeSum_add, cubeSum_add, cubeSum_add, cubeSum_mul,
      cubeSum_mul, cubeSum_mul, cubeSum_one]
    simp only [cubeCount]
    omega
  have hg2 := cubeCount_emod_two (k + 2) g
  rw [hg] at hg2
  have hl2 := cubeCount_dot_even k a
  have h4 : (2 : Int) ^ (k + 2) = 2 ^ k * 4 := by rw [Int.pow_succ, Int.pow_succ]; omega
  rw [hW, h4]
  simp only [ite_true] at hg2
  omega

theorem cubeWalsh_ne_zero (m : Nat) (hm : 2 ≤ m) (g : List Bool → Bool) (hg : cubeXor m g = true)
    (a : List Bool) : cubeWalsh m g a ≠ 0 := by
  have := cubeWalsh_emod_four m hm g hg a
  omega

/-! ## The XOR lift over GF(2) -/

theorem wordXor_length : ∀ a b : List Bool, a.length = b.length → (wordXor a b).length = a.length
  | [], [], _ => rfl
  | _ :: as, _ :: bs, h => by simp [wordXor, wordXor_length as bs (by simpa using h)]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem wordXor_comm : ∀ a b : List Bool, wordXor a b = wordXor b a
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | a :: as, b :: bs => by simp [wordXor, wordXor_comm as bs, Bool.xor_comm]

theorem wordXor_assoc : ∀ a b c : List Bool, wordXor (wordXor a b) c = wordXor a (wordXor b c)
  | a :: as, b :: bs, c :: cs => by simp [wordXor, wordXor_assoc as bs cs]
  | [], _, _ => by simp [wordXor]
  | _ :: _, [], _ => by simp [wordXor]
  | _ :: _, _ :: _, [] => by simp [wordXor]

theorem wordXor_cancel : ∀ a b : List Bool, a.length = b.length → wordXor (wordXor a b) b = a
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by simp [wordXor, wordXor_cancel as bs (by simpa using h)]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-- The XOR of two words of the same length is white exactly when they are equal. -/
theorem wordXor_all : ∀ a b : List Bool, a.length = b.length → (wordXor a b).all (!·) = decide (a = b)
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
    have ih := wordXor_all as bs (by simpa using h)
    simp only [wordXor, List.all_cons, ih, List.cons.injEq]
    cases a <;> cases b <;> simp
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem cubeXor_congr : ∀ (m : Nat) (F G : List Bool → Bool), (∀ x : List Bool, x.length = m → F x = G x) →
    cubeXor m F = cubeXor m G
  | 0, F, G, h => h [] rfl
  | m + 1, F, G, h => by
    simp only [cubeXor]
    rw [cubeXor_congr m (fun x => F (false :: x)) (fun x => G (false :: x)) (fun x hx => h _ (by simp [hx])),
      cubeXor_congr m (fun x => F (true :: x)) (fun x => G (true :: x)) (fun x hx => h _ (by simp [hx]))]

theorem cubeXor_xor : ∀ (m : Nat) (F G : List Bool → Bool),
    cubeXor m (fun x => xor (F x) (G x)) = xor (cubeXor m F) (cubeXor m G)
  | 0, _, _ => rfl
  | m + 1, F, G => by
    simp only [cubeXor]
    rw [cubeXor_xor m (fun x => F (false :: x)), cubeXor_xor m (fun x => F (true :: x))]
    generalize cubeXor m (fun x => F (false :: x)) = p
    generalize cubeXor m (fun x => F (true :: x)) = q
    generalize cubeXor m (fun x => G (false :: x)) = r
    generalize cubeXor m (fun x => G (true :: x)) = s
    revert p q r s
    decide

theorem and_cubeXor : ∀ (m : Nat) (b : Bool) (F : List Bool → Bool),
    (b && cubeXor m F) = cubeXor m (fun x => b && F x)
  | 0, _, _ => rfl
  | m + 1, b, F => by
    simp only [cubeXor]
    rw [← and_cubeXor m b (fun x => F (false :: x)), ← and_cubeXor m b (fun x => F (true :: x))]
    cases b <;> simp

theorem cubeXor_and : ∀ (m : Nat) (b : Bool) (F : List Bool → Bool),
    (cubeXor m F && b) = cubeXor m (fun x => F x && b) := by
  intro m b F
  rw [Bool.and_comm, and_cubeXor]
  exact cubeXor_congr _ _ _ fun x _ => Bool.and_comm _ _

/-- The two orders of a double sum over GF(2). -/
theorem cubeXor_comm : ∀ (m n : Nat) (F : List Bool → List Bool → Bool),
    cubeXor m (fun y => cubeXor n (fun z => F y z)) = cubeXor n (fun z => cubeXor m (fun y => F y z))
  | 0, _, _ => rfl
  | m + 1, n, F => by
    simp only [cubeXor]
    rw [cubeXor_comm m n (fun y z => F (false :: y) z), cubeXor_comm m n (fun y z => F (true :: y) z),
      ← cubeXor_xor]

/-- A sum over GF(2) is invariant under translation by a word of the same length. -/
theorem cubeXor_translate : ∀ (m : Nat) (F : List Bool → Bool) (d : List Bool), d.length = m →
    cubeXor m (fun x => F (wordXor x d)) = cubeXor m F
  | 0, F, [], _ => rfl
  | 0, _, _ :: _, h => by simp at h
  | m + 1, _, [], h => by simp at h
  | m + 1, F, d0 :: d', h => by
    have hd : d'.length = m := by simpa using h
    simp only [cubeXor, wordXor]
    rw [cubeXor_translate m (fun y => F (xor false d0 :: y)) d' hd,
      cubeXor_translate m (fun y => F (xor true d0 :: y)) d' hd]
    cases d0 <;> simp [Bool.xor_comm]

/-- The autocorrelation over GF(2): `∑_u g u g (u ⊕ d)` is the weight of `g` mod 2 at `d = 0` and `0` elsewhere. -/
theorem cubeXor_autocorr : ∀ (m : Nat) (g : List Bool → Bool) (d : List Bool), d.length = m →
    cubeXor m (fun u => g u && g (wordXor u d)) = (cubeXor m g && d.all (!·))
  | 0, g, [], _ => by simp [cubeXor, wordXor]
  | 0, _, _ :: _, h => by simp at h
  | m + 1, _, [], h => by simp at h
  | m + 1, g, d0 :: d', h => by
    have hd : d'.length = m := by simpa using h
    simp only [cubeXor, wordXor]
    cases d0
    · simp only [Bool.xor_false, List.all_cons, Bool.not_false, Bool.true_and]
      rw [cubeXor_autocorr m (fun u => g (false :: u)) d' hd, cubeXor_autocorr m (fun u => g (true :: u)) d' hd]
      cases d'.all (!·) <;> simp
    · simp only [Bool.false_xor, Bool.true_xor, Bool.not_true, List.all_cons, Bool.false_and, Bool.and_false]
      have hsw : cubeXor m (fun u => g (true :: u) && g (false :: wordXor u d')) =
          cubeXor m (fun u => g (false :: u) && g (true :: wordXor u d')) := by
        rw [← cubeXor_translate m (fun u => g (true :: u) && g (false :: wordXor u d')) d' hd]
        exact cubeXor_congr _ _ _ fun u hu => by
          rw [wordXor_cancel u d' (by rw [hu, hd]), Bool.and_comm]
      rw [hsw, Bool.xor_self]

/-- **The XOR lift squares to the identity times the weight.** Over GF(2),
`∑_y g (x ⊕ y) g (y ⊕ z) = (weight of g mod 2) · [x = z]` for words `x`, `z` of length `m`. -/
theorem lift_sq_weight (m : Nat) (g : List Bool → Bool) (x z : List Bool) (hx : x.length = m)
    (hz : z.length = m) :
    cubeXor m (fun y => g (wordXor x y) && g (wordXor y z)) = (cubeXor m g && decide (x = z)) := by
  rw [← cubeXor_translate m (fun y => g (wordXor x y) && g (wordXor y z)) x hx]
  have hxz : (wordXor x z).length = m := by rw [wordXor_length x z (by rw [hx, hz]), hx]
  rw [← wordXor_all x z (by rw [hx, hz]), ← cubeXor_autocorr m g (wordXor x z) hxz]
  exact cubeXor_congr _ _ _ fun u hu => by
    rw [wordXor_comm x (wordXor u x), wordXor_cancel u x (by rw [hu, hx]), wordXor_assoc]

/-- **`M² = 1`.** For `g` of odd weight, the XOR lift `M x y = g (x ⊕ y)` is its own inverse over GF(2). -/
theorem lift_sq (m : Nat) (g : List Bool → Bool) (hg : cubeXor m g = true) (x z : List Bool)
    (hx : x.length = m) (hz : z.length = m) :
    cubeXor m (fun y => g (wordXor x y) && g (wordXor y z)) = decide (x = z) := by
  rw [lift_sq_weight m g x z hx hz, hg, Bool.true_and]

/-- The XOR lift applied to a vector `v` over GF(2): `(M v) x = ∑_y g (x ⊕ y) v y`. -/
def liftApply (m : Nat) (g : List Bool → Bool) (v : List Bool → Bool) (x : List Bool) : Bool :=
  cubeXor m (fun y => g (wordXor x y) && v y)

/-- The point mass: `∑_z [x = z] v z = v x` for `x` of length `m`. -/
theorem cubeXor_delta : ∀ (m : Nat) (v : List Bool → Bool) (x : List Bool), x.length = m →
    cubeXor m (fun z => decide (x = z) && v z) = v x
  | 0, v, [], _ => by simp [cubeXor]
  | 0, _, _ :: _, h => by simp at h
  | m + 1, _, [], h => by simp at h
  | m + 1, v, x0 :: x', h => by
    have hx : x'.length = m := by simpa using h
    simp only [cubeXor, List.cons.injEq]
    have e0 := cubeXor_delta m (fun z => v (false :: z)) x' hx
    have e1 := cubeXor_delta m (fun z => v (true :: z)) x' hx
    have z0 : ∀ b : Bool, cubeXor m (fun z => decide (False ∧ x' = z) && v (b :: z)) = false := by
      intro b
      have := and_cubeXor m false (fun z => v (b :: z))
      simp only [Bool.false_and] at this
      rw [this]
      exact cubeXor_congr _ _ _ fun z _ => by simp
    cases x0
    · simp only [true_and, Bool.false_eq_true, z0, Bool.xor_false]
      exact e0
    · simp only [true_and, Bool.true_eq_false, z0, Bool.false_xor]
      exact e1

/-- **The XOR lift of an odd-weight function is an involution over GF(2)**: `M (M v) = v` on the cube. -/
theorem liftApply_liftApply (m : Nat) (g : List Bool → Bool) (hg : cubeXor m g = true) (v : List Bool → Bool)
    (x : List Bool) (hx : x.length = m) : liftApply m g (liftApply m g v) x = v x := by
  simp only [liftApply]
  rw [cubeXor_congr m _ (fun y => cubeXor m (fun z => g (wordXor x y) && (g (wordXor y z) && v z)))
      (fun y _ => and_cubeXor _ _ _),
    cubeXor_comm, ← cubeXor_delta m v x hx]
  exact cubeXor_congr _ _ _ fun z hz => by
    rw [← lift_sq m g hg x z hx hz, cubeXor_and]
    exact cubeXor_congr _ _ _ fun y _ => by rw [Bool.and_assoc]

/-- **Full rank over GF(2).** The XOR lift of an odd-weight function is injective on the functions of the cube
(and onto them, by `liftApply_liftApply`): as a GF(2) matrix of size `2^m` it has rank `2^m`. -/
theorem lift_injective (m : Nat) (g : List Bool → Bool) (hg : cubeXor m g = true) (v w : List Bool → Bool)
    (h : ∀ x : List Bool, x.length = m → liftApply m g v x = liftApply m g w x) :
    ∀ x : List Bool, x.length = m → v x = w x := by
  intro x hx
  rw [← liftApply_liftApply m g hg v x hx, ← liftApply_liftApply m g hg w x hx]
  exact cubeXor_congr _ _ _ fun y hy => by rw [h y hy]

/-! ## Counting nonzero Walsh coefficients -/

/-- Split the Walsh coefficient along the first cell. -/
theorem cubeWalsh_cons (m : Nat) (g : List Bool → Bool) (b : Bool) (a : List Bool) :
    cubeWalsh (m + 1) g (b :: a) = cubeWalsh m (fun x => g (false :: x)) a +
      (if b then -1 else 1) * cubeWalsh m (fun x => g (true :: x)) a := by
  simp only [cubeWalsh, cubeSum, cubeDot, Bool.and_false, Bool.and_true, Bool.false_xor]
  cases b
  · simp only [Bool.false_xor, Bool.false_eq_true, ite_false, Int.one_mul]
  · simp only [Bool.true_xor, ite_true]
    rw [Int.neg_one_mul, ← cubeSum_neg]
    congr 1
    exact cubeSum_congr _ _ _ fun x _ => sign_xor_not _ _

/-- If the restriction to a white first cell has no zero Walsh coefficient, then at least `2^m` of the `2^(m+1)`
Walsh coefficients are nonzero: the coefficients at `0 :: a` and `1 :: a` sum to twice that of the restriction. -/
theorem walsh_support_ge (m : Nat) (g : List Bool → Bool)
    (h : ∀ a : List Bool, a.length = m → cubeWalsh m (fun x => g (false :: x)) a ≠ 0) :
    2 ^ m ≤ cubeCount (m + 1) (fun a => cubeWalsh (m + 1) g a != 0) := by
  rw [cubeCount, cubeSum, ← cubeSum_one m, ← cubeSum_add]
  refine cubeSum_le _ _ _ fun a ha => ?_
  have h0 := cubeWalsh_cons m g false a
  have h1 := cubeWalsh_cons m g true a
  have hne := h a ha
  simp only [Bool.false_eq_true, ite_false, ite_true] at h0 h1
  by_cases e0 : cubeWalsh (m + 1) g (false :: a) = 0
  · have e1 : cubeWalsh (m + 1) g (true :: a) ≠ 0 := by omega
    simp [e0, e1]
  · by_cases e1 : cubeWalsh (m + 1) g (true :: a) = 0 <;> simp [e0, e1]

/-- If `h` flips with its first cell, its Walsh coefficients at `0 :: a` vanish and those at `1 :: a` are twice those
of the restriction `h (0 :: ·)`. -/
theorem cubeWalsh_flip (m : Nat) (h : List Bool → Bool) (hf : ∀ x, h (true :: x) = !h (false :: x))
    (a : List Bool) :
    cubeWalsh (m + 1) h (false :: a) = 0 ∧
      cubeWalsh (m + 1) h (true :: a) = 2 * cubeWalsh m (fun x => h (false :: x)) a := by
  have e : cubeWalsh m (fun x => h (true :: x)) a = -cubeWalsh m (fun x => h (false :: x)) a := by
    rw [cubeWalsh, cubeWalsh, ← cubeSum_neg]
    exact cubeSum_congr _ _ _ fun x _ => by
      rw [hf x, ← sign_xor_not]
      cases h (false :: x) <;> cases cubeDot a x <;> rfl
  rw [cubeWalsh_cons, cubeWalsh_cons, e]
  simp only [Bool.false_eq_true, ite_false, ite_true]
  omega

/-- **Walsh support.** If `h` on `m + 2` cells flips with its first cell, and `h` with its first two cells white has
odd weight, `m ≥ 2`, then at least `2^m` Walsh coefficients of `h` are nonzero. -/
theorem walsh_support_of_flip (m : Nat) (hm : 2 ≤ m) (h : List Bool → Bool)
    (hf : ∀ x, h (true :: x) = !h (false :: x)) (hodd : cubeXor m (fun x => h (false :: false :: x)) = true) :
    2 ^ m ≤ cubeCount (m + 2) (fun a => cubeWalsh (m + 2) h a != 0) := by
  have hg := walsh_support_ge m (fun x => h (false :: x)) fun a _ =>
    cubeWalsh_ne_zero m hm _ hodd a
  refine Int.le_trans hg (Int.le_of_eq ?_)
  rw [cubeCount, cubeCount, show m + 2 = (m + 1) + 1 from rfl]
  conv => rhs; rw [cubeSum]
  have hz : cubeSum (m + 1) (fun a => if (cubeWalsh (m + 1 + 1) h (false :: a) != 0) then 1 else 0) = 0 :=
    Eq.trans (cubeSum_congr _ _ (fun _ => 0) fun a _ => by simp [(cubeWalsh_flip (m + 1) h hf a).1])
      (cubeSum_zero _)
  rw [hz, Int.zero_add]
  exact cubeSum_congr _ _ _ fun a _ => by
    rw [(cubeWalsh_flip (m + 1) h hf a).2]
    by_cases e : cubeWalsh (m + 1) (fun x => h (false :: x)) a = 0
    · simp [e]
    · have : 2 * cubeWalsh (m + 1) (fun x => h (false :: x)) a ≠ 0 := by omega
      simp [e, this]

/-! ## Rule 30 -/

/-- The row that carries the word `l` on the cells `-t, -t + 1, …` and is white elsewhere. -/
def coneWord (t : Nat) (l : List Bool) : Int → Bool := fun i =>
  if -(t : Int) ≤ i then l.getD (i + t).toNat false else false

/-- The center after `t` steps as a function of the word on its cone `x_{-t}, …, x_t`. -/
def coneFn (t : Nat) (l : List Bool) : Bool := evo (coneWord t l) t 0

/-- The center flips with the first cell of its cone. -/
theorem coneFn_flip (t : Nat) (x : List Bool) : coneFn t (true :: x) = !coneFn t (false :: x) := by
  have e : coneWord t (true :: x) = flipAt (coneWord t (false :: x)) (-t) := by
    funext i
    simp only [coneWord, flipAt]
    by_cases hi : i = -(t : Int)
    · subst hi
      rw [show -(t : Int) + t = 0 by omega]
      simp
    · simp only [hi, ite_false]
      by_cases h2 : -(t : Int) ≤ i
      · obtain ⟨k, hk⟩ : ∃ k : Nat, (i + t).toNat = k + 1 := ⟨(i + t).toNat - 1, by omega⟩
        simp [h2, hk]
      · simp [h2]
  rw [coneFn, e, flip_center]
  rfl

/-- **The restricted center has Walsh coefficients 2 mod 4.** For `t ≥ 2`, if the center with `x_{-t}`, `x_{-t+1}`
white has odd weight on the `2t - 1` cells `x_{-t+2}, …, x_t` (the kit's `coef_center_top`), each of its Walsh
coefficients is `2` mod `4`. -/
theorem center_walsh_emod_four (t : Nat) (ht : 2 ≤ t)
    (hodd : cubeXor (2 * t - 1) (fun x => coneFn t (false :: false :: x)) = true) (a : List Bool) :
    cubeWalsh (2 * t - 1) (fun x => coneFn t (false :: false :: x)) a % 4 = 2 :=
  cubeWalsh_emod_four _ (by omega) _ hodd a

/-- **The XOR lift of the restricted center is invertible over GF(2)**, of rank `2^(2t-1)`, under the same
hypothesis. -/
theorem center_lift_sq (t : Nat) (hodd : cubeXor (2 * t - 1) (fun x => coneFn t (false :: false :: x)) = true)
    (x z : List Bool) (hx : x.length = 2 * t - 1) (hz : z.length = 2 * t - 1) :
    cubeXor (2 * t - 1) (fun y => coneFn t (false :: false :: wordXor x y) &&
      coneFn t (false :: false :: wordXor y z)) = decide (x = z) :=
  lift_sq _ (fun x => coneFn t (false :: false :: x)) hodd x z hx hz

/-- **Walsh support of the center.** For `t ≥ 2`, under the same hypothesis, at least `2^(2t-1)` of the `2^(2t+1)`
Walsh coefficients of the center on its cone are nonzero. -/
theorem center_walsh_support (t : Nat) (ht : 2 ≤ t)
    (hodd : cubeXor (2 * t - 1) (fun x => coneFn t (false :: false :: x)) = true) :
    2 ^ (2 * t - 1) ≤ cubeCount (2 * t + 1) (fun a => cubeWalsh (2 * t + 1) (coneFn t) a != 0) := by
  have := walsh_support_of_flip (2 * t - 1) (by omega) (coneFn t) (coneFn_flip t) hodd
  rwa [show 2 * t - 1 + 2 = 2 * t + 1 by omega] at this

/-- The hypothesis checked by evaluation for `t = 2, 3, 4, 5`. -/
theorem center_odd_small :
    cubeXor 3 (fun x => coneFn 2 (false :: false :: x)) = true ∧
      cubeXor 5 (fun x => coneFn 3 (false :: false :: x)) = true ∧
      cubeXor 7 (fun x => coneFn 4 (false :: false :: x)) = true ∧
      cubeXor 9 (fun x => coneFn 5 (false :: false :: x)) = true := by
  decide +kernel

end Rule30Open
