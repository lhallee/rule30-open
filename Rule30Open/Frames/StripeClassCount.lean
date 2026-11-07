module

public import Rule30Open.Frames.StripeClasses

/-!
# The stripe-class count identity

`S01 B x y`: the kit's stripe relation at time 0 (`StripeRelated x y B`), or equal cell 0 (bit `B`) and the stripe
relation one step later (`StripeRelated (Phi x) (Phi y) (B + 1)`); `BoxS01 A B` is `S01` between rows supported in
`[-A, B]`, and `Joined` is the equivalence closure of a relation.

* `rep_of_stripeRelated`, `rep_of_stripeRelated_one`, `rep_of_S01`: the representative `rep B` (one step to a row with
  cell `B` black, as in `StripeClasses`) is constant on `S01` pairs. A valid time-0 cut `j` sends a row to the row with
  bits `0 .. j` replaced by `stripeLow (j + 1)` (`rep_of_cut`); a valid time-1 cut first inverts one step on a stripe
  word (`tail_of_Phi_stripe`: the preimages of the stripe words of length `n` are `0^(n-1) 1` and a stripe word of
  length `n - 1` followed by a white bit, read from bit 0).
* `joined_iff`: on the box, two rows are joined by `S01` iff they have the same representative.
* `s01_class_count`: for `A, B >= 1` the `S01` classes of the box are exactly the classes of the
  `2^(A+B) + 3 * 2^(A-1)` rows `boxRep A B i`, pairwise not joined.

The natural-language argument is `StripeClassCount.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

open Ruliology.CellularAutomata.Rule30StripeMeeting

namespace StripeClasses

/-! ## The lowest black bit -/

/-- The lowest black bit of `x` (0 for `x = 0`). -/
def lowbit (x : Nat) : Nat :=
  if h : x = 0 then 0 else if x % 2 = 1 then 0 else lowbit (x / 2) + 1
termination_by x
decreasing_by omega

theorem lowbit_spec : ∀ m H x, x = 2 ^ (m + 1) * H + 2 ^ m → lowbit x = m
  | 0, H, x, e => by
    rw [show 2 ^ (0 + 1) = 2 from rfl, show 2 ^ 0 = 1 from rfl] at e
    unfold lowbit
    rw [dite_eq_right (by omega), ite_eq_left (by omega)]
  | m + 1, H, x, e => by
    have e2 : 2 ^ (m + 1 + 1) = 2 * 2 ^ (m + 1) := by rw [Nat.pow_succ]; omega
    have e1 : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [Nat.pow_succ]; omega
    have hpos : 0 < 2 ^ m := Nat.two_pow_pos m
    have hx : x = 2 * (2 ^ (m + 1) * H + 2 ^ m) := by
      rw [e, e2, e1, Nat.mul_add, Nat.mul_assoc]
    have ih := lowbit_spec m H (x / 2) (by omega)
    unfold lowbit
    rw [dite_eq_right (by omega), ite_eq_right (by omega), ih]

/-! ## The representative -/

/-- The representative of the row `x` in the frame with center index `B`: one `S01` step to a row with bit 0 black
when the right half (bits `0 .. B - 1`) is nonempty or the left part ends in `0 1`; the row itself otherwise. -/
def rep (B x : Nat) : Nat :=
  if x = 0 then 0
  else if lowbit x = 0 then x
  else if B < lowbit x then x
  else if x.testBit (lowbit x + 1) = false then x - 2 ^ lowbit x + stripeLow (lowbit x + 1)
  else if lowbit x < B then x - 2 ^ lowbit x + stripeLow (lowbit x)
  else x

theorem pow_lt_pow_succ (m : Nat) : 2 ^ m < 2 ^ (m + 1) := Nat.pow_lt_pow_right (by decide) (by omega)

theorem testBit_low_form (m H : Nat) : (2 ^ (m + 1) * H + 2 ^ m).testBit (m + 1) = decide (H % 2 = 1) := by
  rw [testBit_hi (pow_lt_pow_succ m) (by omega), Nat.sub_self, Nat.testBit_zero]

theorem rep_zero_move (B m H : Nat) (hm1 : 1 ≤ m) (hmB : m ≤ B) (hH : H % 2 = 0) :
    rep B (2 ^ (m + 1) * H + 2 ^ m) = 2 ^ (m + 1) * H + stripeLow (m + 1) := by
  have hl := lowbit_spec m H _ rfl
  have hpos : 0 < 2 ^ m := Nat.two_pow_pos m
  unfold rep
  rw [ite_eq_right (by omega), hl, ite_eq_right (by omega), ite_eq_right (by omega), testBit_low_form,
    ite_eq_left (by simp [hH])]
  omega

theorem rep_one_move (B m H : Nat) (hm1 : 1 ≤ m) (hmB : m < B) (hH : H % 2 = 1) :
    rep B (2 ^ (m + 1) * H + 2 ^ m) = 2 ^ (m + 1) * H + stripeLow m := by
  have hl := lowbit_spec m H _ rfl
  have hpos : 0 < 2 ^ m := Nat.two_pow_pos m
  unfold rep
  rw [ite_eq_right (by omega), hl, ite_eq_right (by omega), ite_eq_right (by omega), testBit_low_form,
    ite_eq_right (by simp [hH]), ite_eq_left hmB]
  omega

theorem rep_odd (B x : Nat) (hx : x % 2 = 1) : rep B x = x := by
  have hl : lowbit x = 0 := lowbit_spec 0 (x / 2) x (by
    rw [show 2 ^ (0 + 1) = 2 from rfl, show 2 ^ 0 = 1 from rfl]; omega)
  unfold rep
  rw [ite_eq_right (by omega), hl, ite_eq_left rfl]

/-! ## Stripe words as bits -/

theorem rowBits_length (a n : Nat) : (rowBits a n).length = n := by
  simp [rowBits]

theorem testBit_mem_rowBits {a n i : Nat} (hi : i < n) : a.testBit i ∈ rowBits a n :=
  List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩

theorem zero_bits_of_rowBits {a n : Nat} {zs : List Bool} (h : rowBits a n = zs) (hz : ZeroWord zs) :
    ∀ i, i < n → a.testBit i = false := by
  intro i hi
  exact hz _ (h ▸ testBit_mem_rowBits hi)

theorem rowBits_split1 {a n : Nat} {L : List Bool} {b : Bool} (h : rowBits a (n + 1) = L ++ [b]) :
    rowBits a n = L ∧ a.testBit n = b := by
  rw [rowBits_succ] at h
  have := List.append_inj' h rfl
  exact ⟨this.1, by simpa using this.2⟩

theorem rowBits_split2 {a n : Nat} {L : List Bool} {b c : Bool} (h : rowBits a (n + 2) = L ++ [b, c]) :
    rowBits a n = L ∧ a.testBit n = b ∧ a.testBit (n + 1) = c := by
  rw [rowBits_succ, rowBits_succ, List.append_assoc] at h
  have := List.append_inj' h rfl
  refine ⟨this.1, ?_, ?_⟩
  · have h2 := this.2
    simp only [List.cons_append, List.nil_append, List.cons.injEq] at h2
    exact h2.1
  · have h2 := this.2
    simp only [List.cons_append, List.nil_append, List.cons.injEq] at h2
    exact h2.2.1

theorem stripeWord_ne_nil {L : List Bool} (h : StripeWord L) : L ≠ [] := by
  cases h <;> simp

theorem stripeWord_last {L : List Bool} (h : StripeWord L) : ∃ L', L = L' ++ [true] := by
  cases h with
  | single zs hz => exact ⟨zs, rfl⟩
  | double zs hz => exact ⟨zs ++ [true], by simp⟩
  | extend h' => rename_i xs; exact ⟨xs ++ [false], by simp⟩

/-- The last letter of a stripe word is black: in bits, a row whose bits `0 .. n - 1` form a stripe word has bit
`n - 1` black. -/
theorem stripeWord_top {a n : Nat} (h : StripeWord (rowBits a n)) : 1 ≤ n ∧ a.testBit (n - 1) = true := by
  have hn : 1 ≤ n := by
    have := stripeWord_ne_nil h
    rcases n with _ | n
    · simp [rowBits] at this
    · omega
  refine ⟨hn, ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  obtain ⟨L', hL'⟩ := stripeWord_last h
  rw [Nat.add_sub_cancel]
  exact (rowBits_split1 hL').2

/-- **A valid time-0 cut fixes the representative.** If bits `0 .. j` of `x` form a stripe word, bit `j + 1` is
white and `j <= B`, then `rep B x` is `x` with bits `0 .. j` replaced by `stripeLow (j + 1)`. -/
theorem rep_of_cut (B : Nat) : ∀ (L : List Bool), StripeWord L → ∀ x j, rowBits x (j + 1) = L →
    x.testBit (j + 1) = false → j ≤ B → rep B x = 2 ^ (j + 1) * (x / 2 ^ (j + 1)) + stripeLow (j + 1) := by
  intro L hL
  induction hL with
  | single zs hz =>
    intro x j hr hj1 hjB
    obtain ⟨hlow, hj⟩ := rowBits_split1 hr
    have hzero := zero_bits_of_rowBits hlow hz
    -- x = 2^(j+1) * H + 2^j with H even
    have hxe : x = 2 ^ (j + 1) * (x / 2 ^ (j + 1)) + 2 ^ j := by
      have hm : x % 2 ^ (j + 1) = 2 ^ j := by
        apply Nat.eq_of_testBit_eq
        intro i
        rw [Nat.testBit_mod_two_pow, testBit_pow]
        by_cases hi : i < j
        · rw [decide_eq_true (by omega : i < j + 1), hzero i hi, decide_eq_false (by omega)]; rfl
        · by_cases hij : i = j
          · subst hij; rw [decide_eq_true (by omega), hj, decide_eq_true rfl]; rfl
          · rw [decide_eq_false (by omega), decide_eq_false hij]; rfl
      have := Nat.div_add_mod x (2 ^ (j + 1))
      omega
    have hH : (x / 2 ^ (j + 1)) % 2 = 0 := by
      have := hj1
      rw [hxe, testBit_low_form] at this
      simpa using this
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · subst h0
      have hodd : x % 2 = 1 := by
        rw [hxe, show 2 ^ (0 + 1) = 2 from rfl, show 2 ^ 0 = 1 from rfl]; omega
      rw [rep_odd B x hodd]
      show x = 2 ^ (0 + 1) * (x / 2 ^ (0 + 1)) + 1
      rw [show 2 ^ (0 + 1) = 2 from rfl]; omega
    · conv => lhs; rw [hxe]
      exact rep_zero_move B j _ h0 hjB hH
  | double zs hz =>
    intro x j hr hj1 hjB
    have hlen := congrArg List.length hr
    rw [rowBits_length, List.length_append] at hlen
    simp only [List.length_cons, List.length_nil] at hlen
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    obtain ⟨hlow, hk, hk1⟩ := rowBits_split2 (show rowBits x (k + 2) = zs ++ [true, true] from hr)
    have hzero := zero_bits_of_rowBits hlow hz
    -- x = 2^(k+1) * H + 2^k with H = 2 q + 1, q = x / 2^(k+2)
    have hxe : x = 2 ^ (k + 1) * (2 * (x / 2 ^ (k + 2)) + 1) + 2 ^ k := by
      have hm : x % 2 ^ (k + 2) = 2 ^ (k + 1) + 2 ^ k := by
        apply Nat.eq_of_testBit_eq
        intro i
        rw [Nat.testBit_mod_two_pow, show 2 ^ (k + 1) + 2 ^ k = 2 ^ (k + 1) * 1 + 2 ^ k by omega,
          Nat.testBit_two_pow_mul_add 1 (pow_lt_pow_succ k) i]
        by_cases hi : i < k
        · rw [decide_eq_true (by omega : i < k + 2), hzero i hi, ite_eq_left (by omega), testBit_pow,
            decide_eq_false (by omega)]; rfl
        · by_cases hik : i = k
          · subst hik; rw [decide_eq_true (by omega), hk, ite_eq_left (by omega), testBit_pow, decide_eq_true rfl]; rfl
          · by_cases hik1 : i = k + 1
            · subst hik1
              rw [decide_eq_true (by omega), hk1, ite_eq_right (by omega), Nat.sub_self]; rfl
            · rw [decide_eq_false (by omega), ite_eq_right (by omega),
                show (1 : Nat) = 2 ^ 0 from rfl, testBit_pow, decide_eq_false (by omega)]; rfl
      have h1 := Nat.div_add_mod x (2 ^ (k + 2))
      have e2 : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by rw [Nat.pow_succ]; omega
      rw [e2] at h1 hm ⊢
      rw [Nat.mul_add, Nat.mul_one, ← Nat.mul_assoc, Nat.mul_comm (2 ^ (k + 1)) 2]
      omega
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0
      have hodd : x % 2 = 1 := by
        rw [hxe, show 2 ^ (0 + 1) = 2 from rfl, show 2 ^ 0 = 1 from rfl]; omega
      rw [rep_odd B x hodd]
      show x = 2 ^ 2 * (x / 2 ^ 2) + 3
      have h1 := Nat.div_add_mod x 4
      have : x % 4 = 3 := by
        rw [hxe, show 2 ^ (0 + 1) = 2 from rfl, show 2 ^ 0 = 1 from rfl]; omega
      rw [show 2 ^ 2 = 4 from rfl]; omega
    · conv => lhs; rw [hxe]
      rw [rep_one_move B k _ h0 (by omega) (by omega)]
      -- 2^(k+1) (2q+1) + stripeLow k = 2^(k+2) q + stripeLow (k+2)
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      show _ = 2 ^ (k' + 1 + 1 + 1) * (x / 2 ^ (k' + 1 + 1 + 1)) + (stripeLow (k' + 1) + 2 ^ (k' + 2))
      have e3 : 2 ^ (k' + 1 + 1 + 1) = 2 * 2 ^ (k' + 2) := by rw [Nat.pow_succ]; omega
      rw [e3, show k' + 1 + 1 = k' + 2 by omega, Nat.mul_add, Nat.mul_one, ← Nat.mul_assoc,
        Nat.mul_comm (2 ^ (k' + 2)) 2]
      omega
  | extend h ih =>
    rename_i xs
    intro x j hr hj1 hjB
    have hlen := congrArg List.length hr
    rw [rowBits_length, List.length_append] at hlen
    simp only [List.length_cons, List.length_nil] at hlen
    have hxs := stripeWord_ne_nil h
    have hxs1 : 1 ≤ xs.length := by
      rcases xs with _ | _
      · exact absurd rfl hxs
      · simp
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
    obtain ⟨hlow, hk, hk1⟩ := rowBits_split2 (show rowBits x (k + 1 + 2) = xs ++ [false, true] by
      rw [show k + 1 + 2 = k + 2 + 1 by omega]; exact hr)
    have hrec := ih x k hlow hk (by omega)
    rw [hrec]
    -- x / 2^(k+1) = 4 (x / 2^(k+3)) + 2, and stripeLow (k+3) = stripeLow (k+1) + 2^(k+2)
    have hq : x / 2 ^ (k + 1) = 4 * (x / 2 ^ (k + 3)) + 2 := by
      have hd : x / 2 ^ (k + 3) = (x / 2 ^ (k + 1)) / 4 := by
        rw [Nat.div_div_eq_div_mul]
        congr 1
        rw [show k + 3 = (k + 1) + 2 by omega, Nat.pow_add]
      have hb0 : (x / 2 ^ (k + 1)) % 2 = 0 := by
        have := hk
        rw [show k + 1 = 0 + (k + 1) by omega, ← Nat.testBit_div_two_pow, Nat.testBit_zero] at this
        simpa using this
      have hb1 : (x / 2 ^ (k + 1) / 2) % 2 = 1 := by
        have := hk1
        rw [show k + 1 + 1 = 1 + (k + 1) by omega, ← Nat.testBit_div_two_pow, Nat.testBit_succ,
          Nat.testBit_zero] at this
        simpa using this
      rw [hd]
      omega
    rw [hq, show k + 2 + 1 = k + 3 by omega]
    show _ = 2 ^ (k + 3) * (x / 2 ^ (k + 3)) + (stripeLow (k + 1) + 2 ^ (k + 2))
    have e3 : 2 ^ (k + 3) = 4 * 2 ^ (k + 1) := by
      rw [show k + 3 = (k + 1) + 2 by omega, Nat.pow_add]; omega
    have e2 : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by rw [Nat.pow_succ]; omega
    rw [e3, e2, Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm (2 ^ (k + 1)) 4]
    omega

/-- **The time-0 stripe relation fixes the representative.** -/
theorem rep_of_stripeRelated {B x y : Nat} (h : StripeRelated x y B) : rep B x = rep B y := by
  rcases h with he | ⟨j, hjB, hsx, hsy, _, _, hzx, hzy, hs⟩
  · rw [he]
  · rw [rep_of_cut B _ hsx x j rfl hzx hjB, rep_of_cut B _ hsy y j rfl hzy hjB]
    congr 2
    apply div_eq_of_testBit
    intro i hi
    by_cases h1 : i = j + 1
    · rw [h1, hzx, hzy]
    · exact hs i (by omega)

/-! ## Inverting one step on a stripe word -/

/-- Rule 30 is left-permutive: in the frame, bit `i` of a row follows from bit `i` of its image and its own bits
`i - 1`, `i - 2`. -/
theorem bit_of_Phi (x i : Nat) : x.testBit i =
    xor ((Phi x).testBit i) ((decide (0 < i) && x.testBit (i - 1)) || (decide (1 < i) && x.testBit (i - 2))) := by
  rw [Phi_bit]
  cases x.testBit i <;> cases ((decide (0 < i) && x.testBit (i - 1)) || (decide (1 < i) && x.testBit (i - 2))) <;> rfl

theorem zero_bits_of_Phi {x k : Nat} (h : ∀ i, i < k → (Phi x).testBit i = false) :
    ∀ i, i < k → x.testBit i = false := by
  intro i
  induction i using Nat.strongRecOn with
  | ind i ih =>
    intro hi
    rw [bit_of_Phi, h i hi]
    by_cases h0 : i = 0
    · subst h0; rfl
    · by_cases h1 : i = 1
      · subst h1
        rw [ih 0 (by omega) (by omega)]; rfl
      · rw [ih (i - 1) (by omega) (by omega), ih (i - 2) (by omega) (by omega)]
        simp

theorem Phi_inj {x y : Nat} (h : Phi x = Phi y) : x = y := by
  apply Nat.eq_of_testBit_eq
  intro i
  induction i using Nat.strongRecOn with
  | ind i ih =>
    rw [bit_of_Phi x i, bit_of_Phi y i, h]
    by_cases h0 : i = 0
    · subst h0; rfl
    · by_cases h1 : i = 1
      · subst h1; rw [ih 0 (by omega)]
      · rw [ih (i - 1) (by omega), ih (i - 2) (by omega)]

end StripeClasses

/-- **One step maps the tails `T_n` onto the stripe words** (the inverse direction): if bits `0 .. n - 1` of the image
form a stripe word, bits `0 .. n - 1` of the row are `0^(n-1) 1` (a black cell followed by white cells), or a stripe
word on bits `0 .. n - 2` followed by a white bit `n - 1`. -/
theorem StripeClasses.tail_of_Phi_stripe : ∀ (L : List Bool), StripeWord L → ∀ x n, rowBits (Phi x) n = L →
    (1 ≤ n ∧ (∀ i, i < n - 1 → x.testBit i = false) ∧ x.testBit (n - 1) = true) ∨
    (2 ≤ n ∧ x.testBit (n - 1) = false ∧ StripeWord (rowBits x (n - 1))) := by
  intro L hL
  induction hL with
  | single zs hz =>
    intro x n hr
    have hlen := congrArg List.length hr
    rw [rowBits_length, List.length_append] at hlen
    simp only [List.length_cons, List.length_nil] at hlen
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    obtain ⟨hlow, hk⟩ := rowBits_split1 hr
    have hz' := zero_bits_of_Phi (zero_bits_of_rowBits hlow hz)
    left
    refine ⟨by omega, fun i hi => hz' i (by omega), ?_⟩
    rw [Nat.add_sub_cancel, bit_of_Phi, hk]
    by_cases h0 : k = 0
    · subst h0; rfl
    · by_cases h1 : k = 1
      · subst h1; rw [hz' 0 (by omega)]; rfl
      · rw [hz' (k - 1) (by omega), hz' (k - 2) (by omega)]; simp
  | double zs hz =>
    intro x n hr
    have hlen := congrArg List.length hr
    rw [rowBits_length, List.length_append] at hlen
    simp only [List.length_cons, List.length_nil] at hlen
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    obtain ⟨hlow, hk, hk1⟩ := rowBits_split2 hr
    have hz' := zero_bits_of_Phi (zero_bits_of_rowBits hlow hz)
    have hxk : x.testBit k = true := by
      rw [bit_of_Phi, hk]
      by_cases h0 : k = 0
      · subst h0; rfl
      · by_cases h1 : k = 1
        · subst h1; rw [hz' 0 (by omega)]; rfl
        · rw [hz' (k - 1) (by omega), hz' (k - 2) (by omega)]; simp
    have hxk1 : x.testBit (k + 1) = false := by
      rw [bit_of_Phi, hk1, show k + 1 - 1 = k by omega, hxk, decide_eq_true (by omega : 0 < k + 1)]
      simp
    right
    refine ⟨by omega, by rw [show k + 2 - 1 = k + 1 by omega]; exact hxk1, ?_⟩
    rw [show k + 2 - 1 = k + 1 by omega]
    exact stripeWord_single_bit hz' hxk
  | extend h ih =>
    rename_i xs
    intro x n hr
    have hlen := congrArg List.length hr
    rw [rowBits_length, List.length_append] at hlen
    simp only [List.length_cons, List.length_nil] at hlen
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    obtain ⟨hlow, hk, hk1⟩ := rowBits_split2 hr
    rcases ih x k hlow with ⟨hk1', hz, htop⟩ | ⟨hk2, hw, hs⟩
    · -- the row ends 0^(k-1) 1 on bits 0 .. k - 1; then bits k, k + 1 are 1, 0
      have hxk : x.testBit k = true := by
        rw [bit_of_Phi, hk, decide_eq_true (by omega : 0 < k), htop]
        simp
      have hxk1 : x.testBit (k + 1) = false := by
        rw [bit_of_Phi, hk1, show k + 1 - 1 = k by omega, hxk, decide_eq_true (by omega : 0 < k + 1)]
        simp
      right
      refine ⟨by omega, by rw [show k + 2 - 1 = k + 1 by omega]; exact hxk1, ?_⟩
      rw [show k + 2 - 1 = k + 1 by omega]
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have htop' : x.testBit k' = true := by simpa using htop
      have hz2 : ∀ i, i < k' → x.testBit i = false := fun i hi => hz i (by omega)
      rw [rowBits_succ, rowBits_succ, rowBits_zeros hz2, htop', hxk, List.append_assoc]
      exact StripeWord.double _ (fun b hb => List.eq_of_mem_replicate hb)
    · -- a stripe word on bits 0 .. k - 2 and a white bit k - 1; then bits k, k + 1 are 1, 0
      have htop := (stripeWord_top hs).2
      have hxk : x.testBit k = true := by
        rw [bit_of_Phi, hk, decide_eq_true (by omega : 0 < k), decide_eq_true (by omega : 1 < k),
          show k - 2 = k - 1 - 1 by omega, htop]
        simp
      have hxk1 : x.testBit (k + 1) = false := by
        rw [bit_of_Phi, hk1, show k + 1 - 1 = k by omega, hxk, decide_eq_true (by omega : 0 < k + 1)]
        simp
      right
      refine ⟨by omega, by rw [show k + 2 - 1 = k + 1 by omega]; exact hxk1, ?_⟩
      rw [show k + 2 - 1 = k + 1 by omega]
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have hw' : x.testBit k' = false := by simpa using hw
      have hs' : StripeWord (rowBits x k') := by simpa using hs
      rw [rowBits_succ, rowBits_succ, hw', hxk, List.append_assoc]
      exact StripeWord.extend hs'

namespace StripeClasses

/-! ## The time-1 relation fixes the representative -/

/-- Above a time-1 cut the rows agree: bit `j + 1` is black in both, and each higher bit follows from the images. -/
theorem agree_above {x y j : Nat} (hs : ∀ i, j + 1 < i → (Phi x).testBit i = (Phi y).testBit i)
    (hx : x.testBit (j + 1) = true) (hy : y.testBit (j + 1) = true) :
    ∀ i, j + 1 ≤ i → x.testBit i = y.testBit i := by
  intro i
  induction i using Nat.strongRecOn with
  | ind i ih =>
    intro hi
    by_cases h1 : i = j + 1
    · rw [h1, hx, hy]
    · rw [bit_of_Phi x i, bit_of_Phi y i, hs i (by omega)]
      by_cases h2 : i = j + 2
      · rw [show i - 1 = j + 1 by omega, hx, hy, decide_eq_true (by omega : 0 < i)]
        simp
      · rw [ih (i - 1) (by omega) (by omega), ih (i - 2) (by omega) (by omega)]

/-- The bit just above a time-1 cut is black. -/
theorem black_above_cut {x j : Nat} (hz : (Phi x).testBit (j + 1) = false)
    (ht : (1 ≤ j + 1 ∧ (∀ i, i < j + 1 - 1 → x.testBit i = false) ∧ x.testBit (j + 1 - 1) = true) ∨
      (2 ≤ j + 1 ∧ x.testBit (j + 1 - 1) = false ∧ StripeWord (rowBits x (j + 1 - 1)))) :
    x.testBit (j + 1) = true := by
  rw [bit_of_Phi, hz, show j + 1 - 1 = j by omega, decide_eq_true (by omega : 0 < j + 1)]
  rcases ht with ⟨_, _, htop⟩ | ⟨h2, _, hs⟩
  · rw [show j + 1 - 1 = j by omega] at htop
    rw [htop]
    simp
  · have := (stripeWord_top hs).2
    rw [show j + 1 - 1 - 1 = j - 1 by omega] at this
    rw [show j + 1 - 2 = j - 1 by omega, this, decide_eq_true (by omega : 1 < j + 1)]
    simp

/-- A row with white bits below `m` and a black bit `m` is `2^(m+1) * H + 2^m`. -/
theorem low_form {x m : Nat} (hz : ∀ i, i < m → x.testBit i = false) (hm : x.testBit m = true) :
    x = 2 ^ (m + 1) * (x / 2 ^ (m + 1)) + 2 ^ m := by
  have h : x % 2 ^ (m + 1) = 2 ^ m := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_mod_two_pow, testBit_pow]
    by_cases hi : i < m
    · rw [decide_eq_true (by omega : i < m + 1), hz i hi, decide_eq_false (by omega)]; rfl
    · by_cases him : i = m
      · subst him; rw [decide_eq_true (by omega), hm, decide_eq_true rfl]; rfl
      · rw [decide_eq_false (by omega), decide_eq_false him]; rfl
  have := Nat.div_add_mod x (2 ^ (m + 1))
  omega

theorem rep_of_cut_one (B x j : Nat) (hj : 1 ≤ j) (hjB : j < B)
    (ht : (1 ≤ j + 1 ∧ (∀ i, i < j + 1 - 1 → x.testBit i = false) ∧ x.testBit (j + 1 - 1) = true) ∨
      (2 ≤ j + 1 ∧ x.testBit (j + 1 - 1) = false ∧ StripeWord (rowBits x (j + 1 - 1))))
    (hx1 : x.testBit (j + 1) = true) :
    rep B x = 2 ^ (j + 1) * (x / 2 ^ (j + 1)) + stripeLow j := by
  simp only [Nat.add_sub_cancel] at ht
  rcases ht with ⟨_, hz, htop⟩ | ⟨_, hw, hs⟩
  · have hxe := low_form hz htop
    have hH : (x / 2 ^ (j + 1)) % 2 = 1 := by
      have := hx1
      rw [hxe, testBit_low_form] at this
      simpa using this
    conv => lhs; rw [hxe]
    exact rep_one_move B j _ hj hjB hH
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    rw [rep_of_cut B _ hs x k rfl hw (by omega)]
    have hb : (x / 2 ^ (k + 1)) % 2 = 0 := by
      have := hw
      rw [show k + 1 = 0 + (k + 1) by omega, ← Nat.testBit_div_two_pow, Nat.testBit_zero] at this
      simpa using this
    have hd : x / 2 ^ (k + 1 + 1) = x / 2 ^ (k + 1) / 2 := by
      rw [Nat.div_div_eq_div_mul, Nat.pow_succ]
    rw [hd, show 2 ^ (k + 1 + 1) = 2 ^ (k + 1) * 2 from Nat.pow_succ 2 (k + 1)]
    generalize x / 2 ^ (k + 1) = q at hb ⊢
    rw [Nat.mul_assoc, show 2 * (q / 2) = q by omega]

/-- **The time-1 stripe relation, with equal cell 0, fixes the representative.** -/
theorem rep_of_stripeRelated_one {B x y : Nat} (hB : 1 ≤ B) (h0 : x.testBit B = y.testBit B)
    (h : StripeRelated (Phi x) (Phi y) (B + 1)) : rep B x = rep B y := by
  rcases h with he | ⟨j, hjB, hsx, hsy, _, _, hzx, hzy, hs⟩
  · rw [Phi_inj he]
  · have tx := tail_of_Phi_stripe _ hsx x (j + 1) rfl
    have ty := tail_of_Phi_stripe _ hsy y (j + 1) rfl
    have bx := black_above_cut hzx tx
    have by' := black_above_cut hzy ty
    have hag := agree_above hs bx by'
    simp only [Nat.add_sub_cancel] at tx ty
    -- two rows whose bits 0 .. j are 0^j 1 and which agree above j are equal
    have heq : (∀ i, i < j → x.testBit i = false) → x.testBit j = true →
        (∀ i, i < j → y.testBit i = false) → y.testBit j = true → x = y := by
      intro hzx' hx hzy' hy
      apply Nat.eq_of_testBit_eq
      intro i
      by_cases hi : i < j
      · rw [hzx' i hi, hzy' i hi]
      · by_cases hij : i = j
        · rw [hij, hx, hy]
        · exact hag i (by omega)
    by_cases hlt : j < B
    · by_cases hj0 : j = 0
      · subst hj0
        rcases tx with ⟨_, hzx', hx⟩ | ⟨h2, _, _⟩
        · rcases ty with ⟨_, hzy', hy⟩ | ⟨h2, _, _⟩
          · rw [heq hzx' hx hzy' hy]
          · omega
        · omega
      · rw [rep_of_cut_one B x j (by omega) hlt (by simpa using tx) bx,
          rep_of_cut_one B y j (by omega) hlt (by simpa using ty) by']
        congr 2
        exact div_eq_of_testBit hag
    · by_cases hjeq : j = B
      · subst hjeq
        rcases tx with ⟨_, hzx', hx⟩ | ⟨_, hwx, hsx'⟩ <;> rcases ty with ⟨_, hzy', hy⟩ | ⟨_, hwy, hsy'⟩
        · rw [heq hzx' hx hzy' hy]
        · rw [hx, hwy] at h0; exact absurd h0 (by decide)
        · rw [hwx, hy] at h0; exact absurd h0 (by decide)
        · -- both rows carry a stripe word on bits 0 .. j - 1 and a white bit j: time-0 related
          apply rep_of_stripeRelated
          obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
          refine Or.inr ⟨k, by omega, hsx', hsy', ?_, ?_, hwx, hwy, ?_⟩
          · simpa using (stripeWord_top hsx').2
          · simpa using (stripeWord_top hsy').2
          · intro i hi; exact hag i (by omega)
      · have hjeq' : j = B + 1 := by omega
        subst hjeq'
        rcases tx with ⟨_, hzx', hx⟩ | ⟨_, hwx, hsx'⟩ <;> rcases ty with ⟨_, hzy', hy⟩ | ⟨_, hwy, hsy'⟩
        · rw [heq hzx' hx hzy' hy]
        · rw [hzx' B (by omega), (by simpa using (stripeWord_top hsy').2 : y.testBit B = true)] at h0
          exact absurd h0 (by decide)
        · rw [hzy' B (by omega), (by simpa using (stripeWord_top hsx').2 : x.testBit B = true)] at h0
          exact absurd h0 (by decide)
        · apply rep_of_stripeRelated
          refine Or.inr ⟨B, Nat.le_refl B, hsx', hsy', ?_, ?_, hwx, hwy, ?_⟩
          · simpa using (stripeWord_top hsx').2
          · simpa using (stripeWord_top hsy').2
          · intro i hi; exact hag i (by omega)

/-! ## The classes -/

/-- The relation `S01`: stripe-related at time 0, or equal cell 0 and stripe-related at time 1. -/
def S01 (B x y : Nat) : Prop :=
  StripeRelated x y B ∨ (x.testBit B = y.testBit B ∧ StripeRelated (Phi x) (Phi y) (B + 1))

end StripeClasses

theorem StripeClasses.rep_of_S01 {B x y : Nat} (hB : 1 ≤ B) (h : S01 B x y) : rep B x = rep B y := by
  rcases h with h | ⟨h0, h1⟩
  · exact rep_of_stripeRelated h
  · exact rep_of_stripeRelated_one hB h0 h1

namespace StripeClasses

/-- Every row is `S01`-related to its representative. -/
theorem S01_rep (B x : Nat) : S01 B x (rep B x) := by
  by_cases hx0 : x = 0
  · subst hx0
    exact Or.inl (Or.inl (by unfold rep; simp))
  obtain ⟨m, H, e⟩ := exists_lowbit x hx0
  have hl := lowbit_spec m H x e
  have hpos : 0 < 2 ^ m := Nat.two_pow_pos m
  by_cases hm0 : m = 0
  · subst hm0
    have hodd : x % 2 = 1 := by
      rw [e, show 2 ^ (0 + 1) = 2 from rfl, show 2 ^ 0 = 1 from rfl]; omega
    rw [rep_odd B x hodd]
    exact Or.inl (Or.inl rfl)
  by_cases hmB : B < m
  · have : rep B x = x := by
      unfold rep
      rw [ite_eq_right hx0, hl, ite_eq_right hm0, ite_eq_left hmB]
    rw [this]
    exact Or.inl (Or.inl rfl)
  rcases Nat.mod_two_eq_zero_or_one H with hH | hH
  · rw [e, rep_zero_move B m H (by omega) (by omega) hH]
    exact Or.inl (time_zero_move H m B hH (by omega))
  · by_cases hmB' : m < B
    · rw [e, rep_one_move B m H (by omega) hmB' hH]
      exact Or.inr (time_one_move H m B hH (by omega) (by omega))
    · have : rep B x = x := by
        unfold rep
        rw [ite_eq_right hx0, hl, ite_eq_right hm0, ite_eq_right hmB, e, testBit_low_form, decide_eq_true hH,
          ite_eq_right (by simp), ite_eq_right hmB']
      rw [this]
      exact Or.inl (Or.inl rfl)

/-- The equivalence closure of a relation: chains of steps taken in either direction. -/
inductive Joined (R : Nat → Nat → Prop) : Nat → Nat → Prop
  | refl (x : Nat) : Joined R x x
  | tail {x y z : Nat} : Joined R x y → (R y z ∨ R z y) → Joined R x z

theorem Joined.single {R : Nat → Nat → Prop} {x y : Nat} (h : R x y) : Joined R x y :=
  Joined.tail (Joined.refl x) (Or.inl h)

theorem Joined.trans {R : Nat → Nat → Prop} {x y z : Nat} (h1 : Joined R x y) (h2 : Joined R y z) :
    Joined R x z := by
  induction h2 with
  | refl => exact h1
  | tail _ hs ih => exact Joined.tail ih hs

theorem Joined.symm {R : Nat → Nat → Prop} {x y : Nat} (h : Joined R x y) : Joined R y x := by
  induction h with
  | refl => exact Joined.refl _
  | @tail b c _ hs ih =>
    have hcb : Joined R c b := Joined.tail (Joined.refl c) hs.symm
    exact hcb.trans ih

/-- `S01` between two rows of the box `[-A, B]`. -/
def BoxS01 (A B x y : Nat) : Prop := x < 2 ^ (A + B + 1) ∧ y < 2 ^ (A + B + 1) ∧ S01 B x y

/-- The representative of a row of the box lies in the box. -/
theorem rep_lt (A B x : Nat) (hx : x < 2 ^ (A + B + 1)) : rep B x < 2 ^ (A + B + 1) := by
  by_cases hx0 : x = 0
  · subst hx0; unfold rep; simpa using hx
  obtain ⟨m, H, e⟩ := exists_lowbit x hx0
  have hl := lowbit_spec m H x e
  -- rep agrees with x on every bit above m
  have key : ∀ W, W < 2 ^ (m + 1) → m + 1 ≤ A + B + 1 → 2 ^ (m + 1) * H + W < 2 ^ (A + B + 1) := by
    intro W hW hm
    apply Nat.lt_pow_two_of_testBit
    intro i hi
    rw [testBit_hi hW (by omega)]
    have := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) hi))
    rw [e, testBit_hi (pow_lt_pow_succ m) (by omega)] at this
    exact this
  unfold rep
  rw [ite_eq_right hx0, hl]
  by_cases hm0 : m = 0
  · rw [ite_eq_left hm0]; exact hx
  rw [ite_eq_right hm0]
  by_cases hmB : B < m
  · rw [ite_eq_left hmB]; exact hx
  rw [ite_eq_right hmB]
  have hpos : 0 < 2 ^ m := Nat.two_pow_pos m
  by_cases hb : x.testBit (m + 1) = false
  · rw [ite_eq_left hb, e, show 2 ^ (m + 1) * H + 2 ^ m - 2 ^ m = 2 ^ (m + 1) * H by omega]
    exact key _ (stripeLow_lt (m + 1)) (by omega)
  · rw [ite_eq_right hb]
    by_cases hmB' : m < B
    · rw [ite_eq_left hmB', e, show 2 ^ (m + 1) * H + 2 ^ m - 2 ^ m = 2 ^ (m + 1) * H by omega]
      exact key _ (Nat.lt_trans (stripeLow_lt m) (pow_lt_pow_succ m)) (by omega)
    · rw [ite_eq_right hmB']; exact hx

end StripeClasses

/-- **The classes of `S01` on the box are the fibers of `rep`.** -/
theorem StripeClasses.joined_iff (A B : Nat) (hB : 1 ≤ B) {x y : Nat} (hx : x < 2 ^ (A + B + 1))
    (hy : y < 2 ^ (A + B + 1)) :
    Joined (BoxS01 A B) x y ↔ rep B x = rep B y := by
  constructor
  · intro h
    clear hy
    induction h with
    | refl => rfl
    | tail _ hs ih =>
      rcases hs with ⟨_, _, h⟩ | ⟨_, _, h⟩
      · rw [ih, rep_of_S01 hB h]
      · rw [ih, rep_of_S01 hB h]
  · intro h
    have h1 : Joined (BoxS01 A B) x (rep B x) := Joined.single ⟨hx, rep_lt A B x hx, S01_rep B x⟩
    have h2 : Joined (BoxS01 A B) y (rep B y) := Joined.single ⟨hy, rep_lt A B y hy, S01_rep B y⟩
    rw [h] at h1
    exact h1.trans h2.symm

namespace StripeClasses

/-! ## Counting the representatives -/

theorem stripeLow_odd (n : Nat) (hn : 1 ≤ n) : stripeLow n % 2 = 1 := by
  have h := stripeLow_testBit n 0
  rw [Nat.testBit_zero, decide_eq_true (show 0 < n ∧ (0 = 0 ∨ (0 + n) % 2 = 1) by omega)] at h
  simpa using h

theorem low_odd (m H W : Nat) (hW : W % 2 = 1) : (2 ^ (m + 1) * H + W) % 2 = 1 := by
  rw [show 2 ^ (m + 1) = 2 * 2 ^ m by rw [Nat.pow_succ]; omega, Nat.mul_assoc]
  omega

/-- The representative is odd (cell `B` black), or it is the row itself with an empty right half and a left part
that does not end in `0 1`. -/
theorem rep_cases (B x : Nat) (hB : 1 ≤ B) :
    rep B x % 2 = 1 ∨ (rep B x = x ∧ x % 2 ^ B = 0 ∧ (x / 2 ^ B) % 4 ≠ 1) := by
  by_cases hx0 : x = 0
  · subst hx0
    right
    unfold rep
    simp
  obtain ⟨m, H, e⟩ := exists_lowbit x hx0
  have hl := lowbit_spec m H x e
  have hpos : 0 < 2 ^ m := Nat.two_pow_pos m
  have hlowz : ∀ i, i < m → x.testBit i = false := by
    intro i hi
    rw [e, testBit_lo (pow_lt_pow_succ m) (by omega), testBit_pow, decide_eq_false (by omega)]
  have hmodB : m ≥ B → x % 2 ^ B = 0 := by
    intro hm
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_mod_two_pow, Nat.zero_testBit]
    by_cases hi : i < B
    · rw [hlowz i (by omega)]; simp
    · rw [decide_eq_false hi]; rfl
  have hbitB : ∀ i, (x / 2 ^ B).testBit i = x.testBit (i + B) := fun i => Nat.testBit_div_two_pow x i
  have hq4 : ∀ q : Nat, q % 4 = 1 ↔ q % 2 = 1 ∧ (q / 2) % 2 = 0 := fun q => by omega
  unfold rep
  rw [ite_eq_right hx0, hl]
  by_cases hm0 : m = 0
  · rw [ite_eq_left hm0]
    left
    rw [e, hm0]
    exact low_odd 0 H 1 rfl
  rw [ite_eq_right hm0]
  by_cases hmB : B < m
  · rw [ite_eq_left hmB]
    right
    refine ⟨rfl, hmodB (by omega), ?_⟩
    intro h4
    have h1 := ((hq4 _).mp h4).1
    have := hbitB 0
    rw [Nat.zero_add, hlowz B hmB, Nat.testBit_zero] at this
    simp [h1] at this
  rw [ite_eq_right hmB]
  by_cases hb : x.testBit (m + 1) = false
  · rw [ite_eq_left hb]
    left
    rw [e, show 2 ^ (m + 1) * H + 2 ^ m - 2 ^ m = 2 ^ (m + 1) * H by omega]
    exact low_odd m H _ (stripeLow_odd (m + 1) (by omega))
  · rw [ite_eq_right hb]
    by_cases hmB' : m < B
    · rw [ite_eq_left hmB']
      left
      rw [e, show 2 ^ (m + 1) * H + 2 ^ m - 2 ^ m = 2 ^ (m + 1) * H by omega]
      exact low_odd m H _ (stripeLow_odd m (by omega))
    · rw [ite_eq_right hmB']
      right
      have hmeq : m = B := by omega
      subst hmeq
      refine ⟨rfl, hmodB (by omega), ?_⟩
      intro h4
      have h2 := ((hq4 _).mp h4).2
      have h3 := Nat.testBit_div_two_pow (n := 1) (x / 2 ^ m) 0
      rw [hbitB, Nat.zero_add, show 1 + m = m + 1 by omega] at h3
      have hb' : x.testBit (m + 1) = true := by simpa using hb
      rw [hb', Nat.testBit_zero] at h3
      simp [show (2 : Nat) ^ 1 = 2 from rfl, h2] at h3

/-- Every odd row of the box, and every row of the box with an empty right half whose left part does not end in
`0 1`, is `boxRep A B i` for some `i < 2^(A+B) + 3 * 2^(A-1)`. -/
theorem boxRep_index (A B y : Nat) (hA : 1 ≤ A) (hy : y < 2 ^ (A + B + 1))
    (hc : y % 2 = 1 ∨ (y % 2 ^ B = 0 ∧ (y / 2 ^ B) % 4 ≠ 1)) :
    ∃ i, i < 2 ^ (A + B) + 3 * 2 ^ (A - 1) ∧ boxRep A B i = y := by
  have hW : 2 ^ (A + B + 1) = 2 * 2 ^ (A + B) := by rw [Nat.pow_succ]; omega
  rcases hc with hodd | ⟨h0, h1⟩
  · refine ⟨y / 2, by omega, ?_⟩
    unfold boxRep
    rw [ite_eq_left (by omega)]
    omega
  · have hpos : 0 < 2 ^ B := Nat.two_pow_pos B
    have hlam : y / 2 ^ B < 2 ^ (A + 1) := by
      rw [Nat.div_lt_iff_lt_mul hpos, ← Nat.pow_add, show A + 1 + B = A + B + 1 by omega]; exact hy
    have hA4 : 2 ^ (A + 1) = 4 * 2 ^ (A - 1) := by
      rw [show A + 1 = (A - 1) + 2 by omega, Nat.pow_add]; omega
    have hye : y = 2 ^ B * (y / 2 ^ B) := by
      have := Nat.div_add_mod y (2 ^ B); omega
    generalize y / 2 ^ B = lam at hlam h1 hye
    subst hye
    obtain ⟨r, hr3, hlr⟩ : ∃ r, r < 3 ∧ 4 * (lam / 4) + leftResidue r = lam := by
      by_cases c0 : lam % 4 = 0
      · exact ⟨0, by decide, by show 4 * (lam / 4) + 0 = lam; omega⟩
      · by_cases c2 : lam % 4 = 2
        · exact ⟨1, by decide, by show 4 * (lam / 4) + 2 = lam; omega⟩
        · exact ⟨2, by decide, by show 4 * (lam / 4) + 3 = lam; omega⟩
    have hq : lam / 4 < 2 ^ (A - 1) := by omega
    refine ⟨2 ^ (A + B) + (3 * (lam / 4) + r), by omega, ?_⟩
    unfold boxRep
    rw [ite_eq_right (by omega), Nat.add_sub_cancel_left, show (3 * (lam / 4) + r) / 3 = lam / 4 by omega,
      show (3 * (lam / 4) + r) % 3 = r by omega, hlr]

/-- A row with an empty right half and a left part that does not end in `0 1` is its own representative. -/
theorem rep_empty_right (B lam : Nat) (hB : 1 ≤ B) (h1 : lam % 4 ≠ 1) : rep B (2 ^ B * lam) = 2 ^ B * lam := by
  by_cases hl0 : lam = 0
  · subst hl0; unfold rep; simp
  obtain ⟨m, H, e⟩ := exists_lowbit lam hl0
  have hy : 2 ^ B * lam = 2 ^ (B + m + 1) * H + 2 ^ (B + m) := by
    rw [e, Nat.mul_add, ← Nat.mul_assoc, ← Nat.pow_add, ← Nat.pow_add, show B + (m + 1) = B + m + 1 by omega]
  have hl := lowbit_spec (B + m) H _ hy
  have hpos : 0 < 2 ^ (B + m) := Nat.two_pow_pos _
  have hne : 2 ^ B * lam ≠ 0 := by rw [hy]; omega
  unfold rep
  rw [ite_eq_right hne, hl, ite_eq_right (by omega)]
  by_cases hm0 : m = 0
  · -- lam is odd, so lam % 4 = 3: bit B + 1 is black and the row is its own representative
    subst hm0
    have hH : H % 2 = 1 := by
      rw [e, show 2 ^ (0 + 1) = 2 from rfl, show 2 ^ 0 = 1 from rfl] at h1; omega
    simp only [Nat.add_zero] at hy hl ⊢
    rw [ite_eq_right (by omega), hy, testBit_low_form, decide_eq_true hH, ite_eq_right (by simp),
      ite_eq_right (by omega)]
  · rw [ite_eq_left (by omega)]

theorem boxRep_fixed (A B i : Nat) (hA : 1 ≤ A) (hB : 1 ≤ B) (hi : i < 2 ^ (A + B) + 3 * 2 ^ (A - 1)) :
    boxRep A B i < 2 ^ (A + B + 1) ∧ rep B (boxRep A B i) = boxRep A B i := by
  have hW : 2 ^ (A + B + 1) = 2 * 2 ^ (A + B) := by rw [Nat.pow_succ]; omega
  unfold boxRep
  by_cases h : i < 2 ^ (A + B)
  · rw [ite_eq_left h]
    exact ⟨by omega, rep_odd B _ (by omega)⟩
  · rw [ite_eq_right h]
    have hres : ∀ r, leftResidue r < 4 ∧ leftResidue r % 4 ≠ 1 := by
      intro r; unfold leftResidue; split
      · decide
      · split <;> decide
    have hA4 : 2 ^ (A + 1) = 4 * 2 ^ (A - 1) := by
      rw [show A + 1 = (A - 1) + 2 by omega, Nat.pow_add]; omega
    have hq : (i - 2 ^ (A + B)) / 3 < 2 ^ (A - 1) := by omega
    obtain ⟨hr4, hr1⟩ := hres ((i - 2 ^ (A + B)) % 3)
    refine ⟨?_, rep_empty_right B _ hB (by omega)⟩
    have hl : 4 * ((i - 2 ^ (A + B)) / 3) + leftResidue ((i - 2 ^ (A + B)) % 3) < 2 ^ (A + 1) := by omega
    calc 2 ^ B * (4 * ((i - 2 ^ (A + B)) / 3) + leftResidue ((i - 2 ^ (A + B)) % 3))
        < 2 ^ B * 2 ^ (A + 1) := Nat.mul_lt_mul_of_pos_left hl (Nat.two_pow_pos B)
      _ = 2 ^ (A + B + 1) := by rw [← Nat.pow_add]; congr 1; omega

theorem boxRep_inj (A B i j : Nat) (hB : 1 ≤ B) (h : boxRep A B i = boxRep A B j) : i = j := by
  have heven : ∀ k : Nat, (2 ^ B * k) % 2 = 0 := by
    intro k
    rw [show 2 ^ B = 2 * 2 ^ (B - 1) by rw [← Nat.pow_succ']; congr 1; omega, Nat.mul_assoc]
    omega
  have hres : ∀ r, r < 3 → leftResidue r < 4 := by
    intro r _; unfold leftResidue; split
    · decide
    · split <;> decide
  have hresinj : ∀ r s, r < 3 → s < 3 → leftResidue r = leftResidue s → r = s := by
    intro r s hr hs hrs
    unfold leftResidue at hrs
    split at hrs <;> split at hrs <;> (try split at hrs) <;> (try split at hrs) <;> omega
  unfold boxRep at h
  by_cases hi' : i < 2 ^ (A + B) <;> by_cases hj' : j < 2 ^ (A + B)
  · rw [ite_eq_left hi', ite_eq_left hj'] at h; omega
  · rw [ite_eq_left hi', ite_eq_right hj'] at h
    have := heven (4 * ((j - 2 ^ (A + B)) / 3) + leftResidue ((j - 2 ^ (A + B)) % 3)); omega
  · rw [ite_eq_right hi', ite_eq_left hj'] at h
    have := heven (4 * ((i - 2 ^ (A + B)) / 3) + leftResidue ((i - 2 ^ (A + B)) % 3)); omega
  · rw [ite_eq_right hi', ite_eq_right hj'] at h
    have h2 := Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos B) h
    have r1 := hres ((i - 2 ^ (A + B)) % 3) (Nat.mod_lt _ (by decide))
    have r2 := hres ((j - 2 ^ (A + B)) % 3) (Nat.mod_lt _ (by decide))
    have hq : (i - 2 ^ (A + B)) / 3 = (j - 2 ^ (A + B)) / 3 := by omega
    have hr : leftResidue ((i - 2 ^ (A + B)) % 3) = leftResidue ((j - 2 ^ (A + B)) % 3) := by omega
    have hr' := hresinj _ _ (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) hr
    omega

end StripeClasses

/-- **The stripe-class count identity.** For `A, B >= 1`, the classes of `S01` on the rows supported in `[-A, B]`
are exactly the classes of the `2^(A+B) + 3 * 2^(A-1)` rows `boxRep A B i`: every row of the box is joined to one of
them, and no two of them are joined. -/
theorem StripeClasses.s01_class_count (A B : Nat) (hA : 1 ≤ A) (hB : 1 ≤ B) :
    (∀ x, x < 2 ^ (A + B + 1) →
      ∃ i, i < 2 ^ (A + B) + 3 * 2 ^ (A - 1) ∧ Joined (BoxS01 A B) x (boxRep A B i)) ∧
    (∀ i j, i < 2 ^ (A + B) + 3 * 2 ^ (A - 1) → j < 2 ^ (A + B) + 3 * 2 ^ (A - 1) →
      Joined (BoxS01 A B) (boxRep A B i) (boxRep A B j) → i = j) := by
  constructor
  · intro x hx
    have hrx := rep_lt A B x hx
    have hc : rep B x % 2 = 1 ∨ (rep B x % 2 ^ B = 0 ∧ (rep B x / 2 ^ B) % 4 ≠ 1) := by
      rcases rep_cases B x hB with h | ⟨he, h0, h1⟩
      · exact Or.inl h
      · rw [he]; exact Or.inr ⟨h0, h1⟩
    obtain ⟨i, hi, hrep⟩ := boxRep_index A B (rep B x) hA hrx hc
    refine ⟨i, hi, ?_⟩
    rw [hrep]
    exact Joined.single ⟨hx, hrx, S01_rep B x⟩
  · intro i j hi hj hij
    obtain ⟨hli, hfi⟩ := boxRep_fixed A B i hA hB hi
    obtain ⟨hlj, hfj⟩ := boxRep_fixed A B j hA hB hj
    have h := (joined_iff A B hB hli hlj).mp hij
    rw [hfi, hfj] at h
    exact boxRep_inj A B i j hB h

end Rule30Open
