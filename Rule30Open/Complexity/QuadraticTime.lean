module

public import Rule30Open.Foundations.Evolve
public import Rule30Open.Foundations.Official
public import Ruliology.CellularAutomata.Rule30Problem3

/-!
# A one-tape machine computes the center column in quadratic time

The kit states Prize Problem 3 for deterministic one-tape Turing machines that read the binary digits of `n`
(`Rule30Problem3.Machine`): no machine computes `center n` within `C · (n + 1)` steps. This module builds one
machine of that model, `simulator`, and proves that it computes `center n` in exactly
`2 n² + 2 n ℓ + 7 n + 3 ℓ + 6` steps, with `ℓ` the number of digits of `n` (`simulator_time`), hence within
`6 (n + 1)²` steps (`simulator_computes`, `center_computes_quadratic`). So the formal Problem 3 is a question about
the exponent of one-tape time between 1 and 2, asked of a nonempty class of machines.

The machine keeps the digits as a binary counter on the cells `0, …, ℓ - 1`, the blank at cell `ℓ` as a separator,
and row `t` of the single black cell on the cells `ℓ + 1, …, ℓ + 1 + 2t`, cell `x` of the row at `ℓ + 1 + t + x`,
with the center marked. One iteration decrements the counter, walks to the row, rewrites it in place as row `t + 1`
shifted one cell right, so the region never grows left, and walks back; when the counter is zero it finds the marked
cell and halts with its color. `tape ℓ m t` is the tape with counter `m` and row `t`; the phases are
`init_phase`, `decrement_phase`, `sweep_phase`, `return_phase` and `final_phase`, composed in `loop` and
`simulator_time`. `computations/one_tape.py` runs the same table in Python and checks the step count.

The natural-language argument is `QuadraticTime.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

open Ruliology.CellularAutomata Rule30Problem3

/-! ### The machine -/

/-- The tape symbols: the kit's blank and two digits, and a row cell by color and whether it is the center. -/
inductive Sym
  | blank
  | d0
  | d1
  | row (black marked : Bool)
  deriving DecidableEq

/-- The kit's numbering: `0` blank, `1` and `2` the digits, `3` to `6` the row cells. -/
def Sym.code : Sym → Fin 7
  | .blank => 0
  | .d0 => 1
  | .d1 => 2
  | .row false false => 3
  | .row true false => 4
  | .row false true => 5
  | .row true true => 6

def Sym.decode (a : Fin 7) : Sym :=
  match a.val with
  | 0 => .blank
  | 1 => .d0
  | 2 => .d1
  | 3 => .row false false
  | 4 => .row true false
  | 5 => .row false true
  | _ => .row true true

/-- The states. `sweep a b m` carries the old cells two and one places left of the head and whether the cell
about to be written is the center; `last b` carries the old cell two places left. -/
inductive St
  | init0
  | init1
  | backRow
  | backDigits
  | scan
  | toRow
  | sweep (a b m : Bool)
  | last (b : Bool)
  | find
  deriving DecidableEq

def St.code : St → Fin 17
  | .init0 => 0
  | .init1 => 1
  | .backRow => 2
  | .backDigits => 3
  | .scan => 4
  | .toRow => 5
  | .find => 6
  | .last false => 7
  | .last true => 8
  | .sweep false false false => 9
  | .sweep true false false => 10
  | .sweep false true false => 11
  | .sweep true true false => 12
  | .sweep false false true => 13
  | .sweep true false true => 14
  | .sweep false true true => 15
  | .sweep true true true => 16

def St.decode (p : Fin 17) : St :=
  match p.val with
  | 0 => .init0
  | 1 => .init1
  | 2 => .backRow
  | 3 => .backDigits
  | 4 => .scan
  | 5 => .toRow
  | 6 => .find
  | 7 => .last false
  | 8 => .last true
  | 9 => .sweep false false false
  | 10 => .sweep true false false
  | 11 => .sweep false true false
  | 12 => .sweep true true false
  | 13 => .sweep false false true
  | 14 => .sweep true false true
  | 15 => .sweep false true true
  | _ => .sweep true true true

/-- The transition table on the named states and symbols: `.inl b` halts with the answer `b`, `.inr (s, a, d)` goes
to state `s`, writes `a` and moves by `d`. The cases that never occur on a run halt with `false`. -/
def trans : St → Sym → Bool ⊕ (St × Sym × Move)
  -- right over the digits to the separator, then one more cell
  | .init0, .blank => .inr (.init1, .blank, .right)
  | .init0, .d0 => .inr (.init0, .d0, .right)
  | .init0, .d1 => .inr (.init0, .d1, .right)
  | .init0, .row v k => .inr (.init0, .row v k, .right)
  -- write the single black cell, marked, and turn back
  | .init1, _ => .inr (.backRow, .row true true, .left)
  -- left over the row to the separator
  | .backRow, .blank => .inr (.backDigits, .blank, .left)
  | .backRow, .d0 => .inr (.backRow, .d0, .left)
  | .backRow, .d1 => .inr (.backRow, .d1, .left)
  | .backRow, .row v k => .inr (.backRow, .row v k, .left)
  -- left over the digits to the blank before cell 0, then back onto cell 0
  | .backDigits, .blank => .inr (.scan, .blank, .right)
  | .backDigits, .d0 => .inr (.backDigits, .d0, .left)
  | .backDigits, .d1 => .inr (.backDigits, .d1, .left)
  | .backDigits, .row v k => .inr (.backDigits, .row v k, .left)
  -- decrement: zeros become ones up to the lowest one, which becomes zero; no one at all means the counter is spent
  | .scan, .d0 => .inr (.scan, .d1, .right)
  | .scan, .d1 => .inr (.toRow, .d0, .right)
  | .scan, .blank => .inr (.find, .blank, .right)
  | .scan, .row _ _ => .inl false
  -- right over the remaining digits and the separator to the row
  | .toRow, .blank => .inr (.sweep false false false, .blank, .right)
  | .toRow, .d0 => .inr (.toRow, .d0, .right)
  | .toRow, .d1 => .inr (.toRow, .d1, .right)
  | .toRow, .row v k => .inr (.toRow, .row v k, .right)
  -- in place and one cell right: the new cell is Rule 30 of the old cells two left, one left and here
  | .sweep a b m, .row v k => .inr (.sweep b v k, .row (rule30 a b v) m, .right)
  | .sweep a b m, .blank => .inr (.last b, .row (rule30 a b false) m, .right)
  | .sweep _ _ _, .d0 => .inl false
  | .sweep _ _ _, .d1 => .inl false
  -- the second new cell past the old right edge, then back
  | .last b, _ => .inr (.backRow, .row (rule30 b false false) false, .left)
  -- right over the row to the marked cell, whose color is the answer
  | .find, .row v true => .inl v
  | .find, .row v false => .inr (.find, .row v false, .right)
  | .find, .blank => .inl false
  | .find, .d0 => .inl false
  | .find, .d1 => .inl false

/-- The machine in the kit's model: 17 states and 7 symbols, the table `trans` through the codes. -/
def simulator : Machine where
  q := 16
  s := 4
  δ := fun p a =>
    match trans (St.decode p) (Sym.decode a) with
    | .inl b => .inl b
    | .inr (p', a', d) => .inr (St.code p', Sym.code a', d)

theorem Sym.decode_code (a : Sym) : Sym.decode (Sym.code a) = a := by
  cases a with
  | row b m => cases b <;> cases m <;> rfl
  | _ => rfl

theorem St.decode_code (s : St) : St.decode (St.code s) = s := by
  cases s with
  | sweep a b m => cases a <;> cases b <;> cases m <;> rfl
  | last b => cases b <;> rfl
  | _ => rfl

/-! ### Configurations and runs in the named types -/

/-- The configuration in state `s`, head at `h`, with the tape `τ` read through the codes. -/
def cfg (s : St) (h : Int) (τ : Int → Sym) : Cfg simulator :=
  ⟨St.code s, h, fun i => Sym.code (τ i)⟩

/-- A step that moves: the table says `.inr (s', a', d)` on the scanned symbol. -/
theorem step_go {s : St} {a : Sym} {s' : St} {a' : Sym} {d : Move} (htr : trans s a = .inr (s', a', d))
    (h : Int) (τ : Int → Sym) (hτ : τ h = a) :
    (cfg s h τ).step = .inr (cfg s' (d.apply h) fun i => if i = h then a' else τ i) := by
  subst hτ
  simp only [Cfg.step, cfg, simulator, St.decode_code, Sym.decode_code, htr]
  congr
  funext i
  by_cases hi : i = h <;> simp [hi]

/-- A step that halts: the table says `.inl b` on the scanned symbol. -/
theorem step_halt {s : St} {a : Sym} {b : Bool} (htr : trans s a = .inl b) (h : Int) (τ : Int → Sym)
    (hτ : τ h = a) : (cfg s h τ).step = .inl b := by
  subst hτ
  simp only [Cfg.step, cfg, simulator, St.decode_code, Sym.decode_code, htr]

/-- `k` steps from a configuration: the answer if the machine has halted, the configuration otherwise. -/
def iter (c : Cfg simulator) : Nat → Bool ⊕ Cfg simulator
  | 0 => .inr c
  | k + 1 =>
    match iter c k with
    | .inl b => .inl b
    | .inr d => d.step

theorem iter_succ_of_inr {c d : Cfg simulator} {k : Nat} (h : iter c k = .inr d) :
    iter c (k + 1) = d.step := by
  simp only [iter, h]

/-- Steps compose: `k` steps to `d`, then `j` more. -/
theorem iter_add_of_inr {c d : Cfg simulator} {k : Nat} (h : iter c k = .inr d) (j : Nat) :
    iter c (k + j) = iter d j := by
  induction j with
  | zero => simpa [iter] using h
  | succ j ih =>
    have hk : k + (j + 1) = (k + j) + 1 := rfl
    rw [hk]
    simp only [iter, ih]

/-- The kit's run is `iter` from the kit's initial configuration. -/
theorem run_eq_iter (n t : Nat) : simulator.run n t = iter (simulator.init n) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Machine.run, ih, iter]
    rcases iter (simulator.init n) t with b | c <;> rfl

/-! ### Walks: states that pass over symbols without changing the tape -/

/-- A state that moves right over every symbol with `P`, writing it back, walks `k` cells over such symbols. -/
theorem walk_right (s : St) (P : Sym → Prop) (hP : ∀ a, P a → trans s a = .inr (s, a, .right)) (h : Int)
    (τ : Int → Sym) (k : Nat) (hpath : ∀ j : Nat, j < k → P (τ (h + j))) :
    iter (cfg s h τ) k = .inr (cfg s (h + k) τ) := by
  induction k with
  | zero => simp [iter]
  | succ k ih =>
    have hk : iter (cfg s h τ) k = .inr (cfg s (h + k) τ) := ih fun j hj => hpath j (by omega)
    have hstep := step_go (hP _ (hpath k (by omega))) (h + k) τ rfl
    have htape : (fun i => if i = h + k then τ (h + k) else τ i) = τ := by
      funext i
      split <;> simp_all
    have hhead : Move.apply .right (h + (k : Int)) = h + ((k + 1 : Nat) : Int) := by
      show h + (k : Int) + 1 = _
      omega
    rw [iter_succ_of_inr hk, hstep, htape, hhead]

/-- The same to the left. -/
theorem walk_left (s : St) (P : Sym → Prop) (hP : ∀ a, P a → trans s a = .inr (s, a, .left)) (h : Int)
    (τ : Int → Sym) (k : Nat) (hpath : ∀ j : Nat, j < k → P (τ (h - j))) :
    iter (cfg s h τ) k = .inr (cfg s (h - k) τ) := by
  induction k with
  | zero => simp [iter]
  | succ k ih =>
    have hk : iter (cfg s h τ) k = .inr (cfg s (h - k) τ) := ih fun j hj => hpath j (by omega)
    have hstep := step_go (hP _ (hpath k (by omega))) (h - k) τ rfl
    have htape : (fun i => if i = h - k then τ (h - k) else τ i) = τ := by
      funext i
      split <;> simp_all
    have hhead : Move.apply .left (h - (k : Int)) = h - ((k + 1 : Nat) : Int) := by
      show h - (k : Int) - 1 = _
      omega
    rw [iter_succ_of_inr hk, hstep, htape, hhead]

/-- `scan` turns `k` consecutive zero digits into ones as it passes over them. -/
theorem scan_walk (h : Int) (τ : Int → Sym) (k : Nat) (hpath : ∀ j : Nat, j < k → τ (h + j) = .d0) :
    iter (cfg .scan h τ) k = .inr (cfg .scan (h + k) fun i => if h ≤ i ∧ i < h + k then .d1 else τ i) := by
  induction k with
  | zero =>
    have htape : (fun i => if h ≤ i ∧ i < h + ((0 : Nat) : Int) then Sym.d1 else τ i) = τ := by
      funext i
      split
      · omega
      · rfl
    simp only [iter]
    rw [htape]
    simp
  | succ k ih =>
    have hk := ih fun j hj => hpath j (by omega)
    -- the cell under the head is outside the range already written, so it still reads `d0`
    have hcur : (fun i => if h ≤ i ∧ i < h + (k : Int) then Sym.d1 else τ i) (h + k) = .d0 := by
      simp only
      split
      · omega
      · exact hpath k (by omega)
    have hstep := step_go (show trans .scan .d0 = .inr (.scan, .d1, .right) from rfl) (h + k)
      (fun i => if h ≤ i ∧ i < h + (k : Int) then Sym.d1 else τ i) hcur
    have htape : (fun i => if i = h + (k : Int) then Sym.d1
        else if h ≤ i ∧ i < h + (k : Int) then Sym.d1 else τ i) =
        fun i => if h ≤ i ∧ i < h + ((k + 1 : Nat) : Int) then Sym.d1 else τ i := by
      funext i
      by_cases h1 : i = h + k
      · subst h1
        split
        · split
          · rfl
          · omega
        · omega
      · simp only [h1, ↓reduceIte]
        split
        · split
          · rfl
          · omega
        · split
          · omega
          · rfl
    have hhead : Move.apply .right (h + (k : Int)) = h + ((k + 1 : Nat) : Int) := by
      show h + (k : Int) + 1 = _
      omega
    rw [iter_succ_of_inr hk, hstep, htape, hhead]

/-! ### The light cone, the digits and the canonical tapes -/

/-- Outside the light cone the single cell's rows are white. -/
theorem single_outside (t : Nat) (x : Int) (hx : x < -(t : Int) ∨ (t : Int) < x) : evolve single t x = false := by
  induction t generalizing x with
  | zero =>
    have hx0 : x ≠ 0 := by omega
    simp [evolve, single, hx0]
  | succ t ih =>
    show rule30 (evolve single t (x - 1)) (evolve single t x) (evolve single t (x + 1)) = false
    rw [ih (x - 1) (by omega), ih x (by omega), ih (x + 1) (by omega)]
    rfl

/-- The number of binary digits of `n`: `0` for `n = 0`, else `log₂ n + 1`. -/
def len (n : Nat) : Nat := if n = 0 then 0 else n.log2 + 1

theorem lt_len_iff (n i : Nat) : i < len n ↔ 2 ^ i ≤ n := by
  unfold len
  by_cases hn : n = 0
  · subst hn
    simp
  · simp only [hn, ite_false]
    have h1 : i < n.log2 + 1 ↔ i ≤ n.log2 := by omega
    rw [h1]
    exact Nat.le_log2 hn

theorem len_le (n : Nat) : len n ≤ n := by
  unfold len
  by_cases hn : n = 0
  · simp [hn]
  · simp only [hn, ite_false]
    have h : n.log2 < n := (Nat.log2_lt hn).2 Nat.lt_two_pow_self
    omega

/-- The bits of `m - 1` from the lowest set bit `j` of `m`: ones below `j`, zero at `j`, unchanged above. -/
theorem testBit_pred {m j : Nat} (hj : m.testBit j = true) (hlow : ∀ i, i < j → m.testBit i = false) (i : Nat) :
    (m - 1).testBit i = if i < j then true else if i = j then false else m.testBit i := by
  induction j generalizing m i with
  | zero =>
    have hodd : m % 2 = 1 := by
      rw [Nat.testBit_zero] at hj
      exact of_decide_eq_true hj
    cases i with
    | zero =>
      have h0 : (m - 1) % 2 = 0 := by omega
      simp [Nat.testBit_zero, h0]
    | succ i =>
      have hdiv : (m - 1) / 2 = m / 2 := by omega
      simp only [Nat.testBit_add_one, hdiv]
      simp
  | succ j ih =>
    -- bit 0 of `m` is clear, so `m` is even; bit `j + 1` is set, so `m ≥ 2`
    have heven : m % 2 = 0 := by
      have h0 := hlow 0 (by omega)
      rw [Nat.testBit_zero] at h0
      have := of_decide_eq_false h0
      omega
    have hm2 : 2 ≤ m := by
      have hne : m ≠ 0 := by
        intro h
        rw [h, Nat.zero_testBit] at hj
        exact Bool.false_ne_true hj
      omega
    -- `m / 2` has lowest set bit `j`
    have hj' : (m / 2).testBit j = true := by
      rw [← Nat.testBit_add_one]
      exact hj
    have hlow' : ∀ i, i < j → (m / 2).testBit i = false := by
      intro i hi
      rw [← Nat.testBit_add_one]
      exact hlow (i + 1) (by omega)
    have hdiv : (m - 1) / 2 = m / 2 - 1 := by omega
    cases i with
    | zero =>
      have h0 : (m - 1) % 2 = 1 := by omega
      simp [Nat.testBit_zero, h0]
    | succ i =>
      rw [Nat.testBit_add_one, hdiv, ih hj' hlow' i, Nat.testBit_add_one]
      simp

/-- A positive number has a lowest set bit. -/
theorem exists_lowest_bit {m : Nat} (hm : m ≠ 0) :
    ∃ j, m.testBit j = true ∧ ∀ i, i < j → m.testBit i = false := by
  obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero hm
  -- the least set bit at or below `i`, by induction on `i`
  have key : ∀ k, (∃ i', i' ≤ k ∧ m.testBit i' = true) →
      ∃ j, m.testBit j = true ∧ ∀ i, i < j → m.testBit i = false := by
    intro k
    induction k with
    | zero =>
      intro ⟨i', hi'k, hi'⟩
      have h0 : i' = 0 := by omega
      subst h0
      exact ⟨0, hi', fun i hi => by omega⟩
    | succ k ih =>
      intro ⟨i', hi'k, hi'⟩
      by_cases hbelow : ∃ i'', i'' ≤ k ∧ m.testBit i'' = true
      · exact ih hbelow
      · have hk : i' = k + 1 := by
          by_cases h : i' ≤ k
          · exact absurd ⟨i', h, hi'⟩ hbelow
          · omega
        subst hk
        refine ⟨k + 1, hi', fun i hi => ?_⟩
        exact Bool.eq_false_iff.2 fun h => hbelow ⟨i, by omega, h⟩
  exact key i ⟨i, Nat.le_refl i, hi⟩

/-- The digit symbol of a bit. -/
def digit (b : Bool) : Sym := if b then .d1 else .d0

/-- The cell `i` of the row region when row `t` is stored with `ℓ` digits: cell `i - (ℓ + 1) - t` of row `t`,
marked at the center. -/
def rowSym (ℓ t : Nat) (i : Int) : Sym :=
  .row (evolve single t (i - (ℓ + 1) - t)) (decide (i = ℓ + 1 + t))

/-- The tape with the counter `m` on `ℓ` digit cells and row `t` on the cells `ℓ + 1, …, ℓ + 1 + 2t`. -/
def tape (ℓ m t : Nat) (i : Int) : Sym :=
  if 0 ≤ i ∧ i < ℓ then digit (m.testBit i.toNat)
  else if (ℓ : Int) + 1 ≤ i ∧ i ≤ ℓ + 1 + 2 * t then rowSym ℓ t i
  else .blank

/-- The kit's input tape: the digits of `n` and nothing else. -/
def tape0 (n : Nat) (i : Int) : Sym :=
  if 0 ≤ i ∧ i < len n then digit (n.testBit i.toNat) else .blank

/-- Writing back the symbol a cell already holds leaves the tape unchanged. -/
theorem init_update_self (τ : Int → Sym) (h : Int) (a : Sym) (ha : τ h = a) :
    (fun i => if i = h then a else τ i) = τ := by
  funext i
  by_cases hi : i = h
  · rw [ite_eq_left hi, hi, ha]
  · rw [ite_eq_right hi]

/-- One moving step, from an explicit configuration to an explicit one. -/
theorem init_step {s : St} {a : Sym} {s' : St} {a' : Sym} {d : Move} (htr : trans s a = .inr (s', a', d))
    {h h' : Int} (hh : d.apply h = h') {τ τ' : Int → Sym} (hτ : τ h = a)
    (hτ' : (fun i => if i = h then a' else τ i) = τ') : iter (cfg s h τ) 1 = .inr (cfg s' h' τ') := by
  show (cfg s h τ).step = _
  rw [step_go htr h τ hτ, hh, hτ']

/-- A digit symbol is `.d0` or `.d1`. -/
theorem init_digit_or (b : Bool) : digit b = .d0 ∨ digit b = .d1 := by
  cases b <;> simp [digit]

theorem init_eq (n : Nat) : simulator.init n = cfg .init0 0 (tape0 n) := by
  unfold Machine.init cfg
  have htape : ∀ i : Int, (if 0 ≤ i ∧ 2 ^ i.toNat ≤ n then
      (if n.testBit i.toNat then (⟨2, by omega⟩ : Fin (simulator.s + 3)) else ⟨1, by omega⟩)
      else ⟨0, by omega⟩) = Sym.code (tape0 n i) := by
    intro i
    unfold tape0
    by_cases h0 : 0 ≤ i
    · have hlen : i < (len n : Int) ↔ 2 ^ i.toNat ≤ n := by
        rw [← lt_len_iff n i.toNat]
        omega
      by_cases h2 : 2 ^ i.toNat ≤ n
      · rw [ite_eq_left (And.intro h0 h2), ite_eq_left (And.intro h0 (hlen.2 h2))]
        cases n.testBit i.toNat <;> rfl
      · rw [ite_eq_right (fun h => h2 h.2), ite_eq_right (fun h => h2 (hlen.1 h.2))]
        rfl
    · rw [ite_eq_right (fun h => h0 h.1), ite_eq_right (fun h => h0 h.1)]
      rfl
  exact congrArg (Cfg.mk _ 0) (funext htape)

/-! ### The phases -/

/-- From the input tape to the counter `n` beside row `0`, in `2 ℓ + 4` steps. -/
theorem init_phase (n : Nat) :
    iter (cfg .init0 0 (tape0 n)) (2 * len n + 4) = .inr (cfg .scan 0 (tape (len n) n 0)) := by
  generalize hℓ : len n = ℓ
  -- the input tape: digits on `0, …, ℓ - 1`, blank at `ℓ` and `ℓ + 1`
  have hdig : ∀ j : Nat, j < ℓ → tape0 n ((0 : Int) + j) = .d0 ∨ tape0 n ((0 : Int) + j) = .d1 := by
    intro j hj
    unfold tape0
    rw [hℓ, ite_eq_left (by omega)]
    exact init_digit_or _
  have hblank0 : tape0 n ℓ = .blank := by
    unfold tape0
    rw [hℓ, ite_eq_right (by omega)]
  have hblank1 : tape0 n ((ℓ : Int) + 1) = .blank := by
    unfold tape0
    rw [hℓ, ite_eq_right (by omega)]
  -- after writing the marked black cell at `ℓ + 1`, the tape is the canonical one with row `0`
  have htape : (fun i => if i = (ℓ : Int) + 1 then Sym.row true true else tape0 n i) = tape ℓ n 0 := by
    funext i
    unfold tape tape0 rowSym
    rw [hℓ]
    by_cases hi : i = (ℓ : Int) + 1
    · subst hi
      rw [ite_eq_left rfl, ite_eq_right (by omega), ite_eq_left (by omega),
        show (ℓ : Int) + 1 - (ℓ + 1) - ((0 : Nat) : Int) = 0 by omega, decide_eq_true (by omega)]
      rfl
    · rw [ite_eq_right hi]
      by_cases hd : 0 ≤ i ∧ i < (ℓ : Int)
      · rw [ite_eq_left hd, ite_eq_left hd]
      · rw [ite_eq_right hd, ite_eq_right hd, ite_eq_right (by omega)]
  -- the canonical tape: blank at `ℓ` and at `-1`, digits on `ℓ - 1, …, 0`
  have hsep : tape ℓ n 0 ℓ = .blank := by
    unfold tape
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  have hneg : tape ℓ n 0 (-1) = .blank := by
    unfold tape
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  have hdig' : ∀ j : Nat, j < ℓ →
      tape ℓ n 0 ((ℓ : Int) - 1 - j) = .d0 ∨ tape ℓ n 0 ((ℓ : Int) - 1 - j) = .d1 := by
    intro j hj
    unfold tape
    rw [ite_eq_left (by omega)]
    exact init_digit_or _
  -- the six sub-phases
  have s1 : iter (cfg .init0 0 (tape0 n)) ℓ = .inr (cfg .init0 ((0 : Int) + ℓ) (tape0 n)) :=
    walk_right .init0 (fun a => a = .d0 ∨ a = .d1) (by intro a ha; rcases ha with rfl | rfl <;> rfl)
      0 (tape0 n) ℓ hdig
  rw [show (0 : Int) + ℓ = ℓ by omega] at s1
  have s2 : iter (cfg .init0 ℓ (tape0 n)) 1 = .inr (cfg .init1 ((ℓ : Int) + 1) (tape0 n)) :=
    init_step (a := .blank) (a' := .blank) (d := .right) rfl rfl hblank0 (init_update_self _ _ _ hblank0)
  have s3 : iter (cfg .init1 ((ℓ : Int) + 1) (tape0 n)) 1 = .inr (cfg .backRow ℓ (tape ℓ n 0)) :=
    init_step (a := .blank) (a' := .row true true) (d := .left) rfl (by show (ℓ : Int) + 1 - 1 = ℓ; omega)
      hblank1 htape
  have s4 : iter (cfg .backRow ℓ (tape ℓ n 0)) 1 = .inr (cfg .backDigits ((ℓ : Int) - 1) (tape ℓ n 0)) :=
    init_step (a := .blank) (a' := .blank) (d := .left) rfl rfl hsep (init_update_self _ _ _ hsep)
  have s5 : iter (cfg .backDigits ((ℓ : Int) - 1) (tape ℓ n 0)) ℓ =
      .inr (cfg .backDigits ((ℓ : Int) - 1 - ℓ) (tape ℓ n 0)) :=
    walk_left .backDigits (fun a => a = .d0 ∨ a = .d1) (by intro a ha; rcases ha with rfl | rfl <;> rfl)
      ((ℓ : Int) - 1) (tape ℓ n 0) ℓ hdig'
  rw [show (ℓ : Int) - 1 - ℓ = -1 by omega] at s5
  have s6 : iter (cfg .backDigits (-1) (tape ℓ n 0)) 1 = .inr (cfg .scan 0 (tape ℓ n 0)) :=
    init_step (a := .blank) (a' := .blank) (d := .right) rfl rfl hneg (init_update_self _ _ _ hneg)
  -- compose
  rw [show 2 * ℓ + 4 = ℓ + (1 + (1 + (1 + (ℓ + 1)))) by omega, iter_add_of_inr s1, iter_add_of_inr s2,
    iter_add_of_inr s3, iter_add_of_inr s4, iter_add_of_inr s5]
  exact s6

/-- A digit cell of the canonical tape holds the digit of the counter. -/
theorem decrement_tape_digit (ℓ m t i : Nat) (hi : i < ℓ) : tape ℓ m t i = digit (m.testBit i) := by
  unfold tape
  split
  · simp
  · omega

/-- A digit cell holds `d0` or `d1`. -/
theorem decrement_tape_digit_or (ℓ m t : Nat) (i : Int) (hi : 0 ≤ i ∧ i < ℓ) :
    tape ℓ m t i = .d0 ∨ tape ℓ m t i = .d1 := by
  unfold tape
  rw [ite_eq_left hi]
  cases m.testBit i.toNat <;> simp [digit]

/-- The separator cell `ℓ` is blank. -/
theorem decrement_tape_sep (ℓ m t : Nat) : tape ℓ m t ℓ = .blank := by
  unfold tape
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]

/-- Off the digit cells the tape does not depend on the counter. -/
theorem decrement_tape_off (ℓ m m' t : Nat) (i : Int) (hi : ¬ (0 ≤ i ∧ i < ℓ)) :
    tape ℓ m t i = tape ℓ m' t i := by
  unfold tape
  rw [ite_eq_right hi, ite_eq_right hi]

/-- Writing back the symbol that is there leaves the tape unchanged. -/
theorem decrement_write_same (τ : Int → Sym) (h : Int) (a : Sym) (hτ : τ h = a) :
    (fun i => if i = h then a else τ i) = τ := by
  funext i
  split
  · rename_i hi
    rw [hi, hτ]
  · rfl

/-- The counter `m ≥ 1` becomes `m - 1` and the head reaches the row, in `ℓ + 1` steps. -/
theorem decrement_phase (n m t : Nat) (hm : 1 ≤ m) (hmn : m ≤ n) :
    iter (cfg .scan 0 (tape (len n) m t)) (len n + 1) =
      .inr (cfg (.sweep false false false) (len n + 1) (tape (len n) (m - 1) t)) := by
  obtain ⟨j, hj, hlow⟩ := exists_lowest_bit (m := m) (by omega)
  -- the lowest one of `m` lies among the `ℓ` digits, since `2 ^ j ≤ m ≤ n`
  have hjl : j < len n := by
    rw [lt_len_iff]
    rcases Nat.lt_or_ge m (2 ^ j) with h | h
    · rw [Nat.testBit_lt_two_pow h] at hj
      exact Bool.noConfusion hj
    · omega
  generalize len n = ℓ at hjl ⊢
  -- (1) `scan` turns the zeros below `j` into ones
  have h1 : iter (cfg .scan 0 (tape ℓ m t)) j =
      .inr (cfg .scan (0 + j) fun i => if 0 ≤ i ∧ i < 0 + j then .d1 else tape ℓ m t i) := by
    apply scan_walk
    intro j' hj'
    rw [Int.zero_add, decrement_tape_digit ℓ m t j' (by omega), hlow j' hj']
    rfl
  -- (2) the one at `j` becomes a zero, and the tape now carries the counter `m - 1`
  have hτ : (fun i : Int => if i = 0 + j then Sym.d0
      else if 0 ≤ i ∧ i < 0 + (j : Int) then Sym.d1 else tape ℓ m t i) = tape ℓ (m - 1) t := by
    funext i
    by_cases hi : 0 ≤ i ∧ i < (ℓ : Int)
    · obtain ⟨k, rfl⟩ : ∃ k : Nat, i = k := ⟨i.toNat, by omega⟩
      rw [decrement_tape_digit ℓ m t k (by omega), decrement_tape_digit ℓ (m - 1) t k (by omega),
        testBit_pred hj hlow k]
      rcases Nat.lt_trichotomy k j with hk | hk | hk
      · rw [ite_eq_right (by omega), ite_eq_left ⟨by omega, by omega⟩, ite_eq_left hk]
        rfl
      · subst hk
        rw [ite_eq_left (by omega), ite_eq_right (Nat.lt_irrefl _), ite_eq_left rfl]
        rfl
      · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
    · rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      exact decrement_tape_off ℓ m (m - 1) t i hi
  have h2 : iter (cfg .scan 0 (tape ℓ m t)) (j + 1) = .inr (cfg .toRow (0 + j + 1) (tape ℓ (m - 1) t)) := by
    rw [iter_succ_of_inr h1, step_go (s := .scan) (a := .d1) rfl (0 + j) _ (by
      rw [ite_eq_right (by omega), Int.zero_add, decrement_tape_digit ℓ m t j hjl, hj]
      rfl)]
    exact congrArg (fun τ => Sum.inr (cfg .toRow (0 + j + 1) τ)) hτ
  -- (3) `toRow` walks over the remaining digits to the separator
  have hH : (0 : Int) + j + 1 + ((ℓ - 1 - j : Nat) : Int) = ℓ := by omega
  have h3 : iter (cfg .scan 0 (tape ℓ m t)) (j + 1 + (ℓ - 1 - j)) =
      .inr (cfg .toRow ℓ (tape ℓ (m - 1) t)) := by
    rw [iter_add_of_inr h2, ← hH]
    refine walk_right .toRow (fun a => a = .d0 ∨ a = .d1) ?_ _ _ _ ?_
    · intro a ha
      rcases ha with rfl | rfl <;> rfl
    · intro j' hj'
      exact decrement_tape_digit_or ℓ (m - 1) t _ ⟨by omega, by omega⟩
  -- (4) the separator sends it into the sweep
  have h4 : iter (cfg .scan 0 (tape ℓ m t)) (j + 1 + (ℓ - 1 - j) + 1) =
      .inr (cfg (.sweep false false false) (ℓ + 1) (tape ℓ (m - 1) t)) := by
    rw [iter_succ_of_inr h3, step_go (s := .toRow) (a := .blank) rfl ℓ _ (decrement_tape_sep ℓ (m - 1) t)]
    exact congrArg (fun τ => Sum.inr (cfg (.sweep false false false) ((ℓ : Int) + 1) τ))
      (decrement_write_same _ _ _ (decrement_tape_sep ℓ (m - 1) t))
  rw [show ℓ + 1 = j + 1 + (ℓ - 1 - j) + 1 by omega]
  exact h4

/-- The tape during the sweep after `k` cells: the cells `ℓ + 1, …, ℓ + k` already hold row `t + 1`. -/
def sweep_mid (ℓ m t k : Nat) (i : Int) : Sym :=
  if (ℓ : Int) + 1 ≤ i ∧ i < ℓ + 1 + k then rowSym ℓ (t + 1) i else tape ℓ m t i

theorem sweep_mid_zero (ℓ m t : Nat) : sweep_mid ℓ m t 0 = tape ℓ m t := by
  funext i
  unfold sweep_mid
  split
  · omega
  · rfl

/-- The row cell at a position, written through its offset `x` from the center. -/
theorem sweep_rowSym_eq (ℓ t : Nat) (i x : Int) (hx : x = i - (ℓ + 1) - t) :
    rowSym ℓ t i = .row (evolve single t x) (decide (x = 0)) := by
  subst hx
  unfold rowSym
  congr 1
  exact decide_eq_decide.mpr ⟨fun h => by omega, fun h => by omega⟩

/-- The cell under the head at step `k ≤ 2 t` is cell `k - t` of row `t`, marked iff `k = t`. -/
theorem sweep_mid_read (ℓ m t k : Nat) (hk : k ≤ 2 * t) :
    sweep_mid ℓ m t k (ℓ + 1 + k) = .row (evolve single t ((k : Int) - t)) (decide (k = t)) := by
  unfold sweep_mid tape
  (repeat' split) <;> first
    | omega
    | rw [sweep_rowSym_eq ℓ t (ℓ + 1 + k) ((k : Int) - t) (by omega)]
      congr 1
      exact decide_eq_decide.mpr ⟨fun h => by omega, fun h => by omega⟩

/-- The cell under the head at step `2 t + 1` is the blank past the old row. -/
theorem sweep_mid_blank (ℓ m t : Nat) :
    sweep_mid ℓ m t (2 * t + 1) (ℓ + 1 + ((2 * t + 1 : Nat) : Int)) = .blank := by
  unfold sweep_mid tape
  (repeat' split) <;> first | rfl | omega

/-- Writing the new row cell at the head advances the sweep by one cell. -/
theorem sweep_mid_succ (ℓ m t k : Nat) :
    (fun i => if i = (ℓ : Int) + 1 + k then rowSym ℓ (t + 1) ((ℓ : Int) + 1 + k) else sweep_mid ℓ m t k i) =
      sweep_mid ℓ m t (k + 1) := by
  funext i
  unfold sweep_mid
  (repeat' split) <;> first | rfl | omega | (subst_vars; rfl)

/-- After `2 t + 3` cells the sweep has written row `t + 1` in full. -/
theorem sweep_mid_full (ℓ m t : Nat) : sweep_mid ℓ m t (2 * t + 3) = tape ℓ m (t + 1) := by
  funext i
  unfold sweep_mid tape
  (repeat' split) <;> first | rfl | omega

/-- Rule 30 on three consecutive cells of row `t` is the middle cell of row `t + 1`. -/
theorem sweep_evolve_succ (t : Nat) (x a c : Int) (ha : a = x - 1) (hc : c = x + 1) :
    rule30 (evolve single t a) (evolve single t x) (evolve single t c) = evolve single (t + 1) x := by
  subst ha hc
  rfl

/-- The symbol the sweep writes at step `k` is the cell `ℓ + 1 + k` of row `t + 1`. -/
theorem sweep_written (ℓ t k : Nat) :
    Sym.row (rule30 (evolve single t ((k : Int) - 2 - t)) (evolve single t ((k : Int) - 1 - t))
        (evolve single t ((k : Int) - t))) (decide (k = t + 1)) =
      rowSym ℓ (t + 1) (ℓ + 1 + k) := by
  rw [sweep_rowSym_eq ℓ (t + 1) (ℓ + 1 + k) ((k : Int) - 1 - t) (by omega),
    sweep_evolve_succ t ((k : Int) - 1 - t) ((k : Int) - 2 - t) ((k : Int) - t) (by omega) (by omega)]
  congr 1
  exact decide_eq_decide.mpr ⟨fun h => by omega, fun h => by omega⟩

/-- The symbol written on the blank past the old row, at step `2 t + 1`. -/
theorem sweep_written_blank (ℓ t : Nat) :
    Sym.row (rule30 (evolve single t (((2 * t + 1 : Nat) : Int) - 2 - t))
        (evolve single t (((2 * t + 1 : Nat) : Int) - 1 - t)) false) (decide (2 * t + 1 = t + 1)) =
      rowSym ℓ (t + 1) (ℓ + 1 + ((2 * t + 1 : Nat) : Int)) := by
  rw [← sweep_written ℓ t (2 * t + 1), single_outside t (((2 * t + 1 : Nat) : Int) - t) (Or.inr (by omega))]

/-- The symbol written by `last`, one cell further, at step `2 t + 2`. -/
theorem sweep_written_last (ℓ t : Nat) :
    Sym.row (rule30 (evolve single t (((2 * t + 1 : Nat) : Int) - 1 - t)) false false) false =
      rowSym ℓ (t + 1) (ℓ + 1 + ((2 * t + 1 + 1 : Nat) : Int)) := by
  have hm : decide (2 * t + 1 + 1 = t + 1) = false := decide_eq_false (by omega)
  rw [← sweep_written ℓ t (2 * t + 1 + 1), hm,
    single_outside t (((2 * t + 1 + 1 : Nat) : Int) - 1 - t) (Or.inr (by omega)),
    single_outside t (((2 * t + 1 + 1 : Nat) : Int) - t) (Or.inr (by omega)),
    show (((2 * t + 1 + 1 : Nat) : Int) - 2 - t) = ((2 * t + 1 : Nat) : Int) - 1 - t by omega]

/-- A sweep step on a row cell. -/
theorem sweep_step_row (a b m v k : Bool) (h : Int) (τ : Int → Sym) (hτ : τ h = .row v k) :
    (cfg (.sweep a b m) h τ).step =
      .inr (cfg (.sweep b v k) (h + 1) fun i => if i = h then .row (rule30 a b v) m else τ i) :=
  step_go (s' := .sweep b v k) (a' := .row (rule30 a b v) m) (d := .right) rfl h τ hτ

/-- A sweep step on the blank. -/
theorem sweep_step_blank (a b m : Bool) (h : Int) (τ : Int → Sym) (hτ : τ h = .blank) :
    (cfg (.sweep a b m) h τ).step =
      .inr (cfg (.last b) (h + 1) fun i => if i = h then .row (rule30 a b false) m else τ i) :=
  step_go (s' := .last b) (a' := .row (rule30 a b false) m) (d := .right) rfl h τ hτ

/-- `last` writes the second new cell and turns back whatever it reads. -/
theorem sweep_trans_last (b : Bool) (a : Sym) :
    trans (.last b) a = .inr (.backRow, .row (rule30 b false false) false, .left) := by
  cases a <;> rfl

/-- The `last` step, on any symbol. -/
theorem sweep_step_last (b : Bool) (h : Int) (τ : Int → Sym) :
    (cfg (.last b) h τ).step =
      .inr (cfg .backRow (h - 1) fun i => if i = h then .row (rule30 b false false) false else τ i) :=
  step_go (sweep_trans_last b (τ h)) h τ rfl

/-- The sweep invariant: after `k ≤ 2 t + 1` steps the state carries cells `k - 2 - t` and `k - 1 - t` of
row `t`, the head is at `ℓ + 1 + k`, and the cells before it hold row `t + 1`. -/
theorem sweep_invariant (ℓ m t k : Nat) (hk : k ≤ 2 * t + 1) :
    iter (cfg (.sweep false false false) (ℓ + 1) (tape ℓ m t)) k =
      .inr (cfg (.sweep (evolve single t ((k : Int) - 2 - t)) (evolve single t ((k : Int) - 1 - t))
        (decide (k = t + 1))) (ℓ + 1 + k) (sweep_mid ℓ m t k)) := by
  induction k with
  | zero =>
    have h1 : evolve single t (((0 : Nat) : Int) - 2 - t) = false := single_outside t _ (Or.inl (by omega))
    have h2 : evolve single t (((0 : Nat) : Int) - 1 - t) = false := single_outside t _ (Or.inl (by omega))
    have h3 : decide (0 = t + 1) = false := decide_eq_false (by omega)
    have h4 : (ℓ : Int) + 1 + ((0 : Nat) : Int) = ℓ + 1 := by omega
    rw [h1, h2, h3, h4, sweep_mid_zero]
    rfl
  | succ k ih =>
    rw [iter_succ_of_inr (ih (by omega)), sweep_step_row _ _ _ _ _ _ _ (sweep_mid_read ℓ m t k (by omega)),
      sweep_written ℓ t k, sweep_mid_succ ℓ m t k]
    have hs : (((k + 1 : Nat) : Int) - 2 - t) = (k : Int) - 1 - t := by omega
    have hs' : (((k + 1 : Nat) : Int) - 1 - t) = (k : Int) - t := by omega
    have hm : decide (k = t) = decide (k + 1 = t + 1) :=
      decide_eq_decide.mpr ⟨fun h => by omega, fun h => by omega⟩
    have hh : (ℓ : Int) + 1 + k + 1 = ℓ + 1 + ((k + 1 : Nat) : Int) := by omega
    rw [hs, hs', hm, hh]

/-- Row `t` becomes row `t + 1` in place, shifted one cell right, in `2 t + 3` steps; the head ends on the last
cell of the new row. -/
theorem sweep_phase (ℓ m t : Nat) :
    iter (cfg (.sweep false false false) (ℓ + 1) (tape ℓ m t)) (2 * t + 3) =
      .inr (cfg .backRow (ℓ + 2 * t + 2) (tape ℓ m (t + 1))) := by
  have h1 := iter_succ_of_inr (sweep_invariant ℓ m t (2 * t + 1) (by omega))
  rw [sweep_step_blank _ _ _ _ _ (sweep_mid_blank ℓ m t), sweep_written_blank, sweep_mid_succ,
    show (ℓ : Int) + 1 + ((2 * t + 1 : Nat) : Int) + 1 = ℓ + 1 + ((2 * t + 1 + 1 : Nat) : Int) by omega] at h1
  have h2 := iter_succ_of_inr h1
  rw [sweep_step_last, sweep_written_last, sweep_mid_succ] at h2
  rw [show 2 * t + 3 = 2 * t + 1 + 1 + 1 from rfl, h2, show 2 * t + 1 + 1 + 1 = 2 * t + 3 from rfl, sweep_mid_full,
    show (ℓ : Int) + 1 + ((2 * t + 1 + 1 : Nat) : Int) - 1 = ℓ + 2 * t + 2 by omega]

/-- Two configurations in the same state agree when their heads and tapes do. -/
theorem return_cfg_congr (s : St) {h h' : Int} {τ τ' : Int → Sym} (hh : h = h') (hτ : τ = τ') :
    cfg s h τ = cfg s h' τ' := by
  subst hh; subst hτ; rfl

/-- Writing back the scanned symbol leaves the tape unchanged. -/
theorem return_write_same (τ : Int → Sym) (h : Int) (a : Sym) (hτ : τ h = a) :
    (fun i => if i = h then a else τ i) = τ := by
  funext i; split <;> simp_all

/-- Back over the row and the digits to cell `0`, in `2 t + ℓ + 4` steps. -/
theorem return_phase (ℓ m t : Nat) :
    iter (cfg .backRow (ℓ + 2 * t + 2) (tape ℓ m (t + 1))) (2 * t + ℓ + 4) =
      .inr (cfg .scan 0 (tape ℓ m (t + 1))) := by
  generalize hτ : tape ℓ m (t + 1) = τ
  -- (1) left over the row cells to the separator at `ℓ`
  have h1 : iter (cfg .backRow (ℓ + 2 * t + 2) τ) (2 * t + 2) = .inr (cfg .backRow ℓ τ) := by
    have hw := walk_left .backRow (fun a => ∃ v k, a = .row v k)
      (by rintro a ⟨v, k, rfl⟩; rfl) (ℓ + 2 * t + 2) τ (2 * t + 2)
      (by
        intro j hj
        have hcell : τ (ℓ + 2 * t + 2 - j) = rowSym ℓ (t + 1) (ℓ + 2 * t + 2 - j) := by
          rw [← hτ]
          unfold tape
          rw [ite_eq_right (by omega), ite_eq_left (by omega)]
        exact ⟨_, _, hcell⟩)
    rw [hw]
    exact congrArg Sum.inr (return_cfg_congr _ (by omega) rfl)
  -- (2) the separator sends the head left into the digits
  have hsep : τ ℓ = .blank := by
    rw [← hτ]
    unfold tape
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  have h2 : iter (cfg .backRow (ℓ + 2 * t + 2) τ) (2 * t + 2 + 1) = .inr (cfg .backDigits (ℓ - 1) τ) := by
    rw [iter_succ_of_inr h1, step_go (s' := .backDigits) (a' := .blank) (d := .left) rfl ℓ τ hsep]
    exact congrArg Sum.inr (return_cfg_congr _ rfl (return_write_same τ ℓ .blank hsep))
  -- (3) left over the digit cells to the blank at `-1`
  have h3 : iter (cfg .backRow (ℓ + 2 * t + 2) τ) (2 * t + 2 + 1 + ℓ) = .inr (cfg .backDigits (-1) τ) := by
    rw [iter_add_of_inr h2]
    have hw := walk_left .backDigits (fun a => a = .d0 ∨ a = .d1)
      (by rintro a (rfl | rfl) <;> rfl) (ℓ - 1) τ ℓ
      (by
        intro j hj
        rw [← hτ]
        unfold tape digit
        rw [ite_eq_left (by omega)]
        split <;> simp)
    rw [hw]
    exact congrArg Sum.inr (return_cfg_congr _ (by omega) rfl)
  -- (4) the blank before cell `0` sends the head back onto cell `0` in `scan`
  have hblank : τ (-1) = .blank := by
    rw [← hτ]
    unfold tape
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  have h4 : iter (cfg .backRow (ℓ + 2 * t + 2) τ) (2 * t + 2 + 1 + ℓ + 1) = .inr (cfg .scan 0 τ) := by
    rw [iter_succ_of_inr h3, step_go (s' := .scan) (a' := .blank) (d := .right) rfl (-1) τ hblank]
    exact congrArg Sum.inr
      (return_cfg_congr _ (by show (-1 : Int) + 1 = 0; omega) (return_write_same τ (-1) .blank hblank))
  have e : 2 * t + ℓ + 4 = 2 * t + 2 + 1 + ℓ + 1 := by omega
  rw [e]
  exact h4

/-- With the counter spent, the machine halts on the marked cell with its color, in `ℓ + n + 2` steps. -/
theorem final_phase (ℓ n : Nat) :
    iter (cfg .scan 0 (tape ℓ 0 n)) (ℓ + n + 2) = .inl (evolve single n 0) := by
  -- (1) `scan` turns the zero digits of the counter `0` into ones and reaches the separator
  have hdigits : ∀ j : Nat, j < ℓ → tape ℓ 0 n ((0 : Int) + j) = .d0 := by
    intro j hj
    unfold tape
    rw [ite_eq_left (by omega)]
    simp [digit, Nat.zero_testBit]
  have h1 := scan_walk 0 (tape ℓ 0 n) ℓ hdigits
  generalize hτ₁ : (fun i => if 0 ≤ i ∧ i < 0 + (ℓ : Int) then Sym.d1 else tape ℓ 0 n i) = τ₁ at h1
  -- (2) the separator sends the head right in `find`
  have hsep : τ₁ (0 + ℓ) = .blank := by
    rw [← hτ₁]
    dsimp only
    rw [ite_eq_right (by omega)]
    unfold tape
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  have h2 : iter (cfg .scan 0 (tape ℓ 0 n)) (ℓ + 1) = .inr (cfg .find (0 + ℓ + 1) τ₁) := by
    rw [iter_succ_of_inr h1, step_go (s' := .find) (a' := .blank) (d := .right) rfl (0 + ℓ) τ₁ hsep]
    exact congrArg Sum.inr (return_cfg_congr _ rfl (return_write_same τ₁ (0 + ℓ) .blank hsep))
  -- (3) right over the unmarked row cells
  have h3 : iter (cfg .scan 0 (tape ℓ 0 n)) (ℓ + 1 + n) = .inr (cfg .find (0 + ℓ + 1 + n) τ₁) := by
    rw [iter_add_of_inr h2]
    exact walk_right .find (fun a => ∃ v, a = .row v false)
      (by rintro a ⟨v, rfl⟩; rfl) (0 + ℓ + 1) τ₁ n
      (by
        intro j hj
        have hcell : τ₁ (0 + ℓ + 1 + j) = .row (evolve single n (0 + ℓ + 1 + j - (ℓ + 1) - n)) false := by
          rw [← hτ₁]
          dsimp only
          rw [ite_eq_right (by omega)]
          unfold tape rowSym
          rw [ite_eq_right (by omega), ite_eq_left (by omega), decide_eq_false (by omega)]
        exact ⟨_, hcell⟩)
  -- (4) the marked cell halts with its color, the center of row `n`
  have hmark : τ₁ (0 + ℓ + 1 + n) = .row (evolve single n 0) true := by
    rw [← hτ₁]
    dsimp only
    rw [ite_eq_right (by omega)]
    unfold tape rowSym
    rw [ite_eq_right (by omega), ite_eq_left (by omega), decide_eq_true (by omega)]
    have e0 : (0 : Int) + ℓ + 1 + n - (ℓ + 1) - n = 0 := by omega
    rw [e0]
  have e : ℓ + n + 2 = ℓ + 1 + n + 1 := by omega
  rw [e, iter_succ_of_inr h3]
  exact step_halt (s := .find) (a := .row (evolve single n 0) true) rfl (0 + ℓ + 1 + n) τ₁ hmark

/-! ### The whole run -/

/-- The steps of the first `t` iterations: `Σ_{s < t} (4 s + 2 ℓ + 8)`. -/
def loopTime (ℓ t : Nat) : Nat := 2 * t * t + 2 * ℓ * t + 6 * t

theorem loopTime_succ (ℓ t : Nat) : loopTime ℓ (t + 1) = loopTime ℓ t + (4 * t + 2 * ℓ + 8) := by
  unfold loopTime
  simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.mul_assoc]
  omega

/-- After `t ≤ n` iterations the counter reads `n - t` beside row `t`. -/
theorem loop (n t : Nat) (ht : t ≤ n) :
    iter (cfg .scan 0 (tape (len n) n 0)) (loopTime (len n) t) = .inr (cfg .scan 0 (tape (len n) (n - t) t)) := by
  induction t with
  | zero => simp [loopTime, iter]
  | succ t ih =>
    have ih' := ih (by omega)
    -- one more iteration: decrement, sweep, return
    have hdec := decrement_phase n (n - t) t (by omega) (by omega)
    have hsw := sweep_phase (len n) (n - t - 1) t
    have hret := return_phase (len n) (n - t - 1) t
    have h1 : iter (cfg .scan 0 (tape (len n) (n - t) t)) ((len n + 1) + (2 * t + 3)) =
        .inr (cfg .backRow (len n + 2 * t + 2) (tape (len n) (n - t - 1) (t + 1))) := by
      rw [iter_add_of_inr hdec, hsw]
    have h2 : iter (cfg .scan 0 (tape (len n) (n - t) t)) ((len n + 1) + (2 * t + 3) + (2 * t + len n + 4)) =
        .inr (cfg .scan 0 (tape (len n) (n - (t + 1)) (t + 1))) := by
      rw [show n - (t + 1) = n - t - 1 by omega, iter_add_of_inr h1, hret]
    have hsplit : 4 * t + 2 * len n + 8 = (len n + 1) + (2 * t + 3) + (2 * t + len n + 4) := by omega
    rw [loopTime_succ, iter_add_of_inr ih', hsplit]
    exact h2

/-- The exact running time on the input `n`, with `ℓ = len n` digits. -/
def time (n : Nat) : Nat := 2 * n * n + 2 * n * len n + 7 * n + 3 * len n + 6

theorem time_eq (n : Nat) : time n = (2 * len n + 4) + loopTime (len n) n + (len n + n + 2) := by
  unfold time loopTime
  simp only [Nat.mul_assoc, Nat.mul_comm (len n) n]
  omega

/-- **The machine halts with `center n` after exactly `time n` steps.** -/
theorem simulator_time (n : Nat) : simulator.run n (time n) = .inl (Rule30Prize.center n) := by
  have h1 : iter (cfg .init0 0 (tape0 n)) ((2 * len n + 4) + loopTime (len n) n) =
      .inr (cfg .scan 0 (tape (len n) 0 n)) := by
    rw [iter_add_of_inr (init_phase n), loop n n (Nat.le_refl n), Nat.sub_self]
  rw [run_eq_iter, init_eq, time_eq, iter_add_of_inr h1, final_phase, evolve_single_center]

theorem time_le (n : Nat) : time n ≤ 6 * (n + 1) ^ 2 := by
  unfold time
  have hl : len n ≤ n := len_le n
  have hnl : n * len n ≤ n * n := Nat.mul_le_mul_left n hl
  rw [Nat.pow_two]
  simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul, Nat.mul_assoc]
  omega

/-- **The center column is computed on one tape within `6 (n + 1)²` steps**, in the kit's model. -/
theorem simulator_computes : Computes simulator Rule30Prize.center fun n => 6 * (n + 1) ^ 2 :=
  Computes.mono (T := time) (fun n => simulator_time n) time_le

/-- **Some machine of the kit's model computes the center column in quadratic time**: the class of machines
that Problem 3 speaks about is not empty, and its question is whether the exponent 2 can fall to 1. -/
theorem center_computes_quadratic :
    ∃ (M : Machine) (C : Nat), Computes M Rule30Prize.center fun n => C * (n + 1) ^ 2 :=
  ⟨simulator, 6, simulator_computes⟩

end Rule30Open
