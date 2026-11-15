"""The potential tables of `Rule30Open.Foundations.StripWhiteDensity` and the text of that module.

For a strip of J adjacent columns with both outside cells free, `table(J)` is the shortest-path potential of
`strip_cycle_mean.potential(J, 0, 2, 5)`, read as a list indexed by the strip's cells as a binary number (column a the
most significant bit): phi(next) + 2 J <= phi(now) + 5 (white cells) on every step. `emit_lean` writes the module.

    python -m computations.strip_potentials --tables 5 6 7 8 9      # print the tables
    python -m computations.strip_potentials --emit-lean > Rule30Open/Foundations/StripWhiteDensity.lean
"""

from __future__ import annotations

import argparse

from computations.strip_cycle_mean import potential


GENERAL = r'''
/-! ### Every width from 5 on -/

/-- White cells of `x` on `a .. a + k - 1`. -/
def rowW (x : Int → Bool) (a : Int) : Nat → Nat
  | 0 => 0
  | k + 1 => rowW x a k + wh (x (a + (k : Int)))

/-- White cells of the columns `a .. a + J - 1` at the times `0 .. n - 1`. -/
def stripW (f : Nat → Int → Bool) (a : Int) (J : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => stripW f a J n + rowW (f n) a J

theorem rowW_add (x : Int → Bool) (a : Int) (J : Nat) :
    ∀ K, rowW x a (J + K) = rowW x a J + rowW x (a + (J : Int)) K
  | 0 => rfl
  | K + 1 => by
    have ih := rowW_add x a J K
    have e : a + ((J + K : Nat) : Int) = a + (J : Int) + (K : Int) := by omega
    show rowW x a (J + K) + wh (x (a + ((J + K : Nat) : Int))) = _
    rw [ih, e]; simp only [rowW]; omega

theorem stripW_add (f : Nat → Int → Bool) (a : Int) (J K : Nat) :
    ∀ n, stripW f a (J + K) n = stripW f a J n + stripW f (a + (J : Int)) K n
  | 0 => rfl
  | n + 1 => by
    have ih := stripW_add f a J K n
    simp only [stripW, ih, rowW_add]; omega

theorem stripW_5 (f : Nat → Int → Bool) (a : Int) : ∀ n, stripW f a 5 n = W5 f a n
  | 0 => rfl
  | n + 1 => by
    have ih := stripW_5 f a n
    simp only [stripW, W5, ih, rowW]
    omega

theorem stripW_6 (f : Nat → Int → Bool) (a : Int) : ∀ n, stripW f a 6 n = W6 f a n
  | 0 => rfl
  | n + 1 => by
    have ih := stripW_6 f a n
    simp only [stripW, W6, ih, rowW]
    omega

theorem stripW_7 (f : Nat → Int → Bool) (a : Int) : ∀ n, stripW f a 7 n = W7 f a n
  | 0 => rfl
  | n + 1 => by
    have ih := stripW_7 f a n
    simp only [stripW, W7, ih, rowW]
    omega

theorem stripW_8 (f : Nat → Int → Bool) (a : Int) : ∀ n, stripW f a 8 n = W8 f a n
  | 0 => rfl
  | n + 1 => by
    have ih := stripW_8 f a n
    simp only [stripW, W8, ih, rowW]
    omega

theorem stripW_9 (f : Nat → Int → Bool) (a : Int) : ∀ n, stripW f a 9 n = W9 f a n
  | 0 => rfl
  | n + 1 => by
    have ih := stripW_9 f a n
    simp only [stripW, W9, ih, rowW]
    omega

/-- **Every strip of `J ≥ 5` adjacent columns of every orbit**: `5 W ≥ 2 J (n - 1)`. -/
theorem strip_white_ge5 (f : Nat → Int → Bool) (hf : IsOrbit f) :
    ∀ J, 5 ≤ J → ∀ (a : Int) (n : Nat), 2 * J * n ≤ 5 * stripW f a J n + 2 * J
  | J, hJ, a, n => by
    by_cases h10 : J < 10
    · have : J = 5 ∨ J = 6 ∨ J = 7 ∨ J = 8 ∨ J = 9 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl
      · rw [stripW_5]; exact strip5_white f hf a n
      · rw [stripW_6]; exact strip6_white f hf a n
      · rw [stripW_7]; exact strip7_white f hf a n
      · rw [stripW_8]; exact strip8_white f hf a n
      · rw [stripW_9]; exact strip9_white f hf a n
    · obtain ⟨k, rfl⟩ : ∃ k, J = 5 + k := ⟨J - 5, by omega⟩
      have h1 := strip_white_ge5 f hf k (by omega) (a + ((5 : Nat) : Int)) n
      have h2 := strip5_white f hf a n
      have hs := stripW_add f a 5 k n
      rw [stripW_5] at hs
      have m : 2 * (5 + k) * n = 10 * n + 2 * k * n := by
        rw [Nat.mul_add, Nat.add_mul]
      omega
'''


def table(J: int) -> list[int]:
    """The potential of width J at the cycle mean 2/5, indexed by the strip read as a binary number."""
    phi = potential(J, 0, 2, 5)
    return [phi[i] for i in range(1 << J)]


def _emit(Js: list[int]) -> str:
    """The module text: a fixed preamble, then one block per width (table, step lemma, telescoping sum)."""
    out = ['''module

public import Ruliology.CellularAutomata.Rule30Jen

/-!
# Strips of five to nine adjacent columns of every orbit are at least 2/5 white

For `J = 5, 6, 7, 8, 9`, in every orbit of Rule 30 (any initial row), the strip of columns
`a .. a + J - 1` has at least `(2 J n - C_J) / 5` white cells at the times `0 .. n - 1`
(`stripJ_white`). The proof telescopes in time with a potential on the strip's own cells, a table
found by shortest paths: `tabJ(next) + 2 J ≤ tabJ(now) + 5 (white cells of the strip)` for every
value of the strip and of the two cells beside it (`stepJ`, by `decide`). Splitting off strips of
width 5, every strip of `J ≥ 5` columns has `5 W ≥ 2 J (n - 1)` (`strip_white_ge5`), so lower white
density at least `2/5`; the orbit of `(11001)^∞` attains `2/5` (`StripWhiteDensity.md`).

The natural-language argument is `StripWhiteDensity.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open
namespace StripWhiteDensity

open Ruliology.CellularAutomata.Rule30Jen

/-- `1` for a white cell. -/
def wh (b : Bool) : Nat := if b then 0 else 1

/-- The bit `1` for a black cell. -/
def bit (b : Bool) : Nat := if b then 1 else 0

/-- One Rule 30 step of a row. -/
def step (x : Int → Bool) : Int → Bool := fun p => rule (x (p - 1)) (x p) (x (p + 1))

/-- An orbit of Rule 30: any sequence of rows, each the image of the one before. -/
def IsOrbit (f : Nat → Int → Bool) : Prop := ∀ t, f (t + 1) = step (f t)

theorem nxt (f : Nat → Int → Bool) (hf : IsOrbit f) (n : Nat) (a : Int) (i : Nat) :
    f (n + 1) (a + (i : Int)) = rule (f n (a + (i : Int) - 1)) (f n (a + (i : Int))) (f n (a + (i : Int) + 1)) := by
  rw [hf n]; rfl
''']
    for J in Js:
        tab=table(J); C=max(tab)
        bs=[f"b{i}" for i in range(J)]
        idx=" + ".join(f"{1<<(J-1-i)} * bit b{i}" for i in range(J))
        nexts=[f"(rule l b0 b1)"]+[f"(rule b{i-1} b{i} b{i+1})" for i in range(1,J-1)]+[f"(rule b{J-2} b{J-1} r)"]
        whs=" + ".join(f"wh b{i}" for i in range(J))
        C_=lambda i: f"(f n (a + ({i} : Nat)))"
        L0="(f n (a + (0 : Nat) - 1))"; R0=f"(f n (a + ({J-1} : Nat) + 1))"
        left=lambda i: L0 if i==0 else C_(i-1)
        right=lambda i: R0 if i==J-1 else C_(i+1)
        nexts_n=[f"(rule {left(i)} {C_(i)} {right(i)})" for i in range(J)]
        eqlines=[]
        for i in range(J):
            eqlines.append(f"      have c{i} : f (n + 1) (a + ({i} : Nat)) = rule {left(i)} {C_(i)} {right(i)} := by")
            eqlines.append(f"        rw [nxt f hf n a {i}]")
            if i>0: eqlines.append(f"        have u : a + (({i} : Nat) : Int) - 1 = a + (({i-1} : Nat) : Int) := by omega")
            if i<J-1: eqlines.append(f"        have v : a + (({i} : Nat) : Int) + 1 = a + (({i+1} : Nat) : Int) := by omega")
            rw=[x for x,c in (("u",i>0),("v",i<J-1)) if c]
            if rw: eqlines.append(f"        rw [{', '.join(rw)}]")
        eqs="\n".join(eqlines)
        cells=lambda t: " ".join(f"(f {t} (a + ({i} : Nat)))" for i in range(J))
        out.append(f'''
/-! ### Width {J} -/

/-- The potential table for width {J}, indexed by the strip read from the left as a binary number. -/
def tab{J} : List Nat := {tab}

/-- The potential of a strip of width {J}. -/
def phi{J} ({" ".join(bs)} : Bool) : Nat := tab{J}.getD ({idx}) 0

set_option maxRecDepth 100000 in
theorem phi{J}_le ({" ".join(bs)} : Bool) : phi{J} {" ".join(bs)} ≤ {C} := by
  revert {" ".join(bs)}
  decide

set_option maxRecDepth 100000 in
/-- **One step for width {J}**, whatever the cells `l` and `r` beside the strip. -/
theorem step{J} (l {" ".join(bs)} r : Bool) :
    phi{J} {" ".join(nexts)} + {2*J} ≤ phi{J} {" ".join(bs)} + 5 * ({whs}) := by
  revert l {" ".join(bs)} r
  decide

/-- White cells of the columns `a .. a + {J-1}` at the times `0 .. n - 1`. -/
def W{J} (f : Nat → Int → Bool) (a : Int) : Nat → Nat
  | 0 => 0
  | n + 1 => W{J} f a n + ({" + ".join(f"wh (f n (a + ({i} : Nat)))" for i in range(J))})

/-- The potential at time `n`. -/
def pot{J} (f : Nat → Int → Bool) (a : Int) (n : Nat) : Nat := phi{J} {cells("n")}

theorem aux{J} (f : Nat → Int → Bool) (hf : IsOrbit f) (a : Int) :
    ∀ n, {2*J} * n + pot{J} f a n ≤ pot{J} f a 0 + 5 * W{J} f a n
  | 0 => by simp [W{J}]
  | n + 1 => by
    have ih := aux{J} f hf a n
    have h := step{J} (f n (a + (0 : Nat) - 1)) {cells("n")} (f n (a + ({J-1} : Nat) + 1))
    have hp : pot{J} f a (n + 1) = phi{J} {" ".join(nexts_n)} := by
      unfold pot{J}
{eqs}
      rw [{",".join(f"c{i}" for i in range(J))}]
    have hq : pot{J} f a n = phi{J} {cells("n")} := rfl
    simp only [W{J}]
    omega

/-- **Every strip of {J} adjacent columns of every orbit**: `5 W ≥ {2*J} n - {C}`. -/
theorem strip{J}_white (f : Nat → Int → Bool) (hf : IsOrbit f) (a : Int) (n : Nat) :
    {2*J} * n ≤ 5 * W{J} f a n + {C} := by
  have h := aux{J} f hf a n
  have : pot{J} f a 0 ≤ {C} := phi{J}_le _ {" ".join("_" for _ in range(J-1))}
  omega
''')
    out.append(GENERAL)
    out.append('''
end StripWhiteDensity
end Rule30Open
''')
    return ''.join(out)


def emit_lean(Js: list[int] | None = None) -> str:
    """The text of Rule30Open/Foundations/StripWhiteDensity.lean for the widths Js (default 5 to 9)."""
    return _emit(Js if Js is not None else [5, 6, 7, 8, 9])


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--tables", type=int, nargs="*")
    ap.add_argument("--emit-lean", action="store_true")
    args = ap.parse_args()
    if args.emit_lean:
        print(emit_lean(), end="")
    for J in args.tables or []:
        print(J, table(J))


if __name__ == "__main__":
    main()
