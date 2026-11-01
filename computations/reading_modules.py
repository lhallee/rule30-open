"""The Lean modules of reading certificates: a rank certificate for one block, one read phase, a width and a word list,
written in the form of `Rule30Open.Columns.ThreeRuns`.

`module_text` writes the whole module from a `Module` (the certificate and its prose); the tables are the ranks of
`reading_certificates.certificate`, packed by `reading_certificates.tables`. `MODULES` holds the modules of the
repository with one block.

`collection_text` writes several blocks into one module (a `Collection`): the body of each block's module in a section
of its own, with its helpers in the namespace `ReadingWords.B<block>` and its headline theorems `readings_<block>`,
`readings_<block>_evolve` and `no_<word>_time_<block>` in `Rule30Open`. `COLLECTIONS` holds them; the rows of
`ReadingWords` (`READING_WORDS`) are, for each block, the forced list of lowest entropy that
`reading_certificates.strongest` finds at a single white phase within 120,000 states.

    python -m computations.reading_modules Runs00001               # print the module
    python -m computations.reading_modules Runs00001 --check       # the file in Rule30Open/Columns is this text
    python -m computations.reading_modules ReadingWords --check    # the 15 blocks of ReadingWords, about 1 s
"""

from __future__ import annotations

import argparse
import sys
from dataclasses import dataclass
from pathlib import Path

from computations.gap_traps import word_entropy
from computations.reading_certificates import Spec, certificate, tables

COLUMNS = Path(__file__).resolve().parent.parent / "Rule30Open" / "Columns"
NUMBERS = {1: "one", 2: "two", 3: "three", 4: "four", 5: "five", 6: "six", 7: "seven"}


@dataclass(frozen=True)
class Module:
    """A reading certificate and the names and prose of its Lean module."""

    name: str
    block: str
    q: int
    width: int
    words: tuple[str, ...]
    title: str
    summary: str
    pred: str
    pred_doc: str
    headline: str
    headline_doc: str
    evolve_doc: str
    step_name: str
    suffix: str = ""


MODULES = {
    "Runs00001": Module(
        name="Runs00001", block="00001", q=0, width=12, words=("11", "1001"),
        title="Under the center column `00001`, column 1 at the first white step has no `11` and no `1001`",
        summary=("Let the center column repeat the block `00001` and look at the right half it drives (the kit's "
                 "`Rule30Ether.drv`),\nfrom any initial right half, finite or not. At the first white step of each "
                 "period, the step just after the black\none, column 1 never reads `11` or `1001` with the last "
                 "reading at time 29 or later: its 1s are isolated and none of\nits runs of 0s has length exactly "
                 "2."),
        pred="SparseOnes",
        pred_doc=("A sequence of bits has no factor `11` or `1001` from index `i0` on: its 1s are isolated and none "
                  "of its\nruns of 0s between two 1s has length 2."),
        headline="runs_00001", headline_doc="Isolated ones.", evolve_doc="Isolated ones for every row.",
        step_name="first white step", suffix="_00001"),
}


def wrap(head: str, items: list[str], sep: str, tail: str, indent: str, width: int = 120) -> str:
    """Join items after head with sep, breaking lines before width with the given indent."""
    lines, cur = [], head
    for k, it in enumerate(items):
        piece = it + (sep if k < len(items) - 1 else tail)
        if len(cur) + len(piece) + (1 if k else 0) > width and cur.strip():
            lines.append(cur.rstrip())
            cur = indent + piece
        else:
            cur = cur + ("" if k == 0 else " ") + piece
    lines.append(cur)
    return "\n".join(lines)


def nested(k: int, period: int) -> str:
    """The time u + k periods, as a left-nested sum."""
    return "u" + f" + {period}" * k


def module_parts(mod: Module) -> tuple[str, str]:
    """The head of the module of a reading certificate (imports, docstring, `namespace Rule30Open`, the opens) and its
    body (the certificate, its proof and the headline theorems)."""
    name, block, q, width, words, title, summary = mod.name, mod.block, mod.q, mod.width, mod.words, mod.title, \
        mod.summary
    pred, pred_doc, headline, headline_doc, evolve_doc, suffix = mod.pred, mod.pred_doc, mod.headline, \
        mod.headline_doc, mod.evolve_doc, mod.suffix
    step_name = mod.step_name
    spec = Spec(block, (q,), width, words)
    _, rank = certificate(spec)  # (P, 2^W, 2^keep)
    assert (rank >= 0).all(), "entry is not forced"
    assert min(len(u) for u in words) >= 2 and block[q] == "0", "words of two readings or more, at a white phase"
    P, K = len(block), spec.keep
    S = 1 << K
    M = int(rank.max())
    B = max(1, M.bit_length())
    tabs = tables(rank, B)
    blist = "[" + ", ".join("true" if c == "1" else "false" for c in block) + "]"
    bname = "w" + block
    n = 1 << width
    # badB: the text (2 s + b) mod 2^len equals the word
    conds = [f"(2 * s + b.toNat) % {1 << len(u)} == {int(u, 2)}" for u in words]
    bad = " ||\n    ".join(f"({c})" for c in conds)
    off = f"({P} - ph % {P}) % {P}" if q == 0 else f"({q} + {P} - ph % {P}) % {P}"
    times = f"T + {P} * i" if q == 0 else f"T + {P} * i + {q}"
    times_doc = f"T + {P} i" if q == 0 else f"T + {P} i + {q}"
    # word theorems: the k-th reading of a word at time u + P k, written u + P + ... + P to meet `suf_period`
    word_thms = []
    i0 = 0
    for u in words:
        m = len(u)
        lo = max(0, M - P * (m - 1))
        # reading i at time P i + off with off <= P - 1 and >= 0; need P i + off >= lo; off >= 0 so i >= ceil(lo / P)
        i0 = max(i0, -(-lo // P))
        bools = ["true" if c == "1" else "false" for c in u]
        conj = " ∧ ".join(f"drv (ctr ph) R {'u' if k == 0 else f'(u + {P * k})'} 1 = {bools[k]}" for k in range(m))
        lines = [f"/-- **No `{u}`.** At the {step_name}s, column 1 never reads `{u}` with the first reading at time "
                 f"`{lo}` or\nlater. -/",
                 f"theorem no_{u}_time{suffix} (u : Nat) (hu : {lo} ≤ u) (hp : (u + ph) % {P} = {q}) :",
                 wrap("    ¬ (", conj.split(" ∧ "), " ∧", ") := by", "      ").replace("¬ ( ", "¬ ("),
                 f"  rintro ⟨{', '.join(f'h{k}' for k in range(m))}⟩"]
        for k in range(2, m):
            lines.append(f"  rw [show u + {P * k} = {nested(k, P)} by omega] at h{k}")
        lines.append(f"  have hb := no_bad R ph ({nested(m - 1, P)}) (by omega) (by omega)")
        rws = [f"suf_period R ph ({nested(k, P)}) (by omega)" for k in range(m - 2, 0, -1)]
        rws.append("suf_period R ph u hp")
        lines.append(wrap("  rw [", rws + [f"h{k}" for k in range(m)], ",", "] at hb", "    ").replace("rw [ ", "rw ["))
        lines.append(f"  rw [bad_{u} _ (suf_lt _ _ _)] at hb")
        lines.append("  exact absurd hb (by decide)")
        word_thms.append("\n".join(lines))
    decide = "decide" if S <= 8 else "decide +kernel"  # plain decide for few stored readings, as Runs00001
    bad_lemmas = []
    for u in words:
        expr = "s"
        for c in u[:-1]:
            expr = f"push ({expr}) {'true' if c == '1' else 'false'}"
        expr = expr.replace("push (s)", "push s")
        last = "true" if u[-1] == "1" else "false"
        line = f"theorem bad_{u} : ∀ s, s < {S} → badB ({expr}) {last} = true := by {decide}"
        stmt = line.removesuffix(f" := by {decide}").split(" ")
        bad_lemmas.append(line if len(line) <= 120 else wrap("", stmt + [f":= by {decide}"], "", "", "    "))
    # predicate
    pred_terms = []
    for u in words:
        conj = " ∧ ".join(f"b {'i' if k == 0 else f'(i + {k})'} = {'true' if c == '1' else 'false'}"
                          for k, c in enumerate(u))
        pred_terms.append(conj)
    lead = len(f"  ∀ i, {i0} ≤ i → ")
    pred_body = " ∧\n    ".join(
        wrap(" " * (lead if k == 0 else 4) + "¬ (", conj.split(" ∧ "), " ∧",
             ")" + (" ∧" if k < len(pred_terms) - 1 else ""), " " * 6)[(lead if k == 0 else 4):].removesuffix(" ∧")
        for k, conj in enumerate(pred_terms))
    maxm = max(len(u) for u in words)
    eqs = []
    for k in range(1, maxm):
        eqs.append(f"  have e{k} : reading R ph (i + {k}) = drv (ctr ph) R ({P} * i + {off} + {P * k}) 1 := by\n"
                   f"    unfold reading; rw [show {P} * (i + {k}) + {off} = {P} * i + {off} + {P * k} by omega]")
    erw = ", ".join(f"e{k}" for k in range(1, maxm))
    tup = ", ".join(f"no_{u}_time{suffix} R ph _ (by omega) hp" for u in words)
    names = ", ".join(f"`no_{u}_time{suffix}`" for u in words)
    ok_thms = "\n".join(f"theorem ok_{p} : allBelowT (partOK {p}) {S} = true := by decide +kernel" for p in range(P))
    parts_cases = "\n".join(f"  | {p}, _ => ok_{p}" for p in range(P))
    hdrwords = ", ".join(f"`{u}`" for u in words)
    tabtext = ",\n".join(f"  {hex(v)}" for v in tabs)
    head = f"""module

public import Rule30Open.Foundations.Evolve
public import Ruliology.CellularAutomata.Rule30EtherThree

/-!
# {title}

{summary}

* `rankTabs`, `rk`, `nodeOK`, `partOK`: a rank certificate over the states (phase, window of columns 1..{width}, last
  {NUMBERS[K]} readings at the {step_name}s). Rank 0 states go to rank 0 states for both values of column {width + 1} and
  complete no forbidden word; a state of positive rank goes to states of smaller rank. Ranks are at most {M}. `ok_p`,
  `parts_ok`: the kernel checks, one per phase.
* `{name}.rank_bound`: along the driven right half, the rank at time `t` is at most `{M} - t`.
* {names}: the forbidden words, stated for the times of the readings.
* `{headline}`: the same for the readings `reading R ph i` of column 1 at the `i`-th {step_name}, `i ≥ {i0}`.
* `{name}.evolve_eq_drv`, `{headline}_evolve`: for every row whose center column repeats `{block}` from time `T`,
  the readings of column 1 at the times `{times_doc}`, `i ≥ {i0}`, avoid the {NUMBERS[len(words)]} words.

The natural-language argument is `{name}.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

open Ruliology.CellularAutomata Rule30Ether Rule30EtherThree Rule30StripCertificates

"""
    body = f"""/-! The certificate and the helpers live in `{name}`; the headline theorems are in `Rule30Open`. -/

namespace {name}

/-! ### The certificate: the attractor ranks of the greatest closed good set, rank 0 for the set itself -/

/-- Rank tables: entry `{S} * p + s` packs the rank of window `w` in bits `{B} w .. {B} w + {B - 1}`. -/
def rankTabs : List Nat := [
{tabtext}
]

/-! ### States, the step and the check -/

/-- The block `{block}`, letter `p` at phase `p`. -/
def {bname} : List Bool := {blist}

/-- The rank of the state with phase `p`, last readings `s` and window `w`: bits `{B} w .. {B} w + {B - 1}` of table
`{S} p + s`. -/
def rk (p s w : Nat) : Nat := (rankTabs.getD ({S} * p + s) 0 >>> ({B} * w)) % {1 << B}

/-- The reading `b` after the readings `s` (newest in bit 0) completes one of {hdrwords}. -/
def badB (s : Nat) (b : Bool) : Bool :=
  {bad}

/-- The last {K} readings after a step from phase `p` with window `w`: at phase {q} column 1 is read. -/
def sNext (p s w : Nat) : Nat := bif p == {q} then (2 * s + (w.testBit 0).toNat) % {S} else s

/-- The window of columns 1..{width} after a step from phase `p`, with column {width + 1} equal to `z`. -/
def wNext (p w : Nat) (z : Bool) : Nat := stripStep {width} ({bname}.getD p false) z w

/-- The certificate at one state: ranks are at most {M}; a state of rank 0 goes to states of rank 0 and completes no
forbidden word; a state of positive rank goes to states of smaller rank. -/
def nodeOK (p s w : Nat) : Bool :=
  let r := rk p s w
  let r0 := rk ((p + 1) % {P}) (sNext p s w) (wNext p w false)
  let r1 := rk ((p + 1) % {P}) (sNext p s w) (wNext p w true)
  decide (r ≤ {M}) && (r != 0 || (r0 == 0 && r1 == 0 && !(p == {q} && badB s (w.testBit 0)))) &&
    (r == 0 || (decide (r0 < r) && decide (r1 < r)))

/-- The certificate at every window, for the phase `p` and the readings `s`. -/
def partOK (p s : Nat) : Bool := allBelowT (fun w => nodeOK p s w) {n}

/-! ### The kernel checks, one per phase -/

{ok_thms}

theorem parts_ok : ∀ p, p < {P} → allBelowT (partOK p) {S} = true
{parts_cases}
  | p + {P}, h => absurd h (by omega)

theorem node_ok {{p s w : Nat}} (hp : p < {P}) (hs : s < {S}) (hw : w < 2 ^ {width}) : nodeOK p s w = true :=
  allBelowT_spec (allBelowT_spec (parts_ok p hp) s hs) w (by have : (2 : Nat) ^ {width} = {n} := rfl; omega)

theorem node_facts {{p s w : Nat}} (h : nodeOK p s w = true) (z : Bool) :
    rk p s w ≤ {M} ∧
      (rk p s w = 0 → rk ((p + 1) % {P}) (sNext p s w) (wNext p w z) = 0 ∧
        (p = {q} → badB s (w.testBit 0) = false)) ∧
      (rk p s w ≠ 0 → rk ((p + 1) % {P}) (sNext p s w) (wNext p w z) < rk p s w) := by
  unfold nodeOK at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, beq_iff_eq,
    Bool.not_eq_true'] at h
  obtain ⟨⟨hM, hA⟩, hB⟩ := h
  refine ⟨hM, fun h0 => ?_, fun h0 => ?_⟩
  · rcases hA with hA | ⟨⟨r0, r1⟩, hbad⟩
    · exact absurd h0 hA
    · refine ⟨by cases z <;> assumption, fun hp => ?_⟩
      subst hp
      simpa using hbad
  · rcases hB with hB | ⟨r0, r1⟩
    · exact absurd hB h0
    · cases z <;> assumption

/-! ### The driven right half and its states -/

/-- The center column `{block}` read from phase `ph`: letter `(t + ph) % {P}` of the block at step `t`. -/
def ctr (ph t : Nat) : Bool := {bname}.getD ((t + ph) % {P}) false

/-- The first `n` values of `f` as bits. -/
def pack (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => pack f n ||| ((f n).toNat <<< n)

theorem testBit_pack (f : Nat → Bool) : ∀ n i, (pack f n).testBit i = (decide (i < n) && f i)
  | 0, i => by simp [pack]
  | n + 1, i => by
    rw [pack, Nat.testBit_or, Nat.testBit_shiftLeft, testBit_toNat, testBit_pack f n i]
    rcases Nat.lt_trichotomy i n with h | h | h
    · simp [h, show ¬ n ≤ i by omega, show i < n + 1 by omega]
    · subst h; simp
    · simp [show ¬ i < n by omega, show i - n ≠ 0 by omega, show ¬ i < n + 1 by omega]

theorem pack_lt (f : Nat → Bool) (n : Nat) : pack f n < 2 ^ n :=
  Nat.lt_pow_two_of_testBit _ fun i hi => by
    rw [testBit_pack, decide_eq_false (by omega), Bool.false_and]

/-- The windows of columns `1..{width}` of `F`, step by step. -/
def win (F : Nat → Nat → Bool) : Nat → Nat
  | 0 => pack (fun i => F 0 (i + 1)) {width}
  | t + 1 => stripStep {width} (F t 0) (F t {width + 1}) (win F t)

theorem win_enc {{F : Nat → Nat → Bool}} (hF : IsR30 F) : ∀ t, EncF F {width} t 0 (win F t)
  | 0 => ⟨pack_lt _ _, fun i hi => by
      show (pack (fun i => F 0 (i + 1)) {width}).testBit i = F 0 (0 + 1 + i)
      rw [testBit_pack, decide_eq_true hi, Bool.true_and, show 0 + 1 + i = i + 1 by omega]⟩
  | t + 1 => encF_step hF (win_enc hF t)

/-- The last {NUMBERS[K]} readings of column 1 at the {step_name}s (newest in bit 0), starting from `0`. -/
def suf (ph : Nat) (F : Nat → Nat → Bool) : Nat → Nat
  | 0 => 0
  | t + 1 => sNext ((t + ph) % {P}) (suf ph F t) (win F t)

theorem suf_lt (ph : Nat) (F : Nat → Nat → Bool) : ∀ t, suf ph F t < {S}
  | 0 => Nat.zero_lt_succ _
  | t + 1 => by
    show sNext _ _ _ < {S}
    unfold sNext
    cases ((t + ph) % {P} == {q})
    · exact suf_lt ph F t
    · exact Nat.mod_lt _ (by decide)

theorem sNext_ne {{p s w : Nat}} (h : p ≠ {q}) : sNext p s w = s := by
  simp [sNext, h]

/-- One more reading. -/
def push (s : Nat) (a : Bool) : Nat := (2 * s + a.toNat) % {S}

section Driven

variable (R : Nat → Bool) (ph : Nat)

theorem win_succ (t : Nat) :
    win (drv (ctr ph) R) (t + 1) = wNext ((t + ph) % {P}) (win (drv (ctr ph) R) t) (drv (ctr ph) R t {width + 1}) := by
  show stripStep {width} (drv (ctr ph) R t 0) _ _ = stripStep _ _ _ _
  rw [drv_col0]
  rfl

theorem state_ok (t : Nat) :
    nodeOK ((t + ph) % {P}) (suf ph (drv (ctr ph) R) t) (win (drv (ctr ph) R) t) = true :=
  node_ok (Nat.mod_lt _ (by decide)) (suf_lt _ _ _) (win_enc (drv_isR30 _ _) t).1

/-- **Rank bound.** Along the driven right half the rank at time `t` is at most `{M} - t`. -/
theorem rank_bound : ∀ t, rk ((t + ph) % {P}) (suf ph (drv (ctr ph) R) t) (win (drv (ctr ph) R) t) ≤ {M} - t
  | 0 => (node_facts (state_ok R ph 0) false).1
  | t + 1 => by
    have ih := rank_bound t
    have hf := node_facts (state_ok R ph t) (drv (ctr ph) R t {width + 1})
    rw [← win_succ] at hf
    have hp : (t + 1 + ph) % {P} = ((t + ph) % {P} + 1) % {P} := by omega
    have hs : suf ph (drv (ctr ph) R) (t + 1) =
        sNext ((t + ph) % {P}) (suf ph (drv (ctr ph) R) t) (win (drv (ctr ph) R) t) := rfl
    rw [hp, hs]
    by_cases h0 : rk ((t + ph) % {P}) (suf ph (drv (ctr ph) R) t) (win (drv (ctr ph) R) t) = 0
    · rw [(hf.2.1 h0).1]; exact Nat.zero_le _
    · have := hf.2.2 h0; omega

/-- From time {M} on, no reading at the {step_name}s completes a forbidden word. -/
theorem no_bad (t : Nat) (ht : {M} ≤ t) (hp : (t + ph) % {P} = {q}) :
    badB (suf ph (drv (ctr ph) R) t) (drv (ctr ph) R t 1) = false := by
  have h0 := rank_bound R ph t
  have hf := node_facts (state_ok R ph t) false
  have hb := (hf.2.1 (by omega)).2 hp
  rwa [encF_head (win_enc (drv_isR30 _ _) t) (by decide)] at hb

/-- The readings move one place at each {step_name}. -/
theorem suf_period (t : Nat) (hp : (t + ph) % {P} = {q}) :
    suf ph (drv (ctr ph) R) (t + {P}) = push (suf ph (drv (ctr ph) R) t) (drv (ctr ph) R t 1) := by
  have h1 : suf ph (drv (ctr ph) R) (t + 1) = push (suf ph (drv (ctr ph) R) t) (drv (ctr ph) R t 1) := by
    show sNext ((t + ph) % {P}) _ _ = _
    rw [hp]
    unfold sNext push
    rw [encF_head (win_enc (drv_isR30 _ _) t) (by decide)]
    rfl
{chr(10).join(f'''  have h{k + 1} : suf ph (drv (ctr ph) R) (t + {k + 1}) = suf ph (drv (ctr ph) R) (t + {k}) := by
    show sNext ((t + {k} + ph) % {P}) (suf ph (drv (ctr ph) R) (t + {k})) (win (drv (ctr ph) R) (t + {k})) = _
    exact sNext_ne (by omega)''' for k in range(1, P))}
  rw [{', '.join(f'h{k}' for k in range(P, 0, -1))}]

end Driven

/-! ### The forbidden words -/

{chr(10).join(bad_lemmas)}

end {name}

open {name}

section Driven

variable (R : Nat → Bool) (ph : Nat)

{(chr(10) + chr(10)).join(word_thms)}

end Driven

/-! ### The readings as a sequence -/

namespace {name}

/-- {pred_doc} -/
def {pred} (b : Nat → Bool) (i0 : Nat) : Prop :=
  ∀ i, i0 ≤ i → {pred_body}

/-- Column 1 of the right half driven by `{block}` from phase `ph`, at the `i`-th {step_name} (the steps `t` with
`(t + ph) % {P} = {q}`). -/
def reading (R : Nat → Bool) (ph i : Nat) : Bool := drv (ctr ph) R ({P} * i + {off}) 1

end {name}

/-- **{headline_doc}** For every right half `R` and phase `ph`, the readings of column 1 at the {step_name}s avoid
{hdrwords} from the {i0}th on. -/
theorem {headline} (R : Nat → Bool) (ph : Nat) : {pred} (reading R ph) {i0} := by
  intro i hi
  have hp : ({P} * i + {off} + ph) % {P} = {q} := by omega
{chr(10).join(eqs)}
  rw [{erw}]
{wrap("  exact ⟨", tup.split(", "), ",", "⟩", "    ") if len(words) > 1 else "  exact " + tup}

/-! ### Every row whose center column repeats `{block}` -/

namespace {name}

/-- From time `T` on, a row whose center column repeats `{block}` from `T` has the right half driven by `{block}` from
phase `0`, started from its own right half at time `T`. -/
theorem evolve_eq_drv (init : Int → Bool) (T : Nat)
    (h : ∀ t, T ≤ t → evolve init t 0 = {bname}.getD ((t - T) % {P}) false) :
    ∀ t p : Nat, evolve init (T + t) (p : Int) = drv (ctr 0) (fun p => evolve init T (p : Int)) t p
  | 0, 0 => by
    rw [drv_col0]
    show evolve init (T + 0) 0 = {bname}.getD ((0 + 0) % {P}) false
    rw [Nat.add_zero, h T (Nat.le_refl T), Nat.sub_self]
  | 0, p + 1 => by rw [drv_init _ _ _ (by omega)]; rfl
  | t + 1, 0 => by
    rw [drv_col0]
    show evolve init (T + (t + 1)) 0 = {bname}.getD ((t + 1 + 0) % {P}) false
    rw [h (T + (t + 1)) (by omega), show T + (t + 1) - T = t + 1 + 0 by omega]
  | t + 1, q + 1 => by
    rw [show T + (t + 1) = (T + t) + 1 by omega]
    show rule30 (evolve init (T + t) (((q + 1 : Nat) : Int) - 1)) (evolve init (T + t) ((q + 1 : Nat) : Int))
        (evolve init (T + t) (((q + 1 : Nat) : Int) + 1)) =
      Rule30Jen.rule (drv _ _ t q) (drv _ _ t (q + 1)) (drv _ _ t (q + 2))
    rw [← evolve_eq_drv init T h t q, ← evolve_eq_drv init T h t (q + 1), ← evolve_eq_drv init T h t (q + 2),
      show ((q + 1 : Nat) : Int) - 1 = ((q : Nat) : Int) by omega,
      show ((q + 1 : Nat) : Int) + 1 = ((q + 2 : Nat) : Int) by omega]
    rfl

end {name}

/-- **{evolve_doc}** If the center column of a row repeats `{block}` from time `T` (letter
`(t - T) % {P}` at time `t`), then column 1 at the times `{times_doc}` avoids {hdrwords} from `i = {i0}` on. -/
theorem {headline}_evolve (init : Int → Bool) (T : Nat)
    (h : ∀ t, T ≤ t → evolve init t 0 = {bname}.getD ((t - T) % {P}) false) :
    {pred} (fun i => evolve init ({times}) 1) {i0} := by
  have e : (fun i => evolve init ({times}) 1) = reading (fun p => evolve init T (p : Int)) 0 := by
    funext i
    rw [show {times} = T + ({P} * i + {off.replace('ph', '0')}) by omega]
    exact evolve_eq_drv init T h ({P} * i + {off.replace('ph', '0')}) 1
  rw [e]
  exact {headline} _ 0
"""
    return head, body


def module_text(mod: Module) -> str:
    """The Lean module of a reading certificate."""
    head, body = module_parts(mod)
    return head + body + "\nend Rule30Open\n"


# ---------------------------------------------------------------------------------------------------------------------
# Several blocks in one module


ORDINALS = {1: "first", 2: "second", 3: "third", 4: "fourth", 5: "fifth", 6: "sixth"}


@dataclass(frozen=True)
class Statement:
    """What the certificate of a module proves: its states, the good states, the largest rank, the first reading from
    which the words are avoided, and the entropy of the sequences without the words."""

    states: int
    good: int
    max_rank: int
    first: int
    entropy: float


def statement(mod: Module) -> Statement:
    """The statement of the certificate of a module, as the module states it."""
    spec = Spec(mod.block, (mod.q,), mod.width, mod.words)
    good, rank = certificate(spec)  # (P, 2^W, 2^keep)
    assert (rank >= 0).all(), "entry is not forced"
    top, period = int(rank.max()), len(mod.block)
    first = max(-(-max(0, top - period * (len(u) - 1)) // period) for u in mod.words)
    return Statement(spec.states, int(good.sum()), top, first, word_entropy(mod.words))


def reading_module(block: str, q: int, width: int, words: tuple[str, ...]) -> Module:
    """The module record of one block in a collection: namespace `ReadingWords.B<block>`, headline
    `readings_<block>`, word theorems `no_<word>_time_<block>`, predicate `Avoids`."""
    whites = [p for p, c in enumerate(block) if c == "0"]
    step_name = f"{ORDINALS[whites.index(q) + 1]} white step"
    listed = ", ".join(f"`{u}`" for u in words)
    return Module(
        name=f"ReadingWords.B{block}", block=block, q=q, width=width, words=words,
        title=f"Under the center column `{block}`, column 1 at the {step_name} avoids {listed}",
        summary="", pred="Avoids",
        pred_doc=f"A sequence of bits has none of the factors {listed} from index `i0` on.",
        headline=f"readings_{block}", headline_doc="Readings.", evolve_doc="Readings of every row.",
        step_name=step_name, suffix=f"_{block}")


@dataclass(frozen=True)
class Collection:
    """Several reading certificates in one Lean module, one section and one namespace per block."""

    name: str
    title: str
    summary: str
    modules: tuple[Module, ...]


def collection_text(col: Collection) -> str:
    """The Lean module of several reading certificates: the body of `module_parts` for each block, in a section of its
    own, so that the `open` of its namespace ends with it."""
    bullets, sections = [], []
    for mod in col.modules:
        st = statement(mod)
        listed = ", ".join(f"`{u}`" for u in mod.words)
        bullets.append(wrap(f"* `{mod.headline}`, `{mod.headline}_evolve`: ", f"`{mod.block}` at the {mod.step_name} "
                            f"(phase {mod.q}), no {listed} from reading {st.first} on; width {mod.width}, ranks at "
                            f"most {st.max_rank}.".split(" "), "", "", "  "))
        _, body = module_parts(mod)
        sections.append(f"/-! ## Block `{mod.block}` -/\n\nsection B{mod.block}\n\n{body}\nend B{mod.block}\n")
    bullet_text = "\n".join(bullets)
    head = f"""module

public import Rule30Open.Foundations.Evolve
public import Ruliology.CellularAutomata.Rule30EtherThree

/-!
# {col.title}

{col.summary}

{bullet_text}

Each block has the certificate of `Rule30Open.Columns.Runs00001` in the namespace `ReadingWords.B<block>`
(`rankTabs`, `nodeOK`, `ok_p`, `parts_ok`, `rank_bound`, `no_bad`, `suf_period`, `evolve_eq_drv`) and its headline
theorems in `Rule30Open`: `no_<word>_time_<block>` by times, `readings_<block>` by readings and
`readings_<block>_evolve` for every row whose center column repeats the block.

The natural-language argument is `{col.name}.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

open Ruliology.CellularAutomata Rule30Ether Rule30EtherThree Rule30StripCertificates

"""
    return head + "\n".join(sections) + "\nend Rule30Open\n"


READING_WORDS: tuple[tuple[str, int, int, tuple[str, ...]], ...] = (  # (block, read phase, width, words)
    ("00011", 0, 7, ("00", "01010")),
    ("00101", 0, 6, ("010", "101", "1111")),
    ("00111", 0, 8, ("11", "1001")),
    ("01011", 2, 2, ("11",)),
    ("000001", 0, 7, ("11", "101")),
    ("000011", 0, 7, ("010", "101110")),
    ("000111", 0, 8, ("11", "101", "1001")),
    ("001101", 0, 6, ("11", "101")),
    ("010111", 0, 6, ("111", "1101")),
    ("0000001", 2, 10, ("00", "0110")),
    ("0000101", 5, 6, ("11",)),
    ("0001001", 0, 9, ("11",)),
    ("0001011", 0, 9, ("101", "1001", "10001")),
    ("0011011", 0, 10, ("000", "00111")),
    ("0110111", 0, 10, ("11", "101")),
)

COLLECTIONS = {
    "ReadingWords": Collection(
        name="ReadingWords",
        title="Beside a center column repeating a block, column 1 at one white step avoids a list of words",
        summary=("For each block below, let the center column repeat it and look at the right half it drives (the "
                 "kit's\n`Rule30Ether.drv`), from any initial right half, finite or not. At one white step of each "
                 "period column 1\nnever reads a word of the block's list once the last reading of the word is at "
                 "the block's largest rank or\nlater."),
        modules=tuple(reading_module(*row) for row in READING_WORDS)),
}


def text_of(name: str) -> str:
    """The text of the module or the collection of this name."""
    return module_text(MODULES[name]) if name in MODULES else collection_text(COLLECTIONS[name])


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("name", choices=sorted(MODULES) + sorted(COLLECTIONS))
    parser.add_argument("--check", action="store_true", help="compare with the file in Rule30Open/Columns")
    args = parser.parse_args()
    text = text_of(args.name)
    if args.check:
        same = (COLUMNS / f"{args.name}.lean").read_text(encoding="utf-8") == text
        print(f"{args.name}.lean is this text" if same else f"{args.name}.lean differs", file=sys.stderr)
        sys.exit(0 if same else 1)
    print(text, end="")


if __name__ == "__main__":
    main()
