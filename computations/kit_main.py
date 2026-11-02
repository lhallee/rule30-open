"""The blocks that the kit's main branch excludes beyond its pinned commit, and the entries here they reach.

This repository pins the kit at commit 932cf8d; its main branch, at a09f245, adds families that exclude whole classes of
blocks as the eventual period of the single cell's center column, for every transient and so in every rotation (the
main branch at 27060a7 adds no family to these: `Rule30Problem3Bounds`, `Rule30LeftAntiPeriod`,
`Rule30ZeroBoundaryStripeCascade`, `Rule30WedgeParity` and the seven period-two and Problem 2 bridge modules exclude no
block unconditionally, and the six modules below are unchanged):

- `Rule30White17Runs.not_eventually_long_white_runs`: every word 1^r1 0^q1 ... 1^rk 0^qk with every q >= 17;
- `Rule30GrammarRuns.not_eventually_grammar`: the same with every pair (r, q) in one of the categories
  (1, >= 10), (2, >= 8), (4, >= 7), (>= 9, >= 9);
- `Rule30ResetMixtures.not_eventually_reset_mixtures`: words 1 0^q1 ... 1 0^qk with every q >= 9 and one q >= 17;
- `Rule30BlackRuns.no_long_black_run_quarter`: a period P with a black run of r < P followed by a white cell and
  9 ceil((P - r) / 4) <= r, and `no_black_white_run_quarter`: a black run of s >= 9 followed by exactly r white cells
  and a black cell, s + r < P, with 1 + 9 floor((P - s - r + 1) / 4) <= r;
- `Rule30PaddedWords.no_padded_word` with its new bounds (`NEW_PADDED`): 0^q u for the tails u listed;
- `Rule30ParametricStripCertificates.not_eventually_paramBlackTable` (`PARAM_BLACK`): 1^r u for the 14 tails listed.

`new_blocks` lists the primitive blocks, as least rotations, that one of these excludes and the pinned kit does not
(`game.kit_blocks`). `repo_blocks` collects the blocks that the Lean modules here marked `kit: new` name, from their
binary and string literals of blocks (`wordOf P 0b...`, `(P, 0b...)`, `⟨P, 0b...`, bare `0b...` in lists of blocks, and
"0101..."), and from the trap and steering reductions of `coverage`. `overlaps` intersects the two.

    python -m computations.kit_main --max-period 21   # about 20 s
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

from tqdm.auto import tqdm

from computations import coverage, game

ROOT = Path(__file__).resolve().parent.parent

# `Rule30PaddedWords.paddedBound` at a09f245 for the tails whose bound is new since 932cf8d: the word 0^q u is
# excluded for q at least the bound. Pure black tails 1^k, k >= 3, k != 4, have the bound 17 (`no_padded_word_black`).
NEW_PADDED = (("1011", 9), ("10011", 9), ("11011", 9), ("101111", 9), ("1101", 11), ("1111", 7))
# `Rule30ParametricStripCertificates.paramBlackTable`: (length, bits, r0) of each tail u = wordOf length bits, most
# significant bit first; the word 1^r u is excluded for r >= r0.
PARAM_BLACK = ((1, 0, 9), (2, 0, 9), (3, 0, 9), (3, 2, 8), (4, 0, 9), (4, 2, 9), (4, 4, 9), (4, 6, 9), (5, 0, 9),
               (5, 2, 8), (5, 6, 15), (5, 10, 15), (5, 12, 9), (5, 14, 9))


def run_pairs(word: str) -> list[tuple[int, int]]:
    """The cyclic word as pairs (r, q): a maximal run of r 1s followed by a maximal run of q 0s, starting at the first
    run of 1s after a 0; empty when the word has no 0 or no 1."""
    if "0" not in word or "1" not in word:
        return []
    start = next(i for i in range(len(word)) if word[i] == "1" and word[i - 1] == "0")
    turned = word[start:] + word[:start]
    return [(len(ones), len(zeros)) for ones, zeros in re.findall(r"(1+)(0+)", turned)]


def white17(word: str) -> bool:
    """`Rule30White17Runs`: every run of 0s has length at least 17."""
    pairs = run_pairs(word)
    return bool(pairs) and all(q >= 17 for _, q in pairs)


def grammar(word: str) -> bool:
    """`Rule30GrammarRuns`: every pair is (1, >= 10), (2, >= 8), (4, >= 7) or (>= 9, >= 9)."""
    pairs = run_pairs(word)
    return bool(pairs) and all((r == 1 and q >= 10) or (r == 2 and q >= 8) or (r == 4 and q >= 7)
                               or (r >= 9 and q >= 9) for r, q in pairs)


def reset_mixture(word: str) -> bool:
    """`Rule30ResetMixtures`: every 1 isolated, every run of 0s at least 9 and one at least 17."""
    pairs = run_pairs(word)
    return bool(pairs) and all(r == 1 and q >= 9 for r, q in pairs) and any(q >= 17 for _, q in pairs)


def quarter(word: str) -> bool:
    """`Rule30BlackRuns.no_long_black_run_quarter` or `no_black_white_run_quarter` applies to some run of the word,
    with the period P its length. For theorem D the black run used is the longest suffix s of the maximal run with
    s + r < P, which makes P - s - r least."""
    P = len(word)
    pairs = run_pairs(word)
    for R, r in pairs:
        if 9 * -(-(P - R) // 4) <= R:
            return True
        s = min(R, P - r - 1)
        if s >= 9 and s + r < P and 1 + 9 * ((P - s - r + 1) // 4) <= r:
            return True
    return False


def padded(word: str) -> bool:
    """`Rule30PaddedWords.no_padded_word` with a bound new since the pin: some maximal run of q 0s followed by the
    rest u of the word, with u in `NEW_PADDED` and q at least its bound, or u = 1^k, k >= 3, k != 4, and q >= 17."""
    P = len(word)
    for i in range(P):
        if word[i] == "0" and word[i - 1] == "1":
            q = len(word[i:] + word[:i]) - len((word[i:] + word[:i]).lstrip("0"))
            u = (word[i:] + word[:i])[q:]
            if any(u == tail and q >= bound for tail, bound in NEW_PADDED):
                return True
            if set(u) == {"1"} and len(u) >= 3 and len(u) != 4 and q >= 17:
                return True
    return False


def param_black(word: str) -> bool:
    """`Rule30ParametricStripCertificates.not_eventually_paramBlackTable`: the word is 1^r u for a maximal run of r
    1s and a tail u of `PARAM_BLACK` with r >= r0."""
    P = len(word)
    tails = {format(bits, f"0{length}b"): r0 for length, bits, r0 in PARAM_BLACK}
    for i in range(P):
        if word[i] == "1" and word[i - 1] == "0":
            turned = word[i:] + word[:i]
            r = len(turned) - len(turned.lstrip("1"))
            u = turned[r:]
            if u in tails and r >= tails[u]:
                return True
    return False


FAMILIES = (("Rule30White17Runs", white17), ("Rule30GrammarRuns", grammar), ("Rule30ResetMixtures", reset_mixture),
            ("Rule30BlackRuns quarter", quarter), ("Rule30PaddedWords", padded),
            ("Rule30ParametricStripCertificates", param_black))


def main_reasons(word: str) -> list[str]:
    """The families of the main branch that exclude `word`."""
    return [name for name, test in FAMILIES if test(word)]


def new_blocks(max_period: int, progress: bool = True) -> dict[str, list[str]]:
    """Each primitive block of period at most `max_period`, as its least rotation, that a family of the main branch
    excludes and the pinned kit does not, with the families that exclude it."""
    pinned = game.kit_blocks(max_period)
    found: dict[str, list[str]] = {}
    for period in tqdm(range(1, max_period + 1), desc="periods", file=sys.stderr, disable=not progress):
        for word in game.necklaces(period):
            if word not in pinned and (reasons := main_reasons(word)):
                found[word] = reasons
    return found


def new_modules() -> list[str]:
    """The Lean modules here whose entry is marked `kit: new`, by name."""
    names = []
    for entry in sorted((ROOT / "Rule30Open").rglob("*.md")):
        head = entry.read_text().split("---")[1] if entry.read_text().startswith("---") else ""
        if re.search(r"^kit:\s*new\b", head, re.M) and entry.with_suffix(".lean").exists():
            names.append(entry.stem)
    return names


def lean_literals(text: str) -> set[str]:
    """The blocks a Lean source names, each as its least rotation: `wordOf P 0b...`, `(P, 0b...)` and `⟨P, 0b...`
    padded to P cells, other binary literals of at most 21 digits at their written length, and strings of 0s and 1s."""
    found = set()
    pattern = re.compile(r"(?:\(|⟨)(\d+), ?0b([01]+)|wordOf (\d+) 0b([01]+)")
    for match in pattern.finditer(text):
        period, bits = int(match.group(1) or match.group(3)), match.group(2) or match.group(4)
        if len(bits) <= period <= 21:
            found.add(bits.zfill(period))
    bare = pattern.sub(" ", text)
    found |= {bits for bits in re.findall(r"0b([01]+)\b", bare) if 2 <= len(bits) <= 21}
    found |= {word for word in re.findall(r'"([01]{2,21})"', text)}
    return {game.least_rotation(word) for word in found}


def repo_blocks() -> dict[str, set[str]]:
    """Each block a `kit: new` module here names or reduces, as its least rotation, with the modules."""
    owners: dict[str, set[str]] = {}
    modules = set(new_modules())
    for path in sorted((ROOT / "Rule30Open").rglob("*.lean")):
        if path.stem in modules:
            for word in lean_literals(path.read_text()):
                owners.setdefault(word, set()).add(path.stem)
    for word, module in coverage.module_blocks():
        if module in modules:
            owners.setdefault(word, set()).add(module)
    for word in coverage.steered_blocks():
        owners.setdefault(word, set()).add("LockBlocks")
    return owners


def overlaps(max_period: int, progress: bool = True) -> list[tuple[str, list[str], list[str]]]:
    """The blocks of `new_blocks` that a `kit: new` module here names or reduces: block, families, modules."""
    fresh = new_blocks(max_period, progress)
    owners = repo_blocks()
    return [(word, fresh[word], sorted(owners[word])) for word in sorted(fresh, key=lambda w: (len(w), w))
            if word in owners]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--max-period", type=int, default=21)
    args = parser.parse_args()
    fresh = new_blocks(args.max_period)
    by_period: dict[int, int] = {}
    for word in fresh:
        by_period[len(word)] = by_period.get(len(word), 0) + 1
    print("new kit blocks by period:", dict(sorted(by_period.items())))
    print("by family:", {name: sum(name in r for r in fresh.values()) for name, _ in FAMILIES})
    hits = overlaps(args.max_period, progress=False)
    print(f"{len(hits)} blocks named by kit: new modules here")
    for word, reasons, modules in hits:
        print(f"  {word} (period {len(word)}): {', '.join(reasons)}; here {', '.join(modules)}")


if __name__ == "__main__":
    main()
