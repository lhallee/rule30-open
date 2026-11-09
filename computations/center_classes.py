"""Which finite rows of a box have equal center columns: on every box of up to 21 cells, exactly the rows that the kit's
stripe relation at time 0 or 1 (S01) joins.

A row of the box [-A, B] is an integer x < 2^(A + B + 1) whose bit k is cell B - k, so cell 0 is bit B: the frame of the
kit's `Rule30StripeMeeting` with center index B. One step of Rule 30 is the kit's Phi(y) = y xor ((y << 1) | (y << 2)),
and the center cell at time t is bit B + t of Phi^t(x). Bit i of Phi(y) reads bits i, i - 1 and i - 2 of y only, so the
first H center cells read y modulo 2^(B + H) only.

The kit proves that S01 rows have equal center columns, and the Lean modules `Rule30Open.Frames.StripeClassCount` and
`Rule30Open.Frames.StripeClasses` prove that S01 has `stripe_classes.formula(A, B)` = 2^(A + B) + 3 * 2^(A - 1)
classes on the box (A, B >= 1), so that the box has at most that many center columns (`box_columns`). So when the
census below finds that many rows with pairwise different center columns, the rows with equal center columns are
exactly the S01 classes, with no horizon assumed. The definitions of the kit and the representative of the Lean
modules, row by row, are in `computations.stripe_classes`; this module does the same for every row at once.

1. `columns`: the first H center cells of each row, packed with time 0 in the top bit of word 0, and `prefix_groups`,
   the rows grouped by them; `census_c` gives the same groups from the C program `center_classes_census.c`.
2. `s01_labels`: the S01 classes, by joining the rows that share a key (time, cut j, the bits above j + 1, and at time
   1 cell 0), with the kit's tail automaton `tailNext` deciding `StripeWord`; `family_labels`: the same classes from
   their explicit description in the entry, with no relation and no step of the rule.
3. `split`: one row of each S01 class of every prefix group that holds several classes, all stepped together until
   every two of them have differed, or the horizon T2. With no survivor the box has formula(A, B) center columns.
4. `census`, `box_census`, `part_census`: the whole method on every row of a box, or on the rows of one left part
   (cells <= 0) with every right half inside [1, B]: the classes, the latest separation, the longest common prefix of
   two rows with different left edges, and the class-size law per left part (`stripe_classes.class_size_law`).
5. `pair_profile`: when two rows first differ at the center, and from when their left halves agree.

    python -m computations.center_classes boxes                      # every box of up to 11 cells, T1 = 400: 5 s
    python -m computations.center_classes boxes --widths 12-21 --c   # every box of 12 to 21 cells: 15 min, 0.5 GB
    python -m computations.center_classes parts                      # 24 left parts, B = 1 .. 10: 10 s
    python -m computations.center_classes parts --c --B 16 \\
        --parts 3,6,13,25,55,100,222,401,891,1602,3558,6428,14259,25646,2741   # 15 left parts, B = 16: 17 s
    python -m computations.center_classes parts --c --B 20 --parts 1602      # 2^20 rows: 35 s, 0.3 GB
    python -m computations.center_classes pair 612687 615009 --B 10   # the last pair of [-10, 10] to differ: 1 s

With --c the prefix groups come from the C program, compiled on first use, at T1 = 128; the split runs to T2 = 20,000.
"""

from __future__ import annotations

import argparse
import subprocess
import sys
from collections import Counter
from collections.abc import Sequence
from dataclasses import dataclass
from pathlib import Path

import numpy as np
from scipy.sparse import coo_matrix
from scipy.sparse.csgraph import connected_components
from tqdm.auto import tqdm

from computations.stripe_classes import class_size_law, classes_all_pairs, formula, phi

U64 = np.uint64
ONE, TWO, S62, S63 = U64(1), U64(2), U64(62), U64(63)
# The kit's tailNext (Rule30Certificates.StripeMeeting): TAIL[s, b] is the state after reading bit b in state s, and
# the bits read so far, from bit 0 upward, form a StripeWord exactly in the states 1 and 3 (`tailFold_accept_iff`).
TAIL = np.array([[0, 1], [2, 3], [4, 3], [2, 4], [4, 4]], dtype=np.uint8)  # (5, 2)
ACCEPT = np.array([False, True, False, True, False])  # (5,)


# ---------------------------------------------------------------------------------------------------------------------
# The laws
# ---------------------------------------------------------------------------------------------------------------------

def part_law(lam: int, B: int) -> int:
    """The number of S01 classes of the 2^B rows with left part `lam` and right half inside [1, B] (B >= 1): 2^(B - 1),
    plus one unless `lam` ends in 0 1; `StripeClasses.right_half_columns` bounds their center columns by it."""
    return sum(class_size_law(B, lam % 4 == 1).values())


# ---------------------------------------------------------------------------------------------------------------------
# Rows and their center columns
# ---------------------------------------------------------------------------------------------------------------------

def box_rows(A: int, B: int) -> np.ndarray:
    """Every row supported in [-A, B], zero row included, in increasing order."""
    return np.arange(1 << (A + B + 1), dtype=U64)  # (2^(A + B + 1),)


def part_rows(lam: int, B: int) -> np.ndarray:
    """Every row with left part `lam` (cells <= 0, bit 0 of `lam` is cell 0) and right half inside [1, B]."""
    return U64(lam << B) | np.arange(1 << B, dtype=U64)  # (2^B,)


def phi_words(Y: np.ndarray) -> None:
    """Phi in place on rows held as words (bit i of a row is bit i % 64 of word i // 64), modulo 2^(64 * words)."""
    # Y: (n, w) uint64
    up = (Y << ONE) | (Y << TWO)  # (n, w)
    if Y.shape[1] > 1:
        up[:, 1:] |= (Y[:, :-1] >> S63) | (Y[:, :-1] >> S62)
    Y ^= up


def columns(rows: np.ndarray, B: int, H: int, progress: bool = False) -> np.ndarray:
    """The first H center cells of each row, packed: cell t is bit 63 - t % 64 of word t // 64, so the order of the
    rows of words is the lexicographic order of the columns. Rows of up to 62 cells."""
    # rows: (n,) uint64
    n = rows.size
    words = (B + H) // 64 + 1
    Y = np.zeros((n, words), dtype=U64)  # (n, words), the rows at time t
    Y[:, 0] = rows
    out = np.zeros((n, (H + 63) // 64), dtype=U64)  # (n, ceil(H / 64))
    width = int(rows.max()).bit_length() if n else 0
    for t in tqdm(range(H), desc="columns", file=sys.stderr, disable=not progress, leave=False):
        k = B + t
        out[:, t >> 6] |= ((Y[:, k >> 6] >> U64(k & 63)) & ONE) << U64(63 - (t & 63))
        live = min(words, (width + 2 * t + 2 + 63) // 64)  # the row after the step lies below bit width + 2t + 2
        phi_words(Y[:, :live])
    return out  # (n, ceil(H / 64))


def bit_length(x: np.ndarray) -> np.ndarray:
    """Bit length of each 64-bit word."""
    # x: (n,) uint64
    x = x.copy()  # (n,)
    out = np.zeros(x.shape, dtype=np.int64)  # (n,)
    for s in (32, 16, 8, 4, 2, 1):
        big = x >= (ONE << U64(s))  # (n,)
        out[big] += s
        x[big] >>= U64(s)
    return out + (x > 0)  # (n,)


def common_prefix(a: np.ndarray, b: np.ndarray, H: int) -> np.ndarray:
    """The length of the common prefix of the packed columns a[i] and b[i], H when they agree on all H cells."""
    # a, b: (n, m) uint64
    x = a ^ b  # (n, m)
    differs = x != 0  # (n, m)
    first = np.argmax(differs, axis=1)  # (n,), the first word that differs (0 if none)
    word = x[np.arange(x.shape[0]), first]  # (n,)
    length = first * 64 + 64 - bit_length(word)  # (n,)
    return np.where(differs.any(axis=1), np.minimum(length, H), H)  # (n,)


def left_edges(rows: np.ndarray, B: int) -> np.ndarray:
    """The cell of the leftmost black cell of each row (rows nonzero)."""
    # rows: (n,) uint64
    return B - (bit_length(rows) - 1)  # (n,)


def prefix_groups(rows: np.ndarray, B: int, T1: int, progress: bool = False) -> tuple[np.ndarray, int, int]:
    """Group the rows by their first T1 center cells. Returns the group of each row (groups numbered in the
    lexicographic order of their prefixes), the longest common prefix of two nonzero rows with different left edges
    (-1 if every edge is the same) and the longest common prefix of two rows in different groups (-1 if one group).
    Both maxima are attained by rows adjacent in the sorted order: the common prefix of two rows is the least over the
    adjacent pairs between them."""
    # rows: (n,) uint64
    cols = columns(rows, B, T1, progress)  # (n, m)
    order = np.lexsort(cols.T[::-1])  # (n,), word 0 most significant
    ordered = cols[order]  # (n, m)
    new = np.ones(rows.size, dtype=bool)  # (n,)
    new[1:] = (ordered[1:] != ordered[:-1]).any(axis=1)
    group = np.empty(rows.size, dtype=np.int64)  # (n,)
    group[order] = np.cumsum(new) - 1
    lcp = common_prefix(ordered[1:], ordered[:-1], T1)  # (n - 1,), adjacent rows
    x = rows[order]  # (n,)
    both = np.flatnonzero((x[1:] != 0) & (x[:-1] != 0))  # (k,), adjacent pairs of nonzero rows
    apart = both[left_edges(x[1:][both], B) != left_edges(x[:-1][both], B)]  # (k',)
    lcp_edge = int(lcp[apart].max()) if apart.size else -1
    lcp_groups = int(lcp[new[1:]].max()) if new[1:].any() else -1
    return group, lcp_edge, lcp_groups


def census_binary(optimize: bool = True) -> Path:
    """computations/center_classes_census.c, compiled once and kept for later processes (`seed_onsets.compiled`)."""
    from computations import seed_onsets
    return seed_onsets.compiled("center_classes_census", ("-O2" if optimize else "-O0", "-w"))


def census_c(rows: np.ndarray, mode: str, first: int, B: int, T1: int, optimize: bool = True,
             progress: bool = False) -> tuple[np.ndarray, int, int]:
    """`prefix_groups` from the C program: mode "box" with first = A, or "part" with first = the left part, and `rows`
    equal to `box_rows(A, B)` or `part_rows(first, B)`. The groups of two or more rows are numbered in the order of the
    program's output, the rows alone in their prefix after them; the zero row of a box, which the program leaves out,
    is alone (its column is white, and no other row's is: no column of a nonzero finite row is eventually constant)."""
    # rows: (n,) uint64, increasing
    run = subprocess.run([str(census_binary(optimize)), mode, str(first), str(B), str(T1)], stdout=subprocess.PIPE,
                         stderr=None if progress else subprocess.DEVNULL, text=True, check=True)
    group = np.full(rows.size, -1, dtype=np.int64)  # (n,)
    count, stats = 0, {}
    for line in run.stdout.splitlines():
        if line.startswith("G"):
            group[np.searchsorted(rows, np.array(line.split()[1:], dtype=U64))] = count
            count += 1
        elif line.startswith("# lcp"):
            key, _, value = line[2:].split()[0].partition("=")
            stats[key] = int(value)
    alone = group < 0  # (n,)
    group[alone] = count + np.arange(int(alone.sum()))
    return group, stats["lcp_left_edge"], stats["lcp_groups"]


# ---------------------------------------------------------------------------------------------------------------------
# The classes of the kit's stripe relation at time 0 or 1
# ---------------------------------------------------------------------------------------------------------------------

def stripe_cuts(rows: np.ndarray, c: int) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    """Every cut j <= c of the kit's `StripeRelated` that each row offers: bits 0 .. j form a StripeWord (so bit j is
    black) and bit j + 1 is white. Two rows that offer the same cut with the same bits above j + 1 are related. Returns
    the index of the row, j and the bits above j + 1, one entry per cut."""
    # rows: (n,) uint64
    state = np.zeros(rows.size, dtype=np.uint8)  # (n,), tailNext after bits 0 .. j
    index, cut, high = [], [], []
    for j in range(c + 1):
        state = TAIL[state, ((rows >> U64(j)) & ONE).astype(np.uint8)]
        ok = ACCEPT[state] & (((rows >> U64(j + 1)) & ONE) == 0)  # (n,)
        i = np.flatnonzero(ok)  # (k,)
        index.append(i)
        cut.append(np.full(i.size, j, dtype=np.int64))
        high.append(rows[i] >> U64(j + 2))
        if (state == 4).all():
            break
    return np.concatenate(index), np.concatenate(cut), np.concatenate(high)  # each (cuts,)


def s01_labels(rows: np.ndarray, B: int, times: Sequence[int] = (0, 1)) -> np.ndarray:
    """The component of each row under S01 among `rows` (distinct, of up to 61 cells), numbered 0, 1, ...: rows that
    share a key (time, cut j, the bits above j + 1, and at time 1 cell 0) are joined."""
    # rows: (n,) uint64
    n = rows.size
    index, key = [], []
    if 0 in times:
        i, j, h = stripe_cuts(rows, B)
        index.append(i)
        key.append((h << U64(8)) | (j.astype(U64) << U64(2)))
    if 1 in times:
        i, j, h = stripe_cuts(rows ^ ((rows << ONE) | (rows << TWO)), B + 1)
        index.append(i)
        key.append((h << U64(8)) | (j.astype(U64) << U64(2)) | TWO | ((rows[i] >> U64(B)) & ONE))
    rows_of_key = np.concatenate(index)  # (e,)
    keys, node = np.unique(np.concatenate(key), return_inverse=True)  # (K,), (e,)
    graph = coo_matrix((np.ones(rows_of_key.size, dtype=np.int8), (rows_of_key, n + node)),
                       shape=(n + keys.size, n + keys.size))
    _, label = connected_components(graph, directed=False)
    return np.unique(label[:n], return_inverse=True)[1].astype(np.int64)  # (n,)


def family_labels(rows: np.ndarray, B: int) -> np.ndarray:
    """The S01 components as the entry describes them, with no relation and no step: a row w tau whose cells q .. B
    (q >= 0) form a StripeWord tau lies in the family of (q, w), which holds every w tau' with tau' a StripeWord on
    q .. B, except the word 1 0 .. 0 when cell q - 1 is black. Families that meet are nested, so each row's class is
    its family with the least q, or the row alone if it lies in none."""
    # rows: (n,) uint64
    state = np.zeros(rows.size, dtype=np.uint8)  # (n,), tailNext after bits 0 .. j, that is cells B - j .. B
    best = np.full(rows.size, -1, dtype=np.int64)  # (n,), the largest j (least q = B - j) of a family of the row
    for j in range(B + 1):
        state = TAIL[state, ((rows >> U64(j)) & ONE).astype(np.uint8)]
        lone = (rows & ((ONE << U64(j + 1)) - ONE)) == (ONE << U64(j))  # (n,), tau = 1 0 .. 0
        black = ((rows >> U64(j + 1)) & ONE) == 1  # (n,), cell q - 1
        best[ACCEPT[state] & ~(lone & black)] = j
    member = best >= 0  # (n,)
    shift = np.where(member, best + 1, 0).astype(U64)  # (n,)
    key = np.where(member, ((rows >> shift) << U64(6)) | shift, (rows << U64(6)) | U64(63))  # (n,), w and q
    return np.unique(key, return_inverse=True)[1].astype(np.int64)  # (n,)


def same_partition(a: np.ndarray, b: np.ndarray) -> bool:
    """Two labelings of the same items define the same partition."""
    # a, b: (n,) int64
    pairs = np.unique(np.stack([a, b], axis=1), axis=0)  # (p, 2)
    return pairs.shape[0] == np.unique(a).size == np.unique(b).size


# ---------------------------------------------------------------------------------------------------------------------
# Splitting the groups
# ---------------------------------------------------------------------------------------------------------------------

@dataclass(frozen=True)
class Split:
    groups: int  # prefix groups that hold two or more S01 components
    latest: int  # the latest time at which two of their components first differ (-1 if there are none)
    pair: tuple[int, int] | None  # two rows that first differ at `latest`
    survivors: int  # sets of two or more components that still agree at T2


def dense(values: np.ndarray, bound: int) -> np.ndarray:
    """Renumber nonnegative integers below `bound` as 0, 1, ... in increasing order."""
    # values: (n,) int64
    present = np.zeros(bound, dtype=bool)  # (bound,)
    present[values] = True
    return (np.cumsum(present) - 1)[values]  # (n,)




def split(rows: np.ndarray, B: int, group: np.ndarray, label: np.ndarray, T2: int,
          progress: bool = False) -> Split:
    """Follow every prefix group that holds several S01 components until its components have pairwise differed: one row
    per component (all rows of a component have one column, by the kit), stepped in lockstep from time 0, the classes
    of equal prefixes refined at each step, and a row dropped once no other row of its group shares its prefix. Checks
    first that no S01 component meets two groups, as the kit's `stripe_related_same_trace` requires."""
    # rows: (n,) uint64; group, label: (n,) int64
    first = np.unique(label, return_index=True)[1]  # (components,), one row of each component
    assert np.array_equal(group[np.argsort(label, kind="stable")], np.repeat(group[first], np.bincount(label))), \
        "an S01 component meets two prefix groups"
    rep_group = group[first]  # (components,)
    several = np.bincount(rep_group)[rep_group] >= 2  # (components,)
    origin = rows[first[several]]  # (m,), the representatives at time 0
    cls = dense(rep_group[several], int(group.max()) + 1) if origin.size else np.zeros(0, dtype=np.int64)  # (m,)
    groups = int(cls.max()) + 1 if cls.size else 0
    width = int(rows.max()).bit_length() if rows.size else 0
    Y = origin[:, None].copy()  # (m, words): the representatives at time t, bit i in word i // 64
    latest, pair = -1, None
    bar = tqdm(total=origin.size, desc="split", file=sys.stderr, disable=not progress, leave=False)
    t = 0
    while t < T2 and cls.size:
        k = B + t
        bit = ((Y[:, k >> 6] >> U64(k & 63)) & ONE).astype(np.int64)  # (m,), the center cell at time t
        total = np.bincount(cls)  # (classes,)
        ones = np.bincount(cls, weights=bit, minlength=total.size).astype(np.int64)  # (classes,)
        parted = np.flatnonzero((ones > 0) & (ones < total))  # (j,), classes that cell t splits
        if parted.size:  # two rows of one class, so of one group and two components, first differ at t
            members = np.flatnonzero(cls == parted[0])  # (g,)
            latest = t
            pair = (int(origin[members[bit[members] == 0][0]]), int(origin[members[bit[members] == 1][0]]))
        new = dense(2 * cls + bit, 2 * total.size)  # (m,)
        keep = np.bincount(new)[new] >= 2  # (m,)
        bar.update(int((~keep).sum()))
        Y, cls, origin = Y[keep], new[keep], origin[keep]
        live = (width + 2 * t + 2 + 63) // 64  # the rows after this step lie below bit width + 2t + 2
        if live > Y.shape[1]:
            Y = np.concatenate([Y, np.zeros((Y.shape[0], live - Y.shape[1]), dtype=U64)], axis=1)
        phi_words(Y)
        t += 1
    bar.close()
    return Split(groups=groups, latest=latest, pair=pair, survivors=int(np.unique(cls).size))


# ---------------------------------------------------------------------------------------------------------------------
# The census of a set of rows
# ---------------------------------------------------------------------------------------------------------------------

@dataclass(frozen=True)
class Census:
    name: str
    B: int
    rows: int
    groups: int  # prefix groups of two or more rows at T1
    members: int  # rows in those groups
    lcp_edge: int  # longest common prefix of two rows with different left edges (-1 if every edge is the same)
    lcp_groups: int  # longest common prefix of two rows in different prefix groups
    components: int  # S01 components
    components0: int  # components of the time-0 relation alone
    split: Split
    mixed: int  # S01 components that hold two different left halves (cells < 0)
    parts: int  # left parts (cells <= 0) among the rows
    part_misses: int  # left parts whose number of classes is not `part_law`
    size_misses: int  # left parts whose class sizes are not `class_size_law`
    sizes: Counter[int]  # {size: number of classes}, over every left part
    families: bool  # the S01 components are the classes of `family_labels`

    @property
    def classes(self) -> int | None:
        """The number of distinct center columns, when no group survived the split."""
        return self.components if self.split.survivors == 0 else None

    @property
    def latest(self) -> int:
        """The latest time at which two rows with different columns first differ."""
        return self.split.latest if self.split.groups else self.lcp_groups


def law_checks(rows: np.ndarray, B: int, label: np.ndarray) -> tuple[int, int, int, Counter[int]]:
    """The left parts of the rows, how many of them miss `part_law` and how many miss `class_size_law` (B >= 1), and
    the class sizes over all of them; each class is taken within the left part of its first row."""
    # rows: (n,) uint64; label: (n,) int64
    part = (rows >> U64(B)).astype(np.int64)  # (n,), the left part of each row
    lams, pid = np.unique(part, return_inverse=True)  # (p,), (n,)
    first = np.unique(label, return_index=True)[1]  # (components,)
    size = np.bincount(label)  # (components,)
    cp = pid[first]  # (components,), the left part of each component
    count = np.bincount(cp, minlength=lams.size)  # (p,)
    sizes = Counter(size.tolist())
    if B == 0:
        return lams.size, 0, 0, sizes
    end = (lams & 3) == 1  # (p,)
    part_miss = int((count != 2 ** (B - 1) + (~end)).sum())
    table = np.zeros((lams.size, B + 2), dtype=np.int64)  # (p, B + 2): classes of each size in each left part
    np.add.at(table, (cp, np.minimum(size, B + 1)), 1)
    expect = np.zeros((2, B + 2), dtype=np.int64)  # (2, B + 2): row 1 for the left parts ending in 0 1
    for row in (0, 1):
        for k, v in class_size_law(B, bool(row)).items():
            expect[row, k] = v
    over = np.zeros(lams.size, dtype=bool)  # (p,)
    np.logical_or.at(over, cp, size > B + 1)
    size_miss = int(((table != expect[end.astype(np.int64)]).any(axis=1) | over).sum())
    return lams.size, part_miss, size_miss, sizes


def census(rows: np.ndarray, B: int, T1: int, T2: int, name: str, c_mode: tuple[str, int] | None = None,
           progress: bool = False) -> Census:
    """The whole method on a set of distinct rows: prefix groups at T1 (numpy, or the C program for `c_mode` =
    ("box", A) or ("part", lam)), S01 components, the split to T2, and the laws per left part."""
    # rows: (n,) uint64, increasing
    if c_mode is None:
        group, lcp_edge, lcp_groups = prefix_groups(rows, B, T1, progress)
    else:
        group, lcp_edge, lcp_groups = census_c(rows, c_mode[0], c_mode[1], B, T1, progress=progress)
    size = np.bincount(group)  # (groups,)
    label = s01_labels(rows, B)  # (n,)
    label0 = s01_labels(rows, B, times=(0,))  # (n,)
    result = split(rows, B, group, label, T2, progress)
    halves = np.unique(np.stack([label, (rows >> U64(B + 1)).astype(np.int64)], axis=1), axis=0)  # (h, 2)
    parts, part_misses, size_misses, sizes = law_checks(rows, B, label)
    return Census(name=name, B=B, rows=rows.size, groups=int((size >= 2).sum()), members=int(size[size >= 2].sum()),
                  lcp_edge=lcp_edge, lcp_groups=lcp_groups, components=int(label.max()) + 1,
                  components0=int(label0.max()) + 1, split=result,
                  mixed=int(halves.shape[0] - (int(label.max()) + 1)), parts=parts, part_misses=part_misses,
                  size_misses=size_misses, sizes=sizes, families=same_partition(label, family_labels(rows, B)))


def box_census(A: int, B: int, T1: int = 128, T2: int = 20000, use_c: bool = True, progress: bool = False) -> Census:
    """`census` of every row supported in [-A, B]."""
    return census(box_rows(A, B), B, T1, T2, f"[{-A}, {B}]", ("box", A) if use_c else None, progress)


def part_census(lam: int, B: int, T1: int = 128, T2: int = 20000, use_c: bool = True,
                progress: bool = False) -> Census:
    """`census` of the rows with left part `lam` and right half inside [1, B]."""
    return census(part_rows(lam, B), B, T1, T2, f"left part {lam}, [1, {B}]", ("part", lam) if use_c else None,
                  progress)


def describe(c: Census, law: int) -> str:
    """One line per census."""
    s = c.split
    pair = f" (rows {s.pair[0]}, {s.pair[1]})" if s.pair and s.groups else ""
    return (f"{c.name}: rows {c.rows:,}, prefix groups {c.groups:,} ({c.members:,} rows), S01 components "
            f"{c.components:,} (time 0 alone {c.components0:,}), groups split {s.groups:,}, survivors {s.survivors}, "
            f"latest separation {c.latest}{pair}, classes {c.classes if c.classes is None else format(c.classes, ',')}"
            f" {'=' if c.classes == law else '!='} law {law:,}; {'' if c.families else 'not '}the families; components "
            f"with two left halves {c.mixed}; left parts {c.parts:,}, missing the count law {c.part_misses}, the size "
            f"law {c.size_misses}; different left edges share at most {c.lcp_edge} cells")


@dataclass(frozen=True)
class PairProfile:
    differ: list[int]  # the cells where the two rows differ at time 0
    first: int  # the first time their center cells differ (-1 if none before the horizon)
    merged: int  # the least t0 such that their left halves (cells < 0) agree at every time t0 .. first
    front: tuple[int, int]  # least and largest leftmost differing cell over the times merged .. first - 1


def pair_profile(a: int, b: int, B: int, T: int) -> PairProfile:
    """Two different rows of a box with right end B, stepped until their center cells differ or T steps."""
    ya, yb = a, b
    agree, fronts, first = [], [], -1
    for t in range(T):
        d = ya ^ yb  # bit k is cell B + t - k
        if (d >> (B + t)) & 1:
            first = t
            break
        agree.append(d >> (B + t + 1) == 0)
        fronts.append(B + t - (d.bit_length() - 1))
        ya, yb = phi(ya), phi(yb)
    end = len(agree)
    merged = end
    while merged > 0 and agree[merged - 1]:
        merged -= 1
    window = fronts[merged:end] or [0]
    return PairProfile(differ=[B - k for k in range((a ^ b).bit_length()) if ((a ^ b) >> k) & 1], first=first,
                       merged=merged, front=(min(window), max(window)))


# ---------------------------------------------------------------------------------------------------------------------
# Command line
# ---------------------------------------------------------------------------------------------------------------------

def _range(text: str) -> list[int]:
    out: list[int] = []
    for piece in text.split(","):
        lo, _, hi = piece.partition("-")
        out += list(range(int(lo), int(hi or lo) + 1))
    return out


def _pair(text: str) -> tuple[int, int]:
    a, b = text.split(",")
    return int(a), int(b)


def run_boxes(args: argparse.Namespace) -> None:
    widths = _range(args.widths)
    boxes = [(W - 1 - B, B) for W in widths for B in range(W)]
    summary: dict[int, list[tuple[Census, int]]] = {W: [] for W in widths}
    paired: dict[int, bool] = {}
    for A, B in tqdm(boxes, desc="boxes", file=sys.stderr, disable=len(boxes) < 30):
        c = box_census(A, B, args.t1, args.t2, use_c=args.c, progress=args.c)
        law = formula(A, B)
        summary[A + B + 1].append((c, law))
        if A + B + 1 <= args.pairs:  # the kit's relation transcribed literally, on every pair, joined by union-find
            ok = same_partition(s01_labels(box_rows(A, B), B), np.array(classes_all_pairs(A, B)))
            paired[A + B + 1] = paired.get(A + B + 1, True) and ok
        print(describe(c, law), flush=True)
    for W, runs in summary.items():
        misses = sum(c.classes != law or c.mixed > 0 or c.part_misses > 0 or c.size_misses > 0 or not c.families
                     for c, law in runs)
        late = max(runs, key=lambda r: r[0].latest)[0]
        edge = max(runs, key=lambda r: r[0].lcp_edge)[0]
        pairs = "" if W not in paired else f"; every pair: {'the same' if paired[W] else 'NOT the same'} classes"
        print(f"width {W}: {len(runs)} boxes, {misses} miss a law; latest separation {late.latest} on {late.name}; "
              f"rows with different left edges share at most {edge.lcp_edge} cells, on {edge.name}{pairs}")


def run_parts(args: argparse.Namespace) -> None:
    misses = 0
    for lam in _range(args.parts):
        for B in _range(args.B):
            c = part_census(lam, B, args.t1, args.t2, use_c=args.c, progress=args.c)
            law = part_law(lam, B)
            misses += c.classes != law or c.size_misses > 0 or not c.families
            print(describe(c, law) + f"; sizes {dict(sorted(c.sizes.items()))}", flush=True)
    print(f"{misses} runs miss the count law or the size law")


def run_pair(args: argparse.Namespace) -> None:
    a, b = args.rows
    p = pair_profile(a, b, args.B, args.steps)
    width = max(a, b).bit_length()
    for x in (a, b):
        print(f"row {x}: cells {args.B - width + 1} .. {args.B}: " + format(x, f"0{width}b").replace("0", "."))
    print(f"they differ at time 0 on cells {sorted(p.differ)}; their center cells first differ at t = {p.first}; "
          f"their left halves agree at every time from {p.merged} to then, while the leftmost differing cell stays "
          f"between cells {p.front[0]} and {p.front[1]}")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = parser.add_subparsers(dest="command", required=True)
    p = sub.add_parser("boxes", help="every box whose number of cells is in --widths")
    p.add_argument("--widths", default="1-11", help="e.g. 1-11 or 12,13")
    p.add_argument("--pairs", type=int, default=6, help="also join every pair of the boxes of up to this many cells")
    p.set_defaults(run=run_boxes)
    p = sub.add_parser("parts", help="the rows of each left part in --parts with right halves inside [1, B]")
    p.add_argument("--parts", default="0-15,25,55,100,222,401,891,1602,2741", help="left parts, bit 0 = cell 0")
    p.add_argument("--B", default="1-10")
    p.set_defaults(run=run_parts)
    for p in list(sub.choices.values()):
        p.add_argument("--c", action="store_true", help="prefix groups from center_classes_census.c")
        p.add_argument("--t1", type=int, help="horizon of the prefix groups: 128 with --c (at most 192), else 400")
        p.add_argument("--t2", type=int, default=20000, help="horizon of the split")
    p = sub.add_parser("pair", help="when two rows of a box first differ, and where their difference lies")
    p.add_argument("rows", type=int, nargs=2)
    p.add_argument("--B", type=int, required=True, help="the right end of the box (cell 0 is bit B)")
    p.add_argument("--steps", type=int, default=20000)
    p.set_defaults(run=run_pair, c=False, t1=None)
    args = parser.parse_args()
    args.t1 = args.t1 or (128 if args.c else 400)
    args.run(args)


if __name__ == "__main__":
    main()
