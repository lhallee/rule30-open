"""The letters a completion feeds to the left cut of the cone: the language W_T, its constraints and growth, the rank
ceiling it gives, and the left cut's distinguishability computed through it.

c_t is cell 0 after t steps (new x_j = x_{j-1} xor (x_j or x_{j+1})), a function of x_{-t} .. x_t. Cut the cone after
its a leftmost cells: the left setting P has bit k equal to x_{-t+k}, the completion r has bit k equal to x_{-t+a+k},
and one step of a row read as a number is `nstep` (the frame moves one cell right). The completion evolves on its own
and acts on P only through its *letters* e_s = nevo(r, s) % 4 (bit 0 the cell next to the cut); by the horizon only
the letters at times s < T = t - (ceil(a/2) - 1) reach the center (`LateSeedCut.lateCen_eq`). W_T is the set of words
e_0 .. e_{T-1} over all completions.

* `word_set`, `word_count`: W_T by enumerating every completion of 2T cells (a word codes letter s in bits 2s, 2s+1).
* `ALLOWED`, `allowed_word`, `word_bound`: the two-letter constraints (after 0 comes 0, 2, 3; after 1 comes 1, 2, 3;
  after 2 comes 1, 3; after 3 comes 0, 2) and the number of words that obey them, 2 P(T + 1) (P the Pell numbers),
  as in the Lean module `LetterWords` (`letter_allowed`, `wordBound`).
* `minimal_forbidden`, `sft_radius`: the minimal forbidden words and the spectral radius of the shift of finite type
  whose k-blocks are W_k, an upper bound on the growth of W_T.
* `columns_from_words`, `rank_and_nl`: the matrix c_t(P, r) has one column per word, so its GF(2) rank and its number
  N_L(t, a) of distinct rows come from the words; `rank_and_nl_full` computes both from every completion instead.
* `ideal_classes`: the classes of the a left cells when every letter word is allowed (the frozen-boundary automaton
  with the three steps unrestricted), the ceiling of what any completion family can separate.
* `edge_shift`: the eventual left edge of a row white left of a black cell, compared with the single cell's up to a
  time shift.
* The C program `letter_words.c` does the large runs (`count`, `forbid`, `entropy`, `follow`, `wordmat`, `refine`,
  `ideal`).

    python -m computations.letter_words --count 15              # |W_T|, T <= 15 (about 30 s with 4 threads)
    python -m computations.letter_words --forbid 12 --entropy 13 # minimal forbidden words, SFT radii (about 1 min)
    python -m computations.letter_words --follow 12              # follower and predecessor set counts (seconds)
    python -m computations.letter_words --rank 14 20             # rank(t, a) and N_L(t, a), t = 14 .. 20 (minutes)
    python -m computations.letter_words --threshold 17 23        # N_L at a = t - 2, t - 3, t - 4 (about 1 h at 23)
    python -m computations.letter_words --ideal 20               # the unrestricted classes, a = 4 .. 20 (seconds)
    python -m computations.letter_words --edges 60 1000          # eventual left edges of random seeds, depth 60
"""

from __future__ import annotations

import argparse
import random
import subprocess

from tqdm.auto import tqdm

ALLOWED: dict[int, tuple[int, ...]] = {0: (0, 2, 3), 1: (1, 2, 3), 2: (1, 3), 3: (0, 2)}
"""The letters that may follow a letter (bit 0 the cell next to the cut, bit 1 the next one)."""


def nstep(r: int) -> int:
    """One step of Rule 30 on a row read as a number, the frame moving one cell right."""
    return r ^ ((r >> 1) | (r >> 2))


def nevo(r: int, s: int) -> int:
    """`nstep` applied s times."""
    for _ in range(s):
        r = nstep(r)
    return r


def word_of(r: int, T: int) -> int:
    """The word of the completion r: letter s = nevo(r, s) % 4 in bits 2s, 2s + 1."""
    w = 0
    for s in range(T):
        w |= (r & 3) << (2 * s)
        r = nstep(r)
    return w


def letters_of(w: int, T: int) -> list[int]:
    """The T letters of a coded word."""
    return [(w >> (2 * s)) & 3 for s in range(T)]


def word_set(T: int, nb: int | None = None) -> set[int]:
    """W_T: the words of T letters over every completion of nb cells (2T by default, which is all that matters)."""
    nb = 2 * T if nb is None else nb
    return {word_of(r, T) for r in range(1 << nb)}


def word_count(T: int) -> int:
    """|W_T|."""
    return len(word_set(T))


def allowed_word(w: int, T: int) -> bool:
    """Does the coded word obey the two-letter constraints?"""
    e = letters_of(w, T)
    return all(e[s + 1] in ALLOWED[e[s]] for s in range(T - 1))


def word_bound(T: int) -> int:
    """The number of words of T >= 1 letters that obey the two-letter constraints: 2 P(T + 1), P the Pell numbers
    (`LetterWords.wordBound`, computed there as low + high words: L' = L + H, H' = 2L + H from L = H = 2)."""
    low, high = 2, 2
    for _ in range(T - 1):
        low, high = low + high, 2 * low + high
    return low + high


def minimal_forbidden(K: int) -> dict[int, int]:
    """The number of minimal forbidden words of each length 2 .. K: not in W, both proper factors of length k - 1 in W."""
    sets = {k: word_set(k) for k in range(1, K + 1)}
    out: dict[int, int] = {}
    for k in range(2, K + 1):
        mask = (1 << (2 * (k - 1))) - 1
        out[k] = sum(1 for w in range(1 << (2 * k))
                     if w not in sets[k] and (w & mask) in sets[k - 1] and (w >> 2) in sets[k - 1])
    return out


def sft_radius(k: int, iterations: int = 400) -> float:
    """The spectral radius of the shift of finite type whose k-blocks are the words of W_k (power iteration on the
    graph of (k - 1)-blocks): |W_T| <= C * radius^T for every T."""
    big, small = word_set(k), word_set(k - 1)
    v = {u: 1.0 for u in small}  # (|W_{k-1}|,)
    lam = 0.0
    for _ in range(iterations):
        nv: dict[int, float] = {}
        for u, x in v.items():
            for e in range(4):
                w = u | (e << (2 * (k - 1)))
                if w in big:
                    nv[w >> 2] = nv.get(w >> 2, 0.0) + x
        s, ss = sum(nv.values()), sum(v.values())
        lam = s / ss
        v = {u: x / s for u, x in nv.items()}
    return lam


def horizon(t: int, a: int) -> tuple[int, int]:
    """(T, n): the letters at times s < T reach the center, and n = ceil(a/2) - 1 steps follow them."""
    n = (a + 1) // 2 - 1
    return t - n, n


def column_of_word(a: int, T: int, n: int, w: int) -> int:
    """The column of a word: bit P is the center for the left cells P, all 2^a settings bit-sliced in Python ints."""
    ones = (1 << (1 << a)) - 1
    row = [sum(1 << P for P in range(1 << a) if (P >> k) & 1) for k in range(a)]  # (a,) ints of 2^a bits
    for s in range(T + n):
        e0 = ones if s < T and (w >> (2 * s)) & 1 else 0
        e1 = ones if s < T and (w >> (2 * s + 1)) & 1 else 0
        ext = row + [e0, e1]  # (a + 2,)
        row = [ext[k] ^ (ext[k + 1] | ext[k + 2]) for k in range(a)]  # (a,)
    return row[0]


def gf2_rank(vectors: list[int]) -> int:
    """The GF(2) rank of a list of bit vectors given as ints."""
    basis: list[int] = []
    for v in vectors:
        for b in basis:
            v = min(v, v ^ b)
        if v:
            basis.append(v)
    return len(basis)


def distinct_rows(cols: list[int], a: int) -> int:
    """The number of distinct rows of the 2^a x len(cols) matrix whose columns are the given bit vectors."""
    return len({tuple((c >> P) & 1 for c in cols) for P in range(1 << a)})


def columns_from_words(t: int, a: int) -> list[int]:
    """The distinct columns of the cut after a cells at time t, one per word of W_T (completions of the cone only)."""
    T, n = horizon(t, a)
    nb = min(2 * t + 1 - a, 2 * T)
    return sorted({column_of_word(a, T, n, w) for w in word_set(T, nb)})


def rank_and_nl(t: int, a: int) -> tuple[int, int]:
    """(GF(2) rank, N_L(t, a)) of the cut after a cells at time t, from the words."""
    cols = columns_from_words(t, a)
    return gf2_rank(cols), distinct_rows(cols, a)


def center_plain(cells: list[int]) -> int:
    """c_t from the 2t + 1 cone cells x_{-t} .. x_t by running the rule on a list."""
    row = list(cells)  # (2t + 1,)
    while len(row) > 1:
        row = [row[i - 1] ^ (row[i] | row[i + 1]) for i in range(1, len(row) - 1)]  # (len - 2,)
    return row[0]


def rank_and_nl_full(t: int, a: int) -> tuple[int, int]:
    """(GF(2) rank, N_L(t, a)) from every completion, by plain runs, without words: an independent check."""
    nb = 2 * t + 1 - a
    cols = []
    for r in range(1 << nb):
        cols.append(sum(center_plain([(P >> k) & 1 for k in range(a)] + [(r >> k) & 1 for k in range(nb)]) << P
                        for P in range(1 << a)))
    return gf2_rank(cols), distinct_rows(cols, a)


def rho(a: int) -> int:
    """2 + floor(2^a / 3), the rank of the left cut after a cells for a <= t - 3 and t <= 14 (left-cut rank)."""
    return 2 + (1 << a) // 3


def ideal_classes(a: int, Tmax: int) -> list[int]:
    """The number of classes of the a left cells under the words of exactly T letters with every letter allowed,
    followed by the horizon, for T = 1 .. Tmax (stopping at 2^a): backward refinement by the three steps."""
    n = (a + 1) // 2 - 1
    mask = (1 << a) - 1
    images = [[nstep((e << a) | x) & mask for x in range(1 << a)] for e in (0, 1, 2)]  # (3, 2^a)
    lab = [nevo(x, n) & 1 for x in range(1 << a)]  # (2^a,)
    out = []
    for _ in range(Tmax):
        keys = [(lab[images[0][x]], lab[images[1][x]], lab[images[2][x]]) for x in range(1 << a)]
        index: dict[tuple[int, int, int], int] = {}
        lab = [index.setdefault(k, len(index)) for k in keys]
        out.append(len(index))
        if len(index) == 1 << a:
            break
    return out


def edge_frame_run(z0: int, J: int, s0: int, count: int) -> list[int]:
    """The left-edge frame (bit j = the cell j places right of the left edge) from z0, times s0 .. s0 + count - 1,
    low J bits: Z' = 4Z xor (2Z or Z)."""
    mask = (1 << J) - 1
    z, out = z0 & mask, []
    for s in range(s0 + count):
        if s >= s0:
            out.append(z)
        z = ((z << 2) ^ ((z << 1) | z)) & mask
    return out


def edge_shift(x: int, J: int, s0: int, period: int = 8) -> int | None:
    """For the row with a black cell and then the bits of x, the time shift tau with Z_{s} = Z^single_{s + tau} on the
    low J bits for s0 <= s < s0 + period (None if there is none). s0 must be past the settling of depth J."""
    ref = edge_frame_run(1, J, s0, period)
    seq = edge_frame_run(1 | (x << 1), J, s0, period)
    for tau in range(period):
        if all(seq[i] == ref[(i + tau) % period] for i in range(period)):
            return tau
    return None


# ---------------------------------------------------------------------------------------------------------------------
# The C program


def run_c(*args: object) -> dict[str, str] | list[str]:
    """Run computations/letter_words.c with the arguments; key-value output as a dict, other output as lines."""
    from computations.seed_onsets import compiled
    binary = compiled("letter_words", ("-O3", "-fopenmp", "-w", "-lm"))
    out = subprocess.run([str(binary), *map(str, args)], stdout=subprocess.PIPE, text=True, check=True).stdout
    lines = [line for line in out.strip().split("\n") if line]
    if all(len(line.split()) == 2 for line in lines) and args[0] in ("count", "wordmat", "refine"):
        return dict(line.split() for line in lines)
    return lines


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--count", type=int, metavar="TMAX")
    parser.add_argument("--forbid", type=int, metavar="K")
    parser.add_argument("--entropy", type=int, metavar="K")
    parser.add_argument("--follow", type=int, metavar="K")
    parser.add_argument("--rank", nargs=2, type=int, metavar=("T0", "T1"))
    parser.add_argument("--threshold", nargs=2, type=int, metavar=("T0", "T1"))
    parser.add_argument("--ideal", type=int, metavar="AMAX")
    parser.add_argument("--edges", nargs=2, type=int, metavar=("J", "SEEDS"))
    args = parser.parse_args()
    if args.count:
        for T in tqdm(range(1, args.count + 1), desc="W_T"):
            c = int(run_c("count", T)["count"])
            print(f"T={T}: |W_T| = {c}, two-letter bound {word_bound(T)}")
    if args.forbid:
        print("\n".join(run_c("forbid", args.forbid)))
    if args.entropy:
        print("\n".join(run_c("entropy", args.entropy)))
    if args.follow:
        print("\n".join(run_c("follow", args.follow)))
    if args.rank:
        for t in range(args.rank[0], args.rank[1] + 1):
            for a in tqdm(range(max(4, t - 8), t - 1), desc=f"t={t}", leave=False):
                d = run_c("wordmat", t, a)
                print(f"t={t} a={a}: |W_T| = {d['words']}, rank = {d['rank']} (rho = {rho(a)}), N_L = {d['NL']}")
    if args.threshold:
        for t in range(args.threshold[0], args.threshold[1] + 1):
            for a in (t - 2, t - 3, t - 4):
                d = run_c("refine", t, a)
                print(f"t={t} a={a}: N_L = {d['NL']}, 2^a - N_L = {(1 << a) - int(d['NL'])}")
    if args.ideal:
        for a in range(4, args.ideal + 1):
            lines = run_c("ideal", a, 4 * a)
            T, classes = lines[-1].split()[1:]
            print(f"a={a}: full separation by all words of T = {T} letters ({classes} classes)")
    if args.edges:
        J, count = args.edges
        rng = random.Random(1)
        s0 = 3 * J // 2 + 40
        shifts: dict[int | None, int] = {}
        for _ in tqdm(range(count), desc="seeds"):
            tau = edge_shift(rng.getrandbits(rng.randint(1, 3 * J)), J, s0)
            shifts[tau] = shifts.get(tau, 0) + 1
        print(f"depth {J}, time {s0}: time shifts of the single cell's left edge {shifts}")


if __name__ == "__main__":
    main()
