/* The largest onset of each left diagonal over every seed row, by branch and bound over the seed's cells.

   The seed rows and diagonals are those of seed_onsets_search.c: D_0 = 1, D_{i+2}(t+1) = D_i(t) xor (D_{i+1}(t) or
   D_{i+2}(t)) with D_{-1} = D_{-2} = 0, from D_i(0) = x_i, so D_i depends on x_1 .. x_i. Here one seed is followed at
   a time, the sequence D_i(0 .. H-1) as H / 8 bytes, stepped eight times at once from a table. The period is 8, a
   multiple of the period of every diagonal of every seed at the depths searched (the caller checks it: a diagonal of
   another period would show an onset near H).

   The bound. Let S_i = max(T_{i-1}, T_i), the time from which the pair (D_{i-1}, D_i) repeats with period 8, and let
   (a, b) be its 16 cells at times S_i .. S_i + 7. From S_i on, the diagonals i + 1, i + 2, ... are the diagonals of a
   row driven by the periodic pair (a, b) from the vector (D_{i+1}(S_i), D_{i+2}(S_i), ...). So for m <= K,
   T_{i+m} <= S_i + G_m(a, b), where G_m(a, b) is the largest onset of driven diagonal m over all 2^m vectors, computed
   exhaustively and kept. A node at depth i >= J - K is left when S_i + G_{d-i}(a, b) <= best_d for every depth
   i < d <= J, best_d being the largest onset of depth d found so far (or given as a hint) on an actual seed: no
   extension of the node can raise any best_d. The search then returns the exact largest onset of every depth <= J,
   with a seed that reaches it, provided every onset it computed, driven or not, is at most H - 9 (the caller checks
   the reported largest onset).

   Build: cc -O3 -march=native -fopenmp seed_onsets_prune.c -o seed_onsets_prune
   Run:   ./seed_onsets_prune J H K SPLIT [WALK] < hints
   hints: lines of seeds x_1 x_2 ... as 0/1 strings (cells past the end are white); every depth of every hint is
   evaluated first, which seeds best_d.
   Output: "j max x_1..x_j" for j = 0 .. J, then "largest onset seen N", "nodes N", "pruned N", "patterns N". */

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXJ 200
#define MAXQ 48
#define MAXK 28

static int J, Q, H, K, SPLIT;
static uint8_t F[2][256][256];               /* F[d][a][b]: bits k = D(8q + k + 1) given D(8q) = d, A and B bytes */
static volatile int best[MAXJ + 1];
static uint8_t best_seed[MAXJ + 1][MAXJ + 1];
static int largest_seen = 0;
static unsigned long long nodes = 0, pruned = 0, patterns = 0;
static int16_t *gcache[1 << 16];              /* G_0 .. G_K for each pair pattern a | b << 8 */

static void init_table(void) {
    for (int d = 0; d < 2; d++)
        for (int a = 0; a < 256; a++)
            for (int b = 0; b < 256; b++) {
                int s = d, out = 0;
                for (int k = 0; k < 8; k++) {
                    s = ((a >> k) & 1) ^ (((b >> k) & 1) | s);
                    out |= s << k;
                }
                F[d][a][b] = (uint8_t)out;
            }
}

/* D(t + 1) = A(t) xor (B(t) or D(t)), D(0) = x, for t < H. */
static void diag(uint8_t *D, const uint8_t *A, const uint8_t *B, int x) {
    int d = x;
    for (int q = 0; q < Q; q++) {
        uint8_t out = F[d][A[q]][B[q]];
        D[q] = (uint8_t)(d | (out << 1));
        d = out >> 7;
    }
}

/* The least T with D(t + 8) = D(t) for T <= t <= H - 9. */
static int onset(const uint8_t *D) {
    for (int q = Q - 2; q >= 0; q--) {
        unsigned x = (unsigned)(D[q] ^ D[q + 1]);
        if (x) return 8 * q + (31 - __builtin_clz(x)) + 1;
    }
    return 0;
}

/* The 8 cells D(s .. s + 7), s <= H - 9. */
static int window8(const uint8_t *D, int s) {
    int q = s >> 3, r = s & 7;
    return (int)(((unsigned)D[q] | ((unsigned)D[q + 1] << 8)) >> r) & 0xFF;
}

static void note_seen(int t) {
    if (t > largest_seen) {
#pragma omp critical(seen)
        if (t > largest_seen) largest_seen = t;
    }
}

/* G_m for the pair pattern: the largest onset of driven diagonal m over all 2^m initial vectors, m <= K. */
static void driven_dfs(uint8_t (*rows)[MAXQ], int k, int16_t *G) {
    if (k > K) return;
    for (int b = 0; b < 2; b++) {
        diag(rows[k + 1], rows[k - 1], rows[k], b);
        int T = onset(rows[k + 1]);
        if (T > G[k]) G[k] = (int16_t)T;
        driven_dfs(rows, k + 1, G);
    }
}

static const int16_t *getG(int pat) {
    int16_t *g = __atomic_load_n(&gcache[pat], __ATOMIC_ACQUIRE);
    if (g) return g;
    int16_t *G = calloc(MAXK + 1, sizeof(int16_t));
    uint8_t rows[MAXK + 3][MAXQ];
    memset(rows, 0, sizeof rows);
    for (int q = 0; q < Q; q++) {
        rows[0][q] = (uint8_t)(pat & 0xFF);
        rows[1][q] = (uint8_t)(pat >> 8);
    }
    driven_dfs(rows, 1, G);
    int top = 0;
    for (int m = 1; m <= K; m++)
        if (G[m] > top) top = G[m];
    note_seen(top);
#pragma omp critical(gcache)
    {
        if (gcache[pat]) {
            free(G);
        } else {
            __atomic_store_n(&gcache[pat], G, __ATOMIC_RELEASE);
            patterns++;
        }
    }
    return gcache[pat];
}

static void record(int d, int T, const uint8_t *path) {
    note_seen(T);
    if (T > best[d]) {
#pragma omp critical(best)
        if (T > best[d]) {
            best[d] = T;
            memcpy(best_seed[d], path, (size_t)d + 1);
        }
    }
}

static int bit_at(const uint8_t *D, int t) { return (D[t >> 3] >> (t & 7)) & 1; }

/* The first t >= s with D(t) = 1, or -1. */
static int first_black(const uint8_t *D, int s) {
    for (int q = s >> 3; q < Q; q++) {
        unsigned x = D[q];
        if (q == s >> 3) x &= (0xFFu << (s & 7)) & 0xFFu;
        if (x) return 8 * q + __builtin_ctz(x);
    }
    return -1;
}

/* max(s, 1 + the last t in [s, H - 9] with D(t + 8) != D(t)). */
static int onset_from(const uint8_t *D, int s) {
    for (int q = Q - 2; q >= 0 && 8 * q + 7 >= s; q--) {
        unsigned x = (unsigned)(D[q] ^ D[q + 1]);
        if (8 * q < s) x &= (0xFFu << (s - 8 * q)) & 0xFFu;
        if (x) {
            int T = 8 * q + (31 - __builtin_clz(x)) + 1;
            return T > s ? T : s;
        }
    }
    return s;
}

/* D(t + 1) = A(t) xor (B(t) or D(t)) for t >= s, from D(s) = c; the cells before s are left as they were. */
static void diag_from(uint8_t *D, const uint8_t *A, const uint8_t *B, int s, int c) {
    int d = c, t = s;
    D[s >> 3] &= (uint8_t)((1u << (s & 7)) - 1);
    for (; t < H && (t & 7); t++) {
        if (d) D[t >> 3] |= (uint8_t)(1u << (t & 7));
        d = bit_at(A, t) ^ (bit_at(B, t) | d);
    }
    for (int q = t >> 3; q < Q; q++) {
        uint8_t out = F[d][A[q]][B[q]];
        D[q] = (uint8_t)(d | (out << 1));
        d = out >> 7;
    }
}

/* The walk bound. A = D_{k-1} and B = D_k are known from time wb on (for every extension of the node). The diagonal
   D_{k+1} is then known from 1 + the first black cell r >= wb of B (behind a black cell the next diagonal forgets its
   past), and if B is white from wb on (it is then white for ever: it repeats from its bound <= H - 9) it is known up to
   its value at wb. So T_{k+1} <= max(w, U), w the time from which D_{k+1} is known and U one more than its last change
   with period 8 on [w, H - 9], for every extension. Returns 1 if every depth d in (k, J] has this bound, or the
   driven bound fb[d], at most best_d. */
static int walk_ok(const uint8_t *A, const uint8_t *B, int wb, int k, const int *fb) {
    if (k == J) return 1;
    uint8_t C[MAXQ] = {0};
    int r = first_black(B, wb);
    for (int c = 0; c < (r >= 0 ? 1 : 2); c++) {
        int wc;
        if (r >= 0) {
            wc = r + 1;
            if (wc > H - 9) return 0;
            diag_from(C, A, B, wc, !bit_at(A, r));  /* D_{k+1}(r + 1) = not D_{k-1}(r) behind the black cell */
        } else {
            wc = wb;
            diag_from(C, A, B, wb, c);
        }
        if (wc > H - 9) return 0;
        int bound = onset_from(C, wc);
        if (bound > H - 9) return 0;
        if (bound > best[k + 1] && !(fb && fb[k + 1] <= best[k + 1])) return 0;
        if (!walk_ok(B, C, wc, k + 1, fb)) return 0;
    }
    return 1;
}

static int WALK = 1;

/* Can a descendant of the node at depth i (pair onset S, rows r1 = D_{i-1}, r2 = D_i) raise some best_d? */
static int must_explore(int i, int S, const uint8_t *r1, const uint8_t *r2) {
    if (i < 1) return 1;
    int fb[MAXJ + 1];
    int have = 0;
    if (J - i <= K) {
        const int16_t *G = getG(window8(r1, S) | (window8(r2, S) << 8));
        int all = 1;
        for (int d = i + 1; d <= J; d++) {
            fb[d] = S + G[d - i];
            if (fb[d] > best[d]) all = 0;
        }
        if (all) return 0;
        have = 1;
    }
    if (WALK && walk_ok(r1, r2, 0, i, have ? fb : NULL)) return 0;
    return 1;
}

typedef struct {
    uint8_t rows[MAXJ + 3][MAXQ];             /* row i + 2 = D_i; rows 0 and 1 = D_{-2}, D_{-1} = white */
    int T[MAXJ + 1];
    uint8_t path[MAXJ + 1];                   /* path[k] = x_k, k >= 1 */
    unsigned long long nodes, pruned;
} Walk;

static void node(Walk *w, int i) {
    w->nodes++;
    int S = i ? (w->T[i - 1] > w->T[i] ? w->T[i - 1] : w->T[i]) : w->T[0];
    if (i == J) return;
    if (!must_explore(i, S, w->rows[i + 1], w->rows[i + 2])) {
        w->pruned++;
        return;
    }
    uint8_t child[2][MAXQ];
    int Tc[2];
    for (int b = 0; b < 2; b++) {
        diag(child[b], w->rows[i + 1], w->rows[i + 2], b);
        Tc[b] = onset(child[b]);
    }
    int first = Tc[1] > Tc[0];               /* the child with the later onset first */
    for (int n = 0; n < 2; n++) {
        int b = n ? !first : first;
        memcpy(w->rows[i + 3], child[b], (size_t)Q);
        w->T[i + 1] = Tc[b];
        w->path[i + 1] = (uint8_t)b;
        record(i + 1, Tc[b], w->path);
        node(w, i + 1);
    }
}

static void start(Walk *w) {
    unsigned long long n = w->nodes, p = w->pruned;
    memset(w, 0, sizeof *w);
    w->nodes = n;
    w->pruned = p;
    diag(w->rows[2], w->rows[0], w->rows[1], 1);
    w->T[0] = onset(w->rows[2]);
    record(0, w->T[0], w->path);
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s J H K SPLIT < hints\n", argv[0]);
        return 2;
    }
    J = atoi(argv[1]);
    H = atoi(argv[2]);
    K = atoi(argv[3]);
    SPLIT = atoi(argv[4]);
    if (argc > 5) WALK = atoi(argv[5]);
    Q = H / 8;
    if (J < 1 || J > MAXJ || H % 8 || Q < 3 || Q > MAXQ || K < 0 || K > MAXK || SPLIT < 0 || SPLIT > J) {
        fprintf(stderr, "bad arguments\n");
        return 2;
    }
    init_table();

    /* hints */
    static char line[4096];
    static Walk hw;
    while (fgets(line, sizeof line, stdin)) {
        int n = 0;
        start(&hw);
        for (int i = 1; i <= J; i++) {
            int b = 0;
            while (line[n] && line[n] != '0' && line[n] != '1') n++;
            if (line[n]) b = line[n++] - '0';
            hw.path[i] = (uint8_t)b;
            diag(hw.rows[i + 2], hw.rows[i], hw.rows[i + 1], b);
            hw.T[i] = onset(hw.rows[i + 2]);
            record(i, hw.T[i], hw.path);
        }
    }

    long tasks = 1L << SPLIT;
    long done = 0;
#pragma omp parallel
    {
        Walk *w = aligned_alloc(64, (sizeof(Walk) + 63) / 64 * 64);
        w->nodes = w->pruned = 0;
#pragma omp for schedule(dynamic, 1)
        for (long task = 0; task < tasks; task++) {
            start(w);
            int alive = 1;
            for (int k = 1; k <= SPLIT && alive; k++) {
                int b = (int)((task >> (k - 1)) & 1);
                w->path[k] = (uint8_t)b;
                diag(w->rows[k + 2], w->rows[k], w->rows[k + 1], b);
                w->T[k] = onset(w->rows[k + 2]);
                record(k, w->T[k], w->path);
                int S = w->T[k - 1] > w->T[k] ? w->T[k - 1] : w->T[k];
                if (k < J && !must_explore(k, S, w->rows[k + 1], w->rows[k + 2])) alive = 0;
            }
            if (alive) node(w, SPLIT);
#pragma omp critical(progress)
            {
                done++;
                if (done % (tasks / 64 > 0 ? tasks / 64 : 1) == 0) {
                    fprintf(stderr, "\r%ld / %ld tasks", done, tasks);
                    fflush(stderr);
                }
            }
        }
#pragma omp critical(totals)
        {
            nodes += w->nodes;
            pruned += w->pruned;
        }
        free(w);
    }
    fprintf(stderr, "\n");

    for (int d = 0; d <= J; d++) {
        printf("%d %d ", d, best[d]);
        for (int k = 1; k <= d; k++) putchar('0' + best_seed[d][k]);
        putchar('\n');
    }
    printf("largest onset seen %d\nnodes %llu\npruned %llu\npatterns %llu\n", largest_seen, nodes, pruned, patterns);
    return 0;
}
