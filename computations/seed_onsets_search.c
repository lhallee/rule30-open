/* The largest onset of each left diagonal over every seed row, by an exhaustive search over the seed's cells.

   A row white left of a black cell lo, with cells x_1, x_2, ... right of it, has left diagonals
   D_i(t) = cell(t, lo - t + i) with D_0 = 1 and D_{i+2}(t+1) = D_i(t) xor (D_{i+1}(t) or D_{i+2}(t)) (D_{-1} = D_{-2} = 0),
   from D_i(0) = x_i. Diagonal i depends on x_1 .. x_i only. The search fixes x_1 .. x_LOW in the lanes of a vector of
   2^LOW bits and walks x_{LOW+1} .. x_J depth first: at a node of depth i it computes the whole sequence D_i(0 .. H-1)
   from D_{i-2} and D_{i-1} and its own bit, for all lanes at once. The onset of D_i in a lane is the least T with
   D_i(t + P) = D_i(t) for T <= t <= H - 1 - P; the search records, for each depth, the largest onset over all seeds, the
   number of seeds that reach it and one of them. If every recorded onset is at most H - 1 - P, every seed's vector
   (D_0 .. D_J) repeats with period P from its largest window onset on, so the window onsets are the true onsets (the
   caller checks this).

   Build: cc -O3 -march=native -fopenmp seed_onsets_search.c -o seed_onsets_search
   Run:   ./seed_onsets_search J H P SPLIT
   Output: one line "j max count x_1..x_j" per depth j = 0 .. J. */

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define LOW 9                                  /* x_1 .. x_LOW live in the lanes */
#define WORDS 8                                /* 2^LOW / 64 */
typedef uint64_t vec __attribute__((vector_size(8 * WORDS)));

#define MAXJ 128
#define MAXH 512

static int J, H, P, SPLIT;

typedef struct {
    int best[MAXJ + 1];
    uint64_t count[MAXJ + 1];
    int lane[MAXJ + 1];
    uint64_t path[MAXJ + 1][2];               /* bits x_{LOW+1} .. x_j of a worst seed, bit k-LOW-1 = x_k */
} Stats;

static int nonzero(vec v) {
    uint64_t a = 0;
    for (int w = 0; w < WORDS; w++) a |= v[w];
    return a != 0;
}

static uint64_t popcount(vec v) {
    uint64_t c = 0;
    for (int w = 0; w < WORDS; w++) c += (uint64_t)__builtin_popcountll(v[w]);
    return c;
}

static int first_lane(vec v) {
    for (int w = 0; w < WORDS; w++)
        if (v[w]) return 64 * w + __builtin_ctzll(v[w]);
    return -1;
}

/* D[t + 1] = A[t] xor (B[t] or D[t]) for t < H - 1, from D[0] = init. */
static void diagonal(vec *D, const vec *A, const vec *B, vec init) {
    vec d = init;
    D[0] = d;
    for (int t = 0; t + 1 < H; t++) {
        d = A[t] ^ (B[t] | d);
        D[t + 1] = d;
    }
}

/* Record the onsets of D (depth i) in st; path holds x_{LOW+1} .. x_i. */
static void record(Stats *st, int i, const vec *D, const uint64_t path[2]) {
    for (int t = H - 1 - P; t >= 0; t--) {
        vec diff = D[t + P] ^ D[t];
        if (nonzero(diff)) {
            int onset = t + 1;
            if (onset > st->best[i]) {
                st->best[i] = onset;
                st->count[i] = popcount(diff);
                st->lane[i] = first_lane(diff);
                st->path[i][0] = path[0];
                st->path[i][1] = path[1];
            } else if (onset == st->best[i]) {
                st->count[i] += popcount(diff);
            }
            return;
        }
    }
    /* onset 0: every lane repeats from the start */
    if (st->best[i] == 0) {
        st->count[i] += (uint64_t)1 << LOW;
    }
}

static void set_bit(uint64_t path[2], int k, int b) {
    if (b) path[k >> 6] |= (uint64_t)1 << (k & 63);
    else path[k >> 6] &= ~((uint64_t)1 << (k & 63));
}

static void dfs(Stats *st, vec (*D)[MAXH], int i, uint64_t path[2], vec zero, vec ones) {
    if (i > J) return;
    for (int b = 0; b < 2; b++) {
        set_bit(path, i - LOW - 1, b);
        diagonal(D[i + 2], D[i], D[i + 1], b ? ones : zero);  /* row i + 2 of D holds diagonal i */
        record(st, i, D[i + 2], path);
        dfs(st, D, i + 1, path, zero, ones);
    }
    set_bit(path, i - LOW - 1, 0);
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s J H P SPLIT\n", argv[0]);
        return 2;
    }
    J = atoi(argv[1]);
    H = atoi(argv[2]);
    P = atoi(argv[3]);
    SPLIT = atoi(argv[4]);
    if (J < LOW || J > MAXJ || H > MAXH || P >= H || SPLIT < 0 || LOW + SPLIT > J || J - LOW > 128) {
        fprintf(stderr, "bad arguments\n");
        return 2;
    }
    vec zero, ones;
    for (int w = 0; w < WORDS; w++) {
        zero[w] = 0;
        ones[w] = ~(uint64_t)0;
    }

    Stats total;
    memset(&total, 0, sizeof total);

    /* the root: diagonals 0 .. LOW, with x_k = bit k - 1 of the lane */
    static vec root[LOW + 3][MAXH];
    memset(root, 0, sizeof root);                /* rows 0, 1 are D_{-2}, D_{-1} = 0 */
    for (int i = 0; i <= LOW; i++) {
        vec init = zero;
        if (i == 0) init = ones;
        else
            for (int lane = 0; lane < (1 << LOW); lane++)
                if ((lane >> (i - 1)) & 1) init[lane >> 6] |= (uint64_t)1 << (lane & 63);
        diagonal(root[i + 2], root[i], root[i + 1], init);
        uint64_t nopath[2] = {0, 0};
        record(&total, i, root[i + 2], nopath);
    }

    long tasks = 1L << SPLIT;
    int done = 0;
#pragma omp parallel
    {
        Stats st;
        memset(&st, 0, sizeof st);
        vec (*D)[MAXH] = aligned_alloc(64, sizeof(vec) * MAXH * (MAXJ + 3));
        memcpy(D[LOW + 1], root[LOW + 1], sizeof(vec) * MAXH);
        memcpy(D[LOW + 2], root[LOW + 2], sizeof(vec) * MAXH);
#pragma omp for schedule(dynamic, 1)
        for (long task = 0; task < tasks; task++) {
            uint64_t path[2] = {0, 0};
            /* the prefix x_{LOW+1} .. x_{LOW+SPLIT} = bits of task; depth LOW + k is recorded once, by the task whose
               bits above k are zero */
            for (int k = 1; k <= SPLIT; k++) {
                int i = LOW + k, b = (int)((task >> (k - 1)) & 1);
                set_bit(path, k - 1, b);
                diagonal(D[i + 2], D[i], D[i + 1], b ? ones : zero);
                if ((task >> k) == 0) record(&st, i, D[i + 2], path);
            }
            dfs(&st, D, LOW + SPLIT + 1, path, zero, ones);
#pragma omp critical
            {
                done++;
                if (done % (tasks / 16 > 0 ? tasks / 16 : 1) == 0) {
                    fprintf(stderr, "\r%d / %ld tasks", done, tasks);
                    fflush(stderr);
                }
            }
        }
#pragma omp critical
        {
            for (int i = 0; i <= J; i++) {
                if (st.best[i] > total.best[i]) {
                    total.best[i] = st.best[i];
                    total.count[i] = st.count[i];
                    total.lane[i] = st.lane[i];
                    total.path[i][0] = st.path[i][0];
                    total.path[i][1] = st.path[i][1];
                } else if (st.best[i] == total.best[i]) {
                    total.count[i] += st.count[i];
                }
            }
        }
        free(D);
    }
    fprintf(stderr, "\n");

    for (int i = 0; i <= J; i++) {
        uint64_t count = i < LOW ? total.count[i] >> (LOW - i) : total.count[i];  /* lanes repeat x_{i+1} .. x_LOW */
        printf("%d %d %llu ", i, total.best[i], (unsigned long long)count);
        for (int k = 1; k <= i; k++) {
            int b = k <= LOW ? (total.lane[i] >> (k - 1)) & 1
                             : (int)((total.path[i][(k - LOW - 1) >> 6] >> ((k - LOW - 1) & 63)) & 1);
            putchar('0' + b);
        }
        putchar('\n');
    }
    return 0;
}
