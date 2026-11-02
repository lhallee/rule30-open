/* Signed sums of the derivative of the center along its second cell, for the top real coefficient of that derivative.

   Rule 30: new x_j = x_{j-1} xor (x_j or x_{j+1}). Flipping the cell x_{-t+1} of the cone of the center c_t changes
   c_t by t + (the parity of the cells (s, -t + 2 + s), 0 <= s < t), the diagonal two cells inside the left edge (the
   kit's AlgebraicDegree.deriv_evol_diag_succ, summed). Those cells are the left edge of the cone of the cell
   (t - 1, 1), whose cells are x_{-t+2} .. x_t. With x_{-t+2} = 0 and x_{t-1} = 0 the derivative is the function

     Q'_t = (t mod 2) xor (parity of the left edge of that cone at the times 1 .. t - 1)

   of the 2t - 3 cells x_{-t+3} .. x_{t-2}, x_t. In the frame of that cone (T = t - 1 steps, positions -T .. T, the
   position p is the cell p + 1), variable k is the position -T + 1 + k, k = 0 .. 2T - 1, x_{-T} = 0, and the program
   fixes variable 2T - 2 (the cell t - 1) white. It prints

     mu <sum over the free assignments y of (-1)^{|y|} Q'_t(y)>

   the top real coefficient of Q'_t up to sign. The rightmost LOW = 9 cells live in the 512 lanes of a vector, the other
   cells are walked in Gray code order with the leftmost flipping most often, and only the forward cone of the flipped
   cell is recomputed, as in query_adversary_sums.c. The OUTER-SPLIT rightmost walked cells are fixed per task and the
   tasks run in parallel with OpenMP.

   Build: cc -O3 -march=native -fopenmp query_evasive_sums.c -o query_evasive_sums
   Run:   ./query_evasive_sums t SPLIT        (3 <= t, 2t - 3 > LOW, t <= 31) */

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#define LOW 9
#define WORDS 8
typedef uint64_t vec __attribute__((vector_size(8 * WORDS)));

#define MAXT 30
#define MAXN (2 * MAXT)

static const uint64_t PAT[6] = {0xAAAAAAAAAAAAAAAAull, 0xCCCCCCCCCCCCCCCCull, 0xF0F0F0F0F0F0F0F0ull,
                                0xFF00FF00FF00FF00ull, 0xFFFF0000FFFF0000ull, 0xFFFFFFFF00000000ull};
static const uint64_t ODD = 0x6996966996696996ull; /* bit b set when b (0 <= b < 64) has odd popcount */

static int T, N, PAR;         /* steps of the cone, its variables N = 2T, the constant t mod 2 */
static int fixedv[MAXN];      /* -1 free, else the fixed value */
static vec lanevar[LOW];      /* inner variable j over the lanes */
static vec mask;              /* lanes that agree with the fixed inner variables */
static int inner0;            /* first inner variable, N - LOW */

/* The signed count: sum over the lanes in `bits` of (-1)^{popcount(lane)}. */
static int64_t signedsum(vec bits) {
    int64_t s = 0;
    for (int w = 0; w < WORDS; w++) {
        int64_t odd = __builtin_popcountll(bits[w] & ODD), even = __builtin_popcountll(bits[w] & ~ODD);
        s += (__builtin_popcount((unsigned)w) & 1) ? odd - even : even - odd;
    }
    return s;
}

#define AT(s, j) ((s) * (2 * MAXT + 1) + (j) + T)

static void recompute(vec *tri, int s, int lo, int hi) {
    for (int j = lo; j <= hi; j++) tri[AT(s, j)] = tri[AT(s - 1, j - 1)] ^ (tri[AT(s - 1, j)] | tri[AT(s - 1, j + 1)]);
}

/* The parity of the left edge at the times 1 .. T, xor t mod 2, on every lane. */
static vec observable(const vec *tri, vec ones) {
    vec acc = PAR ? ones : ones ^ ones;
    for (int s = 1; s <= T; s++) acc ^= tri[AT(s, -(T - s))];
    return acc;
}

/* One task: the walked variables walk[0 .. nw-1] (walk[0] flips most often), the split variables fixed to the bits of
   `high`. Returns the signed sum of the task. */
static int64_t task(const int *walk, int nw, const int *split, int ns, uint64_t high) {
    static __thread vec tri[(MAXT + 1) * (2 * MAXT + 1)];
    vec ones, zero;
    for (int w = 0; w < WORDS; w++) { ones[w] = ~0ull; zero[w] = 0; }
    int value[MAXN + 1];
    for (int k = 0; k < N; k++) value[k] = fixedv[k] >= 0 ? fixedv[k] : 0;
    for (int i = 0; i < ns; i++) value[split[i]] = (high >> i) & 1;
    tri[AT(0, -T)] = zero;
    for (int k = 0; k < N; k++) {
        int p = -T + 1 + k;
        if (k >= inner0 && fixedv[k] < 0) tri[AT(0, p)] = lanevar[k - inner0];
        else tri[AT(0, p)] = value[k] ? ones : zero;
    }
    for (int s = 1; s <= T; s++) recompute(tri, s, -(T - s), T - s);
    int parity = 0;
    for (int i = 0; i < ns; i++) parity ^= (high >> i) & 1;
    int64_t cum = 0;
    uint64_t steps = 1ull << nw;
    for (uint64_t g = 0;; g++) {
        int64_t chunk = signedsum(observable(tri, ones) & mask);
        cum += parity ? -chunk : chunk;
        if (g + 1 == steps) break;
        int i = __builtin_ctzll(g + 1);   /* Gray code: flip walked variable i */
        parity ^= 1;
        int p = -T + 1 + walk[i];
        tri[AT(0, p)] ^= ones;
        for (int s = 1; s <= T; s++) {
            int lo = p - s > -(T - s) ? p - s : -(T - s), hi = p + s < T - s ? p + s : T - s;
            recompute(tri, s, lo, hi);
        }
    }
    return cum;
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: %s t SPLIT\n", argv[0]); return 1; }
    int t = atoi(argv[1]);
    int want_split = atoi(argv[2]);
    T = t - 1;
    N = 2 * T;
    PAR = t & 1;
    if (T > MAXT || N - 1 < LOW + 1) { fprintf(stderr, "need %d < 2t - 3, t <= %d\n", LOW, MAXT + 1); return 1; }
    for (int k = 0; k < N; k++) fixedv[k] = -1;
    fixedv[N - 2] = 0;                 /* the cell t - 1 */
    inner0 = N - LOW;
    for (int w = 0; w < WORDS; w++) mask[w] = ~0ull;
    for (int j = 0; j < LOW; j++) {
        for (int w = 0; w < WORDS; w++) lanevar[j][w] = j < 6 ? PAT[j] : (((w >> (j - 6)) & 1) ? ~0ull : 0);
        int v = fixedv[inner0 + j];
        if (v >= 0) mask &= v ? lanevar[j] : ~lanevar[j];
    }
    int walkall[MAXN], nwalk = 0;
    for (int k = 0; k < inner0; k++)
        if (fixedv[k] < 0) walkall[nwalk++] = k;
    int ns = want_split < nwalk ? want_split : nwalk;
    int nw = nwalk - ns;
    const int *walk = walkall, *split = walkall + nw;
    int64_t total = 0, tasks = 1ll << ns, done = 0;
    #pragma omp parallel for schedule(dynamic, 1) reduction(+ : total)
    for (int64_t h = 0; h < tasks; h++) {
        total += task(walk, nw, split, ns, (uint64_t)h);
        #pragma omp critical
        {
            done++;
            if (tasks >= 16 && done % (tasks / 16) == 0) fprintf(stderr, "t=%d: %lld/%lld tasks\n", t, (long long)done,
                                                                 (long long)tasks);
        }
    }
    printf("mu %lld\n", (long long)total);  /* the fixed inner cell is white, so the lane sign needs no correction */
    return 0;
}
