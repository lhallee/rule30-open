/* Signed sums of the center cell over a subcube of rows, for the top real coefficient of its restrictions.

   g_t is the center after t steps of Rule 30 (new x_j = x_{j-1} xor (x_j or x_{j+1})) from a row with x_{-t} = 0, a
   function of the 2t cells x_{-t+1} .. x_t; variable k is x_{-t+1+k}. Some variables are fixed (FIXED k:v arguments)
   and the others are free. The program prints

     nu = sum over the free assignments y of (-1)^{|y|} g(y),
     S[k][b] = the same sum over the free assignments with y_k = b, for every free k,

   so that the top real coefficient of g restricted to the subcube is +-nu, and that of g with k also fixed to b is
   +-S[k][b].

   The rightmost LOW = 9 cells live in the 512 lanes of a vector (bit b of lane l is bit b of l; bits 0..5 inside a
   word, bits 6..8 the word). The other free cells are walked in Gray code order, the leftmost cell flipping most often,
   and only the cells of the triangle in the forward cone of the flipped cell are recomputed: cell x_{-t+m} changes
   m + 1 cells in each row. The OUTER-SPLIT rightmost walked cells are fixed per task, and the tasks run in parallel
   with OpenMP. Accumulators are 64-bit, enough for t <= 30.

   Build: cc -O3 -march=native -fopenmp query_adversary_sums.c -o query_adversary_sums
   Run:   ./query_adversary_sums T SPLIT [k:v ...]
   Output: "nu <nu>" and one line "k S0 S1" per variable (0 0 for fixed ones). */

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define LOW 9
#define WORDS 8
typedef uint64_t vec __attribute__((vector_size(8 * WORDS)));

#define MAXT 30
#define MAXN (2 * MAXT)

static const uint64_t PAT[6] = {0xAAAAAAAAAAAAAAAAull, 0xCCCCCCCCCCCCCCCCull, 0xF0F0F0F0F0F0F0F0ull,
                                0xFF00FF00FF00FF00ull, 0xFFFF0000FFFF0000ull, 0xFFFFFFFF00000000ull};
static const uint64_t ODD = 0x6996966996696996ull; /* bit b set when b (0 <= b < 64) has odd popcount */

static int T, N;             /* steps and number of variables, N = 2T */
static int fixedv[MAXN];     /* -1 free, else the fixed value */
static vec lanevar[LOW];     /* inner variable j over the lanes */
static vec mask;             /* lanes that agree with the fixed inner variables */
static int inner0;           /* first inner variable, N - LOW */

/* The signed count sum over lanes in `bits` of (-1)^{popcount(lane)}. */
static int64_t signedsum(vec bits) {
    int64_t s = 0;
    for (int w = 0; w < WORDS; w++) {
        int64_t odd = __builtin_popcountll(bits[w] & ODD), even = __builtin_popcountll(bits[w] & ~ODD);
        s += (__builtin_popcount((unsigned)w) & 1) ? odd - even : even - odd;
    }
    return s;
}

typedef struct {
    int64_t total;
    int64_t s1[MAXN];        /* signed sums over the assignments with variable k = 1 */
} Sums;

/* Cell index in the triangle: row s (0..T), position j (-(T-s)..T-s) stored at j + T. */
#define AT(s, j) ((s) * (2 * MAXT + 1) + (j) + T)

static void recompute(vec *tri, int s, int lo, int hi) {
    for (int j = lo; j <= hi; j++) tri[AT(s, j)] = tri[AT(s - 1, j - 1)] ^ (tri[AT(s - 1, j)] | tri[AT(s - 1, j + 1)]);
}

/* One task: the walked variables walk[0 .. nw-1] (walk[0] flips most often), with the split variables fixed to the bits
   of `high`. Adds the sums into *out. */
static void task(const int *walk, int nw, const int *split, int ns, uint64_t high, int innersums, Sums *out) {
    static __thread vec tri[(MAXT + 1) * (2 * MAXT + 1)];
    vec ones, zero;
    for (int w = 0; w < WORDS; w++) { ones[w] = ~0ull; zero[w] = 0; }
    int value[MAXN + 1];
    for (int k = 0; k < N; k++) value[k] = fixedv[k] >= 0 ? fixedv[k] : 0;
    for (int i = 0; i < ns; i++) value[split[i]] = (high >> i) & 1;
    /* row 0: x_{-T} = 0, then variables 0 .. N-1 at positions -T+1 .. T */
    tri[AT(0, -T)] = zero;
    for (int k = 0; k < N; k++) {
        int p = -T + 1 + k;
        if (k >= inner0 && fixedv[k] < 0) tri[AT(0, p)] = lanevar[k - inner0];
        else tri[AT(0, p)] = value[k] ? ones : zero;
    }
    for (int s = 1; s <= T; s++) recompute(tri, s, -(T - s), T - s);
    int parity = 0;
    for (int i = 0; i < ns; i++) parity ^= (high >> i) & 1;
    int64_t cum = 0;                 /* running signed sum of this task */
    int64_t since[MAXN];             /* cum when walked variable i last became 1 */
    int64_t s1walk[MAXN];
    int64_t s1inner[LOW];
    memset(s1walk, 0, sizeof s1walk);
    memset(s1inner, 0, sizeof s1inner);
    int bit[MAXN];
    memset(bit, 0, sizeof bit);
    uint64_t steps = 1ull << nw;
    for (uint64_t g = 0;; g++) {
        vec c = tri[AT(T, 0)] & mask;
        int64_t chunk = signedsum(c);
        if (parity) chunk = -chunk;
        cum += chunk;
        if (innersums)
            for (int j = 0; j < LOW; j++)
                if (fixedv[inner0 + j] < 0) {
                    int64_t v = signedsum(c & lanevar[j]);
                    s1inner[j] += parity ? -v : v;
                }
        if (g + 1 == steps) break;
        int i = __builtin_ctzll(g + 1);   /* Gray code: flip walked variable i */
        int k = walk[i];
        if (bit[i]) { s1walk[i] += cum - since[i]; bit[i] = 0; }
        else { since[i] = cum; bit[i] = 1; }
        parity ^= 1;
        int p = -T + 1 + k;
        tri[AT(0, p)] ^= ones;
        for (int s = 1; s <= T; s++) {
            int lo = p - s > -(T - s) ? p - s : -(T - s), hi = p + s < T - s ? p + s : T - s;
            recompute(tri, s, lo, hi);
        }
    }
    for (int i = 0; i < nw; i++)
        if (bit[i]) s1walk[i] += cum - since[i];
    #pragma omp critical
    {
        out->total += cum;
        for (int i = 0; i < nw; i++) out->s1[walk[i]] += s1walk[i];
        for (int i = 0; i < ns; i++)
            if ((high >> i) & 1) out->s1[split[i]] += cum;
        for (int j = 0; j < LOW; j++) out->s1[inner0 + j] += s1inner[j];
    }
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: %s T SPLIT [k:v ...]\n", argv[0]); return 1; }
    T = atoi(argv[1]);
    int want_split = atoi(argv[2]);
    N = 2 * T;
    if (T > MAXT || N < LOW + 1) { fprintf(stderr, "need %d < 2T <= %d\n", LOW, 2 * MAXT); return 1; }
    for (int k = 0; k < N; k++) fixedv[k] = -1;
    int fixedsum = 0;
    for (int a = 3; a < argc; a++) {
        int k, v;
        if (sscanf(argv[a], "%d:%d", &k, &v) != 2 || k < 0 || k >= N || (v != 0 && v != 1)) return 1;
        fixedv[k] = v;
        fixedsum += v;
    }
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
    const int *walk = walkall, *split = walkall + nw;  /* the rightmost walked cells are split */
    Sums out;
    memset(&out, 0, sizeof out);
    int64_t tasks = 1ll << ns, done = 0;
    #pragma omp parallel for schedule(dynamic, 1)
    for (int64_t h = 0; h < tasks; h++) {
        task(walk, nw, split, ns, (uint64_t)h, 1, &out);
        #pragma omp critical
        {
            done++;
            if (tasks >= 16 && done % (tasks / 16) == 0) fprintf(stderr, "t=%d: %lld/%lld tasks\n", T, (long long)done,
                                                                 (long long)tasks);
        }
    }
    /* The inner sign counted the fixed inner values; remove it. */
    int innerfixed = 0;
    for (int j = 0; j < LOW; j++)
        if (fixedv[inner0 + j] > 0) innerfixed++;
    int64_t sign = (innerfixed & 1) ? -1 : 1;
    (void)fixedsum;
    printf("nu %lld\n", (long long)(sign * out.total));
    for (int k = 0; k < N; k++) {
        if (fixedv[k] >= 0) { printf("%d 0 0\n", k); continue; }
        int64_t s1 = sign * out.s1[k], s0 = sign * out.total - s1;
        printf("%d %lld %lld\n", k, (long long)s0, (long long)s1);
    }
    return 0;
}
