// The relaxed driver game G, for computations/relaxed_game.py.
//
// A left half is a multiword integer: bit k - 1 is cell -k. One step with boundary e (cell 0) is
//     new = (x >> 1) ^ (x | ((x << 1) | e)),
// so cell -k becomes cell -(k + 1) xor (cell -k or cell -(k - 1)), with cell 0 equal to e. The move e = 1 is legal only
// when cell -1 (bit 0) is white, and the payoff counts the moves e = 1. Every mode starts from the white half at time 0.
// m(x), the phase-A prefix, is the largest m with cell -j black exactly for even j, 1 <= j <= m.
//
//     value T        E(t) for t = 1 .. T, T <= 255: lines "t states E(t)". At time t a state is cut to the cells
//                    -1 .. -(T - t): cell -1 at time t + i depends only on the cells -1 .. -(i + 1) at time t, so the
//                    moves of times t .. T - 1 depend only on the cut, and merging equal cuts (keeping the larger
//                    payoff) leaves every E(t), t <= T, exact.
//     reach T        the uncut reachable sets, T <= 318: lines "t N(t) E(t) m(t)", m(t) the largest prefix over them.
//     window s w     from every state reachable at time s, cut to the w cells a window of w moves reads, and with
//                    the payoff reset: lines "i states G(s, s + i)" for i = 1 .. w, the most ones of i moves.
//     cost s w B     from every state reachable at time s, cut to B cells: lines "i states z_1 z_2 ... z_K" for
//                    i = 1 .. w, z_k the fewest zeros of i moves that end at a state with m >= k (prefixes read on the
//                    B - i cells still exact), K the largest such k.
//     beam T W       keeps the W states with the largest payoffs after each step (ties broken by a hash), on uncut
//                    left halves: lines "t best kept candidates", then "play e(0)e(1)...e(T-1)" for a play that
//                    attains the last best. A lower bound on E(T).
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef uint64_t u64;
typedef unsigned __int128 u128;

#define MAXW 5
static int NW = 1;  // words per left half in the uncut modes
static const u64 PHASE_A = 0xAAAAAAAAAAAAAAAAULL;  // bit k - 1 set exactly for even k: the phase-A pattern

static inline u64 mix64(u64 x) {
    x ^= x >> 33; x *= 0xff51afd7ed558ccdULL; x ^= x >> 33; x *= 0xc4ceb9fe1a85ec53ULL; x ^= x >> 33; return x;
}

static void *xmalloc(size_t n) {
    void *p = malloc(n ? n : 1);
    if (!p) { fprintf(stderr, "out of memory (%zu bytes)\n", n); exit(1); }
    return p;
}

static void *xcalloc(size_t n, size_t s) {
    void *p = calloc(n ? n : 1, s);
    if (!p) { fprintf(stderr, "out of memory (%zu items)\n", n); exit(1); }
    return p;
}

// ---------------------------------------------------------------------------------------------------------------------
// value: the cut dynamic program on two-word states with one-byte payoffs

typedef struct { u64 *k0, *k1; uint8_t *v; size_t cap, n; } Tab2;  // v = payoff + 1, 0 = empty

static inline u64 hash2(u64 a, u64 b) { return mix64(a ^ mix64(b + 0x9e3779b97f4a7c15ULL)); }

static void t2init(Tab2 *t, size_t cap) {
    if (cap < 1024) cap = 1024;
    t->cap = cap; t->n = 0;
    t->k0 = xmalloc(cap * 8); t->k1 = xmalloc(cap * 8); t->v = xcalloc(cap, 1);
}

static void t2free(Tab2 *t) { free(t->k0); free(t->k1); free(t->v); }

static void t2put_raw(Tab2 *t, u64 a, u64 b, uint8_t v1) {
    size_t i = (size_t)(((u128)hash2(a, b) * t->cap) >> 64);
    for (;;) {
        if (!t->v[i]) { t->k0[i] = a; t->k1[i] = b; t->v[i] = v1; t->n++; return; }
        if (t->k0[i] == a && t->k1[i] == b) { if (t->v[i] < v1) t->v[i] = v1; return; }
        if (++i == t->cap) i = 0;
    }
}

static void t2put(Tab2 *t, u64 a, u64 b, int v) {
    if ((t->n + 1) * 100 > t->cap * 80) {
        Tab2 u; t2init(&u, t->cap * 3 / 2 + 1024);
        for (size_t i = 0; i < t->cap; i++) if (t->v[i]) t2put_raw(&u, t->k0[i], t->k1[i], t->v[i]);
        t2free(t); *t = u;
    }
    t2put_raw(t, a, b, (uint8_t)(v + 1));
}

static inline void step2(u64 a, u64 b, int e, u64 *na, u64 *nb) {
    u64 sr0 = (a >> 1) | (b << 63), sr1 = b >> 1;
    u64 sl0 = (a << 1) | (u64)e, sl1 = (b << 1) | (a >> 63);
    *na = sr0 ^ (a | sl0); *nb = sr1 ^ (b | sl1);
}

static inline void cut2(u64 *a, u64 *b, int bits) {
    if (bits <= 0) { *a = 0; *b = 0; }
    else if (bits < 64) { *a &= ((u64)1 << bits) - 1; *b = 0; }
    else if (bits == 64) { *b = 0; }
    else if (bits < 128) { *b &= ((u64)1 << (bits - 64)) - 1; }
}

static void mode_value(int T) {
    if (T < 1 || T > 255) { fprintf(stderr, "value needs 1 <= T <= 255\n"); exit(1); }
    size_t n = 1;
    u64 *A = xcalloc(1, 8), *B = xcalloc(1, 8);
    uint8_t *V = xcalloc(1, 1);
    for (int t = 0; t < T; t++) {
        int keep = T - t - 1;  // cells read by the moves of times t + 1 .. T - 1
        Tab2 nt; t2init(&nt, (size_t)(n * 1.15 / 0.8) + 1024);
        for (size_t i = 0; i < n; i++) {
            u64 na, nb;
            step2(A[i], B[i], 0, &na, &nb); cut2(&na, &nb, keep); t2put(&nt, na, nb, V[i]);
            if (!(A[i] & 1)) { step2(A[i], B[i], 1, &na, &nb); cut2(&na, &nb, keep); t2put(&nt, na, nb, V[i] + 1); }
        }
        free(A); free(B); free(V);
        n = nt.n;
        A = xmalloc(n * 8); B = xmalloc(n * 8); V = xmalloc(n);
        size_t j = 0; int best = -1;
        for (size_t i = 0; i < nt.cap; i++) {
            if (!nt.v[i]) continue;
            A[j] = nt.k0[i]; B[j] = nt.k1[i]; V[j] = nt.v[i] - 1;
            if (V[j] > best) best = V[j];
            j++;
        }
        t2free(&nt);
        printf("%d %zu %d\n", t + 1, n, best);
        fflush(stdout);
    }
    free(A); free(B); free(V);
}

// ---------------------------------------------------------------------------------------------------------------------
// The uncut modes: multiword states, two-byte payoffs

typedef struct { u64 *keys; uint16_t *val; size_t cap, n; } Table;  // val = payoff + 1, 0 = empty

static inline u64 hkey(const u64 *k) {
    u64 h = 0x9e3779b97f4a7c15ULL;
    for (int i = 0; i < NW; i++) h = mix64(h ^ k[i] ^ (u64)i * 0x632be59bd9b4e019ULL);
    return h;
}

static void tinit(Table *t, size_t cap) {
    size_t c = 1024;
    while (c < cap) c <<= 1;
    t->cap = c; t->n = 0;
    t->keys = xmalloc(c * NW * sizeof(u64));
    t->val = xcalloc(c, sizeof(uint16_t));
}

static void tfree(Table *t) { free(t->keys); free(t->val); t->keys = NULL; t->val = NULL; t->cap = t->n = 0; }

static void tput_raw(Table *t, const u64 *k, uint16_t v1) {
    size_t mask = t->cap - 1, i = hkey(k) & mask;
    for (;;) {
        if (t->val[i] == 0) { memcpy(t->keys + i * NW, k, NW * sizeof(u64)); t->val[i] = v1; t->n++; return; }
        if (memcmp(t->keys + i * NW, k, NW * sizeof(u64)) == 0) { if (t->val[i] < v1) t->val[i] = v1; return; }
        i = (i + 1) & mask;
    }
}

static void tput(Table *t, const u64 *k, int v) {
    if ((t->n + 1) * 10 > t->cap * 7) {
        Table u; tinit(&u, t->cap * 2);
        for (size_t i = 0; i < t->cap; i++) if (t->val[i]) tput_raw(&u, t->keys + i * NW, t->val[i]);
        tfree(t); *t = u;
    }
    tput_raw(t, k, (uint16_t)(v + 1));
}

static inline void step(const u64 *x, int e, u64 *y) {
    for (int i = 0; i < NW; i++) {
        u64 sr = (x[i] >> 1) | (i + 1 < NW ? x[i + 1] << 63 : 0);
        u64 sl = (x[i] << 1) | (i > 0 ? x[i - 1] >> 63 : (u64)e);
        y[i] = sr ^ (x[i] | sl);
    }
}

static inline void cut(u64 *x, int bits) {  // keep cells -1 .. -bits
    for (int i = 0; i < NW; i++) {
        int lo = 64 * i;
        if (bits <= lo) x[i] = 0;
        else if (bits < lo + 64) x[i] &= ((u64)1 << (bits - lo)) - 1;
    }
}

static int prefix(const u64 *x, int bits) {  // m(x), read on at most `bits` cells
    int m = 0;
    for (int i = 0; i < NW && m < bits; i++) {
        u64 d = x[i] ^ PHASE_A;
        if (d) { m += __builtin_ctzll(d); break; }
        m += 64;
    }
    return m < bits ? m : bits;
}

// one layer: every legal move from table a into table b, cut to `keep` cells when keep > 0
static void layer(Table *a, Table *b, int keep) {
    u64 y[MAXW];
    for (size_t i = 0; i < a->cap; i++) {
        if (!a->val[i]) continue;
        const u64 *x = a->keys + i * NW;
        int v = a->val[i] - 1;
        step(x, 0, y); if (keep > 0) cut(y, keep); tput(b, y, v);
        if (!(x[0] & 1)) { step(x, 1, y); if (keep > 0) cut(y, keep); tput(b, y, v + 1); }
    }
}

static int tmax(const Table *t) {
    int m = -1;
    for (size_t i = 0; i < t->cap; i++) if (t->val[i] && t->val[i] - 1 > m) m = t->val[i] - 1;
    return m;
}

static void set_words(int cells) {
    NW = (cells + 63) / 64;
    if (NW < 1) NW = 1;
    if (NW > MAXW) { fprintf(stderr, "at most %d cells\n", 64 * MAXW); exit(1); }
}

static Table reachable(int s) {  // every left half reachable at time s, with the largest payoff
    Table a, b; tinit(&a, 1024);
    u64 z[MAXW] = {0}; tput(&a, z, 0);
    for (int t = 0; t < s; t++) { tinit(&b, a.n * 2 + 1024); layer(&a, &b, 0); tfree(&a); a = b; }
    return a;
}

static void mode_reach(int T) {
    set_words(T + 2);
    Table a, b; tinit(&a, 1024);
    u64 z[MAXW] = {0}; tput(&a, z, 0);
    for (int t = 0; t < T; t++) {
        tinit(&b, a.n * 2 + 1024); layer(&a, &b, 0); tfree(&a); a = b;
        int mx = 0;
        for (size_t i = 0; i < a.cap; i++)
            if (a.val[i]) { int m = prefix(a.keys + i * NW, t + 2); if (m > mx) mx = m; }
        printf("%d %zu %d %d\n", t + 1, a.n, tmax(&a), mx);
        fflush(stdout);
    }
    tfree(&a);
}

static Table project(Table *a, int bits) {  // cut every state to `bits` cells, payoff reset to 0
    Table p; tinit(&p, a->n + 1024);
    u64 y[MAXW];
    for (size_t i = 0; i < a->cap; i++) {
        if (!a->val[i]) continue;
        memcpy(y, a->keys + i * NW, NW * sizeof(u64)); cut(y, bits); tput(&p, y, 0);
    }
    return p;
}

static void mode_window(int s, int w) {
    set_words((s + 2 > w ? s + 2 : w));
    Table a = reachable(s);
    Table p = project(&a, w), b;
    tfree(&a);
    for (int i = 0; i < w; i++) {
        tinit(&b, p.n * 2 + 1024); layer(&p, &b, w - i - 1 > 0 ? w - i - 1 : 1); tfree(&p); p = b;
        printf("%d %zu %d\n", i + 1, p.n, tmax(&p));
        fflush(stdout);
    }
    tfree(&p);
}

static void mode_cost(int s, int w, int B) {
    if (w >= B) { fprintf(stderr, "cost needs w < B\n"); exit(1); }
    set_words((s + 2 > B ? s + 2 : B));
    Table a = reachable(s);
    Table p = project(&a, B), b;
    tfree(&a);
    int *best = xmalloc((size_t)(B + 1) * sizeof(int));
    for (int i = 0; i < w; i++) {
        int keep = B - i - 1;
        tinit(&b, p.n * 2 + 1024); layer(&p, &b, keep); tfree(&p); p = b;
        for (int k = 0; k <= B; k++) best[k] = -1;  // the most ones over the plays that end with m >= k
        for (size_t j = 0; j < p.cap; j++) {
            if (!p.val[j]) continue;
            int m = prefix(p.keys + j * NW, keep), v = p.val[j] - 1;
            for (int k = 0; k <= m; k++) if (v > best[k]) best[k] = v;
        }
        printf("%d %zu", i + 1, p.n);
        for (int k = 1; k <= keep && best[k] >= 0; k++) printf(" %d", i + 1 - best[k]);
        printf("\n");
        fflush(stdout);
    }
    free(best);
    tfree(&p);
}

// ---------------------------------------------------------------------------------------------------------------------
// beam

typedef struct { int v; u64 h; int idx; } Cand;

static int cmp_cand(const void *a, const void *b) {
    const Cand *p = a, *q = b;
    if (p->v != q->v) return q->v - p->v;
    return (p->h < q->h) ? -1 : (p->h > q->h);
}

static void mode_beam(int T, int W) {
    if (W < 1 || W > (1 << 30)) { fprintf(stderr, "beam needs 1 <= W <= 2^30\n"); exit(1); }
    NW = (T + 2 + 63) / 64;  // any length: the beam keeps W states only
    u64 *X = xcalloc((size_t)W * NW, 8);
    int *V = xcalloc(W, sizeof(int));
    int n = 1;
    uint32_t **back = xmalloc((size_t)(T + 1) * sizeof(uint32_t *));  // back[t][r] = (parent << 1) | e
    u64 *Y = xmalloc((size_t)2 * W * NW * 8);
    int *VY = xmalloc((size_t)2 * W * sizeof(int));
    uint32_t *BY = xmalloc((size_t)2 * W * sizeof(uint32_t));
    Cand *C = xmalloc((size_t)2 * W * sizeof(Cand));
    size_t hcap = 1;
    while (hcap < (size_t)8 * W) hcap <<= 1;
    int *hidx = xmalloc(hcap * sizeof(int));
    for (int t = 0; t < T; t++) {
        for (size_t i = 0; i < hcap; i++) hidx[i] = -1;
        int m = 0;
        for (int i = 0; i < n; i++) {
            const u64 *x = X + (size_t)i * NW;
            for (int e = 0; e <= 1; e++) {
                if (e && (x[0] & 1)) continue;
                u64 *y = Y + (size_t)m * NW;
                step(x, e, y);
                int v = V[i] + e;
                u64 h = hkey(y);
                size_t j = h & (hcap - 1);
                for (;;) {
                    if (hidx[j] < 0) {
                        hidx[j] = m; VY[m] = v; BY[m] = ((uint32_t)i << 1) | (uint32_t)e;
                        C[m].v = v; C[m].h = h; C[m].idx = m; m++;
                        break;
                    }
                    int k = hidx[j];
                    if (memcmp(Y + (size_t)k * NW, y, NW * 8) == 0) {
                        if (VY[k] < v) { VY[k] = v; BY[k] = ((uint32_t)i << 1) | (uint32_t)e; C[k].v = v; }
                        break;
                    }
                    j = (j + 1) & (hcap - 1);
                }
            }
        }
        qsort(C, m, sizeof(Cand), cmp_cand);
        int keep = m < W ? m : W;
        back[t + 1] = xmalloc((size_t)keep * sizeof(uint32_t));
        for (int r = 0; r < keep; r++) {
            int k = C[r].idx;
            memcpy(X + (size_t)r * NW, Y + (size_t)k * NW, NW * 8);
            V[r] = VY[k];
            back[t + 1][r] = BY[k];
        }
        n = keep;
        printf("%d %d %d %d\n", t + 1, V[0], n, m);
        fflush(stdout);
    }
    char *word = xmalloc((size_t)T + 1);
    int r = 0;
    for (int t = T; t >= 1; t--) { word[t - 1] = (char)('0' + (back[t][r] & 1)); r = (int)(back[t][r] >> 1); }
    word[T] = 0;
    printf("play %s\n", word);
    fflush(stdout);
    for (int t = 1; t <= T; t++) free(back[t]);
    free(back); free(word); free(X); free(V); free(Y); free(VY); free(BY); free(C); free(hidx);
}

int main(int argc, char **argv) {
    if (argc < 3) {
        fprintf(stderr, "usage: value T | reach T | window s w | cost s w B | beam T W\n");
        return 1;
    }
    const char *mode = argv[1];
    if (!strcmp(mode, "value")) mode_value(atoi(argv[2]));
    else if (!strcmp(mode, "reach")) mode_reach(atoi(argv[2]));
    else if (!strcmp(mode, "window") && argc > 3) mode_window(atoi(argv[2]), atoi(argv[3]));
    else if (!strcmp(mode, "cost") && argc > 4) mode_cost(atoi(argv[2]), atoi(argv[3]), atoi(argv[4]));
    else if (!strcmp(mode, "beam") && argc > 3) mode_beam(atoi(argv[2]), atoi(argv[3]));
    else { fprintf(stderr, "unknown mode or missing arguments\n"); return 1; }
    return 0;
}
