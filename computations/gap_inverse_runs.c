/* Constant runs of the inverse diagonal over the gap shift, for gap_inverse_runs.py.

   Symbols are 0..3, phi is the kit's table, boundary q = 3 - q. The kit's cone of a stream e has antidiagonals
     D_k[t] = cone(t, k - t),  D_k[0] = 3 - e_k,  D_k[1] = phi(e_{k-1}, D_k[0]),  D_k[t] = phi(D_{k-1}[t-2], D_k[t-1]),
   and inverse(s) = D_s[s] reads e only on [floor(s/2), s]. For a window v = e_h e_{h+1} ... the rows
     E_i[0] = 3 - v_i,  E_i[1] = phi(v_{i-1}, E_i[0]),  E_i[t] = phi(E_{i-1}[t-2], E_i[t-1]),  t <= 2i,
   do not depend on h, and D_{h+i}[t] = E_i[t] for t <= 2i, so inverse(h + i) = E_i[h + i] for every h <= i.

   A run of length r at s is inverse(s) = ... = inverse(s + r - 1) = c in {2, 3}; it is a property of the window
   e_h .. e_{s+r-1}, h = floor(s/2). The search runs over every word of a class (its factor language) of length
   i <= N as a window starting at h = i (s = 2i) and h = i - 1 (s = 2i - 1); from each such word and each value c of
   inverse(s) it follows the run: phi(a, .) is a bijection, so at most one next symbol keeps the run. So N(s, r), the
   number of windows of length ceil(s/2) + r with a run of length at least r at s, is exact for every s <= 2N.

   Classes: 0 the gap shift {1 2 2, 1 2 2 2 2}^omega (its factors: 2-runs between 1s of length 2 or 4, the 2-runs at
   the two ends of length at most 4), 1 binary, 2 hard-core (binary, no 1 after a 1).

   Build: cc -O3 -march=native -fopenmp gap_inverse_runs.c -o gap_inverse_runs
   Run:   ./gap_inverse_runs exhaust CLASS N RMAX SPLIT
            "N s r count" for count > 0, s <= 2N, 1 <= r <= RMAX;
            "W s r word" the least window (in the order 1 < 2) with the longest run at s, r its length;
            "L i count" the number of words of length i <= N; progress "P done total" on stderr.
          ./gap_inverse_runs sample CLASS L COUNT SEED RMAX
            COUNT random streams of length L from the measure of maximal entropy of the class, started in its
            stationary phase; inverse(s) for s < L by the antidiagonals;
            "M s r" the longest run starting at s over the sample (runs cut at L);
            "Q s r count" the streams with a run of length at least r at s, s + r <= L;
            "H r count" the streams whose longest run has length r. */

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <omp.h>

static const uint8_t PHI[4][4] = {{0, 1, 3, 2}, {3, 2, 1, 0}, {3, 2, 0, 1}, {3, 2, 1, 0}};

#define MAXW 200
#define ROW (2 * MAXW + 2)
#define MAXS (2 * MAXW + 2)
#define MAXR 64

static int cls, N, rmax;

static int next_state(int st, int x) {
    if (cls == 1) return 0;
    if (cls == 2) return x == 1 ? (st ? -1 : 1) : 0;
    int seen = st >> 3, d = st & 7;
    if (x == 2) return d < 4 ? (seen << 3) | (d + 1) : -1;
    return (!seen || d == 2 || d == 4) ? 8 : -1;
}

typedef struct {
    uint8_t v[MAXW];
    uint8_t E[MAXW][ROW];
    uint64_t cnt[MAXS][MAXR + 2];
    uint64_t words[MAXW + 1];
    int best[MAXS];
    uint8_t wit[MAXS][MAXW];
} Work;

static void row(Work *w, int i, int x) {
    uint8_t *E = w->E[i];
    w->v[i] = (uint8_t)x;
    E[0] = (uint8_t)(3 - x);
    if (i == 0) return;
    const uint8_t *P = w->E[i - 1];
    E[1] = PHI[w->v[i - 1]][E[0]];
    for (int t = 2; t <= 2 * i; t++) E[t] = PHI[P[t - 2]][E[t - 1]];
}

static void record(Work *w, int s, int len, int i) {
    /* window v[0..i-1] has a run of length len at s */
    w->cnt[s][len]++;
    if (len > w->best[s] || (len == w->best[s] && memcmp(w->v, w->wit[s], (size_t)i) < 0)) {
        w->best[s] = len;
        memcpy(w->wit[s], w->v, (size_t)i);
    }
}

static void follow(Work *w, int i, int st, int s, int h, int c, int len) {
    if (len >= rmax || i >= MAXW) return;
    for (int x = 1; x <= 2; x++) {
        int ns = next_state(st, x);
        if (ns < 0) continue;
        row(w, i, x);
        if (w->E[i][h + i] == c) {
            record(w, s, len + 1, i + 1);
            follow(w, i + 1, ns, s, h, c, len + 1);
            return;
        }
    }
}

/* The node: a word v[0..i-1] (rows E[0..i-1] set) in grammar state st. */
static void dfs(Work *w, int i, int st) {
    for (int x = 1; x <= 2; x++) {
        int ns = next_state(st, x);
        if (ns < 0) continue;
        row(w, i, x);
        w->words[i + 1]++;
        for (int s = 2 * i; s >= 2 * i - 1 && s >= 0; s--) {
            int h = s / 2, c = w->E[i][h + i];
            if (c == 2 || c == 3) {
                record(w, s, 1, i + 1);
                follow(w, i + 1, ns, s, h, c, 1);
            }
        }
        if (i + 1 <= N) dfs(w, i + 1, ns);
    }
}

typedef struct { uint8_t v[32]; int st; } Task;
static Task *tasks;
static int ntasks, cap_tasks, split;

static void serial(Work *w, int i, int st) {
    if (i == split) {
        if (ntasks == cap_tasks) {
            cap_tasks = cap_tasks ? 2 * cap_tasks : 1024;
            tasks = realloc(tasks, (size_t)cap_tasks * sizeof(Task));
        }
        memcpy(tasks[ntasks].v, w->v, (size_t)i);
        tasks[ntasks].st = st;
        ntasks++;
        return;
    }
    for (int x = 1; x <= 2; x++) {
        int ns = next_state(st, x);
        if (ns < 0) continue;
        row(w, i, x);
        w->words[i + 1]++;
        for (int s = 2 * i; s >= 2 * i - 1 && s >= 0; s--) {
            int h = s / 2, c = w->E[i][h + i];
            if (c == 2 || c == 3) {
                record(w, s, 1, i + 1);
                follow(w, i + 1, ns, s, h, c, 1);
            }
        }
        if (i + 1 <= N) serial(w, i + 1, ns);
    }
}

static void merge(Work *into, Work *from) {
    for (int s = 0; s < MAXS; s++) {
        for (int r = 0; r <= MAXR + 1; r++) into->cnt[s][r] += from->cnt[s][r];
        int len = from->best[s];
        if (len == 0) continue;
        int i = s - s / 2 + len;
        if (len > into->best[s] || (len == into->best[s] && memcmp(from->wit[s], into->wit[s], (size_t)i) < 0)) {
            into->best[s] = len;
            memcpy(into->wit[s], from->wit[s], (size_t)i);
        }
    }
    for (int i = 0; i <= MAXW; i++) into->words[i] += from->words[i];
}

static int exhaust(void) {
    Work *total = calloc(1, sizeof(Work));
    if (split > N) split = N;
    serial(total, 0, 0);
    int done = 0, step = ntasks / 100 + 1;
#pragma omp parallel
    {
        Work *w = calloc(1, sizeof(Work));
#pragma omp for schedule(dynamic, 1)
        for (int k = 0; k < ntasks; k++) {
            int st = 0;
            for (int i = 0; i < split; i++) {
                row(w, i, tasks[k].v[i]);
                st = next_state(st, tasks[k].v[i]);
            }
            dfs(w, split, st);
            int d;
#pragma omp atomic capture
            d = ++done;
            if (d % step == 0 || d == ntasks) {
                fprintf(stderr, "P %d %d\n", d, ntasks);
                fflush(stderr);
            }
        }
#pragma omp critical
        merge(total, w);
        free(w);
    }
    for (int s = 0; s <= 2 * N; s++) {
        for (int r = 1; r <= rmax; r++)
            if (total->cnt[s][r]) printf("N %d %d %llu\n", s, r, (unsigned long long)total->cnt[s][r]);
        int len = total->best[s];
        if (len) {
            int i = s - s / 2 + len;
            printf("W %d %d ", s, len);
            for (int j = 0; j < i; j++) putchar('0' + total->wit[s][j]);
            putchar('\n');
        }
    }
    for (int i = 1; i <= N + 1; i++) printf("L %d %llu\n", i, (unsigned long long)total->words[i]);
    free(total);
    free(tasks);
    return 0;
}

/* xorshift64* */
static uint64_t rng_next(uint64_t *s) {
    *s ^= *s >> 12; *s ^= *s << 25; *s ^= *s >> 27;
    return *s * 2685821657736338717ULL;
}
static double rng_unit(uint64_t *s) { return (double)(rng_next(s) >> 11) * (1.0 / 9007199254740992.0); }

static void random_stream(uint8_t *e, int L, uint64_t *rs) {
    if (cls == 1) {
        for (int i = 0; i < L; i++) e[i] = (uint8_t)(1 + (rng_next(rs) >> 63));
        return;
    }
    if (cls == 2) {
        /* the golden-mean measure of maximal entropy: after 2 a 1 with probability 1/phi^2,
           stationary P(1) = 1/(1+phi^2) */
        double g = 1.6180339887498949, p1 = 1.0 / (g * g), q1 = 1.0 / (1.0 + g * g);
        int last = rng_unit(rs) < q1 ? 1 : 2;
        for (int i = 0; i < L; i++) {
            e[i] = (uint8_t)last;
            last = last == 1 ? 2 : (rng_unit(rs) < p1 ? 1 : 2);
        }
        return;
    }
    /* the gap shift: blocks 122 and 12222 with probabilities lambda^-3 and lambda^-5, lambda^5 = lambda^2 + 1; the
       first block has length l with probability proportional to l lambda^-l, entered at a uniform offset */
    double lo = 1.0, hi = 2.0;
    for (int it = 0; it < 80; it++) {
        double m = (lo + hi) / 2;
        if (1 / (m * m * m) + 1 / (m * m * m * m * m) > 1) lo = m; else hi = m;
    }
    double p3 = 1 / (lo * lo * lo), w3 = 3 * p3, w5 = 5 * (1 - p3);
    int l = rng_unit(rs) < w3 / (w3 + w5) ? 3 : 5;
    int off = (int)(rng_unit(rs) * l), i = 0;
    for (int k = off; k < l && i < L; k++) e[i++] = k == 0 ? 1 : 2;
    while (i < L) {
        l = rng_unit(rs) < p3 ? 3 : 5;
        for (int k = 0; k < l && i < L; k++) e[i++] = k == 0 ? 1 : 2;
    }
}

static int sample(int L, long count, uint64_t seed) {
    int *maxrun = calloc((size_t)L, sizeof(int));
    uint64_t *q = calloc((size_t)L * (MAXR + 2), sizeof(uint64_t));
    uint64_t hist[MAXS] = {0};
    long done = 0, step = count / 100 + 1;
#pragma omp parallel
    {
        uint8_t *e = malloc((size_t)L), *I = malloc((size_t)L);
        uint8_t *A = malloc((size_t)L + 1), *B = malloc((size_t)L + 1);
        int *mr = calloc((size_t)L, sizeof(int));
        uint64_t *qq = calloc((size_t)L * (MAXR + 2), sizeof(uint64_t));
        uint64_t hh[MAXS] = {0};
#pragma omp for schedule(dynamic, 64)
        for (long n = 0; n < count; n++) {
            uint64_t rs = seed * 0x9E3779B97F4A7C15ULL + (uint64_t)n * 0xD1B54A32D192ED03ULL + 1;
            for (int k = 0; k < 4; k++) rng_next(&rs);
            random_stream(e, L, &rs);
            /* antidiagonals: A = D_{k-1}, B = D_k */
            for (int k = 0; k < L; k++) {
                B[0] = (uint8_t)(3 - e[k]);
                if (k >= 1) B[1] = PHI[e[k - 1]][B[0]];
                for (int t = 2; t <= k; t++) B[t] = PHI[A[t - 2]][B[t - 1]];
                I[k] = B[k];
                uint8_t *T = A; A = B; B = T;
            }
            int longest = 0;
            for (int s = 0; s < L; s++) {
                int c = I[s], r = 0;
                if (c == 2 || c == 3)
                    while (s + r < L && I[s + r] == c) r++;
                if (r > mr[s]) mr[s] = r;
                if (r > longest) longest = r;
                for (int k = 1; k <= r && k <= MAXR; k++) qq[(size_t)s * (MAXR + 2) + k]++;
            }
            hh[longest < MAXS ? longest : MAXS - 1]++;
            long d;
#pragma omp atomic capture
            d = ++done;
            if (d % step == 0 || d == count) {
                fprintf(stderr, "P %ld %ld\n", d, count);
                fflush(stderr);
            }
        }
#pragma omp critical
        {
            for (int s = 0; s < L; s++) if (mr[s] > maxrun[s]) maxrun[s] = mr[s];
            for (size_t k = 0; k < (size_t)L * (MAXR + 2); k++) q[k] += qq[k];
            for (int r = 0; r < MAXS; r++) hist[r] += hh[r];
        }
        free(e); free(I); free(A); free(B); free(mr); free(qq);
    }
    for (int s = 0; s < L; s++) {
        printf("M %d %d\n", s, maxrun[s]);
        for (int r = 1; r <= rmax && s + r <= L; r++)
            if (q[(size_t)s * (MAXR + 2) + r])
                printf("Q %d %d %llu\n", s, r, (unsigned long long)q[(size_t)s * (MAXR + 2) + r]);
    }
    for (int r = 0; r < MAXS; r++) if (hist[r]) printf("H %d %llu\n", r, (unsigned long long)hist[r]);
    free(maxrun); free(q);
    return 0;
}

int main(int argc, char **argv) {
    if (argc >= 6 && strcmp(argv[1], "exhaust") == 0) {
        cls = atoi(argv[2]); N = atoi(argv[3]); rmax = atoi(argv[4]); split = atoi(argv[5]);
        if (N < 1 || N + rmax + 1 >= MAXW || rmax > MAXR || split > 31) return 2;
        return exhaust();
    }
    if (argc >= 7 && strcmp(argv[1], "sample") == 0) {
        cls = atoi(argv[2]);
        int L = atoi(argv[3]);
        long count = atol(argv[4]);
        uint64_t seed = strtoull(argv[5], NULL, 10);
        rmax = atoi(argv[6]);
        if (L < 1 || L + 1 >= MAXS || rmax > MAXR) return 2;
        return sample(L, count, seed);
    }
    fprintf(stderr, "usage: exhaust CLASS N RMAX SPLIT | sample CLASS L COUNT SEED RMAX\n");
    return 2;
}
