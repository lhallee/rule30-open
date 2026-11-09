/* The letters a completion feeds to the left cut of Rule 30's cone (computations/letter_words.py).
 *
 * A completion is a number r (bit k = the cell k places right of the cut); one step is nstep(r) = r ^ ((r>>1)|(r>>2)),
 * the frame moving one cell right; its letter at time s is nevo(r, s) % 4 (bit 0 = the cell next to the cut). A word of
 * T letters is coded with letter s in bits 2s, 2s+1. The a left cells P (bit 0 = cell -t) run one step as
 * nstep(2^a e + P) mod 2^a for the letter e, and c_t = bit 0 of P after T = t - (ceil(a/2) - 1) letters and
 * n = ceil(a/2) - 1 more steps.
 *
 *   count T        |W_T|, the number of words of T letters over all completions of 2T cells
 *   forbid K       the number of minimal forbidden words of each length 2 .. K
 *   entropy K      the spectral radius of the shift of finite type X_k whose k-blocks are W_k, k = 2 .. K
 *   follow K       distinct follower and predecessor sets of the words of W, lengths up to K
 *   wordmat t a    |W_T|, the GF(2) rank of the cut and N_L(t, a), from the columns of all words
 *   refine t a     N_L(t, a) by refining with the words in a fixed pseudo-random order, stopping when all are apart
 *   ideal a T      the classes of the a left cells under all words of 1 .. T letters with every letter allowed
 *
 * Compile: cc -O3 -fopenmp letter_words.c (OpenMP optional). Output lines are "key value" or as documented.
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#ifdef _OPENMP
#include <omp.h>
#endif

static inline uint64_t nstep(uint64_t r) { return r ^ ((r >> 1) | (r >> 2)); }

static uint64_t word_of(uint64_t r, int T) {
  uint64_t w = 0;
  for (int s = 0; s < T; s++) { w |= (r & 3) << (2 * s); r = nstep(r); }
  return w;
}

/* bitset of the words of T letters over completions of nb cells */
static uint64_t *word_bits(int T, int nb, uint64_t *count) {
  uint64_t nw = 1ULL << (2 * T), nr = 1ULL << nb;
  uint64_t *seen = calloc((nw + 63) / 64, 8);
  #pragma omp parallel for schedule(static, 1 << 14)
  for (uint64_t r = 0; r < nr; r++) {
    uint64_t w = word_of(r, T);
    __atomic_fetch_or(&seen[w >> 6], 1ULL << (w & 63), __ATOMIC_RELAXED);
  }
  uint64_t c = 0;
  for (uint64_t i = 0; i < (nw + 63) / 64; i++) c += __builtin_popcountll(seen[i]);
  *count = c;
  return seen;
}

static int in_set(uint64_t *bits, uint64_t w) { return (bits[w >> 6] >> (w & 63)) & 1; }

static int cmd_count(int T) {
  uint64_t c; uint64_t *b = word_bits(T, 2 * T, &c);
  printf("T %d\ncount %llu\n", T, (unsigned long long)c);
  free(b); return 0;
}

static uint64_t *Wk[20];
static int inW(int k, uint64_t w) { return k == 0 ? 1 : in_set(Wk[k], w); }

static void build_Wk(int K) { for (int k = 1; k <= K; k++) { uint64_t c; Wk[k] = word_bits(k, 2 * k, &c); } }

static int cmd_forbid(int K) {
  build_Wk(K);
  for (int k = 2; k <= K; k++) {
    uint64_t nw = 1ULL << (2 * k), cnt = 0;
    for (uint64_t w = 0; w < nw; w++) {
      if (inW(k, w)) continue;
      uint64_t pre = w & ((1ULL << (2 * (k - 1))) - 1), suf = w >> 2;
      if (inW(k - 1, pre) && inW(k - 1, suf)) cnt++;
    }
    printf("forbidden %d %llu\n", k, (unsigned long long)cnt);
  }
  return 0;
}

static int cmd_entropy(int K) {
  build_Wk(K);
  for (int k = 2; k <= K; k++) {
    uint64_t ns = 1ULL << (2 * (k - 1));
    double *v = malloc(ns * sizeof(double)), *nv = malloc(ns * sizeof(double));
    for (uint64_t u = 0; u < ns; u++) v[u] = inW(k - 1, u) ? 1.0 : 0.0;
    double lam = 0;
    for (int it = 0; it < 600; it++) {
      memset(nv, 0, ns * sizeof(double));
      for (uint64_t u = 0; u < ns; u++) if (v[u] > 0) for (int e = 0; e < 4; e++) {
        uint64_t w = u | ((uint64_t)e << (2 * (k - 1)));
        if (inW(k, w)) nv[w >> 2] += v[u];
      }
      double s = 0, ss = 0;
      for (uint64_t u = 0; u < ns; u++) { s += nv[u]; ss += v[u]; }
      lam = s / ss;
      for (uint64_t u = 0; u < ns; u++) v[u] = nv[u] / s;
    }
    printf("radius %d %.6f\n", k, lam);
    free(v); free(nv);
  }
  return 0;
}

typedef struct { uint64_t h1, h2; } H2;
static int cmp_h2(const void *a, const void *b) {
  const H2 *x = a, *y = b;
  if (x->h1 != y->h1) return x->h1 < y->h1 ? -1 : 1;
  if (x->h2 != y->h2) return x->h2 < y->h2 ? -1 : 1;
  return 0;
}

static int cmd_follow(int K) {
  build_Wk(K);
  for (int dir = 0; dir < 2; dir++) for (int L = 1; L <= 4 && L < K; L++) {
    printf("%s %d", dir == 0 ? "follower" : "predecessor", L);
    for (int k = 1; k + L <= K; k++) {
      uint64_t nu = 1ULL << (2 * k), nv = 1ULL << (2 * L), m = 0;
      H2 *hs = malloc(nu * sizeof(H2));
      for (uint64_t u = 0; u < nu; u++) {
        if (!inW(k, u)) continue;
        uint64_t h1 = 1469598103934665603ULL, h2 = 7;
        for (uint64_t v = 0; v < nv; v++) {
          uint64_t w = dir == 0 ? (u | (v << (2 * k))) : (v | (u << (2 * L)));
          if (inW(k + L, w)) { h1 ^= v + 0x9E3779B97F4A7C15ULL; h1 *= 1099511628211ULL; h2 = h2 * 6364136223846793005ULL + v + 1; }
        }
        hs[m].h1 = h1; hs[m].h2 = h2; m++;
      }
      qsort(hs, m, sizeof(H2), cmp_h2);
      uint64_t d = m ? 1 : 0;
      for (uint64_t i = 1; i < m; i++) if (cmp_h2(&hs[i], &hs[i - 1])) d++;
      printf(" %llu", (unsigned long long)d);
      free(hs);
    }
    printf("\n");
  }
  return 0;
}

/* the column of a word: bit P = c_t for the left cells P, all 2^a at once (W64 words per slice) */
static void column(int a, int T, int n, uint64_t w, const uint64_t *init, uint64_t W64, uint64_t *sa, uint64_t *sb,
                   uint64_t *out) {
  memcpy(sa, init, (size_t)a * W64 * 8);
  for (int s = 0; s < T + n; s++) {
    uint64_t f0 = 0, f1 = 0;
    if (s < T) { f0 = (w >> (2 * s) & 1) ? ~0ULL : 0; f1 = (w >> (2 * s + 1) & 1) ? ~0ULL : 0; }
    for (int j = 0; j < a; j++) {
      const uint64_t *A = sa + (size_t)j * W64;
      const uint64_t *B = j + 1 < a ? sa + (size_t)(j + 1) * W64 : NULL;
      const uint64_t *C = j + 2 < a ? sa + (size_t)(j + 2) * W64 : NULL;
      uint64_t cb = (j + 1 == a) ? f0 : 0, cc = (j + 2 == a) ? f0 : f1;
      uint64_t *D = sb + (size_t)j * W64;
      for (uint64_t q = 0; q < W64; q++) D[q] = A[q] ^ ((B ? B[q] : cb) | (C ? C[q] : cc));
    }
    uint64_t *tmp = sa; sa = sb; sb = tmp;
  }
  memcpy(out, sa, W64 * 8);
}

static uint64_t *slices(int a, uint64_t W64) {
  uint64_t NP = 1ULL << a;
  uint64_t *init = calloc((size_t)a * W64, 8);
  for (uint64_t P = 0; P < NP; P++) for (int j = 0; j < a; j++) if (P >> j & 1) init[(size_t)j * W64 + P / 64] |= 1ULL << (P % 64);
  return init;
}

static uint64_t *word_list(int t, int a, int *T_, int *n_, uint64_t *cnt_) {
  int n = (a + 1) / 2 - 1, T = t - n;
  int nb = 2 * t + 1 - a; if (nb > 2 * T) nb = 2 * T;
  uint64_t cnt; uint64_t *bits = word_bits(T, nb, &cnt);
  uint64_t *wl = malloc(cnt * 8), k = 0, nw = 1ULL << (2 * T);
  for (uint64_t w = 0; w < nw; w++) if (in_set(bits, w)) wl[k++] = w;
  free(bits);
  *T_ = T; *n_ = n; *cnt_ = cnt;
  return wl;
}

static uint32_t refine_classes(uint32_t *cls, uint32_t ncls, const uint64_t *col, uint64_t NP, uint32_t *map0) {
  for (uint64_t c = 0; c < 2 * (uint64_t)ncls; c++) map0[c] = 0xffffffff;
  uint32_t nn = 0;
  for (uint64_t P = 0; P < NP; P++) {
    uint32_t key = cls[P] * 2 + (uint32_t)(col[P / 64] >> (P % 64) & 1);
    if (map0[key] == 0xffffffff) map0[key] = nn++;
    cls[P] = map0[key];
  }
  return nn;
}

static int cmd_wordmat(int t, int a) {
  int T, n; uint64_t cnt; uint64_t *wl = word_list(t, a, &T, &n, &cnt);
  uint64_t NP = 1ULL << a, W64 = (NP + 63) / 64;
  uint64_t *init = slices(a, W64), *cols = calloc((size_t)cnt * W64, 8);
  #pragma omp parallel
  {
    uint64_t *sa = malloc((size_t)a * W64 * 8), *sb = malloc((size_t)a * W64 * 8);
    #pragma omp for schedule(dynamic, 16)
    for (uint64_t i = 0; i < cnt; i++) {
      column(a, T, n, wl[i], init, W64, sa, sb, cols + i * W64);
      if (NP < 64) cols[i * W64] &= (1ULL << NP) - 1;
    }
    free(sa); free(sb);
  }
  uint32_t *cls = calloc(NP, 4), ncls = 1, *map0 = malloc(NP * 2 * 4);
  for (uint64_t i = 0; i < cnt && ncls < NP; i++) ncls = refine_classes(cls, ncls, cols + i * W64, NP, map0);
  int rank = 0;
  for (uint64_t bit = 0; bit < NP && (uint64_t)rank < cnt; bit++) {
    uint64_t q = bit / 64, b = 1ULL << (bit % 64), piv = (uint64_t)-1;
    for (uint64_t i = rank; i < cnt; i++) if (cols[i * W64 + q] & b) { piv = i; break; }
    if (piv == (uint64_t)-1) continue;
    if (piv != (uint64_t)rank) for (uint64_t z = 0; z < W64; z++) {
      uint64_t tmp = cols[piv * W64 + z]; cols[piv * W64 + z] = cols[(uint64_t)rank * W64 + z]; cols[(uint64_t)rank * W64 + z] = tmp;
    }
    #pragma omp parallel for
    for (uint64_t i = 0; i < cnt; i++)
      if (i != (uint64_t)rank && (cols[i * W64 + q] & b)) for (uint64_t z = 0; z < W64; z++) cols[i * W64 + z] ^= cols[(uint64_t)rank * W64 + z];
    rank++;
  }
  printf("t %d\na %d\nT %d\nwords %llu\nrank %d\nNL %u\n", t, a, T, (unsigned long long)cnt, rank, ncls);
  return 0;
}

static int cmd_refine(int t, int a) {
  int T, n; uint64_t cnt; uint64_t *wl = word_list(t, a, &T, &n, &cnt);
  uint64_t st = 88172645463325252ULL;
  for (uint64_t i = cnt - 1; i > 0; i--) {
    st ^= st << 13; st ^= st >> 7; st ^= st << 17;
    uint64_t j = st % (i + 1), tmp = wl[i]; wl[i] = wl[j]; wl[j] = tmp;
  }
  uint64_t NP = 1ULL << a, W64 = (NP + 63) / 64;
  uint64_t *init = slices(a, W64);
  uint32_t *cls = calloc(NP, 4), ncls = 1, *map0 = malloc(NP * 2 * 4);
  int B = 64; uint64_t *cols = malloc((size_t)B * W64 * 8), done = 0;
  while (done < cnt && ncls < NP) {
    int nbatch = cnt - done < (uint64_t)B ? (int)(cnt - done) : B;
    #pragma omp parallel
    {
      uint64_t *sa = malloc((size_t)a * W64 * 8), *sb = malloc((size_t)a * W64 * 8);
      #pragma omp for schedule(dynamic, 1)
      for (int bi = 0; bi < nbatch; bi++) column(a, T, n, wl[done + bi], init, W64, sa, sb, cols + (size_t)bi * W64);
      free(sa); free(sb);
    }
    for (int bi = 0; bi < nbatch && ncls < NP; bi++) {
      if (NP < 64) cols[(size_t)bi * W64] &= (1ULL << NP) - 1;
      ncls = refine_classes(cls, ncls, cols + (size_t)bi * W64, NP, map0);
    }
    done += nbatch;
    fprintf(stderr, "\r%llu/%llu words, %u classes", (unsigned long long)done, (unsigned long long)cnt, ncls);
  }
  fprintf(stderr, "\n");
  printf("t %d\na %d\nT %d\nwords %llu\nused %llu\nNL %u\n", t, a, T, (unsigned long long)cnt, (unsigned long long)done, ncls);
  return 0;
}

static int cmd_ideal(int a, int Tmax) {
  int n = (a + 1) / 2 - 1;
  uint64_t N = 1ULL << a, mask = N - 1;
  uint32_t *L[3];
  for (int e = 0; e < 3; e++) { L[e] = malloc(N * 4); for (uint64_t x = 0; x < N; x++) L[e][x] = (uint32_t)(nstep(((uint64_t)e << a) | x) & mask); }
  uint32_t *c = malloc(N * 4), *nc = malloc(N * 4);
  for (uint64_t x = 0; x < N; x++) { uint64_t y = x; for (int s = 0; s < n; s++) y = nstep(y); c[x] = (uint32_t)(y & 1); }
  uint64_t cap = 1; while (cap < 4 * N) cap <<= 1;
  uint64_t *hk = malloc(cap * 8); uint32_t *hv = malloc(cap * 4);
  for (int T = 1; T <= Tmax; T++) {
    for (uint64_t i = 0; i < cap; i++) hk[i] = ~0ULL;
    uint32_t cnt = 0;
    for (uint64_t x = 0; x < N; x++) {
      uint64_t k = (uint64_t)c[L[0][x]] | ((uint64_t)c[L[1][x]] << 21) | ((uint64_t)c[L[2][x]] << 42);
      uint64_t h = ((k * 0x9E3779B97F4A7C15ULL) >> 20) & (cap - 1);
      while (hk[h] != ~0ULL && hk[h] != k) h = (h + 1) & (cap - 1);
      if (hk[h] == ~0ULL) { hk[h] = k; hv[h] = cnt++; }
      nc[x] = hv[h];
    }
    uint32_t *tmp = c; c = nc; nc = tmp;
    printf("classes %d %u\n", T, cnt);
    if (cnt == N) break;
  }
  return 0;
}

int main(int argc, char **argv) {
  if (argc < 3) { fprintf(stderr, "usage: see the header\n"); return 2; }
  const char *c = argv[1];
  if (!strcmp(c, "count")) return cmd_count(atoi(argv[2]));
  if (!strcmp(c, "forbid")) return cmd_forbid(atoi(argv[2]));
  if (!strcmp(c, "entropy")) return cmd_entropy(atoi(argv[2]));
  if (!strcmp(c, "follow")) return cmd_follow(atoi(argv[2]));
  if (!strcmp(c, "wordmat")) return cmd_wordmat(atoi(argv[2]), atoi(argv[3]));
  if (!strcmp(c, "refine")) return cmd_refine(atoi(argv[2]), atoi(argv[3]));
  if (!strcmp(c, "ideal")) return cmd_ideal(atoi(argv[2]), atoi(argv[3]));
  fprintf(stderr, "unknown command\n");
  return 2;
}
