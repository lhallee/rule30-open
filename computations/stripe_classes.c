/* Number of distinct center-column prefixes of length T among the rows supported in [-A, B].

   Usage: stripe_classes A B T   (T a multiple of 64, at most 2048)
   Prints: A B T rows distinct N(A,B)

   A row x < 2^(A+B+1) has bit k = cell B - k. It is simulated as a bitset whose bit i is cell i - off, off = A + T + 2,
   with one Rule 30 step new(i) = old(i-1) xor (old(i) or old(i+1)), i.e. new = (old << 1) ^ (old | (old >> 1)) in the
   convention of computations/rule30.py (bit i is cell origin + i). The center cell (bit off) is recorded at times
   0 .. T-1 into a T-bit signature; the signatures are sorted and the distinct ones counted.

   With the Lean theorem StripeClasses.box_columns (at most N(A,B) distinct center columns), a count of N(A,B) distinct prefixes
   proves that the box has exactly N(A,B) distinct center columns. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int SW; /* signature words */

static int cmp_sig(const void *a, const void *b) { return memcmp(a, b, (size_t)SW * 8); }

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: stripe_classes A B T\n"); return 1; }
    int A = atoi(argv[1]), B = atoi(argv[2]), T = atoi(argv[3]);
    if (T % 64 || T > 2048) { fprintf(stderr, "T must be a multiple of 64, at most 2048\n"); return 1; }
    SW = T / 64;
    int W = A + B + 1;
    long rows = 1L << W;
    int off = A + T + 2;
    int L = off + B + T + 3;            /* bits needed */
    int NW = (L + 63) / 64 + 1;         /* words, one spare */
    uint64_t *sig = calloc((size_t)rows * SW, 8);
    uint64_t *cur = calloc(NW, 8), *nxt = calloc(NW, 8);
    if (!sig || !cur || !nxt) { fprintf(stderr, "out of memory\n"); return 1; }
    for (long x = 0; x < rows; x++) {
        memset(cur, 0, (size_t)NW * 8);
        for (int k = 0; k < W; k++)
            if ((x >> k) & 1) { int i = B - k + off; cur[i >> 6] |= 1ULL << (i & 63); }
        uint64_t *s = sig + (size_t)x * SW;
        for (int t = 0; t < T; t++) {
            if ((cur[off >> 6] >> (off & 63)) & 1) s[t >> 6] |= 1ULL << (t & 63);
            for (int w = 0; w < NW; w++) {
                uint64_t o = cur[w];
                uint64_t lo = (o << 1) | (w > 0 ? cur[w - 1] >> 63 : 0);          /* bit i <- old bit i-1 */
                uint64_t hi = (o >> 1) | (w + 1 < NW ? cur[w + 1] << 63 : 0);     /* bit i <- old bit i+1 */
                nxt[w] = lo ^ (o | hi);
            }
            uint64_t *tmp = cur; cur = nxt; nxt = tmp;
        }
    }
    qsort(sig, (size_t)rows, (size_t)SW * 8, cmp_sig);
    long distinct = rows > 0 ? 1 : 0;
    for (long i = 1; i < rows; i++)
        if (memcmp(sig + (size_t)(i - 1) * SW, sig + (size_t)i * SW, (size_t)SW * 8)) distinct++;
    long N = (B == 0) ? (1L << (A + 1)) : (A == 0) ? (1L << B) + 1 : (1L << (A + B)) + 3 * (1L << (A - 1));
    printf("%d %d %d %ld %ld %ld\n", A, B, T, rows, distinct, N);
    free(sig); free(cur); free(nxt);
    return 0;
}
