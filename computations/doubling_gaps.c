/* The gap from a white diagonal to the next one, under the pair map F(A, B) = (B, C) on aligned words of period P.

   A word of period P is an integer whose bit t is the cell at time t mod P. For B != 0, C = pair_next(A, B) is the
   P-periodic word with C(t + 1) = A(t) xor (B(t) or C(t)). Where B(t) = 1 the cell is reset, C(t + 1) = not A(t); where
   B(t) = 0 it accumulates, C(t + 1) = A(t) xor C(t). So C(t + 1) = not S(t), with S(t) the XOR of A over the times
   from the last black cell r <= t of B (cyclically) to t. S is a segmented prefix XOR, computed in ceil(log2 P) rounds
   of rotations (a Hillis-Steele scan whose segments start at the black cells of B).

   The regime after a white diagonal w starts at the pair (D_w, D_{w+1}) = (0, Y) and runs along F to the first pair
   whose second word is white; its gap is the number of depths from w to that white diagonal: the least g >= 2 with
   F^(g-1)(0, Y) = (X, 0). At a doubling white diagonal Y is anti-periodic: Y(t + p) = not Y(t), P = 2p.

   Modes (words in hexadecimal, bit 0 the lowest):

     census p cap      every rotation class of anti-periodic words Y of least period 2p (2p <= 64), walked in lockstep
                       up to cap steps. Output: "classes N", then one line "Y gap" per class (gap = cap + 1 if no white
                       diagonal is reached), in the order of the classes' least rotations.
     orbit P cap Y     one regime from (0, Y), P <= 128 (64-bit words for P <= 64). Output: "gap g" (cap + 1 if not reached) and "end X", the
                       first word of the last pair (X, 0), that is D_{w' - 1}. Progress on stderr every 2^28 steps.

   Build: cc -O2 doubling_gaps.c -o doubling_gaps */

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef unsigned __int128 u128;

/* ---------------------------------------------------------------------------------------------------------------- */
/* 64-bit words, P <= 64 */

static int P64;
static uint64_t M64;

static inline uint64_t rotl64(uint64_t x, int d) {
    /* bit t of the result is bit t - d of x (cyclically, P64 bits), 0 < d < P64 */
    return ((x << d) | (x >> (P64 - d))) & M64;
}

static inline uint64_t next64(uint64_t a, uint64_t b) {
    /* b != 0 */
    uint64_t v = a, f = b;
    for (int d = 1; d < P64; d <<= 1) {
        v ^= rotl64(v, d) & ~f;
        f |= rotl64(f, d);
    }
    return P64 == 1 ? ((~v) & M64) : rotl64((~v) & M64, 1);
}

/* ---------------------------------------------------------------------------------------------------------------- */
/* 128-bit words, P <= 128 */

static int P128;
static u128 M128;

static inline u128 rotl128(u128 x, int d) {
    return ((x << d) | (x >> (P128 - d))) & M128;
}

static inline u128 next128(u128 a, u128 b) {
    u128 v = a, f = b;
    for (int d = 1; d < P128; d <<= 1) {
        v ^= rotl128(v, d) & ~f;
        f |= rotl128(f, d);
    }
    return P128 == 1 ? ((~v) & M128) : rotl128((~v) & M128, 1);
}

static u128 parse128(const char *s) {
    u128 x = 0;
    for (; *s; s++) {
        int c = *s, v;
        if (c >= '0' && c <= '9') v = c - '0';
        else if (c >= 'a' && c <= 'f') v = c - 'a' + 10;
        else if (c >= 'A' && c <= 'F') v = c - 'A' + 10;
        else continue;
        x = (x << 4) | (u128)v;
    }
    return x;
}

static void print128(const char *key, u128 x) {
    char buf[40];
    int n = 0;
    if (x == 0) buf[n++] = '0';
    while (x) {
        int v = (int)(x & 15);
        buf[n++] = (char)(v < 10 ? '0' + v : 'a' + v - 10);
        x >>= 4;
    }
    printf("%s ", key);
    while (n) putchar(buf[--n]);
    putchar('\n');
}

/* ---------------------------------------------------------------------------------------------------------------- */

static uint64_t rot64(uint64_t y, int k) { return k % P64 ? rotl64(y, P64 - (k % P64)) : y; }

static int least_period64(uint64_t y) {
    for (int q = 1; q < P64; q++)
        if (P64 % q == 0 && rot64(y, q) == y) return q;
    return P64;
}

static int census(int p, int64_t cap) {
    P64 = 2 * p;
    M64 = P64 == 64 ? ~(uint64_t)0 : (((uint64_t)1 << P64) - 1);
    uint64_t half = ((uint64_t)1 << p) - 1;
    size_t n = 0, room = 1024;
    uint64_t *ys = malloc(room * sizeof(uint64_t));
    for (uint64_t lo = 0; lo <= half; lo++) {
        uint64_t y = lo | (((~lo) & half) << p);
        if (least_period64(y) != P64) continue;
        int least = 1;
        for (int k = 1; k < P64 && least; k++)
            if (rot64(y, k) < y) least = 0;
        if (!least) continue;
        if (n == room) ys = realloc(ys, (room *= 2) * sizeof(uint64_t));
        ys[n++] = y;
    }
    printf("classes %zu\n", n);
    uint64_t *a = calloc(n, sizeof(uint64_t)), *b = malloc(n * sizeof(uint64_t));
    int64_t *gap = malloc(n * sizeof(int64_t));
    size_t *alive = malloc(n * sizeof(size_t));
    size_t live = n;
    for (size_t i = 0; i < n; i++) { b[i] = ys[i]; gap[i] = cap + 1; alive[i] = i; }
    for (int64_t k = 1; k <= cap && live; k++) {
        size_t keep = 0;
        for (size_t s = 0; s < live; s++) {
            size_t i = alive[s];
            uint64_t c = next64(a[i], b[i]);
            a[i] = b[i];
            b[i] = c;
            if (c == 0) gap[i] = k + 1;
            else alive[keep++] = i;
        }
        live = keep;
        if ((k & ((1 << 20) - 1)) == 0)
            fprintf(stderr, "\rp %d: %lld of %lld steps, %zu of %zu classes walking", p, (long long)k, (long long)cap,
                    live, n);
    }
    fprintf(stderr, "\n");
    for (size_t i = 0; i < n; i++) printf("%llx %lld\n", (unsigned long long)ys[i], (long long)gap[i]);
    return 0;
}

static int orbit64(int P, int64_t cap, uint64_t y) {
    P64 = P;
    M64 = P == 64 ? ~(uint64_t)0 : (((uint64_t)1 << P) - 1);
    uint64_t a = 0, b = y & M64;
    int64_t g = cap + 1;
    for (int64_t k = 1; k <= cap; k++) {
        uint64_t c = next64(a, b);
        a = b;
        b = c;
        if (c == 0) { g = k + 1; break; }
        if ((k & ((1 << 28) - 1)) == 0) {
            fprintf(stderr, "\rP %d: %lld of %lld steps", P, (long long)k, (long long)cap);
            fflush(stderr);
        }
    }
    printf("gap %lld\n", (long long)g);
    printf("end %llx\n", (unsigned long long)a);
    return 0;
}

static int orbit(int P, int64_t cap, const char *yhex) {
    if (P <= 64) return orbit64(P, cap, (uint64_t)parse128(yhex));
    P128 = P;
    M128 = P == 128 ? ~(u128)0 : (((u128)1 << P) - 1);
    u128 a = 0, b = parse128(yhex) & M128;
    int64_t g = cap + 1;
    for (int64_t k = 1; k <= cap; k++) {
        u128 c = next128(a, b);
        a = b;
        b = c;
        if (c == 0) { g = k + 1; break; }
        if ((k & ((1 << 28) - 1)) == 0) {
            fprintf(stderr, "\rP %d: %lld of %lld steps", P, (long long)k, (long long)cap);
            fflush(stderr);
        }
    }
    printf("gap %lld\n", (long long)g);
    print128("end", a);
    return 0;
}

int main(int argc, char **argv) {
    if (argc == 4 && !strcmp(argv[1], "census")) {
        int p = atoi(argv[2]);
        if (p < 1 || p > 32) { fprintf(stderr, "census needs 1 <= p <= 32\n"); return 2; }
        return census(p, atoll(argv[3]));
    }
    if (argc == 5 && !strcmp(argv[1], "orbit")) {
        int P = atoi(argv[2]);
        if (P < 1 || P > 128) { fprintf(stderr, "orbit needs 1 <= P <= 128\n"); return 2; }
        return orbit(P, atoll(argv[3]), argv[4]);
    }
    fprintf(stderr, "usage: doubling_gaps census p cap | orbit P cap Yhex\n");
    return 2;
}
