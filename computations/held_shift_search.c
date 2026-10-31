/* The rational points of K by the tree of forced bits, with the period tried at every leaf.

   K is the set of 2-adic integers U with H^t(U) odd at every odd t, H(U) = (U >> 1) xor (U or (U << 1)). Its points
   are the graph of a map from the free bits u_0, u_2, ... to the forced bits u_1, u_3, ... (see held_shift.py). This
   program walks the tree of K to depth M, so 2^(M/2) leaves. At each leaf and each period q <= Q it extends the
   prefix by the rule u_i = u_(i-q) up to depth L and keeps the leaf if the forced bits all agree. A hit is a prefix
   whose periodic extension holds the condition through L - 1 steps; a hit of any preperiod p with p + q <= M is
   found. Survivors by chance are removed by `python -m computations.held_shift --hits`, which checks 1200 steps.

   The walk keeps the anti-diagonals of the space-time diagram as bit words: D_k[s] is cell k - s at step s, and
   D_k = prefix_xor((D_(k-1) or D_(k-2)) << 1) xor (u_k ? all ones : 0), so a new bit costs a few word operations.
   The bit x[k][0] read for the forced bit u_k (k odd) is bit k of the prefix xor.

   Build and run (MinGW needs -mno-avx with OpenMP; L at most 127):
       gcc -O3 -mno-avx -fopenmp held_shift_search.c -o search
       ./search M Q L F threads > hits.txt          # F free bits split over the work items, e.g. 64 56 126 10 8
   Each output line is `q high low`: the first M bits of the point as two 64-bit hexadecimal words. */
#include <stdio.h>
#include <stdlib.h>
#include <omp.h>
typedef unsigned __int128 u128;
static inline u128 pxor(u128 x){x^=x<<1;x^=x<<2;x^=x<<4;x^=x<<8;x^=x<<16;x^=x<<32;x^=x<<64;return x;}
static inline u128 maskk(int k){return k>=127?~(u128)0:(((u128)1<<(k+1))-1);}
static int M,Q,L;
typedef struct {u128 D1,D2,u; int k;} St; /* D1 = D_(k-1), D2 = D_(k-2), u holds bits 0..k-1 */
static void report(u128 u,int q){
  #pragma omp critical
  { printf("%d %016llx %016llx\n",q,(unsigned long long)(u>>64),(unsigned long long)u); fflush(stdout);} }
static void probe(const St*s0,int q){
  u128 D1=s0->D1,D2=s0->D2,u=s0->u;
  for(int k=s0->k;k<L;k++){
    u128 ub=(u>>(k-q))&1;
    u128 P=pxor(((D1|D2)<<1)&maskk(k))&maskk(k);
    if(k&1){ u128 g=(P>>k)&1; if((1^g)!=ub) return; }
    u128 Dk = ub? (P^maskk(k)) : P;
    u |= ub<<k; D2=D1; D1=Dk;
  }
  report(s0->u,q);
}
static void dfs(St s,long long*cnt){
  if(s.k==M){ (*cnt)++; for(int q=1;q<=Q;q++) probe(&s,q); return; }
  int k=s.k;
  u128 P=pxor(((s.D1|s.D2)<<1)&maskk(k))&maskk(k);
  if(k&1){
    u128 ub=1^((P>>k)&1);
    St t; t.D2=s.D1; t.D1= ub?(P^maskk(k)):P; t.u=s.u|(ub<<k); t.k=k+1; dfs(t,cnt);
  } else {
    for(u128 ub=0;ub<2;ub++){ St t; t.D2=s.D1; t.D1= ub?(P^maskk(k)):P; t.u=s.u|(ub<<k); t.k=k+1; dfs(t,cnt);}
  }
}
int main(int argc,char**argv){
  if(argc<6){fprintf(stderr,"usage: search M Q L F threads\n");return 1;}
  M=atoi(argv[1]);Q=atoi(argv[2]);L=atoi(argv[3]);int F=atoi(argv[4]);int nt=atoi(argv[5]);
  omp_set_num_threads(nt);
  long long total=0;
  #pragma omp parallel for schedule(dynamic,1) reduction(+:total)
  for(long long w=0;w<(1LL<<F);w++){
    St s; s.D1=0;s.D2=0;s.u=0;s.k=0;
    for(int k=0;k<2*F;k++){
      u128 P=pxor(((s.D1|s.D2)<<1)&maskk(k))&maskk(k);
      u128 ub; if(k&1){ub=1^((P>>k)&1);} else ub=(w>>(k/2))&1;
      St t; t.D2=s.D1; t.D1=ub?(P^maskk(k)):P; t.u=s.u|(ub<<k); t.k=k+1; s=t;
    }
    long long c=0; dfs(s,&c); total+=c;
  }
  fprintf(stderr,"leaves %lld\n",total);
  return 0;
}
