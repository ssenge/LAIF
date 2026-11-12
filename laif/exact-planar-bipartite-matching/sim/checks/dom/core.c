// Independent engine for Sections 3-5 of notes/DOMINATORS.md. No repo code.
// Modes:
//   core graph N K [Eall|E0|Esample] [seconds] [seed] : all digraphs on N vertices with path 0..K-1 (WLOG by relabelling), all entry sets
//   core graphrand N K seconds seed                    : random digraphs
//   core abs K                                         : all arrays (A,B) for path length K, all (a,b)
//   core absrand KMAX seconds seed                     : structured random arrays up to KMAX
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
typedef unsigned int u32;
typedef unsigned long long u64;
#define INF 100000000
#define MAXK 520
#define MAXN 16
#define LV 11
static u64 C[64];
enum {N_inst,N_cand,N_ring,N_past,N_chain3,N_eqm,N_long,N_y,N_trunc,N_routecross,N_a0,N_afterlast,
  F_L1a,F_L1b,F_L2a_strict,F_L2a_one,F_L2b,F_L5,F_m,F_L6,F_ring_pos,F_ring_once,F_ring_count,F_route,F_marktwice,F_delta,F_lam,F_pt,F_L7,F_L3a,F_L3b,F_Aconn,F_Bconn,F_leaf,F_ptrunc,F_L4part,F_L4root,F_L4a,F_L4b,F_prop,F_strictdiff,F_entry,NUMC};
static const char*NAME[]={"n.inst","n.cand","n.ring","n.past","n.chain>=3","n.eq_m","n.m>j+1","n.y","n.truncY","n.route_cross","n.a0","n.afterlast",
 "FAIL.L1a","FAIL.L1b","FAIL.L2a_strict","FAIL.L2a_one","FAIL.L2b","FAIL.L5","FAIL.m","FAIL.L6","FAIL.ring_pos","FAIL.ring_once","FAIL.ring_count","FAIL.route","FAIL.marktwice","FAIL.delta","FAIL.lam","FAIL.pt","FAIL.L7","FAIL.L3a","FAIL.L3b","FAIL.Aconn","FAIL.Bconn","FAIL.leaf","FAIL.ptrunc","FAIL.L4part","FAIL.L4root","FAIL.L4a","FAIL.L4b","FAIL.prop","FAIL.strictdiff","FAIL.entry"};
static u64 CC[NUMC];
static int printed[NUMC];
static void (*dump)(void)=0;
#define HIT(x) do{CC[x]++; if(x>=F_L1a && !printed[x]){printed[x]=1; printf("FIRST %s at line %d\n",NAME[x],__LINE__); if(dump)dump();}}while(0)

// ---------- Section 5 on arrays. Positions 1..k. A,B arrays. truth m optional.
typedef struct { int k; int A[MAXK+3],B[MAXK+3]; int m[MAXK+3]; int lam[LV][MAXK+3],dlt[LV][MAXK+3]; } St;
#define NA (-1)   /* not in this role at this level */
#define NONE 0    /* role, but no member */

static inline int closed(const St*s,int j,int x){ for(int t=j+1;t<x;t++){ if(s->A[t]<j||s->B[t]>=x) return 0;} return 1; }

static void step2(St*s){
  int k=s->k; int size=1,lev=0;
  for(int j=1;j<=k;j++) s->m[j]=j+1;
  static int g[MAXK+3],ta[MAXK+3],X[MAXK+3];
  while(size<k){
    for(int l=1;l+size<=k;l+=2*size){
      int c=l+size-1,r=l+2*size-1; if(r>k){r=k;CC[N_trunc]++;}
      int mx=-INF,last=0;
      // g(x), x in c+1..r+1
      for(int x=c+1;x<=r+1;x++){
        if(x>=c+2 && mx<x) last=x;
        g[x]=last;
        if(x<=r && s->B[x]>mx) mx=s->B[x];
      }
      for(int a=l;a<=c;a++) ta[a]=INF;
      int t0=INF;
      for(int t=r;t>=c+1;t--){
        if(s->A[t]<l) t0=t;
        else if(s->A[t]<=c) ta[s->A[t]]=t;
      }
      int cur=r+1; if(t0<cur)cur=t0;
      for(int j=l;j<=c;j++){ X[j]=cur; if(ta[j]<cur)cur=ta[j]; }
      int sa=INF,sb=-INF;
      for(int j=c;j>=l;j--){
        int x=g[X[j]];
        int cand=(x&&sa>=j&&sb<x)?x:0;
        // Lemma 5 check: largest x in c+2..r+1 with (j,x) closed
        if(k<=64){
          int best=0; for(int y=r+1;y>=c+2;y--) if(closed(s,j,y)){best=y;break;}
          if(best!=cand) HIT(F_L5);
        }
        if(cand){CC[N_cand]++; if(cand>s->m[j]) s->m[j]=cand;}
        if(s->A[j]<sa)sa=s->A[j];
        if(s->B[j]>sb)sb=s->B[j];
      }
    }
    size*=2;lev++;
  }
}

static void step3(St*s){
  // uses s->m, all levels. Independent re-derivation of g, X, ta at each segment.
  int k=s->k; int size=1,lev=0;
  static int g[MAXK+3],ta[MAXK+3],X[MAXK+3],mark[MAXK+3],nx[MAXK+3];
  while(size<k){
    for(int t=1;t<=k;t++){s->lam[lev][t]=NA;s->dlt[lev][t]=NA;}
    for(int l=1;l+size<=k;l+=2*size){
      int c=l+size-1,r=l+2*size-1; if(r>k)r=k;
      int mx=-INF,last=0;
      for(int x=c+1;x<=r+1;x++){ if(x>=c+2&&mx<x)last=x; g[x]=last; if(x<=r&&s->B[x]>mx)mx=s->B[x]; }
      for(int a=l;a<=c;a++) ta[a]=INF;
      int t0=INF;
      for(int t=r;t>=c+1;t--){ if(s->A[t]<l)t0=t; else if(s->A[t]<=c)ta[s->A[t]]=t; }
      int cur=r+1; if(t0<cur)cur=t0;
      for(int j=l;j<=c;j++){ X[j]=cur; if(ta[j]<cur)cur=ta[j]; }
      // chain
      int lastm=NONE,firstm=NONE,count=0,pm=0,eq=0;
      for(int a=l;a<=c;a++){ if(s->m[a]>c+1){ if(!firstm)firstm=a; if(pm&&s->m[pm]==s->m[a])eq=1; if(pm&&s->m[pm]<s->m[a])HIT(F_L2b); pm=a; lastm=a;count++; } s->lam[lev][a]=lastm; }
      if(count>=3)CC[N_chain3]++; if(eq)CC[N_eqm]++;
      int after=NONE; for(int a=c;a>=l;a--){ nx[a]=after; if(s->m[a]>c+1)after=a; }
      for(int t=c+1;t<=r+1;t++) mark[t]=NA;
      // rings
      int prevlo=-1,prevhi=-1; // for route disjointness we collect intervals: since sends go in increasing a, m decreases
      int nrings=0;
      for(int a=l;a<=c;a++){
        int j0=s->lam[lev][a],j1=nx[a];
        if(!j0||!j1||ta[a]==INF) continue;
        if(s->m[j0]>r||s->m[j0]<=s->m[j1]) continue;
        if(ta[a]!=X[j1]) continue;
        int pos=g[ta[a]];
        if(pos!=s->m[j1]) HIT(F_ring_pos);
        if(ta[a]<s->m[j1]||ta[a]>=s->m[j0]) HIT(F_route);
        if(pos>=c+1&&pos<=r+1&&mark[pos]!=NA) HIT(F_marktwice);
        mark[pos]=j0; nrings++; CC[N_ring]++;
        if(ta[a]!=pos)CC[N_routecross]++;
        // disjoint routes: this interval [pos,ta]; a increases, so m goes down: interval must lie below previous
        if(prevlo>=0 && ta[a]>=prevlo) HIT(F_route);
        prevlo=pos;prevhi=ta[a];
      }
      (void)prevhi;
      // count rings by definition, and check Lemma 6
      int exp=0; int pj=0;
      for(int j=l;j<=c;j++) if(s->m[j]>c+1){
        if(pj && s->m[j]<s->m[pj] && s->m[pj]<=r+1){
          int xx=X[j]; int am=(xx<=r)?s->A[xx]:INF;
          if(!(xx>=s->m[j]&&xx<s->m[pj]&&am>=pj&&am<j)) HIT(F_L6);
          if(s->m[pj]<=r) exp++;
        }
        pj=j;
      }
      if(exp!=nrings) HIT(F_ring_count);
      // rest
      int J=NONE; for(int j=l;j<=c;j++) if(s->m[j]>c+1&&s->m[j]>r) J=j;
      int jp=J?nx[J]:firstm;
      if(jp&&s->m[jp]<=r){ if(mark[s->m[jp]]!=NA)HIT(F_marktwice); mark[s->m[jp]]=J; CC[N_past]++; }
      // delta
      int cu=lastm;
      for(int t=c+1;t<=r;t++){
        if(mark[t]!=NA)cu=mark[t];
        s->dlt[lev][t]=cu;
        int tr=NONE; for(int j=l;j<=c;j++) if(s->m[j]>c+1&&s->m[j]>t) tr=j;
        if(tr!=cu) HIT(F_delta);
      }
    }
    size*=2;lev++;
  }
}

static int deepest_pt(const St*s,int t){
  int lev=0,size=1;
  while(size<s->k){ int d=s->dlt[lev][t]; if(d>0) return d; lev++; size*=2; }
  return 0;
}
static int deepest_y(const St*s,int a,int b){
  if(a==0) return 0;
  if(a==b) return a;
  int x=(a-1)^(b-1),lev=0; while((x>>(lev+1)))lev++;
  int la=s->lam[lev][a],de=s->dlt[lev][b];
  if(la==NA||de==NA){HIT(F_lam);return -1;}
  if(la>0&&de>0) return la<de?la:de;
  for(lev=lev+1;(1<<lev)<s->k;lev++){ int d=s->dlt[lev][b]; if(d>0) return d; }
  return 0;
}

// ---------- graph driver
static int n,kk;
static u32 out_[MAXN],in_[MAXN],EE;
static void dumpg(void){ printf("n=%d k=%d E=%x arcs:",n,kk,EE); for(int u=0;u<n;u++)for(int v=0;v<n;v++)if(out_[u]>>v&1)printf(" %d>%d",u,v); printf("\n"); }
static inline u32 reachm(u32 src,u32 allowed,const u32*o){
  u32 seen=src&allowed,fr=seen;
  while(fr){ int u=__builtin_ctz(fr); fr&=fr-1; u32 nw=o[u]&allowed&~seen; seen|=nw; fr|=nw; }
  return seen;
}
static St S1,S2;
static void lemma4(u32 Q,u32 E,const u32*o,int k,u32 *domw){
  // Q=all here; path 0..k-1; own classes. domw[w] = set dominated by w in Q (reach-based)
  u32 Om=Q&~((1u<<k)-1);
  if(!Om) return;
  // heads: y in Om with arc from path. key = (k-i (i 1-based max), id)
  int key[MAXN]; for(int y=0;y<n;y++)key[y]=INF;
  for(int i=k;i>=1;i--){ u32 hs=o[i-1]&Om; while(hs){int h=__builtin_ctz(hs);hs&=hs-1; if(key[h]==INF)key[h]=(k-i)*100+h;} }
  // e(y)
  int e[MAXN]; for(int y=0;y<n;y++)e[y]=INF;
  // order heads by key
  int done=0; u32 left=Om; u32 classes[MAXN]; int heads[MAXN]; int nc=0;
  while(left&&done<n){
    int bh=-1,bk=INF; for(int y=0;y<n;y++) if((left>>y&1)&&key[y]<bk){bk=key[y];bh=y;}
    if(bh<0){HIT(F_L4part);return;}
    u32 Ky=reachm(1u<<bh,left,o);
    classes[nc]=Ky;heads[nc]=bh;nc++;
    for(u32 w=Ky;w;w&=w-1)e[__builtin_ctz(w)]=bk;
    left&=~Ky; done++;
  }
  // NOTE: greedy by least key gives e(y)=least key of a head that reaches y in D[O]? a head of greater key reached by lesser falls in lesser class; path from best head stays in unassigned part.
  // verify e by definition
  for(int y=0;y<n;y++) if(Om>>y&1){
    int best=INF; for(int h=0;h<n;h++) if((Om>>h&1)&&key[h]<best){ if(reachm(1u<<h,Om,o)>>y&1) best=key[h]; }
    if(best!=e[y]) HIT(F_L4part);
  }
  u32 inv[MAXN];
  for(int ci=0;ci<nc;ci++){
    u32 K=classes[ci]; int h=heads[ci];
    u32 EK=K&E; // entries
    for(int u=0;u<n;u++) if((Q>>u&1)&&!(K>>u&1)) EK|=o[u]&K;
    if(!(EK>>h&1)) HIT(F_entry);
    if(reachm(1u<<h,K,o)!=K) HIT(F_L4root);
    for(u32 ys=K;ys;ys&=ys-1){
      int y=__builtin_ctz(ys);
      for(int w=0;w<n;w++) if(w!=y&&(Q>>w&1)&&w>=k){ // off R
        int dq=!(domw[w]>>y&1)?0:1;
        if(!(K>>w&1)){ if(dq)HIT(F_L4a); continue; }
        u32 got=reachm(EK&~(1u<<w),K&~(1u<<w),o);
        int dk=!(got>>y&1);
        if(dq!=dk)HIT(F_L4b);
      }
    }
  }
  (void)inv;
}

static void check_graph(void){
  CC[N_inst]++;
  int k=kk; u32 all=(1u<<n)-1; u32 Rm=(1u<<k)-1, Om=all&~Rm;
  u32 Rj[MAXN]; int m[MAXN+2];
  for(int j=1;j<=k;j++){
    u32 av=all&~(1u<<(j-1));
    Rj[j]=reachm(EE&av,av,out_);
    m[j]=k+1; for(int t=j+1;t<=k;t++) if(Rj[j]>>(t-1)&1){m[j]=t;break;}
  }
  // feeds
  u32 F[MAXN+1]; int a[MAXN],b[MAXN];
  for(int y=0;y<n;y++){a[y]=INF;b[y]=-INF;}
  for(int i=0;i<=k;i++){
    u32 src=(i==0?EE:out_[i-1])&Om;
    F[i]=reachm(src,Om,out_);
    for(u32 w=F[i];w;w&=w-1){int y=__builtin_ctz(w); if(i<a[y])a[y]=i; if(i>b[y])b[y]=i;}
  }
  // lemma 1
  for(int j=1;j<=k;j++){
    for(int i=1;i<=k;i++) if(i!=j){
      int in=Rj[j]>>(i-1)&1, ex=(i<j||i>=m[j]);
      if(in!=ex)HIT(F_L1a);
    }
    for(u32 w=Om;w;w&=w-1){int y=__builtin_ctz(w);
      int in=Rj[j]>>y&1, ex=(a[y]<j||b[y]>=m[j]);
      if(in!=ex)HIT(F_L1b);
    }
  }
  // strict A,B and one-round A,B
  St*s=&S1,*st=&S2; s->k=k; st->k=k;
  for(int t=1;t<=k;t++){s->A[t]=st->A[t]=INF;s->B[t]=st->B[t]=-INF;}
  int leafok_strict=1;
  for(int t=2;t<=k;t++){
    u32 pt=1u<<(t-1);
    // strict
    for(int i=0;i<=k;i++) if(i!=t&&i!=t-1){
      int jump=(i==0)?((EE&pt)!=0):((out_[i-1]&pt)!=0);
      if(!jump) for(u32 w=F[i];w;w&=w-1){int u=__builtin_ctz(w); if(out_[u]&pt){jump=1;break;}}
      if(jump){ if(i<st->A[t])st->A[t]=i; if(i>st->B[t])st->B[t]=i; }
    }
    // one round
    if(EE&pt){s->A[t]=0;s->B[t]=0;}
    for(int u=0;u<n;u++) if(out_[u]&pt){
      if(u<k){int i=u+1; if(i!=t&&i!=t-1){ if(i<s->A[t])s->A[t]=i; if(i>s->B[t])s->B[t]=i; }}
      else { if(a[u]<s->A[t])s->A[t]=a[u]; if(b[u]>s->B[t])s->B[t]=b[u]; }
    }
    // leaf: if A(t)=a>=1 then p_t has an in-neighbour in A_a (one-round)
    if(s->A[t]>=1&&s->A[t]<INF){ int aa=s->A[t]; int ok=0;
      if(aa==t) ok=1; // own
      for(int u=0;u<n;u++) if(out_[u]&pt){ if(u<k? (u+1==aa):(a[u]==aa)) ok=1; }
      if(!ok)HIT(F_leaf);
    }
    if(st->A[t]>=1&&st->A[t]<INF){ int aa=st->A[t]; int ok=0;
      for(int u=0;u<n;u++) if(out_[u]&pt){ if(u<k? (u+1==aa):(a[u]==aa)) ok=1; }
      if(!ok){ leafok_strict=0; if(aa<t-1) HIT(F_leaf); }
    }
    // the difference between strict and one-round may only be at values >= t-1 for A and <= t for B
    if(s->A[t]!=st->A[t] && !(s->A[t]>=t-1&&st->A[t]>=t-1)) HIT(F_strictdiff);
    if(s->B[t]!=st->B[t] && !(s->B[t]<=t&&st->B[t]<=t)) HIT(F_strictdiff);
  }
  (void)leafok_strict;
  // A_a, B_b connected via feed paths
  for(int aa=1;aa<=k;aa++){
    u32 part=0; for(u32 w=Om;w;w&=w-1){int y=__builtin_ctz(w); if(a[y]==aa)part|=1u<<y;}
    if(part){ u32 got=reachm(1u<<(aa-1),part|1u<<(aa-1),out_); if(got!=(part|1u<<(aa-1))) HIT(F_Aconn); }
    part=0; for(u32 w=Om;w;w&=w-1){int y=__builtin_ctz(w); if(b[y]==aa)part|=1u<<y;}
    if(part){ u32 got=reachm(1u<<(aa-1),part|1u<<(aa-1),out_); if(got!=(part|1u<<(aa-1))) HIT(F_Bconn); }
  }
  // lemma 2 with both arrays, then section 5 with one-round and strict arrays
  for(int j=1;j<=k;j++){
    int best=j+1; for(int x=k+1;x>j+1;x--) if(closed(s,j,x)){best=x;break;}
    if(best!=m[j])HIT(F_L2a_one);
    best=j+1; for(int x=k+1;x>j+1;x--) if(closed(st,j,x)){best=x;break;}
    if(best!=m[j])HIT(F_L2a_strict);
    if(m[j]>j+1)CC[N_long]++;
    for(int jj=j+1;jj<m[j];jj++) if(m[jj]>m[j])HIT(F_L2b);
  }
  for(int pass=0;pass<2;pass++){
    St*w=pass?st:s;
    step2(w);
    for(int j=1;j<=k;j++) if(w->m[j]!=m[j])HIT(F_m);
    step3(w);
  }
  // truth on all dominators: domw[w]=set of vertices unreachable without w
  u32 domw[MAXN];
  for(int w=0;w<n;w++){ u32 av=all&~(1u<<w); domw[w]=all&~reachm(EE&av,av,out_)&~(1u<<w); }
  // lemma 3 and final answers
  for(int t=1;t<=k;t++){
    int tr=0; for(int j=1;j<t;j++) if(domw[j-1]>>(t-1)&1) tr=j;
    for(int w=k;w<n;w++) if(domw[w]>>(t-1)&1)HIT(F_L3a);
    for(int pass=0;pass<2;pass++) if(deepest_pt(pass?st:s,t)!=tr)HIT(F_pt);
  }
  for(u32 ws=Om;ws;ws&=ws-1){int y=__builtin_ctz(ws);
    CC[N_y]++; if(a[y]==0)CC[N_a0]++;
    int tr=0; for(int j=1;j<=k;j++) if(domw[j-1]>>y&1) tr=j;
    for(int pass=0;pass<2;pass++) if(deepest_y(pass?st:s,a[y],b[y])!=tr)HIT(F_L7);
    // order: every on-R dominator of y dominates every off-R dominator of y
    for(int j=1;j<=k;j++) if(domw[j-1]>>y&1) for(int w=k;w<n;w++) if(domw[w]>>y&1){ if(!(domw[j-1]>>w&1))HIT(F_L3b); }
  }
  lemma4(all,EE,out_,k,domw);
}

static u64 rs;
static inline u64 rnd(void){ rs^=rs<<13; rs^=rs>>7; rs^=rs<<17; return rs; }
static void report(void){
  for(int i=0;i<NUMC;i++) if(i<F_L1a||CC[i]) printf("%s=%llu ",NAME[i],CC[i]);
  int f=0; for(int i=F_L1a;i<NUMC;i++) f+=CC[i]>0;
  printf("\nFAILKINDS=%d\n",f); fflush(stdout);
}

static int setup(u64 mask){ // free arcs from mask, path arcs forced
  memset(out_,0,sizeof(out_));
  int bit=0;
  for(int u=0;u<n;u++)for(int v=0;v<n;v++) if(u!=v){
    if(u<kk-1&&v==u+1&&v<kk){out_[u]|=1u<<v;continue;}
    if(mask>>bit&1)out_[u]|=1u<<v;
    bit++;
  }
  u32 all=(1u<<n)-1;
  return reachm(1,all,out_)==all;
}

static void graph(int argc,char**argv){
  n=atoi(argv[2]);kk=atoi(argv[3]); const char*emode=argc>4?argv[4]:"Eall";
  int fr=n*(n-1)-(kk-1);
  u64 tot=1ULL<<fr; dump=dumpg;
  for(u64 mask=0;mask<tot;mask++){
    if(!setup(mask))continue;
    if(!strcmp(emode,"E0")){EE=1;check_graph();}
    else if(!strcmp(emode,"E01")){ for(int e=0;e<n;e++){EE=1u|(1u<<e);check_graph();} }
    else { for(u32 e=0;e<(1u<<(n-1));e++){EE=1u|(e<<1);check_graph();} }
  }
  printf("graph n=%d k=%d E=%s masks=%llu\n",n,kk,emode,tot); report();
}
static void graphrand(int argc,char**argv){
  n=atoi(argv[2]);kk=atoi(argv[3]); double secs=atof(argv[4]); rs=strtoull(argv[5],0,10)*2654435761ULL+88172645463325252ULL; dump=dumpg;
  time_t t0=time(0); u64 it=0;
  while(1){
    if((it&1023)==0&&difftime(time(0),t0)>secs)break;
    it++;
    int dens=1+rnd()%6; u64 mask=0; int fr=n*(n-1)-(kk-1);
    for(int b=0;b<fr;b++) if(rnd()%10<(u64)dens) mask|=1ULL<<b;
    if(!setup(mask))continue;
    u32 e=0; int ed=rnd()%4; for(int v=1;v<n;v++) if(rnd()%6<(u64)ed) e|=1u<<v;
    EE=1u|e; check_graph();
  }
  printf("graphrand n=%d k=%d iters=%llu\n",n,kk,it); report();
}

// ---------- abstract arrays
static St Sa; static int mt[MAXK+3];
static void dumpa(void){ printf("k=%d A,B:",Sa.k); for(int t=2;t<=Sa.k;t++)printf(" %d:(%d,%d)",t,Sa.A[t]>=INF?-9:Sa.A[t],Sa.B[t]<=-INF?-9:Sa.B[t]); printf("\n"); }
static void abs_check(St*s,int ally){
  CC[N_inst]++;
  int k=s->k;
  // truth by reachability on the graph with arcs p_A->p_t, p_B->p_t, path
  static int seen[MAXK+3],stack[MAXK+3];
  static int hd[MAXK+3],nx[4*MAXK],to[4*MAXK]; int ne=0;
  for(int i=0;i<=k;i++)hd[i]=-1;
  #define ADD(u,v) do{to[ne]=v;nx[ne]=hd[u];hd[u]=ne++;}while(0)
  ADD(0,1); for(int t=1;t<k;t++)ADD(t,t+1);
  for(int t=2;t<=k;t++){ if(s->A[t]<INF)ADD(s->A[t],t); if(s->B[t]>-INF&&s->B[t]!=s->A[t])ADD(s->B[t],t); }
  static unsigned char Rj[MAXK+3][MAXK+3]; int bigk=k>256;
  for(int j=1;j<=k;j++){
    memset(seen,0,sizeof(int)*(k+2)); int sp=0; stack[sp++]=0; seen[0]=1;
    while(sp){int u=stack[--sp]; for(int e=hd[u];e>=0;e=nx[e]){int v=to[e]; if(v!=j&&!seen[v]){seen[v]=1;stack[sp++]=v;}}}
    mt[j]=k+1; for(int t=j+1;t<=k;t++) if(seen[t]){mt[j]=t;break;}
    if(!bigk) for(int t=0;t<=k;t++) Rj[j][t]=seen[t];
  }
  step2(s);
  for(int j=1;j<=k;j++){ if(s->m[j]!=mt[j])HIT(F_m); if(mt[j]>j+1)CC[N_long]++; for(int jj=j+1;jj<mt[j];jj++) if(mt[jj]>mt[j]){HIT(F_L2b);break;} }
  step3(s);
  for(int t=1;t<=k;t++){ int tr=0; for(int j=t-1;j>=1;j--) if(mt[j]>t){tr=j;break;} if(deepest_pt(s,t)!=tr)HIT(F_pt); }
  // all pairs (a,b), or a random sample if large
  if(!bigk){
    int samples=ally?-1:40;
    for(int it=0;(ally&&it==0)||(!ally&&it<samples);it++){
      if(ally){
        for(int a=0;a<=k;a++)for(int b=a>1?a:1;b<=k;b++){
          CC[N_y]++;
          int tr=0; for(int j=k;j>=1;j--){ int in=(a!=j&&Rj[j][a])||(b!=j&&Rj[j][b]); if(!in){tr=j;break;} }
          if(deepest_y(s,a,b)!=tr)HIT(F_L7);
        }
      } else {
        int a=rnd()%(k+1),b=1+rnd()%k; if(a>b){int t=a;a=b;b=t;} if(a==0&&b==0)b=1;
        CC[N_y]++;
        int tr=0; for(int j=k;j>=1;j--){ int in=(a!=j&&Rj[j][a])||(b!=j&&Rj[j][b]); if(!in){tr=j;break;} }
        if(deepest_y(s,a,b)!=tr)HIT(F_L7);
      }
    }
  }
}
static void absall(int argc,char**argv){
  int k=atoi(argv[2]); St*s=&Sa; s->k=k; dump=dumpa;
  // options per t
  static int oa[MAXK][300],ob[MAXK][300],no[MAXK];
  for(int t=2;t<=k;t++){
    int c=0; oa[t][c]=INF;ob[t][c]=-INF;c++;
    for(int a=0;a<=k;a++) if(a!=t&&a!=t-1) for(int b=a;b<=k;b++) if(b!=t&&b!=t-1){oa[t][c]=a;ob[t][c]=b;c++;}
    no[t]=c;
  }
  int idx[MAXK]; memset(idx,0,sizeof(idx));
  s->A[1]=INF;s->B[1]=-INF;
  while(1){
    for(int t=2;t<=k;t++){s->A[t]=oa[t][idx[t]];s->B[t]=ob[t][idx[t]];}
    abs_check(s,1);
    int t=2; while(t<=k){ idx[t]++; if(idx[t]<no[t])break; idx[t]=0; t++; }
    if(t>k)break;
  }
  printf("abs k=%d\n",k); report();
}
// structured generator: laminar intervals biased to segment boundaries
static void gen(St*s,int k){
  s->k=k; s->A[1]=INF;s->B[1]=-INF;
  int style=rnd()%6;
  static int lo[MAXK+3],hi[MAXK+3]; // allowed A>=lo(t), B<hi(t) for t
  for(int t=1;t<=k+1;t++){lo[t]=0;hi[t]=k+1;}
  // pick centre at a dyadic boundary
  int nint=rnd()%(k/2+2);
  // nested chain around centre c
  int lev=0; while((1<<(lev+1))<k)lev++; lev=rnd()%(lev+1);
  int size=1<<lev; int segs=(k-1)/(2*size)+1; int l=1+2*size*(rnd()%segs); int c=l+size-1; if(c>=k)c=(k+1)/2;
  int j=(rnd()%3==0)?l:1+rnd()%c, x=(rnd()%2)?((c+size+1<=k+1)?c+size+1:k+1):(c+2+rnd()%(k-c+1));
  if(x>k+1)x=k+1;
  int jl[MAXK],xl[MAXK],ni=0;
  while(j<=c&&x>c+1&&ni<nint){ jl[ni]=j;xl[ni]=x;ni++; int dj=1+rnd()%((style==0)?2:(style==1?1:4)); j+=dj; int dx=(rnd()%3==0)?0:(1+rnd()%((style==2)?1:3)); x-=dx; }
  for(int i=0;i<ni;i++) for(int t=jl[i]+1;t<xl[i];t++){ if(jl[i]>lo[t])lo[t]=jl[i]; if(xl[i]<hi[t])hi[t]=xl[i]; }
  int pfill=style==3?2:(style==4?6:9);
  for(int t=2;t<=k;t++){
    s->A[t]=INF;s->B[t]=-INF;
    // A in [lo,hi) minus t,t-1 ; with bias to keep things closed
    if((int)(rnd()%10)<pfill){
      int tries=4; while(tries--){ int v=lo[t]+rnd()%(hi[t]-lo[t]>0?hi[t]-lo[t]:1); if(v!=t&&v!=t-1&&v<=k){ if(v<s->A[t])s->A[t]=v; if(v>s->B[t])s->B[t]=v; } }
    }
    // violation at ends of nested intervals: back jump to the just-past end, or an entry
    if(rnd()%40==0){ s->A[t]=0; if(s->B[t]<0)s->B[t]=0; }
  }
  // explicit rings: at x, jump from between j_i and j_{i+1}
  for(int i=0;i+1<ni;i++) if(xl[i+1]<xl[i]&&xl[i+1]<=k&&rnd()%4){
    int t=xl[i+1]+rnd()%(xl[i]-xl[i+1]); if(t>k)continue;
    int v=jl[i]+rnd()%(jl[i+1]-jl[i]); if(v==t||v==t-1)continue;
    s->A[t]=v; if(s->B[t]<v)s->B[t]=v;
  }
}
static void absrand(int argc,char**argv){
  int kmax=atoi(argv[2]); double secs=atof(argv[3]); rs=strtoull(argv[4],0,10)*2654435761ULL+88172645463325252ULL; dump=dumpa;
  time_t t0=time(0); u64 it=0;
  while(1){
    if((it&255)==0&&difftime(time(0),t0)>secs)break;
    it++;
    int r=rnd()%10; int k;
    if(r<3){ int p=3+rnd()%6; k=(1<<p)+(int)(rnd()%3)-1; } else k=4+rnd()%(kmax-3);
    if(k>kmax)k=kmax;
    gen(&Sa,k);
    abs_check(&Sa,0);
  }
  printf("absrand kmax=%d iters=%llu\n",kmax,it); report();
}

int main(int argc,char**argv){
  (void)C;
  if(!strcmp(argv[1],"graph"))graph(argc,argv);
  else if(!strcmp(argv[1],"graphrand"))graphrand(argc,argv);
  else if(!strcmp(argv[1],"abs"))absall(argc,argv);
  else if(!strcmp(argv[1],"absrand"))absrand(argc,argv);
  return 0;
}
