// Corollary 1 and 2 of notes/DOMINATORS.md, brute force on all digraphs with n vertices. No repo code.
// cor N [secs seed]     : all digraphs with N<=5. If secs given: random digraphs on N vertices for secs.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
typedef unsigned int u32; typedef unsigned long long u64;
static int n; static u32 o[32],in[32];
static u64 rs=88172645463325252ULL; static inline u64 rnd(void){rs^=rs<<13;rs^=rs>>7;rs^=rs<<17;return rs;}
static inline u32 reachm(u32 src,u32 allowed,const u32*g){ u32 seen=src&allowed,fr=seen; while(fr){int u=__builtin_ctz(fr);fr&=fr-1;u32 nw=g[u]&allowed&~seen;seen|=nw;fr|=nw;} return seen; }
static int ncomps(u32 V,const u32*g,const u32*r){ int c=0; u32 left=V; while(left){int u=__builtin_ctz(left); u32 f=reachm(1u<<u,V,g),b=reachm(1u<<u,V,r); left&=~(f&b); c++;} return c; }
static u64 cBetween,fBetween,cSAP,cSB,cS,cDigraphs,cCor1,cCor1yes,cOutN; static u64 fSAP,fSB,fS,fCor1,fOutN; static int pr;
static void dumpg(const char*w){ if(pr++>5)return; printf("%s n=%d arcs:",w,n); for(int u=0;u<n;u++)for(int v=0;v<n;v++)if(o[u]>>v&1)printf(" %d>%d",u,v); printf("\n"); }
// idom by removal on graph g with N vertices restricted to V from s. out idom[y], or -1
static void idoms(int N,u32 V,int s,const u32*g,int*idom,u32*domby){
  u32 all=reachm(1u<<s,V,g);
  u32 domset[32]; // domset[y]= dominators of y (excluding y)
  for(int y=0;y<N;y++){domset[y]=0;idom[y]=-1;}
  for(u32 ws=all;ws;ws&=ws-1){int w=__builtin_ctz(ws);
    u32 got=(w==s)?0:reachm(1u<<s,V&~(1u<<w),g);
    u32 lost=all&~got&~(1u<<w);
    for(u32 ys=lost;ys;ys&=ys-1){domset[__builtin_ctz(ys)]|=1u<<w;}
  }
  for(u32 ys=all;ys;ys&=ys-1){int y=__builtin_ctz(ys); if(y==s)continue;
    int best=-1,bc=-1; for(u32 ds=domset[y];ds;ds&=ds-1){int d=__builtin_ctz(ds);int c=__builtin_popcount(domset[d]); if(c>bc){bc=c;best=d;}}
    idom[y]=best;
  }
  if(domby)for(int y=0;y<N;y++)domby[y]=domset[y];
}
static void cor2(void){
  u32 all=(1u<<n)-1; for(int v=0;v<n;v++)in[v]=0; for(int u=0;u<n;u++)for(u32 w=o[u];w;w&=w-1)in[__builtin_ctz(w)]|=1u<<u;
  int c0=ncomps(all,o,in);
  // arcs between two components are no strong bridges, by definition on H
  for(int u=0;u<n;u++) for(u32 w=o[u];w;w&=w-1){ int v=__builtin_ctz(w);
    u32 cu=reachm(1u<<u,all,o)&reachm(1u<<u,all,in); if(cu>>v&1) continue;
    u32 og[32],ig[32]; memcpy(og,o,sizeof(u32)*n);memcpy(ig,in,sizeof(u32)*n); og[u]&=~(1u<<v); ig[v]&=~(1u<<u);
    cBetween++; if(ncomps(all,og,ig)>c0){fBetween++;dumpg("between");}
  }
  u32 left=all;
  while(left){
    int s=__builtin_ctz(left); u32 C=reachm(1u<<s,all,o)&reachm(1u<<s,all,in); left&=~C;
    int idF[32],idR[32]; u32 oC[32],iC[32]; for(int u=0;u<n;u++){oC[u]=(C>>u&1)?o[u]&C:0;iC[u]=(C>>u&1)?in[u]&C:0;}
    idoms(n,C,s,oC,idF,0); idoms(n,C,s,iC,idR,0);
    for(u32 vs=C;vs;vs&=vs-1){int v=__builtin_ctz(vs);
      // definition on the whole digraph H
      u32 V=all&~(1u<<v); u32 og[32],ig[32]; for(int u=0;u<n;u++){og[u]=o[u];ig[u]=in[u];}
      int def=ncomps(V,og,ig)>c0;
      int claim;
      if(v==s){ u32 D=C&~(1u<<s); claim=D?(ncomps(D,oC,iC)>1):0; }
      else { claim=0; for(u32 w=oC[v];w;w&=w-1) if(idF[__builtin_ctz(w)]==v)claim=1; for(u32 w=iC[v];w;w&=w-1) if(idR[__builtin_ctz(w)]==v)claim=1;
        // also: v dominates some y iff has out-neighbour with idom v
        int dom=0; { u32 got=reachm(1u<<s,C&~(1u<<v),oC); u32 rc=C&~(1u<<v); if(rc&~got)dom=1; got=reachm(1u<<s,C&~(1u<<v),iC); if(rc&~got)dom=1; }
        cOutN++; if(dom!=claim){fOutN++;dumpg("outN");}
      }
      cSAP++; if(def!=claim){fSAP++;dumpg("SAP");}
    }
    // strong bridges inside C, on the subdivided digraph
    int nb=__builtin_popcount(C); if(nb<2)continue;
    { int cnt=0; for(u32 us=C;us;us&=us-1) cnt+=__builtin_popcount(oC[__builtin_ctz(us)]); if(n+cnt>=32) continue; }
    int id[32],arcsU[32],arcsV[32],na=0; for(int u=0;u<n;u++)id[u]=u;
    u32 sg[32],sr[32]; memset(sg,0,sizeof(sg));memset(sr,0,sizeof(sr));
    for(u32 us=C;us;us&=us-1){int u=__builtin_ctz(us); for(u32 w=oC[u];w;w&=w-1){int v=__builtin_ctz(w); int x=n+na; arcsU[na]=u;arcsV[na]=v;na++; sg[u]|=1u<<x; sg[x]|=1u<<v; sr[v]|=1u<<x; sr[x]|=1u<<u;}}
    u32 VV=C; for(int i=0;i<na;i++)VV|=1u<<(n+i);
    int idSF[32],idSR[32]; idoms(n+na,VV,s,sg,idSF,0); idoms(n+na,VV,s,sr,idSR,0);
    for(int i=0;i<na;i++){int u=arcsU[i],v=arcsV[i],x=n+i;
      u32 og[32],ig[32]; memcpy(og,o,sizeof(u32)*n);memcpy(ig,in,sizeof(u32)*n); og[u]&=~(1u<<v); ig[v]&=~(1u<<u);
      int def=ncomps(all,og,ig)>c0;
      int claim=(idSF[v]==x)||(idSR[u]==x);
      cSB++; if(def!=claim){fSB++;dumpg("SB");}
    }
    (void)id;
  }
}
// Corollary 1: chain of passes with random paths. Lemma 1 by definition of m, a, b.
static void chain(u32 Q,u32 E,int z,int t,u32*claim,int depth){
  // random simple path from z in D[Q]
  int R[32],k=0; u32 on=0; int cur=z; R[k++]=z; on|=1u<<z;
  while(1){ u32 opts=o[cur]&Q&~on; if(!opts||rnd()%5==0)break; int c=__builtin_popcount(opts); int pick=rnd()%c; while(pick--)opts&=opts-1; cur=__builtin_ctz(opts); R[k++]=cur; on|=1u<<cur; }
  u32 Om=Q&~on;
  // positions
  int pos[32]; for(int i=0;i<32;i++)pos[i]=0; for(int i=0;i<k;i++)pos[R[i]]=i+1;
  int m[33];
  for(int j=1;j<=k;j++){ u32 av=Q&~(1u<<R[j-1]); u32 got=reachm(E&av,av,o); m[j]=k+1; for(int i=j+1;i<=k;i++) if(got>>R[i-1]&1){m[j]=i;break;} }
  // a,b for t
  if(on>>t&1){ int tau=pos[t]; for(int j=1;j<tau;j++) if(m[j]>tau) *claim|=1u<<R[j-1]; return; }
  int a=100,b=-1;
  for(int i=0;i<=k;i++){ u32 src=(i==0?E:o[R[i-1]])&Om; if(reachm(src,Om,o)>>t&1){ if(i<a)a=i; if(i>b)b=i; } }
  for(int j=1;j<=k&&j<=a;j++) if(m[j]>b) *claim|=1u<<R[j-1];
  // class of t: heads with keys
  int key[32]; for(int y=0;y<32;y++)key[y]=1000000;
  for(int i=k;i>=1;i--){ for(u32 hs=o[R[i-1]]&Om;hs;hs&=hs-1){int h=__builtin_ctz(hs); if(key[h]==1000000)key[h]=(k-i)*100+h;} }
  u32 left=Om;
  while(left){ int bh=-1,bk=1000000; for(u32 w=left;w;w&=w-1){int y=__builtin_ctz(w); if(key[y]<bk){bk=key[y];bh=y;}}
    u32 K=reachm(1u<<bh,left,o);
    if(K>>t&1){ u32 EK=K&E; for(u32 us=Q&~K;us;us&=us-1){EK|=o[__builtin_ctz(us)]&K;} chain(K,EK,bh,t,claim,depth+1); return; }
    left&=~K; }
}
static void cor1(int rr,int tt){
  u32 all=(1u<<n)-1; u32 Q=reachm(1u<<rr,all,o); if(!(Q>>tt&1)||rr==tt)return;
  u32 def=0; for(u32 ws=Q;ws;ws&=ws-1){int w=__builtin_ctz(ws); if(w==tt)continue; u32 got=(w==rr)?0:reachm(1u<<rr,Q&~(1u<<w),o); if(!(got>>tt&1))def|=1u<<w;}
  u32 claim=0; chain(Q,1u<<rr,rr,tt,&claim,0);
  cCor1++; cCor1yes+=__builtin_popcount(def); if(claim!=def){fCor1++;dumpg("Cor1");}
}
static void report(void){ printf("n=%d digraphs=%llu SAPchecked=%llu fail=%llu outN=%llu fail=%llu bridges=%llu fail=%llu cor1=%llu yes=%llu fail=%llu between=%llu fail=%llu\n",n,cDigraphs,cSAP,fSAP,cOutN,fOutN,cSB,fSB,cCor1,cCor1yes,fCor1,cBetween,fBetween); }
int main(int argc,char**argv){
  n=atoi(argv[1]); int bits=n*(n-1);
  if(argc>2){ double secs=atof(argv[2]); rs=strtoull(argv[3],0,10)*2654435761ULL+rs; time_t t0=time(0); u64 it=0;
    while(1){ if((it++&255)==0&&difftime(time(0),t0)>secs)break;
      memset(o,0,sizeof(o)); int dens=1+rnd()%8; for(int u=0;u<n;u++)for(int v=0;v<n;v++)if(u!=v&&(int)(rnd()%12)<dens)o[u]|=1u<<v;
      cDigraphs++; if(n+__builtin_popcount(0)<=9) cor2(); else cor2();
      for(int q=0;q<6;q++)cor1(rnd()%n,rnd()%n);
    }
  } else {
    u64 tot=1ULL<<bits;
    for(u64 mask=0;mask<tot;mask++){
      memset(o,0,sizeof(o)); int b=0; for(int u=0;u<n;u++)for(int v=0;v<n;v++)if(u!=v){ if(mask>>b&1)o[u]|=1u<<v; b++; }
      cDigraphs++; cor2();
      for(int r=0;r<n;r++)for(int t=0;t<n;t++){ if(n>=5&&(rnd()%4))continue; cor1(r,t); }
    }
  }
  report(); return 0;
}
