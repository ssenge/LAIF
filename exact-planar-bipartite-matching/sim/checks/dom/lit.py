"""Replay of three literal points of notes/DOMINATORS.md. No repo code."""
import itertools, networkx as nx
# 1. Section 4: 'marks itself as an entry if it has an arc from outside its class', read literally, with arcs from unreached vertices.
def inst(b=7):
    arcs={0:set()}; nxt=1
    tri=[]
    for i in range(b):
        w,y,x=nxt,nxt+1,nxt+2; nxt+=3
        arcs[0].add(w); arcs[w]={y}; arcs[x]={y}; tri.append((w,y,x))
    return arcs,tri
arcs,tri=inst()
U=nx.Graph((u,v) for u in arcs for v in arcs[u])
print('planar',nx.check_planarity(U)[0],'n',U.number_of_nodes())
D=nx.DiGraph((u,v) for u in arcs for v in arcs[u])
true={y:d for y,d in nx.immediate_dominators(D,0).items() if y!=0}
print('reached',len(true)+1)
# any path from 0 goes down one branch; other branches are classes {w,y}; x in unreached.
R=[0,tri[0][0],tri[0][1]]
rec={}
# first pass, E={0}: all reached vertices off R get last dominator 0
for v in true:
    rec[v]=0
rec[tri[0][1]]=tri[0][0]
for w,y,x in tri[1:]:
    K={w,y}
    lit={w,y}   # w has an arc from 0 on R, y has an arc from the unreached x, literally outside its class
    G=nx.DiGraph(); G.add_edge('rho',w); G.add_edge('rho',y); G.add_edge(w,y)
    d=nx.immediate_dominators(G,'rho')[y]
    if d!='rho': rec[y]=d
wrong={y:(rec[y],true[y]) for y in true if rec[y]!=true[y]}
print('literal reading wrong at (y:(record,idom))',wrong)
# 2. Diameter of the subdivision: K4 with one arc per edge
K4=nx.complete_graph(4)
S=nx.Graph()
for u,v in K4.edges():
    x=('x',u,v); S.add_edge(u,x); S.add_edge(x,v)
print('K4 D',nx.diameter(K4),'subdivided',nx.diameter(S),'claimed bound',2*nx.diameter(K4)+1,'planar',nx.check_planarity(S)[0])
# larger D: search small planar graphs with all arcs subdivided
import random
rng=random.Random(1); worst={}
for _ in range(20000):
    n=rng.randrange(4,12); G=nx.gnm_random_graph(n,rng.randrange(n-1,3*n-6+1),seed=rng.randrange(10**9))
    if not nx.is_connected(G) or not nx.check_planarity(G)[0]: continue
    S=nx.Graph()
    for u,v in G.edges():
        x=('x',u,v); S.add_edge(u,x); S.add_edge(x,v)
    d=nx.diameter(G); e=nx.diameter(S)-2*d
    worst[d]=max(worst.get(d,-9),e)
print('max subdivided diameter minus 2D by D',worst)
# 3. Section 5: strict A(t) of Section 3 cannot come from neighbours, and p_t may have no neighbour in A_a
n=7; k=6
arcs={0:{1},1:{2,6},2:{3},3:{4},4:{5,6},5:set(),6:{2}}  # p1..p6=0..5, u=6; p2->u, p5->u, u->p3
O={6}
print('t=3: u fed by indices 2 and 5. strict A(3)=B(3)=5, a(u)=2, b(u)=5. In-neighbours of p3: p2 and u. Neighbours of p3:',sorted(set(arcs[2])|{v for v in arcs if 2 in arcs[v]}),'A_5={p5}=vertex 4')
