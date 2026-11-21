"""Brute-force checks of the averaging formula and of Lemma 1.

1. On tiny instances (m = 3 names, N <= 6 positions), the probability that f(x_t) = l_t for all t, averaged
   over uniform arrangements and injective namings, equals the falling-factorial formula of the proof.
2. For random monomials, G(t, p) is a polynomial of degree <= s in t whose t^d coefficient has p-degree <= d.
3. G(1, p) equals the formula for the actual instance (special row with pM ones, F filler rows).
"""
import itertools, random
from fractions import Fraction as Fr
import sympy as sp
def ff(x,a):
    r=1
    for i in range(a): r*=(x-i)
    return r
def brute(rows, m, xs, labels):
    # rows: list of (k1,k0); N = total; uniform arrangement and injective naming
    slots=[(ri,b) for ri,(k1,k0) in enumerate(rows) for b,c in ((1,k1),(0,k0)) for _ in range(c)]
    N=len(slots); hit=0; tot=0
    for perm in itertools.permutations(range(N)):
        for names in itertools.permutations(range(m), len(rows)):
            tot+=1
            ok=all((names[slots[perm[x]][0]],slots[perm[x]][1])==l for x,l in zip(xs,labels))
            hit+=ok
    return Fr(hit,tot)
def formula(rows, m, N, labels):
    nm=sorted(set(l[0] for l in labels)); u=len(nm); s=len(labels)
    a=[sum(1 for l in labels if l==(v,1)) for v in nm]; b=[sum(1 for l in labels if l==(v,0)) for v in nm]
    tot=0
    for tup in itertools.permutations(range(len(rows)),u):
        pr=1
        for v,rho in enumerate(tup): pr*=ff(rows[rho][0],a[v])*ff(rows[rho][1],b[v])
        tot+=pr
    return Fr(tot, ff(N,s)*ff(m,u))
random.seed(3)
for trial in range(6):
    rows=random.choice([[(1,1),(2,0),(0,1)],[(1,2),(2,0)],[(0,2),(1,1),(1,0)],[(3,1)]])
    m=3; N=sum(a+b for a,b in rows)
    s=random.randint(1,3); xs=random.sample(range(N),s)
    labels=[(random.randrange(m),random.randrange(2)) for _ in range(s)]
    assert brute(rows,m,xs,labels)==formula(rows,m,N,labels),(rows,labels)
print("formula ok")
# Lemma 1 (iii): symbolic G for one monomial, rows: R-1 others, special (p t M ones), F+1-t fillers bias c
t,p=sp.symbols('t p')
def Gsym(labels, others, M, F, c, m):
    N=None
    nm=sorted(set(l[0] for l in labels)); u=len(nm); s=len(labels)
    a=[sum(1 for l in labels if l==(v,1)) for v in nm]; b=[sum(1 for l in labels if l==(v,0)) for v in nm]
    tot=0
    # each slot v is: 'S' special, 'F' filler, or an index of others
    kinds=['S','F']+list(range(len(others)))
    for ass in itertools.product(kinds, repeat=u):
        if ass.count('S')>1: continue
        oth=[x for x in ass if x not in ('S','F')]
        if len(set(oth))<len(oth): continue
        j=ass.count('F'); pr=ff(F+1-t,j)
        for v,kd in enumerate(ass):
            if kd=='S': pr*=ff(p*t*M,a[v])*ff((1-p)*t*M,b[v])
            elif kd=='F': pr*=ff(sp.Rational(c)*M,a[v])*ff((1-sp.Rational(c))*M,b[v])
            else: pr*=ff(others[kd][0],a[v])*ff(others[kd][1],b[v])
        tot+=pr
    return sp.expand(tot)
for trial in range(20):
    s=random.randint(1,5); labels=[(random.randrange(4),random.randrange(2)) for _ in range(s)]
    G=Gsym(labels, [(1,3),(2,2)], 4, 3, Fr(1,2), 6)
    P=sp.Poly(G,t,p)
    for (dt,dp),co in P.terms(): assert dp<=dt and dt<=s, (labels,dt,dp)
print("Lemma 1 (iii) degree structure ok")
for trial in range(20):
    s = random.randint(1, 4); labels = [(random.randrange(6), random.randrange(2)) for _ in range(s)]
    others, M, F, c, m = [(1, 3), (2, 2)], 4, 3, Fr(1, 2), 6
    G = Gsym(labels, others, M, F, c, m)
    for k in range(M + 1):
        rows = others + [(k, M - k)] + [(int(c * M), int((1 - c) * M))] * F
        N = sum(a + b for a, b in rows)
        lhs = G.subs({t: 1, p: sp.Rational(k, M)})
        assert lhs / (ff(N, s) * ff(m, len(set(l[0] for l in labels)))) == formula(rows, m, N, labels)
print("G(1, p) matches the actual instance")
