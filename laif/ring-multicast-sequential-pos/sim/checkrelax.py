"""Checks every relaxed inequality of the proof on simulated instances: orient, play orders A and B exactly
(worst tie choices), read p (first right-goer of 0..o-1 in A) and q (first left-goer of o-1..0 in B), normalize
OPT = 1, map the instance to the variables of the relaxation of its case and assert A x <= h for every row."""
import random, sys
from fractions import Fraction as F
from ring import play, perms_AB, mirror
from proof_certs import rows_dm, rows_window, low1, low2


def rows_low(case):
    return low1 if case == "q>=p" else low2


def check(a):
    n = len(a) - 1; o = max(range(n + 1), key=lambda k: a[k])
    b, o = (a, o) if sum(a[:o]) >= sum(a[o + 1:]) else (mirror(a), n - o)   # o moves with the mirror
    A, B, o = perms_AB(b, o)
    _, dA = play(b, A); _, dB = play(b, B)
    T = sum(b); OPT = T - b[o]
    if OPT == 0: return None
    x = [v / OPT for v in b]; s = x[o]
    p = next((j for j in range(o) if dA[j] == "R"), None)
    q = next((j for j in range(o - 1, -1, -1) if dB[j] == "L"), -1)
    if p is None: return "no p"
    z = min(s - x[p], s - x[q + 1])
    d = p - q
    if d <= 0:
        v = [x[p], sum(x[:p]), x[q + 1], s, z]; R = rows_low("q>=p")
    elif d == 1:
        if p == 0: assert z <= 0; return "p=0"
        v = [x[p], sum(x[:p]), s, z]; R = rows_low("q+1=p")
    elif d in (2, 3):
        m = 0 if d == 2 else 1
        U = sum(x[:max(q - m + 1, 0)]); C = [x[q - t] if q - t >= 0 else F(0) for t in range(m)]
        Bv = [x[q + i] for i in range(1, d + 1)]
        v = [U] + C + Bv + [s, z]; nv, R = rows_dm(d, m)
        if q == -1: R = [r for r in R if r[0] != "B_q"]
    else:
        e = [x[p - t] for t in range(4)]; V = sum(x[:p - 3])
        v = e + [V, s, z]; nv, R = rows_window(4)
    for nm, r, hh in R:
        lhs = sum(F(c) * vv for c, vv in zip(r, v))
        assert lhs <= F(hh), (nm, b, p, q, d, lhs, hh)
    assert z <= F(1, 3), (b, z)
    return d


if __name__ == "__main__":
  rng = random.Random(int(sys.argv[2]) if len(sys.argv) > 2 else 3); seen = {}
  for it in range(int(sys.argv[1])):
    n = rng.randint(2, 30); kind = rng.random()
    if kind < 0.3: a = [F(rng.randint(0, 20)) for _ in range(n + 1)]
    elif kind < 0.6: a = [F(rng.choice([0, 0, rng.randint(1, 30)])) for _ in range(n + 1)]
    else:
        h = rng.randint(2, 7); a = [F(rng.randint(0, 40)) for _ in range(h)] + [F(0)] * rng.randint(0, 20)
        a += [F(rng.randint(20, 60))] + [F(rng.randint(0, 3)) for _ in range(rng.randint(0, 3))]
    if sum(a) == 0: continue
    r = check(a); key = r if not isinstance(r, int) else ("d<=0" if r <= 0 else f"d={r}" if r <= 3 else "d>=4")
    seen[key] = seen.get(key, 0) + 1
  print("all relaxed rows hold; cases seen:", seen)
