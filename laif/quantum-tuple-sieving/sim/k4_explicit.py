"""Independent explicit form of the 4-tuple cost (no recursion), checked against k4_chain.time_k.
Per repetition (log2/d): T0 = 2m + p1, T1 = 2m + W(t1, a1 | a1), S = m - ell solutions.
Per solution: max(T0 - S, T1 - S + 2 * inner) / 2 with inner = max(m + p2, max(m + W(t2, a2 | a2), 0) + m + p3) / 2,
valid when completions per prefix are below one (asserted). Total = max(ell + m, ell + S + per solution)."""
import sys
from math import log2, sqrt, acos, degrees
sys.path.insert(0, __file__.rsplit("/", 1)[0])
from k4_chain import p, W, time_k

m = log2(256 / 125) / 6
t = [1 / 4, 1 / sqrt(6), sqrt(3 / 8)]
a = [0.23294119, 0.42108008, 0.42108008]
P = [p(c) for c in a]
Wl = [W(ti, c, c) for ti, c in zip(t, a)]
cover = [W(c, c, ti) - p(c) for ti, c in zip(t, a)]          # probability a solution is covered at level i
ell = -sum(cover)
S = m - ell
T0, T1 = 2 * m + P[0], 2 * m + Wl[0]
triples = T1 + m + Wl[1]
assert S < T1 and S < triples and abs(triples + m + Wl[2] - S) < 1e-9   # under one completion per prefix; counts agree
inner = max(m + P[1], max(m + Wl[1], 0) + m + P[2]) / 2
per = max(T0 - S, T1 - S + 2 * inner) / 2
total = max(ell + m, ell + S + per)
print(f"ell {ell:.6f}  S {S:.6f}  T0 {T0:.6f}  T1 {T1:.6f}  buckets {[round(m + x, 6) for x in P]}  good {[round(m + x, 6) for x in Wl]}")
print(f"terms: preprocessing {ell + m:.6f}, search via T0 {ell + S + (T0 - S) / 2:.6f}, via T1 {ell + S + (T1 - S) / 2 + inner:.6f}")
print(f"explicit total {total:.6f}, recursive {time_k(m, t, a):.6f}")
assert abs(total - time_k(m, t, a)) < 1e-9 and total < 0.3178 - 0.013
