"""Toffoli counts per shot for 24Mg (USDB), source encoding of 2607.21563 against the Majorana encoding with shifts.
Query count (source App. A): Q_W = 2^m, m = ceil(log2(pi lambda / (2 sqrt(x) dE))), dE = 0.01 MeV; x is not stated.
The source cost per walk step is C_W = Toffoli / Q_W from its Table I. Its 220-qubit row needs C_W >= d = 2224 (a QROM
read of d entries without extra ancillae costs at least d Toffoli), and 1.36e9 / 2^20 < 2224, so m = 19, x >= 0.307.
Upper bound on the extra cost per step of the Majorana encoding, added on top of C_W (the source's two-body Sel, which
it replaces, is not subtracted): 4 selected Majorana operators by unary iteration, 4 (N - 1); the term class from
index comparisons (p = r, p = s, q = r, q = s on 5-bit indices, computed and uncomputed), 4 * 2 * 5; a class-dependent
uniform superposition over 8, 2 or 1 Majorana choices and its uncompute, 16. Signs and phases of the Majorana
monomials are parities of the choice bits and the stored sign bit (Clifford). The QROM keeps one entry per term."""
import math
N, dE, d_src = 24, 0.01, 2224
lam_src, lam_new = 1849.97, 706.72          # check_usdb.py, hybrid.py
rows = [(1.07e9, 608), (1.09e9, 349), (1.36e9, 220)]   # Table I(a), approach (i)
extra = 4 * (N - 1) + 4 * 2 * 5 + 16
def m_of(lam, x): return math.ceil(math.log2(math.pi * lam / (2 * math.sqrt(x) * dE)))
assert 1.36e9 / 2 ** 20 < d_src <= 1.36e9 / 2 ** 19          # forces m_src = 19
xs = [k / 10000 for k in range(1, 10000) if m_of(lam_src, k / 10000) == 19]
print("x range with m_src = 19: [%.4f, 1); extra Toffoli per step <= %d" % (xs[0], extra))
for T, q in rows:
    CW = T / 2 ** 19; CW2 = CW + extra
    print("source %.3g Toffoli at %d qubits: C_W = %.0f, new C_W <= %.0f (+%.1f%%), qubits + 5" % (T, q, CW, CW2, 100 * extra / CW))
    for mn in sorted({m_of(lam_new, x) for x in xs}, reverse=True):
        xr = [x for x in xs if m_of(lam_new, x) == mn]
        print("   x in [%.3f, %.3f]: m 19 -> %d, Toffoli <= %.3g, ratio >= %.2f" % (xr[0], xr[-1], mn, 2 ** mn * CW2, T / (2 ** mn * CW2)))
    print("   continuous Q_W ~ lambda: ratio >= %.2f" % (lam_src * CW / (lam_new * CW2)))
    assert all(T / (2 ** m_of(lam_new, x) * CW2) > 1.7 for x in xs)
