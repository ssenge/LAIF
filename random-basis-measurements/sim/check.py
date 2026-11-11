"""Checks for the note on three and four random bases (run: python -I sim/check.py, about 10 minutes).
1. Codimension count of Theorem 1: for orthonormal rows (r1, r2) with dark set D (|D| = m), the functionals
   Re(r1_x conj r2_x), x not in D, restricted to the orthogonal complement of r1, have rank d - m - 1.
2. Three uniformly random bases: a regular zero of the information is found in every sampled instance, d = 3..12.
3. Exact certificates (rational unitary bases, root-existence test in rational arithmetic) for d = 3..12.
4. Four uniformly random bases: no zero is found (consistency with Theorem 1).
5. Theorem 2: the dual class (1 + x)^{-(n+1)} mod 2 has top degree i(n) = 2^r - 1 - m for n = 2^r + m, the list of
   dimensions where three bases are excluded, and a zero for three mutually unbiased bases in d = 5."""
import os
import sys
import numpy as np
from scipy.stats import unitary_group

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from k3 import solve
from cert3 import certify
from math import comb


def i_top(n):
    """largest i <= n with C(n + i, i) odd, the top degree (in x) of (1 + x)^{-(n+1)} mod 2"""
    return max(i for i in range(n + 1) if comb(n + i, i) % 2)


def check_topology(rng):
    for n in range(1, 200):
        r = n.bit_length() - 1
        assert i_top(n) == 2 ** r - 1 - (n - 2 ** r)
    ds = [n + 1 for n in range(2, 90) if 2 * i_top(n) > n]
    print(f"5. top degree of the dual class verified for n < 200; three bases are excluded (3n < 2n + 2 i(n)) for d = {ds}")
    d = 5; w = np.exp(2j * np.pi / d); x = np.arange(d)
    F = np.exp(2j * np.pi * np.outer(x, x) / d) / np.sqrt(d); Q = np.diag(w ** (x * x)) @ F
    res, q, _ = solve([np.eye(d), F, Q], 200, rng)
    print(f"   three mutually unbiased bases in d = 5: zero with residual {res:.1e} at smallest outcome probability {q:.1e}")
    assert res < 1e-13


def check_codim(rng):
    for d in range(2, 9):
        for m in range(0, d):
            U = unitary_group.rvs(d, random_state=rng)
            r1 = U[0].copy(); r1[:m] = 0; r1 /= np.linalg.norm(r1)
            # real coordinates of r2 in C^d; the complement of r1: Re and Im of sum r1_x conj r2_x vanish
            def fun(x, r2): return (x * np.conj(r2)).real
            E = []
            for k in range(2 * d):
                e = np.zeros(d, complex); e[k % d] = 1 if k < d else 1j
                E.append(e)
            A = np.array([[(r1[x] * np.conj(e[x])).real for e in E] for x in range(m, d)])
            C = np.array([[(np.sum(r1 * np.conj(e))).real for e in E], [(np.sum(r1 * np.conj(e))).imag for e in E]])
            N = np.linalg.svd(C)[2][2:].T                     # basis of the complement of r1
            rank = np.linalg.matrix_rank(A @ N, tol=1e-10)
            assert rank == d - m - 1, (d, m, rank)
    print("1. codimension count: rank d - m - 1 for d = 2..8 and every dark count m, so the blind bases of a fixed (psi, u) have codimension d - 1 + m")


def check_search(rng, K, ds, n):
    for d in ds:
        found = 0; qs = []
        for _ in range(n):
            Us = [unitary_group.rvs(d, random_state=rng) for _ in range(K)]
            res, q, x = solve(Us, 40, rng)
            ok = res < 1e-13 and q > 1e-6
            found += ok; qs.append(res)
        print(f"   K = {K}, d = {d}: zero at a regular state in {found}/{n} instances; residual of the best point between {min(qs):.1e} and {max(qs):.1e}", flush=True)
        if K == 3: assert found == n
        if K == 4: assert min(qs) > 1e-6


if __name__ == "__main__":
    rng = np.random.default_rng(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
    check_codim(rng)
    print("2. three uniformly random bases, least squares from 40 starts per instance:", flush=True)
    check_search(rng, 3, [3, 4, 5, 6, 8, 10, 12], 10)
    print("3. exact certificates:", flush=True)
    for d in range(3, 13):
        h, rad, q, ok = certify(d, 100 * d)
        print(f"   d = {d}: h = {h:.1e} < 1/2, root within {rad:.1e} (infinity norm), smallest outcome probability {q:.1e}: {'certified' if ok else 'FAILED'}", flush=True)
        assert ok
    print("4. four uniformly random bases:", flush=True)
    check_search(rng, 4, [3, 4, 5, 6], 5)
    check_topology(rng)
    print("all checks passed")
