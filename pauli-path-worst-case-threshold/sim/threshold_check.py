"""Worst-case failure of path truncation in the string basis on one layer of majority gates.

Block polynomial G(z) = z * sum_S Maj^(S) z^|S| for observable Z_1 behind a k-qubit majority permutation,
input |0...0>, depolarizing noise of rate p = 1 - z on every qubit before and after the layer. For K blocks
the truncation error at cutoff l is |sum_{w>l} c_w z^w| with sum_w c_w x^w = G(x)^K. The signs give
G(ix)^K = (-Ghat(x))^K with Ghat(x) = sum_w |c_w| x^w per block, so the largest tail term is at least
Ghat(z)^K/N with N = (k-1)K/2 + 1 nonzero terms.
"""
import itertools
from fractions import Fraction
from math import comb, sqrt
import numpy as np


def maj_poly(k):
    """Coefficients g[w] of G(x) = x * sum_S Maj^(S) x^|S| for k-bit majority (k odd), exact."""
    g = [Fraction(0)] * (k + 2)
    for j in range(1, k + 1, 2):
        coef = Fraction((-1) ** ((j - 1) // 2) * comb((k - 1) // 2, (j - 1) // 2) * comb(k - 1, (k - 1) // 2),
                        comb(k - 1, j - 1) * 2 ** (k - 1))
        g[1 + j] += comb(k, j) * coef  # all |S| = j coefficients are equal
    return g


def pmul(a, b):
    out = [Fraction(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                out[i + j] += x * y
    return out


def ppow(a, K):
    out = [Fraction(1)]
    for _ in range(K):
        out = pmul(out, a)
    return out


def peval(a, z):
    return sum(c * z ** w for w, c in enumerate(a))


def errors(g, K, z):
    """Truncation errors |sum_{w>l} c_w z^w| for every cutoff l."""
    c = ppow(g, K)
    tail, out = Fraction(0), {}
    for w in range(len(c) - 1, -1, -1):
        out[w] = abs(tail)
        tail += c[w] * z ** w
    return out, abs(tail)


def check_block_by_simulation():
    """For k = 3, 5: V^dag Z_1 V = Maj(Z) for a permutation V; string coefficients match maj_poly."""
    for k in (3, 5):
        xs = list(itertools.product((0, 1), repeat=k))
        maj = {x: 1 if sum(x) <= k // 2 else -1 for x in xs}  # +1 for majority 0, as Z eigenvalues
        # permutation pi with Z_1 value of pi(x) equal to maj(x): both balanced
        plus = [y for y in xs if y[0] == 0]
        minus = [y for y in xs if y[0] == 1]
        pi = {}
        for x in xs:
            pi[x] = plus.pop() if maj[x] == 1 else minus.pop()
        idx = {x: i for i, x in enumerate(xs)}
        V = np.zeros((2 ** k, 2 ** k))
        for x in xs:
            V[idx[pi[x]], idx[x]] = 1
        Z1 = np.diag([1 - 2 * x[0] for x in xs])
        A = V.T @ Z1 @ V
        assert np.allclose(np.diag(A), [maj[x] for x in xs]) and np.allclose(A, np.diag(np.diag(A)))
        # frequency coefficients of the diagonal by weight, then G(x) = x sum_S Maj^(S) x^|S|
        g = [0.0] * (k + 2)
        for S in itertools.product((0, 1), repeat=k):
            chi = [(-1) ** sum(s * xi for s, xi in zip(S, x)) for x in xs]
            g[1 + sum(S)] += np.dot(chi, np.diag(A)) / 2 ** k
        assert np.allclose(g, [float(t) for t in maj_poly(k)])
        if k == 3:  # the gate of [1, Eq. (19)]: swaps |011> and |100>, fixes the rest
            V19 = np.eye(8)[:, [0, 1, 2, 4, 3, 5, 6, 7]]
            assert np.allclose(V19.T @ Z1 @ V19, np.diag([maj[x] for x in xs]))
        # noisy value: depolarize, apply V, depolarize, measure Z_1; equals G(z) with z = 1 - p
        p = 0.3
        rho = np.zeros((2 ** k, 2 ** k))
        rho[0, 0] = 1
        for q in range(k):
            rho = depolarize(rho, q, k, p)
        rho = V @ rho @ V.T
        for q in range(k):
            rho = depolarize(rho, q, k, p)
        assert abs(np.trace(Z1 @ rho) - float(peval(maj_poly(k), Fraction(7, 10)))) < 1e-12
    print("block check: V^dag Z_1 V = Maj for k = 3, 5; string weights and noisy values match G")


def depolarize(rho, q, k, p):
    X = np.array([[0, 1], [1, 0]])
    Y = np.array([[0, -1j], [1j, 0]])
    Z = np.diag([1, -1])
    out = (1 - 3 * p / 4) * rho
    for P in (X, Y, Z):
        M = np.kron(np.kron(np.eye(2 ** q), P), np.eye(2 ** (k - q - 1)))
        out = out + (p / 4) * M @ rho @ M.conj().T
    return np.real_if_close(out)


def ghat(g, z):
    return sum(abs(c) * z ** w for w, c in enumerate(g))


def check_majority3():
    g = maj_poly(3)
    assert g == [0, 0, Fraction(3, 2), 0, Fraction(-1, 2)]
    pstar = 1 - sqrt((sqrt(17) - 3) / 2)
    print(f"k = 3: G(z) = 1.5 z^2 - 0.5 z^4, Ghat(z) = 1.5 z^2 + 0.5 z^4, Ghat(1 - p) = 1 at p* = {pstar:.4f}")
    for p in (Fraction(20, 100), Fraction(22, 100), Fraction(24, 100), Fraction(26, 100), Fraction(30, 100)):
        z = 1 - p
        row = []
        for K in (10, 40, 160):
            c = ppow(g, K)
            assert ppow([abs(t) for t in g], K) == [abs(t) for t in c]  # sum_w |F_w| x^w = Ghat(x)^K exactly
            errs, true = errors(g, K, z)
            worst = max(errs.values())
            low = ghat(g, z) ** K / (2 * (K + 1))
            lbad = max(errs, key=errs.get)
            assert 2 * K - 2 <= lbad <= 4 * K
            assert worst >= low and true <= 1
            if ghat(g, z) < 1:  # tail bound r^l Ghat(z/r)^K <= r^l with Ghat(z/r) = 1
                r = find_r(g, z)
                assert all(e <= r ** l * (1 + 1e-12) for l, e in errs.items())
            row.append(f"K = {K}: worst error {float(worst):.3g} >= {float(low):.3g}")
        print(f"  p = {float(p):.2f}, Ghat = {float(ghat(g, z)):.4f}: " + "; ".join(row))


def find_r(g, z):
    lo, hi = float(z), 1.0  # Ghat(z/r) decreasing in r
    for _ in range(80):
        mid = (lo + hi) / 2
        lo, hi = (mid, hi) if sum(abs(float(c)) * (float(z) / mid) ** w for w, c in enumerate(g)) > 1 else (lo, mid)
    return Fraction(hi)


def check_all_rates():
    for p in (Fraction(1, 2), Fraction(7, 10), Fraction(8, 10)):
        z = 1 - p
        k = 3
        while ghat(maj_poly(k), z) <= 1:
            k += 2
        g = maj_poly(k)
        assert k <= 2 / float(z) ** 4 + 1  # level one alone gives Ghat >= z^2 sqrt(k/2)
        K = 30
        errs, true = errors(g, K, z)
        worst = max(errs.values())
        assert worst >= ghat(g, z) ** K / ((k - 1) * K + 2) and true <= 1  # (k-1)K/2 + 1 nonzero terms
        print(f"p = {float(p):.1f}: smallest odd k with Ghat > 1 is {k} (bound 2/z^4 = {2 / float(z) ** 4:.0f}); "
              f"Ghat = {float(ghat(g, z)):.4f}, K = {K} blocks: worst error {float(worst):.3g}, true value {float(true):.2e}")


def check_prescribed_cutoff():
    """Lemma 2: for every even cutoff l, some K <= l/2 and J in {0, 1} idle qubits give
    E_l >= z^2 beta^((k-1)/2) x0^(-l) / l, where Ghat(z x0) = 1 and beta = [x^2]Ghat(zx) x0^2."""
    for k, p, lmax in ((3, Fraction(24, 100), 120), (5, Fraction(30, 100), 80)):
        g, z = maj_poly(k), 1 - Fraction(p)
        lo, hi = 0.0, 1.0  # x0 with Ghat(z x0) = 1, from below so the bound is safe
        for _ in range(80):
            mid = (lo + hi) / 2
            lo, hi = (mid, hi) if float(ghat(g, z * Fraction(mid))) < 1 else (lo, mid)
        x0 = Fraction(lo)
        beta = abs(g[2]) * z ** 2 * x0 ** 2
        tails = {K: errors(g, K, z)[0] for K in range(1, lmax // 2 + 1)}
        worst_ratio = float("inf")
        for l in range(2, lmax + 1, 2):
            best = 0
            for K in range(1, l // 2 + 1):
                t = tails[K]
                e0 = t.get(l, Fraction(0))
                e1 = z ** 2 * t.get(l - 2, Fraction(0))  # one idle qubit multiplies the polynomial by x^2
                best = max(best, e0, e1)
            bound = z ** 2 * beta ** ((k - 1) // 2) / (x0 ** l * l)
            assert best >= bound, (k, l)
            worst_ratio = min(worst_ratio, float(best / bound))
        print(f"k = {k}, p = {float(p)}: every even cutoff l <= {lmax} has a circuit with error >= "
              f"z^2 beta^((k-1)/2) x0^-l / l, x0 = {float(x0):.4f} (growth rate 1/x0 = {1 / float(x0):.4f}); "
              f"smallest ratio worst error / bound {worst_ratio:.2f}")


def check_level_one():
    for k in range(3, 202, 2):
        g = maj_poly(k)
        assert float(g[2]) >= sqrt(k / 2)  # level-one mass, the x^2 coefficient of Ghat_k
    print("level one mass of k-bit majority >= sqrt(k/2) for odd k = 3..201")


if __name__ == "__main__":
    check_block_by_simulation()
    check_majority3()
    check_all_rates()
    check_prescribed_cutoff()
    check_level_one()
    print("string path threshold checks pass")
