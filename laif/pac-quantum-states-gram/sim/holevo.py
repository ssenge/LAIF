"""Exact checks for Theorem 1 (logs base 2).

Instance: psi_0 = e_0, psi_i = sqrt(1 - lam) u + sqrt(lam) e_i (i = 1..d), with e_0, e_1..e_d, u orthonormal.
Distribution: mass 1 - 8 eps on psi_0, 8 eps/d on each psi_i. Concepts: c(psi_0) = 0, any labels on psi_1..psi_d.
One example: rho_c = sum_x D(x) |psi_x><psi_x| (x) |c(x)><c(x)|, c uniform.
Asserts:
  1. Gram matrix of psi_0..psi_d has smallest eigenvalue lam (linear independence).
  2. Spectrum of omega_s (average of s of the psi_i): 1 - lam + lam/s once, lam/s with multiplicity s - 1.
  3. Exact chi = S(E rho_c) - E S(rho_c) by enumeration of all 2^d labellings (d <= 10) equals the closed form
     8 eps E[1 - h(f) + phi(d) - f phi(fd) - (1 - f) phi((1 - f) d)], and
     chi <= 8 eps K, K = 1/d + lam (1 + log2 e) + (lam/d) log2(d/(4 lam)).
  4. The closed form for d up to 4096 (sum over the count of ones), with the same bound.
  6. Corollary 2: for two concepts that swap the labels of psi_1, psi_2 (mass m each, rest on psi_0),
     Tr sigma^s rho^(1-s) = 1 - 2m(2 lam - lam^2) for every s in [0, 1].
  5. The resulting sample bound against the upper bound (d + ln 1/delta)/(eps lam) of [1, Theorem 2].
"""
import itertools, math
import numpy as np

LOG2E = math.log2(math.e)


def S(rho):
    w = np.linalg.eigvalsh(rho); w = w[w > 1e-14]
    return float(-(w * np.log2(w)).sum())


def eta(x):
    return 0.0 if x <= 0 else -x * math.log2(x)


def hb(p):
    return eta(p) + eta(1 - p)


def phi(s, lam):          # entropy of omega_s, from the spectrum in assert 2
    return eta(1 - lam + lam / s) + (s - 1) * eta(lam / s) if s >= 1 else 0.0


def K(d, lam):
    return 1 / d + lam * (1 + LOG2E) + (lam / d) * math.log2(d / (4 * lam))


def chi_closed(d, lam, eps):  # 8 eps E[1 - h(f) + phi(d) - f phi(fd) - (1-f) phi((1-f)d)], c uniform
    tot = 0.0
    for k in range(d + 1):
        f = k / d
        tot += math.comb(d, k) / 2 ** d * (1 - hb(f) + phi(d, lam) - f * phi(k, lam) - (1 - f) * phi(d - k, lam))
    return 8 * eps * tot


def vectors(d, lam):
    V = np.zeros((d + 1, d + 2)); V[0, 0] = 1
    for i in range(1, d + 1):
        V[i, d + 1] = math.sqrt(1 - lam); V[i, i] = math.sqrt(lam)
    return V                                             # V[x] = psi_x in R^{d+2}


for d in range(2, 11):
    for lam in [1.0, 0.5, 0.1, 0.01]:
        V = vectors(d, lam)
        assert abs(np.linalg.eigvalsh(V @ V.T).min() - lam) < 1e-9
        for s in range(1, d + 1):
            w = np.sort(np.linalg.eigvalsh(sum(np.outer(V[i], V[i]) for i in range(1, s + 1)) / s))[::-1]
            ref = np.r_[1 - lam + lam / s, np.full(s - 1, lam / s), np.zeros(d + 2 - s)]
            assert np.allclose(w, ref, atol=1e-10)
        for eps in [0.01, 0.1]:
            D = np.r_[1 - 8 * eps, np.full(d, 8 * eps / d)]
            P = [np.outer(V[x], V[x]) for x in range(d + 1)]
            mean = np.zeros((2 * (d + 2), 2 * (d + 2))); ES = 0.0
            for c in itertools.product([0, 1], repeat=d):
                lab = (0,) + c
                rho = sum(D[x] * np.kron(P[x], np.diag([1 - lab[x], lab[x]])) for x in range(d + 1))
                mean += rho / 2 ** d; ES += S(rho) / 2 ** d
            chi = S(mean) - ES
            assert abs(chi - chi_closed(d, lam, eps)) < 1e-9, (d, lam, eps, chi, chi_closed(d, lam, eps))
            if d >= 4:
                assert chi <= 8 * eps * K(d, lam) + 1e-12, (d, lam, eps, chi, K(d, lam))
    print(f"d = {d:2d}: Gram, spectra and exact chi = closed form checked; chi/(8 eps) at lam = 0.01: {chi_closed(d, 0.01, 1) / 8:.5f}")

for d in [16, 64, 256, 1024, 4096]:
    for lam in [1.0, 0.1, 0.01, 1 / d]:
        c = chi_closed(d, lam, 1) / 8
        assert c <= K(d, lam) + 1e-12
        if lam >= 1 / d:
            assert K(d, lam) <= 1 / d + 3.45 * lam + 1e-12
        r = d // 8
        logV = math.log2(sum(math.comb(d, j) for j in range(r + 1)))
        eps, delta = 0.01, 0.01
        t_low = ((1 - delta) * (d - logV) - 1) / (8 * eps * K(d, lam))
        t_up = (d + math.log(1 / delta)) / (eps * lam)
        assert t_low > 0
        print(f"d = {d:4d}, lam = {lam:8.5f}: chi/(8 eps) = {c:.5f} <= K = {K(d, lam):.5f};  t >= {t_low:10.0f}, (d + ln 1/delta)/(eps lam) = {t_up:11.0f}, ratio {t_up / t_low:6.1f}")


def mpow(A, s):
    w, U = np.linalg.eigh(A); w = np.clip(w, 0, None)
    return (U * np.where(w > 1e-14, w ** s, 0.0)) @ U.T


for d in [3, 5]:
    for lam in [1.0, 0.3, 0.01]:
        V = vectors(d, lam); P = [np.outer(V[x], V[x]) for x in range(d + 1)]
        for m in [0.02, 0.15]:
            L0, L1 = np.diag([1.0, 0]), np.diag([0, 1.0])
            rest = (1 - 2 * m) * np.kron(P[0], L0)
            sig = rest + m * np.kron(P[1], L1) + m * np.kron(P[2], L0)
            rho = rest + m * np.kron(P[1], L0) + m * np.kron(P[2], L1)
            for s_ in np.linspace(0, 1, 11):
                q = np.trace(mpow(sig, s_) @ mpow(rho, 1 - s_))
                assert abs(q - (1 - 2 * m * (2 * lam - lam ** 2))) < 1e-9, (d, lam, m, s_, q)
print("Corollary 2: Tr sigma^s rho^(1-s) = 1 - 2m(2 lam - lam^2) for all s checked")
print("all checks passed")
