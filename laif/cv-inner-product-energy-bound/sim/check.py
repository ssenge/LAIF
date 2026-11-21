"""Checks for the bounds on energy-constrained distributed inner product estimation of m-mode states,
class C_{m,E} = {tau : Tr(nu_tot tau) <= b}, b = m(E - 1/2).
1. Counting: the number of photon-number states with total photon number <= K is C(K+m, m) >= (1 + K/m)^m, and for
   K = floor(b/(100 eps)) this is >= ((E - 1/2)/(100 eps))^m; the cutoff space dim C(N-1+m, m), N = ceil(4b/eps),
   is <= (e (1 + 4(E - 1/2)/eps))^m.
2. Hard states sqrt(1-e1) e^{i theta}|vac> + sqrt(e1)|phi>, phi on total photon number 1..K, e1 = 100 eps,
   lie in C_{m,E}.
3. Total-photon cutoff bias |Tr(rho sigma) - Tr(P rho P P sigma P)| <= 2 max(q_rho, q_sigma) <= 2b/N on random
   states of C_{m,E}."""
import itertools, math
from fractions import Fraction as F
import numpy as np
rng = np.random.default_rng(1)
# 1. counting, exact
for m in range(1, 9):
    for E in (F(3, 4), F(1), F(2), F(7)):
        b = m * (E - F(1, 2))
        for eps in (F(1, 10 ** 3), F(1, 10 ** 4), F(1, 10 ** 5)):
            if eps > b / 100: continue
            K = math.floor(b / (100 * eps)); assert K >= 1
            c = math.comb(K + m, m)
            assert c >= (1 + F(K, m)) ** m >= ((E - F(1, 2)) / (100 * eps)) ** m
            N = math.ceil(4 * b / eps); D = math.comb(N - 1 + m, m)
            assert D <= (math.e * (1 + 4 * float(E - F(1, 2)) / float(eps))) ** m
            assert F(b) / N <= eps / 4
print("counting bounds hold")
def fock(m, nmax):  # photon-number basis with total photon number <= nmax
    return [n for t in range(nmax + 1) for n in itertools.product(range(t + 1), repeat=m) if sum(n) == t]
# 2. energy of the hard states
for m, E, eps in ((1, 1.0, 1e-3), (2, 0.75, 2e-4), (3, 0.6, 1e-4)):
    b = m * (E - 0.5); e1 = 100 * eps; K = math.floor(b / e1 + 1e-12); B = fock(m, K); tot = np.array([sum(n) for n in B])
    for _ in range(50):
        phi = rng.standard_normal(len(B)) + 1j * rng.standard_normal(len(B)); phi[0] = 0; phi /= np.linalg.norm(phi)
        psi = math.sqrt(1 - e1) * np.exp(2j * math.pi * rng.random()) * (np.arange(len(B)) == 0) + math.sqrt(e1) * phi
        assert abs(np.linalg.norm(psi) - 1) < 1e-12 and (abs(psi) ** 2 @ tot) <= b + 1e-12
    print(f"m={m}: hard states in C_mE, K={K}, d={len(B) - 1}")
# 3. bias of the total-photon cutoff on random energy-bounded states
def rand_state(B, tot, b):
    r = rng.integers(1, 4); G = rng.standard_normal((len(B), r)) + 1j * rng.standard_normal((len(B), r))
    G *= np.exp(-rng.random() * 3 * tot)[:, None]; rho = G @ G.conj().T; rho /= np.trace(rho).real
    en = np.trace(rho * tot).real                       # Tr(nu rho), nu diagonal
    if en > b: lam = b / en; rho = lam * rho; rho[0, 0] += 1 - lam   # mix with vacuum to meet the budget
    return rho
for m, nmax in ((1, 30), (2, 14), (3, 8)):
    B = fock(m, nmax); tot = np.array([sum(n) for n in B])
    for _ in range(300):
        b = rng.random() * 2; N = int(rng.integers(1, nmax)); P = np.diag((tot <= N - 1).astype(float))
        rho, sig = rand_state(B, tot, b), rand_state(B, tot, b)
        assert np.trace(rho * tot).real <= b + 1e-9 and np.trace(sig * tot).real <= b + 1e-9
        q = max(1 - np.trace(P @ rho).real, 1 - np.trace(P @ sig).real); assert q <= b / N + 1e-9
        bias = abs(np.trace(rho @ sig) - np.trace(P @ rho @ P @ P @ sig @ P))
        assert bias <= 2 * q + 1e-9 and bias <= 2 * b / N + 1e-9
print("cutoff bias bound holds; all checks passed")
# 4. fallback instance for small d: fidelity of sqrt(1-a)|0> + sqrt(a)|1>, a in {50 eps, 53 eps}, is >= 1 - eps/20
for eps in np.geomspace(1e-12, 1e-4, 200):
    F_ = (math.sqrt((1 - 50 * eps) * (1 - 53 * eps)) + math.sqrt(2650) * eps) ** 2
    assert F_ >= 1 - eps / 20
# 5. total-photon cutoff dimension never exceeds the per-mode one: C(N-1+m, m) <= N^m <= L^m
for m in range(1, 9):
    for N in range(1, 60): assert math.comb(N - 1 + m, m) <= N ** m
print("fallback fidelity and dimension comparison hold")
