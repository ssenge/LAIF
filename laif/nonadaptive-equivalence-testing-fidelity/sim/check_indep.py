# Checks for Theorem 2 of the README (independence testing): constants, Beta tail, Schmidt/Jensen tail, projected Gaussian. Asserts throughout.
import numpy as np, math
from scipy import stats
rng = np.random.default_rng(2)
c0, K = 1 / 10, 7.5

# Lemma 2': ||G|| <= ||H|| + ||tr_C H||/d_C + ||tr_A H||/D_A + |tr H|/D <= 4.75 + 4.75/2 + 5.6/56 + 1/4 <= K
assert 4.75 + 4.75 / 2 + 5.6 / 56 + 0.25 <= K and c0 * K <= 0.75
assert (5.6 / 1.25) ** 2 / 2 - 2 * math.log(21) > 3.9          # net bound on C^{d_C}: 2 e^{-3.9 d_C}
assert 0.75 * 0.75 * (1 - 1 / 56 ** 2) >= 0.5                   # chi^2 lower tail x = k/64: 0.75 k >= D^2/2 for d_C >= 2
gap = c0 ** 2 / (16 * 1.75 ** 1.5); assert gap >= 1 / 3800
print(f"1 ok: K = {K}, c0 = {c0}, gap 1/{1/gap:.0f} >= 1/3800")

# Beta tail: P(Beta(D,D) > 3/4) <= sqrt(D/(D-1)) e^{-(D-1)/4}, and C(2D,D) <= 4^D/sqrt(pi D)
for D in range(2, 400):
    assert math.lgamma(2 * D + 1) - 2 * math.lgamma(D + 1) <= D * math.log(4) - 0.5 * math.log(math.pi * D)
    assert stats.beta.sf(0.75, D, D) <= math.sqrt(D / (D - 1)) * math.exp(-(D - 1) / 4)
print("2 ok: Beta(D,D) tail bound for D < 400")

# Jensen over Schmidt components: t = <v|(Pi_W (x) I)|v> for entangled v, Monte Carlo tail vs bound
def haar(n):
    q, r = np.linalg.qr(rng.normal(size=(n, n)) + 1j * rng.normal(size=(n, n))); return q * (np.diag(r) / abs(np.diag(r)))
for DA, dC in ((6, 2), (8, 3), (12, 2)):
    v = rng.normal(size=2 * DA * dC) + 1j * rng.normal(size=2 * DA * dC); v /= np.linalg.norm(v); V = v.reshape(2 * DA, dC)
    ts = []
    for _ in range(4000):
        U = haar(2 * DA)[:, DA:]                                  # light block
        ts.append(np.linalg.norm(U.conj().T @ V) ** 2)
    ts = np.array(ts); bound = math.sqrt(DA / (DA - 1)) * math.exp(-(DA - 1) / 4)
    lam = 2 * (DA - 1); mgf = np.mean(np.exp(lam * (ts - 0.5)))
    assert mgf <= math.sqrt(DA / (DA - 1)) * math.exp(lam ** 2 / (16 * (DA - 1))) * 1.05 and np.mean(ts > 0.75) <= bound + 0.01
    print(f"3 ok DA={DA} dC={dC}: P(t>3/4) MC {np.mean(ts>0.75):.4f} <= {bound:.4f}; MGF {mgf:.3f}")

# projected Gaussian: P = (id - Pi_A)(x)(id - Pi_C), norms and Frobenius mass
def projG(DA, dC):
    D = DA * dC; a = rng.normal(size=(D, D)) + 1j * rng.normal(size=(D, D)); H = (a + a.conj().T) / 2 / math.sqrt(D)
    T = H.reshape(DA, dC, DA, dC)
    trC = np.einsum('acbc->ab', T); trA = np.einsum('acad->cd', T); tr = np.trace(H)
    G = H - np.kron(trC, np.eye(dC)) / dC - np.kron(np.eye(DA), trA) / DA + tr * np.eye(D) / D
    Gt = G.reshape(DA, dC, DA, dC)
    assert abs(np.einsum('acbc->ab', Gt)).max() < 1e-10 and abs(np.einsum('acad->cd', Gt)).max() < 1e-10
    return np.linalg.norm(G, 2), np.linalg.norm(G) ** 2 / D
for DA, dC in ((16, 2), (24, 2), (12, 4)):
    r = np.array([projG(DA, dC) for _ in range(100)])
    assert r[:, 0].max() <= K and r[:, 1].min() >= 0.5
    print(f"4 ok DA={DA} dC={dC}: max ||G|| {r[:,0].max():.2f} <= {K}, min ||G||_F^2/D {r[:,1].min():.3f} >= 1/2")

# final count: A <= 4N, trA <= 4ND, N <= 13 D^{3/2}/eps^2 -> exponent 16 c0^4 169
x = 16 * c0 ** 4 * 169; pE = 1 - 2e-3
assert x / 56 <= 0.5 and 0.05 + 0.5 * math.sqrt(math.exp(x) / pE ** 2 - 1) < 1 / 3
# dimension condition D_A >= 1 + 4 ln(41 D_A d_C / eps) gives 40.4 D_A d_C e^{-(D_A-1)/4} <= eps (Markov at 1/20, sum c = 2 N D)
for dC in (2, 10, 1000):
    for L in (0.7, 5, 50):
        DA = 56
        while DA < 1 + 4 * math.log(41 * DA * dC * math.exp(L)): DA += 1
        assert 20 * 2 * DA * dC * math.sqrt(DA / (DA - 1)) * math.exp(-(DA - 1) / 4) <= math.exp(-L)
print(f"5 ok: exponent {x:.4f}, TV < 1/3; dimension condition")

# 6. instance at small size: P orthogonal projection of rank (D_A^2-1)(d_C^2-1), marginals, product of marginals = null, fidelity gap
import scipy.linalg as sl
def basis(n):
    B = []
    for i in range(n):
        for j in range(n):
            M = np.zeros((n, n), complex)
            if i == j: M[i, i] = 1
            elif i < j: M[i, j] = M[j, i] = 1 / math.sqrt(2)
            else: M[i, j] = -1j / math.sqrt(2); M[j, i] = 1j / math.sqrt(2)
            B.append(M)
    return B
def Pmap(H, DA, dC):
    T = H.reshape(DA, dC, DA, dC)
    return H - np.kron(np.einsum('acbc->ab', T), np.eye(dC)) / dC - np.kron(np.eye(DA), np.einsum('acad->cd', T)) / DA + np.trace(H) * np.eye(DA * dC) / (DA * dC)
DA, dC = 3, 2; Bs = basis(DA * dC)
Pm = np.array([[np.trace(a @ Pmap(b, DA, dC)).real for b in Bs] for a in Bs])
assert np.allclose(Pm, Pm.T) and np.allclose(Pm @ Pm, Pm) and round(np.trace(Pm)) == (DA ** 2 - 1) * (dC ** 2 - 1)
for e in (0.5, 0.1, 0.01):
    for _ in range(20):
        D = DA * dC; a = rng.normal(size=(D, D)) + 1j * rng.normal(size=(D, D)); G = Pmap((a + a.conj().T) / 2 / math.sqrt(D), DA, dC)
        if np.linalg.norm(G, 2) > K or np.linalg.norm(G) ** 2 < D / 2: continue
        W = np.kron(haar(2 * DA), np.eye(dC))
        null = W @ np.diag([(1 - e) / D] * D + [e / D] * D).astype(complex) @ W.conj().T
        pert = np.zeros((2 * D, 2 * D), complex); pert[D:, D:] = e * c0 / D * G; sig = null + W @ pert @ W.conj().T
        T4 = sig.reshape(2 * DA, dC, 2 * DA, dC); sA = np.einsum('acbc->ab', T4); sC = np.einsum('acad->cd', T4)
        assert np.allclose(np.kron(sA, sC), null) and np.linalg.eigvalsh(sig).min() > 0
        s = sl.sqrtm(null); f = np.sqrt(np.clip(np.linalg.eigvalsh(s @ sig @ s), 0, None)).sum()
        assert 1 - f >= e / 3800
print("6 ok: projection, marginals, product of marginals = null, 1 - F >= eps/3800")
