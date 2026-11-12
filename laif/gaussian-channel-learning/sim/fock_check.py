# Fock-space checks (one mode, truncation K):
#  (1) the trace-distance bound for Gaussian states used in Lemma 4 (fact from [3]) on random pairs;
#  (2) Theorem 1 on pure-loss channels Phi_eta (X = sqrt(eta), Y = 1 - eta), in operator-sum form: the trace distance of the
#      outputs on a truncated two-mode squeezed input of mean photon number E is below the bound.
import numpy as np
from scipy.linalg import expm
from bounds import general_bound, margin_bound
K = 70
a = np.diag(np.sqrt(np.arange(1, K)), 1); ad = a.T; n = ad @ a
x = (a + ad) / np.sqrt(2); p = (a - ad) / (1j * np.sqrt(2))

def gauss_state(V, mu):
    """Gaussian state with covariance V, mean mu: thermal -> squeeze/rotate -> displace (exact in moments)."""
    nu = np.sqrt(np.linalg.det(V))
    nth = (nu - 1) / 2
    th = np.diag((nth / (nth + 1)) ** np.arange(K) / (nth + 1)) if nth > 1e-12 else np.diag(np.eye(K)[0])
    # V = nu R diag(e^{2s}, e^{-2s}) R^T
    w, U = np.linalg.eigh(V / nu)
    s = np.log(w[1]) / 2; phi = np.arctan2(U[1, 1], U[0, 1])
    S = expm(-s / 2 * (a @ a - ad @ ad)); Rr = expm(1j * phi * n)
    D = expm((mu[0] + 1j * mu[1]) / np.sqrt(2) * ad - (mu[0] - 1j * mu[1]) / np.sqrt(2) * a)
    rho = D @ Rr @ S @ th @ S.conj().T @ Rr.conj().T @ D.conj().T
    return rho / np.trace(rho).real

def moments(rho):
    R = [x, p]
    mu = np.array([np.trace(rho @ o).real for o in R])
    V = np.array([[np.trace(rho @ (R[i] @ R[j] + R[j] @ R[i])).real - 2 * mu[i] * mu[j] for j in range(2)] for i in range(2)])
    return V, mu

tn = lambda M: np.abs(np.linalg.eigvalsh((M + M.conj().T) / 2)).sum()
rng = np.random.default_rng(3)
Om = np.array([[0, 1.], [-1, 0]])
worst = 0
for t in range(40):
    def rv():
        A = rng.normal(size=(2, 2)) * 0.4
        V = (np.eye(2) + A @ A.T) * rng.uniform(1, 1.6)
        return V
    V1, V2 = rv(), rv()
    m1 = rng.normal(size=2) * 0.5; m2 = m1 + rng.normal(size=2) * 0.2
    r1, r2 = gauss_state(V1, m1), gauss_state(V2, m2)
    W1, mm1 = moments(r1); W2, mm2 = moments(r2)
    assert np.allclose(W1, V1, atol=1e-6) and np.allclose(mm1, m1, atol=1e-6), (W1, V1)   # truncation ok
    lhs = tn(r1 - r2) / 2
    Vb = (V1 + V2) / 2
    dV = V1 - V2; w, U = np.linalg.eigh(dV); absdV = (U * np.abs(w)) @ U.T
    rhs = (1 + np.sqrt(3)) / 8 * np.trace(absdV @ Om.T @ Vb @ Om) + np.sqrt(min(np.linalg.norm(V1, 2), np.linalg.norm(V2, 2)) / 2) * np.linalg.norm(m1 - m2)
    assert lhs <= rhs + 1e-9, (lhs, rhs)                                                            # (1)
    worst = max(worst, lhs / rhs)
print(f"(1) Gaussian trace-distance bound holds on 40 random pairs, largest ratio {worst:.3f}")

# (2) pure-loss channels in operator-sum form; input: truncated two-mode squeezed vacuum with mean photon number E
from math import comb
K = 32                                             # enough for E <= 2: tail weight (2/3)^32 < 1e-5
def att_kraus(eta, L):
    Ks = []
    for l in range(L):
        Kl = np.zeros((K, K))
        for k in range(l, K):
            Kl[k - l, k] = np.sqrt(float(comb(k, l))) * eta ** ((k - l) / 2) * (1 - eta) ** (l / 2)
        Ks.append(Kl)
    return Ks
def thermal_att(eta, nth):
    """Thermal attenuator = pure loss eta' followed by quantum-limited amplifier; here only nth = 0 is used."""
    assert nth == 0
    return att_kraus(eta, K)
def out_state(Ks, psi):
    # psi: K x K coefficient matrix of sum_ij c_ij |i>_R |j>_A; output on R (x) B
    rho = 0
    for Kl in Ks:
        v = psi @ Kl.T
        f = v.reshape(-1)
        rho = rho + np.outer(f, f.conj())
    return rho
print("(2) pure-loss attenuators, eta2 = eta1 + delta, input TMSV with mean photon number E:")
for E in (0.5, 2.0):
    lam = E / (E + 1)
    c = np.sqrt(lam) ** np.arange(K) * np.sqrt(1 - lam)
    psi = np.diag(c / np.linalg.norm(c))
    for eta1, dl in ((0.5, 0.05), (0.9, 0.05), (0.98, 0.01), (0.9, 1e-6)):
        eta2 = eta1 + dl
        r1 = out_state(att_kraus(eta1, K), psi); r2 = out_state(att_kraus(eta2, K), psi)
        lhs = tn(r1 - r2) / 2
        dX = np.sqrt(eta2) - np.sqrt(eta1); dY = dl
        xs = np.exp(np.linspace(np.log(1e-12), np.log(1.9), 800))
        rhs = min(general_bound(E, 1, 1.0, 1.0, xi, dX, dY, 0) for xi in xs)
        assert lhs <= rhs, (lhs, rhs)
        print(f"   E = {E}, eta = {eta1} -> {eta1} + {dl}: distance {lhs:.4f} <= bound {rhs:.3f}")
