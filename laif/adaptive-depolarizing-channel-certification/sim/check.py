# Checks for chancert/NOTES.md: GUE* covariance, weighted recursion (W1), Haar moment, channel validity.
import itertools, math, numpy as np
rng = np.random.default_rng(7)
def gue0(d, k=1):
    a = rng.normal(size=(k, d, d)) + 1j * rng.normal(size=(k, d, d)); H = (a + a.conj().transpose(0, 2, 1)) / 2 / math.sqrt(d)
    return H - np.einsum('kii->k', H).real[:, None, None] / d * np.eye(d)
def unit(d):
    v = rng.normal(size=d) + 1j * rng.normal(size=d); return v / np.linalg.norm(v)
d, K = 4, 400000
G = gue0(d, K)
# 1. E[(x'Gx)(y'Gy)] = (d|<x,y>|^2 - 1)/d^2
x, y = unit(d), unit(d)
qx = np.einsum('i,kij,j->k', x.conj(), G, x).real; qy = np.einsum('i,kij,j->k', y.conj(), G, y).real
mc, ex = (qx * qy).mean(), (d * abs(np.vdot(x, y)) ** 2 - 1) / d ** 2
assert abs(mc - ex) < 6 * (qx * qy).std() / math.sqrt(K), (mc, ex); print("1 ok: GUE* covariance", mc, ex)
# 2. weighted L(z) = sum over matchings of prod eps^2 c_a c_b (d|<z_a,z_b>|^2-1)/d^2 ; and the recursion
def L_exact(z, c, eps):
    t = len(z); tot = 0.0
    def rec(rem, acc):
        nonlocal tot
        if not rem: tot += acc; return
        i, rest = rem[0], rem[1:]
        rec(rest, acc)                                   # i unmatched
        for j in rest:
            w = eps ** 2 * c[i] * c[j] * (d * abs(np.vdot(z[i], z[j])) ** 2 - 1) / d ** 2
            rec([k for k in rest if k != j], acc * w)
    rec(list(range(t)), 1.0); return tot
eps, t = 0.3, 4
z = [unit(d) for _ in range(t)]; c = rng.random(t)
q = np.array([np.einsum('i,kij,j->k', v.conj(), G, v).real for v in z])
Lmc = np.prod(1 + eps * c[:, None] * q, axis=0); Le = L_exact(z, c, eps)
assert abs(Lmc.mean() - Le) < 6 * Lmc.std() / math.sqrt(K), (Lmc.mean(), Le)
sub = lambda S: L_exact([z[i] for i in S], [c[i] for i in S], eps)
rhs = sub(range(t - 1)) + sum(eps ** 2 * c[i] * c[t - 1] / d ** 2 * (d * abs(np.vdot(z[i], z[t - 1])) ** 2 - 1)
                                * sub([k for k in range(t - 1) if k != i]) for i in range(t - 1))
assert abs(rhs - Le) < 1e-12
Hm = sum(c[i] * (d * np.outer(z[i], z[i].conj()) - np.eye(d)) * sub([k for k in range(t - 1) if k != i]) / sub(range(t - 1)) for i in range(t - 1))
assert abs(Le / sub(range(t - 1)) - 1 - eps ** 2 * c[t - 1] / d ** 2 * np.vdot(z[t - 1], Hm @ z[t - 1]).real) < 1e-12
print("2 ok: weighted Isserlis sum and recursion", Lmc.mean(), Le)
# 3. Haar: E (phi' rho phi)^2 = (tr rho^2 + 1)/(m(m+1))
m = 5; a = rng.normal(size=(m, m)) + 1j * rng.normal(size=(m, m)); rho = a @ a.conj().T; rho /= np.trace(rho).real
ph = rng.normal(size=(K, m)) + 1j * rng.normal(size=(K, m)); ph /= np.linalg.norm(ph, axis=1)[:, None]
v = np.einsum('ki,ij,kj->k', ph.conj(), rho, ph).real ** 2
ex = (np.trace(rho @ rho).real + 1) / (m * (m + 1))
assert abs(v.mean() - ex) < 6 * v.std() / math.sqrt(K) and ex <= 2 / (m * (m + 1)); print("3 ok: Haar fourth moment", v.mean(), ex)
# 4. channel: Choi PSD, TP, output at phi is eps*||G||_1/d far, ratio 1 + eps c x'Gx
for d2, m2 in ((6, 3), (10, 4)):
    for _ in range(20):
        Gs = gue0(d2)[0]
        if np.linalg.norm(Gs, 2) > 5 or np.linalg.norm(Gs) ** 2 < d2 / 2: continue
        e2 = 0.1; f = unit(m2)
        N = lambda r: np.trace(r) * np.eye(d2) / d2 + e2 / d2 * np.vdot(f, r @ f) * Gs
        J = sum(np.kron(np.outer(np.eye(m2)[i], np.eye(m2)[j]), N(np.outer(np.eye(m2)[i], np.eye(m2)[j]))) for i in range(m2) for j in range(m2))
        assert np.linalg.eigvalsh(J).min() > -1e-12
        r = np.outer(f, f.conj()); out = N(r)
        assert abs(np.trace(out) - 1) < 1e-12 and abs(np.linalg.eigvalsh(out - np.eye(d2) / d2)).sum() >= e2 / 10 - 1e-12
        s = unit(m2); xx = unit(d2); cc = abs(np.vdot(f, s)) ** 2
        assert abs(d2 * np.vdot(xx, N(np.outer(s, s.conj())) @ xx).real - (1 + e2 * cc * np.vdot(xx, Gs @ xx).real)) < 1e-12
print("4 ok: channel CPTP, diamond >= eps/10, step ratio 1 + eps c x'Gx")
# 5. ancilla: identity (1) sum_f w_f w_f^dag = a I, martingale identity, Lambda' <= (kappa a/d) I, Haar averages of c_f
def haar_u(n):
    q, r = np.linalg.qr(rng.normal(size=(n, n)) + 1j * rng.normal(size=(n, n))); return q * (np.diag(r) / abs(np.diag(r)))
for d2, m2, k in ((3, 4, 3), (4, 3, 5), (2, 6, 4)):
    psi = rng.normal(size=(m2, k)) + 1j * rng.normal(size=(m2, k)); psi /= np.linalg.norm(psi)   # psi[a, b]
    rhoB = psi.T @ psi.conj()                                                          # Tr_A |psi><psi|
    F = haar_u(d2 * k)                                                                 # orthonormal basis f of C^d (x) C^k, omega_f = 1
    def stats(phi):
        v = phi.conj() @ psi                                                           # v = (<phi| (x) I) psi
        W, cs, X = [], [], []
        for j in range(d2 * k):
            f = F[:, j].reshape(d2, k); w = f @ v.conj(); q = np.vdot(F[:, j], np.kron(np.eye(d2), rhoB) @ F[:, j]).real
            W.append(w); cs.append(np.vdot(w, w).real / q); X.append(q / d2)
        return v, np.array(W), np.array(cs), np.array(X)
    phi = unit(m2); v, W, cs, p0 = stats(phi); a = np.vdot(v, v).real
    assert abs(p0.sum() - 1) < 1e-12 and cs.max() <= 1 + 1e-12 and abs(np.vdot(phi, (psi @ psi.conj().T) @ phi).real - a) < 1e-12
    assert np.allclose(sum(np.outer(w, w.conj()) for w in W), a * np.eye(d2))
    assert np.allclose(sum(p * c * np.outer(w, w.conj()) / np.vdot(w, w).real for p, c, w in zip(p0, cs, W)), a / d2 * np.eye(d2))
    kap = np.median(cs); Lp = sum(p * c * c * np.outer(w, w.conj()) / np.vdot(w, w).real for p, c, w in zip(p0, cs, W) if c <= kap)
    assert np.linalg.eigvalsh(kap * a / d2 * np.eye(d2) - Lp).min() > -1e-12
    # alternative probabilities = p0 (1 + eps c x'Gx) for the bipartite output
    Gs = gue0(d2)[0]; e2 = 0.05
    out = np.kron(np.eye(d2) / d2, rhoB) + e2 / d2 * np.kron(Gs, np.outer(v, v.conj()))
    for j in range(d2 * k):
        w = W[j]; x = w / np.linalg.norm(w)
        assert abs(np.vdot(F[:, j], out @ F[:, j]).real - p0[j] * (1 + e2 * cs[j] * np.vdot(x, Gs @ x).real)) < 1e-12
    # Haar averages over phi for fixed outcomes: E c^2 <= 2/m^2, E c^4 <= 24/m^4
    S2, S4 = np.zeros(d2 * k), np.zeros(d2 * k); T = 20000
    for _ in range(T):
        _, _, c_, _ = stats(unit(m2)); S2 += c_ ** 2; S4 += c_ ** 4
    assert (S2 / T).max() <= 2 / (m2 * (m2 + 1)) * 1.05 and (S4 / T).max() <= 24 / m2 ** 4 * 1.05
print("5 ok: ancilla identity (1), martingale identity, Lambda' bound, step ratio, Haar averages of c_f")
