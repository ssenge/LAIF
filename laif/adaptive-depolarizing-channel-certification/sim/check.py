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
