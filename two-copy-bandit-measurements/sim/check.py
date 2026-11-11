"""Checks for the note on two-copy measurements in the qubit bandit (README.md).

Instance: reward F = |0><0| on a qubit, arm rho = (I + ax X + az Z)/2, confusing set z >= zs.
f(M, s) = (1/2) D(P_rho2 || P_s2) per copy, for a POVM M on two copies; V2 = sup_M inf_s f(M, s).

1. The product spectral measurement gives K_inf, the maximally entangled basis gives 0.345 at the instance of [1].
2. The dual certificate: a measure mu on the circle C (z = zs, radius fixed by the one-excitation block) with
   the two stated moments, and the self-adjoint Y fixed by tangency at the product basis. Checks: the moments,
   Y self-adjoint, tr Y / 2 = K_inf, and max over unit psi of E_mu phi_s(psi) - <psi|Y|psi> <= 1e-10, which gives
   V2 <= K_inf. The measure is found by a linear program over 720 angles with cutting planes.
3. The same for further instances.
"""
import sys

import numpy as np
from scipy.optimize import linprog, minimize

I2 = np.eye(2); SX = np.array([[0, 1], [1, 0]]); SY = np.array([[0, -1j], [1j, 0]]); SZ = np.diag([1., -1.])
SEED = int(sys.argv[1]) if len(sys.argv) > 1 else 7
rng = np.random.default_rng(SEED)


def st(r):
    return (I2 + r[0] * SX + r[1] * SY + r[2] * SZ) / 2


def two(S):
    return np.einsum("kab,kcd->kacbd", S, S).reshape(len(S), 4, 4)


def nrm(A):
    return A / np.linalg.norm(A, axis=-1, keepdims=True)


def kl_rows(R2, S2, psis):  # p log(p/q) for each psi (rows) and each adversary state (columns)
    pp = np.real(np.einsum("ka,ab,kb->k", psis.conj(), R2, psis))
    qq = np.real(np.einsum("ka,jab,kb->kj", psis.conj(), S2, psis))
    return pp[:, None] * np.log(pp[:, None] / qq)


class Instance:
    def __init__(self, ax, az, zs):
        self.rho = st([ax, 0, az]); self.R2 = np.kron(self.rho, self.rho); self.zs = zs
        r00, r11, r01 = self.rho[0, 0].real, self.rho[1, 1].real, self.rho[0, 1].real
        s0, s1 = (1 + zs) / 2, (1 - zs) / 2
        self.kinf = r00 * np.log(r00 / s0) + r11 * np.log(r11 / s1)
        al, be = r00 / s0, r11 / s1
        self.Ew = r01 * np.log(al / be) / (al - be)                      # E sigma_01
        self.Ew2 = r01 ** 2 * 2 * np.log(al / be) / (al ** 2 - be ** 2)  # E sigma_01^2
        self.radius = 2 * np.sqrt(s0 * s1 * r01 ** 2 / (r00 * r11))     # transverse radius of C

    def f(self, V, pts):  # per-copy divergence for the measurement with rank-one elements V[i]^dagger V[i]
        S2 = two(np.array([st(t) for t in pts]))
        p = np.real(np.einsum("ia,ab,ib->i", V.conj(), self.R2, V))
        q = np.real(np.einsum("ia,kab,ib->ki", V.conj(), S2, V))
        return 0.5 * np.sum(np.where(p > 1e-15, p * np.log(np.maximum(p, 1e-300) / np.maximum(q, 1e-300)), 0), axis=1)

    def inner_min(self, V):  # inf over the confusing set: grid, then local refinement
        pts = [(r * np.cos(a), r * np.sin(a), z) for z in np.linspace(self.zs, 1, 15)
               for r in np.linspace(0, np.sqrt(max(1 - z * z, 0)) * 0.999, 30) for a in np.linspace(0, 2 * np.pi, 48, endpoint=False)]
        vals = self.f(V, pts); best = np.inf
        for i in np.argsort(vals)[:5]:
            def obj(u):
                z = self.zs + (1 - self.zs) / (1 + np.exp(-np.clip(u[2], -50, 50)))
                rm = np.sqrt(1 - z * z) * 0.99999; rad = rm * np.tanh(np.hypot(u[0], u[1])); a = np.arctan2(u[1], u[0])
                return self.f(V, [(rad * np.cos(a), rad * np.sin(a), z)])[0]
            x, y, z = pts[i]; z = min(max(z, self.zs + 1e-4), 1 - 1e-4); rm = np.sqrt(1 - z * z) * 0.99999
            t = np.arctanh(min(np.hypot(x, y) / rm, 0.999)); a = np.arctan2(y, x)
            u0 = [t * np.cos(a) + 1e-6, t * np.sin(a), np.log((z - self.zs) / (1 - z))]
            best = min(best, minimize(obj, u0, method="Nelder-Mead", options=dict(xatol=1e-10, fatol=1e-13, maxiter=5000)).fun)
        return best

    def certificate(self, final, na=720):
        ang = np.linspace(-np.pi, np.pi, na, endpoint=False)
        pts = [(self.radius * np.cos(a), self.radius * np.sin(a), self.zs) for a in ang]
        S2 = two(np.array([st(t) for t in pts])); p = np.real(np.diag(self.R2)); q = np.real(np.diag(S2[0]))
        Ys = np.zeros((na, 4, 4), complex)
        for i in range(4):  # tangency at the product basis vector e_i
            Ys[:, :, i] = (np.log(p[i] / q[i]) + 1) * self.R2[:, i] - (p[i] / q[i]) * S2[:, :, i]
        w = (np.array(pts)[:, 0] - 1j * np.array(pts)[:, 1]) / 2
        A_eq = np.vstack([np.ones(na), w.real, w.imag, (w ** 2).real, (w ** 2).imag])
        b_eq = [1, self.Ew, 0, self.Ew2, 0]

        def rows(psis):
            return kl_rows(self.R2, S2, psis) - np.real(np.einsum("ka,jab,kb->kj", psis.conj(), Ys, psis))

        cuts = [nrm(rng.normal(size=(2000, 4)) + 1j * rng.normal(size=(2000, 4)))]
        for i in range(4):
            for eps in (1e-3, 1e-2, 0.1, 0.3):
                cuts.append(nrm(np.eye(4)[i] + eps * (rng.normal(size=(150, 4)) + 1j * rng.normal(size=(150, 4)))))
        PS = np.vstack(cuts)
        for _ in range(40):
            res = linprog(np.r_[np.zeros(na), 1], A_ub=np.hstack([rows(PS), -np.ones((len(PS), 1))]), b_ub=np.zeros(len(PS)),
                          A_eq=np.hstack([A_eq, np.zeros((5, 1))]), b_eq=b_eq, bounds=[(0, None)] * na + [(None, None)], method="highs")
            lam = res.x[:na]
            lam = (lam + lam[(-np.arange(na)) % na]) / 2  # mirror image y -> -y, same violation by symmetry
            v, new = self.violation(lam, rows, 200)
            if v < 1e-10:
                v, new = self.violation(lam, rows, final)  # stop only when the large search also passes
                if v < 1e-10:
                    break
            PS = np.vstack([PS, new])
        Y = np.einsum("j,jab->ab", lam, Ys)
        return ang, lam, Y, v, A_eq @ lam - b_eq, rows

    def violation(self, lam, rows, starts):
        act = lam > 1e-13

        def g(x):
            psi = x[:4] + 1j * x[4:]
            return -(rows(nrm(psi)[None])[0, act] @ lam[act])
        seeds = [rng.normal(size=8) for _ in range(starts)]
        for i in range(4):
            seeds += [np.eye(8)[i] + 0.05 * rng.normal(size=8) for _ in range(starts // 8)]
        out = sorted(((-r.fun, r.x[:4] + 1j * r.x[4:]) for r in (minimize(g, s, method="BFGS", options=dict(gtol=1e-11)) for s in seeds)),
                     key=lambda t: -t[0])
        return out[0][0], nrm(np.array([o[1] for o in out[:30]]))


def check_baselines():
    I = Instance(0.9, 0.0, 0.9)
    me = np.array([[1, 0, 0, 1], [1, 0, 0, -1], [0, 1, 1, 0], [0, 1, -1, 0]]) / np.sqrt(2) + 0j
    a, b = I.inner_min(np.eye(4) + 0j), I.inner_min(me)
    assert abs(a - I.kinf) < 1e-8 and abs(b - 0.34506) < 1e-4
    print(f"1. instance of [1]: K_inf = {I.kinf:.6f}; product spectral {a:.6f}; maximally entangled basis {b:.5f}", flush=True)


def check_certificate(ax, az, zs, label, starts=1500):
    global rng
    rng = np.random.default_rng(SEED)  # each instance from the same seed, so it can be rerun alone
    I = Instance(ax, az, zs)
    ang, lam, Y, v, mom, rows = I.certificate(starts)
    v2, _ = I.violation(lam, rows, starts)  # a fresh search
    herm = np.abs(Y - Y.conj().T).max(); tr = np.real(np.trace(Y)) / 2
    ok = herm < 1e-9 and abs(tr - I.kinf) < 1e-9 and np.abs(mom).max() < 1e-8 and max(v, v2) < 1e-10
    assert ok, (herm, tr - I.kinf, np.abs(mom).max(), v, v2)
    sup = np.degrees(ang[lam > 1e-6])
    print(f"   {label}: arm ({ax}, 0, {az}), zs = {zs}: K_inf = {I.kinf:.6f}, circle radius {I.radius:.6f}, "
          f"moments ok, tr Y / 2 = K_inf, max violation {max(v, v2):.1e}, {len(sup)} atoms", flush=True)


if __name__ == "__main__":
    check_baselines()
    print("2. dual certificate at the instance of [1]:", flush=True)
    check_certificate(0.9, 0.0, 0.9, "instance of [1]", starts=3000)
    print("3. further instances:", flush=True)
    for ax, az, zs in [(0.6, 0.0, 0.9), (0.9, 0.3, 0.9), (0.5, -0.5, 0.5), (0.99, 0.0, 0.5), (0.3, 0.2, 0.95)]:
        check_certificate(ax, az, zs, "instance")
    print("all checks passed")
