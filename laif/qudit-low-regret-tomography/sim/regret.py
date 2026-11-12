# Low-regret pure-state tomography with two-outcome rank-one projectors (algorithm of the README).
# Usage: python regret.py d_list T_list [runs] [mode]   mode = practical (default) or proof
import sys
import numpy as np


def haar(d, rng):
    v = rng.normal(size=d) + 1j * rng.normal(size=d)
    return v / np.linalg.norm(v)


def infid(a, b):
    return 1 - abs(np.vdot(a, b)) ** 2 / (np.vdot(a, a).real * np.vdot(b, b).real)


class Oracle:
    """T copies of psi; meas(phi, n) measures n copies with the projector onto phi."""

    def __init__(self, psi, T, rng):
        self.psi, self.T, self.rng, self.used, self.reg = psi, T, rng, 0, 0.0

    def meas(self, phi, n):
        n = min(n, self.T - self.used)
        if n <= 0:
            return 0, 0
        q = min(max(abs(np.vdot(phi, self.psi)) ** 2, 0.0), 1.0)
        self.used += n
        self.reg += n * (1 - q)  # expected regret of these copies
        return self.rng.binomial(n, q), n


def warm_once(o, d, N2):
    """one warm-up run: index j ~ p_j by rejection, then the four-phase star around j."""
    for _ in range(8 * d):
        j = int(o.rng.integers(d))
        e = np.zeros(d, complex); e[j] = 1
        k, n = o.meas(e, 1)
        if n == 0:
            return None
        if k == 1:
            break
    else:
        return None
    z = np.zeros(d, complex)
    k, n = o.meas(e, N2); z[j] = k / max(n, 1)
    for l in range(d):
        if l == j:
            continue
        qh = []
        for eta in (0, np.pi / 2, np.pi, 3 * np.pi / 2):
            v = np.zeros(d, complex); v[j] = 1; v[l] = np.exp(1j * eta); v /= np.sqrt(2)
            k, n = o.meas(v, N2); qh.append(k / max(n, 1))
        z[l] = (qh[0] - qh[2]) / 2 + 1j * (qh[1] - qh[3]) / 2  # estimates conj(psi_j) psi_l
    nz = np.linalg.norm(z)
    return z / nz if nz > 0 else None


def select(cands, r):
    """a candidate with more than half of all candidates within angle 2r."""
    ang = lambda a, b: np.arccos(min(1.0, abs(np.vdot(a, b))))
    L = len(cands)
    for c in cands:
        if c is not None and sum(1 for b in cands if b is not None and ang(c, b) <= 2 * r) > L / 2:
            return c
    good = [c for c in cands if c is not None]
    return good[0] if good else None


def run(d, T, rng, C2, Lw, A, B, eps0=1 / 16):
    psi = haar(d, rng); o = Oracle(psi, T, rng)
    x = np.log(T * (np.log2(T) + 2))
    r = np.arcsin(np.sqrt(eps0)) / 3
    cands = [warm_once(o, d, int(np.ceil(C2 * d))) for _ in range(Lw)]
    c = select(cands, r)
    if c is None:
        c = np.eye(d, dtype=complex)[0]
    warm = (o.used, o.reg, infid(c, psi))
    eps, ok = eps0, infid(c, psi) <= eps0
    while o.used < T:
        s = np.sqrt(eps); N = int(np.ceil((A * (d - 1) + B * x) / eps))
        Q = np.linalg.qr(np.column_stack([c, np.eye(d, dtype=complex)[:, :d]]))[0][:, 1:d]
        Q = Q - np.outer(c, c.conj() @ Q)  # orthonormal basis of the complement of c
        xh = np.zeros(d, complex)
        for jj in range(d - 1):
            w = Q[:, jj]
            for ph in (1, 1j):
                kp, n1 = o.meas(np.cos(s) * c + np.sin(s) * ph * w, N)
                km, n2 = o.meas(np.cos(s) * c - np.sin(s) * ph * w, N)
                if n1 == 0 or n2 == 0:
                    continue
                xh += (kp / n1 - km / n2) / (2 * np.sin(2 * s)) * ph * w
        if o.used >= T and (n1 == 0 or n2 == 0):
            break
        c = c + xh; c /= np.linalg.norm(c); eps /= 2
        ok = ok and infid(c, psi) <= eps
    return o.reg, warm, ok


if __name__ == "__main__":
    runs = int(sys.argv[3]) if len(sys.argv) > 3 else 20
    mode = sys.argv[4] if len(sys.argv) > 4 else "practical"
    # proof constants: N2 = 750 d, Lw from the median bound, N = (458 (d-1) + 71 x)/eps
    pars = dict(C2=750, A=458, B=71) if mode == "proof" else dict(C2=16, A=3, B=0.5)
    rng = np.random.default_rng(1)
    for d in [int(v) for v in sys.argv[1].split(",")]:
        for T in [int(float(v)) for v in sys.argv[2].split(",")]:
            x = np.log(T * (np.log2(T) + 2))
            Lw = int(np.ceil(8.1 * x)) if mode == "proof" else 3
            R = [run(d, T, rng, Lw=Lw, **pars) for _ in range(runs)]
            regs = np.array([q[0] for q in R]); okf = np.mean([q[2] for q in R])
            wr = np.mean([q[1][1] for q in R]); wf = np.mean([q[1][2] for q in R])
            print(f"{mode} d={d:3d} T={T:9d} regret mean {regs.mean():10.1f} max {regs.max():10.1f}"
                  f"  mean/(d^2 ln T) {regs.mean() / (d * d * np.log(T)):6.2f}  warm-up regret {wr:9.1f}"
                  f" warm-up infid {wf:.4f}  all epochs on track {okf:.2f}", flush=True)
            if mode == "proof":
                assert okf == 1.0
