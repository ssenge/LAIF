# Budgeted phases: low-regret pure-state tomography without the d log^2 T term (algorithm of the README, Theorem 3).
# Usage: python regret2.py d_list T_list [runs] [mode]   mode = practical (default) or proof
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


def warm_run(o, d, N2):
    """one warm-up run (rejection, then four-phase star); returns a unit vector."""
    for _ in range(8 * d):
        j = int(o.rng.integers(d)); e = np.zeros(d, complex); e[j] = 1
        k, n = o.meas(e, 1)
        if n == 0:
            return None
        if k == 1:
            break
    else:
        return np.eye(d, dtype=complex)[0]
    z = np.zeros(d, complex)
    k, n = o.meas(e, N2); z[j] = k / max(n, 1)
    for l in range(d):
        if l == j:
            continue
        qh = []
        for eta in (0, np.pi / 2, np.pi, 3 * np.pi / 2):
            v = np.zeros(d, complex); v[j] = 1; v[l] = np.exp(1j * eta); v /= np.sqrt(2)
            k, n = o.meas(v, N2); qh.append(k / max(n, 1))
        z[l] = (qh[0] - qh[2]) / 2 + 1j * (qh[1] - qh[3]) / 2
    nz = np.linalg.norm(z)
    return z / nz if nz > 0 else np.eye(d, dtype=complex)[0]


def phase(o, c, eps, N, B):
    """one phase; pairs are measured alternately, one copy at a time, in blocks.
    Returns ('done', new c) or ('abort', rate) or ('end', None)."""
    d = len(c); s = np.sqrt(eps)
    Q = np.linalg.qr(np.column_stack([c, np.eye(d, dtype=complex)]))[0][:, 1:d]
    Q = Q - np.outer(c, c.conj() @ Q)
    psi = o.psi; zeros = 0; used0 = o.used; xh = np.zeros(d, complex)
    for jj in range(d - 1):
        for ph in (1, 1j):
            u = ph * Q[:, jj]
            vp, vm = np.cos(s) * c + np.sin(s) * u, np.cos(s) * c - np.sin(s) * u
            qp, qm = abs(np.vdot(vp, psi)) ** 2, abs(np.vdot(vm, psi)) ** 2
            # N alternating pairs (+, -); pair types (+ outcome, - outcome) are i.i.d. multinomial
            n_left = o.T - o.used
            P = min(N, n_left // 2)
            if P <= 0:
                return "end", None
            pr = np.array([(1 - qp) * (1 - qm), (1 - qp) * qm, qp * (1 - qm), qp * qm])
            pr = np.clip(pr, 0, None); pr /= pr.sum()
            cnt = o.rng.multinomial(P, pr)  # types 00, 01, 10, 11 (0 = zero outcome)
            zb = 2 * cnt[0] + cnt[1] + cnt[2]
            if zeros + zb >= B:  # budget reached inside this block: locate the pair by bisection
                need = B - zeros; off = 0; Pc, cc = P, cnt
                while Pc > 1:
                    h = Pc // 2
                    first = o.rng.multivariate_hypergeometric(cc, h)
                    zf = 2 * first[0] + first[1] + first[2]
                    if zf >= need:
                        Pc, cc = h, first
                    else:
                        need -= zf; off += h; Pc, cc = Pc - h, cc - first
                typ = int(np.argmax(cc))  # the single pair: + zero if typ in (0, 1), - zero if typ in (0, 2)
                stop = 2 * off + (1 if (need == 1 and typ in (0, 1)) else 2)
                o.used += stop; o.reg += (stop + 1) // 2 * (1 - qp) + stop // 2 * (1 - qm)
                return "abort", B / (o.used - used0)
            o.used += 2 * P; o.reg += P * (2 - qp - qm)
            zeros += int(zb)
            if P < N:
                return "end", None
            kp = int(cnt[2] + cnt[3]); km = int(cnt[1] + cnt[3])
            xh += (kp / N - km / N) / (2 * np.sin(2 * s)) * u
    c = c + xh
    return "done", c / np.linalg.norm(c)


def run(d, T, rng, C, theta, C2, eps0=1 / 128):
    psi = haar(d, rng); o = Oracle(psi, T, rng)
    level, c = -1, None; phases = warmups = aborts = 0
    while o.used < T:
        phases += 1
        if level < 0:
            warmups += 1; c = warm_run(o, d, int(np.ceil(C2 * d)))
            if c is None:
                break
            level = 0; continue
        eps = eps0 * 2.0 ** -level; N = int(np.ceil(C * d / eps)); n = 4 * (d - 1) * N
        B = int(np.ceil(theta * eps * n))
        res, val = phase(o, c, eps, N, B)
        if res == "done":
            c = val; level += 1
        elif res == "abort":
            aborts += 1; rho = val
            ok = [k for k in range(level + 1) if eps0 * 2.0 ** -k >= 2 * rho]
            level = max(ok) if ok else -1
        else:
            break
    return o.reg, phases, warmups, aborts, infid(c, psi) if c is not None else 1.0


if __name__ == "__main__":
    runs = int(sys.argv[3]) if len(sys.argv) > 3 else 20
    mode = sys.argv[4] if len(sys.argv) > 4 else "practical"
    pars = dict(C=40, theta=3.5, C2=500) if mode == "proof" else dict(C=4, theta=3, C2=16)
    rng = np.random.default_rng(2)
    for d in [int(v) for v in sys.argv[1].split(",")]:
        for T in [int(float(v)) for v in sys.argv[2].split(",")]:
            R = [run(d, T, rng, **pars) for _ in range(runs)]
            reg = np.array([r[0] for r in R])
            print(f"{mode} d={d:3d} T={T:.0e} regret mean {reg.mean():11.1f} max {reg.max():11.1f}"
                  f"  mean/(d^2 ln T) {reg.mean() / (d * d * np.log(T)):8.2f}  phases {np.mean([r[1] for r in R]):6.1f}"
                  f" warm-ups {np.mean([r[2] for r in R]):4.2f} aborts {np.mean([r[3] for r in R]):5.2f}"
                  f" final infid {np.mean([r[4] for r in R]):.2e}", flush=True)
