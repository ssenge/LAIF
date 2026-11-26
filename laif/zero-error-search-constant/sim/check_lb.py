"""Checks for the lower bound E[rounds] >= (pi/4 + 1/2 - theta) / (2 theta_m), sin theta = 1/sqrt N, sin theta_m = sqrt(m/N),
for zero-error search of one marked item among N with at most m parallel queries per round (expected number of rounds).
State of a symmetrized algorithm: survival a and mean amplitude beta = |mean_y psi_y|; omega = arccos(beta / sqrt a);
potential Phi = a h(omega), h = K (c - omega) on [0, w*], K (c - 2 w* + omega) on [w*, pi/2], c = pi/4 + 1/2 - theta,
w* = pi/2 - theta/2, K = 1/(2 theta_m).
(1) Rotation lemma on random vectors: |mean'| >= sqrt(a) cos(omega + 2 theta_p) for psi'_y = (I - 2 Pi_y) psi_y with
    Pi_y = sum_{A contains y} P_A, {P_A} orthogonal, |A| <= m, p = mean |Pi_y mean|^2 / |mean|^2 <= m/N.
(2) The same through the exact one-round SOCP (all algorithms): |d omega| <= 2 theta_m.
(3) Stop condition h sin 2w + h' (cos^2 w - 1/N) <= 0 on (0, pi/2), for N = 2 .. 10^6, m = 1.
(4) Closed-form bound <= exact SDP optimum (bss.py), and the ratio to (pi/4) sqrt N tends to 1/2 + 1/pi.
(5) Along the optimal SDP trajectory: Phi_t - Phi_{t+1} <= a_t (query) and Phi does not drop at stops."""
import os
for _v in ("RAYON_NUM_THREADS", "OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "VECLIB_MAXIMUM_THREADS"): os.environ[_v] = "1"
import numpy as np
import warnings; warnings.filterwarnings("ignore")
import parallel, bss

from parallel import omega

def h(N, m, w):
    th = np.arcsin(1 / np.sqrt(N)); K = 1 / (2 * np.arcsin(np.sqrt(m / N))); c = np.pi / 4 + 0.5 - th; ws = np.pi / 2 - th / 2
    return np.where(w <= ws, K * (c - w), K * (c - 2 * ws + w))

def main():
    rng = np.random.default_rng(7)
    # (1)
    worst = np.inf
    for trial in range(300):
        N = int(rng.integers(2, 12)); m = int(rng.integers(1, N + 1)); D = int(rng.integers(N + 1, 40))
        psi = rng.normal(size=(N, D)) + 1j * rng.normal(size=(N, D))
        if trial % 2: psi = psi * 0.1 + rng.normal(size=D)            # nearly equal states (small omega)
        psi /= np.sqrt((np.abs(psi) ** 2).sum(1).mean())
        U = np.linalg.qr(rng.normal(size=(D, D)) + 1j * rng.normal(size=(D, D)))[0]
        lab = [frozenset(rng.choice(N, size=int(rng.integers(0, m + 1)), replace=False)) for _ in range(D)]
        Pi = [sum((np.outer(U[:, i], U[:, i].conj()) for i in range(D) if y in lab[i]), np.zeros((D, D))) for y in range(N)]
        mean = psi.mean(0); beta = np.linalg.norm(mean); w = np.arccos(min(1, beta))
        p = np.mean([np.linalg.norm(P @ mean) ** 2 for P in Pi]) / beta ** 2
        assert p <= m / N + 1e-12
        new = np.array([(np.eye(D) - 2 * Pi[y]) @ psi[y] for y in range(N)]).mean(0)
        tp = np.arcsin(np.sqrt(p)); slack = np.linalg.norm(new) - np.cos(min(np.pi, w + 2 * tp))
        assert slack >= -1e-10, (trial, slack); worst = min(worst, slack)
    print("(1) rotation lemma on 300 random families: ok, min slack %.2e" % worst, flush=True)
    # (2)
    for N, m in ((8, 1), (64, 1), (1024, 1), (16, 2), (64, 4), (256, 8)):
        tm = np.arcsin(np.sqrt(m / N)); r = 0
        for b in np.linspace(-1 / (N - 1), 1, 31):
            for s in (1, -1):
                bp = parallel.reach(N, m, 1.0, b, s)
                if bp is not None: r = max(r, abs(omega(N, 1, np.clip(bp, -1 / (N - 1), 1)) - omega(N, 1, b)) / (2 * tm))
        assert r <= 1 + 1e-4, (N, m, r)   # SOCP accuracy; the lemma itself is exact
    print("(2) one round of <= m parallel queries moves omega by at most 2 theta_m (SOCP, N <= 1024, m <= 8): ok", flush=True)
    # (3)
    for N in list(range(2, 40)) + [100, 1000, 10 ** 4, 10 ** 6]:
        th = np.arcsin(1 / np.sqrt(N)); ws = np.pi / 2 - th / 2
        w = np.concatenate([np.linspace(1e-9, np.pi / 2 - 1e-9, 200001), ws + np.linspace(-1e-4, 1e-4, 2001) * th])
        w = w[(w > 0) & (w < np.pi / 2)]
        hv = h(N, 1, w); hp = np.where(w <= ws, -1.0, 1.0) / (2 * th)
        assert (hv * np.sin(2 * w) + hp * (np.cos(w) ** 2 - 1 / N)).max() <= 1e-12, N
    print("(3) stop condition holds for N = 2..39, 100, 1e3, 1e4, 1e6", flush=True)
    # (4), (5)
    c0 = np.pi / 4 + 0.5
    for N, T in ((16, 24), (64, 36), (256, 60), (1024, 120)):
        val, a, d, b = bss.solve(N, T)
        th = np.arcsin(1 / np.sqrt(N)); lb = (c0 - th) / (2 * th)
        assert lb <= val + 1e-6, (N, lb, val)
        ok = True
        for t in range(T):
            if a[t] < 1e-7: break
            Phi = lambda aa, bb: aa * float(h(N, 1, omega(N, aa, bb)))
            bt1 = b[t + 1]; at1 = a[t + 1]
            # query: (a_t, b_t) -> (a_t, b_t+1); stop: (a_t, b_t+1) -> (a_t+1, b_t+1)
            ok &= Phi(a[t], b[t]) - Phi(a[t], bt1) <= a[t] * (1 + 1e-3) + 1e-6   # SDP solutions are accurate to about 1e-4
            if at1 > 1e-7: ok &= Phi(at1, bt1) >= Phi(a[t], bt1) - 1e-5
        assert ok, N
        print("(4,5) N=%5d: bound %.4f <= optimum %.4f; ratios %.5f, %.5f (1/2 + 1/pi = %.5f); potential steps ok"
              % (N, lb, val, lb / (np.pi / 4 * np.sqrt(N)), val / (np.pi / 4 * np.sqrt(N)), 0.5 + 1 / np.pi), flush=True)
    print("ok")


if __name__ == "__main__":
    main()
