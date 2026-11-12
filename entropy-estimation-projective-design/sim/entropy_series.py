# Checks for the power-series estimator of entropy near I/d from a projective 2-design, with asserts.
#  (1) exact second moments of the shifted snapshot Y = (d+1)P - I - I/d under the design measure, for the stabilizer
#      2-designs on 1 and 2 qubits: E[Y (x) Y] = ((d+1)/d)(F - I (x) I/d), and E[Y C Y] <= ((d+1)/d) tr(C) I for C >= 0;
#  (2) the chain bound E|tr(Y_1 B_1 ... Y_j B_j)|^2 <= (1 + 1/d)^j prod_i ||B_i||_F^2, exactly by enumeration (j <= 3, d = 4)
#      and with the likelihood ratio d tr(rho P) <= 5/4 on the local ball;
#  (3) the estimator: risk of the degree-K batch estimator against the quadratic one, with uniformly random pure-state measurements,
#      and against the explicit bound of Theorem 1.
# python -I entropy_series.py
import itertools
import math
import numpy as np

rng = np.random.default_rng(1)


def stabilizer_states(q):
    """All stabilizer states on q = 1, 2 qubits as unit vectors (up to phase)."""
    d = 2 ** q
    if q == 1:
        s = 1 / math.sqrt(2)
        return [np.array(v, dtype=complex) for v in
                ([1, 0], [0, 1], [s, s], [s, -s], [s, 1j * s], [s, -1j * s])]
    out = []
    # two-qubit stabilizer states: amplitudes in {0, +-1, +-i} on supports of size 1, 2, 4 (affine), normalized
    vals = [0, 1, -1, 1j, -1j]
    seen = []
    one = stabilizer_states(1)
    cand = [np.kron(a, b) for a in one for b in one]
    # entangled ones: (|0>|a> + w |1>|b>)/sqrt2 with a, b orthogonal one-qubit stabilizer pairs, w in {1, -1, i, -i}
    for a, b in itertools.product(one, one):
        if abs(np.vdot(a, b)) < 1e-9:
            for w in (1, -1, 1j, -1j):
                cand.append((np.kron([1, 0], a) + w * np.kron([0, 1], b)) / math.sqrt(2))
    for v in cand:
        if all(abs(abs(np.vdot(u, v)) - 1) > 1e-9 for u in seen):
            seen.append(v)
    return seen


def proj(v):
    return np.outer(v, v.conj())


for q, count in ((1, 6), (2, 60)):
    St = stabilizer_states(q)
    d = 2 ** q
    assert len(St) == count, (q, len(St))
    I = np.eye(d)
    Ys = [(d + 1) * proj(v) - I - I / d for v in St]
    # 2-design check: average of P (x) P equals 2 Pi_sym / (d (d+1))
    F = np.zeros((d * d, d * d))
    for i in range(d):
        for j in range(d):
            F[i * d + j, j * d + i] = 1
    PP = sum(np.kron(proj(v), proj(v)) for v in St) / len(St)
    assert np.allclose(PP, (np.eye(d * d) + F) / (d * (d + 1)))
    YY = sum(np.kron(Y, Y) for Y in Ys) / len(Ys)
    assert np.allclose(YY, (d + 1) / d * (F - np.eye(d * d) / d))
    for _ in range(20):
        G = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d))
        C = G @ G.conj().T
        YCY = sum(Y @ C @ Y for Y in Ys) / len(Ys)
        assert np.allclose(YCY, (d + 1) / d * (np.trace(C).real * I - C / d))
        gap = (d + 1) / d * np.trace(C).real * I - YCY
        assert np.linalg.eigvalsh(gap).min() > -1e-9
    print(f"d = {d}: stabilizer 2-design, E[Y (x) Y] and E[Y C Y] identities hold")

    # (2) chain bound, exactly over all tuples, with random B_i and with the reweighting by a local state
    for j in (1, 2, 3):
        if d == 2 and j == 3:
            pass
        for trial in range(3):
            Bs = []
            for _ in range(j):
                G = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d))
                Bs.append(G)
            bound = (1 + 1 / d) ** j * np.prod([np.linalg.norm(B) ** 2 for B in Bs])
            H = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d)); H = H + H.conj().T
            H -= np.trace(H) / d * I; H *= 1 / (4 * d) / np.abs(np.linalg.eigvalsh(H)).max()
            rho = I / d + H
            w = [d * np.vdot(v, rho @ v).real for v in St]
            assert max(w) <= 1.25 + 1e-12 and min(w) >= 0.75 - 1e-12
            tot_u = tot_r = 0.0
            for idx in itertools.product(range(len(St)), repeat=j):
                M = np.eye(d, dtype=complex)
                for a, B in zip(idx, Bs):
                    M = M @ Ys[a] @ B
                val = abs(np.trace(M)) ** 2
                tot_u += val
                tot_r += val * np.prod([w[a] for a in idx])
            tot_u /= len(St) ** j
            tot_r /= len(St) ** j
            assert tot_u <= bound * (1 + 1e-9), (d, j, tot_u, bound)
            assert tot_r <= 1.25 ** j * bound * (1 + 1e-9)
        print(f"d = {d}, j = {j}: chain bound holds for all tuples (ratio at last trial {tot_u / bound:.3f})")


# (3) estimators with uniformly random pure-state measurements
def series_coef(k):
    return (-1) ** k / (k * (k - 1))


def entropy(rho):
    ev = np.linalg.eigvalsh(rho)
    return float(-(ev * np.log(ev)).sum())


def sample_Y(rho, n, d):
    """n shifted snapshots from the uniform pure-state measurement: density d<psi|rho|psi> w.r.t. the uniform measure, by rejection (ratio <= 5/4)."""
    out = []
    got = 0
    while got < n:
        m = int((n - got) * 1.4) + 16
        g = rng.normal(size=(m, d)) + 1j * rng.normal(size=(m, d))
        g /= np.linalg.norm(g, axis=1, keepdims=True)
        p = d * np.einsum("mi,ij,mj->m", g.conj(), rho, g).real / 1.25
        keep = g[rng.random(m) < p]
        out.append(keep)
        got += len(keep)
    return np.concatenate(out)[:n]


def batch_mean_Y(V, d):
    # mean of (d+1)|v><v| - I - I/d over the rows of V
    return (d + 1) * (V.T @ V.conj()) / len(V) - (1 + 1 / d) * np.eye(d)


def estimators(V, d, K):
    n = len(V)
    est = {}
    S = math.log(d)
    quad = None
    for k in range(2, K + 1):
        m = n // k
        Hs = [batch_mean_Y(V[b * m:(b + 1) * m], d) for b in range(k)]
        M = np.eye(d, dtype=complex)
        for Hb in Hs:
            M = M @ Hb
        S -= series_coef(k) * d ** (k - 1) * np.trace(M).real
        if k == 2:
            quad = S
    clip = lambda x: min(math.log(d), max(0.0, x))
    return clip(quad), clip(S)


def theorem_bound(d, n, r, K):
    """Explicit risk bound of Theorem 1 (sum of standard deviations plus the remainder, squared)."""
    a = 15 / 8                                  # (5/4)(1 + 1/d) with d >= 2
    sd = 0.0
    for k in range(2, K + 1):
        v = sum(math.comb(k, c) * (a / (n // k)) ** c * d ** c * r ** (2 * (k - c)) for c in range(1, k + 1))
        sd += d ** (k - 1) / (k * (k - 1)) * math.sqrt(v)
    rem = sum((d * r) ** k / (k * (k - 1)) for k in range(K + 1, 200))
    return (sd + rem) ** 2


for d, n, reps in ((4, 40000, 300), (8, 160000, 100), (4, 1000000, 60)):
    r = 1 / (4 * d)
    ev = np.full(d, r / (d - 1)); ev[-1] = -r                # traceless, operator norm r
    U, _ = np.linalg.qr(rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d)))
    rho = U @ np.diag(1 / d + ev) @ U.conj().T
    S0 = entropy(rho)
    K = max(2, math.ceil(math.log(n / d, 16)) + 1)
    errs = np.array([[e - S0 for e in estimators(sample_Y(rho, n, d), d, K)] for _ in range(reps)])
    mse = (errs ** 2).mean(axis=0)
    se = (errs ** 2).std(axis=0) / math.sqrt(reps)
    rate = d ** 3 * r ** 2 / n + d ** 4 / n ** 2
    bnd = theorem_bound(d, n, r, K)
    bias_q = errs[:, 0].mean()
    # exact bias of the quadratic estimator before clipping: log d - (d/2) tr H^2 - S(rho)
    H = rho - np.eye(d) / d
    bq = math.log(d) - d / 2 * np.trace(H @ H).real - S0
    print(f"d = {d}, n = {n}, dr = 1/4, K = {K}: MSE quadratic {mse[0]:.2e} (bias {bias_q:+.2e}), "
          f"degree K {mse[1]:.2e} +- {se[1]:.1e}; rate d^3 r^2/n + d^4/n^2 = {rate:.2e}; Theorem 1 bound {bnd:.2e}; "
          f"squared bias of the quadratic estimator {bq ** 2:.2e}")
    assert mse[1] <= bnd + 3 * se[1]
    if bq ** 2 > 2 * rate:
        assert mse[1] + 3 * se[1] < mse[0]
print("entropy checks: ok")
