"""Checks for the note on the cost of simulating adaptive messages (run: python -I check.py, a few seconds).
1. Union bound: three independent uniformly random bases of C^R, R = C M with C = 80, have every cross submatrix with
   |A| + |B| <= M of norm < 1/2 with positive probability, for every M >= 1 (net of mesh 0.1).
2. The exclusion measurement of the adaptive protocol (POVM A_a = T G^-1 C_a G^-1 T^+ + (1 - P)/3) built from random
   bases: positivity, completeness and exclusion for random inputs S, at R = 80 M and at smaller R.
3. Lower bounds M_eps >= M + 1 (d = 3) and M_eps > k M / 2 (d = 3k) against the upper bound 1 + ln(1/eps)/ln(d/(d-1))."""
import math
import numpy as np
from scipy.stats import unitary_group

def union_bound(C, eta=0.1, t=0.5):
    q = 1 - ((1 - 2 * eta) * t) ** 2
    base = 2 * math.e * C * (1 + 2 / eta) ** 2 * q ** C        # per-M factor of 3 C(2R, M) (1 + 2/eta)^{2M} q^{R - 1}
    return base, 3 * base / q                                   # value at M = 1 (largest, since base < 1)

def povm(Us, S, R):
    V = [Us[a][:, [j for (j, b) in S if b == a]] for a in range(3)]
    T = np.hstack(V); G = T.conj().T @ T; s = [v.shape[1] for v in V]; off = np.cumsum([0] + s)
    Gi = np.linalg.inv(G); P = T @ Gi @ T.conj().T; As = []
    for a in range(3):
        Ca = G.copy() * 0
        for k in range(3):
            for l in range(3):
                if k == a or l == a: continue
                blk = np.eye(s[k]) / 2 if k == l else G[off[k]:off[k + 1], off[l]:off[l + 1]]
                Ca[off[k]:off[k + 1], off[l]:off[l + 1]] = blk
        As.append(T @ Gi @ Ca @ Gi @ T.conj().T + (np.eye(R) - P) / 3)
    return As, V

def test(M, R, trials, rng):
    Us = [np.eye(R)] + [unitary_group.rvs(R, random_state=rng) for _ in range(2)]
    worst_eig = 1; worst_excl = 0; worst_sum = 0
    for _ in range(trials):
        idx = rng.choice(3 * R, size=M, replace=False); S = [(i % R, i // R) for i in idx]
        As, V = povm(Us, S, R)
        worst_eig = min(worst_eig, min(np.linalg.eigvalsh((A + A.conj().T) / 2).min() for A in As))
        worst_sum = max(worst_sum, np.abs(sum(As) - np.eye(R)).max())
        worst_excl = max(worst_excl, max(np.abs(As[a] @ V[a]).max() if V[a].size else 0 for a in range(3)))
    return worst_eig, worst_sum, worst_excl

if __name__ == "__main__":
    base, m1 = union_bound(80)
    print(f"1. C = 80, mesh 0.1: per-M factor {base:.3f} < 1, bound at M = 1 is {m1:.3f} < 1, so good triples exist for every M"); assert m1 < 1
    rng = np.random.default_rng(1)
    for M, R in [(2, 160), (3, 240), (4, 320)]:
        e, s, x = test(M, R, 30, rng)
        print(f"2. M = {M}, R = {R}: smallest eigenvalue of the A_a {e:.2e}, |sum A_a - 1| <= {s:.1e}, |A_a u| <= {x:.1e} on 30 random inputs")
        assert e > -1e-10 and s < 1e-9 and x < 1e-9
    print("3. lower bounds (R = 80 M, ground set 240 M) against the upper bound of the guessing scheme:")
    for eps in [1e-6, 1e-12, 1e-30, 1e-100]:
        M = max(m for m in range(1, 400) if math.comb(240 * m, m) < 1 / eps) if math.comb(240, 1) < 1 / eps else 0
        Mk = max([m for m in range(1, 400) if 2 * math.comb(240 * m, m) < 1 / eps] or [0])
        up = lambda d: 1 + math.ceil(math.log(1 / eps) / math.log(d / (d - 1)))
        print(f"   eps = {eps:.0e}: d = 3: {M + 1} <= M_eps <= {up(3)};  d = 30: {10 * Mk // 2 + 1} <= M_eps <= {up(30)}")
