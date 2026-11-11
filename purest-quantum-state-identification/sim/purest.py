# Purest-state identification with single-copy measurements in random bases.
# Checks, with asserts:
#  (1) the moment identities E_U S = (1 + P)/(d + 1) and E_U sum_x p_x^3 = (1 + 3P + 2 tr rho^3)/((d + 1)(d + 2));
#  (2) the basis variance bound Var_U S <= 48 d / ((d^2 - 1)(d + 1)(d + 2)) (Lemma 1) on several spectra;
#  (3) the block variance bound V_m = 64/d^3 + 24/(m d^2) + 8/(m^2 d) (Lemma 2) and unbiasedness of the block statistic;
#  (4) the elimination algorithm (scaled-down constants) returns the purest state, and its copy count per arm
#      follows sqrt(d)/Delta + 1/Delta^2: at a fixed gap the count grows like sqrt(d), not like d.
# python -I purest.py
import sys
import numpy as np


def frame(d, r, rng):
    """r orthonormal columns of a Haar unitary (the rows of U^dagger restricted to the support of rho)."""
    z = (rng.standard_normal((d, r)) + 1j * rng.standard_normal((d, r))) / np.sqrt(2)
    q, rr = np.linalg.qr(z)
    return q * (np.diag(rr) / np.abs(np.diag(rr)))


def probs(lam, d, rng):
    """Outcome distribution p_x = <x|U rho U^dagger|x> for rho = diag(lam) (support size r) and Haar U."""
    lam = np.asarray(lam, float)
    if np.allclose(lam, 1.0 / d) and len(lam) == d:
        return np.full(d, 1.0 / d)
    q = frame(d, len(lam), rng)
    p = (np.abs(q) ** 2) @ lam
    return p / p.sum()


def block(lam, d, m, rng):
    """One block: a fresh Haar basis, m copies, the unbiased collision statistic g."""
    c = rng.multinomial(m, probs(lam, d, rng))
    return float((c * (c - 1)).sum()) / (m * (m - 1))


def purity(lam):
    return float(np.sum(np.asarray(lam) ** 2))


def Vm(d, m):
    return 64 / d ** 3 + 24 / (m * d ** 2) + 8 / (m ** 2 * d)


def spectra(d, rng):
    w = rng.exponential(size=d); w /= w.sum()
    out = {"pure": [1.0], "rank2": [0.5, 0.5], "skew2": [0.8, 0.2], "rank4": [0.25] * 4,
            "random": list(w), "mixed": [1.0 / d] * d}
    return {k: v for k, v in out.items() if len(v) <= d}


def check_moments(rng):
    for d in [2, 4, 8, 16, 32]:
        for name, lam in spectra(d, rng).items():
            n = 40000
            S = np.empty(n); S3 = np.empty(n)
            for k in range(n):
                p = probs(lam, d, rng)
                S[k] = np.sum(p ** 2); S3[k] = np.sum(p ** 3)
            P = purity(lam); P3 = float(np.sum(np.asarray(lam) ** 3))
            mS, m3 = (1 + P) / (d + 1), (1 + 3 * P + 2 * P3) / ((d + 1) * (d + 2))
            se = S.std() / np.sqrt(n) + 1e-12; se3 = S3.std() / np.sqrt(n) + 1e-12
            assert abs(S.mean() - mS) <= 5 * se + 1e-12, (d, name, S.mean(), mS)
            assert abs(S3.mean() - m3) <= 5 * se3 + 1e-12, (d, name)
            vb = 48 * d / ((d * d - 1) * (d + 1) * (d + 2))
            # sample variance has relative error about sqrt(2/n); allow 5 percent slack
            assert S.var() <= 1.05 * vb, (d, name, S.var(), vb)
            print(f"  d={d:3d} {name:7s}: Var_U S = {S.var():.3e}, bound {vb:.3e}, ratio {S.var() / vb:.3f}")


def check_block(rng):
    for d, m in [(4, 2), (8, 3), (16, 4), (16, 16), (64, 8), (64, 64)]:
        for name, lam in spectra(d, rng).items():
            n = 30000
            g = np.array([block(lam, d, m, rng) for _ in range(n)])
            mu = (1 + purity(lam)) / (d + 1)
            assert abs(g.mean() - mu) <= 5 * g.std() / np.sqrt(n) + 1e-12, (d, m, name)
            assert g.var() <= 1.05 * Vm(d, m), (d, m, name, g.var(), Vm(d, m))
        print(f"  d={d:3d} m={m:3d}: block mean and variance bound hold on all spectra")


def eliminate(states, d, delta, rng, scale):
    """Successive elimination in epochs eps = 2^-l. scale < 1 shrinks the number of blocks per group (the
    constant 64 of the second-moment bound); scale = 1 is the algorithm of the proof."""
    K = len(states)
    active = list(range(K)); copies = np.zeros(K); l = 0
    while len(active) > 1:
        l += 1
        eps = 2.0 ** -l
        m = int(min(d, max(2, np.ceil(np.sqrt(d) / eps))))
        B = int(np.ceil(scale * 64 * (d + 1) ** 2 * Vm(d, m) / eps ** 2))
        G = int(np.ceil(8 * np.log(4 * K * l * l / delta) * min(1.0, 4 * scale)))
        w = {}
        for i in active:
            means = [np.mean([block(states[i], d, m, rng) for _ in range(B)]) for _ in range(G)]
            w[i] = np.median(means); copies[i] += G * B * m
        top = max(w.values())
        active = [i for i in active if w[i] >= top - eps / (2 * (d + 1))]
    return active[0], copies


def check_algorithm(rng):
    # arm 0 is pure; the others have purity 1 - gap
    def state(P):                      # rank-2 spectrum (1 - a, a) with purity P >= 1/2
        a = (1 - np.sqrt(2 * P - 1)) / 2
        return [1 - a, a]
    rows = []
    for d in [16, 64, 256, 1024]:
        gaps = [0.5, 0.5, 0.5]
        states = [[1.0]] + [state(1 - g) for g in gaps]
        ok = 0; cnt = []
        runs = 20
        for _ in range(runs):
            best, copies = eliminate(states, d, 0.1, rng, scale=1 / 16)
            ok += best == 0; cnt.append(copies.sum())
        rows.append((d, np.mean(cnt)))
        print(f"  d={d:5d}, gaps 0.5: correct {ok}/{runs}, mean copies {np.mean(cnt):9.0f}, "
              f"copies/sqrt(d) {np.mean(cnt) / np.sqrt(d):8.0f}", flush=True)
        assert ok >= runs - 2
    # copies grow like sqrt(d): the ratio between d = 1024 and d = 16 is near 8, far below 64
    ratio = rows[-1][1] / rows[0][1]
    assert ratio < 16, ratio
    print(f"  copies(d=1024)/copies(d=16) = {ratio:.2f} (sqrt ratio 8, linear ratio 64)")


def check_single_basis(rng):
    """Copies in ONE random basis needed to rank a pure state above a state of purity 1/2 with probability 0.9:
    the threshold m grows like sqrt(d) (the term sqrt(d)/Delta of Theorem 1)."""
    rows = []
    for d in [64, 256, 1024, 4096, 16384]:
        def win(m, trials=2000):
            return np.mean([block([1.0], d, m, rng) > block([0.5, 0.5], d, m, rng) for _ in range(trials)])
        m = 2
        while win(m) < 0.9:
            m = int(np.ceil(m * 1.25))
        rows.append((d, m))
        print(f"  d={d:5d}: m = {m:4d} copies per basis, m/sqrt(d) = {m / np.sqrt(d):.2f}", flush=True)
    big = [m / np.sqrt(d) for d, m in rows if d >= 1024]
    assert max(big) / min(big) < 1.25, big   # for d >= 1024, m/sqrt(d) is nearly constant
    for (d1, m1), (d2, m2) in zip(rows[2:], rows[3:]):
        assert m2 / m1 < 2.5, (d1, d2)       # a factor 4 in d costs about a factor 2 in m, not 4


if __name__ == "__main__":
    rng = np.random.default_rng(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
    print("moments and basis variance (Lemma 1):"); check_moments(rng)
    print("block statistic (Lemma 2):"); check_block(rng)
    print("elimination algorithm:"); check_algorithm(rng)
    print("one basis, gap 1/2:"); check_single_basis(rng)
    print("purest checks: ok")
