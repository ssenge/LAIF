# Checks for the doubling learner of Gaussian unitaries G = D_r U_S, with asserts.
# Moments are propagated exactly (a Gaussian unitary acts affinely on the mean and by congruence on the covariance),
# and each empirical mean of N heterodyne samples is drawn from its exact law N(mean, (V + 1)/(2N)).
#  (1) coarse stage: symmetric coherent probes and the symplectic rounding S~ = S^ Q^-1, Q = sqrt(-Omega S^T Omega S^);
#  (2) doubling stages k = 1, 2, 4, ...: every input fed to G has mean photon number <= nin, the invariants
#      k ||log W|| <= gamma and ||b|| <= eta / (4 k e^gamma) hold, and the final bound
#      sqrt(72 m (n+1) ||W - 1||) + sqrt(2 (n' + 1)) ||r~ - r|| <= eps holds;
#  (3) the rotation example: 1/2 ||U_theta - id||_{diamond, n} >= sqrt(n theta / pi);
#  (4) a single-mode squeezer with ||S|| = z maps the vacuum to (z^2 + z^-2 - 2)/4 > 0 photons, below z^2 (0 + 1/2) - 1/2.
# python -I doubling.py
import math
import numpy as np
from scipy.linalg import expm, logm, sqrtm

rng = np.random.default_rng(7)


def omega(m):
    return np.kron(np.eye(m), np.array([[0.0, 1.0], [-1.0, 0.0]]))   # ordering (x1, p1, ..., xm, pm)


def proj_sp(K, Om):
    return (K + Om @ K.T @ Om) / 2


def random_symplectic(m, z):
    """S = O1 Z O2 with passive O1, O2 and single-mode squeezers, ||S|| <= z."""
    Om = omega(m)
    def passive():
        A = rng.normal(size=(m, m)) + 1j * rng.normal(size=(m, m))
        U, _ = np.linalg.qr(A)
        O = np.zeros((2 * m, 2 * m))
        O[0::2, 0::2] = U.real; O[0::2, 1::2] = -U.imag; O[1::2, 0::2] = U.imag; O[1::2, 1::2] = U.real
        return O
    s = rng.uniform(0, math.log(z), size=m)
    Z = np.diag(np.repeat(np.exp(s), 2) * np.tile([1, -1], m).astype(float) ** 0)
    Z = np.diag(np.ravel([[math.exp(t), math.exp(-t)] for t in s]))
    S = passive() @ Z @ passive()
    assert np.allclose(S.T @ Om @ S, Om) and np.linalg.norm(S, 2) <= z + 1e-9
    return S


def photons(mean, V):
    return (np.trace(V).real - len(mean)) / 4 + mean @ mean / 2


def opnorm(A):
    return np.linalg.norm(A, 2)


def gauss_norm_tail(n, delta):
    return math.sqrt(2 * math.log(1 / delta))


def run(m, z, nbar, nin, eps, delta):
    Om = omega(m); I = np.eye(2 * m)
    S = random_symplectic(m, z)
    r = rng.normal(size=2 * m) * 3.0                       # the displacement is not bounded in the problem
    eta = math.sqrt(nin / 2)
    gamma = min(0.25, nin / (5 * m))
    nprime = z * z * (nbar + m / 2)
    kA = 64 * m * (nbar + 1) * gamma / eps ** 2
    kB = z * eta * math.sqrt(nprime + 1) / (2 * math.sqrt(2) * eps)
    L = max(0, math.ceil(math.log2(max(kA, kB, 1))))
    dp = delta / (2 * L + 3)                                 # coarse stage and two events per doubling stage
    tail = 2 * math.sqrt(2 * m) + math.sqrt(2 * math.log(1 / dp))
    queries = 0
    maxph = 0.0

    def G_in(mean, V):
        nonlocal queries, maxph
        ph = photons(mean, V)
        maxph = max(maxph, ph)
        assert ph <= nin * (1 + 1e-12), (ph, nin)
        queries += 1
        return S @ mean + r, S @ V @ S.T

    # (1) coarse stage
    e0 = gamma / (40 * z ** 3)
    Nc = math.ceil(z * z * tail ** 2 / (2 * eta ** 2 * e0 ** 2))
    Sh = np.zeros((2 * m, 2 * m))
    for i in range(2 * m):
        e = I[i]
        outs = []
        for sgn in (1, -1):
            mu, V = G_in(sgn * eta * e, I)
            queries += Nc - 1                                   # Nc identical probes, one simulated exactly
            outs.append(rng.multivariate_normal(mu, (V + I) / (2 * Nc)))
        Sh[:, i] = (outs[0] - outs[1]) / (2 * eta)
    assert opnorm(Sh - S) <= e0
    Q = np.real(sqrtm(-Om @ Sh.T @ Om @ Sh))
    T = Sh @ np.linalg.inv(Q)
    assert np.allclose(T.T @ Om @ T, Om, atol=1e-10)
    assert opnorm(T - S) <= 9 * z * z * e0
    W = np.linalg.solve(T, S)
    assert opnorm(np.real(logm(W))) <= gamma
    coarse_queries = queries

    def chain(x, Tinv, chat, k):
        """k corrected steps x -> T^-1 (S x + r) - chat started at the coherent state |x>. The photon number of the
        input of every query is checked: at every step for k <= 4096, otherwise at 4096 evenly spaced steps and at
        the last one (the step map is affine, so the state after j steps is computed directly from W^j)."""
        nonlocal maxph
        Wc = Tinv @ S
        bc = Tinv @ r - chat
        js = range(k) if k <= 4096 else sorted(set(np.linspace(0, k - 1, 4096).astype(int)))
        for j in js:
            Wj = np.linalg.matrix_power(Wc, j)
            Mj = sum((np.linalg.matrix_power(Wc, i) for i in range(j)), np.zeros_like(Wc)) if j <= 64 else \
                np.linalg.solve(Wc - I, Wj - I)
            ph = photons(Wj @ x + Mj @ bc, Wj @ Wj.T)
            maxph = max(maxph, ph)
            assert ph <= nin * (1 + 1e-12), (ph, nin)
        Wk = np.linalg.matrix_power(Wc, k)
        Mk = sum((np.linalg.matrix_power(Wc, i) for i in range(k)), np.zeros_like(Wc)) if k <= 64 else \
            np.linalg.solve(Wc - I, Wk - I)
        # cross-check of the affine power against step-by-step composition for short chains
        if k <= 64:
            mu, V = x.copy(), I.copy()
            for _ in range(k):
                mu, V = Tinv @ (S @ mu + r) - chat, Tinv @ S @ V @ S.T @ Tinv.T
            assert np.allclose(mu, Wk @ x + Mk @ bc) and np.allclose(V, Wk @ Wk.T)
        return Wk @ x + Mk @ bc, Wk @ Wk.T

    # (2) doubling stages
    N = math.ceil(100 * tail ** 2 / (eta ** 2 * gamma ** 2))
    chat = np.zeros(2 * m)                                   # current guess of c = T^-1 r
    Tinv = np.linalg.inv(T)
    for t in range(L + 1):
        k = 2 ** t
        W = Tinv @ S
        K = np.real(logm(W))
        b = Tinv @ r - chat
        assert np.allclose(proj_sp(K, Om), K, atol=1e-9)
        assert k * opnorm(K) <= gamma * (1 + 1e-9)
        if k >= 2:
            assert np.linalg.norm(b) <= eta / (4 * k * math.exp(gamma)) * (1 + 1e-9)
        A = np.zeros((2 * m, 2 * m)); vsum = np.zeros(2 * m)
        for i in range(2 * m):
            outs = []
            for sgn in (1, -1):
                mu, V = chain(sgn * eta * I[i], Tinv, chat, k)
                queries += N * k
                outs.append(rng.multivariate_normal(mu, (V + I) / (2 * N)))
            A[:, i] = (outs[0] - outs[1]) / (2 * eta)
            vsum += (outs[0] + outs[1]) / 2
        Wk = np.linalg.matrix_power(W, k)
        tau = opnorm(A - Wk)
        assert tau <= gamma / 8
        Khat = proj_sp(np.real(logm(A)), Om) / k
        assert opnorm(Khat - K) <= 1.44 * tau / k
        assert np.linalg.norm(vsum / (2 * m) - sum(np.linalg.matrix_power(W, j) for j in range(k)) @ b) <= 0.0145 * eta if k <= 64 else True
        vhat = vsum / (2 * m)
        bnew = b - vhat / k
        E = expm(Khat)
        T = T @ E
        Tinv = np.linalg.inv(T)
        chat = np.linalg.solve(E, chat + vhat / k)
        assert np.allclose(T.T @ Om @ T, Om, atol=1e-8)
        W2 = Tinv @ S
        K2 = np.real(logm(W2))
        b2 = Tinv @ r - chat
        assert opnorm(W2 - I) <= 0.21 * gamma / k
        assert opnorm(K2) <= gamma / (2 * k)
        assert np.linalg.norm(b2) <= eta / (8 * k * math.exp(gamma)) * (1 + 1e-9)
    W = Tinv @ S
    rt = T @ chat
    theta = opnorm(W - I)
    bound = math.sqrt(72 * m * (nbar + 1) * theta) + math.sqrt(2 * (nprime + 1)) * np.linalg.norm(rt - r)
    assert bound <= eps, bound
    total_formula = 4 * m * Nc + sum(4 * m * N * 2 ** t for t in range(L + 1))
    assert queries == total_formula
    return queries, coarse_queries, bound, maxph, theta, 2 ** L


print(" m   z   nbar  nin    eps      queries     coarse  doubling*eps^2   bound/eps  max input photons/nin")
for m, z, nbar, nin in ((1, 1.5, 1.0, 2.0), (1, 2.0, 10.0, 4.0), (2, 1.5, 2.0, 4.0), (2, 2.0, 2.0, 1.0)):
    prev = None
    for eps in (0.2, 0.1, 0.05, 0.025, 0.0125):
        q, qc, bnd, mp, th, kL = run(m, z, nbar, nin, eps, 0.1)
        print(f"{m:2d} {z:4.1f} {nbar:5.1f} {nin:4.1f} {eps:7.4f} {q:12.3e} {qc:10.3e} {(q - qc) * eps ** 2:14.3e} {bnd / eps:10.3f} {mp / nin:8.3f}")
    print()

# (3) rotation example: input sqrt(1-p)|0> + sqrt(p)|k>, p = n/k, k = floor(pi/theta)
for n in (1, 3, 10):
    for theta in (0.05, 0.01, 0.002):
        assert theta <= math.pi / (2 * n + 1)
        k = math.floor(math.pi / theta)
        p = n / k
        assert k >= 2 * n
        ov = abs(1 - p + p * np.exp(-1j * k * theta))
        dist = math.sqrt(1 - ov ** 2)
        Sth = np.array([[math.cos(theta), math.sin(theta)], [-math.sin(theta), math.cos(theta)]])
        assert dist >= math.sqrt(n * theta / math.pi) and dist >= math.sqrt(n * opnorm(Sth - np.eye(2)) / math.pi)
        print(f"rotation n = {n}, theta = {theta}: trace distance {dist:.4f} >= sqrt(n theta / pi) = {math.sqrt(n * theta / math.pi):.4f}")
for z in (1.5, 2.0, 4.0):
    Sq = np.diag([z, 1 / z])
    ph = photons(np.zeros(2), Sq @ Sq.T)
    assert abs(ph - (z * z + z ** -2 - 2) / 4) < 1e-12 and 0 < ph <= z * z / 2 - 1 / 2
    print(f"squeezer z = {z}: vacuum output photon number {ph:.4f}, bound z^2 (n + m/2) - m/2 at n = 0: {z * z / 2 - 0.5:.4f}")
print("doubling checks: ok")
