# (1) The simplified forms of Theorem 1 (Q-form, margin form, optimized form) dominate the explicit bounds of bounds.py.
# (2) Sample sizes of Theorem 2 for example parameters.
import numpy as np
from bounds import general_bound, margin_bound, sim_bound, e_out
rng = np.random.default_rng(5)
Qf = lambda m, z, y, E: 11 * m * z * (z ** 2 + y) + np.sqrt(z ** 2 + y) * (2 * E + 3 * m)
Pf = lambda m, z, y, E, xi: 11 * m * z * (z ** 2 + y) / xi ** 2 + np.sqrt(z ** 2 + y) * (2 * E + 3 * m) / np.sqrt(xi)
for t in range(20000):
    m = int(rng.integers(1, 9)); z = rng.uniform(1, 5); y = rng.uniform(0, 10); E = rng.uniform(0, 100)
    xi = np.exp(rng.uniform(np.log(1e-6), 0)); dX, dY = np.exp(rng.uniform(np.log(1e-9), 0, size=2))
    lhs = general_bound(E, m, z, y, xi, dX, dY, 0)
    assert lhs <= 2 * np.sqrt(m * xi * (2 * E + 1)) + (dX + dY) * Qf(m, z, y, E) / xi ** 2 + 1e-12      # (1)
    assert margin_bound(E, m, z, y, xi, dX, dY, 0) <= (dX + dY) * Pf(m, z, y, E, xi) + 1e-12            # (1)
    A = 2 * np.sqrt(m * (2 * E + 1)); B = (dX + dY) * Qf(m, z, y, E)
    if 4 * B <= A:
        xs = (4 * B / A) ** 0.4
        assert xs <= 1 and abs(A * np.sqrt(xs) + B / xs ** 2 - 1.25 * 4 ** 0.2 * A ** 0.8 * B ** 0.2) < 1e-9 * (1 + A)
        assert 1.25 * 4 ** 0.2 * A ** 0.8 * B ** 0.2 <= 2.88 * (m * (2 * E + 1)) ** 0.4 * B ** 0.2
print("(1) simplified forms of Theorem 1 dominate the explicit bounds on 20000 random parameter sets")

def sizes(m, z, y, E, nin, eps, dfail, xi0=None):
    z1, y1 = z + 1, y + 1
    if xi0 is None:
        dl = (3 * eps / (4 * 2.88)) ** 5 / (Qf(m, z1, y1, E) * (m * (2 * E + 1)) ** 2)
    else:
        dl = 3 * eps / (4 * Pf(m, z1, y1, E, xi0))
    sig2 = (z ** 2 + y + 1) / 2
    lg = np.sqrt(2 * np.log(3 / dfail))
    NX = 144 * (2 * z + 1) ** 2 * sig2 * (2 * m + lg) ** 2 / (nin * dl ** 2)
    nS = (48 * sig2 / dl) ** 2 * (np.sqrt(2 * m) + np.sqrt(2 * np.log(6 / dfail))) ** 2
    NS = 2 * nS / (4 * m + 1) + 2
    Nd = 16 * sig2 * (np.sqrt(2 * m) + lg) ** 2 * (2 * z ** 2 * E + z ** 2 * m + m * y + 1) / eps ** 2
    N = int(np.ceil(max(NX, NS, Nd)))
    return (4 * m + 1) * N
print("(2) total queries (4m + 1) N of Theorem 2, delta = 0.01, z = 1, y = 1, E = 1, inputs with at most 10 photons:")
for m in (1, 2, 4):
    for eps in (0.1, 0.01):
        print(f"   m = {m}, eps = {eps}: general {sizes(m, 1, 1, 1, 10, eps, 0.01):.2e}; noise margin 0.5: {sizes(m, 1, 1, 1, 10, eps, 0.01, 0.5):.2e}")
