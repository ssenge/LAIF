"""Checks for the influence-greedy decision tree on random bounded low-degree polynomials.

For f : {0,1}^N -> [0,1] of degree <= d (random, N <= 9) the script checks
  (a) total influence  sum_i E[(f(X) - f(X^i))^2] <= d                      (classical bound)
  (b) E_b[I(f|x_i=b)] = I(f) - Inf_i(f)                                    (restriction identity)
  (c) the greedy tree of depth <= k satisfies k*phi*bad <= k*phi*tau/eps^2 + I(f),
      with phi the least influence queried at an inner node              (inductive bound)
and prints the explicit depth bound against the bound obtained with the exponent 7.
"""
import itertools, math, random
import numpy as np

def cube(N):
    return np.array(list(itertools.product([0, 1], repeat=N)), dtype=float)

def rand_poly(N, d, rng):
    sets = [S for r in range(d + 1) for S in itertools.combinations(range(N), r)]
    coef = {S: rng.gauss(0, 1) for S in sets}
    X = cube(N)
    v = np.array([sum(c * np.prod([x[j] for j in S]) for S, c in coef.items()) for x in X])
    lo, hi = v.min(), v.max()
    return (v - lo) / (hi - lo) if hi > lo else np.zeros_like(v)  # affine map keeps the degree

def idx(N):
    return {tuple(int(b) for b in x): k for k, x in enumerate(cube(N))}

def flip_perm(N, i):
    X, I = cube(N), idx(N)
    return np.array([I[tuple(int(1 - b) if j == i else int(b) for j, b in enumerate(x))] for x in X])

def fix_perm(N, i, b):
    X, I = cube(N), idx(N)
    return np.array([I[tuple(b if j == i else int(c) for j, c in enumerate(x))] for x in X])

def inf(f, N, i): return float(np.mean((f - f[flip_perm(N, i)]) ** 2))
def tot(f, N): return sum(inf(f, N, i) for i in range(N))
def var(f): return float(np.var(f))

def greedy(f, N, k, tau, eps, phis):
    """Returns the 0/1 vector of bad inputs for the greedy tree (on the full cube)."""
    if k == 0 or var(f) < tau:
        return (np.abs(f.mean() - f) > eps).astype(float)
    infl = [inf(f, N, i) for i in range(N)]
    i = int(np.argmax(infl)); phis.append(infl[i])
    X = cube(N)
    out = np.zeros(len(f))
    for b in (0, 1):
        g = f[fix_perm(N, i, b)]
        badg = greedy(g, N, k - 1, tau, eps, phis)
        mask = X[:, i] == b
        out[mask] = badg[mask]  # g ignores x_i; the branch tree is read with x_i = b
    return out

rng = random.Random(1)
for trial in range(60):
    N, d = rng.randint(3, 8), rng.randint(1, 4)
    f = rand_poly(N, d, rng)
    I = tot(f, N)
    assert I <= d + 1e-9, (N, d, I)
    i = rng.randrange(N)
    avg = sum(tot(f[fix_perm(N, i, b)], N) for b in (0, 1)) / 2
    assert abs(avg - (I - inf(f, N, i))) < 1e-9
    for eps, delta in [(0.1, 0.2), (0.2, 0.1), (0.05, 0.5)]:
        tau = eps ** 2 * delta / 2
        for k in range(0, N + 1):
            phis = []
            bad = greedy(f, N, k, tau, eps, phis).mean()
            phi = min(phis) if phis else 0.0
            assert k * phi * bad <= k * phi * tau / eps ** 2 + I + 1e-12, (N, d, k)
        assert greedy(f, N, N, tau, eps, []).mean() <= tau / eps ** 2 + 1e-12  # full depth: every leaf has var < tau
print("all asserts passed (60 random polynomials)")

c = 8 * math.sqrt(15) / (125 * math.pi ** 4)
const = 2 ** 3.5 / c
print(f"depth bound 2d/(delta*phi) = {const:.1f} * d^7 / (eps^5 delta^3.5)")
for T, eps, delta in [(1, 0.1, 0.1), (5, 0.1, 0.1), (10, 0.01, 0.01)]:
    d = 2 * T
    ours = 2 * d / (delta * c * (eps ** 2 * delta / 2) ** 2.5 / d ** 6)
    seven = (4 * T) ** 8 * eps ** -14 * delta ** -8
    print(f"T={T} eps={eps} delta={delta}: ours {ours:.3e}, exponent-7 bound {seven:.3e}")
