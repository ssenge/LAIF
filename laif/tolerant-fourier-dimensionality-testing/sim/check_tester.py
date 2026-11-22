"""Classical simulation of the two-phase tolerant tester on abstract Fourier distributions over F_2^n.

Yes: some subspace U of dim k has mass <= 4 alpha eps outside. No: every subspace of dim <= k has mass >= 2 eps
outside (checked exhaustively). Amplitude estimation is replaced by exact values perturbed at random within the stated errors
(|w_hat - w| <= (x/8) max(w, eps) in phase B), amplified samples by exact conditional samples. Checks acceptance rates and the query count.
"""
import itertools, math, random
import numpy as np

n = 5
VEC = list(range(1 << n))

def span(basis):
    S = {0}
    for b in basis:
        S |= {s ^ b for s in S}
    return S

def subspaces(dim):
    seen = set()
    for basis in itertools.combinations(VEC[1:], dim):
        S = frozenset(span(basis))
        if len(S) == 1 << dim:
            seen.add(S)
    return list(seen)

SUB = {d: subspaces(d) for d in range(0, 4)}

def outside(mu, S):
    return sum(p for s, p in mu.items() if s not in S)

def min_outside(mu, k):
    return min(outside(mu, S) for d in range(k + 1) for S in SUB[d])

def make_yes(k, alpha, eps, rng):
    U = rng.choice(SUB[k]); U = sorted(U)
    mu = {}
    noise = 4 * alpha * eps * rng.random()
    out = [s for s in VEC if s not in U]
    w = np.array([rng.random() for _ in U]); w /= w.sum()
    for s, p in zip(U, w): mu[s] = (1 - noise) * p
    v = np.array([rng.random() for _ in out]); v /= v.sum()
    for s, p in zip(out, v): mu[s] = mu.get(s, 0) + noise * p
    return mu

def make_no(k, eps, rng):
    while True:
        heavy = rng.sample(VEC[1:], k + 2)
        mu = {0: 1 - 3 * eps * (k + 2) / 2}
        rest = 1 - mu[0]
        for s in heavy: mu[s] = rest / len(heavy)
        if min_outside(mu, k) >= 2 * eps:
            return mu

def sample(mu, W, rng):
    items = [(s, p) for s, p in mu.items() if s not in W]
    r = rng.random() * sum(p for _, p in items)
    for s, p in items:
        r -= p
        if r <= 0: return s
    return items[-1][0]

def tester(mu, k, alpha, eps, rng, C=1.0):
    x = 1 - 2 * alpha
    Lam = max(4, 80 * alpha * k)
    W, basis, cost = {0}, [], 0.0
    while True:
        w = outside(mu, W)
        cost += 2 * math.log(k + 2) / math.sqrt(Lam * eps)
        large = w >= Lam * eps or (w >= Lam * eps / 2 and rng.random() < 0.5)
        if not large: break
        cost += 2 * math.log(k + 2) / math.sqrt(Lam * eps / 2)
        s = sample(mu, W, rng); basis.append(s); W = span(basis)
        if len(basis) > k: return False, cost
    d = len(basis)
    delta = x / 8
    w_hat = w + delta * max(w, eps) * rng.uniform(-1, 1)
    cost += 1 / (x * math.sqrt(eps))
    if w_hat <= (1 + 2 * alpha) * eps: return True, cost
    m = int(math.ceil(C * Lam * k / x ** 2 * math.log(math.e * Lam / x)))
    xs = [sample(mu, W, rng) for _ in range(m)]
    cost += m / math.sqrt(eps)
    tau = (1 + 2 * alpha) * (eps / w_hat) * m
    for dd in range(0, k - d + 1):
        for V in SUB[dd]:
            T = span(basis + [v for v in V if v])
            if len(T) > 1 << k: continue
            if sum(1 for s in xs if s not in T) <= tau: return True, cost
    return False, cost

rng = random.Random(7)
for k, alpha, eps in [(1, 0.1, 0.02), (2, 0.1, 0.02), (2, 0.25, 0.01), (2, 0.05, 0.005)]:
    ya = sum(tester(make_yes(k, alpha, eps, rng), k, alpha, eps, rng)[0] for _ in range(60))
    nos = [make_no(k, eps, rng) for _ in range(60)]
    na = [tester(mu, k, alpha, eps, rng) for mu in nos]
    rej = sum(1 for a, _ in na if not a)
    c = max(cst for _, cst in na)
    old = k / (eps * (1 - 2 * alpha) ** 2) * math.log(1 / (eps * (1 - 2 * alpha)))
    assert ya >= 50 and rej >= 50, (k, alpha, eps, ya, rej)
    print(f"k={k} alpha={alpha} eps={eps}: yes accepted {ya}/60, no rejected {rej}/60, cost <= {c:.0f} (k/eps scale {old:.0f})")
