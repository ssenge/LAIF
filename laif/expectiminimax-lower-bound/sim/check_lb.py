"""Checks for the expectiminimax lower bound construction.

1. Tree values: on the promise inputs the value of every node is one of two numbers, and the
   root gap is the product of Delta_j/deg over the chance layers.
2. Adv+- (min formulation, an SDP) of small composed instances is at least the product of the
   Adv+- of the layer functions, including a partial outer function.
"""
import itertools, random
import numpy as np, cvxpy as cp

def tree_value(x, deg, layers):
    """layers from the root: ('chance', t, Delta) or ('max'|'min'); x: leaf bits, deg**D of them."""
    def val(lo, depth):
        if depth == len(layers):
            return float(x[lo])
        size = deg ** (len(layers) - depth - 1)
        ch = [val(lo + i * size, depth + 1) for i in range(deg)]
        kind = layers[depth][0]
        return max(ch) if kind == 'max' else min(ch) if kind == 'min' else sum(ch) / deg
    return val(0, 0)

def sample(deg, layers, depth, bit, rng):
    """A promise input below a node at `depth` whose Boolean value is `bit`."""
    if depth == len(layers):
        return [bit]
    kind = layers[depth][0]
    if kind == 'chance':
        _, t, d = layers[depth]
        k = t + d if bit else t
        hi = set(rng.sample(range(deg), k))
        bits = [1 if i in hi else 0 for i in range(deg)]
    elif kind == 'max':   # OR
        bits = [rng.randint(0, 1) for _ in range(deg)] if bit else [0] * deg
        if bit and not any(bits): bits[rng.randrange(deg)] = 1
    else:                 # AND
        bits = [1] * deg if bit else [rng.randint(0, 1) for _ in range(deg)]
        if not bit and all(bits): bits[rng.randrange(deg)] = 0
    return [y for b in bits for y in sample(deg, layers, depth + 1, b, rng)]

def two_values(deg, layers):
    lo, hi = 0.0, 1.0
    for kind in reversed(layers):
        if kind[0] == 'chance':
            _, t, d = kind
            lo, hi = lo + (hi - lo) * t / deg, lo + (hi - lo) * (t + d) / deg
    return lo, hi

rng = random.Random(1)
cases = [(3, [('chance', 1, 1), ('max',), ('chance', 0, 3), ('min',)]),
         (3, [('chance', 0, 1), ('max',), ('chance', 1, 2), ('min',)]),
         (4, [('chance', 1, 2), ('min',), ('chance', 2, 1), ('max',)]),
         (2, [('chance', 0, 1), ('max',)]),
         (3, [('chance', 1, 1), ('max',), ('chance', 1, 1), ('max',), ('chance', 0, 2), ('min',)])]
for deg, layers in cases:
    lo, hi = two_values(deg, layers)
    gap = np.prod([k[2] / deg for k in layers if k[0] == 'chance'])
    assert abs((hi - lo) - gap) < 1e-12
    for _ in range(200):
        b = rng.randint(0, 1)
        x = sample(deg, layers, 0, b, rng)
        assert len(x) == deg ** len(layers)
        assert abs(tree_value(x, deg, layers) - (hi if b else lo)) < 1e-12
print("tree values checked on", len(cases), "layouts")

def adv(f, n):
    """Adv+-(f) for a partial Boolean f given as dict input-tuple -> bit, by the SDP
    min max_x sum_j X_j[x,x]  s.t.  sum_{j: x_j != y_j} X_j[x,y] = 1 when f(x) != f(y)."""
    D = list(f); N = len(D)
    A = np.array(D); F = np.array([f[x] for x in D])
    diff = F[:, None] != F[None, :]
    X = [cp.Variable((N, N), PSD=True) for _ in range(n)]
    s = cp.Variable()
    S = sum(cp.multiply((A[:, None, j] != A[None, :, j]).astype(float), X[j]) for j in range(n))
    cons = [sum(cp.diag(X[j]) for j in range(n)) <= s, S[diff] == 1]
    cp.Problem(cp.Minimize(s), cons).solve(solver='CLARABEL' if N < 60 else 'SCS', **({} if N < 60 else {'eps': 1e-6, 'max_iters': 200000}))
    return s.value

def ew(deg, t, d):
    return {x: int(sum(x) == t + d) for x in itertools.product((0, 1), repeat=deg) if sum(x) in (t, t + d)}
def gate(deg, kind):
    return {x: int(any(x)) if kind == 'or' else int(all(x)) for x in itertools.product((0, 1), repeat=deg)}
def compose(f, g, deg, m):
    out = {}
    for parts in itertools.product(list(g), repeat=deg):
        y = tuple(g[p] for p in parts)
        if y in f:
            out[tuple(b for p in parts for b in p)] = f[y]
    return out

for deg, (t, d), kind in [(2, (0, 1), 'or'), (2, (1, 1), 'and'), (2, (0, 2), 'or'), (3, (1, 1), 'or')]:  # deg 3 takes about 10 min
    f, g = ew(deg, t, d), gate(deg, kind)
    af, ag, afg = adv(f, deg), adv(g, deg), adv(compose(f, g, deg, deg), deg * deg)
    print(f"deg={deg} EW(t={t},D={d}) o {kind}: Adv(f)={af:.4f} Adv(g)={ag:.4f} product={af*ag:.4f} Adv(fog)={afg:.4f}")
    assert afg >= af * ag * (1 - 1e-3)
print("composition lower bound checked")
