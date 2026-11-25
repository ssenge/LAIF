"""Search for CNOT + Ry circuits preparing the Dicke state D(n,k) from |0..0>.
A skeleton is a list of qubit pairs (control, target). The circuit is: Ry on every qubit, then for each pair a CNOT
followed by Ry on both of its qubits. Real amplitudes only (Dicke states are real).
Loss = 1 - <D|psi>^2, minimized by L-BFGS with an exact gradient (forward/backward pass).
usage: python search.py n k c [restarts]   prints the best loss per skeleton class that reaches < 1e-10.
"""
import itertools, math, sys
import numpy as np
from scipy.optimize import minimize

def dicke(n, k):
    v = np.zeros(2 ** n)
    for s in itertools.combinations(range(n), k):
        v[sum(1 << (n - 1 - q) for q in s)] = 1
    return v / np.linalg.norm(v)

def ry(psi, n, q, th):
    """apply Ry(th) on qubit q to a real state psi (shape 2^n)"""
    p = psi.reshape(2 ** q, 2, -1)
    c, s = math.cos(th / 2), math.sin(th / 2)
    a, b = p[:, 0, :].copy(), p[:, 1, :].copy()
    out = np.empty_like(p); out[:, 0, :] = c * a - s * b; out[:, 1, :] = s * a + c * b
    return out.reshape(-1)

def dry(psi, n, q, th):
    return ry(psi, n, q, th + math.pi) * 0.5

def cnot(psi, n, ctl, tgt):
    p = psi.reshape([2] * n).copy()
    idx = [slice(None)] * n; idx[ctl] = 1
    sub = p[tuple(idx)]
    t = tgt if tgt < ctl else tgt - 1
    p[tuple(idx)] = np.flip(sub, axis=t)
    return p.reshape(-1)

def gates(n, skel):
    g = [("ry", q) for q in range(n)]
    for (a, b) in skel:
        g += [("cx", a, b), ("ry", a), ("ry", b)]
    return g

def loss_grad(th, n, g, target):
    psi = np.zeros(2 ** n); psi[0] = 1
    states, j = [], 0
    for op in g:
        if op[0] == "ry":
            states.append(psi); psi = ry(psi, n, op[1], th[j]); j += 1
        else:
            psi = cnot(psi, n, op[1], op[2])
    ov = target @ psi
    lam = target.copy(); grad = np.zeros_like(th); j = len(th)
    for op in reversed(g):   # lam = adjoint of the remaining circuit applied to target
        if op[0] == "ry":
            j -= 1
            grad[j] = lam @ dry(states[j], n, op[1], th[j])
            lam = ry(lam, n, op[1], -th[j])
        else:
            lam = cnot(lam, n, op[1], op[2])
    return 1 - ov ** 2, -2 * ov * grad

def solve(n, k, skel, restarts, rng):
    g = gates(n, skel); m = sum(1 for o in g if o[0] == "ry"); target = dicke(n, k); best = (1.0, None)
    for _ in range(restarts):
        r = minimize(loss_grad, rng.uniform(0, 2 * math.pi, m), args=(n, g, target), jac=True, method="L-BFGS-B",
                     options={"maxiter": 2000, "ftol": 1e-16, "gtol": 1e-12})
        if r.fun < best[0]: best = (r.fun, r.x)
        if best[0] < 1e-12: break
    return best

def skeletons(n, c):
    """unordered pairs suffice up to local gates only for the pair choice; we keep CNOT orientation free by
    enumerating both orientations only for the first use of a pair. Canonical form: first pair (0,1)."""
    pairs = list(itertools.permutations(range(n), 2))
    for s in itertools.product(pairs, repeat=c):
        if c and s[0] != (0, 1): continue
        if any(s[i] == s[i + 1] for i in range(c - 1)): continue   # CX CX with Ry between can be merged? keep simple: skip repeats
        yield list(s)

if __name__ == "__main__":
    n, k, c = map(int, sys.argv[1:4]); restarts = int(sys.argv[4]) if len(sys.argv) > 4 else 20
    rng = np.random.default_rng(0)
    # self-check of the gradient
    g = gates(3, [(0, 1), (1, 2)]); th = rng.uniform(0, 6, 7); t = dicke(3, 1)
    f0, gr = loss_grad(th, 3, g, t); e = np.zeros(7); e[2] = 1e-6
    assert abs((loss_grad(th + e, 3, g, t)[0] - f0) / 1e-6 - gr[2]) < 1e-4
    hits = 0
    if len(sys.argv) > 5:   # sampled skeletons: python search.py n k c restarts samples seed
        samples, srng = int(sys.argv[5]), np.random.default_rng(int(sys.argv[6]) if len(sys.argv) > 6 else 1)
        pairs = list(itertools.permutations(range(n), 2))
        def sampled():
            for _ in range(samples):
                s = [(0, 1)]
                while len(s) < c:
                    p = pairs[srng.integers(len(pairs))]
                    if p != s[-1]: s.append(p)
                yield s
        it = sampled()
    else:
        it = skeletons(n, c)
    for s in it:
        f, x = solve(n, k, s, restarts, rng)
        if f < 1e-10:
            hits += 1; print("HIT", s, f, flush=True)
            if hits >= 3: break
    print("done n=%d k=%d c=%d hits=%d" % (n, k, c, hits))
