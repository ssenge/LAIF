"""Exhaustive check of Theorem 2 (a) for small depth: all model functions of stabilizer-only circuits with L <= 6
encoding calls (deduplicated on a grid), r = 1. For the target g = 1/2 the best sup error on [delta, 1] must be at
least 1/2 - L delta (derivative bound), and at most 24^(L+1) functions exist."""
import itertools, numpy as np
def R(axis, k):
    a = np.eye(3); i, j = [(1, 2), (2, 0), (0, 1)][axis]; c, s = [(1, 0), (0, 1), (-1, 0), (0, -1)][k]
    a[i, i], a[i, j], a[j, i], a[j, j] = c, -s, s, c; return a
gens = [R(0, 1), R(1, 1), R(2, 1)]
cl = {tuple(np.eye(3).round().astype(int).ravel())}; frontier = [np.eye(3)]
while frontier:                                           # the 24 rotations permuting +-e_x, +-e_y, +-e_z
    new = []
    for M in frontier:
        for g in gens:
            N = (g @ M).round(); key = tuple(N.astype(int).ravel())
            if key not in cl: cl.add(key); new.append(N)
    frontier = new
CL = [np.array(k, float).reshape(3, 3) for k in cl]; assert len(CL) == 24
x = np.r_[np.linspace(-1, 1, 801)]; c, s = np.cos(x), np.sin(x)
def enc(v):                                               # R_z(x) acting on a batch of vectors v[..., 3, len(x)]
    return np.stack([c * v[0] - s * v[1], s * v[0] + c * v[1], v[2]])
states = {}
for V in CL:                                              # after V_0: vector V e_z, constant in x
    v = np.repeat((V @ [0, 0, 1.0])[:, None], len(x), 1); states[v.round(9).tobytes()] = v
for L in range(1, 7):
    nxt = {}
    for v in states.values():
        w = enc(v)
        for V in CL:
            u = V @ w; nxt.setdefault(u.round(9).tobytes(), u)
    states = nxt
    fs = np.unique(np.array([v[2] for v in states.values()]).round(9), axis=0)
    assert len(fs) <= 24 ** (L + 1)
    for d in [0.05, 0.1, 0.2]:
        m = (np.abs(x) >= d); err = np.abs(fs[:, m] - 0.5).max(1).min()
        assert err >= 0.5 - L * d - 1e-9, (L, d, err)
    print(f"L={L}: {len(fs)} distinct model functions; best sup error to 1/2 on delta<=|x|<=1 for delta=0.05: "
          f"{np.abs(fs[:, np.abs(x) >= 0.05] - 0.5).max(1).min():.4f} (bound {max(0, 0.5 - 0.05 * L):.2f})", flush=True)
