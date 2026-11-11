"""Tree value of the spin dynamics of xor_limit.py on the (D+1)-regular q-uniform hypertree around a root clause, with
gamma = G / sqrt(D) on the raw field sum_e J_e prod m. Prints (sat - 1/2) / sqrt(q / (2D)), comparable with nu.
Schedules with 3p + 1 entries use the axis mixer, with 4p + 2 or 5p + 2 entries also the linear output rule of xor_limit.py.
usage: xor_tree.py q p params.jsonl D samples [batch]"""
import sys, json, math
import numpy as np


def loo(X):
    """Leave-one-out products along the last axis."""
    pre = np.cumprod(np.concatenate([np.ones_like(X[..., :1]), X[..., :-1]], -1), -1)
    suf = np.cumprod(np.concatenate([np.ones_like(X[..., :1]), X[..., :0:-1]], -1), -1)[..., ::-1]
    return pre * suf


def run(q, p, prm, D, B, rng):
    n_ = len(prm); lin = n_ in (4 * p + 2, 5 * p + 2); wo = np.asarray(prm[n_ - 2 * p - 1:]) if lin else None
    base = prm[:n_ - 2 * p - 1] if lin else prm; th = np.asarray(base[2 * p + 1:]) if len(base) == 3 * p + 1 else None
    al, G, b = base[0], np.asarray(base[1:p + 1]), np.asarray(base[p + 1:2 * p + 1])
    g = G / math.sqrt(D); br = D * (q - 1)
    N = [q * br ** l for l in range(p + 1)]
    u = np.ones(2) / math.sqrt(2); w = np.array([1.0, -1.0]) / math.sqrt(2); sg = np.array([1.0, -1.0])
    psi = [np.cos(al) * u + np.sin(al) * rng.choice([-1.0, 1.0], size=(B, N[l], 1)) * w for l in range(p + 1)]
    psi = [x.astype(complex) for x in psi]
    Jr = rng.choice([-1.0, 1.0], size=B)
    Jc = [rng.choice([-1.0, 1.0], size=(B, N[l], D)) for l in range(p)]
    feat_m, feat_h = [], []
    for t in range(p):
        top = p - t - 1
        m = [np.abs(x[..., 0]) ** 2 - np.abs(x[..., 1]) ** 2 for x in psi[:top + 2]]
        feat_m.append(m[0])
        new = []
        for l in range(top + 1):
            ch = m[l + 1].reshape(B, N[l], D, q - 1).prod(-1)
            h = (Jc[l] * ch).sum(-1)
            if l == 0:
                h = h + Jr[:, None] * loo(m[0])
            else:
                sib = loo(m[l].reshape(B, N[l - 1], D, q - 1)).reshape(B, N[l])
                par = np.repeat(m[l - 1], br, axis=1) * np.repeat(Jc[l - 1].reshape(B, -1), q - 1, axis=1)
                h = h + par * sib
            if l == 0: feat_h.append(h / math.sqrt(D))
            x = psi[l] * np.exp(-1j * g[t] * h[..., None] * sg)
            if th is None:
                new.append(x + (np.exp(-1j * b[t]) - 1) * (x @ u)[..., None] * u)
            else:
                new.append(np.cos(b[t] / 2) * x - 1j * np.sin(b[t] / 2) * np.stack([np.exp(-1j * th[t]) * x[..., 1], np.exp(1j * th[t]) * x[..., 0]], -1))
        psi = new
    mf = np.abs(psi[0][..., 0]) ** 2 - np.abs(psi[0][..., 1]) ** 2
    if lin: mf = np.einsum("k,kbi->bi", wo, np.stack(feat_m + [mf] + feat_h))   # output weights as in xor_limit.py lin
    s = np.where(mf >= 0, 1.0, -1.0)
    return (1 + Jr * s.prod(-1)) / 2


if __name__ == "__main__":
    q, p = int(sys.argv[1]), int(sys.argv[2]); D = int(sys.argv[4]); n = int(float(sys.argv[5]))
    B = int(sys.argv[6]) if len(sys.argv) > 6 else 64
    prm = [json.loads(l) for l in open(sys.argv[3]) if json.loads(l)["q"] == q and json.loads(l)["p"] == p][-1]["params"]
    rng = np.random.default_rng(2026); vals = []
    while len(vals) * B < n: vals.append(run(q, p, prm, D, B, rng))
    v = np.concatenate(vals); sc = math.sqrt(q / (2 * D))
    print(D, round((v.mean() - 0.5) / sc, 4), "+-", round(v.std() / math.sqrt(len(v)) / sc, 4), flush=True)
