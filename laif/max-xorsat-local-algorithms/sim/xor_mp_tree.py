"""Tree value of the message passing of xor_mp.py on the (D+1)-regular q-uniform hypertree around a root clause.
Prints (sat - 1/2) / sqrt(q / (2D)), comparable with nu. usage: xor_mp_tree.py q p params.jsonl D samples [batch] [H]"""
import sys, json, math
import numpy as np
from xor_tree import loo
from xor_mp import unpack


def run(q, p, H, x, D, B, rng):
    nets, c0 = unpack(np.asarray(x), p, H)
    net = lambda P, v: np.tensordot(np.tanh(np.einsum("hk,...k->...h", P[0], v) + P[1]), P[2], 1) + P[3]
    br = D * (q - 1); N = [q * br ** l for l in range(p + 1)]
    s = [rng.choice([-1.0, 1.0], size=(B, N[l])) for l in range(p + 1)]
    ph = [[] for _ in range(p + 1)]
    Jr = rng.choice([-1.0, 1.0], size=B)
    Jc = [rng.choice([-1.0, 1.0], size=(B, N[l], D)) for l in range(p)]
    feat = lambda l, t: np.stack([s[l]] + ph[l] + [np.zeros_like(s[l])] * (p - t), -1)   # (s, phi_0..phi_{t-1}, 0...)
    for t in range(p):
        top = p - t - 1
        m = [np.tanh(c0) * s[l] if t == 0 else np.tanh(net(nets[t - 1], feat(l, t))) for l in range(top + 2)]
        hs = []
        for l in range(top + 1):
            h = (Jc[l] * m[l + 1].reshape(B, N[l], D, q - 1).prod(-1)).sum(-1)
            if l == 0:
                h = h + Jr[:, None] * loo(m[0])
            else:
                sib = loo(m[l].reshape(B, N[l - 1], D, q - 1)).reshape(B, N[l])
                par = np.repeat(m[l - 1], br, axis=1) * np.repeat(Jc[l - 1].reshape(B, -1), q - 1, axis=1)
                h = h + par * sib
            hs.append(h / math.sqrt(D))
        for l in range(top + 1): ph[l].append(hs[l])
    out = np.where(net(nets[p - 1], feat(0, p)) >= 0, 1.0, -1.0)
    return (1 + Jr * out.prod(-1)) / 2


if __name__ == "__main__":
    q, p = int(sys.argv[1]), int(sys.argv[2]); D = int(sys.argv[4]); n = int(float(sys.argv[5]))
    B = int(sys.argv[6]) if len(sys.argv) > 6 else 64; H = int(sys.argv[7]) if len(sys.argv) > 7 else 8
    x = [r for r in map(json.loads, open(sys.argv[3])) if r["q"] == q and r["p"] == p and r.get("H") == H][-1]["params"]
    rng = np.random.default_rng(2026); vals = []
    while len(vals) * B < n: vals.append(run(q, p, H, x, D, B, rng))
    v = np.concatenate(vals); sc = math.sqrt(q / (2 * D))
    print(D, round((v.mean() - 0.5) / sc, 4), "+-", round(v.std() / math.sqrt(len(v)) / sc, 4), flush=True)
