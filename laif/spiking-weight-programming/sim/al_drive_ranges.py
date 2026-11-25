"""Check that every drive of every used neuron of the AL network (sim/al.py), as computed in 32-bit floating
point, lies in the low range [lo, L] or the high range [F, inf) of its kind in lean/LeakyGate/Basic.lean, and
that the neuron fires exactly at the high drives.

usage: al_drive_ranges.py [N_SEQUENCES] [SEED]
"""
import json, sys
import numpy as np
import torch
from al import circuit, make_batch, THR, N1, N2, N3, K

RANGES = {                      # kind: (lo, L, F), as in the Lean file
    "and_gate": (-0.43, 0.34, 1.07),
    "counter_unit": (-1.68, 0.34, 1.32),
    "crossing_unit": (-1.18, 0.34, 1.07),
    "relay_unit": (-0.01, 0.01, 0.99),
}

if __name__ == "__main__":
    torch.set_num_threads(1)
    a = sys.argv[1:]
    n, seed = (int(a[0]) if a else 2000), (int(a[1]) if len(a) > 1 else 0)
    c = circuit()
    x, _, _ = make_batch(n, np.random.default_rng(seed))
    kinds = [("and_gate", 1, slice(0, 16)), ("counter_unit", 2, slice(0, 2 * K)),
             ("crossing_unit", 2, slice(2 * K, 2 * K + 2)), ("relay_unit", 3, slice(0, 2))]
    seen = {k: [np.inf, -np.inf, np.inf] for k, _, _ in kinds}          # min low, max low, min high
    B, decay = x.shape[1], 0.3
    v1 = torch.zeros(B, N1); y1 = torch.zeros(B, N1); v2 = torch.zeros(B, N2); y2 = torch.zeros(B, N2)
    v3 = torch.zeros(B, N3); y3 = torch.zeros(B, N3)
    with torch.no_grad():
        for t in range(x.shape[0]):
            d1 = x[t] @ c["fc0"].T + c["b0"] + y1 @ c["rec1"].T + c["rb1"]
            v1 = decay * v1 * (1 - y1) + d1; y1 = (v1 > THR).float()
            d2 = y1 @ c["fc1"].T + c["b1"] + y2 @ c["rec2"].T + c["rb2"]
            v2 = decay * v2 * (1 - y2) + d2; y2 = (v2 > THR).float()
            d3 = y2 @ c["fc2"].T + c["b2"]
            v3 = decay * v3 * (1 - y3) + d3; y3 = (v3 > THR).float()
            for kind, layer, sl in kinds:
                d = (d1, d2, d3)[layer - 1][:, sl]; y = (y1, y2, y3)[layer - 1][:, sl]
                lo, L, F = RANGES[kind]
                low, high = (d >= lo) & (d <= L), d >= F
                assert bool((low | high).all()), (kind, t, float(d[~(low | high)][0]))
                assert bool((high == (y > 0)).all()), (kind, t)
                s = seen[kind]
                if low.any():
                    s[0] = min(s[0], float(d[low].min())); s[1] = max(s[1], float(d[low].max()))
                if high.any():
                    s[2] = min(s[2], float(d[high].min()))
    print(json.dumps(dict(check="drives of the AL network inside the ranges of the gate lemma", sequences=n, seed=seed,
                          observed={k: dict(min_low=round(v[0], 6), max_low=round(v[1], 6), min_high=round(v[2], 6))
                                    for k, v in seen.items()}, ranges=RANGES)))
