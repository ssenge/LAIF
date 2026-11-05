"""Fresh-sample evaluation of a fixed (tau, t) for lv_threshold.py, in chunks.
usage: lv_threshold_certify.py k d m tau t total [seed]"""
import sys, json, math
import numpy as np
from lv_plus_rule import labels
from lv_threshold import value
k, d, m = map(int, sys.argv[1:4]); tau = float(sys.argv[4]); t = int(sys.argv[5]); total = int(float(sys.argv[6]))
rng = np.random.default_rng(int(sys.argv[7]) if len(sys.argv) > 7 else 99)
chunk, s, s2, n = 50_000, 0.0, 0.0, 0
while n < total:
    lab, adj = labels(k, d, m, tau, chunk, rng)
    mu, se = value(lab, adj, t, k, rng.random((2, chunk, k)))
    s += mu * chunk; s2 += (se ** 2 * chunk + mu ** 2) * chunk; n += chunk
mean = s / n; se = math.sqrt((s2 / n - mean ** 2) / n)
print(json.dumps({"k": k, "d": d, "m": m, "girth": 2 * m + 2, "tau": tau, "t": t, "samples": n, "mean": round(mean, 6), "se": round(se, 6)}))
