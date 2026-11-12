"""Evaluate a fixed (tau, rule) of lv_plus_rule.py on fresh samples in chunks; report the mean, the
standard error and a one-sided lower confidence bound (normal approximation and Hoeffding).
usage: lv_certify.py k d m total_samples [seed]"""
import sys, json, math
import numpy as np
from lv_plus_rule import labels, cut

k, d, m = map(int, sys.argv[1:4]); total = int(float(sys.argv[4])); seed = int(sys.argv[5]) if len(sys.argv) > 5 else 2026
cfg = json.load(open(f"lvrule_{k}_{d}_{m}.json"))
rule = {(r[0][0], tuple(r[0][1:])): r[1] for r in cfg["rule"]}
rng = np.random.default_rng(seed); chunk = 200_000; s = s2 = 0.0; n = 0
while n < total:
    lab, adj = labels(k, d, m, cfg["tau"], chunk, rng)
    mu, se = cut(lab, adj, rule, k, rng.random((2, chunk, k)))
    s += mu * chunk; s2 += (se ** 2 * chunk + mu ** 2) * chunk; n += chunk
mean = s / n; var = s2 / n - mean ** 2; se = math.sqrt(var / n)
z = 3.719                                        # one-sided 1e-4
hoef = mean - math.sqrt(math.log(1e4) / (2 * n))
print(json.dumps({"k": k, "d": d, "m": m, "girth": 2 * m + 4, "tau": cfg["tau"], "samples": n,
                  "mean": round(mean, 6), "se": round(se, 6), "lcb_normal_1e-4": round(mean - z * se, 6),
                  "lcb_hoeffding_1e-4": round(hoef, 6)}))
