"""Table of the pixel test from pixel_runs.jsonl: mean and sample standard deviation over seeds per variant."""
import json, sys
import numpy as np

rows = [json.loads(l) for l in open(sys.argv[1] if len(sys.argv) > 1 else "pixel_runs.jsonl")]
groups = {}
for r in rows:
    groups.setdefault((r["variant"], r["mu"]), []).append(r)
print("variant  mu  seeds  position R2  background R2  action response  success  final distance")
for (v, mu), rs in groups.items():
    cell = lambda k: f"{np.mean([r[k] for r in rs]):.3f} ± {np.std([r[k] for r in rs], ddof=1) if len(rs) > 1 else 0:.3f}"
    print(v, mu, len(rs), *(cell(k) for k in ("r2_pos", "r2_bg", "response", "success", "dist_end")), sep="  ")
assert all(len(rs) == 3 for (v, mu), rs in groups.items() if v != "cov")
