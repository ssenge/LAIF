"""The label algorithm with label A empty: one representation, table and claw finding only.
Its exponent must equal (2/7)(h(p)+1-p), and the steps must work on real instances."""
import math
from collections import Counter
import check
from opt import H, seven_sum, inner

for p in (.05, .1, .2, .25, .47, .6, .9):
    u = (H(p, 1-p) + 1 - p)/2       # B and C split evenly, each list is one typed half
    assert abs(inner(u, 0.0) - seven_sum(p)) < 1e-12
print("inner(u, 0) == (2/7)(h(p)+1-p) at all tested p")
check.A1 = check.A0 = 0.0
check.SIGMA = 4*((H(.25, .75) + .75)/2)/7
for n, runs in ((15, 40), (20, 30), (23, 8)):
    for kind in ("random", "heavy"):
        st = Counter()
        for seed in range(runs):
            check.run(n, kind, 5000*n + seed, st)
        print(n, kind, dict(st), flush=True)
