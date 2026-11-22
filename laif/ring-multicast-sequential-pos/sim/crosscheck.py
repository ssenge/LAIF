"""Cross-check of the proof against the exact simulator on random rings: for every instance, the better of the
orders A and B (ring.best_two, worst tie choices, orientation as in the paper) costs at most 4/3 OPT."""
import random, sys
from fractions import Fraction as F
from ring import best_two, opt

rng = random.Random(int(sys.argv[2]) if len(sys.argv) > 2 else 1); worst = F(0); cnt = 0
for it in range(int(sys.argv[1])):
    n = rng.randint(2, 40)
    kind = rng.random()
    if kind < 0.4: a = [F(rng.randint(0, 20)) for _ in range(n + 1)]
    elif kind < 0.7: a = [F(rng.choice([0, 0, 0, rng.randint(1, 30)])) for _ in range(n + 1)]
    elif kind < 0.85: a = [F(rng.randint(1, 1000), rng.randint(1, 50)) for _ in range(n + 1)]
    else:                                      # near the worst structure: a few edges, zeros, one far large edge
        h = rng.randint(2, 6); a = [F(rng.randint(0, 40)) for _ in range(h)] + [F(0)] * rng.randint(0, 25)
        a += [F(rng.randint(30, 60))] + [F(rng.randint(0, 3)) for _ in range(rng.randint(0, 3))]
    if sum(a) == 0: continue
    r = best_two(a) if opt(a) > 0 else F(1)
    worst = max(worst, r); cnt += 1
    assert r <= F(4, 3), (a, r)
print("instances", cnt, "worst best-of-two ratio", worst, float(worst))
