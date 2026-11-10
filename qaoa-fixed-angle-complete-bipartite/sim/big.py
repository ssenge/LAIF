"""K_{d,d} at refined tree-optimal p = 2 angles for a list of large d."""
import math, os, sys
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from qaoa import kdd_cut
from refine import newton, tree

x = np.array([0.496, 0.26912, 0.7636, 1.3316])
for d in [int(a) for a in sys.argv[1:]]:
    x, gn = newton(x, d)
    t = tree(x, d)
    k = kdd_cut(x[:2], x[2:] / math.sqrt(d), d)
    print(f"{d} {t:.13f} {k:.13f} {k - t:+.6e} {gn:.1e} sqrt(d)(t-1/2)={math.sqrt(d)*(t-.5):.6f} sqrt(d)(K-1/2)={math.sqrt(d)*(k-.5):.6f} " + " ".join(f"{v:.10f}" for v in x), flush=True)
