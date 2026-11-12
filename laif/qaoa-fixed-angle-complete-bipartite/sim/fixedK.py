"""K_{d,d} cut fraction at fixed angles for a list of d. mode 'sqrt': gamma = g/sqrt(d); mode 'lin': gamma = g/d.
Usage: python fixedK.py mode b1 b2 g1 g2 d1 d2 ..."""
import math, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from qaoa import kdd_cut

mode = sys.argv[1]
b1, b2, g1, g2 = map(float, sys.argv[2:6])
for d in map(int, sys.argv[6:]):
    sc = math.sqrt(d) if mode == "sqrt" else d
    k = kdd_cut([b1, b2], [g1 / sc, g2 / sc], d)
    print(d, f"{k:.12f}", f"{math.sqrt(d) * (k - 0.5):.6f}", flush=True)
