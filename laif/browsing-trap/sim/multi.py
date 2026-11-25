"""Several tree species in the browsing-trap model: final canopy compositions from different initial states, for a
sweep of browser density D.  Species: palatable fast recruiter (fir/maple-like), unpalatable slower (spruce-like),
medium (beech-like)."""
import numpy as np
from trap import make, settle

k = 4
f = np.array([2.0, 1.2, 1.6]); g = np.array([0.5, 0.5, 0.45]); mC = np.array([0.02, 0.02, 0.02])
pi = np.array([1.0, 0.1, 0.4])
rhs, S = make((f, g, mC, pi, k, 1.0, 50.0, 1.0, 0.05, 0.05))
starts = {"mixed": [0.2, 0.2, 0.2], "spruce": [0.01, 0.6, 0.01], "fir": [0.6, 0.01, 0.01]}
for D in (0.5, 2.0, 5.0, 10.0, 20.0, 40.0):
    row = []
    for name, C0 in starts.items():
        y0 = np.r_[np.repeat(np.array(C0), k)*2, C0]
        C = settle(rhs, y0, D, T=40000)[-S:]
        row.append(f"{name}->[{', '.join(f'{c:.2f}' for c in C)}]")
    print(f"D={D:5.1f}  " + "  ".join(row))

# alternative compositions at the same browser density: fir only from the fir start, spruce only from the spruce start
D = 2.0
fin = {}
for name, C0 in starts.items():
    y0 = np.r_[np.repeat(np.array(C0), k)*2, C0]
    fin[name] = settle(rhs, y0, D, T=40000)[-S:]
assert fin["fir"][0] > 0.3 and fin["fir"][1] < 1e-3
assert fin["spruce"][1] > 0.3 and fin["spruce"][0] < 1e-3
print("alternative compositions at D = 2 confirmed")
