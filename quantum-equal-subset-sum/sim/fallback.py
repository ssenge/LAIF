"""The same method with the older k-SUM route: meet in the middle by claw finding, (h(p)+1-p)/3,
in place of 7-SUM, so with no use of the 7-SUM theorem. Also writes the data for the paper's figure."""
from exact import labels
from opt import H, seven_sum
import sys

mitm = lambda p: (H(p, 1-p) + 1 - p)/3
grid = [k/400 for k in range(4, 200)]
vals = [(p, labels(p)[0]) for p in grid]
print("max min(claw, labels):", max((min(mitm(p), v), p) for p, v in vals))
with open("curves.dat", "w") as f:
    for p, v in vals:
        f.write(f"{p:.4f} {seven_sum(p):.5f} {v:.5f}\n")
