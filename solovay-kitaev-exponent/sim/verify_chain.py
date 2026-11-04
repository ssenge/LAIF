"""Replay the best chain of a mixed.py log and compare its formal valuations with exact ones."""
import ast
import sys

sys.argv, log, stop = [sys.argv[0]], sys.argv[1], int(sys.argv[2])
from mixed import concat, image, true_vals

moves = []
on = False
for line in open(log):
    if line.startswith("best deep"):
        on = True
    elif on and line.startswith("    ("):
        moves.append(ast.literal_eval(line.strip()))
window = ("p",)
for mv in moves:
    w = concat([image(window[l], s) for l, s in mv])
    window = ((w,) + window)[:2]
    if len(w) > stop:
        break
    K = min(4 * len(w) + 8, 2200)
    print(f"L={len(w):6d} exact vals (K={K}): {true_vals(w, K)}", flush=True)
