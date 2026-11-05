"""Tests the two facts behind the quantum walk on trees of real Vertex Cover instances, from the spectrum of U = R_B R_A.
Marked vertex: the eigenvalue 1 has squared overlap at least 1/2 with the root. No marked vertex: the squared weight of the
root on phases of absolute value at most 2 chi is at most (2 chi sqrt(T n))^2, up to the constant of the cited lemma. The
measured quantity is the phase below which the root has squared weight 1/4, against 1/sqrt(T n)."""
import random
import sys
import numpy as np
from scipy.linalg import schur
from tree import Tree, TooLarge, reflections, random_regular, minimum_cover


def spectrum(t):
    RA, RB = reflections(t)
    A, Z = schur(RB @ RA, output="complex")     # unitary, so A is diagonal and Z is orthonormal also on degenerate eigenvalues
    return np.angle(np.diag(A)), np.abs(Z[0].conj())**2


def weight_up_to(phase, wt, chi):
    return wt[np.abs(phase) <= chi].sum()


if __name__ == "__main__":
    rng = random.Random(1)
    print(f"{'graph':14} {'k':>3} {'T':>6} {'n':>3} {'marked':>6} {'root on 1':>10} {'phase at 1/4':>13} {'x sqrt(Tn)':>11}")
    bad = 0
    for d, sizes in ((3, (16, 24, 36, 48)), (4, (14, 18, 26, 34)), (6, (16, 24, 30, 36)), (8, (16, 24, 30, 36)), (12, (20, 26, 32))):
        for size in sizes:
            for seed in range(2):
                adj = random_regular(size, d, rng)
                try:
                    m = minimum_cover(adj)
                except TooLarge:
                    continue
                for k in (m - 1, m):
                    t = Tree(adj, k)
                    if t.T > 1000 or t.T < 3:
                        continue
                    phase, wt = spectrum(t)
                    on1 = weight_up_to(phase, wt, 1e-9)
                    order = np.argsort(np.abs(phase))
                    cum = np.cumsum(wt[order]/wt.sum())
                    at = np.abs(phase)[order][np.searchsorted(cum, .25)]
                    scaled = at*np.sqrt(t.T*t.n)
                    if t.has_marked():
                        bad += on1/wt.sum() < .5
                    else:
                        bad += scaled < 1
                    print(f"{d}-reg n={size:<6} {k:3} {t.T:6} {t.n:3} {sum(t.marked):6} {on1/wt.sum():10.3f} {at:13.4f} {scaled:11.3f}", flush=True)
    print(f"{bad} failed checks")
    sys.exit(1 if bad else 0)
