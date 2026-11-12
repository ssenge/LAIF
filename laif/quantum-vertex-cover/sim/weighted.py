"""The walk on a computation tree, where a vertex v takes t_v steps from its parent, as used in Theorem 1. Each edge of a
Vertex Cover search tree is expanded into t_v vertices of weight t_v, with t_v = 1 + B(v)^{3/8}, the cost of a value call of log
measure (3/4) log B(v) under Theorem 1, for B = x^budget. Checks, from the Schur form of U = R_B R_A: with a marked leaf, the root
has weight at least 1/2 on eigenvalue 1; without one, its weight on phases |theta| <= eps is at most eps^2 (1 + D T), with
T = sum t_v^2. Exact linear algebra on small trees: it tests the operator, not the nesting of circuits."""
import math
import random
import sys
import numpy as np
from scipy.linalg import schur
from tree import Tree, TooLarge, random_regular

X = 1.4656


def expand(t, times):
    """Parent, weight and marked flag of the expanded tree, and its even or odd depth."""
    D = max(1, max(t.depth))
    parent, weight, marked, depth = [None], [1/D], [False], [0]
    end = {0: 0}
    for v in range(1, t.T):
        at = end[t.parent[v]]
        for _ in range(times[v]):
            parent.append(at)
            weight.append(float(times[v]))
            marked.append(False)
            depth.append(depth[at] + 1)
            at = len(parent) - 1
        marked[at] = t.marked[v]
        end[v] = at
    return parent, weight, marked, depth, D


def operator(parent, weight, marked, depth):
    size = len(parent)
    kids = [[] for _ in range(size)]
    for y in range(1, size):
        kids[parent[y]].append(y)
    RA, RB = np.eye(size, dtype=complex), np.eye(size, dtype=complex)
    for x in range(size):
        if marked[x]:
            continue
        v = np.zeros(size, complex)
        v[x] = math.sqrt(weight[x])
        for y in kids[x]:
            v[y] = math.sqrt(weight[y])
        v /= np.linalg.norm(v)
        if depth[x] % 2 == 0:
            RA -= 2*np.outer(v, v.conj())
        else:
            RB -= 2*np.outer(v, v.conj())
    return RB @ RA


if __name__ == "__main__":
    rng = random.Random(11)
    bad = yes = no = tested = 0
    low, high = 1.0, 0.0
    print(f"{'graph':14} {'k':>3} {'T nodes':>7} {'expanded':>8} {'D':>3} {'sum t^2':>8} {'root on 1':>9} {'worst ratio':>11}")
    for d, sizes in ((3, (16, 20, 24, 30)), (4, (14, 18, 22)), (6, (14, 18))):
        for size in sizes:
            adj = random_regular(size, d, rng)
            for frac in (.4, .5, .6, .7):
                k = int(frac*size)
                try:
                    t = Tree(adj, k, limit=120)
                except TooLarge:
                    continue
                if t.T < 3:
                    continue
                times = [0] + [1 + int(X**(.375*max(b, 0))) for b in t.budget[1:]]
                parent, weight, marked, depth, D = expand(t, times)
                if len(parent) > 900:
                    continue
                A, Z = schur(operator(parent, weight, marked, depth), output="complex")
                theta = np.abs(np.angle(np.diag(A)))/2
                root = np.abs(Z[0].conj())**2
                on_one = root[theta < 1e-9].sum()
                total = sum(c*c for c in times)
                if t.has_marked():
                    yes += 1
                    low = min(low, on_one)
                    bad += on_one < .5 - 1e-9
                    ratio = 0.0
                else:
                    no += 1
                    ratio = 0.0
                    for eps in theta[theta*theta*(1 + D*total) < 1]:
                        ratio = max(ratio, root[theta <= eps].sum()/(eps*eps*(1 + D*total)))
                    tested += ratio > 0
                    high = max(high, ratio)
                    bad += ratio > 1 + 1e-9
                print(f"{d}-reg n={size:<8} {k:>3} {t.T:>7} {len(parent):>8} {D:>3} {total:>8} {on_one:>9.3f} {ratio:>11.3f}")
    bad += yes == 0 or tested == 0
    print(f"{yes} trees with a marked leaf: root on eigenvalue 1 at least {low:.3f}. {no} without, {tested} with a phase inside the range: weight on small phases at most {high:.3f} of the bound. {bad} failed checks")
    sys.exit(1 if bad else 0)
