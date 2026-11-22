"""Exact network design game with equal cost sharing on an undirected graph (fair cost sharing).

Model (arXiv 1211.2090, Sec. 2): k players, player i picks a simple s_i-t_i path,
edge cost c_e split equally among its users. NE = no player has a strictly cheaper
path given the others. PoS = min NE cost / min profile cost.
"""
from fractions import Fraction
from itertools import product
import numpy as np


def simple_paths(n, edges, s, t):
    """All simple s-t paths as frozensets of edge indices."""
    adj = {v: [] for v in range(n)}
    for j, (a, b) in enumerate(edges):
        adj[a].append((b, j)); adj[b].append((a, j))
    out = []

    def dfs(v, seen, used):
        if v == t:
            out.append(frozenset(used)); return
        for w, j in adj[v]:
            if w not in seen:
                dfs(w, seen | {w}, used + [j])
    dfs(s, {s}, [])
    return out


class Game:
    def __init__(self, n, edges, pairs):
        self.n, self.edges, self.pairs = n, list(edges), list(pairs)
        self.m = len(self.edges)
        self.paths = [simple_paths(n, self.edges, s, t) for s, t in pairs]
        # incidence matrices for fast float evaluation
        self.A = [np.array([[1.0 if e in p else 0.0 for e in range(self.m)] for p in ps])
                  for ps in self.paths]
        self.profiles = np.array(list(product(*[range(len(ps)) for ps in self.paths])))
        U = [A[self.profiles[:, i]] for i, A in enumerate(self.A)]   # (P, m) per player
        self.U = np.stack(U)            # (k, P, m)
        self.K = self.U.sum(0)          # (P, m) users per edge

    # ---------- float (fast) ----------
    def eval_float(self, c, tol=1e-9):
        c = np.asarray(c, float)
        used = self.K > 0
        cost = used @ c
        isne = np.ones(len(self.profiles), bool)
        for i, A in enumerate(self.A):
            share = np.where(self.K > 0, c / np.maximum(self.K, 1), 0.0)
            cur = (self.U[i] * share).sum(1)
            dev = (c / (self.K - self.U[i] + 1)) @ A.T        # (P, paths_i)
            isne &= dev.min(1) >= cur - tol
        return cost, isne

    def pos_float(self, c):
        cost, isne = self.eval_float(c)
        return cost[isne].min() / cost.min()

    # ---------- exact ----------
    def exact(self, c):
        """Exact (OPT, bestNE, PoS, list of NE profiles with costs). c: list of Fractions."""
        c = [Fraction(x) for x in c]
        k = len(self.pairs)
        best_opt, nes = None, []
        for prof in product(*[range(len(ps)) for ps in self.paths]):
            P = [self.paths[i][prof[i]] for i in range(k)]
            ke = [sum(e in p for p in P) for e in range(self.m)]
            cost = sum(c[e] for e in range(self.m) if ke[e])
            best_opt = cost if best_opt is None else min(best_opt, cost)
            ok = True
            for i in range(k):
                cur = sum(c[e] / ke[e] for e in P[i])
                for Q in self.paths[i]:
                    d = sum(c[e] / (ke[e] - (e in P[i]) + 1) for e in Q)
                    if d < cur:
                        ok = False; break
                if not ok:
                    break
            if ok:
                nes.append((cost, prof))
        nes.sort()
        return best_opt, nes[0][0], nes[0][0] / best_opt, nes


def paper_fig2b():
    # vertices: 0=t1=t3, 1=t2, 2=s1, 3=s2, 4=s3  (arXiv 1211.2090, Fig. 2(b))
    E = [((0, 1), 318), ((2, 0), 549), ((2, 3), 113), ((3, 1), 556),
         ((0, 4), 664), ((1, 4), 418), ((3, 4), 277)]
    g = Game(5, [e for e, _ in E], [(2, 0), (3, 1), (4, 0)])
    return g, [Fraction(w) for _, w in E]


if __name__ == "__main__":
    g, c = paper_fig2b()
    opt, ne, pos, nes = g.exact(c)
    print("profiles", len(g.profiles), "OPT", opt, "bestNE", ne, "PoS", pos, float(pos), "#NE", len(nes))
    assert opt == 1126 and ne == 1769 and pos == Fraction(1769, 1126) and len(nes) == 1
    assert abs(g.pos_float(c) - 1769 / 1126) < 1e-12
    print("OK: Fig. 2(b) reproduces PoS = 1769/1126 with a unique NE")
