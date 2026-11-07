"""Bases for the weighted corollaries: one extension oracle per run (weighted approximate monotone local
search of Esmer, Kulik, Marx, Neuen, Sharma 2023 allows a single pair (alpha, c)), so the base is the
minimum over the oracles of best({(alpha, c)}, beta); the quantum base is its square root."""
import math
from bounds import best_base, up, worst

WEIGHTED = {  # problem: oracles (alpha, c); alpha = 1 are trees, c = 1 polynomial-time approximations
    "Weighted Vertex Cover": [(1, 1.381), (2, 1)],
    "Weighted 3-Hitting Set": [(1, 2.168), (3, 1)],
    "Weighted 4-Hitting Set": [(1, 4.0), (4, 1)],
    "Weighted 5-Hitting Set": [(1, 5.0), (5, 1)],
    "Weighted Feedback Vertex Set": [(2, 1)],
    "Weighted Multicut on Trees": [(2, 1)],
}
BETAS = (1.1, 1.2, 1.5, 1.8)

if __name__ == "__main__":
    # Table 1 of the weighted paper: (1, 1.363) gives 1.158 at beta = 1.1, (2, 1) gives 1.659
    assert abs(best_base([(1, 1.363)], 1.1) - 1.158) < 6e-4
    assert abs(best_base([(2, 1)], 1.1) - 1.659) < 6e-4
    print("reference values reproduced")
    print("quantum exact Weighted Vertex Cover through the 1.381^k tree:", up(math.sqrt(2 - 1 / 1.381)))
    for name, L in WEIGHTED.items():
        row = []
        for beta in BETAS:
            b, o = min((best_base([o], beta), o) for o in L)
            ex = worst(1000, beta, [o]) - 1000 * math.log(b)    # exact discrete cost at n = 1000
            assert ex <= 2 * math.log(1001), (name, beta, ex)
            row.append(f"beta={beta} {o}: {b:.5f} -> {math.sqrt(b):.5f} <= {up(math.sqrt(b))}")
        print(f"{name:36s} " + "  ".join(row))
