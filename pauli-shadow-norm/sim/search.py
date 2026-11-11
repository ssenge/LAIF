# longer search for the worst-case ratio S(rho)/Tr(rho^2); saves the best rho per N
import sys, numpy as np, shadow as S
N, restarts, iters = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
rng = np.random.default_rng(N)
Us, FN = S.setup(N)
best = (0, None, None)
for rank in [1, 2, 4, 8, 2 ** N]:
    if rank > 2 ** N:
        continue
    for _ in range(restarts):
        v, rho = S.ascend(N, Us, FN, rng, rank, iters=iters)
        if v > best[0]:
            best = (v, rho, rank)
    print(f"N={N} rank<={rank}: best so far {best[0]:.5f} (rank {best[2]}), per qubit {best[0] ** (1 / N):.5f}", flush=True)
np.save(f"best_rho_N{N}.npy", best[1])
