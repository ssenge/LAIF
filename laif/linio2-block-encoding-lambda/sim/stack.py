"""Stack the reductions on one k-mesh: GDF baseline, shift only, gauge-optimized factor, gauge + shift.
Lambda re-evaluated with dflam.lam on the transformed (hcore, L); Toffolis from openfermion's pbc DF cost model.
Usage: stack.py data.npz rotL.npy [label]"""
import sys, json
import numpy as np
from scipy.optimize import minimize
import dflam, opt_shift
from openfermion.resource_estimates.pbc.df.compute_df_resources import compute_cost

def shift_opt(L, hc, ne):
    obj, beta, naux = opt_shift.make_objective(L, hc, ne)
    r = minimize(obj, np.zeros(naux + 1), jac=True, method="L-BFGS-B", options={"maxiter": 3000, "maxfun": 6000})
    return dflam.shifted(hc, L, r.x[:-1], r.x[-1], ne)

def report(name, hc, L, mkq, mesh, nmo, ne):
    nk = len(hc)
    out = {"variant": name}
    naux = max(L[k, j].shape[0] for k in range(nk) for j in range(nk))
    for th in [1e-13, 1e-4, 1e-3]:
        lt, l1, l2, neig = dflam.lam(hc, L, mkq, th, True)
        cost = compute_cost(2 * nmo, lt, 2 * naux * nk, neig, list(mesh))
        out[f"{th:g}"] = {"lambda": lt, "one": l1, "two": l2, "num_eig": neig,
                          "toffoli": int(cost.total_toffolis), "per_step": int(cost.toffolis_per_step), "qubits": int(cost.logical_qubits)}
    return out

if __name__ == "__main__":
    d = np.load(sys.argv[1], allow_pickle=True)
    L, hc, kpts, mesh = d["L"], d["hcore"], d["kpts"], list(d["mesh"])
    import lno_cell
    mkq = dflam.kmap(kpts, lno_cell.r3m().lattice_vectors())
    nk, nmo = len(hc), hc[0].shape[0]
    ne = int(d["nelec"]) * nk
    Lr = np.load(sys.argv[2], allow_pickle=True)
    if Lr.dtype != object:                       # Gamma output of rot_gamma.py: (r, m, m)
        tmp = np.empty((1, 1), dtype=object); tmp[0, 0] = Lr; Lr = tmp
    # the rotated factor gives the same ERI blocks
    # every ERI block per Q, checked with a random sketch of the Gram matrix F_Q^T conj(F_Q) (vectors stacked over k)
    rng = np.random.default_rng(1)
    for Q in range(nk):
        F0 = np.concatenate([L[k, mkq[Q, k]].reshape(L[k, mkq[Q, k]].shape[0], -1) for k in range(nk)], axis=1)
        F1 = np.concatenate([Lr[k, mkq[Q, k]].reshape(Lr[k, mkq[Q, k]].shape[0], -1) for k in range(nk)], axis=1)
        Om = rng.normal(size=(F0.shape[1], 8)) + 1j * rng.normal(size=(F0.shape[1], 8))
        g0, g1 = F0.T @ (F0.conj() @ Om), F1.T @ (F1.conj() @ Om)
        assert np.abs(g0 - g1).max() < 1e-6 * np.abs(g0).max(), (Q, np.abs(g0 - g1).max())
    rows = [report("gdf", hc, L, mkq, mesh, nmo, ne)]
    h2, L2 = shift_opt(L, hc, ne); rows.append(report("gdf+shift", h2, L2, mkq, mesh, nmo, ne))
    rows.append(report("gauge", hc, Lr, mkq, mesh, nmo, ne))
    h3, L3 = shift_opt(Lr, hc, ne); rows.append(report("gauge+shift", h3, L3, mkq, mesh, nmo, ne))
    lab = sys.argv[3] if len(sys.argv) > 3 else sys.argv[1]
    with open("stack.jsonl", "a") as fh:
        for r in rows:
            r["system"] = lab
            fh.write(json.dumps(r) + "\n")
            print(r["variant"], {k: (round(v["lambda"], 2), v["num_eig"], f'{v["toffoli"]:.3g}') for k, v in r.items() if isinstance(v, dict)})
