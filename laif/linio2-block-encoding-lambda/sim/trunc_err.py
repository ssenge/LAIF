"""Gamma point: Frobenius norm of the ERI change caused by the second-factorization cutoff, per factor variant."""
import sys, numpy as np, dflam
def trunc_factor(X, th):
    out = []
    for x in X:
        e, V = np.linalg.eigh(x)
        keep = np.abs(e) * np.abs(e).sum() >= th
        out.append((V[:, keep] * e[keep]) @ V[:, keep].conj().T)
    return np.array(out)
def err(X, th):
    Xt = trunc_factor(X, th)
    F, Ft = X.reshape(len(X), -1), Xt.reshape(len(X), -1)
    return np.linalg.norm(Ft.T @ Ft.conj() - F.T @ F.conj())
if __name__ == "__main__":
    d = np.load(sys.argv[1], allow_pickle=True)
    X = d["L"][0, 0].real
    U = np.load(sys.argv[2], allow_pickle=True)
    U = (U[0, 0] if U.dtype == object else U).real
    for th in [1e-4, 3e-4, 1e-3, 3e-3, 1e-2]:
        print(th, "gdf", err(X, th), "gauge", err(U, th))
