"""Vanishing order of Yehuda's words w_n(a, b) = u_n(a, bab^-1) in SL(d), d = 2, 3, 4, ...

Exact arithmetic in M_d(F_P[e]/e^K), with a = exp(eA), b = exp(eB) for random traceless A, B.
The order is a lower bound on nothing: it is the true order at this random point (mod P), which
equals the generic order with high probability. Yehuda proves order >= d_n for d = 2. The
question here is what happens for d >= 3, where his half-turn symmetry is not available.
Compare: Elkasapy's general construction grows like phi = 1.618 per doubling, tribonacci 1.839.
"""
import sys

import numpy as np

P = 1048573  # prime below 2^20, so that int64 sums of products cannot overflow for K < 2^20


def mul(x, y, K):
    out = np.zeros_like(x)
    for k in range(K):
        out[k] = (x[: k + 1] @ y[k::-1]).sum(axis=0) % P
    return out


def exp_series(A, K):
    """exp(eA) truncated at e^K."""
    d = A.shape[0]
    out = np.zeros((K, d, d), dtype=np.int64)
    term = np.eye(d, dtype=np.int64)
    for k in range(K):
        out[k] = term
        term = term @ A % P * pow(k + 1, -1, P) % P
    return out


def order(x):
    """Least k >= 1 with a nonzero coefficient, or len(x) if there is none below the cap."""
    for k in range(1, len(x)):
        if x[k].any():
            return k
    return len(x)


def run(d, levels, K, seed):
    rng = np.random.default_rng(seed)
    def traceless():
        M = rng.integers(0, P, (d, d))
        M[-1, -1] = (-sum(M[i, i] for i in range(d - 1))) % P
        return M
    A, B = traceless(), traceless()
    a, ai = exp_series(A, K), exp_series(-A % P, K)
    b, bi = exp_series(B, K), exp_series(-B % P, K)
    p, pi = a, ai
    q = mul(mul(b, a, K), bi, K)
    qi = mul(mul(b, ai, K), bi, K)
    def seed_word(p, q, pi, qi):
        return mul(mul(mul(p, p, K), qi, K), pi, K)
    # images of u under 1, tau, rho, tau*rho. tau: p<->q. rho: p->q^-1, q->p^-1. tau*rho: p->p^-1, q->q^-1
    u = {"1": seed_word(p, q, pi, qi), "t": seed_word(q, p, qi, pi),
         "r": seed_word(qi, pi, q, p), "tr": seed_word(pi, qi, p, q)}
    compose = {("1", "t"): "t", ("t", "t"): "1", ("r", "t"): "tr", ("tr", "t"): "r",
               ("1", "r"): "r", ("t", "r"): "tr", ("r", "r"): "1", ("tr", "r"): "t"}
    orders = [order(u["1"])]
    for n in range(levels):
        s = "t" if n % 2 == 0 else "r"
        u = {g: mul(u[g], u[compose[(g, s)]], K) for g in u}
        orders.append(order(u["1"]))
    return orders


if __name__ == "__main__":
    known = [2, 5, 8, 15, 28, 51, 94, 173, 318]
    got = run(2, 5, 60, 1)
    assert got[:6] == [max(a, b) for a, b in zip(got[:6], known)], got  # Yehuda: order >= d_n for d = 2
    I = exp_series(np.zeros((2, 2), dtype=np.int64), 5)
    assert order(mul(I, I, 5)) == 5
    print("self-check ok: order >= d_n for d = 2")
    print("Yehuda d_n:", known)
    levels, K = int(sys.argv[1]) if len(sys.argv) > 1 else 8, int(sys.argv[2]) if len(sys.argv) > 2 else 340
    for d in (2, 3, 4, 5, 8):
        print(f"d={d}:", [min(run(d, levels, K, s)[i] for s in range(2)) for i in range(levels + 1)], flush=True)
