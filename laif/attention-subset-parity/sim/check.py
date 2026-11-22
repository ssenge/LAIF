"""One softmax attention head (row-wise maps phi_Q, phi_K, phi_V of (x_j, j), output map psi) computes chi_S.

Embedding dimension m = 1, one head. Key c 1[j in S] with c = ceil(ln(4 k N)), query 1, value x_j.
The output is then within 1/(2k) of the mean of x over S, and psi rounds it to the parity of S.
Second head (S given as input marks s_j): m = 2, all scores 0, value (s_j x_j, s_j), exact counts.
Asserts: exact equality with chi_S on every input of small N, on random inputs for large N,
also after rounding the head output to p = ceil(log2(4k)) + 2 fractional bits.
"""
import itertools, math
import numpy as np

rng = np.random.default_rng(1)


def head(X, S, N):
    k = len(S)
    c = math.ceil(math.log(4 * k * N))
    key = np.zeros(N); key[list(S)] = c
    w = np.exp(key - key.max()); w /= w.sum()                # softmax of q k_j with q = 1, same for every row
    z = X @ w                                                # attention output, identical at every token
    p = math.ceil(math.log2(4 * k)) + 2
    z = np.round(z * 2 ** p) / 2 ** p                         # p-bit fixed-point output
    w_out = 1 - w[list(S)].sum()
    assert 2 * k * w_out < 1 / 2                               # weight outside S
    t = k - 2 * np.rint((k - z * k) / 2)                     # psi: nearest count sum_{j in S} x_j (same parity as k)
    return np.where(((k - t) / 2) % 2 == 0, 1, -1)


for N in range(1, 13):
    X = np.array(list(itertools.product([-1, 1], repeat=N)))
    for k in range(1, N + 1):
        for S in itertools.combinations(range(N), k):
            assert (head(X, S, N) == X[:, list(S)].prod(1)).all()
for N in [100, 1000, 10 ** 5]:
    for k in [1, 2, 3, 7, 20, 50]:
        if k > N: continue
        S = rng.choice(N, k, replace=False)
        X = rng.choice([-1, 1], size=(200, N))
        assert (head(X, S, N) == X[:, S].prod(1)).all()


def marked(X, s):
    N = len(s)
    z1, z2 = (X * s).mean(1), s.mean() * np.ones(len(X))        # uniform softmax: weights exactly 1/N
    p = math.ceil(math.log2(N)) + 2
    z1, z2 = np.round(z1 * 2 ** p) / 2 ** p, np.round(z2 * 2 ** p) / 2 ** p
    t, k = np.rint(z1 * N), np.rint(z2 * N)                      # exact counts sum_{s_j = 1} x_j and |S|
    return np.where(((k - t) / 2) % 2 == 0, 1, -1)


for N in range(1, 11):
    X = np.array(list(itertools.product([-1, 1], repeat=N)))
    for s in itertools.product([0, 1], repeat=N):
        s = np.array(s)
        assert (marked(X, s) == np.where(s == 1, X, 1).prod(1)).all()
print("all checks passed")
