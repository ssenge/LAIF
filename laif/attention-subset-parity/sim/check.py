"""One softmax attention unit in the model of [2] (input map, unit with Q, K, V, output map) computes chi_S.

Proposition 1 (S fixed): embedding e_j = 1[j in S] x_j in R^1, Q = K = 0, V = 1.
Proposition 2 (S as input marks): embedding e_j = (s_j x_j, s_j) in R^2, Q = K = 0, V = I.
Variant of Proposition 2 without positions (input dimension 1, input y_j = s_j x_j): e_j = (y_j, y_j^2).
The unit output is rounded to p = ceil(log2 N) + 2 fractional bits; the output map recovers the counts.
Asserts: exact equality with chi_S on every input of small N, on random inputs for large N.
"""
import itertools, math
import numpy as np

rng = np.random.default_rng(1)


def unit(E, Q, K, V):                                  # E: batch x N x m, softmax(E Q K^T E^T) E V, row 0
    sc = np.einsum('bm,mn,kn,bjk->bj', E[:, 0], Q, K, E)          # scores of row 0 only
    w = np.exp(sc - sc.max(1, keepdims=True)); w /= w.sum(1, keepdims=True)
    return np.einsum('bj,bjm,mn->bn', w, E, V)


def rnd(z, N):
    p = math.ceil(math.log2(N)) + 2
    return np.round(z * 2 ** p) / 2 ** p


def par(t, k):
    return np.where(((k - t) / 2) % 2 == 0, 1, -1)


def prop1(X, S):
    N = X.shape[1]; ind = np.zeros(N); ind[list(S)] = 1
    E = (X * ind)[:, :, None]
    z = rnd(unit(E, np.zeros((1, 1)), np.zeros((1, 1)), np.eye(1)), N)
    return par(np.rint(N * z[:, 0]), len(S))           # output map knows k = |S|


def prop2(X, s, positions=True):
    N = X.shape[1]
    y = X * s
    E = np.stack([y, np.broadcast_to(s, X.shape)], 2) if positions else np.stack([y, y ** 2], 2)
    z = rnd(unit(E, np.zeros((2, 2)), np.zeros((2, 2)), np.eye(2)), N)
    return par(np.rint(N * z[:, 0]), np.rint(N * z[:, 1]))


for N in range(1, 13):
    X = np.array(list(itertools.product([-1, 1], repeat=N)))
    for k in range(1, N + 1):
        for S in itertools.combinations(range(N), k):
            assert (prop1(X, S) == X[:, list(S)].prod(1)).all()
for N in [100, 1000, 10 ** 4]:
    for k in [1, 2, 3, 7, 20, 50]:
        for _ in range(3):
            S = rng.choice(N, k, replace=False)
            X = rng.choice([-1, 1], size=(100, N))
            assert (prop1(X, S) == X[:, S].prod(1)).all()
for N in range(1, 11):
    X = np.array(list(itertools.product([-1, 1], repeat=N)))
    for s in itertools.product([0, 1], repeat=N):
        s = np.array(s); target = np.where(s == 1, X, 1).prod(1)
        assert (prop2(X, s) == target).all() and (prop2(X, s, False) == target).all()
print("all checks passed")
