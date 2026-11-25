"""Recursions U -> W(U) = S_n^{k1} S^{j1} ... S^{j_{r-1}} S_n^{kr}, n = O(U) e_z, S = R_z(pi/2).
G(word, t) is the z-component of the new axis as a function of t = n_z; W uses 2r copies of U."""
import itertools, numpy as np

def rotn(t, k):                       # rotations of R^3 by k quarter-turns about n(t) = (sqrt(1-t^2), 0, t), batched
    s = np.sqrt(np.clip(1 - t * t, 0, None)); z = np.zeros_like(t)
    K = np.stack([np.stack([z, -t, z], -1), np.stack([t, z, -s], -1), np.stack([z, s, z], -1)], -2)
    th = k * np.pi / 2
    return np.eye(3) + np.sin(th) * K + (1 - np.cos(th)) * K @ K

SZ = np.array([[0, -1, 0], [1, 0, 0], [0, 0, 1.0]])

def G(word, t):
    t = np.atleast_1d(np.asarray(t, float)); M = np.broadcast_to(np.eye(3), t.shape + (3, 3))
    for typ, k in word:
        M = M @ (rotn(t, k) if typ == "n" else np.linalg.matrix_power(SZ, k))
    return M[..., 2, 2]

def words(r):
    for ks in itertools.product([1, 2, 3], repeat=r):
        for js in itertools.product([1, 2, 3], repeat=r - 1):
            w = [("n", ks[0])]
            for j, k in zip(js, ks[1:]): w += [("z", j), ("n", k)]
            yield w
