"""Explicit finite weighted 4-design in C^d from a certificate measure on (a, b, c) (cert_d{d}_t4.json).
Each support point (a, b, c, w) gives the states (sqrt a, +-sqrt b e^{i theta}, sqrt(1 - a - b) u), cos^2 theta = c,
with and without complex conjugation, where u runs over a cubature of the unit sphere of C^{d-2}: 8 phases per
coordinate (exact for phase frequencies up to 7) times Gauss-Legendre nodes for the uniform law of the moduli
(exact for the degrees that occur). This is an exact quadrature of the H-average, so the ensemble is a 4-design.
The script checks E|<x|phi>|^{2t} = 1/C(d+t-1, t) for t <= 4 at random x (this fixes the (t, t) moments), and
compares the Fisher form at the frame (e_1, e_2), computed from the state vectors, with the certificate value."""
import sys, json, itertools
from fractions import Fraction as Fr
from math import comb
import numpy as np

def cubature(m):
    """nodes r (squared moduli) with weights for the uniform law on the simplex of dimension m - 1."""
    if m == 1: return [(np.array([1.0]), 1.0)]
    x, wx = np.polynomial.legendre.leggauss(6); x = (x + 1) / 2; wx = wx / 2
    if m == 2: return [(np.array([xi, 1 - xi]), wi) for xi, wi in zip(x, wx)]
    assert m == 3
    return [(np.array([xi, (1 - xi) * yi, (1 - xi) * (1 - yi)]), 2 * (1 - xi) * wi * wj) for xi, wi in zip(x, wx) for yi, wj in zip(x, wx)]

def ensemble(J):
    d = J["d"]; m = d - 2; NP = 8
    ph = np.exp(2j * np.pi * np.arange(NP) / NP)
    T, Tw = [], []
    for r, wr in cubature(m):
        for P in itertools.product(ph, repeat=m):
            T.append(np.sqrt(r) * np.array(P)); Tw.append(wr / NP ** m)
    T = np.array(T); Tw = np.array(Tw)
    S, pi = [], []
    for row in J["design"]:
        A, B, C, w = (float(Fr(x)) for x in row)
        th = np.arccos(np.sqrt(C)); rho = np.sqrt(max(1 - A - B, 0.0))
        for sg in (1, -1):
            head = np.array([np.sqrt(A), sg * np.sqrt(B) * np.exp(1j * th)])
            X = np.hstack([np.tile(head, (len(T), 1)), rho * T])
            for Y in (X, X.conj()):
                S.append(Y); pi.append(w * Tw / 4)
    return np.vstack(S), np.concatenate(pi)

def frame_form(S, pi, d):
    a = S[:, 0]; keep = np.abs(a) > 0                     # outcomes with <phi|psi> = 0 are omitted
    z = np.conj(S[keep, 1]) * a[keep] / np.abs(a[keep])  # <phi|e_2> <psi|phi> / |<psi|phi>|
    return float(np.sum(d * pi[keep] * z.real ** 2))

if __name__ == "__main__":
    J = json.load(open(sys.argv[1])); d = J["d"]
    S, pi = ensemble(J)
    assert abs(pi.sum() - 1) < 1e-12 and (pi > 0).all() and np.abs(np.linalg.norm(S, axis=1) - 1).max() < 1e-12
    rng = np.random.default_rng(1)
    X = rng.normal(size=(200, d)) + 1j * rng.normal(size=(200, d)); X /= np.linalg.norm(X, axis=1, keepdims=True)
    ov = np.abs(S.conj() @ X.T) ** 2
    err = [np.abs(pi @ ov ** t - 1 / comb(d + t - 1, t)).max() for t in (1, 2, 3, 4, 5)]
    assert max(err[:4]) < 1e-12, err
    F = frame_form(S, pi, d); U = float(Fr(J["upper"]))
    assert abs(F - U) < 1e-12, (F, U)
    print(f"d={d}: {len(S)} states, 4-design error {max(err[:4]):.1e} (t = 5: {err[4]:.1e}), frame Fisher form {F:.12f} = upper {U:.12f}")
