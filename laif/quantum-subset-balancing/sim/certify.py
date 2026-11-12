"""Certifies the exponent over all symmetric profiles on [-d:d] by adaptive boxes in (w_1, ..., w_d), w_0 = 1 - sum.

For a fixed kernel W(L, x, y | c) each of a, a0, ux, uy is concave in the profile: a = H(L) - sum pi_c H(L | c), a0 is
linear, and H(x | L) is concave in the joint law, which is linear in pi. So the tangent at the centre of a box bounds
each cost term from above on the whole box, and a linear function is largest at a corner. Three options per box:
quantum search over typed vectors, the empty scheme, and a kernel solved at the centre. Side conditions are linear in
pi and are checked at the corners. Floats with a slack here; the certificate is re-evaluated in interval arithmetic by
verify.py from the saved kernels. Usage: python certify.py d target [start_size]
"""
import math, os, pickle, sys
os.environ["OMP_NUM_THREADS"] = "1"
from itertools import product
from multiprocessing import Pool
import numpy as np
from opt import Scheme, wide_labels, profile, entropy

SLACK = 1e-7
MIN_RES = 1e-3      # a0 + sigma at every corner, so that P0 is exponential
d = int(sys.argv[1]) if __name__ == "__main__" or len(sys.argv) > 1 else 2
target = float(sys.argv[2]) if len(sys.argv) > 2 else 1.0
S = Scheme(d, wide_labels(d))
CS = np.arange(-d, d + 1)


def pi_vec(w):
    """pi as an array over CS, from (w_1, ..., w_d). Works off the simplex too, as a linear map."""
    w0 = 1 - sum(w)
    return np.array([w0 if c == 0 else w[abs(c) - 1]/2 for c in CS])


def q_of(W, pi):
    return W*pi[S.c + d]


def tangents(W, pi0, sigma):
    """Value and gradient (in q) of the cost terms at pi0, as a list of (value, grad, const)."""
    q0 = q_of(W, pi0)
    q0s = np.maximum(q0, 1e-300)
    (a, a0, ux, uy), (da, da0, dux, duy) = S.parts(q0s)
    terms = [(a/2 + a0, da/2 + da0, sigma),
             (a/2 + 2/3*(ux - a0), da/2 + 2/3*(dux - da0), sigma/2 - 2/3*sigma),
             (a/2 + 2/3*(uy - a0), da/2 + 2/3*(duy - da0), sigma/2 - 2/3*sigma),
             (a/2, da/2, sigma/2)]
    return q0, terms


def corners(lo, hi):
    return [np.array(v) for v in product(*zip(lo, hi))]


def bound_kernel(W, sigma, lo, hi, center):
    pi0 = pi_vec(center)
    q0, terms = tangents(W, pi0, sigma)
    best = -9.0
    for v in corners(lo, hi):
        q = q_of(W, pi_vec(v))
        for val, grad, const in terms:
            # only cells with positive mass at the centre carry a term; a zero kernel entry stays zero
            best = max(best, val + float(grad[W > 0] @ (q - q0)[W > 0]) + const)
    return best


def vary_mask(W):
    """Cells in a (c, L) class with at least two positive kernel entries: only there do counted representations vary."""
    return (W > 0) & (np.bincount(S.kCL, weights=(W > 0).astype(float))[S.kCL] > 1)


def sides_ok(W, sigma, lo, hi):
    """Representations distinct and P0 exponential, at every corner of the box. X != Y is forced by a pinned coordinate."""
    vary = vary_mask(W)
    coeff = a0_coeff(W)
    for v in corners(lo, hi):
        pi = pi_vec(v)
        q = q_of(W, pi)
        if vary.any() and 1 - pi[d] - q[vary].sum() <= 1e-3:
            return False
        if float(q @ coeff) + sigma <= MIN_RES:
            return False
    return True


def a0_coeff(W):
    """a0 is linear in q for a fixed kernel: per cell, -log2 of W(L, x, y | c) / W(L | c)."""
    wcl = np.bincount(S.kCL, weights=W)[S.kCL]
    out = np.zeros_like(W)
    pos = W > 0
    out[pos] = -np.log2(W[pos]/wcl[pos])
    return out


def kernel_of(q, pi):
    W = np.zeros(S.n)
    for i in range(S.n):
        if S.c[i] in pi and pi[S.c[i]] > 0:
            W[i] = q[i]/pi[S.c[i]]
    W[W < 1e-9] = 0
    tot = np.bincount(S.c + d, weights=W, minlength=2*d + 1)
    return W/tot[S.c + d]


def empty_kernel():
    W = np.zeros(S.n)
    for i in range(S.n):
        if S.labs[S.L[i]] in ((2*d, 0, d), (0, 2*d, -d)):
            W[i] = 0.5
    return W


def grover_bound(lo, hi, center):
    pi0 = pi_vec(center)
    grad = -np.log2(pi0) - 1/math.log(2)
    val = entropy({c: pi0[i] for i, c in enumerate(CS)})/2
    return max(val + float(grad @ (pi_vec(v) - pi0))/2 for v in corners(lo, hi))


def centre_of(lo, hi):
    c = (np.array(lo) + np.array(hi))/2
    s = c.sum()
    if s >= 1 - 1e-4:
        c = c/s*(1 - 1e-4)
    return np.maximum(c, 1e-6)


def check_box(box):
    """Returns ('ok', option, kernel, sigma) or ('split', box)."""
    lo, hi = box
    if sum(lo) >= 1:
        return ("out", box)
    c = centre_of(lo, hi)
    if grover_bound(lo, hi, c) <= target - SLACK:
        return ("ok", box, "grover", None, None)
    W = empty_kernel()
    (_, a0, ux, uy), _ = S.parts(np.maximum(q_of(W, pi_vec(c)), 1e-300))
    sigma = max(1e-3, 4*max(ux, uy)/7)
    if bound_kernel(W, sigma, lo, hi, c) <= target - SLACK and sides_ok(W, sigma, lo, hi):
        return ("ok", box, "empty", W, sigma)
    w = [1 - c.sum()] + list(c)
    pi = profile(d, w)
    v, q = S.solve(pi, starts=2, seed=int(c.sum()*1e6) % 2**31, margin=0.02)
    if q is None or v > target:
        return ("split", box)
    W = kernel_of(q, pi)
    (_, a0, ux, uy), _ = S.parts(np.maximum(q_of(W, pi_vec(c)), 1e-300))
    sigma = max(1e-3, (4*max(ux, uy) - 10*a0)/7)
    if bound_kernel(W, sigma, lo, hi, c) <= target - SLACK and sides_ok(W, sigma, lo, hi):
        return ("ok", box, "kernel", W, sigma)
    return ("split", box)


def split(box):
    lo, hi = box
    mid = [(a + b)/2 for a, b in zip(lo, hi)]
    return [(tuple(l if not b else m for l, m, b in zip(lo, mid, bits)),
             tuple(m if not b else h for h, m, b in zip(hi, mid, bits)))
            for bits in product((0, 1), repeat=len(lo))]


if __name__ == "__main__":
    size0 = float(sys.argv[3]) if len(sys.argv) > 3 else 1/8
    m = round(1/size0)
    boxes = [(tuple(i*size0 for i in t), tuple((i + 1)*size0 for i in t)) for t in product(range(m), repeat=d) if sum(t) < m]
    done, depth, counts = [], 0, {"grover": 0, "empty": 0, "kernel": 0}
    with Pool(11) as p:
        while boxes and depth < 12:
            res = p.map(check_box, boxes, chunksize=8)
            boxes = []
            for r in res:
                if r[0] == "ok":
                    done.append(r[1:])
                    counts[r[2]] += 1
                elif r[0] == "split":
                    boxes.extend(split(r[1]))
            depth += 1
            print(f"depth {depth}: certified {len(done)} {counts}, to split {len(boxes)}, size {size0/2**depth:.5f}", flush=True)
    print(f"d={d} target={target}: {'CERTIFIED' if not boxes else 'NOT CERTIFIED'}; {len(done)} boxes {counts}; baseline {2/7*math.log2(2*d+1):.5f}")
    with open(f"cert_{d}.pkl", "wb") as f:
        pickle.dump(dict(d=d, target=target, done=done, left=boxes), f)
    sys.exit(0 if not boxes else 1)
