"""Largest vanishing order r of any nontrivial word of length <= 2*ell in SL(d).

Meet in the middle: two distinct reduced words u, v of length <= ell that agree in
M_d(F_P[e]/e^t) at a random point (a, b) = (exp(eA), exp(eB)) give the nontrivial word u v^-1 of
length <= 2*ell and order >= t. All reduced words are tried, so this is exhaustive for words of the
form u v^-1 with |u|, |v| <= ell, which is every word of length <= 2*ell.
Each record is rechecked at a second random point, so false collisions are removed.
Large d approximates the free group (nilpotence degree, Kuperberg Thm 5.x: lim ccan_SU(d) = nil).
"""
import sys

import numpy as np

from ccan import P, exp_series, mul, order

LETTERS = "aAbB"
INV = {0: 1, 1: 0, 2: 3, 3: 2}


def traceless(rng, d):
    M = rng.integers(0, P, (d, d))
    M[-1, -1] = (-sum(M[i, i] for i in range(d - 1))) % P
    return M


def generators(d, K, seed):
    rng = np.random.default_rng(seed)
    A, B = traceless(rng, d), traceless(rng, d)
    return [exp_series(A, K), exp_series(-A % P, K), exp_series(B, K), exp_series(-B % P, K)]


def word_order(word, d, K, seed):
    g = generators(d, K, seed)
    x = exp_series(np.zeros((d, d), dtype=np.int64), K)
    for ch in word:
        x = mul(x, g[LETTERS.index(ch)], K)
    return order(x)


def right_mul(F, g, K):
    out = np.zeros_like(F)
    for k in range(K):
        for i in range(k + 1):
            out[:, k] += F[:, i] @ g[k - i]
        out[:, k] %= P
    return out


def search(d, ell, K, seed=1):
    g = generators(d, K, seed)
    rng = np.random.default_rng(seed + 100)
    R = rng.integers(1, P, (K, 4, d, d))
    F = exp_series(np.zeros((d, d), dtype=np.int64), K)[None]
    last = np.array([-1])
    words = [""]
    parents, letters = [np.array([-1])], [np.array([-1])]
    def hashes(F):
        H = np.zeros((len(F), K), dtype=np.uint64)
        h = np.zeros(len(F), dtype=np.uint64)
        for k in range(K):
            for c in range(4):
                v = (F[:, k][:, None, :, :] * R[k, c][None, None]).sum(axis=(1, 2, 3)) % P
                h = h * np.uint64(1048583) + v.astype(np.uint64)
            H[:, k] = h
        return H
    allH = [hashes(F)]
    offset, results = 0, {}
    for L in range(1, ell + 1):
        newF, newlast, newp = [], [], []
        for ch in range(4):
            mask = last != INV[ch]
            newF.append(right_mul(F[mask], g[ch], K))
            newlast.append(np.full(mask.sum(), ch))
            newp.append(np.nonzero(mask)[0] + offset)
        offset += len(F)
        F, last = np.concatenate(newF), np.concatenate(newlast)
        parents.append(np.concatenate(newp))
        letters.append(last)
        allH.append(hashes(F))
        H = np.concatenate(allH)
        P_all, L_all = np.concatenate(parents), np.concatenate(letters)
        def word(i):
            s = ""
            while i > 0:
                s = LETTERS[L_all[i]] + s
                i = P_all[i]
            return s
        best = 0
        for t in range(K - 1, 0, -1):
            order_idx = np.argsort(H[:, t], kind="stable")
            hs = H[order_idx, t]
            dup = np.nonzero(hs[1:] == hs[:-1])[0]
            found = None
            for j in dup[:200]:
                u, v = word(order_idx[j]), word(order_idx[j + 1])
                w = reduce(u + invert(v))
                if w and word_order(w, d, K, seed + 7) >= t + 1:
                    if found is None or len(w) < len(found):
                        found = w
            if found:
                best = t + 1
                results[2 * L] = (best, found)
                break
        print(f"d={d} length<={2 * L:3d} words={len(H):9d} max order={best} {results.get(2 * L, ('', ''))[1]}", flush=True)
    return results


def invert(w):
    return w[::-1].swapcase()


def reduce(w):
    out = []
    for ch in w:
        if out and out[-1] == ch.swapcase():
            out.pop()
        else:
            out.append(ch)
    return "".join(out)


if __name__ == "__main__":
    assert reduce("abBA") == "" and invert("aB") == "bA"
    assert word_order("abAB", 2, 8, 3) == 2  # the commutator has order 2
    assert word_order("abABaBAb", 3, 8, 3) >= 3  # [[a,b],... ] sanity: order above the commutator
    print("self-check ok")
    d, ell, K = (int(x) for x in sys.argv[1:4])
    search(d, ell, K)
