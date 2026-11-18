"""Parallel tempering (single-spin Metropolis sweeps, 14 replicas on a geometric ladder, neighbour swaps after every sweep)
on the 156-qubit heavy-hex HUBO, with the metric of arXiv:2510.26735: ln Z~ over the distinct states produced by all replicas,
counting one state per replica per sweep. Compared with N = 50 000 exact Boltzmann samples (hubo.Eliminator).
Usage: python -I pt156.py <seed> [max multiple of 50 000]"""
import os, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from numba import njit
from hubo import heron156, instance, energy, Eliminator

@njit(cache=True)
def sweeps(Z, Tl, nsw, ptr, tix, tv, tc, E, thr, buf, bufE, nbuf):
    R, n = Z.shape; cnt = nbuf
    for s in range(nsw):
        for r in range(R):
            b = 1.0 / Tl[r]
            for i in range(n):
                d = 0.0
                for q in range(ptr[i], ptr[i + 1]):
                    k = tix[q]; p = tc[k]
                    for a in range(3):
                        v = tv[k, a]
                        if v >= 0: p *= Z[r, v]
                    d -= 2.0 * p
                if d <= 0 or np.random.random() < np.exp(-b * d):
                    Z[r, i] = -Z[r, i]; E[r] += d
            if E[r] <= thr and cnt < buf.shape[0]:
                for i in range(n): buf[cnt, i] = Z[r, i]
                bufE[cnt] = E[r]; cnt += 1
        for r in range(R - 1):                                            # swaps between neighbouring temperatures
            x = (1.0 / Tl[r] - 1.0 / Tl[r + 1]) * (E[r] - E[r + 1])
            if x >= 0 or np.random.random() < np.exp(x):
                for i in range(n): t = Z[r, i]; Z[r, i] = Z[r + 1, i]; Z[r + 1, i] = t
                t2 = E[r]; E[r] = E[r + 1]; E[r + 1] = t2
    return cnt

def main(seed, kmax=1000, R=14, Tmin=0.02, Tmax=1.5, Ts=(0.25, 0.125, 0.1, 0.05, 0.02), N0=50_000):
    G = heron156(); n, terms = instance(seed, G); El = Eliminator(n, terms); e0, _ = El.ground()
    tv = -np.ones((len(terms), 3), np.int64); tc = np.array([c for _, c in terms])
    for k, (idx, _) in enumerate(terms): tv[k, :len(idx)] = idx
    inc = [[] for _ in range(n)]
    for k, (idx, _) in enumerate(terms):
        for i in idx: inc[i].append(k)
    ptr = np.cumsum([0] + [len(a) for a in inc]).astype(np.int64); tix = np.array([k for a in inc for k in a], np.int64)
    Tl = Tmin * (Tmax / Tmin) ** (np.arange(R) / (R - 1)); rng = np.random.default_rng(100 + seed); np.random.seed(seed)
    Z = rng.choice(np.array([-1, 1], np.int8), (R, n)).astype(np.int64); E = energy(terms, Z)
    thr = e0 + 20 * max(Ts)                                               # states above it weigh below exp(-20) at every T in Ts
    seen = {}; exact = {}
    for T in Ts:
        S = El.sample(1 / T, N0, np.random.default_rng(seed)); U = np.unique(S, axis=0)
        exact[T] = (El.log_z(1 / T), np.logaddexp.reduce(-energy(terms, U) / T))
    print(f"seed {seed}: E0 {e0:.4f}, ladder {np.round(Tl, 3).tolist()}", flush=True)
    for T in Ts: print(f"  T={T}: lnZ - lnZ~(exact sampler, 50000) = {exact[T][0] - exact[T][1]:.4f}", flush=True)
    done = 0; t0 = time.perf_counter(); marks = [m for m in (1, 3, 10, 30, 100, 300, 1000) if m <= kmax]
    buf = np.zeros((400_000, n), np.int64); bufE = np.zeros(400_000)
    for m in marks:
        target = m * N0 // R                                               # sweeps so that R * sweeps = m * 50 000 states
        while done < target:
            step = min(20_000, target - done)
            c = sweeps(Z, Tl, step, ptr, tix, tv, tc, E, thr, buf, bufE, 0); done += step
            assert c < buf.shape[0]
            for z, e in zip(buf[:c], bufE[:c]): seen.setdefault(z.tobytes(), e)
        el = time.perf_counter() - t0; Ev = np.fromiter(seen.values(), float)
        row = "; ".join(f"T={T}: lnZ - lnZ~ {exact[T][0] - np.logaddexp.reduce(-Ev / T):.4f}" for T in Ts)
        print(f"  PT {m}x50000 states ({el:.0f} s, {1e6 * el / (done * R):.2f} us per state, min E {Ev.min():.4f}): {row}", flush=True)
    assert abs(energy(terms, np.frombuffer(min(seen, key=seen.get), np.int64)[None])[0] - min(seen.values())) < 1e-6

if __name__ == "__main__":
    main(int(sys.argv[1]), int(sys.argv[2]) if len(sys.argv) > 2 else 1000)
