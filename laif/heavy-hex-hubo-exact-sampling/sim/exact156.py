"""Exact ln Z, ground energy and the metric ln Z~(N) = ln sum over distinct sampled states of exp(-E/T) of arXiv:2510.26735
for N exact Boltzmann samples, on fresh Sidon-set instances of the 156-qubit heavy-hex HUBO. Usage: python -I exact156.py [seeds]"""
import os, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from hubo import heron156, instance, energy, Eliminator

def lnz_tilde(S, terms, T):
    U = np.unique(S, axis=0); return np.logaddexp.reduce(-energy(terms, U) / T), len(U)

if __name__ == "__main__":
    seeds = [int(s) for s in sys.argv[1:]] or [0, 1, 2, 3, 4]
    G = heron156(); NS = (1000, 10_000, 50_000)
    for seed in seeds:
        n, terms = instance(seed, G); El = Eliminator(n, terms)
        t0 = time.perf_counter(); e0, z0 = El.ground(); tg = time.perf_counter() - t0
        assert abs(energy(terms, z0)[0] - e0) < 1e-9
        print(f"seed {seed}: ground energy {e0:.4f} ({1e3 * tg:.0f} ms), elimination width {El.width}", flush=True)
        for T in (0.5, 0.25, 0.125, 0.1, 0.05, 0.02):
            t0 = time.perf_counter(); lz = El.log_z(1 / T); tz = time.perf_counter() - t0
            t0 = time.perf_counter(); S = El.sample(1 / T, NS[-1], np.random.default_rng(seed)); ts = time.perf_counter() - t0
            row = []
            for N in NS:
                lt, d = lnz_tilde(S[:N], terms, T); row.append(f"N={N}: lnZ-lnZ~ {lz - lt:.3f} ({d} distinct)")
            print(f"  T={T}: lnZ {lz:.3f} (+E0/T {lz + e0 / T:.3f}; {1e3 * tz:.0f} ms), sampling {1e6 * (ts - tz) / NS[-1]:.1f} us per sample; "
                  + "; ".join(row), flush=True)
