"""Compare curve.csv with the lower envelope of known quantum sieving points (memory, time), extended to larger
memory (an algorithm with memory M also runs with more). Known points:
  [2] Table 2, quantum BLS16 (Alg. 4.1), k = 2..6, 28..30, hybrid (Alg. 4.2), and the low-memory hybrid row;
  [2] Table 3, k-List with LSF, k = 2..5, both regimes; [2] Fig. 1 curves (3-sieve with LSF from (0.1887, 0.3266)
  down to (0.2908, 0.2908); k-sieves k >= 10 not below their time optimum 0.29893);
  [1] 3-tuple 0.284551 at 0.188722; quantum 2-sieve 0.2563 (QQRAM) and 0.2571 (QCRAM) at 0.2075;
  [3] Tables 4 and 5, quantum 3- and 4-sieves with tailored filtering; [4] Table 2, their re-optimization.
The k = 3 rows of curve.csv are [1] with other angles and count as known.
Run: python envelope.py"""
import csv

KNOWN = [
    (0.2075, 0.3112), (0.1907, 0.3306), (0.1796, 0.3289), (0.1685, 0.3219), (0.1596, 0.3147), (0.1395, 0.29893),
    (0.1731, 0.3197), (0.1638, 0.3088), (0.1595, 0.3059),
    (0.1887, 0.3349), (0.1724, 0.3215), (0.1587, 0.3305), (0.1473, 0.3655),
    (0.2653, 0.2653), (0.2908, 0.2908), (0.3013, 0.3013), (0.3048, 0.3048),
    (0.2075, 0.2925), (0.1887, 0.3266), (0.1724, 0.3178), (0.1587, 0.3281),
    (0.188722, 0.284551), (0.2075, 0.2563), (0.2075, 0.2571),
    (0.1887, 0.3098), (0.189, 0.3073), (0.190, 0.3056), (0.1907, 0.3053),     # [3] Table 4, quantum 3-sieve
    (0.1724, 0.3276), (0.175, 0.3153), (0.180, 0.3127), (0.1813, 0.3120),     # [3] Table 5, quantum 4-sieve
    (0.1887, 0.3097), (0.190, 0.3060), (0.1724, 0.3260), (0.175, 0.3159), (0.180, 0.3129),   # [4] Table 2, re-optimized [3]
]

def envelope(M):
    return min(t for m, t in KNOWN if m <= M + 1e-9)

rows = list(csv.DictReader(open("curve.csv")))
# k = 3 is the algorithm of [1] with other angles ([1, Lemma 3.16] holds for general angles): count it as known
KNOWN += [(float(r["memory"]), float(r["time"])) for r in rows if r["k"] == "3"]
best = {}
for r in rows:
    M, t, mem, k = float(r["M"]), float(r["time"]), float(r["memory"]), int(r["k"])
    assert mem <= M + 1e-6
    if k >= 4 and (M not in best or t < best[M][0]):
        best[M] = (t, k, mem)
below = []
for M in sorted(best):
    t, k, mem = best[M]
    e = envelope(M)                      # anything known with memory at most M
    print(f"memory {mem:.4f} (bound {M:.4f}): k={k} time {t:.6f}, known envelope {e:.6f}, gain {e - t:+.6f}")
    if t < e:
        below.append(M)
assert min(below) <= 0.1625 and max(below) >= 0.1875 and all(M < 0.1887 for M in below)
print(f"k >= 4 below the known envelope for memory bounds {min(below):.4f} to {max(below):.4f}")
