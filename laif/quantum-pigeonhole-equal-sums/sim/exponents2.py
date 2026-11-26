"""Exponents (units of n, log2) per F-scale k: 2^k <= F < 2^{k+1}; reduced instance N0 = 2^k, Delta = 2^{2k-n}.
L5: classical small-F branch 2^{k/2}.
QA (QRACM): one random bin (P <= Delta), bin size T = N0/P, kappa = Delta/P frequent sums in it; classical table of R bin
    elements, Grover over the bin. Valid only if the table catches a frequent sum in expectation: R + kappa - T >= 0.
    Cost max(P, R, T - (kappa + R)/2).
PF (QRAQM, implied by [ESA25 + 2111.07059]): one random bin, pair finding (T^2/kappa)^{1/3}: max(P, (2T - kappa)/3).
QB (QRAQM): P >= Delta, VTAA over bins, element distinctness in a bin: max(P, (P - Delta)/2 + 2(k - P)/3)."""
G = 400

def grid(a, b):
    return [a + (b - a) * i / G for i in range(G + 1)] if b >= a else []

def qa(k):
    D = 2 * k - 1
    best = None
    for P in grid(0, D):
        T, ka = k - P, D - P
        for R in grid(max(0, T - ka), k):
            c = max(P, R, T - (ka + R) / 2)
            best = c if best is None or c < best else best
    return best

def pf(k):
    D = 2 * k - 1
    return min((max(P, (2 * (k - P) - (D - P)) / 3) for P in grid(0, D)), default=None)

def qb(k):
    D = 2 * k - 1
    return min((max(P, (P - D) / 2 + 2 * (k - P) / 3) for P in grid(max(D, 0), k)), default=None)

def worst(branches):
    w, arg = 0, None
    for j in range(0, 1001):
        k = j / 1000
        v = min(x for x in [k / 2] + [b(k) for b in branches] if x is not None)
        if v > w: w, arg = v, k
    return w, arg

for name, br in [("classical L5 only", []), ("QRACM: L5+QA", [qa]), ("QRAQM implied: L5+PF", [pf]),
                 ("QRAQM: L5+PF+QB", [pf, qb]), ("all", [qa, pf, qb])]:
    w, a = worst(br)
    print(f"{name:24s} worst exponent {w:.4f} at k = {a:.3f} n")

assert abs(worst([])[0] - 0.5) < 1e-3
assert abs(worst([qa])[0] - 1 / 3) < 2e-3            # QRACM table + Grover: no gain over 2^{n/3}
assert abs(worst([pf])[0] - 2 / 7) < 2e-3            # implied by [ESA 2025] + [2111.07059]
assert abs(worst([pf, qb])[0] - 3 / 11) < 2e-3       # Theorem 1
w, a = worst([pf, qb]); assert abs(a - 6 / 11) < 5e-3
