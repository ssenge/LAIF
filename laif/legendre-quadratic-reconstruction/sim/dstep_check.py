"""Exact state-vector check of the hidden constant term step: f = h - D with h a known polynomial over F_p and
chi the quadratic character. The algorithm:
  1. prepares sum_x |x>, queries chi(f(x)), keeps the outcome "nonzero" and applies the phase chi(f(x));
  2. maps x -> (y, j) with y = h(x) and j the rank of x among the roots of h(X) = y (reversible given y), and
     measures j;
  3. on the y register applies the Fourier transform over F_p, multiplies by chi(k), applies the inverse
     transform and measures.
Claim: the outcome is D with probability exactly sum_j |H_j \\ {D}|^2 / p^2, where H_j is the set of values
y with more than j preimages, and this is at least (1 - d/p)^2 / d (at most d ranks occur, Cauchy-Schwarz)."""
import numpy as np

rng = np.random.default_rng(1)


def legendre_table(p):
    chi = np.full(p, -1, dtype=np.int64)
    chi[(np.arange(1, p) ** 2) % p] = 1
    chi[0] = 0
    return chi


def poly_eval(c, x, p):
    r = np.zeros_like(x)
    for a in c:                      # Horner, highest coefficient first
        r = (r * x + a) % p
    return r


def run(p, c, D):
    chi = legendre_table(p)
    x = np.arange(p)
    y = poly_eval(c, x, p)
    f = (y - D) % p
    # rank of x among the preimages of y = h(x), in increasing order of x
    order = np.lexsort((x, y))
    j = np.empty(p, dtype=np.int64)
    ys = y[order]
    start = np.r_[0, np.flatnonzero(np.diff(ys)) + 1]
    run_id = np.repeat(np.arange(len(start)), np.diff(np.r_[start, p]))
    j[order] = np.arange(p) - start[run_id]
    amp = chi[f] / np.sqrt(p)                         # after the query; zero where f(x) = 0
    total = 0.0
    for jj in range(j.max() + 1):
        sel = j == jj
        phi = np.zeros(p, complex)
        phi[y[sel]] = amp[sel]                        # sub-state on y for measured rank jj (unnormalized)
        a = np.fft.ifft(phi) * np.sqrt(p) * chi       # Fourier transform, then multiply by chi(k)
        b = np.fft.fft(a) / np.sqrt(p)                # inverse transform
        total += np.abs(b[D]) ** 2                    # P(rank jj and outcome D)
    counts = np.bincount(y, minlength=p)
    claim = sum(np.sum((counts > jj) & (np.arange(p) != D)) ** 2 for jj in range(counts.max())) / p ** 2
    lower = (1 - (len(c) - 1) / p) ** 2 / (len(c) - 1)
    return total, claim, lower, len(c) - 1


if __name__ == "__main__":
    worst = 0.0
    for p in [1009, 7919, 20011]:
        cases = [[1, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0]]          # x^2, x^3, x^6
        cases += [[1] + list(rng.integers(0, p, size=d)) for d in [2, 3, 4, 5]]   # random monic, degree 2..5
        for c in cases:
            D = int(rng.integers(0, p))
            pr, claim, lower, d = run(p, [int(v) for v in c], D)
            worst = max(worst, abs(pr - claim))
            assert pr >= lower - 1e-12
            print(f"p={p:6d} deg {d} h={'x^%d' % d if all(v == 0 for v in c[1:]) else 'random':7s}: "
                  f"P(D) = {pr:.6f}, claim {claim:.6f}, lower bound (1 - d/p)^2/d = {lower:.6f}")
    assert worst < 1e-9
    print(f"largest deviation from the exact formula: {worst:.1e}")
