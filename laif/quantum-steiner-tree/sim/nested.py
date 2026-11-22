"""Cost of nested quantum minimum finding over the balanced split recursion of Minimum Steiner Tree, polynomial space.

Recursion (split theorem, restated as Lemma 3 and Theorem 4 of arXiv:1904.03581): for eta > 0,
  W_G(K) = min over K1 with |K1| = (1/2 +- eta)|K| and A subset of V with |A| <= s = ceil(log2(1/eta)) of
           W_G(K1 + A) + W_{G/A}(K2 + v_A),     K2 = K - (K1 + A).
A node with m terminals searches its at most 2^m (n+1)^s choices by quantum minimum finding; each choice evaluates the
two children one after the other. Children have at most r(m) = floor((1/2 + eta) m) + s + 1 terminals. At m <= m0 =
max(ceil(log2 n), M), with M = max(ceil(2 (s + 2) / (1 - 2 eta)), ceil(1 / eta)) a constant above which r(m) < m and
the balanced range (1/2 +- eta) m holds an integer, the value is computed classically by the subset dynamic program in 3^m poly(n) time and 2^m n space.

Upper bound on log2 of the cost, with a factor L(m) = C (m + s log2(n+1) + 2 log2 k + 10) per level for minimum finding
with error reduction (C a constant):
  log2 Q(m) = m/2 + (s/2) log2(n+1) + log2(2 L(m)) + log2 Q(r(m)),   log2 Q(m) = m log2 3 + c0 log2 n for m <= m0.
Checked here: for each delta in the table and the stated eta, log2 Q(k) <= (1 + delta) k + f log2 n on a grid of k up to
10^7 and n up to 2^40, with the excess decreasing in k at the top of the grid; the k-exponent tends to 1/(1 - 2 eta). """
from math import ceil, floor, log2

C, c0 = 64, 3

def logQ(k, n, eta):
    s = ceil(log2(1 / eta)); m0 = max(ceil(log2(n)), ceil(2 * (s + 2) / (1 - 2 * eta)), ceil(1 / eta)); tot = 0.0; m = k; depth = 0
    while m > m0:
        r = int((0.5 + eta) * m) + s + 1
        assert r < m, (m, r)                       # the recursion shrinks once m exceeds the cutoff (checked below)
        L = C * (m + s * log2(n + 1) + 2 * log2(max(k, 2)) + 10)
        tot += m / 2 + (s / 2) * log2(n + 1) + log2(2 * L); m = r; depth += 1
    return tot + m * log2(3) + c0 * log2(n), depth

def worst_f(delta, eta, ks, ns):
    """Smallest f with logQ <= (1 + delta) k + f log2 n on the grid."""
    return max((logQ(k, n, eta)[0] - (1 + delta) * k) / log2(n) for k in ks for n in ns)

ns = [2 ** e for e in range(4, 41, 2)]             # n from 16 to 2^40
ks = list(range(1, 200)) + list(range(200, 20001, 50)) + [10 ** e for e in range(5, 8)] + [3 * 10 ** e for e in range(5, 7)]
STATED = {0.5: 34, 0.25: 26, 0.1: 36, 0.05: 76}
for delta, eta in ((0.5, 0.05), (0.25, 0.02), (0.1, 0.005), (0.05, 0.002)):
    s = ceil(log2(1 / eta))
    M = max(ceil(2 * (s + 2) / (1 - 2 * eta)), ceil(1 / eta))  # above M splits shrink and the range holds an integer
    assert all(floor((0.5 + eta) * m) >= ceil((0.5 - eta) * m) for m in range(M, M + 10 ** 4))
    assert all(int((0.5 + eta) * m) + s + 1 < m for m in range(M + 1, M + 10 ** 4))
    assert 1 / (1 - 2 * eta) < 1 + delta           # the limit exponent lies below 1 + delta
    f = worst_f(delta, eta, ks, ns)
    # beyond the grid the excess (log2 Q - (1 + delta) k) / log2 n only falls: check it is decreasing in k at the top end
    for n in ns:
        e = [(logQ(k, n, eta)[0] - (1 + delta) * k) / log2(n) for k in (10 ** 6, 3 * 10 ** 6, 10 ** 7)]
        assert e[0] > e[1] > e[2], (n, e)
    lim = [logQ(10 ** 7, n, eta)[0] / 10 ** 7 for n in (2 ** 10, 2 ** 20)]
    print(f"delta={delta:5.3f}  eta={eta:6.4f}  s={s:2d}  M={M:3d}  f(delta) <= {f:7.2f}   log2 Q / k at k=10^7: "
          f"{lim[0]:.4f} (n=2^10), {lim[1]:.4f} (n=2^20); limit 1/(1-2 eta) = {1 / (1 - 2 * eta):.4f}")
    assert ceil(f) == STATED[delta], (delta, f)    # the README states the ceiling
    assert all(l < 1 + delta for l in lim)
print("all checks passed")
