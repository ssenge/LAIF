"""Exact certificate that (log f)''' < 0 on (n/2, n) for the density f of U_1 + ... + U_n, U_i uniform on [0, 1].
On the piece s = j + t (0 <= t <= 1), f is proportional to F_j(t) = sum_{k <= j} (-1)^k C(n, k) (t + j - k)^(n-1), an
integer polynomial, and (log f)''' has the sign of N = F''' F^2 - 3 F F' F'' + 2 F'^3. Negativity of an integer
polynomial on [0, 1] is certified by its coefficients in the basis C(D, i) t^i (1 - t)^(D - i) (all negative), bisecting exactly where needed.
On the last piece [n-1, n], f is proportional to (n - s)^(n-1) and (log f)''' = -2(n-1)/(n-s)^3 < 0.
At the centre s = n/2, N vanishes; there the factor (s - n/2) is divided out exactly."""
import sys
from math import comb, gcd
from multiprocessing import Pool

def mul(p, q):
    r = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        if a:
            for j, b in enumerate(q): r[i + j] += a * b
    return r
def add(*ps):
    r = [0] * max(len(p) for p in ps)
    for p in ps:
        for i, a in enumerate(p): r[i] += a
    return r
def scal(c, p): return [c * a for a in p]
def der(p): return [i * p[i] for i in range(1, len(p))] or [0]
def shift_pow(c, m):                                   # (t + c)^m
    return [comb(m, i) * c ** (m - i) for i in range(m + 1)]

def piece(n, j):
    F = [0] * n
    for k in range(j + 1):
        F = add(F, scal((-1) ** k * comb(n, k), shift_pow(j - k, n - 1)))
    return F

def Nof(F):
    F1 = der(F); F2 = der(F1); F3 = der(F2)
    return add(mul(F3, mul(F, F)), scal(-3, mul(F, mul(F1, F2))), scal(2, mul(F1, mul(F1, F1))))

def compose_affine(p, a, b, den):                       # den^deg * p((a + b u)/den) as a polynomial in u
    D = len(p) - 1; r = [0] * (D + 1); base = [1]       # base = (a + b u)^k den^(D-k)
    lin = [a, b]
    for k in range(D + 1):
        term = scal(p[k] * den ** (D - k), base)
        r = add(r, term); base = mul(base, lin)
    return r

def bern_negative(p):
    """True if the integer polynomial p (power basis in u) is < 0 on [0, 1]."""
    D = len(p) - 1
    B = [sum(comb(D - k, i - k) * p[k] for k in range(i + 1)) for i in range(D + 1)]   # C(D, i) * coefficient in that basis
    L = 1
    for i in range(D + 1): L = L * comb(D, i) // gcd(L, comb(D, i))
    return bern_rec([B[i] * (L // comb(D, i)) for i in range(D + 1)], 0)

def bern_rec(b, depth):                                 # b = positive multiple of the coefficients in that basis
    if all(c < 0 for c in b): return True
    if b[0] >= 0 or b[-1] >= 0 or depth > 40: return False
    D = len(b) - 1; left = [b[0] << D]; right = [b[-1] << D]; cur = b
    for r in range(1, D + 1):                           # exact halving by the corner-cutting recursion, scaled by 2^D
        cur = [cur[i] + cur[i + 1] for i in range(len(cur) - 1)]
        left.append(cur[0] << (D - r)); right.append(cur[-1] << (D - r))
    return bern_rec(left, depth + 1) and bern_rec(right[::-1], depth + 1)

def selfcheck(n):
    from fractions import Fraction
    P = [piece(n, j) for j in range(n)]
    ev = lambda p, t: sum(c * t ** i for i, c in enumerate(p))
    for j in range(n - 1):                                                     # f is C^(n-2) across the integers
        p, q = P[j], P[j + 1]
        for _ in range(n - 1):
            assert ev(p, 1) == ev(q, 0); p, q = der(p), der(q)
    assert sum(sum(Fraction(c, i + 1) for i, c in enumerate(p)) for p in P) == comb(n - 1, 0) * __import__("math").factorial(n - 1)   # total mass 1
    assert P[-1] == [comb(n - 1, i) * (-1) ** i for i in range(n)]               # last piece (1 - t)^(n-1)

def check_n(n):
    selfcheck(n)
    ok = True; worst = None
    for j in range(n // 2, n - 1):                      # pieces [j, j+1] meeting (n/2, n-1]
        N = Nof(piece(n, j))
        while len(N) > 1 and N[-1] == 0: N.pop()
        if n % 2 == 0 and j == n // 2:                  # centre at t = 0
            assert N[0] == 0 or n < 5; Q = N[1:] if N[0] == 0 else N   # n = 4 (control only): f''' jumps at the centre
        elif n % 2 == 1 and j == n // 2:                # centre at t = 1/2: t = (1 + u)/2, divide by u
            Q = compose_affine(N, 1, 1, 2); assert Q[0] == 0; Q = Q[1:]
        else:
            Q = N
        good = bern_negative(Q)
        ok = ok and good
        if not good: worst = j
    return n, ok, worst

if __name__ == "__main__":
    lo, hi = int(sys.argv[1]), int(sys.argv[2])
    with Pool(int(sys.argv[3]) if len(sys.argv) > 3 else 8) as pool:
        for n, ok, worst in pool.imap(check_n, range(lo, hi + 1)):
            print(f"n = {n}: (log f)''' < 0 on (n/2, n) {'certified' if ok else 'NOT certified, piece ' + str(worst)}", flush=True)
