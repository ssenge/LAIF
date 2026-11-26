# Interval check (outward rounding, mpmath.iv) of the final constants of Theorems 1-3 in the README.
from mpmath import iv
iv.dps = 40
d = iv.mpf(10) ** 4; delta = iv.mpf(1) / 10 ** 5
eta = 6 * iv.exp(-iv.mpf('0.56') * d + iv.mpf('8.1') * iv.sqrt(d))      # Lemma 3; decreasing in d for d >= 53
s = iv.mpf('0.0724')                                                      # any s > 0 is allowed; close to (38 delta)^(1/3)
tv2 = s + eta + 16 * delta + (iv.exp(18 * delta) - 1) / s ** 2            # Theorem 2
assert (iv.exp(18 * delta) - 1).b <= (19 * delta).a and tv2.b <= iv.mpf('0.109').a
c1 = iv.mpf('0.05'); t1 = 2 * tv2 + 2 * c1                                 # Theorem 1: n = 0.05 m^2 B
assert t1.b < (iv.mpf(1) / 3).a
c3 = iv.mpf('0.015'); k = iv.mpf('5.5') + iv.mpf('6.5') / iv.log(d)       # Theorem 3: n = 0.015 m^2 B / ln d
assert k.b <= iv.mpf('6.21').a; t3 = 2 * tv2 + c3 * k
assert t3.b < (iv.mpf(1) / 3).a
assert (c1 * delta / 100).a >= 5e-9 * (1 - 1e-12) and (c3 * delta / 100).a >= 1.5e-9 * (1 - 1e-12)
print(f"TV Thm 2 <= {float(tv2.b):.6f}; Thm 1 total <= {float(t1.b):.6f} (margin {float((iv.mpf(1)/3 - t1).a):.4f}); "
      f"Thm 3 total <= {float(t3.b):.6f} (margin {float((iv.mpf(1)/3 - t3).a):.4f}); constants 5e-9, 1.5e-9 ok")
