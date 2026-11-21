"""Symbolic proof that E X^2 <= 2 (E X)^2 for all d >= 2 (so the second-moment constant (E X)^2/(4 E X^2) is >= 1/8):
the numerator of 2 (E X)^2 - E X^2 in t = d - 2 has nonnegative coefficients and the denominator is positive."""
import sympy as sp
d, t = sp.symbols("d t", positive=True)
ES = 2 / (d + 1); ES2 = 4 * (d + 5) / ((d + 1) * (d + 2) * (d + 3))
EX = sp.simplify(ES - 1 / d); EX2 = sp.simplify(ES2 - 2 * ES / d + 1 / d ** 2)
num, den = sp.fraction(sp.together(2 * EX ** 2 - EX2))
pn, pd_ = sp.Poly(sp.expand(num.subs(d, t + 2)), t), sp.Poly(sp.expand(den.subs(d, t + 2)), t)
print("EX =", sp.factor(EX), " EX2 =", sp.factor(EX2))
print("numerator coeffs in t:", pn.all_coeffs(), "\ndenominator coeffs in t:", pd_.all_coeffs())
assert all(c >= 0 for c in pn.all_coeffs()) and all(c >= 0 for c in pd_.all_coeffs()) and pd_.all_coeffs()[-1] > 0
print("E X^2 <= 2 (E X)^2 for all d >= 2")
