"""Print the README circuit description of a certificate file cert_<n>_<k>.txt written by certify.py."""
import ast, sys
from fractions import Fraction

def fmt(u, pq, m, names):
    parts = []
    if pq != (0, 1):
        t = names[pq]; parts.append(("−" if u < 0 else "") + ("2" if abs(u) == 2 else "") + t)
    if m:
        fr = Fraction(m, 4); num, den = abs(fr.numerator), fr.denominator
        t = ("" if num == 1 else str(num)) + "π" + ("" if den == 1 else "/%d" % den)
        if parts: parts.append(("− " if fr < 0 else "+ ") + t)
        else: parts.append(("−" if fr < 0 else "") + t)
    return "R_y(%s)" % (" ".join(parts) if parts else "0")

lines = open(sys.argv[1]).read().splitlines()
head = dict(kv.split("=", 1) for kv in lines[0].split(" ", 3)[:3]); skel = ast.literal_eval(lines[0].split("skeleton=")[1])
ang = ast.literal_eval(lines[2]); n = int(head["n"])
bases = sorted({a[1] for a in ang if a[1] != (0, 1)}, key=lambda pq: pq[0] / pq[1])
letters = "abcdefgh"; names = {pq: letters[i] for i, pq in enumerate(bases)}
def root(pq):
    p, q = pq
    return "√(%d/%d)" % (p, q) if q != 1 else "1"
print("Let " + ", ".join("%s = arccos %s" % (names[pq], root(pq)) for pq in bases) + ".")
print("First apply " + ", ".join("%s to qubit %d" % (fmt(*ang[q], names), q) for q in range(n)) + ".\n")
print("| CNOT | Rotation on the control | Rotation on the target |\n|---|---|---|")
j = n
for (a, b) in skel:
    print("| %d → %d | %s | %s |" % (a, b, fmt(*ang[j], names), fmt(*ang[j + 1], names))); j += 2
