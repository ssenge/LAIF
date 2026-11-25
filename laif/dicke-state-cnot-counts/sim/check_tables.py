"""Parse the circuit text printed by tables.py back into angles and simulate it in floating point (independent of the
certificate data path). usage: python tables.py cert.txt | python check_tables.py n k"""
import math, re, sys
import numpy as np
from search import dicke

n, k = int(sys.argv[1]), int(sys.argv[2]); txt = sys.stdin.read()
base = {m.group(1): math.acos(math.sqrt(int(m.group(2)) / int(m.group(3))))
        for m in re.finditer(r"(\w) = arccos √\((\d+)/(\d+)\)", txt)}
def val(e):
    e = e.replace("−", "-").replace(" ", "")
    tot = 0.0
    for sgn, coef, sym in re.findall(r"([+-]?)(\d*(?:/\d+)?)(π/?\d*|[a-h])", e):
        pass
    tot, i = 0.0, 0
    for term in re.findall(r"[+-]?[^+-]+", e):
        s = -1 if term.startswith("-") else 1; t = term.lstrip("+-")
        if t == "0": continue
        if "π" in t:
            num, _, den = t.partition("π"); num = float(num) if num else 1.0; den = float(den[1:]) if den else 1.0
            tot += s * num * math.pi / den
        else:
            c = 2.0 if t[0] == "2" else 1.0; tot += s * c * base[t[-1]]
    return tot
psi = np.zeros(2 ** n); psi[0] = 1
def ry(psi, q, th):
    p = psi.reshape(2 ** q, 2, -1).copy(); a, b = p[:, 0, :].copy(), p[:, 1, :].copy(); c, s = math.cos(th / 2), math.sin(th / 2)
    p[:, 0, :] = c * a - s * b; p[:, 1, :] = s * a + c * b; return p.reshape(-1)
def cx(psi, a, b):
    out = psi.copy()
    for i in range(2 ** n):
        if (i >> (n - 1 - a)) & 1: out[i] = psi[i ^ (1 << (n - 1 - b))]
    return out
first = re.search(r"First apply (.*)\.\n", txt).group(1)
for m in re.finditer(r"R_y\(([^)]*)\) to qubit (\d)", first): psi = ry(psi, int(m.group(2)), val(m.group(1)))
rows = 0
for m in re.finditer(r"\| (\d) → (\d) \| R_y\(([^)]*)\) \| R_y\(([^)]*)\) \|", txt):
    a, b = int(m.group(1)), int(m.group(2)); psi = cx(psi, a, b); psi = ry(psi, a, val(m.group(3))); psi = ry(psi, b, val(m.group(4))); rows += 1
f = abs(psi @ dicke(n, k)); print("CNOTs", rows, "fidelity", f); assert abs(f - 1) < 1e-12
