"""High-precision certificate: refine a double-precision solution by least-squares steps with exact derivatives in mpmath (80 digits), with the
pinned angles exact, and write the angles to 40 digits. Then an independent check re-simulates the written angles at
100 digits and reports 1 - fidelity.
usage: python hp_cert.py n k 'skeleton' x.npy pins out.txt      (pins: i:expr,... with expr in mpmath syntax)
       python hp_cert.py --check out.txt"""
import ast, math, sys
import mpmath as mp

def simulate(n, skel, th, dps):
    mp.mp.dps = dps
    psi = [mp.mpf(0)] * 2 ** n; psi[0] = mp.mpf(1); j = 0
    def ry(psi, q, t):
        c, s = mp.cos(t / 2), mp.sin(t / 2); out = list(psi)
        for i in range(2 ** n):
            if not (i >> (n - 1 - q)) & 1:
                jj = i | (1 << (n - 1 - q)); out[i] = c * psi[i] - s * psi[jj]; out[jj] = s * psi[i] + c * psi[jj]
        return out
    def cx(psi, a, b):
        return [psi[i ^ (1 << (n - 1 - b))] if (i >> (n - 1 - a)) & 1 else psi[i] for i in range(2 ** n)]
    for q in range(n): psi = ry(psi, q, th[j]); j += 1
    for (a, b) in skel:
        psi = cx(psi, a, b); psi = ry(psi, a, th[j]); j += 1; psi = ry(psi, b, th[j]); j += 1
    return psi

def target(n, k):
    w = 1 / mp.sqrt(math.comb(n, k)); return [w if bin(i).count("1") == k else mp.mpf(0) for i in range(2 ** n)]

if sys.argv[1] == "--check":
    lines = open(sys.argv[2]).read().splitlines()
    n, k = int(lines[0].split()[0].split("=")[1]), int(lines[0].split()[1].split("=")[1])
    skel = ast.literal_eval(lines[0].split("skeleton=")[1])
    mp.mp.dps = 100; th = [mp.mpf(v) for v in lines[2:] if v.strip()]
    assert len(th) == n + 2 * len(skel)
    if "edges=" in lines[1]:                 # restricted connectivity: every CNOT acts on an allowed pair
        edges = ast.literal_eval(lines[1].split("edges=")[1])
        assert all((a, b) in edges or (b, a) in edges for a, b in skel)
        print("all CNOT gates act on the %d allowed pairs" % len(edges))
    psi = simulate(n, skel, th, 100); t = target(n, k)
    ov = mp.fsum(a * b for a, b in zip(psi, t))
    print("n=%d k=%d CNOT gates %d, 1 - fidelity = %s" % (n, k, len(skel), mp.nstr(1 - ov ** 2, 5)))
    assert 1 - ov ** 2 < mp.mpf("1e-70")
    sys.exit()

import numpy as np
n, k = int(sys.argv[1]), int(sys.argv[2]); skel = ast.literal_eval(sys.argv[3]); x0 = np.load(sys.argv[4])
pins = dict((int(a), b) for a, b in (p.split(":") for p in sys.argv[5].split(","))) if sys.argv[5] else {}
out = sys.argv[6]
mp.mp.dps = 80
th = [mp.mpf(float(v)) for v in x0]
for i, e in pins.items(): th[i] = mp.mpf(eval(e, {"mp": mp, "pi": mp.pi, "acos": mp.acos, "sqrt": mp.sqrt}))
free = [i for i in range(len(th)) if i not in pins]
t = target(n, k)
psi = simulate(n, skel, th, 80); sgn = 1 if mp.fsum(a * b for a, b in zip(psi, t)) > 0 else -1
for it in range(12):
    psi = simulate(n, skel, th, 80); r = [a - sgn * b for a, b in zip(psi, t)]
    nr = mp.sqrt(mp.fsum(v * v for v in r)); print("iteration", it, "residual", mp.nstr(nr, 3), flush=True)
    if nr < mp.mpf("1e-75"): break
    J = mp.matrix(len(r), len(free))
    for c, i in enumerate(free):             # derivative of R_y(t) is R_y(t + pi) / 2
        th2 = list(th); th2[i] = th[i] + mp.pi; col = simulate(n, skel, th2, 80)
        for rr in range(len(r)): J[rr, c] = col[rr] / 2
    JT = J.T; step = mp.lu_solve(JT * J, JT * mp.matrix(r))
    for c, i in enumerate(free): th[i] -= step[c]
with open(out, "w") as f:
    f.write("n=%d k=%d cnots=%d skeleton=%s\nangles in radians, gate order: R_y on qubits 0..n-1, then per CNOT R_y on control and target\n"
            % (n, k, len(skel), skel))
    for v in th: f.write(mp.nstr(v, 40) + "\n")
print("written", out)
