"""Find closed-form angles for a circuit found by search.py and check it exactly.
1. Gauge fixing: pin angles to multiples of pi/2 while the loss stays at zero (as gauge.py).
2. Identification: every angle is matched to s * arccos(sqrt(p/q)) + m pi/4 with q <= QMAX (tolerance 1e-7).
3. Exact check: cos and sin of every half angle are polynomials in generators (A_c, B_c for each c; cos, sin(pi/8);
   square roots of primes). Every amplitude minus its target value reduces to zero modulo relations that hold at the
   true values of the generators, by exact symbolic elimination.
usage: python certify.py n k 'skeleton' seed     (writes cert_<n>_<k>.txt with the angles)
       python certify.py --check cert_<n>_<k>.txt   (repeats the exact check from a certificate)"""
import ast, math, sys, itertools
import numpy as np
import sympy as sp
from scipy.optimize import minimize
from search import dicke, gates, loss_grad, solve

QMAX = int(__import__("os").environ.get("QMAX", "40"))

def gauge(n, k, skel, seed):
    rng = np.random.default_rng(seed); target = dicke(n, k); g = gates(n, skel)
    f, x = solve(n, k, skel, 60, rng); assert f < 1e-12, f
    fixed = {}
    def opt(x0, fixed):
        free = [i for i in range(len(x0)) if i not in fixed]
        def fun(y):
            z = x0.copy(); z[free] = y
            for i, v in fixed.items(): z[i] = v
            l, gr = loss_grad(z, n, g, target); return l, gr[free]
        best = (9, None)
        for t in range(8):
            y0 = x0[free] if t == 0 else rng.uniform(0, 2 * math.pi, len(free))
            r = minimize(fun, y0, jac=True, method="L-BFGS-B", options={"maxiter": 4000, "ftol": 1e-17, "gtol": 1e-14})
            if r.fun < best[0]: best = (r.fun, r.x)
            if best[0] < 1e-15: break
        z = x0.copy(); z[free] = best[1]
        for i, v in fixed.items(): z[i] = v
        return best[0], z
    for i in range(len(x)):
        for v in (0.0, math.pi, math.pi / 2, -math.pi / 2):
            trial = dict(fixed); trial[i] = v
            l, z = opt(x, trial)
            if l < 1e-14: fixed, x = trial, z; break
    return x

def identify(x):
    """angle = u * arccos(sqrt(p/q)) + m pi/4 with u in {-2..2}; bases already in use are tried first, so that
    related angles share one generator"""
    cands = {}
    for q in range(1, QMAX + 1):
        for p in range(1, q):
            if math.gcd(p, q) == 1: cands[(p, q)] = math.acos(math.sqrt(p / q))
    used, out = [], []
    def match(v, bases, us):
        best = None
        for pq in bases:
            base = cands[pq] if pq != (0, 1) else 0.0
            for u in us:
                for m in range(-8, 9):
                    d = abs((v - (u * base + m * math.pi / 4) + math.pi) % (2 * math.pi) - math.pi)
                    if best is None or d < best[0]: best = (d, u, pq, m)
        return best
    for v in x:
        best = match(v, [(0, 1)] + used, (-2, -1, 1, 2))
        if best[0] > 1e-7:
            best = match(v, list(cands), (-1, 1))
            if best[0] < 1e-7: used.append(best[2])
        out.append(best[1:] if best[0] < 1e-7 else None)
    return out

def rad(r, P):
    """sqrt of a positive rational r as coefficient times a product of prime-radical symbols"""
    r = sp.Rational(r); num = r.p * r.q; coef = sp.Rational(1, r.q)
    out = coef
    for p, e in sp.factorint(num).items():
        out *= sp.Integer(p) ** (e // 2)
        if e % 2:
            if p not in P: P[p] = sp.Symbol("r%d" % p)
            out *= P[p]
    return out

def exact(n, k, skel, ang):
    P = {}; gens = {}; rel = []
    Cp, Sp = sp.symbols("Cp Sp")                                      # cos, sin(pi/8)
    for (u, pq, m) in ang:
        if pq != (0, 1) and pq not in gens:
            c = rad(sp.Rational(pq[0], pq[1]), P); sn = rad(1 - sp.Rational(pq[0], pq[1]), P)
            if c.is_Rational:     # half-angle cosine and sine are square roots of rationals: no new generator
                gens[pq] = (rad((1 + c) / 2, P), rad((1 - c) / 2, P), None)
            else:
                A, B = sp.symbols("A%d_%d B%d_%d" % (pq + pq))
                gens[pq] = (A, B, math.acos(math.sqrt(pq[0] / pq[1])))
                rel += [A**2 + B**2 - 1, A**2 - B**2 - c, 2 * A * B - sn]
    r2 = rad(2, P) / 2 * 2                                            # sqrt(2) as a generator expression
    rel += [Cp**2 + Sp**2 - 1, Cp**2 - Sp**2 - r2 / 2, 2 * Cp * Sp - r2 / 2]
    rel += [sym**2 - p for p, sym in P.items()]
    allg = [g for (A, B, t) in gens.values() if t is not None for g in (A, B)] + [Cp, Sp] + list(P.values())
    G = sp.groebner(rel, *allg, order="grevlex", domain="QQ")
    val = {Cp: math.cos(math.pi / 8), Sp: math.sin(math.pi / 8)}
    for (A, B, t) in gens.values():
        if t is not None: val[A] = math.cos(t / 2); val[B] = math.sin(t / 2)
    for p, sym in P.items(): val[sym] = math.sqrt(p)
    for e in G.exprs: assert abs(float(e.subs(val))) < 1e-10, e
    def half(u, pq, m):
        cm, sm = sp.Integer(1), sp.Integer(0)
        for _ in range(abs(m)):
            sg = 1 if m > 0 else -1
            cm, sm = cm * Cp - sg * sm * Sp, sm * Cp + sg * cm * Sp
        if pq != (0, 1):
            A, B, _ = gens[pq]; B = (1 if u > 0 else -1) * B
            for _ in range(abs(u)):
                cm, sm = cm * A - sm * B, sm * A + cm * B
        return sp.expand(cm), sp.expand(sm)
    psi = [sp.Integer(0)] * 2 ** n; psi[0] = sp.Integer(1)
    bit = lambda i, q: (i >> (n - 1 - q)) & 1
    def ry(psi, q, cs):
        c, s = cs; out = list(psi)
        for i in range(2 ** n):
            if not bit(i, q):
                j = i | (1 << (n - 1 - q))
                out[i] = G.reduce(sp.expand(c * psi[i] - s * psi[j]))[1]; out[j] = G.reduce(sp.expand(s * psi[i] + c * psi[j]))[1]
        return out
    cx = lambda psi, a, b: [psi[i ^ (1 << (n - 1 - b))] if bit(i, a) else psi[i] for i in range(2 ** n)]
    j = 0
    for q in range(n): psi = ry(psi, q, half(*ang[j])); j += 1
    for (a, b) in skel:
        psi = cx(psi, a, b); psi = ry(psi, a, half(*ang[j])); j += 1; psi = ry(psi, b, half(*ang[j])); j += 1
    # Flipping the sign of one generator pair (A, B) multiplies every rotation that uses it, and hence the whole state,
    # by -1. The checks below are invariant under such flips: off-target amplitudes vanish, all target amplitudes are
    # equal, and the square of one of them is 1 / C(n, k). Together they say the state is +-D(n, k).
    sign = 1 if sum(float(psi[i].subs(val)) for i in range(2 ** n) if bin(i).count("1") == k) > 0 else -1
    tgt = [i for i in range(2 ** n) if bin(i).count("1") == k]; i0 = tgt[0]
    checks = [(i, psi[i]) for i in range(2 ** n) if i not in tgt] + [(i, psi[i] - psi[i0]) for i in tgt[1:]]
    checks.append((i0, psi[i0] ** 2 - sp.Rational(1, math.comb(n, k))))
    for i, e in checks:
        res = G.reduce(sp.expand(e))[1]
        assert res == 0, (i, float(res.subs(val)), str(res)[:300])
    return sign

def angle_value(u, pq, m):
    return (u * math.acos(math.sqrt(pq[0] / pq[1])) if pq != (0, 1) else 0) + m * math.pi / 4

def repair(n, k, skel, x, ang, rng):
    """pin every angle that has no closed form to a nearby closed form, if the loss stays at zero"""
    target = dicke(n, k); g = gates(n, skel)
    cands = [(0.0, (1, (0, 1), m)) for m in range(-8, 9)]
    for q in range(1, QMAX + 1):
        for p in range(1, q):
            if math.gcd(p, q) == 1:
                for u in (-1, 1):
                    for m in range(-8, 9): cands.append((0.0, (u, (p, q), m)))
    for i, a in enumerate(ang):
        if a is not None: continue
        fixed = {j: angle_value(*b) for j, b in enumerate(ang) if b is not None}
        order = sorted(cands, key=lambda c: abs((x[i] - angle_value(*c[1]) + math.pi) % (2 * math.pi) - math.pi))
        for _, c in order[:60]:
            fx = dict(fixed); fx[i] = angle_value(*c); free = [j for j in range(len(x)) if j not in fx]
            def fun(y):
                z = x.copy(); z[free] = y
                for j, v in fx.items(): z[j] = v
                l, gr = loss_grad(z, n, g, target); return l, gr[free]
            r = minimize(fun, x[free], jac=True, method="L-BFGS-B", options={"maxiter": 4000, "ftol": 1e-17, "gtol": 1e-14})
            if r.fun < 1e-14:
                x = x.copy(); x[free] = r.x
                for j, v in fx.items(): x[j] = v
                new = identify(x)
                ang = [b if b is not None else new[j] for j, b in enumerate(ang)]; ang[i] = c
                print("pinned angle", i, "to", c, flush=True); break
        else:
            raise SystemExit("no closed form for angle %d (%.12f)" % (i, x[i]))
    return x, ang

if __name__ == "__main__" and sys.argv[1] == "--check":     # python certify.py --check cert_6_3.txt
    lines = open(sys.argv[2]).read().splitlines()
    head = dict(kv.split("=", 1) for kv in lines[0].split(" ")[:3]); skel = ast.literal_eval(lines[0].split("skeleton=")[1])
    n, k, ang = int(head["n"]), int(head["k"]), ast.literal_eval(lines[2])
    assert int(head["cnots"]) == len(skel)
    xe = np.array([angle_value(*a) for a in ang])
    assert abs(loss_grad(xe, n, gates(n, skel), dicke(n, k))[0]) < 1e-12
    sign = exact(n, k, skel, ang)
    print("exact: the circuit prepares D(%d,%d) with %d CNOT gates, global sign %d" % (n, k, len(skel), sign))
elif __name__ == "__main__":
    n, k = int(sys.argv[1]), int(sys.argv[2]); skel = ast.literal_eval(sys.argv[3]); seed = int(sys.argv[4])
    cache = "gauge_cert_%d_%d.npy" % (n, k)
    try:
        x = np.load(cache)
    except OSError:
        x = gauge(n, k, skel, seed); np.save(cache, x)
    ang = identify(x)
    if any(a is None for a in ang): x, ang = repair(n, k, skel, x, ang, np.random.default_rng(seed))
    print("angles", ang, flush=True)
    xe = np.array([angle_value(*a) for a in ang])
    fl = loss_grad(xe, n, gates(n, skel), dicke(n, k))[0]; print("float loss of the closed form", fl); assert abs(fl) < 1e-12
    sign = exact(n, k, skel, ang)
    with open("cert_%d_%d.txt" % (n, k), "w") as f:
        f.write("n=%d k=%d cnots=%d skeleton=%s\nangles (u, (p,q), m): angle = u*arccos(sqrt(p/q)) + m*pi/4, (0,1) = 0\n%s\n"
                % (n, k, len(skel), skel, ang))
    print("exact: the circuit prepares D(%d,%d) with %d CNOT gates, global sign %d" % (n, k, len(skel), sign))
