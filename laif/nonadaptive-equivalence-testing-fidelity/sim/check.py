# Numerical checks for Theorem 1 of the README (Lemmas 1 to 5). Asserts throughout.
import numpy as np, math
from scipy import stats
rng = np.random.default_rng(1)
def haar(n):
    q, r = np.linalg.qr(rng.normal(size=(n, n)) + 1j * rng.normal(size=(n, n)))
    return q * (np.diag(r) / abs(np.diag(r)))
def gue0(D):  # traceless, E|H_ab|^2 = 1/D
    a = rng.normal(size=(D, D)) + 1j * rng.normal(size=(D, D)); H = (a + a.conj().T) / 2 / math.sqrt(D)
    return H - np.trace(H).real / D * np.eye(D)
def psd_sqrt(a):
    w, v = np.linalg.eigh(a); return (v * np.sqrt(np.clip(w, 0, None))) @ v.conj().T
def rootfid(a, b):
    s = psd_sqrt(a); return np.sqrt(np.clip(np.linalg.eigvalsh(s @ b @ s), 0, None)).sum()
phi = lambda t, e: t / ((1 - e) * (1 - t) + e * t)
c0 = 3 / 20

# 1. instance: states, fidelity, trace distance (Lemma 1)
for D in (8, 16, 32):
    for e in (0.3, 1e-2, 1e-4):
        for _ in range(20):
            G = gue0(D)
            if np.linalg.norm(G, 2) > 5 or np.linalg.norm(G) ** 2 < D / 2: continue
            W = haar(2 * D)
            r0 = np.diag([(1 - e) / D] * D + [e / D] * D).astype(complex); s0 = r0.copy(); s0[D:, D:] += e * c0 / D * G
            rho, sig = W @ r0 @ W.conj().T, W @ s0 @ W.conj().T
            assert abs(np.trace(sig) - 1) < 1e-12 and np.linalg.eigvalsh(sig).min() >= e / (4 * D) - 1e-15
            f = rootfid(rho, sig); g = np.linalg.eigvalsh(G)
            assert abs(f - ((1 - e) + e / D * np.sqrt(1 + c0 * g).sum())) < 1e-9
            assert 1 - f >= e * c0 ** 2 * (g ** 2).sum() / (8 * 1.75 ** 1.5 * D) * (1 - 1e-9) >= e / 1700 * (1 - 1e-9)
            assert abs(0.5 * abs(np.linalg.eigvalsh(rho - sig)).sum() - e * c0 / (2 * D) * abs(g).sum()) < 1e-12
print("1 ok: instance valid, 1 - F >= eps/1700 on E")

# 2. Beta tail and dimension condition (Lemma 2)
for D in range(2, 400):
    assert stats.beta.sf(0.75, D, D) <= D / 2 * 0.75 ** (D - 1)
for L in np.linspace(0.7, 200, 400):          # L = ln(1/eps)
    D = math.ceil(60 + 4 * L); assert D * D * 0.75 ** (D - 1) <= math.exp(-L) / 20
print("2 ok: P(Beta(D,D) > 3/4) <= (D/2)(3/4)^(D-1); D >= 60 + 4 ln(1/eps) suffices")

# 3. Gaussian facts on E (Lemma 2): ||G||_op <= 5, ||G||_F^2 >= D/2 (net bound: 1.25 * 3.8 = 4.75, plus 1/4)
assert 1.25 * 3.8 + 0.25 <= 5 and 3.8 ** 2 / 2 - 2 * math.log(21) > 1.13 and c0 * 5 <= 0.75
assert c0 ** 2 / (16 * 1.75 ** 1.5) >= 1 / 1700
for D in (4, 8, 16, 32, 64):
    ops, fr = zip(*[(np.linalg.norm(G, 2), np.linalg.norm(G) ** 2) for G in (gue0(D) for _ in range(300))])
    assert np.mean(ops) <= 2 and (D < 16 or (max(ops) <= 5 and min(fr) >= D / 2))
print("3 ok: net constants; D >= 16: all 300 draws in E")

# 4. operator T, identities, exact MGF vs Monte Carlo, and the bound (Lemmas 4, 5)
def herm_basis(D):
    B = []
    for a in range(D):
        M = np.zeros((D, D), complex); M[a, a] = 1; B.append(M)
        for b in range(a + 1, D):
            M = np.zeros((D, D), complex); M[a, b] = M[b, a] = 1 / math.sqrt(2); B.append(M)
            M = np.zeros((D, D), complex); M[a, b] = -1j / math.sqrt(2); M[b, a] = 1j / math.sqrt(2); B.append(M)
    return np.array(B)
def schedule(D, N, aligned):  # list of bases of C^{2D} (already rotated by W^dagger); weights c = 1
    out = []
    for i in range(N):
        if i < aligned:
            A = np.zeros((2 * D, 2 * D), complex); A[:D, :D] = haar(D); A[D:, D:] = haar(D)
            th = 0.2 * rng.random()          # nearly V-aligned basis: rotate pairs by a small angle
            R = np.block([[np.cos(th) * np.eye(D), -np.sin(th) * np.eye(D)], [np.sin(th) * np.eye(D), np.cos(th) * np.eye(D)]])
            out.append(R @ A)
        else: out.append(haar(2 * D))
    return out
for D, N, aligned, e in ((3, 5, 0, 0.1), (3, 5, 2, 0.05), (4, 6, 3, 0.01), (4, 6, 6, 0.2)):
    B = herm_basis(D); n = D * D; sch = schedule(D, N, aligned)
    T = np.zeros((n, n)); A = np.zeros((D, D), complex); Agood = np.zeros((D, D), complex); badtr = 0.0
    Ti = []
    for V in sch:
        Tk = np.zeros((n, n))
        for j in range(2 * D):
            u = V[D:, j]; t = np.vdot(u, u).real; uh = u / math.sqrt(t); lam = t * phi(t, e)
            a = np.einsum('i,kij,j->k', uh.conj(), B, uh).real
            Tk += lam * np.outer(a, a); P_ = lam * np.outer(uh, uh.conj()); A += P_
            if t <= 0.75: Agood += P_
            else: badtr += lam
        Ti.append(Tk); T += Tk
    nA = np.linalg.norm(A, 2); trA = np.trace(A).real; tau = np.linalg.eigvalsh(T)
    assert tau.min() > -1e-10 and abs(np.trace(T) - trA) < 1e-9 and tau.max() <= nA + 1e-9
    assert np.linalg.eigvalsh(3 / (1 - e) * N * np.eye(D) - Agood).min() > -1e-9 and nA <= 3 / (1 - e) * N + badtr + 1e-9
    iv = np.einsum('kii->k', B).real / math.sqrt(D); P = np.eye(n) - np.outer(iv, iv); S = P @ T @ P
    ts = np.linalg.eigvalsh(S); assert (ts ** 2).sum() <= nA * trA + 1e-9
    # identity h_i = gamma <G, T_i G'> from the outcome probabilities, and E_j g = 0, 1 + h_i >= 0
    gam = e * e * c0 * c0 / D
    for _ in range(20):
        G, G2 = gue0(D), gue0(D)
        if max(np.linalg.norm(G, 2), np.linalg.norm(G2, 2)) > 3: continue
        cG, cG2 = (np.einsum('kij,ji->k', B, M).real for M in (G, G2))
        for V, Tk in zip(sch, Ti):
            r0 = np.diag([(1 - e) / D] * D + [e / D] * D)
            q = np.einsum('ij,i,ij->j', V.conj(), np.diag(r0), V).real
            dq, dq2 = (e * c0 / D * np.einsum('ij,ik,kj->j', V[D:].conj(), M, V[D:]).real for M in (G, G2))
            assert abs(dq.sum()) < 1e-12 and (q + dq).min() > 0
            h = (dq * dq2 / q).sum(); assert abs(h - gam * cG @ Tk @ cG2) < 1e-12 and 1 + h >= 0
    # MGF: E exp(theta <g, S g'>) = prod (1 - theta^2 tau^2)^(-1/2) <= exp(theta^2 sum tau^2) for theta^2 tau_max^2 <= 1/2
    th = math.sqrt(0.15) / ts.max(); exact = np.prod((1 - th * th * ts ** 2) ** -0.5)
    g = rng.normal(size=(400000, n)); g2 = rng.normal(size=(400000, n))
    mc = np.exp(th * np.einsum('ni,ij,nj->n', g, S, g2)); est, se = mc.mean(), mc.std() / math.sqrt(len(mc))
    assert abs(est - exact) < 6 * se + 1e-3 and exact <= math.exp(th * th * (ts ** 2).sum()) <= math.exp(th * th * nA * trA)
    th = math.sqrt(0.5) / ts.max(); assert np.prod((1 - th * th * ts ** 2) ** -0.5) <= math.exp(th * th * (ts ** 2).sum())
    print(f"4 ok D={D} N={N} aligned={aligned} eps={e}: ||A||/N={nA/N:.2f} trA/(ND)={trA/(N*D):.2f} bad tr/N={badtr/N:.2f} MC={est:.4f} exact={exact:.4f}")

# 5. final constants (Theorem A)
x = 49 * c0 ** 4 * 9          # N = 3 D^(3/2) / eps^2
assert 49 * c0 ** 4 * 9 / 60 <= 0.5
for D in (60, 100, 1000):
    pE = 1 - 2 * math.exp(-1.13 * D) - 2 * math.exp(-D * D / 32) - math.exp(-(D * D - 1) / 36)
    assert 0.05 + 0.5 * math.sqrt(math.exp(x) / pE ** 2 - 1) < 1 / 3
print("5 ok: N <= 3 D^(3/2)/eps^2 gives TV <= 0.05 + 0.5 sqrt(e^(441 c0^4)/P(E)^2 - 1) < 1/3")
