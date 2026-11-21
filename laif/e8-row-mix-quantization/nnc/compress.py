"""Weight-level compression methods.

Every method maps a weight matrix W (out x in) and an optional input second moment
H = X^T X (in x in) to (W_hat, bits), where bits is the storage of the compressed form.
The output error that calibration-aware methods minimize is tr((W - W_hat) H (W - W_hat)^T).
"""
import math
import torch
import tntorch as tn

FP = 16  # bits of one uncompressed weight, scale or zero point


def chol(H, damp=0.01):
    H = H.double()
    H = H + damp * H.diagonal().mean() * torch.eye(H.shape[0], dtype=H.dtype)
    return torch.linalg.cholesky(H)


def svd_robust(A):
    """Thin SVD; falls back to LAPACK gesvd when divide-and-conquer fails (repeated zero singular values)."""
    try:
        return torch.linalg.svd(A, full_matrices=False)
    except Exception:
        import scipy.linalg
        U, S, Vh = scipy.linalg.svd(A.double().numpy(), full_matrices=False, lapack_driver='gesvd')
        return tuple(torch.from_numpy(x).to(A.dtype) for x in (U, S, Vh))


def tt_svd(M, ranks, ins, outs):
    """TT-SVD of a TT-matrix M (prod ins x prod outs), cores (r, i_k, o_k, r') as in tntorch."""
    d = len(ins)
    T = M.reshape(ins + outs).permute([p for k in range(d) for p in (k, k + d)])  # (i1, o1, i2, o2, ...)
    cores, r, rest = [], 1, T.reshape(-1)
    for k in range(d - 1):
        A = rest.reshape(r * ins[k] * outs[k], -1)
        U, S, Vh = svd_robust(A)
        rk = min(ranks[k], S.numel())
        cores.append(U[:, :rk].reshape(r, ins[k], outs[k], rk))
        rest, r = S[:rk, None] * Vh[:rk], rk
    cores.append(rest.reshape(r, ins[-1], outs[-1], 1))
    return cores


def werr(W, What, H):
    """Relative output error tr(E H E^T) / tr(W H W^T)."""
    E = (W - What).double()
    H = H.double()
    return (torch.einsum('oi,ij,oj->', E, H, E) / torch.einsum('oi,ij,oj->', W.double(), H, W.double())).item()


# ---------------------------------------------------------------- quantization
def _qparams(Wg, b):
    lo, hi = Wg.amin(-1, keepdim=True), Wg.amax(-1, keepdim=True)
    return (hi - lo).clamp(min=1e-8) / (2 ** b - 1), lo


def _code(u, v):
    """Index of the nearest level of the sorted codebook v for each entry of u."""
    return torch.bucketize(u, (v[1:] + v[:-1]) / 2)


def _vcode(U, V, chunk=1 << 16):
    """Index of the nearest codeword of V (K x 2) for each consecutive pair of the last dim of U."""
    P = U.reshape(-1, 2)
    return torch.cat([torch.cdist(P[k:k + chunk], V).argmin(1) for k in range(0, len(P), chunk)]).reshape(*U.shape[:-1], -1)


def _q(w, s, lo, b, v=None):
    """Affine grid lo + s * level; levels 0..2^b-1, or the sorted codebook v (2^b levels, same units)."""
    if v is None:
        return ((w - lo) / s).round().clamp(0, 2 ** b - 1) * s + lo
    return v[_code((w - lo) / s, v)] * s + lo


def rtn(W, H=None, b=4, g=128):
    """Asymmetric round-to-nearest, min-max per group of g inputs."""
    o, i = W.shape
    g = g if g and i % g == 0 else i
    Wg = W.reshape(o, i // g, g)
    s, lo = _qparams(Wg, b)
    return _q(Wg, s, lo, b).reshape(o, i), o * i * b + (o * i // g) * 2 * FP


def rtn_flat(T, b, g=64):
    """RTN on an arbitrary tensor, groups of g consecutive entries; returns (T_hat, bits)."""
    n = T.numel()
    pad = (-n) % g
    f = torch.cat([T.reshape(-1), T.new_zeros(pad)]).reshape(-1, g)
    s, lo = _qparams(f, b)
    return _q(f, s, lo, b).reshape(-1)[:n].reshape(T.shape), n * b + (f.shape[0]) * 2 * FP


def _qparams_mse(Wg, b, grid=(1.0, 0.95, 0.9, 0.85, 0.8, 0.75, 0.7), v=None):
    """Min-max range shrunk by the factor (per row) that minimizes the squared rounding error."""
    best, out = None, None
    for f in grid:
        lo, hi = Wg.amin(-1, keepdim=True) * f, Wg.amax(-1, keepdim=True) * f
        sc = (hi - lo).clamp(min=1e-8) / (2 ** b - 1)
        err = ((_q(Wg, sc, lo, b, v) - Wg) ** 2).sum(-1, keepdim=True)
        if best is None:
            best, out = err, (sc, lo)
        else:
            m = err < best
            best = torch.where(m, err, best)
            out = (torch.where(m, sc, out[0]), torch.where(m, lo, out[1]))
    return out


def block_hadamard(n, seed=0, bs=64):
    """Orthogonal R = (I (x) Hadamard_bs / sqrt(bs)) diag(random signs); bs = largest power of 2 <= 64 dividing n."""
    import scipy.linalg
    while n % bs:
        bs //= 2
    Hd = torch.tensor(scipy.linalg.hadamard(bs), dtype=torch.float64) / bs ** 0.5
    sg = torch.randint(0, 2, (n,), generator=torch.Generator().manual_seed(seed)).double() * 2 - 1
    return torch.block_diag(*[Hd] * (n // bs)) * sg[None, :]


def kron_rotation(n, seed=0):
    """Orthogonal R = (Q_m (x) Hadamard_p / sqrt(p)) diag(random signs), n = m p with p the largest power
    of 2 dividing n and Q_m a seeded random orthogonal m x m: a rank-1 TT-matrix that mixes every input,
    also across the 64-wide blocks (attention heads) that block_hadamard keeps apart. Regenerated from
    the seed, so no stored bits; online cost O(n (log p + m))."""
    import scipy.linalg
    p = n & -n
    m = n // p
    Hd = torch.tensor(scipy.linalg.hadamard(p), dtype=torch.float64) / p ** 0.5
    Qm = torch.linalg.qr(torch.randn(m, m, generator=torch.Generator().manual_seed(seed), dtype=torch.float64))[0]
    sg = torch.randint(0, 2, (n,), generator=torch.Generator().manual_seed(seed)).double() * 2 - 1
    return torch.kron(Qm.contiguous(), Hd) * sg[None, :]


def _refit(W, Q, H, S, L, g, b, v=None):
    """Codes of Q fixed, the scale and zero point of every group of a row re-solved in closed form for the
    least H-weighted row error (normal equations, 2 x #groups unknowns per row), stored at fp16. A row keeps
    its old parameters unless the new ones lower its error, so the error never rises; no extra bits."""
    o, i = W.shape
    G = i // g
    W, Q, H, S, L = W.double(), Q.double(), H.double(), S.double(), L.double()
    gid = torch.arange(i) // g
    U = (Q - L[:, gid]) / S[:, gid]
    if v is None:
        C = U.round().clamp(0, 2 ** b - 1)  # levels GPTQ chose
    elif v.dim() == 2:  # pair codebook: codeword of each consecutive column pair
        C = v.double()[_vcode(U, v.double())].reshape(o, i)
    else:
        C = v.double()[_code(U, v.double())]
    P = torch.nn.functional.one_hot(gid, G).double()  # i x G group indicator
    HP = H @ P
    ss = torch.stack([(C * (C[:, h * g:(h + 1) * g] @ H[h * g:(h + 1) * g])) @ P for h in range(G)], 2)  # o x G x G
    sl = torch.einsum('oj,jg,jh->ogh', C, P, HP)
    ll = (P.T @ HP).expand(o, G, G)
    M = torch.cat([torch.cat([ss, sl], 2), torch.cat([sl.transpose(1, 2), ll], 2)], 1)
    HW = W @ H
    r = torch.cat([(C * HW) @ P, HW @ P], 1)
    M = M + 1e-10 * M.diagonal(dim1=1, dim2=2).mean(1)[:, None, None] * torch.eye(2 * G, dtype=M.dtype)
    th = torch.linalg.solve(M, r[..., None])[..., 0].half().double()  # stored as fp16
    Qn = C * th[:, gid] + th[:, G + gid]
    err = lambda X: torch.einsum('oi,ij,oj->o', W - X, H, W - X)
    keep = (err(Qn) < err(Q)) & th.isfinite().all(1)
    k = keep[:, None]
    return torch.where(k, Qn, Q).float(), torch.where(k, th[:, :G], S).float(), torch.where(k, th[:, G:], L).float()


def _gptq_pass(W, Hinv, g, b, block, qp, S=None, L=None, v=None):
    """One GPTQ sweep over the columns of W with error feedback through Hinv (upper Cholesky factor of H^-1).
    Group scales and zero points come from qp at the start of each group, or from fixed S, L (o x #groups).
    Returns Q and the S, L used."""
    W = W.clone()
    o, i = W.shape
    fixed = S is not None
    if not fixed:
        S, L = torch.zeros(o, i // g), torch.zeros(o, i // g)
    Q = torch.zeros_like(W)
    for i1 in range(0, i, block):
        i2 = min(i1 + block, i)
        W1, Q1, E1, Hi = W[:, i1:i2].clone(), torch.zeros(o, i2 - i1), torch.zeros(o, i2 - i1), Hinv[i1:i2, i1:i2]
        for j in range(0, i2 - i1, 2 if v is not None and v.dim() == 2 else 1):
            if (i1 + j) % g == 0:
                h = (i1 + j) // g
                if not fixed:
                    s, lo = qp(torch.cat([W1[:, j:], W[:, i2:]], 1)[:, :g], b)
                    S[:, h], L[:, h] = s[:, 0], lo[:, 0]
                s, lo = S[:, h], L[:, h]
            if v is not None and v.dim() == 2:  # joint pair: nearest codeword in the H^-1 block metric
                T = torch.linalg.inv(Hi[j:j + 2, j:j + 2])
                w = W1[:, j:j + 2]
                c = torch.cdist(((w - lo[:, None]) / s[:, None]) @ T, v @ T).argmin(1)
                q = v[c] * s[:, None] + lo[:, None]
                Q1[:, j:j + 2] = q
                e = (w - q) @ T
                W1[:, j:] -= e @ Hi[j:j + 2, j:]
                E1[:, j:j + 2] = e
                continue
            w = W1[:, j]
            q = _q(w, s, lo, b, v)
            Q1[:, j] = q
            e = (w - q) / Hi[j, j]
            W1[:, j:] -= e[:, None] * Hi[j, j:][None, :]
            E1[:, j] = e
        Q[:, i1:i2] = Q1
        W[:, i2:] -= E1 @ Hinv[i1:i2, i2:]
    return Q, S, L


def _lloyd(W, d, g, b, clip, iters=20, rounds=3):
    """Codebook of 2^b sorted levels in grid units (uniform grid: 0..2^b-1) for the group-affine grid of W:
    weighted 1-D k-means of the normalized weights (w - lo) / s, each weighted by d_j s^2 (its squared error
    in output units under the diagonal d of H), alternated with the group ranges for the current codebook."""
    o, i = W.shape
    v = torch.arange(2 ** b, dtype=torch.float32)
    Wg = W.reshape(o, i // g, g)
    for _ in range(rounds):
        s, lo = _qparams_mse(Wg, b, v=v) if clip else _qparams(Wg, b)
        u = ((Wg - lo) / s).reshape(-1)
        wt = (d.reshape(1, i // g, g) * s ** 2).expand_as(Wg).reshape(-1)
        for _ in range(iters):
            c = _code(u, v)
            den = torch.zeros(2 ** b).index_add_(0, c, wt)
            v = torch.where(den > 0, torch.zeros(2 ** b).index_add_(0, c, wt * u) / den.clamp(min=1e-30), v).sort().values
    return v.half().float()  # stored at fp16


def _lloyd2(W, d, g, b, clip, iters=20, nfit=1 << 16):
    """Pair codebook of 2^(2b) points in grid units for consecutive column pairs: weighted 2-D k-means of the
    normalized pairs (each coordinate weighted by d_j s^2), started from the product of the 1-D codebook v1
    of _lloyd and run at v1's group ranges, so its weighted distortion (on the fitted pairs) is at most that of
    the product codebook. Fitted on at most nfit pairs drawn with a fixed seed. Returns (V, v1); v1 picks the
    group ranges."""
    o, i = W.shape
    v1 = _lloyd(W, d, g, b, clip)
    Wg = W.reshape(o, i // g, g)
    s, lo = _qparams_mse(Wg, b, v=v1) if clip else _qparams(Wg, b)
    u = ((Wg - lo) / s).reshape(-1, 2)
    wt = (d.reshape(1, i // g, g) * s ** 2).expand_as(Wg).reshape(-1, 2).double()
    if len(u) > nfit:  # shortcut: fit on a fixed subsample of pairs; raise nfit if 2^(2b) nears it
        sub = torch.randperm(len(u), generator=torch.Generator().manual_seed(0))[:nfit]
        u, wt = u[sub], wt[sub]
    V = torch.cartesian_prod(v1, v1)
    K = len(V)
    for _ in range(iters):
        wf = wt.float()  # sum_c w_c (u_c - V_c)^2 without the V-independent term
        c = torch.cat([(wf[k:k + 8192] @ (V ** 2).T - 2 * (wf[k:k + 8192] * u[k:k + 8192]) @ V.T).argmin(1)
                       for k in range(0, len(u), 8192)])
        den = torch.zeros(K, 2, dtype=torch.float64).index_add_(0, c, wt)
        num = torch.zeros(K, 2, dtype=torch.float64).index_add_(0, c, wt * u.double())
        V = torch.where(den > 0, num / den.clamp(min=1e-300), V.double()).float()
    return V.half().float(), v1  # stored at fp16


def gptq(W, H, b=4, g=128, damp=0.01, block=128, act=0, clip=0, had=0, refit=0, alt=0, nu=0, vq=0):
    """GPTQ with groups. act: columns in order of decreasing H_jj (group index per column stored);
    clip: MSE-optimal range per group; had: quantize W R with an orthogonal R deployed as an online
    rotation of the input (no stored bits): 1 random-sign block Hadamard, 2 Kronecker rotation over all
    inputs, 3 whichever of the two gives the lower H-weighted error (one stored bit per layer).
    refit: after GPTQ, re-solve each row's group scales and zero points for the H-weighted error (_refit).
    alt (with refit): that many more rounds of GPTQ with the refit scales and zero points held fixed
    (codes re-chosen with error feedback) followed by another refit; a row takes a round's result only
    where its H-weighted error drops, so the error never rises. Stops early once a round lowers the layer
    error by under 0.1 %. Same storage format, no extra bits.
    nu: non-uniform grid. Every group keeps its scale and zero point, but the 2^b levels are a per-layer
    codebook (_lloyd, stored at fp16: 2^b * 16 bits per layer) instead of 0..2^b-1; GPTQ rounds to the
    nearest level, refit and alt work on the codebook values.
    vq: pair codebook. Consecutive columns (in GPTQ order, inside one group) are coded jointly by one of
    2^(2b) points of a per-layer 2-D codebook (_lloyd2, stored at fp16: 2^(2b) * 2 * 16 bits per layer), each
    coordinate mapped through its group's scale and zero point; same 2b code bits per pair. GPTQ takes two
    columns per step: nearest codeword in the metric of the 2 x 2 block of the H^-1 Cholesky factor, block
    error feedback. Refit and alt work unchanged on the decoded codeword coordinates."""
    if had == 3:
        (Q1, b1), (Q2, b2) = (gptq(W, H, b, g, damp, block, act, clip, h, refit, alt, nu, vq) for h in (1, 2))
        return (Q1, b1 + 1) if werr(W, Q1, H) <= werr(W, Q2, H) else (Q2, b2 + 1)
    if had:
        R = (block_hadamard if had == 1 else kron_rotation)(W.shape[1]).float()
        Q, bits = gptq(W @ R, R.T @ H.float() @ R, b, g, damp, block, act, clip, 0, refit, alt, nu, vq)
        return Q @ R.T, bits
    W = W.clone().float()
    o, i = W.shape
    g = g if g and i % g == 0 else i
    H = H.clone().float()
    dead = H.diagonal() == 0
    H[dead, dead] = 1
    W[:, dead] = 0
    perm = torch.argsort(H.diagonal(), descending=True) if act else torch.arange(i)
    W, H = W[:, perm], H[perm][:, perm]
    if refit:
        W0, H0 = W.clone(), H.clone()
    H += damp * H.diagonal().mean() * torch.eye(i)
    Hinv = torch.linalg.cholesky(torch.cholesky_inverse(torch.linalg.cholesky(H)), upper=True)
    if vq:
        assert g % 2 == 0 and block % 2 == 0
        v, v1 = _lloyd2(W, H.diagonal(), g, b, clip)
    else:
        v = v1 = _lloyd(W, H.diagonal(), g, b, clip) if nu else None
    qp = (lambda X, b: _qparams_mse(X, b, v=v1)) if clip else _qparams
    Q, S, L = _gptq_pass(W, Hinv, g, b, block, qp, v=v)
    if refit:
        Q, S, L = _refit(W0, Q, H0, S, L, g, b, v)
        e = row_err(W0, Q, H0)
        for _ in range(alt):
            Qa, Sa, La = _refit(W0, _gptq_pass(W, Hinv, g, b, block, None, S, L, v)[0], H0, S, L, g, b, v)
            ea = torch.minimum(row_err(W0, Qa, H0), e)
            if ea.sum() > (1 - 1e-3) * e.sum():  # converged: a round gains under 0.1 % of the layer error
                break
            k = (ea < e)[:, None]
            Q, S, L, e = torch.where(k, Qa, Q), torch.where(k, Sa, S), torch.where(k, La, L), torch.minimum(ea, e)
    Q = Q[:, torch.argsort(perm)]
    gidx = i * math.ceil(math.log2(max(2, i // g))) if act else 0
    return Q, o * i * b + (o * i // g) * 2 * FP + gidx + (2 ** (2 * b) * 2 * FP if vq else 2 ** b * FP if nu else 0)


E8P_PAD = [[3, 1, 1, 1, 3, 3, 3, 3], [1, 3, 1, 1, 3, 3, 3, 3], [1, 1, 3, 1, 3, 3, 3, 3], [1, 1, 1, 3, 3, 3, 3, 3],
           [3, 3, 3, 1, 3, 3, 1, 1], [3, 3, 3, 1, 3, 1, 3, 1], [3, 3, 3, 1, 1, 3, 3, 1], [3, 3, 3, 1, 3, 1, 1, 3],
           [3, 3, 3, 1, 1, 3, 1, 3], [3, 3, 3, 1, 1, 1, 3, 3], [3, 3, 1, 3, 3, 3, 1, 1], [3, 3, 1, 3, 3, 1, 3, 1],
           [3, 3, 1, 3, 1, 3, 3, 1], [3, 3, 1, 3, 3, 1, 1, 3], [3, 3, 1, 3, 1, 3, 1, 3], [3, 3, 1, 3, 1, 1, 3, 3],
           [3, 1, 3, 3, 3, 3, 1, 1], [3, 1, 3, 3, 3, 1, 3, 1], [3, 1, 3, 3, 1, 3, 3, 1], [3, 1, 3, 3, 3, 1, 1, 3],
           [3, 1, 3, 3, 1, 3, 1, 3], [1, 3, 3, 3, 1, 1, 3, 3], [1, 3, 3, 3, 3, 3, 1, 1], [1, 3, 3, 3, 3, 1, 3, 1],
           [1, 3, 3, 3, 1, 3, 3, 1], [1, 3, 3, 3, 3, 1, 1, 3], [1, 3, 3, 3, 1, 3, 1, 3], [1, 1, 3, 3, 1, 3, 3, 3],
           [3, 3, 1, 1, 3, 3, 3, 1]]  # QuIP# (2402.04396) App. C.1, in units of 1/2


def e8p_source():
    """Source set S of the E8P codebook: the 227 absolute-value patterns of half-odd vectors with norm^2 <= 10
    plus 29 of norm^2 12. Codebook: sigma * s + t, s in S, sigma a sign pattern with sigma * s of even sum
    (in D8^), t = +-1/4: 2^16 points of E8 + 1/4, 2 bits per weight."""
    import itertools
    base = [v for v in itertools.product((1, 3, 5), repeat=8) if sum(x * x for x in v) <= 40]
    return torch.tensor(base + E8P_PAD, dtype=torch.float32) / 2


def e8p_nearest(Y, S):
    """Nearest E8P point to each row of Y (N x 8). Per shift t and source s the best sign pattern is sign(y - t);
    if that pattern has odd sum, the cheapest single flip (min s_i |y_i - t|) restores parity."""
    r = torch.arange(len(Y))
    n2 = (S ** 2).sum(1)
    best, out = None, None
    for t in (0.25, -0.25):
        X = Y - t
        sg = torch.where(X < 0, -1.0, 1.0)
        A = X.abs()
        odd = torch.remainder(torch.round(sg @ S.T), 2) == 1
        pen = (A[:, None, :] * S[None]).min(-1).values
        d = n2 - 2 * (A @ S.T) + 4 * pen * odd  # ||x - q||^2 - ||x||^2
        k = d.argmin(1)
        q = sg * S[k]
        fl = odd[r, k]
        j = (A * S[k]).argmin(1)
        q[r[fl], j[fl]] *= -1
        q = q + t
        dk = ((Y - q) ** 2).sum(1)
        if best is None:
            best, out = dk, q
        else:
            m = dk < best
            best, out = torch.where(m, dk, best), torch.where(m[:, None], q, out)
    return out


E8P_SCALE = 0.96  # step c: W / (c rms(W)) is quantized; argmin of the Gaussian MSE (sim/test_quip.py)


def quip(W, H, damp=0.01, block=128, c=E8P_SCALE, seed=0, rescale=0, ro=1, rows=0, tune=0, ri=2):
    """2-bit lattice quantization in the QuIP# form without fine-tuning: random-sign Hadamard-Kronecker rotations
    on both sides (kron_rotation; seeded, deployed online, no stored bits), one fp16 scale per matrix, and
    block LDL rounding: 8 columns at a time to the nearest E8P point, block error feedback through the
    upper Cholesky factor of H^-1 (as the GPTQ pass). Bits: 2 per weight + 16.
    rescale=a: quantize W D, H -> D^-1 H D^-1 with D = diag(H_jj^(a/2)) at fp16 (folded into the input
    rotation; + 16 bits per input), so columns that carry input energy get finer steps after mixing.
    ro=0: no output rotation; rows=1: one fp16 scale per row (+ 16 bits per output).
    tune=k: k passes of block coordinate descent after the LDL rounding (QuIP#'s quip_tune_iters): block t of
    8 columns is re-rounded at Q_t + (W - Q) H[:, t] H[t, t]^-1, the minimizer of the H-weighted error over
    that block with the others fixed; a row keeps a pass only where its error drops.
    ri: input rotation, 2 kron_rotation, 1 block_hadamard (the rotation of gptq had=1, so rows can be mixed)."""
    if rescale:
        d = H.diagonal().float().clamp(min=1e-8 * H.diagonal().max().item()) ** (rescale / 2)
        d = (d / d.mean()).half().float()
        Q, bits = quip(W * d, H / d[:, None] / d[None], damp, block, c, seed, 0, ro, rows, tune, ri)
        return Q / d, bits + FP * W.shape[1]
    o, i = W.shape
    assert i % 8 == 0
    Ri = (kron_rotation if ri == 2 else block_hadamard)(i, seed).float()
    Ro = kron_rotation(o, seed + 1).float() if ro else torch.eye(o)
    Wn = Ro.T @ W.float() @ Ri
    s = (c * (Wn.pow(2).mean(1, keepdim=True) if rows else Wn.pow(2).mean()).sqrt()).half().float()
    s = torch.where(s > 0, s, torch.full_like(s, 2.0 ** -14))  # zero rows: E8P has no zero point, so the smallest normal fp16 step
    Wn = Wn / s
    W0 = Wn.clone() if tune else None
    Hr = Ri.T @ H.float() @ Ri
    Hr += damp * Hr.diagonal().mean() * torch.eye(i)
    Hinv = torch.linalg.cholesky(torch.cholesky_inverse(torch.linalg.cholesky(Hr)), upper=True)
    S = e8p_source()
    Q = torch.zeros_like(Wn)
    for i1 in range(0, i, block):
        i2 = min(i1 + block, i)
        W1, E1, Hi = Wn[:, i1:i2].clone(), torch.zeros(o, i2 - i1), Hinv[i1:i2, i1:i2]
        for j in range(0, i2 - i1, 8):
            w = W1[:, j:j + 8]
            q = e8p_nearest(w, S)
            Q[:, i1 + j:i1 + j + 8] = q
            e = (w - q) @ torch.linalg.inv(Hi[j:j + 8, j:j + 8])
            W1[:, j:] -= e @ Hi[j:j + 8, j:]
            E1[:, j:j + 8] = e
        Wn[:, i2:] -= E1 @ Hinv[i1:i2, i2:]
    if tune:
        Q = _e8p_tune(W0, Q, Hr, S, tune)
    return Ro @ (Q * s) @ Ri.T, 2 * o * i + FP * (o if rows else 1)


def _e8p_tune(W, Q, H, S, passes):
    """Block coordinate descent on tr((W - Q) H (W - Q)^T) over blocks of 8 columns, rounding to E8P;
    per row, the best pass is kept (the objective is a sum over rows)."""
    best, e = Q.clone(), row_err(W, Q, H)
    Hb = [torch.linalg.inv(H[j:j + 8, j:j + 8]) for j in range(0, W.shape[1], 8)]
    for _ in range(passes):
        R = (W - Q) @ H
        for k, j in enumerate(range(0, W.shape[1], 8)):
            q = e8p_nearest(Q[:, j:j + 8] + R[:, j:j + 8] @ Hb[k], S)
            R -= (q - Q[:, j:j + 8]) @ H[j:j + 8]
            Q[:, j:j + 8] = q
        ea = row_err(W, Q, H)
        k = ea < e
        best[k], e = Q[k], torch.minimum(ea, e)
    return best


def row_err(W, Q, H):
    """Per-row output error e_o H e_o^T; the layer error tr(E H E^T) is their sum."""
    E = (W - Q).double()
    return torch.einsum('oi,ij,oj->o', E, H.double(), E)


def allocate(D, bs, budget):
    """Greedy rate-distortion allocation: D (o x len(bs)) row errors at widths bs (ascending);
    upgrade the row with the largest error drop per extra bit until sum(bits) would pass budget.
    Returns the width index per row."""
    o = D.shape[0]
    k = torch.zeros(o, dtype=torch.long)
    used = o * bs[0]
    rows = torch.arange(o)
    while True:
        up = k < len(bs) - 1
        nk = (k + 1).clamp(max=len(bs) - 1)
        cost = torch.tensor(bs)[nk] - torch.tensor(bs)[k]
        gain = torch.where(up & (used + cost <= budget), (D[rows, k] - D[rows, nk]) / cost.clamp(min=1), -torch.inf)
        j = int(gain.argmax())
        if gain[j] <= 0:
            return k
        used += int(cost[j])
        k[j] += 1


def gmix(W, H, bpw=3.25, lo=2, hi=4, g=128, act=1, clip=1, had=1, cb=0.0, lam=0.0, e8=0, e8c=E8P_SCALE, e8tune=0, **gk):
    """GPTQ with a bit width per output row. GPTQ treats rows independently (H is shared), so the
    layer error is the sum of per-row errors and a row quantized at width b equals that row of a
    full GPTQ run at b. Run GPTQ at every width in lo..hi, then allocate widths by greedy
    rate-distortion under the bpw budget (scales, group indices and a per-row width tag counted).
    cb > 0: budget is cb code bits per weight plus that layer's own overhead, instead of bpw.
    lam > 0: no per-layer budget; one rate-distortion slope for the whole model. Each row takes the width
    minimizing sum_j F_oj E_oj^2 + lam * 1e-6 * bits, with F the diagonal empirical Fisher of the loss
    (nnc/fisher.py), so row errors are in loss units and comparable across layers; lam sets the bpw.
    e8=1 (with lam): one more option per row, the E8P lattice code of quip (2 bits per weight, one fp16 scale per row,
    no groups, no output rotation, the same online input rotation as the GPTQ runs: had=1 block Hadamard, 2 Kronecker),
    so a row costs 2 i + 16 bits instead of b i + its group scales. Rows stay independent, so the mix is exact.
    e8c, e8tune: quip's scale c and tune passes."""
    o, i = W.shape
    bs = list(range(lo, hi + 1))
    if had == 3:  # one rotation for all widths (rows share the online input rotation), chosen at the middle width
        bm = bs[len(bs) // 2]
        had = min((1, 2), key=lambda h: werr(W, gptq(W, H, bm, g, act=act, clip=clip, had=h, **gk)[0], H))
        runs = [gptq(W, H, b, g, act=act, clip=clip, had=had, **gk) for b in bs]
        runs = [(Q, bb + 1) for Q, bb in runs]  # rotation flag
    else:
        runs = [gptq(W, H, b, g, act=act, clip=clip, had=had, **gk) for b in bs]
    nopt = len(bs) + (1 if e8 else 0)
    over = runs[0][1] - o * i * lo + (o * math.ceil(math.log2(nopt)) if nopt > 1 else 0)
    over += sum(2 ** (2 * b) * 2 * FP if gk.get('vq') else 2 ** b * FP if gk.get('nu') else 0
                for b in bs[1:])  # one codebook per width (runs[0] holds the lowest)
    if e8:
        assert lam and had in (1, 2), 'e8 needs the Fisher slope and one fixed input rotation'
        gg = g if g and i % g == 0 else i
        rs = (i // gg) * 2 * FP  # group scales and zero points of one scalar row (inside over)
        Qe, _ = quip(W, H, c=e8c, ro=0, rows=1, tune=e8tune, ri=had)
        rowbits = torch.tensor([b * i + rs for b in bs] + [2 * i + FP], dtype=torch.float64)
        runs = runs + [(Qe, None)]
        over -= o * rs  # per-row costs now carry their own scales
    else:
        rowbits = torch.tensor([b * i for b in bs], dtype=torch.float64)
    if lam:
        from .fisher import lookup
        F = lookup(W).double()
        D = torch.stack([((W - Q).double() ** 2 * F).sum(1) for Q, _ in runs], 1)
        k = (D + lam * 1e-6 * rowbits).argmin(1)  # exact Lagrangian optimum per row
        Q = torch.stack([Qb for Qb, _ in runs])[k, torch.arange(o)]
        return Q, over + int(rowbits[k].sum().item())
    else:
        D = torch.stack([row_err(W, Q, H) for Q, _ in runs], 1)
        k = allocate(D, bs, int(cb * o) if cb else int((bpw * o * i - over) // i))
    Q = torch.stack([Qb for Qb, _ in runs])[k, torch.arange(o)]
    return Q, over + sum(bs[int(x)] for x in k) * i


# ---------------------------------------------------------------- low rank
def _rank(o, i, bpw, pb):
    return max(1, int(bpw * o * i / (pb * (o + i))))


def lowrank_factors(W, r, H=None):
    """Best rank-r factors A (o x r), B (r x i); with H the H-weighted optimum (whitened SVD)."""
    if H is None:
        U, S, Vh = svd_robust(W.double())
        A, B = U[:, :r] * S[:r].sqrt(), S[:r].sqrt()[:, None] * Vh[:r]
    else:
        L = chol(H)
        U, S, Vh = svd_robust(W.double() @ L)
        A = U[:, :r] * S[:r].sqrt()
        B = torch.linalg.solve_triangular(L, S[:r].sqrt()[:, None] * Vh[:r], upper=False, left=False)
    return A.float(), B.float()


def svd(W, H=None, bpw=4.0, whiten=1, fb=16, g=64):
    """Low rank at budget bpw; factors stored at fb bits (RTN, groups g) if fb < 16."""
    pb = FP if fb >= 16 else fb + 2 * FP / g
    r = _rank(*W.shape, bpw, pb)
    A, B = lowrank_factors(W, r, H if whiten else None)
    if fb >= 16:
        return A @ B, r * sum(W.shape) * FP
    (Aq, ba), (Bq, bb) = rtn_flat(A, fb, g), rtn_flat(B, fb, g)
    return Aq @ Bq, ba + bb


def qlr(W, H=None, b=3, g=128, r=0.0, whiten=1, q='gptq', **gk):
    """W ~ Q(W) + A B: quantize, then a (whitened) low-rank fit of the residual; r = rank fraction of min(o,i)."""
    Q, bits = (gptq(W, H, b, g, **gk) if q == 'gptq' and H is not None else rtn(W, None, b, g))
    k = int(r * min(W.shape))
    if k == 0:
        return Q, bits
    A, B = lowrank_factors(W - Q, k, H if whiten else None)
    return Q + A @ B, bits + k * sum(W.shape) * FP


def lrq(W, H=None, b=3, g=128, r=0.05, whiten=1, fb=16, **gk):
    """W ~ A B + Q(W - A B): structured low-rank part first, GPTQ on the residual (H-aware)."""
    k = int(r * min(W.shape))
    A, B = lowrank_factors(W, k, H if whiten else None) if k else (W.new_zeros(W.shape[0], 0), W.new_zeros(0, W.shape[1]))
    lb = k * sum(W.shape) * FP
    if fb < 16 and k:
        (A, ba), (B, bb) = rtn_flat(A, fb, 64), rtn_flat(B, fb, 64)
        lb = ba + bb
    L = A @ B
    Q, qb = gptq(W - L, H, b, g, **gk) if H is not None else rtn(W - L, None, b, g)
    return L + Q, lb + qb


def ttq(W, H=None, b=3, g=128, tbpw=1.0, d=3, kron=0, diag=0.0, **gk):
    """W ~ T + Q(W - T): a TT part at tbpw bits per weight, GPTQ on the residual."""
    T, tb = tt(W, H, bpw=tbpw, d=d, kron=kron, diag=diag)
    Q, qb = gptq(W - T, H, b, g, **gk) if H is not None else rtn(W - T, None, b, g)
    return T + Q, tb + qb


# ---------------------------------------------------------------- pruning
def prune(W, H=None, s=0.5, wanda=1, b=16, g=128):
    """Unstructured pruning per output row (Wanda score |W| * ||x_j|| if wanda), bitmap + values."""
    score = W.abs() * (H.diagonal().clamp(min=0).sqrt()[None, :] if wanda and H is not None else 1)
    k = int(s * W.shape[1])
    idx = score.argsort(1)[:, :k]
    Wp = W.clone().scatter_(1, idx, 0.0)
    nnz = Wp.numel() - k * W.shape[0]
    if b >= 16:
        return Wp, W.numel() + nnz * FP
    Wq, _ = rtn(Wp, None, b, g)
    Wq = Wq * (Wp != 0)
    return Wq, W.numel() + nnz * b + (W.numel() // g) * 2 * FP


# ---------------------------------------------------------------- tensor trains
def _factor(n, d):
    if d == 1:
        return [n]
    best = None
    divs = {f for a in range(2, int(n ** 0.5) + 1) if n % a == 0 for f in (a, n // a)}
    for f in sorted(divs):
        if True:
            rest = _factor(n // f, d - 1)
            if rest is None:
                continue
            c = sorted([f] + rest)
            if best is None or max(c) / min(c) < max(best) / min(best):
                best = c
    return best


def tt_dims(n, d):
    """Balanced factorization of n' >= n into d factors (n' = n padded when n factors badly)."""
    for m in range(n, int(n * 1.15) + 2):
        f = _factor(m, d)
        if f and max(f) <= 2.2 * m ** (1 / d):
            return m, f
    return n, _factor(n, d) or [n]


def _tt_params(ins, outs, r):
    d = len(ins)
    rk = [1] + [r] * (d - 1) + [1]
    # bond rank cannot exceed the matricization rank
    for k in range(1, d):
        left = math.prod(a * b for a, b in zip(ins[:k], outs[:k]))
        right = math.prod(a * b for a, b in zip(ins[k:], outs[k:]))
        rk[k] = min(r, left, right)
    return sum(rk[k] * ins[k] * outs[k] * rk[k + 1] for k in range(d)), rk[1:-1]


def nearest_kron(H, dims, iters=8):
    """Rank-1 Kronecker approximation H ~ H_1 x ... x H_d (mode 1 most significant), PSD factors."""
    d = len(dims)
    T = H.double().reshape(dims + dims)
    T = T.permute([p for k in range(d) for p in (k, k + d)])  # (i1, j1, i2, j2, ...)
    F = [torch.eye(n, dtype=T.dtype) for n in dims]
    letters = 'abcdefghijklmnopqrstuvwxyz'
    idx = ''.join(letters[2 * k] + letters[2 * k + 1] for k in range(d))
    for _ in range(iters):
        for k in range(d):
            ops = [F[m] for m in range(d) if m != k]
            sub = ','.join(letters[2 * m] + letters[2 * m + 1] for m in range(d) if m != k)
            M = torch.einsum(f'{idx},{sub}->{letters[2 * k]}{letters[2 * k + 1]}', T, *ops)
            M = (M + M.T) / 2
            F[k] = M / M.norm()
    lam = torch.einsum(f'{idx},' + ','.join(letters[2 * m] + letters[2 * m + 1] for m in range(d)) + '->', T, *F)
    F = [(f * f.trace().sign()) for f in F]
    F[0] = F[0] * lam.abs()
    return F


def _mode_mult(X, mats, dims):
    """X: (o, prod dims) -> X (x) multiplied on input mode k by mats[k] from the right."""
    o = X.shape[0]
    T = X.reshape([o] + dims)
    for k, Mk in enumerate(mats):
        T = torch.movedim(torch.tensordot(T, Mk, dims=([k + 1], [0])), -1, k + 1)
    return T.reshape(o, -1)


def tt_cores(W, bpw=4.0, d=3, H=None, kron=1, fb=16, g=64, refine=0, lr=1e-3):
    """TT-matrix approximation at budget bpw. With H and kron, whitening by the nearest Kronecker
    factor of H keeps the TT format exact: W L -> TT-SVD -> cores times L_k^{-1}.
    Returns cores (tntorch layout r, i_k, o_k, r'), dims and bits."""
    o, i = W.shape
    pb = FP if fb >= 16 else fb + 2 * FP / g
    ip, ins = tt_dims(i, d)
    op, outs = tt_dims(o, d)
    if len(ins) != d or len(outs) != d:
        raise ValueError(f'cannot factor {W.shape} into {d} modes')
    Wp = torch.zeros(op, ip, dtype=torch.float64)
    Wp[:o, :i] = W.double()
    budget = bpw * o * i / pb
    r = 1
    while _tt_params(ins, outs, r + 1)[0] <= budget and r < 4096:
        r += 1
    _, ranks = _tt_params(ins, outs, r)
    Ls = None
    if H is not None and kron:
        Hp = torch.eye(ip, dtype=torch.float64) * H.double().diagonal().mean() * 1e-3
        Hp[:i, :i] += H.double()
        Ls = [chol(Hk, 1e-3) for Hk in nearest_kron(Hp, ins)]
        Wp = _mode_mult(Wp, Ls, ins)
    cores = tt_svd(Wp.T.contiguous(), list(ranks), ins, outs)
    if Ls is not None:
        for k, Lk in enumerate(Ls):
            Linv_T = torch.linalg.inv(Lk).T  # M = W_hat^T, so input mode gets L_k^{-T}
            cores[k] = torch.einsum('ij,ajob->aiob', Linv_T, cores[k])
    if refine and H is not None:
        cores = _refine(cores, W, H, ins, outs, o, i, refine, lr)
    bits = sum(c.numel() for c in cores) * FP
    if fb < 16:
        q = [rtn_flat(c.float(), fb, g) for c in cores]
        cores, bits = [c for c, _ in q], sum(bb for _, bb in q)
    return [c.float() for c in cores], (ins, outs, o, i), bits


def tt_full(cores, dims):
    ins, outs, o, i = dims
    t = tn.TTMatrix([c.double() for c in cores], ranks=[c.shape[-1] for c in cores[:-1]], input_dims=ins, output_dims=outs)
    return t.torch().T[:o, :i].float()


def _refine(cores, W, H, ins, outs, o, i, steps, lr):
    """Adam on the cores against the exact H-weighted error, H truncated to its top eigenpairs."""
    ev, V = torch.linalg.eigh(H.double())
    k = min(len(ev), 512)
    P = (V[:, -k:] * ev[-k:].clamp(min=0).sqrt()).float()  # H ~ P P^T
    WP = W.float() @ P
    ps = [torch.nn.Parameter(c.float()) for c in cores]
    opt = torch.optim.Adam(ps, lr=lr)
    dims = (ins, outs, o, i)
    base = WP.norm() ** 2
    for _ in range(steps):
        opt.zero_grad()
        loss = ((tt_full_grad(ps, dims) @ P - WP) ** 2).sum() / base
        loss.backward()
        opt.step()
    return [p.detach().double() for p in ps]


def tt_full_grad(cores, dims):
    ins, outs, o, i = dims
    T = cores[0][0]  # (i1, o1, r)
    for c in cores[1:]:
        T = torch.einsum('...r,rjps->...jps', T, c)
    d = len(cores)
    T = T[..., 0]  # (i1, o1, i2, o2, ...)
    T = T.permute([2 * k + 1 for k in range(d)] + [2 * k for k in range(d)])
    return T.reshape(math.prod(outs), math.prod(ins))[:o, :i]


def diag_scale(H, alpha, floor=0.1):
    """s = sqrt(diag H)^alpha / mean, floored so that rarely active inputs are not amplified by 1/s."""
    s = H.diagonal().clamp(min=1e-12).sqrt() ** alpha
    return (s / s.mean()).clamp(min=floor).float()


def tt(W, H=None, bpw=4.0, d=3, kron=1, fb=16, g=64, refine=0, lr=1e-3, diag=0.0):
    """diag = alpha > 0: diagonal activation preconditioner s = sqrt(diag H)^alpha (as in 2610.10085),
    deployed as an input rescaling x / s that costs one 16-bit scale per input; combinable with kron."""
    if diag and H is not None:
        s = diag_scale(H, diag)
        bpw -= FP / W.shape[0]
        cores, dims, bits = tt_cores(W * s[None], bpw, d, H / (s[:, None] * s[None]), kron, fb, g, refine, lr)
        return tt_full(cores, dims) / s[None], bits + W.shape[1] * FP
    cores, dims, bits = tt_cores(W, bpw, d, H, kron, fb, g, refine, lr)
    return tt_full(cores, dims), bits


def none(W, H=None):
    return W.clone(), W.numel() * FP


METHODS = dict(none=none, rtn=rtn, gptq=gptq, gmix=gmix, quip=quip, svd=svd, qlr=qlr, lrq=lrq, ttq=ttq, prune=prune, tt=tt)


def parse(spec):
    """'tt:bpw=4,d=3,kron=1' -> (fn, kwargs)."""
    name, _, args = spec.partition(':')
    kw = {}
    for a in filter(None, args.split(',')):
        k, v = a.split('=')
        kw[k] = v if k == 'q' else (float(v) if '.' in v or 'e' in v else int(v))
    return METHODS[name], kw
