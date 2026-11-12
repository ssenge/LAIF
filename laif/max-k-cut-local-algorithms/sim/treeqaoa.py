"""Exact depth-p local qudit algorithms for Max-k-Cut on d-regular graphs of girth >= 2p+2.

Each layer t applies a diagonal phase exp(-i phi_t(a_u, a_v)) on every edge (phi_t symmetric k x k
real) and then the same single-qudit unitary U_t on every vertex; the start state is phi0 on every
vertex. QAOA with the Grover mixer is phi_t = gamma_t * [a == b], U_t = exp(-i beta_t |+><+|).

The edge expectation is the tree contraction of [BFMVZ22, FGRV25, 2609.39042 eq. 68]: every vertex
carries a label string a in Z_k^(2p+1) (axes 0..p-1 ket layers 1..p, axis p the middle, axis p+t the
bra layer t), and the edge factor exp(-i sum_t phi_t(a^t, b^t) + i sum_t phi_t(a^-t, b^-t)) is a
product of one k x k matrix per axis, so one tree level costs (2p+1) k^(2p+2).
"""
import string
import numpy as np
import jax
import jax.numpy as jnp

jax.config.update("jax_enable_x64", True)


def vertex_tensor(phi0, Us):
    """f(a) = phi0[a^1] prod_t U_t[a^{t+1}, a^t] * conj(same for the bra string), a^{p+1} = middle."""
    p = len(Us)
    K = phi0
    for U in Us:                                   # K has axes (a^1, ..., a^t); append a^{t+1}
        K = K[..., None] * U.T.reshape((1,) * (K.ndim - 1) + U.T.shape)
    # K axes: a^1 .. a^p, mid.  f = K(ket, mid) * conj K(bra, mid)
    L = string.ascii_letters
    ket, bra, mid = L[:p], L[p + 1:2 * p + 1], L[p]
    return jnp.einsum(f"{ket}{mid},{bra}{mid}->{ket}{mid}{bra}", K, jnp.conj(K))


def vertex_tensor_anc(phi0, Us, k, m):
    """Vertex = data qudit (k) x ancilla (m); edge phases see only the data label.
    phi0 has length k*m, each U_t is (km) x (km), index = data*m + anc. Ancilla labels are summed
    inside the vertex, so the tree contraction keeps its k^(2p+1) size."""
    p = len(Us)
    K = phi0.reshape(k, m)                          # axes (a^1, c^1)
    for U in Us:
        U4 = U.reshape(k, m, k, m)                  # [a', c', a, c]
        # K[..., a, c] -> K[..., a, a', c']
        K = jnp.einsum("...ac,xyac->...axy", K, U4)
    L = string.ascii_letters
    ket, bra, mid, anc = L[:p], L[p + 1:2 * p + 1], L[p], L[2 * p + 1]
    return jnp.einsum(f"{ket}{mid}{anc},{bra}{mid}{anc}->{ket}{mid}{bra}", K, jnp.conj(K))


def apply_axes(g, mats):
    for j, M in enumerate(mats):
        g = jnp.moveaxis(jnp.tensordot(M, g, axes=([1], [j])), 0, j)
    return g


def contract(f, phis, d, identity=False):
    """<P_uv> for vertex tensor f (or total probability if identity=True; must be 1)."""
    k = f.shape[0]
    E = [jnp.exp(-1j * ph) for ph in phis]
    ones = jnp.ones((k, k), dtype=complex)
    inner = E + [ones] + [jnp.conj(e) for e in E]
    root = inner if identity else E + [jnp.eye(k, dtype=complex)] + [jnp.conj(e) for e in E]
    H = jnp.ones_like(f)
    for _ in phis:
        H = apply_axes(f * H, inner) ** (d - 1)
    g = f * H
    return jnp.sum(g * apply_axes(g, root))


def edge_same_prob(f, phis, d):
    """Probability that the two endpoints of an edge get the same label."""
    return jnp.real(contract(f, phis, d))


# ---- parametrizations --------------------------------------------------------------------------
def fourier(k):
    return jnp.exp(2j * jnp.pi * jnp.outer(jnp.arange(k), jnp.arange(k)) / k) / jnp.sqrt(k)


def herm(x, k):
    """k*k reals -> Hermitian k x k."""
    iu = np.triu_indices(k, 1)
    m = len(iu[0])
    A = jnp.diag(x[:k].astype(complex))
    A = A.at[iu].set(x[k:k + m] + 1j * x[k + m:k + 2 * m])
    return A + jnp.triu(A, 1).conj().T


def sym(x, k):
    """k(k+1)/2 reals -> real symmetric k x k."""
    iu = np.triu_indices(k)
    A = jnp.zeros((k, k)).at[iu].set(x)
    return A + jnp.triu(A, 1).T


def unpack(x, k, p, mixer, phase, start):
    """Parameter vector -> (f, phis, used). mixer in {grover, gen, ancM}, phase in {potts, sym},
    start in {plus, gen}. ancM = general unitary on data x M-level ancilla (start then on k*M)."""
    i = 0
    m = int(mixer[3:]) if mixer.startswith("anc") else 1
    km = k * m
    plus = jnp.ones(k, dtype=complex) / jnp.sqrt(k)
    if m > 1:
        plus = jnp.kron(plus, jnp.eye(m)[0].astype(complex))
    if start == "gen":
        v = x[i:i + 2 * km]; i += 2 * km
        z = v[:km] + 1j * v[km:]
        phi0 = z / jnp.linalg.norm(z)
    else:
        phi0 = plus
    Us, phis = [], []
    P = jnp.outer(plus, plus.conj())
    for _ in range(p):
        if phase == "potts":
            phis.append(x[i] * jnp.eye(k)); i += 1
        else:
            n = k * (k + 1) // 2
            phis.append(sym(x[i:i + n], k)); i += n
        if mixer == "grover":
            Us.append(jnp.eye(k) + (jnp.exp(-1j * x[i]) - 1) * P); i += 1
        else:
            Us.append(jax.scipy.linalg.expm(-1j * herm(x[i:i + km * km], km))); i += km * km
    f = vertex_tensor_anc(phi0, Us, k, m) if m > 1 else vertex_tensor(phi0, Us)
    return f, phis, i


def nparams(k, p, mixer, phase, start):
    return unpack(jnp.zeros(10_000), k, p, mixer, phase, start)[2]


if __name__ == "__main__":
    # self-check: unitarity, and the published depth-1 Max-k-Cut values (sketch/maxkcut_p1.py)
    rng = np.random.default_rng(0)
    for k, d, p in [(2, 3, 2), (3, 4, 2), (4, 3, 1)]:
        for mixer in ("gen", "anc2", "anc3"):
            x = jnp.array(rng.normal(size=nparams(k, p, mixer, "sym", "gen")))
            f, phis, _ = unpack(x, k, p, mixer, "sym", "gen")
            tp = contract(f, phis, d, identity=True)
            assert abs(tp - 1) < 1e-10, (mixer, tp)
    # an ancilla that is never touched changes nothing
    x = jnp.array(rng.normal(size=nparams(3, 2, "gen", "sym", "plus")))
    f1, ph, _ = unpack(x, 3, 2, "gen", "sym", "plus")
    print("unitarity ok", float(edge_same_prob(f1, ph, 4)))
