"""Sparse odd threshold rules z_u = sign(g_u - T(n1 <= n2 <= n3)), T built from a few odd features (T(-n3,-n2,-n1) =
-T(n1,n2,n3), so the rule commutes with a global sign flip). Trained smoothed, valued hard."""
import sys, numpy as np, jax, jax.numpy as jnp
FEAT = {"n2": lambda a, b, c: b, "n1+n3": lambda a, b, c: a + c, "n2^2(n1+n3)": lambda a, b, c: b * b * (a + c),
        "n1n2n3": lambda a, b, c: a * b * c, "n2^3": lambda a, b, c: b ** 3, "n1^2-n3^2": lambda a, b, c: a * a - c * c,
        "n2(n1-n3)": lambda a, b, c: b * (a - c), "n2(n1^2+n3^2)": lambda a, b, c: b * (a * a + c * c),
        "n1^3+n3^3": lambda a, b, c: a ** 3 + c ** 3}
names = sys.argv[1].split(",")
def T(P, nb):
    s = jnp.sort(nb, -1); a, b, c = s[..., 0], s[..., 1], s[..., 2]
    return sum(P[k] * FEAT[f](a, b, c) for k, f in enumerate(names))
def at2(q): q1, q2, q3 = q[..., 0], q[..., 1], q[..., 2]; return q1*q2 + q1*q3 + q2*q3 - 2*q1*q2*q3
def val(P, k, n, s):
    a, b, c = jax.random.split(k, 3)
    gv = jax.random.normal(a, (n,)); gn = jax.random.normal(b, (n, 3)); gc = jax.random.normal(c, (n, 3, 2))
    pv = (1 + jnp.tanh(s * (gv - T(P, gn)))) / 2
    pw = (1 + jnp.tanh(s * (gn - T(P, jnp.concatenate([gv[:, None, None].repeat(3, 1), gc], -1))))) / 2
    return jnp.mean(pv * at2(1 - pw) + (1 - pv) * at2(pw))
if __name__ == "__main__":
    g = jax.jit(jax.value_and_grad(lambda P, k, s: -val(P, k, 40000, s)))
    P = jnp.zeros(len(names)).at[0].set(1.0); m = jnp.zeros_like(P); v = jnp.zeros_like(P)
    for i in range(1, 5001):
        l, gr = g(P, jax.random.PRNGKey(i), 2.0 + 28.0 * i / 5000)
        m = 0.9 * m + 0.1 * gr; v = 0.999 * v + 0.001 * gr * gr
        P = P - 0.003 * (m / (1 - 0.9 ** i)) / (jnp.sqrt(v / (1 - 0.999 ** i)) + 1e-8)
    print(dict(zip(names, np.round(np.array(P), 3))),
          "hard", round(np.mean([float(val(P, jax.random.PRNGKey(10**7 + j), 2_000_000, 1e7)) for j in range(4)]), 4), flush=True)
