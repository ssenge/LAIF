# Lemma 2 (information of one measurement), Lemma 3 (exact linear model) and Lemma 4 (update) on random instances
import numpy as np
rng = np.random.default_rng(5)
def chart(theta, d):  # psi(theta) = (|0> + v)/sqrt(1+|theta|^2)
    v = np.zeros(d, complex); v[1:] = theta[0::2] + 1j * theta[1::2]; v[0] = 1
    return v / np.linalg.norm(v)
worst = 0
for _ in range(3000):
    d = int(rng.integers(2, 9)); m = 2 * (d - 1)
    th = rng.normal(size=m) * rng.uniform(0, 1.5) / np.sqrt(m)
    phi = rng.normal(size=d) + 1j * rng.normal(size=d); phi /= np.linalg.norm(phi)
    if rng.random() < 0.5:  # actions near the state
        phi = chart(th, d) + rng.normal(size=d) * 10 ** rng.uniform(-4, -1); phi /= np.linalg.norm(phi)
    q = lambda t: abs(np.vdot(phi, chart(t, d))) ** 2
    q0 = q(th); h = 1e-6
    g = np.array([(q(th + h * e) - q(th - h * e)) / (2 * h) for e in np.eye(m)])
    if 1e-9 < q0 < 1 - 1e-9:
        worst = max(worst, g @ g / (q0 * (1 - q0)))
print("max |grad q|^2 / (q (1 - q)) (Lemma 2, at most 4):", worst)
assert worst <= 4 + 1e-4
# exact linear model: q+ - q- = 2 sin(2s) Re<w, conj(alpha) beta>
for _ in range(1000):
    d = int(rng.integers(2, 9)); psi = rng.normal(size=d) + 1j * rng.normal(size=d); psi /= np.linalg.norm(psi)
    c = rng.normal(size=d) + 1j * rng.normal(size=d); c /= np.linalg.norm(c)
    w = rng.normal(size=d) + 1j * rng.normal(size=d); w -= np.vdot(c, w) * c; w /= np.linalg.norm(w)
    s = rng.uniform(0, 1.5); al = np.vdot(c, psi); be = psi - al * c
    qp = abs(np.vdot(np.cos(s) * c + np.sin(s) * w, psi)) ** 2; qm = abs(np.vdot(np.cos(s) * c - np.sin(s) * w, psi)) ** 2
    assert abs(qp - qm - np.sin(2 * s) * 2 * np.real(np.vdot(w, np.conj(al) * be))) < 1e-12
    # D(c', psi) <= |err|^2 for c' ~ c + tau + err with tau = beta/alpha, err tangent
    tau = be / al; err = rng.normal(size=d) + 1j * rng.normal(size=d); err -= np.vdot(c, err) * c; err *= rng.uniform(0, 1)
    y = c + tau + err; D = 1 - abs(np.vdot(y, psi)) ** 2 / np.vdot(y, y).real
    assert D <= np.vdot(err, err).real + 1e-12
print("linear model and update bound: ok")
