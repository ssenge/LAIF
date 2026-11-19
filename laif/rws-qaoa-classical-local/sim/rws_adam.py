"""The warm start of arXiv:2603.10191, Eq. (11), by Adam on theta (p_i = sin^2(theta_i / 2), m_i = cos theta_i), maximizing
L(theta) = sum_E (1 - m_i m_j)/2 + lam sum_i (1 - m_i^2)   (= E[cut] + 4 lam sum p (1 - p)),
best L of M starts with theta ~ U[0, span). Self-check: python -I rws_adam.py test"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from rws_local import graph, rws_ca

def L_of(nb, m, lam):                                   # m: (M, N); each edge counted twice in nb
    return 0.25 * (1 - m[:, :, None] * m[:, nb]).sum((1, 2)) + lam * (1 - m * m).sum(1)

def adam(nb, lam, M, lr, steps, span, seed, b1=0.9, b2=0.999, eps=1e-8):
    """Best-of-M Adam ascent; steps is an int or a list of checkpoints (one trajectory, best start taken at each)."""
    cps = [steps] if np.isscalar(steps) else sorted(steps); res = []
    rng = np.random.default_rng(seed); th = rng.uniform(0, span, (M, nb.shape[0]))
    mo = np.zeros_like(th); v = np.zeros_like(th)
    for t in range(1, cps[-1] + 1):
        c, s = np.cos(th), np.sin(th)
        g = 0.5 * s * c[:, nb].sum(2) + lam * np.sin(2 * th)        # dL/dtheta, ascent
        mo = b1 * mo + (1 - b1) * g; v = b2 * v + (1 - b2) * g * g
        th += lr * (mo / (1 - b1 ** t)) / (np.sqrt(v / (1 - b2 ** t)) + eps)
        if t in cps: m = np.cos(th); k = np.argmax(L_of(nb, m, lam)); res.append(m[k].copy())
    return res[0] if np.isscalar(steps) else res

if __name__ == "__main__":
    if sys.argv[1] == "test":                           # gradient check and agreement with coordinate ascent
        G, nb = graph(30, 0); rng = np.random.default_rng(1); th = rng.uniform(0, 6, (1, 30)); lam = 0.6
        g = 0.5 * np.sin(th) * np.cos(th)[:, nb].sum(2) + lam * np.sin(2 * th); h = 1e-6
        for i in range(5):
            e = np.zeros_like(th); e[0, i] = h
            fd = (L_of(nb, np.cos(th + e), lam) - L_of(nb, np.cos(th - e), lam))[0] / (2 * h)
            assert abs(fd - g[0, i]) < 1e-6, (fd, g[0, i])
        m_ca, f_ca = rws_ca(nb, lam, 20, 0); m_ad = adam(nb, lam, 20, 1e-2, 5000, 2 * np.pi, 0)
        f_ad = L_of(nb, m_ad[None], lam)[0]
        assert abs(L_of(nb, m_ca[None], lam)[0] - f_ca) < 1e-9 and f_ad <= f_ca + 1e-9, (f_ad, f_ca)
        print("rws_adam self-checks passed", f_ca, f_ad); sys.exit()
