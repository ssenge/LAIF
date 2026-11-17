# Population SIGReg (characteristic-function statistic of each slice, weight exp(-t^2/2), integral over R) for Gaussian embeddings N(0, M):
# each slice a^T z ~ N(0, s2) with s2 = a^T M a, a uniform on the sphere.
import numpy as np
rng = np.random.default_rng(0)
s2pi = np.sqrt(2*np.pi)
def D(s2):  # int (e^{-s2 t^2/2} - e^{-t^2/2})^2 e^{-t^2/2} dt
    return s2pi*(1/np.sqrt(2*s2+1) - 2/np.sqrt(s2+2) + 1/np.sqrt(3))
h = 1e-4; D2 = (D(1+h)-2*D(1)+D(1-h))/h**2
assert abs(D(1.0)) < 1e-12
def sigreg(eigs, nslice=20000):
    K = len(eigs); a = rng.standard_normal((nslice, K)); a /= np.linalg.norm(a, axis=1, keepdims=True)
    return D((a**2) @ eigs).mean()
print("D''(1) =", D2)
print(f"{'K':>6} {'rank K/2':>12} {'pred 2nd order':>15} {'rank K/8':>12} {'pred':>12} {'scale 0.5 iso':>14}")
for K in [16, 64, 256, 1024, 4096]:
    e1 = np.r_[np.full(K//2, 2.0), np.zeros(K - K//2)]
    e2 = np.r_[np.full(K//8, 8.0), np.zeros(K - K//8)]
    p = lambda e: D2/2 * 2*np.var(e)/(K+2)
    v1, v2 = sigreg(e1), sigreg(e2)
    print(f"{K:>6} {v1:12.3e} {p(e1):15.3e} {v2:12.3e} {p(e2):12.3e} {D(0.5):14.3e}")
    if K >= 256: assert abs(v1/p(e1) - 1) < 0.1
