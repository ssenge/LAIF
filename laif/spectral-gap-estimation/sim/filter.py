"""Lemma 1: an even polynomial filter with degree 2D, D = ceil(2 sqrt(ln(4/a) ln(2/a)) / w), w = theta_b - theta_p >= t sqrt(2 Delta).
Coefficients a_k = 2 sin(2 k theta_c) / (pi k) * exp(-2 k^2 sigma^2), sigma = w / sqrt(8 ln(2/a))."""
import numpy as np
from numpy.polynomial import chebyshev as C


def filt(delta, t, a):
    tp, tb = np.arccos(1 - delta * (1 - t)), np.arccos(1 - delta * (1 + t))
    w, tc = tb - tp, (tb + tp) / 2
    sig = w / np.sqrt(8 * np.log(2 / a))
    D = int(np.ceil(2 * np.sqrt(np.log(4 / a) * np.log(2 / a)) / w))
    k = np.arange(1, D + 1)
    c = np.zeros(2 * D + 1)
    c[0] = 2 * tc / np.pi
    c[2 * k] = 2 * np.sin(2 * k * tc) / (np.pi * k) * np.exp(-2 * k ** 2 * sig ** 2)
    return c / (1 + a / 4), D, w


def check(delta, t, a):
    c, D, w = filt(delta, t, a)
    assert w >= t * np.sqrt(2 * delta) * (1 - 1e-12)
    assert 2 * D <= 2 * np.sqrt(2) * np.log(4 / a) / (t * np.sqrt(delta)) + 2
    # values on the grid theta_j = pi j / M by a real FFT (M >= 16 D), plus exact values at the band edges
    M = 1 << int(np.ceil(np.log2(max(16 * len(c), 4096))))
    spec = np.zeros(M + 1)
    spec[: len(c)] = c
    spec[0] *= 2
    f = np.fft.irfft(spec, 2 * M)[: M + 1] * M      # f(theta_j) = sum_n c_n cos(n theta_j)
    th = np.pi * np.arange(M + 1) / M
    edges = np.array([np.arccos(1 - delta * (1 - t)), np.arccos(1 - delta * (1 + t))])
    th = np.concatenate([th, edges, np.pi - edges])
    f = np.concatenate([f, C.chebval(np.cos(th[M + 1:]), c)])
    x = np.cos(th)
    blk = np.abs(x) <= 1 - delta * (1 + t)
    pas = np.abs(x) >= 1 - delta * (1 - t)
    assert np.all(np.abs(f[blk]) <= a), np.abs(f[blk]).max() / a
    assert np.all(f[pas] >= 1 - a), f[pas].min()
    return 2 * D, np.abs(f[blk]).max() / a, f[pas].min()


def main():
    print("delta     t      alpha     degree  deg*t*sqrt(delta)/ln(4/alpha)  max|f|_block/alpha  min f_pass")
    for delta in [1e-1, 1e-2, 1e-3, 1e-4]:
        for t in [0.9, 0.5, 0.1, 0.03]:
            for a in [1e-2, 1e-4]:
                d, rb, mp = check(delta, t, a)
                print(f"{delta:7.0e} {t:5.2f} {a:8.0e} {d:9d} {d * t * np.sqrt(delta) / np.log(4 / a):10.3f} {rb:22.3f} {mp:12.6f}")
    print("filter: all asserts passed")


if __name__ == "__main__":
    main()
