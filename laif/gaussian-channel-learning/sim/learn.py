# Sampling check of the learner of Theorem 2 on random one- and two-mode Gaussian channels.
# Heterodyne outcomes of a Gaussian output with mean mu and covariance V are N(mu, (V + I)/2).
# Checks with asserts: the errors stay below the high-probability bounds b_X, b_d, b_Sigma in at least a
# 1 - delta fraction of runs, and the repaired noise matrix always gives a valid channel (with the margin xi0).
import numpy as np
from teleport import rand_channel, Om
rng = np.random.default_rng(11)

def learn(X, Y, d, m, N, eta, xi0, z, y, delta):
    Sig = (X @ X.T + Y + np.eye(2 * m)) / 2
    L = np.linalg.cholesky(Sig)
    draw = lambda mu: mu + rng.normal(size=(N, 2 * m)) @ L.T
    S0 = draw(d)
    d_hat = S0.mean(0)
    cols, pairs = [], [(S0[0::2][: N // 2] - S0[1::2][: N // 2]) / np.sqrt(2)]
    for j in range(2 * m):
        e = np.zeros(2 * m); e[j] = eta
        Sp, Sm = draw(X @ e + d), draw(-X @ e + d)
        cols.append((Sp.mean(0) - Sm.mean(0)) / (2 * eta))
        for T in (Sp, Sm):
            pairs.append((T[0::2][: N // 2] - T[1::2][: N // 2]) / np.sqrt(2))
    X_hat = np.array(cols).T
    P = np.vstack(pairs); n = len(P)
    Sig_hat = P.T @ P / n
    dp = delta / 3
    sig = np.sqrt((z ** 2 + y + 1) / 2)
    bd = sig * (np.sqrt(2 * m) + np.sqrt(2 * np.log(1 / dp))) / np.sqrt(N)
    bX = sig * (2 * m + np.sqrt(2 * np.log(1 / dp))) / (eta * np.sqrt(2 * N))
    ep = np.sqrt(2 * m / n) + np.sqrt(2 * np.log(2 / dp) / n)
    bS = sig ** 2 * (2 * ep + ep ** 2)
    Y_hat = 2 * Sig_hat - np.eye(2 * m) - X_hat @ X_hat.T
    lam = 2 * bS + (2 + xi0) * (2 * z + bX) * bX
    Y_rep = Y_hat + lam * np.eye(2 * m)
    ok = (np.linalg.norm(d_hat - d) <= bd, np.linalg.norm(X_hat - X, 2) <= bX, np.linalg.norm(Sig_hat - Sig, 2) <= bS)
    return X_hat, Y_rep, d_hat, ok

delta = 0.1
for m, xi0 in ((1, 0.0), (1, 0.3), (2, 0.0), (2, 0.2)):
    fails, invalid = 0, 0
    runs = 300
    for t in range(runs):
        X, Y = rand_channel(m, margin=xi0)
        z = np.linalg.norm(X, 2); y = np.linalg.norm(Y, 2)
        d = rng.normal(size=2 * m)
        Xh, Yh, dh, ok = learn(X, Y, d, m, N=400, eta=2.0, xi0=xi0, z=z, y=y, delta=delta)
        fails += not all(ok)
        if all(ok):   # the repair is guaranteed on the success event
            M = Yh - xi0 * Xh @ Xh.T + 1j * (Om(m) - Xh @ Om(m) @ Xh.T)
            invalid += np.linalg.eigvalsh(M).min() < -1e-9
    assert fails <= delta * runs and invalid == 0, (m, fails, invalid)
    print(f"m = {m}, margin {xi0}: error bounds violated in {fails}/{runs} runs (allowed {delta * runs:.0f}); repaired channels valid in all successful runs")
