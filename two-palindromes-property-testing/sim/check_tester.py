"""Quantum tester for the concatenation of two even palindromes, simulated exactly.
x in L_REV iff x_i = x_{c-i} (mod n) for some odd c in [1, n-3] (c = 2|u| - 1).
One query: (1/sqrt(2n)) sum_{i,b} |i,b>|f(i,b)>, f(i,0) = x_i, f(i,1) = x_{-i}. Measure the value, apply the QFT of Z_n
to i, measure k, then measure the qubit b in the X or the Y basis. Each sample gives an unbiased estimate Z of
omega^{-kc} on yes-instances. score(c') = mean Re(omega^{k c'} Z), an estimate of the autocorrelation R(c' - c).
Output the valid c' of maximal score, then check x_i = x_{c'-i} on random i classically."""
import numpy as np, sys

def outcome_tables(x, sig, y=None):
    n = len(x); idx = np.arange(n)
    if y is None: y = x[(-idx) % n]                            # reflection: f(i, 1) = x_{-i}; else f(i, 1) = y_i
    probs, states = [], []
    for v in range(sig):
        a0 = (x == v).astype(complex); a1 = (y == v).astype(complex)
        F0 = np.fft.fft(a0); F1 = np.fft.fft(a1)              # sum_i omega^{-ki} a(i), sign convention irrelevant below
        p = (np.abs(F0) ** 2 + np.abs(F1) ** 2) / (2 * n * n)  # Pr[v, k]
        probs.append(p); states.append((F0, F1))
    return np.array(probs), states

def R(x, d):
    return np.mean(x == np.roll(x, -d))

def basis_means(a, b):
    """Qubit a|0> + b|1>: probability of +1 in the X and in the Y basis, and E[Z] for Z = 2s (X) or 2is (Y),
    basis uniform."""
    pX = abs(a + b) ** 2 / 2; pY = abs(a - 1j * b) ** 2 / 2
    return pX, pY, (2 * pX - 1) + 1j * (2 * pY - 1)

def samples(x, sig, rng, T, y=None):
    n = len(x)
    P, S = outcome_tables(x, sig, y)
    flat = P.ravel() / P.sum()
    draws = rng.choice(flat.size, size=T, p=flat)
    ks, zs = np.empty(T), np.empty(T, complex)
    for t, dv in enumerate(draws):
        v, k = divmod(dv, n)
        a, b = S[v][0][k], S[v][1][k]
        nrm = np.sqrt(abs(a) ** 2 + abs(b) ** 2); pX, pY, _ = basis_means(a / nrm, b / nrm)
        if rng.random() < 0.5: zs[t] = 2 if rng.random() < pX else -2
        else: zs[t] = 2j if rng.random() < pY else -2j
        ks[t] = k
    return ks, zs

def best(ks, zs, cand, n):
    # with fft's sign the qubit is (1, omega^{+kc}) on yes-instances: E[Z] = omega^{kc}
    score = (np.exp(-2j * np.pi * np.outer(cand, ks) / n) * zs).real.mean(axis=1)
    return cand[np.argmax(score)]

def tester(x, sig, eps, rng, T):
    n = len(x)
    if n % 2 or n < 4: return False, None                       # no word of L_REV has this length
    c = best(*samples(x, sig, rng, T), np.arange(1, n - 2, 2), n)
    m = int(np.ceil(32 / eps)); i = rng.integers(0, n, m)
    return np.sum(x[i] != x[(c - i) % n]) < 1.5 * eps * m, c

def shift_tester(x, y, sig, eps, rng):
    n = len(x); T = int(np.ceil(116 * np.log(6 * n) / (3 * eps)))
    s = best(*samples(x, sig, rng, T, y), np.arange(n), n)
    m = int(np.ceil(64 / eps)); i = rng.integers(0, n, m)
    return np.sum(y[i] != x[(i + s) % n]) < 0.75 * eps * m, s

def yes_instance(n, sig, rng, kind):
    c = 2 * rng.integers(1, n // 2) - 1
    if c > n - 3: c = 1
    if kind == "random": x = rng.integers(0, sig, n)
    elif kind == "sparse": x = (rng.random(n) < 0.03).astype(int)
    else: p = int(rng.integers(2, 9)); x = np.tile(rng.integers(0, sig, p), n // p + 1)[:n]; x[rng.integers(0, n, 3)] = 1
    for i in range(n):                                          # enforce x_i = x_{c-i}
        x[(c - i) % n] = x[i] if i <= (c - i) % n else x[(c - i) % n]
    assert all(x[i] == x[(c - i) % n] for i in range(n))
    return x, c

def dist_to_L(x):
    n = len(x)
    return min(sum(x[i] != x[(c - i) % n] for i in range(n)) // 2 for c in range(1, n - 2, 2))

if __name__ == "__main__":
    rng = np.random.default_rng(5)
    # autocorrelation identity: sum_{v,k} Pr[v,k] E[Z] omega^{-k c'} = R(c' - c), checked exactly
    for _ in range(30):
        n = int(rng.integers(8, 200)) * 2; sig = int(rng.integers(2, 4))
        x, c = yes_instance(n, sig, rng, rng.choice(["random", "sparse", "periodic"]))
        P, S = outcome_tables(x, sig)
        for cp in rng.integers(0, n, 5):
            tot = 0
            for v in range(sig):
                F0, F1 = S[v]; k = np.arange(n); den = np.sqrt(np.abs(F0) ** 2 + np.abs(F1) ** 2); den[den == 0] = 1
                EZ = basis_means(F0 / den, F1 / den)[2]
                assert np.allclose(EZ[P[v] > 1e-12], np.exp(2j * np.pi * k * c / n)[P[v] > 1e-12])
                tot += (P[v] * EZ * np.exp(-2j * np.pi * k * cp / n)).sum()
            assert abs(tot - R(x, (cp - c) % n)) < 1e-9, (tot, R(x, (cp - c) % n))
            sec = sum((P[v] * np.abs(1 - np.exp(2j * np.pi * np.arange(n) * (cp - c) / n)) ** 2).sum() for v in range(sig))
            assert abs(sec - 2 * (1 - R(x, (cp - c) % n))) < 1e-9          # second moment of the Bernstein step
    print("identity: score expectation equals the autocorrelation R(c' - c); qubit phase exact on yes-instances")
    eps = 0.05; fails = {"yes": 0, "no": 0}; runs = {"yes": 0, "no": 0}
    for trial in range(120):
        n = int(rng.choice([64, 256, 1024, 4096] if trial % 2 == 0 else [64, 256, 1024])); sig = 2
        T = int(np.ceil(58 * np.log(3 * n) / (3 * eps)))   # the sample count of the theorem
        if trial % 2 == 0:
            x, c = yes_instance(n, sig, rng, ["random", "sparse", "periodic"][trial % 3])
            ok, _ = tester(x, sig, eps, rng, T); runs["yes"] += 1; fails["yes"] += (not ok)
        else:
            x = rng.integers(0, sig, n)
            if trial % 4 == 3:                                  # near-symmetric: a yes-instance with 3 eps n flips
                x, _ = yes_instance(n, sig, rng, "random"); x[rng.choice(n, int(3 * eps * n), replace=False)] ^= 1
            if n <= 1024: assert dist_to_L(x) >= eps * n
            else: continue
            ok, _ = tester(x, sig, eps, rng, T); runs["no"] += 1; fails["no"] += ok
    print("tester, eps", eps, "errors:", fails, "of", runs)
    # cyclic shifts: y_i = x_{i+s}; the qubit phase is omega^{ks} and the score expectation is R(s' - s)
    errs = 0
    for _ in range(40):
        n = int(rng.integers(8, 300)); sig = int(rng.integers(2, 4))
        x = rng.integers(0, sig, n) if rng.random() < 0.5 else (rng.random(n) < 0.05).astype(int)
        sh = int(rng.integers(0, n)); y = np.roll(x, -sh)
        P, S = outcome_tables(x, sig, y); k = np.arange(n)
        for sp in rng.integers(0, n, 5):
            tot = 0
            for v in range(sig):
                F0, F1 = S[v]; den = np.sqrt(np.abs(F0) ** 2 + np.abs(F1) ** 2); den[den == 0] = 1
                EZ = basis_means(F0 / den, F1 / den)[2]
                assert np.allclose(EZ[P[v] > 1e-12], np.exp(2j * np.pi * k * sh / n)[P[v] > 1e-12])
                tot += (P[v] * EZ * np.exp(-2j * np.pi * k * sp / n)).sum()
            assert abs(tot - R(x, (sp - sh) % n)) < 1e-9
    print("cyclic shifts: qubit phase exact and score expectation equals R(s' - s) on 40 instances")
    # a second axis with mismatch rate just above eps: x symmetric about c and c2, then pairs {i, c - i} flipped
    acc = runs2 = 0; rates = []
    for _ in range(40):
        n = int(rng.choice([128, 512])); c = 2 * int(rng.integers(1, n // 4)) - 1; c2 = c + 2 * int(rng.integers(1, 4))
        g = c2 - c; x = np.zeros(n, int)
        base = rng.integers(0, 2, n)
        for i in range(n):                                      # symmetric about c and c2: x_i = x_{c-i} = x_{i+c2-c}
            x[i] = base[min(i % np.gcd(g, n), (c - i) % np.gcd(g, n))]
        assert all(x[i] == x[(c - i) % n] for i in range(n)) and all(x[i] == x[(c2 - i) % n] for i in range(n))
        for i in rng.choice(n, int(0.6 * eps * n), replace=False):
            x[i] ^= 1; x[(c - i) % n] = x[i]
        assert all(x[i] == x[(c - i) % n] for i in range(n))
        r2 = np.mean(x != x[(c2 - np.arange(n)) % n]); rates.append(r2)
        runs2 += 1; acc += tester(x, 2, eps, rng, int(np.ceil(58 * np.log(3 * n) / (3 * eps))))[0]
    print("second axis: accepted", acc, "of", runs2, "yes-instances; mismatch rate of the second axis from",
          round(min(rates), 3), "to", round(max(rates), 3), "(eps =", eps, ")")
    assert acc >= 0.8 * runs2
    ok_yes = ok_no = 0
    for t in range(40):
        n = int(rng.choice([64, 256])); x = rng.integers(0, 2, n); sh = int(rng.integers(0, n))
        if t % 2 == 0:
            ok_yes += shift_tester(x, np.roll(x, -sh), 2, eps, rng)[0]
        else:
            y = rng.integers(0, 2, n)
            assert min(np.sum(y != np.roll(x, -s2)) for s2 in range(n)) >= eps * n
            ok_no += not shift_tester(x, y, 2, eps, rng)[0]
    print("cyclic shift tester: correct on", ok_yes, "of 20 yes and", ok_no, "of 20 no")
    assert ok_yes >= 17 and ok_no >= 17
