"""The shift identities at full size, with AES and the real POLYVAL (n = 128).

HCTR2 follows its specification (ePrint 2021/1441, Section 3) and is checked against the published test vectors when
their file is given. CHCTR is HCTR2 under K2 applied to HCTR2 under K1 with the same tweak. HCTR++ follows Figure 4 of
ePrint 2026/383 with POLYVAL over GF(2^256), as fixed in the public reference code. For random keys, tweaks and inputs x,
and for elements s of the subgroups S, the script checks C(x xor s) = C(x) xor s and D(y xor s) = D(y) xor s,
the recovery of the hash keys from s, and the shift at longer messages and partial last blocks.
Run with python fullsize.py [HCTR2_AES256.json]."""
import json
import os
import sys
from cryptography.hazmat.primitives.ciphers import Cipher, algorithms, modes

# ------------------------------------------------------------------ fields, little-endian, bit i <-> x^i

R128 = (1 << 128) | (1 << 127) | (1 << 126) | (1 << 121) | 1
R256 = (1 << 256) | (1 << 254) | (1 << 251) | (1 << 246) | 1


def mul(a, b, R):
    k = R.bit_length() - 1
    r = 0
    while b:
        if b & 1:
            r ^= a
        b >>= 1
        a <<= 1
        if a >> k:
            a ^= R
    return r


def power(a, e, R):
    r = 1
    while e:
        if e & 1:
            r = mul(r, a, R)
        a = mul(a, a, R)
        e >>= 1
    return r


def inv(a, R):
    k = R.bit_length() - 1
    return power(a, (1 << k) - 2, R)


XI128 = inv(power(2, 128, R128), R128)          # x^-128
XI256 = inv(power(2, 256, R256), R256)          # x^-256
assert XI128 == (1 << 127) | (1 << 124) | (1 << 121) | (1 << 114) | 1


def I(b):
    return int.from_bytes(b, "little")


def B(x, n=16):
    return x.to_bytes(n, "little")


def xor(a, b):
    return bytes(u ^ v for u, v in zip(a, b))


def aes(key):
    c = Cipher(algorithms.AES(key), modes.ECB())
    return (lambda b: c.encryptor().update(b)), (lambda b: c.decryptor().update(b))


# ------------------------------------------------------------------ HCTR2

def polyval(h, data, R, XI, w):
    hx = mul(I(h), XI, R)
    acc = 0
    for i in range(0, len(data), w):
        acc = mul(acc ^ I(data[i:i + w]), hx, R)
    return B(acc, w)


def pad(x, w):
    return x + b"\0" * (-len(x) % w)


def H(h, T, M, w=16, R=R128, XI=XI128):
    if len(M) % w == 0:
        return polyval(h, B(16 * len(T) + 2, w) + pad(T, w) + M, R, XI, w)
    return polyval(h, B(16 * len(T) + 3, w) + pad(T, w) + pad(M + b"\1", w), R, XI, w)


class HCTR2:
    def __init__(self, key):
        self.E, self.D = aes(key)
        self.h, self.L = self.E(B(0)), self.E(B(1))

    def xctr(self, S, m):
        return b"".join(self.E(xor(S, B(i))) for i in range(1, -(-m // 16) + 1))[:m]

    def enc(self, T, P):
        M, N = P[:16], P[16:]
        MM = xor(M, H(self.h, T, N))
        UU = self.E(MM)
        S = xor(xor(MM, UU), self.L)
        V = xor(N, self.xctr(S, len(N)))
        return xor(UU, H(self.h, T, V)) + V

    def dec(self, T, C):
        U, V = C[:16], C[16:]
        UU = xor(U, H(self.h, T, V))
        MM = self.D(UU)
        S = xor(xor(MM, UU), self.L)
        N = xor(V, self.xctr(S, len(V)))
        return xor(MM, H(self.h, T, N)) + N


class CHCTR:
    def __init__(self, key):
        self.a, self.b = HCTR2(key[:32]), HCTR2(key[32:])

    def enc(self, T, P):
        return self.b.enc(T, self.a.enc(T, P))

    def dec(self, T, C):
        return self.a.dec(T, self.b.dec(T, C))


# ------------------------------------------------------------------ HCTR++

def H2(h, T, M):
    return H(h, T, M, 32, R256, XI256)


class HCTRPP:
    def __init__(self, key):
        self.E, _ = aes(key)
        blk = [self.E(B(i)) for i in range(1, 7)]
        self.h1, self.h2, self.kb = blk[0] + blk[1], blk[2] + blk[3], blk[4] + blk[5]

    def rekey(self, r, x, inverse=False):
        uv = H2(self.kb, b"", r)
        u, v = uv[:16], uv[16:]
        E, D = aes(u)
        return xor((D if inverse else E)(xor(x, v)), v)

    def crypt(self, T, data, decrypt=False):
        ha, hb = (self.h2, self.h1) if decrypt else (self.h1, self.h2)
        h12 = xor(self.h1, self.h2)
        b1, rest = data[:16], data[16:]
        x1 = H2(ha, T, rest)
        cc = self.rekey(x1[16:], xor(b1, x1[:16]))
        x = H2(h12, T, cc)
        r, j = x[:16], x[16:]
        m = -(-len(rest) // 16)
        ks = b"".join(self.rekey(xor(r, B(i)), xor(j, B(i))) for i in range(1, m + 1))
        out = xor(rest, ks)
        x2 = H2(hb, T, out)
        return xor(self.rekey(x2[16:], cc, inverse=True), x2[:16]) + out

    def enc(self, T, P):
        return self.crypt(T, P)

    def dec(self, T, C):
        return self.crypt(T, C, True)


# ------------------------------------------------------------------ subgroups

def hx(h, R=R128, XI=XI128):
    """The multiplier h x^-n by which POLYVAL multiplies."""
    return mul(I(h), XI, R)


def s_hctr2(h, d):
    """(lambda(d), d) for N = d of l blocks: lambda(d) = sum_i d_i hx^(l-i)."""
    w, l = hx(h), len(d) // 16
    a = 0
    for i in range(l):
        a ^= mul(I(d[16 * i:16 * i + 16]), power(w, l - i, R128), R128)
    return B(a) + d


def s_chctr(h1, h2, d1):
    """(d1 p, d1, d1 s) with s = w1 + w2, p = w1 w2."""
    w1, w2 = hx(h1), hx(h2)
    x = I(d1)
    return B(mul(x, mul(w1, w2, R128), R128)) + d1 + B(mul(x, w1 ^ w2, R128))


def s_hctrpp(h1, h2, z):
    """(a, d1, d1 s) in GF(2^256) with d1 p = a (upper half 0) for a = z."""
    w1, w2 = hx(h1, R256, XI256), hx(h2, R256, XI256)
    p, s = mul(w1, w2, R256), w1 ^ w2
    d1 = mul(I(z), inv(p, R256), R256)
    return z + B(d1, 32) + B(mul(d1, s, R256), 32)


def s_hctrpp1(h, z):
    """(a, d) with d hx = a (upper half 0), the one-block rest."""
    d = mul(I(z), inv(hx(h, R256, XI256), R256), R256)
    return z + B(d, 32)


def roots(s, p, R):
    """The two roots of X^2 + sX + p: X = sY with Y^2 + Y = p/s^2, a GF(2)-linear equation in Y."""
    k = R.bit_length() - 1
    c = mul(p, inv(mul(s, s, R), R), R)
    cols = [mul(1 << i, 1 << i, R) ^ (1 << i) for i in range(k)]
    rows, piv = [], []
    for i, col in enumerate(cols):
        v, comb = col, 1 << i
        for (pv, pc), bit in zip(rows, piv):
            if v >> bit & 1:
                v ^= pv
                comb ^= pc
        if v:
            rows.append((v, comb))
            piv.append(v.bit_length() - 1)
    v, comb = c, 0
    for (pv, pc), bit in zip(rows, piv):
        if v >> bit & 1:
            v ^= pv
            comb ^= pc
    assert v == 0, "no root"
    y = comb
    return sorted((mul(s, y, R), mul(s, y ^ 1, R)))


def rnd(n):
    return os.urandom(n)


def main():
    ok = True
    if len(sys.argv) > 1:
        vec = [v for v in json.load(open(sys.argv[1])) if v["cipher"]["cipher"] == "HCTR2"]
        good = 0
        for v in vec:
            c = HCTR2(bytes.fromhex(v["input"]["key_hex"]))
            T, P, C = (bytes.fromhex(v["input"]["tweak_hex"]), bytes.fromhex(v["plaintext_hex"]),
                       bytes.fromhex(v["ciphertext_hex"]))
            good += c.enc(T, P) == C and c.dec(T, C) == P
        print(f"HCTR2 test vectors: {good}/{len(vec)}")
        ok &= good == len(vec)
    trials = 20
    for name, mk, klen, size in (("HCTR2", HCTR2, 32, 16 + 16), ("HCTR2 3 blocks", HCTR2, 32, 16 + 48),
                                 ("CHCTR", CHCTR, 64, 16 + 32), ("HCTR++", HCTRPP, 16, 16 + 64)):
        good = 0
        for _ in range(trials):
            c = mk(rnd(klen))
            T = rnd(16)
            if name.startswith("HCTR2"):
                s = s_hctr2(c.h, rnd(size - 16))
            elif name == "CHCTR":
                s = s_chctr(c.a.h, c.b.h, rnd(16))
            else:
                s = s_hctrpp(c.h1, c.h2, rnd(16) + b"\0" * 16)
                s = s[:16] + s[32:]                  # first block a; the trailing half of the hash shift is 0
            x, y = rnd(size), rnd(size)
            good += (c.enc(T, xor(x, s)) == xor(c.enc(T, x), s) and c.dec(T, xor(y, s)) == xor(c.dec(T, y), s)
                     and c.dec(T, c.enc(T, x)) == x)
        print(f"{name:15s} C(x+s) = C(x)+s and D(y+s) = D(y)+s: {good}/{trials}")
        ok &= good == trials
    # HCTR++ with a one-block rest: the rest of C xor x is invariant under (a, d) with d hx1 = a; for decryption with h2
    good = 0
    for _ in range(trials):
        c = HCTRPP(rnd(16))
        T = rnd(16)
        z = rnd(16) + b"\0" * 16
        s1, s2 = s_hctrpp1(c.h1, z), s_hctrpp1(c.h2, z)
        s1, s2 = s1[:16] + s1[32:], s2[:16] + s2[32:]
        x = rnd(48)
        good += (xor(c.enc(T, xor(x, s1)), xor(x, s1))[16:] == xor(c.enc(T, x), x)[16:]
                 and xor(c.dec(T, xor(x, s2)), xor(x, s2))[16:] == xor(c.dec(T, x), x)[16:])
    print(f"HCTR++ 1 block  rest of g invariant (enc with h1, dec with h2): {good}/{trials}")
    ok &= good == trials
    # key recovery from one element of S
    good = 0
    for _ in range(trials):
        c = HCTR2(rnd(32))
        s = s_hctr2(c.h, rnd(16))
        w = mul(I(s[:16]), inv(I(s[16:]), R128), R128)
        e = CHCTR(rnd(64))
        t = s_chctr(e.a.h, e.b.h, rnd(16))
        i = inv(I(t[16:32]), R128)
        rr = roots(mul(I(t[32:]), i, R128), mul(I(t[:16]), i, R128), R128)
        good += w == hx(c.h) and rr == sorted((hx(e.a.h), hx(e.b.h)))
    print(f"key recovery from one element of S (HCTR2, CHCTR): {good}/{trials}")
    ok &= good == trials
    # HCTR++: w1 from S_1 on encryption and w2 on decryption, as in the attack
    good = 0
    for _ in range(trials):
        c = HCTRPP(rnd(16))
        z = rnd(16) + b"\0" * 16
        for h in (c.h1, c.h2):
            t = s_hctrpp1(h, z)
            good += mul(I(t[:32]), inv(I(t[32:]), R256), R256) == hx(h, R256, XI256)
    print(f"key recovery from one element of S_1 (HCTR++, enc and dec): {good}/{2 * trials}")
    ok &= good == 2 * trials
    # Theorem 2 at other lengths: HCTR2 with a partial last block; CHCTR and HCTR++ with shifts on the last two blocks
    good = 0
    for _ in range(trials):
        c = HCTR2(rnd(32))
        T, rest = rnd(16), 16 + int.from_bytes(rnd(1), "little") % 40 + 1
        d = rnd(rest)
        dp = pad(d, 16)                              # the 0x01 padding bit is constant and cancels
        s = s_hctr2(c.h, dp)[:16] + d
        x = rnd(16 + rest)
        good += c.enc(T, xor(x, s)) == xor(c.enc(T, x), s)
        e = CHCTR(rnd(64))
        l = 2 + int.from_bytes(rnd(1), "little") % 3
        t = s_chctr(e.a.h, e.b.h, rnd(16))
        s = t[:16] + b"\0" * (16 * (l - 2)) + t[16:]
        x = rnd(16 + 16 * l)
        good += e.enc(T, xor(x, s)) == xor(e.enc(T, x), s)
        p = HCTRPP(rnd(16))
        l = 2 + int.from_bytes(rnd(1), "little") % 2
        t = s_hctrpp(p.h1, p.h2, rnd(16) + b"\0" * 16)
        s = t[:16] + b"\0" * (32 * (l - 2)) + t[32:]
        x = rnd(16 + 32 * l)
        good += p.enc(T, xor(x, s)) == xor(p.enc(T, x), s)
    print(f"Theorem 2 at other lengths (HCTR2 partial blocks, CHCTR and HCTR++ longer rests): {good}/{3 * trials}")
    ok &= good == 3 * trials
    print("all checks passed" if ok else "SOME CHECK FAILED")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
