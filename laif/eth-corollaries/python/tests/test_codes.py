import random
from itertools import product

from ethcor.cnf import count_sized
from ethcor.codes import brute_num_log, codeCNF, cssF, distance, in_ker, num_log, pats

STEANE = [[3, 4, 5, 6], [1, 2, 5, 6], [0, 2, 4, 6]]  # the Hamming [7,4,3] checks; H_X = H_Z
SHOR_Z = [[0, 1], [1, 2], [3, 4], [4, 5], [6, 7], [7, 8]]
SHOR_X = [[0, 1, 2, 3, 4, 5], [3, 4, 5, 6, 7, 8]]
CODE_422 = [[0, 1, 2, 3]]  # [[4,2,2]]: H_X = H_Z = XXXX / ZZZZ


def random_code(rng: random.Random, n: int, w: int) -> tuple[list[list[int]], list[list[int]]]:
    """Random checks; H1 ⊆ (rowspace H2)^⊥ is not required by the counts."""
    def checks():
        return [rng.sample(range(n), rng.randint(1, min(w, n))) for _ in range(rng.randint(0, n))]
    return checks(), checks()


def test_pats():
    """`Code.pats w`: every Bool list of length at most w, once."""
    for w in range(5):
        P = pats(w)
        assert len(P) + 1 == 2 ** (w + 1)
        assert sorted(map(tuple, P)) == sorted(t for L in range(w + 1) for t in product((False, True), repeat=L))


def test_cnt_cssF():
    """`Code.cnt_cssF`: the solutions of cssF with s + 2n + 1 true variables are the pairs (x, y),
    |x| = s, x ∈ ker H1, y ∈ ker H2, ⟨x, y⟩ = e."""
    rng = random.Random(11)
    for _ in range(40):
        n = rng.randint(1, 4)
        w = rng.randint(1, 3)
        H1, H2 = random_code(rng, n, w)
        F = {e: cssF(w, n, codeCNF(H1, H2), e) for e in (False, True)}
        for s in range(n + 1):
            for e in (False, True):
                pairs = sum(1 for x in product((0, 1), repeat=n) if sum(x) == s and in_ker(H1, x)
                            for y in product((0, 1), repeat=n)
                            if in_ker(H2, y) and sum(a * b for a, b in zip(x, y)) % 2 == e)
                assert count_sized(F[e], 5 * n + 2, s + 2 * n + 1) == pairs, (H1, H2, s, e)


def test_num_log_random():
    """`CodeTM.css_counts` against brute force (x ∈ ker H1 outside rowspace H2)."""
    rng = random.Random(12)
    for _ in range(40):
        n = rng.randint(1, 5)
        H1, H2 = random_code(rng, n, 3)
        for s in range(n + 1):
            assert num_log(H1, H2, n, s) == brute_num_log(H1, H2, n, s), (H1, H2, s)


def test_known_codes():
    """Steane [[7,1,3]]: 7 logical operators of weight 3; [[4,2,2]]: distance 2; Shor [[9,1,3]]:
    Z-type distance 3 (ZZZ on a block row), X-type distance 3."""
    assert [num_log(STEANE, STEANE, 7, s) for s in range(4)] == [0, 0, 0, 7]
    assert distance(STEANE, STEANE, 7) == 3
    assert distance(CODE_422, CODE_422, 4) == 2
    assert num_log(CODE_422, CODE_422, 4, 2) == brute_num_log(CODE_422, CODE_422, 4, 2) == 6
    assert distance(SHOR_X, SHOR_Z, 9) == 3
    assert distance(SHOR_Z, SHOR_X, 9) == 3
