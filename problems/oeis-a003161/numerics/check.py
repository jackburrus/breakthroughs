"""Exact checks for OEIS A003161 (Z.-W. Sun, 2019): b(n p^k) = b(n p^(k-1)) (mod p^(3k)) for p >= 5,
where a(n) = sum_{k <= n/2} (C(n,k) - C(n,k-1))^3 and b(n) = a(2n - 1). Standard library, exact integers.

Also tests the proof split: with N = m p and ballot numbers B(N, k) = C(2N-1, k) - C(2N-1, k-1)
= C(2N, k)(N - k)/N, write b(mp) = M + R where M sums k = ip (multiples of p) and R the rest.
The PRD's plan needs  M = b(m)  and  R = 0  modulo p^(3(v_p(m)+1)) separately.
Usage: python3 check.py [LIMIT]   (checks n p^k <= LIMIT, default 200)
"""
from fractions import Fraction
from math import comb
import sys


def a(n):
    return sum((comb(n, k) - (comb(n, k - 1) if k else 0)) ** 3 for k in range(n // 2 + 1))


def b(n):
    return a(2 * n - 1)


def ballot(N, k):  # C(2N-1, k) - C(2N-1, k-1)
    return comb(2 * N - 1, k) - (comb(2 * N - 1, k - 1) if k else 0)


def vp(x, p):
    if x == 0:
        return 10 ** 9
    v = 0
    while x % p == 0:
        x //= p
        v += 1
    return v


def main(limit):
    assert [a(n) for n in range(12)] == [1, 1, 2, 9, 36, 190, 980, 5705, 33040, 204876, 1268568, 8209278]  # OEIS data
    cases = 0
    for p in (5, 7, 11, 13, 17, 19, 23):
        for k in (1, 2, 3):
            for n in range(1, 13):
                if n * p ** k > limit:
                    continue
                d = b(n * p ** k) - b(n * p ** (k - 1))
                assert d % p ** (3 * k) == 0, (p, k, n)
                cases += 1
    print(f"supercongruence holds in all {cases} cases with n p^k <= {limit}, p in 5..23, k <= 3")
    split = []
    for p in (5, 7, 11, 13):
        for m in range(1, 16):
            if m * p > limit:
                continue
            N, t = m * p, 3 * (vp(m, p) + 1)
            M = sum(ballot(N, i * p) ** 3 for i in range(m))
            R = sum(ballot(N, j) ** 3 for j in range(N) if j % p)
            assert M + R == b(N)
            split.append((p, m, vp(M - b(m), p) >= t, vp(R, p) >= t))
    ok = all(x[2] and x[3] for x in split)
    print(f"proof split (M = b(m), R = 0 mod p^(3(v+1))) holds separately in all {len(split)} cases: {ok}")
    if not ok:
        print("  failing (p, m, M ok, R ok):", [x for x in split if not (x[2] and x[3])][:10])


if __name__ == '__main__':
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 200)
