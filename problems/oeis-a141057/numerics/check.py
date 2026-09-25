"""Exact checks for OEIS A141057 conjecture 2 (Peter Bala, 2022/23), as stated in formal-conjectures:
aInt(n p^k) = aInt(n p^(k-1)) (mod p^(3k)) for all integers n != 0, primes p >= 5, k >= 1, where
aInt(n) = a(n) for n >= 0 and aInt(-m) = sum_{k=0}^{m} C(-m,k)^3 F(k), C(-m,k) = (-1)^k C(m+k-1,k),
F(k) = sum_j C(k,j)^3 (Franel numbers). Standard library, exact integers.

Also tests, for negative n, the term-by-term split our proof uses: with N = m p and e = v_p(m), split
aInt(-N) at the pairs (k, j) = (i p, l p) (S). Modulo p^(3e+3), every other pair vanishes (V) and each
multiple pair matches the (i, l) term of aInt(-m) (P).
Usage: python3 check.py [LIMIT]   (checks |n| p^k <= LIMIT, default 700)
"""
from math import comb
import sys


def franel(K):
    return [sum(comb(k, j) ** 3 for j in range(k + 1)) for k in range(K + 1)]


def gbin(n, k):  # generalized binomial C(n, k) for integer n, k >= 0
    if n >= 0:
        return comb(n, k)
    return (-1) ** k * comb(-n + k - 1, k)


def aInt(n, F):
    if n >= 0:
        return sum(comb(n, k) ** 3 * F[k] for k in range(n + 1))
    m = -n
    return sum(gbin(-m, k) ** 3 * F[k] for k in range(m + 1))


def vp(x, p):
    if x == 0:
        return 10 ** 9
    v = 0
    while x % p == 0:
        x //= p
        v += 1
    return v


def main(limit):
    F = franel(limit)
    # OEIS A141057 data and Bala's negative-index values
    assert [aInt(n, F) for n in range(6)] == [1, 3, 27, 381, 6219, 111753]
    assert [aInt(-m, F) for m in range(1, 8)] == [-1, 255, -53893, 14396623, -4388536251,
                                                  1461954981315, -518606406878589]
    cases = 0
    for p in (5, 7, 11, 13, 17, 19, 23):
        for k in (1, 2, 3):
            for n in list(range(-12, 0)) + list(range(1, 13)):
                if abs(n) * p ** k > limit:
                    continue
                assert (aInt(n * p ** k, F) - aInt(n * p ** (k - 1), F)) % p ** (3 * k) == 0, (p, k, n)
                cases += 1
    print(f"conjecture 2 holds in all {cases} cases (n in -12..12 minus 0, |n| p^k <= {limit}, p <= 23, k <= 3)")
    # term-by-term split for negative indices
    bad = []
    total = 0
    for p in (5, 7, 11):
        for m in range(1, 12):
            N = m * p
            if N > 160:
                continue
            t = 3 * (vp(m, p) + 1)
            for kk in range(N + 1):
                for j in range(kk + 1):
                    T = (gbin(-N, kk) * comb(kk, j)) ** 3
                    if kk % p == 0 and j % p == 0:
                        d = T - (gbin(-m, kk // p) * comb(kk // p, j // p)) ** 3
                        if vp(d, p) < t:
                            bad.append(('multiple', p, m, kk, j))
                    elif vp(T, p) < t:
                        bad.append(('other', p, m, kk, j))
                    total += 1
    print(f"term-by-term split holds for all {total} terms (N = m p <= 160): {not bad}", bad[:5])


if __name__ == '__main__':
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 700)
