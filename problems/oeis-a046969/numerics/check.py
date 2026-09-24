"""Exact checks for OEIS A046969 Conjecture I (standard library, exact int/Fraction arithmetic only).

a(n) = den(B_{2n} / (2n(2n-1))), Mathlib's `bernoulli` convention (B_1 = -1/2; only even indices matter).
Claim to prove: for primes p > 3 with q = 2p - 1 prime, a(p) = 12 q, hence a(p)/12 = q is prime.

Checks:
  1. a(1..10) match the OEIS data (guards the definition).
  2. a(p) = 12(2p-1) exactly, for every such p <= P_EXACT (exact Bernoulli numbers).
  3. The two power-sum congruences the proof uses, for every such p <= P_CONG:
       L2:  p^2 | S_{2p}(p)            where S_m(l) = sum_{k<l} k^m
       L3:  S_{q+1}(q) / q = 1/12 (mod q)   (so q || S_{q+1}(q))
  4. den(B_{2p}) = 6 for every such p <= P_EXACT (the von Staudt-Clausen step).

Usage: python3 check.py [P_EXACT] [P_CONG]    (defaults 200 3000; 400 20000 takes ~15 s)
"""
from fractions import Fraction
from math import comb
import sys


def primes_upto(n):
    s = bytearray([1]) * (n + 1)
    s[0:2] = b'\x00\x00'
    for i in range(2, int(n ** .5) + 1):
        if s[i]:
            s[i * i::i] = bytearray(len(s[i * i::i]))
    return {i for i in range(n + 1) if s[i]}


def bernoulli_list(N):
    B = [Fraction(0)] * (N + 1)
    B[0] = Fraction(1)
    for m in range(1, N + 1):
        B[m] = -sum(comb(m + 1, k) * B[k] for k in range(m)) / (m + 1)
    return B


def a(n, B):
    m = 2 * n
    return (B[m] / (m * (m - 1))).denominator


def main(p_exact, p_cong):
    B = bernoulli_list(2 * max(p_exact, 10))
    assert [a(n, B) for n in range(1, 11)] == [12, 360, 1260, 1680, 1188, 360360, 156, 122400, 244188, 125400]
    P = primes_upto(4 * max(p_exact, p_cong))
    targets = sorted(p for p in P if 3 < p <= p_exact and (2 * p - 1) in P)
    for p in targets:
        assert B[2 * p].denominator == 6, p
        assert a(p, B) == 12 * (2 * p - 1), p
    print(f"exact: den(B_2p) = 6 and a(p) = 12(2p-1) for all {len(targets)} primes 3 < p <= {p_exact} with 2p-1 prime")
    count = 0
    for p in sorted(p for p in P if 3 < p <= p_cong and (2 * p - 1) in P):
        q = 2 * p - 1
        assert sum(pow(k, 2 * p, p * p) for k in range(1, p)) % (p * p) == 0, ('L2', p)
        s = sum(pow(k, q + 1, q * q) for k in range(1, q)) % (q * q)
        assert s % q == 0 and (s // q) % q == pow(12, -1, q), ('L3', p)
        count += 1
    print(f"congruences: L2 and L3 hold for all {count} primes 3 < p <= {p_cong} with 2p-1 prime")


if __name__ == '__main__':
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 200, int(sys.argv[2]) if len(sys.argv) > 2 else 3000)
