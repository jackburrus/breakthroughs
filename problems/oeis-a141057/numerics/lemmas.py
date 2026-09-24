"""Exact checks of the Lean lemma statements in ../lean/A141057/, in the general forms stated there.

Each check mirrors one Lean statement literally: natural-number subtraction truncates at 0,
C(n, k) = 0 for k > n, and v(0) = 0 (Mathlib's padicValNat). Standard library, exact integers.
For U, D and K, whose proofs need p >= 5, the same check also runs at p = 3 and must find a
counterexample, so the hypothesis matters and the check has teeth. P needs no such check: at
p = 3 the cube recovers the factor of 3 that Jacobsthal loses, so P can hold there too.
Usage: python3 lemmas.py
"""
from math import comb

PRIMES = (5, 7, 11, 13)


def C(n, k):
    return comb(n, k) if 0 <= k <= n else 0


def sub(a, b):  # truncated subtraction on naturals
    return max(a - b, 0)


def v(p, x):  # padicValNat p x, with v(0) = 0
    if x == 0:
        return 0
    e = 0
    while x % p == 0:
        x //= p
        e += 1
    return e


def dvd(d, x):
    return x % d == 0


# U: for p^s | N, the sums of a^-1 and a^-2 over 0 <= a < N, p not dividing a, vanish mod p^s.
def U(p, s, N):
    q = p**s
    units = [a for a in range(N) if a % p]
    return (
        sum(pow(a, -1, q) for a in units) % q == 0
        and sum(pow(a, -2, q) for a in units) % q == 0
    )


# D: p^(3 + 3 min(v B, v L)) | prod_{a < L p, p not dividing a} (B p + a) - prod a.
def D(p, L, B):
    q = p ** (3 + 3 * min(v(p, B), v(p, L)))
    P0 = P1 = 1
    for a in range(L * p):
        if a % p:
            P0 = P0 * a % q
            P1 = P1 * (B * p + a) % q
    return (P1 - P0) % q == 0


# K: B <= A -> p^(v C(A,B) + 3 + 3 min(v B, v(A - B))) | C(A p, B p) - C(A, B).
def K(p, A, B):
    e = v(p, C(A, B)) + 3 + 3 * min(v(p, B), v(p, sub(A, B)))
    return dvd(p**e, C(A * p, B * p) - C(A, B))


# KNeg: 1 <= m -> p^(v C(m+i-1, i) + 3 + 3 min(v i, v m)) | C(m p + i p - 1, i p) - C(m + i - 1, i).
def KNeg(p, m, i):
    e = v(p, C(sub(m + i, 1), i)) + 3 + 3 * min(v(p, i), v(p, m))
    return dvd(p**e, C(sub(m * p + i * p, 1), i * p) - C(sub(m + i, 1), i))


# A (valuation bounds from absorption), p prime:
def A_pos(p, N, k):  # 1 <= k <= N -> v N <= v k + v C(N, k)
    return v(p, N) <= v(p, k) + v(p, C(N, k))


def A_neg(p, N, k):  # 1 <= N -> 1 <= k -> v N <= v k + v C(N + k - 1, k)
    return v(p, N) <= v(p, k) + v(p, C(sub(N + k, 1), k))


def A_kummer(p, x, y):  # 1 <= x -> 1 <= y -> v(x + y) <= v C(x + y, x) + min(v x, v y)
    return v(p, x + y) <= v(p, C(x + y, x)) + min(v(p, x), v(p, y))


def A_symm_neg(N, k, j):  # j <= k -> C(N+k-1, k) C(k, j) = C(N+j-1, j) C(N+k-1, k-j)
    return C(sub(N + k, 1), k) * C(k, j) == C(sub(N + j, 1), j) * C(
        sub(N + k, 1), sub(k, j)
    )


# V: not (p | k and p | j) -> p^(v N) | C(N, k) C(k, j)  (and the negative-index analogue).
def V_pos(p, N, k, j):
    return dvd(p ** v(p, N), C(N, k) * C(k, j))


def V_neg(p, N, k, j):
    return dvd(p ** v(p, N), C(sub(N + k, 1), k) * C(k, j))


# P: per-term supercongruences, p^(3 (v m + 1)).
def P_pos(p, m, i, l):  # l <= i <= m
    return dvd(
        p ** (3 * (v(p, m) + 1)),
        (C(m * p, i * p) * C(i * p, l * p)) ** 3 - (C(m, i) * C(i, l)) ** 3,
    )


def P_neg(p, m, i, l):  # 1 <= m, l <= i
    lhs = C(sub(m * p + i * p, 1), i * p) * C(i * p, l * p)
    rhs = C(sub(m + i, 1), i) * C(i, l)
    return dvd(p ** (3 * (v(p, m) + 1)), lhs**3 - rhs**3)


# R: one-step supercongruence p^(3 (v m + 1)) | aInt(+-m p) - aInt(+-m), as FC defines aInt.
def franel(K_):
    return [sum(comb(k, j) ** 3 for j in range(k + 1)) for k in range(K_ + 1)]


def aInt(n, F):
    if n >= 0:
        return sum(comb(n, k) ** 3 * F[k] for k in range(n + 1))
    m = -n
    return sum(((-1) ** k * C(m + k - 1, k)) ** 3 * F[k] for k in range(m + 1))


def run(name, cases, pred):
    n = 0
    for c in cases:
        assert pred(*c), (name, c)
        n += 1
    print(f"{name}: holds in all {n} cases")


def counterexample(name, cases, pred):
    for c in cases:
        if not pred(*c):
            print(f"{name} at p = 3 fails, as expected, e.g. at {c}")
            return
    raise AssertionError(
        f"{name} unexpectedly holds at p = 3: the p >= 5 check has no teeth"
    )


def main():
    run(
        "U",
        (
            (p, s, N)
            for p in PRIMES
            for s in (1, 2, 3)
            for N in range(0, 4 * p**s + 1, p**s)
            if N <= 6000
        ),
        U,
    )
    counterexample("U", ((3, s, N) for s in (1, 2) for N in range(0, 30, 3**s)), U)
    run("D", ((p, L, B) for p in (5, 7) for L in range(0, 31) for B in range(0, 61)), D)
    counterexample("D", ((3, L, B) for L in range(0, 10) for B in range(0, 10)), D)
    run(
        "K",
        ((p, A, B) for p in (5, 7, 11) for A in range(0, 41) for B in range(0, A + 1)),
        K,
    )
    counterexample("K", ((3, A, B) for A in range(0, 12) for B in range(0, A + 1)), K)
    run(
        "KNeg",
        ((p, m, i) for p in (5, 7, 11) for m in range(1, 31) for i in range(0, 31)),
        KNeg,
    )
    run(
        "A_pos",
        (
            (p, N, k)
            for p in (2, 3) + PRIMES
            for N in range(1, 151)
            for k in range(1, N + 1)
        ),
        A_pos,
    )
    run(
        "A_neg",
        (
            (p, N, k)
            for p in (2, 3) + PRIMES
            for N in range(1, 81)
            for k in range(1, 81)
        ),
        A_neg,
    )
    run(
        "A_kummer",
        (
            (p, x, y)
            for p in (2, 3) + PRIMES
            for x in range(1, 81)
            for y in range(1, 81)
        ),
        A_kummer,
    )
    run(
        "A_symm_neg",
        (
            (N, k, j)
            for N in range(0, 41)
            for k in range(0, 41)
            for j in range(0, k + 1)
        ),
        A_symm_neg,
    )
    run(
        "V_pos",
        (
            (p, N, k, j)
            for p in (2, 3) + PRIMES
            for N in range(0, 61)
            for k in range(0, N + 3)
            for j in range(0, k + 3)
            if not (k % p == 0 and j % p == 0)
        ),
        V_pos,
    )
    run(
        "V_neg",
        (
            (p, N, k, j)
            for p in (2, 3) + PRIMES
            for N in range(0, 61)
            for k in range(0, 61)
            for j in range(0, k + 3)
            if not (k % p == 0 and j % p == 0)
        ),
        V_neg,
    )
    run(
        "P_pos",
        (
            (p, m, i, l)
            for p in (5, 7)
            for m in range(0, 26)
            for i in range(0, m + 1)
            for l in range(0, i + 1)
        ),
        P_pos,
    )
    run(
        "P_neg",
        (
            (p, m, i, l)
            for p in (5, 7)
            for m in range(1, 26)
            for i in range(0, 26)
            for l in range(0, i + 1)
        ),
        P_neg,
    )
    # identities used by KNeg and R_neg
    run(
        "(m + i) C(m + i - 1, i) = m C(m + i, i)",
        ((m, i) for m in range(1, 60) for i in range(0, 60)),
        lambda m, i: (m + i) * C(m + i - 1, i) == m * C(m + i, i),
    )
    F = franel(7 * 30)
    run(
        "R_pos",
        ((p, m) for p in (5, 7) for m in range(1, 31)),
        lambda p, m: dvd(p ** (3 * (v(p, m) + 1)), aInt(m * p, F) - aInt(m, F)),
    )
    run(
        "R_neg",
        ((p, m) for p in (5, 7) for m in range(1, 31)),
        lambda p, m: dvd(p ** (3 * (v(p, m) + 1)), aInt(-m * p, F) - aInt(-m, F)),
    )


if __name__ == "__main__":
    main()
