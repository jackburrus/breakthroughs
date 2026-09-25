"""Exact checks of the Lean lemma statements in ../lean/A141057/, in the general forms stated there.

Each check mirrors one Lean statement literally: natural-number subtraction truncates at 0,
C(n, k) = 0 for k > n, and v(0) = 0 (Mathlib's padicValNat). Hypotheses of the form p^e | n are
tested at the largest such e (every smaller e follows), and up to a cap when n = 0.
Standard library, exact integers.
For U, D and K, whose proofs need p >= 5, the same check also runs at p = 3 and must find a
counterexample, so the hypothesis matters and the check has teeth. P needs no such check: at
p = 3 the cube recovers the factor of 3 that Jacobsthal loses, so P can hold there too.
Usage: python3 lemmas.py
"""
from math import comb, gcd

PRIMES = (5, 7, 11, 13)
CAP = 4  # exponents tried when the hypothesis is p^e | 0


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


def exps(p, *xs):  # every e with p^e dividing all of xs
    nonzero = [x for x in xs if x != 0]
    return range(min(v(p, x) for x in nonzero) + 1 if nonzero else CAP + 1)


def dvd(d, x):
    return x % d == 0


def prod(xs, q=None):
    r = 1
    for x in xs:
        r = r * x if q is None else r * x % q
    return r


def coprime_below(p, N):  # the a < N prime to p
    return [a for a in range(N) if a % p]


# U: p >= 5 -> the squares of the units of ZMod (p^s) sum to 0.
def U(p, s):
    q = p**s
    return sum(u * u for u in coprime_below(p, q)) % q == 0


# U.sum_range_coprime: 1 <= s -> the sum over a < p^s c, p not dividing a, of f(a mod p^s)
# is c times the sum over the units. Tried with f = a^-2 and a^3 + 1, valued in ZMod (p^s).
def U_blocks(p, s, c):
    q = p**s
    units = coprime_below(p, q)
    for f in (lambda a: pow(a, -2, q), lambda a: (a**3 + 1) % q):
        lhs = sum(f(a % q) for a in coprime_below(p, q * c)) % q
        if lhs != c * sum(f(u) for u in units) % q:
            return False
    return True


# D: p^r | x -> p^s | N -> prod_{a < N, p not dividing a} (x + a) = prod a mod p^(3 min(r, s)).
def D(p, x, N, r, s):
    q = p ** (3 * min(r, s))
    S = coprime_below(p, N)
    return prod((x + a for a in S), q) == prod(S, q)


# The step of D's proof that uses U: for s >= 1 and p^s | N, sum over the a < N prime to p of
# (a (N - a))^-1 vanishes mod p^s.
def D_pairs(p, s, N):
    q = p**s
    return sum(pow(a * (N - a), -1, q) for a in coprime_below(p, N)) % q == 0


# K: p^u | a -> p^u | b -> p^w | C(a + b, a) ->
#    C((a + b) p, a p) = C(a + b, a) mod p^(w + 3 u + 3).
def K(p, a, b):
    c = C(a + b, a)
    return all(
        dvd(p ** (w + 3 * u + 3), C((a + b) * p, a * p) - c)
        for u in exps(p, a, b)
        for w in exps(p, c)
    )


# KNeg: p^u | a -> p^u | b -> p^w | C(b + a - 1, a) ->
#    C(b p + a p - 1, a p) = C(b + a - 1, a) mod p^(w + 3 u + 3).
def KNeg(p, a, b):
    c = C(sub(b + a, 1), a)
    return all(
        dvd(p ** (w + 3 * u + 3), C(sub(b * p + a * p, 1), a * p) - c)
        for u in exps(p, a, b)
        for w in exps(p, c)
    )


# The identities behind K and KNeg: with H(c) = prod_{j < a p, p not dividing j} (c p + j),
# C((a + b) p, a p) H(0) = C(a + b, a) H(b) and C(b p + a p - 1, a p) H(0) = C(b + a - 1, a) H(b),
# from split_one / split_zero: prod_{j < n p} (c p + j + d) = p^n prod_{i < n} (c + i + d) H(c), d = 0, 1.
def K_split(p, a, b):
    def H(c):
        return prod(c * p + j for j in coprime_below(p, a * p))

    splits = all(
        prod(c * p + j + d for j in range(a * p))
        == p**a * prod(c + i + d for i in range(a)) * H(c)
        for c in (0, b)
        for d in (0, 1)
    )
    return (
        splits
        and C((a + b) * p, a * p) * H(0) == C(a + b, a) * H(b)
        and C(sub(b * p + a * p, 1), a * p) * H(0) == C(sub(b + a, 1), a) * H(b)
    )


# A (absorption, as divisibilities), no hypotheses:
def A_absorb(N, k):  # N | k C(N, k)
    return dvd_or_zero(N, k * C(N, k))


def A_absorbNeg(N, k):  # N | k C(N + k - 1, k)
    return dvd_or_zero(N, k * C(sub(N + k, 1), k))


def A_gcd(x, y):  # x + y | gcd(x, y) C(x + y, x)
    return dvd_or_zero(x + y, gcd(x, y) * C(x + y, x))


def A_gcdNeg(N, k):  # N | gcd(N, k) C(N + k - 1, k)
    return dvd_or_zero(N, gcd(N, k) * C(sub(N + k, 1), k))


def A_symm_neg(
    N, k, j
):  # 1 <= N -> j <= k -> C(N+k-1, k) C(k, j) = C(N+j-1, j) C(N+k-1, k-j)
    return C(sub(N + k, 1), k) * C(k, j) == C(sub(N + j, 1), j) * C(
        sub(N + k, 1), sub(k, j)
    )


def dvd_or_zero(d, x):  # d | x in N, where 0 | x means x = 0
    return x == 0 if d == 0 else x % d == 0


# V: p^e | N -> not (p | k and p | j) -> p^e | C(N, k) C(k, j)  (and the negative-index analogue).
def V_pos(p, N, k, j):
    return all(dvd(p**e, C(N, k) * C(k, j)) for e in exps(p, N))


def V_neg(p, N, k, j):
    return all(dvd(p**e, C(sub(N + k, 1), k) * C(k, j)) for e in exps(p, N))


# P: per-summand supercongruences modulo p^(3 e + 3).
def P_summand(p, a, b, c):  # p^e | a + b + c
    lhs = C((a + b + c) * p, (a + b) * p) * C((a + b) * p, a * p)
    rhs = C(a + b + c, a + b) * C(a + b, a)
    return all(dvd(p ** (3 * e + 3), lhs**3 - rhs**3) for e in exps(p, a + b + c))


def P_summandNeg(p, m, a, b):  # 1 <= m, p^e | m
    lhs = C(sub(m * p + (a + b) * p, 1), (a + b) * p) * C((a + b) * p, a * p)
    rhs = C(sub(m + a + b, 1), a + b) * C(a + b, a)
    return all(dvd(p ** (3 * e + 3), lhs**3 - rhs**3) for e in exps(p, m))


# R: aInt as FC defines it.
def franel(K_):
    return [sum(comb(k, j) ** 3 for j in range(k + 1)) for k in range(K_ + 1)]


def aInt(n, F):
    if n >= 0:
        return sum(comb(n, k) ** 3 * F[k] for k in range(n + 1))
    m = -n
    return sum(((-1) ** k * C(m + k - 1, k)) ** 3 * F[k] for k in range(m + 1))


def R_stepInt(
    p, n, F
):  # p^e | n -> aInt(n p) = aInt(n) mod p^(3 e + 3); R_step, R_stepNeg are n >= 0, n < 0
    return all(
        dvd(p ** (3 * e + 3), aInt(n * p, F) - aInt(n, F)) for e in exps(p, abs(n))
    )


def R_pow(p, n, j, F):  # aInt(n p^(j + 1)) = aInt(n p^j) mod p^(3 (j + 1))
    return dvd(p ** (3 * (j + 1)), aInt(n * p ** (j + 1), F) - aInt(n * p**j, F))


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
    run("U", ((p, s) for p in PRIMES for s in range(0, 5) if p ** s <= 30000), U)
    counterexample("U", ((3, s) for s in (1, 2, 3)), U)
    run(
        "U_blocks",
        ((p, s, c) for p in (3,) + PRIMES for s in (1, 2) for c in range(0, 5)),
        U_blocks,
    )
    run(
        "D",
        (
            (p, x, N, r, s)
            for p in (5, 7)
            for r in range(0, 3)
            for s in range(0, 3)
            for N in range(0, 4 * p**s + 1, p**s)
            if N <= 400
            for x in range(-3 * p**r, 3 * p**r + 1, p**r)
        ),
        D,
    )
    counterexample(
        "D",
        (
            (3, x, N, r, s)
            for r in (1, 2)
            for s in (1, 2)
            for N in range(3**s, 4 * 3**s, 3**s)
            for x in range(3**r, 4 * 3**r, 3**r)
        ),
        D,
    )
    run(
        "D_pairs",
        (
            (p, s, N)
            for p in PRIMES
            for s in (1, 2, 3)
            for N in range(p**s, 5 * p**s, p**s)
            if N <= 12000
        ),
        D_pairs,
    )
    run(
        "K",
        ((p, a, b) for p in (5, 7, 11) for a in range(0, 31) for b in range(0, 31)),
        K,
    )
    counterexample("K", ((3, a, b) for a in range(0, 12) for b in range(0, 12)), K)
    run(
        "KNeg",
        ((p, a, b) for p in (5, 7, 11) for a in range(0, 31) for b in range(0, 31)),
        KNeg,
    )
    run(
        "K_split",
        ((p, a, b) for p in (3, 5, 7) for a in range(0, 9) for b in range(0, 9)),
        K_split,
    )
    run("A_absorb", ((N, k) for N in range(0, 151) for k in range(0, 155)), A_absorb)
    run(
        "A_absorbNeg", ((N, k) for N in range(0, 81) for k in range(0, 81)), A_absorbNeg
    )
    run("A_gcd", ((x, y) for x in range(0, 81) for y in range(0, 81)), A_gcd)
    run("A_gcdNeg", ((N, k) for N in range(0, 81) for k in range(0, 81)), A_gcdNeg)
    run(
        "A_symm_neg",
        (
            (N, k, j)
            for N in range(1, 41)
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
        "P_summand",
        (
            (p, a, b, c)
            for p in (5, 7)
            for a in range(0, 16)
            for b in range(0, 16)
            for c in range(0, 16)
        ),
        P_summand,
    )
    run(
        "P_summandNeg",
        (
            (p, m, a, b)
            for p in (5, 7)
            for m in range(1, 26)
            for a in range(0, 13)
            for b in range(0, 13)
        ),
        P_summandNeg,
    )
    F = franel(7 * 30 * 7)
    run(
        "R_stepInt",
        ((p, n, F) for p in (5, 7) for n in range(-30, 31)),
        R_stepInt,
    )
    run(
        "R_pow",
        (
            (p, n, j, F)
            for p in (5, 7)
            for n in range(-6, 7)
            for j in range(0, 3)
            if abs(n) * p ** (j + 1) <= 7 * 30 * 7
        ),
        R_pow,
    )


if __name__ == "__main__":
    main()
