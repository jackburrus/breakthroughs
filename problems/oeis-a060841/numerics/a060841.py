"""Exact numerics for OEIS A060841 conjecture 1.

Everything here uses Python integers and fractions.Fraction only, so every
reported number is exact. The notation follows ../BLUEPRINT.md:

    M_n[i][j] = 1 / lcm(i, j)                       (1 <= i, j <= n)
    R(n)      = 1 / det M_n = prod_{k<=n} k^2 / phi(k)   (Lemma L1)
    T_S(n)    = sum_{p in S} v2(p - 1) * floor(n / p)
    T(n)      = T_S(n) with S = all odd primes <= n
    RHS(n)    = v2(n!) + floor(n / 2)

v2(R(n)) = RHS(n) - T(n), so R(n) fails to be 2-integral exactly when
T(n) > RHS(n).
"""

from fractions import Fraction
from math import gcd, prod

INTEGER_SET = frozenset(range(1, 35)) | {36, 38}
"""The set integerDetN = [1, 34] ∪ {36, 38} from the Lean statement."""

THREE_HALVES = Fraction(3, 2)


# --- elementary arithmetic -------------------------------------------------


def primes_upto(n):
    """All primes p <= n, ascending."""
    if n < 2:
        return []
    sieve = bytearray([1]) * (n + 1)
    sieve[0] = sieve[1] = 0
    for i in range(2, int(n**0.5) + 1):
        if sieve[i]:
            sieve[i * i :: i] = bytearray(len(sieve[i * i :: i]))
    return [i for i, flag in enumerate(sieve) if flag]


def odd_primes_upto(n):
    return [p for p in primes_upto(n) if p > 2]


def totients_upto(n):
    """List phi with phi[k] = Euler's totient of k for 0 <= k <= n (phi[0] = 0)."""
    phi = list(range(n + 1))
    for i in range(2, n + 1):
        if phi[i] == i:
            for j in range(i, n + 1, i):
                phi[j] -= phi[j] // i
    return phi


def totient(k):
    return totients_upto(k)[k]


def vp(p, m):
    """p-adic valuation of a nonzero integer or Fraction m."""
    if isinstance(m, Fraction):
        return vp(p, m.numerator) - vp(p, m.denominator)
    if m == 0:
        raise ValueError("valuation of 0")
    m = abs(m)
    if p == 2:
        return (m & -m).bit_length() - 1
    count = 0
    while m % p == 0:
        m //= p
        count += 1
    return count


def legendre(p, n):
    """v_p(n!) by Legendre's formula sum_{i>=1} floor(n / p^i)."""
    total, power = 0, p
    while power <= n:
        total += n // power
        power *= p
    return total


def binary_digit_sum(n):
    return bin(n).count("1")


# --- L1: the determinant and its closed form -------------------------------


def lcm_matrix(n):
    """M_n as a list of rows of Fractions, M[i-1][j-1] = 1/lcm(i, j)."""
    return [
        [Fraction(gcd(i, j), i * j) for j in range(1, n + 1)] for i in range(1, n + 1)
    ]


def gcd_matrix(n):
    return [[gcd(i, j) for j in range(1, n + 1)] for i in range(1, n + 1)]


def det_fraction(matrix):
    """Exact determinant of a square Fraction matrix by Gaussian elimination."""
    a = [[Fraction(x) for x in row] for row in matrix]
    size = len(a)
    det = Fraction(1)
    for col in range(size):
        pivot = next((r for r in range(col, size) if a[r][col] != 0), None)
        if pivot is None:
            return Fraction(0)
        if pivot != col:
            a[col], a[pivot] = a[pivot], a[col]
            det = -det
        det *= a[col][col]
        for r in range(col + 1, size):
            factor = a[r][col] / a[col][col]
            if factor:
                for c in range(col, size):
                    a[r][c] -= factor * a[col][c]
    return det


def det_bareiss(matrix):
    """Exact determinant of a square integer matrix (fraction-free Bareiss)."""
    a = [list(row) for row in matrix]
    size = len(a)
    sign, prev = 1, 1
    for k in range(size - 1):
        if a[k][k] == 0:
            swap = next((r for r in range(k + 1, size) if a[r][k] != 0), None)
            if swap is None:
                return 0
            a[k], a[swap] = a[swap], a[k]
            sign = -sign
        for i in range(k + 1, size):
            for j in range(k + 1, size):
                a[i][j] = (a[i][j] * a[k][k] - a[i][k] * a[k][j]) // prev
        prev = a[k][k]
    return sign * a[size - 1][size - 1] if size else 1


def divisor_indicator_matrix(n):
    """A[i-1][d-1] = 1 if d divides i: lower unitriangular, G = A diag(phi) A^T."""
    return [[1 if i % d == 0 else 0 for d in range(1, n + 1)] for i in range(1, n + 1)]


def inverse_det_closed_form(n):
    """R(n) = prod_{k<=n} k^2 / phi(k) as an exact Fraction."""
    phi = totients_upto(n)
    return Fraction(prod(k * k for k in range(1, n + 1)), prod(phi[1 : n + 1]))


def inverse_det_sequence(max_n):
    """Yield (n, R(n)) for 1 <= n <= max_n incrementally, in lowest terms."""
    phi = totients_upto(max_n)
    num, den = 1, 1
    for k in range(1, max_n + 1):
        num *= k * k
        den *= phi[k]
        g = gcd(num, den)
        num //= g
        den //= g
        yield k, Fraction(num, den)


def integer_n_upto(max_n):
    """All n <= max_n with R(n) an integer, from the exact closed form."""
    return [n for n, value in inverse_det_sequence(max_n) if value.denominator == 1]


# --- valuations of R(n) ----------------------------------------------------


def valuation_formula(p, n, primes=None):
    """v_p(R(n)) = v_p(n!) + floor(n/p) - sum_{q prime <= n} v_p(q-1) floor(n/q).

    Valid for every prime p (for p = 2 the q = 2 term vanishes because v2(1) = 0).
    """
    if primes is None:
        primes = primes_upto(n)
    subtract = sum(vp(p, q - 1) * (n // q) for q in primes if q <= n and q > 2)
    return legendre(p, n) + n // p - subtract


def v2_totient_product_direct(n):
    """v2(prod_{k<=n} phi(k)) summed term by term."""
    phi = totients_upto(n)
    return sum(vp(2, phi[k]) for k in range(1, n + 1))


def v2_totient_product_formula(n, primes=None):
    """The PRD formula: v2(n!) - floor(n/2) + sum_{3<=p<=n} v2(p-1) floor(n/p)."""
    return legendre(2, n) - n // 2 + T(n, primes)


def T(n, primes=None):
    """T(n) = sum over odd primes p <= n of v2(p-1) * floor(n/p)."""
    if primes is None:
        primes = primes_upto(n)
    return sum(vp(2, p - 1) * (n // p) for p in primes if 2 < p <= n)


def T_S(n, S):
    """T_S(n) = sum_{p in S} v2(p-1) * floor(n/p) for a fixed prime set S."""
    return sum(vp(2, p - 1) * (n // p) for p in S)


def rhs(n):
    """RHS(n) = v2(n!) + floor(n/2)."""
    return legendre(2, n) + n // 2


def two_adic_failure_scan(max_n):
    """Return the n <= max_n where T(n) <= RHS(n) (R(n) is 2-integral).

    Runs in O(max_n log log max_n) by updating T(n) and v2(n!) incrementally:
    T(n) - T(n-1) = sum_{odd prime p | n} v2(p-1).
    """
    increments = [0] * (max_n + 1)
    for p in odd_primes_upto(max_n):
        weight = vp(2, p - 1)
        for multiple in range(p, max_n + 1, p):
            increments[multiple] += weight
    t_value, v2_fact, integral = 0, 0, []
    for n in range(1, max_n + 1):
        t_value += increments[n]
        v2_fact += vp(2, n)
        if t_value <= v2_fact + n // 2:
            integral.append(n)
    return integral


def superadditive_scan(max_n):
    """Return the n <= max_n where 2 T(n) < 3 n (the 3n/2 relaxation fails)."""
    increments = [0] * (max_n + 1)
    for p in odd_primes_upto(max_n):
        weight = vp(2, p - 1)
        for multiple in range(p, max_n + 1, p):
            increments[multiple] += weight
    t_value, failures = 0, []
    for n in range(1, max_n + 1):
        t_value += increments[n]
        if 2 * t_value < 3 * n:
            failures.append(n)
    return failures


def odd_prime_valuations(n):
    """{p: v_p(R(n))} for every odd prime p <= n."""
    primes = primes_upto(n)
    return {p: valuation_formula(p, n, primes) for p in primes if p > 2}


# --- L3: the linear (floor-bound) argument ---------------------------------


def linear_constants(S):
    """Exact (A, V, B) for a prime set S.

    A = sum v2(p-1)/p,  V = sum v2(p-1),  B = sum v2(p-1)(p-1)/p = V - A.
    The floor bound floor(n/p) >= (n - (p-1))/p gives T_S(n) >= A n - B.
    """
    A = sum((Fraction(vp(2, p - 1), p) for p in S), Fraction(0))
    V = sum(vp(2, p - 1) for p in S)
    B = sum((Fraction(vp(2, p - 1) * (p - 1), p) for p in S), Fraction(0))
    assert B == V - A
    return A, V, B


def linear_threshold(S, refined=False):
    """Smallest integer N0 such that the linear bound proves T_S(n) > RHS(n) for n >= N0.

    crude   (refined=False): uses RHS(n) < 3n/2, needs A n - B >= 3n/2.
    refined (refined=True):  uses RHS(n) <= 3n/2 - 1, needs A n - B > 3n/2 - 1.
    Returns None when A <= 3/2 (the bound never wins).
    """
    A, _, B = linear_constants(S)
    slope = A - THREE_HALVES
    if slope <= 0:
        return None
    if refined:
        # smallest integer n with slope * n > B - 1
        bound = (B - 1) / slope
        n0 = bound.numerator // bound.denominator + 1
    else:
        # smallest integer n with slope * n >= B
        bound = B / slope
        n0 = -((-bound.numerator) // bound.denominator)
    return max(n0, 1)


def optimal_linear_prime_set(search_limit=2000, refined=False):
    """Best S for the linear argument, scanning prefixes of the odd primes.

    Adding a prime p with weight a = v2(p-1)/p, b = a (p-1) to S changes the
    real threshold t = B / (A - 3/2) (crude) to (B + b) / (A + a - 3/2), which
    is smaller iff b / a = p - 1 < t. So an optimal S is a prefix of the odd
    primes (see BLUEPRINT.md, L3), and scanning prefixes finds the optimum.
    Returns (N0, S).
    """
    best = None
    odd = odd_primes_upto(search_limit)
    for k in range(1, len(odd) + 1):
        S = odd[:k]
        n0 = linear_threshold(S, refined=refined)
        if n0 is not None and (best is None or n0 < best[0]):
            best = (n0, S)
    return best


def linear_bound_holds(n, S):
    """Exact check of the floor bound T_S(n) >= A n - B at one n."""
    A, _, B = linear_constants(S)
    return T_S(n, S) >= A * n - B


# --- L3': the superadditive window argument --------------------------------


def G(n, S):
    """G_S(n) = 2 T_S(n) - 3n. Superadditive in n because T_S is."""
    return 2 * T_S(n, S) - 3 * n


def window_certificate(n0, step, S=None):
    """Check the finite hypotheses that prove 2 T(n) >= 3n for every n >= n0.

    For a fixed set S of odd primes (default: odd primes < n0 + step, so that
    T_S = T on the window):
      (a) G_S(step) >= 0, and
      (b) G_S(n) >= 0 for every n in [n0, n0 + step).
    Superadditivity then gives G_S(n) >= G_S(n - step) + G_S(step) >= 0 for
    n >= n0 + step by induction, and T(n) >= T_S(n). Returns (ok, S).
    """
    if S is None:
        S = odd_primes_upto(n0 + step - 1)
    ok = G(step, S) >= 0 and all(G(n, S) >= 0 for n in range(n0, n0 + step))
    return ok, S


def smallest_window_step(n0, max_step=None):
    """Smallest step m such that window_certificate(n0, m) succeeds, or None."""
    for step in range(1, (max_step or 4 * n0) + 1):
        ok, _ = window_certificate(n0, step)
        if ok:
            return step
    return None


def smallest_window_prime_set(n0, step):
    """Shortest prefix S = odd primes <= P that certifies (n0, step), or None.

    Shrinking S only lowers T_S, so the shortest working prefix is found by a
    forward scan.
    """
    for P in odd_primes_upto(n0 + step - 1):
        S = odd_primes_upto(P)
        ok, _ = window_certificate(n0, step, S)
        if ok:
            return S
    return None
