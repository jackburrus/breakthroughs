"""Regression tests for the claims in REPORT.md and ../BLUEPRINT.md.

Run from this directory:  python3 -m unittest -v
"""

import unittest
from fractions import Fraction
from math import gcd, prod
from pathlib import Path

import a060841 as a
import report

HERE = Path(__file__).resolve().parent

PRD_S = [
    3,
    5,
    7,
    11,
    13,
    17,
    19,
    23,
    29,
    31,
    37,
    41,
    43,
    47,
    53,
    59,
    61,
    67,
    71,
    73,
    79,
]
PRD_A = Fraction(3049629558983711743173310451026, 1608822383670336453949542277065)
PRD_B = Fraction(51650331485807727691111126969184, 1608822383670336453949542277065)


class Arithmetic(unittest.TestCase):
    def test_totients(self):
        self.assertEqual(a.totients_upto(12)[1:], [1, 1, 2, 2, 4, 2, 6, 4, 6, 4, 10, 4])

    def test_valuations(self):
        self.assertEqual(a.vp(2, 96), 5)
        self.assertEqual(a.vp(3, Fraction(2, 27)), -3)
        for n in range(0, 300):
            self.assertEqual(a.legendre(2, n), n - a.binary_digit_sum(n))

    def test_bareiss_matches_fraction_det(self):
        for n in range(1, 9):
            g = a.gcd_matrix(n)
            self.assertEqual(a.det_bareiss(g), a.det_fraction(g))


class L1Determinant(unittest.TestCase):
    def test_lcm_matrix_matches_closed_form(self):
        for n in range(1, 13):
            det = a.det_fraction(a.lcm_matrix(n))
            self.assertEqual(1 / det, a.inverse_det_closed_form(n), n)

    def test_smith_determinant(self):
        phi = a.totients_upto(30)
        for n in range(1, 31):
            self.assertEqual(a.det_bareiss(a.gcd_matrix(n)), prod(phi[1 : n + 1]), n)

    def test_gcd_factorization(self):
        # G = A diag(phi) A^T  <=>  sum_{d | gcd(i,j)} phi(d) = gcd(i,j)
        n = 24
        phi = a.totients_upto(n)
        A = a.divisor_indicator_matrix(n)
        for i in range(n):
            self.assertEqual(A[i][i], 1)
            self.assertTrue(all(A[i][d] == 0 for d in range(i + 1, n)))
            for j in range(n):
                entry = sum(A[i][d] * phi[d + 1] * A[j][d] for d in range(n))
                self.assertEqual(entry, gcd(i + 1, j + 1))

    def test_lean_statement_values(self):
        # a_1 .. a_5 from FormalConjectures/OEIS/60841.lean
        nums = [a.inverse_det_closed_form(n).numerator for n in range(1, 6)]
        self.assertEqual(nums, [1, 4, 18, 144, 900])

    def test_oeis_bfile(self):
        bfile = report.read_bfile()
        self.assertEqual(len(bfile), 400)
        for n, value in a.inverse_det_sequence(400):
            self.assertEqual(value.numerator, bfile[n], n)

    def test_oeis_comment_n35(self):
        # Harry J. Smith, OEIS A060841: 1/det(35) = .../2
        self.assertEqual(
            a.inverse_det_closed_form(35),
            Fraction(5029296746186844716050163189085401314000634765625, 2),
        )


class Integrality(unittest.TestCase):
    def test_integer_set_closed_form(self):
        self.assertEqual(set(a.integer_n_upto(1500)), a.INTEGER_SET)

    def test_integer_set_two_adic_scan(self):
        self.assertEqual(set(a.two_adic_failure_scan(50000)), a.INTEGER_SET)

    def test_v2_totient_product_formula(self):
        for n in range(1, 600):
            self.assertEqual(
                a.v2_totient_product_direct(n), a.v2_totient_product_formula(n), n
            )

    def test_v2_of_R(self):
        for n, value in a.inverse_det_sequence(600):
            self.assertEqual(a.vp(2, value), a.rhs(n) - a.T(n), n)


class L2FiniteRange(unittest.TestCase):
    def test_valuation_formula_every_prime(self):
        for n in range(1, 82):
            value = a.inverse_det_closed_form(n)
            for p in a.primes_upto(n + 5):
                self.assertEqual(a.valuation_formula(p, n), a.vp(p, value), (p, n))

    def test_odd_primes_never_obstruct_below_82(self):
        for n in range(1, 82):
            self.assertTrue(all(v >= 2 for v in a.odd_prime_valuations(n).values()), n)

    def test_two_adic_decides_below_82(self):
        for n in range(1, 82):
            self.assertEqual(a.rhs(n) >= a.T(n), n in a.INTEGER_SET, n)

    def test_n35_37_fail_by_one(self):
        self.assertEqual(a.rhs(35) - a.T(35), -1)
        self.assertEqual(a.rhs(37) - a.T(37), -1)


class L3Linear(unittest.TestCase):
    def test_prd_constants(self):
        A, V, B = a.linear_constants(PRD_S)
        self.assertEqual(a.odd_primes_upto(79), PRD_S)
        self.assertEqual((A, V, B), (PRD_A, 34, PRD_B))
        self.assertTrue(Fraction(18955, 10000) < A < Fraction(18956, 10000))
        self.assertTrue(Fraction(3210, 100) < B < Fraction(3211, 100))

    def test_prd_inequality_at_82(self):
        # A n - B >= 3n/2 at n = 82 and the slope is positive, so for all n >= 82
        self.assertGreater(PRD_A, Fraction(3, 2))
        self.assertGreaterEqual(PRD_A * 82 - PRD_B, Fraction(3, 2) * 82)
        self.assertLess(PRD_A * 81 - PRD_B, Fraction(3, 2) * 81)

    def test_small_denominator_under_approximation(self):
        # A >= 3791/2000 suffices for both linear routes (BLUEPRINT.md, L3)
        A_low = Fraction(3791, 2000)
        self.assertLessEqual(A_low, PRD_A)
        self.assertEqual(A_low * 83 - 34 - 123, Fraction(653, 2000))
        self.assertEqual(A_low * 80 - 34 - Fraction(235, 2), Fraction(7, 50))

    def test_prd_rounded_constants_are_not_a_valid_bound(self):
        # 1.8956 rounds A up, so A n - B < 1.8956 n - 32.11 once n >= 166
        self.assertLess(PRD_A, Fraction(18956, 10000))
        self.assertLess(PRD_A * 166 - PRD_B, Fraction(18956, 10000) * 166 - Fraction(3211, 100))

    def test_thresholds(self):
        self.assertEqual(a.linear_threshold(PRD_S), 82)
        self.assertEqual(a.linear_threshold(PRD_S, refined=True), 79)
        self.assertEqual(a.linear_threshold(a.odd_primes_upto(73)), 82)
        self.assertEqual(a.linear_threshold(a.odd_primes_upto(71)), 83)

    def test_optimum(self):
        crude, S_crude = a.optimal_linear_prime_set(search_limit=1000)
        refined, S_refined = a.optimal_linear_prime_set(search_limit=1000, refined=True)
        self.assertEqual((crude, S_crude[-1]), (82, 73))
        self.assertEqual((refined, S_refined[-1]), (79, 73))

    def test_floor_bound(self):
        for n in range(0, 1000):
            self.assertTrue(a.linear_bound_holds(n, PRD_S), n)

    def test_rhs_bounds(self):
        for n in range(1, 5000):
            self.assertLessEqual(2 * a.rhs(n), 3 * n - 2, n)


class L3Window(unittest.TestCase):
    def test_superadditive(self):
        S = a.odd_primes_upto(89)
        for x in range(0, 120):
            for y in range(0, 120):
                self.assertGreaterEqual(a.G(x + y, S), a.G(x, S) + a.G(y, S))

    def test_certificate_n0_50(self):
        ok, S = a.window_certificate(50, 41)
        self.assertTrue(ok)
        self.assertEqual(S, a.odd_primes_upto(89))
        self.assertEqual(a.G(41, S), 1)
        self.assertEqual(a.smallest_window_step(50), 41)

    def test_smallest_window_prime_set(self):
        self.assertEqual(a.smallest_window_prime_set(50, 41), a.odd_primes_upto(47))
        self.assertTrue(a.window_certificate(50, 41, PRD_S)[0])
        self.assertFalse(a.window_certificate(50, 41, a.odd_primes_upto(43))[0])

    def test_no_certificate_below_50(self):
        self.assertEqual(2 * a.T(49) - 3 * 49, -1)
        self.assertIsNone(a.smallest_window_step(49))

    def test_relaxation_failures(self):
        self.assertEqual(a.superadditive_scan(50000), list(range(1, 41)) + [49])


class GeneratedFiles(unittest.TestCase):
    def test_report_is_current(self):
        text, ok = report.build(5000, 200000, 30, 60)
        self.assertTrue(ok)
        self.assertEqual((HERE / "REPORT.md").read_text(), text)

    def test_csv_is_current(self):
        self.assertEqual(
            (HERE / "valuations_n_le_81.csv").read_text(), report.valuation_csv()
        )


if __name__ == "__main__":
    unittest.main()
