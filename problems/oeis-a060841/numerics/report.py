"""Regenerate REPORT.md and valuations_n_le_81.csv from the exact harness.

Usage (standard library only):

    python3 report.py                      # print the report to stdout
    python3 report.py --write              # also rewrite REPORT.md and the CSV
    python3 report.py --max-n 10000 --scan-n 1000000
"""

import argparse
import csv
import io
from fractions import Fraction
from math import gcd, prod
from pathlib import Path

import a060841 as a

HERE = Path(__file__).resolve().parent
L2_LIMIT = 81


def read_bfile(path=HERE / "data" / "b060841.txt"):
    """{n: a(n)} from the OEIS b-file (numerators of R(n))."""
    terms = {}
    for line in path.read_text().splitlines():
        parts = line.split()
        if len(parts) == 2 and not line.startswith("#"):
            terms[int(parts[0])] = int(parts[1])
    return terms


def fmt_fraction(x):
    return f"{x.numerator}/{x.denominator}" if x.denominator != 1 else str(x.numerator)


def approx(x, digits=6):
    return f"{float(x):.{digits}f}"


def section_l1(out, det_n, bareiss_n):
    out.append("## L1: determinant identity\n")
    mismatches = [
        n
        for n in range(1, det_n + 1)
        if 1 / a.det_fraction(a.lcm_matrix(n)) != a.inverse_det_closed_form(n)
    ]
    out.append(
        f"- Gaussian elimination over Fraction on M_n, n = 1..{det_n}: "
        f"1/det M_n equals prod k^2/phi(k) for every n. Mismatches: {mismatches or 'none'}."
    )
    phi = a.totients_upto(bareiss_n)
    smith = [
        n
        for n in range(1, bareiss_n + 1)
        if a.det_bareiss(a.gcd_matrix(n)) != prod(phi[1 : n + 1])
    ]
    out.append(
        f"- Bareiss on the integer gcd matrix G_n, n = 1..{bareiss_n}: "
        f"det G_n = prod phi(k) (Smith). Mismatches: {smith or 'none'}."
    )
    factor = [n for n in range(1, bareiss_n + 1) if not _factorization_holds(n, phi)]
    out.append(
        f"- Entrywise factorization G = A diag(phi) A^T with A[i][d] = [d | i], "
        f"n = 1..{bareiss_n}. Failures: {factor or 'none'}.\n"
    )
    return not mismatches and not smith and not factor


def _factorization_holds(n, phi):
    return all(
        sum(phi[d] for d in range(1, n + 1) if i % d == 0 and j % d == 0) == gcd(i, j)
        for i in range(1, n + 1)
        for j in range(1, n + 1)
    )


def section_integrality(out, max_n, scan_n):
    out.append("## Integrality set from the exact closed form\n")
    bfile = read_bfile()
    integral, bfile_bad, v2_bad = [], [], []
    primes = a.primes_upto(max_n)
    for n, value in a.inverse_det_sequence(max_n):
        if value.denominator == 1:
            integral.append(n)
        if n in bfile and bfile[n] != value.numerator:
            bfile_bad.append(n)
        if a.vp(2, value) != a.rhs(n) - a.T(n, primes):
            v2_bad.append(n)
    ok_set = set(integral) == a.INTEGER_SET
    out.append(
        f"- R(n) = prod k^2/phi(k) computed exactly in lowest terms for n = 1..{max_n}. "
        f"Integer exactly for n in {_ranges(integral)}. "
        f"Matches integerDetN = [1,34] ∪ {{36,38}}: {'yes' if ok_set else 'NO'}."
    )
    out.append(
        f"- Numerators agree with the OEIS b-file a(1..{max(bfile)}): "
        f"{'yes' if not bfile_bad else 'NO, at ' + str(bfile_bad)}."
    )
    out.append(
        f"- v2(R(n)) = RHS(n) - T(n) for every n <= {max_n}: "
        f"{'yes' if not v2_bad else 'NO, at ' + str(v2_bad)}."
    )
    phi_bad = [
        n
        for n in range(1, min(max_n, 2000) + 1)
        if a.v2_totient_product_direct(n) != a.v2_totient_product_formula(n)
    ]
    out.append(
        f"- v2(prod phi(k)) direct sum vs the PRD formula, n = 1..{min(max_n, 2000)}: "
        f"{'equal' if not phi_bad else 'DIFFER at ' + str(phi_bad)}."
    )
    two_adic_integral = a.two_adic_failure_scan(scan_n)
    relax = a.superadditive_scan(scan_n)
    out.append(
        f"- 2-adic scan to n = {scan_n}: T(n) <= RHS(n) (2-integral) exactly for n in "
        f"{_ranges(two_adic_integral)}; so v2(R(n)) < 0 for every other n <= {scan_n}."
    )
    out.append(
        f"- The 3n/2 relaxation 2 T(n) >= 3n fails exactly for n in {_ranges(relax)} "
        f"(n <= {scan_n}).\n"
    )
    return (
        ok_set
        and not bfile_bad
        and not v2_bad
        and not phi_bad
        and set(two_adic_integral) == a.INTEGER_SET
    )


def _ranges(ns):
    ns = sorted(ns)
    if not ns:
        return "{}"
    parts, start, prev = [], ns[0], ns[0]
    for n in ns[1:] + [None]:
        if n is not None and n == prev + 1:
            prev = n
            continue
        parts.append(f"[{start},{prev}]" if prev > start else str(start))
        if n is not None:
            start = prev = n
    return "{" + ", ".join(parts) + "}"


def section_l2(out):
    out.append(f"## L2: every valuation for n <= {L2_LIMIT}\n")
    out.append(
        "Full per-prime table: `valuations_n_le_81.csv` (v_p(R(n)) for p = 2 and every "
        "odd prime p <= n; primes p > n have v_p = 0).\n"
    )
    out.append(
        "| n | T(n) | RHS(n) | v2(R(n)) | min odd v_p (at p) | 2T(n) - 3n | integer |"
    )
    out.append("|---|---|---|---|---|---|---|")
    ok = True
    for n in range(1, L2_LIMIT + 1):
        odd = a.odd_prime_valuations(n)
        v2 = a.rhs(n) - a.T(n)
        if odd:
            p_min = min(odd, key=lambda p: (odd[p], p))
            odd_cell = f"{odd[p_min]} ({p_min})"
        else:
            odd_cell = "-"
        integer = v2 >= 0 and all(v >= 0 for v in odd.values())
        ok &= integer == (n in a.INTEGER_SET)
        ok &= all(v >= 0 for v in odd.values())
        out.append(
            f"| {n} | {a.T(n)} | {a.rhs(n)} | {v2} | {odd_cell} | "
            f"{2 * a.T(n) - 3 * n} | {'yes' if integer else 'no'} |"
        )
    out.append("")
    out.append(
        "Every odd-prime valuation for n <= 81 is >= 0 (the minimum is listed), so for "
        "n <= 81 integrality is decided by v2 alone.\n"
    )
    return ok


def valuation_csv():
    primes = a.primes_upto(L2_LIMIT)
    buf = io.StringIO()
    writer = csv.writer(buf, lineterminator="\n")
    writer.writerow(["n"] + [f"v{p}" for p in primes])
    for n in range(1, L2_LIMIT + 1):
        value = a.inverse_det_closed_form(n)
        row = [n]
        for p in primes:
            v = a.valuation_formula(p, n)
            assert v == a.vp(p, value)
            row.append(v)
        writer.writerow(row)
    return buf.getvalue()


def section_l3(out):
    out.append("## L3: the linear floor bound\n")
    out.append(
        "T_S(n) >= A n - B with A = sum_{p in S} v2(p-1)/p, V = sum v2(p-1), "
        "B = sum v2(p-1)(p-1)/p = V - A. "
        "Crude: RHS(n) < 3n/2, need A n - B >= 3n/2. "
        "Refined: RHS(n) <= 3n/2 - 1, need A n - B > 3n/2 - 1.\n"
    )
    for label, S in (
        ("PRD set: the 21 odd primes <= 79", a.odd_primes_upto(79)),
        (
            "Smallest set reaching N0 = 82: the 20 odd primes <= 73",
            a.odd_primes_upto(73),
        ),
    ):
        A, V, B = a.linear_constants(S)
        slope = A - a.THREE_HALVES
        out.append(f"### {label}\n")
        out.append(f"- S = {S}")
        out.append(f"- weights v2(p-1) = {[a.vp(2, p - 1) for p in S]}, V = {V}")
        out.append(f"- A = {fmt_fraction(A)} ≈ {approx(A, 10)}")
        out.append(f"- B = V - A = {fmt_fraction(B)} ≈ {approx(B, 10)}")
        out.append(f"- A - 3/2 = {fmt_fraction(slope)} ≈ {approx(slope, 10)}")
        out.append(
            f"- crude threshold B/(A - 3/2) ≈ {approx(B / slope)} → N0 = "
            f"{a.linear_threshold(S)}; refined (B-1)/(A - 3/2) ≈ "
            f"{approx((B - 1) / slope)} → N0 = {a.linear_threshold(S, refined=True)}"
        )
        at82 = A * 82 - B - Fraction(3, 2) * 82
        out.append(
            f"- slack at n = 82 (crude): A·82 - B - 123 = {fmt_fraction(at82)} ≈ {approx(at82)}\n"
        )
    out.append("### Threshold by prefix set S = odd primes <= P\n")
    out.append("| P | A | B | crude N0 | refined N0 |")
    out.append("|---|---|---|---|---|")
    for P in a.odd_primes_upto(113):
        S = a.odd_primes_upto(P)
        A, _, B = a.linear_constants(S)
        crude = a.linear_threshold(S)
        refined = a.linear_threshold(S, refined=True)
        out.append(
            f"| {P} | {approx(A)} | {approx(B)} | {crude or '-'} | {refined or '-'} |"
        )
    crude_best = a.optimal_linear_prime_set()
    refined_best = a.optimal_linear_prime_set(refined=True)
    out.append("")
    out.append(
        f"Best over all prefixes up to 2000 (and hence over all finite S, by the "
        f"exchange argument in BLUEPRINT.md): crude N0 = {crude_best[0]} "
        f"(first reached at P = {crude_best[1][-1]}), refined N0 = {refined_best[0]} "
        f"(first reached at P = {refined_best[1][-1]}).\n"
    )
    return crude_best[0] == 82 and refined_best[0] == 79


def section_window(out):
    out.append("## L3': superadditive window argument\n")
    out.append(
        "G_S(n) = 2 T_S(n) - 3n is superadditive. If G_S(m) >= 0 and G_S(n) >= 0 on "
        "[N0, N0 + m), then G_S(n) >= 0 for all n >= N0, so T(n) >= 3n/2 > RHS(n).\n"
    )
    full49 = 2 * a.T(49) - 3 * 49
    out.append(
        f"- Lower limit: 2 T(49) - 3·49 = {full49} < 0 and T_S <= T for every S, so no "
        f"prime set proves 2 T_S(n) >= 3n at n = 49. Any N0 for this relaxation is >= 50."
    )
    out.append("")
    out.append("| N0 | smallest step m | window | size of S (odd primes < N0 + m) |")
    out.append("|---|---|---|---|")
    ok = True
    for n0 in (50, 51, 55, 60, 70, 79, 82):
        m = a.smallest_window_step(n0)
        if m is None:
            ok = False
            out.append(f"| {n0} | none | - | - |")
            continue
        _, S = a.window_certificate(n0, m)
        out.append(f"| {n0} | {m} | [{n0}, {n0 + m - 1}] | {len(S)} |")
    out.append("")
    out.append(
        "The smallest m with G(m) >= 0 is 41 (G(41) = 1), so the window is always 41 "
        "values long. No N0 <= 49 has a certificate.\n"
    )
    small = a.smallest_window_prime_set(50, 41)
    out.append(
        f"- Smallest prefix set certifying (N0, m) = (50, 41): the {len(small)} odd "
        f"primes <= {small[-1]}. The PRD set (odd primes <= 79) also certifies it: "
        f"{a.window_certificate(50, 41, a.odd_primes_upto(79))[0]}."
    )
    window = ", ".join(
        f"{n}:{a.G(n, a.odd_primes_upto(89))}" for n in range(50, 91)
    )
    out.append(f"- G(n) = 2 T(n) - 3n on the window (S = odd primes <= 89): {window}.\n")
    ok &= small == a.odd_primes_upto(47)
    ok &= a.smallest_window_step(49) is None and a.smallest_window_step(50) == 41
    return ok


def section_tradeoff(out):
    out.append("## Tradeoff: N0 against the finite check\n")
    out.append(
        "L2 must decide integrality for 1 <= n < N0. For n in [1,34] ∪ {36,38} that "
        "needs every prime (divisibility of (n!)^2 by prod phi(k)); for n in "
        "{35, 37} ∪ [39, N0) only the 2-adic inequality T(n) > RHS(n).\n"
    )
    out.append(
        "| route | N0 | L2 range | 2-adic-only L2 cases | extra finite work in L3 |"
    )
    out.append("|---|---|---|---|---|")
    rows = (
        ("linear, crude (PRD)", 82, "S = 20 or 21 odd primes, one rational inequality"),
        (
            "linear, refined (v2(n!) <= n-1)",
            79,
            "S = 20 or 21 odd primes, one rational inequality",
        ),
        (
            "superadditive window",
            50,
            "G_S >= 0 on [50, 90] plus G_S(41) >= 0, S = 14 odd primes <= 47 suffice",
        ),
    )
    for label, n0, extra in rows:
        two_adic = 2 + max(0, n0 - 39)
        out.append(f"| {label} | {n0} | 1..{n0 - 1} | {two_adic} | {extra} |")
    out.append("")


def build(max_n, scan_n, det_n, bareiss_n):
    out = [
        "# A060841 numerics report\n",
        "Generated by `python3 report.py --write`; do not edit by hand. All arithmetic is "
        "exact (int and Fraction). Notation as in ../BLUEPRINT.md.\n",
    ]
    checks = {
        "L1": section_l1(out, det_n, bareiss_n),
        "integrality": section_integrality(out, max_n, scan_n),
        "L2": section_l2(out),
        "L3 linear": section_l3(out),
        "L3 window": section_window(out),
    }
    section_tradeoff(out)
    out.append("## Summary\n")
    for name, ok in checks.items():
        out.append(f"- {name}: {'confirmed' if ok else 'NOT CONFIRMED'}")
    out.append("")
    return "\n".join(out), all(checks.values())


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--max-n", type=int, default=5000, help="closed-form range")
    parser.add_argument("--scan-n", type=int, default=200000, help="2-adic scan range")
    parser.add_argument("--det-n", type=int, default=30, help="Fraction det range")
    parser.add_argument(
        "--bareiss-n", type=int, default=60, help="gcd-matrix det range"
    )
    parser.add_argument(
        "--write", action="store_true", help="rewrite REPORT.md and CSV"
    )
    args = parser.parse_args()
    text, ok = build(args.max_n, args.scan_n, args.det_n, args.bareiss_n)
    print(text)
    if args.write:
        (HERE / "REPORT.md").write_text(text)
        (HERE / "valuations_n_le_81.csv").write_text(valuation_csv())
    raise SystemExit(0 if ok else 1)


if __name__ == "__main__":
    main()
