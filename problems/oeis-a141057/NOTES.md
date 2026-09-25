# A141057 conjecture 2: status and proof structure

The target is `OeisA141057.conjecture2` in formal-conjectures: Bala's supercongruences
a(n p^k) ≡ a(n p^(k−1)) (mod p^(3k)) for primes p ≥ 5, for his extension of A141057 to negative n.
The plan is `PRD.md`, the Lean proof is in `lean/`, and `numerics/lemmas.py` checks every lemma statement.

## Open status, re-verified Sep 24, 2026

| Source | Finding |
| --- | --- |
| formal-conjectures main `2424bb4` (Sep 24, 19:42 UTC) | `conjecture2` is still `research open` with no `formal_proof`. `FormalConjectures/OEIS/141057.lean` is byte-identical to our pin `40a8592`. It was last touched by `6fbb54f` (the Sep 18 "modulize" chore). Main is 6 commits ahead of the pin, and none of them touch this file or `FormalConjecturesUtil`, so the pin stays and the shared tree is reused. |
| FC pull requests | No PR, open or closed, mentions 141057 apart from #5016 (added the statement, merged Aug 20) and #5594 (linked the positive-case proof, merged Sep 12). Searches for "supercongruence" and "Abelian cubes" also find #4946 (open, 43 AutoOeis conjectures) and #6008 (merged, marks five problems solved), and neither touches this file. GitHub code search for `OeisA141057` finds only the FC file. |
| Epoch AI's OEIS Open benchmark (LeanOpenProblems-results main `fd09021`, Sep 16; arXiv:2608.11941 v2) | States only the positive-n conjecture for A141057. All of its A141057 runs target that problem. |
| OEIS A141057 | Still revision 35 (Aug 20, 2026), with no later edits in the history. Bala's comment on negative n is unchanged: the extension "appears to satisfy the same supercongruences". |

Nobody has targeted the negative-index statement.

## Prior work

Epoch AI's agent proved the positive-index case (`conjecture1`) in August 2026, and formal-conjectures links that proof.

## Proof structure

The upstream statement covers both signs of n, so the proof treats a(N) and aInt(−N) side by side.
Everything reduces to one step: if p^e divides n, then aInt(n p) ≡ aInt(n) (mod p^(3e+3)).
Taking n p^j, which p^j divides, gives the conjecture with k = j + 1.

Write a summand of a(N) as C(N, k) C(k, j), cubed, and a summand of aInt(−N) as (−1)^k C(N+k−1, k) C(k, j), cubed.
The one step splits the sum over j ≤ k ≤ N p into the pairs that are both multiples of p and the rest.

1. **Absorption (A).** k C(N, k) = N C(N−1, k−1) says N divides k C(N, k). The negative twin says N divides k C(N+k−1, k).
   Since N also divides N C, it divides gcd(N, k) C. So x + y divides gcd(x, y) C(x+y, x).
2. **Vanishing (V).** If p ∤ k, then p^e ∣ N ∣ k C(N, k) forces p^e ∣ C(N, k). If p ∣ k but p ∤ j, move j into
   the first binomial first. With N = n p, every pair that is not both a multiple of p contributes a multiple of p^(3e+3).
3. **Unit squares (U).** For p ≥ 5, the squares of the units of Z/p^s sum to 0. Doubling permutes the units,
   so the sum T satisfies T = 4T, and 3 is a unit. The integers below c p^s prime to p cover each unit c times.
4. **Shifted products (D).** Let F(x) be the product of (x + a) over a < N prime to p. If p^r ∣ x and p^s ∣ N,
   then F(x) ≡ F(0) mod p^(3t), with t = min(r, s). The reflection a ↦ N − a gives F(x)² as the product of
   a(N−a) + x(x+N). Expanding to first order in y = x(x+N) leaves y times the sum of 1/(a(N−a)).
   Modulo p^t, 1/(a(N−a)) is −1/a², and the inverse squares sum to 0 by U. Then F(x) + F(0) ≡ 2F(0) (mod p)
   is prime to p and cancels.
5. **Jacobsthal–Kazandzidis (K, K⁻).** C(M+n, n) n! = (M+1)⋯(M+n). At M = b p and n = a p, split off the
   multiples of p. Comparing with the same identity at (b, a) gives C((a+b)p, ap) H(0) = C(a+b, a) H(b),
   where H(b) is the product of (bp + j) over j < ap prime to p. D gives H(b) ≡ H(0) mod p^(3u+3) when
   p^u divides a and b. The negative side runs the same argument on M(M+1)⋯(M+n−1).
6. **Per-summand congruence (P).** Index a summand by j = a, k = a+b, N = a+b+c. K (or K⁻) gives each binomial
   factor to relative precision 3u + 3, with u the valuation of a gcd. A bounds e by those gcds and the valuations
   of the small binomials. A product keeps the relative precision, and cubing adds twice the valuation,
   which reaches p^(3e+3).
7. **Summation (S, R).** S splits the triangle of indices at the multiples of p. V and P give the one step for
   n ≥ 0 and n < 0 (the sign (−1)^(ip) is (−1)^i, as p is odd). `Main.lean` applies it to n p^(k−1).

`lean/CLAUDE.md` maps these steps to files and lemma names. `lean/scripts/check.sh` builds the proof and
confirms that `A141057.conjecture2` uses only `propext`, `Classical.choice` and `Quot.sound`.
