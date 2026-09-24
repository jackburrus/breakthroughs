# PRD: OEIS A003161 Supercongruence for Cubed Ballot Numbers (stretch)

Sep 24, 2026 · Draft for Jack Burrus (scout survey)

## Summary

Target: `OeisA3161.conjecture` in google-deepmind/formal-conjectures, `FormalConjectures/OEIS/3161.lean:69-70` at main `2424bb4`.
The sequence is a(n) = Σ_{k ≤ n/2} (C(n,k) − C(n,k−1))³, the sum of cubed ballot numbers (Gould's S(3,n)).
The conjecture, with b(n) = a(2n−1), is b(n p^k) ≡ b(n p^(k−1)) (mod p^(3k)) for primes p ≥ 5 and n, k ≥ 1.
The OEIS entry records it as Peter Bala's (Mar 20, 2023); FC's docstring credits Z.-W. Sun (Nov 2019).

This is the stretch pick.
It is genuinely open and in the same family as A141057, so the Jacobsthal and unit-sum machinery built there carries over.
But four frontier-model attempts at $50 each did not solve it.
My numerics also show that the simple term-by-term split that proves A141057 works here only when p ∤ n.
The k ≥ 2 case needs cancellation across terms.
Start only after A046969 and A141057, and use the go/no-go gate below.

## Verification of open status

| Source | What it says | Checked |
| --- | --- | --- |
| formal-conjectures main `2424bb4` | `conjecture` is `research open` with no `formal_proof`. | File read |
| Epoch OEIS Open | Sample `oeis_3161_conjecture_1` has the same statement as FC. Four runs attempted it (three models at $50, plus Gemini 3.1 Pro): none accepted. | Isolated statement and run trees |
| AlphaProof Nexus, atlas-lean | No A003161 output. | Grep and tree |
| OEIS A003161 | Stated as a conjecture, with no proof or counterexample noted. | Live entry read |
| Literature | Sun-style supercongruences are often proved by WZ or symbolic summation, but I found no paper on this sum. The check is incomplete. | One web search |

## Problem background and proof sketch

The ballot number C(2N−1,k) − C(2N−1,k−1) equals C(2N,k)·(N−k)/N, so b(N) = Σ_{k<N} (C(2N,k)(N−k)/N)³.
Take N = mp and split the sum into k = ip (M) and the rest (R).

- For M, Jacobsthal–Kazandzidis gives C(2mp, ip) ≡ C(2m, i) to high p-adic order, so M ≈ b(m).
- For R, each term is a p-adic unit: v_p(C(2mp,k)) ≥ v_p(m) + 1 exactly cancels the 1/(mp)³.
  So R vanishes only through cancellation. Mod p this is visible: by Lucas, C(2mp−1, k−1) ≡ ±C(2m−1, ⌊(k−1)/p⌋) (mod p), and the residues in each block of p − 1 come with alternating signs.

`numerics/check.py` (exact) shows the following.

- The conjecture holds in all 115 cases with n·p^k ≤ 400, p ∈ {5, …, 23} and k ≤ 3.
- M ≡ b(m) and R ≡ 0 (mod p^(3(v_p(m)+1))) hold separately in all 55 cases with p ∤ m.
- They both fail separately in the 5 cases with p ∣ m (m = 5, 7, 14, 11, 13), even though M + R ≡ b(m) there.

So the k = 1, p ∤ n case looks provable with the A141057 tools.
The general k needs a new idea: a finer grouping by v_p(k), a WZ certificate, or a recurrence-based argument using the P-recursive recurrence in the OEIS.

## Goals and non-goals

Goals:

- Phase 1, as a partial result: b(np) ≡ b(n) (mod p³) for p ∤ n. Not enough to flip the FC tag.
- Phase 2: the full statement, if a cross-cancellation argument is found on paper first.

Non-goals:

- Anything else about S(r,n), such as Gould's divisibility problem.

## Approach

1. Reuse U, K and A from the A141057 project (unit sums, Jacobsthal–Kazandzidis, valuation bounds).
2. Prove the mod-p³ block cancellation for R when p ∤ m. The first-order terms are Σ_{r<p} r^{−j}-type unit sums; check the order to which each vanishes numerically before formalizing.
3. Gate: before writing Lean for phase 2, produce a paper proof of the p ∣ m case and check each intermediate congruence numerically with `check.py`.

## Milestones

| Step | Done when |
| --- | --- |
| A141057 machinery landed | U, K and A are available as a library |
| Phase 1 on paper, then in Lean | The p ∤ n, k = 1 lemma compiles |
| Phase 2 go/no-go | A written cross-cancellation argument passes numerical checks; otherwise shelve |

## Risks

| Risk | Likelihood | Mitigation |
| --- | --- | --- |
| No elementary argument for p ∣ m | High | The gate above; try a WZ-style or recurrence approach, or a literature search on Sun/Bala ballot supercongruences |
| Already proved in a paper we missed | Medium | Do a deeper literature pass (Guo, Zudilin, Mao, Z.-W. Sun lists) before phase 2 |
| Phase 1 alone does not change the FC status | Certain | Treat it as infrastructure, not a deliverable |

## Sources

- FC `FormalConjectures/OEIS/3161.lean` at `2424bb4`
- OEIS A003161 (Bala comment, Mar 20, 2023; recurrence by Mark van Hoeij)
- epoch-research/LeanOpenProblems-results runs attempting `oeis_3161_conjecture_1`
