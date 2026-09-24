# A141057 conjecture 2: status and Epoch reuse notes

Sep 24, 2026. Companion to `PRD.md`. The Lean project is `lean/`; its `CLAUDE.md` holds the prover rules and lemma table.

## Open status, re-verified Sep 24, 2026

| Source | Finding |
| --- | --- |
| formal-conjectures main `2424bb4` (Sep 24, 19:42 UTC) | `conjecture2` is still `research open` with no `formal_proof`. `FormalConjectures/OEIS/141057.lean` is byte-identical to our pin `40a8592`. It was last touched by `6fbb54f` (the Sep 18 "modulize" chore). Main is 6 commits ahead of the pin, and none of them touch this file or `FormalConjecturesUtil`, so the pin stays and the shared tree is reused. |
| FC pull requests | No PR, open or closed, mentions 141057 apart from #5016 (added the statement, merged Aug 20) and #5594 (linked the positive-case proof, merged Sep 12). Searches for "supercongruence" and "Abelian cubes" also find #4946 (open, 43 AutoOeis conjectures) and #6008 (merged, marks five problems solved), and neither touches this file. GitHub code search for `OeisA141057` finds only the FC file. |
| Epoch LeanOpenProblems-results main `fd09021` (Sep 16) | A141057 appears in four runs, all on the positive-n problem `oeis_a141057_supercongruence_conjecture`. Claude Opus 4.8 (`oeis-full-50usd-ant`) is accepted. Gemini 3.5 Flash (`oeis-full-50usd-gdm`) and GPT-5.5 (`oeis-full-50usd-oai`) are rejected. One run is new since the PRD: Gemini 3.1 Pro (`oeis-open-full-gemini31pro`, Sep 16), which was rejected because its file did not compile. `metadata/oeis/conjectures.json` states only the positive conjecture for A141057. |
| Epoch paper, arXiv:2608.11941 v2 | Lists only the positive-n conjecture for A141057. |
| OEIS A141057 | Still revision 35 (Aug 20, 2026), with no later edits in the history. Bala's comment on negative n is unchanged: the extension "appears to satisfy the same supercongruences". |

Nobody has targeted the negative-index statement.

## Reusing Epoch's positive-case proof

Source: `runs/oeis-full-50usd-ant-j0j0g4uzligm1k41/oeis_a141057_supercongruence_conjecture/Submission/Spec.lean` at commit `f02efd9` (the commit FC links), 978 lines, Lean v4.27.0.
Its natural-language proof is `metadata.json` (`full_proof`) in the same run directory.
Epoch's repository has no license, so read it as a map and write our own code (the PRD leaves permission as an open owner decision).
We build on Lean v4.33.1, so expect some Mathlib names to have drifted.

| Epoch (Spec.lean line) | Our lemma | Reuse |
| --- | --- | --- |
| `isUnit_unit_mul` 16, `US_zero` 22, `zmod_mul_inv` 49, `US_inv` 56, `US_inv2` 70, `isUnit_two_zmod`/`isUnit_three_zmod` 253/258 | `U_sum_inv`, `U_sum_inv_sq` | The argument is sign-free and carries over unchanged. Doubling permutes the units of `ZMod m`, and `2⁻¹ - 1`, `2⁻² - 1` are units when `p ≥ 5`. |
| `sum_block` 91, `sum_zmod_eq_sum_range` 118, `RED` 127, `sumAinv` 263, `sumAinv2` 267 | same | Reduces a sum over `range N` filtered by `p ∤ a` to `N / p^s` copies of a sum over units. `sumAinv`/`sumAinv2` are our U statements, with `a⁻¹ * a⁻¹` in place of `a⁻¹ ^ 2`. |
| `zmod_mul_inv'` 273, `prod_zmod_inv` 279, `key2` 292, `zmod_unit_mul_inv` 323, `prod_compl_eq` 326, `dvd_e2` 338 | `D_shiftProd` (the `e₂` bound) | Unchanged. `key2` is `(∑ x)² = ∑ x² + 2 ∑_{pairs}`. |
| `neg_zmod_inv` 376, `dvd_T1` 384 | `D_shiftProd` (the `e₁` bound) | Unchanged. It pairs `c` with `L p - c`. |
| `prod_const_add_expand` 499, `dvd_Delta` 511 | `D_shiftProd` | Same statement. Epoch takes the products in ℤ (`(B*p:ℤ) + a`); ours are ℕ products cast to ℤ, which fits K's factorial identities. |
| `gg` 156, `prod_Icc_id_eq_fac` 158, `fac_split` 163, `F3` 190, `gg_add` 223, `kazan` 563 | `K_jacobsthal` | Same statement. We write the exponent as `v + 3 + 3 * min` where Epoch writes `v + (3 + 3 * min)`. |
| `padicVal_choose_ge` 646 | `A_pos` | Same statement. |
| `kummerBin` 661 | `A_kummer` | Same statement. |
| `perterm` 671 | `P_cube` + `P_pos` | Lines 685–796 are the sign-free algebra, which we isolated as `P_cube` (it has no binomials in it). Epoch orders the multinomial as `C(mp, ip) C((m-i)p, jp)`. We follow upstream's order `C(mp, ip) C(ip, lp)`, so K is applied at `(m, i)` and `(i, l)`, and the second side condition uses `A_pos (m, i)` + `A_kummer (l, i - l)`. |
| `multinom_symm` 810 | Mathlib `Nat.choose_mul` | Mathlib now covers the positive symmetry. The negative one is the new `A_symm_neg`. |
| `gt` 805, `Dom` 807, `A141057_eq` 834 | none | Epoch rewrote a(N) as a multinomial sum over pairs `(r, s)`. We do not need this: upstream's `aInt` is already the triangle `∑_k ∑_{j ≤ k}`, and `S_split` works on it directly for both signs. |
| `Claim1` 847 | `V_pos` | Same idea. Ours is uncubed and needs no range hypothesis. |
| `red` 886 | `R_pos` | Same shape, but the split goes through `S_split` rather than an image of `Dom m`. |
| main theorem 955 | `R_dvd` | Same reduction `m = n p^(k-1)`, now over ℤ via `R_oneStep`. |

New, with no Epoch counterpart: `KNeg_jacobsthal`, `A_neg`, `A_symm_neg`, `V_neg`, `P_neg`, `R_neg`, `R_oneStep` (the sign split), and the generic `S_split`.
The reusable part (U, D, K, about lines 16–645 of Spec.lean) is also the hardest.

## Proof route for negative indices

For `m ≥ 1`, `aInt(-m) = ∑_{k ≤ m} ∑_{j ≤ k} (-1)^k (C(m+k-1, k) C(k, j))³`.
At `N = m p`, the non-multiple pairs vanish modulo `p^(3 (v_p m + 1))` by `V_neg`, because `k C(N+k-1, k) = N C(N+k-1, k-1)`.
The multiple pairs `(i p, l p)` match the `(i, l)` terms of `aInt(-m)` by `P_neg`, because `(-1)^(i p) = (-1)^i`.
`P_neg` needs `KNeg_jacobsthal`, which comes from `K_jacobsthal` at `(m + i, i)` and the identity `(m + i) C(m + i - 1, i) = m C(m + i, i)`.
The truncation `k ≤ m p` is compatible with the split: `p ∣ k ≤ m p` if and only if `k = i p` with `i ≤ m`.
`../numerics/lemmas.py` checks every lemma statement in the general form stated in Lean.
