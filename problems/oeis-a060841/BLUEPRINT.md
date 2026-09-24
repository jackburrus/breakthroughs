# Blueprint: OEIS A060841 conjecture 1

This is a human-readable proof of `OeisA60841.conjecture1`, split into lemmas that Lean provers can take one at a time.
Every number here is exact, and the numerics harness in `numerics/` checks each claim.
To rerun it, go to `numerics/` and run `python3 report.py` (output: `numerics/REPORT.md`) or `python3 -m unittest`.
Section 8 lists the steps the numerics do not confirm, or that correct the PRD.

## 0. Target and notation

The statement as merged (FormalConjectures/OEIS/60841.lean, PR #6456):

```lean
def lcmMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun i j : Fin n ↦ 1 / ((Nat.lcm (i.val + 1) (j.val + 1) : ℚ))
def integerDetN : Set ℕ := Set.Icc 1 34 ∪ {36, 38}
theorem conjecture1 :
    ∀ n : ℕ, 1 ≤ n → (((lcmMatrix n).det)⁻¹.den = 1 ↔ n ∈ integerDetN)
```

Notation (indices are 1-based, as in `i.val + 1`):

| symbol | meaning |
| --- | --- |
| `M_n` | `lcmMatrix n`, the matrix with entries `M[i][j] = 1/lcm(i, j)` for `1 ≤ i, j ≤ n` |
| `R(n)` | `(det M_n)⁻¹ ∈ ℚ` |
| `φ` | Euler's totient function |
| `N(n)` | `(n!)²` |
| `D(n)` | `∏_{k=1}^{n} φ(k)` |
| `v_ℓ(x)` | the ℓ-adic valuation of a nonzero rational `x`, for a prime ℓ |
| `T_S(n)` | `Σ_{p∈S} v₂(p−1)·⌊n/p⌋`, for a finite set S of odd primes |
| `T(n)` | `T_S(n)` with S = all odd primes `≤ n` |
| `RHS(n)` | `v₂(n!) + ⌊n/2⌋` |
| `I` | `integerDetN = [1, 34] ∪ {36, 38}` |

## 1. Lemma L1: the determinant identity

**L1.** For every `n ≥ 0`, `det M_n = D(n) / N(n)`. In particular `det M_n ≠ 0` and

    R(n) = N(n) / D(n) = ∏_{k=1}^{n} k² / φ(k).

The proof has four steps.

1. **Gauss's identity.** For `m ≥ 1`, `Σ_{d | m} φ(d) = m` (Mathlib: `Nat.sum_totient`).
2. **Factor the gcd matrix.** Let `G[i][j] = gcd(i, j)` and `A[i][d] = 1` if `d | i`, else `0`.
   The divisors of both `i` and `j` are exactly the divisors of `gcd(i, j)`, so step 1 gives

       G[i][j] = Σ_{d | gcd(i,j)} φ(d) = Σ_{d=1}^{n} A[i][d] · φ(d) · A[j][d].

   So `G = A · diag(φ(1), …, φ(n)) · Aᵀ`.
3. **Smith's determinant.** `A` is lower unitriangular: `d | i` forces `d ≤ i`, and `A[i][i] = 1`.
   So `det A = det Aᵀ = 1`, and `det G = ∏ φ(k) = D(n)`.
4. **Scale to M.** Since `gcd(i, j) · lcm(i, j) = i · j` (Mathlib: `Nat.gcd_mul_lcm`), `M[i][j] = gcd(i, j)/(i·j)`.
   So `M = Δ⁻¹ G Δ⁻¹` with `Δ = diag(1, …, n)`, and `det M = D(n) / (n!)²`.
   This is nonzero because every `φ(k) ≥ 1` for `k ≥ 1`.

**Why `det M_n ≠ 0` matters in Lean.** In Lean `(0 : ℚ)⁻¹ = 0` and `(0 : ℚ).den = 1`.
Without `det ≠ 0`, the `den = 1` side of the iff says nothing, so L1 is what makes it meaningful.

Numerics: 1/det by exact Fraction elimination equals `∏ k²/φ(k)` for n ≤ 30.
Bareiss on the integer matrix `G` gives `det G = D(n)` for n ≤ 60, and the entrywise factorization holds for n ≤ 60.
The numerators match the OEIS b-file (a(1..400)) and the file's `a_1 … a_5` tests.

## 2. Lemma V: exact valuation of R(n) at every prime

**V1 (totient valuation).** For `k ≥ 1` and a prime ℓ,

    v_ℓ(φ(k)) = [ℓ | k] · (v_ℓ(k) − 1) + Σ_{q prime, q | k} v_ℓ(q − 1).

Proof: `φ(k) = ∏_{q^e ∥ k} q^{e−1}(q − 1)`. The factor `q^{e−1}` contributes `e−1` exactly when `q = ℓ`, and each `(q − 1)` contributes `v_ℓ(q − 1)`.
Mathlib's `Nat.totient_eq_prod_factorization` states this product form (verify the name against the pinned Mathlib).

**V2 (summed).** For `n ≥ 1` and a prime ℓ, using `Σ_{k≤n} v_ℓ(k) = v_ℓ(n!)`, `#{k ≤ n : ℓ | k} = ⌊n/ℓ⌋` and `#{k ≤ n : q | k} = ⌊n/q⌋`:

    v_ℓ(D(n)) = v_ℓ(n!) − ⌊n/ℓ⌋ + Σ_{q prime ≤ n} v_ℓ(q − 1)·⌊n/q⌋
    v_ℓ(R(n)) = 2·v_ℓ(n!) − v_ℓ(D(n))
              = v_ℓ(n!) + ⌊n/ℓ⌋ − Σ_{q prime ≤ n} v_ℓ(q − 1)·⌊n/q⌋.

**V3 (the 2-adic formula).** For ℓ = 2, the `q = 2` term vanishes because `v₂(1) = 0`, so

    v₂(D(n)) = v₂(n!) − ⌊n/2⌋ + T(n)          (the PRD formula)
    v₂(R(n)) = RHS(n) − T(n).

So `R(n)` is 2-integral iff `T(n) ≤ RHS(n)`.

**Inequality version, enough for L3.** L3 only needs the lower bound

    v₂(φ(k)) ≥ [2 | k]·(v₂(k) − 1) + Σ_{odd p | k} v₂(p − 1),

and summing over k gives `v₂(D(n)) ≥ v₂(n!) − ⌊n/2⌋ + T(n)`.
This follows from `(p−1) | φ(k)` for distinct odd `p | k` (they come from coprime prime-power factors) together with `2^{v₂(k)−1} | φ(k)`.
Proving the inequality may be easier than proving the equality.

**V4 (the factorial).** `v₂(n!) = n − s₂(n)`, where `s₂` is the binary digit sum (Legendre).
So for `n ≥ 1`, `v₂(n!) ≤ n − 1`, and therefore

    2·RHS(n) ≤ 2(n − 1) + n = 3n − 2,   i.e.   RHS(n) ≤ 3n/2 − 1   (n ≥ 1).

Candidate Mathlib lemmas: `Nat.emultiplicity_two_factorial_lt` (older name `Nat.multiplicity_two_factorial_lt`) gives `v₂(n!) < n` for `n ≠ 0`, and `sub_one_mul_padicValNat_factorial` gives Legendre in digit form.

Numerics: V2 matches direct valuations of `R(n)` at every prime `≤ n + 5` for n ≤ 81.
V3 matches `v₂(R(n))` for n ≤ 5000.
The direct `Σ v₂(φ(k))` matches the PRD formula for n ≤ 2000.
V4 holds for n < 5000.

## 3. Reduction of `den = 1` to divisibility and valuations

Let `n ≥ 1`. By L1, `R(n) = N(n)/D(n)` with `N(n), D(n)` positive integers. Then:

- `R(n).den = 1 ⟺ D(n) | N(n) ⟺ v_ℓ(R(n)) ≥ 0` for every prime ℓ.
- If `v_ℓ(R(n)) < 0` for a single prime ℓ, then `R(n).den ≠ 1`.
- Only primes `ℓ ≤ n` matter: for `ℓ > n`, V2 gives `v_ℓ(R(n)) = 0`.

## 4. Lemma L2: the finite range `1 ≤ n < N0`

L2 splits `[1, N0)` into two kinds of n. The value of N0 depends on which route L3 takes (section 6).

**L2a (integer direction, 36 values).** For `n ∈ I = [1, 34] ∪ {36, 38}`, `D(n) | (n!)²`.

- Numerics: every valuation of `R(n)` is ≥ 0 for these n.
  The odd-prime valuations are all ≥ 2 for every `n ≤ 81`, so only the prime 2 is ever tight.
- The 2-adic value `v₂(R(n))` is exactly 0 at n = 31 and n = 38. These are the tight cases.
- The largest numbers involved are around `(38!)² ≈ 2.7·10⁸⁹`.
  A Lean check can decide `D(n) ∣ N(n)` directly, or compare valuations prime by prime for primes ≤ 37.

**L2b (non-integer direction).** For `n ∈ {35, 37} ∪ [39, N0)`, `T(n) > RHS(n)`.
By V3 this gives `v₂(R(n)) < 0`, so `R(n).den ≠ 1`, and none of these n is in I.

`v₂(R(n)) = RHS(n) − T(n)` near the boundary (exact, from `numerics/REPORT.md`):

| n | 28 | 29 | 30 | 31 | 32 | 33 | 34 | 35 | 36 | 37 | 38 | 39 | 40 | 41 | 42 | 43 | 44 | 45 | 46 | 47 | 48 | 49 | 50 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| v₂(R(n)) | 4 | 2 | 1 | 0 | 6 | 4 | 2 | −1 | 1 | −1 | 0 | −3 | −1 | −4 | −4 | −5 | −3 | −6 | −5 | −6 | −2 | −3 | −3 |

`numerics/valuations_n_le_81.csv` has every valuation `v_p(R(n))` for p = 2 and every odd prime p ≤ n, for n ≤ 81.
`numerics/REPORT.md` has the per-n table of `T(n)`, `RHS(n)` and the minimum odd valuation.

## 5. Lemma L3, route A: the linear floor bound (the PRD route)

Fix the PRD set of the 21 odd primes ≤ 79:

    S = {3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79}

with weights `c_p = v₂(p − 1)`:

| p | 3 | 5 | 7 | 11 | 13 | 17 | 19 | 23 | 29 | 31 | 37 | 41 | 43 | 47 | 53 | 59 | 61 | 67 | 71 | 73 | 79 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| c_p | 1 | 2 | 1 | 1 | 2 | 4 | 1 | 1 | 2 | 1 | 2 | 3 | 1 | 1 | 2 | 1 | 2 | 1 | 1 | 3 | 1 |

Exact constants (the denominator is `∏_{p∈S} p = 1608822383670336453949542277065`):

    V = Σ c_p                  = 34
    A = Σ c_p / p              = 3049629558983711743173310451026 / 1608822383670336453949542277065  ≈ 1.8955663409
    B = Σ c_p (p − 1) / p = V − A = 51650331485807727691111126969184 / 1608822383670336453949542277065 ≈ 32.1044336591
    A − 3/2                    = 1272791966956414124497994070857 / 3217644767340672907899084554130  ≈ 0.3955663409

**F (floor bound).** For all `n ≥ 0` and `p ≥ 1`: `p·⌊n/p⌋ ≥ n − (p − 1)`, i.e. `n < p·(⌊n/p⌋ + 1)` (Mathlib: `Nat.lt_mul_div_succ`).
Multiply by `c_p/p ≥ 0` and sum over S:

    T_S(n) ≥ Σ c_p (n + 1 − p)/p = A·(n + 1) − V = A·n − B      (all n ≥ 0).

**Monotonicity.** For `n ≥ 79`, every `p ∈ S` is `≤ n`, so `T(n) ≥ T_S(n)`.
In fact `T(n) ≥ T_S(n)` for every n and every set S of odd primes: a prime `p > n` contributes `⌊n/p⌋ = 0`.

Two variants, depending on how RHS(n) is bounded:

- **A-crude (PRD).** `RHS(n) < 3n/2`, from `v₂(n!) < n` and `⌊n/2⌋ ≤ n/2`. It suffices that `A·n − B ≥ 3n/2`, i.e. `n ≥ B/(A − 3/2)`.

      B/(A − 3/2) = 103300662971615455382222253938368 / 1272791966956414124497994070857 ≈ 81.1607

  So the crude variant needs **n ≥ 82**. Cleared check at n = 82: `A·83 − 34 − 123 = 534139159405251413306629935953/1608822383670336453949542277065 ≈ 0.3320 ≥ 0`.
  The slope `A − 3/2 > 0` extends this to all n ≥ 82.
- **A-refined.** `RHS(n) ≤ 3n/2 − 1` (V4, which rests on the same fact `v₂(n!) ≤ n − 1`). It suffices that `A·n − B > 3n/2 − 1`, i.e. `n > (B − 1)/(A − 3/2)`.

      (B − 1)/(A − 3/2) = 100083018204274782474323169384238 / 1272791966956414124497994070857 ≈ 78.6327

  So the refined variant needs **n ≥ 79**. Cleared check at n = 79: `A·80 − 34 − 235/2 = 93509437056386672203672442693/643528953468134581579816910826 ≈ 0.1453 > 0`.
  At n = 78 the check fails (≈ −0.25).

Then `T(n) ≥ T_S(n) ≥ A·n − B > RHS(n)`, so `v₂(R(n)) < 0` and `R(n).den ≠ 1` for every `n ≥ 82` (crude) or `n ≥ 79` (refined).

**Small-denominator option.** `A ≥ 3791/2000 = 1.8955`, and this under-approximation is enough for both variants:

- crude: `(3791/2000)·83 − 34 − 123 = 653/2000 ≥ 0`
- refined: `(3791/2000)·80 − 34 − 235/2 = 7/50 > 0`

So a prover can prove `Σ c_p/p ≥ 3791/2000` once (norm_num on 21 terms), then run `linarith` with small numbers.

**Optimality of S (no finite prime set does better with this bound).**
Adding a prime p to S changes `(A, B)` by `(a, b) = (c_p/p, c_p(p−1)/p)`, with `b/a = p − 1`.
The real threshold `t = B/(A − 3/2)` becomes `(B + b)/(A + a − 3/2)`, which is smaller iff `p − 1 < t` (crude; use `B − 1` for refined).

Suppose S is optimal, `p ∈ S`, `q < p` is an odd prime, and `q ∉ S`.
Optimality gives `p − 1 ≤ t`, since otherwise dropping p would lower t. So `q − 1 < t`, and adding q strictly lowers t, a contradiction.
So an optimal S is a set of consecutive odd primes starting at 3, and scanning those sets up to 2000 gives:

- crude: best N0 = 82, first reached by the 20 odd primes ≤ 73 (t ≈ 81.2652). S ≤ 79 (t ≈ 81.1607) and S ≤ 83 also give 82.
- refined: best N0 = 79, first reached by the odd primes ≤ 73 (t ≈ 78.6536). S ≤ 79 gives t ≈ 78.6327.

The per-set table of thresholds is in `numerics/REPORT.md`.

## 6. Lemma L3, route B: superadditive window (N0 = 50)

Let `G_S(n) = 2·T_S(n) − 3n`.

**Superadditivity.** `⌊(x + y)/p⌋ ≥ ⌊x/p⌋ + ⌊y/p⌋` and `c_p ≥ 0`, so `T_S(x + y) ≥ T_S(x) + T_S(y)`.
The `−3n` part is additive, so `G_S(x + y) ≥ G_S(x) + G_S(y)`.

**Window lemma.** Suppose `G_S(m) ≥ 0` for some `m ≥ 1`, and `G_S(n) ≥ 0` for every `n ∈ [N0, N0 + m)`. Then `G_S(n) ≥ 0` for all `n ≥ N0`.
Proof by strong induction: for `n ≥ N0 + m`, `n − m ≥ N0`, so `G_S(n) ≥ G_S(n − m) + G_S(m) ≥ 0`.

**Certificate.** Take `N0 = 50`, `m = 41`, window `[50, 90]`.

- The window can use the 14 odd primes ≤ 47. The PRD set (odd primes ≤ 79) and the odd primes ≤ 89 also work.
- With S = odd primes ≤ 89, `T_S = T` on the window. The values of `G(n) = 2T(n) − 3n` there are:

      n    : 50 51 52 53 54 55 56 57 58 59 60 61 62 63 64 65 66 67 68 69 70
      G(n) :  0  7  8  9  8 11 10 11 12 11 14 15 14 15 12 17 18 17 22 23 26
      n    : 71 72 73 74 75 76 77 78 79 80 81 82 83 84 85 86 87 88 89 90
      G(n) : 25 24 27 28 31 30 31 34 33 34 33 36 35 36 45 44 47 46 49 52

  The step value is `G(41) = 1`.
- For n ≥ 50, the window lemma then gives `T(n) ≥ T_S(n) ≥ 3n/2 > 3n/2 − 1 ≥ RHS(n)`, so `v₂(R(n)) < 0`.

**Lower limit of this relaxation.** `2T(49) − 3·49 = −1`, and `T_S ≤ T` for every S.
So no prime set proves `2T_S(n) ≥ 3n` at n = 49, and N0 = 50 is optimal for the `3n/2` relaxation.
The smallest usable step is `m = 41`, because `G(m) < 0` for every `m ≤ 40`.
Numerically, `2T(n) ≥ 3n` fails exactly for `n ∈ [1, 40] ∪ {49}` up to n = 200000.

## 7. Assembly

Let `n ≥ 1`. Choose a route, which fixes `N0 ∈ {82, 79, 50}`.

- `n < N0`: apply L2a if `n ∈ I`, and L2b otherwise. L2b covers `{35, 37} ∪ [39, N0)`, which is exactly `[1, N0) \ I`.
- `n ≥ N0`: L3 gives `R(n).den ≠ 1`, and `n ≥ 50 > 38` gives `n ∉ I`.

Tradeoff (full table in `numerics/REPORT.md`):

| route | N0 | L2 range | L2b (2-adic only) cases | extra finite work in L3 |
| --- | --- | --- | --- | --- |
| A-crude (PRD) | 82 | 1..81 | 45 | one rational inequality with 20 or 21 primes |
| A-refined | 79 | 1..78 | 42 | same inequality; uses `v₂(n!) ≤ n − 1`, which the crude variant already needs |
| B window | 50 | 1..49 | 13 | 41 window checks on [50, 90] plus `G_S(41) ≥ 0`, with 14 primes |

L2a (the 36 integer cases) is the same for every route, and so is L1.
Recommendation: A-refined costs nothing over A-crude and removes 3 cases.
Route B trades 29 L2b cases for 41 simpler window checks plus one induction.
Either B or A is cheap; pick the one whose Lean shape is easiest (a single `linarith` versus an induction plus a `decide` over a range).

## 8. Checks and flags

Confirmed by the numerics (`python3 -m unittest` in `numerics/`, 32 tests):

- The integrality set of `R(n)`, computed from the exact closed form, is exactly I for n ≤ 5000.
- The 2-adic valuation alone breaks integrality for every `n ∉ I` with `n ≤ 200000`, matching the PRD.
- All constants and thresholds in sections 5 and 6, and the n = 35 value `R(35) = 5029296746186844716050163189085401314000634765625/2` from the OEIS comment.

Flags:

1. **The PRD's rounded constants are not a valid bound as written.**
   The PRD writes `Σ ≥ 1.8956 n − 32.11`, but 1.8956 rounds A up (`A ≈ 1.895566 < 1.8956`).
   The floor bound gives only `A·n − B`, which falls below `1.8956 n − 32.11` once `n ≥ 166`.
   The inequality `T_S(n) ≥ 1.8956 n − 32.11` still holds numerically for 82 ≤ n < 200000, but F does not prove it.
   Use the exact A and B, or a rational lower bound on A such as 3791/2000, as in section 5.
2. **L1 is checked only up to n = 30 (direct determinant) and n = 60 (Smith).** Beyond that it rests on the proof in section 1, which is standard, but no Lean proof exists yet.
3. **`det ≠ 0` must be proved.** It is not a numerics issue: in Lean, `(0)⁻¹.den = 1`, so the integer direction needs L1's `det M_n ≠ 0`.
4. **Tight cases.** `v₂(R(n)) = 0` at n = 31 and n = 38, and `v₂(R(n)) = −1` at n = 35 and n = 37.
   An off-by-one in any formula shows up at these four values first, so check them explicitly in Lean.
5. **The PRD's "from n = 51 onward".** It matches the strict relaxation `2T(n) > 3n`, which holds for all n ≥ 51.
   The non-strict `2T(n) ≥ 3n`, which is all L3 needs, holds from n = 50, as section 6 uses.
6. **Nothing here is Lean-verified.** The Mathlib lemma names above are candidates to check against the pinned Mathlib version.
