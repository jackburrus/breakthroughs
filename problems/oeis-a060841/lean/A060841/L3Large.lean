import A060841.Defs
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# L3: uniform 2-adic bound for `n ≥ threshold`

For `n ≥ threshold` the 2-adic valuation of `∏ φ(k)` exceeds that of `(n!)²`, so the
closed form is not an integer. See `../BLUEPRINT.md` §2 and §5–6: use the exact constants
(or `A ≥ 3791/2000`), not the PRD's rounded 1.8956 and 32.11.

Route A (crude) of the blueprint, with the 21 odd primes `≤ 79` and the weights `c_p ≤ v₂(p - 1)`:

1. per `k ≥ 1`, `v₂(k) + Σ_{p ∈ S, p ∣ k} c_p ≤ v₂(φ k) + [2 ∣ k]` (from Euler's product formula);
2. summed over `k ≤ n`: `v₂(n!) + Σ_{p ∈ S} c_p ⌊n/p⌋ ≤ v₂(∏ φ k) + ⌊n/2⌋`;
3. `v₂(n!) < n` and the floor bound `Σ c_p ⌊n/p⌋ ≥ n + ⌊n/2⌋` for `n ≥ 82` (via `A ≥ 3791/2000`),
   so `v₂(∏ φ k) > 2 v₂(n!)` and `∏ φ k ∤ (n!)²`.
-/

namespace A060841

open Finset

/-- The odd primes `≤ 79` (the PRD set `S`, BLUEPRINT §5). -/
def primesS : Finset ℕ :=
  {3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79}

/-- `c_p = v₂(p - 1)` for `p ∈ primesS` (BLUEPRINT §5 table). -/
def wt (p : ℕ) : ℕ :=
  if p = 17 then 4 else if p = 41 ∨ p = 73 then 3
  else if p = 5 ∨ p = 13 ∨ p = 29 ∨ p = 37 ∨ p = 53 ∨ p = 61 then 2 else 1

theorem primesS_spec : ∀ p ∈ primesS, p.Prime ∧ 2 ^ wt p ∣ p - 1 := by
  decide +kernel

/-- `A = Σ c_p / p ≥ 3791/2000` (BLUEPRINT §5, small-denominator option). -/
theorem sum_wt_div : (3791 : ℚ) / 2000 ≤ ∑ p ∈ primesS, (wt p : ℚ) / p := by
  decide +kernel

theorem sum_wt : ∑ p ∈ primesS, (wt p : ℚ) = 34 := by
  decide +kernel

/-- Step 1: the 2-adic valuation of `φ k`, bounded below through Euler's product formula. -/
theorem two_adic_totient (k : ℕ) (hk : k ≠ 0) :
    k.factorization 2 + ∑ p ∈ primesS, (if p ∣ k then wt p else 0)
      ≤ (Nat.totient k).factorization 2 + (if 2 ∣ k then 1 else 0) := by
  have hpf : ∀ p ∈ k.primeFactors, p ≠ 0 := fun p hp => (Nat.prime_of_mem_primeFactors hp).ne_zero
  have hpf1 : ∀ p ∈ k.primeFactors, p - 1 ≠ 0 := fun p hp => by
    have := (Nat.prime_of_mem_primeFactors hp).two_le; omega
  have h := congrArg (fun m => m.factorization 2) (Nat.totient_mul_prod_primeFactors k)
  rw [Nat.factorization_mul (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hk)).ne'
      (prod_ne_zero_iff.mpr hpf),
    Nat.factorization_mul hk (prod_ne_zero_iff.mpr hpf1),
    Nat.factorization_prod hpf, Nat.factorization_prod hpf1] at h
  simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.coe_finsetSum, Finset.sum_apply] at h
  -- the primes of `k` contribute exactly `[2 ∣ k]` at 2
  have h2 : ∑ p ∈ k.primeFactors, p.factorization 2 = if 2 ∣ k then 1 else 0 := by
    rw [sum_congr rfl fun p hp => by
      rw [(Nat.prime_of_mem_primeFactors hp).factorization, Finsupp.single_apply]]
    rw [sum_ite_eq']
    simp [Nat.prime_two, hk]
  -- the primes of `S` dividing `k` are among the prime factors of `k`
  have hS : ∑ p ∈ primesS, (if p ∣ k then wt p else 0)
      ≤ ∑ p ∈ k.primeFactors, (p - 1).factorization 2 := by
    rw [← sum_filter]
    calc ∑ p ∈ primesS with p ∣ k, wt p
        ≤ ∑ p ∈ primesS with p ∣ k, (p - 1).factorization 2 := by
          apply sum_le_sum
          intro p hp
          obtain ⟨hpS, -⟩ := mem_filter.mp hp
          obtain ⟨pp, hdvd⟩ := primesS_spec p hpS
          have : p - 1 ≠ 0 := by have := pp.two_le; omega
          exact (Nat.prime_two.pow_dvd_iff_le_factorization this).mp hdvd
      _ ≤ ∑ p ∈ k.primeFactors, (p - 1).factorization 2 := by
          apply sum_le_sum_of_subset
          intro p hp
          obtain ⟨hpS, hpk⟩ := mem_filter.mp hp
          exact Nat.mem_primeFactors.mpr ⟨(primesS_spec p hpS).1, hpk, hk⟩
  omega

theorem Icc_one_eq_Ioc (n : ℕ) : Icc 1 n = Ioc 0 n := by
  ext k; simp only [mem_Icc, mem_Ioc]; omega

theorem prod_Ioc_id (n : ℕ) : ∏ k ∈ Ioc 0 n, k = n.factorial := by
  rw [← Finset.prod_Ico_id_eq_factorial]
  rfl

/-- Step 2: summed over `k ≤ n`. -/
theorem two_adic_prod_totient (n : ℕ) :
    n.factorial.factorization 2 + ∑ p ∈ primesS, wt p * (n / p)
      ≤ (∏ k ∈ Icc 1 n, Nat.totient k).factorization 2 + n / 2 := by
  rw [Icc_one_eq_Ioc]
  have hk : ∀ k ∈ Ioc 0 n, k ≠ 0 := fun k hk => by simp at hk; omega
  have hφ : ∀ k ∈ Ioc 0 n, Nat.totient k ≠ 0 := fun k hk' =>
    (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (hk k hk'))).ne'
  have hsum := sum_le_sum fun k hk' => two_adic_totient k (hk k hk')
  rw [sum_add_distrib, sum_add_distrib] at hsum
  rw [← prod_Ioc_id, Nat.factorization_prod_apply hk, Nat.factorization_prod_apply hφ]
  have hdiv : ∀ p, ∑ k ∈ Ioc 0 n, (if p ∣ k then 1 else 0) = n / p := fun p => by
    rw [sum_boole]; exact_mod_cast Nat.Ioc_filter_dvd_card_eq_div n p
  have hswap : ∑ k ∈ Ioc 0 n, ∑ p ∈ primesS, (if p ∣ k then wt p else 0)
      = ∑ p ∈ primesS, wt p * (n / p) := by
    rw [sum_comm]
    refine sum_congr rfl fun p _ => ?_
    rw [← hdiv p, mul_sum]
    exact sum_congr rfl fun k _ => by split_ifs <;> simp
  rw [hswap, hdiv 2] at hsum
  exact hsum

/-- Step 3: the floor bound (BLUEPRINT §5, route A with `A ≥ 3791/2000`). -/
theorem floor_bound (n : ℕ) (hn : 82 ≤ n) : n + n / 2 ≤ ∑ p ∈ primesS, wt p * (n / p) := by
  have hp : ∀ p ∈ primesS, ((wt p : ℚ) / p) * (n + 1) - wt p ≤ (wt p : ℚ) * ((n / p : ℕ) : ℚ) :=
    fun p hpS => by
      have pp := (primesS_spec p hpS).1
      have hp0 : (0 : ℚ) < p := by exact_mod_cast pp.pos
      have hfl : n + 1 ≤ p * (n / p) + p := by
        have := Nat.div_add_mod n p; have := Nat.mod_lt n pp.pos; nlinarith
      have hfl' : ((n : ℚ) + 1) ≤ p * ((n / p : ℕ) : ℚ) + p := by exact_mod_cast hfl
      have hw : (0 : ℚ) ≤ wt p := by positivity
      rw [div_mul_eq_mul_div, div_sub' hp0.ne', div_le_iff₀ hp0]
      nlinarith
  have hsum := sum_le_sum hp
  rw [sum_sub_distrib, ← sum_mul, sum_wt] at hsum
  have hA := sum_wt_div
  have hn' : (82 : ℚ) ≤ n := by exact_mod_cast hn
  have h2 : (2 : ℚ) * ((n / 2 : ℕ) : ℚ) ≤ n := by exact_mod_cast Nat.mul_div_le n 2
  have hmul : (3791 : ℚ) / 2000 * (n + 1) ≤ (∑ p ∈ primesS, (wt p : ℚ) / p) * (n + 1) :=
    mul_le_mul_of_nonneg_right hA (by positivity)
  have key : ((n + n / 2 : ℕ) : ℚ) ≤ ((∑ p ∈ primesS, wt p * (n / p) : ℕ) : ℚ) := by
    push_cast
    linarith
  exact_mod_cast key

theorem closedForm_eq (n : ℕ) :
    closedForm n = ((n.factorial ^ 2 : ℕ) : ℚ) / ((∏ k ∈ Icc 1 n, Nat.totient k : ℕ) : ℚ) := by
  rw [closedForm, prod_div_distrib, Icc_one_eq_Ioc, ← prod_Ioc_id]
  push_cast
  rw [prod_pow]

theorem L3_large (n : ℕ) (hn : threshold ≤ n) : (closedForm n).den ≠ 1 := by
  have hn82 : 82 ≤ n := hn
  have hD : ∏ k ∈ Icc 1 n, Nat.totient k ≠ 0 := prod_ne_zero_iff.mpr fun k hk => by
    simp at hk; exact (Nat.totient_pos.mpr (by omega)).ne'
  rw [closedForm_eq, ne_eq, Rat.den_div_natCast_eq_one_iff _ _ hD]
  intro hdvd
  have hle := (Nat.factorization_le_iff_dvd hD (by positivity)).mpr hdvd 2
  rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul] at hle
  have hfac : n.factorial.factorization 2 < n := by
    rw [Nat.factorization_def _ Nat.prime_two]
    exact padicValNat_factorial_lt_of_ne_zero 2 (by omega)
  have h1 := two_adic_prod_totient n
  have h2 := floor_bound n hn82
  omega

end A060841
