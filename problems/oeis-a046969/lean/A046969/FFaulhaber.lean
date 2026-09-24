import A046969.Defs
import Mathlib.Data.Rat.Lemmas

/-!
# F: Faulhaber modulo `ℓ²`

`S_m(ℓ) ≡ ℓ·B_m (mod ℓ²)` in the `ℓ`-integral sense, for a prime `ℓ`, even `m ≥ 4` and
`ℓ ∤ m + 1`. From `sum_range_pow`: the `i = m` term is `ℓ·B_m`, the `i = m - 1` term vanishes
(`B_{m-1} = 0`), and every other term is `ℓ^{≥3}·B_i·C(m+1, i)/(m+1)` with `v_ℓ(B_i) ≥ -1`
(von Staudt–Clausen for even `i`, `B_1 = -1/2`, `B_i = 0` for odd `i > 1`) and `ℓ ∤ m + 1`.
See `../PRD.md`, Approach step 2.
-/

namespace A046969

namespace FFaulhaber

/-- `x` is `ℓ`-integral: `ℓ` does not divide its denominator. -/
def Integral (ℓ : ℕ) (x : ℚ) : Prop := ¬ ℓ ∣ x.den

variable {ℓ : ℕ}

theorem Integral.add (hℓ : ℓ.Prime) {x y : ℚ} (hx : Integral ℓ x) (hy : Integral ℓ y) :
    Integral ℓ (x + y) := fun h ↦
  (hℓ.dvd_mul.mp (h.trans (Rat.add_den_dvd x y))).elim hx hy

theorem Integral.sub (hℓ : ℓ.Prime) {x y : ℚ} (hx : Integral ℓ x) (hy : Integral ℓ y) :
    Integral ℓ (x - y) := fun h ↦
  (hℓ.dvd_mul.mp (h.trans (Rat.sub_den_dvd x y))).elim hx hy

theorem Integral.mul (hℓ : ℓ.Prime) {x y : ℚ} (hx : Integral ℓ x) (hy : Integral ℓ y) :
    Integral ℓ (x * y) := fun h ↦
  (hℓ.dvd_mul.mp (h.trans (Rat.mul_den_dvd x y))).elim hx hy

theorem Integral.intCast (hℓ : ℓ.Prime) (n : ℤ) : Integral ℓ n := by
  simp [Integral, hℓ.ne_one]

theorem Integral.natCast (hℓ : ℓ.Prime) (n : ℕ) : Integral ℓ n := by
  simp [Integral, hℓ.ne_one]

theorem Integral.inv_natCast {n : ℕ} (hn : ¬ ℓ ∣ n) : Integral ℓ (n : ℚ)⁻¹ := by
  unfold Integral
  rw [Rat.inv_natCast_den]
  split_ifs <;> simp_all

theorem Integral.sum (hℓ : ℓ.Prime) {ι : Type*} (s : Finset ι) (f : ι → ℚ)
    (h : ∀ i ∈ s, Integral ℓ (f i)) : Integral ℓ (∑ i ∈ s, f i) :=
  Finset.sum_induction f (Integral ℓ) (fun _ _ ↦ Integral.add hℓ)
    (by exact_mod_cast Integral.natCast hℓ 0) h

/-- `v_ℓ(B_i) ≥ -1`: `ℓ·B_i` is `ℓ`-integral for every `i`. -/
theorem integral_mul_bernoulli (hℓ : ℓ.Prime) (i : ℕ) : Integral ℓ (ℓ * bernoulli i) := by
  rcases Nat.even_or_odd i with ⟨k, rfl⟩ | hodd
  · -- von Staudt–Clausen: `B_{2k} = z - ∑ 1/r` over primes `r` with `r - 1 ∣ 2k`
    obtain ⟨z, hz⟩ := Bernoulli.vonStaudt_clausen k
    have hB : (ℓ : ℚ) * bernoulli (k + k) = ℓ * z - ∑ r ∈ Finset.range (2 * k + 2) with
        r.Prime ∧ (r - 1) ∣ 2 * k, (ℓ : ℚ) * (r : ℚ)⁻¹ := by
      rw [← two_mul, ← Finset.mul_sum, ← mul_sub, hz]
      simp
    rw [hB]
    refine Integral.sub hℓ (Integral.mul hℓ (Integral.natCast hℓ ℓ) (Integral.intCast hℓ z)) ?_
    refine Integral.sum hℓ _ _ fun r hr ↦ ?_
    have hr : r.Prime := (Finset.mem_filter.mp hr).2.1
    by_cases hrℓ : r = ℓ
    · subst hrℓ
      rw [mul_inv_cancel₀ (by exact_mod_cast hr.ne_zero)]
      exact_mod_cast Integral.natCast hℓ 1
    · exact Integral.mul hℓ (Integral.natCast hℓ ℓ) (Integral.inv_natCast fun h ↦
        hrℓ ((Nat.prime_dvd_prime_iff_eq hℓ hr).mp h).symm)
  · by_cases hi : i = 1
    · subst hi
      by_cases hℓ2 : ℓ = 2
      · subst hℓ2
        simp only [Integral, bernoulli_one]
        norm_num
      · have hB : (ℓ : ℚ) * bernoulli 1 = ((-ℓ : ℤ) : ℚ) * ((2 : ℕ) : ℚ)⁻¹ := by
          rw [bernoulli_one]; push_cast; ring
        rw [hB]
        exact Integral.mul hℓ (Integral.intCast hℓ _) (Integral.inv_natCast fun h ↦
          hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp h))
    · rw [bernoulli_eq_zero_of_odd hodd (by obtain ⟨k, rfl⟩ := hodd; omega), mul_zero]
      exact_mod_cast Integral.natCast hℓ 0

end FFaulhaber

open FFaulhaber in
theorem F_faulhaber (ℓ m : ℕ) (hℓ : ℓ.Prime) (hm : 4 ≤ m) (hme : Even m) (hdvd : ¬ ℓ ∣ m + 1) :
    ∃ r : ℚ, ¬ ℓ ∣ r.den ∧ (powSum m ℓ : ℚ) = ℓ * bernoulli m + ℓ ^ 2 * r := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  refine ⟨∑ i ∈ Finset.range (n + 1), ((ℓ ^ (n - i) : ℕ) : ℚ) * (ℓ * bernoulli i) *
      ((n + 2 + 1).choose i : ℕ) * ((n + 2 + 1 : ℕ) : ℚ)⁻¹, ?_, ?_⟩
  · -- each term is `ℓ^(n-i) · (ℓ·B_i) · C(n+3, i) / (n+3)`, and `ℓ ∤ n + 3`
    refine Integral.sum hℓ _ _ fun i _ ↦ ?_
    exact (((Integral.natCast hℓ _).mul hℓ (integral_mul_bernoulli hℓ i)).mul hℓ
      (Integral.natCast hℓ _)).mul hℓ (Integral.inv_natCast hdvd)
  · -- split off `i = n + 2` (giving `ℓ·B_{n+2}`) and `i = n + 1` (`B_{n+1} = 0`)
    have hodd : bernoulli (n + 1) = 0 :=
      bernoulli_eq_zero_of_odd (Nat.odd_add_one.mpr (by simpa [Nat.even_add] using hme))
        (by omega)
    have hne : ((n + 2 + 1 : ℕ) : ℚ) ≠ 0 := by positivity
    rw [powSum, Nat.cast_sum]
    push_cast
    rw [sum_range_pow, Finset.sum_range_succ, Finset.sum_range_succ, hodd,
      Nat.choose_succ_self_right, Finset.mul_sum, zero_mul, zero_mul, zero_div, add_zero,
      Nat.add_sub_cancel_left, add_comm]
    congr 1
    · push_cast
      field_simp
    · refine Finset.sum_congr rfl fun i hi ↦ ?_
      rw [show n + 2 + 1 - i = n - i + 3 by simp at hi; omega]
      push_cast
      field_simp
      ring

end A046969
