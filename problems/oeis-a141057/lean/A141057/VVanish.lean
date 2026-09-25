import A141057.AAbsorption
import Mathlib.Data.Nat.Prime.Basic

/-!
# V: the terms whose indices are not both multiples of `p` vanish

PRD step 1 (node V). If `p ^ e ∣ N`, the summand `C(N, k) C(k, j)` of `a(N)`, and the summand
`C(N+k-1, k) C(k, j)` of `aInt(-N)`, is divisible by `p ^ e` unless `p ∣ k` and `p ∣ j`
(`R` cubes this). Proof: for `p ∤ i`, `p ^ e ∣ N ∣ i C(N, i)` (A) and `p ^ e` is prime to `i`,
so `p ^ e ∣ C(N, i)`. Take `i = k`, or, if `p ∣ k` but `p ∤ j`, take `i = j` after moving `j`
into the first binomial (`Nat.choose_mul`, resp. `A_symm_neg`).
Checked by `../numerics/lemmas.py` (checks `V_pos`, `V_neg`).
-/

namespace A141057

/-- **V₊**: if `p ^ e ∣ N`, then `p ^ e ∣ C(N, k) C(k, j)` unless `p ∣ k` and `p ∣ j`. -/
theorem V_pos {p N k j e : ℕ} (hp : p.Prime) (he : p ^ e ∣ N) (hkj : ¬ (p ∣ k ∧ p ∣ j)) :
    p ^ e ∣ N.choose k * k.choose j := by
  have key : ∀ i, ¬ p ∣ i → p ^ e ∣ N.choose i := fun i hi =>
    (Nat.Coprime.pow_left e ((hp.coprime_iff_not_dvd).mpr hi)).dvd_of_dvd_mul_left
      (he.trans (A_absorb N i))
  by_cases hk : p ∣ k
  · have hj : ¬ p ∣ j := fun hj => hkj ⟨hk, hj⟩
    rcases Nat.lt_or_ge k j with hjk | hjk
    · simp [Nat.choose_eq_zero_of_lt hjk]
    rw [Nat.choose_mul hjk]
    exact (key j hj).mul_right _
  · exact (key k hk).mul_right _

/-- **V₋**: if `p ^ e ∣ N`, then `p ^ e ∣ C(N + k - 1, k) C(k, j)` unless `p ∣ k` and `p ∣ j`. -/
theorem V_neg {p N k j e : ℕ} (hp : p.Prime) (he : p ^ e ∣ N) (hkj : ¬ (p ∣ k ∧ p ∣ j)) :
    p ^ e ∣ (N + k - 1).choose k * k.choose j := by
  have key : ∀ i, ¬ p ∣ i → p ^ e ∣ (N + i - 1).choose i := fun i hi =>
    (Nat.Coprime.pow_left e ((hp.coprime_iff_not_dvd).mpr hi)).dvd_of_dvd_mul_left
      (he.trans (A_absorbNeg N i))
  by_cases hk : p ∣ k
  · have hj : ¬ p ∣ j := fun hj => hkj ⟨hk, hj⟩
    rcases Nat.lt_or_ge k j with hjk | hjk
    · simp [Nat.choose_eq_zero_of_lt hjk]
    -- `k ≠ 0`, since `j ≤ k` and `p ∤ j`
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hj (by rw [Nat.le_zero.mp hjk]; exact dvd_zero p)
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · rw [Nat.choose_eq_zero_of_lt (show 0 + k - 1 < k by omega), Nat.zero_mul]
      exact dvd_zero _
    rw [A_symm_neg N k j hN hjk]
    exact (key j hj).mul_right _
  · exact (key k hk).mul_right _

end A141057
