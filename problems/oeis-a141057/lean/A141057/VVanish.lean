import A141057.AAbsorption

/-!
# V: the terms whose indices are not both multiples of `p` vanish

PRD step 1 (node V). A summand `(C(N, k) C(k, j))³` of `a(N)`, or `(C(N+k-1, k) C(k, j))³` of
`aInt(-N)`, is divisible by `p ^ (3 v_p N)` unless `p ∣ k` and `p ∣ j`. Here the uncubed forms.
Proof idea: if `p ∤ k`, apply `A_pos`/`A_neg` at `k`; if `p ∣ k` but `p ∤ j`, first move `j`
into the first binomial (`Nat.choose_mul`, resp. `A_symm_neg`) and apply them at `j`.
No bound on `k` or `j` is needed: out of range the binomials vanish.
Checked by `../numerics/lemmas.py` (checks `V_pos`, `V_neg`).
-/

namespace A141057

/-- **V₊**: `p ^ v_p N ∣ C(N, k) C(k, j)` unless `p ∣ k` and `p ∣ j`. -/
theorem V_pos (p N k j : ℕ) (hp : p.Prime) (hkj : ¬ (p ∣ k ∧ p ∣ j)) :
    p ^ padicValNat p N ∣ N.choose k * k.choose j := by
  rcases Nat.lt_or_ge N k with hNk | hkN
  · rw [Nat.choose_eq_zero_of_lt hNk, zero_mul]; exact dvd_zero _
  rcases Nat.lt_or_ge k j with hkj' | hjk
  · rw [Nat.choose_eq_zero_of_lt hkj', mul_zero]; exact dvd_zero _
  by_cases hk : p ∣ k
  · -- `p ∤ j`: move `j` into the first binomial, `C(N, k) C(k, j) = C(N, j) C(N - j, k - j)`
    have hj : ¬ p ∣ j := fun hj => hkj ⟨hk, hj⟩
    have hj1 : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr (by rintro rfl; exact hj (dvd_zero p))
    have hv := A_pos p N j hp hj1 (by omega)
    rw [padicValNat.eq_zero_of_not_dvd hj, zero_add] at hv
    rw [Nat.choose_mul hjk]
    exact ((pow_dvd_pow p hv).trans pow_padicValNat_dvd).mul_right _
  · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr (by rintro rfl; exact hk (dvd_zero p))
    have hv := A_pos p N k hp hk1 hkN
    rw [padicValNat.eq_zero_of_not_dvd hk, zero_add] at hv
    exact ((pow_dvd_pow p hv).trans pow_padicValNat_dvd).mul_right _

/-- **V₋**: `p ^ v_p N ∣ C(N + k - 1, k) C(k, j)` unless `p ∣ k` and `p ∣ j`. -/
theorem V_neg (p N k j : ℕ) (hp : p.Prime) (hkj : ¬ (p ∣ k ∧ p ∣ j)) :
    p ^ padicValNat p N ∣ (N + k - 1).choose k * k.choose j := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rw [padicValNat_zero_right, pow_zero]; exact one_dvd _
  rcases Nat.lt_or_ge k j with hkj' | hjk
  · rw [Nat.choose_eq_zero_of_lt hkj', mul_zero]; exact dvd_zero _
  by_cases hk : p ∣ k
  · -- `p ∤ j`: move `j` into the first binomial with `A_symm_neg`
    have hj : ¬ p ∣ j := fun hj => hkj ⟨hk, hj⟩
    have hj1 : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr (by rintro rfl; exact hj (dvd_zero p))
    have hv := A_neg p N j hp hN hj1
    rw [padicValNat.eq_zero_of_not_dvd hj, zero_add] at hv
    rw [A_symm_neg N k j hN hjk]
    exact ((pow_dvd_pow p hv).trans pow_padicValNat_dvd).mul_right _
  · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr (by rintro rfl; exact hk (dvd_zero p))
    have hv := A_neg p N k hp hN hk1
    rw [padicValNat.eq_zero_of_not_dvd hk, zero_add] at hv
    exact ((pow_dvd_pow p hv).trans pow_padicValNat_dvd).mul_right _

end A141057
