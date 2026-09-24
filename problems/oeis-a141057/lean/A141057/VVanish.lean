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
  sorry

/-- **V₋**: `p ^ v_p N ∣ C(N + k - 1, k) C(k, j)` unless `p ∣ k` and `p ∣ j`. -/
theorem V_neg (p N k j : ℕ) (hp : p.Prime) (hkj : ¬ (p ∣ k ∧ p ∣ j)) :
    p ^ padicValNat p N ∣ (N + k - 1).choose k * k.choose j := by
  sorry

end A141057
