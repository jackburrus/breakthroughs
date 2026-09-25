import A141057.KJacobsthal

/-!
# K⁻: Jacobsthal–Kazandzidis for the negative-index binomials

PRD step 2, negative side. `C(-M, n) = (-1)^n C(M + n - 1, n)`, and for a prime `p ≥ 5`: if `p ^ u`
divides `a` and `b`, and `p ^ w` divides `C(b + a - 1, a)`, then
`C(b p + a p - 1, a p) ≡ C(b + a - 1, a)` modulo `p ^ (w + 3 u + 3)`.
Proof: as for K, with the ascending product `C(M + n - 1, n) n! = M (M + 1) ⋯ (M + n - 1)` in place of
`(M + 1) ⋯ (M + n)`. At `M = b p`, `n = a p`, its multiples of `p` are `p (b + i)` for `0 ≤ i < a`,
and the rest multiply to the same `H(b)` as in K (`split_zero`), so
`C(b p + a p - 1, a p) H(0) = C(b + a - 1, a) H(b)`, and `congr_of_eq` finishes.
Checked by `../numerics/lemmas.py` (check `KNeg`).
-/

namespace A141057

open K Finset in
/-- **K⁻**: if `p ^ u ∣ a`, `p ^ u ∣ b` and `p ^ w ∣ C(b + a - 1, a)`, then
`C(b p + a p - 1, a p) ≡ C(b + a - 1, a) (mod p ^ (w + 3 u + 3))` (`p ≥ 5`). -/
theorem K_chooseNeg {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) {a b u w : ℕ} (hua : p ^ u ∣ a)
    (hub : p ^ u ∣ b) (hw : p ^ w ∣ (b + a - 1).choose a) :
    ((b * p + a * p - 1).choose (a * p) : ℤ) ≡ ((b + a - 1).choose a : ℤ)
      [ZMOD (p : ℤ) ^ (w + 3 * u + 3)] := by
  have hp0 := hp.pos
  refine congr_of_eq hp h5 hua hub hw ?_
  -- `C(b p + a p - 1, a p) (a p)! = b p (b p + 1) ⋯ (b p + a p - 1)`, split at the multiples of `p`
  have hbig := asc_zero (b * p) (a * p)
  rw [split_zero p b a hp0, factorial_split p a hp0] at hbig
  have hsmall := asc_zero b a
  have hpos : 0 < p ^ a * ∏ i ∈ range a, (i + 1) :=
    Nat.mul_pos (pow_pos hp0 a) (prod_pos fun i _ => Nat.succ_pos i)
  refine Nat.eq_of_mul_eq_mul_left hpos ?_
  rw [← hsmall] at hbig
  linear_combination hbig

end A141057
