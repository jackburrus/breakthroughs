import A141057.KJacobsthal

/-!
# K⁻: Jacobsthal–Kazandzidis for the negative-index binomials

PRD step 2, negative side. `C(-m, i) = (-1)^i C(m + i - 1, i)`, and for `m ≥ 1`
`C(m p + i p - 1, i p) ≡ C(m + i - 1, i) (mod p ^ (v_p C(m + i - 1, i) + 3 + 3 min(v_p i, v_p m)))`.
Proof idea: `(m + i) C(m + i - 1, i) = m C(m + i, i)`, and the same at `(m p, i p)` after
cancelling `p`, so `(m + i) (C(m p + i p - 1, i p) - C(m + i - 1, i)) = m (C((m + i) p, i p) - C(m + i, i))`.
Apply K with `(A, B) = (m + i, i)` and divide by the `p`-part of `m + i`, using
`v_p C(m + i - 1, i) = v_p m + v_p C(m + i, i) - v_p (m + i)`.
Checked by `../numerics/lemmas.py` (check `KNeg`).
-/

namespace A141057

/-- **K⁻**: `p ^ (v_p C(m+i-1, i) + 3 + 3 min(v_p i, v_p m)) ∣ C(m p + i p - 1, i p) - C(m + i - 1, i)`. -/
theorem KNeg_jacobsthal (p m i : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hm : 1 ≤ m) :
    (p : ℤ) ^ (padicValNat p ((m + i - 1).choose i) + 3 +
        3 * min (padicValNat p i) (padicValNat p m)) ∣
      ((m * p + i * p - 1).choose (i * p) : ℤ) - ((m + i - 1).choose i : ℤ) := by
  sorry

end A141057
