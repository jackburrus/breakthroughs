import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# A: absorption and symmetry, as `p`-adic valuation bounds

PRD step 1 inputs (node A). Each bound comes from an absorption identity:
`k C(N, k) = N C(N - 1, k - 1)` (for `A_pos`), `k C(N + k - 1, k) = N C(N + k - 1, k - 1)`
(for `A_neg`), and `A_kummer` is `A_pos` at `x` and at `y`, with `C(x + y, x) = C(x + y, y)`.
`A_symm_neg` moves the index `j` into the negative-index binomial; its positive analogue is
Mathlib's `Nat.choose_mul`. No `p ≥ 5` here: any prime works.
Checked by `../numerics/lemmas.py` (checks `A_pos`, `A_neg`, `A_kummer`, `A_symm_neg`).
-/

namespace A141057

/-- **A₊**: `v_p N ≤ v_p k + v_p C(N, k)` for `1 ≤ k ≤ N`. -/
theorem A_pos (p N k : ℕ) (hp : p.Prime) (hk : 1 ≤ k) (hkN : k ≤ N) :
    padicValNat p N ≤ padicValNat p k + padicValNat p (N.choose k) := by
  sorry

/-- **A₋**: `v_p N ≤ v_p k + v_p C(N + k - 1, k)` for `1 ≤ N` and `1 ≤ k`. -/
theorem A_neg (p N k : ℕ) (hp : p.Prime) (hN : 1 ≤ N) (hk : 1 ≤ k) :
    padicValNat p N ≤ padicValNat p k + padicValNat p ((N + k - 1).choose k) := by
  sorry

/-- **A_Kummer**: `v_p (x + y) ≤ v_p C(x + y, x) + min(v_p x, v_p y)` for `x, y ≥ 1`. -/
theorem A_kummer (p x y : ℕ) (hp : p.Prime) (hx : 1 ≤ x) (hy : 1 ≤ y) :
    padicValNat p (x + y) ≤
      padicValNat p ((x + y).choose x) + min (padicValNat p x) (padicValNat p y) := by
  sorry

/-- **A_symm⁻**: `C(N+k-1, k) C(k, j) = C(N+j-1, j) C(N+k-1, k-j)` (both are the multinomial
`(N+k-1)! / ((N-1)! j! (k-j)!)`). -/
theorem A_symm_neg (N k j : ℕ) (hN : 1 ≤ N) (hjk : j ≤ k) :
    (N + k - 1).choose k * k.choose j = (N + j - 1).choose j * (N + k - 1).choose (k - j) := by
  sorry

end A141057
