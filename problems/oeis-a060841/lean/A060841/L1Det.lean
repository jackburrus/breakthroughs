import A060841.Defs

/-!
# L1: closed form of the lcm-matrix determinant

`1 / det M_n = ∏_{k=1}^{n} k² / φ(k)`, via Smith's determinant `det (gcd i j) = ∏ φ(k)`
and `M = D⁻¹ G D⁻¹` with `D = diag(1, …, n)`. See the PRD, Approach step 1.
-/

namespace A060841

open OeisA60841

theorem L1_det_closedForm (n : ℕ) : ((lcmMatrix n).det)⁻¹ = closedForm n := by
  sorry

end A060841
