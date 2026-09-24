import A060841.Defs
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# L1: closed form of the lcm-matrix determinant

`1 / det M_n = ∏_{k=1}^{n} k² / φ(k)`, via Smith's determinant `det (gcd i j) = ∏ φ(k)`
and `M = D⁻¹ G D⁻¹` with `D = diag(1, …, n)`. See `../BLUEPRINT.md` §1.

The statement also forces `det M_n ≠ 0` (`closedForm n ≠ 0`, and `(0 : ℚ)⁻¹ = 0`), which the
integer direction of the iff depends on (blueprint §8, flag 3).
-/

namespace A060841

/-- A copy of `OeisA60841.lcmMatrix`, so this file need not import upstream (and all of
Mathlib). `Main.lean` checks it is the upstream definition by `rfl`; do not change it. -/
def lcmMat (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun i j : Fin n ↦ 1 / ((Nat.lcm (i.val + 1) (j.val + 1) : ℚ))

theorem L1_det_closedForm (n : ℕ) : ((lcmMat n).det)⁻¹ = closedForm n := by
  sorry

end A060841
