import A060841.Defs

/-!
# L3: uniform 2-adic bound for `n ≥ threshold`

For `n ≥ threshold` the 2-adic valuation of `∏ φ(k)` exceeds that of `(n!)²`, so the
closed form is not an integer. See the PRD, Approach step 3.
-/

namespace A060841

theorem L3_large (n : ℕ) (hn : threshold ≤ n) : (closedForm n).den ≠ 1 := by
  sorry

end A060841
