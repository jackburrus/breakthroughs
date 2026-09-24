import A060841.Defs

/-!
# L3: uniform 2-adic bound for `n ≥ threshold`

For `n ≥ threshold` the 2-adic valuation of `∏ φ(k)` exceeds that of `(n!)²`, so the
closed form is not an integer. See `../BLUEPRINT.md` §2 and §5–6: use the exact constants
(or `A ≥ 3791/2000`), not the PRD's rounded 1.8956 and 32.11.
-/

namespace A060841

theorem L3_large (n : ℕ) (hn : threshold ≤ n) : (closedForm n).den ≠ 1 := by
  sorry

end A060841
