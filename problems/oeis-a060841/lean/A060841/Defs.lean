import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Field.Rat
import Mathlib.Data.Nat.Totient

/-!
# Shared definitions for the A060841 conjecture 1 proof

Everything here is ours, not upstream. This file (and every lemma file) imports only the
specific Mathlib modules it needs; the upstream statement is imported only by `Main.lean`.
See `CLAUDE.md` and `../BLUEPRINT.md`.
-/

namespace A060841

/-- The closed form of `1 / det (lcmMatrix n)`: `R(n) = ∏_{k=1}^{n} k² / φ(k)`. -/
def closedForm (n : ℕ) : ℚ :=
  ∏ k ∈ Finset.Icc 1 n, ((k : ℚ) ^ 2 / (Nat.totient k : ℚ))

/-- The split between the finite check (L2, `n < threshold`) and the uniform
2-adic bound (L3, `threshold ≤ n`). Change it here only; L2 and L3 read it from here.
It must stay above 38 (see `lt_threshold`). 82 is the PRD's crude route A; the blueprint
also allows 79 (refined route A) or 50 (window route B), see `../BLUEPRINT.md` §5–7. -/
def threshold : ℕ := 82

theorem lt_threshold : 38 < threshold := by decide

end A060841
