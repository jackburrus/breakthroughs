import FormalConjectures.OEIS.«60841»

/-!
# Shared definitions for the A060841 conjecture 1 proof

Everything here is ours, not upstream. The upstream statement and definitions
(`OeisA60841.lcmMatrix`, `OeisA60841.integerDetN`, `OeisA60841.conjecture1`) are imported
from `FormalConjectures.OEIS.«60841»` and must never be edited or restated.
-/

namespace A060841

/-- The closed form of `1 / det (lcmMatrix n)`: `∏_{k=1}^{n} k² / φ(k)`. -/
def closedForm (n : ℕ) : ℚ :=
  ∏ k ∈ Finset.Icc 1 n, ((k : ℚ) ^ 2 / (Nat.totient k : ℚ))

/-- The split between the finite check (L2, `n < threshold`) and the uniform
2-adic bound (L3, `threshold ≤ n`). Change it here only; L2 and L3 read it from here.
It must stay above 38 (see `lt_threshold`). -/
def threshold : ℕ := 82

theorem lt_threshold : 38 < threshold := by decide

end A060841
