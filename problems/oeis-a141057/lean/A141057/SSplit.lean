import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.Int.Defs

/-!
# S: splitting a triangular double sum at the multiples of `p`

PRD step 3 bookkeeping, sign-free. The double sum `∑_{k ≤ m p} ∑_{j ≤ k} f k j` agrees modulo
`q` with `∑_{i ≤ m} ∑_{l ≤ i} g i l` when every summand with `(k, j)` not both multiples of `p`
is `≡ 0`, and `f (i p) (l p) ≡ g i l` for `l ≤ i ≤ m`: the pairs of multiples of `p` in the
triangle `j ≤ k ≤ m p` are exactly `(i p, l p)` with `l ≤ i ≤ m`.
Both signs use it: `R_pos` with `f k j = (C(m p, k) C(k, j))³`, `R_neg` with the signed
negative-index summands.
-/

namespace A141057

/-- **S**: the double sum over `j ≤ k ≤ m p` reduces modulo `q` to the one over `l ≤ i ≤ m`. -/
theorem S_split (p m : ℕ) (hp : 0 < p) (q : ℤ) (f g : ℕ → ℕ → ℤ)
    (hV : ∀ k j, k ≤ m * p → j ≤ k → ¬ (p ∣ k ∧ p ∣ j) → q ∣ f k j)
    (hP : ∀ i l, i ≤ m → l ≤ i → q ∣ f (i * p) (l * p) - g i l) :
    q ∣ (∑ k ∈ Finset.range (m * p + 1), ∑ j ∈ Finset.range (k + 1), f k j) -
      ∑ i ∈ Finset.range (m + 1), ∑ l ∈ Finset.range (i + 1), g i l := by
  sorry

end A141057
