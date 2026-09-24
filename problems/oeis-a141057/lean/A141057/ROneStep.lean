import A141057.Defs
import A141057.SSplit
import A141057.VVanish
import A141057.PPerTerm

/-!
# R: the one-step supercongruence, and the reduction to it

PRD step 3 (node R) and the final reduction (node M). For `m ≥ 1`,
`p ^ (3 (v_p m + 1)) ∣ aInt(m p) - aInt(m)` and `∣ aInt(-m p) - aInt(-m)`: expand `aInt` into
the double sums of cubes, then apply S with V (cubed, using `v_p (m p) = v_p m + 1`) and P.
For `n < 0` the summands carry the sign `(-1)^k`, and `(-1)^(i p) = (-1)^i` as `p` is odd.
`R_dvd` takes `m = |n| p ^ (k - 1)`, whose valuation is at least `k - 1`; `Main.lean` turns it
into the upstream `Int.ModEq` statement.
Checked by `../numerics/lemmas.py` (checks `R_pos`, `R_neg`) and `../numerics/check.py`.
-/

namespace A141057

/-- **R₊**: `p ^ (3 (v_p m + 1)) ∣ aInt(m p) - aInt(m)` for `m ≥ 1`. -/
theorem R_pos (p m : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hm : 1 ≤ m) :
    (p : ℤ) ^ (3 * (padicValNat p m + 1)) ∣ aInt ((m * p : ℕ) : ℤ) - aInt (m : ℤ) := by
  sorry

/-- **R₋**: `p ^ (3 (v_p m + 1)) ∣ aInt(-m p) - aInt(-m)` for `m ≥ 1`. -/
theorem R_neg (p m : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hm : 1 ≤ m) :
    (p : ℤ) ^ (3 * (padicValNat p m + 1)) ∣ aInt (-((m * p : ℕ) : ℤ)) - aInt (-(m : ℤ)) := by
  sorry

/-- **R**: both signs at once, for any integer `n ≠ 0`. -/
theorem R_oneStep (p : ℕ) (n : ℤ) (hp : p.Prime) (hp5 : 5 ≤ p) (hn : n ≠ 0) :
    (p : ℤ) ^ (3 * (padicValNat p n.natAbs + 1)) ∣ aInt (n * p) - aInt n := by
  sorry

/-- **M**: the conjecture as a divisibility, `p ^ (3 k) ∣ aInt(n p ^ (k - 1)) - aInt(n p ^ k)`. -/
theorem R_dvd (p k : ℕ) (n : ℤ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 1 ≤ k) (hn : n ≠ 0) :
    (p : ℤ) ^ (3 * k) ∣ aInt (n * p ^ (k - 1)) - aInt (n * p ^ k) := by
  sorry

end A141057
