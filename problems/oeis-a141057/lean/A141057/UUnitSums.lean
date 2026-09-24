import Mathlib.Data.ZMod.Basic

/-!
# U: sums of inverse units modulo `p ^ s`

PRD step 2 input ("Approach", node U). For a prime `p ≥ 5` and `p ^ s ∣ N`, the inverses of the
integers `0 ≤ a < N` prime to `p` sum to zero modulo `p ^ s`, and so do their squares.
Proof idea: multiplication by 2 permutes the units of `ZMod (p ^ s)`, so each sum `S` satisfies
`S = 2⁻¹ S` (resp. `S = 2⁻² S`), and `2⁻¹ - 1`, `2⁻² - 1 = (2⁻¹ - 1)(2⁻¹ + 1)` are units since
`2, 3` are prime to `p`; then split `range N` into `N / p ^ s` blocks of length `p ^ s`.
Checked by `../numerics/lemmas.py` (check `U`), which also shows both fail at `p = 3`.
-/

namespace A141057

/-- **U₁**: `∑ a⁻¹ = 0` in `ZMod (p ^ s)`, over `0 ≤ a < N` with `p ∤ a`, when `p ^ s ∣ N`. -/
theorem U_sum_inv (p s N : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hN : p ^ s ∣ N) :
    ∑ a ∈ (Finset.range N).filter (fun a => ¬ p ∣ a), ((a : ZMod (p ^ s)))⁻¹ = 0 := by
  sorry

/-- **U₂**: `∑ (a⁻¹)² = 0` in `ZMod (p ^ s)`, over `0 ≤ a < N` with `p ∤ a`, when `p ^ s ∣ N`. -/
theorem U_sum_inv_sq (p s N : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hN : p ^ s ∣ N) :
    ∑ a ∈ (Finset.range N).filter (fun a => ¬ p ∣ a), ((a : ZMod (p ^ s)))⁻¹ ^ 2 = 0 := by
  sorry

end A141057
