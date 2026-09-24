import A141057.UUnitSums
import Mathlib.NumberTheory.Padics.PadicVal.Defs

/-!
# D: the shifted-product congruence

PRD step 2 (inside node K). With `S = {0 ≤ a < L p : p ∤ a}`, shifting every factor of
`∏_{a ∈ S} a` by `B p` changes the product only modulo `p ^ (3 + 3 min(v_p B, v_p L))`.
Proof idea: expand `∏ (B p + a) = ∑_r (B p)^r e_r`, where `e_r` sums the products of all but
`r` elements of `S`. With `s = v_p L + 1` (so `p ^ s ∣ L p`), U gives `p ^ (2 s) ∣ e_1`
(pair `c` with `L p - c`: `2 e_1 = L p · ∑_c ∏_{a ≠ c, L p - c} a` and the sum is
`≡ -(∏ a) ∑ c⁻² ≡ 0`) and `p ^ s ∣ e_2` (`(∑ a⁻¹)² = ∑ a⁻² + 2 ∑_{pairs} a⁻¹ b⁻¹`).
Then `r = 1, 2, ≥ 3` contribute `p ^ ((v_p B + 1) + 2 s)`, `p ^ (2 (v_p B + 1) + s)`,
`p ^ (3 (v_p B + 1))`, each at least `p ^ (3 + 3 min(v_p B, v_p L))`.
Checked by `../numerics/lemmas.py` (check `D`), which also shows it fails at `p = 3`.
-/

namespace A141057

/-- **D**: `p ^ (3 + 3 min(v_p B, v_p L)) ∣ ∏ (B p + a) - ∏ a` over `0 ≤ a < L p`, `p ∤ a`. -/
theorem D_shiftProd (p L B : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    (p : ℤ) ^ (3 + 3 * min (padicValNat p B) (padicValNat p L)) ∣
      ((∏ a ∈ (Finset.range (L * p)).filter (fun a => ¬ p ∣ a), (B * p + a) : ℕ) : ℤ) -
        ((∏ a ∈ (Finset.range (L * p)).filter (fun a => ¬ p ∣ a), a : ℕ) : ℤ) := by
  sorry

end A141057
