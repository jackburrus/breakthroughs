import A046969.Defs

/-!
# F: Faulhaber modulo `ℓ²`

`S_m(ℓ) ≡ ℓ·B_m (mod ℓ²)` in the `ℓ`-integral sense, for a prime `ℓ`, even `m ≥ 4` and
`ℓ ∤ m + 1`. From `sum_range_pow`: the `i = m` term is `ℓ·B_m`, the `i = m - 1` term vanishes
(`B_{m-1} = 0`), and every other term is `ℓ^{≥3}·B_i·C(m+1, i)/(m+1)` with `v_ℓ(B_i) ≥ -1`
(von Staudt–Clausen for even `i`, `B_1 = -1/2`, `B_i = 0` for odd `i > 1`) and `ℓ ∤ m + 1`.
See `../PRD.md`, Approach step 2.
-/

namespace A046969

theorem F_faulhaber (ℓ m : ℕ) (hℓ : ℓ.Prime) (hm : 4 ≤ m) (hme : Even m) (hdvd : ¬ ℓ ∣ m + 1) :
    ∃ r : ℚ, ¬ ℓ ∣ r.den ∧ (powSum m ℓ : ℚ) = ℓ * bernoulli m + ℓ ^ 2 * r := by
  sorry

end A046969
