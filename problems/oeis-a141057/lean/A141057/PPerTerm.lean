import A141057.KNegJacobsthal
import A141057.AAbsorption

/-!
# P: the per-term supercongruences, both signs

PRD step 2 (node P). With `t = v_p m`, the summand of `a(m p)` (resp. `aInt(-m p)`) at indices
`(i p, l p)` agrees with the summand of `a(m)` (resp. `aInt(-m)`) at `(i, l)` modulo
`p ^ (3 (t + 1))`, up to the sign `(-1)^(i p) = (-1)^i`, which `R_neg` handles.
`P_cube` is the sign-free algebra: write `c₁ = d₁ + e₁`, `c₂ = d₂ + e₂`, then
`C - D = d₁ e₂ + d₂ e₁ + e₁ e₂` has valuation `≥ t + 1`, and `C³ - D³ = (C - D)³ + 3 C D (C - D)`.
`P_pos` feeds it K at `(m, i)` and `(i, l)`; `P_neg` feeds it K⁻ at `(m, i)` and K at `(i, l)`.
The side conditions come from A: `c₁ ≠ d₁` forces `1 ≤ i` (and `i < m` for `P_pos`),
`c₂ ≠ d₂` forces `1 ≤ l < i`.
Checked by `../numerics/lemmas.py` (checks `P_pos`, `P_neg`).
-/

namespace A141057

/-- **P_cube**: the algebra behind both per-term congruences; any `p`. -/
theorem P_cube (p t v₁ v₂ w₁ w₂ : ℕ) (c₁ d₁ c₂ d₂ : ℤ)
    (hd₁ : (p : ℤ) ^ v₁ ∣ d₁) (hd₂ : (p : ℤ) ^ v₂ ∣ d₂)
    (he₁ : (p : ℤ) ^ (v₁ + 3 + 3 * w₁) ∣ c₁ - d₁) (he₂ : (p : ℤ) ^ (v₂ + 3 + 3 * w₂) ∣ c₂ - d₂)
    (ht₁ : c₁ ≠ d₁ → t ≤ v₁ + v₂ + w₁) (ht₂ : c₂ ≠ d₂ → t ≤ v₁ + v₂ + w₂) :
    (p : ℤ) ^ (3 * (t + 1)) ∣ (c₁ * c₂) ^ 3 - (d₁ * d₂) ^ 3 := by
  sorry

/-- **P₊**: `(C(m p, i p) C(i p, l p))³ ≡ (C(m, i) C(i, l))³ (mod p ^ (3 (v_p m + 1)))`. -/
theorem P_pos (p m i l : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hi : i ≤ m) (hl : l ≤ i) :
    (p : ℤ) ^ (3 * (padicValNat p m + 1)) ∣
      (((m * p).choose (i * p) * (i * p).choose (l * p) : ℕ) : ℤ) ^ 3 -
        ((m.choose i * i.choose l : ℕ) : ℤ) ^ 3 := by
  sorry

/-- **P₋**: `(C(m p + i p - 1, i p) C(i p, l p))³ ≡ (C(m + i - 1, i) C(i, l))³
(mod p ^ (3 (v_p m + 1)))`. -/
theorem P_neg (p m i l : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hm : 1 ≤ m) (hl : l ≤ i) :
    (p : ℤ) ^ (3 * (padicValNat p m + 1)) ∣
      (((m * p + i * p - 1).choose (i * p) * (i * p).choose (l * p) : ℕ) : ℤ) ^ 3 -
        (((m + i - 1).choose i * i.choose l : ℕ) : ℤ) ^ 3 := by
  sorry

end A141057
