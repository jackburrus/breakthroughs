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

namespace P

/-- Multiply two divisibilities by powers of `P`, keeping any smaller exponent. -/
theorem pow_dvd_mul {P : ℤ} {a b e : ℕ} {x y : ℤ} (hx : P ^ a ∣ x) (hy : P ^ b ∣ y)
    (h : e ≤ a + b) : P ^ e ∣ x * y :=
  (pow_dvd_pow P h).trans (by rw [pow_add]; exact mul_dvd_mul hx hy)

end P

/-- **P_cube**: the algebra behind both per-term congruences; any `p`. -/
theorem P_cube (p t v₁ v₂ w₁ w₂ : ℕ) (c₁ d₁ c₂ d₂ : ℤ)
    (hd₁ : (p : ℤ) ^ v₁ ∣ d₁) (hd₂ : (p : ℤ) ^ v₂ ∣ d₂)
    (he₁ : (p : ℤ) ^ (v₁ + 3 + 3 * w₁) ∣ c₁ - d₁) (he₂ : (p : ℤ) ^ (v₂ + 3 + 3 * w₂) ∣ c₂ - d₂)
    (ht₁ : c₁ ≠ d₁ → t ≤ v₁ + v₂ + w₁) (ht₂ : c₂ ≠ d₂ → t ≤ v₁ + v₂ + w₂) :
    (p : ℤ) ^ (3 * (t + 1)) ∣ (c₁ * c₂) ^ 3 - (d₁ * d₂) ^ 3 := by
  have hc₁ : (p : ℤ) ^ v₁ ∣ c₁ := by
    rw [show c₁ = d₁ + (c₁ - d₁) by ring]
    exact dvd_add hd₁ ((pow_dvd_pow _ (by omega)).trans he₁)
  have hc₂ : (p : ℤ) ^ v₂ ∣ c₂ := by
    rw [show c₂ = d₂ + (c₂ - d₂) by ring]
    exact dvd_add hd₂ ((pow_dvd_pow _ (by omega)).trans he₂)
  have hCD : (p : ℤ) ^ (2 * (v₁ + v₂)) ∣ c₁ * c₂ * (d₁ * d₂) :=
    P.pow_dvd_mul (P.pow_dvd_mul hc₁ hc₂ le_rfl) (P.pow_dvd_mul hd₁ hd₂ le_rfl) (by omega)
  -- `C - D = X + Y + Z`; each piece is `≡ 0 (mod p ^ (t + 1))`, and `≡ 0 (mod p ^ (3 (t + 1)))`
  -- after multiplying by `C D`
  have hX : (p : ℤ) ^ (t + 1) ∣ d₁ * (c₂ - d₂) ∧
      (p : ℤ) ^ (3 * (t + 1)) ∣ c₁ * c₂ * (d₁ * d₂) * (d₁ * (c₂ - d₂)) := by
    rcases eq_or_ne c₂ d₂ with h | h
    · simp [h]
    · have := ht₂ h
      exact ⟨P.pow_dvd_mul hd₁ he₂ (by omega),
        P.pow_dvd_mul hCD (P.pow_dvd_mul hd₁ he₂ le_rfl) (by omega)⟩
  have hY : (p : ℤ) ^ (t + 1) ∣ d₂ * (c₁ - d₁) ∧
      (p : ℤ) ^ (3 * (t + 1)) ∣ c₁ * c₂ * (d₁ * d₂) * (d₂ * (c₁ - d₁)) := by
    rcases eq_or_ne c₁ d₁ with h | h
    · simp [h]
    · have := ht₁ h
      exact ⟨P.pow_dvd_mul hd₂ he₁ (by omega),
        P.pow_dvd_mul hCD (P.pow_dvd_mul hd₂ he₁ le_rfl) (by omega)⟩
  have hZ : (p : ℤ) ^ (t + 1) ∣ (c₁ - d₁) * (c₂ - d₂) ∧
      (p : ℤ) ^ (3 * (t + 1)) ∣ c₁ * c₂ * (d₁ * d₂) * ((c₁ - d₁) * (c₂ - d₂)) := by
    rcases eq_or_ne c₁ d₁ with h | h
    · simp [h]
    · have := ht₁ h
      exact ⟨P.pow_dvd_mul he₁ he₂ (by omega),
        P.pow_dvd_mul hCD (P.pow_dvd_mul he₁ he₂ le_rfl) (by omega)⟩
  have hδ : (p : ℤ) ^ (t + 1) ∣ c₁ * c₂ - d₁ * d₂ := by
    rw [show c₁ * c₂ - d₁ * d₂ = d₁ * (c₂ - d₂) + d₂ * (c₁ - d₁) + (c₁ - d₁) * (c₂ - d₂) by ring]
    exact dvd_add (dvd_add hX.1 hY.1) hZ.1
  -- `C³ - D³ = (C - D)³ + 3 C D (C - D)`
  rw [show (c₁ * c₂) ^ 3 - (d₁ * d₂) ^ 3 = (c₁ * c₂ - d₁ * d₂) ^ 3 +
      3 * (c₁ * c₂ * (d₁ * d₂) * (d₁ * (c₂ - d₂)) + c₁ * c₂ * (d₁ * d₂) * (d₂ * (c₁ - d₁)) +
        c₁ * c₂ * (d₁ * d₂) * ((c₁ - d₁) * (c₂ - d₂))) by ring]
  refine dvd_add ?_ ((dvd_add (dvd_add hX.2 hY.2) hZ.2).mul_left 3)
  rw [mul_comm 3, pow_mul]
  exact pow_dvd_pow_of_dvd hδ 3

/-- **P₊**: `(C(m p, i p) C(i p, l p))³ ≡ (C(m, i) C(i, l))³ (mod p ^ (3 (v_p m + 1)))`. -/
theorem P_pos (p m i l : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hi : i ≤ m) (hl : l ≤ i) :
    (p : ℤ) ^ (3 * (padicValNat p m + 1)) ∣
      (((m * p).choose (i * p) * (i * p).choose (l * p) : ℕ) : ℤ) ^ 3 -
        ((m.choose i * i.choose l : ℕ) : ℤ) ^ 3 := by
  push_cast
  refine P_cube p (padicValNat p m) (padicValNat p (m.choose i)) (padicValNat p (i.choose l))
    (min (padicValNat p i) (padicValNat p (m - i))) (min (padicValNat p l) (padicValNat p (i - l)))
    _ _ _ _ (by exact_mod_cast pow_padicValNat_dvd) (by exact_mod_cast pow_padicValNat_dvd)
    (K_jacobsthal p m i hp hp5 hi) (K_jacobsthal p i l hp hp5 hl) ?_ ?_
  · -- `C(m p, i p) ≠ C(m, i)` forces `0 < i < m`
    intro h
    have hi0 : 1 ≤ i := by
      rcases Nat.eq_zero_or_pos i with rfl | h0
      · simp at h
      · exact h0
    have him : 1 ≤ m - i := by
      rcases Nat.lt_or_ge i m with h1 | h1
      · omega
      · exfalso; apply h; rw [show i = m by omega]; simp
    have hk := A_kummer p i (m - i) hp hi0 him
    rw [show i + (m - i) = m by omega] at hk
    omega
  · -- `C(i p, l p) ≠ C(i, l)` forces `0 < l < i`
    intro h
    have hl0 : 1 ≤ l := by
      rcases Nat.eq_zero_or_pos l with rfl | h0
      · simp at h
      · exact h0
    have hil : 1 ≤ i - l := by
      rcases Nat.lt_or_ge l i with h1 | h1
      · omega
      · exfalso; apply h; rw [show l = i by omega]; simp
    have hk := A_kummer p l (i - l) hp hl0 hil
    rw [show l + (i - l) = i by omega] at hk
    have ha := A_pos p m i hp (by omega) hi
    omega

/-- **P₋**: `(C(m p + i p - 1, i p) C(i p, l p))³ ≡ (C(m + i - 1, i) C(i, l))³
(mod p ^ (3 (v_p m + 1)))`. -/
theorem P_neg (p m i l : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hm : 1 ≤ m) (hl : l ≤ i) :
    (p : ℤ) ^ (3 * (padicValNat p m + 1)) ∣
      (((m * p + i * p - 1).choose (i * p) * (i * p).choose (l * p) : ℕ) : ℤ) ^ 3 -
        (((m + i - 1).choose i * i.choose l : ℕ) : ℤ) ^ 3 := by
  push_cast
  refine P_cube p (padicValNat p m) (padicValNat p ((m + i - 1).choose i))
    (padicValNat p (i.choose l)) (min (padicValNat p i) (padicValNat p m))
    (min (padicValNat p l) (padicValNat p (i - l)))
    _ _ _ _ (by exact_mod_cast pow_padicValNat_dvd) (by exact_mod_cast pow_padicValNat_dvd)
    (KNeg_jacobsthal p m i hp hp5 hm) (K_jacobsthal p i l hp hp5 hl) ?_ ?_
  · -- `C(m p + i p - 1, i p) ≠ C(m + i - 1, i)` forces `0 < i`
    intro h
    have hi0 : 1 ≤ i := by
      rcases Nat.eq_zero_or_pos i with rfl | h0
      · simp at h
      · exact h0
    have ha := A_neg p m i hp hm hi0
    omega
  · -- `C(i p, l p) ≠ C(i, l)` forces `0 < l < i`
    intro h
    have hl0 : 1 ≤ l := by
      rcases Nat.eq_zero_or_pos l with rfl | h0
      · simp at h
      · exact h0
    have hil : 1 ≤ i - l := by
      rcases Nat.lt_or_ge l i with h1 | h1
      · omega
      · exfalso; apply h; rw [show l = i by omega]; simp
    have hk := A_kummer p l (i - l) hp hl0 hil
    rw [show l + (i - l) = i by omega] at hk
    have ha := A_neg p m i hp hm (by omega)
    omega

end A141057
