import A141057.KNegJacobsthal
import A141057.AAbsorption
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# P: the per-summand supercongruences, both signs

PRD step 2 (node P). Write a summand of `a(N)` at indices `j ≤ k ≤ N` as `C(N, k) C(k, j)` with
`j = a`, `k = a + b`, `N = a + b + c`. If `p ^ e ∣ N`, the summand of `a(N p)` at `(k p, j p)`,
cubed, agrees with the summand of `a(N)` at `(k, j)`, cubed, modulo `p ^ (3 e + 3)` (`P_summand`);
`P_summandNeg` is the same for `aInt(-m p)` and `aInt(-m)` when `p ^ e ∣ m`, without the sign.
Proof, by relative precision. Say `X ≡ x` to relative precision `ρ` if `p ^ α ∣ x` and
`X ≡ x (mod p ^ (α + ρ))`. Products keep `ρ` (`P.mul_congr`), and cubing adds `2 α`
(`P.cube_congr`, as `X³ - x³ = (X - x)(X² + X x + x²)`). K (resp. K⁻) gives each binomial factor to
relative precision `3 u + 3`, with `u` the valuation of a gcd; A bounds `e` by those gcds and the
valuations `α`, `β` of the two small binomials, so both factors reach `ρ = 3 (e - α - β) + 3`, and
the cubed product reaches `3 (α + β) + ρ ≥ 3 e + 3`.
Checked by `../numerics/lemmas.py` (checks `P_summand`, `P_summandNeg`).
-/

namespace A141057

namespace P

/-- Multiplying two congruences held to the same relative precision `ρ`. -/
theorem mul_congr {d x X y Y : ℤ} {α β ρ : ℕ} (hx : d ^ α ∣ x) (hy : d ^ β ∣ y)
    (hX : X ≡ x [ZMOD d ^ (α + ρ)]) (hY : Y ≡ y [ZMOD d ^ (β + ρ)]) :
    X * Y ≡ x * y [ZMOD d ^ (α + β + ρ)] := by
  rw [Int.modEq_iff_dvd] at hX hY ⊢
  have hY' : d ^ β ∣ Y := by
    rw [show Y = y - (y - Y) by ring]
    exact dvd_sub hy ((pow_dvd_pow d (Nat.le_add_right β ρ)).trans hY)
  rw [show x * y - X * Y = (x - X) * Y + x * (y - Y) by ring]
  refine dvd_add ?_ ?_
  · rw [show α + β + ρ = α + ρ + β by omega, pow_add]
    exact mul_dvd_mul hX hY'
  · rw [add_assoc, pow_add]
    exact mul_dvd_mul hx hY

/-- Cubing a congruence held to relative precision `ρ` gains `2 α`. -/
theorem cube_congr {d x X : ℤ} {α ρ : ℕ} (hx : d ^ α ∣ x) (hX : X ≡ x [ZMOD d ^ (α + ρ)]) :
    X ^ 3 ≡ x ^ 3 [ZMOD d ^ (3 * α + ρ)] := by
  rw [Int.modEq_iff_dvd] at hX ⊢
  have hX' : d ^ α ∣ X := by
    rw [show X = x - (x - X) by ring]
    exact dvd_sub hx ((pow_dvd_pow d (Nat.le_add_right α ρ)).trans hX)
  have hsq : ∀ {u v : ℤ}, d ^ α ∣ u → d ^ α ∣ v → d ^ (2 * α) ∣ u * v := fun hu hv => by
    rw [two_mul, pow_add]
    exact mul_dvd_mul hu hv
  rw [show x ^ 3 - X ^ 3 = (x - X) * (x * x + x * X + X * X) by ring,
    show 3 * α + ρ = α + ρ + 2 * α by omega, pow_add]
  exact mul_dvd_mul hX (dvd_add (dvd_add (hsq hx hx) (hsq hx hX')) (hsq hX' hX'))

/-- `e ≤ v_p(g) + v_p(y)` from `p ^ e ∣ g y`, for `g y ≠ 0`. -/
theorem le_of_dvd_mul {p e g y : ℕ} [Fact p.Prime] (hg : g ≠ 0) (hy : y ≠ 0) (h : p ^ e ∣ g * y) :
    e ≤ padicValNat p g + padicValNat p y := by
  rwa [padicValNat_dvd_iff_le (mul_ne_zero hg hy), padicValNat.mul hg hy] at h

/-- The last step of both signs: from the two factors, each to relative precision
`ρ = 3 (e - α - β) + 3`, to the cubed products modulo `p ^ (3 e + 3)`. -/
theorem summand_congr {p : ℕ} {X x Y y e : ℕ}
    (hX : (X : ℤ) ≡ x [ZMOD (p : ℤ) ^ (padicValNat p x +
      (3 * (e - (padicValNat p x + padicValNat p y)) + 3))])
    (hY : (Y : ℤ) ≡ y [ZMOD (p : ℤ) ^ (padicValNat p y +
      (3 * (e - (padicValNat p x + padicValNat p y)) + 3))]) :
    ((X * Y : ℕ) : ℤ) ^ 3 ≡ ((x * y : ℕ) : ℤ) ^ 3 [ZMOD (p : ℤ) ^ (3 * e + 3)] := by
  have hx : (p : ℤ) ^ padicValNat p x ∣ x := by exact_mod_cast pow_padicValNat_dvd
  have hy : (p : ℤ) ^ padicValNat p y ∣ y := by exact_mod_cast pow_padicValNat_dvd
  have hxy : (p : ℤ) ^ (padicValNat p x + padicValNat p y) ∣ ((x * y : ℕ) : ℤ) := by
    rw [pow_add]
    push_cast
    exact mul_dvd_mul hx hy
  have h := cube_congr hxy (by push_cast; exact mul_congr hx hy hX hY)
  exact h.of_dvd (pow_dvd_pow _ (by omega))

end P

open P in
/-- **P₊**: if `p ^ e ∣ a + b + c`, then modulo `p ^ (3 e + 3)`,
`(C((a+b+c) p, (a+b) p) C((a+b) p, a p))³ ≡ (C(a+b+c, a+b) C(a+b, a))³` (`p ≥ 5`). -/
theorem P_summand {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) {a b c e : ℕ} (he : p ^ e ∣ a + b + c) :
    ((((a + b + c) * p).choose ((a + b) * p) * ((a + b) * p).choose (a * p) : ℕ) : ℤ) ^ 3 ≡
      (((a + b + c).choose (a + b) * (a + b).choose a : ℕ) : ℤ) ^ 3
        [ZMOD (p : ℤ) ^ (3 * e + 3)] := by
  have : Fact p.Prime := ⟨hp⟩
  -- `a = b = 0`: every binomial is `1`
  rcases Nat.eq_zero_or_pos (a + b) with hab | hab
  · obtain ⟨rfl, rfl⟩ : a = 0 ∧ b = 0 := ⟨by omega, by omega⟩
    simp
  have hx0 : (a + b + c).choose (a + b) ≠ 0 := (Nat.choose_pos (by omega)).ne'
  have hy0 : (a + b).choose a ≠ 0 := (Nat.choose_pos (by omega)).ne'
  have hg₁ : Nat.gcd (a + b) c ≠ 0 := Nat.gcd_ne_zero_left (by omega)
  have hg₂ : Nat.gcd a b ≠ 0 := by
    rw [Ne, Nat.gcd_eq_zero_iff]
    omega
  -- `p ^ e ∣ gcd(a + b, c) C(a+b+c, a+b)`, and `p ^ e ∣ (a + b) C(a+b+c, a+b) ∣ gcd(a, b) C(a+b, a) C(a+b+c, a+b)`
  have he₁ := le_of_dvd_mul hg₁ hx0 (he.trans (A_gcd (a + b) c))
  have he₂ := le_of_dvd_mul (mul_ne_zero hg₂ hy0) hx0
    ((he.trans (A_absorb (a + b + c) (a + b))).trans (Nat.mul_dvd_mul_right (A_gcd a b) _))
  rw [padicValNat.mul hg₂ hy0] at he₂
  refine summand_congr ?_ ?_
  · refine (K_choose hp h5 (u := padicValNat p (Nat.gcd (a + b) c))
      (pow_padicValNat_dvd.trans (Nat.gcd_dvd_left _ _))
      (pow_padicValNat_dvd.trans (Nat.gcd_dvd_right _ _)) pow_padicValNat_dvd).of_dvd ?_
    exact pow_dvd_pow _ (by omega)
  · refine (K_choose hp h5 (u := padicValNat p (Nat.gcd a b))
      (pow_padicValNat_dvd.trans (Nat.gcd_dvd_left _ _))
      (pow_padicValNat_dvd.trans (Nat.gcd_dvd_right _ _)) pow_padicValNat_dvd).of_dvd ?_
    exact pow_dvd_pow _ (by omega)

open P in
/-- **P₋**: if `1 ≤ m` and `p ^ e ∣ m`, then modulo `p ^ (3 e + 3)`,
`(C(m p + (a+b) p - 1, (a+b) p) C((a+b) p, a p))³ ≡ (C(m + (a+b) - 1, a+b) C(a+b, a))³` (`p ≥ 5`). -/
theorem P_summandNeg {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) {m a b e : ℕ} (hm : 1 ≤ m)
    (he : p ^ e ∣ m) :
    (((m * p + (a + b) * p - 1).choose ((a + b) * p) * ((a + b) * p).choose (a * p) : ℕ) : ℤ) ^ 3 ≡
      (((m + (a + b) - 1).choose (a + b) * (a + b).choose a : ℕ) : ℤ) ^ 3
        [ZMOD (p : ℤ) ^ (3 * e + 3)] := by
  have : Fact p.Prime := ⟨hp⟩
  rcases Nat.eq_zero_or_pos (a + b) with hab | hab
  · obtain ⟨rfl, rfl⟩ : a = 0 ∧ b = 0 := ⟨by omega, by omega⟩
    simp
  have hx0 : (m + (a + b) - 1).choose (a + b) ≠ 0 := (Nat.choose_pos (by omega)).ne'
  have hy0 : (a + b).choose a ≠ 0 := (Nat.choose_pos (by omega)).ne'
  have hg₁ : Nat.gcd m (a + b) ≠ 0 := Nat.gcd_ne_zero_left (by omega)
  have hg₂ : Nat.gcd a b ≠ 0 := by
    rw [Ne, Nat.gcd_eq_zero_iff]
    omega
  -- `p ^ e ∣ m ∣ gcd(m, a + b) C(m+a+b-1, a+b)`, and `m ∣ (a + b) C(m+a+b-1, a+b)`
  have he₁ := le_of_dvd_mul hg₁ hx0 (he.trans (A_gcdNeg m (a + b)))
  have he₂ := le_of_dvd_mul (mul_ne_zero hg₂ hy0) hx0
    ((he.trans (A_absorbNeg m (a + b))).trans (Nat.mul_dvd_mul_right (A_gcd a b) _))
  rw [padicValNat.mul hg₂ hy0] at he₂
  refine summand_congr ?_ ?_
  · refine (K_chooseNeg hp h5 (u := padicValNat p (Nat.gcd m (a + b)))
      (pow_padicValNat_dvd.trans (Nat.gcd_dvd_right _ _))
      (pow_padicValNat_dvd.trans (Nat.gcd_dvd_left _ _)) pow_padicValNat_dvd).of_dvd ?_
    exact pow_dvd_pow _ (by omega)
  · refine (K_choose hp h5 (u := padicValNat p (Nat.gcd a b))
      (pow_padicValNat_dvd.trans (Nat.gcd_dvd_left _ _))
      (pow_padicValNat_dvd.trans (Nat.gcd_dvd_right _ _)) pow_padicValNat_dvd).of_dvd ?_
    exact pow_dvd_pow _ (by omega)

end A141057
