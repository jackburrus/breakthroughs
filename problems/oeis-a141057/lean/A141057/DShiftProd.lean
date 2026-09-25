import A141057.UUnitSums
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Int.ModEq
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# D: shifting the units below `N` by a multiple of `p`

PRD step 2 (inside node K). Let `S` be the integers `0 ≤ a < N` prime to `p` and
`F(x) = ∏_{a ∈ S} (x + a)`. If `p ^ r ∣ x` and `p ^ s ∣ N`, then `F(x) ≡ F(0)` modulo
`p ^ (3 t)`, `t = min(r, s)` (`p ≥ 5`).
Proof, by squaring. The reflection `a ↦ N - a` permutes `S`, so
`F(x)² = ∏ (x + a)(x + N - a) = ∏ (b_a + y)` and `F(0)² = ∏ b_a`, with `b_a = a (N - a)` prime to
`p` and `y = x (x + N)`, which `p ^ (r + t)` divides. In `ZMod (p ^ (3 t))`, with `z_a = b_a⁻¹`,
`∏ (b_a + y) = (∏ b_a)(1 + y ∑ z_a + y² ρ)`. Here `y² = 0`, and `y ∑ z_a = 0` because modulo `p ^ t`
each `z_a` is `-(a⁻¹)²` (as `N ≡ 0`), and those sum to zero by U. So `p ^ (3 t)` divides
`F(x)² - F(0)² = (F(x) - F(0))(F(x) + F(0))`, and `F(x) + F(0) ≡ 2 F(0) (mod p)` is prime to `p`.
Checked by `../numerics/lemmas.py` (checks `D`, `D_pairs`); `D` also fails at `p = 3`.
-/

namespace A141057

namespace D

open Finset

/-- First-order expansion of `∏ (1 + y z_a)` in any commutative ring. -/
theorem prod_one_add {R : Type*} [CommRing R] (S : Finset ℕ) (z : ℕ → R) (y : R) :
    ∃ ρ : R, ∏ a ∈ S, (1 + y * z a) = 1 + y * ∑ a ∈ S, z a + y ^ 2 * ρ := by
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert j S hj ih =>
    obtain ⟨ρ, hρ⟩ := ih
    exact ⟨z j * ∑ a ∈ S, z a + ρ + y * z j * ρ, by rw [prod_insert hj, sum_insert hj, hρ]; ring⟩

/-- In `ZMod (p ^ k)`, an element whose image in `ZMod (p ^ j)` vanishes is a multiple of `p ^ j`. -/
theorem pow_dvd_of_castHom_eq_zero {p j k : ℕ} (hjk : j ≤ k) [NeZero (p ^ k)] (w : ZMod (p ^ k))
    (h : ZMod.castHom (pow_dvd_pow p hjk) (ZMod (p ^ j)) w = 0) : (p : ZMod (p ^ k)) ^ j ∣ w := by
  rw [← ZMod.natCast_zmod_val w, map_natCast, ZMod.natCast_eq_zero_iff] at h
  obtain ⟨c, hc⟩ := h
  rw [← ZMod.natCast_zmod_val w, hc, Nat.cast_mul, Nat.cast_pow]
  exact dvd_mul_right _ _

/-- `a ↦ N - a` maps the `a < N` prime to `p` into themselves, when `p ∣ N`. -/
theorem reflect_mem {p N a : ℕ} (hN : p ∣ N) (ha : a ∈ (range N).filter (fun a => ¬ p ∣ a)) :
    N - a ∈ (range N).filter (fun a => ¬ p ∣ a) := by
  rw [mem_filter, mem_range] at ha ⊢
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact ha.2 (dvd_zero p)
  refine ⟨by omega, fun h => ha.2 ?_⟩
  rw [← Nat.sub_sub_self ha.1.le]
  exact Nat.dvd_sub hN h

/-- The reflection `a ↦ N - a` does not change a product over the `a < N` prime to `p`. -/
theorem prod_reflect {M : Type*} [CommMonoid M] {p N : ℕ} (hN : p ∣ N) (g : ℕ → M) :
    ∏ a ∈ range N with ¬ p ∣ a, g (N - a) = ∏ a ∈ range N with ¬ p ∣ a, g a := by
  have hinv : ∀ a ∈ (range N).filter (fun a => ¬ p ∣ a), N - (N - a) = a := fun a ha =>
    Nat.sub_sub_self (mem_range.mp (mem_filter.mp ha).1).le
  exact prod_nbij' (fun a => N - a) (fun a => N - a) (fun _ => reflect_mem hN)
    (fun _ => reflect_mem hN) hinv hinv fun _ _ => rfl

/-- A prime `p` is prime to any integer it does not divide. -/
theorem isCoprime_of_not_dvd {p : ℕ} (hp : p.Prime) {z : ℤ} (h : ¬ (p : ℤ) ∣ z) :
    IsCoprime (p : ℤ) z := by
  rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd, Int.natAbs_natCast]
  exact (hp.coprime_iff_not_dvd).mpr fun h' => h (Int.natCast_dvd.mpr h')

end D

open D in
/-- **D**: `∏ (x + a) ≡ ∏ a (mod p ^ (3 min(r, s)))` over the `0 ≤ a < N` prime to `p`, when
`p ^ r ∣ x` and `p ^ s ∣ N` (`p ≥ 5`). -/
theorem D_shift_prod {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) {x : ℤ} {N r s : ℕ}
    (hx : (p : ℤ) ^ r ∣ x) (hN : p ^ s ∣ N) :
    ∏ a ∈ Finset.range N with ¬ p ∣ a, (x + a) ≡ ∏ a ∈ Finset.range N with ¬ p ∣ a, (a : ℤ)
      [ZMOD (p : ℤ) ^ (3 * min r s)] := by
  set t := min r s with ht
  rcases Nat.eq_zero_or_pos t with ht0 | ht1
  · rw [ht0, mul_zero, pow_zero]
    exact Int.modEq_one
  have htr : t ≤ r := min_le_left r s
  have hts : t ≤ s := min_le_right r s
  have ht3 : t ≤ 3 * t := by omega
  set S := (Finset.range N).filter (fun a => ¬ p ∣ a) with hS
  have hmem : ∀ a ∈ S, a < N ∧ ¬ p ∣ a := fun a ha => by
    rwa [hS, Finset.mem_filter, Finset.mem_range] at ha
  have hpN : p ∣ N := (dvd_pow_self p (by omega)).trans hN
  have hcop : ∀ k, ∀ a ∈ S, a.Coprime (p ^ k) ∧ (N - a).Coprime (p ^ k) := fun k a ha =>
    ⟨Nat.Coprime.pow_right k (Nat.coprime_comm.mp ((hp.coprime_iff_not_dvd).mpr (hmem a ha).2)),
      Nat.Coprime.pow_right k (Nat.coprime_comm.mp
        ((hp.coprime_iff_not_dvd).mpr (hmem (N - a) (reflect_mem hpN ha)).2))⟩
  set F := ∏ a ∈ S, (x + a) with hF
  set F₀ := ∏ a ∈ S, (a : ℤ) with hF₀
  -- the squares, as products over `S` of `b_a + y` and of `b_a`
  have hFF : F * F = ∏ a ∈ S, ((a : ℤ) * ((N - a : ℕ) : ℤ) + x * (x + N)) := by
    rw [hF]
    nth_rewrite 2 [← prod_reflect hpN (fun a => x + (a : ℤ))]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun a ha => ?_
    rw [Nat.cast_sub (hmem a ha).1.le]
    ring
  have hFF₀ : F₀ * F₀ = ∏ a ∈ S, ((a : ℤ) * ((N - a : ℕ) : ℤ)) := by
    rw [hF₀]
    nth_rewrite 2 [← prod_reflect hpN (fun a => (a : ℤ))]
    rw [← Finset.prod_mul_distrib]
  -- `p ^ (r + t) ∣ y = x (x + N)`
  have hy : (p : ℤ) ^ (r + t) ∣ x * (x + N) := by
    rw [pow_add]
    refine mul_dvd_mul hx (dvd_add ((pow_dvd_pow _ htr).trans hx) ?_)
    exact_mod_cast (pow_dvd_pow p hts).trans hN
  -- Step 1: `p ^ (3 t) ∣ F² - F₀²`, computed in `R = ZMod (p ^ (3 t))`.
  have hsq : (p : ℤ) ^ (3 * t) ∣ F * F - F₀ * F₀ := by
    have : NeZero (p ^ (3 * t)) := ⟨pow_ne_zero _ hp.ne_zero⟩
    have : NeZero (p ^ t) := ⟨pow_ne_zero _ hp.ne_zero⟩
    have hy2 : (((x * (x + N)) ^ 2 : ℤ) : ZMod (p ^ (3 * t))) = 0 := by
      have h2 : (p : ℤ) ^ ((r + t) * 2) ∣ (x * (x + N)) ^ 2 := by
        rw [pow_mul]
        exact pow_dvd_pow_of_dvd hy 2
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd, Nat.cast_pow]
      exact (pow_dvd_pow _ (by omega)).trans h2
    have hyR : (p : ZMod (p ^ (3 * t))) ^ (r + t) ∣ ((x * (x + N) : ℤ) : ZMod (p ^ (3 * t))) := by
      simpa using (Int.castRingHom (ZMod (p ^ (3 * t)))).map_dvd hy
    rw [hFF, hFF₀, show (p : ℤ) ^ (3 * t) = ((p ^ (3 * t) : ℕ) : ℤ) by push_cast; rfl,
      ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast at hy2 hyR ⊢
    set y : ZMod (p ^ (3 * t)) := (x : ZMod (p ^ (3 * t))) * (x + N) with hydef
    set z : ℕ → ZMod (p ^ (3 * t)) :=
      fun a => (a : ZMod (p ^ (3 * t)))⁻¹ * ((N - a : ℕ) : ZMod (p ^ (3 * t)))⁻¹ with hz
    have hbz : ∀ a ∈ S, (a : ZMod (p ^ (3 * t))) * ((N - a : ℕ) : ZMod (p ^ (3 * t))) * z a = 1 :=
      fun a ha => by
        have h1 := ZMod.coe_mul_inv_eq_one a (hcop (3 * t) a ha).1
        have h2 := ZMod.coe_mul_inv_eq_one (N - a) (hcop (3 * t) a ha).2
        rw [hz]
        linear_combination (((N - a : ℕ) : ZMod (p ^ (3 * t))) *
          ((N - a : ℕ) : ZMod (p ^ (3 * t)))⁻¹) * h1 + h2
    -- `∑ z_a` is a multiple of `p ^ t`: modulo `p ^ t`, `z_a = -(a⁻¹)²`, and U applies
    set φ := ZMod.castHom (pow_dvd_pow p ht3) (ZMod (p ^ t)) with hφ
    have hNt : ((N : ℕ) : ZMod (p ^ t)) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr ((pow_dvd_pow p hts).trans hN)
    have hφz : ∀ a ∈ S, φ (z a) = -((a : ZMod (p ^ t))⁻¹) ^ 2 := fun a ha => by
      have h1 : φ (z a) * ((a : ZMod (p ^ t)) * -(a : ZMod (p ^ t))) = 1 := by
        have := congrArg φ (hbz a ha)
        rw [map_mul, map_mul, map_natCast, map_natCast, map_one, Nat.cast_sub (hmem a ha).1.le,
          hNt, zero_sub] at this
        linear_combination this
      have h2 := ZMod.coe_mul_inv_eq_one a (hcop t a ha).1
      linear_combination (-(φ (z a)) * (1 + (a : ZMod (p ^ t)) * (a : ZMod (p ^ t))⁻¹)) * h2 +
        (-((a : ZMod (p ^ t))⁻¹ ^ 2)) * h1
    have hzsum : (p : ZMod (p ^ (3 * t))) ^ t ∣ ∑ a ∈ S, z a := by
      apply pow_dvd_of_castHom_eq_zero ht3
      rw [← hφ, map_sum, Finset.sum_congr rfl hφz, Finset.sum_neg_distrib, neg_eq_zero]
      obtain ⟨c, hc⟩ := (pow_dvd_pow p hts).trans hN
      rw [hS, hc, U.sum_range_coprime hp ht1 (fun w => w⁻¹ ^ 2) c]
      simp only [ZMod.inv_coe_unit]
      rw [Fintype.sum_equiv (Equiv.inv _) (fun u => ((u⁻¹ : (ZMod (p ^ t))ˣ) : ZMod (p ^ t)) ^ 2)
        (fun u => (u : ZMod (p ^ t)) ^ 2) fun _ => rfl, U_sum_unit_sq hp h5 t, smul_zero]
    -- so `y ∑ z_a = 0` in `R`
    have hp3t : (p : ZMod (p ^ (3 * t))) ^ (3 * t) = 0 := by
      rw [← Nat.cast_pow, ZMod.natCast_self]
    have hyz : y * ∑ a ∈ S, z a = 0 := by
      obtain ⟨c, hc⟩ := mul_dvd_mul hyR hzsum
      rw [hc, ← pow_add, show r + t + t = 3 * t + (r - t) by omega, pow_add, hp3t, zero_mul,
        zero_mul]
    obtain ⟨ρ, hρ⟩ := prod_one_add S z y
    have hprod : ∏ a ∈ S, ((a : ZMod (p ^ (3 * t))) * ((N - a : ℕ) : ZMod (p ^ (3 * t))) + y) =
        (∏ a ∈ S, ((a : ZMod (p ^ (3 * t))) * ((N - a : ℕ) : ZMod (p ^ (3 * t))))) *
          ∏ a ∈ S, (1 + y * z a) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun a ha => ?_
      linear_combination (-y) * hbz a ha
    rw [hprod, hρ]
    linear_combination (∏ a ∈ S, ((a : ZMod (p ^ (3 * t))) * ((N - a : ℕ) : ZMod (p ^ (3 * t))))) *
      (hyz + ρ * hy2)
  -- Step 2: cancel `F + F₀`, which is `2 F₀` modulo `p` and so prime to `p`.
  have hnd : ¬ (p : ℤ) ∣ F + F₀ := by
    have : Fact p.Prime := ⟨hp⟩
    intro hd
    have hx0 : (x : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd x p).mpr ((dvd_pow_self (p : ℤ) (by omega)).trans hx)
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hd
    push_cast [hF, hF₀, hx0, zero_add, ← two_mul] at h
    rcases mul_eq_zero.mp h with h2 | h0
    · have h2' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h2
      rw [ZMod.natCast_eq_zero_iff] at h2'
      exact absurd (Nat.le_of_dvd two_pos h2') (by omega)
    · obtain ⟨a, ha, ha0⟩ := Finset.prod_eq_zero_iff.mp h0
      rw [ZMod.natCast_eq_zero_iff] at ha0
      exact (hmem a ha).2 ha0
  rw [Int.modEq_iff_dvd, dvd_sub_comm]
  rw [show F * F - F₀ * F₀ = (F - F₀) * (F + F₀) by ring] at hsq
  exact ((isCoprime_of_not_dvd hp hnd).pow_left).dvd_of_dvd_mul_right hsq

end A141057
