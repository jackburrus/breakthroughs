import A046969.L1Den
import A046969.FFaulhaber
import A046969.L2PowSum
import A046969.L3PowSum

/-!
# L4: `a p = 12 (2p - 1)`

With `q = 2p - 1` and `B_{2p} = N / 6` (L1): F with L2 gives `p ∣ N`, and F with L3 (at
`q + 1 = 2p`) gives `q ∤ N`. Then `B_{2p} / (2p·q) = N / (12·p·q) = N' / (12·q)` with
`N = p·N'` and `N'` coprime to 2, 3 and `q`, so `a p = 12 q`. See `../PRD.md`, step 4.
-/

namespace A046969

namespace L4

/-- A prime `ℓ` dividing `m·n` in `ℤ` divides `m` when `ℓ ∤ n`. -/
theorem int_dvd_of_dvd_mul {ℓ : ℕ} (hℓ : ℓ.Prime) {m : ℤ} {n : ℕ} (hn : ¬ ℓ ∣ n)
    (h : (ℓ : ℤ) ∣ m * n) : (ℓ : ℤ) ∣ m := by
  rw [Int.natCast_dvd, Int.natAbs_mul, Int.natAbs_natCast] at h
  exact Int.natCast_dvd.mpr ((hℓ.dvd_mul.mp h).resolve_right hn)

/-- F with L2: `p` divides the numerator of `B_{2p}`, since `B_{2p} = p·(S/p² - r)`. -/
theorem p_dvd_num (p : ℕ) (hp : p.Prime) (h3 : 3 < p) (hden : (bernoulli (2 * p)).den = 6) :
    (p : ℤ) ∣ (bernoulli (2 * p)).num := by
  have hp1 : ¬ p ∣ 2 * p + 1 := fun h ↦
    hp.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right (dvd_mul_left p 2)).mp h))
  obtain ⟨r, hr, hF⟩ := F_faulhaber p (2 * p) hp (by omega) (even_two_mul p) hp1
  obtain ⟨c, hc⟩ := L2_sq_dvd_powSum p hp h3
  rw [hc] at hF
  push_cast at hF
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hB : bernoulli (2 * p) = p * c - p * r := by
    apply mul_left_cancel₀ hp0
    linear_combination (-1 : ℚ) * hF
  have hBn : ((bernoulli (2 * p)).num : ℚ) = bernoulli (2 * p) * 6 := by
    rw [← Rat.mul_den_eq_num, hden]; norm_num
  have hrn : (r.num : ℚ) = r * r.den := (Rat.mul_den_eq_num r).symm
  have key : (bernoulli (2 * p)).num * r.den = (p : ℤ) * (6 * (c * r.den - r.num)) := by
    have : ((bernoulli (2 * p)).num * r.den : ℚ) = (p : ℚ) * (6 * (c * r.den - r.num)) := by
      rw [hBn, hrn, hB]; ring
    exact_mod_cast this
  exact int_dvd_of_dvd_mul hp hr ⟨_, key⟩

/-- F with L3: `q` does not divide the numerator of `B_{q+1}`, since `B_{q+1} = S/q - q·r`
and `12·(S/q) ≡ 1 (mod q)`. -/
theorem q_not_dvd_num (q : ℕ) (hq : q.Prime) (h5 : 5 ≤ q) (hden : (bernoulli (q + 1)).den = 6) :
    ¬ (q : ℤ) ∣ (bernoulli (q + 1)).num := by
  have hq2 : ¬ q ∣ q + 1 + 1 := fun h ↦ by
    have := Nat.le_of_dvd two_pos ((Nat.dvd_add_right (dvd_refl q)).mp h); omega
  obtain ⟨r, hr, hF⟩ :=
    F_faulhaber q (q + 1) hq (by omega) (hq.odd_of_ne_two (by omega)).add_one hq2
  obtain ⟨⟨s, hs⟩, h12⟩ := L3_powSum_div q hq h5
  rw [hs, Nat.mul_div_cancel_left s hq.pos] at h12
  rw [hs] at hF
  push_cast at hF
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne_zero
  have hB : bernoulli (q + 1) = s - q * r := by
    apply mul_left_cancel₀ hq0
    linear_combination (-1 : ℚ) * hF
  have hBn : ((bernoulli (q + 1)).num : ℚ) = bernoulli (q + 1) * 6 := by
    rw [← Rat.mul_den_eq_num, hden]; norm_num
  have hrn : (r.num : ℚ) = r * r.den := (Rat.mul_den_eq_num r).symm
  have key : (6 * s * r.den : ℕ) = (bernoulli (q + 1)).num * r.den + (q : ℤ) * (6 * r.num) := by
    have : ((6 * s * r.den : ℕ) : ℚ) =
        ((bernoulli (q + 1)).num * r.den : ℚ) + (q : ℚ) * (6 * r.num) := by
      push_cast; rw [hBn, hrn, hB]; ring
    exact_mod_cast this
  intro hN
  have h6 : q ∣ 6 * s * r.den := by
    rw [← Int.natCast_dvd_natCast, key]
    exact dvd_add (dvd_mul_of_dvd_left hN _) (dvd_mul_right _ _)
  have h12s : q ∣ 12 * s := by
    rw [show 12 * s = 2 * (6 * s) by ring]
    exact dvd_mul_of_dvd_right ((hq.dvd_mul.mp h6).resolve_right hr) 2
  have h1 : 12 * s % q = 1 % q := h12
  rw [Nat.mod_eq_zero_of_dvd h12s, Nat.mod_eq_of_lt hq.one_lt] at h1
  exact zero_ne_one h1

end L4

theorem L4_a_eq (p : ℕ) (hp : p.Prime) (hp' : (2 * p - 1).Prime) (h3 : 3 < p) :
    a p = 12 * (2 * p - 1) := by
  have hden := L1_den_bernoulli p hp hp' h3
  have hpN := L4.p_dvd_num p hp h3 hden
  have ha : a p = (bernoulli (2 * p) / ((2 * p * (2 * p - 1) : ℕ) : ℚ)).den := by
    simp only [a, hp.ne_zero, if_false]
  rw [ha]
  obtain ⟨q, hq⟩ : ∃ q, 2 * p - 1 = q := ⟨_, rfl⟩
  rw [hq] at hp' ⊢
  have h2p : 2 * p = q + 1 := by omega
  have hqN := L4.q_not_dvd_num q hp' (by omega) (h2p ▸ hden)
  rw [← h2p] at hqN
  obtain ⟨N, hN⟩ := hpN
  have hB : bernoulli (2 * p) = (p * N : ℚ) / 6 := by
    rw [← Rat.num_div_den (bernoulli (2 * p)), hden, hN]; push_cast; ring
  have hN6 : Nat.Coprime N.natAbs 6 := by
    have := (bernoulli (2 * p)).reduced
    rw [hden, hN, Int.natAbs_mul] at this
    exact Nat.Coprime.coprime_mul_left this
  have hNq : Nat.Coprime N.natAbs q := by
    rw [Nat.coprime_comm, hp'.coprime_iff_not_dvd]
    intro h
    exact hqN (hN ▸ Dvd.dvd.mul_left (Int.natCast_dvd.mpr h) _)
  have hN12q : Nat.Coprime N.natAbs (12 * q) :=
    Nat.Coprime.mul_right
      (Nat.Coprime.coprime_dvd_right (by norm_num : 12 ∣ 6 ^ 2) (Nat.Coprime.pow_right 2 hN6)) hNq
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hp'.ne_zero
  have heq : bernoulli (2 * p) / ((2 * p * q : ℕ) : ℚ) = (N : ℚ) / (((12 * q : ℕ) : ℤ) : ℚ) := by
    rw [hB, div_div, div_eq_div_iff (by push_cast; positivity) (by push_cast; positivity)]
    push_cast; ring
  have hden' := Rat.den_div_eq_of_coprime (a := N) (b := ((12 * q : ℕ) : ℤ))
    (by have := hp'.pos; positivity) (by rwa [Int.natAbs_natCast])
  rw [← heq] at hden'
  exact_mod_cast hden'

end A046969
