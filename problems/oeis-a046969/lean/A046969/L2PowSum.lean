import A046969.Defs
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.Basic

/-!
# L2: `p² ∣ S_{2p}(p)`

Doubling permutes the nonzero residues mod `p`, and `(r + p·t)^{2p} ≡ r^{2p} (mod p²)` because
`p ∣ 2p`, so `2^{2p}·S_{2p}(p) ≡ S_{2p}(p) (mod p²)`. Since `2^{2p} - 1 ≡ 3 (mod p)` is a unit
for `p > 3`, `p² ∣ S_{2p}(p)`. Holds for every prime `p > 3` (no condition on `2p - 1`).
See `../PRD.md`, step 2.
-/

namespace A046969

namespace L2

/-- `a ≡ b (mod p)` gives `a^{2p} ≡ b^{2p} (mod p²)`. -/
theorem pow_two_mul_eq_of_modEq {p a b : ℕ} (h : a ≡ b [MOD p]) :
    (a : ZMod (p ^ 2)) ^ (2 * p) = (b : ZMod (p ^ 2)) ^ (2 * p) := by
  have hab : ((p : ℕ) : ZMod (p ^ 2)) ∣ (a : ZMod (p ^ 2)) - b := by
    obtain ⟨c, hc⟩ := (Nat.modEq_iff_dvd.mp h.symm)
    refine ⟨c, ?_⟩
    have := congrArg (Int.cast : ℤ → ZMod (p ^ 2)) hc
    push_cast at this
    exact this
  have hpow : ((p : ℕ) : ZMod (p ^ 2)) ^ 2 ∣ (a : ZMod (p ^ 2)) ^ p - (b : ZMod (p ^ 2)) ^ p := by
    have := dvd_sub_pow_of_dvd_sub hab 1
    rwa [pow_one] at this
  rw [← Nat.cast_pow, ZMod.natCast_self, zero_dvd_iff, sub_eq_zero] at hpow
  rw [mul_comm, pow_mul, pow_mul, hpow]

/-- `k ↦ 2k mod p` permutes `range p`, so it leaves `S_{2p}(p) mod p²` unchanged. -/
theorem sum_double_mod (p : ℕ) (hp : p.Prime) (h3 : 3 < p) :
    ∑ k ∈ Finset.range p, ((2 * k % p : ℕ) : ZMod (p ^ 2)) ^ (2 * p) =
      ∑ k ∈ Finset.range p, (k : ZMod (p ^ 2)) ^ (2 * p) := by
  obtain ⟨c, hc⟩ : ∃ c, 2 * c = p + 1 := by
    obtain ⟨k, hk⟩ := hp.odd_of_ne_two (by omega)
    exact ⟨k + 1, by omega⟩
  have hinv : ∀ k < p, k * (2 * c) % p = k := fun k hk ↦ by
    rw [hc, mul_add, mul_one, mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hk]
  refine Finset.sum_nbij' (fun k ↦ 2 * k % p) (fun k ↦ k * c % p) ?_ ?_ ?_ ?_ (fun _ _ ↦ rfl)
  · intro k _; simpa using Nat.mod_lt _ hp.pos
  · intro k _; simpa using Nat.mod_lt _ hp.pos
  · intro k hk
    rw [Finset.mem_range] at hk
    rw [Nat.mod_mul_mod, mul_comm 2 k, mul_assoc, hinv k hk]
  · intro k hk
    rw [Finset.mem_range] at hk
    rw [Nat.mul_mod_mod, ← mul_assoc, mul_comm 2 k, mul_assoc, hinv k hk]

end L2

theorem L2_sq_dvd_powSum (p : ℕ) (hp : p.Prime) (h3 : 3 < p) : p ^ 2 ∣ powSum (2 * p) p := by
  have := Fact.mk hp
  set S : ZMod (p ^ 2) := ∑ k ∈ Finset.range p, (k : ZMod (p ^ 2)) ^ (2 * p) with hS
  -- doubling: `2^{2p}·S = S`
  have hdouble : (2 : ZMod (p ^ 2)) ^ (2 * p) * S = S := by
    rw [hS, Finset.mul_sum, ← L2.sum_double_mod p hp h3]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [L2.pow_two_mul_eq_of_modEq (Nat.mod_modEq (2 * k) p), ← mul_pow]
    push_cast
    rfl
  -- `2^{2p} - 1 ≡ 3 (mod p)` is a unit mod `p²`
  have hunit : IsUnit ((2 : ZMod (p ^ 2)) ^ (2 * p) - 1) := by
    have h1 : 1 ≤ 2 ^ (2 * p) := Nat.one_le_two_pow
    have hcast : (((2 ^ (2 * p) - 1 : ℕ) : ZMod (p ^ 2))) = (2 : ZMod (p ^ 2)) ^ (2 * p) - 1 := by
      push_cast [h1]
      rfl
    rw [← hcast, ZMod.isUnit_iff_coprime, Nat.coprime_pow_right_iff two_pos, Nat.coprime_comm,
      hp.coprime_iff_not_dvd, ← ZMod.natCast_eq_zero_iff]
    push_cast [h1]
    rw [mul_comm, pow_mul, ZMod.pow_card]
    norm_num
    intro h
    have := (ZMod.natCast_eq_zero_iff 3 p).mp (by exact_mod_cast h)
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have hS0 : S = 0 := by
    have : ((2 : ZMod (p ^ 2)) ^ (2 * p) - 1) * S = 0 := by rw [sub_mul, hdouble, one_mul, sub_self]
    exact hunit.mul_right_eq_zero.mp this
  rw [← ZMod.natCast_eq_zero_iff, powSum]
  push_cast
  exact hS0

end A046969
