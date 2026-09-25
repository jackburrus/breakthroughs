import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination

/-!
# U: the squares of the units modulo `p ^ s` sum to zero

PRD step 2 input (node U). For a prime `p ≥ 5`, `∑ u² = 0` over the units `u` of `ZMod (p ^ s)`.
Proof: `u ↦ 2 u` permutes the units, so the sum `T` satisfies `T = 4 T`; then `3 T = 0`, and `3`
is a unit because `p ≥ 5`.
`U.sum_range_coprime` turns a sum over the units into one over the integers `0 ≤ a < c p ^ s` prime
to `p`: each block of `p ^ s` consecutive integers meets every unit exactly once. D uses both.
Checked by `../numerics/lemmas.py` (checks `U`, `U_blocks`); `U` also fails at `p = 3`.
-/

namespace A141057

namespace U

open Finset

/-- A natural number `0 < c < p` is a unit modulo `p ^ s`. -/
theorem isUnit_small {p s c : ℕ} (hp : p.Prime) (hc0 : 0 < c) (hcp : c < p) :
    IsUnit (c : ZMod (p ^ s)) :=
  (ZMod.isUnit_iff_coprime c (p ^ s)).mpr (Nat.Coprime.pow_right s
    (Nat.coprime_comm.mp ((hp.coprime_iff_not_dvd).mpr (Nat.not_dvd_of_pos_of_lt hc0 hcp))))

/-- One block: the integers `0 ≤ a < p ^ s` prime to `p` are the units of `ZMod (p ^ s)`. -/
theorem sum_block {M : Type*} [AddCommMonoid M] {p s : ℕ} (hp : p.Prime) (hs : 1 ≤ s)
    [NeZero (p ^ s)] (f : ZMod (p ^ s) → M) :
    ∑ a ∈ range (p ^ s) with ¬ p ∣ a, f a = ∑ u : (ZMod (p ^ s))ˣ, f u := by
  have hcop : ∀ a, ¬ p ∣ a → a.Coprime (p ^ s) := fun a ha =>
    Nat.Coprime.pow_right s (Nat.coprime_comm.mp ((hp.coprime_iff_not_dvd).mpr ha))
  refine sum_bij' (fun a ha => ZMod.unitOfCoprime a (hcop a (mem_filter.mp ha).2))
    (fun u _ => (u : ZMod (p ^ s)).val) (fun _ _ => mem_univ _) (fun u _ => ?_) (fun a ha => ?_)
    (fun u _ => ?_) (fun a _ => ?_)
  · -- the value of a unit is below `p ^ s` and prime to `p`
    refine mem_filter.mpr ⟨mem_range.mpr (ZMod.val_lt _), fun hdvd => hp.one_lt.ne' ?_⟩
    exact Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hdvd (ZMod.val_coe_unit_coprime u))
      (dvd_pow_self p (by omega))
  · rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast,
      Nat.mod_eq_of_lt (mem_range.mp (mem_filter.mp ha).1)]
  · exact Units.ext (by simp)
  · rw [ZMod.coe_unitOfCoprime]

/-- `c` blocks: over the integers `0 ≤ a < p ^ s c` prime to `p`, a function of `a` modulo `p ^ s`
sums to `c` times its sum over the units of `ZMod (p ^ s)`. -/
theorem sum_range_coprime {M : Type*} [AddCommMonoid M] {p s : ℕ} (hp : p.Prime) (hs : 1 ≤ s)
    [NeZero (p ^ s)] (f : ZMod (p ^ s) → M) (c : ℕ) :
    ∑ a ∈ range (p ^ s * c) with ¬ p ∣ a, f a = c • ∑ u : (ZMod (p ^ s))ˣ, f u := by
  have hps : p ∣ p ^ s := dvd_pow_self p (by omega)
  induction c with
  | zero => simp
  | succ c ih =>
    rw [succ_nsmul, ← ih, ← sum_block hp hs f, sum_filter, sum_filter, sum_filter, Nat.mul_succ,
      sum_range_add]
    congr 1
    refine sum_congr rfl fun a _ => ?_
    have hcast : ((p ^ s * c + a : ℕ) : ZMod (p ^ s)) = a := by
      rw [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, zero_add]
    simp only [Nat.dvd_add_right (dvd_mul_of_dvd_left hps c), hcast]

end U

open U in
/-- **U**: for a prime `p ≥ 5`, the squares of the units of `ZMod (p ^ s)` sum to zero. -/
theorem U_sum_unit_sq {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (s : ℕ) [NeZero (p ^ s)] :
    ∑ u : (ZMod (p ^ s))ˣ, (u : ZMod (p ^ s)) ^ 2 = 0 := by
  obtain ⟨two, htwo⟩ := isUnit_small (s := s) hp (c := 2) (by norm_num) (by omega)
  have h3 : IsUnit (3 : ZMod (p ^ s)) := by
    simpa using isUnit_small (s := s) hp (c := 3) (by norm_num) (by omega)
  -- doubling permutes the units
  have hT : ∑ u : (ZMod (p ^ s))ˣ, (u : ZMod (p ^ s)) ^ 2 =
      4 * ∑ u : (ZMod (p ^ s))ˣ, (u : ZMod (p ^ s)) ^ 2 := by
    calc ∑ u : (ZMod (p ^ s))ˣ, (u : ZMod (p ^ s)) ^ 2
        = ∑ u : (ZMod (p ^ s))ˣ, ((two * u : (ZMod (p ^ s))ˣ) : ZMod (p ^ s)) ^ 2 :=
          (Fintype.sum_equiv (Equiv.mulLeft two) _ _ fun _ => rfl).symm
      _ = 4 * ∑ u : (ZMod (p ^ s))ˣ, (u : ZMod (p ^ s)) ^ 2 := by
          simp only [Units.val_mul, htwo, mul_pow, ← Finset.mul_sum]
          norm_num
  exact h3.mul_right_eq_zero.mp (by linear_combination -hT)

end A141057
