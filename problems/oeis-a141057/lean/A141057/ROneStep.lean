import A141057.Defs
import A141057.SSplit
import A141057.VVanish
import A141057.PPerTerm

/-!
# R: the one-step supercongruence, and the reduction to it

PRD step 3 (node R) and the final reduction (node M). For `m ≥ 1`,
`p ^ (3 (v_p m + 1)) ∣ aInt(m p) - aInt(m)` and `∣ aInt(-m p) - aInt(-m)`: expand `aInt` into
the double sums of cubes, then apply S with V (cubed, using `v_p (m p) = v_p m + 1`) and P.
For `n < 0` the summands carry the sign `(-1)^k`, and `(-1)^(i p) = (-1)^i` as `p` is odd.
`R_dvd` takes `m = |n| p ^ (k - 1)`, whose valuation is at least `k - 1`; `Main.lean` turns it
into the upstream `Int.ModEq` statement.
Checked by `../numerics/lemmas.py` (checks `R_pos`, `R_neg`) and `../numerics/check.py`.
-/

namespace A141057

namespace R

open Finset

/-- `aInt N` for `N ≥ 0`, as the triangle of cubed summands `(C(N, k) C(k, j))³`. -/
theorem aInt_natCast (N : ℕ) :
    aInt (N : ℤ) =
      ∑ k ∈ range (N + 1), ∑ j ∈ range (k + 1), ((N.choose k * k.choose j : ℕ) : ℤ) ^ 3 := by
  simp only [aInt, Nat.cast_nonneg, if_true, Int.toNat_natCast]
  push_cast
  refine sum_congr rfl fun k _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun j _ => ?_
  ring

/-- `aInt (-N)` for `N ≥ 1`, as the signed triangle `(-1)^k (C(N+k-1, k) C(k, j))³`. -/
theorem aInt_neg_natCast (N : ℕ) (hN : 1 ≤ N) :
    aInt (-(N : ℤ)) = ∑ k ∈ range (N + 1), ∑ j ∈ range (k + 1),
      (-1) ^ k * (((N + k - 1).choose k * k.choose j : ℕ) : ℤ) ^ 3 := by
  have h : ¬ (0 ≤ -(N : ℤ)) := by omega
  simp only [aInt, h, if_false, neg_neg, Int.toNat_natCast]
  refine sum_congr rfl fun k _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun j _ => ?_
  have hs : ((-1 : ℤ) ^ k) ^ 3 = (-1) ^ k := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  push_cast
  rw [mul_pow, hs]
  ring

end R

/-- **R₊**: `p ^ (3 (v_p m + 1)) ∣ aInt(m p) - aInt(m)` for `m ≥ 1`. -/
theorem R_pos (p m : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hm : 1 ≤ m) :
    (p : ℤ) ^ (3 * (padicValNat p m + 1)) ∣ aInt ((m * p : ℕ) : ℤ) - aInt (m : ℤ) := by
  have : Fact p.Prime := ⟨hp⟩
  have hv : padicValNat p (m * p) = padicValNat p m + 1 := by
    rw [padicValNat.mul (by omega) hp.ne_zero, padicValNat.self hp.one_lt]
  rw [R.aInt_natCast, R.aInt_natCast]
  refine S_split p m hp.pos _ (fun k j => (((m * p).choose k * k.choose j : ℕ) : ℤ) ^ 3)
    (fun i l => ((m.choose i * i.choose l : ℕ) : ℤ) ^ 3) ?_ ?_
  · intro k j _ _ hkj
    have h := V_pos p (m * p) k j hp hkj
    rw [hv] at h
    rw [mul_comm 3, pow_mul]
    exact pow_dvd_pow_of_dvd (by exact_mod_cast h) 3
  · intro i l hi hl
    exact P_pos p m i l hp hp5 hi hl

/-- **R₋**: `p ^ (3 (v_p m + 1)) ∣ aInt(-m p) - aInt(-m)` for `m ≥ 1`. -/
theorem R_neg (p m : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hm : 1 ≤ m) :
    (p : ℤ) ^ (3 * (padicValNat p m + 1)) ∣ aInt (-((m * p : ℕ) : ℤ)) - aInt (-(m : ℤ)) := by
  have : Fact p.Prime := ⟨hp⟩
  have hv : padicValNat p (m * p) = padicValNat p m + 1 := by
    rw [padicValNat.mul (by omega) hp.ne_zero, padicValNat.self hp.one_lt]
  rw [R.aInt_neg_natCast (m * p) (Nat.mul_pos hm hp.pos), R.aInt_neg_natCast m hm]
  refine S_split p m hp.pos _
    (fun k j => (-1) ^ k * (((m * p + k - 1).choose k * k.choose j : ℕ) : ℤ) ^ 3)
    (fun i l => (-1) ^ i * (((m + i - 1).choose i * i.choose l : ℕ) : ℤ) ^ 3) ?_ ?_
  · intro k j _ _ hkj
    have h := V_neg p (m * p) k j hp hkj
    rw [hv] at h
    refine Dvd.dvd.mul_left ?_ _
    rw [mul_comm 3, pow_mul]
    exact pow_dvd_pow_of_dvd (by exact_mod_cast h) 3
  · intro i l _ hl
    -- `p` is odd, so `(-1)^(i p) = (-1)^i`
    have hsign : (-1 : ℤ) ^ (i * p) = (-1) ^ i := by
      rw [mul_comm, pow_mul, (hp.odd_of_ne_two (by omega)).neg_one_pow]
    rw [hsign, ← mul_sub]
    exact (P_neg p m i l hp hp5 hm hl).mul_left _

/-- **R**: both signs at once, for any integer `n ≠ 0`. -/
theorem R_oneStep (p : ℕ) (n : ℤ) (hp : p.Prime) (hp5 : 5 ≤ p) (hn : n ≠ 0) :
    (p : ℤ) ^ (3 * (padicValNat p n.natAbs + 1)) ∣ aInt (n * p) - aInt n := by
  rcases lt_or_gt_of_ne hn with h | h
  · obtain ⟨m, rfl⟩ := Int.exists_eq_neg_ofNat h.le
    rw [Int.natAbs_neg, Int.natAbs_natCast, show -(m : ℤ) * p = -((m * p : ℕ) : ℤ) by push_cast; ring]
    exact R_neg p m hp hp5 (by omega)
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h.le
    rw [Int.natAbs_natCast, show (m : ℤ) * p = ((m * p : ℕ) : ℤ) by push_cast; ring]
    exact R_pos p m hp hp5 (by omega)

/-- **M**: the conjecture as a divisibility, `p ^ (3 k) ∣ aInt(n p ^ (k - 1)) - aInt(n p ^ k)`. -/
theorem R_dvd (p k : ℕ) (n : ℤ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 1 ≤ k) (hn : n ≠ 0) :
    (p : ℤ) ^ (3 * k) ∣ aInt (n * p ^ (k - 1)) - aInt (n * p ^ k) := by
  have : Fact p.Prime := ⟨hp⟩
  -- one step at `m = n p ^ (k - 1)`, with `v_p |m| = v_p |n| + k - 1 ≥ k - 1`
  have hm : n * (p : ℤ) ^ (k - 1) ≠ 0 := mul_ne_zero hn (pow_ne_zero _ (by exact_mod_cast hp.ne_zero))
  have h := R_oneStep p (n * p ^ (k - 1)) hp hp5 hm
  rw [mul_assoc, ← pow_succ, Nat.sub_add_cancel hk, Int.natAbs_mul, Int.natAbs_pow,
    Int.natAbs_natCast, padicValNat.mul (Int.natAbs_ne_zero.mpr hn) (pow_ne_zero _ hp.ne_zero),
    padicValNat.prime_pow] at h
  rw [dvd_sub_comm]
  exact (pow_dvd_pow _ (by omega)).trans h

end A141057
