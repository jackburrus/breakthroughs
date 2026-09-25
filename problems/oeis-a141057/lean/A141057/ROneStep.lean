import A141057.Defs
import A141057.SSplit
import A141057.VVanish
import A141057.PPerTerm

/-!
# R: the one-step supercongruence, and the reduction to it

PRD step 3 (node R) and the final reduction (node M). If `p ^ e ∣ m`, then
`aInt(m p) ≡ aInt(m)` and `aInt(-m p) ≡ aInt(-m)` modulo `p ^ (3 e + 3)`: expand `aInt` into the
triangles of cubed summands, then apply S, with V (cubed, as `p ^ (e + 1) ∣ m p`) for the indices
not both multiples of `p`, and P for the rest, written `(l p, (l + b) p)` inside `(l + b + c) p`.
For `n < 0` the summands carry the sign `(-1)^k`, and `(-1)^(i p) = (-1)^i` as `p` is odd.
`R_stepInt` joins the signs (`n = 0` is trivial), and `R_pow` takes `n p ^ j`, which `p ^ j` divides;
`Main.lean` reindexes `k = j + 1` to reach the upstream statement.
Checked by `../numerics/lemmas.py` (checks `R_step`, `R_stepNeg`, `R_stepInt`) and `../numerics/check.py`.
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

/-- **R₊**: if `p ^ e ∣ m`, then `aInt(m p) ≡ aInt(m) (mod p ^ (3 e + 3))`. -/
theorem R_step {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) {m e : ℕ} (he : p ^ e ∣ m) :
    aInt ((m * p : ℕ) : ℤ) ≡ aInt (m : ℤ) [ZMOD (p : ℤ) ^ (3 * e + 3)] := by
  have hmp : p ^ (e + 1) ∣ m * p := by
    rw [pow_succ]
    exact Nat.mul_dvd_mul he dvd_rfl
  rw [R.aInt_natCast, R.aInt_natCast, Int.modEq_iff_dvd, dvd_sub_comm]
  refine S_split p m hp.pos _ (fun k j => (((m * p).choose k * k.choose j : ℕ) : ℤ) ^ 3)
    (fun i l => ((m.choose i * i.choose l : ℕ) : ℤ) ^ 3) ?_ ?_
  · intro k j _ _ hkj
    rw [show 3 * e + 3 = (e + 1) * 3 by ring, pow_mul]
    exact pow_dvd_pow_of_dvd (by exact_mod_cast V_pos hp hmp hkj) 3
  · -- write `l ≤ i ≤ m` as `l`, `i = l + b`, `m = l + b + c`
    intro i l hi hl
    obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hl
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hi
    exact (P_summand hp h5 he).symm.dvd

/-- **R₋**: if `1 ≤ m` and `p ^ e ∣ m`, then `aInt(-m p) ≡ aInt(-m) (mod p ^ (3 e + 3))`. -/
theorem R_stepNeg {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) {m e : ℕ} (hm : 1 ≤ m) (he : p ^ e ∣ m) :
    aInt (-((m * p : ℕ) : ℤ)) ≡ aInt (-(m : ℤ)) [ZMOD (p : ℤ) ^ (3 * e + 3)] := by
  have hmp : p ^ (e + 1) ∣ m * p := by
    rw [pow_succ]
    exact Nat.mul_dvd_mul he dvd_rfl
  rw [R.aInt_neg_natCast (m * p) (Nat.mul_pos hm hp.pos), R.aInt_neg_natCast m hm,
    Int.modEq_iff_dvd, dvd_sub_comm]
  refine S_split p m hp.pos _
    (fun k j => (-1) ^ k * (((m * p + k - 1).choose k * k.choose j : ℕ) : ℤ) ^ 3)
    (fun i l => (-1) ^ i * (((m + i - 1).choose i * i.choose l : ℕ) : ℤ) ^ 3) ?_ ?_
  · intro k j _ _ hkj
    refine Dvd.dvd.mul_left ?_ _
    rw [show 3 * e + 3 = (e + 1) * 3 by ring, pow_mul]
    exact pow_dvd_pow_of_dvd (by exact_mod_cast V_neg hp hmp hkj) 3
  · intro i l _ hl
    obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hl
    -- `p` is odd, so `(-1)^((l + b) p) = (-1)^(l + b)`
    have hsign : (-1 : ℤ) ^ ((l + b) * p) = (-1) ^ (l + b) := by
      rw [pow_mul', (hp.odd_of_ne_two (by omega)).neg_one_pow]
    rw [hsign, ← mul_sub]
    exact (P_summandNeg hp h5 hm he).symm.dvd.mul_left _

/-- **R**: for an integer `n` with `p ^ e ∣ n`, `aInt(n p) ≡ aInt(n) (mod p ^ (3 e + 3))`. -/
theorem R_stepInt {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) {n : ℤ} {e : ℕ} (he : (p : ℤ) ^ e ∣ n) :
    aInt (n * p) ≡ aInt n [ZMOD (p : ℤ) ^ (3 * e + 3)] := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · have hm : p ^ e ∣ m := by exact_mod_cast he
    simpa using R_step hp h5 hm
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    have hm' : p ^ e ∣ m := by
      rw [dvd_neg] at he
      exact_mod_cast he
    rw [show -(m : ℤ) * p = -((m * p : ℕ) : ℤ) by push_cast; ring]
    exact R_stepNeg hp h5 hm hm'

/-- **M**: one more factor of `p`, `aInt(n p ^ (j + 1)) ≡ aInt(n p ^ j) (mod p ^ (3 (j + 1)))`. -/
theorem R_pow {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (n : ℤ) (j : ℕ) :
    aInt (n * (p : ℤ) ^ (j + 1)) ≡ aInt (n * (p : ℤ) ^ j) [ZMOD (p : ℤ) ^ (3 * (j + 1))] := by
  rw [pow_succ, ← mul_assoc, show 3 * (j + 1) = 3 * j + 3 by ring]
  exact R_stepInt hp h5 (dvd_mul_left _ _)

end A141057
