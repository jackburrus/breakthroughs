import A141057.KJacobsthal
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# K⁻: Jacobsthal–Kazandzidis for the negative-index binomials

PRD step 2, negative side. `C(-m, i) = (-1)^i C(m + i - 1, i)`, and for `m ≥ 1`
`C(m p + i p - 1, i p) ≡ C(m + i - 1, i) (mod p ^ (v_p C(m + i - 1, i) + 3 + 3 min(v_p i, v_p m)))`.
Proof idea: `(m + i) C(m + i - 1, i) = m C(m + i, i)`, and the same at `(m p, i p)` after
cancelling `p`, so `(m + i) (C(m p + i p - 1, i p) - C(m + i - 1, i)) = m (C((m + i) p, i p) - C(m + i, i))`.
Apply K with `(A, B) = (m + i, i)` and divide by the `p`-part of `m + i`, using
`v_p C(m + i - 1, i) = v_p m + v_p C(m + i, i) - v_p (m + i)`.
Checked by `../numerics/lemmas.py` (check `KNeg`).
-/

namespace A141057

/-- **K⁻**: `p ^ (v_p C(m+i-1, i) + 3 + 3 min(v_p i, v_p m)) ∣ C(m p + i p - 1, i p) - C(m + i - 1, i)`. -/
theorem KNeg_jacobsthal (p m i : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hm : 1 ≤ m) :
    (p : ℤ) ^ (padicValNat p ((m + i - 1).choose i) + 3 +
        3 * min (padicValNat p i) (padicValNat p m)) ∣
      ((m * p + i * p - 1).choose (i * p) : ℤ) - ((m + i - 1).choose i : ℤ) := by
  have : Fact p.Prime := ⟨hp⟩
  have hp0 : 0 < p := hp.pos
  have hmp : 1 ≤ m * p := Nat.mul_pos hm hp0
  -- K at `(A, B) = (m + i, i)`
  have hK := K_jacobsthal p (m + i) i hp hp5 (by omega)
  rw [Nat.add_sub_cancel, add_mul] at hK
  -- absorption, `(n + 1) C(n, k) = (n + 1 - k) C(n + 1, k)`, at `n + 1 = m + i` and at `m p + i p`
  have hI1 : (m + i) * (m + i - 1).choose i = m * (m + i).choose i := by
    have h := Nat.choose_mul_succ_eq (m + i - 1) i
    rw [show m + i - 1 + 1 = m + i by omega, show m + i - i = m by omega] at h
    rw [mul_comm, h, mul_comm]
  have hI2 : (m + i) * (m * p + i * p - 1).choose (i * p) = m * (m * p + i * p).choose (i * p) := by
    have h := Nat.choose_mul_succ_eq (m * p + i * p - 1) (i * p)
    rw [show m * p + i * p - 1 + 1 = m * p + i * p by omega,
      show m * p + i * p - i * p = m * p by omega] at h
    apply Nat.eq_of_mul_eq_mul_right hp0
    calc (m + i) * (m * p + i * p - 1).choose (i * p) * p
        = (m * p + i * p - 1).choose (i * p) * (m * p + i * p) := by ring
      _ = (m * p + i * p).choose (i * p) * (m * p) := h
      _ = m * (m * p + i * p).choose (i * p) * p := by ring
  -- so `(m + i) (c - d) = m (C((m + i) p, i p) - C(m + i, i))`
  have hZ : ((m + i : ℕ) : ℤ) * (((m * p + i * p - 1).choose (i * p) : ℤ) - ((m + i - 1).choose i : ℤ)) =
      (m : ℤ) * (((m * p + i * p).choose (i * p) : ℤ) - ((m + i).choose i : ℤ)) := by
    rw [mul_sub, mul_sub]
    exact_mod_cast congrArg₂ (fun a b : ℕ => (a : ℤ) - b) hI2 hI1
  -- compare valuations: `v (m + i) + v C(m + i - 1, i) = v m + v C(m + i, i)`
  have hv := congrArg (padicValNat p) hI1
  rw [padicValNat.mul (by omega) (Nat.choose_pos (by omega)).ne',
    padicValNat.mul (by omega) (Nat.choose_pos (by omega)).ne'] at hv
  rw [padicValInt_dvd_iff]
  by_cases h0 : ((m * p + i * p - 1).choose (i * p) : ℤ) - ((m + i - 1).choose i : ℤ) = 0
  · exact Or.inl h0
  right
  have h1 : (p : ℤ) ^ (padicValNat p ((m + i).choose i) + 3 +
      3 * min (padicValNat p i) (padicValNat p m) + padicValNat p m) ∣
      ((m + i : ℕ) : ℤ) * (((m * p + i * p - 1).choose (i * p) : ℤ) - ((m + i - 1).choose i : ℤ)) := by
    rw [hZ, pow_add, mul_comm (m : ℤ)]
    exact mul_dvd_mul hK (by exact_mod_cast pow_padicValNat_dvd)
  rw [padicValInt_dvd_iff] at h1
  rcases h1 with h1 | h1
  · exfalso
    exact mul_ne_zero (by exact_mod_cast (show m + i ≠ 0 by omega)) h0 h1
  rw [padicValInt.mul (by exact_mod_cast (show m + i ≠ 0 by omega)) h0, padicValInt.of_nat] at h1
  omega

end A141057
