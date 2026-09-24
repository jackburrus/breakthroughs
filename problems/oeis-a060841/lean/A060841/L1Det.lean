import A060841.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# L1: closed form of the lcm-matrix determinant

`1 / det M_n = ∏_{k=1}^{n} k² / φ(k)`, via Smith's determinant `det (gcd i j) = ∏ φ(k)`
and `M = D⁻¹ G D⁻¹` with `D = diag(1, …, n)`. See `../BLUEPRINT.md` §1.

The statement also forces `det M_n ≠ 0` (`closedForm n ≠ 0`, and `(0 : ℚ)⁻¹ = 0`), which the
integer direction of the iff depends on (blueprint §8, flag 3).
-/

namespace A060841

open Matrix Finset

/-- A copy of `OeisA60841.lcmMatrix`, so this file need not import upstream (and all of
Mathlib). `Main.lean` checks it is the upstream definition by `rfl`; do not change it. -/
def lcmMat (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun i j : Fin n ↦ 1 / ((Nat.lcm (i.val + 1) (j.val + 1) : ℚ))

/-! ### Smith's determinant: `G = A · diag(φ) · Aᵀ`

Helpers live in `A060841.L1` so they cannot clash with L2/L3 helpers or `Main.lean` when all
three lemma files are imported together. -/

namespace L1

/-- The divisibility matrix: `A i d = 1` if `d + 1 ∣ i + 1`, else `0` (indices shifted by one). -/
def divMat (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun i d : Fin n ↦ if d.val + 1 ∣ i.val + 1 then 1 else 0

/-- The gcd matrix `G i j = gcd (i + 1) (j + 1)`. -/
def gcdMat (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun i j : Fin n ↦ (Nat.gcd (i.val + 1) (j.val + 1) : ℚ)

/-- `d ↦ φ (d + 1)`, the diagonal of the middle factor. -/
def phiVec (n : ℕ) : Fin n → ℚ := fun d ↦ (Nat.totient (d.val + 1) : ℚ)

/-- `A` is lower triangular: `d + 1 ∣ i + 1` forces `d ≤ i`. -/
theorem divMat_isLowerTriangular (n : ℕ) : (divMat n).IsLowerTriangular := by
  intro i d hid
  have hlt : i.val < d.val := hid
  simp only [divMat, of_apply]
  rw [if_neg]
  intro h
  have := Nat.le_of_dvd (Nat.succ_pos _) h
  omega

theorem det_divMat (n : ℕ) : (divMat n).det = 1 := by
  rw [det_of_isLowerTriangular _ (divMat_isLowerTriangular n)]
  simp [divMat]

/-- Gauss's identity read over `Fin n`: for `1 ≤ g ≤ n`, `∑_{d ≤ n, d ∣ g} φ d = g`. -/
theorem sum_totient_fin {n g : ℕ} (hg : g ≠ 0) (hgn : g ≤ n) :
    ∑ d : Fin n, (if d.val + 1 ∣ g then Nat.totient (d.val + 1) else 0) = g := by
  rw [Fin.sum_univ_eq_sum_range (fun d ↦ if d + 1 ∣ g then Nat.totient (d + 1) else 0)]
  have h := Finset.sum_range_succ' (fun d ↦ if d ∣ g then Nat.totient d else 0) n
  simp only [Nat.totient_zero, ite_self, add_zero] at h
  rw [← h, ← Finset.sum_filter]
  conv_rhs => rw [← Nat.sum_totient g]
  congr 1
  ext m
  simp only [mem_filter, mem_range, Nat.mem_divisors]
  constructor
  · rintro ⟨_, h⟩
    exact ⟨h, hg⟩
  · rintro ⟨h, _⟩
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hg) h
    exact ⟨by omega, h⟩

/-- The entrywise factorization `G = A · diag(φ) · Aᵀ`. -/
theorem gcdMat_eq (n : ℕ) :
    gcdMat n = divMat n * diagonal (phiVec n) * (divMat n)ᵀ := by
  ext i j
  have hg : Nat.gcd (i.val + 1) (j.val + 1) ≠ 0 := Nat.gcd_ne_zero_left (Nat.succ_ne_zero _)
  have hgn : Nat.gcd (i.val + 1) (j.val + 1) ≤ n :=
    (Nat.gcd_le_left _ (Nat.succ_pos _)).trans i.isLt
  rw [mul_apply]
  simp only [gcdMat, divMat, phiVec, of_apply, mul_diagonal, transpose_apply]
  rw [← sum_totient_fin hg hgn]
  push_cast
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  simp only [Nat.dvd_gcd_iff]
  split_ifs <;> simp_all

theorem det_gcdMat (n : ℕ) : (gcdMat n).det = ∏ d, phiVec n d := by
  rw [gcdMat_eq, det_mul, det_mul, det_transpose, det_divMat, det_diagonal, one_mul, mul_one]

/-! ### Scaling: `M = Δ⁻¹ G Δ⁻¹` -/

/-- `i ↦ 1 / (i + 1)`, the diagonal of `Δ⁻¹`. -/
def invVec (n : ℕ) : Fin n → ℚ := fun i ↦ ((i.val + 1 : ℕ) : ℚ)⁻¹

/-- `1 / lcm(a, b) = gcd(a, b) / (a b)`, entrywise, from `gcd · lcm = a b`. -/
theorem lcmMat_eq_diag (n : ℕ) :
    lcmMat n = diagonal (invVec n) * gcdMat n * diagonal (invVec n) := by
  ext i j
  simp only [lcmMat, gcdMat, invVec, of_apply, mul_diagonal, diagonal_mul]
  have h : ((Nat.gcd (i.val + 1) (j.val + 1) : ℕ) : ℚ) * (Nat.lcm (i.val + 1) (j.val + 1) : ℚ)
      = ((i.val + 1 : ℕ) : ℚ) * ((j.val + 1 : ℕ) : ℚ) := by
    exact_mod_cast Nat.gcd_mul_lcm (i.val + 1) (j.val + 1)
  have hl : (Nat.lcm (i.val + 1) (j.val + 1) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.lcm_ne_zero (Nat.succ_ne_zero _) (Nat.succ_ne_zero _))
  have hi : ((i.val + 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)
  have hj : ((j.val + 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)
  field_simp
  exact h.symm.trans (mul_comm _ _)

theorem det_lcmMat (n : ℕ) :
    (lcmMat n).det = ∏ i, (invVec n i * phiVec n i * invVec n i) := by
  rw [lcmMat_eq_diag, det_mul, det_mul, det_diagonal, det_gcdMat, ← prod_mul_distrib,
    ← prod_mul_distrib]

/-- Reindex a product over `Fin n` (entry `i + 1`) as a product over `Icc 1 n`. -/
theorem prod_fin_eq_prod_Icc (f : ℕ → ℚ) (n : ℕ) :
    ∏ i : Fin n, f (i.val + 1) = ∏ k ∈ Icc 1 n, f k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.prod_univ_castSucc, prod_Icc_succ_top (by omega)]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih]

theorem closedForm_ne_zero (n : ℕ) : closedForm n ≠ 0 := by
  rw [closedForm, prod_ne_zero_iff]
  intro k hk
  have hk0 : k ≠ 0 := by simp only [mem_Icc] at hk; omega
  have hφ : Nat.totient k ≠ 0 := by simpa using hk0
  exact div_ne_zero (pow_ne_zero 2 (Nat.cast_ne_zero.mpr hk0)) (Nat.cast_ne_zero.mpr hφ)

end L1

open L1

theorem L1_det_closedForm (n : ℕ) : ((lcmMat n).det)⁻¹ = closedForm n := by
  rw [det_lcmMat, ← prod_inv_distrib, closedForm,
    ← prod_fin_eq_prod_Icc (fun k ↦ (k : ℚ) ^ 2 / (Nat.totient k : ℚ))]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  simp only [invVec, phiVec]
  rw [mul_inv, mul_inv, inv_inv, div_eq_mul_inv]
  ring

/-! ### `det M_n ≠ 0` (blueprint §8, flag 3) -/

theorem lcmMat_det_eq (n : ℕ) : (lcmMat n).det = (closedForm n)⁻¹ := by
  rw [← L1_det_closedForm, inv_inv]

theorem lcmMat_det_ne_zero (n : ℕ) : (lcmMat n).det ≠ 0 := by
  rw [lcmMat_det_eq]
  exact inv_ne_zero (closedForm_ne_zero n)

end A060841
