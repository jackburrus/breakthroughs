import A060841.Defs
import Mathlib.Data.Rat.Lemmas

/-!
# L2: finite check for `1 ≤ n < threshold`

Both directions of the iff for every small `n`, including 35 and 37, by kernel-checkable
computation (`decide`, `norm_num`; never `native_decide`). See `../BLUEPRINT.md` §3–4.
The right-hand side is `n ∈ integerDetN` unfolded; `Main.lean` does the conversion.

Route: `closedForm n = (∏ k²) / (∏ φ(k))` over `ℕ` casts, so by `Rat.den_div_natCast_eq_one_iff`
its denominator is `1` iff `∏ φ(k) ∣ ∏ k²`, which one `decide +kernel` checks for all `n < threshold`.
-/

namespace A060841

/-- `∏_{k=1}^{n} φ(k)` over `ℕ`, the denominator of `closedForm n` before reduction. -/
def phiProd (n : ℕ) : ℕ := ∏ k ∈ Finset.Icc 1 n, Nat.totient k

/-- `∏_{k=1}^{n} k²` over `ℕ` (that is, `(n!)²`), the numerator of `closedForm n`. -/
def sqProd (n : ℕ) : ℕ := ∏ k ∈ Finset.Icc 1 n, k ^ 2

theorem phiProd_ne_zero (n : ℕ) : phiProd n ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun _ hk =>
    (Nat.totient_pos.mpr (Finset.mem_Icc.mp hk).1).ne'

theorem closedForm_eq_div (n : ℕ) :
    closedForm n = (sqProd n : ℚ) / (phiProd n : ℚ) := by
  simp only [closedForm, sqProd, phiProd, Nat.cast_prod, Nat.cast_pow, Finset.prod_div_distrib]

theorem closedForm_den_eq_one_iff (n : ℕ) :
    (closedForm n).den = 1 ↔ phiProd n ∣ sqProd n := by
  rw [closedForm_eq_div]
  exact Rat.den_div_natCast_eq_one_iff _ _ (phiProd_ne_zero n)

/-- The whole finite range in one kernel computation (seconds for `threshold = 82`). -/
theorem phiProd_dvd_sqProd_iff :
    ∀ n < threshold, 1 ≤ n → (phiProd n ∣ sqProd n ↔ n ≤ 34 ∨ n = 36 ∨ n = 38) := by
  decide +kernel

theorem L2_small (n : ℕ) (h1 : 1 ≤ n) (hn : n < threshold) :
    (closedForm n).den = 1 ↔ n ≤ 34 ∨ n = 36 ∨ n = 38 := by
  rw [closedForm_den_eq_one_iff]
  exact phiProd_dvd_sqProd_iff n hn h1

end A060841
