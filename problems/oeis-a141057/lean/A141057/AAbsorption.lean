import Mathlib.Data.Nat.Choose.Basic

/-!
# A: absorption, as divisibilities

PRD step 1 inputs (node A). The absorption identity `k C(N, k) = N C(N - 1, k - 1)` says that
`N` divides `k C(N, k)`, and its negative-index twin `k C(N + k - 1, k) = N C(N + k - 1, k - 1)`
says that `N` divides `k C(N + k - 1, k)`. Every valuation bound of the proof comes from these two
facts: `N` divides both `k C` and `N C`, hence `gcd(N, k) C` (`A_gcd`, `A_gcdNeg`).
`A_symm_neg` moves the index `j` into the negative-index binomial; its positive analogue is
Mathlib's `Nat.choose_mul`. Nothing here needs `p` or any bound on `N` and `k`.
Checked by `../numerics/lemmas.py` (checks `A_absorb`, `A_absorbNeg`, `A_gcd`, `A_gcdNeg`,
`A_symm_neg`).
-/

namespace A141057

namespace A

/-- If `N` divides `a c` and `b c`, it divides `gcd(a, b) c`. -/
theorem dvd_gcd_mul {N a b c : ℕ} (ha : N ∣ a * c) (hb : N ∣ b * c) : N ∣ Nat.gcd a b * c := by
  rw [← Nat.gcd_mul_right]
  exact Nat.dvd_gcd ha hb

end A

/-- **A**: `N ∣ k C(N, k)`, as `k C(N, k) = N C(N - 1, k - 1)`. -/
theorem A_absorb (N k : ℕ) : N ∣ k * N.choose k := by
  rcases N with _ | n
  · rcases k with _ | k <;> simp
  rcases k with _ | k
  · simp
  exact ⟨n.choose k, by rw [Nat.add_one_mul_choose_eq, Nat.mul_comm (k + 1)]⟩

/-- **A⁻**: `N ∣ k C(N + k - 1, k)`, as `k C(N + k - 1, k) = N C(N + k - 1, k - 1)`. -/
theorem A_absorbNeg (N k : ℕ) : N ∣ k * (N + k - 1).choose k := by
  rcases k with _ | k
  · simp
  refine ⟨(N + k).choose k, ?_⟩
  rw [show N + (k + 1) - 1 = N + k by omega, Nat.mul_comm (k + 1), Nat.choose_succ_right_eq,
    Nat.add_sub_cancel, Nat.mul_comm]

/-- **A_gcd**: `x + y ∣ gcd(x, y) C(x + y, x)`, from `A_absorb` at `x` and at `y`. -/
theorem A_gcd (x y : ℕ) : x + y ∣ Nat.gcd x y * (x + y).choose x := by
  refine A.dvd_gcd_mul (A_absorb _ x) ?_
  rw [Nat.choose_symm_add]
  exact A_absorb _ y

/-- **A_gcd⁻**: `N ∣ gcd(N, k) C(N + k - 1, k)`, from `A_absorbNeg`. -/
theorem A_gcdNeg (N k : ℕ) : N ∣ Nat.gcd N k * (N + k - 1).choose k :=
  A.dvd_gcd_mul (Nat.dvd_mul_right N _) (A_absorbNeg N k)

/-- **A_symm⁻**: `C(N+k-1, k) C(k, j) = C(N+j-1, j) C(N+k-1, k-j)` (both are the multinomial
`(N+k-1)! / ((N-1)! j! (k-j)!)`). -/
theorem A_symm_neg (N k j : ℕ) (hN : 1 ≤ N) (hjk : j ≤ k) :
    (N + k - 1).choose k * k.choose j = (N + j - 1).choose j * (N + k - 1).choose (k - j) := by
  -- both sides are `C(N+k-1, j) C(N+k-1-j, N-1)`
  rw [Nat.choose_mul hjk, Nat.choose_symm_of_eq_add (show N + k - 1 = (k - j) + (N + j - 1) by omega),
    Nat.mul_comm ((N + j - 1).choose j), Nat.choose_mul (show j ≤ N + j - 1 by omega),
    Nat.choose_symm_of_eq_add (show N + k - 1 - j = (k - j) + (N + j - 1 - j) by omega)]

end A141057
