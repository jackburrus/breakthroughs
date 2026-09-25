import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Tactic.Ring

/-!
# S: splitting a triangular double sum at the multiples of `p`

PRD step 3 bookkeeping, sign-free. The double sum `∑_{k ≤ m p} ∑_{j ≤ k} f k j` agrees modulo
`q` with `∑_{i ≤ m} ∑_{l ≤ i} g i l` when every summand with `(k, j)` not both multiples of `p`
is `≡ 0`, and `f (i p) (l p) ≡ g i l` for `l ≤ i ≤ m`: the pairs of multiples of `p` in the
triangle `j ≤ k ≤ m p` are exactly `(i p, l p)` with `l ≤ i ≤ m`.
Both signs use it: `R_step` with `f k j = (C(m p, k) C(k, j))³`, `R_stepNeg` with the signed
negative-index summands.
-/

namespace A141057

namespace S

open Finset

/-- A sum over `k ≤ M p` splits into the multiples `k = i p`, `i ≤ M`, and the rest. -/
theorem sum_range_mul (p M : ℕ) (hp : 0 < p) (h : ℕ → ℤ) :
    ∑ k ∈ range (M * p + 1), h k =
      ∑ i ∈ range (M + 1), h (i * p) + ∑ k ∈ (range (M * p + 1)).filter (fun k => ¬ p ∣ k), h k := by
  rw [← sum_filter_add_sum_filter_not (range (M * p + 1)) (fun k => p ∣ k)]
  congr 1
  rw [← sum_image (g := fun i => i * p) (fun a _ b _ hab => Nat.eq_of_mul_eq_mul_right hp hab)]
  congr 1
  ext k
  simp only [mem_filter, mem_range, mem_image]
  constructor
  · rintro ⟨hk, i, rfl⟩
    refine ⟨i, ?_, mul_comm i p⟩
    have : p * i ≤ p * M := by rw [mul_comm p M]; omega
    have := Nat.le_of_mul_le_mul_left this hp
    omega
  · rintro ⟨i, hi, rfl⟩
    exact ⟨by have := Nat.mul_le_mul_right p (show i ≤ M by omega); omega, dvd_mul_left p i⟩

end S

open Finset in
/-- **S**: the double sum over `j ≤ k ≤ m p` reduces modulo `q` to the one over `l ≤ i ≤ m`. -/
theorem S_split (p m : ℕ) (hp : 0 < p) (q : ℤ) (f g : ℕ → ℕ → ℤ)
    (hV : ∀ k j, k ≤ m * p → j ≤ k → ¬ (p ∣ k ∧ p ∣ j) → q ∣ f k j)
    (hP : ∀ i l, i ≤ m → l ≤ i → q ∣ f (i * p) (l * p) - g i l) :
    q ∣ (∑ k ∈ Finset.range (m * p + 1), ∑ j ∈ Finset.range (k + 1), f k j) -
      ∑ i ∈ Finset.range (m + 1), ∑ l ∈ Finset.range (i + 1), g i l := by
  rw [S.sum_range_mul p m hp (fun k => ∑ j ∈ range (k + 1), f k j),
    sum_congr rfl (fun i _ => S.sum_range_mul p i hp (f (i * p))), sum_add_distrib]
  have hrw :
      (∑ i ∈ range (m + 1), ∑ l ∈ range (i + 1), f (i * p) (l * p)) +
          (∑ i ∈ range (m + 1), ∑ j ∈ (range (i * p + 1)).filter (fun j => ¬ p ∣ j), f (i * p) j) +
          (∑ k ∈ (range (m * p + 1)).filter (fun k => ¬ p ∣ k), ∑ j ∈ range (k + 1), f k j) -
        ∑ i ∈ range (m + 1), ∑ l ∈ range (i + 1), g i l =
      (∑ i ∈ range (m + 1), ∑ l ∈ range (i + 1), (f (i * p) (l * p) - g i l)) +
          (∑ i ∈ range (m + 1), ∑ j ∈ (range (i * p + 1)).filter (fun j => ¬ p ∣ j), f (i * p) j) +
          (∑ k ∈ (range (m * p + 1)).filter (fun k => ¬ p ∣ k), ∑ j ∈ range (k + 1), f k j) := by
    simp only [sum_sub_distrib]; ring
  rw [hrw]
  refine dvd_add (dvd_add ?_ ?_) ?_
  · refine dvd_sum fun i hi => dvd_sum fun l hl => ?_
    rw [mem_range] at hi hl
    exact hP i l (by omega) (by omega)
  · refine dvd_sum fun i hi => dvd_sum fun j hj => ?_
    rw [mem_range] at hi
    rw [mem_filter, mem_range] at hj
    exact hV (i * p) j (Nat.mul_le_mul_right p (by omega)) (by omega) (fun h => hj.2 h.2)
  · refine dvd_sum fun k hk => dvd_sum fun j hj => ?_
    rw [mem_filter, mem_range] at hk
    rw [mem_range] at hj
    exact hV k j (by omega) (by omega) (fun h => hk.2 h.1)

end A141057
