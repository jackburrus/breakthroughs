import A141057.DShiftProd
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.RingTheory.Coprime.Lemmas

/-!
# K: the Jacobsthal–Kazandzidis congruence, from ascending products

PRD step 2 (node K). For a prime `p ≥ 5`: if `p ^ u` divides `a` and `b`, and `p ^ w` divides
`C(a + b, a)`, then `C((a + b) p, a p) ≡ C(a + b, a)` modulo `p ^ (w + 3 u + 3)`.
Proof: `C(M + n, n) n! = (M + 1)(M + 2) ⋯ (M + n)`. At `M = b p`, `n = a p`, the factors that are
multiples of `p` are `p (b + i)` for `1 ≤ i ≤ a`; the others multiply to
`H(b) = ∏_{j < a p, p ∤ j} (b p + j)` (`split_one`). Comparing with the same identity at `(b, a)`,
and at `M = 0` for `(a p)!`, gives `C((a + b) p, a p) H(0) = C(a + b, a) H(b)`. D says
`H(b) ≡ H(0)` modulo `p ^ (3 u + 3)`, and `H(0)` is prime to `p` (`congr_of_eq`).
The negative-index twin `K_chooseNeg` (next file) runs the same argument on `M (M + 1) ⋯ (M + n - 1)`.
Checked by `../numerics/lemmas.py` (checks `K`, `K_split`); `K` also fails at `p = 3`.
-/

namespace A141057

namespace K

open Finset

/-- Splitting a filtered product over `range (n + m)` at `n`. -/
theorem prod_filter_range_add {M : Type*} [CommMonoid M] (P : ℕ → Prop) [DecidablePred P]
    (f : ℕ → M) (n m : ℕ) :
    ∏ j ∈ range (n + m) with P j, f j =
      (∏ j ∈ range n with P j, f j) * ∏ t ∈ range m with P (n + t), f (n + t) := by
  simp only [prod_filter, prod_range_add]

/-- Inside a block `c p, …, c p + p - 1`, the factors prime to `p` are `c p + t`, `1 ≤ t < p`. -/
theorem prod_block_units (q c : ℕ) :
    ∏ t ∈ range (q + 1) with ¬ (q + 1) ∣ t, (c * (q + 1) + t) =
      ∏ t ∈ range q, (c * (q + 1) + t + 1) := by
  rw [prod_filter, prod_range_succ']
  simp only [dvd_zero, not_true_eq_false, if_false, mul_one]
  refine prod_congr rfl fun t ht => ?_
  rw [if_pos (Nat.not_dvd_of_pos_of_lt t.succ_pos (Nat.succ_lt_succ (mem_range.mp ht))), add_assoc]

/-- `c p (c p + 1) ⋯ (c p + p - 1) = p c ∏_{t < p, p ∤ t} (c p + t)`. -/
theorem block_zero (p c : ℕ) (hp : 0 < p) :
    ∏ t ∈ range p, (c * p + t) = p * c * ∏ t ∈ range p with ¬ p ∣ t, (c * p + t) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  rw [prod_block_units, prod_range_succ']
  simp only [← add_assoc, add_zero]
  ring

/-- `(c p + 1)(c p + 2) ⋯ (c p + p) = p (c + 1) ∏_{t < p, p ∤ t} (c p + t)`. -/
theorem block_one (p c : ℕ) (hp : 0 < p) :
    ∏ t ∈ range p, (c * p + t + 1) = p * (c + 1) * ∏ t ∈ range p with ¬ p ∣ t, (c * p + t) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  rw [prod_block_units, prod_range_succ]
  ring

/-- Moving a block of `p` factors from `n p + t` to `(c + n) p + t`. -/
theorem prod_block_shift (p c n : ℕ) (g : ℕ → ℕ) :
    ∏ t ∈ range p with ¬ p ∣ n * p + t, g (c * p + (n * p + t)) =
      ∏ t ∈ range p with ¬ p ∣ t, g ((c + n) * p + t) := by
  simp only [Nat.dvd_add_right (dvd_mul_left p n)]
  exact prod_congr rfl fun t _ => by rw [add_mul, add_assoc]

/-- `∏_{j < n p} (c p + j) = p ^ n ∏_{i < n} (c + i) ∏_{j < n p, p ∤ j} (c p + j)`. -/
theorem split_zero (p c n : ℕ) (hp : 0 < p) :
    ∏ j ∈ range (n * p), (c * p + j) =
      p ^ n * (∏ i ∈ range n, (c + i)) * ∏ j ∈ range (n * p) with ¬ p ∣ j, (c * p + j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [add_one_mul, prod_range_add (fun j => c * p + j), prod_filter_range_add, ih,
      prod_range_succ (fun i => c + i), pow_succ, prod_block_shift p c n (fun j => j)]
    have hb : ∏ t ∈ range p, (c * p + (n * p + t)) = ∏ t ∈ range p, ((c + n) * p + t) :=
      prod_congr rfl fun t _ => by ring
    rw [hb, block_zero p (c + n) hp]
    ring

/-- `∏_{j < n p} (c p + j + 1) = p ^ n ∏_{i < n} (c + i + 1) ∏_{j < n p, p ∤ j} (c p + j)`. -/
theorem split_one (p c n : ℕ) (hp : 0 < p) :
    ∏ j ∈ range (n * p), (c * p + j + 1) =
      p ^ n * (∏ i ∈ range n, (c + i + 1)) * ∏ j ∈ range (n * p) with ¬ p ∣ j, (c * p + j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [add_one_mul, prod_range_add (fun j => c * p + j + 1), prod_filter_range_add, ih,
      prod_range_succ (fun i => c + i + 1), pow_succ, prod_block_shift p c n (fun j => j)]
    have hb : ∏ t ∈ range p, (c * p + (n * p + t) + 1) = ∏ t ∈ range p, ((c + n) * p + t + 1) :=
      prod_congr rfl fun t _ => by ring
    rw [hb, block_one p (c + n) hp]
    ring

/-- `(n p)! = p ^ n n! ∏_{j < n p, p ∤ j} j`, with the factorials as products of `j + 1`. -/
theorem factorial_split (p n : ℕ) (hp : 0 < p) :
    ∏ j ∈ range (n * p), (j + 1) =
      p ^ n * (∏ i ∈ range n, (i + 1)) * ∏ j ∈ range (n * p) with ¬ p ∣ j, j := by
  simpa using split_one p 0 n hp

/-- `C(M + n, n) n! = (M + 1) ⋯ (M + n)`. -/
theorem asc_one (M n : ℕ) :
    (M + n).choose n * ∏ j ∈ range n, (j + 1) = ∏ j ∈ range n, (M + j + 1) := by
  rw [prod_range_add_one_eq_factorial, Nat.mul_comm ((M + n).choose n),
    ← Nat.ascFactorial_eq_factorial_mul_choose, Nat.ascFactorial_eq_prod_range]
  exact prod_congr rfl fun j _ => by ring

/-- `C(M + n - 1, n) n! = M (M + 1) ⋯ (M + n - 1)`. -/
theorem asc_zero (M n : ℕ) :
    (M + n - 1).choose n * ∏ j ∈ range n, (j + 1) = ∏ j ∈ range n, (M + j) := by
  rw [prod_range_add_one_eq_factorial, Nat.mul_comm ((M + n - 1).choose n),
    ← Nat.ascFactorial_eq_factorial_mul_choose', Nat.ascFactorial_eq_prod_range]

/-- The common last step: from `X H(0) = x H(b)` and `p ^ w ∣ x`, D and the cancellation of
`H(0)`, which is prime to `p`, give `X ≡ x (mod p ^ (w + 3 u + 3))`. -/
theorem congr_of_eq {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) {a b u w X x : ℕ} (hua : p ^ u ∣ a)
    (hub : p ^ u ∣ b) (hw : p ^ w ∣ x)
    (key : X * ∏ j ∈ range (a * p) with ¬ p ∣ j, j =
      x * ∏ j ∈ range (a * p) with ¬ p ∣ j, (b * p + j)) :
    (X : ℤ) ≡ x [ZMOD (p : ℤ) ^ (w + 3 * u + 3)] := by
  have hD := D_shift_prod hp h5 (x := ((b * p : ℕ) : ℤ)) (N := a * p) (r := u + 1) (s := u + 1)
    (by rw [pow_succ]; push_cast; exact mul_dvd_mul (by exact_mod_cast hub) dvd_rfl)
    (by rw [pow_succ]; exact mul_dvd_mul hua dvd_rfl)
  rw [min_self, show 3 * (u + 1) = 3 * u + 3 by ring] at hD
  rw [Int.modEq_iff_dvd] at hD ⊢
  have hkey : ((x : ℤ) - X) * ((∏ j ∈ range (a * p) with ¬ p ∣ j, j : ℕ) : ℤ) =
      x * (∏ j ∈ range (a * p) with ¬ p ∣ j, (j : ℤ) -
        ∏ j ∈ range (a * p) with ¬ p ∣ j, (((b * p : ℕ) : ℤ) + j)) := by
    have h : ((X * ∏ j ∈ range (a * p) with ¬ p ∣ j, j : ℕ) : ℤ) =
        ((x * ∏ j ∈ range (a * p) with ¬ p ∣ j, (b * p + j) : ℕ) : ℤ) := by rw [key]
    push_cast at h ⊢
    linear_combination -h
  have hdvd : (p : ℤ) ^ (w + (3 * u + 3)) ∣ ((x : ℤ) - X) *
      ((∏ j ∈ range (a * p) with ¬ p ∣ j, j : ℕ) : ℤ) := by
    rw [hkey, pow_add]
    exact mul_dvd_mul (by exact_mod_cast hw) hD
  have hH : ¬ p ∣ ∏ j ∈ range (a * p) with ¬ p ∣ j, j := by
    rw [Prime.dvd_finsetProd_iff hp.prime]
    rintro ⟨j, hj, hpj⟩
    exact (mem_filter.mp hj).2 hpj
  have hcop : IsCoprime ((p : ℤ) ^ (w + (3 * u + 3)))
      ((∏ j ∈ range (a * p) with ¬ p ∣ j, j : ℕ) : ℤ) := by
    exact_mod_cast Nat.Coprime.isCoprime
      (Nat.Coprime.pow_left (w + (3 * u + 3)) ((hp.coprime_iff_not_dvd).mpr hH))
  rw [← add_assoc] at hcop hdvd
  exact hcop.dvd_of_dvd_mul_right hdvd

end K

open K Finset in
/-- **K**: if `p ^ u ∣ a`, `p ^ u ∣ b` and `p ^ w ∣ C(a + b, a)`, then
`C((a + b) p, a p) ≡ C(a + b, a) (mod p ^ (w + 3 u + 3))` (`p ≥ 5`). -/
theorem K_choose {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) {a b u w : ℕ} (hua : p ^ u ∣ a)
    (hub : p ^ u ∣ b) (hw : p ^ w ∣ (a + b).choose a) :
    (((a + b) * p).choose (a * p) : ℤ) ≡ ((a + b).choose a : ℤ) [ZMOD (p : ℤ) ^ (w + 3 * u + 3)] := by
  have hp0 := hp.pos
  refine congr_of_eq hp h5 hua hub hw ?_
  -- `C(b p + a p, a p) (a p)! = (b p + 1) ⋯ (b p + a p)`, split at the multiples of `p`
  have hbig := asc_one (b * p) (a * p)
  rw [split_one p b a hp0, factorial_split p a hp0] at hbig
  have hsmall := asc_one b a
  rw [show (a + b) * p = b * p + a * p by ring, show a + b = b + a from Nat.add_comm a b]
  have hpos : 0 < p ^ a * ∏ i ∈ range a, (i + 1) :=
    Nat.mul_pos (pow_pos hp0 a) (prod_pos fun i _ => Nat.succ_pos i)
  refine Nat.eq_of_mul_eq_mul_left hpos ?_
  rw [← hsmall] at hbig
  linear_combination hbig

end A141057
