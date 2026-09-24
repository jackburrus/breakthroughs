import A046969.Defs
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.Multiplicity

/-!
# L3: `S_{q+1}(q) / q ≡ 1/12 (mod q)`

Doubling modulo `q²`, where now `(r + q·t)^{q+1} ≡ r^{q+1} + q·t·r^q`, gives
`(2^{q+1} - 1)·S_{q+1}(q) ≡ q·∑_{j odd, j ≤ q-2} j^q (mod q²)`. Mod `q`: `2^{q+1} ≡ 4` and the
odd-number sum is `((q - 1)/2)² ≡ 1/4`. Stated as `q ∣ S` and `12·(S / q) ≡ 1 (mod q)`, for
every prime `q ≥ 5`; the proof uses it at `q = 2p - 1`, where `q + 1 = 2p`.
See `../PRD.md`, step 3.

With `q = 2h + 1`, the doubled residues `2k` (`k < q`) are the evens `2j ≤ 2h` and the numbers
`q + (2j + 1)` for `j < h`, while `range q` itself is the same evens plus the odds `2j + 1`, so
`(2^n - 1)·S_n(q) = ∑_{j<h} ((2j + 1 + q)^n - (2j + 1)^n)` exactly (`L3.doubling`), with no
permutation argument.
-/

namespace A046969

namespace L3

open Finset

/-- Split `range (2h + 1)` into its `h + 1` even and `h` odd members. -/
theorem sum_range_parity (f : ℕ → ℤ) (h : ℕ) :
    ∑ k ∈ range (2 * h + 1), f k =
      ∑ j ∈ range (h + 1), f (2 * j) + ∑ j ∈ range h, f (2 * j + 1) := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [show 2 * (h + 1) + 1 = 2 * h + 1 + 1 + 1 by ring, sum_range_succ f (2 * h + 1 + 1),
      sum_range_succ f (2 * h + 1), ih, sum_range_succ (fun j ↦ f (2 * j)) (h + 1),
      sum_range_succ (fun j ↦ f (2 * j + 1)) h, show 2 * h + 1 + 1 = 2 * (h + 1) by ring]
    ring

/-- The doubling identity for `q = 2h + 1`: `(2^n - 1)·S_n(q) = ∑_{j<h} ((2j+1+q)^n - (2j+1)^n)`. -/
theorem doubling (n q h : ℕ) (hq : q = 2 * h + 1) :
    (2 ^ n - 1 : ℤ) * ∑ k ∈ range q, (k : ℤ) ^ n =
      ∑ j ∈ range h, ((((2 * j + 1 : ℕ) : ℤ) + q) ^ n - ((2 * j + 1 : ℕ) : ℤ) ^ n) := by
  subst hq
  have h2 : (2 ^ n : ℤ) * ∑ k ∈ range (2 * h + 1), (k : ℤ) ^ n =
      ∑ j ∈ range (h + 1), ((2 * j : ℕ) : ℤ) ^ n +
        ∑ j ∈ range h, (((2 * j + 1 : ℕ) : ℤ) + ((2 * h + 1 : ℕ) : ℤ)) ^ n := by
    rw [mul_sum, show 2 * h + 1 = (h + 1) + h by ring, sum_range_add]
    congr 1 <;> refine sum_congr rfl fun j _ ↦ ?_ <;> rw [← mul_pow] <;> push_cast <;> ring
  rw [sub_mul, h2, one_mul, sum_range_parity (fun k ↦ (k : ℤ) ^ n), sum_sub_distrib]
  ring

/-- The sum of the first `h` odd numbers is `h²`. -/
theorem sum_odd (h : ℕ) : ∑ j ∈ range h, (2 * j + 1) = h ^ 2 := by
  induction h with
  | zero => simp
  | succ h ih => rw [sum_range_succ, ih]; ring

end L3

open Finset in
theorem L3_powSum_div (q : ℕ) (hq : q.Prime) (h5 : 5 ≤ q) :
    q ∣ powSum (q + 1) q ∧ 12 * (powSum (q + 1) q / q) ≡ 1 [MOD q] := by
  have := Fact.mk hq
  obtain ⟨h, hqh⟩ := hq.odd_of_ne_two (by omega)
  set S := powSum (q + 1) q with hSdef
  set T : ℤ := ∑ j ∈ range h, ((2 * j + 1 : ℕ) : ℤ) ^ q with hT
  have hS : (S : ℤ) = ∑ k ∈ range q, (k : ℤ) ^ (q + 1) := by simp [hSdef, powSum]
  -- `(2^{q+1} - 1)·S ≡ q·(q + 1)·T (mod q²)`, one binomial step per odd `2j + 1`.
  have key : (q : ℤ) ^ 2 ∣ (2 ^ (q + 1) - 1) * (S : ℤ) - q * (q + 1) * T := by
    rw [hS, L3.doubling (q + 1) q h hqh, hT, mul_sum, ← sum_sub_distrib]
    refine dvd_sum fun j _ ↦ ?_
    have := sq_dvd_add_pow_sub_sub (q : ℤ) ((2 * j + 1 : ℕ) : ℤ) (q + 1)
    convert this using 1
    rw [Nat.add_sub_cancel]; push_cast; ring
  -- In `ZMod q`: `2^{q+1} - 1 = 3`, a unit since `q ≥ 5`.
  have h3 : (2 : ZMod q) ^ (q + 1) - 1 = 3 := by
    rw [pow_succ, ZMod.pow_card]; norm_num
  have h3ne : (3 : ZMod q) ≠ 0 := by
    intro h0
    have h0' : ((3 : ℕ) : ZMod q) = 0 := by exact_mod_cast h0
    rw [ZMod.natCast_eq_zero_iff] at h0'
    have := Nat.le_of_dvd (by norm_num) h0'
    omega
  have hqz : ((q : ℕ) : ZMod q) = 0 := ZMod.natCast_self q
  -- Step 1: `q ∣ S`.
  have hdvd : q ∣ S := by
    have hz : (((2 ^ (q + 1) - 1) * (S : ℤ) - q * (q + 1) * T : ℤ) : ZMod q) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mpr
        (dvd_trans (dvd_pow_self (q : ℤ) two_ne_zero) key)
    push_cast at hz
    rw [h3, hqz, zero_mul, zero_mul, sub_zero] at hz
    rw [← ZMod.natCast_eq_zero_iff]
    exact (mul_eq_zero.mp hz).resolve_left h3ne
  refine ⟨hdvd, ?_⟩
  -- Step 2: `S = q·s` and `3·s ≡ T ≡ h² (mod q)`, so `12·s ≡ (2h)² = (q - 1)² ≡ 1`.
  obtain ⟨s, hs⟩ := hdvd
  rw [hs, Nat.mul_div_cancel_left s hq.pos]
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne_zero
  have key' : (q : ℤ) ∣ (2 ^ (q + 1) - 1) * (s : ℤ) - (q + 1) * T := by
    rw [hs] at key
    have e : (2 ^ (q + 1) - 1) * ((q * s : ℕ) : ℤ) - q * (q + 1) * T =
        (q : ℤ) * ((2 ^ (q + 1) - 1) * (s : ℤ) - (q + 1) * T) := by push_cast; ring
    rw [e, pow_two] at key
    exact (mul_dvd_mul_iff_left hq0).mp key
  have hz : (((2 ^ (q + 1) - 1) * (s : ℤ) - (q + 1) * T : ℤ) : ZMod q) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mpr key'
  have hTz : ((T : ℤ) : ZMod q) = ((h ^ 2 : ℕ) : ZMod q) := by
    rw [hT, ← L3.sum_odd h]
    push_cast
    exact sum_congr rfl fun j _ ↦ by
      rw [show (2 * (j : ZMod q) + 1) = ((2 * j + 1 : ℕ) : ZMod q) by push_cast; ring,
        ZMod.pow_card]
  have h2h : (2 * (h : ZMod q)) = -1 := by
    have : ((2 * h + 1 : ℕ) : ZMod q) = 0 := hqh ▸ hqz
    push_cast at this
    linear_combination this
  have h3s : (3 : ZMod q) * s = (h : ZMod q) ^ 2 := by
    have hz' := hz
    push_cast at hz' hTz
    rw [h3, hqz, zero_add, one_mul, hTz] at hz'
    linear_combination hz'
  rw [← ZMod.natCast_eq_natCast_iff]
  push_cast
  linear_combination 4 * h3s + (2 * (h : ZMod q) - 1) * h2h
