import A046969.Defs

/-!
# L1: the denominator of `B_{2p}` is 6

By von Staudt–Clausen (`Bernoulli.vonStaudt_clausen`), `den B_{2p}` is the product of the
primes `r` with `r - 1 ∣ 2p`, so `r ∈ {2, 3, p + 1, 2p + 1}`. Here `p + 1` is even and larger
than 2, and `3 ∣ 2p + 1` because 3 divides neither `2p` nor the prime `2p - 1 > 3`.
See `../PRD.md`, step 1.
-/

namespace A046969

namespace L1

/-- The von Staudt–Clausen primes for `B_{2p}`: `r - 1 ∣ 2p` leaves only 2 and 3. -/
theorem vonStaudtPrimes_eq (p : ℕ) (hp : p.Prime) (hp' : (2 * p - 1).Prime) (h3 : 3 < p) :
    (Finset.range (2 * p + 2)).filter (fun r ↦ r.Prime ∧ (r - 1) ∣ 2 * p) = {2, 3} := by
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have h3p : ¬ 3 ∣ p := fun h ↦ by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h; omega
  have h3q : ¬ 3 ∣ 2 * p - 1 := fun h ↦ by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp').mp h; omega
  ext r
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hr, hrp, hdvd⟩
    obtain ⟨d₁, d₂, hd₁, hd₂, he⟩ := Nat.dvd_mul.mp hdvd
    rcases (Nat.dvd_prime Nat.prime_two).mp hd₁ with rfl | rfl <;>
      rcases (Nat.dvd_prime hp).mp hd₂ with h | h <;> subst d₂
    · omega
    · -- `r = p + 1` is even and larger than 2
      obtain ⟨k, hk⟩ := hodd
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hrp).mp ⟨k + 1, by omega⟩
      omega
    · omega
    · -- `r = 2p + 1` is divisible by 3 and larger than 3
      have h3r : 3 ∣ r := by
        rcases (by omega : p % 3 = 1 ∨ p % 3 = 2) with hm | hm <;> omega
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hrp).mp h3r
      omega
  · rintro (rfl | rfl)
    · exact ⟨by omega, Nat.prime_two, one_dvd _⟩
    · exact ⟨by omega, Nat.prime_three, dvd_mul_right 2 p⟩

end L1

theorem L1_den_bernoulli (p : ℕ) (hp : p.Prime) (hp' : (2 * p - 1).Prime) (h3 : 3 < p) :
    (bernoulli (2 * p)).den = 6 := by
  obtain ⟨z, hz⟩ := Bernoulli.vonStaudt_clausen p
  rw [L1.vonStaudtPrimes_eq p hp hp' h3, Finset.sum_pair (by decide)] at hz
  have hB : bernoulli (2 * p) = (z : ℚ) - 5 / 6 := by
    rw [hz]; push_cast; ring
  rw [hB, Rat.intCast_sub_den]
  norm_num

end A046969
