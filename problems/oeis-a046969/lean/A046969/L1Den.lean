import A046969.Defs

/-!
# L1: the denominator of `B_{2p}` is 6

By von Staudt–Clausen (`Bernoulli.vonStaudt_clausen`), `den B_{2p}` is the product of the
primes `r` with `r - 1 ∣ 2p`, so `r ∈ {2, 3, p + 1, 2p + 1}`. Here `p + 1` is even and larger
than 2, and `3 ∣ 2p + 1` because 3 divides neither `2p` nor the prime `2p - 1 > 3`.
See `../PRD.md`, step 1.
-/

namespace A046969

theorem L1_den_bernoulli (p : ℕ) (hp : p.Prime) (hp' : (2 * p - 1).Prime) (h3 : 3 < p) :
    (bernoulli (2 * p)).den = 6 := by
  sorry

end A046969
