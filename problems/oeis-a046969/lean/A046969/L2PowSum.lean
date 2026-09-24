import A046969.Defs

/-!
# L2: `p² ∣ S_{2p}(p)`

Doubling permutes the nonzero residues mod `p`, and `(r + p·t)^{2p} ≡ r^{2p} (mod p²)` because
`p ∣ 2p`, so `2^{2p}·S_{2p}(p) ≡ S_{2p}(p) (mod p²)`. Since `2^{2p} - 1 ≡ 3 (mod p)` is a unit
for `p > 3`, `p² ∣ S_{2p}(p)`. Holds for every prime `p > 3` (no condition on `2p - 1`).
See `../PRD.md`, step 2.
-/

namespace A046969

theorem L2_sq_dvd_powSum (p : ℕ) (hp : p.Prime) (h3 : 3 < p) : p ^ 2 ∣ powSum (2 * p) p := by
  sorry

end A046969
