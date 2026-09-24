import A046969.L1Den
import A046969.FFaulhaber
import A046969.L2PowSum
import A046969.L3PowSum

/-!
# L4: `a p = 12 (2p - 1)`

With `q = 2p - 1` and `B_{2p} = N / 6` (L1): F with L2 gives `p ∣ N`, and F with L3 (at
`q + 1 = 2p`) gives `q ∤ N`. Then `B_{2p} / (2p·q) = N / (12·p·q) = N' / (12·q)` with
`N = p·N'` and `N'` coprime to 2, 3 and `q`, so `a p = 12 q`. See `../PRD.md`, step 4.
-/

namespace A046969

theorem L4_a_eq (p : ℕ) (hp : p.Prime) (hp' : (2 * p - 1).Prime) (h3 : 3 < p) :
    a p = 12 * (2 * p - 1) := by
  sorry

end A046969
