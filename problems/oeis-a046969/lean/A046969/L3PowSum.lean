import A046969.Defs

/-!
# L3: `S_{q+1}(q) / q ≡ 1/12 (mod q)`

Doubling modulo `q²`, where now `(r + q·t)^{q+1} ≡ r^{q+1} + q·t·r^q`, gives
`(2^{q+1} - 1)·S_{q+1}(q) ≡ q·∑_{j odd, j ≤ q-2} j^q (mod q²)`. Mod `q`: `2^{q+1} ≡ 4` and the
odd-number sum is `((q - 1)/2)² ≡ 1/4`. Stated as `q ∣ S` and `12·(S / q) ≡ 1 (mod q)`, for
every prime `q ≥ 5`; the proof uses it at `q = 2p - 1`, where `q + 1 = 2p`.
See `../PRD.md`, step 3.
-/

namespace A046969

theorem L3_powSum_div (q : ℕ) (hq : q.Prime) (h5 : 5 ≤ q) :
    q ∣ powSum (q + 1) q ∧ 12 * (powSum (q + 1) q / q) ≡ 1 [MOD q] := by
  sorry

end A046969
