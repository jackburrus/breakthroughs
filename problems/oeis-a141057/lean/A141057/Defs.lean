import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Data.Nat.Choose.Basic

/-!
# Shared definitions for the A141057 Conjecture 2 proof

Everything here is ours, not upstream. This file (and every lemma file) imports only the
specific Mathlib modules it needs; the upstream statement is imported only by `Main.lean`.
See `CLAUDE.md` and `../PRD.md`.
-/

namespace A141057

/-- A copy of `OeisA141057.aInt`, so the lemma files need not import upstream (and all of Mathlib).
`Main.lean` checks it is the upstream definition by `rfl`; do not change it. -/
def aInt (n : ℤ) : ℤ :=
  if 0 ≤ n then
    let nNat := n.toNat
    (∑ k ∈ Finset.range (nNat + 1), (nNat.choose k ^ 3) * ∑ j ∈ Finset.range (k + 1), (k.choose j ^ 3) : ℕ)
  else
    let nNat := (-n).toNat
    ∑ k ∈ Finset.range (nNat + 1), ((-1 : ℤ) ^ k * (nNat + k - 1).choose k : ℤ) ^ 3 *
      ∑ j ∈ Finset.range (k + 1), ((k.choose j : ℤ) ^ 3)

end A141057
