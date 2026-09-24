import Mathlib.NumberTheory.Bernoulli

/-!
# Shared definitions for the A046969 Conjecture I proof

Everything here is ours, not upstream. This file (and every lemma file) imports only the
specific Mathlib modules it needs; the upstream statement is imported only by `Main.lean`.
See `CLAUDE.md` and `../PRD.md`.
-/

namespace A046969

/-- A copy of `OeisA46969.a`, so the lemma files need not import upstream (and all of Mathlib).
`Main.lean` checks it is the upstream definition by `rfl`; do not change it. -/
def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let m := 2 * n
    let k := m * (m - 1)
    (bernoulli m / (k : ℚ)).den

/-- The power sum `S_m(n) = ∑_{k<n} k^m`. -/
def powSum (m n : ℕ) : ℕ := ∑ k ∈ Finset.range n, k ^ m

end A046969
