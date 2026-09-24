import A060841.Defs

/-!
# L2: finite check for `1 ≤ n < threshold`

Both directions of the iff for every small `n`, including 35 and 37, by kernel-checkable
computation (`decide`, `norm_num`; never `native_decide`). See `../BLUEPRINT.md` §3–4.
The right-hand side is `n ∈ integerDetN` unfolded; `Main.lean` does the conversion.
-/

namespace A060841

theorem L2_small (n : ℕ) (h1 : 1 ≤ n) (hn : n < threshold) :
    (closedForm n).den = 1 ↔ n ≤ 34 ∨ n = 36 ∨ n = 38 := by
  sorry

end A060841
