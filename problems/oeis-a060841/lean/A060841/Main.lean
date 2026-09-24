import A060841.L1Det
import A060841.L2Small
import A060841.L3Large

/-!
# Assembly of `OeisA60841.conjecture1`

The type is taken verbatim from the upstream theorem with `type_of%`, so nothing is
restated: if upstream changes the statement, this file follows it (or stops compiling).
Do not add proof work here; it belongs in L1, L2 or L3.
-/

namespace A060841

open OeisA60841

theorem conjecture1 : type_of% @OeisA60841.conjecture1 := by
  intro n h1
  rw [L1_det_closedForm]
  by_cases hn : n < threshold
  · exact L2_small n h1 hn
  · have hlarge : threshold ≤ n := Nat.le_of_not_lt hn
    have hnot : n ∉ integerDetN := by
      have := lt_threshold
      simp only [integerDetN, Set.mem_union, Set.mem_Icc, Set.mem_insert_iff,
        Set.mem_singleton_iff]
      omega
    simp only [hnot, iff_false]
    exact L3_large n hlarge

end A060841
