import FormalConjectures.OEIS.«60841»
import A060841.L1Det
import A060841.L2Small
import A060841.L3Large

/-!
# Assembly of `OeisA60841.conjecture1`

The only file that imports the upstream statement. The type is taken verbatim from the
upstream theorem with `type_of%`, so nothing is restated, and `lcmMat` is checked to be
upstream's `lcmMatrix` by `rfl`. Do not add proof work here; it belongs in L1, L2 or L3.
-/

namespace A060841

open OeisA60841

theorem lcmMat_eq : lcmMat = lcmMatrix := rfl

theorem conjecture1 : type_of% @OeisA60841.conjecture1 := by
  intro n h1
  rw [← lcmMat_eq, L1_det_closedForm]
  have hI : n ∈ integerDetN ↔ n ≤ 34 ∨ n = 36 ∨ n = 38 := by
    simp only [integerDetN, Set.mem_union, Set.mem_Icc, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    omega
  rw [hI]
  by_cases hn : n < threshold
  · exact L2_small n h1 hn
  · have := lt_threshold
    have hnot : ¬ (n ≤ 34 ∨ n = 36 ∨ n = 38) := by omega
    simp only [hnot, iff_false]
    exact L3_large n (by omega)

end A060841
