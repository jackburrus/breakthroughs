import FormalConjectures.OEIS.«141057»
import A141057.ROneStep

/-!
# Assembly of `OeisA141057.conjecture2`

The only file that imports the upstream statement. The type is taken verbatim from the
upstream theorem with `type_of%`, so nothing is restated, and `aInt` is checked to be
upstream's `aInt` by `rfl`. Do not add proof work here; it belongs in the lemma files.
-/

namespace A141057

theorem aInt_eq : aInt = OeisA141057.aInt := rfl

theorem conjecture2 : type_of% @OeisA141057.conjecture2 := by
  intro p k n hp h_p_ge_5 h_k_pos hn
  rw [← aInt_eq]
  exact Int.modEq_iff_dvd.mpr (R_dvd p k n hp h_p_ge_5 h_k_pos hn)

end A141057
