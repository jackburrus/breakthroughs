import FormalConjectures.OEIS.«46969»
import A046969.L4Assembly

/-!
# Assembly of `OeisA46969.conjecture1`

The only file that imports the upstream statement. The type is taken verbatim from the
upstream theorem with `type_of%`, so nothing is restated, and `a` is checked to be
upstream's `a` by `rfl`. Do not add proof work here; it belongs in the lemma files.
-/

namespace A046969

theorem a_eq : a = OeisA46969.a := rfl

theorem conjecture1 : type_of% @OeisA46969.conjecture1 := by
  intro p hp hp' h3
  rw [← a_eq, L4_a_eq p hp hp' h3, Nat.mul_div_cancel_left _ (by norm_num)]
  exact hp'

end A046969
