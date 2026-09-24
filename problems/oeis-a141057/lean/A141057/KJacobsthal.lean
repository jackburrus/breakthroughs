import A141057.DShiftProd
import Mathlib.Data.Nat.Choose.Basic

/-!
# K: the Jacobsthal–Kazandzidis congruence

PRD step 2 (node K). For a prime `p ≥ 5` and `B ≤ A`,
`C(A p, B p) ≡ C(A, B) (mod p ^ (v_p C(A, B) + 3 + 3 min(v_p B, v_p (A - B))))`.
Proof idea: let `G(R) = ∏_{1 ≤ j ≤ R p, p ∤ j} j`, so `(R p)! = G(R) p ^ R R!`. With `L = A - B`,
this gives `C(A p, B p) G(B) G(L) = C(A, B) G(A)` and `G(A) = G(B) ∏_{0 ≤ a < L p, p ∤ a} (B p + a)`,
hence `(C(A p, B p) - C(A, B)) G(L) = C(A, B) (∏ (B p + a) - ∏ a)`. Apply D and cancel `G(L)`,
which is prime to `p`.
Checked by `../numerics/lemmas.py` (check `K`), which also shows it fails at `p = 3`.
-/

namespace A141057

/-- **K**: `p ^ (v_p C(A, B) + 3 + 3 min(v_p B, v_p (A - B))) ∣ C(A p, B p) - C(A, B)`. -/
theorem K_jacobsthal (p A B : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hBA : B ≤ A) :
    (p : ℤ) ^ (padicValNat p (A.choose B) + 3 +
        3 * min (padicValNat p B) (padicValNat p (A - B))) ∣
      ((A * p).choose (B * p) : ℤ) - (A.choose B : ℤ) := by
  sorry

end A141057
