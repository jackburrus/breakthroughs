# A141057 Lean project: rules for provers

The plan is `../PRD.md`. `../NOTES.md` has the open-status check and the proof structure.
Each lemma file's docstring sketches its proof. Check any numeric claim with `../numerics/lemmas.py` before trying to prove it.

## Target

Prove `OeisA141057.conjecture2` exactly as merged upstream in google-deepmind/formal-conjectures
(`FormalConjectures/OEIS/141057.lean`, pinned by commit in `lakefile.toml`):

```lean
theorem conjecture2 (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k)
    (hn : n ≠ 0) :
    aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]
```

Our proof is `A141057.conjecture2` in `A141057/Main.lean`. Its type is `type_of% @OeisA141057.conjecture2`,
so it is the upstream statement by construction. Upstream's `conjecture1` and `conjecture2` are both `sorry`, so never cite them.
The statement covers both signs of `n`, so the positive case is proved again here.

## Layout: one lemma file per letter

Each hypothesis `p ≥ 5` below also includes `p.Prime`. Exponents come from hypotheses `p ^ e ∣ n`, not from valuations.

| File | Lemmas | Statement | Uses |
| --- | --- | --- | --- |
| `UUnitSums.lean` | `U_sum_unit_sq`, `U.sum_range_coprime` | `∑ u ^ 2 = 0` over the units of `ZMod (p^s)` (`p ≥ 5`); a sum over `a < p^s c`, `p ∤ a`, of a function of `a` mod `p^s` is `c` times its sum over the units | |
| `DShiftProd.lean` | `D_shift_prod` | `∏ (x + a) ≡ ∏ a [ZMOD p^(3 min(r, s))]` over `a < N`, `p ∤ a`, if `p^r ∣ x` and `p^s ∣ N` (`p ≥ 5`) | U |
| `KJacobsthal.lean` | `K_choose` | `C((a+b) p, a p) ≡ C(a+b, a) [ZMOD p^(w + 3u + 3)]` if `p^u ∣ a`, `p^u ∣ b`, `p^w ∣ C(a+b, a)` (`p ≥ 5`) | D |
| `KNegJacobsthal.lean` | `K_chooseNeg` | `C(b p + a p - 1, a p) ≡ C(b+a-1, a) [ZMOD p^(w + 3u + 3)]` if `p^u ∣ a`, `p^u ∣ b`, `p^w ∣ C(b+a-1, a)` (`p ≥ 5`) | K's helpers, D |
| `AAbsorption.lean` | `A_absorb`, `A_absorbNeg`, `A_gcd`, `A_gcdNeg`, `A_symm_neg` | `N ∣ k C(N,k)`, `N ∣ k C(N+k-1,k)`, `x+y ∣ gcd(x,y) C(x+y,x)`, `N ∣ gcd(N,k) C(N+k-1,k)`, and `C(N+k-1,k) C(k,j) = C(N+j-1,j) C(N+k-1,k-j)` | |
| `VVanish.lean` | `V_pos`, `V_neg` | `p^e ∣ N` gives `p^e ∣ C(N,k) C(k,j)` and `∣ C(N+k-1,k) C(k,j)` unless `p ∣ k ∧ p ∣ j` | A |
| `PPerTerm.lean` | `P_summand`, `P_summandNeg` | the cubed summands at `((a+b) p, a p)` and `(a+b, a)` agree `[ZMOD p^(3e+3)]` if `p^e ∣ a+b+c` (resp. `p^e ∣ m`, `1 ≤ m`) | K, K⁻, A |
| `SSplit.lean` | `S_split` | a double sum over `j ≤ k ≤ m p` reduces mod `q` to one over `l ≤ i ≤ m` | |
| `ROneStep.lean` | `R_step`, `R_stepNeg`, `R_stepInt`, `R_pow` | `p^e ∣ n` gives `aInt(n p) ≡ aInt(n) [ZMOD p^(3e+3)]`; then `aInt(n p^(j+1)) ≡ aInt(n p^j) [ZMOD p^(3(j+1))]` | S, V, P |

- Every file is proved: there is no `sorry`, and `scripts/check.sh` passes with only the standard axioms.
- `Defs.lean` holds `aInt`, a copy of upstream's `aInt`, and `Main.lean` proves them equal by `rfl`. Do not change it.
- `Main.lean` only reindexes `k = j + 1` and applies `R_pow`. Do not put proof work there.
- Helper lemmas go in their lemma's file, inside a `namespace A141057.<Letter>` so that helpers cannot clash when R
  imports every lemma file, or in a new `A141057/<Letter>/*.lean` file imported only by it.
  Do not change a lemma's statement without sign-off: other files depend on it exactly as stated.

## Imports: keep lemma files light

Only `Main.lean` imports upstream, which pulls in all of Mathlib (about 90 s and 3.3 GB per load on this machine).
Lemma files import specific Mathlib modules and load in seconds. Keep it that way:

- Never `import Mathlib`, `import FormalConjecturesUtil` or the upstream module in a lemma file.
- Add the narrowest Mathlib module that has the lemma you need (its path is the file under `.lake/packages/mathlib/Mathlib/`).
  `exact?` and `apply?` search only what is imported, so add the likely module before searching.

## Hard rules

- Never edit, copy or restate the upstream statement or definitions (`a`, `aInt`, `conjecture2`), other than the copy of `aInt`
  checked by `rfl`. Never touch `.lake/packages/`.
- No `native_decide` (nor `decide +native`, `Lean.ofReduceBool`). Use `decide`, `decide +kernel`, `norm_num`, `simp`.
- No new axioms, no `axiom` declarations, no `implemented_by`/`extern` tricks.
- After every change, build your lemma and keep it green, for example `lake build A141057.DShiftProd` (seconds).
  `sorry` is allowed only in lemmas not yet proved.
- Before reporting a lemma done, run `scripts/check.sh` once (full build plus axiom check, a few minutes).
- Do not bump the formal-conjectures `rev`, the `lean-toolchain` or Mathlib, and never run `lake update`.

## Checking axioms

```sh
scripts/check.sh
```

It runs `lake build`, then `#print axioms A141057.conjecture2` (from `scripts/Axioms.lean`). It fails on any axiom
other than `propext`, `Classical.choice` and `Quot.sound`. `sorryAx` appears, and fails the check, until every lemma is done.
To check one lemma quickly, put `import A141057.DShiftProd` and `#print axioms A141057.D_shift_prod` in a
scratch file and run `lake env lean <file>`.

## Setup in a new worktree: share the dependencies

```sh
scripts/shared-lake.sh        # link .lake/packages to the shared prebuilt tree (seconds)
scripts/shared-lake.sh status
```

Both scripts are thin wrappers around `tools/lean/` at the repository root, which every problem shares.
This project pins the same formal-conjectures commit as A060841 and A046969, so all three use one
shared tree under `~/.cache/breakthroughs-lake/<pin>`. That tree is read-only and safe for any number of worktrees at once.
If it is missing or stale, the script falls back to a normal private build.
`scripts/shared-lake.sh unlink` gives this worktree a private copy. Each worktree still builds its own
`A141057.*` modules in its own `.lake/build`.

## Running two or more provers on this 16 GB Mac

- Build only your own lemma module while iterating. Never run a bare `lake build` in a loop, because it rebuilds `Main.lean`.
- Cap Lean threads per prover: `export LEAN_NUM_THREADS=4`. Lake has no jobs flag, and this setting also limits its build parallelism.
  `scripts/check.sh` sets 4 by default.
- `scripts/check.sh` holds a machine-wide lock (`~/.cache/breakthroughs-lake/check.lock`, shared with other problems),
  so full checks queue instead of loading all of Mathlib at the same time. Expect to wait if another prover is checking.
- Keep `decide` and kernel computations small, because one runaway kernel reduction can use many GB. Add a memory limit while
  experimenting, for example `lake env lean -M 4096 <file>`.
