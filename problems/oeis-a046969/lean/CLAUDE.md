# A046969 Lean project: rules for provers

Plan and the proof to formalize: `../PRD.md` (steps 1–4 of "Problem background").
Check any numeric claim with `../numerics/check.py` before trying to prove it.

## Target

Prove `OeisA46969.conjecture1` exactly as merged upstream in google-deepmind/formal-conjectures
(`FormalConjectures/OEIS/46969.lean`, pinned by commit in `lakefile.toml`):

```lean
theorem conjecture1 (p : ℕ) (hp : p.Prime) (hp' : (2 * p - 1).Prime) (h3 : 3 < p) :
    (a p / 12).Prime
```

Our proof is `A046969.conjecture1` in `A046969/Main.lean`. Its type is `type_of% @OeisA46969.conjecture1`,
so it is the upstream statement by construction. The upstream theorem itself is `sorry`; never cite it.

## Layout: one lemma per file, one prover per file

`S_m(n) = powSum m n = ∑_{k<n} k^m` and `q = 2p - 1`.

| File | Lemma | Statement |
| --- | --- | --- |
| `A046969/L1Den.lean` | `L1_den_bernoulli` (proved) | `(bernoulli (2 * p)).den = 6` (p, q prime, `3 < p`) |
| `A046969/FFaulhaber.lean` | `F_faulhaber` | `∃ r, ¬ ℓ ∣ r.den ∧ S_m(ℓ) = ℓ·B_m + ℓ²·r` (ℓ prime, m even, `4 ≤ m`, `¬ ℓ ∣ m + 1`) |
| `A046969/L2PowSum.lean` | `L2_sq_dvd_powSum` | `p ^ 2 ∣ powSum (2 * p) p` (p prime, `3 < p`) |
| `A046969/L3PowSum.lean` | `L3_powSum_div` | `q ∣ powSum (q + 1) q ∧ 12 * (powSum (q + 1) q / q) ≡ 1 [MOD q]` (q prime, `5 ≤ q`) |
| `A046969/L4Assembly.lean` | `L4_a_eq` | `a p = 12 * (2 * p - 1)` (p, q prime, `3 < p`), from L1, F, L2, L3 |

- F, L2 and L3 are stated more generally than the PRD needs (any prime, not just `p` with `2p - 1` prime);
  `../numerics/` confirms the general forms. L4 applies F at `(ℓ, m) = (p, 2p)` and `(q, q + 1)`:
  `p ∤ 2p + 1` and `q ∤ 2p + 1 = q + 2`.
- `A046969/Defs.lean` holds `powSum` and `a`, a copy of upstream's `a`; `Main.lean` proves them equal by `rfl`.
  Do not change `a`.
- `A046969/Main.lean` already assembles L4 into the upstream theorem and builds. Do not put proof work there.
- Edit only the file for your lemma. Helper lemmas go in that file (inside a `namespace A046969.<Lemma>` so
  helpers cannot clash when L4 imports every lemma file), or in a new `A046969/<Lemma>/*.lean` file imported
  only by it. Do not change a lemma's statement without sign-off: L4 depends on all four exactly as stated.

## Imports: keep lemma files light

Only `Main.lean` imports upstream, which pulls in all of Mathlib (about 90 s and 3.3 GB per load on this machine).
Lemma files import specific Mathlib modules (`Defs.lean` brings `Mathlib.NumberTheory.Bernoulli`) and load in
seconds. Keep it that way:

- Never `import Mathlib`, `import FormalConjecturesUtil` or the upstream module in a lemma file.
- Add the narrowest Mathlib module that has the lemma you need (its path is the file under `.lake/packages/mathlib/Mathlib/`).
  `exact?` and `apply?` only search what is imported, so add the likely module before searching.

## Hard rules

- Never edit, copy or restate the upstream statement or definitions (`a`, `conjecture1`), other than the copy of `a`
  checked by `rfl`. Never touch `.lake/packages/`.
- No `native_decide` (nor `decide +native`, `Lean.ofReduceBool`). Use `decide`, `decide +kernel`, `norm_num`, `simp`.
- No new axioms, no `axiom` declarations, no `implemented_by`/`extern` tricks.
- After every change, build your lemma and keep it green: `lake build A046969.L2PowSum` (seconds).
  `sorry` is allowed only in lemmas not yet proved.
- Before reporting a lemma done, run `scripts/check.sh` once (full build plus axiom check, a few minutes).
- Do not bump the formal-conjectures `rev`, the `lean-toolchain` or Mathlib, and never run `lake update`.
- Mathlib's von Staudt–Clausen proof (`Mathlib/NumberTheory/Bernoulli.lean`) has private helpers you cannot call;
  Epoch's Conjecture II proof (linked from upstream) has v_ℓ(B_i) machinery but no license, so read it as a
  reference only and write our own code.

## Checking axioms

```sh
scripts/check.sh
```

It runs `lake build`, then `#print axioms A046969.conjecture1` (from `scripts/Axioms.lean`), and fails on anything
beyond `propext`, `Classical.choice`, `Quot.sound`. `sorryAx` shows up (and fails) until every lemma is done.
To check one lemma quickly, put `import A046969.L2PowSum` and `#print axioms A046969.L2_sq_dvd_powSum` in a
scratch file and run `lake env lean <file>`.

## Setup in a new worktree: share the dependencies

```sh
scripts/shared-lake.sh        # link .lake/packages to the shared prebuilt tree (seconds)
scripts/shared-lake.sh status
```

Both scripts are thin wrappers around `tools/lean/` at the repository root, shared with every problem.
This project pins the same formal-conjectures commit as `problems/oeis-a060841/lean/`, so both use one
shared tree under `~/.cache/breakthroughs-lake/<pin>`. The tree is read-only and safe for any number of
worktrees at once; if it is missing or stale, the script falls back to a normal private build.
`scripts/shared-lake.sh unlink` gives this worktree a private copy. Each worktree still builds its own
`A046969.*` modules in its own `.lake/build`.

## Running two or more provers on this 16 GB Mac

- Build only your own lemma module while iterating. Never run a bare `lake build` in a loop: it rebuilds `Main.lean`.
- Cap Lean threads per prover: `export LEAN_NUM_THREADS=4`. Lake has no jobs flag; this also limits its build parallelism.
  `scripts/check.sh` sets 4 by default.
- `scripts/check.sh` holds a machine-wide lock (`~/.cache/breakthroughs-lake/check.lock`, shared with other problems),
  so full checks queue instead of loading all of Mathlib at the same time. Expect to wait if another prover is checking.
- Keep `decide`/kernel computations small: one runaway kernel reduction can use many GB. Add a limit while
  experimenting, for example `lake env lean -M 4096 <file>`.
