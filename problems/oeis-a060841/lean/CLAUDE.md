# A060841 Lean project: rules for provers

Plan: `../PRD.md`. The proof to formalize, with exact constants: `../BLUEPRINT.md` (follow it over the PRD where they differ).
Check any numeric claim with `../numerics/` before trying to prove it.

## Target

Prove `OeisA60841.conjecture1` exactly as merged upstream in google-deepmind/formal-conjectures
(`FormalConjectures/OEIS/60841.lean`, pinned by commit in `lakefile.toml`):

```lean
theorem conjecture1 :
    ∀ n : ℕ, 1 ≤ n → (((lcmMatrix n).det)⁻¹.den = 1 ↔ n ∈ integerDetN)
```

Our proof is `A060841.conjecture1` in `A060841/Main.lean`. Its type is `type_of% @OeisA60841.conjecture1`,
so it is the upstream statement by construction. The upstream theorem itself is `sorry`; never cite it.

## Layout: one lemma per file, one prover per file

| File | Lemma | Statement |
| --- | --- | --- |
| `A060841/L1Det.lean` | `L1_det_closedForm` | `((lcmMat n).det)⁻¹ = closedForm n` |
| `A060841/L2Small.lean` | `L2_small` | `1 ≤ n → n < threshold → ((closedForm n).den = 1 ↔ n ≤ 34 ∨ n = 36 ∨ n = 38)` |
| `A060841/L3Large.lean` | `L3_large` | `threshold ≤ n → (closedForm n).den ≠ 1` |

- `A060841/Defs.lean` holds `closedForm` and `threshold` (currently 82, the PRD's route; the blueprint also allows 79 or 50).
  The L2/L3 split is that one constant, and it must stay above 38. Changing it or `closedForm` affects every prover, so agree on it first.
- `lcmMat` (in `L1Det.lean`) is a copy of upstream's `lcmMatrix`; `Main.lean` proves them equal by `rfl`. Do not change it.
- L1 implies `det ≠ 0` (because `closedForm n ≠ 0`), and the integer direction depends on this (blueprint §8, flag 3).
- `A060841/Main.lean` already assembles the three lemmas and builds. Do not put proof work there.
- Edit only the file for your lemma. Helper lemmas go in that file, or in a new `A060841/<Lemma>/*.lean`
  file imported only by it. Do not change a lemma's statement without sign-off.

## Imports: keep lemma files light

Only `Main.lean` imports upstream, which pulls in all of Mathlib (about 80 s and 3.3 GB per load on this machine).
Lemma files import specific Mathlib modules and load in seconds. Keep it that way:

- Never `import Mathlib`, `import FormalConjecturesUtil` or the upstream module in a lemma file.
- Add the narrowest Mathlib module that has the lemma you need (its path is the file under `.lake/packages/mathlib/Mathlib/`).
  `exact?` and `apply?` only search what is imported, so add the likely module before searching.

## Hard rules

- Never edit, copy or restate the upstream statement or definitions (`lcmMatrix`, `integerDetN`, `conjecture1`), other than `lcmMat` checked by `rfl`.
  Never touch `.lake/packages/`.
- No `native_decide` (nor `decide +native`, `Lean.ofReduceBool`). Use `decide`, `decide +kernel`, `norm_num`, `simp`.
- No new axioms, no `axiom` declarations, no `implemented_by`/`extern` tricks.
- After every change, build your lemma and keep it green: `lake build A060841.L3Large` (seconds).
  `sorry` is allowed only in lemmas not yet proved.
- Before reporting a lemma done, run `scripts/check.sh` once (full build plus axiom check, a few minutes).
- Do not bump the formal-conjectures `rev`, the `lean-toolchain` or Mathlib, and never run `lake update`.

## Checking axioms

```sh
scripts/check.sh
```

It runs `lake build`, then `#print axioms A060841.conjecture1` (from `scripts/Axioms.lean`), and fails on anything
beyond `propext`, `Classical.choice`, `Quot.sound`. `sorryAx` shows up (and fails) until all three lemmas are done.
To check one lemma quickly, put `import A060841.L3Large` and `#print axioms A060841.L3_large` in a scratch file
and run `lake env lean <file>`.

## Setup in a new worktree: share the dependencies

```sh
scripts/shared-lake.sh        # link .lake/packages to the shared prebuilt tree (seconds)
scripts/shared-lake.sh status
```

The first run on a machine fetches the Mathlib cache, builds the upstream support library privately
(about 15 min) and publishes the result to `~/.cache/breakthroughs-lake/<pin>`. Later worktrees link to it in seconds.
The shared tree is read-only and safe for any number of worktrees at once. If it is missing or stale, the script
falls back to a normal private build. `scripts/shared-lake.sh unlink` gives this worktree a private copy.
Each worktree still builds its own `A060841.*` modules in its own `.lake/build`.

## Running two or more provers on this 16 GB Mac

- Build only your own lemma module while iterating. Never run a bare `lake build` in a loop: it rebuilds `Main.lean`.
- Cap Lean threads per prover: `export LEAN_NUM_THREADS=4`. Lake has no jobs flag; this also limits its build parallelism.
  `scripts/check.sh` sets 4 by default.
- `scripts/check.sh` holds a machine-wide lock (`~/.cache/breakthroughs-lake/check.lock`), so full checks from
  several worktrees queue instead of loading all of Mathlib at the same time. Expect to wait if another prover is checking.
- Use the shared tree (above). One copy of the Mathlib `.olean` files lets the OS page cache hold it once for every prover.
- Keep `decide`/kernel computations small (split ranges, compare valuations per prime): one runaway kernel
  reduction can use many GB. Add a limit while experimenting, for example `lake env lean -M 4096 <file>`.
