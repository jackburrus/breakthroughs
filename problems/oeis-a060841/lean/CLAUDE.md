# A060841 Lean project: rules for provers

Plan and math: `../PRD.md` (read the Approach section before starting).

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
| `A060841/L1Det.lean` | `L1_det_closedForm` | `((lcmMatrix n).det)⁻¹ = closedForm n` |
| `A060841/L2Small.lean` | `L2_small` | `1 ≤ n → n < threshold → ((closedForm n).den = 1 ↔ n ∈ integerDetN)` |
| `A060841/L3Large.lean` | `L3_large` | `threshold ≤ n → (closedForm n).den ≠ 1` |

- `A060841/Defs.lean` holds `closedForm` and `threshold` (currently 82). The L2/L3 split is that one constant;
  it must stay above 38. Changing it or `closedForm` affects every prover, so agree on it first.
- `A060841/Main.lean` already assembles the three lemmas and builds. Do not put proof work there.
- Edit only the file for your lemma. Helper lemmas go in that file, or in a new `A060841/<Lemma>/*.lean`
  file imported only by it. Do not change a lemma's statement without sign-off.

## Hard rules

- Never edit, copy or restate the upstream statement or definitions (`lcmMatrix`, `integerDetN`, `conjecture1`).
  Never touch `.lake/packages/`.
- No `native_decide` (nor `decide +native`, `Lean.ofReduceBool`). Use `decide`, `decide +kernel`, `norm_num`, `simp`.
- No new axioms, no `axiom` declarations, no `implemented_by`/`extern` tricks.
- Run `lake build` after every change and keep it green. `sorry` is allowed only in lemmas not yet proved.
- Do not bump the formal-conjectures `rev`, the `lean-toolchain` or Mathlib.

## Checking axioms

```sh
scripts/check.sh
```

It runs `lake build`, then `#print axioms A060841.conjecture1` (from `scripts/Axioms.lean`), and fails on anything
beyond `propext`, `Classical.choice`, `Quot.sound`. `sorryAx` shows up (and fails) until all three lemmas are done.
To check one lemma, run `lake env lean` on a scratch file with `import A060841` and `#print axioms A060841.L3_large`.

## Setup on a fresh clone

`lake update` is not needed (the manifest is committed). Run `lake exe cache get` to fetch the Mathlib build cache
instead of compiling Mathlib, then `lake build`. The first build compiles formal-conjectures' own support library.
