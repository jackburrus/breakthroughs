# Project agent memory

This file is the project's committed home for project-intrinsic agent knowledge: build, test, release, architecture, and sharp-edge notes that should travel with the code.

- Each problem lives under `problems/<id>/`: `PRD.md` is the owner's plan, `BLUEPRINT.md` the human-readable proof the Lean work follows.
- A060841 numerics: `problems/oeis-a060841/numerics/` is standard-library Python with exact int/Fraction arithmetic only. Check any intermediate claim there before trying to prove it.
- Run its tests with `python3 -m unittest` inside that directory. They fail if `REPORT.md` or `valuations_n_le_81.csv` is stale; regenerate both with `python3 report.py --write`.
- Outward steps (GitHub forks or PRs, OEIS comments, publishing write-ups) belong to the project owner, not agents.
- Each `problems/<id>/lean/` is a Lake project pinned to google-deepmind/formal-conjectures by commit; its `CLAUDE.md` holds the prover rules (no `native_decide`, no new axioms, never edit upstream statements) and `scripts/check.sh` is the build-and-axiom gate.
- Only `<ID>/Main.lean` imports upstream (all of Mathlib, minutes per load); lemma files import specific Mathlib modules. New worktrees run `scripts/shared-lake.sh` to share one prebuilt dependency tree per pin across problems; never compile Mathlib.
- Both per-project scripts wrap `tools/lean/`; a new problem copies the wrappers and keeps the same pin when upstream allows, so it reuses the tree.

## Maintaining this file

Keep this file for knowledge useful to almost every future agent session in this project.
Do not repeat what the codebase already shows; point to the authoritative file or command instead.
Prefer rewriting or pruning existing entries over appending new ones.
When updating this file, preserve this bar for all agents and keep entries concise.
