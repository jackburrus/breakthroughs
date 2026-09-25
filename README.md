# Breakthroughs

Work on open problems where a solution can be checked by a machine.

- `problems/oeis-a060841/`: a Lean 4 proof attempt for OEIS A060841 conjecture 1 (integrality of 1/det of the n by n lcm matrix exactly for n in 1..34, 36, 38). See its PRD, the proof blueprint (`BLUEPRINT.md`) and the exact numerics harness (`numerics/`).
- `problems/oeis-a046969/`: PRD for OEIS A046969 Conjecture I (a(p)/12 prime for primes p > 3 with 2p-1 prime); proof via a(p) = 12(2p-1), von Staudt-Clausen and two power-sum congruences. Numerics in `numerics/check.py`.
- `problems/oeis-a141057/`: a Lean 4 proof of OEIS A141057 conjecture 2 (Bala's supercongruences for the negative-index extension, both signs), in `lean/`, which builds with only the standard axioms. See its PRD, `NOTES.md` (open-status check and proof structure), and `numerics/lemmas.py`, which checks every lemma statement. Epoch AI's agent proved the positive-index case in August 2026.
- `problems/oeis-a003161/`: stretch PRD for the A003161 supercongruence for cubed ballot numbers.
