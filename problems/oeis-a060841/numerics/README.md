# A060841 numerics harness

Exact checks (Python standard library, `int` and `Fraction` only) for every numeric claim in `../BLUEPRINT.md`.

- `a060841.py`: the library. It covers the closed form, determinant checks, valuations, the L3 constants and thresholds, and the window certificate.
- `report.py`: regenerates `REPORT.md` and `valuations_n_le_81.csv`. Run `python3 report.py --write`; options: `--max-n`, `--scan-n`, `--det-n`, `--bareiss-n`.
- `test_a060841.py`: regression tests (`python3 -m unittest`, about 10 s). They also fail if the generated files are stale.
- `data/b060841.txt`: the OEIS A060841 b-file (a(1..400), dated 3 August 2015), used as an external cross-check. OEIS content is CC BY-SA 4.0.
