# Working on this formalization

Read `README.md` and `docs/ROADMAP.md` before extending the library.

- Use the pinned Lean/mathlib versions and commit dependency changes explicitly.
- Run `lake build` and `lake env lean scripts/Audit.lean` before committing proofs.
- No `sorry`, `admit`, project-specific mathematical axioms, or `native_decide`.
- Pending mathematical claims belong in the roadmap, not as assumed theorems.
- Preserve the link between slope formulas and `Metric.infDist` in the taxicab metric.
- Keep strict inequalities, nonzero denominator hypotheses, vertical lines, and
  symmetry reductions explicit. Never use arbitrary rotations as taxicab isometries.
- Track the paper's numbering and distinguish canonical from fully general claims.
- Update the verification status when proofs are added.
