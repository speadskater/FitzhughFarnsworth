# FitzhughFarnsworth

A Lean 4 + mathlib formalization of Joshua M. Fitzhugh and David L. Farnsworth,
[The Behavior of Midsets When Repeatedly Taking the Midset of Two Lines in ℓ₁ Geometry](https://doi.org/10.1155/2014/832647),
*International Journal of Mathematics and Mathematical Sciences* (2014), Article 832647.

**The target is the whole paper, developed in verified stages. The formalization is not complete.**
The first stage proves the taxicab metric, distances to origin-centered lines,
the axes/diagonals cycle, and the geometric correctness and octant invariants of
Algorithm 6 in its canonical configuration. General convergence remains open.

## Build

Install [Lean's elan toolchain manager](https://lean-lang.org/install/), then run:

```sh
git clone git@github.com:speadskater/FitzhughFarnsworth.git
cd FitzhughFarnsworth
lake exe cache get
lake build
lake env lean scripts/Audit.lean
```

Lean and mathlib are pinned to `v4.35.0`; `lake-manifest.json` pins the exact
dependency commits. VS Code with the Lean 4 extension provides interactive proof
states when this directory is opened.

## Library

```text
FitzhughFarnsworth.lean                 # Imports the entire library
FitzhughFarnsworth/
  MetricGeometry.lean                 # Taxicab plane and metric axioms
  Midsets.lean                        # Equidistance sets using Metric.infDist
  LineDistances.lean                  # Distance formulas and geometric midsets
  LineConfigurations.lean             # Canonical even/odd slope regions
  IteratedMidsets.lean                 # Parity maps and verified iteration
  Convergence.lean                    # Limit specification and fixed-cycle lemma
```

The dedicated `Point` type has the distance `|x₁ - x₂| + |y₁ - y₂|`.
It avoids accidentally inheriting mathlib's maximum metric on `ℝ × ℝ`.
Line distances are proved from the infimum of point distances, with explicit
nearest points. Vertical lines are represented separately from finite slopes.

`SlopePair.evenIterate s n` is the pair at the paper's index `2*n`;
`oddIterate s n` is the pair at index `2*n+1`. The midset of the two component
lines is their next pair's union. Iteration retains the component lines: it
does not take the distance to their union as a substitute for two inputs.

## Verification status

| Paper component | Status |
| --- | --- |
| Taxicab metric and distance-to-line foundations | Proved |
| Theorem 1 | Proved for the canonical even/odd orientations; symmetry reduction pending |
| Theorem 2: orthogonal fixed cycles and 45° rotation | Pending |
| Theorem 3: axes ↔ diagonals | Proved as equalities of geometric sets |
| Theorems 4–5: reduction of the remaining configurations | Pending |
| Algorithm 6 | Defined; geometric correctness and all-iterate octant bounds proved for canonical input |
| Theorem 7: characterization of limiting cycles | Pending |
| Theorem 8: reciprocal symmetry | Pending |
| Theorem 9: monotonicity and convergence | Pending |
| Table 1 and Section 4 angle conventions | Pending |

See [the proof roadmap](docs/ROADMAP.md) for the next stages and precise remaining
obligations. This status table distinguishes canonical statements from the full
geometric theorems.

CI builds the library with warnings treated as errors and audits every exported
declaration in the project namespace. Only Lean's usual `propext`,
`Classical.choice`, and `Quot.sound` axioms are allowed. There are no `sorry`
proofs or project-specific mathematical axioms; unproved results stay in the
roadmap rather than appearing as assumed theorems.
