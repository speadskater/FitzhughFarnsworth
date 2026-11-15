# FitzhughFarnsworth

A Lean 4 + mathlib formalization of Joshua M. Fitzhugh and David L. Farnsworth,
[The Behavior of Midsets When Repeatedly Taking the Midset of Two Lines in ℓ₁ Geometry](https://doi.org/10.1155/2014/832647),
*International Journal of Mathematics and Mathematical Sciences* (2014), Article 832647.

**The numbered theorems and Algorithm 6 now have machine-checked proofs.**
The library includes general geometric reduction for distinct intersecting affine
lines, canonical slope convergence, orthogonal two-cycles, Euclidean rotation and
angle statements, and the geometric constructions in Section 4.

The entire paper is not yet certified word for word: the published numerical
roundings remain outside Lean. High-precision reproduction flags two entries of
Table 1; see [the numerical notes](docs/NUMERICAL_NOTES.md).

## Build

Install [Lean's elan toolchain manager](https://lean-lang.org/install/), then run:

```sh
git clone https://github.com/speadskater/FitzhughFarnsworth.git
cd FitzhughFarnsworth
lake exe cache get
lake build
lake env lean scripts/Audit.lean
```

Lean and mathlib are pinned to `v4.35.0`; `lake-manifest.json` pins exact dependency
commits. Open the repository in VS Code with the Lean 4 extension for interactive
proof states. GitHub CI runs both the build and the proof-dependency audit.

## Library

The original six modules remain the foundation, with supporting proofs in submodules:

| Module | Contents |
| --- | --- |
| `MetricGeometry.lean` | Taxicab plane and metric axioms |
| `Midsets.lean` | Equidistance sets using `Metric.infDist` |
| `LineDistances.lean` | Distances to all origin lines; geometric midset formulas |
| `LineConfigurations.lean` | Canonical even/odd slope regions |
| `LineConfigurations/Reduction.lean` | Full geometric reduction, symmetries, affine translation |
| `LineConfigurations/Boundary.lean` | All axis/diagonal cases of Theorem 4 |
| `LineConfigurations/Euclidean.lean` | Inner products, actual set cycles, rotations and angles |
| `LineConfigurations/Translated.lean` | Fixed cycles and rotations about arbitrary intersections |
| `IteratedMidsets.lean` | Algorithm 6 and geometric correctness of every step |
| `IteratedMidsets/Algebra.lean` | Closed formulas, fixed points and reciprocal symmetry |
| `Convergence.lean` | Existence, uniqueness, limiting cycles and shared symmetric limits |
| `Convergence/Monotonicity.lean` | Strict monotonicity and uniform interior bounds |
| `Convergence/Angles.lean` | Geometric limiting cycles; angles approach π/2 |
| `Convergence/Enclosures.lean` | Rigorous finite-iterate error bounds |
| `AngleConventions.lean` | Section 4's four constructions, diamond arcs and sector areas |
| `AngleConventions/Comparison.lean` | Exact proof that all four conventions can differ |

`FitzhughFarnsworth.lean` imports the complete library.

## Correspondence with the paper

| Paper component | Verified result / entry point |
| --- | --- |
| Theorem 1 | `configuration_one_two_steps`, both orientations and input orderings |
| Theorem 2 | `midset_midset_eq_self_iff_even/odd`, `midset_eq_rotate_of_orthogonal`; translated versions included |
| Theorem 3 | `midset_axes`, `midset_diagonals` |
| Theorem 4 | `configuration_three_two_steps`: specifically Configuration 1 after two steps |
| Theorem 5 | `reduces_intersecting_affine_lines`: the stronger bound of **two** steps |
| Algorithm 6 | `evenIterate_midset`, `oddIterate_midset` |
| Theorem 7 | `convergesToCycle_characterization`, `exists_geometric_limit_cycle` |
| Theorem 8 | `evenIterate_reciprocal`, `evenIterate_of_angle_symmetry` |
| Theorem 9 | `exists_orthogonal_limit_cycle`, strict slope/product/angle monotonicity, `exists_shared_orthogonal_limit_cycle` |
| Section 4 | Four conventions and their geometric properties; `exists_four_distinct_bisectors` separates all four on an exact rational example |
| Table 1 and numerical examples | Reproduced numerically; exact decimal certification pending |

Most iteration theorems are in namespace `FitzhughFarnsworth.SlopePair`.
The [proof roadmap](docs/ROADMAP.md) records the remaining scope and useful entry points.

## Mathematical scope

The dedicated `Point` type carries `|x₁-x₂| + |y₁-y₂|`, avoiding the default
maximum metric on `ℝ × ℝ`. Line distances are proved from the infimum of point
distances with explicit nearest points. Vertical lines and boundary slopes are
included. Translation, coordinate swap and reflection are proved taxicab
isometries. Euclidean rotation is used only for the paper's Euclidean claims.

`evenIterate s n` denotes paper index `2*n`; `oddIterate s n` denotes `2*n+1`.
Convergence means convergence of both slope subsequences. The two component
lines remain separate inputs to each midset operation. The general affine
reduction and the canonical slope analysis are separate theorems, following the
paper's normalization at the intersection. No Hausdorff convergence claim for
unbounded line sets is made.

Only Lean's usual `propext`, `Classical.choice`, and `Quot.sound` axioms are
allowed by the audit. There are no unfinished proofs or project-specific
mathematical axioms in the library.

## Numerical reproduction

This uses only Python's standard library:

```sh
python3 examples/reproduce_paper.py --precision 80
```

It is an independent numerical illustration, not a substitute for a Lean proof.
The formal `limit_enclosure` theorem provides a foundation for future certified
rounding: each limiting shallow slope lies between `a_n` and `-1/b_n`, and the
interval width tends to zero.
