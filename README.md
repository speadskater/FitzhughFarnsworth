# FitzhughFarnsworth

A Lean 4 + mathlib project formalizing three papers by Joshua M. Fitzhugh and
David L. Farnsworth, together with Joshua M. Fitzhugh's Wallis moment extension.
Verification status is tracked separately for each paper.

| Paper | Status |
| --- | --- |
| [The Behavior of Midsets When Repeatedly Taking the Midset of Two Lines in ℓ₁ Geometry](https://doi.org/10.1155/2014/832647) (2014) | Complete at the stated intersecting-line scope, including end-to-end correctness |
| [A Construction That Produces Wallis-Type Formulas](https://repository.rit.edu/article/2109/) (2013) | Complete at the stated positive-parameter scope, including all `p > 0` area formulas and documented source corrections |
| [The Behavior of Normality when Iteratively Finding the Normal to a Line in an ℓₚ Geometry](https://repository.rit.edu/article/2108/) (2013) | Complete for finite `p > 1` and the stated regular-graph scope, including metric normality, geometric limits, and a correction to the concluding circumference claim |
| [Area Moments from a Wallis-Type Geometric Construction](papers/wallis-moments/wallis-moments.pdf) (2026 research draft) | Central results verified in Lean at the documented scope; independent human review pending |

**The three original papers are fully formalized at their documented scopes.**
The [roadmap](docs/ROADMAP.md) records the verified equations, hypotheses, and
source corrections, including the regularity assumptions for the normality paper.

An additional Wallis extension is verified: measured area moments of every real
order `r > -1`, their relation to construction side ratios, higher-order
recurrences, and cyclic unit-volume attachments from a cube of any positive
starting volume. This extension is separate from the original paper's scope.
The accompanying research draft is available as a
[PDF](papers/wallis-moments/wallis-moments.pdf) and
[LaTeX source](papers/wallis-moments/wallis-moments.tex), with
[build and review notes](papers/wallis-moments/README.md).

Reusable results from all three papers are packaged as seven small mathlib
candidate patches. The [upstream overview](docs/UPSTREAM.md),
[Wallis review guide](docs/WALLIS_UPSTREAM.md), and
[normality review guide](docs/NORMALITY_UPSTREAM.md) describe their independent
checks and the human review still needed before submission.

For the **midset paper**, the mathematical formalization includes end-to-end
correctness of the iteration.
Starting from arbitrary distinct intersecting affine lines, the general iteration
preserves genuine line components, takes the actual metric midset at every step,
and converges to a distinct orthogonal two-cycle. The limit pairs differ by a
Euclidean 45° rotation. The result holds independently of component ordering.

The numbered theorems, Algorithm 6, and Section 4's geometric constructions are
also proved. Numerical illustrations are separate from this mathematical scope;
the [numerical notes](docs/NUMERICAL_NOTES.md) record a reproduction of the paper's
printed values, without making their certification a prerequisite for correctness.

## Build

Install [Lean's elan toolchain manager](https://lean-lang.org/install/), then run:

```sh
git clone https://github.com/speadskater/FitzhughFarnsworth.git
cd FitzhughFarnsworth
lake exe cache get
lake build
python3 scripts/lint_project.py
lake exe lint-style
lake env lean scripts/Audit.lean
python3 scripts/test_audit.py
```

For a machine with limited memory, use `LEAN_NUM_THREADS=1 lake build`.
Development checks also run inside a Linux systemd scope with `MemoryMax=6G`
and `MemorySwapMax=0`; builds and audits run sequentially.

Lean is pinned to `v4.36.0-rc2` and mathlib to commit
`cbe1882f5b62496bdfc6bbe540a2b3f2db852440` (master checked on 2026-11-15).
`lake-manifest.json` pins every dependency. Open the repository in VS Code with
the Lean 4 extension for interactive proof states. The build enables mathlib's
standard source linters; CI also runs declaration/style linting and the axiom audit.
The declaration-lint runner includes private declarations and rejects an empty
linter set; the pinned default `lake lint` driver currently loads no environment
linters for this project.

## Normality library

The normality paper is *Advances in Pure Mathematics* **3** (2013), 647–652,
DOI [10.4236/apm.2013.38086](https://doi.org/10.4236/apm.2013.38086).
Its modules use namespace `FitzhughFarnsworth.Normality`:

| Module | Verified contents |
| --- | --- |
| `Normality/Basic.lean` | Formulas (3)–(6), sign and reciprocal identities, explicit axes and diagonals, and the Euclidean involution |
| `Normality/Iteration.lean` | Formulas (7)–(11), nonzero iterate preservation, reflection and reciprocal symmetry |
| `Normality/Geometry.lean` | Lemma 3.1 from minimization in the actual p-metric, uniqueness, every iteration step, isometries, and `Metric.infDist` |
| `Normality/Convergence.lean` | Theorems 3.4–3.5: all positive slope ranges, strict parity monotonicity, and finite or infinite limits |
| `Normality/LineConvergence.lean` | Actual projective-line limits for both signs, vertical limits, exact boundary cycles, and uniqueness of every geometric evolution |
| `Normality/Radon.lean` | Conjugate exponents, equations (12)–(14), the differential equation and its uniqueness, and the alternating-quadrant involution |
| `Normality/RadonGeometry.lean` | Convex joined disk, exact quadrant formulas, norm axioms, and a separate standard Lean normed-space instance |
| `Normality/RadonNormality.lean` | Theorem 4.1's geometric sufficiency: unique normals, reflexivity for arbitrary vectors, and attained metric infima |
| `Normality/UnitCircle.lean` | Explicit p-circle contact points, tangency, joined unit-circle equations, differentiable axis joins, and uniqueness of the q-circle graph |
| `Normality/Circumference.lean` | Regular arc charts, actual velocities, corrected circumference integrals, and the exact counterexample at `p = 6` |
| `Normality/Circumference/PathLength.lean` | Connection to mathlib path lengths in the p-metric and joined metric |

`Parameters` requires finite `p > 1`. `Direction.isNormal_iff_eq_next` proves
that the iteration uses the unique distance-minimizing normal. Line convergence
uses mathlib's real projective line: both signs of infinite slope approach the
same vertical line. `Direction.evolution_eq_iterate` connects these conclusions
to every sequence that takes geometric normals.

For Theorem 4.1, `Radon.Plane g` is the actual constructed normed space, with
p-arcs in quadrants I/III and conjugate q-arcs in II/IV.
`Radon.normality_reflexive_vectors` proves reflexive normality for arbitrary
vectors. `Radon.quadrant_unique_graph` proves necessity for a continuous
upper-left quadrant graph, positive in its interior, with positive interior
derivative, the endpoint value `f 0 = 1`, and the paper's reflexive tangency
condition against the given p-arc. These assumptions are explicit.

The [roadmap](docs/ROADMAP.md#normality-paper-2013) gives the theorem correspondence
and scope. The [source-check notes](docs/NORMALITY_NOTES.md) document three
Table 1 discrepancies and the exact refutation of the concluding circumference
claim: at `p = 6`, the joined perimeter is below 7 and the original p-circle
perimeter is above 7. Numerical tables are reproduced separately with
`python3 examples/reproduce_normality.py`. Two reusable calculus lemmas are
packaged in the [normality review guide](docs/NORMALITY_UPSTREAM.md).

## Wallis library

The Wallis paper is *Advances in Pure Mathematics* **3** (2013), 579–585,
DOI [10.4236/apm.2013.36074](https://doi.org/10.4236/apm.2013.36074).
Its modules use namespace `FitzhughFarnsworth.Wallis`:

| Module | Verified contents |
| --- | --- |
| `Wallis/Construction.lean` | Equations (13)–(20), positive dimensions, attachment areas, strict growth, unique dimension sequences, and the finite product underlying (21) |
| `Wallis/GammaProducts.lean` | Two-factor Gamma products; balance, convergence to zero, and divergence to positive infinity |
| `Wallis/FiniteProducts.lean` | Full finite-factor identity (8)–(9), with positive shifts and equal sums |
| `Wallis/Convergence.lean` | Equation (23), the Gamma limit for arbitrary positive starting sides with equal positive attachment areas |
| `Wallis/Asymptotics.lean` | Equation (22) and the complete two-dimensional ratio-limit classification |
| `Wallis/BoxConstruction.lean` | Equations (24)–(34), including all intermediate attachment volumes |
| `Wallis/BoxConvergence.lean` | Equation (36), Gamma limit (37), and the two unbalanced width-to-depth cases |
| `Wallis/PCircle.lean` | Measured disk and upper-half areas (11)–(12) for `p ≥ 1`; product limits and a divergence proof for the misprinted (39) |
| `Wallis/AreaIntegrals.lean` | Real beta integral (10), the substitution in (11), and the quarter-disk integral for every `p > 0` |
| `Wallis/Area.lean` | Fubini's area formula, both Gamma expressions in (11), and the actual upper-half area (12) for all `p > 0`, including nonconvex disks |
| `Wallis/BoxSpecializations.lean` | (38), corrected (39), and (40), for the general parameter conditions and explicit constructions throughout both ranges of `p` |
| `Wallis/Hypercube.lean` | Section 5.3: every intermediate unit-volume attachment, all side-ratio limits, and (41) |
| `Wallis/MomentIntegrals.lean` | Integrability and beta/Gamma evaluation for every `p > 0` and real moment order `r > -1` |
| `Wallis/Moments.lean` | Actual measured quarter-disk moments, Fubini, positivity, the higher-order recurrence, and recovery from orders modulo `N` |
| `Wallis/ShiftedHypercube.lean` | Arbitrary positive starting volume, every intermediate attachment, strict coordinate ordering, Gamma limits, and exact recovery of the unit construction |
| `Wallis/MomentRatios.lean` | All ordered side ratios as moment quotients, all integer moments as rescaled side-ratio limits, and shifted real orders |
| `Wallis/Classical.lean` | The unit-square recurrence equals mathlib's finite Wallis product, with bounds and limit π/2, equations (1)–(2) |

`Parameters` requires `a, b, A, B > 0`. `dimensions n` is the rectangle after
`2*n` attachments: first area `A` to the right, then area `B` above.
`Parameters.ratio_tendsto_gammaLimit` proves the equal-area limit for these actual
dimensions. The ratio tends to zero for `A < B` and to positive infinity for
`A > B`; `exists_ratio_limit_iff` distinguishes finite limits from positive ones.

`BoxParameters` similarly requires six positive inputs and performs three
attachments per iteration. Its width-to-depth ratio has a positive finite limit
exactly when `A = C`. The specialization theorems retain the paper's general
parameter conditions and separately supply unit initial cubes for every
`p > 2` and `1 < p < 2`.

`Hypercube.partialDimensions N n j : Fin N → ℝ` describes the intermediate box
after `N*n + j` attachments. `attachment_volume` proves that each added box has
volume one. `ratio_tendsto` covers all coordinate pairs, and
`first_last_ratio_tendsto` gives (41) for every `N ≥ 2`.

`pCircleProduct_tendsto_area_of_pos` connects the products to the actual Lebesgue
measure of the upper p-disk for every `p > 0`. `diskArea_eq_integral`,
`diskArea_eq_beta_integral`, and `diskArea_eq_gamma_add_one` prove the displayed
area calculation in (11). `unitDisk_not_convex` proves the loss of convexity for
`0 < p < 1`; the area proof does not assume convexity. The
[roadmap](docs/ROADMAP.md#wallis-paper-2013) explains the source discrepancies
and the precise verified scope.

For the moment extension, `quarterMoment p r` is a Lebesgue integral over the
actual first-quadrant planar p-disk. `weightedMoment p r` is `(r+2)` times that
moment. `Hypercube.ratio_tendsto_moments` covers every ordered pair;
`normalized_side_tendsto` identifies each side normalized by the shortest one
with its weighted moment. `scaled_ratio_tendsto_quarterMoment` recovers every
nonnegative integer order from the original finite set of sides.
`ShiftedHypercube.ratio_tendsto_moments` proves that changing the initial volume
to `v > 0` changes the represented orders to `v+i-1`, including fractional
orders. All of these statements retain the actual attachment construction.

## Midset library

The original six modules remain the foundation, with supporting proofs in submodules:

| Module | Contents |
| --- | --- |
| `MetricGeometry.lean` | Taxicab plane using mathlib's `WithLp 1 (ℝ × ℝ)` |
| `Midsets.lean` | Paper compatibility names for the generic midset API |
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

The `Dynamics/` modules connect these foundations into the general functions:

| Module | Contents |
| --- | --- |
| `Dynamics/Basic.lean` | Valid geometric pairs, actual midset steps, distance profiles and cycles |
| `Dynamics/Iteration.lean` | General `next`, `iterate`, `evolution`, and affine input construction |
| `Dynamics/Sequence.lean` | Prefix and translation transport, including parity changes |
| `Dynamics/Canonical.lean` | Connects existing slope iteration to geometric evolutions |
| `Dynamics/Global.lean` | Composes general reduction and canonical convergence |
| `Dynamics/Uniqueness.lean` | Component and evolution uniqueness up to ordering |
| `Dynamics/Rotation.lean` | 45° rotation for every geometric orthogonal two-cycle |
| `Dynamics/Reduction.lean` | The finite reduction bound for every actual evolution |
| `Dynamics/Correctness.lean` | End-to-end correctness and agreement with the existing functions |

`FitzhughFarnsworth.lean` imports the complete library.

The reusable files under `FitzhughFarnsworth/Mathlib/` depend only on mathlib.
They provide union distance and midsets in pseudometric spaces, a real beta
integral, balanced Gamma-product limits, the measure of regions with closed
vertical sections, derivative gluing, and a criterion for convex minima. The paper modules use these generic results through their
existing compatibility theorems. See [upstream preparation](docs/UPSTREAM.md)
for the seven candidate patches.

## Midset correctness entry points

In namespace `FitzhughFarnsworth.Dynamics`:

- `intersecting_affine_lines_end_to_end` starts from two affine equations and
  their common point and proves correctness of the defined evolution.
- `evolution_end_to_end` includes exact initial state, valid midset steps, a
  two-step reduction bound, a distinct orthogonal cycle, its 45° rotation relation,
  and actual distance limits.
- `every_evolution_converges` covers every valid iteration, so convergence does
  not depend on the particular component selection used by `next`.
- `evolution_even_agrees_with_slopes` and `evolution_odd_agrees_with_slopes` connect
  the general function back to the original `evenIterate` and `oddIterate`.

See [the function specification and proof chain](docs/FUNCTIONS.md).

## Correspondence with the midset paper

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
| Table 1 and numerical examples | Separate numerical illustrations; not part of the mathematical correctness target |

Most iteration theorems are in namespace `FitzhughFarnsworth.SlopePair`.
The [proof roadmap](docs/ROADMAP.md) records the remaining scope and useful entry points.

## Midset mathematical scope

`Point` abbreviates mathlib's `WithLp 1 (ℝ × ℝ)` and inherits its metric,
normed group, and real normed-space structures. Its distance is
`|x₁-x₂| + |y₁-y₂|`; `Point.mk x y` constructs a point and `.x`/`.y` access its
coordinates. Line distances are proved from the infimum of point
distances with explicit nearest points. Vertical lines and boundary slopes are
included. Translation, coordinate swap and reflection are proved taxicab
isometries. Euclidean rotation is used only for the paper's Euclidean claims.

`evenIterate s n` denotes paper index `2*n`; `oddIterate s n` denotes `2*n+1`.
The canonical theorems prove convergence of both slope subsequences. The general
end-to-end theorem connects those results to pointwise convergence of distance
to the iterated line unions: at each fixed point, the even and odd distances
approach the distances to the corresponding limiting pair. The two component
lines remain separate inputs to each midset operation. This is a mathematical
iteration using classical choice, not an executable numerical implementation;
component uniqueness proves its geometric result is independent of that choice.
No global Hausdorff convergence claim for unbounded line sets is made.

## Verification

Only Lean's usual `propext`, `Classical.choice`, and `Quot.sound` axioms are
allowed by the audit. It explicitly loads every project module's private
declarations and tracks module ownership, including generic namespaces. Its
regression checks reject public axioms, unused private axioms, and unused
private unfinished proofs. There are no unfinished proofs or project-specific
mathematical axioms in the library.

## License and contribution status

The code is released under [Apache 2.0](LICENSE). It was developed with OpenAI
Codex, including generated proof scripts and refactoring. Kernel verification
and local linting are complete technical checks, not an upstream review or an
acceptance decision. Any upstream submission requires a human contributor to
understand the proofs and disclose the AI assistance under
[mathlib's contribution policy](https://leanprover-community.github.io/contribute/index.html).

## Numerical reproduction

This uses only Python's standard library:

```sh
python3 examples/reproduce_paper.py --precision 80
```

It is an independent numerical illustration, not a substitute for a Lean proof.
The formal `limit_enclosure` theorem provides a foundation for future certified
rounding: each limiting shallow slope lies between `a_n` and `-1/b_n`, and the
interval width tends to zero.
