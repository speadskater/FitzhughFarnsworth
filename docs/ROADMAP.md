# Proof roadmap

This repository covers three Fitzhugh–Farnsworth papers. Completion of one paper
does not imply completion of the others.

| Paper | Verification status | Work order |
| --- | --- | --- |
| Midset iteration (2014) | Complete at the stated intersecting-line scope | Existing foundation |
| Wallis-type formulas (2013) | Complete for positive input parameters and all `p > 0` area formulas, with documented source corrections | Completed |
| Normality iteration (2013) | Main numbered results complete for finite `p > 1`, with explicit regularity hypotheses for quadrant uniqueness | Completed |

## Wallis paper (2013)

Source: [A Construction That Produces Wallis-Type Formulas](https://repository.rit.edu/article/2109/),
*Advances in Pure Mathematics* **3** (2013), 579–585, DOI
[10.4236/apm.2013.36074](https://doi.org/10.4236/apm.2013.36074).
The [publisher PDF](https://www.scirp.org/journal/PaperDownload.aspx?paperID=36380)
is the reference for equations (1)–(41). The paper uses numbered equations,
rather than the numbered theorems of the midset paper.

### Completed: rectangle construction and full ratio-limit classification

All entry points below are in `FitzhughFarnsworth.Wallis`, with the general
construction theorems in its `Parameters` namespace.

| Paper component | Verified result / entry point |
| --- | --- |
| (13) | `width_zero`, `height_zero` |
| (14)–(15) | `right_attachment_area`, `top_attachment_area` |
| (16)–(17) | `area_even`, `area_odd` |
| (18)–(19) | `width_succ_mul`, `height_succ_mul`, derived from the area identities |
| (20) | `ratio_succ` |
| Finite product preceding (21) | `ratio_eq_prod`, with indices `0, …, n-1` |
| (22) | `balance_iff`: the printed balance equation is equivalent to `A = B` |
| (23) | `ratio_tendsto_gammaLimit`, for all positive `a, b, A, B` with `A = B` |
| Unequal-area cases from Section 2 | `ratio_tendsto_zero` for `A < B`; `ratio_tendsto_atTop` for `A > B` |
| (1)–(2), unit-square specialization | `unitSquare_ratio_eq_wallis`, `unitSquare_ratio_tendsto` |

`Parameters` explicitly requires positive initial sides and positive attachment
areas. `dimensions n` performs `n` pairs of attachments; `width_pos`, `height_pos`,
and the area positivity lemmas ensure that every division is geometrically
valid. Both side sequences are strictly increasing. `dimensions_unique` proves
that the initial dimensions and the two attachment-area equations determine
these same sequences. Area here is the product of the rectangle's side lengths.

The Gamma argument is `a*b/(2*A)`. Equation (23) is proved for the actual
dimension ratio, not just for a separately defined product; its limit is strictly
positive. The proof uses mathlib's Euler limit for `Real.Gamma`. The unit-square
case also independently connects the recurrence to mathlib's existing Wallis
product and inherits its finite upper and lower bounds.
`unitSquare_ratio_eq_pCircleProduct` connects this construction to `p = 2`,
and `diskArea_two` proves that the measured Euclidean disk area is `π`.

`ratio_tendsto_pos_iff` characterizes positive finite limits by `A = B` and
identifies their value. `exists_ratio_limit_iff` proves that a finite limit
exists exactly when `A ≤ B`, including the zero limit. The unbalanced proofs
factor the finite products into a Gamma approximation and a power of the index.

### Completed: Gamma products

`tendsto_balanced_finset_prod` proves (8)–(9) for any finite index set, with the
same number of numerator and denominator factors and equal sums of shifts.
The zero-based shifts are strictly positive, equivalent to requiring the
paper's one-based shifts to exceed `-1`. Empty products are included.
`tendsto_balanced_prod` is the two-factor API used by the geometric constructions;
`tendsto_linear_prod_zero` and `tendsto_linear_prod_atTop` classify its unbalanced
cases. All these statements follow from mathlib's Euler limit for Gamma.

### Completed: three-dimensional construction and specializations

General three-dimensional results use namespace `Wallis.BoxParameters`.

| Paper component | Verified result / entry point |
| --- | --- |
| (24) | `width_zero`, `height_zero`, `depth_zero` |
| (25)–(27) | `right_attachment_volume`, `top_attachment_volume`, `depth_attachment_volume` |
| (28)–(30) | `volume_cycle`, `volume_after_right`, `volume_after_top` |
| (31)–(33) | `width_succ_mul`, `height_succ_mul`, `depth_succ_mul` |
| (34) and the finite product in (35) | `ratio_succ`, `ratio_eq_prod`, `ratio_eq_linear_prod` |
| (36) | `balance_iff`: equivalent to `A = C` |
| (37) | `ratio_tendsto_gammaLimit`, with `gammaLimit_eq_paper` giving the printed expression |
| Unbalanced width-to-depth limits | `ratio_tendsto_zero` for `A < C`; `ratio_tendsto_atTop` for `A > C` |
| (38) | `Wallis.unitCube_ratio_tendsto` |
| Corrected (39) | `ratio_eq_pCircleProduct_of_right_volume`, `ratio_tendsto_area_of_right_volume` |
| (40) | `ratio_eq_pCircleProduct_of_right_top_volume`, `ratio_tendsto_area_of_right_top_volume` |

The general specialization theorems keep `a = c`, `A = C`, and either `A = abc`
or `A+B = abc` explicit. The respective inequalities `p > 2` and `1 < p < 2`
are proved from positive input parameters. Separately, `Wallis.boxAboveTwo` and
`Wallis.boxBelowTwo` provide concrete positive-parameter constructions for every
exponent in those ranges. These are examples of the general theorems, not
replacements for their hypotheses.

### Completed: measured areas and N-dimensional construction

`Wallis.unitDisk` is the subset of `Fin 2 → ℝ` defined by
`|x₀|^p + |x₁|^p ≤ 1`. `diskArea` and `upperHalfArea` use Lebesgue measure.
`volume_unitDisk_of_pos`, `diskArea_eq_gamma_of_pos`, and
`upperHalfArea_eq_gamma_of_pos` prove the area conclusions of (11)–(12) for every
`p > 0`. They use vertical slices and Fubini, without assuming convexity.
`pCircleProduct_tendsto_area_of_pos` identifies the infinite product with the
measured upper-half area throughout this range. The original `p ≥ 1` proofs,
which reuse mathlib's ℓₚ-ball volume theorem and negation invariance, remain as
independent checks of the convex case.

`Wallis.Hypercube` formalizes Section 5.3 with `Fin N` coordinate states.
`partial_zero` and `partial_full` connect each cycle's endpoints; `partial_pos`
keeps every side positive. `volume_partial` proves volume `1 + N*n + j`, and
`attachment_volume` proves that every individual update adds volume one.
`partial_step_other` keeps the other coordinates unchanged.

`ratio_tendsto` proves the general Gamma limit for every ordered coordinate pair.
`first_last_ratio_eq_product` connects the first-to-last ratio to the same
p-circle products, and `first_last_ratio_tendsto` proves (41) for every `N ≥ 2`,
with the actual measured upper N-circle area as its limit.

### Source discrepancies and interpretation

- The last fractions printed in (18) and (19), on page 582, contain extra
  factors of `n` multiplying the constant terms of the numerators. The preceding
  lines and the attachment equations give numerators
  `(A+B)*n + ab + A` and `(A+B)*n + ab + A + B`, respectively. The formalization
  derives these formulas from (14)–(17); the printed final fractions already
  fail at `n = 0` for positive inputs.
- The balance conditions near (22) and (36) concern a finite, nonzero Gamma
  product limit. They must not be interpreted as excluding convergence to zero
  when the numerator growth is smaller. Both unbalanced cases are now proved.
- Equation (39), page 584, prints `pn + p + 2` as its first numerator. The
  construction with `A = C = abc` gives `pn - p + 2`, matching (40).
  `printed_product39_tendsto_atTop` proves that the product as printed diverges
  to positive infinity for every `p > 0`. For the unit cube (`p = 3`), the
  first ratio is `3/2` (`unitCube_ratio_one`), whereas the printed product starts
  at `6`. The verified (39) results explicitly use the corrected sign.

### Completed: full area integral and nonconvex range

`Wallis.AreaIntegrals` derives the real beta integral from mathlib's complex
beta/Gamma identity. The monotone substitution theorem handles derivatives only
on the open interval, so singular endpoint derivatives introduce no extra
restriction on `p`.

| Paper component | Verified result / entry point |
| --- | --- |
| (10), positive real parameters | `integral_beta` |
| (11), geometric area integral | `volume_unitDisk_eq_integral`, `diskArea_eq_integral` |
| (11), substitution `t = x^p` | `pCircle_integral_substitution`, `diskArea_eq_beta_integral` |
| (11), first Gamma quotient | `diskArea_eq_gamma_add_one` |
| (11), second Gamma quotient | `diskArea_eq_gamma_of_pos`, using `gammaHalfArea` |
| (12), measured upper-half area | `volume_upperHalfDisk_eq_integral`, `upperHalfArea_eq_gamma_of_pos` |
| Nonconvexity for `0 < p < 1` | `unitDisk_not_convex` |

The full integral calculation and measured area conclusions hold for every
`p > 0`, including `0 < p < 1`. The geometric construction specializations
retain their separate positive-input hypotheses and `p > 1` ranges.

### Wallis completion scope

The construction, convergence, finite-factor Gamma identities, and area claims
are verified at the positive-parameter scope used in the paper. Equations
(18), (19), and (39) use the explicitly documented corrections; the false
printed product in (39) is refuted rather than assumed. Standard Gamma facts
from the cited background are reused from pinned mathlib. No Wallis proof
obligations remain within this scope.

### Completed: Wallis upstream packaging

Three independent candidate patches extract the real beta integral, the balanced
finite-factor Gamma limit, and the measure of a region with closed vertical
sections. The area lemma supports an arbitrary sigma-finite base measure,
integrable functions on a measurable set, and almost-everywhere ordering.
The existing Wallis statements now reuse these generic lemmas; their hypotheses,
paper correspondence, and mathematical scope are unchanged.

Each patch and their combination passed isolated builds, axiom audits including
private declarations, 15 environment linters, and focused source-style checks
at the pinned mathlib baseline. Negative controls verify that the candidate
audit rejects an unused private axiom and missing private-declaration imports.
The [review guide](WALLIS_UPSTREAM.md) links the patches, reproducible tooling,
and recorded results. Human review of naming, generality, and suitability is
still required; upstream submission and acceptance have not occurred.

## Normality paper (2013)

Source: [The Behavior of Normality when Iteratively Finding the Normal to a Line
in an ℓₚ Geometry](https://repository.rit.edu/article/2108/),
*Advances in Pure Mathematics* **3** (2013), 647–652, DOI
[10.4236/apm.2013.38086](https://doi.org/10.4236/apm.2013.38086).
The [publisher PDF](https://content.scirp.org/pdf/apm_2013112711512066.pdf) is the
reference for Lemmas 3.1–3.3, Theorems 3.4–3.5 and 4.1, and equations (1)–(14).

### Completed: geometric normality and iteration

Entry points use namespace `FitzhughFarnsworth.Normality`. `Parameters` carries
`p > 1`, and `exponent` is `1/(p-1)`. `Parameters.Plane` is mathlib's
`WithLp (ENNReal.ofReal p) (ℝ × ℝ)` with its standard norm and metric.

`Parameters.IsNormal v w` says that the origin minimizes distance from `v`
to the line spanned by `w`. Convexity and differentiation of
`|x|^p + |y|^p` prove its equivalence to the supporting-tangent equation.
The derivative exists even when a coordinate is zero. This yields the slope
formula and uniqueness; normality is never an assumption attached to the
recurrence. Homogeneity extends the conclusion to every point of the normal
line, and the infimum-distance theorem proves that the minimum is attained.

| Paper component | Verified result / entry point |
| --- | --- |
| Section 2, distance and tangency definitions | `Parameters.isNormal_iff`, `energy_min_iff`, `IsNormal.infDist` |
| Lemma 3.1, (3)–(4) | `Parameters.isNormal_finite_iff`, `Direction.isNormal_iff_eq_next`, `normalSlope_positive_formula`, `normalSlope_negative_formula` |
| Explicit unit-circle contact and tangent | `Parameters.contact`, `norm_contact`, `energy_contact`, `contact_tangent` |
| Lemma 3.2, (5)–(9) | `normalSlope_twoStep_of_pos/neg`, `slopeIterate_even_formula`, `slopeIterate_odd_formula` |
| Lemma 3.3, (10)–(11) | `Parameters.slopeIterate_reciprocal` |
| Geometric symmetry reductions | `swapIsometry`, `reflectIsometry`, `isNormal_swap_iff`, `isNormal_reflect_iff`, together with the scalar reflection/reciprocal identities |
| Actual geometric evolution | `Direction.iterate_isNormal`, `next_infDist`, `evolution_eq_iterate` |
| Axis and diagonal cycles | `Direction.axes_cycle`, `diagonals_cycle`, `iterate_of_cycle` |
| Euclidean case `p = 2` | `euclidean_next_involutive` |

`Direction.vertical` is separate from finite slopes. The auxiliary scalar value
`normalSlope 0` is never used as the horizontal line's update.
`slopeIterate_ne_zero` preserves all finite-slope denominator hypotheses.
No arbitrary rotations are used as isometries.

### Completed: Theorems 3.4 and 3.5

The scalar theorems cover both `0 < m < 1` and `m > 1`, with strict
monotonicity of each parity subsequence. Reflection supplies the negative
initial-slope results; reciprocal symmetry explains the two positive ranges.

| Parameter and initial slope | Even subsequence | Odd subsequence |
| --- | --- | --- |
| `p > 2`, `0 < m < 1` | Strictly increases to `1`, staying in `(0,1)` | Strictly increases to `-1`, staying below `-1` |
| `p > 2`, `m > 1` | Strictly decreases to `1`, staying above `1` | Strictly decreases to `-1`, staying in `(-1,0)` |
| `1 < p < 2`, `0 < m < 1` | Strictly decreases to `0` | Strictly decreases to negative infinity |
| `1 < p < 2`, `m > 1` | Strictly increases to positive infinity | Strictly increases to `0` from below |

`Parameters.even_tendsto_one`, `odd_tendsto_neg_one`, `even_tendsto_zero`,
`odd_tendsto_atBot`, `even_tendsto_atTop`, and `odd_tendsto_zero` give the limits.
The `strictMono_*` and `strictAnti_*` theorems give strict monotonicity, while
`even_mem_Ioo`, `odd_lt_neg_one`, `one_lt_even`, and `odd_mem_Ioo` retain the
strict bounds throughout the iteration.

The geometric statements use mathlib's real projective line with its quotient
topology, identifying nonzero scalar multiples of spanning vectors.
`Direction.iterate_tendsto_diagonals`, `iterate_tendsto_axes_of_lt_one`, and
`iterate_tendsto_axes_of_one_lt` prove convergence to the actual limiting lines.
Their negative-slope counterparts are also explicit. `projective_tendsto_vertical`
uses the reciprocal chart, so both positive and negative infinite slopes have
the same vertical limit. Global Hausdorff convergence of unbounded lines is
not asserted. Exact axis and diagonal cycles and the Euclidean involution
cover the boundary cases excluded from the strict convergence statements.

### Completed: Theorem 4.1 and the joined geometry

`Parameters.conjugate` has exponent `q = p/(p-1)` and proves
`1/p + 1/q = 1`. Applying conjugation twice returns the original parameter.

`Radon.joinedNorm` is constructed as the maximum of four convex functions,
each the p- or q-norm of the positive coordinate parts in a specified quadrant.
The proof establishes convexity globally and then derives the piecewise formula.
Positive definiteness, absolute homogeneity, and the triangle inequality produce
`Radon.Plane g`, a separate Lean normed space. Its closed unit ball is the
centrally symmetric joined disk, and `joinedNorm_eq_one_iff` identifies its
unit circle with the p- and q-arcs in alternating quadrants.

| Theorem 4.1 component | Verified result / entry point |
| --- | --- |
| Conjugate exponents | `Parameters.conjugate_identity`, `conjugate_conjugate` |
| Constructed norm and unit disk | `Radon.convexOn_joinedNorm`, `joinedNorm_smul`, `joinedNorm_add_le`, `normCore`, `mem_closedBall_iff`, `mem_disk_iff` |
| Exact unit-circle equation | `Radon.joinedNorm_eq_one_iff`, `upperArc_on_circle`, `rightArc_on_circle` |
| Axis joins | `hasDerivAt_joined_horizontal`, `hasDerivAt_joined_vertical`, `hasDerivAt_upperArc_zero`, plus central symmetry and coordinate swap |
| Unique actual normal direction | `Radon.isNormal_iff_eq_radonNext`, `radonNext_infDist` |
| Reflexivity for all lines/vectors | `Radon.normality_reflexive`, `normality_reflexive_vectors` |
| (12)–(14), differential equation | `Parameters.reflexive_tangent_iff`, `hasDerivAt_conjugate_energy_zero` |
| Uniqueness of the second-quadrant arc | `Parameters.quadrant_unique`, `Radon.quadrant_unique_graph` |

The uniqueness theorem assumes a graph `f` continuous on `[-1,0]`, positive
on `(-1,0)`, with `f 0 = 1`, a positive derivative at every interior point,
and `Parameters.IsNormal (1, f' x) (x, f x)` there. Together with the actual
derivative hypothesis, this last condition is precisely the paper's requirement
that the two tangent/radial directions agree under reflexivity with the given
first-quadrant p-arc. It does not assume the unknown arc's formula. The proof
derives the differential equation, proves that `(-x)^q + f(x)^q` is constant,
uses the endpoint to fix that constant to one, and identifies the graph with
the explicit q-circle arc. Central symmetry determines the fourth quadrant.

Join results assert matching first derivatives and differentiable local graph
charts. They do not assert arbitrary higher smoothness for real exponents.

### Normality completion scope

Lemma 3.1–3.3 and Theorems 3.4–3.5 and 4.1 are verified for finite `p > 1`,
with the regular-graph assumptions above for Theorem 4.1's uniqueness direction.
The convergence proofs include every starting direction and all parameter
boundary cases within that range. No proof obligations remain in this scope.

Completion validation passed: `lake build` (6,010 jobs), the axiom audit
(1,510 project declarations, including 25 outside the project namespace),
all 15 declaration linters, source-style linting, and the audit's rejection
controls. The Wallis package freshness check also passed. Checks ran sequentially
with one Lean thread, a 6 GiB memory limit, and no swap allowance.

Tables 1–2, application examples, and the concluding circumference comparison
are outside this main-results target. In particular, Schäffer's cited perimeter
theorem and a formal arc-length comparison for the joined curve are not proved
here. The library does not claim the general classification of all Radon curves,
or handle the excluded nonsmooth `p = 1` and infinite-exponent geometries.
Normality mathlib extraction and upstream human review remain separate work.

## Midset paper (2014)

Source: Fitzhugh and Farnsworth (2014), DOI
[10.1155/2014/832647](https://doi.org/10.1155/2014/832647).
The [publisher PDF](https://onlinelibrary.wiley.com/doi/pdf/10.1155/2014/832647)
is the reference for equations (1)–(18).

### Completed: geometric foundations and reduction

- Taxicab metric, metric-infimum midsets, and distances to all finite-slope lines
  plus the vertical axis. The diagonal boundary slopes are included.
- Theorem 1 for both Configuration 1 orientations and either input ordering,
  with actual midset equalities and return to the original octants.
- Theorem 2 as equality of geometric line unions, with an equivalence to actual
  Euclidean inner-product orthogonality and an exact π/4 rotation. The statements
  also transport to arbitrary intersection points.
- Theorem 3's axes/diagonals cycle.
- Theorem 4 for every axis/diagonal choice, with Configuration 1 specifically
  reached after exactly two midset steps.
- Exhaustive Theorem 5 reduction. `ReducesIn` and `ReducesInAt` retain the actual
  midset equality and distinct line components at every step. For any distinct,
  nondegenerate intersecting affine lines, **two** steps suffice, improving the
  paper's three-step bound.
- Configuration 1/2 is stable under the next midset step.

This covers parallel-to-axis lines and all boundaries without encoding a separate
numerical label for each of the ten configurations. Parallel or coincident input
lines are outside the paper's scope.

### Completed: iteration, symmetry and convergence

- Algorithm 6 and its exact connection to geometric midsets at every iterate.
- Equations (13)–(14), nonzero denominators, and fixed points for both parity maps.
- Theorem 8's reciprocal symmetry for every iterate, together with the paper's
  equivalent Euclidean angle hypotheses.
- Theorem 9's strict slope/product inequalities on both sides of `a*b = -1`.
- Uniform bounds for both slope sequences that keep their limits in the open
  canonical region. Convergence is not inferred just from boundedness of `a`.
- Existence and uniqueness of both parity limits; passing the rational maps
  to the limit with their denominator hypotheses proved.
- Theorems 7 and 9: both limiting pairs are orthogonal, are distinct as geometric
  sets, form a genuine two-cycle, and differ by a Euclidean π/4 rotation.
- Reciprocal initial pairs have the same limiting cycle.
- The Euclidean angle between the even pair's upper rays converges monotonically
  to π/2, with strict monotonicity off the orthogonality locus.

### Completed: end-to-end correctness of the actual functions

- `State v` represents two distinct genuine affine lines through `v`.
- `next` chooses the components of their actual metric midset; `next_spec` proves
  that equality, and `iterate`/`evolution` preserve validity at every step.
- General geometric reduction is composed with the existing slope algorithm into
  an infinite valid evolution, accounting for finite prefixes and parity changes.
- The components of a valid line union are unique up to swapping. Every valid
  evolution from the same geometric input therefore has the same union at every
  index, regardless of its choices of component labels.
- `every_evolution_converges` transfers the constructed convergence proof to all
  valid evolutions. `evolution_end_to_end` states correctness for the actual
  defined function, using distances to the geometric unions, and includes the
  distinct orthogonal two-cycle and its 45° rotation relation.
- The general function agrees with `evenIterate` and `oddIterate` on canonical
  inputs; implicit affine equations are handled by the coordinate-facing theorem.

The mathematical function is noncomputable, using classical choice of line
components. Convergence is pointwise distance-to-union convergence along even
and odd indices. Ordered components need not retain their labels, and global
Hausdorff convergence of unbounded lines is not asserted. See [FUNCTIONS.md](FUNCTIONS.md).

### Completed: Section 4 constructions

`AngleConventions.lean` defines Euclidean, taxicab arc, first-midset, and limiting
bisector slopes. The arc construction is connected to explicit unit-diamond
points and actual taxicab distances along its edges. Its two polygonal arc
lengths and determinant-defined sector areas are equal. The perimeter is 8 and
the taxicab sine divided by arc angle is ½ on the first edge away from the axis.
The limiting convention uses the proved existence/uniqueness and convergence API.

For the exact initial slopes `(1/4, -2)`, `exists_four_distinct_bisectors` proves
that all four conventions differ, in the order Euclidean < limiting < first-midset
< arc. The limiting object is supplied by the convergence theorem, and rational
enclosures separate it from the other slopes. The Euclidean bound follows from
a proved trigonometric quadratic. The paper's original decimal example is
reproduced numerically, not yet certified in Lean.

### Completed: rigorous error-bound infrastructure

For any finite even iterate, `limit_enclosure` places the limiting shallow slope
between `a_n` and `-1/b_n`. `limit_error_le_enclosure_width` bounds the approximation
error by their separation; `tendsto_enclosure_width_zero` proves that separation
vanishes. These are exact Lean theorems about real values.

### Scope and optional extensions

The midset target is the paper's mathematics and end-to-end correctness of the
functions. It is complete at the stated nondegenerate intersecting-line scope.
The table of decimal approximations is an illustration, not an outstanding
mathematical proof obligation. Optional exact-decimal certification work has
been parked separately following the project owner's scope correction.

The numerical reproduction and its apparent discrepancies remain documented in
[NUMERICAL_NOTES.md](NUMERICAL_NOTES.md). Background results from the cited
literature are not independently re-formalized. Sector area uses the explicit
polygonal determinant formula. An executable numerical implementation or a
measure-theoretic area bridge would be separate extensions, not prerequisites
for the proved midset results.

## Working rules

- Every milestone must pass `lake build` and `lake env lean scripts/Audit.lean`.
- Preserve hypotheses, nonzero denominators, and the geometric interpretation.
- No `sorry`, `admit`, custom mathematical axioms, or `native_decide`.
- Keep numerical experiments separate from formal decimal certificates.
- Update the README and this roadmap when the verified scope changes, keeping
  each paper's status and numbering separate.

## Mathlib preparation for the midset library

- The plane now uses the standard `WithLp 1 (ℝ × ℝ)` metric and normed-space
  instances. Coordinate swap, reflection, and translation reuse existing
  isometry constructions.
- General distance-to-union and midset lemmas are independent of the paper's
  types. Their assumptions explicitly cover nonempty sets and isometry
  surjectivity where required; empty-set behavior is documented and proved.
- Configuration sign and denominator lemmas replace repeated local arithmetic.
  Iteration has zero, successor, addition, and tail APIs. The combined
  correctness statement is assembled from named validity, reduction, geometric
  limit, and individual even/odd distance-limit theorems.
- The dependency pin tracks the mathlib master snapshot of 2026-11-15, with
  mathlib source linters, declaration/style checks, and a module-based axiom audit.
- [UPSTREAM.md](UPSTREAM.md) records two midset and three Wallis candidate patches
  and the remaining human review and suitability decisions. The full paper
  formalizations remain a downstream project.
