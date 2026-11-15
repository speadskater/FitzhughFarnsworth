# Proof roadmap

Source: Fitzhugh and Farnsworth (2014), DOI
[10.1155/2014/832647](https://doi.org/10.1155/2014/832647).
The [publisher PDF](https://onlinelibrary.wiley.com/doi/pdf/10.1155/2014/832647)
is the reference for equations (1)–(18).

## Completed: geometric foundations and reduction

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

## Completed: iteration, symmetry and convergence

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

The analytic theorem is about the canonical slope iteration. The general affine
reduction is separately formalized; there is no combined theorem for a newly
defined generic affine-line sequence or a topology of unbounded line sets.

## Completed: Section 4 constructions

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

## Completed: rigorous error-bound infrastructure

For any finite even iterate, `limit_enclosure` places the limiting shallow slope
between `a_n` and `-1/b_n`. `limit_error_le_enclosure_width` bounds the approximation
error by their separation; `tendsto_enclosure_width_zero` proves that separation
vanishes. These are exact Lean theorems about real values.

## Remaining: certified numerical statements

1. Supply certified intervals for the initial trigonometric slopes in Table 1.
2. Propagate arithmetic intervals through the iteration and combine them with
   `limit_enclosure` and certified arctangent bounds to prove decimal roundings.
3. Resolve the apparent discrepancies recorded in [NUMERICAL_NOTES.md](NUMERICAL_NOTES.md).
   Do not force a formal proof of the printed decimals if the exact values differ.
4. Certify the original Section 4 numerical example, explicitly distinguishing
   exact initial angles from the rounded slopes used in the paper's arithmetic.

Background literature comparisons and general Minkowski-space results cited in
the introduction are not claimed as formalized here. The polygonal area formula
is defined by a determinant; it is not yet connected to mathlib's measure-theoretic
area API. Neither extension is needed by the numbered midset theorems.

## Working rules

- Every milestone must pass `lake build` and `lake env lean scripts/Audit.lean`.
- Preserve hypotheses, nonzero denominators, and the geometric interpretation.
- No `sorry`, `admit`, custom mathematical axioms, or `native_decide`.
- Keep numerical experiments separate from formal decimal certificates.
- Update the README and this roadmap when the verified scope changes.
