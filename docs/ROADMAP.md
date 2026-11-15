# Proof roadmap

Source: Fitzhugh and Farnsworth (2014), DOI
[10.1155/2014/832647](https://doi.org/10.1155/2014/832647).
The [publisher PDF](https://onlinelibrary.wiley.com/doi/pdf/10.1155/2014/832647)
is the reference for equations (1)–(18); the HTML text extraction omits some formulas.

## Stage 1 — Verified geometric foundation

Completed:

- A taxicab `MetricSpace Point`, with metric axioms checked by Lean.
- Generic midsets using `Metric.infDist`, including symmetry and closedness.
- Distances to the vertical axis and every finite-slope line, including ±1.
- Theorem 3 (`midset_axes`, `midset_diagonals`).
- The geometric identity `midset_shallow_steep` behind the slope update.
- Canonical Configuration 1 transitions (`toOdd_config`, `toEven_config`).
- Algorithm 6 parity subsequences, their region invariants, and their equality
  with geometric midsets (`evenIterate_midset`, `oddIterate_midset`).
- A definition of convergence of both parity subsequences and the elementary
  fact that an exact two-step fixed point gives a constant pair of subsequences.

## Stage 2 — Full configuration geometry

1. Represent arbitrary nondegenerate lines and unordered pairs of distinct,
   intersecting lines, retaining vertical lines.
2. Prove translation, coordinate-swap, and sign-change isometries preserve
   distance to a set and midsets. Do not use arbitrary Euclidean rotations as
   taxicab isometries.
3. Give an exhaustive classification corresponding to configurations 1–10.
4. Lift the canonical Theorem 1 through the allowed symmetries.
5. Prove Theorem 2: the two-step map fixes a Configuration 1 pair exactly when
   its direction vectors are Euclidean orthogonal. Separately establish the
   claimed 45° rotation of the unordered line pair.
6. Prove Theorems 4–5, including boundary slopes and exceptional Configuration 2
   cases. For example, opposite shallow slopes have zero average, producing the
   axes before the diagonals; they must not be classified as open octants.

The scope is distinct intersecting lines. Parallel or coincident lines do not
belong to the paper's ten configurations and need separate statements.

## Stage 3 — Algebra and symmetry

1. Derive the closed two-step formulas (13)–(14) from `twoStep`, proving every
   denominator nonzero from the configuration assumptions.
2. Establish reciprocal symmetry `(a, b) ↦ (-1/b, -1/a)` and prove it commutes
   with the two-step map (Theorem 8). Connect the slope formulation to the
   paper's Euclidean angle hypotheses.
3. Prove the strict monotonicity and product inequalities on each side of
   `a*b = -1`, treating the equality case separately.

## Stage 4 — Convergence

1. Prove bounds sufficient for convergence of **both** even slope sequences.
   A bounded increasing `a` sequence alone is not a proof that the decreasing
   `b` sequence has a finite limit.
2. Keep limits away from singular denominators, using bounds inherited from
   the initial pair. Open octant bounds for each finite iterate alone do not
   imply that the limit remains in an open octant.
3. Prove continuity of the appropriate rational maps at those limits, pass
   the recurrence to the limit, and identify the orthogonal two-cycle
   (Theorem 7).
4. Complete Theorem 9, including equality of limits for reciprocal initial
   data, and translate slope monotonicity into the stated angle monotonicity.

These are explicit proof obligations, not a claim that the paper's conclusions
are false. The formalization must supply details abbreviated in its prose.

## Stage 5 — Angles and numerical illustrations

Define the four Section 4 bisector conventions with explicit ray and angle
choices. Establish the claimed relationships for taxicab arc length and area.
Reproduce Table 1 and the example comparisons, keeping floating-point
experiments separate from formal proofs. Any claim that a decimal is correctly
rounded requires a certified error bound; finite iteration alone is insufficient.

## Working rules

- Every milestone must pass `lake build` and `lake env lean scripts/Audit.lean`.
- Do not weaken hypotheses, replace geometric midsets with unconnected slope
  recurrences, or insert mathematical axioms to make a theorem compile.
- Keep pending claims here, without `sorry`, `admit`, or `native_decide` in the
  trusted proof library.
- Record whether a result covers the canonical orientation or every line pair.
- Update the README status table when a stage changes.
