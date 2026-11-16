# Normality source checks and circumference correction

The numbered normality results remain valid at the scope in the
[roadmap](ROADMAP.md#normality-paper-2013). Further checking found three numerical
discrepancies in Table 1 and a false circumference assertion in the concluding
paragraph. The circumference assertion now has an exact Lean counterexample.

## Numerical tables

The entries below were checked against the
[publisher PDF, page 650](https://content.scirp.org/pdf/apm_2013112711512066.pdf#page=4).
Python's `Decimal` implementation evaluates the closed slope formula with
80 digits and 20 guard digits, using exact rational parameters and exponents.
Each reciprocal column is computed independently.

| Table 1 entry | Printed | Reproduced at the same precision |
| --- | ---: | ---: |
| `m₁`, initial slope `5` | −0.3120 | −0.3420 |
| `m₃`, initial slope `1/5` | −1.6111 | −1.6110 |
| `m₇`, initial slope `1/5` | −1.1000 | −1.0988 |

All Table 2 entries agree at their printed precision. These decimal comparisons
are numerical reproductions, not Lean certificates of rounded transcendental
values. The closed formulas and reciprocal identity are separately proved in Lean.

```sh
python3 examples/reproduce_normality.py --precision 80
python3 examples/reproduce_normality.py --precision 80 --json
```

The script uses only the Python standard library. It also calculates the
circumferences below using streamed quadrature at two resolutions, with a
change of variable to improve endpoint regularity. Its memory use does not
grow with the number of integration steps. Resolution differences are reported
as a numerical check, not as certified error bounds.

## The concluding circumference assertion

The [paragraph on page 652](https://content.scirp.org/pdf/apm_2013112711512066.pdf#page=6)
asserts that the joined Radon curve has the same self-circumference as the
original conjugate p- and q-circles. This conclusion does not follow from the
equality of the two original circles' self-circumferences.

Length depends on the norm applied to the tangent vector. Along a p-arc in
the first quadrant, that tangent has coordinates of opposite signs, so the
joined norm measures it with the q-norm. Along a q-arc in the second quadrant,
the tangent is measured with the p-norm. The constituent circle and the joined
circle therefore use different norms on the same p-arc.

For a regular octant chart, put

\[
r_p(t)=(1+t^p)^{-1/p},\qquad
\gamma_p(t)=(r_p(t),t r_p(t)),\qquad 0\le t\le1.
\]

Its velocity is

\[
\gamma'_p(t)=(1+t^p)^{-1/p-1}(-t^{p-1},1).
\]

Both its coordinates and its derivative remain finite at the endpoints. If
`q = p/(p-1)`, its speed in the q-norm simplifies to

\[
\|\gamma'_p(t)\|_q=(1+t^p)^{-2/p}.
\]

The corrected expression for the joined curve's self-circumference is

\[
C_{\rm joined}(p)=
4\int_0^1(1+t^p)^{-2/p}\,dt+
4\int_0^1(1+t^q)^{-2/q}\,dt.
\]

In contrast, the original p-circle has self-circumference

\[
C_p=8\int_0^1
(1+t^p)^{-1/p-1}\bigl(1+t^{p(p-1)}\bigr)^{1/p}\,dt.
\]

These formulas give the following illustrations, each using its own norm:

| `p` | `q` | Original p-circle | Original q-circle | Joined circle |
| ---: | ---: | ---: | ---: | ---: |
| 2 | 2 | 6.28318531 | 6.28318531 | 6.28318531 |
| 4 | 4/3 | 6.79386965 | 6.79386965 | 6.24978861 |
| 6 | 6/5 | 7.14536637 | 7.14536637 | 6.20762292 |

The equality between the two original dual circles is the cited Schäffer
result; it is not disproved by this correction. A later reference also explains
the area relation for normalized Radon curves: Ghandehari and Martini,
[On self-circumferences in Minkowski planes](https://dehesa.unex.es/bitstream/10662/9841/1/2605-5686_34_1_19.pdf),
*Extracta Mathematicae* 34 (2019), 19–28, Theorem 6. That general theorem and
the general Schäffer theorem are not assumed or independently formalized here.

## Exact Lean counterexample

The circumference calculation uses actual velocities and their specified
norms. `Circumference/PathLength.lean` connects these integrals to mathlib's
`Manifold.pathELength`, with the ambient norm on each tangent space.
The octant chart lies on the unit circle, covers the whole first octant, and
is injective. The other arcs are supplied by coordinate swap, central symmetry,
and the explicitly reflected conjugate arc.

For `p = 6`, the proof establishes the strict separation

\[
C_{\rm joined}(6)<7<C_6.
\]

The upper bound uses the exact comparison with
`(1+t²)^(-3/2)` and the fundamental theorem of calculus. The lower bound uses
the vertical coordinate of the actual velocity and
`2^(-1/6) > 7/8`. No floating-point calculation, numerical quadrature, custom
axiom, or assumed perimeter identity enters these proofs.

Entry points in `FitzhughFarnsworth.Normality.Circumference`:

- `hasDerivAt_octant`, `hasDerivAt_normed_octant`, `octant_on_circle`;
- `exists_octant_parameter`, `octant_injOn`;
- `conjugate_speed`, `joinedPerimeter_formula`;
- `octant_pathELength`, `selfPerimeter_eq_pathELength`, `joinedPerimeter_eq_pathELength`;
- `joinedPerimeter_six_lt_seven`, `seven_lt_selfPerimeter_six`;
- `joinedPerimeter_ne_selfPerimeter`.

The false closing assertion has therefore been refuted rather than added as
a theorem. This correction does not alter Lemmas 3.1–3.3 or Theorems 3.4–3.5
and 4.1.
