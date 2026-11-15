# Numerical reproduction and source discrepancies

Reference: Fitzhugh and Farnsworth (2014),
[DOI 10.1155/2014/832647](https://doi.org/10.1155/2014/832647), Table 1 and Section 4.

These observations are **numerical evidence, not Lean-certified decimal claims**.
The script uses Python `decimal` with 20 guard digits, a Machin formula for π,
Taylor series for sine/cosine/arctangent, and the paper's actual alternating
slope maps. Runs at 80 and 120 requested digits agree at every displayed digit.
The stopping criterion uses the separation of the candidate slopes `a` and `-1/b`;
transcendental and arithmetic rounding errors are not formally enclosed by the script.

```sh
python3 examples/reproduce_paper.py --precision 80
python3 examples/reproduce_paper.py --precision 120
```

## Table 1

All entries reproduce at two decimals except this symmetric pair:

| Initial θ | Initial φ | Printed | Settled numerical angle | Rounded numerical angle |
| --- | --- | --- | --- | --- |
| 31.5° | 130.5° | 36.46° | 36.465446857354067…° | 36.47° |
| 40.5° | 121.5° | 36.46° | 36.465446857354067…° | 36.47° |

The symmetry agrees with the formally proved reciprocal-symmetry theorem.

The statement about obtaining the tabulated values within five pairs of steps
also needs a precise numerical interpretation. For θ=40.5°, φ=103.5°, taking the
shallow slope after exactly five two-step updates gives 30.015165518779043…°,
which rounds to 30.02°. The settled value is 30.013963174328233…°, rounding to the
printed 30.01°. This observation concerns the literal fifth iterate, not every
possible estimator using the two slopes.

## Section 4

Using the stated input angles 4.5° and 130.5° before numerical approximation:

| Convention | Numerical slope | Numerical angle |
| --- | --- | --- |
| Euclidean | 2.414213562373 | 67.500000000000° |
| Taxicab arc | 3.288245611271 | 73.084773565322° |
| First midset | 7.392453221500 | 82.296185866663° |
| Limiting midset | 3.096091603460 | 72.100173278856° |

Separately, `AngleConventions/Comparison.lean` formally proves all four conventions
differ for the exact rational starting slopes `(1/4, -2)`, without numerical
assumptions. That theorem is an exact illustrative alternative, not a certificate
for the original 4.5°/130.5° example.

The paper rounds slopes and intermediate arc lengths before some subsequent
calculations. That is a different computation from starting with the exact
angles, so differences here are not automatically errors. The formal library
currently proves the constructions and their geometric properties; it does not
silently treat these displayed numbers as exact constants.

## Route to formal certification

`SlopePair.limit_enclosure` and `limit_error_le_enclosure_width` already provide
exact truncation bounds in Lean. What remains is certified trigonometric input
and output bounds, together with certified arithmetic, to turn these numerical
observations into proofs about the paper's exact initial angles.
