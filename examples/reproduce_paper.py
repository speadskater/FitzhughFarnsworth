#!/usr/bin/env python3
"""High-precision numerical reproduction, NOT a Lean proof or interval certificate.

Uses only Python's standard library. Decimal trigonometry avoids binary-float
artifacts; the finite computations and stopping criterion remain numerical.
The Lean library independently proves convergence and monotonicity.
"""

import argparse
from decimal import Decimal as D, localcontext


def arctan(x, epsilon):
    if x < 0:
        return -arctan(-x, epsilon)
    multiplier = D(1)
    while x > D("0.2"):
        x = x / (1 + (1 + x * x).sqrt())
        multiplier *= 2
    total, term, n = x, x, 1
    while True:
        term *= -x * x
        addition = term / (2 * n + 1)
        total += addition
        if abs(addition) < epsilon:
            return multiplier * total
        n += 1


def sin_cos(x, epsilon):
    sine, cosine = x, D(1)
    st, ct, n = x, D(1), 1
    while True:
        st *= -x * x / ((2 * n) * (2 * n + 1))
        ct *= -x * x / ((2 * n - 1) * (2 * n))
        sine += st
        cosine += ct
        if max(abs(st), abs(ct)) < epsilon:
            return sine, cosine
        n += 1


def two_step(a, b):
    delta = b * (a - 1) / (b - 1)
    epsilon = b * (a + 1) / (b + 1)
    return epsilon * (delta + 1) / (epsilon + 1), epsilon * (delta - 1) / (epsilon - 1)


def numerical_limit(a, b, tolerance):
    for steps in range(1001):
        if abs(a + 1 / b) < tolerance:
            return (a - 1 / b) / 2, steps
        a, b = two_step(a, b)
    raise ArithmeticError("Numerical stopping criterion not reached")


PUBLISHED_TABLE = [
    ["4.50", "9.10", "14.11", "19.91", "27.10"],
    ["9.10", "13.50", "18.20", "23.53", "30.01"],
    ["14.11", "18.20", "22.50", "27.31", "33.07"],
    ["19.91", "23.53", "27.31", "31.50", "36.46"],
    ["27.10", "30.01", "33.07", "36.46", "40.50"],
]


def main(precision):
    with localcontext() as context:
        context.prec = precision + 20
        epsilon = D(10) ** (-precision - 15)
        tolerance = D(10) ** (-precision)
        pi = 16 * arctan(D(1) / 5, epsilon) - 4 * arctan(D(1) / 239, epsilon)

        def tangent_degrees(theta):
            sine, cosine = sin_cos(theta * pi / 180, epsilon)
            return sine / cosine

        def degrees_of_slope(slope):
            return arctan(slope, epsilon) * 180 / pi

        angles = [D("4.5") + 9 * i for i in range(5)]
        print(f"Decimal precision: {precision} (+20 guard digits)")
        print("Numerical evidence only; no certified transcendental error bounds.\n")
        print("Table 1: converged numerical estimates in degrees")
        print("theta / phi     " + " ".join(f"{x+90:>8.1f}" for x in angles))
        differences = []
        five_step_differences = []
        for i, theta in enumerate(angles):
            row = []
            for j, phi0 in enumerate(angles):
                phi = phi0 + 90
                a, b = tangent_degrees(theta), tangent_degrees(phi)
                limit, _ = numerical_limit(a, b, tolerance)
                result = degrees_of_slope(limit)
                rounded = f"{result:.2f}"
                row.append(rounded)
                if rounded != PUBLISHED_TABLE[i][j]:
                    differences.append((theta, phi, PUBLISHED_TABLE[i][j], result))
                for _ in range(5):
                    a, b = two_step(a, b)
                after_five = degrees_of_slope(a)
                if f"{after_five:.2f}" != rounded:
                    five_step_differences.append((theta, phi, after_five, result))
            print(f"{theta:>11.1f}     " + " ".join(f"{x:>8}" for x in row))

        print("\nDifferences from the published table:")
        for theta, phi, published, computed in differences:
            print(f"  ({theta}, {phi}): paper {published}; computed {computed:.15f}")
        if not differences:
            print("  None")

        print("\nFive two-step updates versus the settled estimate (rounded to 0.01 degrees):")
        for theta, phi, five, settled in five_step_differences:
            print(f"  ({theta}, {phi}): after five {five:.15f}; settled {settled:.15f}")
        if not five_step_differences:
            print("  All match")

        a, b = tangent_degrees(D("4.5")), tangent_degrees(D("130.5"))
        arc_midpoint = (2 * a / (1 + a) + 2 + 2 / (1 - b)) / 2
        limit, _ = numerical_limit(a, b, tolerance)
        options = [
            ("Euclidean", tangent_degrees(D("67.5"))),
            ("Taxicab arc", arc_midpoint / (2 - arc_midpoint)),
            ("First midset", b * (a + 1) / (b + 1)),
            ("Limiting midset", (1 + limit) / (1 - limit)),
        ]
        print("\nSection 4, using exact input angles before numerical approximation:")
        for name, slope in options:
            print(f"  {name:<18} slope {slope:.12f}; angle {degrees_of_slope(slope):.12f}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--precision", type=int, default=80)
    args = parser.parse_args()
    if not 30 <= args.precision <= 300:
        parser.error("--precision must be between 30 and 300")
    main(args.precision)
