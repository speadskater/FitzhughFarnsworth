#!/usr/bin/env python3
"""Reproduce the normality tables and compare circumference formulas.

Only Python's standard library is used. Decimal table values and float
quadrature are numerical illustrations, not interval certificates or Lean proofs.
Quadrature is streamed, with constant storage, at two resolutions.
"""

from __future__ import annotations

import argparse
from decimal import Decimal, localcontext
from fractions import Fraction
import json
import math


TABLES = [
    ("Table 1", Fraction(5, 2), Fraction(1, 5), [
        ("-2.9240", "-0.3120"), ("0.4890", "2.0448"),
        ("-1.6111", "-0.6207"), ("0.7277", "1.3743"),
        ("-1.2361", "-0.8090"), ("0.8682", "1.1518"),
        ("-1.1000", "-0.9101"), ("0.9391", "1.0648"),
    ]),
    ("Table 2", Fraction(5, 3), Fraction(4, 5), [
        ("-1.3975", "-0.7155"), ("0.6053", "1.6521"),
        ("-2.1236", "-0.4709"), ("0.3231", "3.0946"),
        ("-5.4439", "-0.1837"), ("0.0787", "12.702"),
        ("-45.269", "-0.0221"), ("0.0033", "304.58"),
    ]),
]


def decimal(value: Fraction) -> Decimal:
    return Decimal(value.numerator) / Decimal(value.denominator)


def iterate(p: Fraction, initial: Fraction, n: int) -> Decimal:
    exponent = (-1 / (p - 1)) ** n
    magnitude = (decimal(initial).ln() * decimal(exponent)).exp()
    return magnitude if n % 2 == 0 else -magnitude


def simpson(function, steps: int) -> float:
    if steps < 2 or steps % 2:
        raise ValueError("Simpson steps must be a positive even number of at least two")
    # t = u^30 removes the low regularity at t=0 for the exponents compared here.
    def transformed(u: float) -> float:
        return 30 * u ** 29 * function(u ** 30)

    total = math.fsum((transformed(0.0), transformed(1.0)))
    total += 4 * math.fsum(transformed(i / steps) for i in range(1, steps, 2))
    total += 2 * math.fsum(transformed(i / steps) for i in range(2, steps, 2))
    return total / (3 * steps)


def perimeters(p: float, steps: int) -> dict:
    q = p / (p - 1)

    def own_speed(r: float, t: float) -> float:
        return ((1 + t ** r) ** (-1 / r - 1)
                * (1 + t ** (r * (r - 1))) ** (1 / r))

    def dual_speed(r: float, t: float) -> float:
        return (1 + t ** r) ** (-2 / r)

    return {
        "p": p, "q": q, "steps": steps,
        "lp_self_perimeter": 8 * simpson(lambda t: own_speed(p, t), steps),
        "lq_self_perimeter": 8 * simpson(lambda t: own_speed(q, t), steps),
        "joined_self_perimeter": 4 * (simpson(lambda t: dual_speed(p, t), steps)
                                       + simpson(lambda t: dual_speed(q, t), steps)),
    }


def reproduce(precision: int, steps: int) -> dict:
    if precision < 30:
        raise ValueError("Use at least 30 decimal digits")
    result = {"decimal_digits": precision, "table_discrepancies": [], "tables": [],
              "circumferences": [],
              "status": "Numerical illustration; quadrature errors are not certified."}
    with localcontext() as context:
        context.prec = precision + 20
        for label, p, m, published in TABLES:
            rows = []
            for n, row in enumerate(published, 1):
                values = [iterate(p, initial, n) for initial in (m, 1 / m)]
                reciprocity_error = abs(values[0] * values[1] - 1)
                if reciprocity_error > Decimal(10) ** (-precision):
                    raise ArithmeticError("The independently computed reciprocal columns disagree")
                rounded = [str(value.quantize(Decimal(printed)))
                           for value, printed in zip(values, row)]
                for column, (printed, value) in enumerate(zip(row, rounded), 1):
                    if printed != value:
                        result["table_discrepancies"].append({
                            "table": label, "n": n, "column": column,
                            "published": printed, "reproduced": value,
                        })
                rows.append({"n": n, "published": list(row), "rounded": rounded,
                             "values": [format(value, f".{precision}g") for value in values]})
            result["tables"].append({"table": label, "p": str(p),
                                     "initial_slopes": [str(m), str(1 / m)], "rows": rows})
    for p in (2.0, 4.0, 6.0):
        coarse, fine = perimeters(p, steps), perimeters(p, 2 * steps)
        fine["resolution_differences"] = {
            key: abs(fine[key] - coarse[key])
            for key in ("lp_self_perimeter", "lq_self_perimeter", "joined_self_perimeter")
        }
        result["circumferences"].append(fine)
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--precision", type=int, default=80)
    parser.add_argument("--steps", type=int, default=8192)
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()
    data = reproduce(args.precision, args.steps)
    if args.json:
        print(json.dumps(data, indent=2))
        return
    print(data["status"])
    for table in data["tables"]:
        print(f"\n{table['table']}: p={table['p']}, initial slopes {table['initial_slopes']}")
        for row in table["rows"]:
            print(f"  m{row['n']}: {row['rounded'][0]:>10} {row['rounded'][1]:>10}")
    print("\nDifferences from the printed tables:")
    for row in data["table_discrepancies"]:
        print(f"  {row['table']}, m{row['n']}, column {row['column']}: "
              f"printed {row['published']}; reproduced {row['reproduced']}")
    print("\nCircumferences (each measured in its own norm):")
    for row in data["circumferences"]:
        print(f"  p={row['p']:g}, q={row['q']:.10g}: "
              f"lp {row['lp_self_perimeter']:.10f}; lq {row['lq_self_perimeter']:.10f}; "
              f"joined {row['joined_self_perimeter']:.10f}")
        print(f"    maximum change on doubling resolution: "
              f"{max(row['resolution_differences'].values()):.3g}")


if __name__ == "__main__":
    main()
