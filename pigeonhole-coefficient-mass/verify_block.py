"""Replay the rational block calibration and the four dual values in Table 1."""

from collections import Counter
from decimal import Decimal, localcontext
from fractions import Fraction
from itertools import product


# Integer weights are 30 times the paper's weights.
WEIGHTS = {
    (): -30,
    (1,): 10,
    (2,): 10,
    (3,): 0,
    (1, 1): -6,
    (1, 2): -4,
    (1, 1, 1): 5,
}
LABELS = tuple(range(1, 7))
LETTERS = (0,) + LABELS


def verify_calibration():
    weights = {}
    masses = [0, 0, 0, 0]
    for string in product(LETTERS, repeat=3):
        frequencies = Counter(letter for letter in string if letter != 0)
        weight = WEIGHTS[tuple(sorted(frequencies.values()))]
        weights[string] = weight
        masses[len(frequencies)] += weight

    allowed = [()] + [(label,) for label in LABELS]
    for mask in product((False, True), repeat=len(LABELS)):
        allowed.append((0,) + tuple(label for label, keep in zip(LABELS, mask) if keep))

    minimum = maximum = 0
    for first, second in product(allowed, repeat=2):
        slice_sums = [
            sum(weights[a, b, c] for a in first for b in second)
            for c in LETTERS
        ]
        for third in allowed:
            value = sum(slice_sums[c] for c in third)
            minimum = min(minimum, value)
            maximum = max(maximum, value)

    if (minimum, maximum) != (-30, 30) or masses != [-30, 360, -900, 600]:
        raise ValueError("Rational block calibration failed")
    print(f"{len(allowed) ** 3:,} boxes: scaled extrema [{minimum}, {maximum}]")
    return [mass // 30 for mass in reversed(masses)]


def dual_value(n, polynomial):
    k = 2 * ((2 * n - 1) // 12)
    coefficients = [1]
    for _ in range(k):
        expanded = [0] * (len(coefficients) + len(polynomial) - 1)
        for i, coefficient in enumerate(coefficients):
            for j, factor in enumerate(polynomial):
                expanded[i + j] += coefficient * factor
        coefficients = expanded
    return 2 * n * sum(
        Fraction(coefficient, 2 * n - 3 * k + i)
        for i, coefficient in enumerate(coefficients)
    )


if __name__ == "__main__":
    polynomial = verify_calibration()
    print("n    log(dual value)    rate")
    with localcontext() as context:
        context.prec = 40
        for n in (48, 96, 192, 384):
            value = dual_value(n, polynomial)
            logarithm = (Decimal(value.numerator) / Decimal(value.denominator)).ln()
            print(f"{n:3d}  {logarithm:15.2f}    {logarithm / n:.3f}")
