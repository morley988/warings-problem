"""Compute the unit-square index for Eisenstein rings pi^e=2(1+c*pi).

All arithmetic takes place modulo pi^(e+2).  The distinct valuations
of the integral-basis terms give coefficient moduli 4,4,2,...,2.
"""
from itertools import product


def square(x, twist, moduli):
    e = len(x)
    coefficients = [0] * (2 * e - 1)
    for i, a in enumerate(x):
        for j, b in enumerate(x):
            coefficients[i + j] += a * b
    for i in reversed(range(e, len(coefficients))):
        c = coefficients[i]
        coefficients[i - e] += 2 * c
        coefficients[i - e + 1] += 2 * twist * c
    return tuple(c % modulus for c, modulus in zip(coefficients, moduli))


def span(generators, moduli):
    zero = (0,) * len(moduli)
    covered = {zero}
    for generator in generators:
        if generator in covered:
            continue
        previous = list(covered)
        multiple = generator
        while multiple not in covered:
            covered.update(tuple((a + b) % m for a, b, m in zip(x, multiple, moduli)) for x in previous)
            multiple = tuple((a + b) % m for a, b, m in zip(multiple, generator, moduli))
    return covered


def check(e, twist):
    moduli = [4, 4] + [2] * (e - 2)
    ring = list(product(*(range(m) for m in moduli)))
    squares = {square(x, twist, moduli) for x in ring}
    unit_squares = {square(x, twist, moduli) for x in ring if x[0] % 2}
    full = span(squares, moduli)
    unit = span(unit_squares, moduli)
    index = len(full) // len(unit)
    predicted = 2 if (e == 2 and twist == 1) or (e >= 4 and e % 2 == 0 and twist == 0) else 1
    assert len(full) == predicted * len(unit)
    print(f"e={e}, c={twist}: |J|={len(full)}, |C|={len(unit)}, index={index}")


if __name__ == "__main__":
    for degree in range(2, 10):
        for choice in (0, 1):
            check(degree, choice)
