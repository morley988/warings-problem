"""Enumerate the cube sumsets of Z_3[pi]/(pi^precision), pi**e = ±3.

Each element has e coefficients. Coefficient i is taken modulo
3**ceil((precision-i)/e). Degree-e carries in products are exact.
"""
from itertools import product


def cube_data(e, sign, precision):
    moduli = tuple(3 ** ((precision - i + e - 1) // e) for i in range(e))
    elements = product(*(range(m) for m in moduli))

    def add(x, y):
        return tuple((a + b) % m for a, b, m in zip(x, y, moduli))

    def multiply(x, y):
        coefficients = [0] * e
        for i, a in enumerate(x):
            for j, b in enumerate(y):
                degree = i + j
                carry = 3 * sign if degree >= e else 1
                coefficients[degree % e] += a * b * carry
        return tuple(a % m for a, m in zip(coefficients, moduli))

    cubes = {multiply(multiply(x, x), x) for x in elements}
    sums = {(0,) * e}
    sizes = [1]
    while True:
        next_sums = {add(x, y) for x in sums for y in cubes}
        if next_sums == sums:
            return sizes
        sums = next_sums
        sizes.append(len(sums))


def main():
    expected = {(2, 1): (7, 9), (2, -1): (17, 27),
                (4, 1): (17, 27), (4, -1): (151, 243)}
    for (e, sign), (numerator, denominator) in expected.items():
        for precision in (e + 3, e + 4):
            counts = cube_data(e, sign, precision)
            three, eligible = counts[3], counts[-1]
            assert three * denominator == eligible * numerator
            print(f'e={e}, pi^e={sign*3:+d}, level={precision}: '
                  f'{three}/{eligible} = {numerator}/{denominator}')


if __name__ == '__main__':
    main()
