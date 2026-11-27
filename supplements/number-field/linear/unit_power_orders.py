"""Check local unit-power indices for Eisenstein rings pi^e=p(a+b*pi).

The residue ring is O/(p*pi^2).  Its integral-basis coefficient moduli
are p^2,p^2,p,...,p for e>=2. All powers are computed by multiplication
in this finite ring. The predicted index is compared with the ranks of
the additive spans of all powers and unit powers.
"""
from itertools import product


def multiply(x, y, p, a, b):
    e = len(x)
    z = [0] * (2 * e - 1)
    for i, coefficient in enumerate(x):
        if coefficient:
            for j, other in enumerate(y):
                z[i + j] += coefficient * other
    for i in reversed(range(e, len(z))):
        z[i - e] += p * a * z[i]
        z[i - e + 1] += p * b * z[i]
    return [c % (p * p if i < 2 else p) for i, c in enumerate(z[:e])]


def power(x, p, a, b):
    z = [1] + [0] * (len(x) - 1)
    exponent = p
    while exponent:
        if exponent % 2:
            z = multiply(z, x, p, a, b)
        x = multiply(x, x, p, a, b)
        exponent //= 2
    return z


def extend(basis, vector, p):
    for i, pivot in enumerate(basis):
        if not vector[i]:
            continue
        if pivot is None:
            multiplier = pow(vector[i], -1, p)
            basis[i] = [(v * multiplier) % p for v in vector]
            return
        multiplier = vector[i]
        vector = [(v - multiplier * w) % p for v, w in zip(vector, pivot)]


def check(p, e, a, b):
    # Any two roots equal mod pi^r have equal pth powers mod p*pi^2.
    r = max(2, (e + p + 1) // p)
    all_powers = [None] * (e - 1)
    unit_powers = [None] * (e - 1)
    for digits in product(range(p), repeat=r):
        root = list(digits) + [0] * (e - r)
        z = power(root, p, a, b)
        assert z[1] % p == 0
        # The shared generator 1 removes the full constant coordinate.
        vector = [z[1] // p] + z[2:]
        extend(all_powers, vector, p)
        if digits[0]:
            extend(unit_powers, vector, p)
    difference = sum(v is not None for v in all_powers) - sum(v is not None for v in unit_powers)
    predicted = ((e == p - 1 and a == p - 1) or
                 (e == p and b == p - 1) or
                 (e >= 2 * p and e % p == 0 and b == 0) or
                 (e >= p and e % p != 0 and (e + 1) % p != 0))
    assert difference == int(predicted), (p, e, a, b, difference, predicted)


if __name__ == "__main__":
    cases = 0
    for p, maximum in ((2, 9), (3, 12), (5, 11), (7, 14), (11, 12)):
        for e in range(2, maximum + 1):
            for a in sorted({1, p - 1}):
                for b in sorted({0, 1, p - 1}):
                    check(p, e, a, b)
                    cases += 1
    print(f"Verified {cases} Eisenstein presentations at residue characteristics 2, 3, 5, 7, 11.")
