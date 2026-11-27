"""Finite arithmetic for the densities of six fourth powers in quadratic fields."""
from fractions import Fraction

def reachable(directions, modulus, count):
    zero = (0,) * len(directions[0])
    rows = {zero}
    counts = [1]
    for _ in range(count):
        rows |= {tuple((x + y) % modulus for x, y in zip(row, vector))
                 for row in rows for vector in directions}
        counts.append(len(rows))
    return counts

def primitive_scalars(step):
    return {(units + step * others) % 16
            for units in range(1, 7) for others in range(7 - units)}

def main():
    all_classes = set(range(16))
    assert all_classes - primitive_scalars(4) == {0}
    assert all_classes - primitive_scalars(-4) == {8}
    # In the unramified quadratic completion, either lift of each Teichmuller
    # direction is a fourth power, and a unit absorbs the residual error in 16O.
    directions = [(j * x, j * y) for (x, y) in ((1, 0), (0, 1), (-1, -1))
                  for j in (1, 9)]
    counts = reachable(directions, 16, 7)
    assert counts == [1, 7, 25, 58, 106, 166, 226, 256]
    inert = Fraction(counts[6], 256)
    even_radicand = (Fraction(15, 16) - Fraction(3, 64)) / (1 - Fraction(1, 16))
    gaussian = Fraction(15, 16) + Fraction(1, 64)
    split = Fraction(6, 15)**2
    mean = split/3 + inert/3 + even_radicand/6 + gaussian/12 + Fraction(1, 12)
    assert (inert, even_radicand, gaussian, mean) == (
        Fraction(113, 128), Fraction(19, 20), Fraction(61, 64), Fraction(12839, 19200))
    print("Unramified counts", counts)
    print("Relative densities split, inert, even, Gaussian, sqrt(-5):",
          split, inert, even_radicand, gaussian, 1)
    print("Mean in fundamental discriminant order", mean)

if __name__ == "__main__":
    main()
