"""Exact fourth-power widths in (Z/16)[t]/(t^3-2), for the local examples."""
from itertools import product


def multiply(left, right):
    coefficients = [0, 0, 0]
    for i, x in enumerate(left):
        for j, y in enumerate(right):
            carry, index = divmod(i + j, 3)
            coefficients[index] += x * y * (2 ** carry)
    return tuple(x % 16 for x in coefficients)


def add(left, right):
    return tuple((x + y) % 16 for x, y in zip(left, right))


def main():
    unit_powers = set()
    all_powers = set()
    for root in product(range(4), repeat=3):
        square = multiply(root, root)
        power = multiply(square, square)
        all_powers.add(power)
        if root[0] % 2:
            unit_powers.add(power)
    assert (len(all_powers), len(unit_powers)) == (22, 16)
    eligible = set(product(range(16), range(0, 16, 2), range(0, 16, 2)))
    ordinary = {(0, 0, 0)}
    primitive = set()
    print("summands,ordinary,primitive")
    for count in range(1, 11):
        primitive = {add(x, y) for x in ordinary for y in unit_powers} | {
            add(x, y) for x in primitive for y in all_powers
        }
        ordinary = {add(x, y) for x in ordinary for y in all_powers}
        print(f"{count},{len(ordinary)},{len(primitive)}")
        if count == 9:
            assert (8, 2, 2) not in ordinary
    assert ordinary == primitive == eligible


if __name__ == "__main__":
    main()
