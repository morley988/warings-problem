"""Verify the dyadic squareclass probabilities for multiquadratic fields.

The bits represent the squareclasses of -1, 2 and 5 respectively.
Products of squareclasses are represented by the XOR of their indices.
"""
from collections import defaultdict
from fractions import Fraction


def span_with(space, element):
    return space.union(value ^ element for value in space)


def local_obstruction(space):
    if len(space) == 1:
        return True
    if len(space) == 2:
        return next(value for value in space if value) in (1, 2, 3, 6, 7)
    return space == frozenset((0, 1, 2, 3))


def probabilities(rank):
    weights = (8, 2, 1, 1, 8, 2, 1, 1)
    law = {frozenset((0,)): 1}
    for _ in range(rank):
        following = defaultdict(int)
        for space, count in law.items():
            for element, weight in enumerate(weights):
                following[span_with(space, element)] += count * weight
        law = following
    assert sum(law.values()) == 24**rank
    return tuple(Fraction(sum(count for space, count in law.items()
                              if len(space) == 2**dimension and local_obstruction(space)),
                          24**rank) for dimension in range(3))


def predicted(rank):
    a = Fraction(1, 3)**rank
    b = Fraction(5, 12)**rank
    c = Fraction(3, 8)**rank
    d = Fraction(1, 2)**rank
    return a, b + 4*c - 5*a, d - b - 2*c + 2*a


if __name__ == "__main__":
    for rank in range(2, 21):
        assert probabilities(rank) == predicted(rank)
    print("Exact local-state checks for ranks 2 through 20 passed.")
    print("Biquadratic obstruction probabilities:", *probabilities(2))
