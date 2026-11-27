"""Rational first-moment upper bound and collision surplus for three positive cubes."""
from collections import Counter
from fractions import Fraction
from functools import lru_cache
from math import prod


@lru_cache(maxsize=None)
def residue_distribution(modulus):
    cubes = Counter(pow(x, 3, modulus) for x in range(modulus))
    pairs = Counter()
    for a, n in cubes.items():
        for b, m in cubes.items():
            pairs[(a+b) % modulus] += n*m
    triples = Counter()
    for a, n in pairs.items():
        for b, m in cubes.items():
            triples[(a+b) % modulus] += n*m
    return Counter(triples[a] for a in range(modulus))


def crt_distribution(moduli):
    groups = Counter({1: 1})
    for modulus in moduli:
        next_groups = Counter()
        for a, m in groups.items():
            for b, n in residue_distribution(modulus).items():
                next_groups[a*b] += m*n
        groups = next_groups
    return groups



def bounds(moduli):
    modulus = prod(moduli)
    denominator = 100000 * modulus**2
    upper_num = surplus_num = 0
    active = 0
    groups = crt_distribution(moduli)
    assert sum(groups.values()) == modulus
    assert sum(n*count for n, count in groups.items()) == modulus**3
    for triples, count in groups.items():
        lower = 11867 * triples
        upper = 11869 * triples
        upper_num += count * min(denominator, upper)
        j = lower // denominator
        if j >= 2:
            surplus_num += count * (j - 1) * (2 * lower - (j+2) * denominator)
            if lower > 2*denominator:
                active += count
    upper = Fraction(upper_num, denominator*modulus)
    surplus = Fraction(surplus_num, 2*denominator*modulus)
    gamma_low = Fraction(11867, 100000)
    improved = gamma_low - Fraction(42,25)*gamma_low**2 + surplus
    return upper, surplus, improved, Fraction(active,modulus)


if __name__ == "__main__":
    moduli = [729, 512, 343, 13, 19, 31, 37, 43]
    upper, surplus, improved, active = bounds(moduli)
    assert upper == Fraction(728028583078263256286286854758069,
                              6231646102240614790247825894400000)
    print("Upper density:", upper, float(upper))
    print("Forced high-multiplicity surplus:", surplus, float(surplus))
    print("Conditional lower density:", improved, float(improved))
    print("Proportion of residue classes with mean above two:", float(active))
