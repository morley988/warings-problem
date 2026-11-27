"""Compute exact energies of cubed modular square roots in a sharp interval.

Usage: python square_modulus_energy.py   (requires NumPy)
Each multiplicity is counted with integer cyclic convolution. The interval
has radius floor(p^(2/3)); no Fourier rounding enters these calculations.
"""
from collections import Counter
from math import isqrt
import numpy as np


def cube_root_floor(n):
    low, high = 0, 1
    while high**3 <= n:
        high *= 2
    while high - low > 1:
        mid = (high + low) // 2
        if mid**3 <= n:
            low = mid
        else:
            high = mid
    return low


def circle_convolution(counts, shifts):
    result = np.zeros_like(counts)
    for shift, weight in shifts.items():
        result += weight * np.roll(counts, shift)
    return result


def energies(p, r):
    q = p*p
    radius = cube_root_floor(q)
    # For fixed residues y0 mod p, solve the second digit linearly.
    shifts = Counter()
    by_residue = {}
    for v in range(-radius, radius+1):
        if v % p:
            by_residue.setdefault(v % p, []).append(v)
    for y0 in range(1,p):
        base = -3*r*y0*y0
        inverse = pow(-6*r*y0, -1, p)
        for v in by_residue.get(base % p, ()):
            digit = ((v-base)//p * inverse) % p
            y = y0 + digit*p
            assert (3*r*y*y+v) % q == 0
            shifts[pow(y,3,q)] += 1
    size = sum(shifts.values())
    assert size**6 < 2**63
    counts = np.zeros(q, dtype=np.int64)
    for x, weight in shifts.items():
        counts[x] = weight
    pairs = circle_convolution(counts, shifts)
    triples = circle_convolution(pairs, shifts)
    return size, int(np.dot(pairs,pairs)), int(np.dot(triples,triples))


def main():
    print("p,Z,square_class,roots,E2,E3")
    for p in (29,43,67,97,149,223,331,499,743,1009):
        assert all(p % d for d in range(2,isqrt(p)+1))
        nonresidue = next(r for r in range(2,p) if pow(r,(p-1)//2,p)==p-1)
        for r in (1,nonresidue):
            size,e2,e3 = energies(p,r)
            print(p,cube_root_floor(p*p),r,size,e2,e3,sep=",",flush=True)


if __name__ == "__main__":
    main()
