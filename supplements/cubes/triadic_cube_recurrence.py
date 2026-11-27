"""Exact primitive three-cube measure for residue degree one and 3∤e.

The ring is Z_3[π], π**e = sign*3. Signed choices exhaust the tame
extensions in this residue degree. Fourier convolution below uses finite
prime fields. No floating point rounding or random sampling is used.
"""
import argparse
from itertools import product
from fractions import Fraction
from math import prod
import numpy as np


def prime(n):
    return n >= 2 and all(n % i for i in range(2, int(n**0.5) + 1))


def fourier(values, prime_modulus, inverse=False):
    order_nine_root = next(
        x for g in range(2, prime_modulus)
        if (x := pow(g, (prime_modulus - 1)//9, prime_modulus)) != 1
        and pow(x, 3, prime_modulus) != 1)
    if inverse:
        order_nine_root = pow(order_nine_root, -1, prime_modulus)
    for axis, width in enumerate(values.shape):
        weights = [[pow(order_nine_root, (9//width)*j*k, prime_modulus)
                    for k in range(width)] for j in range(width)]
        source = np.moveaxis(values, axis, 0)
        result = np.empty_like(source)
        for j in range(width):
            acc = np.zeros(source.shape[1:], dtype=np.int64)
            for k in range(width):
                acc = (acc + source[k] * weights[j][k]) % prime_modulus
            result[j] = acc
        values = np.moveaxis(result, 0, axis)
    if inverse:
        values = (values * pow(values.size, -1, prime_modulus)) % prime_modulus
    return values


def cube_density(e, sign):
    if e < 1 or e % 3 == 0 or sign not in (-1, 1):
        raise ValueError('require e>0, 3∤e, and sign ±1')
    r, ell = e//2 + 1, (e+2)//3
    precision = e+r
    coordinates = []
    for i in range(e):
        modulus = 3**((precision-i+e-1)//e)
        divisor = 1 if i % 3 == 0 else 3
        if modulus > divisor:
            coordinates.append((i, modulus//divisor, divisor))
    shape = tuple(m for _, m, _ in coordinates)
    assert prod(shape) == 3**(ell+r)
    cubes = np.zeros(shape, dtype=np.int64)

    # Enumerate pairs (x,x^2,x^3) recursively in the digits of x, using
    # (x+d*pi^j)^3 = x^3+3x²dπ^j+3xd²π^(2j)+d³π^(3j).
    zero = (0,)*e
    def add_shift(target, source, shift, factor):
        for i, value in enumerate(source):
            degree = i+shift
            target[degree % e] += value*factor*(sign*3)**(degree//e)
    def visit(j, x, square, cube):
        if j == r:
            assert all(cube[i] % d == 0 for i, _, d in coordinates)
            index = tuple((cube[i]//d) % m for i, m, d in coordinates)
            cubes[index] = 1
            return
        for digit in (0, 1, -1):
            xc, xs, xx = list(cube), list(square), list(x)
            add_shift(xc, square, j, 3*digit)
            add_shift(xc, x, 2*j, 3*digit*digit)
            xc[(3*j) % e] += digit**3*(3*sign)**((3*j)//e)
            add_shift(xs, x, j, 2*digit)
            xs[(2*j) % e] += digit**2*(3*sign)**((2*j)//e)
            xx[j % e] += digit*(3*sign)**(j//e)
            visit(j+1, xx, xs, xc)

    visit(0, zero, zero, zero)
    seen = np.zeros(shape, dtype=bool)
    upper = int(cubes.sum())**2
    combined_modulus = 1
    modulus = 1000000009
    while combined_modulus <= upper:
        while not prime(modulus):
            modulus += 9
        assert modulus % 9 == 1 and modulus < 2**31
        freq = fourier(cubes, modulus)
        freq = (freq**2 % modulus) * freq % modulus
        counts = fourier(freq, modulus, inverse=True)
        seen |= counts != 0
        combined_modulus *= modulus
        modulus += 9
    return int(np.count_nonzero(seen)), cubes.size


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('indices', nargs='*', type=int, default=[2,4,5,8,11])
    args = parser.parse_args()
    for e in args.indices:
        for sign in (1,-1) if e % 2 == 0 else (1,):
            n, total = cube_density(e, sign)
            print(f'e={e}, π^e={sign*3:+d}, level={e+e//2+1}: '
                  f'{n}/{total} = {Fraction(n,total)}',flush=True)


if __name__ == '__main__':
    main()
