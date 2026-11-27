"""Check the additive-polynomial Witt carry over small prime fields.

Coefficients are polynomials in T over F_p. The product in U records
the big Witt coordinates, which project onto the p-typical coordinates.
No numerical approximation is used.
"""
from itertools import product


def polynomial_sum(left, right, p):
    result = dict(left)
    for degree, value in right.items():
        result[degree] = (result.get(degree, 0) + value) % p
        if not result[degree]:
            del result[degree]
    return result


def polynomial_product(left, right, p):
    result = {}
    for i, x in left.items():
        for j, y in right.items():
            result[i+j] = (result.get(i+j, 0) + x*y) % p
    return {degree: value for degree, value in result.items() if value}


def product_in_u(roots, p):
    rows = [{0: 1}]
    for root in roots:
        negative = {degree: -value for degree, value in root.items()}
        terms = [polynomial_product(row, negative, p) for row in rows]
        rows.append({})
        for i, term in enumerate(terms):
            rows[i+1] = polynomial_sum(rows[i+1], term, p)
    return rows


def check(p, depth):
    representatives = [{degree: v for degree, v in enumerate(digits) if v}
                       for digits in product(range(p), repeat=depth)]
    baseline = product_in_u(representatives, p)
    shift = {depth: 1, depth+1: 1}
    moved = product_in_u([polynomial_sum(v, shift, p) for v in representatives], p)
    assert moved[:-1] == baseline[:-1]
    change = polynomial_sum(moved[-1], {i: -v for i, v in baseline[-1].items()}, p)
    threshold = (p**depth-1)//(p-1)
    assert min(change) == threshold
    assert threshold % p == 1
    return len(representatives), threshold


if __name__ == "__main__":
    for p, depth in ((2, 1), (2, 2), (2, 3), (2, 4), (3, 1), (3, 2), (3, 3), (5, 2)):
        count, order = check(p, depth)
        print(f"p={p} depth={depth}: {count} terms, first degree {order}")
