"""Verify the local, smooth-moment and fibre certificates using Python 3."""
import contextlib
import io
import json
import runpy
import subprocess
import sys
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent / "certificates"
Q = Fraction


def smooth_excesses(degree):
    """Recover the input curve from its original exact moment computation."""
    script = {9: "ninth-field.py", 10: "tenth-field.py"}[degree]
    with contextlib.redirect_stdout(io.StringIO()):
        program = runpy.run_path(str(HERE / script))
        if degree == 9:
            exponents = program["final"]
        else:
            program["verify"]()
            exponents = program["DATA"]["b"]
    loss_free_order = {9: 46, 10: 56}[degree]
    points = {2 * s: Q(value) + degree - 2 * s
              for s, value in enumerate(exponents) if s >= 2}
    points[loss_free_order] = Q(0)
    for order in points:
        if order > loss_free_order:
            points[order] = Q(0)
    hull = []
    for order, excess in sorted(points.items()):
        while len(hull) >= 2:
            (u, first), (v, second) = hull[-2:]
            if (second - first) * (order - v) < (excess - second) * (v - u):
                break
            hull.pop()
        hull.append((order, excess))
    return dict(hull)


def interpolate(curve, r):
    if r in curve:
        return curve[r]
    lo = max(q for q in curve if q < r)
    hi = min(q for q in curve if q > r)
    return ((hi-r) * curve[lo] + (r-lo) * curve[hi]) / (hi-lo)


def check_cover(k, upper, sigma):
    theta = upper / k + Q(1, 10**6)
    intervals = []
    for j in range(k-1):
        if 2**j * sigma > Q(1, 2):
            continue
        if j > 0 and theta > 1 - 2**j * sigma:
            continue
        left = j * theta + 2**(j+1) * sigma
        right = j + 2 - (2**(j+2) - 2) * sigma
        if left <= right:
            intervals.append((left, right))
    covered = Q(1)
    for left, right in sorted(intervals):
        if left <= covered:
            covered = max(covered, right)
    assert covered > upper


def verify_policy(data):
    k, ordinary, total = data["k"], data["ordinary"], data["total"]
    restricted = total - ordinary
    share = Q(ordinary, k*(k+1))
    r = restricted/(1-share)
    ambient = smooth_excesses(k)
    ceiling = -(-r.numerator // r.denominator)
    curve = {q: interpolate(ambient, Q(q)) for q in range(4, ceiling+1)}
    previous_order = 0
    for row in data["rows"]:
        order, prior = Q(row["q"]), Q(row["h"])
        upper, z, result = Q(row["M"]), Q(row["z"]), Q(row["delta"])
        lower = upper-Q(1, 1000)
        assert previous_order < order and k+2 <= order and 4 <= prior < order
        assert 0 < lower < upper < k/2 and result >= 0 and z > 0
        check_cover(k, upper, 2*z+Q(1, 10000))
        high = (1-lower/k) * curve[order-2]
        low = curve[prior]-(order-prior)*z
        assert max(high,low) <= result < curve[order]
        curve[order] = result
        previous_order = order
    gain = share - (1-share)*interpolate(curve, r)
    assert gain == Q(data["gain"]) and gain > 0
    critical = {9: 46, 10: 56}[k]
    pruning = Q(ordinary*critical, critical-restricted)
    assert pruning > 2*k
    print(f"k={k}: {total} variables, minor saving {gain}, pruning order {pruning}")


def main():
    files = sorted(HERE.glob("*.py"))
    assert len(files) == 9
    for path in files:
        command = [sys.executable, str(path)]
        result = subprocess.run(command, cwd=HERE, capture_output=True, text=True)
        if result.returncode:
            raise RuntimeError(result.stdout + result.stderr)
        print(f"{path.name}: passed")
    for policy in json.loads((HERE / "fibres.json").read_text()):
        verify_policy(policy)


if __name__ == "__main__":
    main()
