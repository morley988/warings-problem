"""Check continuous conductor coverage for every modulus in the field schedules.

This reads the actual integer tokens compiled by Lean and the exponent-pair
table whose arithmetic and word safety are checked in WaringDualEnvelope.
The cell endpoints are rounded inward to the common denominator 10,000.
"""
from pathlib import Path
import re
import argparse
import json

ROOT = Path(__file__).resolve().parents[1]
B = 10000
T = 10**32
E = 10**9
TOKEN = re.compile(r"def b\d+ : Schedule := ⟨(\d+),(\d+),(\d+),(\d+),\[([^\]]*)\]⟩", re.S)
PAIR = re.compile(r"\(\[(?:true|false|,|\s)*\],⟨(\d+),(\d+),(\d+),(\d+),(\d+)⟩\)")


def ceildiv(n, d):
    return (n+d-1)//d


def ordinary_cells(k, m, sig):
    denom = B*k
    common = T*denom
    intervals = []
    for j in range(min(k-2, 40)+1):
        y = (1<<j)*sig
        if 2*y>T or (j and m*T>denom*(T-y)):
            break
        lo = ceildiv(B*(j*m*T+2*y*denom), common)
        hi = B*((j+2)*T-(4*y-2*sig))//T
        intervals.append((lo,hi,j+1))
    for j in range(2, min(k, 200)+1):
        y = min(1 << (j-1), j*(j-1))*sig
        if 2*y>T:
            break
        lo = ceildiv(B*(j+1)*(y*denom+j*m*T), common)
        hi = B*min((j+1)*(common-m*T-y*denom),j*common-j*m*T-y*denom)//common
        intervals.append((lo,hi,j+40))
    endpoint = B
    path = []
    placed = 0
    intervals.sort()
    while endpoint < m:
        best = endpoint
        token = None
        while placed < len(intervals) and intervals[placed][0] <= endpoint:
            _, stop, choice = intervals[placed]
            if stop > best:
                best, token = stop, choice
            placed += 1
        if token is None:
            return None
        path.append(token)
        endpoint = best
    assert len(path) <= 16
    return sum(tok * 256**idx for idx, tok in enumerate(path))


def paired(k, m, sig, pair):
    x,y,d,loss,ld = pair
    # σ ≤ 1−λ+κ−κM−(D+1)(M/k), clearing all denominators.
    return (sig*d*B*ld*(B*k) + T*(y*B*ld*(B*k)+x*m*ld*(B*k)+(loss+ld)*d*B*m)
            <= T*(d+x)*B*ld*(B*k))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--emit", type=Path, help="write [least degree, integer gain, modulus, conductor code] rows")
    options = parser.parse_args()
    mesh = ROOT/'WaringFieldSmall'
    by_row = {}
    bands = []
    for path in mesh.glob('Section*.lean'):
        for match in TOKEN.finditer(path.read_text()):
            lo,hi,j,a = map(int,match.groups()[:4])
            bands.append((lo,hi))
            for word in map(int,match[5].split(',')):
                z, m, times = word%(2**32), word//(2**32)%(2**24), word//(2**56)
                assert z>0 and B<m<B*lo and times>0
                by_row[z,m] = min(by_row.get((z,m),lo),lo)
    assert sorted(bands)[0][0]==11 and sorted(bands)[-1][1]==2500
    assert all(x[1]+1==y[0] for x,y in zip(sorted(bands),sorted(bands)[1:]))
    pairs = [tuple(map(int,h)) for h in PAIR.findall((ROOT/'WaringDualEnvelope/Bank.lean').read_text())]
    elementary=0
    arithmetic=0
    witnesses = []
    for (gain,m),k in sorted(by_row.items()):
        sig=ceildiv(20001*gain*(T//(2*E)),10000)
        code = ordinary_cells(k,m,sig)
        if code is not None:
            elementary+=1
        else:
            assert k>=21,(k,gain,m)
            idx = next(i for i,p in enumerate(pairs) if paired(k,m,sig,p))
            code = 2**130 + idx
            arithmetic+=1
        witnesses.append([k,gain,m,str(code)])
    if options.emit:
        options.emit.write_text(json.dumps(witnesses,separators=(",",":"))+"\n")
    print(f'{len(bands)} degree intervals, {len(by_row)} distinct rows, '
          f'{elementary} elementary conductor covers and {arithmetic} arithmetic covers.')


if __name__=='__main__':
    main()
