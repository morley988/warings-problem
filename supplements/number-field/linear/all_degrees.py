"""Finite and uniform marked-moment orders over number fields for every k>=11.

The source bounds use ordinary Weyl savings for the preliminary orders.
The final orders use the tagged bilinear saving 1/(15 k). All computations
in the tests and certified inequalities use integer or rational arithmetic.
"""
import gzip
import json
import sys
from bisect import bisect_right
from fractions import Fraction as Q
from pathlib import Path

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / 'mesh'))
import linear_verify as V
import dual_verify as D
import uniform_verify as C

SCALE = 10**9
DEN = V.B * V.RETENTION.denominator

def ceil_div(a, b):
    return -(-a // b)

def even_ceiling(a):
    return a + a % 2

def rows_for_small(k):
    """Dyadic A and ordinary degree-reduction cells, avoiding A/B word exclusions."""
    z = 12 * V.T // 100
    rows = []
    for _ in range(105):
        lo, hi = V.B, (k*V.B)//2-1
        while lo < hi:
            m = (lo+hi+1)//2
            if V.covered(z,m,k):
                lo = m
            else:
                hi = m-1
        assert V.covered(z,lo,k)
        rows.append((z,lo))
        z = z*93//100
    return rows

def band_rows(band):
    k, _, entries = band
    z = int(D.ztop(k)*V.T)
    selected = []
    for i, (m, word_index) in enumerate(entries):
        if i % 7 == 0 or i+1 == len(entries):
            assert m*2 < k*V.B
            assert (V.covered(z,m,k) if word_index < 0
                    else D.pair_ok(z,m,k,D.PAIRS[word_index]))
            selected.append((z,m))
        z = V.next_height(z)
    return selected

def preliminary_bound(k, upper, rows):
    """Normalized even order from ED plus fibre contraction at fixed terminal M."""
    z0 = D.ztop(k)
    assert rows[0][0] == int(z0*V.T)
    assert V.RETENTION*Q(rows[0][1],V.B) > 2*(1-z0)
    value = 2+V.logarithm((1-z0)/z0)
    for (z,m),(next_z,_) in zip(rows,rows[1:]):
        length = V.RETENTION*Q(m,V.B)
        value += V.outward(2*V.logarithm(Q(z,next_z))/length)
    z,m = rows[-1]
    length = V.RETENTION*Q(m,V.B)
    correction = 2*V.logarithm(max(Q(1),Q(z,V.T)*upper*(upper-1)))/length
    return V.outward(value+correction+Q(10,k))

def discrete(k, rows):
    """Even-moment induction, absolute defect rounded upward to 1/SCALE."""
    w = k*(k+1)
    z = [2*h*SCALE//V.T for h,_ in rows]
    length = [V.RETENTION.numerator*m for _,m in rows]
    crossover = [-(s*DEN//l) for s,l in zip(z,length)]
    assert sorted(crossover)==crossover
    cap = 1 << min(k,32)
    ed = defect = (k-1)*SCALE
    best_pre = best_tagged = 20*k
    for r in range(2,8*k,2):
        if r>k+1 and r<w:
            a = w*defect//(SCALE+defect)+1
            b = ceil_div(r*(w-a),w)
            pre = even_ceiling(a+b)
            if a<=w and pre>2*k and pre>=r and pre>=a:
                best_pre = min(pre,best_pre)
            needed = 15*k*defect//SCALE + 1
            tagged = even_ceiling(1+r+needed)
            if tagged>2*k:
                best_tagged = min(tagged,best_tagged)
        old_ed = ed
        ed -= (2*old_ed*SCALE*(cap-1))//((k*SCALE+old_ed)*cap)
        if r>k+1:
            i = bisect_right(crossover,-(defect//k))
            choices = {max(0,min(len(rows)-1,i+offset)) for offset in (-1,0,1)}
            saving = max(min(z[j],defect*length[j]//(k*DEN)) for j in choices)
            defect = min(ed,defect-saving)
        else:
            defect=ed
    return best_pre,best_tagged

def main():
    with gzip.open(ROOT/'mesh/dual_witness.json.gz','rt') as f:
        witnesses=json.load(f)
    worst_pre, worst_tagged = Q(0),Q(0)
    previous = 10
    for k in range(11,21):
        preliminary,tagged = discrete(k,rows_for_small(k))
        worst_pre=max(worst_pre,Q(preliminary,k))
        worst_tagged=max(worst_tagged,Q(tagged+1,k))
        assert k==previous+1
        previous=k
    for band in witnesses['finite']:
        k,upper,_=band
        assert k==previous+1
        previous=upper
        rows=band_rows(band)
        bounded=preliminary_bound(k,upper,rows)
        worst_pre=max(worst_pre,bounded)
        for degree in range(k,min(upper,2500)+1):
            _,tagged=discrete(degree,rows)
            worst_tagged=max(worst_tagged,Q(tagged+1,degree))
    assert previous==10**12-1
    assert worst_pre<Q(742,100)
    assert worst_tagged<Q(6873,1000)
    # At k>=2501 the 1/(15k) saving on a-1 of the original a factors
    # dominates the old BW terminal; ceil(c k)>=100 throughout this range.
    assert Q(249,500)/Q(742,100)>Q(1,15)
    # log(2501)>7.5 follows from e<11/4 and (11/4)^15<2501^2.
    assert (Q(11,4))**15 < 2501**2
    assert Q(99,100)*(Q(15,2)+Q(802113,100000))>15
    assert (Q(21,10)*50)>100
    print('Preliminary normalized order',worst_pre,float(worst_pre))
    print('Largest (S+1)/k at 11<=k<=2500:',worst_tagged,float(worst_tagged))
    print('At k>=2501, the rational final schedule applies with a single ordinary factor.')
    # Check the exact scalar order at all remaining k. The already-proved
    # stronger finite field kernel above 10^12 is additional slack.
    C.main()

if __name__=='__main__':
    main()
