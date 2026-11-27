"""Exact replay of the eight sixth-power exponent inequalities.

The analytic transformations are established in the article; this program
verifies their finite rational inequalities.
"""
from fractions import Fraction as F
from pathlib import Path
import json

ROWS = [
    (3, [], (1, 1), F(8), [4545]),
    (4, [], (2, 2), F(8), [8333]),
    (5, [5], (1, 2), F(10), [10673, 5080]),
    (6, [6], (2, 2), F(32, 3), [11855, 8751]),
    (7, [7, 6], (1, 2), F(12), [12981, 10763, 5551]),
    (8, [8, 7], (2, 2), F(40, 3), [13784, 12076, 8562]),
    (9, [9, 8, 8], (1, 1), F(16), [14593, 13194, 10858, 1059]),
    (10, [10, 9, 9], (1, 2), F(18), [15303, 14283, 12101, 6908]),
]
B = {r: F(v) for r, v in zip(range(6, 21, 2),
     ['3.0915','4.334','5.726','7.233','8.852','10.562','12.356','14.220'])}

def mu(x, values):
    if x == 4:
        return F(2)
    if x == F(32, 3):
        return (2*values[10] + values[12])/3
    if x == F(40, 3):
        return (values[12] + 2*values[14])/3
    return values[int(x)]

def update(row, values):
    S, path, (l1, l2), u, integers = row
    phi = [F(0)] + [F(z, 100000) for z in integers]
    d = len(integers)
    Phi = [sum(phi[:j+1]) for j in range(d+1)]
    q = [1-v for v in Phi]
    s = [None, S-1]
    for t in path:
        s.append(2*s[-1]-t)
    c = 2*s[d]/u
    if l1 == l2:
        a, b = F(1, 2**l1), F(0)
    else:
        b = (1-2**l1*(1-c))/(2**l2-2**l1)
        a = 1-b-c
    assert a+b+c == 1 and 2**l1*a + 2**l2*b == 1
    assert min(a,b,c) >= 0
    def A(l):
        return (2**l-l+(2**l-1)*d-5*(2**l-1)*Phi[d]
                +(Phi[d] if d+l == 6 else 0))
    T = a*A(l1)+b*A(l2)+c*q[d]*mu(u, values)
    for j in range(d-1, 0, -1):
        t = path[j-1]
        p = 2*s[j]-t
        diag = 1+j-6*Phi[j]+Phi[j+1]+mu(2*p,values)*q[j+1]
        T = (mu(2*t,values)*q[j]+j-5*Phi[j]
             +(2*p-1)*phi[j+1]+max(diag,T))/2
    outer_diag = 1+2*(S-1)*phi[1]+mu(2*(S-1),values)*q[1]
    candidate = max(outer_diag,(2*S-3)*phi[1]+T)
    side = [Phi[I]+6*(phi[I-1]+phi[I]) for I in range(3,d+1)]
    assert all(z < 2 for z in side)
    return candidate, side, (a,b,c)

def main():
    ledger=[]
    largest=F(0)
    for row in ROWS:
        r=2*row[0]
        result, side, weights=update(row,B)
        slack=B[r]-result
        assert slack > 0
        largest=max([largest]+side)
        ledger.append({'order':r,'b':str(B[r]),'T_b':str(result),
                       'T_b_decimal':format(float(result),'.12f'),
                       'slack':str(slack),'holder_weights':list(map(str,weights)),
                       'terminal_side_conditions':list(map(str,side))})
        print(r, format(float(result),'.12f'), 'slack', str(slack))
    initial={r:F(v) for r,v in zip(range(6,21,2),
        ['3.5','5','6.75','8.5','10.25','12','13.875','15.75'])}
    assert max(initial[r]-B[r] for r in B) == F('1.53')
    # The sup-norm contraction is proved analytically branch by branch;
    # here verify the advertised finite bound after 79 simultaneous rounds.
    bound=B[20]+F('1.53')*F(23,25)**79
    assert bound < F(14)+F(2,9)
    report={'certificate':'Sixth-power rational inequalities',
            'rows':ledger,'largest_terminal_condition':str(largest),
            'contraction_upper_bound':'23/25',
            '79_round_order20_bound':str(bound),
            '79_round_order20_decimal':float(bound),
            'target':'14+2/9'}
    Path(__file__).with_suffix('.json').write_text(json.dumps(report,indent=2)+'\n')
    print('largest condition',float(largest))
    print('79-round upper bound',float(bound))

if __name__ == '__main__':
    main()

# The chronological conditions for the common auxiliary lemma.
for row in ROWS:
    phi=[F(v,100000) for v in row[-1]]
    assert all(sum(phi[:i+1])+4*phi[i]<=1 for i in range(len(phi)))
