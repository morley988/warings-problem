"""Uniform coefficient using a finite-radical lift of the depth-fourteen menu."""
from fractions import Fraction as Q
from pathlib import Path
import gzip
import json
from asymptotic_verify import B, T, F, PITCH, RET, TAU, exponents
from linear_verify import ceiling, logarithm, outward
import dual_verify

# Up to 300, this single upper bound applies to the squarefree radical's
# exponent throughout the last degree band. Each accepted word has D<=1.
ROOT = 180000
K = ROOT**2
DEN = 8*ROOT
NUM = 1

def admissible(z, pairs):
    sigma=ceiling(200001*z,100000)
    endpoint=max([B]+[
        B+B*q*((s-r)*T*DEN-s*(sigma*DEN+2*NUM*T))//(s*p*T*DEN)
        for p,q,r,s in pairs])
    cells=[]
    for j in range(2,2*F+2):
        t=min(1<<(j-1),j*(j-1))*sigma
        if 2*t>T:break
        lo=ceiling(B*(j+1)*(t*DEN+j*NUM*T),T*DEN)
        hi=min(B*(j+1)*((T-t)*DEN-NUM*T)//(T*DEN),
               B*((j*T-t)*DEN-j*NUM*T)//(T*DEN))
        if lo<=hi:cells.append((lo,hi))
    for lo,hi in sorted(cells):
        if lo>endpoint:break
        endpoint=max(endpoint,hi)
    return min(F*B,endpoint)

def tail():
    pairs=exponents()
    # A and B act on the model exponent by unimodular integral maps of
    # sup norm at most 2. A row, or difference of rows, has coefficients
    # bounded by 2**15, hence no exceptional positive degree reaches K.
    assert K>2**15
    z0=Q(107,1000);z=int(T*z0);cost=Q(0);previous=B
    for i in range(30000):
        m=admissible(z,pairs);assert m>=previous;previous=m
        length=RET*Q(m,B)
        if i==0:assert length>2*(1-z0)
        if m==F*B:break
        zz=z*PITCH//(PITCH+1)
        cost+=outward(2*logarithm(Q(z,zz))/length);z=zz
    assert m==F*B and Q(z,T)*F**2>TAU
    h=Q(3,2);b=h+Q(1,F)
    assert 2*TAU*h*b<min(1/(h+Q(2,F))-b/64,1-1/h-Q(1,8*ROOT),(h-1)*F-b/64)
    cost+=outward(2*logarithm(Q(z,T)*F**2/TAU)/(F*RET))+outward(4/(F*RET))
    C=outward(2+logarithm((1-z0)/z0)+cost)
    X=64*TAU/RET*(logarithm(Q(K))+Q(81,10)); assert X>8
    return outward(C+16*logarithm(X)/(ROOT*RET)+Q(16,ROOT)+Q(7,K))

def main():
    with gzip.open(Path(__file__).with_name('dual_witness.json.gz'),'rt') as f:rows=json.load(f)['finite']
    previous=20;upper=Q(137,20)
    for row in rows:
        low,high,_=row;assert low==previous+1
        upper=max(upper,dual_verify.run(row)+Q(1,low));previous=high
        if high>=K-1:break
    assert previous>=K-1
    end=tail();total=max(upper,end)
    print('Finite',upper,'large degrees',end,'uniform with the additional summand',total,
          '=',float(total),flush=True)
    assert total<Q(6873,1000)

if __name__=='__main__':main()
