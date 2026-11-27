"""Exact finite-degree checks for the arithmetic exponent-pair improvement."""
from fractions import Fraction as Q
from pathlib import Path
from math import isqrt
import gzip,json
import linear_verify as V

def noproblem(coeff):
    a,b=coeff
    assert a or b
    return not a or (-b)%a or (-b)//a<21

def parameters(word):
    h=Q(1,2); x=y=D=h
    for op in word:
        if op=='A':x,y,D=x/(2+2*x),(x+y+1)/(2+2*x),max(h,(D+1)/2)
        else:
            assert op=='B';x,y,D=y-h,x+h,D+1+y-h
    # The fraction e/d is the model phase exponent. Each operation on a
    # sum uses the last letter first. Test the possible exceptional k.
    d=(0,1);e=(1,0)
    for op in reversed(word):
        a=(e[0]-d[0],e[1]-d[1])
        assert all(noproblem(t) for t in (d,e,a)),word
        if op=='A':e=a
        else:d=a
    a=(e[0]-d[0],e[1]-d[1])
    assert all(noproblem(t) for t in (d,e,a)),word
    return x,y,1+D

def pair_ok(z,m,K,row,theta=None):
    x,y,c=row
    t=Q(m,V.B*K) if theta is None else theta
    return 1-y+x-x*Q(m,V.B)-c*t>=Q(V.ceiling(20001*z,10000),V.T)

WORDS=Path(__file__).with_name('exponent_words.txt').read_text().split()
PAIRS=[parameters(w.replace('-','')) for w in WORDS]

def ztop(K):
    z=max([V.ZO]+[min(Q(107,1000),
            (1-y-x-2*c/K)/(2*(1-x-c/K))-Q(1,1000))
          for x,y,c in PAIRS if x+c/K<1])
    return max(V.ZO,Q(int(100000*z),100000))

def run(band):
    K,J,entries=band
    z0=ztop(K);z=int(z0*V.T)
    assert V.Q(entries[0][0],V.B)*V.RETENTION>2*(1-z0)
    c=min(Q(7,20),Q(21,10*isqrt(K)))
    target=c/(J*(V.logarithm(Q(J))+Q(81,10)))
    cost=Q(0);past=V.B
    for m,index in entries:
        assert past<=m<V.B*K;past=m
        assert (V.covered(z,m,K) if index<0 else pair_ok(z,m,K,PAIRS[index]))
        L=V.RETENTION*Q(m,V.B)
        if 2*Q(z,V.T)/L<target:
            return V.outward(2+V.logarithm((1-z0)/z0)+cost-2/L+c+Q(6,K))
        zz=V.next_height(z)
        cost+=V.outward(2*V.logarithm(Q(z,zz))/L)
        z=zz
    raise ValueError(K)

def infinite(K,rows):
    assert isqrt(K)**2==K
    z0=Q(107,1000);z=int(z0*V.T);past=V.B;cost=Q(0)
    l=V.TAIL_START;tau=Q(1,14)
    theta=Q(1,8*isqrt(K))
    for i,(m,index) in enumerate(rows):
        assert m>=past;past=m
        if index<0:
            assert V.covered(z,m,K,theta.numerator,theta.denominator)
        else:
            assert pair_ok(z,m,K,PAIRS[index],theta)
        L=V.RETENTION*Q(m,V.B)
        if i==0: assert L>2*(1-z0)
        if i+1==len(rows):break
        zz=V.next_height(z)
        cost+=V.outward(2*V.logarithm(Q(z,zz))/L);z=zz
    assert m==l*V.B and Q(z,V.T)*l**2>tau
    h=Q(3,2);b=h+Q(1,l)
    assert 2*tau*h*b<min(1/(h+Q(2,l))-b/64,1-1/h-theta,(h-1)*l-b/64)
    cost+=V.outward(2*V.logarithm(Q(z,V.T)*l**2/tau)/(l*V.RETENTION))
    cost+=V.outward(4/(l*V.RETENTION))
    C=V.outward(2+V.logarithm((1-z0)/z0)+cost)
    X=64*tau/V.RETENTION*(V.logarithm(Q(K))+Q(81,10))
    assert X>8 and K>=10**8
    return V.outward(C+16*V.logarithm(X)/(isqrt(K)*V.RETENTION)+Q(16,isqrt(K))+Q(6,K)),C

def main():
    p=Path(__file__).with_name('dual_witness.json.gz')
    with gzip.open(p,'rt') as f:w=json.load(f)
    end=20;upper=Q(137,20);with_one=Q(137,20)
    for row in w['finite']:
        k,j,_=row;assert k==end+1
        c=run(row);upper=max(upper,c);with_one=max(with_one,c+Q(1,k));end=j
        print(k,j,float(c),flush=True)
    K,rows=w['infinite'];assert K==end+1
    last,asym=infinite(K,rows);upper=max(upper,last);with_one=max(with_one,last+Q(1,K))
    print('All degrees',upper,'large degrees',last,'limiting',asym)
    print('With one extra summand at k>=21',with_one)
    assert upper<Q(6874,1000) and with_one<Q(6874,1000)
if __name__=='__main__':main()
