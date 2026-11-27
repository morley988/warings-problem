"""Exact checks for the scalar moment iteration and the linear Waring estimates.

Run with Python 3. The conductors in the compressed witness are integers in
units of 1/B. Floating-point calculations are unnecessary for verification.
"""
import gzip
import json
from fractions import Fraction as Q
from math import isqrt
from pathlib import Path

B = 10000
T = 10**32
DIGITS = 10**16
TAIL_START = 120
DEGREE_CUTOFF = 200
PITCH = 400
ZTOP = 9985 * T // 100000
ZO = Q(ZTOP, T)
RETENTION = Q(99999, 100000)
FILE = Path(__file__).with_name("linear_witness.json.gz")

def ceiling(a, b):
    return -(-a // b)

def outward(x):
    return Q(ceiling(x.numerator * DIGITS, x.denominator), DIGITS)

def logarithm(x):
    """Rational upper enclosure for log(x), x>=1."""
    assert x >= 1
    if x < Q(5, 4):
        t=x-1
        return outward(t-t*t/2+t**3/3)
    n=0
    while x>=2:
        x/=2
        n+=1
    def series(u):
        y=(u-1)/(u+1)
        return 2*(sum((y**(2*j+1))/(2*j+1) for j in range(16))+
                  y**33/(33*(1-y*y)))
    return outward(n*series(Q(2)) + series(x))

def covered(z,m,K,theta_num=None,theta_den=None):
    """Inner coverage with modulus M=m/B, dyadic and Weyl intervals.
       theta=m/(BK) normally. An independent upper bound for theta can
       be passed when proving the semi-infinite band."""
    if m==B: return True
    assert B<m<B*K
    if theta_num is None:
        h,den=m,B*K
    else:
        h,den=theta_num,theta_den
    sigma=ceiling(20001*z,10000)  # sigma/T > 2 z/T.
    common=T*den
    cells=[]
    for j in range(min(40,K-2)+1):
        y=(1<<j)*sigma
        if 2*y>T or (j and h*T>den*(T-y)):break
        low=ceiling(B*(j*h*T+2*y*den),common)
        high=B*((j+2)*T-(4*y-2*sigma))//T
        if low<=high:cells.append((low,high))
    for j in range(2,min(K,DEGREE_CUTOFF)+1):
        t=min(2**(j-1),j*(j-1))*sigma
        if 2*t>T:break
        low=ceiling(B*(j+1)*(t*den+j*h*T),common)
        high=B*min((j+1)*(common-h*T-t*den),
                   j*common-j*h*T-t*den)//common
        if low<=high:cells.append((low,high))
    endpoint=B
    for lo,hi in sorted(cells):
        if lo>endpoint:break
        endpoint=max(endpoint,hi)
        if endpoint>=m:return True
    if theta_num is not None: return False
    F=TAIL_START
    if endpoint < B*F: return False
    # For j=ceil(h U), N=e+f/F, the products are checked after
    # clearing denominators in the three Weyl inequalities.
    for e,f in ((3,2),(7,5),(4,3),(5,4),(6,5),(11,10),(21,20)):
        if e*m+f*B>f*B*K:continue
        N=e*F+f
        # W = sigma*(e/f)*(N/(fF))*M^2; units are exact.
        numer=sigma*e*N*m*m
        denom=T*f*f*F*B**2
        if numer*(e*F+2*f)*f*F*B**2*K > (
            f**2*F**2*B**2*K-N*m*m*(e*F+2*f))*denom:continue
        if numer*e*B*K > ((e-f)*B*K-e*m)*denom:continue
        if numer*f*F*B**2*K > ((e-f)*F**2*B**2*K-N*m*m)*denom:continue
        return True
    return False

def next_height(z):
    return z*PITCH//(PITCH+1)

def check_finite(band):
    K,J,ms = band
    assert 21<=K<=J
    c=min(Q(7,20),Q(21,10*isqrt(K)))
    target=c/(J*(logarithm(Q(J))+Q(81,10)))
    cost=Q(0);z=ZTOP
    assert RETENTION*Q(ms[0],B)>2*(1-ZO)
    for i,m in enumerate(ms):
        assert i==0 or m>=ms[i-1]
        assert covered(z,m,K),(K,i,z,m)
        length=RETENTION*Q(m,B)
        if 2*Q(z,T)/length < target:
            return outward(2+logarithm((1-ZO)/ZO)+cost-2/length+c+Q(6,K))
        zz=next_height(z)
        cost+=outward(2*logarithm(Q(z,zz))/length)
        z=zz
    raise ValueError(("Insufficient rows",K,J))

def check_infinite(K,ms):
    # Every k>=K: H=sqrt(k)/8, m/k<=1/(8 sqrt(K)).
    r=isqrt(K); assert r*r==K
    F=TAIL_START; tau=Q(1,14)
    z=ZTOP; cost=Q(0)
    for i,m in enumerate(ms):
        assert covered(z,m,K,1,8*r),(i,m)
        assert i==0 or ms[i-1]<=m
        length=Q(m,B)*RETENTION
        if i==0: assert length>2*(1-ZO)
        if i==len(ms)-1:break
        zz=next_height(z)
        cost+=outward(2*logarithm(Q(z,zz))/length)
        z=zz
    assert m==F*B
    assert Q(z,T)>=tau/F**2
    h=Q(3,2); b=h+Q(1,F)
    assert 2*tau*h*b < min(1/(h+Q(2,F))-b/64,
                            1-1/h-Q(1,8*r),(h-1)*F-b/64)
    cost+=outward(2*logarithm(Q(z,T)*F**2/tau)/(F*RETENTION))
    cost+=outward(4/(F*RETENTION))
    asym=outward(2+logarithm((1-ZO)/ZO)+cost)
    # a=ceil(16 sqrt(k)), d*=16/(sqrt(k) k(log k+8.1)).
    # The cap starts at normalized defect d_H=2tau/(RETENTION H^3).
    # d_H/d*=(64tau/RETENTION)(log k+8.1).
    # (log(C(log x+8.1)))/sqrt(x) is decreasing here.
    X=64*tau/RETENTION*(logarithm(Q(K))+Q(81,10))
    assert X>8 and K>=10**8
    clipped=outward(16*logarithm(X)/(r*RETENTION))
    total=outward(asym+clipped+Q(16,r)+Q(6,K))
    return total,asym

def main():
    with gzip.open(FILE,'rt',encoding='utf-8') as f:data=json.load(f)
    end=20;all_bounds=[Q(137,20)]
    for band in data["finite"]:
        K,J,_=band
        assert K==end+1
        val=check_finite(band)
        print(K,J,float(val),flush=True)
        all_bounds.append(val);end=J
    K,ms=data["infinite"]
    assert K==end+1
    tail,asym=check_infinite(K,ms)
    all_bounds.append(tail)
    print("Infinite band",K,tail,"asymptotic",asym)
    print("All degrees",max(all_bounds))
    assert max(all_bounds)<Q(6919,1000)
    assert asym<Q(6919,1000)
if __name__=='__main__':main()
