"""Limiting coefficient after arithmetic A- and B-processes, exact rationals."""
from fractions import Fraction as Q
DIGITS = 10**16

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



B=10**6
T=10**32
F=300
PITCH=1000
DEPTH=14
RET=Q(99999,100000)
TAU=Q(1,14)

def exponents():
    """All pairs obtained with at most DEPTH applications of A,B."""
    half=Q(1,2)
    seen={(half,half)}; frontier=seen.copy()
    for _ in range(DEPTH):
        batch=set()
        for x,y in frontier:
            batch.add((x/(2+2*x),(x+y+1)/(2+2*x)))
            batch.add((y-half,x+half))
        frontier=batch-seen;seen|=batch
    return [(x.numerator,x.denominator,y.numerator,y.denominator)
            for x,y in seen if x]

def admissible(z,ps):
    # At amplitude z, the strict Gram threshold is 2z.
    sigma=ceiling(200001*z,100000)
    endpoint=max([B]+[B+B*q*((s-r)*T-s*sigma)//(s*p*T) for p,q,r,s in ps])
    cells=[]
    for j in range(2,2*F+2):
        t=min(1<<(j-1),j*(j-1))*sigma
        if 2*t>T:break
        lo=ceiling(B*(j+1)*t,T)
        hi=B*min((j+1)*(T-t),j*T-t)//T
        if lo<=hi:cells.append((lo,hi))
    for lo,hi in sorted(cells):
        if lo>endpoint:break
        endpoint=max(endpoint,hi)
    return min(F*B,endpoint)

def main():
    ps=exponents(); z0=Q(107,1000); z=int(T*z0);cost=Q(0);previous=B
    for i in range(30000):
        m=admissible(z,ps);assert m>=previous;previous=m
        L=Q(m,B)*RET
        if i==0: assert L>2*(1-z0)
        if m==F*B:break
        zz=z*PITCH//(1+PITCH)
        cost+=outward(2*logarithm(Q(z,zz))/L)
        z=zz
    assert m==F*B and Q(z,T)*F**2>TAU
    h=Q(3,2);b=h+Q(1,F)
    assert 2*TAU*h*b<min(1/(h+Q(2,F))-b/64,Q(1,3),(h-1)*F-b/64)
    cost+=outward(2*logarithm(Q(z,T)*F**2/TAU)/(F*RET))+outward(4/(F*RET))
    C=outward(2+logarithm((1-z0)/z0)+cost)
    print(f"{len(ps)} exponent pairs, {i+1} height levels, rational ceiling {C} = {float(C):.12f}",flush=True)
    assert C == Q(34360293397827451, 5000000000000000)
if __name__=='__main__':main()
