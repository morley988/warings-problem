"""Finite, field-uniform upper bound for all k >= 10^12, using the ordinary
number-field Weyl exponent 1/(k(k-1)). Arithmetic is exact throughout."""
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

ROOT=10**6
K=ROOT**2

def admissible(z,pairs):
    # The same radical bound works at every modulus up to sqrt(k)/8.
    den=8*ROOT
    sigma=ceiling(200001*z,100000)
    endpoint=max([B]+[
        B+B*q*((s-r)*T*den-s*(sigma*den+2*T))//(s*p*T*den)
        for p,q,r,s in pairs])
    cells=[]
    for j in range(2,2*F+2):
        t=min(1<<(j-1),j*(j-1))*sigma
        if 2*t>T: break
        lo=ceiling(B*(j+1)*(t*den+j*T),T*den)
        hi=min(B*(j+1)*((T-t)*den-T)//(T*den),
               B*((j*T-t)*den-j*T)//(T*den))
        if lo<=hi: cells.append((lo,hi))
    for lo,hi in sorted(cells):
        if lo>endpoint: break
        endpoint=max(endpoint,hi)
    return min(F*B,endpoint)

def main():
    assert K>2**15 and F<ROOT//8
    pairs=exponents()
    z0=Q(107,1000);z=int(z0*T);cost=Q(0);past=B
    for i in range(30000):
        m=admissible(z,pairs)
        assert past<=m
        past=m
        L=RET*Q(m,B)
        if i==0: assert L>2*(1-z0)
        if m==F*B: break
        nz=z*PITCH//(PITCH+1)
        cost+=outward(2*logarithm(Q(z,nz))/L)
        z=nz
    assert m==F*B and Q(z,T)*F**2>TAU
    h=Q(3,2);b=h+Q(1,F)
    assert 2*TAU*h*b<min(1/(h+Q(2,F))-b/64,
                           1-1/h-Q(1,8*ROOT),(h-1)*F-b/64)
    base=outward(2+logarithm((1-z0)/z0)+cost+
           outward(2*logarithm(Q(z,T)*F**2/TAU)/(F*RET))+
           outward(4/(F*RET)))
    cap=outward(Q(16,ROOT)/RET*logarithm(128*TAU*K/RET))
    answer=outward(base+cap+Q(16,ROOT)+Q(16,K))
    print('levels',i+1,'uniform envelope',base,'cap',cap,
          'total',answer,'=',float(answer),flush=True)
    assert answer<Q(6873,1000)
if __name__=='__main__': main()
