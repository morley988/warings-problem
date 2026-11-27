"""Finite moments and mixed minor-arc tests, degrees 8 through 20."""
import gzip, json
from bisect import bisect_left
from fractions import Fraction as Q
from functools import lru_cache
from math import ceil
from pathlib import Path

CUTOFFS=(42,50,60,68,76,84,92,100,110,118,128,138,148)
@lru_cache(maxsize=None)
def conductor(k,M,sigma):
    theta=M/k+Q(1,10**6);cells=[]
    for i in range(k-1):
        a=(2**i)*sigma
        if 2*a>1 or (i>0 and theta>1-a):break
        lo=i*theta+2*a
        hi=i+2-(4*a-2*sigma)
        if lo<=hi:cells.append((lo,hi))
    endpoint=Q(1)
    for lo,hi in sorted(cells):
        if lo>endpoint:break
        endpoint=max(endpoint,hi)
    assert endpoint>M

def hull(points):
    nodes=[]
    for x,y in sorted(points):
        while len(nodes)>1:
            a,b=nodes[-2:]
            if (b[1]-a[1])*(x-b[0])<(y-b[1])*(b[0]-a[0]):break
            nodes.pop()
        nodes.append((x,y))
    return nodes

def value(nodes,x):
    j=bisect_left(nodes,(x,))
    if nodes[j][0]==x:return nodes[j][1]
    assert j>0
    (u,a),(v,b)=nodes[j-1:j+1]
    return ((v-x)*a+(x-u)*b)/(v-u)

def verify(v,seed):
    k=v['k'];a=v['a'];s=v['s'];b=s-a;w=k*(k+1)
    cutoff=CUTOFFS[k-8]
    points=[(4,Q(k-2))]+[(u,Q(t)+k-u) for u,t in zip(range(6,6+2*len(seed),2),seed)]
    if k>=17:
        u=(96,104,112,120)[k-17]
        assert cutoff-u>(w-cutoff)*dict(points)[u]
    points.append((cutoff,Q(0)))
    nodes=hull(points);g=v['grid'];r=Q(b*w,w-a)
    curve={Q(i,g):value(nodes,Q(i,g)) for i in range(4*g,ceil(r*g)+1)}
    origin=Q(v['shift']);room=Q(v['room'])
    previous=0
    for order,h,M,z,D in v['rows']:
        u,h,M,z,D=map(Q,(order,h,M,z,D))
        assert u>previous and u>=k+2 and 4<=h<u and 0<origin<M<k and z>0
        conductor(k,M,2*z+room)
        assert max(0,(1-(M-origin)/k)*curve[u-2],curve[h]-(u-h)*z)<=D<curve[u]
        curve[u]=D;previous=u
    excess=value(sorted(curve.items()),r)
    gain=Q(a,w)-(1-Q(a,w))*excess
    assert gain==Q(v['gain']) and gain>0
    annular=Q(a*cutoff,cutoff-b)
    assert cutoff>b and annular>=k+2 and s>=4*k
    print(f"k={k:2d}  s={s:3d}  saving={gain}  rows={len(v['rows'])}")
if __name__=='__main__':
    with gzip.open(Path(__file__).with_name('small_witness.json.gz'),'rt') as f:d=json.load(f)
    assert [r['k'] for r in d['certificates']]==list(range(8,21))
    for r in d['certificates']:verify(r,d['seeds'][str(r['k'])])
