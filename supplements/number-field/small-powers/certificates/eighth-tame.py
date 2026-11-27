#!/usr/bin/env python3
"""Exact primitive eighth-power certificate in Z2[pi], pi^5=2.

The target quotient is A/(16*pi) = Z/32 + (Z/16)pi + ... + (Z/16)pi^4.
Eighth powers depend only on roots modulo2*pi, so all64 root classes
are checked. Ordinary width21 upgrades to primitive width22 by applying
the result to target minus1 and appending the unit root1.
"""
from collections import Counter,deque
from itertools import product
from pathlib import Path
import hashlib,json

MOD=(32,16,16,16,16)

def mul(x,y):
    z=[0]*9
    for i,a in enumerate(x):
        for j,b in enumerate(y):z[i+j]+=a*b
    for i in range(8,4,-1):z[i-5]+=2*z[i]
    return tuple(z[i]%MOD[i] for i in range(5))

def add(x,y):return tuple((a+b)%m for a,b,m in zip(x,y,MOD))

def main():
    roots=[(a,)+b for a in range(4) for b in product(range(2),repeat=4)]
    image={}
    for r in roots:
        x=r
        for _ in range(3):x=mul(x,x)
        image.setdefault(x,r)
    generators=sorted(image)
    zero=(0,)*5;dist={zero:0};parent={};queue=deque([zero])
    while queue:
        x=queue.popleft()
        for j,g in enumerate(generators):
            y=add(x,g)
            if y not in dist:
                dist[y]=dist[x]+1;parent[y]=(x,j);queue.append(y)
    for y,(x,j) in parent.items():
        assert add(x,generators[j])==y and dist[y]==dist[x]+1
    for x in dist:
        for g in generators:assert add(x,g) in dist
    assert len(dist)==8192 and max(dist.values())==21
    serialized=json.dumps(sorted((list(x),d) for x,d in dist.items()),separators=(',',':')).encode()
    result={'minimal_polynomial':'X^5-2','root_modulus':'2*pi','target_modulus':'16*pi',
            'root_classes_checked':len(roots),'distinct_power_images':len(generators),
            'generators':[{'value':g,'root':image[g]} for g in generators],
            'generated_group_order':len(dist),'ordinary_width':max(dist.values()),
            'primitive_bound':max(dist.values())+1,'distance_histogram':dict(sorted(Counter(dist.values()).items())),
            'distance_table_sha256':hashlib.sha256(serialized).hexdigest(),
            'checks':['all64rootclasses','exactringarithmetic','allparentwitnesses','closureunderallgenerators'],
            'status':'passed'}
    path=Path(__file__).with_suffix('.json');path.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='generators'},indent=2))

if __name__=='__main__':main()
