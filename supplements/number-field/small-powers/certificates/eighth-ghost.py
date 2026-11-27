#!/usr/bin/env python3
"""Finite algebra certificate for the seven-root eighth-power chart.

Checks all 64 binary polynomials modulo T^6 and eight carry relations in
the injective combined ghost model for W4(F2[[T]])/I_(2,4,6,6).
No local-field sampling or floating-point arithmetic is used.
"""
from itertools import product
from pathlib import Path
import hashlib,json

N=(2,4,6,6)
ROOTS=((1,0,0,0,0,0),(1,0,0,0,0,1),(1,0,0,0,1,0),
       (1,0,0,1,0,0),(1,0,1,0,0,0),(1,1,0,0,0,0),
       (0,1,0,0,0,0),(0,1,1,0,0,0))
ORDERS=(16,2,2,2,2,4,4,2)

def mul(a,b):
    z=[0]*6
    for i,x in enumerate(a):
        for j,y in enumerate(b[:6-i]):z[i+j]=(z[i+j]+x*y)%16
    return z

def ghost(root):
    p=list(root);out=[]
    for j,n in enumerate(N):
        out.extend((x*(1<<(3-j)))%16 for x in p[:n])
        p=mul(p,p)
    return tuple(out)

def add(x,y):return tuple((a+b)%16 for a,b in zip(x,y))
def scale(c,x):return tuple(c*a%16 for a in x)

def main():
    gens=[ghost(x) for x in ROOTS]
    normal={tuple([0]*sum(N)):()};carries=[]
    for i,(g,o) in enumerate(zip(gens,ORDERS)):
        carry=scale(o,g)
        assert carry in normal, ('carry failure',i,carry)
        carries.append({'generator_index':i,'multiple':o,'earlier_coefficients':normal[carry]})
        expanded={}
        for v,coeffs in normal.items():
            for c in range(o):
                w=add(v,scale(c,g))
                assert w not in expanded,('normal form collision',i)
                expanded[w]=coeffs+(c,)
        normal=expanded
    witnesses=[]
    for root in product(range(2),repeat=6):
        v=ghost(root);assert v in normal,('power image missing',root)
        c=normal[v]
        check=tuple([0]*sum(N))
        for n,g in zip(c,gens):check=add(check,scale(n,g))
        assert check==v
        witnesses.append({'root_coefficients':root,'positive_generator_coefficients':c})
    out={'weights':N,'generator_roots':ROOTS,'generator_vectors':gens,
         'cyclic_quotient_orders':ORDERS,'carry_relations':carries,
         'normal_form_count':len(normal),'positive_coefficient_budget':sum(o-1 for o in ORDERS),
         'all_binary_roots_checked':len(witnesses),'witnesses':witnesses,
         'status':'all exact identities and carry relations passed'}
    path=Path(__file__).with_suffix('.json')
    path.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:out[k] for k in ('normal_form_count','positive_coefficient_budget','all_binary_roots_checked','status')}))
    print('carry relations',carries)
    print('sha256',hashlib.sha256(path.read_bytes()).hexdigest())

if __name__=='__main__':main()
