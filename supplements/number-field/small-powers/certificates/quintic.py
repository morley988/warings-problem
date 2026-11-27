#!/usr/bin/env python3
"""Exact six-row fifth-power smooth-moment supersolution.
Analytic prerequisites: fundamental field differencing, auxiliary L2/L4,
sharp cubic coefficient dissection, and degree-ten mu44 <= 34.227.
Only fractions.Fraction is used for verification.
"""
from fractions import Fraction as F
import json

B=[F(0),F(1),F(2)]+list(map(F,['3.1364','4.4389','5.9254','7.5422','9.2726','11.0764']))
ROWS=[
 (3,'A',1,1,[68130]),
 (4,'A',1,2,[105600]),
 (5,'A',2,2,[136590,72270]),
 (6,'A',2,2,[151340,113110]),
 (7,'E',2,6,[163790,139365,139360]),
 (8,'E',2,6,[169960,138337,138330]),
]
MU=F('34.227')

def at(vals,x):
 x=F(x)
 i=x.numerator//x.denominator
 if i==len(vals)-1:return vals[i]
 assert 0<=i<len(vals)-1
 return vals[i]+(x-i)*(vals[i+1]-vals[i])

def row_value(vals,row):
 S,kind,j,ell,raw=row
 ph=[F(x,10**6)for x in raw]
 if kind=='A':
  assert all(0<x<=F(1,5)for x in ph)
  assert all(ph[i]>=ph[i+1]for i in range(j-1))
  cum=[F(0)]
  for x in ph:cum.append(cum[-1]+x)
  p=2**ell;b=F(p-1,p);r=S-j
  C=F(p-ell+(p-1)*j,p)+F((p-1)*(1-5),p)*cum[j]+b*at(vals,F(r)/b)*(1-cum[j])
  for i in range(j-1,0,-1):
   u=S-i-1;t=S-i+1
   D=1+i-5*cum[i]+cum[i+1]+at(vals,u)*(1-cum[i+1])
   P=(at(vals,t)*(1-cum[i])+i-4*cum[i]+(2*u-1)*ph[i])/2
   C=P+max(D,C)/2
  return max(1+ph[0]+at(vals,S-1)*(1-ph[0]),C)+(2*S-3)*ph[0]
 theta,phi,u=ph;r=ell
 assert F(1,15)<=theta<=F(1,5) and 0<phi<=theta
 assert phi<5*theta-F(1,3)
 assert 0<u<phi and u<-1-5*theta+15*phi
 assert 4*u+theta+phi<1 and 6*u+5*theta+24*phi<5
 rho=(1+F(21,22)*u+(F(1,3)+(34-MU)*theta)/22)/4
 assert rho<F(1,3)
 q=1-theta-phi;t=2*(S-1)-r
 P=(at(vals,t)*(1-theta)+1-4*theta+(2*r-1)*phi)/2
 D=2-4*theta+phi+at(vals,r)*q
 C=3-4*(theta+phi)+max(-rho+at(vals,r)*q,(-F(5,4)+F(3,4)*at(vals,F(4*r,3)))*q)
 return max(1+at(vals,S-1)+(2*S-2-at(vals,S-1))*theta,(2*S-3)*theta+P+max(D,C)/2)

def verify():
 outs=[row_value(B,row)for row in ROWS]
 for row,out in zip(ROWS,outs):assert out<B[row[0]],(row[0],float(out),float(B[row[0]]))
 contraction=F(94,100)
 assert all(1-F(row[4][0],10**6)<contraction for row in ROWS)
 # Every branch has total variable coefficient <=1-theta;
 # see the accompanying proof. All coefficients are nonnegative.
 Delta=B[8]-11
 assert Delta<F(1,13)
 saving=(1-13*Delta)/14
 assert saving>0 and 2-12*Delta>0
 print(json.dumps(dict(status='VERIFIED',rows=[dict(s=row[0],kind=row[1],parameters=row[4],bound=str(B[row[0]]),output=str(out),slack=str(B[row[0]]-out))for row,out in zip(ROWS,outs)],contraction=str(contraction),joint16=str(B[8]),Delta16=str(Delta),minor_saving=str(saving),bootstrap18_margin=str(2-12*Delta)),indent=2))
if __name__=='__main__':verify()
