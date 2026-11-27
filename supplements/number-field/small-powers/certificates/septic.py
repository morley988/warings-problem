#!/usr/bin/env python3
"""Self-contained exact verification of the twelve rows printed in the TeX.
All arithmetic is rational; no optimization library or external data is used.
The analytic transformations are established in the article.
"""
from fractions import Fraction as Q
D=100000
b=list(map(lambda x:Q(x,D),[0,100000,200000,306493,426513,559014,
 701542,854214,1015371,1184806,1360673,1542553,1729695,1919477,2111765]))
# s, process, ell, t, phi numerators, certified slack numerator /10^8.
rows=[
(3,'A',1,0,[3196],52177),
(4,'A',2,0,[6818],8692),
(5,'B',2,5,[8699,3541],10185),
(6,'A',2,0,[9641,6937],12539),
(7,'B',2,6,[10564,8803,4059],14896),
(8,'A',2,0,[11203,9889,6902],12594),
(9,'B',2,8,[11874,10797,8946,4151],16152),
(10,'A',2,0,[12330,11453,9898,6609],13579),
(11,'A',2,0,[12805,12028,10870,8586],14177),
(12,'A',2,0,[13252,12659,10684,10188],17123),
(13,'M',0,0,[13392,12953,12116,10714],14754),
(14,'M',0,0,[13559,13070,12326,10846],15886)]
def at(t):
 t=Q(t);assert 0<=t<=14;i=t.numerator//t.denominator
 return b[i] if t==i else b[i]+(t-i)*(b[i+1]-b[i])
for s,kind,ell,t,nums,claimed in rows:
 ph=[Q(x,D)for x in nums];j=len(ph);Phi=[Q(0)]
 for x in ph:Phi.append(Phi[-1]+x)
 q=[1-x for x in Phi];u=s-j
 assert all(0<=x<=Q(1,7)for x in ph)
 assert all(ph[i]>=ph[i+1]for i in range(j-1))
 assert ph[0]>=Q(3,100)
 def kappa(l):
  p=2**l;return p-l+(p-1)*(j-6*Phi[j])
 if kind=='M':
  assert j==4 and 7*q[j]>2
  C=5-6*Phi[4]+max(-Q(1,4)+q[4]*at(u),
                     q[4]*(-Q(7,4)+Q(3,4)*at(Q(4,3)*u)))
 else:
  for I in range(3,j+1):assert Phi[I]+7*(ph[I-2]+ph[I-1])<=2
  p=2**ell
  if kind=='A':
   c=1-Q(1,p);C=kappa(ell)/p+c*q[j]*at(Q(u)/c)
  else:
   c=Q(u,t);a=2*(1-c)-Q(2,p);bb=Q(2,p)-(1-c)
   assert min(a,bb,c)>=0 and a+bb+c==1 and a*(p//2)+bb*p==1
   C=a*kappa(ell-1)+bb*kappa(ell)+c*q[j]*at(t)
 for i in range(j-1,0,-1):
  ui=s-i-1;ti=s-i+1
  Di=1+i-7*Phi[i]+Phi[i+1]+q[i+1]*at(ui)
  Ei=(q[i]*at(ti)+i-6*Phi[i]+(2*ui-1)*ph[i])/2
  C=Ei+max(Di,C)/2
 out=(2*s-3)*ph[0]+max(1+ph[0]+(1-ph[0])*at(s-1),C)
 assert s<out<b[s]<2*s
 slack=b[s]-out
 assert slack>=Q(claimed,10**8)>0
 print(s,'exact row slack =',slack)
assert b[14]==Q(422353,20000)<21+Q(59,500)
assert 24-(Q(6,56)*48+Q(25,28)*(21+Q(59,500)))==Q(1,560)
assert 4-24*Q(59,500)==Q(146,125)
print('VERIFIED: all 12 rows, contraction <=97/100, lambda14 <=21.11765.')
