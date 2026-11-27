#!/usr/bin/env python3
"""Exact rational certificate for the uniform tenth-power 55-variable theorem.
The analytic A/B and cubic processes are proved in the accompanying article.
Requires only Python's standard library.
"""
from fractions import Fraction as F
import json

DATA=json.loads(r'''
{"k":10,"b":[
"0", "1", "2", "3028131/1000000", "129901/31250", "5365973/1000000",
"3323309/500000", "7996737/1000000", "4707187/500000", "170228/15625", "3109397/250000", "438663/31250",
"7845711/500000", "8697193/500000", "2392839/125000", "20930391/1000000", "22754051/1000000", "24609057/1000000",
"26489639/1000000", "28391489/1000000", "15155733/500000", "6449299/200000", "8548479/250000", "36152339/1000000"
],"rows":[
{"s": 3, "j": 1, "kind": "A", "l": 1, "t": null, "elimination": null, "phi_q": ["140570369/10000000000"]},
{"s": 4, "j": 1, "kind": "A", "l": 2, "t": null, "elimination": null, "phi_q": ["43305479/1000000000"]},
{"s": 5, "j": 2, "kind": "A", "l": 1, "t": null, "elimination": null, "phi_q": ["68023071/1250000000", "41410159/10000000000"]},
{"s": 6, "j": 2, "kind": "B", "l": 2, "t": 6, "elimination": null, "phi_q": ["605612047/10000000000", "93705547/2500000000"]},
{"s": 7, "j": 2, "kind": "A", "l": 2, "t": null, "elimination": null, "phi_q": ["163502499/2500000000", "524575413/10000000000"]},
{"s": 8, "j": 3, "kind": "B", "l": 2, "t": 7, "elimination": null, "phi_q": ["139136119/2000000000", "613706039/10000000000", "360453041/10000000000"]},
{"s": 9, "j": 3, "kind": "A", "l": 2, "t": null, "elimination": null, "phi_q": ["729186953/10000000000", "83362213/1250000000", "515008069/10000000000"]},
{"s": 10, "j": 4, "kind": "A", "l": 2, "t": null, "elimination": [3, 2, 1, 0], "phi_q": ["764197749/10000000000", "17857641/250000000", "312565769/5000000000", "91973821/2500000000"]},
{"s": 11, "j": 4, "kind": "A", "l": 2, "t": null, "elimination": [3, 2, 1, 0], "phi_q": ["24778203/312500000", "751066453/10000000000", "136372043/2000000000", "2624147/50000000"]},
{"s": 12, "j": 5, "kind": "A", "l": 2, "t": null, "elimination": [4, 3, 2, 1, 0], "phi_q": ["821575941/10000000000", "784217893/10000000000", "366550181/5000000000", "317438187/5000000000", "75219727/2000000000"]},
{"s": 13, "j": 5, "kind": "A", "l": 2, "t": null, "elimination": [4, 3, 2, 1, 0], "phi_q": ["423033453/5000000000", "813159149/10000000000", "384001839/5000000000", "138801669/2000000000", "104722983/2000000000"]},
{"s": 14, "j": 6, "kind": "B", "l": 2, "t": 11, "elimination": [5, 4, 3, 2, 1, 0], "phi_q": ["5434847/62500000", "839775001/10000000000", "802641957/10000000000", "186585929/2500000000", "39979059/625000000", "91495767/2500000000"]},
{"s": 15, "j": 6, "kind": "A", "l": 2, "t": null, "elimination": [5, 4, 3, 2, 1, 0], "phi_q": ["889297053/10000000000", "431544313/5000000000", "828979911/10000000000", "195216913/2500000000", "694894303/10000000000", "501213907/10000000000"]},
{"s": 16, "j": 6, "kind": "B", "l": 3, "t": 13, "elimination": [5, 4, 3, 2, 1, 0], "phi_q": ["908150303/10000000000", "442340377/5000000000", "428245931/5000000000", "816741897/10000000000", "725992797/10000000000", "623513161/10000000000"]},
{"s": 17, "j": 7, "kind": "A", "l": 2, "t": null, "elimination": [6, 5, 4, 3, 2, 1, 0], "phi_q": ["924732191/10000000000", "905239739/10000000000", "44092667/500000000", "809797191/10000000000", "359909863/5000000000", "159959939/2500000000", "435846503/10000000000"]},
{"s": 18, "j": 7, "kind": "M", "phi_q": ["46884441/500000000", "921700817/10000000000", "901785377/10000000000", "7022689/80000000", "169805397/2000000000", "810067149/10000000000", "3/40"]},
{"s": 19, "j": 7, "kind": "M", "phi_q": ["237069431/2500000000", "467101251/5000000000", "229193249/2500000000", "894167027/10000000000", "864420747/10000000000", "411025271/5000000000", "749999999/10000000000"]},
{"s": 20, "j": 7, "kind": "M", "phi_q": ["957456777/10000000000", "472391183/5000000000", "92891887/1000000000", "453984069/5000000000", "219499799/2500000000", "831665711/10000000000", "3/40"]},
{"s": 21, "j": 7, "kind": "M", "phi_q": ["482542133/5000000000", "190782771/2000000000", "58697777/625000000", "459559601/5000000000", "889387537/10000000000", "840231609/10000000000", "3/40"]},
{"s": 22, "j": 7, "kind": "M", "phi_q": ["971360897/10000000000", "19229607/200000000", "189585673/2000000000", "92841029/1000000000", "449184893/5000000000", "84707757/1000000000", "3/40"]},
{"s": 23, "j": 7, "kind": "M", "phi_q": ["977371993/10000000000", "484347571/5000000000", "957224127/10000000000", "940589327/10000000000", "914812231/10000000000", "217890059/2500000000", "395818973/5000000000"]}
]}
''')

def interp(b,t):
 t=F(t);assert 0<=t<=len(b)-1
 i=t.numerator//t.denominator
 return b[i] if t==i else (i+1-t)*b[i]+(t-i)*b[i+1]

def exact(k,b,r):
 S=r['s'];j=r['j'];phi=list(map(F,r['phi_q']));total=sum(phi);q=1-total;at=lambda t:interp(b,t)
 assert all(0<f<F(1,k) for f in phi)
 assert all(phi[i]<=1-sum(phi[:i])for i in range(j))
 u=S-j
 if r['kind']=='M':
  assert j==k-3 and k*q>2
  amp=1+j+(1-k)*total
  C=max(amp-F(1,4)+q*at(u),amp+q*(-F(k,4)+F(3,4)*at(F(4*u,3))))
 else:
  l=r['l'];p=2**l;assert 1<=l<=3 and 1<=j<=k-1-l
  used=[l] if r['kind']=='A' else [l-1,l]
  for order in used:
   for appended in range(order):
    residual=k-j-appended;assert residual>=2
    if j!=1 and residual%2==0 and residual>=6:assert total<=F(1,3)
  J=(k-j-l+1)//2
  if r['elimination'] is None:assert j<=J+1
  else:
   assert r['elimination']==list(range(j-1,-1,-1))
   for i in range(j):assert sum(phi[:i+1])+(k-2)*phi[i]<=1
  def kap(ell):pp=2**ell;return pp-ell+(pp-1)*(j+(1-k)*total)
  if r['kind']=='A':
   c=1-F(1,p);C=kap(l)/p+c*q*at(F(u)/c)
  else:
   t=r['t'];c=F(u,t);a=2*(1-c)-F(2,p);bb=F(2,p)-(1-c)
   assert min(a,bb,c)>=0 and a+bb+c==1 and a*(p//2)+bb*p==1
   C=a*kap(l-1)+bb*kap(l)+c*q*at(t)
 for i in range(j-1,0,-1):
  pre=sum(phi[:i]);ui=S-i-1;ti=S-i+1
  E=(i+(1-k)*pre+(2*ui-1)*phi[i]+(1-pre)*at(ti))/2
  D=i+1+(1-k)*pre+phi[i]+(1-pre-phi[i])*at(ui)
  C=E+max(D,C)/2
 out=(2*S-3)*phi[0]+max(1+phi[0]+(1-phi[0])*at(S-1),C)
 assert max(S,2*S-k)<=out<b[S],(S,float(out),float(b[S]))
 return out

def verify():
 k=DATA['k'];b=list(map(F,DATA['b']));assert k==10
 assert b[:3]==list(map(F,(0,1,2)))
 assert [r['s']for r in DATA['rows']]==list(range(3,24))
 slacks=[];phi1=[]
 for r in DATA['rows']:
  result=exact(k,b,r);slacks.append(b[r['s']]-result);phi1.append(F(r['phi_q'][0]))
 assert min(slacks)==F(65679537093,40000000000000000)>0
 assert 1-min(phi1)==F(9859429631,10000000000)<1
 assert b[22]==F(34193916,1000000)<F(34227,1000)
 delta=b[23]-36;assert delta==F(152339,1000000)
 margin=56-46-(110-56)*delta
 assert margin==F(886847,500000)>0
 a,bb,c=F(3,22),F(46,55),F(3,110)
 assert a+bb+c==1 and 110*a==15 and 46*bb+56*c==40
 saving=a-bb*delta
 assert saving==F(246203,27500000)>0
 assert F(15)/(1-F(40,56))==F(105,2)>20
 print('21 exact seed rows passed.')
 print('Minimum supersolution slack:',min(slacks))
 print('Contraction at most:',1-min(phi1))
 print('Full 44th-moment exponent:',b[22])
 print('Delta46:',delta)
 print('Bootstrap margin:',margin)
 print('Minor-arc saving:',saving)
 print('Analytic conclusion: 55 variables, uniformly over number fields.')

if __name__=='__main__':verify()
