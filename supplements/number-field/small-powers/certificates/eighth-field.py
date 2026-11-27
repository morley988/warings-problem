#!/usr/bin/env python3
"""Exact certificate; all analytic premises are proved in the manuscript."""
from fractions import Fraction as F
import json

SEEDS={
8:([0, 1000000, 2000000, 3046989, 4216499, 5491581, 6856667, 8310610, 9842873, 11452921, 13128318, 14866494, 16656149, 18490145, 20362923, 22269027, 24200341, 26150576, 28115091, 30089898, 32072146],[
(3, 'A', 1, 0, [234903730], False),
(4, 'A', 2, 0, [574019066], False),
(5, 'A', 1, 0, [727052915, 221429275], False),
(6, 'A', 2, 0, [809783242, 562805614], False),
(7, 'B', 2, 7, [882581976, 734440434, 263392407], False),
(8, 'A', 2, 0, [935533228, 827985009, 558042871], False),
(9, 'A', 2, 0, [990797142, 905540566, 749313767], False),
(10, 'A', 2, 0, [1031597344, 961403162, 836579341, 548998511], True),
(11, 'A', 2, 0, [1074221665, 1012236938, 922288755, 740466992], True),
(12, 'A', 2, 0, [1106949463, 1055547399, 977035374, 841990311, 527947234], True),
(13, 'A', 2, 0, [1135604602, 1090153632, 1024821569, 912379896, 684837846], True),
(14, 'A', 2, 0, [1162117406, 1123542368, 1070247412, 949156116, 813562385], True),
(15, 'A', 2, 0, [1186363867, 1156892994, 1093820448, 937560384, 803623186], True),
(16, 'A', 2, 0, [1204529686, 1185105398, 1087194987, 931881418, 798755501], True),
(17, 'A', 2, 0, [1218149633, 1206087867, 1082251785, 927644387, 795123760], True),
(18, 'A', 2, 0, [1228585446, 1222118985, 1078470795, 924403538, 792345890], True),
(19, 'A', 2, 0, [1236077788, 1234109194, 1075687573, 922017920, 790301074], True),
(20, 'A', 2, 0, [1241511020, 1242754281, 1073676385, 920294044, 788823466], True),
]),
16:([0, 1000000, 2000000, 3007492, 4063843, 5178749, 6341235, 7545733, 8790255, 10076926, 11401974, 12767190, 14170227, 15611941, 17090638, 18659938, 20265171, 21900470, 23564877, 25256429, 26973004, 28712662, 30474472, 32257964, 34062610, 35888365, 37735550, 39605675, 41503017, 43442618, 45476950],[
(3, 'A', 1, 0, [37414197], False),
(4, 'A', 1, 0, [188298668], False),
(5, 'A', 2, 0, [291922104], False),
(6, 'A', 1, 0, [337019148, 82529262], False),
(7, 'B', 2, 8, [361381975, 240453276], False),
(8, 'A', 2, 0, [378851332, 307163452], False),
(9, 'B', 2, 9, [397615430, 359291438, 199227299], False),
(10, 'A', 2, 0, [410254477, 382831518, 288575973], False),
(11, 'B', 2, 10, [424766731, 404882933, 361222671, 184037872], False),
(12, 'A', 2, 0, [436525663, 419528978, 385915026, 279229557], False),
(13, 'B', 2, 12, [449362623, 434343819, 413375685, 363298780, 181075949], False),
(14, 'A', 2, 0, [460814412, 446935396, 427851512, 391200512, 275915456], False),
(15, 'B', 2, 13, [488601671, 459517246, 444545990, 421601419, 370044564, 192789497], True),
(16, 'A', 2, 0, [488983581, 486345145, 456811263, 437557944, 399379876, 289341394], True),
(17, 'B', 2, 14, [494240208, 487641647, 484032399, 453965752, 430129669, 375646281, 203018466], True),
(18, 'B', 3, 14, [501982135, 493143959, 485876194, 480497859, 447400164, 410595812, 309910596], True),
(19, 'B', 3, 14, [510036657, 501140788, 492112716, 484313475, 477582628, 442812982, 397540410], True),
(20, 'A', 1, 0, [517846379, 509348577, 500481232, 491595321, 484221489, 479012032, 451728176, 428542946, 376483961], True),
(21, 'A', 1, 0, [525299753, 517193147, 508723316, 500003214, 491590441, 485595778, 464772956, 433788092, 404868886, 318822420, 0], True),
(22, 'A', 1, 0, [532660084, 524710546, 516677372, 508465683, 500513796, 494301898, 461511374, 430743949, 402027686, 318917324, 0], True),
(23, 'B', 2, 19, [539892466, 532194248, 524483527, 517083988, 510597893, 491716524, 458935423, 428339728, 399783746, 318600313, 0], True),
(24, 'B', 2, 19, [546801742, 539548829, 532258365, 525570370, 520805035, 489001043, 456400974, 425974242, 397575959, 369598125, 130565745], True),
(25, 'B', 2, 19, [553499949, 546686983, 540142819, 534592848, 521671826, 486893704, 454434124, 424138516, 395862615, 369471774, 218626657], True),
(26, 'A', 2, 0, [559913658, 553542379, 547645930, 543288863, 519707277, 485060126, 452722784, 422541265, 394371847, 368080391, 272451775], True),
(27, 'A', 2, 0, [566242010, 560057990, 554744632, 551317389, 517842531, 483319696, 451098383, 421025157, 392956813, 366759692, 324088483], True),
(28, 'B', 3, 22, [573083193, 566589653, 561778491, 553236577, 516354138, 481930529, 449801827, 419815039, 391827369, 365705545, 341325175], True),
(29, 'B', 3, 22, [582922068, 573528102, 568700817, 551656600, 514879494, 480554194, 448517248, 418616098, 390708358, 364661134, 340350392], True),
(30, 'A', 2, 0, [604502390, 583157999, 575827996, 549100774, 512494055, 478327785, 446439266, 416676648, 388898205, 362971658, 338773547, 289139661], True),
]),
}

report={}
for k,(ints,rows) in SEEDS.items():
 b=[F(x,10**6)for x in ints];bounds=[];minphi=F(1)
 def at(t):
  t=F(t);assert 0<=t<=len(b)-1
  i=t.numerator//t.denominator
  return b[i] if t==i else (i+1-t)*b[i]+(t-i)*b[i+1]
 for S,kind,ell,t,nums,prefix in rows:
  phi=[F(x,10**10)for x in nums];j=len(phi);p=2**ell;u=S-j
  assert 1 <= ell <= 3 and 1 <= j <= k-1-ell
  assert all(0<=f<F(1,k) for f in phi)
  assert all(phi[i] <= 1-sum(phi[:i]) for i in range(j))
  minphi=min(minphi,phi[0]);total=sum(phi)
  def special(l):return j==1 or (l==1 and ((k-j)%2 or k-j in (2,4))) or (l==2 and 3<=k-j<=5) or (l==3 and k-j in (4,5))
  used=[ell] if kind=='A' else [ell-1,ell]
  for order in used:
   assert 1 <= order <= 3
   for appended in range(order):
    residual = k-j-appended
    assert residual >= 2
    if residual % 2 == 0 and residual >= 6:
     assert total <= F(1,3)
  assert all(special(l) or total<=F(1,3) for l in used)
  J=(k-j-ell+1)//2
  if not prefix:assert j<=J+1
  else:
   for i in range(j):assert sum(phi[:i+1])+(k-2)*phi[i]<=1
  def kap(l):p=2**l;return p-l+(p-1)*(j+(1-k)*total)
  if kind=='A':
   c=1-F(1,p);C=kap(ell)/p+c*(1-total)*at(F(u)/c)
  else:
   c=F(u,t);a=2*(1-c)-F(2,p);bb=F(2,p)-(1-c)
   assert min(a,bb,c)>=0 and a+bb+c==1 and a*(p//2)+bb*p==1
   C=a*kap(ell-1)+bb*kap(ell)+c*(1-total)*at(t)
  for i in range(j-1,0,-1):
   pre=sum(phi[:i]);ui=S-i-1;ti=S-i+1
   E=(i+(1-k)*pre+(2*ui-1)*phi[i]+(1-pre)*at(ti))/2
   D=i+1+(1-k)*pre+phi[i]+(1-pre-phi[i])*at(ui)
   C=E+max(D,C)/2
  out=(2*S-3)*phi[0]+max(1+phi[0]+(1-phi[0])*at(S-1),C)
  assert S<=out<b[S],(k,S,float(out),float(b[S]),float(b[S]-out))
  bounds.append({'s':S,'b':str(b[S]),'out':str(out),'slack':str(b[S]-out)})
 print(k,'all',len(bounds),'rows passed; minimum slack',float(min(F(x['slack'])for x in bounds)),'contraction <=',float(1-minphi))
 report[k]={'rows':bounds,'contraction':str(1-minphi)}

# All fixed policies, in literal rational data.
POLICIES=json.loads(r'''
{
"14":{
"phi":[
"5793479/50000000","11191889/100000000","10604341/100000000",
"9516681/100000000","3846939/50000000","806929/25000000"],
"path":[13, 12, 11, 10, 9, 8],"v":20,
"pieces":[
["0","1/8",[
[["z2",-1,2],"99999/200000"],
[["refined",0,44],"22727/1000000"],
[["refined",1,46],"10869/500000"],
[["refined",2,48],"20833/1000000"],
[["basic",3,2],"1659/4000"],
[["refined",3,52],"1639/500000"],
[["cube",4,60],"8333/500000"]
]],
["1/8","1/4",[
[["z2",-1,2],"99999/200000"],
[["refined",0,40],"24999/1000000"],
[["refined",1,42],"23809/1000000"],
[["refined",2,44],"22727/1000000"],
[["basic",3,2],"203269/500000"],
[["refined",3,46],"4063/1000000"],
[["refined",4,56],"279/15625"]
]],
["1/4","3/8",[
[["z2",-1,2],"99999/200000"],
[["refined",0,38],"5263/200000"],
[["refined",1,38],"5263/200000"],
[["refined",2,40],"24999/1000000"],
[["basic",3,2],"198741/500000"],
[["refined",3,42],"4881/1000000"],
[["refined",4,50],"19999/1000000"]
]],
["3/8","1/2",[
[["z2",-1,2],"99999/200000"],
[["refined",0,34],"29411/1000000"],
[["refined",1,34],"29411/1000000"],
[["refined",2,36],"27777/1000000"],
[["basic",3,2],"384593/1000000"],
[["refined",3,38],"6073/1000000"],
[["refined",4,44],"22727/1000000"]
]],
["1/2","5/8",[
[["z2",-1,2],"99999/200000"],
[["refined",0,30],"8333/250000"],
[["refined",1,32],"31249/1000000"],
[["refined",2,32],"31249/1000000"],
[["basic",3,2],"2983/8000"],
[["refined",3,34],"7477/1000000"],
[["refined",4,42],"23809/1000000"]
]],
["5/8","3/4",[
[["z2",-1,2],"99999/200000"],
[["refined",0,28],"35713/1000000"],
[["refined",1,28],"35713/1000000"],
[["refined",2,28],"35713/1000000"],
[["refined",3,32],"31249/1000000"],
[["basic",4,2],"354683/1000000"],
[["refined",4,42],"6919/1000000"]
]],
["3/4","7/8",[
[["z2",-1,2],"99999/200000"],
[["refined",0,24],"20833/500000"],
[["refined",1,24],"20833/500000"],
[["refined",2,26],"38461/1000000"],
[["refined",3,32],"31249/1000000"],
[["basic",4,2],"339299/1000000"],
[["refined",4,42],"1913/250000"]
]],
["7/8","1",[
[["z2",-1,2],"135579/1000000"],
[["z4_refined",-1,4],"182207/1000000"],
[["refined",0,22],"22727/500000"],
[["refined",1,24],"20833/500000"],
[["refined",2,26],"38461/1000000"],
[["basic",3,2],"6767/250000"],
[["refined",3,32],"29557/1000000"],
[["basic",4,2],"99999/200000"]
]]
]}
,
"15":{
"phi":[
"5878239/50000000","2280537/20000000","10847441/100000000",
"1980311/20000000","4095097/50000000"],
"path":[14, 13, 12, 11, 11],"v":null,
"pieces":[
["0","1/8",[
[["z2",-1,2],"99999/200000"],
[["refined",0,44],"22727/1000000"],
[["refined",1,44],"22727/1000000"],
[["refined",2,46],"10869/500000"],
[["basic",3,2],"206021/500000"],
[["refined",3,50],"1759/500000"],
[["refined",4,58],"17241/1000000"]
]],
["1/8","1/4",[
[["z2",-1,2],"99999/200000"],
[["refined",0,40],"24999/1000000"],
[["refined",1,40],"24999/1000000"],
[["refined",2,42],"23809/1000000"],
[["basic",3,2],"16101/40000"],
[["refined",3,44],"443/100000"],
[["refined",4,52],"1923/100000"]
]],
["1/4","3/8",[
[["z2",-1,2],"99999/200000"],
[["refined",0,36],"27777/1000000"],
[["refined",1,38],"5263/200000"],
[["refined",2,38],"5263/200000"],
[["basic",3,2],"392471/1000000"],
[["refined",3,40],"84/15625"],
[["refined",4,46],"10869/500000"]
]],
["3/8","1/2",[
[["z2",-1,2],"99999/200000"],
[["refined",0,32],"31249/1000000"],
[["refined",1,34],"29411/1000000"],
[["refined",2,34],"29411/1000000"],
[["basic",3,2],"378153/1000000"],
[["refined",3,36],"423/62500"],
[["refined",4,40],"24999/1000000"]
]],
["1/2","5/8",[
[["z2",-1,2],"99999/200000"],
[["refined",0,28],"35713/1000000"],
[["refined",1,30],"8333/250000"],
[["refined",2,30],"8333/250000"],
[["basic",3,2],"9029/25000"],
[["refined",3,32],"8677/1000000"],
[["refined",4,36],"27777/1000000"]
]],
["5/8","3/4",[
[["z2",-1,2],"99999/200000"],
[["refined",0,24],"20833/500000"],
[["refined",1,26],"38461/1000000"],
[["refined",2,26],"38461/1000000"],
[["refined",3,28],"35713/1000000"],
[["basic",4,2],"67323/200000"],
[["refined",4,36],"2269/250000"]
]],
["3/4","7/8",[
[["z2",-1,2],"99999/200000"],
[["refined",0,20],"49999/1000000"],
[["refined",1,20],"49999/1000000"],
[["refined",2,22],"22727/500000"],
[["refined",3,26],"38461/1000000"],
[["basic",4,2],"152631/500000"],
[["refined",4,36],"5409/500000"]
]],
["7/8","1",[
[["z2",-1,2],"841/8000"],
[["z4_refined",-1,4],"98717/500000"],
[["refined",0,18],"27777/500000"],
[["refined",1,20],"49999/1000000"],
[["refined",2,22],"22727/500000"],
[["basic",3,2],"2157/250000"],
[["refined",3,26],"37797/1000000"],
[["basic",4,2],"249997/500000"]
]]
]}
,
"16":{
"phi":[
"5944601/50000000","5776809/50000000","1376757/12500000",
"2514103/25000000","4096319/50000000"],
"path":[15, 14, 13, 12, 11],"v":null,
"pieces":[
["0","1/8",[
[["z2",-1,2],"99999/200000"],
[["refined",0,44],"22727/1000000"],
[["refined",1,44],"22727/1000000"],
[["refined",2,46],"10869/500000"],
[["basic",3,2],"411889/1000000"],
[["refined",3,48],"3671/1000000"],
[["refined",4,58],"17241/1000000"]
]],
["1/8","1/4",[
[["z2",-1,2],"99999/200000"],
[["refined",0,40],"24999/1000000"],
[["refined",1,40],"24999/1000000"],
[["refined",2,42],"23809/1000000"],
[["basic",3,2],"16101/40000"],
[["refined",3,44],"443/100000"],
[["refined",4,52],"1923/100000"]
]],
["1/4","3/8",[
[["z2",-1,2],"99999/200000"],
[["refined",0,36],"27777/1000000"],
[["refined",1,38],"5263/200000"],
[["refined",2,38],"5263/200000"],
[["basic",3,2],"392471/1000000"],
[["refined",3,40],"84/15625"],
[["refined",4,46],"10869/500000"]
]],
["3/8","1/2",[
[["z2",-1,2],"99999/200000"],
[["refined",0,32],"31249/1000000"],
[["refined",1,34],"29411/1000000"],
[["refined",2,34],"29411/1000000"],
[["basic",3,2],"189707/500000"],
[["refined",3,36],"3349/500000"],
[["refined",4,42],"23809/1000000"]
]],
["1/2","5/8",[
[["z2",-1,2],"99999/200000"],
[["refined",0,30],"8333/250000"],
[["refined",1,30],"8333/250000"],
[["refined",2,30],"8333/250000"],
[["basic",3,2],"3637/10000"],
[["refined",3,32],"4259/500000"],
[["refined",4,36],"27777/1000000"]
]],
["5/8","3/4",[
[["z2",-1,2],"99999/200000"],
[["refined",0,26],"38461/1000000"],
[["refined",1,26],"38461/1000000"],
[["refined",2,26],"38461/1000000"],
[["refined",3,28],"35713/1000000"],
[["basic",4,2],"340009/1000000"],
[["refined",4,36],"1111/125000"]
]],
["3/4","7/8",[
[["z2",-1,2],"99999/200000"],
[["refined",0,22],"22727/500000"],
[["refined",1,22],"22727/500000"],
[["refined",2,22],"22727/500000"],
[["refined",3,26],"38461/1000000"],
[["basic",4,2],"314887/1000000"],
[["refined",4,36],"10283/1000000"]
]],
["7/8","1",[
[["z2",-1,2],"106167/1000000"],
[["z4_refined",-1,4],"196913/1000000"],
[["refined",0,20],"49999/1000000"],
[["refined",1,20],"49999/1000000"],
[["refined",2,22],"22727/500000"],
[["basic",3,2],"7041/500000"],
[["refined",3,26],"37377/1000000"],
[["basic",4,2],"249997/500000"]
]]
]}
,
"17":{
"phi":[
"5998369/50000000","11673903/100000000","1392129/12500000",
"10234991/100000000"],
"path":[16, 15, 14, 14],"v":null,
"pieces":[
["0","1/8",[
[["z2",-1,2],"99999/200000"],
[["basic",0,2],"85661/200000"],
[["refined",0,42],"3413/1000000"],
[["refined",1,42],"23809/1000000"],
[["refined",2,44],"22727/1000000"],
[["refined",3,46],"10869/500000"]
]],
["1/8","1/4",[
[["z2",-1,2],"99999/200000"],
[["basic",0,2],"52587/125000"],
[["refined",0,38],"4173/1000000"],
[["refined",1,38],"5263/200000"],
[["refined",2,40],"24999/1000000"],
[["refined",3,42],"23809/1000000"]
]],
["1/4","3/8",[
[["z2",-1,2],"99999/200000"],
[["basic",0,2],"407621/1000000"],
[["refined",0,32],"5773/1000000"],
[["refined",1,34],"29411/1000000"],
[["refined",2,34],"29411/1000000"],
[["refined",3,36],"27777/1000000"]
]],
["3/8","1/2",[
[["z2",-1,2],"99999/200000"],
[["basic",0,2],"389739/1000000"],
[["refined",0,28],"63/8000"],
[["refined",1,28],"35713/1000000"],
[["refined",2,30],"8333/250000"],
[["refined",3,30],"8333/250000"]
]],
["1/2","5/8",[
[["z2",-1,2],"99999/200000"],
[["basic",0,2],"358329/1000000"],
[["refined",0,22],"6439/500000"],
[["refined",1,22],"22727/500000"],
[["refined",2,24],"20833/500000"],
[["refined",3,24],"20833/500000"]
]],
["5/8","3/4",[
[["z2",-1,2],"99999/200000"],
[["basic",0,2],"130207/500000"],
[["refined",0,14],"1369/40000"],
[["refined",1,14],"71427/1000000"],
[["refined",2,14],"71427/1000000"],
[["refined",3,16],"62499/1000000"]
]],
["3/4","7/8",[
[["z2",-1,2],"233391/500000"],
[["z4",-1,4],"8303/500000"],
[["refined",0,6],"2657/40000"],
[["refined",0,8],"75179/1000000"],
[["refined",1,8],"62499/500000"],
[["refined",2,8],"62499/500000"],
[["refined",3,8],"62499/500000"]
]],
["7/8","1",[
[["z4",-1,4],"69863/1000000"],
[["z4_refined",-1,4],"180133/1000000"],
[["refined",0,4],"249997/1000000"],
[["refined",1,6],"20833/125000"],
[["refined",2,6],"20833/125000"],
[["refined",3,6],"20833/125000"]
]]
]}

}
''' )
def interpolate(raw):
    values, witnesses = [], []
    for i in range(len(raw)):
        candidates = [(raw[i], i, i)]
        candidates += [((b-i)*raw[a]/(b-a)+(i-a)*raw[b]/(b-a), a, b)
                       for a in range(i+1) for b in range(i, len(raw)) if a < b]
        value, a, b = min(candidates)
        values.append(value)
        witnesses.append((a, b))
    return values, witnesses


GRID=10**12
def resource(k, phi, height, coeff, res):
    (kind, i, order), _ = res
    total = sum(phi)
    length = 1-total
    h = k-2-k*total
    if kind == 'z2':
        assert i == -1 and order == 2 and h >= 1
        return F(1)
    if kind == 'z4':
        assert i == -1 and order == 4
        return min(height, F(2), h)
    if kind == 'z4_refined':
        assert i == -1 and order == 4
        return min(2*height-h, F(2))
    assert 0 <= i < len(phi) and order % 2 == 0
    assert 2 <= order <= 2*(len(coeff)-1)
    assert kind in ('basic','refined','cube')
    f = phi[i]
    if kind == 'basic':
        assert order == 2
        caps = [f, k-6-k*total+4*k*f, length/4, (k*length-(4*k-1)*f)/6]
        assert min(caps) >= 0
        return min(caps)
    delta = max(F(0), coeff[order//2]-order+2*k)
    cap0 = min(2*k*f, k-3-k*total+k*f, (k-6-k*total+6*k*f)/2)
    assert cap0 >= 0
    cap = height-2+2*k*f if kind == 'refined' else height/3
    return min(cap0, cap)-delta*f

def evaluate(k, curve, coeff, s, policy):
    phi = list(map(F, policy['phi']))
    path = policy['path']
    j = len(phi)
    assert len(path) == j and path[0] == s-1 and 1 <= j <= k-2
    assert all(0 <= f <= F(1,k) for f in phi)
    totals = [F(0)]
    for f in phi: totals.append(totals[-1]+f)
    lengths = [1-t for t in totals]
    shifts = [i-k*t for i,t in enumerate(totals)]
    top = F(k,2)*lengths[j]
    assert top > 1
    amplitude = 1+shifts[j]+totals[j]
    r = path[-1]
    v = policy['v'] or 2*r
    c = F(2*r,v) if policy['v'] is not None else F(1)
    a = 1-c
    gamma = 1-2*a
    assert v % 2 == 0 and 0 <= a <= F(1,2) and 0 < c <= 1
    assert gamma >= 0 and a+c == 1 and gamma+2*a == 1
    assert all(phi[i] <= lengths[i] for i in range(j))
    assert curve[v//2] >= max(F(v,2),v-k)
    assert curve[r] >= max(F(r),2*r-k)
    prefix = [1-totals[i]-(k-2)*phi[i-1] for i in range(2,j+1)] if policy['v'] is not None else []
    assert all(t >= 0 for t in prefix)
    base = (gamma+a)*amplitude+c*(v-k)*lengths[j]
    dv = max(F(0), curve[v//2]-v+k)
    dr = max(F(0), curve[r]-2*r+k)
    cn = F(2,k)*c*dv
    root = F(1,2**(k-j-2))
    major = amplitude+(2*r-k)*lengths[j]+max(F(0),F(2,k)*dr-F(1,k-j))
    ends, pieces, last = [major], [], F(0)
    for lo,hi,resources in policy['pieces']:
        lo,hi = F(lo),F(hi)
        assert lo == last and lo < hi <= 1
        last = hi
        mass = sum((F(weight) for _,weight in resources),F(0))
        loads = [F(0)]*(j+1)
        for (_,i,order),weight in resources:
            assert F(weight) > 0
            loads[i+1] += order*F(weight)
        assert mass <= 1 and all(0 <= load <= 1 for load in loads)
        endpoints = []
        for t in (lo,hi):
            ell = 1+t*(top-1)
            saving = sum((F(res[1])*resource(k,phi,ell,coeff,res) for res in resources),F(0))
            exponent = base+cn*ell-gamma*root*min(F(1),saving)
            endpoints.append(dict(ell=ell,saving=saving,exponent=exponent))
            ends.append(exponent)
        pieces.append(dict(mass=mass,loads=loads,endpoints=endpoints))
    assert last == 1
    current, backwards = max(ends), []
    for i in range(j-1,0,-1):
        rr,u = path[i-1],path[i]
        h = 2*rr-u
        assert 0 < h < 2*rr
        diagonal = 1+shifts[i]+totals[i+1]+curve[u]*lengths[i+1]
        prefactor = (curve[h]*lengths[i]+shifts[i]+totals[i]+(2*u-1)*phi[i])/2
        current = prefactor+max(diagonal,current)/2
        backwards.append(dict(i=i,diagonal=diagonal,prefix=prefactor,output=current))
    first = 1+phi[0]+curve[s-1]*lengths[1]
    raw = (2*s-3)*phi[0]+max(first,current)
    rounded = F((raw.numerator*GRID+raw.denominator-1)//raw.denominator,GRID)
    return dict(major=major,prefix_margins=prefix,pieces=pieces,backward=backwards,raw_lambda=raw,rounded_up=rounded)


def run(source, coefficient, parameters, rounds):
    coeff_interp = interpolate(coefficient)
    previous, history = source[:], []
    for r in range(1,rounds+1):
        inter = interpolate(previous)
        entries = [evaluate(8,inter[0],coeff_interp[0],int(s),p)
                   for s,p in sorted(parameters.items(),key=lambda kv:int(kv[0]))]
        outputs = previous[:]
        for (s,_),entry in zip(sorted(parameters.items(),key=lambda kv:int(kv[0])),entries):
            s = int(s)
            outputs[s] = min(inter[0][s],entry['rounded_up'])
        history.append(dict(iteration=r,inputs=previous,interpolation=inter,entries=entries,outputs=outputs))
        previous = outputs
    return coeff_interp,history,interpolate(previous)


source=[F(x,10**6)for x in SEEDS[8][0]]
coefficient=[F(x,10**6)for x in SEEDS[16][0]]
_,history,final=run(source,coefficient,POLICIES,12)
delta=final[0][17]-26
assert delta==F(5857852793,50000000000)
assert delta<F(2,17)
print('VERIFIED eighth-power field certificate: delta34=',delta,'gate margin=',4-34*delta)

assert delta < F(2929,25000) < F(2,17)
assert (4-34*F(2929,25000))/72 == F(23,100000)
for s in range(14,18):
    print('order',2*s,'exponent',final[0][s],'excess',final[0][s]-(2*s-8))
