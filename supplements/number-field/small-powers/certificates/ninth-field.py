#!/usr/bin/env python3

"""Exact ninth-power certificate; analytic premises are proved in the manuscript."""

from fractions import Fraction as F

import json


DEGREE=9
CURVE=[0, 1000000, 2000000, 3035816, 4182300, 5419716, 6738319, 8135645, 9603938, 11142513, 12746354, 14410598, 16129237, 17896005, 19705700, 21551232, 23428999, 25333544, 27259337, 29202038, 31157968, 33124215, 35098519]
ROWS=[
(3, 'A', 1, 0, [179036170], False),
(4, 'A', 2, 0, [494174759], False),
(5, 'A', 1, 0, [621879419, 115059758], False),
(6, 'B', 2, 6, [695593421, 462394825], False),
(7, 'A', 2, 0, [755128706, 625405045], False),
(8, 'B', 2, 7, [798538520, 707130147, 449675915], False),
(9, 'A', 2, 0, [842039650, 769577206, 619021054], False),
(10, 'A', 2, 0, [880554724, 821567289, 717047271, 450210128], True),
(11, 'A', 2, 0, [915732629, 865400157, 788108407, 624740956], True),
(12, 'A', 2, 0, [946884858, 903198647, 840730176, 727963834, 450315087], True),
(13, 'A', 2, 0, [974169126, 935599415, 882414351, 794472457, 606925149], True),
(14, 'B', 2, 11, [999076762, 965217616, 920647847, 852624692, 724605779, 419237993], True),
(15, 'A', 2, 0, [1019323750, 990374131, 950827088, 879934378, 769942581, 548716139], True),
(16, 'A', 2, 0, [1038796560, 1013885885, 982865601, 870556493, 761736932, 658304785], True),
(17, 'A', 2, 0, [1055176568, 1036086416, 988592126, 865018110, 756890847, 662279491], True),
(18, 'A', 2, 0, [1068025541, 1054097784, 984734584, 861642761, 753937416, 659695239], True),
(19, 'A', 2, 0, [1078260443, 1068238183, 981687671, 858976712, 751604623, 657654045], True),
(20, 'A', 2, 0, [1086238129, 1079365052, 979299602, 856887151, 749776257, 656054225], True),
(21, 'A', 2, 0, [1092460207, 1088022959, 977439604, 855259653, 748352196, 654808172], True),
(22, 'A', 2, 0, [1097344279, 1094823942, 975978972, 853981600, 747233900, 653829663], True),
]

def verify():
    b=[F(v,10**6) for v in CURVE]
    rows=[]; minimum_phi=F(1); prefix_slacks=[]
    def at(t):
        t=F(t); assert 0<=t<=len(b)-1
        i=t.numerator//t.denominator
        return b[i] if t==i else b[i]+(t-i)*(b[i+1]-b[i])
    for s,kind,ell,t,nums,chronological in ROWS:
        phi=[F(v,10**10) for v in nums];j=len(phi)
        assert 1<=ell<=3 and 1<=j<=DEGREE-1-ell
        assert 1<=j<s and all(0<=v<F(1,DEGREE) for v in phi)
        total=[sum(phi[:i]) for i in range(j+1)]
        q=[1-v for v in total]
        assert all(phi[i]<=q[i] for i in range(j))
        orders=[ell] if kind=="A" else [ell-1,ell]
        J=(DEGREE-j-ell+1)//2
        assert J>=1
        if chronological:
            for i in range(j):
                slack=1-total[i+1]-(DEGREE-2)*phi[i]
                assert slack>=0
                prefix_slacks.append(slack)
        else:
            assert j<=J+1
        for order in orders:
            assert 1<=order<=3
            for appended in range(order):
                residual=DEGREE-j-appended
                assert residual>=2 and residual//2>=J
                if residual%2==0 and residual>=6:
                    assert total[j]<=F(1,3)
        def aux(order):
            p=2**order
            return p-order+(p-1)*(j-(DEGREE-1)*total[j])
        u=s-j;p=2**ell
        if kind=="A":
            c=1-F(1,p)
            current=aux(ell)/p+c*q[j]*at(F(u)/c)
        else:
            assert kind=="B"
            c=F(u,t);a=2*(1-c)-F(2,p);d=F(2,p)-(1-c)
            assert min(a,d,c)>=0 and a+d+c==1
            assert a*(p//2)+d*p==1
            current=a*aux(ell-1)+d*aux(ell)+c*q[j]*at(t)
        for i in reversed(range(1,j)):
            u=s-i-1;v=s-i+1
            assert 0<v<2*(s-i)
            diagonal=1+i-DEGREE*total[i]+total[i+1]+q[i+1]*at(u)
            prefactor=(q[i]*at(v)+i-(DEGREE-1)*total[i]+(2*u-1)*phi[i])/2
            current=prefactor+max(diagonal,current)/2
        output=(2*s-3)*phi[0]+max(1+phi[0]+q[1]*at(s-1),current)
        assert max(s,2*s-DEGREE)<=output<b[s]<2*s
        minimum_phi=min(minimum_phi,phi[0])
        rows.append((s,output,b[s]-output))
    assert min(x[2] for x in rows)==F(43740673471,40000000000000000)
    assert 1-minimum_phi==F(982096383,1000000000)
    assert min(prefix_slacks)==F(1,5000000000)
    return b,rows,1-minimum_phi

def refine(b, rounds=24):
    """Beginning-of-round inputs; every new exponent rounded upward."""
    grid=10**12;history=[]
    for iteration in range(rounds):
        def at(t):
            t=F(t);assert 0<=t<=len(b)-1
            i=t.numerator//t.denominator
            return b[i] if t==i else b[i]+(t-i)*(b[i+1]-b[i])
        new=b[:]
        for s,kind,ell,t,nums,chronological in ROWS:
            phi=[F(v,10**10)for v in nums];j=len(phi)
            total=[sum(phi[:i])for i in range(j+1)];q=[1-x for x in total]
            def aux(order):
                pp=2**order
                return pp-order+(pp-1)*(j-8*total[j])
            u=s-j;p=2**ell
            if kind=="A":
                c=1-F(1,p);current=aux(ell)/p+c*q[j]*at(F(u)/c)
            else:
                c=F(u,t);a=2*(1-c)-F(2,p);d=F(2,p)-(1-c)
                current=a*aux(ell-1)+d*aux(ell)+c*q[j]*at(t)
            for i in reversed(range(1,j)):
                u=s-i-1;v=s-i+1
                diagonal=1+i-9*total[i]+total[i+1]+q[i+1]*at(u)
                factor=(q[i]*at(v)+i-8*total[i]+(2*u-1)*phi[i])/2
                current=factor+max(diagonal,current)/2
            raw=(2*s-3)*phi[0]+max(1+phi[0]+q[1]*at(s-1),current)
            rounded=F((raw.numerator*grid+raw.denominator-1)//raw.denominator,grid)
            assert rounded>=raw
            new[s]=min(b[s],rounded)
        assert all(max(F(i),F(2*i-9))<=new[i]<=b[i]for i in range(len(b)))
        b=new;history.append(b[:])
    return b,history



source9, rows9, rho9 = verify()

assert 44*rho9**1024 < min(row[2] for row in rows9)

source9, seed_history9 = refine(source9, 24)

EXPECTED_SOURCE9 = list(map(F, [

    '0',

    '1',

    '2',

    '1517903617/500000000',

    '418229474839/100000000000',

    '541971147069/100000000000',

    '3369156664507/500000000000',

    '8135638882429/1000000000000',

    '960393089121/100000000000',

    '445700243877/40000000000',

    '12746346059899/1000000000000',

    '14410586823381/1000000000000',

    '100807605439/6250000000',

    '17895964268487/1000000000000',

    '9852809826683/500000000000',

    '21551085549629/1000000000000',

    '23428755886157/1000000000000',

    '3166646686557/125000000000',

    '545176291443/20000000000',

    '29201360351041/1000000000000',

    '7789282771479/250000000000',

    '3312322993363/100000000000',

    '7019475446201/200000000000',

]))

assert source9 == EXPECTED_SOURCE9

print('Verified 20 degree-nine seed rows and 24 refinement rounds')


SEEDS={18:(
[0, 1000000, 2000000, 3005107, 4048469, 5146988, 6289328, 7467683, 8681624, 9933259, 11218619, 12538919, 13893656, 15282351, 16705014, 18160923, 19649745, 21170711, 22723143, 24306116, 25918677, 27559735, 29228132, 30922636, 32641958, 34384850, 36150022, 37936763, 39742902, 41567190, 43408399, 45265286], [
(3, 'A', 1, 0, [25445089], False),
(4, 'A', 1, 0, [144775325], False),
(5, 'B', 2, 6, [249310178], False),
(6, 'A', 1, 0, [293300611, 33775452], False),
(7, 'B', 2, 8, [312316861, 184319571], False),
(8, 'A', 2, 0, [327509329, 253232998], False),
(9, 'B', 2, 10, [343838343, 308344041, 134438480], False),
(10, 'A', 2, 0, [353748243, 329255689, 229935253], False),
(11, 'A', 2, 0, [364747875, 346393644, 294724463], False),
(12, 'B', 2, 11, [374941846, 360586605, 329428842, 212902972], False),
(13, 'A', 2, 0, [384603906, 371968172, 349892378, 283309642], False),
(14, 'A', 2, 0, [394360448, 382996242, 367260593, 332115022, 205577177], False),
(15, 'A', 2, 0, [403637234, 392987282, 379456894, 355224268, 284287546], False),
(16, 'A', 2, 0, [412887898, 402694056, 391097047, 374101870, 336300627, 208221365], False),
(17, 'A', 2, 0, [421825049, 412010236, 401123341, 387122000, 361338467, 289180249], False),
(18, 'A', 2, 0, [430600898, 421086173, 410930588, 398931678, 381083602, 341242476, 214151090], True),
(19, 'A', 2, 0, [439087199, 429886593, 420120921, 409183066, 394631371, 367977177, 295961604], True),
(20, 'A', 2, 0, [447318769, 438419346, 429075827, 418893515, 406657955, 387871418, 346621244, 221280611], True),
(21, 'B', 3, 17, [455239458, 446668268, 437668591, 428049544, 417055657, 402293866, 375263352, 305617705], True),
(22, 'A', 1, 0, [462865240, 454674103, 446144049, 437276264, 428046996, 418223737, 407101594, 391948659, 363164235, 283349913, 0], True),
(23, 'A', 1, 0, [470108280, 462256143, 454028437, 445422334, 436362596, 426595418, 415179183, 399100107, 367770913, 283288037, 0], True),
(24, 'A', 1, 0, [477008285, 469538225, 461696347, 453521196, 445078092, 436487805, 426862943, 401753358, 378120808, 341684999, 196953973], True),
(25, 'A', 1, 0, [483607603, 476580146, 469306604, 461992045, 455215393, 450194012, 423712011, 398787775, 375329671, 353251455, 332471957, 282530486, 0], True),
(26, 'A', 1, 0, [489839606, 483286832, 476579497, 470127455, 464924949, 447955391, 421605074, 396804776, 373463318, 351494888, 330818718, 282405153, 0], True),
(27, 'A', 1, 0, [495839815, 489603887, 483453269, 477751920, 473726535, 445860268, 419633194, 394948888, 371716601, 349850918, 329271452, 282336234, 0], True),
(28, 'B', 2, 21, [501187033, 495803541, 490212492, 485607775, 472187597, 444411856, 418269982, 393665865, 370509050, 348714400, 328201788, 282214555, 0], True),
(29, 'B', 2, 24, [506233337, 501274916, 496622811, 492801787, 470768655, 443076381, 417013065, 392482884, 369395656, 347666500, 327215529, 300861547, 54714982], True),
(30, 'B', 2, 24, [510936918, 506435074, 502304545, 498842556, 469498876, 441881295, 415888278, 391424262, 368399305, 346728758, 326332948, 307136892, 125828621], True),
(31, 'A', 2, 0, [515323049, 511350707, 507888173, 497966945, 468674772, 441105667, 415158275, 390737200, 367752659, 346120149, 325760141, 306597779, 179060600], True),
])}

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


assert len(SEEDS[18][1]) == 29
assert F(report[18]['contraction']) == F(9974554911,10**10)
assert min(F(r['slack']) for r in report[18]['rows']) == F(72464782233,160000000000000000)


coefficient18 = [F(v,10**6) for v in SEEDS[18][0]]

GRID = 10**12

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
        assert min(caps) == f and f > 0
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

POLICIES = json.loads(r'''
{
"17":{
"phi":[
"42033/400000","10289747/100000000","9976839/100000000",
"9517079/100000000","4367143/50000000","652933/10000000"],
"path":[16, 15, 14, 13, 12, 11],"v":null,
"pieces":[
["0","1/4",[
[["z2",-1,2],"99999/200000"],
[["refined",0,44],"22727/1000000"],
[["refined",1,44],"22727/1000000"],
[["refined",2,46],"10869/500000"],
[["basic",3,2],"48997/125000"],
[["refined",3,46],"587/125000"],
[["refined",4,50],"19999/1000000"],
[["refined",5,62],"252/15625"]
]],
["1/4","1/2",[
[["z2",-1,2],"99999/200000"],
[["refined",0,36],"27777/1000000"],
[["refined",1,36],"27777/1000000"],
[["refined",2,36],"27777/1000000"],
[["basic",3,2],"362697/1000000"],
[["refined",3,38],"3613/500000"],
[["refined",4,40],"24999/1000000"],
[["refined",5,46],"10869/500000"]
]],
["1/2","3/4",[
[["z2",-1,2],"99999/200000"],
[["refined",0,26],"38461/1000000"],
[["refined",1,26],"38461/1000000"],
[["refined",2,26],"38461/1000000"],
[["refined",3,26],"38461/1000000"],
[["refined",4,28],"35713/1000000"],
[["basic",5,2],"150479/500000"],
[["refined",5,42],"9477/1000000"]
]],
["3/4","1",[
[["z2",-1,2],"99999/200000"],
[["refined",0,14],"71427/1000000"],
[["refined",1,16],"62499/1000000"],
[["refined",2,18],"27777/500000"],
[["refined",3,20],"49999/1000000"],
[["refined",4,26],"38461/1000000"],
[["basic",5,2],"104077/500000"],
[["refined",5,42],"13897/1000000"]
]]
]}
,
"18":{
"phi":[
"10612499/100000000","10413773/100000000","2529797/25000000",
"1929101/20000000","2206251/25000000","7202381/100000000"],
"path":[17, 16, 15, 14, 13, 12],"v":null,
"pieces":[
["0","1/4",[
[["z2",-1,2],"99999/200000"],
[["refined",0,44],"22727/1000000"],
[["refined",1,44],"22727/1000000"],
[["refined",2,46],"10869/500000"],
[["refined",3,46],"10869/500000"],
[["basic",4,2],"389397/1000000"],
[["refined",4,50],"4423/1000000"],
[["refined",5,58],"17241/1000000"]
]],
["1/4","1/2",[
[["z2",-1,2],"99999/200000"],
[["refined",0,36],"27777/1000000"],
[["refined",1,36],"27777/1000000"],
[["refined",2,36],"27777/1000000"],
[["refined",3,38],"5263/200000"],
[["basic",4,2],"90423/250000"],
[["refined",4,40],"1383/200000"],
[["refined",5,46],"10869/500000"]
]],
["1/2","3/4",[
[["z2",-1,2],"99999/200000"],
[["refined",0,26],"38461/1000000"],
[["refined",1,28],"35713/1000000"],
[["refined",2,28],"35713/1000000"],
[["refined",3,28],"35713/1000000"],
[["refined",4,30],"8333/250000"],
[["basic",5,2],"155559/500000"],
[["refined",5,38],"497/50000"]
]],
["3/4","1",[
[["z2",-1,2],"99999/200000"],
[["refined",0,18],"27777/500000"],
[["refined",1,18],"27777/500000"],
[["refined",2,20],"49999/1000000"],
[["refined",3,24],"20833/500000"],
[["refined",4,28],"35713/1000000"],
[["basic",5,2],"49651/200000"],
[["refined",5,38],"13249/1000000"]
]]
]}
,
"19":{
"phi":[
"10702571/100000000","2628391/25000000","5115113/50000000",
"9758589/100000000","8900681/100000000","7211449/100000000"],
"path":[18, 17, 16, 15, 14, 13],"v":null,
"pieces":[
["0","1/4",[
[["z2",-1,2],"99999/200000"],
[["refined",0,44],"22727/1000000"],
[["refined",1,44],"22727/1000000"],
[["refined",2,46],"10869/500000"],
[["refined",3,46],"10869/500000"],
[["basic",4,2],"389397/1000000"],
[["refined",4,50],"4423/1000000"],
[["refined",5,58],"17241/1000000"]
]],
["1/4","1/2",[
[["z2",-1,2],"99999/200000"],
[["refined",0,36],"27777/1000000"],
[["refined",1,36],"27777/1000000"],
[["refined",2,38],"5263/200000"],
[["refined",3,38],"5263/200000"],
[["basic",4,2],"363231/1000000"],
[["refined",4,40],"3419/500000"],
[["refined",5,46],"10869/500000"]
]],
["1/2","3/4",[
[["z2",-1,2],"99999/200000"],
[["refined",0,28],"35713/1000000"],
[["refined",1,28],"35713/1000000"],
[["refined",2,28],"35713/1000000"],
[["refined",3,28],"35713/1000000"],
[["refined",4,30],"8333/250000"],
[["basic",5,2],"314533/1000000"],
[["refined",5,40],"9273/1000000"]
]],
["3/4","1",[
[["z2",-1,2],"99999/200000"],
[["refined",0,18],"27777/500000"],
[["refined",1,20],"49999/1000000"],
[["refined",2,22],"22727/500000"],
[["refined",3,24],"20833/500000"],
[["refined",4,28],"35713/1000000"],
[["basic",5,2],"51917/200000"],
[["refined",5,40],"601/50000"]
]]
]}
,
"20":{
"phi":[
"2694939/25000000","10604903/100000000","5165569/50000000",
"4935573/50000000","1127903/12500000"],
"path":[19, 18, 17, 16, 15],"v":null,
"pieces":[
["0","1/4",[
[["z2",-1,2],"99999/200000"],
[["basic",0,2],"201653/500000"],
[["refined",0,42],"1151/250000"],
[["refined",1,42],"23809/1000000"],
[["refined",2,42],"23809/1000000"],
[["refined",3,44],"22727/1000000"],
[["refined",4,46],"10869/500000"]
]],
["1/4","1/2",[
[["z2",-1,2],"99999/200000"],
[["basic",0,2],"73161/200000"],
[["refined",0,30],"1789/200000"],
[["refined",1,30],"8333/250000"],
[["refined",2,32],"31249/1000000"],
[["refined",3,32],"31249/1000000"],
[["refined",4,34],"29411/1000000"]
]],
["1/2","3/4",[
[["z2",-1,2],"99999/200000"],
[["basic",0,2],"93749/500000"],
[["refined",0,14],"22321/500000"],
[["refined",1,14],"71427/1000000"],
[["refined",2,14],"71427/1000000"],
[["refined",3,16],"62499/1000000"],
[["refined",4,16],"62499/1000000"]
]],
["3/4","1",[
[["z2",-1,2],"99999/200000"],
[["refined",0,10],"99999/1000000"],
[["refined",1,10],"99999/1000000"],
[["refined",2,10],"99999/1000000"],
[["refined",3,10],"99999/1000000"],
[["refined",4,10],"99999/1000000"]
]]
]}

}
''')


for half_order, policy in POLICIES.items():
    phi = list(map(F, policy['phi']))
    assert policy['v'] is None and len(phi) in (5,6)
    assert all(0 < x < F(1,9) for x in phi)
    assert 7-9*sum(phi) > 1 and F(9,2)*(1-sum(phi)) > 1
    for lo,hi,recipe in policy['pieces']:
        for (kind,i,order),weight in recipe:
            assert kind in ('z2','basic','refined')
            if kind == 'refined':
                assert 0 <= i < len(phi) and order % 2 == 0
                assert 2 <= order <= 62
                f = phi[i]
                assert min(18*f,6-9*sum(phi)+9*f,
                           (3-9*sum(phi)+54*f)/2) > 0

coeff = interpolate(coefficient18)[0]
previous = source9[:]
history = []
for round_number in range(1,8):
    curve = interpolate(previous)[0]
    outputs = previous[:]
    entries = []
    for s,policy in sorted(POLICIES.items(),key=lambda x:int(x[0])):
        s = int(s)
        entry = evaluate(9,curve,coeff,s,policy)
        outputs[s] = min(curve[s],entry['rounded_up'])
        entries.append(entry)
    history.append(dict(round=round_number,inputs=previous,
                        entries=entries,outputs=outputs))
    previous = outputs
final = interpolate(previous)[0]
delta40 = final[20]-31
assert delta40 == F(8516302869,62500000000)
assert delta40 < F(1363,10000) < F(3,22)
assert 6-44*delta40 == F(70668441,15625000000)
assert (6-44*F(1363,10000))/90 == F(7,225000)
assert 5*(final[19]-29)+74*delta40-11 == F(6959911153,500000000000)
print('VERIFIED ninth-power field certificate: delta40 =',delta40)
print('Strict global margin 6-44*delta40 =',6-44*delta40)
for s in range(17,21):
    print('order',2*s,'exponent',final[s],'excess',final[s]-(2*s-9))
