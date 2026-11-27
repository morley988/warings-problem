import WaringSmall.Degree16.C01

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace WaringSmall.Degree16
theorem p0 : Derivation 16 inputs ⟨46,1⟩ ⟨19028113,10000000⟩ :=
  .seed _ _ (by decide +kernel)
theorem p1 : Derivation 16 inputs ⟨48,1⟩ ⟨16883143,10000000⟩ :=
  .seed _ _ (by decide +kernel)
theorem p2 : Derivation 16 inputs ⟨185,4⟩ ⟨75039967,40000000⟩ :=
  .interpolate _ _ p0 p1 (by decide +kernel)
theorem p3 : Derivation 16 inputs ⟨93,2⟩ ⟨36983741,20000000⟩ :=
  .interpolate _ _ p0 p1 (by decide +kernel)
theorem p4 : Derivation 16 inputs ⟨187,4⟩ ⟨72894997,40000000⟩ :=
  .interpolate _ _ p0 p1 (by decide +kernel)
theorem p5 : Derivation 16 inputs ⟨47,1⟩ ⟨4488907,2500000⟩ :=
  .interpolate _ _ p0 p1 (by decide +kernel)
theorem p6 : Derivation 16 inputs ⟨189,4⟩ ⟨70750027,40000000⟩ :=
  .interpolate _ _ p0 p1 (by decide +kernel)
theorem p7 : Derivation 16 inputs ⟨95,2⟩ ⟨34838771,20000000⟩ :=
  .interpolate _ _ p0 p1 (by decide +kernel)
theorem p8 : Derivation 16 inputs ⟨191,4⟩ ⟨68605057,40000000⟩ :=
  .interpolate _ _ p0 p1 (by decide +kernel)
theorem p9 : Derivation 16 inputs ⟨193,4⟩ ⟨16636643,10000000⟩ :=
  .step _ _ ⟨907,500⟩ ⟨363,200⟩ ⟨493,5000⟩ ⟨1973,10000⟩ p2 p1 c0 (by decide +kernel)
theorem p10 : Derivation 16 inputs ⟨97,2⟩ ⟨1639118467,1000000000⟩ :=
  .step _ _ ⟨1819,1000⟩ ⟨91,50⟩ ⟨5891,60000⟩ ⟨2947,15000⟩ p3 p9 c1 (by decide +kernel)
theorem p11 : Derivation 16 inputs ⟨195,4⟩ ⟨1614676801,1000000000⟩ :=
  .step _ _ ⟨228,125⟩ ⟨73,40⟩ ⟨2933,30000⟩ ⟨5869,30000⟩ p4 p10 c2 (by decide +kernel)
theorem p12 : Derivation 16 inputs ⟨49,1⟩ ⟨1590339301,1000000000⟩ :=
  .step _ _ ⟨1829,1000⟩ ⟨183,100⟩ ⟨1947,20000⟩ ⟨487,2500⟩ p5 p11 c3 (by decide +kernel)
theorem p13 : Derivation 16 inputs ⟨197,4⟩ ⟨97881623,62500000⟩ :=
  .step _ _ ⟨917,500⟩ ⟨367,200⟩ ⟨727,7500⟩ ⟨5819,30000⟩ p6 p12 c4 (by decide +kernel)
theorem p14 : Derivation 16 inputs ⟨99,2⟩ ⟨770988401,500000000⟩ :=
  .step _ _ ⟨1839,1000⟩ ⟨46,25⟩ ⟨5791,60000⟩ ⟨2897,15000⟩ p7 p13 c5 (by decide +kernel)
theorem p15 : Derivation 16 inputs ⟨199,4⟩ ⟨758975901,500000000⟩ :=
  .step _ _ ⟨461,250⟩ ⟨369,200⟩ ⟨961,10000⟩ ⟨1923,10000⟩ p8 p14 c6 (by decide +kernel)
theorem p16 : Derivation 16 inputs ⟨50,1⟩ ⟨746963401,500000000⟩ :=
  .step _ _ ⟨461,250⟩ ⟨369,200⟩ ⟨961,10000⟩ ⟨1923,10000⟩ p1 p14 c6 (by decide +kernel)
theorem p17 : Derivation 16 inputs ⟨201,4⟩ ⟨1470318469,1000000000⟩ :=
  .step _ _ ⟨233,125⟩ ⟨373,200⟩ ⟨2833,30000⟩ ⟨5669,30000⟩ p9 p16 c7 (by decide +kernel)
theorem p18 : Derivation 16 inputs ⟨101,2⟩ ⟨361755659,250000000⟩ :=
  .step _ _ ⟨1879,1000⟩ ⟨47,25⟩ ⟨5591,60000⟩ ⟨2797,15000⟩ p10 p17 c8 (by decide +kernel)
theorem p19 : Derivation 16 inputs ⟨203,4⟩ ⟨1424039303,1000000000⟩ :=
  .step _ _ ⟨947,500⟩ ⟨379,200⟩ ⟨1379,15000⟩ ⟨5519,30000⟩ p11 p18 c9 (by decide +kernel)
theorem p20 : Derivation 16 inputs ⟨51,1⟩ ⟨1401264303,1000000000⟩ :=
  .step _ _ ⟨238,125⟩ ⟨381,200⟩ ⟨911,10000⟩ ⟨1823,10000⟩ p12 p19 c10 (by decide +kernel)
theorem p21 : Derivation 16 inputs ⟨205,4⟩ ⟨689380271,500000000⟩ :=
  .step _ _ ⟨957,500⟩ ⟨383,200⟩ ⟨677,7500⟩ ⟨5419,30000⟩ p13 p20 c11 (by decide +kernel)
theorem p22 : Derivation 16 inputs ⟨103,2⟩ ⟨169563297,125000000⟩ :=
  .step _ _ ⟨1929,1000⟩ ⟨193,100⟩ ⟨5341,60000⟩ ⟨334,1875⟩ p14 p21 c12 (by decide +kernel)
theorem p23 : Derivation 16 inputs ⟨207,4⟩ ⟨1334460543,1000000000⟩ :=
  .step _ _ ⟨1939,1000⟩ ⟨97,50⟩ ⟨5291,60000⟩ ⟨2647,15000⟩ p15 p22 c13 (by decide +kernel)
theorem p24 : Derivation 16 inputs ⟨52,1⟩ ⟨1312518877,1000000000⟩ :=
  .step _ _ ⟨243,125⟩ ⟨389,200⟩ ⟨2633,30000⟩ ⟨5269,30000⟩ p16 p23 c14 (by decide +kernel)
theorem p25 : Derivation 16 inputs ⟨209,4⟩ ⟨161348193,125000000⟩ :=
  .step _ _ ⟨977,500⟩ ⟨391,200⟩ ⟨163,1875⟩ ⟨5219,30000⟩ p17 p24 c15 (by decide +kernel)
theorem p26 : Derivation 16 inputs ⟨105,2⟩ ⟨1269364711,1000000000⟩ :=
  .step _ _ ⟨1969,1000⟩ ⟨197,100⟩ ⟨5141,60000⟩ ⟨643,3750⟩ p18 p25 c16 (by decide +kernel)
theorem p27 : Derivation 16 inputs ⟨211,4⟩ ⟨1248152211,1000000000⟩ :=
  .step _ _ ⟨1979,1000⟩ ⟨99,50⟩ ⟨1697,20000⟩ ⟨849,5000⟩ p19 p26 c17 (by decide +kernel)
theorem p28 : Derivation 16 inputs ⟨53,1⟩ ⟨245429609,200000000⟩ :=
  .step _ _ ⟨1989,1000⟩ ⟨199,100⟩ ⟨5041,60000⟩ ⟨1261,7500⟩ p20 p27 c18 (by decide +kernel)
theorem p29 : Derivation 16 inputs ⟨213,4⟩ ⟨1206456379,1000000000⟩ :=
  .step _ _ ⟨501,250⟩ ⟨401,200⟩ ⟨2483,30000⟩ ⟨4969,30000⟩ p21 p28 c19 (by decide +kernel)
theorem p30 : Derivation 16 inputs ⟨107,2⟩ ⟨592986523,500000000⟩ :=
  .step _ _ ⟨1007,500⟩ ⟨403,200⟩ ⟨1229,15000⟩ ⟨4919,30000⟩ p22 p29 c20 (by decide +kernel)
theorem p31 : Derivation 16 inputs ⟨215,4⟩ ⟨582849023,500000000⟩ :=
  .step _ _ ⟨253,125⟩ ⟨81,40⟩ ⟨811,10000⟩ ⟨1623,10000⟩ p23 p30 c21 (by decide +kernel)
theorem p32 : Derivation 16 inputs ⟨54,1⟩ ⟨229132983,200000000⟩ :=
  .step _ _ ⟨1017,500⟩ ⟨407,200⟩ ⟨301,3750⟩ ⟨4819,30000⟩ p24 p31 c22 (by decide +kernel)
theorem p33 : Derivation 16 inputs ⟨217,4⟩ ⟨1125887691,1000000000⟩ :=
  .step _ _ ⟨511,250⟩ ⟨409,200⟩ ⟨2383,30000⟩ ⟨4769,30000⟩ p25 p32 c23 (by decide +kernel)
theorem p34 : Derivation 16 inputs ⟨109,2⟩ ⟨553170929,500000000⟩ :=
  .step _ _ ⟨2059,1000⟩ ⟨103,50⟩ ⟨4691,60000⟩ ⟨2347,15000⟩ p26 p33 c24 (by decide +kernel)
theorem p35 : Derivation 16 inputs ⟨219,4⟩ ⟨543502179,500000000⟩ :=
  .step _ _ ⟨2069,1000⟩ ⟨207,100⟩ ⟨1547,20000⟩ ⟨387,2500⟩ p27 p34 c25 (by decide +kernel)
theorem p36 : Derivation 16 inputs ⟨55,1⟩ ⟨133484399,125000000⟩ :=
  .step _ _ ⟨2079,1000⟩ ⟨52,25⟩ ⟨4591,60000⟩ ⟨2297,15000⟩ p28 p35 c26 (by decide +kernel)
theorem p37 : Derivation 16 inputs ⟨221,4⟩ ⟨1048954359,1000000000⟩ :=
  .step _ _ ⟨2089,1000⟩ ⟨209,100⟩ ⟨4541,60000⟩ ⟨284,1875⟩ p29 p36 c27 (by decide +kernel)
theorem p38 : Derivation 16 inputs ⟨111,2⟩ ⟨515173013,500000000⟩ :=
  .step _ _ ⟨263,125⟩ ⟨421,200⟩ ⟨2233,30000⟩ ⟨4469,30000⟩ p30 p37 c28 (by decide +kernel)
theorem p39 : Derivation 16 inputs ⟨223,4⟩ ⟨505973013,500000000⟩ :=
  .step _ _ ⟨1057,500⟩ ⟨423,200⟩ ⟨46,625⟩ ⟨1473,10000⟩ p31 p38 c29 (by decide +kernel)
theorem p40 : Derivation 16 inputs ⟨56,1⟩ ⟨24843859,25000000⟩ :=
  .step _ _ ⟨531,250⟩ ⟨17,8⟩ ⟨2183,30000⟩ ⟨4369,30000⟩ p32 p39 c30 (by decide +kernel)
theorem p41 : Derivation 16 inputs ⟨225,4⟩ ⟨975771027,1000000000⟩ :=
  .step _ _ ⟨1067,500⟩ ⟨427,200⟩ ⟨1079,15000⟩ ⟨4319,30000⟩ p33 p40 c31 (by decide +kernel)
theorem p42 : Derivation 16 inputs ⟨113,2⟩ ⟨19161841,20000000⟩ :=
  .step _ _ ⟨268,125⟩ ⟨429,200⟩ ⟨711,10000⟩ ⟨1423,10000⟩ p34 p41 c32 (by decide +kernel)
theorem p43 : Derivation 16 inputs ⟨227,4⟩ ⟨18812591,20000000⟩ :=
  .step _ _ ⟨2159,1000⟩ ⟨54,25⟩ ⟨1397,20000⟩ ⟨699,5000⟩ p35 p42 c33 (by decide +kernel)
theorem p44 : Derivation 16 inputs ⟨57,1⟩ ⟨115421923,125000000⟩ :=
  .step _ _ ⟨2169,1000⟩ ⟨217,100⟩ ⟨4141,60000⟩ ⟨259,1875⟩ p36 p43 c34 (by decide +kernel)
theorem p45 : Derivation 16 inputs ⟨229,4⟩ ⟨906329551,1000000000⟩ :=
  .step _ _ ⟨2179,1000⟩ ⟨109,50⟩ ⟨4091,60000⟩ ⟨2047,15000⟩ p37 p44 c35 (by decide +kernel)
theorem p46 : Derivation 16 inputs ⟨115,2⟩ ⟨889492051,1000000000⟩ :=
  .step _ _ ⟨2189,1000⟩ ⟨219,100⟩ ⟨1347,20000⟩ ⟨337,2500⟩ p38 p45 c36 (by decide +kernel)
theorem p47 : Derivation 16 inputs ⟨231,4⟩ ⟨174573339,200000000⟩ :=
  .step _ _ ⟨2199,1000⟩ ⟨11,5⟩ ⟨3991,60000⟩ ⟨1997,15000⟩ p39 p46 c37 (by decide +kernel)
theorem p48 : Derivation 16 inputs ⟨58,1⟩ ⟨856550029,1000000000⟩ :=
  .step _ _ ⟨1107,500⟩ ⟨443,200⟩ ⟨979,15000⟩ ⟨3919,30000⟩ p40 p47 c38 (by decide +kernel)
theorem p49 : Derivation 16 inputs ⟨233,4⟩ ⟨26263803,31250000⟩ :=
  .step _ _ ⟨278,125⟩ ⟨89,40⟩ ⟨1933,30000⟩ ⟨3869,30000⟩ p41 p48 c39 (by decide +kernel)
theorem p50 : Derivation 16 inputs ⟨117,2⟩ ⟨1610433,1953125⟩ :=
  .step _ _ ⟨1117,500⟩ ⟨447,200⟩ ⟨159,2500⟩ ⟨1273,10000⟩ p42 p49 c40 (by decide +kernel)
theorem p51 : Derivation 16 inputs ⟨235,4⟩ ⟨80885003,100000000⟩ :=
  .step _ _ ⟨561,250⟩ ⟨449,200⟩ ⟨1883,30000⟩ ⟨3769,30000⟩ p43 p50 c41 (by decide +kernel)
theorem p52 : Derivation 16 inputs ⟨59,1⟩ ⟨793307173,1000000000⟩ :=
  .step _ _ ⟨1127,500⟩ ⟨451,200⟩ ⟨272,4375⟩ ⟨8711,70000⟩ p44 p51 c42 (by decide +kernel)
theorem p53 : Derivation 16 inputs ⟨237,4⟩ ⟨155579649,200000000⟩ :=
  .step _ _ ⟨2269,1000⟩ ⟨227,100⟩ ⟨8629,140000⟩ ⟨2159,17500⟩ p45 p52 c43 (by decide +kernel)
theorem p54 : Derivation 16 inputs ⟨119,2⟩ ⟨152524649,200000000⟩ :=
  .step _ _ ⟨571,250⟩ ⟨457,200⟩ ⟨611,10000⟩ ⟨1223,10000⟩ p46 p53 c44 (by decide +kernel)
theorem p55 : Derivation 16 inputs ⟨239,4⟩ ⟨373741087,500000000⟩ :=
  .step _ _ ⟨2299,1000⟩ ⟨23,10⟩ ⟨8479,140000⟩ ⟨4243,35000⟩ p47 p54 c45 (by decide +kernel)
theorem p56 : Derivation 16 inputs ⟨60,1⟩ ⟨366259837,500000000⟩ :=
  .step _ _ ⟨2319,1000⟩ ⟨58,25⟩ ⟨1197,20000⟩ ⟨599,5000⟩ p48 p55 c46 (by decide +kernel)
theorem p57 : Derivation 16 inputs ⟨241,4⟩ ⟨358867873,500000000⟩ :=
  .step _ _ ⟨2339,1000⟩ ⟨117,50⟩ ⟨8279,140000⟩ ⟨4143,35000⟩ p49 p56 c47 (by decide +kernel)
theorem p58 : Derivation 16 inputs ⟨121,2⟩ ⟨703130389,1000000000⟩ :=
  .step _ _ ⟨2359,1000⟩ ⟨59,25⟩ ⟨8179,140000⟩ ⟨4093,35000⟩ p50 p57 c48 (by decide +kernel)
theorem p59 : Derivation 16 inputs ⟨243,4⟩ ⟨172175901,250000000⟩ :=
  .step _ _ ⟨2379,1000⟩ ⟨119,50⟩ ⟨8079,140000⟩ ⟨4043,35000⟩ p51 p58 c49 (by decide +kernel)
theorem p60 : Derivation 16 inputs ⟨61,1⟩ ⟨67445539,100000000⟩ :=
  .step _ _ ⟨2399,1000⟩ ⟨12,5⟩ ⟨7979,140000⟩ ⟨3993,35000⟩ p52 p59 c50 (by decide +kernel)
theorem p61 : Derivation 16 inputs ⟨245,4⟩ ⟨165096437,250000000⟩ :=
  .step _ _ ⟨2419,1000⟩ ⟨121,50⟩ ⟨7879,140000⟩ ⟨3943,35000⟩ p53 p60 c51 (by decide +kernel)
theorem p62 : Derivation 16 inputs ⟨123,2⟩ ⟨646494677,1000000000⟩ :=
  .step _ _ ⟨2439,1000⟩ ⟨61,25⟩ ⟨7779,140000⟩ ⟨3893,35000⟩ p54 p61 c52 (by decide +kernel)
theorem p63 : Derivation 16 inputs ⟨247,4⟩ ⟨632782177,1000000000⟩ :=
  .step _ _ ⟨2459,1000⟩ ⟨123,50⟩ ⟨1097,20000⟩ ⟨549,5000⟩ p55 p62 c53 (by decide +kernel)
theorem p64 : Derivation 16 inputs ⟨62,1⟩ ⟨619248249,1000000000⟩ :=
  .step _ _ ⟨2479,1000⟩ ⟨62,25⟩ ⟨7579,140000⟩ ⟨3793,35000⟩ p56 p63 c54 (by decide +kernel)
theorem p65 : Derivation 16 inputs ⟨249,4⟩ ⟨605858687,1000000000⟩ :=
  .step _ _ ⟨1247,500⟩ ⟨499,200⟩ ⟨67,1250⟩ ⟨1073,10000⟩ p57 p64 c55 (by decide +kernel)
theorem p66 : Derivation 16 inputs ⟨125,2⟩ ⟨592651027,1000000000⟩ :=
  .step _ _ ⟨1257,500⟩ ⟨503,200⟩ ⟨1851,35000⟩ ⟨7411,70000⟩ p58 p65 c56 (by decide +kernel)
theorem p67 : Derivation 16 inputs ⟨251,4⟩ ⟨579630171,1000000000⟩ :=
  .step _ _ ⟨1267,500⟩ ⟨507,200⟩ ⟨913,17500⟩ ⟨7311,70000⟩ p59 p66 c57 (by decide +kernel)
theorem p68 : Derivation 16 inputs ⟨63,1⟩ ⟨566795449,1000000000⟩ :=
  .step _ _ ⟨1277,500⟩ ⟨511,200⟩ ⟨1801,35000⟩ ⟨7211,70000⟩ p60 p67 c58 (by decide +kernel)
theorem p69 : Derivation 16 inputs ⟨253,4⟩ ⟨554146191,1000000000⟩ :=
  .step _ _ ⟨1287,500⟩ ⟨103,40⟩ ⟨222,4375⟩ ⟨7111,70000⟩ p61 p68 c59 (by decide +kernel)
theorem p70 : Derivation 16 inputs ⟨127,2⟩ ⟨8463777,15625000⟩ :=
  .step _ _ ⟨1297,500⟩ ⟨519,200⟩ ⟨1751,35000⟩ ⟨7011,70000⟩ p62 p69 c60 (by decide +kernel)
theorem p71 : Derivation 16 inputs ⟨255,4⟩ ⟨2646989,5000000⟩ :=
  .step _ _ ⟨2619,1000⟩ ⟨131,50⟩ ⟨6879,140000⟩ ⟨3443,35000⟩ p63 p70 c61 (by decide +kernel)
theorem p72 : Derivation 16 inputs ⟨64,1⟩ ⟨517292443,1000000000⟩ :=
  .step _ _ ⟨2639,1000⟩ ⟨66,25⟩ ⟨6779,140000⟩ ⟨3393,35000⟩ p64 p71 c62 (by decide +kernel)
theorem p73 : Derivation 16 inputs ⟨257,4⟩ ⟨252680939,500000000⟩ :=
  .step _ _ ⟨1327,500⟩ ⟨531,200⟩ ⟨419,8750⟩ ⟨6711,70000⟩ p65 p72 c63 (by decide +kernel)
theorem p74 : Derivation 16 inputs ⟨129,2⟩ ⟨19744169,40000000⟩ :=
  .step _ _ ⟨1337,500⟩ ⟨107,40⟩ ⟨1651,35000⟩ ⟨6611,70000⟩ p66 p73 c64 (by decide +kernel)
theorem p75 : Derivation 16 inputs ⟨259,4⟩ ⟨482034583,1000000000⟩ :=
  .step _ _ ⟨2699,1000⟩ ⟨27,10⟩ ⟨6479,140000⟩ ⟨3243,35000⟩ p67 p74 c65 (by decide +kernel)
theorem p76 : Derivation 16 inputs ⟨65,1⟩ ⟨58830439,125000000⟩ :=
  .step _ _ ⟨2719,1000⟩ ⟨68,25⟩ ⟨6379,140000⟩ ⟨3193,35000⟩ p68 p75 c66 (by decide +kernel)
theorem p77 : Derivation 16 inputs ⟨261,4⟩ ⟨114857753,250000000⟩ :=
  .step _ _ ⟨2739,1000⟩ ⟨137,50⟩ ⟨897,20000⟩ ⟨449,5000⟩ p69 p76 c67 (by decide +kernel)
theorem p78 : Derivation 16 inputs ⟨131,2⟩ ⟨112099271,250000000⟩ :=
  .step _ _ ⟨2759,1000⟩ ⟨69,25⟩ ⟨6179,140000⟩ ⟨3093,35000⟩ p70 p77 c68 (by decide +kernel)
theorem p79 : Derivation 16 inputs ⟨263,4⟩ ⟨437541727,1000000000⟩ :=
  .step _ _ ⟨2779,1000⟩ ⟨139,50⟩ ⟨6079,140000⟩ ⟨3043,35000⟩ p71 p78 c69 (by decide +kernel)
theorem p80 : Derivation 16 inputs ⟨66,1⟩ ⟨213432471,500000000⟩ :=
  .step _ _ ⟨2799,1000⟩ ⟨14,5⟩ ⟨5979,140000⟩ ⟨2993,35000⟩ p72 p79 c70 (by decide +kernel)
theorem p81 : Derivation 16 inputs ⟨265,4⟩ ⟨52045841,125000000⟩ :=
  .step _ _ ⟨2819,1000⟩ ⟨141,50⟩ ⟨5879,140000⟩ ⟨2943,35000⟩ p73 p80 c71 (by decide +kernel)
theorem p82 : Derivation 16 inputs ⟨133,2⟩ ⟨203023543,500000000⟩ :=
  .step _ _ ⟨2839,1000⟩ ⟨71,25⟩ ⟨5779,140000⟩ ⟨2893,35000⟩ p74 p81 c72 (by decide +kernel)
theorem p83 : Derivation 16 inputs ⟨267,4⟩ ⟨79181203,200000000⟩ :=
  .step _ _ ⟨2859,1000⟩ ⟨143,50⟩ ⟨5679,140000⟩ ⟨2843,35000⟩ p75 p82 c73 (by decide +kernel)
theorem p84 : Derivation 16 inputs ⟨67,1⟩ ⟨48244637,125000000⟩ :=
  .step _ _ ⟨2879,1000⟩ ⟨72,25⟩ ⟨797,20000⟩ ⟨399,5000⟩ p76 p83 c74 (by decide +kernel)
theorem p85 : Derivation 16 inputs ⟨269,4⟩ ⟨23511741,62500000⟩ :=
  .step _ _ ⟨2899,1000⟩ ⟨29,10⟩ ⟨5479,140000⟩ ⟨2743,35000⟩ p77 p84 c75 (by decide +kernel)
theorem p86 : Derivation 16 inputs ⟨135,2⟩ ⟨366592641,1000000000⟩ :=
  .step _ _ ⟨2919,1000⟩ ⟨73,25⟩ ⟨5379,140000⟩ ⟨2693,35000⟩ p78 p85 c76 (by decide +kernel)
theorem p87 : Derivation 16 inputs ⟨271,4⟩ ⟨178585391,500000000⟩ :=
  .step _ _ ⟨2939,1000⟩ ⟨147,50⟩ ⟨5279,140000⟩ ⟨2643,35000⟩ p79 p86 c77 (by decide +kernel)
theorem p88 : Derivation 16 inputs ⟨68,1⟩ ⟨43490321,125000000⟩ :=
  .step _ _ ⟨2959,1000⟩ ⟨74,25⟩ ⟨5179,140000⟩ ⟨2593,35000⟩ p80 p87 c78 (by decide +kernel)
theorem p89 : Derivation 16 inputs ⟨273,4⟩ ⟨169426463,500000000⟩ :=
  .step _ _ ⟨2979,1000⟩ ⟨149,50⟩ ⟨5079,140000⟩ ⟨2543,35000⟩ p81 p88 c79 (by decide +kernel)
theorem p90 : Derivation 16 inputs ⟨137,2⟩ ⟨65992371,200000000⟩ :=
  .step _ _ ⟨2999,1000⟩ ⟨3,1⟩ ⟨4979,140000⟩ ⟨2493,35000⟩ p82 p89 c80 (by decide +kernel)
theorem p91 : Derivation 16 inputs ⟨275,4⟩ ⟨64249871,200000000⟩ :=
  .step _ _ ⟨3019,1000⟩ ⟨151,50⟩ ⟨697,20000⟩ ⟨349,5000⟩ p83 p90 c81 (by decide +kernel)
theorem p92 : Derivation 16 inputs ⟨69,1⟩ ⟨312715427,1000000000⟩ :=
  .step _ _ ⟨3039,1000⟩ ⟨76,25⟩ ⟨4779,140000⟩ ⟨2393,35000⟩ p84 p91 c82 (by decide +kernel)
theorem p93 : Derivation 16 inputs ⟨277,4⟩ ⟨30436007,100000000⟩ :=
  .step _ _ ⟨3059,1000⟩ ⟨153,50⟩ ⟨4679,140000⟩ ⟨2343,35000⟩ p85 p92 c83 (by decide +kernel)
theorem p94 : Derivation 16 inputs ⟨139,2⟩ ⟨29616103,100000000⟩ :=
  .step _ _ ⟨1537,500⟩ ⟨123,40⟩ ⟨1151,35000⟩ ⟨4611,70000⟩ p86 p93 c84 (by decide +kernel)
theorem p95 : Derivation 16 inputs ⟨279,4⟩ ⟨288118173,1000000000⟩ :=
  .step _ _ ⟨1547,500⟩ ⟨619,200⟩ ⟨563,17500⟩ ⟨4511,70000⟩ p87 p94 c85 (by decide +kernel)
theorem p96 : Derivation 16 inputs ⟨70,1⟩ ⟨4378967,15625000⟩ :=
  .step _ _ ⟨1557,500⟩ ⟨623,200⟩ ⟨1101,35000⟩ ⟨4411,70000⟩ p88 p95 c86 (by decide +kernel)
theorem p97 : Derivation 16 inputs ⟨281,4⟩ ⟨54504111,200000000⟩ :=
  .step _ _ ⟨1567,500⟩ ⟨627,200⟩ ⟨58,1875⟩ ⟨1859,30000⟩ p89 p96 c87 (by decide +kernel)
theorem p98 : Derivation 16 inputs ⟨141,2⟩ ⟨264891389,1000000000⟩ :=
  .step _ _ ⟨3159,1000⟩ ⟨79,25⟩ ⟨1831,60000⟩ ⟨917,15000⟩ p90 p97 c88 (by decide +kernel)
theorem p99 : Derivation 16 inputs ⟨283,4⟩ ⟨257366389,1000000000⟩ :=
  .step _ _ ⟨398,125⟩ ⟨637,200⟩ ⟨301,10000⟩ ⟨603,10000⟩ p91 p98 c89 (by decide +kernel)
end WaringSmall.Degree16
