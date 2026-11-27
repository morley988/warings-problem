import WaringSmall.Degree13.C01

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace WaringSmall.Degree13
theorem p0 : Derivation 13 inputs ⟨38,1⟩ ⟨14190897,10000000⟩ :=
  .seed _ _ (by decide +kernel)
theorem p1 : Derivation 13 inputs ⟨40,1⟩ ⟨12190701,10000000⟩ :=
  .seed _ _ (by decide +kernel)
theorem p2 : Derivation 13 inputs ⟨153,4⟩ ⟨5576349,4000000⟩ :=
  .interpolate _ _ p0 p1 (by decide +kernel)
theorem p3 : Derivation 13 inputs ⟨77,2⟩ ⟨427839,312500⟩ :=
  .interpolate _ _ p0 p1 (by decide +kernel)
theorem p4 : Derivation 13 inputs ⟨155,4⟩ ⟨26881647,20000000⟩ :=
  .interpolate _ _ p0 p1 (by decide +kernel)
theorem p5 : Derivation 13 inputs ⟨39,1⟩ ⟨13190799,10000000⟩ :=
  .interpolate _ _ p0 p1 (by decide +kernel)
theorem p6 : Derivation 13 inputs ⟨157,4⟩ ⟨25881549,20000000⟩ :=
  .interpolate _ _ p0 p1 (by decide +kernel)
theorem p7 : Derivation 13 inputs ⟨79,2⟩ ⟨50763,40000⟩ :=
  .interpolate _ _ p0 p1 (by decide +kernel)
theorem p8 : Derivation 13 inputs ⟨159,4⟩ ⟨24881451,20000000⟩ :=
  .interpolate _ _ p0 p1 (by decide +kernel)
theorem p9 : Derivation 13 inputs ⟨161,4⟩ ⟨1195268961,1000000000⟩ :=
  .step _ _ ⟨927,500⟩ ⟨371,200⟩ ⟨1429,15000⟩ ⟨5719,30000⟩ p2 p1 c0 (by decide +kernel)
theorem p10 : Derivation 13 inputs ⟨81,2⟩ ⟨1171868961,1000000000⟩ :=
  .step _ _ ⟨937,500⟩ ⟨15,8⟩ ⟨117,1250⟩ ⟨1873,10000⟩ p3 p9 c1 (by decide +kernel)
theorem p11 : Derivation 13 inputs ⟨163,4⟩ ⟨1148781461,1000000000⟩ :=
  .step _ _ ⟨1889,1000⟩ ⟨189,100⟩ ⟨1847,20000⟩ ⟨231,1250⟩ p4 p10 c2 (by decide +kernel)
theorem p12 : Derivation 13 inputs ⟨41,1⟩ ⟨1126006461,1000000000⟩ :=
  .step _ _ ⟨238,125⟩ ⟨381,200⟩ ⟨911,10000⟩ ⟨1823,10000⟩ p5 p11 c3 (by decide +kernel)
theorem p13 : Derivation 13 inputs ⟨165,4⟩ ⟨1103543961,1000000000⟩ :=
  .step _ _ ⟨1919,1000⟩ ⟨48,25⟩ ⟨1797,20000⟩ ⟨899,5000⟩ p6 p12 c4 (by decide +kernel)
theorem p14 : Derivation 13 inputs ⟨83,2⟩ ⟨10812519,10000000⟩ :=
  .step _ _ ⟨481,250⟩ ⟨77,40⟩ ⟨2683,30000⟩ ⟨5369,30000⟩ p7 p13 c5 (by decide +kernel)
theorem p15 : Derivation 13 inputs ⟨167,4⟩ ⟨10591019,10000000⟩ :=
  .step _ _ ⟨967,500⟩ ⟨387,200⟩ ⟨443,5000⟩ ⟨1773,10000⟩ p8 p14 c6 (by decide +kernel)
theorem p16 : Derivation 13 inputs ⟨42,1⟩ ⟨518580117,500000000⟩ :=
  .step _ _ ⟨243,125⟩ ⟨389,200⟩ ⟨2633,30000⟩ ⟨5269,30000⟩ p1 p15 c7 (by decide +kernel)
theorem p17 : Derivation 13 inputs ⟨169,4⟩ ⟨253882767,250000000⟩ :=
  .step _ _ ⟨1959,1000⟩ ⟨49,25⟩ ⟨5191,60000⟩ ⟨2597,15000⟩ p9 p16 c8 (by decide +kernel)
theorem p18 : Derivation 13 inputs ⟨85,2⟩ ⟨497107201,500000000⟩ :=
  .step _ _ ⟨987,500⟩ ⟨79,40⟩ ⟨1279,15000⟩ ⟨5119,30000⟩ p10 p17 c9 (by decide +kernel)
theorem p19 : Derivation 13 inputs ⟨171,4⟩ ⟨243302559,250000000⟩ :=
  .step _ _ ⟨1989,1000⟩ ⟨199,100⟩ ⟨5041,60000⟩ ⟨1261,7500⟩ p11 p18 c10 (by decide +kernel)
theorem p20 : Derivation 13 inputs ⟨43,1⟩ ⟨95251857,100000000⟩ :=
  .step _ _ ⟨501,250⟩ ⟨401,200⟩ ⟨2483,30000⟩ ⟨4969,30000⟩ p12 p19 c11 (by decide +kernel)
theorem p21 : Derivation 13 inputs ⟨173,4⟩ ⟨116519387,125000000⟩ :=
  .step _ _ ⟨2019,1000⟩ ⟨101,50⟩ ⟨4891,60000⟩ ⟨2447,15000⟩ p13 p20 c12 (by decide +kernel)
theorem p22 : Derivation 13 inputs ⟨87,2⟩ ⟨91208843,100000000⟩ :=
  .step _ _ ⟨1017,500⟩ ⟨407,200⟩ ⟨301,3750⟩ ⟨4819,30000⟩ p14 p21 c13 (by decide +kernel)
theorem p23 : Derivation 13 inputs ⟨175,4⟩ ⟨111541783,125000000⟩ :=
  .step _ _ ⟨2049,1000⟩ ⟨41,20⟩ ⟨4741,60000⟩ ⟨593,3750⟩ p15 p22 c14 (by decide +kernel)
theorem p24 : Derivation 13 inputs ⟨44,1⟩ ⟨87289001,100000000⟩ :=
  .step _ _ ⟨2059,1000⟩ ⟨103,50⟩ ⟨4691,60000⟩ ⟨2347,15000⟩ p16 p23 c15 (by decide +kernel)
theorem p25 : Derivation 13 inputs ⟨177,4⟩ ⟨853656677,1000000000⟩ :=
  .step _ _ ⟨1037,500⟩ ⟨83,40⟩ ⟨577,7500⟩ ⟨4619,30000⟩ p17 p24 c16 (by decide +kernel)
theorem p26 : Derivation 13 inputs ⟨89,2⟩ ⟨208683961,250000000⟩ :=
  .step _ _ ⟨2089,1000⟩ ⟨209,100⟩ ⟨4541,60000⟩ ⟨284,1875⟩ p18 p25 c17 (by decide +kernel)
theorem p27 : Derivation 13 inputs ⟨179,4⟩ ⟨163214843,200000000⟩ :=
  .step _ _ ⟨2099,1000⟩ ⟨21,10⟩ ⟨1497,20000⟩ ⟨749,5000⟩ p19 p26 c18 (by decide +kernel)
theorem p28 : Derivation 13 inputs ⟨45,1⟩ ⟨159534843,200000000⟩ :=
  .step _ _ ⟨1057,500⟩ ⟨423,200⟩ ⟨46,625⟩ ⟨1473,10000⟩ p20 p27 c19 (by decide +kernel)
theorem p29 : Derivation 13 inputs ⟨181,4⟩ ⟨155917343,200000000⟩ :=
  .step _ _ ⟨2129,1000⟩ ⟨213,100⟩ ⟨1447,20000⟩ ⟨181,1250⟩ p21 p28 c20 (by decide +kernel)
theorem p30 : Derivation 13 inputs ⟨91,2⟩ ⟨152362343,200000000⟩ :=
  .step _ _ ⟨268,125⟩ ⟨429,200⟩ ⟨711,10000⟩ ⟨1423,10000⟩ p22 p29 c21 (by decide +kernel)
theorem p31 : Derivation 13 inputs ⟨183,4⟩ ⟨148869843,200000000⟩ :=
  .step _ _ ⟨2159,1000⟩ ⟨54,25⟩ ⟨1397,20000⟩ ⟨699,5000⟩ p23 p30 c22 (by decide +kernel)
theorem p32 : Derivation 13 inputs ⟨46,1⟩ ⟨145439843,200000000⟩ :=
  .step _ _ ⟨1087,500⟩ ⟨87,40⟩ ⟨343,5000⟩ ⟨1373,10000⟩ p24 p31 c23 (by decide +kernel)
theorem p33 : Derivation 13 inputs ⟨185,4⟩ ⟨710257549,1000000000⟩ :=
  .step _ _ ⟨273,125⟩ ⟨437,200⟩ ⟨2033,30000⟩ ⟨4069,30000⟩ p25 p32 c24 (by decide +kernel)
theorem p34 : Derivation 13 inputs ⟨93,2⟩ ⟨693628383,1000000000⟩ :=
  .step _ _ ⟨2199,1000⟩ ⟨11,5⟩ ⟨3991,60000⟩ ⟨1997,15000⟩ p26 p33 c25 (by decide +kernel)
theorem p35 : Derivation 13 inputs ⟨187,4⟩ ⟨677311717,1000000000⟩ :=
  .step _ _ ⟨1107,500⟩ ⟨443,200⟩ ⟨979,15000⟩ ⟨3919,30000⟩ p27 p34 c26 (by decide +kernel)
theorem p36 : Derivation 13 inputs ⟨47,1⟩ ⟨132242113,200000000⟩ :=
  .step _ _ ⟨278,125⟩ ⟨89,40⟩ ⟨1933,30000⟩ ⟨3869,30000⟩ p28 p35 c27 (by decide +kernel)
theorem p37 : Derivation 13 inputs ⟨189,4⟩ ⟨161353683,250000000⟩ :=
  .step _ _ ⟨2239,1000⟩ ⟨56,25⟩ ⟨3791,60000⟩ ⟨1897,15000⟩ p29 p36 c28 (by decide +kernel)
theorem p38 : Derivation 13 inputs ⟨95,2⟩ ⟨201559,320000⟩ :=
  .step _ _ ⟨1127,500⟩ ⟨451,200⟩ ⟨272,4375⟩ ⟨8711,70000⟩ p30 p37 c29 (by decide +kernel)
theorem p39 : Derivation 13 inputs ⟨191,4⟩ ⟨614462947,1000000000⟩ :=
  .step _ _ ⟨2269,1000⟩ ⟨227,100⟩ ⟨8629,140000⟩ ⟨2159,17500⟩ p31 p38 c30 (by decide +kernel)
theorem p40 : Derivation 13 inputs ⟨48,1⟩ ⟨59923259,100000000⟩ :=
  .step _ _ ⟨2289,1000⟩ ⟨229,100⟩ ⟨8529,140000⟩ ⟨1067,8750⟩ p32 p39 c31 (by decide +kernel)
theorem p41 : Derivation 13 inputs ⟨193,4⟩ ⟨116836161,200000000⟩ :=
  .step _ _ ⟨2309,1000⟩ ⟨231,100⟩ ⟨8429,140000⟩ ⟨2109,17500⟩ p33 p40 c32 (by decide +kernel)
theorem p42 : Derivation 13 inputs ⟨97,2⟩ ⟨284676117,500000000⟩ :=
  .step _ _ ⟨1167,500⟩ ⟨467,200⟩ ⟨519,8750⟩ ⟨8311,70000⟩ p34 p41 c33 (by decide +kernel)
theorem p43 : Derivation 13 inputs ⟨195,4⟩ ⟨277351117,500000000⟩ :=
  .step _ _ ⟨1177,500⟩ ⟨471,200⟩ ⟨293,5000⟩ ⟨1173,10000⟩ p35 p42 c34 (by decide +kernel)
theorem p44 : Derivation 13 inputs ⟨49,1⟩ ⟨540275449,1000000000⟩ :=
  .step _ _ ⟨2379,1000⟩ ⟨119,50⟩ ⟨8079,140000⟩ ⟨4043,35000⟩ p36 p43 c35 (by decide +kernel)
theorem p45 : Derivation 13 inputs ⟨197,4⟩ ⟨263035939,500000000⟩ :=
  .step _ _ ⟨601,250⟩ ⟨481,200⟩ ⟨3977,70000⟩ ⟨7961,70000⟩ p37 p44 c36 (by decide +kernel)
theorem p46 : Derivation 13 inputs ⟨99,2⟩ ⟨128034041,250000000⟩ :=
  .step _ _ ⟨1217,500⟩ ⟨487,200⟩ ⟨1951,35000⟩ ⟨7811,70000⟩ p38 p45 c37 (by decide +kernel)
theorem p47 : Derivation 13 inputs ⟨199,4⟩ ⟨31151479,62500000⟩ :=
  .step _ _ ⟨2459,1000⟩ ⟨123,50⟩ ⟨1097,20000⟩ ⟨549,5000⟩ p39 p46 c38 (by decide +kernel)
theorem p48 : Derivation 13 inputs ⟨50,1⟩ ⟨484934379,1000000000⟩ :=
  .step _ _ ⟨621,250⟩ ⟨497,200⟩ ⟨3777,70000⟩ ⟨7561,70000⟩ p40 p47 c39 (by decide +kernel)
theorem p49 : Derivation 13 inputs ⟨201,4⟩ ⟨94331719,200000000⟩ :=
  .step _ _ ⟨313,125⟩ ⟨501,200⟩ ⟨3727,70000⟩ ⟨7461,70000⟩ p41 p48 c40 (by decide +kernel)
theorem p50 : Derivation 13 inputs ⟨101,2⟩ ⟨458591327,1000000000⟩ :=
  .step _ _ ⟨2529,1000⟩ ⟨253,100⟩ ⟨1047,20000⟩ ⟨131,1250⟩ p42 p49 c41 (by decide +kernel)
theorem p51 : Derivation 13 inputs ⟨203,4⟩ ⟨222863521,500000000⟩ :=
  .step _ _ ⟨1277,500⟩ ⟨511,200⟩ ⟨1801,35000⟩ ⟨7211,70000⟩ p43 p50 c42 (by decide +kernel)
theorem p52 : Derivation 13 inputs ⟨51,1⟩ ⟨54136639,125000000⟩ :=
  .step _ _ ⟨2579,1000⟩ ⟨129,50⟩ ⟨7079,140000⟩ ⟨3543,35000⟩ p44 p51 c43 (by decide +kernel)
theorem p53 : Derivation 13 inputs ⟨205,4⟩ ⟨84139127,200000000⟩ :=
  .step _ _ ⟨651,250⟩ ⟨521,200⟩ ⟨3477,70000⟩ ⟨6961,70000⟩ p45 p52 c44 (by decide +kernel)
theorem p54 : Derivation 13 inputs ⟨103,2⟩ ⟨81709127,200000000⟩ :=
  .step _ _ ⟨1317,500⟩ ⟨527,200⟩ ⟨243,5000⟩ ⟨973,10000⟩ p46 p53 c45 (by decide +kernel)
theorem p55 : Derivation 13 inputs ⟨207,4⟩ ⟨7932377,20000000⟩ :=
  .step _ _ ⟨2659,1000⟩ ⟨133,50⟩ ⟨6679,140000⟩ ⟨3343,35000⟩ p47 p54 c46 (by decide +kernel)
theorem p56 : Derivation 13 inputs ⟨52,1⟩ ⟨384915279,1000000000⟩ :=
  .step _ _ ⟨671,250⟩ ⟨537,200⟩ ⟨3277,70000⟩ ⟨6561,70000⟩ p48 p55 c47 (by decide +kernel)
theorem p57 : Derivation 13 inputs ⟨209,4⟩ ⟨186717461,500000000⟩ :=
  .step _ _ ⟨2709,1000⟩ ⟨271,100⟩ ⟨6429,140000⟩ ⟨1609,17500⟩ p49 p56 c48 (by decide +kernel)
theorem p58 : Derivation 13 inputs ⟨105,2⟩ ⟨18108889,50000000⟩ :=
  .step _ _ ⟨1367,500⟩ ⟨547,200⟩ ⟨197,4375⟩ ⟨6311,70000⟩ p50 p57 c49 (by decide +kernel)
theorem p59 : Derivation 13 inputs ⟨211,4⟩ ⟨87785963,250000000⟩ :=
  .step _ _ ⟨2759,1000⟩ ⟨69,25⟩ ⟨6179,140000⟩ ⟨3093,35000⟩ p51 p58 c50 (by decide +kernel)
theorem p60 : Derivation 13 inputs ⟨53,1⟩ ⟨340344557,1000000000⟩ :=
  .step _ _ ⟨348,125⟩ ⟨557,200⟩ ⟨3027,70000⟩ ⟨6061,70000⟩ p52 p59 c51 (by decide +kernel)
theorem p61 : Derivation 13 inputs ⟨213,4⟩ ⟨329793017,1000000000⟩ :=
  .step _ _ ⟨2809,1000⟩ ⟨281,100⟩ ⟨847,20000⟩ ⟨53,625⟩ p53 p60 c52 (by decide +kernel)
theorem p62 : Derivation 13 inputs ⟨107,2⟩ ⟨2555787,8000000⟩ :=
  .step _ _ ⟨2839,1000⟩ ⟨71,25⟩ ⟨5779,140000⟩ ⟨2893,35000⟩ p54 p61 c53 (by decide +kernel)
theorem p63 : Derivation 13 inputs ⟨215,4⟩ ⟨309376947,1000000000⟩ :=
  .step _ _ ⟨358,125⟩ ⟨573,200⟩ ⟨2827,70000⟩ ⟨5661,70000⟩ p55 p62 c54 (by decide +kernel)
theorem p64 : Derivation 13 inputs ⟨54,1⟩ ⟨299503733,1000000000⟩ :=
  .step _ _ ⟨2889,1000⟩ ⟨289,100⟩ ⟨5529,140000⟩ ⟨346,4375⟩ p56 p63 c55 (by decide +kernel)
theorem p65 : Derivation 13 inputs ⟨217,4⟩ ⟨289853733,1000000000⟩ :=
  .step _ _ ⟨1457,500⟩ ⟨583,200⟩ ⟨193,5000⟩ ⟨773,10000⟩ p57 p64 c56 (by decide +kernel)
theorem p66 : Derivation 13 inputs ⟨109,2⟩ ⟨70106737,250000000⟩ :=
  .step _ _ ⟨2939,1000⟩ ⟨147,50⟩ ⟨5279,140000⟩ ⟨2643,35000⟩ p58 p65 c57 (by decide +kernel)
theorem p67 : Derivation 13 inputs ⟨219,4⟩ ⟨27121811,100000000⟩ :=
  .step _ _ ⟨2959,1000⟩ ⟨74,25⟩ ⟨5179,140000⟩ ⟨2593,35000⟩ p59 p66 c58 (by decide +kernel)
theorem p68 : Derivation 13 inputs ⟨55,1⟩ ⟨262222391,1000000000⟩ :=
  .step _ _ ⟨373,125⟩ ⟨597,200⟩ ⟨361,10000⟩ ⟨723,10000⟩ p60 p67 c59 (by decide +kernel)
theorem p69 : Derivation 13 inputs ⟨221,4⟩ ⟨126729309,500000000⟩ :=
  .step _ _ ⟨3009,1000⟩ ⟨301,100⟩ ⟨4929,140000⟩ ⟨617,8750⟩ p61 p68 c60 (by decide +kernel)
theorem p70 : Derivation 13 inputs ⟨111,2⟩ ⟨48982641,200000000⟩ :=
  .step _ _ ⟨1517,500⟩ ⟨607,200⟩ ⟨1201,35000⟩ ⟨4811,70000⟩ p62 p69 c61 (by decide +kernel)
theorem p71 : Derivation 13 inputs ⟨223,4⟩ ⟨59144543,250000000⟩ :=
  .step _ _ ⟨3059,1000⟩ ⟨153,50⟩ ⟨4679,140000⟩ ⟨2343,35000⟩ p63 p70 c62 (by decide +kernel)
theorem p72 : Derivation 13 inputs ⟨56,1⟩ ⟨228452233,1000000000⟩ :=
  .step _ _ ⟨771,250⟩ ⟨617,200⟩ ⟨2277,70000⟩ ⟨4561,70000⟩ p64 p71 c63 (by decide +kernel)
theorem p73 : Derivation 13 inputs ⟨225,4⟩ ⟨44108661,200000000⟩ :=
  .step _ _ ⟨3109,1000⟩ ⟨311,100⟩ ⟨4429,140000⟩ ⟨1109,17500⟩ p65 p72 c64 (by decide +kernel)
theorem p74 : Derivation 13 inputs ⟨113,2⟩ ⟨212822483,1000000000⟩ :=
  .step _ _ ⟨1567,500⟩ ⟨627,200⟩ ⟨58,1875⟩ ⟨1859,30000⟩ p66 p73 c65 (by decide +kernel)
theorem p75 : Derivation 13 inputs ⟨227,4⟩ ⟨4104283,20000000⟩ :=
  .step _ _ ⟨791,250⟩ ⟨633,200⟩ ⟨913,30000⟩ ⟨1829,30000⟩ p67 p74 c66 (by decide +kernel)
theorem p76 : Derivation 13 inputs ⟨57,1⟩ ⟨3955033,20000000⟩ :=
  .step _ _ ⟨3199,1000⟩ ⟨16,5⟩ ⟨597,20000⟩ ⟨299,5000⟩ p68 p75 c67 (by decide +kernel)
theorem p77 : Derivation 13 inputs ⟨229,4⟩ ⟨23804373,125000000⟩ :=
  .step _ _ ⟨1617,500⟩ ⟨647,200⟩ ⟨439,15000⟩ ⟨1759,30000⟩ p69 p76 c68 (by decide +kernel)
theorem p78 : Derivation 13 inputs ⟨115,2⟩ ⟨22910623,125000000⟩ :=
  .step _ _ ⟨1637,500⟩ ⟨131,40⟩ ⟨143,5000⟩ ⟨573,10000⟩ p70 p77 c69 (by decide +kernel)
theorem p79 : Derivation 13 inputs ⟨231,4⟩ ⟨176301651,1000000000⟩ :=
  .step _ _ ⟨1657,500⟩ ⟨663,200⟩ ⟨419,15000⟩ ⟨1679,30000⟩ p71 p78 c70 (by decide +kernel)
theorem p80 : Derivation 13 inputs ⟨58,1⟩ ⟨84752909,500000000⟩ :=
  .step _ _ ⟨3359,1000⟩ ⟨84,25⟩ ⟨1631,60000⟩ ⟨817,15000⟩ p72 p79 c71 (by decide +kernel)
theorem p81 : Derivation 13 inputs ⟨233,4⟩ ⟨81439857,500000000⟩ :=
  .step _ _ ⟨3399,1000⟩ ⟨17,5⟩ ⟨1591,60000⟩ ⟨797,15000⟩ p73 p80 c72 (by decide +kernel)
theorem p82 : Derivation 13 inputs ⟨117,2⟩ ⟨2444389,15625000⟩ :=
  .step _ _ ⟨861,250⟩ ⟨689,200⟩ ⟨773,30000⟩ ⟨1549,30000⟩ p74 p81 c73 (by decide +kernel)
theorem p83 : Derivation 13 inputs ⟨235,4⟩ ⟨15018673,100000000⟩ :=
  .step _ _ ⟨3489,1000⟩ ⟨349,100⟩ ⟨1501,60000⟩ ⟨94,1875⟩ p75 p82 c74 (by decide +kernel)
theorem p84 : Derivation 13 inputs ⟨59,1⟩ ⟨14409923,100000000⟩ :=
  .step _ _ ⟨3529,1000⟩ ⟨353,100⟩ ⟨487,20000⟩ ⟨61,1250⟩ p76 p83 c75 (by decide +kernel)
theorem p85 : Derivation 13 inputs ⟨237,4⟩ ⟨138178397,1000000000⟩ :=
  .step _ _ ⟨3569,1000⟩ ⟨357,100⟩ ⟨1421,60000⟩ ⟨89,1875⟩ p77 p84 c76 (by decide +kernel)
theorem p86 : Derivation 13 inputs ⟨119,2⟩ ⟨132424231,1000000000⟩ :=
  .step _ _ ⟨3609,1000⟩ ⟨361,100⟩ ⟨1381,60000⟩ ⟨173,3750⟩ p78 p85 c77 (by decide +kernel)
theorem p87 : Derivation 13 inputs ⟨239,4⟩ ⟨126836731,1000000000⟩ :=
  .step _ _ ⟨3649,1000⟩ ⟨73,20⟩ ⟨447,20000⟩ ⟨28,625⟩ p79 p86 c78 (by decide +kernel)
theorem p88 : Derivation 13 inputs ⟨60,1⟩ ⟨60707949,500000000⟩ :=
  .step _ _ ⟨3689,1000⟩ ⟨369,100⟩ ⟨1301,60000⟩ ⟨163,3750⟩ p80 p87 c79 (by decide +kernel)
theorem p89 : Derivation 13 inputs ⟨241,4⟩ ⟨29040433,250000000⟩ :=
  .step _ _ ⟨3729,1000⟩ ⟨373,100⟩ ⟨1261,60000⟩ ⟨79,1875⟩ p81 p88 c80 (by decide +kernel)
theorem p90 : Derivation 13 inputs ⟨121,2⟩ ⟨111085071,1000000000⟩ :=
  .step _ _ ⟨3769,1000⟩ ⟨377,100⟩ ⟨407,20000⟩ ⟨51,1250⟩ p82 p89 c81 (by decide +kernel)
theorem p91 : Derivation 13 inputs ⟨243,4⟩ ⟨106182019,1000000000⟩ :=
  .step _ _ ⟨3809,1000⟩ ⟨381,100⟩ ⟨1181,60000⟩ ⟨74,1875⟩ p83 p90 c82 (by decide +kernel)
theorem p92 : Derivation 13 inputs ⟨61,1⟩ ⟨50717387,500000000⟩ :=
  .step _ _ ⟨3849,1000⟩ ⟨77,20⟩ ⟨1141,60000⟩ ⟨143,3750⟩ p84 p91 c83 (by decide +kernel)
theorem p93 : Derivation 13 inputs ⟨245,4⟩ ⟨48423637,500000000⟩ :=
  .step _ _ ⟨3889,1000⟩ ⟨389,100⟩ ⟨367,20000⟩ ⟨23,625⟩ p85 p92 c84 (by decide +kernel)
theorem p94 : Derivation 13 inputs ⟨123,2⟩ ⟨92426441,1000000000⟩ :=
  .step _ _ ⟨3929,1000⟩ ⟨393,100⟩ ⟨1061,60000⟩ ⟨133,3750⟩ p86 p93 c85 (by decide +kernel)
theorem p95 : Derivation 13 inputs ⟨247,4⟩ ⟨17632257,200000000⟩ :=
  .step _ _ ⟨991,250⟩ ⟨793,200⟩ ⟨171,10000⟩ ⟨343,10000⟩ p87 p94 c86 (by decide +kernel)
theorem p96 : Derivation 13 inputs ⟨62,1⟩ ⟨10506619,125000000⟩ :=
  .step _ _ ⟨1001,250⟩ ⟨801,200⟩ ⟨493,30000⟩ ⟨989,30000⟩ p88 p95 c87 (by decide +kernel)
theorem p97 : Derivation 13 inputs ⟨249,4⟩ ⟨20022613,250000000⟩ :=
  .step _ _ ⟨4039,1000⟩ ⟨101,25⟩ ⟨317,20000⟩ ⟨159,5000⟩ p89 p96 c88 (by decide +kernel)
theorem p98 : Derivation 13 inputs ⟨125,2⟩ ⟨15251397,200000000⟩ :=
  .step _ _ ⟨4079,1000⟩ ⟨102,25⟩ ⟨9507,620000⟩ ⟨4769,155000⟩ p90 p97 c89 (by decide +kernel)
theorem p99 : Derivation 13 inputs ⟨251,4⟩ ⟨18128561,250000000⟩ :=
  .step _ _ ⟨1031,250⟩ ⟨33,8⟩ ⟨4641,310000⟩ ⟨9313,310000⟩ p91 p98 c90 (by decide +kernel)
end WaringSmall.Degree13
