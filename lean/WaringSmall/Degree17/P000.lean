import WaringSmall.Degree17.C07

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace WaringSmall.Degree17
theorem p0 : Derivation 17 inputs ⟨50,1⟩ ⟨19159903,10000000⟩ :=
  .seed _ _ (by decide +kernel)
theorem p1 : Derivation 17 inputs ⟨52,1⟩ ⟨17117441,10000000⟩ :=
  .seed _ _ (by decide +kernel)
theorem p2 : Derivation 17 inputs ⟨1201,24⟩ ⟨458816441,240000000⟩ :=
  .interpolate _ _ p0 p1 (by decide +kernel)
theorem p3 : Derivation 17 inputs ⟨601,12⟩ ⟨45779521,24000000⟩ :=
  .interpolate _ _ p0 p1 (by decide +kernel)
theorem p4 : Derivation 17 inputs ⟨401,8⟩ ⟨152257993,80000000⟩ :=
  .interpolate _ _ p0 p1 (by decide +kernel)
theorem p5 : Derivation 17 inputs ⟨301,6⟩ ⟨113938187,60000000⟩ :=
  .interpolate _ _ p0 p1 (by decide +kernel)
theorem p6 : Derivation 17 inputs ⟨1205,24⟩ ⟨454731517,240000000⟩ :=
  .interpolate _ _ p0 p1 (by decide +kernel)
theorem p7 : Derivation 17 inputs ⟨201,4⟩ ⟨75618381,40000000⟩ :=
  .interpolate _ _ p0 p1 (by decide +kernel)
theorem p8 : Derivation 17 inputs ⟨1207,24⟩ ⟨90537811,48000000⟩ :=
  .interpolate _ _ p0 p1 (by decide +kernel)
theorem p9 : Derivation 17 inputs ⟨151,3⟩ ⟨28229239,15000000⟩ :=
  .interpolate _ _ p0 p1 (by decide +kernel)
theorem p10 : Derivation 17 inputs ⟨403,8⟩ ⟨150215531,80000000⟩ :=
  .interpolate _ _ p0 p1 (by decide +kernel)
theorem p11 : Derivation 17 inputs ⟨605,12⟩ ⟨224812681,120000000⟩ :=
  .interpolate _ _ p0 p1 (by decide +kernel)
theorem p12 : Derivation 17 inputs ⟨1211,24⟩ ⟨448604131,240000000⟩ :=
  .interpolate _ _ p0 p1 (by decide +kernel)
theorem p13 : Derivation 17 inputs ⟨101,2⟩ ⟨1491943,800000⟩ :=
  .interpolate _ _ p0 p1 (by decide +kernel)
theorem p14 : Derivation 17 inputs ⟨1213,24⟩ ⟨446561669,240000000⟩ :=
  .interpolate _ _ p0 p1 (by decide +kernel)
theorem p15 : Derivation 17 inputs ⟨607,12⟩ ⟨222770219,120000000⟩ :=
  .interpolate _ _ p0 p1 (by decide +kernel)
theorem p16 : Derivation 17 inputs ⟨405,8⟩ ⟨148173069,80000000⟩ :=
  .interpolate _ _ p0 p1 (by decide +kernel)
theorem p17 : Derivation 17 inputs ⟨152,3⟩ ⟨55437247,30000000⟩ :=
  .interpolate _ _ p0 p1 (by decide +kernel)
theorem p18 : Derivation 17 inputs ⟨1217,24⟩ ⟨88495349,48000000⟩ :=
  .interpolate _ _ p0 p1 (by decide +kernel)
theorem p19 : Derivation 17 inputs ⟨203,4⟩ ⟨73575919,40000000⟩ :=
  .interpolate _ _ p0 p1 (by decide +kernel)
theorem p20 : Derivation 17 inputs ⟨1219,24⟩ ⟨440434283,240000000⟩ :=
  .interpolate _ _ p0 p1 (by decide +kernel)
theorem p21 : Derivation 17 inputs ⟨305,6⟩ ⟨109853263,60000000⟩ :=
  .interpolate _ _ p0 p1 (by decide +kernel)
theorem p22 : Derivation 17 inputs ⟨407,8⟩ ⟨146130607,80000000⟩ :=
  .interpolate _ _ p0 p1 (by decide +kernel)
theorem p23 : Derivation 17 inputs ⟨611,12⟩ ⟨43737059,24000000⟩ :=
  .interpolate _ _ p0 p1 (by decide +kernel)
theorem p24 : Derivation 17 inputs ⟨1223,24⟩ ⟨436349359,240000000⟩ :=
  .interpolate _ _ p0 p1 (by decide +kernel)
theorem p25 : Derivation 17 inputs ⟨51,1⟩ ⟨1133667,625000⟩ :=
  .interpolate _ _ p0 p1 (by decide +kernel)
theorem p26 : Derivation 17 inputs ⟨1225,24⟩ ⟨434306897,240000000⟩ :=
  .interpolate _ _ p0 p1 (by decide +kernel)
theorem p27 : Derivation 17 inputs ⟨613,12⟩ ⟨216642833,120000000⟩ :=
  .interpolate _ _ p0 p1 (by decide +kernel)
theorem p28 : Derivation 17 inputs ⟨409,8⟩ ⟨28817629,16000000⟩ :=
  .interpolate _ _ p0 p1 (by decide +kernel)
theorem p29 : Derivation 17 inputs ⟨307,6⟩ ⟨107810801,60000000⟩ :=
  .interpolate _ _ p0 p1 (by decide +kernel)
theorem p30 : Derivation 17 inputs ⟨1229,24⟩ ⟨430221973,240000000⟩ :=
  .interpolate _ _ p0 p1 (by decide +kernel)
theorem p31 : Derivation 17 inputs ⟨205,4⟩ ⟨71533457,40000000⟩ :=
  .interpolate _ _ p0 p1 (by decide +kernel)
theorem p32 : Derivation 17 inputs ⟨1231,24⟩ ⟨428179511,240000000⟩ :=
  .interpolate _ _ p0 p1 (by decide +kernel)
theorem p33 : Derivation 17 inputs ⟨154,3⟩ ⟨10678957,6000000⟩ :=
  .interpolate _ _ p0 p1 (by decide +kernel)
theorem p34 : Derivation 17 inputs ⟨411,8⟩ ⟨142045683,80000000⟩ :=
  .interpolate _ _ p0 p1 (by decide +kernel)
theorem p35 : Derivation 17 inputs ⟨617,12⟩ ⟨212557909,120000000⟩ :=
  .interpolate _ _ p0 p1 (by decide +kernel)
theorem p36 : Derivation 17 inputs ⟨1235,24⟩ ⟨424094587,240000000⟩ :=
  .interpolate _ _ p0 p1 (by decide +kernel)
theorem p37 : Derivation 17 inputs ⟨103,2⟩ ⟨35256113,20000000⟩ :=
  .interpolate _ _ p0 p1 (by decide +kernel)
theorem p38 : Derivation 17 inputs ⟨1237,24⟩ ⟨3376417,1920000⟩ :=
  .interpolate _ _ p0 p1 (by decide +kernel)
theorem p39 : Derivation 17 inputs ⟨619,12⟩ ⟨210515447,120000000⟩ :=
  .interpolate _ _ p0 p1 (by decide +kernel)
theorem p40 : Derivation 17 inputs ⟨413,8⟩ ⟨140003221,80000000⟩ :=
  .interpolate _ _ p0 p1 (by decide +kernel)
theorem p41 : Derivation 17 inputs ⟨155,3⟩ ⟨26186777,15000000⟩ :=
  .interpolate _ _ p0 p1 (by decide +kernel)
theorem p42 : Derivation 17 inputs ⟨1241,24⟩ ⟨417967201,240000000⟩ :=
  .interpolate _ _ p0 p1 (by decide +kernel)
theorem p43 : Derivation 17 inputs ⟨207,4⟩ ⟨13898199,8000000⟩ :=
  .interpolate _ _ p0 p1 (by decide +kernel)
theorem p44 : Derivation 17 inputs ⟨1243,24⟩ ⟨415924739,240000000⟩ :=
  .interpolate _ _ p0 p1 (by decide +kernel)
theorem p45 : Derivation 17 inputs ⟨311,6⟩ ⟨103725877,60000000⟩ :=
  .interpolate _ _ p0 p1 (by decide +kernel)
theorem p46 : Derivation 17 inputs ⟨415,8⟩ ⟨137960759,80000000⟩ :=
  .interpolate _ _ p0 p1 (by decide +kernel)
theorem p47 : Derivation 17 inputs ⟨623,12⟩ ⟨206430523,120000000⟩ :=
  .interpolate _ _ p0 p1 (by decide +kernel)
theorem p48 : Derivation 17 inputs ⟨1247,24⟩ ⟨82367963,48000000⟩ :=
  .interpolate _ _ p0 p1 (by decide +kernel)
theorem p49 : Derivation 17 inputs ⟨1249,24⟩ ⟨53363991,31250000⟩ :=
  .step _ _ ⟨9099,5000⟩ ⟨91,50⟩ ⟨14747,150000⟩ ⟨58991,300000⟩ p2 p1 c0 (by decide +kernel)
theorem p50 : Derivation 17 inputs ⟨625,12⟩ ⟨1703551323,1000000000⟩ :=
  .step _ _ ⟨9099,5000⟩ ⟨91,50⟩ ⟨14747,150000⟩ ⟨58991,300000⟩ p3 p1 c0 (by decide +kernel)
theorem p51 : Derivation 17 inputs ⟨417,8⟩ ⟨212434037,125000000⟩ :=
  .step _ _ ⟨2281,1250⟩ ⟨73,40⟩ ⟨29369,300000⟩ ⟨58741,300000⟩ p4 p50 c1 (by decide +kernel)
theorem p52 : Derivation 17 inputs ⟨313,6⟩ ⟨423848317,250000000⟩ :=
  .step _ _ ⟨2281,1250⟩ ⟨73,40⟩ ⟨29369,300000⟩ ⟨58741,300000⟩ p5 p50 c1 (by decide +kernel)
theorem p53 : Derivation 17 inputs ⟨1253,24⟩ ⟨845665801,500000000⟩ :=
  .step _ _ ⟨9149,5000⟩ ⟨183,100⟩ ⟨2437,25000⟩ ⟨19497,100000⟩ p6 p52 c2 (by decide +kernel)
theorem p54 : Derivation 17 inputs ⟨209,4⟩ ⟨337453987,200000000⟩ :=
  .step _ _ ⟨9149,5000⟩ ⟨183,100⟩ ⟨2437,25000⟩ ⟨19497,100000⟩ p7 p52 c2 (by decide +kernel)
theorem p55 : Derivation 17 inputs ⟨1255,24⟩ ⟨420802067,250000000⟩ :=
  .step _ _ ⟨9149,5000⟩ ⟨183,100⟩ ⟨2437,25000⟩ ⟨19497,100000⟩ p8 p52 c2 (by decide +kernel)
theorem p56 : Derivation 17 inputs ⟨157,3⟩ ⟨1679163963,1000000000⟩ :=
  .step _ _ ⟨4587,2500⟩ ⟨367,200⟩ ⟨29119,300000⟩ ⟨58241,300000⟩ p9 p55 c3 (by decide +kernel)
theorem p57 : Derivation 17 inputs ⟨419,8⟩ ⟨1675119657,1000000000⟩ :=
  .step _ _ ⟨4587,2500⟩ ⟨367,200⟩ ⟨29119,300000⟩ ⟨58241,300000⟩ p10 p55 c3 (by decide +kernel)
theorem p58 : Derivation 17 inputs ⟨629,12⟩ ⟨1671092713,1000000000⟩ :=
  .step _ _ ⟨9199,5000⟩ ⟨46,25⟩ ⟨14497,150000⟩ ⟨57991,300000⟩ p11 p57 c4 (by decide +kernel)
theorem p59 : Derivation 17 inputs ⟨1259,24⟩ ⟨1667065769,1000000000⟩ :=
  .step _ _ ⟨9199,5000⟩ ⟨46,25⟩ ⟨14497,150000⟩ ⟨57991,300000⟩ p12 p57 c4 (by decide +kernel)
theorem p60 : Derivation 17 inputs ⟨105,2⟩ ⟨831528093,500000000⟩ :=
  .step _ _ ⟨1153,625⟩ ⟨369,200⟩ ⟨9623,100000⟩ ⟨19247,100000⟩ p13 p59 c5 (by decide +kernel)
theorem p61 : Derivation 17 inputs ⟨1261,24⟩ ⟨1659046603,1000000000⟩ :=
  .step _ _ ⟨1153,625⟩ ⟨369,200⟩ ⟨9623,100000⟩ ⟨19247,100000⟩ p14 p59 c5 (by decide +kernel)
theorem p62 : Derivation 17 inputs ⟨631,12⟩ ⟨1655037019,1000000000⟩ :=
  .step _ _ ⟨1153,625⟩ ⟨369,200⟩ ⟨9623,100000⟩ ⟨19247,100000⟩ p15 p59 c5 (by decide +kernel)
theorem p63 : Derivation 17 inputs ⟨421,8⟩ ⟨1651044797,1000000000⟩ :=
  .step _ _ ⟨9249,5000⟩ ⟨37,20⟩ ⟨3593,37500⟩ ⟨57491,300000⟩ p16 p62 c6 (by decide +kernel)
theorem p64 : Derivation 17 inputs ⟨158,3⟩ ⟨65882103,40000000⟩ :=
  .step _ _ ⟨9249,5000⟩ ⟨37,20⟩ ⟨3593,37500⟩ ⟨57491,300000⟩ p17 p62 c6 (by decide +kernel)
theorem p65 : Derivation 17 inputs ⟨1265,24⟩ ⟨1643060353,1000000000⟩ :=
  .step _ _ ⟨9249,5000⟩ ⟨37,20⟩ ⟨3593,37500⟩ ⟨57491,300000⟩ p18 p62 c6 (by decide +kernel)
theorem p66 : Derivation 17 inputs ⟨211,4⟩ ⟨409771373,250000000⟩ :=
  .step _ _ ⟨4637,2500⟩ ⟨371,200⟩ ⟨28619,300000⟩ ⟨57241,300000⟩ p19 p65 c7 (by decide +kernel)
theorem p67 : Derivation 17 inputs ⟨1267,24⟩ ⟨1635110631,1000000000⟩ :=
  .step _ _ ⟨4637,2500⟩ ⟨371,200⟩ ⟨28619,300000⟩ ⟨57241,300000⟩ p20 p65 c7 (by decide +kernel)
theorem p68 : Derivation 17 inputs ⟨317,6⟩ ⟨163113577,100000000⟩ :=
  .step _ _ ⟨4637,2500⟩ ⟨371,200⟩ ⟨28619,300000⟩ ⟨57241,300000⟩ p21 p65 c7 (by decide +kernel)
theorem p69 : Derivation 17 inputs ⟨423,8⟩ ⟨162717827,100000000⟩ :=
  .step _ _ ⟨9299,5000⟩ ⟨93,50⟩ ⟨4749,50000⟩ ⟨18997,100000⟩ p22 p68 c8 (by decide +kernel)
theorem p70 : Derivation 17 inputs ⟨635,12⟩ ⟨162322077,100000000⟩ :=
  .step _ _ ⟨9299,5000⟩ ⟨93,50⟩ ⟨4749,50000⟩ ⟨18997,100000⟩ p23 p69 c8 (by decide +kernel)
theorem p71 : Derivation 17 inputs ⟨1271,24⟩ ⟨161926327,100000000⟩ :=
  .step _ _ ⟨9299,5000⟩ ⟨93,50⟩ ⟨4749,50000⟩ ⟨18997,100000⟩ p24 p70 c8 (by decide +kernel)
theorem p72 : Derivation 17 inputs ⟨53,1⟩ ⟨403830783,250000000⟩ :=
  .step _ _ ⟨2331,1250⟩ ⟨373,200⟩ ⟨28369,300000⟩ ⟨56741,300000⟩ p25 p71 c9 (by decide +kernel)
theorem p73 : Derivation 17 inputs ⟨1273,24⟩ ⟨1611382993,1000000000⟩ :=
  .step _ _ ⟨2331,1250⟩ ⟨373,200⟩ ⟨28369,300000⟩ ⟨56741,300000⟩ p26 p71 c9 (by decide +kernel)
theorem p74 : Derivation 17 inputs ⟨637,12⟩ ⟨803721427,500000000⟩ :=
  .step _ _ ⟨2331,1250⟩ ⟨373,200⟩ ⟨28369,300000⟩ ⟨56741,300000⟩ p27 p71 c9 (by decide +kernel)
theorem p75 : Derivation 17 inputs ⟨425,8⟩ ⟨1603520077,1000000000⟩ :=
  .step _ _ ⟨9349,5000⟩ ⟨187,100⟩ ⟨7061,75000⟩ ⟨56491,300000⟩ p28 p74 c10 (by decide +kernel)
theorem p76 : Derivation 17 inputs ⟨319,6⟩ ⟨1599597299,1000000000⟩ :=
  .step _ _ ⟨9349,5000⟩ ⟨187,100⟩ ⟨7061,75000⟩ ⟨56491,300000⟩ p29 p74 c10 (by decide +kernel)
theorem p77 : Derivation 17 inputs ⟨1277,24⟩ ⟨1595674521,1000000000⟩ :=
  .step _ _ ⟨9349,5000⟩ ⟨187,100⟩ ⟨7061,75000⟩ ⟨56491,300000⟩ p30 p74 c10 (by decide +kernel)
theorem p78 : Derivation 17 inputs ⟨213,4⟩ ⟨1591751743,1000000000⟩ :=
  .step _ _ ⟨9349,5000⟩ ⟨187,100⟩ ⟨7061,75000⟩ ⟨56491,300000⟩ p31 p74 c10 (by decide +kernel)
theorem p79 : Derivation 17 inputs ⟨1279,24⟩ ⟨1587846327,1000000000⟩ :=
  .step _ _ ⟨4687,2500⟩ ⟨15,8⟩ ⟨9373,100000⟩ ⟨18747,100000⟩ p32 p78 c11 (by decide +kernel)
theorem p80 : Derivation 17 inputs ⟨160,3⟩ ⟨158394091,100000000⟩ :=
  .step _ _ ⟨4687,2500⟩ ⟨15,8⟩ ⟨9373,100000⟩ ⟨18747,100000⟩ p33 p78 c11 (by decide +kernel)
theorem p81 : Derivation 17 inputs ⟨427,8⟩ ⟨1580035493,1000000000⟩ :=
  .step _ _ ⟨4687,2500⟩ ⟨15,8⟩ ⟨9373,100000⟩ ⟨18747,100000⟩ p34 p78 c11 (by decide +kernel)
theorem p82 : Derivation 17 inputs ⟨641,12⟩ ⟨1576130077,1000000000⟩ :=
  .step _ _ ⟨4687,2500⟩ ⟨15,8⟩ ⟨9373,100000⟩ ⟨18747,100000⟩ p35 p81 c11 (by decide +kernel)
theorem p83 : Derivation 17 inputs ⟨1283,24⟩ ⟨78611233,50000000⟩ :=
  .step _ _ ⟨4687,2500⟩ ⟨15,8⟩ ⟨9373,100000⟩ ⟨18747,100000⟩ p36 p78 c11 (by decide +kernel)
theorem p84 : Derivation 17 inputs ⟨107,2⟩ ⟨313667321,200000000⟩ :=
  .step _ _ ⟨9399,5000⟩ ⟨47,25⟩ ⟨13997,150000⟩ ⟨55991,300000⟩ p37 p83 c12 (by decide +kernel)
theorem p85 : Derivation 17 inputs ⟨1285,24⟩ ⟨1564448549,1000000000⟩ :=
  .step _ _ ⟨9399,5000⟩ ⟨47,25⟩ ⟨13997,150000⟩ ⟨55991,300000⟩ p38 p83 c12 (by decide +kernel)
theorem p86 : Derivation 17 inputs ⟨643,12⟩ ⟨780280247,500000000⟩ :=
  .step _ _ ⟨9399,5000⟩ ⟨47,25⟩ ⟨13997,150000⟩ ⟨55991,300000⟩ p39 p83 c12 (by decide +kernel)
theorem p87 : Derivation 17 inputs ⟨429,8⟩ ⟨778336219,500000000⟩ :=
  .step _ _ ⟨9399,5000⟩ ⟨47,25⟩ ⟨13997,150000⟩ ⟨55991,300000⟩ p40 p83 c12 (by decide +kernel)
theorem p88 : Derivation 17 inputs ⟨161,3⟩ ⟨1552784383,1000000000⟩ :=
  .step _ _ ⟨9399,5000⟩ ⟨47,25⟩ ⟨13997,150000⟩ ⟨55991,300000⟩ p41 p83 c12 (by decide +kernel)
theorem p89 : Derivation 17 inputs ⟨1289,24⟩ ⟨1548913689,1000000000⟩ :=
  .step _ _ ⟨1178,625⟩ ⟨377,200⟩ ⟨27869,300000⟩ ⟨55741,300000⟩ p42 p88 c13 (by decide +kernel)
theorem p90 : Derivation 17 inputs ⟨215,4⟩ ⟨309008599,200000000⟩ :=
  .step _ _ ⟨1178,625⟩ ⟨377,200⟩ ⟨27869,300000⟩ ⟨55741,300000⟩ p43 p88 c13 (by decide +kernel)
theorem p91 : Derivation 17 inputs ⟨1291,24⟩ ⟨15411723,10000000⟩ :=
  .step _ _ ⟨1178,625⟩ ⟨377,200⟩ ⟨27869,300000⟩ ⟨55741,300000⟩ p44 p88 c13 (by decide +kernel)
theorem p92 : Derivation 17 inputs ⟨323,6⟩ ⟨768650803,500000000⟩ :=
  .step _ _ ⟨1178,625⟩ ⟨377,200⟩ ⟨27869,300000⟩ ⟨55741,300000⟩ p45 p88 c13 (by decide +kernel)
theorem p93 : Derivation 17 inputs ⟨431,8⟩ ⟨1533430911,1000000000⟩ :=
  .step _ _ ⟨1178,625⟩ ⟨377,200⟩ ⟨27869,300000⟩ ⟨55741,300000⟩ p46 p88 c13 (by decide +kernel)
theorem p94 : Derivation 17 inputs ⟨647,12⟩ ⟨1529560217,1000000000⟩ :=
  .step _ _ ⟨1178,625⟩ ⟨377,200⟩ ⟨27869,300000⟩ ⟨55741,300000⟩ p47 p88 c13 (by decide +kernel)
theorem p95 : Derivation 17 inputs ⟨1295,24⟩ ⟨381426721,250000000⟩ :=
  .step _ _ ⟨9449,5000⟩ ⟨189,100⟩ ⟨289,3125⟩ ⟨18497,100000⟩ p48 p94 c14 (by decide +kernel)
theorem p96 : Derivation 17 inputs ⟨54,1⟩ ⟨1521853551,1000000000⟩ :=
  .step _ _ ⟨9449,5000⟩ ⟨189,100⟩ ⟨289,3125⟩ ⟨18497,100000⟩ p1 p94 c14 (by decide +kernel)
theorem p97 : Derivation 17 inputs ⟨1297,24⟩ ⟨1518000217,1000000000⟩ :=
  .step _ _ ⟨9449,5000⟩ ⟨189,100⟩ ⟨289,3125⟩ ⟨18497,100000⟩ p49 p94 c14 (by decide +kernel)
theorem p98 : Derivation 17 inputs ⟨649,12⟩ ⟨302832849,200000000⟩ :=
  .step _ _ ⟨4737,2500⟩ ⟨379,200⟩ ⟨27619,300000⟩ ⟨55241,300000⟩ p50 p97 c15 (by decide +kernel)
theorem p99 : Derivation 17 inputs ⟨433,8⟩ ⟨1510328273,1000000000⟩ :=
  .step _ _ ⟨4737,2500⟩ ⟨379,200⟩ ⟨27619,300000⟩ ⟨55241,300000⟩ p51 p97 c15 (by decide +kernel)
end WaringSmall.Degree17
