import WaringSmall.Degree14.C00

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace WaringSmall.Degree14
theorem p0 : Derivation 14 inputs ⟨40,1⟩ ⟨16547883,10000000⟩ :=
  .seed _ _ (by decide +kernel)
theorem p1 : Derivation 14 inputs ⟨42,1⟩ ⟨18009,12500⟩ :=
  .seed _ _ (by decide +kernel)
theorem p2 : Derivation 14 inputs ⟨41,1⟩ ⟨30955083,20000000⟩ :=
  .interpolate _ _ p0 p1 (by decide +kernel)
theorem p3 : Derivation 14 inputs ⟨43,1⟩ ⟨336111397,250000000⟩ :=
  .step _ _ ⟨1839,1000⟩ ⟨46,25⟩ ⟨5791,60000⟩ ⟨2897,15000⟩ p2 p1 c0 (by decide +kernel)
theorem p4 : Derivation 14 inputs ⟨44,1⟩ ⟨312398897,250000000⟩ :=
  .step _ _ ⟨1859,1000⟩ ⟨93,50⟩ ⟨1897,20000⟩ ⟨949,5000⟩ p1 p3 c1 (by decide +kernel)
theorem p5 : Derivation 14 inputs ⟨45,1⟩ ⟨1160160511,1000000000⟩ :=
  .step _ _ ⟨1919,1000⟩ ⟨48,25⟩ ⟨1797,20000⟩ ⟨899,5000⟩ p3 p4 c2 (by decide +kernel)
theorem p6 : Derivation 14 inputs ⟨46,1⟩ ⟨1074295179,1000000000⟩ :=
  .step _ _ ⟨491,250⟩ ⟨393,200⟩ ⟨861,10000⟩ ⟨1723,10000⟩ p4 p5 c3 (by decide +kernel)
theorem p7 : Derivation 14 inputs ⟨47,1⟩ ⟨124106099,125000000⟩ :=
  .step _ _ ⟨2019,1000⟩ ⟨101,50⟩ ⟨4891,60000⟩ ⟨2447,15000⟩ p5 p6 c4 (by decide +kernel)
theorem p8 : Derivation 14 inputs ⟨48,1⟩ ⟨915529699,1000000000⟩ :=
  .step _ _ ⟨2069,1000⟩ ⟨207,100⟩ ⟨1547,20000⟩ ⟨387,2500⟩ p6 p7 c5 (by decide +kernel)
theorem p9 : Derivation 14 inputs ⟨49,1⟩ ⟨210643509,250000000⟩ :=
  .step _ _ ⟨2119,1000⟩ ⟨53,25⟩ ⟨4391,60000⟩ ⟨2197,15000⟩ p7 p8 c6 (by decide +kernel)
theorem p10 : Derivation 14 inputs ⟨50,1⟩ ⟨773687991,1000000000⟩ :=
  .step _ _ ⟨2169,1000⟩ ⟨217,100⟩ ⟨4141,60000⟩ ⟨259,1875⟩ p8 p9 c7 (by decide +kernel)
theorem p11 : Derivation 14 inputs ⟨51,1⟩ ⟨177256513,250000000⟩ :=
  .step _ _ ⟨2219,1000⟩ ⟨111,50⟩ ⟨1297,20000⟩ ⟨649,5000⟩ p9 p10 c8 (by decide +kernel)
theorem p12 : Derivation 14 inputs ⟨52,1⟩ ⟨647747481,1000000000⟩ :=
  .step _ _ ⟨2279,1000⟩ ⟨57,25⟩ ⟨8579,140000⟩ ⟨4293,35000⟩ p10 p11 c9 (by decide +kernel)
theorem p13 : Derivation 14 inputs ⟨53,1⟩ ⟨36844039,62500000⟩ :=
  .step _ _ ⟨591,250⟩ ⟨473,200⟩ ⟨4077,70000⟩ ⟨8161,70000⟩ p11 p12 c10 (by decide +kernel)
theorem p14 : Derivation 14 inputs ⟨54,1⟩ ⟨26721897,50000000⟩ :=
  .step _ _ ⟨2449,1000⟩ ⟨49,20⟩ ⟨7729,140000⟩ ⟨967,8750⟩ p12 p13 c11 (by decide +kernel)
theorem p15 : Derivation 14 inputs ⟨55,1⟩ ⟨15443,32000⟩ :=
  .step _ _ ⟨2539,1000⟩ ⟨127,50⟩ ⟨7279,140000⟩ ⟨3643,35000⟩ p13 p14 c12 (by decide +kernel)
theorem p16 : Derivation 14 inputs ⟨56,1⟩ ⟨69439,160000⟩ :=
  .step _ _ ⟨1317,500⟩ ⟨527,200⟩ ⟨243,5000⟩ ⟨973,10000⟩ p14 p15 c13 (by decide +kernel)
theorem p17 : Derivation 14 inputs ⟨57,1⟩ ⟨77738959,200000000⟩ :=
  .step _ _ ⟨681,250⟩ ⟨109,40⟩ ⟨3177,70000⟩ ⟨6361,70000⟩ p15 p16 c14 (by decide +kernel)
theorem p18 : Derivation 14 inputs ⟨58,1⟩ ⟨173350969,500000000⟩ :=
  .step _ _ ⟨2819,1000⟩ ⟨141,50⟩ ⟨5879,140000⟩ ⟨2943,35000⟩ p16 p17 c15 (by decide +kernel)
theorem p19 : Derivation 14 inputs ⟨59,1⟩ ⟨30792957,100000000⟩ :=
  .step _ _ ⟨2909,1000⟩ ⟨291,100⟩ ⟨5429,140000⟩ ⟨1359,17500⟩ p17 p18 c16 (by decide +kernel)
theorem p20 : Derivation 14 inputs ⟨60,1⟩ ⟨27243343,100000000⟩ :=
  .step _ _ ⟨2999,1000⟩ ⟨3,1⟩ ⟨4979,140000⟩ ⟨2493,35000⟩ p18 p19 c17 (by decide +kernel)
theorem p21 : Derivation 14 inputs ⟨61,1⟩ ⟨24008343,100000000⟩ :=
  .step _ _ ⟨3089,1000⟩ ⟨309,100⟩ ⟨647,20000⟩ ⟨81,1250⟩ p19 p20 c18 (by decide +kernel)
theorem p22 : Derivation 14 inputs ⟨62,1⟩ ⟨21023343,100000000⟩ :=
  .step _ _ ⟨3199,1000⟩ ⟨16,5⟩ ⟨597,20000⟩ ⟨299,5000⟩ p20 p21 c19 (by decide +kernel)
theorem p23 : Derivation 14 inputs ⟨63,1⟩ ⟨182800097,1000000000⟩ :=
  .step _ _ ⟨418,125⟩ ⟨669,200⟩ ⟨823,30000⟩ ⟨1649,30000⟩ p21 p22 c20 (by decide +kernel)
theorem p24 : Derivation 14 inputs ⟨64,1⟩ ⟨1233127,7812500⟩ :=
  .step _ _ ⟨3489,1000⟩ ⟨349,100⟩ ⟨1501,60000⟩ ⟨94,1875⟩ p22 p23 c21 (by decide +kernel)
theorem p25 : Derivation 14 inputs ⟨65,1⟩ ⟨13532359,100000000⟩ :=
  .step _ _ ⟨3639,1000⟩ ⟨91,25⟩ ⟨1351,60000⟩ ⟨677,15000⟩ p23 p24 c22 (by decide +kernel)
theorem p26 : Derivation 14 inputs ⟨66,1⟩ ⟨11522359,100000000⟩ :=
  .step _ _ ⟨473,125⟩ ⟨757,200⟩ ⟨201,10000⟩ ⟨403,10000⟩ p24 p25 c23 (by decide +kernel)
theorem p27 : Derivation 14 inputs ⟨67,1⟩ ⟨97442651,1000000000⟩ :=
  .step _ _ ⟨3919,1000⟩ ⟨98,25⟩ ⟨357,20000⟩ ⟨179,5000⟩ p25 p26 c24 (by decide +kernel)
theorem p28 : Derivation 14 inputs ⟨68,1⟩ ⟨81858131,1000000000⟩ :=
  .step _ _ ⟨2027,500⟩ ⟨811,200⟩ ⟨39,2500⟩ ⟨313,10000⟩ p26 p27 c25 (by decide +kernel)
theorem p29 : Derivation 14 inputs ⟨69,1⟩ ⟨16973807,250000000⟩ :=
  .step _ _ ⟨4249,1000⟩ ⟨17,4⟩ ⟨8657,620000⟩ ⟨543,19375⟩ p27 p28 c26 (by decide +kernel)
theorem p30 : Derivation 14 inputs ⟨70,1⟩ ⟨55727847,1000000000⟩ :=
  .step _ _ ⟨4469,1000⟩ ⟨447,100⟩ ⟨7557,620000⟩ ⟨1897,77500⟩ p28 p29 c27 (by decide +kernel)
theorem p31 : Derivation 14 inputs ⟨71,1⟩ ⟨22613961,500000000⟩ :=
  .step _ _ ⟨2337,500⟩ ⟨187,40⟩ ⟨1633,155000⟩ ⟨6563,310000⟩ p29 p30 c28 (by decide +kernel)
theorem p32 : Derivation 14 inputs ⟨72,1⟩ ⟨9081649,250000000⟩ :=
  .step _ _ ⟨2437,500⟩ ⟨39,8⟩ ⟨1383,155000⟩ ⟨5563,310000⟩ p30 p31 c29 (by decide +kernel)
theorem p33 : Derivation 14 inputs ⟨73,1⟩ ⟨7209427,250000000⟩ :=
  .step _ _ ⟨2537,500⟩ ⟨203,40⟩ ⟨337,45000⟩ ⟨1357,90000⟩ p31 p32 c30 (by decide +kernel)
theorem p34 : Derivation 14 inputs ⟨2100,29⟩ ⟨240901157,7250000000⟩ :=
  .interpolate _ _ p32 p33 (by decide +kernel)

theorem outcome : Outcome 14 77 7 92 inputs ⟨9098843,7500000000⟩ :=
  ⟨⟨2100,29⟩, ⟨240901157,7250000000⟩, p34, (by decide +kernel)⟩
end WaringSmall.Degree14
