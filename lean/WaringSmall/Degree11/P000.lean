import WaringSmall.Degree11.C00

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace WaringSmall.Degree11
theorem p0 : Derivation 11 inputs ⟨32,1⟩ ⟨11640483,10000000⟩ :=
  .seed _ _ (by decide +kernel)
theorem p1 : Derivation 11 inputs ⟨34,1⟩ ⟨9674841,10000000⟩ :=
  .seed _ _ (by decide +kernel)
theorem p2 : Derivation 11 inputs ⟨33,1⟩ ⟨5328831,5000000⟩ :=
  .interpolate _ _ p0 p1 (by decide +kernel)
theorem p3 : Derivation 11 inputs ⟨35,1⟩ ⟨219717391,250000000⟩ :=
  .step _ _ ⟨1929,1000⟩ ⟨193,100⟩ ⟨5341,60000⟩ ⟨334,1875⟩ p2 p1 c0 (by decide +kernel)
theorem p4 : Derivation 11 inputs ⟨36,1⟩ ⟨793864681,1000000000⟩ :=
  .step _ _ ⟨987,500⟩ ⟨79,40⟩ ⟨1279,15000⟩ ⟨5119,30000⟩ p1 p3 c1 (by decide +kernel)
theorem p5 : Derivation 11 inputs ⟨37,1⟩ ⟨357580067,500000000⟩ :=
  .step _ _ ⟨2049,1000⟩ ⟨41,20⟩ ⟨4741,60000⟩ ⟨593,3750⟩ p3 p4 c2 (by decide +kernel)
theorem p6 : Derivation 11 inputs ⟨38,1⟩ ⟨320780067,500000000⟩ :=
  .step _ _ ⟨1057,500⟩ ⟨423,200⟩ ⟨46,625⟩ ⟨1473,10000⟩ p4 p5 c3 (by decide +kernel)
theorem p7 : Derivation 11 inputs ⟨39,1⟩ ⟨573493413,1000000000⟩ :=
  .step _ _ ⟨2179,1000⟩ ⟨109,50⟩ ⟨4091,60000⟩ ⟨2047,15000⟩ p5 p6 c4 (by decide +kernel)
theorem p8 : Derivation 11 inputs ⟨40,1⟩ ⟨510726747,1000000000⟩ :=
  .step _ _ ⟨561,250⟩ ⟨449,200⟩ ⟨1883,30000⟩ ⟨3769,30000⟩ p6 p7 c5 (by decide +kernel)
theorem p9 : Derivation 11 inputs ⟨41,1⟩ ⟨451591033,1000000000⟩ :=
  .step _ _ ⟨2339,1000⟩ ⟨117,50⟩ ⟨8279,140000⟩ ⟨4143,35000⟩ p7 p8 c6 (by decide +kernel)
theorem p10 : Derivation 11 inputs ⟨42,1⟩ ⟨396741033,1000000000⟩ :=
  .step _ _ ⟨2459,1000⟩ ⟨123,50⟩ ⟨1097,20000⟩ ⟨549,5000⟩ p8 p9 c7 (by decide +kernel)
theorem p11 : Derivation 11 inputs ⟨43,1⟩ ⟨10812443,31250000⟩ :=
  .step _ _ ⟨1287,500⟩ ⟨103,40⟩ ⟨222,4375⟩ ⟨7111,70000⟩ p9 p10 c8 (by decide +kernel)
theorem p12 : Derivation 11 inputs ⟨44,1⟩ ⟨74893887,250000000⟩ :=
  .step _ _ ⟨1347,500⟩ ⟨539,200⟩ ⟨813,17500⟩ ⟨6511,70000⟩ p10 p11 c9 (by decide +kernel)
theorem p13 : Derivation 11 inputs ⟨45,1⟩ ⟨16092847,62500000⟩ :=
  .step _ _ ⟨1407,500⟩ ⟨563,200⟩ ⟨369,8750⟩ ⟨5911,70000⟩ p11 p12 c10 (by decide +kernel)
theorem p14 : Derivation 11 inputs ⟨46,1⟩ ⟨10983529,50000000⟩ :=
  .step _ _ ⟨1467,500⟩ ⟨587,200⟩ ⟨663,17500⟩ ⟨5311,70000⟩ p12 p13 c11 (by decide +kernel)
theorem p15 : Derivation 11 inputs ⟨47,1⟩ ⟨9303529,50000000⟩ :=
  .step _ _ ⟨1527,500⟩ ⟨611,200⟩ ⟨21,625⟩ ⟨673,10000⟩ p13 p14 c12 (by decide +kernel)
theorem p16 : Derivation 11 inputs ⟨48,1⟩ ⟨78026957,500000000⟩ :=
  .step _ _ ⟨3189,1000⟩ ⟨319,100⟩ ⟨1801,60000⟩ ⟨451,7500⟩ p14 p15 c13 (by decide +kernel)
theorem p17 : Derivation 11 inputs ⟨49,1⟩ ⟨32270559,250000000⟩ :=
  .step _ _ ⟨3369,1000⟩ ⟨337,100⟩ ⟨1621,60000⟩ ⟨203,3750⟩ p15 p16 c14 (by decide +kernel)
theorem p18 : Derivation 11 inputs ⟨50,1⟩ ⟨105421513,1000000000⟩ :=
  .step _ _ ⟨3569,1000⟩ ⟨357,100⟩ ⟨1421,60000⟩ ⟨89,1875⟩ p16 p17 c15 (by decide +kernel)
theorem p19 : Derivation 11 inputs ⟨51,1⟩ ⟨21242829,250000000⟩ :=
  .step _ _ ⟨3759,1000⟩ ⟨94,25⟩ ⟨1231,60000⟩ ⟨617,15000⟩ p17 p18 c16 (by decide +kernel)
theorem p20 : Derivation 11 inputs ⟨52,1⟩ ⟨16905329,250000000⟩ :=
  .step _ _ ⟨3949,1000⟩ ⟨79,20⟩ ⟨347,20000⟩ ⟨87,2500⟩ p18 p19 c17 (by decide +kernel)
theorem p21 : Derivation 11 inputs ⟨53,1⟩ ⟨13223071,250000000⟩ :=
  .step _ _ ⟨2077,500⟩ ⟨831,200⟩ ⟨2283,155000⟩ ⟨9163,310000⟩ p19 p20 c18 (by decide +kernel)
theorem p22 : Derivation 11 inputs ⟨264,5⟩ ⟨69797613,1250000000⟩ :=
  .interpolate _ _ p20 p21 (by decide +kernel)

theorem outcome : Outcome 11 57 7 68 inputs ⟨202387,1320000000⟩ :=
  ⟨⟨264,5⟩, ⟨69797613,1250000000⟩, p22, (by decide +kernel)⟩
end WaringSmall.Degree11
