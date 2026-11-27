import WaringSmall.Degree10.C00

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace WaringSmall.Degree10
theorem p0 : Derivation 10 inputs ⟨28,1⟩ ⟨5713459,5000000⟩ :=
  .seed _ _ (by decide +kernel)
theorem p1 : Derivation 10 inputs ⟨30,1⟩ ⟨9303709,10000000⟩ :=
  .seed _ _ (by decide +kernel)
theorem p2 : Derivation 10 inputs ⟨29,1⟩ ⟨20730627,20000000⟩ :=
  .interpolate _ _ p0 p1 (by decide +kernel)
theorem p3 : Derivation 10 inputs ⟨31,1⟩ ⟨839271,1000000⟩ :=
  .step _ _ ⟨238,125⟩ ⟨381,200⟩ ⟨911,10000⟩ ⟨1823,10000⟩ p2 p1 c0 (by decide +kernel)
theorem p4 : Derivation 10 inputs ⟨32,1⟩ ⟨750671,1000000⟩ :=
  .step _ _ ⟨967,500⟩ ⟨387,200⟩ ⟨443,5000⟩ ⟨1773,10000⟩ p1 p3 c1 (by decide +kernel)
theorem p5 : Derivation 10 inputs ⟨33,1⟩ ⟨669571,1000000⟩ :=
  .step _ _ ⟨253,125⟩ ⟨81,40⟩ ⟨811,10000⟩ ⟨1623,10000⟩ p3 p4 c2 (by decide +kernel)
theorem p6 : Derivation 10 inputs ⟨34,1⟩ ⟨18559,31250⟩ :=
  .step _ _ ⟨2089,1000⟩ ⟨209,100⟩ ⟨4541,60000⟩ ⟨284,1875⟩ p4 p5 c3 (by decide +kernel)
theorem p7 : Derivation 10 inputs ⟨35,1⟩ ⟨131169,250000⟩ :=
  .step _ _ ⟨541,250⟩ ⟨433,200⟩ ⟨2083,30000⟩ ⟨4169,30000⟩ p5 p6 c4 (by decide +kernel)
theorem p8 : Derivation 10 inputs ⟨36,1⟩ ⟨230607,500000⟩ :=
  .step _ _ ⟨1117,500⟩ ⟨447,200⟩ ⟨159,2500⟩ ⟨1273,10000⟩ p6 p7 c5 (by decide +kernel)
theorem p9 : Derivation 10 inputs ⟨37,1⟩ ⟨402079,1000000⟩ :=
  .step _ _ ⟨2339,1000⟩ ⟨117,50⟩ ⟨8279,140000⟩ ⟨4143,35000⟩ p7 p8 c6 (by decide +kernel)
theorem p10 : Derivation 10 inputs ⟨38,1⟩ ⟨347571,1000000⟩ :=
  .step _ _ ⟨308,125⟩ ⟨493,200⟩ ⟨3827,70000⟩ ⟨7661,70000⟩ p8 p9 c7 (by decide +kernel)
theorem p11 : Derivation 10 inputs ⟨39,1⟩ ⟨297721,1000000⟩ :=
  .step _ _ ⟨2599,1000⟩ ⟨13,5⟩ ⟨997,20000⟩ ⟨499,5000⟩ p9 p10 c8 (by decide +kernel)
theorem p12 : Derivation 10 inputs ⟨40,1⟩ ⟨252693,1000000⟩ :=
  .step _ _ ⟨1367,500⟩ ⟨547,200⟩ ⟨197,4375⟩ ⟨6311,70000⟩ p10 p11 c9 (by decide +kernel)
theorem p13 : Derivation 10 inputs ⟨41,1⟩ ⟨106227,500000⟩ :=
  .step _ _ ⟨358,125⟩ ⟨573,200⟩ ⟨2827,70000⟩ ⟨5661,70000⟩ p11 p12 c10 (by decide +kernel)
theorem p14 : Derivation 10 inputs ⟨42,1⟩ ⟨176911,1000000⟩ :=
  .step _ _ ⟨2999,1000⟩ ⟨3,1⟩ ⟨4979,140000⟩ ⟨2493,35000⟩ p12 p13 c11 (by decide +kernel)
theorem p15 : Derivation 10 inputs ⟨43,1⟩ ⟨72989,500000⟩ :=
  .step _ _ ⟨3129,1000⟩ ⟨313,100⟩ ⟨1861,60000⟩ ⟨233,3750⟩ p13 p14 c12 (by decide +kernel)
theorem p16 : Derivation 10 inputs ⟨44,1⟩ ⟨23639,200000⟩ :=
  .step _ _ ⟨3319,1000⟩ ⟨83,25⟩ ⟨557,20000⟩ ⟨279,5000⟩ p14 p15 c13 (by decide +kernel)
theorem p17 : Derivation 10 inputs ⟨45,1⟩ ⟨94179,1000000⟩ :=
  .step _ _ ⟨3549,1000⟩ ⟨71,20⟩ ⟨1441,60000⟩ ⟨361,7500⟩ p15 p16 c14 (by decide +kernel)
theorem p18 : Derivation 10 inputs ⟨46,1⟩ ⟨36873,500000⟩ :=
  .step _ _ ⟨941,250⟩ ⟨753,200⟩ ⟨613,30000⟩ ⟨1229,30000⟩ p16 p17 c15 (by decide +kernel)
theorem p19 : Derivation 10 inputs ⟨47,1⟩ ⟨71,1250⟩ :=
  .step _ _ ⟨3969,1000⟩ ⟨397,100⟩ ⟨1021,60000⟩ ⟨64,1875⟩ p17 p18 c16 (by decide +kernel)
theorem p20 : Derivation 10 inputs ⟨4840,103⟩ ⟨2933673,51500000⟩ :=
  .interpolate _ _ p18 p19 (by decide +kernel)

theorem outcome : Outcome 10 51 7 60 inputs ⟨566327,55000000⟩ :=
  ⟨⟨4840,103⟩, ⟨2933673,51500000⟩, p20, (by decide +kernel)⟩
end WaringSmall.Degree10
