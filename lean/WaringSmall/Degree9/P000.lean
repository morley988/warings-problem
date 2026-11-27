import WaringSmall.Degree9.C00

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace WaringSmall.Degree9
theorem p0 : Derivation 9 inputs ⟨26,1⟩ ⟨4479763,5000000⟩ :=
  .seed _ _ (by decide +kernel)
theorem p1 : Derivation 9 inputs ⟨28,1⟩ ⟨7055987,10000000⟩ :=
  .seed _ _ (by decide +kernel)
theorem p2 : Derivation 9 inputs ⟨27,1⟩ ⟨16015513,20000000⟩ :=
  .interpolate _ _ p0 p1 (by decide +kernel)
theorem p3 : Derivation 9 inputs ⟨29,1⟩ ⟨622833,1000000⟩ :=
  .step _ _ ⟨501,250⟩ ⟨401,200⟩ ⟨2483,30000⟩ ⟨4969,30000⟩ p2 p1 c0 (by decide +kernel)
theorem p4 : Derivation 9 inputs ⟨30,1⟩ ⟨272283,500000⟩ :=
  .step _ _ ⟨1027,500⟩ ⟨411,200⟩ ⟨393,5000⟩ ⟨1573,10000⟩ p1 p3 c1 (by decide +kernel)
theorem p5 : Derivation 9 inputs ⟨31,1⟩ ⟨94823,200000⟩ :=
  .step _ _ ⟨2149,1000⟩ ⟨43,20⟩ ⟨4241,60000⟩ ⟨1061,7500⟩ p3 p4 c2 (by decide +kernel)
theorem p6 : Derivation 9 inputs ⟨32,1⟩ ⟨204999,500000⟩ :=
  .step _ _ ⟨278,125⟩ ⟨89,40⟩ ⟨1933,30000⟩ ⟨3869,30000⟩ p4 p5 c3 (by decide +kernel)
theorem p7 : Derivation 9 inputs ⟨33,1⟩ ⟨175449,500000⟩ :=
  .step _ _ ⟨2339,1000⟩ ⟨117,50⟩ ⟨8279,140000⟩ ⟨4143,35000⟩ p5 p6 c4 (by decide +kernel)
theorem p8 : Derivation 9 inputs ⟨34,1⟩ ⟨296941,1000000⟩ :=
  .step _ _ ⟨621,250⟩ ⟨497,200⟩ ⟨3777,70000⟩ ⟨7561,70000⟩ p6 p7 c5 (by decide +kernel)
theorem p9 : Derivation 9 inputs ⟨35,1⟩ ⟨248341,1000000⟩ :=
  .step _ _ ⟨1317,500⟩ ⟨527,200⟩ ⟨243,5000⟩ ⟨973,10000⟩ p7 p8 c6 (by decide +kernel)
theorem p10 : Derivation 9 inputs ⟨36,1⟩ ⟨205099,1000000⟩ :=
  .step _ _ ⟨348,125⟩ ⟨557,200⟩ ⟨3027,70000⟩ ⟨6061,70000⟩ p8 p9 c7 (by decide +kernel)
theorem p11 : Derivation 9 inputs ⟨37,1⟩ ⟨83691,500000⟩ :=
  .step _ _ ⟨1467,500⟩ ⟨587,200⟩ ⟨663,17500⟩ ⟨5311,70000⟩ p9 p10 c8 (by decide +kernel)
theorem p12 : Derivation 9 inputs ⟨38,1⟩ ⟨67427,500000⟩ :=
  .step _ _ ⟨771,250⟩ ⟨617,200⟩ ⟨2277,70000⟩ ⟨4561,70000⟩ p10 p11 c9 (by decide +kernel)
theorem p13 : Derivation 9 inputs ⟨39,1⟩ ⟨133,1250⟩ :=
  .step _ _ ⟨3279,1000⟩ ⟨82,25⟩ ⟨1711,60000⟩ ⟨857,15000⟩ p11 p12 c10 (by decide +kernel)
theorem p14 : Derivation 9 inputs ⟨40,1⟩ ⟨1641,20000⟩ :=
  .step _ _ ⟨3529,1000⟩ ⟨353,100⟩ ⟨487,20000⟩ ⟨61,1250⟩ p12 p13 c11 (by decide +kernel)
theorem p15 : Derivation 9 inputs ⟨41,1⟩ ⟨7723,125000⟩ :=
  .step _ _ ⟨1887,500⟩ ⟨151,40⟩ ⟨38,1875⟩ ⟨1219,30000⟩ p13 p14 c12 (by decide +kernel)
theorem p16 : Derivation 9 inputs ⟨3330,83⟩ ⟨660749,8300000⟩ :=
  .interpolate _ _ p14 p15 (by decide +kernel)

theorem outcome : Outcome 9 44 7 50 inputs ⟨39251,9000000⟩ :=
  ⟨⟨3330,83⟩, ⟨660749,8300000⟩, p16, (by decide +kernel)⟩
end WaringSmall.Degree9
