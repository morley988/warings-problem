import WaringSmall.Degree8.C00

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace WaringSmall.Degree8
theorem p0 : Derivation 8 inputs ⟨22,1⟩ ⟨8664781,10000000⟩ :=
  .seed _ _ (by decide +kernel)
theorem p1 : Derivation 8 inputs ⟨24,1⟩ ⟨6561197,10000000⟩ :=
  .seed _ _ (by decide +kernel)
theorem p2 : Derivation 8 inputs ⟨26,1⟩ ⟨1225253,2500000⟩ :=
  .seed _ _ (by decide +kernel)
theorem p3 : Derivation 8 inputs ⟨23,1⟩ ⟨7612989,10000000⟩ :=
  .interpolate _ _ p0 p1 (by decide +kernel)
theorem p4 : Derivation 8 inputs ⟨25,1⟩ ⟨286051517,500000000⟩ :=
  .step _ _ ⟨1989,1000⟩ ⟨199,100⟩ ⟨5041,60000⟩ ⟨1261,7500⟩ p3 p1 c0 (by decide +kernel)
theorem p5 : Derivation 8 inputs ⟨27,1⟩ ⟨1047503,2500000⟩ :=
  .step _ _ ⟨268,125⟩ ⟨429,200⟩ ⟨711,10000⟩ ⟨1423,10000⟩ p4 p2 c1 (by decide +kernel)
theorem p6 : Derivation 8 inputs ⟨28,1⟩ ⟨17707969,50000000⟩ :=
  .step _ _ ⟨2219,1000⟩ ⟨111,50⟩ ⟨1297,20000⟩ ⟨649,5000⟩ p2 p5 c2 (by decide +kernel)
theorem p7 : Derivation 8 inputs ⟨29,1⟩ ⟨295710097,1000000000⟩ :=
  .step _ _ ⟨1177,500⟩ ⟨471,200⟩ ⟨293,5000⟩ ⟨1173,10000⟩ p5 p6 c3 (by decide +kernel)
theorem p8 : Derivation 8 inputs ⟨30,1⟩ ⟨48572959,200000000⟩ :=
  .step _ _ ⟨1257,500⟩ ⟨503,200⟩ ⟨1851,35000⟩ ⟨7411,70000⟩ p6 p7 c4 (by decide +kernel)
theorem p9 : Derivation 8 inputs ⟨31,1⟩ ⟨196314541,1000000000⟩ :=
  .step _ _ ⟨2689,1000⟩ ⟨269,100⟩ ⟨6529,140000⟩ ⟨817,8750⟩ p7 p8 c5 (by decide +kernel)
theorem p10 : Derivation 8 inputs ⟨32,1⟩ ⟨155928827,1000000000⟩ :=
  .step _ _ ⟨358,125⟩ ⟨573,200⟩ ⟨2827,70000⟩ ⟨5661,70000⟩ p8 p9 c6 (by decide +kernel)
theorem p11 : Derivation 8 inputs ⟨33,1⟩ ⟨121793113,1000000000⟩ :=
  .step _ _ ⟨3039,1000⟩ ⟨76,25⟩ ⟨4779,140000⟩ ⟨2393,35000⟩ p9 p10 c7 (by decide +kernel)
theorem p12 : Derivation 8 inputs ⟨34,1⟩ ⟨11587461,125000000⟩ :=
  .step _ _ ⟨811,250⟩ ⟨649,200⟩ ⟨291,10000⟩ ⟨583,10000⟩ p10 p11 c8 (by decide +kernel)
theorem p13 : Derivation 8 inputs ⟨35,1⟩ ⟨8527421,125000000⟩ :=
  .step _ _ ⟨3519,1000⟩ ⟨88,25⟩ ⟨1471,60000⟩ ⟨737,15000⟩ p11 p12 c9 (by decide +kernel)
theorem p14 : Derivation 8 inputs ⟨2232,65⟩ ⟨137172817,1625000000⟩ :=
  .interpolate _ _ p12 p13 (by decide +kernel)

theorem outcome : Outcome 8 38 7 42 inputs ⟨12609061,600000000⟩ :=
  ⟨⟨2232,65⟩, ⟨137172817,1625000000⟩, p14, (by decide +kernel)⟩
end WaringSmall.Degree8
