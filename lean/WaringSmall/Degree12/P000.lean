import WaringSmall.Degree12.C00

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace WaringSmall.Degree12
theorem p0 : Derivation 12 inputs ⟨34,1⟩ ⟨14028589,10000000⟩ :=
  .seed _ _ (by decide +kernel)
theorem p1 : Derivation 12 inputs ⟨36,1⟩ ⟨11895563,10000000⟩ :=
  .seed _ _ (by decide +kernel)
theorem p2 : Derivation 12 inputs ⟨35,1⟩ ⟨3240519,2500000⟩ :=
  .interpolate _ _ p0 p1 (by decide +kernel)
theorem p3 : Derivation 12 inputs ⟨37,1⟩ ⟨1095122967,1000000000⟩ :=
  .step _ _ ⟨233,125⟩ ⟨373,200⟩ ⟨2833,30000⟩ ⟨5669,30000⟩ p2 p1 c0 (by decide +kernel)
theorem p4 : Derivation 12 inputs ⟨38,1⟩ ⟨1002772967,1000000000⟩ :=
  .step _ _ ⟨1889,1000⟩ ⟨189,100⟩ ⟨1847,20000⟩ ⟨231,1250⟩ p1 p3 c1 (by decide +kernel)
theorem p5 : Derivation 12 inputs ⟨39,1⟩ ⟨916344143,1000000000⟩ :=
  .step _ _ ⟨1959,1000⟩ ⟨49,25⟩ ⟨5191,60000⟩ ⟨2597,15000⟩ p3 p4 c2 (by decide +kernel)
theorem p6 : Derivation 12 inputs ⟨40,1⟩ ⟨417237119,500000000⟩ :=
  .step _ _ ⟨1007,500⟩ ⟨403,200⟩ ⟨1229,15000⟩ ⟨4919,30000⟩ p4 p5 c3 (by decide +kernel)
theorem p7 : Derivation 12 inputs ⟨41,1⟩ ⟨189489393,250000000⟩ :=
  .step _ _ ⟨2079,1000⟩ ⟨52,25⟩ ⟨4591,60000⟩ ⟨2297,15000⟩ p5 p6 c4 (by decide +kernel)
theorem p8 : Derivation 12 inputs ⟨42,1⟩ ⟨686076903,1000000000⟩ :=
  .step _ _ ⟨1067,500⟩ ⟨427,200⟩ ⟨1079,15000⟩ ⟨4319,30000⟩ p6 p7 c5 (by decide +kernel)
theorem p9 : Derivation 12 inputs ⟨43,1⟩ ⟨619377663,1000000000⟩ :=
  .step _ _ ⟨1097,500⟩ ⟨439,200⟩ ⟨251,3750⟩ ⟨4019,30000⟩ p7 p8 c6 (by decide +kernel)
theorem p10 : Derivation 12 inputs ⟨44,1⟩ ⟨69651099,125000000⟩ :=
  .step _ _ ⟨1127,500⟩ ⟨451,200⟩ ⟨272,4375⟩ ⟨8711,70000⟩ p8 p9 c7 (by decide +kernel)
theorem p11 : Derivation 12 inputs ⟨45,1⟩ ⟨6229907,12500000⟩ :=
  .step _ _ ⟨293,125⟩ ⟨469,200⟩ ⟨4127,70000⟩ ⟨8261,70000⟩ p9 p10 c8 (by decide +kernel)
theorem p12 : Derivation 12 inputs ⟨46,1⟩ ⟨443363989,1000000000⟩ :=
  .step _ _ ⟨1227,500⟩ ⟨491,200⟩ ⟨963,17500⟩ ⟨7711,70000⟩ p10 p11 c9 (by decide +kernel)
theorem p13 : Derivation 12 inputs ⟨47,1⟩ ⟨392110347,1000000000⟩ :=
  .step _ _ ⟨2559,1000⟩ ⟨64,25⟩ ⟨7179,140000⟩ ⟨3593,35000⟩ p11 p12 c10 (by decide +kernel)
theorem p14 : Derivation 12 inputs ⟨48,1⟩ ⟨344760347,1000000000⟩ :=
  .step _ _ ⟨2669,1000⟩ ⟨267,100⟩ ⟨947,20000⟩ ⟨237,2500⟩ p12 p13 c11 (by decide +kernel)
theorem p15 : Derivation 12 inputs ⟨49,1⟩ ⟨301338919,1000000000⟩ :=
  .step _ _ ⟨2779,1000⟩ ⟨139,50⟩ ⟨6079,140000⟩ ⟨3043,35000⟩ p13 p14 c12 (by decide +kernel)
theorem p16 : Derivation 12 inputs ⟨50,1⟩ ⟨130923031,500000000⟩ :=
  .step _ _ ⟨2889,1000⟩ ⟨289,100⟩ ⟨5529,140000⟩ ⟨346,4375⟩ p14 p15 c13 (by decide +kernel)
theorem p17 : Derivation 12 inputs ⟨51,1⟩ ⟨226154859,1000000000⟩ :=
  .step _ _ ⟨1497,500⟩ ⟨599,200⟩ ⟨1251,35000⟩ ⟨5011,70000⟩ p15 p16 c14 (by decide +kernel)
theorem p18 : Derivation 12 inputs ⟨52,1⟩ ⟨194224317,1000000000⟩ :=
  .step _ _ ⟨3099,1000⟩ ⟨31,10⟩ ⟨4479,140000⟩ ⟨2243,35000⟩ p16 p17 c15 (by decide +kernel)
theorem p19 : Derivation 12 inputs ⟨53,1⟩ ⟨82555947,500000000⟩ :=
  .step _ _ ⟨3239,1000⟩ ⟨81,25⟩ ⟨1751,60000⟩ ⟨877,15000⟩ p17 p18 c16 (by decide +kernel)
theorem p20 : Derivation 12 inputs ⟨54,1⟩ ⟨138928561,1000000000⟩ :=
  .step _ _ ⟨3419,1000⟩ ⟨171,50⟩ ⟨1571,60000⟩ ⟨787,15000⟩ p18 p19 c17 (by decide +kernel)
theorem p21 : Derivation 12 inputs ⟨55,1⟩ ⟨23132379,200000000⟩ :=
  .step _ _ ⟨1797,500⟩ ⟨719,200⟩ ⟨349,15000⟩ ⟨1399,30000⟩ p19 p20 c18 (by decide +kernel)
theorem p22 : Derivation 12 inputs ⟨56,1⟩ ⟨19062379,200000000⟩ :=
  .step _ _ ⟨3769,1000⟩ ⟨377,100⟩ ⟨407,20000⟩ ⟨51,1250⟩ p20 p21 c19 (by decide +kernel)
theorem p23 : Derivation 12 inputs ⟨57,1⟩ ⟨77744071,1000000000⟩ :=
  .step _ _ ⟨1967,500⟩ ⟨787,200⟩ ⟨11,625⟩ ⟨353,10000⟩ p21 p22 c20 (by decide +kernel)
theorem p24 : Derivation 12 inputs ⟨58,1⟩ ⟨31337757,500000000⟩ :=
  .step _ _ ⟨4109,1000⟩ ⟨411,100⟩ ⟨9357,620000⟩ ⟨2347,77500⟩ p22 p23 c21 (by decide +kernel)
theorem p25 : Derivation 12 inputs ⟨59,1⟩ ⟨9911877,200000000⟩ :=
  .step _ _ ⟨2177,500⟩ ⟨871,200⟩ ⟨2033,155000⟩ ⟨8163,310000⟩ p23 p24 c22 (by decide +kernel)
theorem p26 : Derivation 12 inputs ⟨60,1⟩ ⟨38576779,1000000000⟩ :=
  .step _ _ ⟨2307,500⟩ ⟨923,200⟩ ⟨427,38750⟩ ⟨6863,310000⟩ p24 p25 c23 (by decide +kernel)
theorem p27 : Derivation 12 inputs ⟨8892,149⟩ ⟨6275105159,149000000000⟩ :=
  .interpolate _ _ p25 p26 (by decide +kernel)

theorem outcome : Outcome 12 64 7 76 inputs ⟨724894841,156000000000⟩ :=
  ⟨⟨8892,149⟩, ⟨6275105159,149000000000⟩, p27, (by decide +kernel)⟩
end WaringSmall.Degree12
