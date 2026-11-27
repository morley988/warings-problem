import WaringSmall.Degree13.P000

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace WaringSmall.Degree13
theorem p100 : Derivation 13 inputs ⟨63,1⟩ ⟨68872309,1000000000⟩ :=
  .step _ _ ⟨2087,500⟩ ⟨167,40⟩ ⟨1129,77500⟩ ⟨9063,310000⟩ p92 p99 c91 (by decide +kernel)
theorem p101 : Derivation 13 inputs ⟨253,4⟩ ⟨65342111,1000000000⟩ :=
  .step _ _ ⟨4229,1000⟩ ⟨423,100⟩ ⟨8757,620000⟩ ⟨2197,77500⟩ p93 p100 c92 (by decide +kernel)
theorem p102 : Derivation 13 inputs ⟨127,2⟩ ⟨30966413,500000000⟩ :=
  .step _ _ ⟨4289,1000⟩ ⟨429,100⟩ ⟨8457,620000⟩ ⟨1061,38750⟩ p94 p101 c93 (by decide +kernel)
theorem p103 : Derivation 13 inputs ⟨255,4⟩ ⟨29326897,500000000⟩ :=
  .step _ _ ⟨2177,500⟩ ⟨871,200⟩ ⟨2033,155000⟩ ⟨8163,310000⟩ p95 p102 c94 (by decide +kernel)
theorem p104 : Derivation 13 inputs ⟨64,1⟩ ⟨55505811,1000000000⟩ :=
  .step _ _ ⟨4419,1000⟩ ⟨221,50⟩ ⟨7807,620000⟩ ⟨3919,155000⟩ p96 p103 c95 (by decide +kernel)
theorem p105 : Derivation 13 inputs ⟨257,4⟩ ⟨13122219,250000000⟩ :=
  .step _ _ ⟨1121,250⟩ ⟨897,200⟩ ⟨3741,310000⟩ ⟨7513,310000⟩ p97 p104 c96 (by decide +kernel)
theorem p106 : Derivation 13 inputs ⟨129,2⟩ ⟨12400559,250000000⟩ :=
  .step _ _ ⟨568,125⟩ ⟨909,200⟩ ⟨3591,310000⟩ ⟨7213,310000⟩ p98 p105 c97 (by decide +kernel)
theorem p107 : Derivation 13 inputs ⟨259,4⟩ ⟨23416523,500000000⟩ :=
  .step _ _ ⟨1151,250⟩ ⟨921,200⟩ ⟨111,10000⟩ ⟨223,10000⟩ p99 p106 c98 (by decide +kernel)
theorem p108 : Derivation 13 inputs ⟨65,1⟩ ⟨22089507,500000000⟩ :=
  .step _ _ ⟨583,125⟩ ⟨933,200⟩ ⟨3291,310000⟩ ⟨6613,310000⟩ p100 p107 c99 (by decide +kernel)
theorem p109 : Derivation 13 inputs ⟨261,4⟩ ⟨41635869,1000000000⟩ :=
  .step _ _ ⟨4719,1000⟩ ⟨118,25⟩ ⟨6307,620000⟩ ⟨3169,155000⟩ p101 p108 c100 (by decide +kernel)
theorem p110 : Derivation 13 inputs ⟨131,2⟩ ⟨39203611,1000000000⟩ :=
  .step _ _ ⟨2387,500⟩ ⟨191,40⟩ ⟨377,38750⟩ ⟨6063,310000⟩ p102 p109 c101 (by decide +kernel)
theorem p111 : Derivation 13 inputs ⟨263,4⟩ ⟨36882241,1000000000⟩ :=
  .step _ _ ⟨4829,1000⟩ ⟨483,100⟩ ⟨5757,620000⟩ ⟨1447,77500⟩ p103 p110 c102 (by decide +kernel)
theorem p112 : Derivation 13 inputs ⟨1638,25⟩ ⟨195089507,5000000000⟩ :=
  .interpolate _ _ p110 p111 (by decide +kernel)

theorem outcome : Outcome 13 70 7 84 inputs ⟨4910493,5200000000⟩ :=
  ⟨⟨1638,25⟩, ⟨195089507,5000000000⟩, p112, (by decide +kernel)⟩
end WaringSmall.Degree13
