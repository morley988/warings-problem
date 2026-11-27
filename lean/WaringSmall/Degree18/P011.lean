import WaringSmall.Degree18.P010

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace WaringSmall.Degree18
theorem p1100 : Derivation 18 inputs ⟨587,6⟩ ⟨86017,3906250⟩ :=
  .step _ _ ⟨14637,2500⟩ ⟨1171,200⟩ ⟨28499,6300000⟩ ⟨57061,6300000⟩ p1052 p1099 c695 (by decide +kernel)
theorem p1101 : Derivation 18 inputs ⟨783,8⟩ ⟨21832731,1000000000⟩ :=
  .step _ _ ⟨29299,5000⟩ ⟨293,50⟩ ⟨4729,1050000⟩ ⟨18937,2100000⟩ p1053 p1100 c696 (by decide +kernel)
theorem p1102 : Derivation 18 inputs ⟨1175,12⟩ ⟨10823363,500000000⟩ :=
  .step _ _ ⟨29349,5000⟩ ⟨587,100⟩ ⟨7031,1575000⟩ ⟨56311,6300000⟩ p1054 p1101 c697 (by decide +kernel)
theorem p1103 : Derivation 18 inputs ⟨2351,24⟩ ⟨171699,8000000⟩ :=
  .step _ _ ⟨29399,5000⟩ ⟨147,25⟩ ⟨1991,450000⟩ ⟨7973,900000⟩ p1055 p1102 c698 (by decide +kernel)
theorem p1104 : Derivation 18 inputs ⟨98,1⟩ ⟨21279677,1000000000⟩ :=
  .step _ _ ⟨29449,5000⟩ ⟨589,100⟩ ⟨1151,262500⟩ ⟨18437,2100000⟩ p1056 p1103 c699 (by decide +kernel)
theorem p1105 : Derivation 18 inputs ⟨2353,24⟩ ⟨10548903,500000000⟩ :=
  .step _ _ ⟨14737,2500⟩ ⟨1179,200⟩ ⟨27499,6300000⟩ ⟨55061,6300000⟩ p1057 p1104 c700 (by decide +kernel)
theorem p1106 : Derivation 18 inputs ⟨1177,12⟩ ⟨5229397,250000000⟩ :=
  .step _ _ ⟨7381,1250⟩ ⟨1181,200⟩ ⟨9083,2100000⟩ ⟨18187,2100000⟩ p1058 p1105 c701 (by decide +kernel)
theorem p1107 : Derivation 18 inputs ⟨785,8⟩ ⟨20738197,1000000000⟩ :=
  .step _ _ ⟨29549,5000⟩ ⟨591,100⟩ ⟨6781,1575000⟩ ⟨54311,6300000⟩ p1059 p1106 c702 (by decide +kernel)
theorem p1108 : Derivation 18 inputs ⟨589,6⟩ ⟨20560459,1000000000⟩ :=
  .step _ _ ⟨29599,5000⟩ ⟨148,25⟩ ⟨1493,350000⟩ ⟨5979,700000⟩ p1060 p1107 c703 (by decide +kernel)
theorem p1109 : Derivation 18 inputs ⟨2357,24⟩ ⟨6523,320000⟩ :=
  .step _ _ ⟨29649,5000⟩ ⟨593,100⟩ ⟨832,196875⟩ ⟨53311,6300000⟩ p1061 p1108 c704 (by decide +kernel)
theorem p1110 : Derivation 18 inputs ⟨393,4⟩ ⟨10104559,500000000⟩ :=
  .step _ _ ⟨14837,2500⟩ ⟨1187,200⟩ ⟨8833,2100000⟩ ⟨17687,2100000⟩ p1062 p1109 c705 (by decide +kernel)
theorem p1111 : Derivation 18 inputs ⟨2359,24⟩ ⟨10017757,500000000⟩ :=
  .step _ _ ⟨7431,1250⟩ ⟨1189,200⟩ ⟨26249,6300000⟩ ⟨52561,6300000⟩ p1063 p1110 c706 (by decide +kernel)
theorem p1112 : Derivation 18 inputs ⟨295,3⟩ ⟨9931471,500000000⟩ :=
  .step _ _ ⟨29749,5000⟩ ⟨119,20⟩ ⟨311,75000⟩ ⟨2491,300000⟩ p1064 p1111 c707 (by decide +kernel)
theorem p1113 : Derivation 18 inputs ⟨16416,167⟩ ⟨1670290553,83500000000⟩ :=
  .interpolate _ _ p1111 p1112 (by decide +kernel)

theorem outcome : Outcome 18 104 8 128 inputs ⟨36634383,9500000000⟩ :=
  ⟨⟨16416,167⟩, ⟨1670290553,83500000000⟩, p1113, (by decide +kernel)⟩
end WaringSmall.Degree18
