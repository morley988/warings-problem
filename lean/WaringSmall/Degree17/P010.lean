import WaringSmall.Degree17.P009

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace WaringSmall.Degree17
theorem p1000 : Derivation 17 inputs ⟨275,3⟩ ⟨22397881,1000000000⟩ :=
  .step _ _ ⟨3603,625⟩ ⟨1153,200⟩ ⟨30749,6300000⟩ ⟨61561,6300000⟩ p952 p999 c664 (by decide +kernel)
theorem p1001 : Derivation 17 inputs ⟨2201,24⟩ ⟨22196169,1000000000⟩ :=
  .step _ _ ⟨14437,2500⟩ ⟨231,40⟩ ⟨4357,900000⟩ ⟨8723,900000⟩ p953 p1000 c665 (by decide +kernel)
theorem p1002 : Derivation 17 inputs ⟨367,4⟩ ⟨21995997,1000000000⟩ :=
  .step _ _ ⟨28899,5000⟩ ⟨289,50⟩ ⟨15187,3150000⟩ ⟨60811,6300000⟩ p954 p1001 c666 (by decide +kernel)
theorem p1003 : Derivation 17 inputs ⟨2203,24⟩ ⟨4359353,200000000⟩ :=
  .step _ _ ⟨28949,5000⟩ ⟨579,100⟩ ⟨7531,1575000⟩ ⟨60311,6300000⟩ p955 p1002 c667 (by decide +kernel)
theorem p1004 : Derivation 17 inputs ⟨551,6⟩ ⟨10799593,500000000⟩ :=
  .step _ _ ⟨28999,5000⟩ ⟨29,5⟩ ⟨4979,1050000⟩ ⟨19937,2100000⟩ p956 p1003 c668 (by decide +kernel)
theorem p1005 : Derivation 17 inputs ⟨735,8⟩ ⟨21403261,1000000000⟩ :=
  .step _ _ ⟨29049,5000⟩ ⟨581,100⟩ ⟨529,112500⟩ ⟨8473,900000⟩ p957 p1004 c669 (by decide +kernel)
theorem p1006 : Derivation 17 inputs ⟨1103,12⟩ ⟨10604427,500000000⟩ :=
  .step _ _ ⟨14537,2500⟩ ⟨1163,200⟩ ⟨9833,2100000⟩ ⟨19687,2100000⟩ p958 p1005 c670 (by decide +kernel)
theorem p1007 : Derivation 17 inputs ⟨2207,24⟩ ⟨21015409,1000000000⟩ :=
  .step _ _ ⟨7281,1250⟩ ⟨233,40⟩ ⟨29249,6300000⟩ ⟨58561,6300000⟩ p959 p1006 c671 (by decide +kernel)
theorem p1008 : Derivation 17 inputs ⟨92,1⟩ ⟨20823617,1000000000⟩ :=
  .step _ _ ⟨14587,2500⟩ ⟨1167,200⟩ ⟨28999,6300000⟩ ⟨58061,6300000⟩ p960 p1007 c672 (by decide +kernel)
theorem p1009 : Derivation 17 inputs ⟨2209,24⟩ ⟨20633479,1000000000⟩ :=
  .step _ _ ⟨3653,625⟩ ⟨1169,200⟩ ⟨1369,300000⟩ ⟨2741,300000⟩ p961 p1008 c673 (by decide +kernel)
theorem p1010 : Derivation 17 inputs ⟨1105,12⟩ ⟨20444651,1000000000⟩ :=
  .step _ _ ⟨29249,5000⟩ ⟨117,20⟩ ⟨1789,393750⟩ ⟨57311,6300000⟩ p962 p1009 c674 (by decide +kernel)
theorem p1011 : Derivation 17 inputs ⟨737,8⟩ ⟨20256993,1000000000⟩ :=
  .step _ _ ⟨29299,5000⟩ ⟨293,50⟩ ⟨4729,1050000⟩ ⟨18937,2100000⟩ p963 p1010 c675 (by decide +kernel)
theorem p1012 : Derivation 17 inputs ⟨27540,299⟩ ⟨6081048789,299000000000⟩ :=
  .interpolate _ _ p1010 p1011 (by decide +kernel)

theorem outcome : Outcome 17 97 7 118 inputs ⟨918951211,306000000000⟩ :=
  ⟨⟨27540,299⟩, ⟨6081048789,299000000000⟩, p1012, (by decide +kernel)⟩
end WaringSmall.Degree17
