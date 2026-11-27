import WaringSharp.Band05Part00

namespace WaringSharp.Band05
open WaringEnvelope WaringDualEnvelope
set_option maxRecDepth 8192
set_option maxHeartbeats 5500000


theorem checked : WaringDualEnvelope.Certified cfg (6873*D/1000-ceilDiv D cfg.first) := by
  constructor
  · decide +kernel
  · refine ⟨⟨16681979371863615865635400294,123606,26647694937256⟩, ?_, ?_⟩
    · exact step0 |>.trans step1
    · decide +kernel

#print axioms checked
end WaringSharp.Band05
