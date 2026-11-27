import WaringSharp.Band07Part00

namespace WaringSharp.Band07
open WaringEnvelope WaringDualEnvelope
set_option maxRecDepth 8192
set_option maxHeartbeats 5500000


theorem checked : WaringDualEnvelope.Certified cfg (6873*D/1000-ceilDiv D cfg.first) := by
  constructor
  · decide +kernel
  · refine ⟨⟨6411055623385666284845922306,208224,26704365366520⟩, ?_, ?_⟩
    · exact step0 |>.trans step1 |>.trans step2 |>.trans step3 |>.trans step4
    · decide +kernel

#print axioms checked
end WaringSharp.Band07
