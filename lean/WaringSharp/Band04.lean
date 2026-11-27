import WaringSharp.Band04Part00

namespace WaringSharp.Band04
open WaringEnvelope WaringDualEnvelope
set_option maxRecDepth 8192
set_option maxHeartbeats 5500000


theorem checked : WaringDualEnvelope.Certified cfg (6873*D/1000-ceilDiv D cfg.first) := by
  constructor
  · decide +kernel
  · refine ⟨⟨29922150446562364189841776257,97752,26380626118897⟩, ?_, ?_⟩
    · exact step0 |>.trans step1
    · decide +kernel

#print axioms checked
end WaringSharp.Band04
