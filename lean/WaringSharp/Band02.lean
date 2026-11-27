import WaringSharp.Band02Part00

namespace WaringSharp.Band02
open WaringEnvelope WaringDualEnvelope
set_option maxRecDepth 8192
set_option maxHeartbeats 5500000


theorem checked : WaringDualEnvelope.Certified cfg (6873*D/1000-ceilDiv D cfg.first) := by
  constructor
  · decide +kernel
  · refine ⟨⟨106114349807118868816282463432,79173,24968455069299⟩, ?_, ?_⟩
    · exact step0
    · decide +kernel

#print axioms checked
end WaringSharp.Band02
