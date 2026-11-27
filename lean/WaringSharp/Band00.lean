import WaringSharp.Band00Part00

namespace WaringSharp.Band00
open WaringEnvelope WaringDualEnvelope
set_option maxRecDepth 8192
set_option maxHeartbeats 5500000


theorem checked : WaringDualEnvelope.Certified cfg (6873*D/1000-ceilDiv D cfg.first) := by
  constructor
  · decide +kernel
  · refine ⟨⟨293901420134085238098549868242,65066,22038265668412⟩, ?_, ?_⟩
    · exact step0
    · decide +kernel

#print axioms checked
end WaringSharp.Band00
