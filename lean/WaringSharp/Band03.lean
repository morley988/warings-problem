import WaringSharp.Band03Part00

namespace WaringSharp.Band03
open WaringEnvelope WaringDualEnvelope
set_option maxRecDepth 8192
set_option maxHeartbeats 5500000


theorem checked : WaringDualEnvelope.Certified cfg (6873*D/1000-ceilDiv D cfg.first) := by
  constructor
  · decide +kernel
  · refine ⟨⟨55165329787235699139300171131,88721,25859660098691⟩, ?_, ?_⟩
    · exact step0
    · decide +kernel

#print axioms checked
end WaringSharp.Band03
