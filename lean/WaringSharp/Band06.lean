import WaringSharp.Band06Part00

namespace WaringSharp.Band06
open WaringEnvelope WaringDualEnvelope
set_option maxRecDepth 8192
set_option maxHeartbeats 5500000


theorem checked : WaringDualEnvelope.Certified cfg (6873*D/1000-ceilDiv D cfg.first) := by
  constructor
  · decide +kernel
  · refine ⟨⟨10406376047032610828686764985,161866,26676764562199⟩, ?_, ?_⟩
    · exact step0 |>.trans step1 |>.trans step2
    · decide +kernel

#print axioms checked
end WaringSharp.Band06
