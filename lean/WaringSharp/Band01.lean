import WaringSharp.Band01Part00

namespace WaringSharp.Band01
open WaringEnvelope WaringDualEnvelope
set_option maxRecDepth 8192
set_option maxHeartbeats 5500000


theorem checked : WaringDualEnvelope.Certified cfg (6873*D/1000-ceilDiv D cfg.first) := by
  constructor
  · decide +kernel
  · refine ⟨⟨187505085873093028306721636992,70871,23448319965030⟩, ?_, ?_⟩
    · exact step0
    · decide +kernel

#print axioms checked
end WaringSharp.Band01
