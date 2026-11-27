import WaringSharp.Band10Part00
import WaringSharp.Band10Part01

namespace WaringSharp.Band10
open WaringEnvelope WaringDualEnvelope
set_option maxRecDepth 8192
set_option maxHeartbeats 5500000


theorem checked : WaringDualEnvelope.Certified cfg (6873*D/1000-ceilDiv D cfg.first) := by
  constructor
  · decide +kernel
  · refine ⟨⟨1454533786742081064923287986,433236,27242889971336⟩, ?_, ?_⟩
    · exact step0 |>.trans step1 |>.trans step2 |>.trans step3 |>.trans step4 |>.trans step5 |>.trans step6 |>.trans step7 |>.trans step8 |>.trans step9 |>.trans step10 |>.trans step11 |>.trans step12 |>.trans step13 |>.trans step14 |>.trans step15 |>.trans step16
    · decide +kernel

#print axioms checked
end WaringSharp.Band10
