import WaringSharp.Band21Part00
import WaringSharp.Band21Part01
import WaringSharp.Band21Part02
import WaringSharp.Band21Part03
import WaringSharp.Band21Part04

namespace WaringSharp.Band21
open WaringEnvelope WaringDualEnvelope
set_option maxRecDepth 8192
set_option maxHeartbeats 5500000


theorem checked : WaringDualEnvelope.Certified cfg (6873*D/1000-ceilDiv D cfg.first) := by
  constructor
  · decide +kernel
  · refine ⟨⟨6279554375771640971470761,5756996,27443206342591⟩, ?_, ?_⟩
    · exact step0 |>.trans step1 |>.trans step2 |>.trans step3 |>.trans step4 |>.trans step5 |>.trans step6 |>.trans step7 |>.trans step8 |>.trans step9 |>.trans step10 |>.trans step11 |>.trans step12 |>.trans step13 |>.trans step14 |>.trans step15 |>.trans step16 |>.trans step17 |>.trans step18 |>.trans step19 |>.trans step20 |>.trans step21 |>.trans step22 |>.trans step23 |>.trans step24 |>.trans step25 |>.trans step26 |>.trans step27 |>.trans step28 |>.trans step29 |>.trans step30 |>.trans step31 |>.trans step32 |>.trans step33 |>.trans step34 |>.trans step35 |>.trans step36 |>.trans step37 |>.trans step38 |>.trans step39 |>.trans step40 |>.trans step41 |>.trans step42 |>.trans step43 |>.trans step44 |>.trans step45 |>.trans step46 |>.trans step47 |>.trans step48 |>.trans step49 |>.trans step50 |>.trans step51 |>.trans step52 |>.trans step53 |>.trans step54 |>.trans step55
    · decide +kernel

#print axioms checked
end WaringSharp.Band21
