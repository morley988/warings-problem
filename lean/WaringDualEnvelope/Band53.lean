import WaringDualEnvelope.Band53Part00
import WaringDualEnvelope.Band53Part01
import WaringDualEnvelope.Band53Part02
import WaringDualEnvelope.Band53Part03
import WaringDualEnvelope.Band53Part04
import WaringDualEnvelope.Band53Part05
import WaringDualEnvelope.Band53Part06
import WaringDualEnvelope.Band53Part07

namespace WaringDualEnvelope.Band53
open WaringEnvelope WaringDualEnvelope
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000

theorem checked : WaringDualEnvelope.Certified cfg (6874*D/1000) := by
  constructor
  · decide +kernel
  · refine ⟨⟨522256386849865599526649512,1200000,27179424035953⟩, ?_, ?_⟩
    · exact step0 |>.trans step1 |>.trans step2 |>.trans step3 |>.trans step4 |>.trans step5 |>.trans step6 |>.trans step7 |>.trans step8 |>.trans step9 |>.trans step10 |>.trans step11 |>.trans step12 |>.trans step13 |>.trans step14 |>.trans step15 |>.trans step16 |>.trans step17 |>.trans step18 |>.trans step19 |>.trans step20 |>.trans step21 |>.trans step22 |>.trans step23 |>.trans step24 |>.trans step25 |>.trans step26 |>.trans step27 |>.trans step28 |>.trans step29 |>.trans step30 |>.trans step31 |>.trans step32 |>.trans step33 |>.trans step34 |>.trans step35 |>.trans step36 |>.trans step37 |>.trans step38 |>.trans step39 |>.trans step40 |>.trans step41 |>.trans step42 |>.trans step43 |>.trans step44 |>.trans step45 |>.trans step46 |>.trans step47 |>.trans step48 |>.trans step49 |>.trans step50 |>.trans step51 |>.trans step52 |>.trans step53 |>.trans step54 |>.trans step55 |>.trans step56 |>.trans step57 |>.trans step58 |>.trans step59 |>.trans step60 |>.trans step61 |>.trans step62 |>.trans step63 |>.trans step64 |>.trans step65 |>.trans step66 |>.trans step67 |>.trans step68 |>.trans step69 |>.trans step70 |>.trans step71 |>.trans step72 |>.trans step73 |>.trans step74 |>.trans step75
    · decide +kernel

#print axioms checked
end WaringDualEnvelope.Band53
