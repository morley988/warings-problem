import WaringSharp.Band36Part00
import WaringSharp.Band36Part01
import WaringSharp.Band36Part02
import WaringSharp.Band36Part03
import WaringSharp.Band36Part04
import WaringSharp.Band36Part05
import WaringSharp.Band36Part06
import WaringSharp.Band36Part07
import WaringSharp.Band36Part08
import WaringSharp.Band36Part09
import WaringSharp.Band36Part10
import WaringSharp.Band36Part11
import WaringSharp.Band36Part12
import WaringSharp.Band36Part13

namespace WaringSharp.Band36
open WaringEnvelope WaringDualEnvelope
set_option maxRecDepth 8192
set_option maxHeartbeats 5500000


theorem checked : WaringDualEnvelope.Certified cfg (6873*D/1000-ceilDiv D cfg.first) := by
  constructor
  · decide +kernel
  · refine ⟨⟨4271031346740051771231,203720292,27443170430905⟩, ?_, ?_⟩
    · exact step0 |>.trans step1 |>.trans step2 |>.trans step3 |>.trans step4 |>.trans step5 |>.trans step6 |>.trans step7 |>.trans step8 |>.trans step9 |>.trans step10 |>.trans step11 |>.trans step12 |>.trans step13 |>.trans step14 |>.trans step15 |>.trans step16 |>.trans step17 |>.trans step18 |>.trans step19 |>.trans step20 |>.trans step21 |>.trans step22 |>.trans step23 |>.trans step24 |>.trans step25 |>.trans step26 |>.trans step27 |>.trans step28 |>.trans step29 |>.trans step30 |>.trans step31 |>.trans step32 |>.trans step33 |>.trans step34 |>.trans step35 |>.trans step36 |>.trans step37 |>.trans step38 |>.trans step39 |>.trans step40 |>.trans step41 |>.trans step42 |>.trans step43 |>.trans step44 |>.trans step45 |>.trans step46 |>.trans step47 |>.trans step48 |>.trans step49 |>.trans step50 |>.trans step51 |>.trans step52 |>.trans step53 |>.trans step54 |>.trans step55 |>.trans step56 |>.trans step57 |>.trans step58 |>.trans step59 |>.trans step60 |>.trans step61 |>.trans step62 |>.trans step63 |>.trans step64 |>.trans step65 |>.trans step66 |>.trans step67 |>.trans step68 |>.trans step69 |>.trans step70 |>.trans step71 |>.trans step72 |>.trans step73 |>.trans step74 |>.trans step75 |>.trans step76 |>.trans step77 |>.trans step78 |>.trans step79 |>.trans step80 |>.trans step81 |>.trans step82 |>.trans step83 |>.trans step84 |>.trans step85 |>.trans step86 |>.trans step87 |>.trans step88 |>.trans step89 |>.trans step90 |>.trans step91 |>.trans step92 |>.trans step93 |>.trans step94 |>.trans step95 |>.trans step96 |>.trans step97 |>.trans step98 |>.trans step99 |>.trans step100 |>.trans step101 |>.trans step102 |>.trans step103 |>.trans step104 |>.trans step105 |>.trans step106 |>.trans step107 |>.trans step108 |>.trans step109 |>.trans step110 |>.trans step111 |>.trans step112 |>.trans step113 |>.trans step114 |>.trans step115 |>.trans step116 |>.trans step117 |>.trans step118 |>.trans step119 |>.trans step120 |>.trans step121 |>.trans step122 |>.trans step123 |>.trans step124 |>.trans step125 |>.trans step126 |>.trans step127 |>.trans step128 |>.trans step129 |>.trans step130 |>.trans step131 |>.trans step132 |>.trans step133 |>.trans step134 |>.trans step135 |>.trans step136 |>.trans step137 |>.trans step138 |>.trans step139 |>.trans step140 |>.trans step141 |>.trans step142 |>.trans step143 |>.trans step144 |>.trans step145 |>.trans step146 |>.trans step147 |>.trans step148 |>.trans step149 |>.trans step150 |>.trans step151 |>.trans step152 |>.trans step153 |>.trans step154 |>.trans step155 |>.trans step156 |>.trans step157 |>.trans step158 |>.trans step159 |>.trans step160 |>.trans step161 |>.trans step162 |>.trans step163
    · decide +kernel

#print axioms checked
end WaringSharp.Band36
