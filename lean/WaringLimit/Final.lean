import WaringLimit.Section00
import WaringLimit.Section01
import WaringLimit.Section02
import WaringLimit.Section03
import WaringLimit.Section04
import WaringLimit.Section05
import WaringLimit.Section06
import WaringLimit.Section07
import WaringLimit.Section08
import WaringLimit.Section09
import WaringLimit.Section10
import WaringLimit.Section11
import WaringLimit.Section12
import WaringLimit.Section13
import WaringLimit.Section14
import WaringLimit.Section15
import WaringLimit.Section16
import WaringLimit.Section17
import WaringLimit.Section18
namespace WaringLimit

theorem finite_menu : Path start ⟨82817374586005068049791141,299919932,27366835951284936⟩ := by
  apply Path.trans Section00.checked
  apply Path.trans Section01.checked
  apply Path.trans Section02.checked
  apply Path.trans Section03.checked
  apply Path.trans Section04.checked
  apply Path.trans Section05.checked
  apply Path.trans Section06.checked
  apply Path.trans Section07.checked
  apply Path.trans Section08.checked
  apply Path.trans Section09.checked
  apply Path.trans Section10.checked
  apply Path.trans Section11.checked
  apply Path.trans Section12.checked
  apply Path.trans Section13.checked
  apply Path.trans Section14.checked
  apply Path.trans Section15.checked
  apply Path.trans Section16.checked
  apply Path.trans Section17.checked
  exact Section18.checked

theorem limiting_certificate : Certified 68720586795654902 := by
  refine ⟨words_checked.2, ⟨82817374586005068049791141,299919932,27366835951284936⟩, finite_menu, 117757111, ?_⟩
  decide +kernel

#print axioms limiting_certificate
end WaringLimit
