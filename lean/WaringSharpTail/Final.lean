import WaringSharpTail.Section00
import WaringSharpTail.Section01
import WaringSharpTail.Section02
import WaringSharpTail.Section03
import WaringSharpTail.Section04
import WaringSharpTail.Section05
import WaringSharpTail.Section06
import WaringSharpTail.Section07
import WaringSharpTail.Section08
import WaringSharpTail.Section09
import WaringSharpTail.Section10
import WaringSharpTail.Section11
import WaringSharpTail.Section12
import WaringSharpTail.Section13
import WaringSharpTail.Section14
import WaringSharpTail.Section15
import WaringSharpTail.Section16
import WaringSharpTail.Section17
import WaringSharpTail.Section18
namespace WaringSharpTail

theorem finite_menu : Path start ⟨82817374586005068049791141,299919620,27367186488109433⟩ := by
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

theorem limiting_certificate : Certified 68720937332479399 := by
  refine ⟨WaringLimit.words_checked.2, ⟨82817374586005068049791141,299919620,27367186488109433⟩, finite_menu, 117756855, ?_⟩
  decide +kernel

#print axioms limiting_certificate
end WaringSharpTail
