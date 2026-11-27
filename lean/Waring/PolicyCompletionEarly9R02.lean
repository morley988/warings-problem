import Waring.PolicyCompletionEarly9Data
import Waring.PolicyCompletionReplay9
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Waring.Certificate
theorem earlyPolicies9_02_conditions : ∀ i : Fin earlyPolicies9_02.size, PolicyCompletionReplay9.PolicyConditions earlyPolicies9_02[i.val]! := by decide +kernel
theorem earlyRound9_02_checked : checkRound 9 earlyPolicies9_02 earlyCoefficient9.values earlyRound9_01.outputs earlyRound9_02 = true := by decide +kernel
theorem earlyRound9_02_height : RoundHeightAssociation 9 earlyPolicies9_02 earlyCoefficient9.values earlyRound9_02 := by decide +kernel
theorem earlyRound9_02_recurrence : RoundRecurrenceAssociation 9 earlyPolicies9_02 earlyRound9_02 := by decide +kernel
theorem earlyRound9_02_moments : RoundMomentAssociation 9 earlyPolicies9_02 earlyCoefficient9.values earlyRound9_02 := by decide +kernel
theorem earlyRound9_02_sound : RoundEntrySound 9 earlyPolicies9_02 earlyCoefficient9.values earlyRound9_02 :=
  PolicyCompletionReplay9.round_entry_sound _ _ _ earlyPolicies9_02_conditions earlyRound9_02_height earlyRound9_02_recurrence earlyRound9_02_moments
#print axioms earlyPolicies9_02_conditions
#print axioms earlyRound9_02_checked
#print axioms earlyRound9_02_sound
end Waring.Certificate
