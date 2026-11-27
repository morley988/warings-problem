import Waring.PolicyCompletionEarly9Data
import Waring.PolicyCompletionReplay9
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Waring.Certificate
theorem earlyPolicies9_09_conditions : ∀ i : Fin earlyPolicies9_09.size, PolicyCompletionReplay9.PolicyConditions earlyPolicies9_09[i.val]! := by decide +kernel
theorem earlyRound9_09_checked : checkRound 9 earlyPolicies9_09 earlyCoefficient9.values earlyRound9_08.outputs earlyRound9_09 = true := by decide +kernel
theorem earlyRound9_09_height : RoundHeightAssociation 9 earlyPolicies9_09 earlyCoefficient9.values earlyRound9_09 := by decide +kernel
theorem earlyRound9_09_recurrence : RoundRecurrenceAssociation 9 earlyPolicies9_09 earlyRound9_09 := by decide +kernel
theorem earlyRound9_09_moments : RoundMomentAssociation 9 earlyPolicies9_09 earlyCoefficient9.values earlyRound9_09 := by decide +kernel
theorem earlyRound9_09_sound : RoundEntrySound 9 earlyPolicies9_09 earlyCoefficient9.values earlyRound9_09 :=
  PolicyCompletionReplay9.round_entry_sound _ _ _ earlyPolicies9_09_conditions earlyRound9_09_height earlyRound9_09_recurrence earlyRound9_09_moments
#print axioms earlyPolicies9_09_conditions
#print axioms earlyRound9_09_checked
#print axioms earlyRound9_09_sound
end Waring.Certificate
