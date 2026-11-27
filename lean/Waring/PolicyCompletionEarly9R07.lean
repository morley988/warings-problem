import Waring.PolicyCompletionEarly9Data
import Waring.PolicyCompletionReplay9
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Waring.Certificate
theorem earlyPolicies9_07_conditions : ∀ i : Fin earlyPolicies9_07.size, PolicyCompletionReplay9.PolicyConditions earlyPolicies9_07[i.val]! := by decide +kernel
theorem earlyRound9_07_checked : checkRound 9 earlyPolicies9_07 earlyCoefficient9.values earlyRound9_06.outputs earlyRound9_07 = true := by decide +kernel
theorem earlyRound9_07_height : RoundHeightAssociation 9 earlyPolicies9_07 earlyCoefficient9.values earlyRound9_07 := by decide +kernel
theorem earlyRound9_07_recurrence : RoundRecurrenceAssociation 9 earlyPolicies9_07 earlyRound9_07 := by decide +kernel
theorem earlyRound9_07_moments : RoundMomentAssociation 9 earlyPolicies9_07 earlyCoefficient9.values earlyRound9_07 := by decide +kernel
theorem earlyRound9_07_sound : RoundEntrySound 9 earlyPolicies9_07 earlyCoefficient9.values earlyRound9_07 :=
  PolicyCompletionReplay9.round_entry_sound _ _ _ earlyPolicies9_07_conditions earlyRound9_07_height earlyRound9_07_recurrence earlyRound9_07_moments
#print axioms earlyPolicies9_07_conditions
#print axioms earlyRound9_07_checked
#print axioms earlyRound9_07_sound
end Waring.Certificate
