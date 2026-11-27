import Waring.PolicyCompletionEarly9Data
import Waring.PolicyCompletionReplay9
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Waring.Certificate
theorem earlyPolicies9_08_conditions : ∀ i : Fin earlyPolicies9_08.size, PolicyCompletionReplay9.PolicyConditions earlyPolicies9_08[i.val]! := by decide +kernel
theorem earlyRound9_08_checked : checkRound 9 earlyPolicies9_08 earlyCoefficient9.values earlyRound9_07.outputs earlyRound9_08 = true := by decide +kernel
theorem earlyRound9_08_height : RoundHeightAssociation 9 earlyPolicies9_08 earlyCoefficient9.values earlyRound9_08 := by decide +kernel
theorem earlyRound9_08_recurrence : RoundRecurrenceAssociation 9 earlyPolicies9_08 earlyRound9_08 := by decide +kernel
theorem earlyRound9_08_moments : RoundMomentAssociation 9 earlyPolicies9_08 earlyCoefficient9.values earlyRound9_08 := by decide +kernel
theorem earlyRound9_08_sound : RoundEntrySound 9 earlyPolicies9_08 earlyCoefficient9.values earlyRound9_08 :=
  PolicyCompletionReplay9.round_entry_sound _ _ _ earlyPolicies9_08_conditions earlyRound9_08_height earlyRound9_08_recurrence earlyRound9_08_moments
#print axioms earlyPolicies9_08_conditions
#print axioms earlyRound9_08_checked
#print axioms earlyRound9_08_sound
end Waring.Certificate
