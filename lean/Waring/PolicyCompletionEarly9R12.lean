import Waring.PolicyCompletionEarly9Data
import Waring.PolicyCompletionReplay9
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Waring.Certificate
theorem earlyPolicies9_12_conditions : ∀ i : Fin earlyPolicies9_12.size, PolicyCompletionReplay9.PolicyConditions earlyPolicies9_12[i.val]! := by decide +kernel
theorem earlyRound9_12_checked : checkRound 9 earlyPolicies9_12 earlyCoefficient9.values earlyRound9_11.outputs earlyRound9_12 = true := by decide +kernel
theorem earlyRound9_12_height : RoundHeightAssociation 9 earlyPolicies9_12 earlyCoefficient9.values earlyRound9_12 := by decide +kernel
theorem earlyRound9_12_recurrence : RoundRecurrenceAssociation 9 earlyPolicies9_12 earlyRound9_12 := by decide +kernel
theorem earlyRound9_12_moments : RoundMomentAssociation 9 earlyPolicies9_12 earlyCoefficient9.values earlyRound9_12 := by decide +kernel
theorem earlyRound9_12_sound : RoundEntrySound 9 earlyPolicies9_12 earlyCoefficient9.values earlyRound9_12 :=
  PolicyCompletionReplay9.round_entry_sound _ _ _ earlyPolicies9_12_conditions earlyRound9_12_height earlyRound9_12_recurrence earlyRound9_12_moments
#print axioms earlyPolicies9_12_conditions
#print axioms earlyRound9_12_checked
#print axioms earlyRound9_12_sound
end Waring.Certificate
