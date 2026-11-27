import Waring.PolicyCompletionEarly9Data
import Waring.PolicyCompletionReplay9
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Waring.Certificate
theorem earlyPolicies9_10_conditions : ∀ i : Fin earlyPolicies9_10.size, PolicyCompletionReplay9.PolicyConditions earlyPolicies9_10[i.val]! := by decide +kernel
theorem earlyRound9_10_checked : checkRound 9 earlyPolicies9_10 earlyCoefficient9.values earlyRound9_09.outputs earlyRound9_10 = true := by decide +kernel
theorem earlyRound9_10_height : RoundHeightAssociation 9 earlyPolicies9_10 earlyCoefficient9.values earlyRound9_10 := by decide +kernel
theorem earlyRound9_10_recurrence : RoundRecurrenceAssociation 9 earlyPolicies9_10 earlyRound9_10 := by decide +kernel
theorem earlyRound9_10_moments : RoundMomentAssociation 9 earlyPolicies9_10 earlyCoefficient9.values earlyRound9_10 := by decide +kernel
theorem earlyRound9_10_sound : RoundEntrySound 9 earlyPolicies9_10 earlyCoefficient9.values earlyRound9_10 :=
  PolicyCompletionReplay9.round_entry_sound _ _ _ earlyPolicies9_10_conditions earlyRound9_10_height earlyRound9_10_recurrence earlyRound9_10_moments
#print axioms earlyPolicies9_10_conditions
#print axioms earlyRound9_10_checked
#print axioms earlyRound9_10_sound
end Waring.Certificate
