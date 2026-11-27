import Waring.PolicyCompletionEarly9Data
import Waring.PolicyCompletionReplay9
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Waring.Certificate
theorem earlyPolicies9_11_conditions : ∀ i : Fin earlyPolicies9_11.size, PolicyCompletionReplay9.PolicyConditions earlyPolicies9_11[i.val]! := by decide +kernel
theorem earlyRound9_11_checked : checkRound 9 earlyPolicies9_11 earlyCoefficient9.values earlyRound9_10.outputs earlyRound9_11 = true := by decide +kernel
theorem earlyRound9_11_height : RoundHeightAssociation 9 earlyPolicies9_11 earlyCoefficient9.values earlyRound9_11 := by decide +kernel
theorem earlyRound9_11_recurrence : RoundRecurrenceAssociation 9 earlyPolicies9_11 earlyRound9_11 := by decide +kernel
theorem earlyRound9_11_moments : RoundMomentAssociation 9 earlyPolicies9_11 earlyCoefficient9.values earlyRound9_11 := by decide +kernel
theorem earlyRound9_11_sound : RoundEntrySound 9 earlyPolicies9_11 earlyCoefficient9.values earlyRound9_11 :=
  PolicyCompletionReplay9.round_entry_sound _ _ _ earlyPolicies9_11_conditions earlyRound9_11_height earlyRound9_11_recurrence earlyRound9_11_moments
#print axioms earlyPolicies9_11_conditions
#print axioms earlyRound9_11_checked
#print axioms earlyRound9_11_sound
end Waring.Certificate
