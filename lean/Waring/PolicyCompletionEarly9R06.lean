import Waring.PolicyCompletionEarly9Data
import Waring.PolicyCompletionReplay9
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Waring.Certificate
theorem earlyPolicies9_06_conditions : ∀ i : Fin earlyPolicies9_06.size, PolicyCompletionReplay9.PolicyConditions earlyPolicies9_06[i.val]! := by decide +kernel
theorem earlyRound9_06_checked : checkRound 9 earlyPolicies9_06 earlyCoefficient9.values earlyRound9_05.outputs earlyRound9_06 = true := by decide +kernel
theorem earlyRound9_06_height : RoundHeightAssociation 9 earlyPolicies9_06 earlyCoefficient9.values earlyRound9_06 := by decide +kernel
theorem earlyRound9_06_recurrence : RoundRecurrenceAssociation 9 earlyPolicies9_06 earlyRound9_06 := by decide +kernel
theorem earlyRound9_06_moments : RoundMomentAssociation 9 earlyPolicies9_06 earlyCoefficient9.values earlyRound9_06 := by decide +kernel
theorem earlyRound9_06_sound : RoundEntrySound 9 earlyPolicies9_06 earlyCoefficient9.values earlyRound9_06 :=
  PolicyCompletionReplay9.round_entry_sound _ _ _ earlyPolicies9_06_conditions earlyRound9_06_height earlyRound9_06_recurrence earlyRound9_06_moments
#print axioms earlyPolicies9_06_conditions
#print axioms earlyRound9_06_checked
#print axioms earlyRound9_06_sound
end Waring.Certificate
