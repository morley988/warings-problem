import Waring.PolicyCompletionEarly9Data
import Waring.PolicyCompletionReplay9
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Waring.Certificate
theorem earlyPolicies9_03_conditions : ∀ i : Fin earlyPolicies9_03.size, PolicyCompletionReplay9.PolicyConditions earlyPolicies9_03[i.val]! := by decide +kernel
theorem earlyRound9_03_checked : checkRound 9 earlyPolicies9_03 earlyCoefficient9.values earlyRound9_02.outputs earlyRound9_03 = true := by decide +kernel
theorem earlyRound9_03_height : RoundHeightAssociation 9 earlyPolicies9_03 earlyCoefficient9.values earlyRound9_03 := by decide +kernel
theorem earlyRound9_03_recurrence : RoundRecurrenceAssociation 9 earlyPolicies9_03 earlyRound9_03 := by decide +kernel
theorem earlyRound9_03_moments : RoundMomentAssociation 9 earlyPolicies9_03 earlyCoefficient9.values earlyRound9_03 := by decide +kernel
theorem earlyRound9_03_sound : RoundEntrySound 9 earlyPolicies9_03 earlyCoefficient9.values earlyRound9_03 :=
  PolicyCompletionReplay9.round_entry_sound _ _ _ earlyPolicies9_03_conditions earlyRound9_03_height earlyRound9_03_recurrence earlyRound9_03_moments
#print axioms earlyPolicies9_03_conditions
#print axioms earlyRound9_03_checked
#print axioms earlyRound9_03_sound
end Waring.Certificate
