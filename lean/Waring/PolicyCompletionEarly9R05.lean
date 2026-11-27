import Waring.PolicyCompletionEarly9Data
import Waring.PolicyCompletionReplay9
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Waring.Certificate
theorem earlyPolicies9_05_conditions : ∀ i : Fin earlyPolicies9_05.size, PolicyCompletionReplay9.PolicyConditions earlyPolicies9_05[i.val]! := by decide +kernel
theorem earlyRound9_05_checked : checkRound 9 earlyPolicies9_05 earlyCoefficient9.values earlyRound9_04.outputs earlyRound9_05 = true := by decide +kernel
theorem earlyRound9_05_height : RoundHeightAssociation 9 earlyPolicies9_05 earlyCoefficient9.values earlyRound9_05 := by decide +kernel
theorem earlyRound9_05_recurrence : RoundRecurrenceAssociation 9 earlyPolicies9_05 earlyRound9_05 := by decide +kernel
theorem earlyRound9_05_moments : RoundMomentAssociation 9 earlyPolicies9_05 earlyCoefficient9.values earlyRound9_05 := by decide +kernel
theorem earlyRound9_05_sound : RoundEntrySound 9 earlyPolicies9_05 earlyCoefficient9.values earlyRound9_05 :=
  PolicyCompletionReplay9.round_entry_sound _ _ _ earlyPolicies9_05_conditions earlyRound9_05_height earlyRound9_05_recurrence earlyRound9_05_moments
#print axioms earlyPolicies9_05_conditions
#print axioms earlyRound9_05_checked
#print axioms earlyRound9_05_sound
end Waring.Certificate
