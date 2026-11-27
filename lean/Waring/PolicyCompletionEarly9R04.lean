import Waring.PolicyCompletionEarly9Data
import Waring.PolicyCompletionReplay9
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Waring.Certificate
theorem earlyPolicies9_04_conditions : ∀ i : Fin earlyPolicies9_04.size, PolicyCompletionReplay9.PolicyConditions earlyPolicies9_04[i.val]! := by decide +kernel
theorem earlyRound9_04_checked : checkRound 9 earlyPolicies9_04 earlyCoefficient9.values earlyRound9_03.outputs earlyRound9_04 = true := by decide +kernel
theorem earlyRound9_04_height : RoundHeightAssociation 9 earlyPolicies9_04 earlyCoefficient9.values earlyRound9_04 := by decide +kernel
theorem earlyRound9_04_recurrence : RoundRecurrenceAssociation 9 earlyPolicies9_04 earlyRound9_04 := by decide +kernel
theorem earlyRound9_04_moments : RoundMomentAssociation 9 earlyPolicies9_04 earlyCoefficient9.values earlyRound9_04 := by decide +kernel
theorem earlyRound9_04_sound : RoundEntrySound 9 earlyPolicies9_04 earlyCoefficient9.values earlyRound9_04 :=
  PolicyCompletionReplay9.round_entry_sound _ _ _ earlyPolicies9_04_conditions earlyRound9_04_height earlyRound9_04_recurrence earlyRound9_04_moments
#print axioms earlyPolicies9_04_conditions
#print axioms earlyRound9_04_checked
#print axioms earlyRound9_04_sound
end Waring.Certificate
