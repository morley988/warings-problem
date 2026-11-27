import Waring.PolicyCompletionEarly9Data
import Waring.PolicyCompletionReplay9
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Waring.Certificate
theorem earlyPolicies9_01_conditions : ∀ i : Fin earlyPolicies9_01.size, PolicyCompletionReplay9.PolicyConditions earlyPolicies9_01[i.val]! := by decide +kernel
theorem earlyRound9_01_checked : checkRound 9 earlyPolicies9_01 earlyCoefficient9.values alternateSource9 earlyRound9_01 = true := by decide +kernel
theorem earlyRound9_01_height : RoundHeightAssociation 9 earlyPolicies9_01 earlyCoefficient9.values earlyRound9_01 := by decide +kernel
theorem earlyRound9_01_recurrence : RoundRecurrenceAssociation 9 earlyPolicies9_01 earlyRound9_01 := by decide +kernel
theorem earlyRound9_01_moments : RoundMomentAssociation 9 earlyPolicies9_01 earlyCoefficient9.values earlyRound9_01 := by decide +kernel
theorem earlyRound9_01_sound : RoundEntrySound 9 earlyPolicies9_01 earlyCoefficient9.values earlyRound9_01 :=
  PolicyCompletionReplay9.round_entry_sound _ _ _ earlyPolicies9_01_conditions earlyRound9_01_height earlyRound9_01_recurrence earlyRound9_01_moments
#print axioms earlyPolicies9_01_conditions
#print axioms earlyRound9_01_checked
#print axioms earlyRound9_01_sound
end Waring.Certificate
