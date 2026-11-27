import Waring.PolicyCompletionEarly8Data
import Waring.PolicyCompletionReplay8
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Waring.Certificate
theorem earlyRound8_12_checked : checkRound 8 policies8 earlyCoefficient8.values earlyRound8_11.outputs earlyRound8_12 = true := by decide +kernel
theorem earlyRound8_12_height : RoundHeightAssociation 8 policies8 earlyCoefficient8.values earlyRound8_12 := by decide +kernel
theorem earlyRound8_12_recurrence : RoundRecurrenceAssociation 8 policies8 earlyRound8_12 := by decide +kernel
theorem earlyRound8_12_moments : RoundMomentAssociation 8 policies8 earlyCoefficient8.values earlyRound8_12 := by decide +kernel
theorem earlyRound8_12_sound : RoundEntrySound 8 policies8 earlyCoefficient8.values earlyRound8_12 :=
  PolicyCompletionReplay8.round_entry_sound _ _ earlyRound8_12_height earlyRound8_12_recurrence earlyRound8_12_moments
#print axioms earlyRound8_12_checked
#print axioms earlyRound8_12_sound
end Waring.Certificate
