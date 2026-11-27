import Waring.PolicyCompletionEarly8Data
import Waring.PolicyCompletionReplay8
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Waring.Certificate
theorem earlyRound8_07_checked : checkRound 8 policies8 earlyCoefficient8.values earlyRound8_06.outputs earlyRound8_07 = true := by decide +kernel
theorem earlyRound8_07_height : RoundHeightAssociation 8 policies8 earlyCoefficient8.values earlyRound8_07 := by decide +kernel
theorem earlyRound8_07_recurrence : RoundRecurrenceAssociation 8 policies8 earlyRound8_07 := by decide +kernel
theorem earlyRound8_07_moments : RoundMomentAssociation 8 policies8 earlyCoefficient8.values earlyRound8_07 := by decide +kernel
theorem earlyRound8_07_sound : RoundEntrySound 8 policies8 earlyCoefficient8.values earlyRound8_07 :=
  PolicyCompletionReplay8.round_entry_sound _ _ earlyRound8_07_height earlyRound8_07_recurrence earlyRound8_07_moments
#print axioms earlyRound8_07_checked
#print axioms earlyRound8_07_sound
end Waring.Certificate
