import Waring.PolicyCompletionEarly8Data
import Waring.PolicyCompletionReplay8
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Waring.Certificate
theorem earlyRound8_10_checked : checkRound 8 policies8 earlyCoefficient8.values earlyRound8_09.outputs earlyRound8_10 = true := by decide +kernel
theorem earlyRound8_10_height : RoundHeightAssociation 8 policies8 earlyCoefficient8.values earlyRound8_10 := by decide +kernel
theorem earlyRound8_10_recurrence : RoundRecurrenceAssociation 8 policies8 earlyRound8_10 := by decide +kernel
theorem earlyRound8_10_moments : RoundMomentAssociation 8 policies8 earlyCoefficient8.values earlyRound8_10 := by decide +kernel
theorem earlyRound8_10_sound : RoundEntrySound 8 policies8 earlyCoefficient8.values earlyRound8_10 :=
  PolicyCompletionReplay8.round_entry_sound _ _ earlyRound8_10_height earlyRound8_10_recurrence earlyRound8_10_moments
#print axioms earlyRound8_10_checked
#print axioms earlyRound8_10_sound
end Waring.Certificate
