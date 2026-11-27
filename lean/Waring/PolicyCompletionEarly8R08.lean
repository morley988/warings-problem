import Waring.PolicyCompletionEarly8Data
import Waring.PolicyCompletionReplay8
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Waring.Certificate
theorem earlyRound8_08_checked : checkRound 8 policies8 earlyCoefficient8.values earlyRound8_07.outputs earlyRound8_08 = true := by decide +kernel
theorem earlyRound8_08_height : RoundHeightAssociation 8 policies8 earlyCoefficient8.values earlyRound8_08 := by decide +kernel
theorem earlyRound8_08_recurrence : RoundRecurrenceAssociation 8 policies8 earlyRound8_08 := by decide +kernel
theorem earlyRound8_08_moments : RoundMomentAssociation 8 policies8 earlyCoefficient8.values earlyRound8_08 := by decide +kernel
theorem earlyRound8_08_sound : RoundEntrySound 8 policies8 earlyCoefficient8.values earlyRound8_08 :=
  PolicyCompletionReplay8.round_entry_sound _ _ earlyRound8_08_height earlyRound8_08_recurrence earlyRound8_08_moments
#print axioms earlyRound8_08_checked
#print axioms earlyRound8_08_sound
end Waring.Certificate
