import Waring.PolicyCompletionEarly8Data
import Waring.PolicyCompletionReplay8
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Waring.Certificate
theorem earlyRound8_02_checked : checkRound 8 policies8 earlyCoefficient8.values earlyRound8_01.outputs earlyRound8_02 = true := by decide +kernel
theorem earlyRound8_02_height : RoundHeightAssociation 8 policies8 earlyCoefficient8.values earlyRound8_02 := by decide +kernel
theorem earlyRound8_02_recurrence : RoundRecurrenceAssociation 8 policies8 earlyRound8_02 := by decide +kernel
theorem earlyRound8_02_moments : RoundMomentAssociation 8 policies8 earlyCoefficient8.values earlyRound8_02 := by decide +kernel
theorem earlyRound8_02_sound : RoundEntrySound 8 policies8 earlyCoefficient8.values earlyRound8_02 :=
  PolicyCompletionReplay8.round_entry_sound _ _ earlyRound8_02_height earlyRound8_02_recurrence earlyRound8_02_moments
#print axioms earlyRound8_02_checked
#print axioms earlyRound8_02_sound
end Waring.Certificate
