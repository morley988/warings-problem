import Waring.PolicyCompletionEarly8Data
import Waring.PolicyCompletionReplay8
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Waring.Certificate
theorem earlyRound8_06_checked : checkRound 8 policies8 earlyCoefficient8.values earlyRound8_05.outputs earlyRound8_06 = true := by decide +kernel
theorem earlyRound8_06_height : RoundHeightAssociation 8 policies8 earlyCoefficient8.values earlyRound8_06 := by decide +kernel
theorem earlyRound8_06_recurrence : RoundRecurrenceAssociation 8 policies8 earlyRound8_06 := by decide +kernel
theorem earlyRound8_06_moments : RoundMomentAssociation 8 policies8 earlyCoefficient8.values earlyRound8_06 := by decide +kernel
theorem earlyRound8_06_sound : RoundEntrySound 8 policies8 earlyCoefficient8.values earlyRound8_06 :=
  PolicyCompletionReplay8.round_entry_sound _ _ earlyRound8_06_height earlyRound8_06_recurrence earlyRound8_06_moments
#print axioms earlyRound8_06_checked
#print axioms earlyRound8_06_sound
end Waring.Certificate
