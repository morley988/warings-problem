import Waring.PolicyCompletionEarly8Data
import Waring.PolicyCompletionReplay8
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Waring.Certificate
theorem earlyRound8_01_checked : checkRound 8 policies8 earlyCoefficient8.values alternateSource8 earlyRound8_01 = true := by decide +kernel
theorem earlyRound8_01_height : RoundHeightAssociation 8 policies8 earlyCoefficient8.values earlyRound8_01 := by decide +kernel
theorem earlyRound8_01_recurrence : RoundRecurrenceAssociation 8 policies8 earlyRound8_01 := by decide +kernel
theorem earlyRound8_01_moments : RoundMomentAssociation 8 policies8 earlyCoefficient8.values earlyRound8_01 := by decide +kernel
theorem earlyRound8_01_sound : RoundEntrySound 8 policies8 earlyCoefficient8.values earlyRound8_01 :=
  PolicyCompletionReplay8.round_entry_sound _ _ earlyRound8_01_height earlyRound8_01_recurrence earlyRound8_01_moments
#print axioms earlyRound8_01_checked
#print axioms earlyRound8_01_sound
end Waring.Certificate
