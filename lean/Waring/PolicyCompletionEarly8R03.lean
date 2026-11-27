import Waring.PolicyCompletionEarly8Data
import Waring.PolicyCompletionReplay8
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Waring.Certificate
theorem earlyRound8_03_checked : checkRound 8 policies8 earlyCoefficient8.values earlyRound8_02.outputs earlyRound8_03 = true := by decide +kernel
theorem earlyRound8_03_height : RoundHeightAssociation 8 policies8 earlyCoefficient8.values earlyRound8_03 := by decide +kernel
theorem earlyRound8_03_recurrence : RoundRecurrenceAssociation 8 policies8 earlyRound8_03 := by decide +kernel
theorem earlyRound8_03_moments : RoundMomentAssociation 8 policies8 earlyCoefficient8.values earlyRound8_03 := by decide +kernel
theorem earlyRound8_03_sound : RoundEntrySound 8 policies8 earlyCoefficient8.values earlyRound8_03 :=
  PolicyCompletionReplay8.round_entry_sound _ _ earlyRound8_03_height earlyRound8_03_recurrence earlyRound8_03_moments
#print axioms earlyRound8_03_checked
#print axioms earlyRound8_03_sound
end Waring.Certificate
