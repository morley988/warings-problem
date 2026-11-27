import Waring.PolicyCompletionEarly8Data
import Waring.PolicyCompletionReplay8
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Waring.Certificate
theorem earlyRound8_04_checked : checkRound 8 policies8 earlyCoefficient8.values earlyRound8_03.outputs earlyRound8_04 = true := by decide +kernel
theorem earlyRound8_04_height : RoundHeightAssociation 8 policies8 earlyCoefficient8.values earlyRound8_04 := by decide +kernel
theorem earlyRound8_04_recurrence : RoundRecurrenceAssociation 8 policies8 earlyRound8_04 := by decide +kernel
theorem earlyRound8_04_moments : RoundMomentAssociation 8 policies8 earlyCoefficient8.values earlyRound8_04 := by decide +kernel
theorem earlyRound8_04_sound : RoundEntrySound 8 policies8 earlyCoefficient8.values earlyRound8_04 :=
  PolicyCompletionReplay8.round_entry_sound _ _ earlyRound8_04_height earlyRound8_04_recurrence earlyRound8_04_moments
#print axioms earlyRound8_04_checked
#print axioms earlyRound8_04_sound
end Waring.Certificate
