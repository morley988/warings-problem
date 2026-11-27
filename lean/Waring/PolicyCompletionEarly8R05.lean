import Waring.PolicyCompletionEarly8Data
import Waring.PolicyCompletionReplay8
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Waring.Certificate
theorem earlyRound8_05_checked : checkRound 8 policies8 earlyCoefficient8.values earlyRound8_04.outputs earlyRound8_05 = true := by decide +kernel
theorem earlyRound8_05_height : RoundHeightAssociation 8 policies8 earlyCoefficient8.values earlyRound8_05 := by decide +kernel
theorem earlyRound8_05_recurrence : RoundRecurrenceAssociation 8 policies8 earlyRound8_05 := by decide +kernel
theorem earlyRound8_05_moments : RoundMomentAssociation 8 policies8 earlyCoefficient8.values earlyRound8_05 := by decide +kernel
theorem earlyRound8_05_sound : RoundEntrySound 8 policies8 earlyCoefficient8.values earlyRound8_05 :=
  PolicyCompletionReplay8.round_entry_sound _ _ earlyRound8_05_height earlyRound8_05_recurrence earlyRound8_05_moments
#print axioms earlyRound8_05_checked
#print axioms earlyRound8_05_sound
end Waring.Certificate
