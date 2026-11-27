import Waring.PolicyCompletionEarly8Data
import Waring.PolicyCompletionReplay8
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Waring.Certificate
theorem earlyRound8_11_checked : checkRound 8 policies8 earlyCoefficient8.values earlyRound8_10.outputs earlyRound8_11 = true := by decide +kernel
theorem earlyRound8_11_height : RoundHeightAssociation 8 policies8 earlyCoefficient8.values earlyRound8_11 := by decide +kernel
theorem earlyRound8_11_recurrence : RoundRecurrenceAssociation 8 policies8 earlyRound8_11 := by decide +kernel
theorem earlyRound8_11_moments : RoundMomentAssociation 8 policies8 earlyCoefficient8.values earlyRound8_11 := by decide +kernel
theorem earlyRound8_11_sound : RoundEntrySound 8 policies8 earlyCoefficient8.values earlyRound8_11 :=
  PolicyCompletionReplay8.round_entry_sound _ _ earlyRound8_11_height earlyRound8_11_recurrence earlyRound8_11_moments
#print axioms earlyRound8_11_checked
#print axioms earlyRound8_11_sound
end Waring.Certificate
