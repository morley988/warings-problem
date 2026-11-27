import Waring.PolicyCompletionEarly8Data

import Waring.EndgameCompletionPolicySemanticsLookups

set_option maxRecDepth 100000

set_option maxHeartbeats 0

noncomputable section

namespace Waring.Certificate

open SmoothMoments

theorem earlyCoefficient8_checked : checkInterpolation earlyCoefficientSource8 earlyCoefficient8 = true := by decide +kernel

theorem earlyFinal8_checked : checkInterpolation earlyRound8_12.outputs earlyFinal8 = true := by decide +kernel

theorem earlyFinal8_delta32 : delta 8 earlyFinal8.values 32 = some earlyDelta8_32 := by decide +kernel

theorem earlyFinal8_delta34 : delta 8 earlyFinal8.values 34 = some earlyDelta8_34 := by decide +kernel

theorem early8_strict_criterion : (earlyDelta8_32 : ℝ) + 7 * (earlyDelta8_34 : ℝ) < 1 := by
  exact_mod_cast (show earlyDelta8_32 + 7 * earlyDelta8_34 < 1 by decide +kernel)

#print axioms early8_strict_criterion

end Waring.Certificate
