import Waring.PolicyCompletionEarly9Data

import Waring.EndgameCompletionPolicySemanticsLookups

set_option maxRecDepth 100000

set_option maxHeartbeats 0

noncomputable section

namespace Waring.Certificate

open SmoothMoments

theorem earlyCoefficient9_checked : checkInterpolation earlyCoefficientSource9 earlyCoefficient9 = true := by decide +kernel

theorem earlyFinal9_checked : checkInterpolation earlyRound9_12.outputs earlyFinal9 = true := by decide +kernel

theorem earlyFinal9_delta38 : delta 9 earlyFinal9.values 38 = some earlyDelta9_38 := by decide +kernel

theorem earlyFinal9_delta40 : delta 9 earlyFinal9.values 40 = some earlyDelta9_40 := by decide +kernel

theorem early9_strict_criterion : 5 * (earlyDelta9_38 : ℝ) + 74 * (earlyDelta9_40 : ℝ) < 11 := by
  exact_mod_cast (show 5 * earlyDelta9_38 + 74 * earlyDelta9_40 < 11 by decide +kernel)

#print axioms early9_strict_criterion

end Waring.Certificate
