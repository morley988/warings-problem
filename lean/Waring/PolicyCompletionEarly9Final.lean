import Waring.PolicyCompletionEarly9R01

import Waring.PolicyCompletionEarly9R02

import Waring.PolicyCompletionEarly9R03

import Waring.PolicyCompletionEarly9R04

import Waring.PolicyCompletionEarly9R05

import Waring.PolicyCompletionEarly9R06

import Waring.PolicyCompletionEarly9R07

import Waring.PolicyCompletionEarly9R08

import Waring.PolicyCompletionEarly9R09

import Waring.PolicyCompletionEarly9R10

import Waring.PolicyCompletionEarly9R11

import Waring.PolicyCompletionEarly9R12

import Waring.PolicyCompletionEarly9Checks

set_option maxRecDepth 100000

set_option maxHeartbeats 0

noncomputable section

namespace Waring.Certificate

open SmoothMoments

theorem early_final9_admissible
    (hseed : AdmissibleCurve 9 alternateSource9)
    (hcoefficientSeed : AdmissibleCurve 18 earlyCoefficientSource9) :
    AdmissibleCurve 9 earlyFinal9.values := by

  have hc : AdmissibleCurve 18 earlyCoefficient9.values :=
    checkedInterpolation_admissible 18 earlyCoefficientSource9 earlyCoefficient9
      earlyCoefficient9_checked hcoefficientSeed

  have h01 := checkedRound_admissible_of_entries 9 earlyPolicies9_01 earlyCoefficient9.values
    alternateSource9 earlyRound9_01 earlyRound9_01_checked hseed hc earlyRound9_01_sound

  have h02 := checkedRound_admissible_of_entries 9 earlyPolicies9_02 earlyCoefficient9.values
    earlyRound9_01.outputs earlyRound9_02 earlyRound9_02_checked h01 hc earlyRound9_02_sound

  have h03 := checkedRound_admissible_of_entries 9 earlyPolicies9_03 earlyCoefficient9.values
    earlyRound9_02.outputs earlyRound9_03 earlyRound9_03_checked h02 hc earlyRound9_03_sound

  have h04 := checkedRound_admissible_of_entries 9 earlyPolicies9_04 earlyCoefficient9.values
    earlyRound9_03.outputs earlyRound9_04 earlyRound9_04_checked h03 hc earlyRound9_04_sound

  have h05 := checkedRound_admissible_of_entries 9 earlyPolicies9_05 earlyCoefficient9.values
    earlyRound9_04.outputs earlyRound9_05 earlyRound9_05_checked h04 hc earlyRound9_05_sound

  have h06 := checkedRound_admissible_of_entries 9 earlyPolicies9_06 earlyCoefficient9.values
    earlyRound9_05.outputs earlyRound9_06 earlyRound9_06_checked h05 hc earlyRound9_06_sound

  have h07 := checkedRound_admissible_of_entries 9 earlyPolicies9_07 earlyCoefficient9.values
    earlyRound9_06.outputs earlyRound9_07 earlyRound9_07_checked h06 hc earlyRound9_07_sound

  have h08 := checkedRound_admissible_of_entries 9 earlyPolicies9_08 earlyCoefficient9.values
    earlyRound9_07.outputs earlyRound9_08 earlyRound9_08_checked h07 hc earlyRound9_08_sound

  have h09 := checkedRound_admissible_of_entries 9 earlyPolicies9_09 earlyCoefficient9.values
    earlyRound9_08.outputs earlyRound9_09 earlyRound9_09_checked h08 hc earlyRound9_09_sound

  have h10 := checkedRound_admissible_of_entries 9 earlyPolicies9_10 earlyCoefficient9.values
    earlyRound9_09.outputs earlyRound9_10 earlyRound9_10_checked h09 hc earlyRound9_10_sound

  have h11 := checkedRound_admissible_of_entries 9 earlyPolicies9_11 earlyCoefficient9.values
    earlyRound9_10.outputs earlyRound9_11 earlyRound9_11_checked h10 hc earlyRound9_11_sound

  have h12 := checkedRound_admissible_of_entries 9 earlyPolicies9_12 earlyCoefficient9.values
    earlyRound9_11.outputs earlyRound9_12 earlyRound9_12_checked h11 hc earlyRound9_12_sound

  exact checkedInterpolation_admissible 9 earlyRound9_12.outputs earlyFinal9
    earlyFinal9_checked h12

theorem early_final9_excesses
    (hfinal : AdmissibleCurve 9 earlyFinal9.values) :
    AdmissibleExcess 9 38 (earlyDelta9_38 : ℝ) ∧
    AdmissibleExcess 9 40 (earlyDelta9_40 : ℝ) := by
  exact ⟨(delta_admissible_of_eq_some hfinal earlyFinal9_delta38).1,
    (delta_admissible_of_eq_some hfinal earlyFinal9_delta40).1⟩

#print axioms early_final9_admissible

#print axioms early_final9_excesses

end Waring.Certificate
