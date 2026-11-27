import Waring.PolicyCompletionEarly8R01

import Waring.PolicyCompletionEarly8R02

import Waring.PolicyCompletionEarly8R03

import Waring.PolicyCompletionEarly8R04

import Waring.PolicyCompletionEarly8R05

import Waring.PolicyCompletionEarly8R06

import Waring.PolicyCompletionEarly8R07

import Waring.PolicyCompletionEarly8R08

import Waring.PolicyCompletionEarly8R09

import Waring.PolicyCompletionEarly8R10

import Waring.PolicyCompletionEarly8R11

import Waring.PolicyCompletionEarly8R12

import Waring.PolicyCompletionEarly8Checks
import Waring.SeedCompletionAlternate8Seeds
import Waring.SeedCompletionEarly16Curve

set_option maxRecDepth 100000

set_option maxHeartbeats 0

noncomputable section

namespace Waring.Certificate

open SmoothMoments

theorem early_final8_admissible
    (hseed : AdmissibleCurve 8 alternateSource8)
    (hcoefficientSeed : AdmissibleCurve 16 earlyCoefficientSource8) :
    AdmissibleCurve 8 earlyFinal8.values := by

  have hc : AdmissibleCurve 16 earlyCoefficient8.values :=
    checkedInterpolation_admissible 16 earlyCoefficientSource8 earlyCoefficient8
      earlyCoefficient8_checked hcoefficientSeed

  have h01 := checkedRound_admissible_of_entries 8 policies8 earlyCoefficient8.values
    alternateSource8 earlyRound8_01 earlyRound8_01_checked hseed hc earlyRound8_01_sound

  have h02 := checkedRound_admissible_of_entries 8 policies8 earlyCoefficient8.values
    earlyRound8_01.outputs earlyRound8_02 earlyRound8_02_checked h01 hc earlyRound8_02_sound

  have h03 := checkedRound_admissible_of_entries 8 policies8 earlyCoefficient8.values
    earlyRound8_02.outputs earlyRound8_03 earlyRound8_03_checked h02 hc earlyRound8_03_sound

  have h04 := checkedRound_admissible_of_entries 8 policies8 earlyCoefficient8.values
    earlyRound8_03.outputs earlyRound8_04 earlyRound8_04_checked h03 hc earlyRound8_04_sound

  have h05 := checkedRound_admissible_of_entries 8 policies8 earlyCoefficient8.values
    earlyRound8_04.outputs earlyRound8_05 earlyRound8_05_checked h04 hc earlyRound8_05_sound

  have h06 := checkedRound_admissible_of_entries 8 policies8 earlyCoefficient8.values
    earlyRound8_05.outputs earlyRound8_06 earlyRound8_06_checked h05 hc earlyRound8_06_sound

  have h07 := checkedRound_admissible_of_entries 8 policies8 earlyCoefficient8.values
    earlyRound8_06.outputs earlyRound8_07 earlyRound8_07_checked h06 hc earlyRound8_07_sound

  have h08 := checkedRound_admissible_of_entries 8 policies8 earlyCoefficient8.values
    earlyRound8_07.outputs earlyRound8_08 earlyRound8_08_checked h07 hc earlyRound8_08_sound

  have h09 := checkedRound_admissible_of_entries 8 policies8 earlyCoefficient8.values
    earlyRound8_08.outputs earlyRound8_09 earlyRound8_09_checked h08 hc earlyRound8_09_sound

  have h10 := checkedRound_admissible_of_entries 8 policies8 earlyCoefficient8.values
    earlyRound8_09.outputs earlyRound8_10 earlyRound8_10_checked h09 hc earlyRound8_10_sound

  have h11 := checkedRound_admissible_of_entries 8 policies8 earlyCoefficient8.values
    earlyRound8_10.outputs earlyRound8_11 earlyRound8_11_checked h10 hc earlyRound8_11_sound

  have h12 := checkedRound_admissible_of_entries 8 policies8 earlyCoefficient8.values
    earlyRound8_11.outputs earlyRound8_12 earlyRound8_12_checked h11 hc earlyRound8_12_sound

  exact checkedInterpolation_admissible 8 earlyRound8_12.outputs earlyFinal8
    earlyFinal8_checked h12

theorem early_final8_excesses
    (hfinal : AdmissibleCurve 8 earlyFinal8.values) :
    AdmissibleExcess 8 32 (earlyDelta8_32 : ℝ) ∧
    AdmissibleExcess 8 34 (earlyDelta8_34 : ℝ) := by
  exact ⟨(delta_admissible_of_eq_some hfinal earlyFinal8_delta32).1,
    (delta_admissible_of_eq_some hfinal earlyFinal8_delta34).1⟩

theorem early_final8_admissible_actual : AdmissibleCurve 8 earlyFinal8.values :=
  early_final8_admissible
    Waring.SeedCompletionAlternate8Seeds.alternate_source8_admissible
    Waring.SeedCompletionEarly16Curve.early_coefficient8_admissible

theorem early_final8_excesses_actual :
    AdmissibleExcess 8 32 (earlyDelta8_32 : ℝ) ∧
    AdmissibleExcess 8 34 (earlyDelta8_34 : ℝ) :=
  early_final8_excesses early_final8_admissible_actual

#print axioms early_final8_admissible_actual
#print axioms early_final8_excesses_actual
#print axioms early8_strict_criterion

#print axioms early_final8_admissible

#print axioms early_final8_excesses

end Waring.Certificate
