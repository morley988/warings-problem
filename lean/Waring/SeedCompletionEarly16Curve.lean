import Waring.SeedCompletionAlternate16Steps03
import Waring.SeedCompletionEarly16Data
import Waring.CertificateInterpolation

/-! The actual admissibility of the complete first coefficient sweep. -/
noncomputable section
namespace Waring.SeedCompletionEarly16Curve
open SmoothMoments SeedCompletionAlternate16Seeds

theorem early_coefficient8_admissible :
    Certificate.AdmissibleCurve 16 Certificate.earlyCoefficientSource8 := by
  intro i hi
  have hib : i≤30 := by norm_num [Certificate.earlyCoefficientSource8] at hi; omega
  interval_cases i
  · apply admissibleExponent_mono (admissibleExponent_zero 16)
    norm_num [Certificate.earlyCoefficientSource8,Certificate.Q]
  · apply admissibleExponent_mono (admissibleExponent_two (k := 16) (by norm_num))
    norm_num [Certificate.earlyCoefficientSource8,Certificate.Q]
  · apply admissibleExponent_mono (FourthMomentSeed.admissibleExponent_four (k := 16) (by norm_num))
    norm_num [Certificate.earlyCoefficientSource8,Certificate.Q]
  · apply admissibleExponent_mono (SeedCompletionEven16SecondSeeds.degree16_half_3)
    norm_num [Certificate.earlyCoefficientSource8,Certificate.Q]
  · apply admissibleExponent_mono (SeedCompletionEven16SecondSeeds.degree16_half_4)
    norm_num [Certificate.earlyCoefficientSource8,Certificate.Q]
  · apply admissibleExponent_mono (SeedCompletionEven16SecondSeeds.degree16_half_5)
    norm_num [Certificate.earlyCoefficientSource8,Certificate.Q]
  · apply admissibleExponent_mono (SeedCompletionEven16SecondSeeds.degree16_half_6)
    norm_num [Certificate.earlyCoefficientSource8,Certificate.Q]
  · apply admissibleExponent_mono (SeedCompletionEven16SecondSeeds.degree16_half_7)
    norm_num [Certificate.earlyCoefficientSource8,Certificate.Q]
  · apply admissibleExponent_mono (SeedCompletionEven16SecondSeeds.degree16_half_8)
    norm_num [Certificate.earlyCoefficientSource8,Certificate.Q]
  · apply admissibleExponent_mono (SeedCompletionHigher16SimpleSeeds.degree16_half_9)
    norm_num [Certificate.earlyCoefficientSource8,Certificate.Q]
  · apply admissibleExponent_mono (SeedCompletionHigher16SimpleSeeds.degree16_half_10)
    norm_num [Certificate.earlyCoefficientSource8,Certificate.Q]
  · apply admissibleExponent_mono (SeedCompletionHigher16SimpleSeeds.degree16_half_11)
    norm_num [Certificate.earlyCoefficientSource8,Certificate.Q]
  · apply admissibleExponent_mono (SeedCompletionHigher16SimpleSeeds.degree16_half_12)
    norm_num [Certificate.earlyCoefficientSource8,Certificate.Q]
  · apply admissibleExponent_mono (SeedCompletionHigher16SimpleSeeds.degree16_half_13)
    norm_num [Certificate.earlyCoefficientSource8,Certificate.Q]
  · apply admissibleExponent_mono (SeedCompletionHigher16SimpleSeeds.degree16_half_14)
    norm_num [Certificate.earlyCoefficientSource8,Certificate.Q]
  · apply admissibleExponent_mono (half_15_01)
    norm_num [Certificate.earlyCoefficientSource8,Certificate.Q]
  · apply admissibleExponent_mono (half_16_01)
    norm_num [Certificate.earlyCoefficientSource8,Certificate.Q]
  · apply admissibleExponent_mono (half_17_01)
    norm_num [Certificate.earlyCoefficientSource8,Certificate.Q]
  · apply admissibleExponent_mono (half_18_01)
    norm_num [Certificate.earlyCoefficientSource8,Certificate.Q]
  · apply admissibleExponent_mono (half_19_01)
    norm_num [Certificate.earlyCoefficientSource8,Certificate.Q]
  · apply admissibleExponent_mono (half_20_01)
    norm_num [Certificate.earlyCoefficientSource8,Certificate.Q]
  · apply admissibleExponent_mono (half_21_01)
    norm_num [Certificate.earlyCoefficientSource8,Certificate.Q]
  · apply admissibleExponent_mono (half_22_01)
    norm_num [Certificate.earlyCoefficientSource8,Certificate.Q]
  · apply admissibleExponent_mono (half_23_01)
    norm_num [Certificate.earlyCoefficientSource8,Certificate.Q]
  · apply admissibleExponent_mono (half_24_01)
    norm_num [Certificate.earlyCoefficientSource8,Certificate.Q]
  · apply admissibleExponent_mono (half_25_01)
    norm_num [Certificate.earlyCoefficientSource8,Certificate.Q]
  · apply admissibleExponent_mono (half_26_01)
    norm_num [Certificate.earlyCoefficientSource8,Certificate.Q]
  · apply admissibleExponent_mono (half_27_01)
    norm_num [Certificate.earlyCoefficientSource8,Certificate.Q]
  · apply admissibleExponent_mono (half_28_01)
    norm_num [Certificate.earlyCoefficientSource8,Certificate.Q]
  · apply admissibleExponent_mono (half_29_01)
    norm_num [Certificate.earlyCoefficientSource8,Certificate.Q]
  · apply admissibleExponent_mono (half_30_01)
    norm_num [Certificate.earlyCoefficientSource8,Certificate.Q]

#print axioms early_coefficient8_admissible
end Waring.SeedCompletionEarly16Curve
