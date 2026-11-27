import Waring.SeedCompletionAlternate18Steps02
import Waring.SeedCompletionEarly18Data

/-! Actual admissibility of the exact first-sweep coefficient curve.
Every entry refers to an already proved admissible exponent. -/
noncomputable section
set_option maxHeartbeats 2000000
namespace Waring.SeedCompletionEarly18Seeds
open SmoothMoments

theorem early18_half_0 : AdmissibleExponent 18 0 (0/1 : ℝ) := by
  simpa only [div_one] using admissibleExponent_zero 18

theorem early18_half_1 : AdmissibleExponent 18 2 (1/1 : ℝ) := by
  simpa only [div_one] using (admissibleExponent_two (k := 18) (by norm_num))

theorem early18_half_2 : AdmissibleExponent 18 4 (2/1 : ℝ) := by
  simpa only [div_one] using (FourthMomentSeed.admissibleExponent_four (k := 18) (by norm_num))

theorem early18_half_3 : AdmissibleExponent 18 6 (3756358640053/1250000000000 : ℝ) := SeedCompletionEven18SecondSeeds.degree18_half_3

theorem early18_half_4 : AdmissibleExponent 18 8 (10121122230059/2500000000000 : ℝ) := SeedCompletionEven18SecondSeeds.degree18_half_4

theorem early18_half_5 : AdmissibleExponent 18 10 (51469670939311/10000000000000 : ℝ) := SeedCompletionEven18SecondSeeds.degree18_half_5

theorem early18_half_6 : AdmissibleExponent 18 12 (62893076047531/10000000000000 : ℝ) := SeedCompletionEven18SecondSeeds.degree18_half_6

theorem early18_half_7 : AdmissibleExponent 18 14 (14935325336369/2000000000000 : ℝ) := SeedCompletionEven18SecondSeeds.degree18_half_7

theorem early18_half_8 : AdmissibleExponent 18 16 (43408015744041/5000000000000 : ℝ) := SeedCompletionEven18SecondSeeds.degree18_half_8

theorem early18_half_9 : AdmissibleExponent 18 18 (49666190250643/5000000000000 : ℝ) := SeedCompletionHigher18SimpleSeeds.degree18_half_9

theorem early18_half_10 : AdmissibleExponent 18 20 (4487439529203/400000000000 : ℝ) := SeedCompletionHigher18SimpleSeeds.degree18_half_10

theorem early18_half_11 : AdmissibleExponent 18 22 (125388987919393/10000000000000 : ℝ) := SeedCompletionHigher18SimpleSeeds.degree18_half_11

theorem early18_half_12 : AdmissibleExponent 18 24 (34734087923671/2500000000000 : ℝ) := SeedCompletionHigher18SimpleSeeds.degree18_half_12

theorem early18_half_13 : AdmissibleExponent 18 26 (152823304157929/10000000000000 : ℝ) := SeedCompletionHigher18SimpleSeeds.degree18_half_13

theorem early18_half_14 : AdmissibleExponent 18 28 (83524965758289/5000000000000 : ℝ) := SeedCompletionHigher18SimpleSeeds.degree18_half_14

theorem early18_half_15 : AdmissibleExponent 18 30 (36321804174739/2000000000000 : ℝ) := SeedCompletionHigher18SimpleSeeds.degree18_half_15

theorem early18_half_16 : AdmissibleExponent 18 32 (196497247557249/10000000000000 : ℝ) := SeedCompletionHigher18SimpleSeeds.degree18_half_16

theorem early18_half_17 : AdmissibleExponent 18 34 (105853452759601/5000000000000 : ℝ) := SeedCompletionHigher18SimpleSeeds.degree18_half_17

theorem early18_half_18 : AdmissibleExponent 18 36 (56943719677/2500000000 : ℝ) := SeedCompletionAlternate18Seeds.half_18_01

theorem early18_half_19 : AdmissibleExponent 18 38 (244132867199/10000000000 : ℝ) := SeedCompletionAlternate18Seeds.half_19_01

theorem early18_half_20 : AdmissibleExponent 18 40 (130370579271/5000000000 : ℝ) := SeedCompletionAlternate18Seeds.half_20_01

theorem early18_half_21 : AdmissibleExponent 18 42 (69398983451/2500000000 : ℝ) := SeedCompletionAlternate18Seeds.half_21_01

theorem early18_half_22 : AdmissibleExponent 18 44 (294681560701/10000000000 : ℝ) := SeedCompletionAlternate18Seeds.half_22_01

theorem early18_half_23 : AdmissibleExponent 18 46 (311981827523/10000000000 : ℝ) := SeedCompletionAlternate18Seeds.half_23_01

theorem early18_half_24 : AdmissibleExponent 18 48 (329493912951/10000000000 : ℝ) := SeedCompletionAlternate18Seeds.half_24_01

theorem early18_half_25 : AdmissibleExponent 18 50 (347217235209/10000000000 : ℝ) := SeedCompletionAlternate18Seeds.half_25_01

theorem early18_half_26 : AdmissibleExponent 18 52 (91288259851/2500000000 : ℝ) := SeedCompletionAlternate18Seeds.half_26_01

theorem early18_half_27 : AdmissibleExponent 18 54 (383312569361/10000000000 : ℝ) := SeedCompletionAlternate18Seeds.half_27_01

theorem early18_half_28 : AdmissibleExponent 18 56 (200854983193/5000000000 : ℝ) := SeedCompletionAlternate18Seeds.half_28_01

theorem early18_half_29 : AdmissibleExponent 18 58 (420391726201/10000000000 : ℝ) := SeedCompletionAlternate18Seeds.half_29_01

theorem early18_half_30 : AdmissibleExponent 18 60 (21975797931/500000000 : ℝ) := SeedCompletionAlternate18Seeds.half_30_01

theorem early18_half_31 : AdmissibleExponent 18 62 (459668326301/10000000000 : ℝ) := SeedCompletionAlternate18Seeds.half_31_01

theorem early_coefficient9_admissible :
    Certificate.AdmissibleCurve 18 Certificate.earlyCoefficientSource9 := by
  intro i hi
  have hib : i ≤ 31 := by norm_num [Certificate.earlyCoefficientSource9] at hi; omega
  interval_cases i
  · convert early18_half_0 using 1 <;>
      norm_num [Certificate.earlyCoefficientSource9, Certificate.Q]
  · convert early18_half_1 using 1 <;>
      norm_num [Certificate.earlyCoefficientSource9, Certificate.Q]
  · convert early18_half_2 using 1 <;>
      norm_num [Certificate.earlyCoefficientSource9, Certificate.Q]
  · convert early18_half_3 using 1 <;>
      norm_num [Certificate.earlyCoefficientSource9, Certificate.Q]
  · convert early18_half_4 using 1 <;>
      norm_num [Certificate.earlyCoefficientSource9, Certificate.Q]
  · convert early18_half_5 using 1 <;>
      norm_num [Certificate.earlyCoefficientSource9, Certificate.Q]
  · convert early18_half_6 using 1 <;>
      norm_num [Certificate.earlyCoefficientSource9, Certificate.Q]
  · convert early18_half_7 using 1 <;>
      norm_num [Certificate.earlyCoefficientSource9, Certificate.Q]
  · convert early18_half_8 using 1 <;>
      norm_num [Certificate.earlyCoefficientSource9, Certificate.Q]
  · convert early18_half_9 using 1 <;>
      norm_num [Certificate.earlyCoefficientSource9, Certificate.Q]
  · convert early18_half_10 using 1 <;>
      norm_num [Certificate.earlyCoefficientSource9, Certificate.Q]
  · convert early18_half_11 using 1 <;>
      norm_num [Certificate.earlyCoefficientSource9, Certificate.Q]
  · convert early18_half_12 using 1 <;>
      norm_num [Certificate.earlyCoefficientSource9, Certificate.Q]
  · convert early18_half_13 using 1 <;>
      norm_num [Certificate.earlyCoefficientSource9, Certificate.Q]
  · convert early18_half_14 using 1 <;>
      norm_num [Certificate.earlyCoefficientSource9, Certificate.Q]
  · convert early18_half_15 using 1 <;>
      norm_num [Certificate.earlyCoefficientSource9, Certificate.Q]
  · convert early18_half_16 using 1 <;>
      norm_num [Certificate.earlyCoefficientSource9, Certificate.Q]
  · convert early18_half_17 using 1 <;>
      norm_num [Certificate.earlyCoefficientSource9, Certificate.Q]
  · convert early18_half_18 using 1 <;>
      norm_num [Certificate.earlyCoefficientSource9, Certificate.Q]
  · convert early18_half_19 using 1 <;>
      norm_num [Certificate.earlyCoefficientSource9, Certificate.Q]
  · convert early18_half_20 using 1 <;>
      norm_num [Certificate.earlyCoefficientSource9, Certificate.Q]
  · convert early18_half_21 using 1 <;>
      norm_num [Certificate.earlyCoefficientSource9, Certificate.Q]
  · convert early18_half_22 using 1 <;>
      norm_num [Certificate.earlyCoefficientSource9, Certificate.Q]
  · convert early18_half_23 using 1 <;>
      norm_num [Certificate.earlyCoefficientSource9, Certificate.Q]
  · convert early18_half_24 using 1 <;>
      norm_num [Certificate.earlyCoefficientSource9, Certificate.Q]
  · convert early18_half_25 using 1 <;>
      norm_num [Certificate.earlyCoefficientSource9, Certificate.Q]
  · convert early18_half_26 using 1 <;>
      norm_num [Certificate.earlyCoefficientSource9, Certificate.Q]
  · convert early18_half_27 using 1 <;>
      norm_num [Certificate.earlyCoefficientSource9, Certificate.Q]
  · convert early18_half_28 using 1 <;>
      norm_num [Certificate.earlyCoefficientSource9, Certificate.Q]
  · convert early18_half_29 using 1 <;>
      norm_num [Certificate.earlyCoefficientSource9, Certificate.Q]
  · convert early18_half_30 using 1 <;>
      norm_num [Certificate.earlyCoefficientSource9, Certificate.Q]
  · convert early18_half_31 using 1 <;>
      norm_num [Certificate.earlyCoefficientSource9, Certificate.Q]

#print axioms early_coefficient9_admissible
end Waring.SeedCompletionEarly18Seeds
