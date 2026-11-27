import Waring.SeedCompletionAlternate9Steps13

noncomputable section
set_option maxHeartbeats 2000000
namespace Waring.SeedCompletionAlternate9Seeds
open SmoothMoments FirstStageTransport SeedCompletionNaturalBox
open SeedCompletionSourceBounds SeedCompletionPaddedSource SeedCompletionGeneralTerminal
open PolicyCompletionMajorPowerRanges SeedCompletionDivisorPowerScales
open PolicyCompletionSharpResidualSource

theorem alternate9_half_0 : AdmissibleExponent 9 0 (0/1 : ℝ) := by
  simpa only [div_one] using admissibleExponent_zero 9

theorem alternate9_half_1 : AdmissibleExponent 9 2 (1/1 : ℝ) := by
  simpa only [div_one] using (admissibleExponent_two (k := 9) (by norm_num))

theorem alternate9_half_2 : AdmissibleExponent 9 4 (2/1 : ℝ) := by
  simpa only [div_one] using (FourthMomentSeed.admissibleExponent_four (k := 9) (by norm_num))

theorem alternate9_half_3 : AdmissibleExponent 9 6 (7589513/2500000 : ℝ) := NinthFirstSeeds.source9_six

theorem alternate9_half_4 : AdmissibleExponent 9 8 (20911447/5000000 : ℝ) := NinthFirstSeeds.source9_eight

theorem alternate9_half_5 : AdmissibleExponent 9 10 (10839411262123/2000000000000 : ℝ) := SeedCompletionNinthSecondSeeds.ninth_half_5

theorem alternate9_half_6 : AdmissibleExponent 9 12 (131607585753/19531250000 : ℝ) := SeedCompletionNinthSecondSeeds.ninth_half_6

theorem alternate9_half_7 : AdmissibleExponent 9 14 (40678172815313/5000000000000 : ℝ) := SeedCompletionNinthSecondSeeds.ninth_half_7

theorem alternate9_half_8 : AdmissibleExponent 9 16 (19207854001131/2000000000000 : ℝ) := SeedCompletionHigher9SimpleSeeds.degree9_half_8

theorem alternate9_half_9 : AdmissibleExponent 9 18 (111425025776259/10000000000000 : ℝ) := SeedCompletionHigher9SimpleSeeds.degree9_half_9

theorem alternate9_half_10 : AdmissibleExponent 9 20 (127463434667/10000000000 : ℝ) := half_10_12

theorem alternate9_half_11 : AdmissibleExponent 9 22 (144105873659/10000000000 : ℝ) := half_11_12

theorem alternate9_half_12 : AdmissibleExponent 9 24 (8064613057/500000000 : ℝ) := half_12_12

theorem alternate9_half_13 : AdmissibleExponent 9 26 (178959946183/10000000000 : ℝ) := half_13_12

theorem alternate9_half_14 : AdmissibleExponent 9 28 (197056896931/10000000000 : ℝ) := half_14_12

theorem alternate9_half_15 : AdmissibleExponent 9 30 (43102443749/2000000000 : ℝ) := half_15_12

theorem alternate9_half_16 : AdmissibleExponent 9 32 (2342898811/100000000 : ℝ) := half_16_12

theorem alternate9_half_17 : AdmissibleExponent 9 34 (126667667711/5000000000 : ℝ) := half_17_12

theorem alternate9_half_18 : AdmissibleExponent 9 36 (272593264251/10000000000 : ℝ) := half_18_12

theorem alternate9_half_19 : AdmissibleExponent 9 38 (292020275127/10000000000 : ℝ) := half_19_12

theorem alternate9_half_20 : AdmissibleExponent 9 40 (311579570947/10000000000 : ℝ) := half_20_12

theorem alternate9_half_21 : AdmissibleExponent 9 42 (8281051003/250000000 : ℝ) := half_21_12

theorem alternate9_half_22 : AdmissibleExponent 9 44 (350985080263/10000000000 : ℝ) := half_22_12

theorem alternate_source9_admissible :
    Certificate.AdmissibleCurve 9 Certificate.alternateSource9 := by
  intro i hi
  have hib : i≤22 := by norm_num [Certificate.alternateSource9] at hi; omega
  interval_cases i
  · convert alternate9_half_0 using 1 <;>
      norm_num [Certificate.alternateSource9,Certificate.Q]
  · convert alternate9_half_1 using 1 <;>
      norm_num [Certificate.alternateSource9,Certificate.Q]
  · convert alternate9_half_2 using 1 <;>
      norm_num [Certificate.alternateSource9,Certificate.Q]
  · convert alternate9_half_3 using 1 <;>
      norm_num [Certificate.alternateSource9,Certificate.Q]
  · convert alternate9_half_4 using 1 <;>
      norm_num [Certificate.alternateSource9,Certificate.Q]
  · convert alternate9_half_5 using 1 <;>
      norm_num [Certificate.alternateSource9,Certificate.Q]
  · convert alternate9_half_6 using 1 <;>
      norm_num [Certificate.alternateSource9,Certificate.Q]
  · convert alternate9_half_7 using 1 <;>
      norm_num [Certificate.alternateSource9,Certificate.Q]
  · convert alternate9_half_8 using 1 <;>
      norm_num [Certificate.alternateSource9,Certificate.Q]
  · convert alternate9_half_9 using 1 <;>
      norm_num [Certificate.alternateSource9,Certificate.Q]
  · convert alternate9_half_10 using 1 <;>
      norm_num [Certificate.alternateSource9,Certificate.Q]
  · convert alternate9_half_11 using 1 <;>
      norm_num [Certificate.alternateSource9,Certificate.Q]
  · convert alternate9_half_12 using 1 <;>
      norm_num [Certificate.alternateSource9,Certificate.Q]
  · convert alternate9_half_13 using 1 <;>
      norm_num [Certificate.alternateSource9,Certificate.Q]
  · convert alternate9_half_14 using 1 <;>
      norm_num [Certificate.alternateSource9,Certificate.Q]
  · convert alternate9_half_15 using 1 <;>
      norm_num [Certificate.alternateSource9,Certificate.Q]
  · convert alternate9_half_16 using 1 <;>
      norm_num [Certificate.alternateSource9,Certificate.Q]
  · convert alternate9_half_17 using 1 <;>
      norm_num [Certificate.alternateSource9,Certificate.Q]
  · convert alternate9_half_18 using 1 <;>
      norm_num [Certificate.alternateSource9,Certificate.Q]
  · convert alternate9_half_19 using 1 <;>
      norm_num [Certificate.alternateSource9,Certificate.Q]
  · convert alternate9_half_20 using 1 <;>
      norm_num [Certificate.alternateSource9,Certificate.Q]
  · convert alternate9_half_21 using 1 <;>
      norm_num [Certificate.alternateSource9,Certificate.Q]
  · convert alternate9_half_22 using 1 <;>
      norm_num [Certificate.alternateSource9,Certificate.Q]

#print axioms alternate_source9_admissible
end Waring.SeedCompletionAlternate9Seeds
