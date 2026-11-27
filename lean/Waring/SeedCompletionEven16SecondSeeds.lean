import Waring.SeedCompletionEvenSecondHolder
import Waring.SeedCompletionTwoStageUpdate
import Waring.SeedCompletionFirstGeneralA
import Waring.SeedCompletionFirstBGeneral
import Waring.CertificateData

/-! # Unconditional degree-16 source seeds through moment 16

Thirty exact finite A/B rounds start with proved endpoint moments.
Every auxiliary estimate is a theorem about the literal source sums.
All parameter balances and upward roundings are checked in Lean.
No published seed estimate or limiting recurrence value is assumed.
-/
noncomputable section
namespace Waring.SeedCompletionEven16SecondSeeds
open SmoothMoments FirstStageTransport SeedCompletionSecondScales
open SeedCompletionFirstGeneralA SeedCompletionSourceBounds

private theorem half_2_00 : AdmissibleExponent 16 4 2 :=
  FourthMomentSeed.admissibleExponent_four (by norm_num)

private theorem half_3_00 : AdmissibleExponent 16 6 (25/8 : ℝ) := by
  have h := endpoint_admissible (s := 1) (by norm_num : 0 < (16 : ℕ))
    half_2_00 (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_00 : AdmissibleExponent 16 8 (551/128 : ℝ) := by
  have h := endpoint_admissible (s := 2) (by norm_num : 0 < (16 : ℕ))
    half_3_00 (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_00 : AdmissibleExponent 16 10 (11337/2048 : ℝ) := by
  have h := endpoint_admissible (s := 3) (by norm_num : 0 < (16 : ℕ))
    half_4_00 (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_6_00 : AdmissibleExponent 16 12 (68146667480469/10000000000000 : ℝ) := by
  have h := endpoint_admissible (s := 4) (by norm_num : 0 < (16 : ℕ))
    half_5_00 (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_7_00 : AdmissibleExponent 16 14 (4069375038147/500000000000 : ℝ) := by
  have h := endpoint_admissible (s := 5) (by norm_num : 0 < (16 : ℕ))
    half_6_00 (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_8_00 : AdmissibleExponent 16 16 (95050781965257/10000000000000 : ℝ) := by
  have h := endpoint_admissible (s := 6) (by norm_num : 0 < (16 : ℕ))
    half_7_00 (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_3_01 : AdmissibleExponent 16 6 (15176072234763/5000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
    (φ := (39/2215 : ℝ)) half_4_00 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_01 : AdmissibleExponent 16 8 (20797824957007/5000000000000 : ℝ) := by
  have h := admissible_eight_B_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
    (φ := (7442378541417/177442378541417 : ℝ)) half_3_01 half_6_00
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_01 : AdmissibleExponent 16 10 (13328391366363/2500000000000 : ℝ) := by
  apply first_stage_admissible_source (s := 3) (φ := (22476958449413/502476958449413 : ℝ)) (χ := (2521545112771498/502476958449413 : ℝ))
    (by norm_num : 0 < (16 : ℕ)) half_4_01 (by norm_num) (by norm_num)
  · have h := first_A_cross_power (u := 4) (v := 5) (w := 6)
      (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
      (φ := (22476958449413/502476958449413 : ℝ)) (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
      (by norm_num) (by norm_num) half_5_00 half_6_00
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_01 : AdmissibleExponent 16 12 (65458993428449/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 4) (u := 3) (t := 6)
    (φ₁ := (459539903697/10000000000000 : ℝ)) (φ₂ := (451314942081/10000000000000 : ℝ)) (χ := (513651063718913765755432527/100000000000000000000000000 : ℝ)) (γ := (25682553185947/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_01 half_4_01 half_6_00
  · have h := even_B_second_cross (u := 4) (t := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (459539903697/10000000000000 : ℝ)) (φ₂ := (451314942081/10000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_00
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_7_01 : AdmissibleExponent 16 14 (19554942241357/2500000000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 5) (u := 4) (t := 7)
    (φ₁ := (50618345911/1000000000000 : ℝ)) (φ₂ := (139563267481/2500000000000 : ℝ)) (χ := (484833407930202156870114131/80000000000000000000000000 : ℝ)) (γ := (60604175991279/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_6_01 half_5_01 half_7_00
  · have h := even_B_second_cross (u := 5) (t := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (50618345911/1000000000000 : ℝ)) (φ₂ := (139563267481/2500000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/8 : ℝ)) (c := (5/8 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_00
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_8_01 : AdmissibleExponent 16 16 (45755547004507/5000000000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 6) (u := 5) (t := 8)
    (φ₁ := (532747286383/10000000000000 : ℝ)) (φ₂ := (292854560133/5000000000000 : ℝ)) (χ := (2829287607827543244254618621/400000000000000000000000000 : ℝ)) (γ := (70732190195689/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_01 half_6_01 half_8_00
  · have h := even_A_second_cross (u := 6) (v := 8) (w := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (532747286383/10000000000000 : ℝ)) (φ₂ := (292854560133/5000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_00 half_8_00
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_02 : AdmissibleExponent 16 6 (1509298894901/500000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
    (φ := (797824957007/85797824957007 : ℝ)) half_4_01 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_02 : AdmissibleExponent 16 8 (41052204515691/10000000000000 : ℝ) := by
  have h := admissible_eight_B_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
    (φ := (5087037632409/175087037632409 : ℝ)) half_3_02 half_6_01
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_02 : AdmissibleExponent 16 10 (13112676257767/2500000000000 : ℝ) := by
  apply first_stage_admissible_source (s := 3) (φ := (5959102098863/165959102098863 : ℝ)) (χ := (828753476448782/165959102098863 : ℝ))
    (by norm_num : 0 < (16 : ℕ)) half_4_02 (by norm_num) (by norm_num)
  · have h := first_A_cross_power (u := 4) (v := 5) (w := 6)
      (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
      (φ := (5959102098863/165959102098863 : ℝ)) (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
      (by norm_num) (by norm_num) half_5_01 half_6_01
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_02 : AdmissibleExponent 16 12 (4020382877057/625000000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 4) (u := 3) (t := 6)
    (φ₁ := (197208076699/5000000000000 : ℝ)) (φ₂ := (55203209721/2000000000000 : ℝ)) (χ := (526597062762761601424572479/100000000000000000000000000 : ℝ)) (γ := (52659706276277/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_02 half_4_02 half_6_01
  · have h := even_B_second_cross (u := 4) (t := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (197208076699/5000000000000 : ℝ)) (φ₂ := (55203209721/2000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_01
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_7_02 : AdmissibleExponent 16 14 (76743427515569/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 5) (u := 4) (t := 7)
    (φ₁ := (54273694967/1250000000000 : ℝ)) (φ₂ := (206467106537/5000000000000 : ℝ)) (χ := (49526057547887673608594533/8000000000000000000000000 : ℝ)) (γ := (3095378596743/500000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_6_02 half_5_02 half_7_01
  · have h := even_B_second_cross (u := 5) (t := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (54273694967/1250000000000 : ℝ)) (φ₂ := (206467106537/5000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/8 : ℝ)) (c := (5/8 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_01
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_8_02 : AdmissibleExponent 16 16 (17934084679559/2000000000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 6) (u := 5) (t := 8)
    (φ₁ := (231359032529/5000000000000 : ℝ)) (φ₂ := (460785018767/10000000000000 : ℝ)) (χ := (57524481999691965319144087/8000000000000000000000000 : ℝ)) (γ := (71905602499619/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_02 half_6_02 half_8_01
  · have h := even_A_second_cross (u := 6) (v := 8) (w := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (231359032529/5000000000000 : ℝ)) (φ₂ := (460785018767/10000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_01 half_8_01
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_03 : AdmissibleExponent 16 6 (30123027296687/10000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
    (φ := (1052204515691/171052204515691 : ℝ)) half_4_02 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_03 : AdmissibleExponent 16 8 (20411640409031/5000000000000 : ℝ) := by
  have h := admissible_eight_B_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
    (φ := (2040035719769/87040035719769 : ℝ)) half_3_03 half_6_02
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_03 : AdmissibleExponent 16 10 (26041015988087/5000000000000 : ℝ) := by
  apply first_stage_admissible_source (s := 3) (φ := (39836032057/1239836032057 : ℝ)) (χ := (154461644057036/30995900801425 : ℝ))
    (by norm_num : 0 < (16 : ℕ)) half_4_03 (by norm_num) (by norm_num)
  · have h := first_A_cross_power (u := 4) (v := 5) (w := 6)
      (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
      (φ := (39836032057/1239836032057 : ℝ)) (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
      (by norm_num) (by norm_num) half_5_02 half_6_02
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_03 : AdmissibleExponent 16 12 (31913443562257/5000000000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 4) (u := 3) (t := 6)
    (φ₁ := (364133793709/10000000000000 : ℝ)) (φ₂ := (89698445853/5000000000000 : ℝ)) (χ := (42657440178993729218013603/8000000000000000000000000 : ℝ)) (γ := (53321800223743/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_03 half_4_03 half_6_02
  · have h := even_B_second_cross (u := 4) (t := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (364133793709/10000000000000 : ℝ)) (φ₂ := (89698445853/5000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_02
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_7_03 : AdmissibleExponent 16 14 (76056024933821/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 5) (u := 4) (t := 7)
    (φ₁ := (99208397719/2500000000000 : ℝ)) (φ₂ := (328370783741/10000000000000 : ℝ)) (χ := (200578838892712094561646097/32000000000000000000000000 : ℝ)) (γ := (62680887153973/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_6_03 half_5_03 half_7_02
  · have h := even_B_second_cross (u := 5) (t := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (99208397719/2500000000000 : ℝ)) (φ₂ := (328370783741/10000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/8 : ℝ)) (c := (5/8 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_02
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_8_03 : AdmissibleExponent 16 16 (44376444521743/5000000000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 6) (u := 5) (t := 8)
    (φ₁ := (210877108193/5000000000000 : ℝ)) (φ₂ := (386180880997/10000000000000 : ℝ)) (χ := (581839652266136592956517709/80000000000000000000000000 : ℝ)) (γ := (18182489133317/2500000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_03 half_6_03 half_8_02
  · have h := even_A_second_cross (u := 6) (v := 8) (w := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (210877108193/5000000000000 : ℝ)) (φ₂ := (386180880997/10000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_02 half_8_02
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_04 : AdmissibleExponent 16 6 (7524097441933/2500000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
    (φ := (411640409031/85411640409031 : ℝ)) half_4_03 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_04 : AdmissibleExponent 16 8 (10180565745301/2500000000000 : ℝ) := by
  have h := admissible_eight_B_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
    (φ := (4275420693/204275420693 : ℝ)) half_3_04 half_6_03
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_04 : AdmissibleExponent 16 10 (51920336396787/10000000000000 : ℝ) := by
  apply first_stage_admissible_source (s := 3) (φ := (7550949576023/247550949576023 : ℝ)) (χ := (1232436210700942/247550949576023 : ℝ))
    (by norm_num : 0 < (16 : ℕ)) half_4_04 (by norm_num) (by norm_num)
  · have h := first_A_cross_power (u := 4) (v := 5) (w := 6)
      (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
      (φ := (7550949576023/247550949576023 : ℝ)) (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
      (by norm_num) (by norm_num) half_5_03 half_6_03
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_04 : AdmissibleExponent 16 12 (15900521341787/2500000000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 4) (u := 3) (t := 6)
    (φ₁ := (2798270777/80000000000 : ℝ)) (φ₂ := (129688527519/10000000000000 : ℝ)) (χ := (134131684471508039725028877/25000000000000000000000000 : ℝ)) (γ := (13413168447151/2500000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_04 half_4_04 half_6_03
  · have h := even_B_second_cross (u := 4) (t := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (2798270777/80000000000 : ℝ)) (φ₂ := (129688527519/10000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_03
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_7_04 : AdmissibleExponent 16 14 (18933965556749/2500000000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 5) (u := 4) (t := 7)
    (φ₁ := (94585804889/2500000000000 : ℝ)) (φ₂ := (283697437731/10000000000000 : ℝ)) (χ := (504732385421670173917108759/80000000000000000000000000 : ℝ)) (γ := (63091548177709/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_6_04 half_5_04 half_7_03
  · have h := even_B_second_cross (u := 5) (t := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (94585804889/2500000000000 : ℝ)) (φ₂ := (283697437731/10000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/8 : ℝ)) (c := (5/8 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_03
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_8_04 : AdmissibleExponent 16 16 (22076642138769/2500000000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 6) (u := 5) (t := 8)
    (φ₁ := (200010956123/5000000000000 : ℝ)) (φ₂ := (346250952999/10000000000000 : ℝ)) (χ := (292806226352856840613086779/40000000000000000000000000 : ℝ)) (γ := (14640311317643/2000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_04 half_6_04 half_8_03
  · have h := even_A_second_cross (u := 6) (v := 8) (w := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (200010956123/5000000000000 : ℝ)) (φ₂ := (346250952999/10000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_03 half_8_03
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_05 : AdmissibleExponent 16 6 (30084612629729/10000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
    (φ := (180565745301/42680565745301 : ℝ)) half_4_04 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_05 : AdmissibleExponent 16 8 (5084593218243/1250000000000 : ℝ) := by
  have h := admissible_eight_B_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
    (φ := (343286010769/17343286010769 : ℝ)) half_3_05 half_6_04
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_05 : AdmissibleExponent 16 10 (51847994446741/10000000000000 : ℝ) := by
  apply first_stage_admissible_source (s := 3) (φ := (2455962529491/82455962529491 : ℝ)) (χ := (410325891026534/82455962529491 : ℝ))
    (by norm_num : 0 < (16 : ℕ)) half_4_05 (by norm_num) (by norm_num)
  · have h := first_A_cross_power (u := 4) (v := 5) (w := 6)
      (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
      (φ := (2455962529491/82455962529491 : ℝ)) (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
      (by norm_num) (by norm_num) half_5_04 half_6_04
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_05 : AdmissibleExponent 16 12 (31749812108529/5000000000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 4) (u := 3) (t := 6)
    (φ₁ := (10718853707/312500000000 : ℝ)) (φ₂ := (6568245459/625000000000 : ℝ)) (χ := (16816900704660674459766663/3125000000000000000000000 : ℝ)) (γ := (10762816450983/2000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_05 half_4_05 half_6_04
  · have h := even_B_second_cross (u := 4) (t := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (10718853707/312500000000 : ℝ)) (φ₂ := (6568245459/625000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_04
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_7_05 : AdmissibleExponent 16 14 (75586796156193/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 5) (u := 4) (t := 7)
    (φ₁ := (92352126433/2500000000000 : ℝ)) (φ₂ := (261268425891/10000000000000 : ℝ)) (χ := (253192807527209642909607913/40000000000000000000000000 : ℝ)) (γ := (12659640376361/2000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_6_05 half_5_05 half_7_04
  · have h := even_B_second_cross (u := 5) (t := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (92352126433/2500000000000 : ℝ)) (φ₂ := (261268425891/10000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/8 : ℝ)) (c := (5/8 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_04
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_8_05 : AdmissibleExponent 16 16 (4404645203183/500000000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 6) (u := 5) (t := 8)
    (φ₁ := (389067420639/10000000000000 : ℝ)) (φ₂ := (326045517061/10000000000000 : ℝ)) (χ := (7344871814285998680449261/1000000000000000000000000 : ℝ)) (γ := (4590544883929/625000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_05 half_6_05 half_8_04
  · have h := even_A_second_cross (u := 6) (v := 8) (w := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (389067420639/10000000000000 : ℝ)) (φ₂ := (326045517061/10000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_04 half_8_04
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_06 : AdmissibleExponent 16 6 (30079301458789/10000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
    (φ := (84593218243/21334593218243 : ℝ)) half_4_05 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_06 : AdmissibleExponent 16 8 (5082000127643/1250000000000 : ℝ) := by
  have h := admissible_eight_B_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
    (φ := (83525532487/4333525532487 : ℝ)) half_3_06 half_6_05
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_06 : AdmissibleExponent 16 10 (6476899612413/1250000000000 : ℝ) := by
  apply first_stage_admissible_source (s := 3) (φ := (3642902256491/123642902256491 : ℝ)) (χ := (615157816766710/123642902256491 : ℝ))
    (by norm_num : 0 < (16 : ℕ)) half_4_06 (by norm_num) (by norm_num)
  · have h := first_A_cross_power (u := 4) (v := 5) (w := 6)
      (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
      (φ := (3642902256491/123642902256491 : ℝ)) (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
      (by norm_num) (by norm_num) half_5_05 half_6_05
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_06 : AdmissibleExponent 16 12 (3172629543273/500000000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 4) (u := 3) (t := 6)
    (φ₁ := (169907715793/5000000000000 : ℝ)) (φ₂ := (932062209/100000000000 : ℝ)) (χ := (26945741446844082056468531/5000000000000000000000000 : ℝ)) (γ := (5389148289369/1000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_06 half_4_06 half_6_05
  · have h := even_B_second_cross (u := 4) (t := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (169907715793/5000000000000 : ℝ)) (φ₂ := (932062209/100000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_05
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_7_06 : AdmissibleExponent 16 14 (1179960014803/156250000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 5) (u := 4) (t := 7)
    (φ₁ := (182576895523/5000000000000 : ℝ)) (φ₂ := (250338522757/10000000000000 : ℝ)) (χ := (50719234410719110269565051/8000000000000000000000000 : ℝ)) (γ := (316995215067/50000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_6_06 half_5_06 half_7_05
  · have h := even_B_second_cross (u := 5) (t := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (182576895523/5000000000000 : ℝ)) (φ₂ := (250338522757/10000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/8 : ℝ)) (c := (5/8 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_05
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_8_06 : AdmissibleExponent 16 16 (687435244921/78125000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 6) (u := 5) (t := 8)
    (φ₁ := (191855785413/5000000000000 : ℝ)) (φ₂ := (158075327623/5000000000000 : ℝ)) (χ := (18393065202249870830004809/2500000000000000000000000 : ℝ)) (γ := (73572260809003/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_06 half_6_06 half_8_05
  · have h := even_A_second_cross (u := 6) (v := 8) (w := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (191855785413/5000000000000 : ℝ)) (φ₂ := (158075327623/5000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_05 half_8_05
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_07 : AdmissibleExponent 16 6 (30076879924201/10000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
    (φ := (82000127643/21332000127643 : ℝ)) half_4_06 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_07 : AdmissibleExponent 16 8 (2032324083483/500000000000 : ℝ) := by
  have h := admissible_eight_B_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
    (φ := (1649415508529/86649415508529 : ℝ)) half_3_07 half_6_06
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_07 : AdmissibleExponent 16 10 (12950049958073/2500000000000 : ℝ) := by
  apply first_stage_admissible_source (s := 3) (φ := (3624264496357/123624264496357 : ℝ)) (χ := (615006309028634/123624264496357 : ℝ))
    (by norm_num : 0 < (16 : ℕ)) half_4_07 (by norm_num) (by norm_num)
  · have h := first_A_cross_power (u := 4) (v := 5) (w := 6)
      (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
      (φ := (3624264496357/123624264496357 : ℝ)) (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
      (by norm_num) (by norm_num) half_5_06 half_6_06
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_07 : AdmissibleExponent 16 12 (63430909443951/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 4) (u := 3) (t := 6)
    (φ₁ := (169161449423/5000000000000 : ℝ)) (φ₂ := (17509546911/2000000000000 : ℝ)) (χ := (8426276817516525286793679/1562500000000000000000000 : ℝ)) (γ := (53928171632107/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_07 half_4_07 half_6_06
  · have h := even_B_second_cross (u := 4) (t := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (169161449423/5000000000000 : ℝ)) (φ₂ := (17509546911/2000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_06
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_7_07 : AdmissibleExponent 16 14 (15097039258857/2000000000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 5) (u := 4) (t := 7)
    (φ₁ := (90786630567/2500000000000 : ℝ)) (φ₂ := (7659652051/312500000000 : ℝ)) (χ := (79309169749591331401441/12500000000000000000000 : ℝ)) (γ := (15861833949919/2500000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_6_07 half_5_07 half_7_06
  · have h := even_B_second_cross (u := 5) (t := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (90786630567/2500000000000 : ℝ)) (φ₂ := (7659652051/312500000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/8 : ℝ)) (c := (5/8 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_06
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_8_07 : AdmissibleExponent 16 16 (87944130016573/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 6) (u := 5) (t := 8)
    (φ₁ := (381142556599/10000000000000 : ℝ)) (φ₂ := (311401496827/10000000000000 : ℝ)) (χ := (11505047293423882746275981/1562500000000000000000000 : ℝ)) (γ := (73632302677913/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_07 half_6_07 half_8_06
  · have h := even_A_second_cross (u := 6) (v := 8) (w := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (381142556599/10000000000000 : ℝ)) (φ₂ := (311401496827/10000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_06 half_8_06
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_08 : AdmissibleExponent 16 6 (30075768531919/10000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
    (φ := (32324083483/8532324083483 : ℝ)) half_4_07 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_08 : AdmissibleExponent 16 8 (4064209501859/1000000000000 : ℝ) := by
  have h := admissible_eight_B_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
    (φ := (3279372380113/173279372380113 : ℝ)) half_3_08 half_6_07
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_08 : AdmissibleExponent 16 10 (1035866097061/200000000000 : ℝ) := by
  apply first_stage_admissible_source (s := 3) (φ := (192839053789/6592839053789 : ℝ)) (χ := (163983094597378/32964195268945 : ℝ))
    (by norm_num : 0 < (16 : ℕ)) half_4_08 (by norm_num) (by norm_num)
  · have h := first_A_cross_power (u := 4) (v := 5) (w := 6)
      (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
      (φ := (192839053789/6592839053789 : ℝ)) (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
      (by norm_num) (by norm_num) half_5_07 half_6_07
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_08 : AdmissibleExponent 16 12 (1981902793537/312500000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 4) (u := 3) (t := 6)
    (φ₁ := (337626243651/10000000000000 : ℝ)) (φ₂ := (84879264791/10000000000000 : ℝ)) (χ := (539454297266144235374295367/100000000000000000000000000 : ℝ)) (γ := (53945429726619/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_08 half_4_08 half_6_07
  · have h := even_B_second_cross (u := 4) (t := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (337626243651/10000000000000 : ℝ)) (φ₂ := (84879264791/10000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_07
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_7_08 : AdmissibleExponent 16 14 (3018808576671/400000000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 5) (u := 4) (t := 7)
    (φ₁ := (14488209529/400000000000 : ℝ)) (φ₂ := (12131754431/500000000000 : ℝ)) (χ := (203104618959131362282639563/32000000000000000000000000 : ℝ)) (γ := (63470193424729/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_6_08 half_5_08 half_7_07
  · have h := even_B_second_cross (u := 5) (t := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (14488209529/400000000000 : ℝ)) (φ₂ := (12131754431/500000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/8 : ℝ)) (c := (5/8 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_07
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_8_08 : AdmissibleExponent 16 16 (17584372694483/2000000000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 6) (u := 5) (t := 8)
    (φ₁ := (47490647797/1250000000000 : ℝ)) (φ₂ := (154575293449/5000000000000 : ℝ)) (χ := (1473219648595490928483732997/200000000000000000000000000 : ℝ)) (γ := (36830491214889/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_08 half_6_08 half_8_07
  · have h := even_A_second_cross (u := 6) (v := 8) (w := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (47490647797/1250000000000 : ℝ)) (φ₂ := (154575293449/5000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_07 half_8_07
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_09 : AdmissibleExponent 16 6 (15037628172493/5000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
    (φ := (64209501859/17064209501859 : ℝ)) half_4_08 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_09 : AdmissibleExponent 16 8 (40640068324743/10000000000000 : ℝ) := by
  have h := admissible_eight_B_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
    (φ := (817594175803/43317594175803 : ℝ)) half_3_09 half_6_08
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_09 : AdmissibleExponent 16 10 (51790123964103/10000000000000 : ℝ) := by
  apply first_stage_admissible_source (s := 3) (φ := (1805903225039/61805903225039 : ℝ)) (χ := (307452216398536/61805903225039 : ℝ))
    (by norm_num : 0 < (16 : ℕ)) half_4_09 (by norm_num) (by norm_num)
  · have h := first_A_cross_power (u := 4) (v := 5) (w := 6)
      (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
      (φ := (1805903225039/61805903225039 : ℝ)) (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
      (by norm_num) (by norm_num) half_5_08 half_6_08
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_09 : AdmissibleExponent 16 12 (63416251547571/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 4) (u := 3) (t := 6)
    (φ₁ := (168650877909/5000000000000 : ℝ)) (φ₂ := (16725680561/2000000000000 : ℝ)) (χ := (215814029398565320893023091/40000000000000000000000000 : ℝ)) (γ := (26976753674821/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_09 half_4_09 half_6_08
  · have h := even_B_second_cross (u := 4) (t := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (168650877909/5000000000000 : ℝ)) (φ₂ := (16725680561/2000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_08
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_7_09 : AdmissibleExponent 16 14 (37731628312697/5000000000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 5) (u := 4) (t := 7)
    (φ₁ := (361765548201/10000000000000 : ℝ)) (φ₂ := (241473316071/10000000000000 : ℝ)) (χ := (12696186500219656664986789/2000000000000000000000000 : ℝ)) (γ := (63480932501099/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_6_09 half_5_09 half_7_08
  · have h := even_B_second_cross (u := 5) (t := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (361765548201/10000000000000 : ℝ)) (φ₂ := (241473316071/10000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/8 : ℝ)) (c := (5/8 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_08
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_8_09 : AdmissibleExponent 16 16 (10988934479437/1250000000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 6) (u := 5) (t := 8)
    (φ₁ := (75870553179/2000000000000 : ℝ)) (φ₂ := (61618433351/2000000000000 : ℝ)) (χ := (11787925463760718102305803/1600000000000000000000000 : ℝ)) (γ := (14734906829701/2000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_09 half_6_09 half_8_08
  · have h := even_A_second_cross (u := 6) (v := 8) (w := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (75870553179/2000000000000 : ℝ)) (φ₂ := (61618433351/2000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_08 half_8_08
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_10 : AdmissibleExponent 16 6 (30075019698601/10000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
    (φ := (640068324743/170640068324743 : ℝ)) half_4_09 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_10 : AdmissibleExponent 16 8 (40639130456533/10000000000000 : ℝ) := by
  have h := admissible_eight_B_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
    (φ := (3266212150369/173266212150369 : ℝ)) half_3_10 half_6_09
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_10 : AdmissibleExponent 16 10 (51788653355511/10000000000000 : ℝ) := by
  apply first_stage_admissible_source (s := 3) (φ := (962665176643/32962665176643 : ℝ)) (χ := (273284246356986/54937775294405 : ℝ))
    (by norm_num : 0 < (16 : ℕ)) half_4_10 (by norm_num) (by norm_num)
  · have h := first_A_cross_power (u := 4) (v := 5) (w := 6)
      (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
      (φ := (962665176643/32962665176643 : ℝ)) (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
      (by norm_num) (by norm_num) half_5_09 half_6_09
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_10 : AdmissibleExponent 16 12 (31707051448639/5000000000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 4) (u := 3) (t := 6)
    (φ₁ := (337150827533/10000000000000 : ℝ)) (φ₂ := (83044287341/10000000000000 : ℝ)) (χ := (67446594902276305197077031/12500000000000000000000000 : ℝ)) (γ := (53957275921823/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_10 half_4_10 half_6_09
  · have h := even_B_second_cross (u := 4) (t := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (337150827533/10000000000000 : ℝ)) (φ₂ := (83044287341/10000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_09
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_7_10 : AdmissibleExponent 16 14 (75460026399809/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 5) (u := 4) (t := 7)
    (φ₁ := (180780336381/5000000000000 : ℝ)) (φ₂ := (30116271893/1250000000000 : ℝ)) (χ := (63485954472016511574245539/10000000000000000000000000 : ℝ)) (γ := (31742977236009/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_6_10 half_5_10 half_7_09
  · have h := even_B_second_cross (u := 5) (t := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (180780336381/5000000000000 : ℝ)) (φ₂ := (30116271893/1250000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/8 : ℝ)) (c := (5/8 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_09
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_8_10 : AdmissibleExponent 16 16 (87906639591899/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 6) (u := 5) (t := 8)
    (φ₁ := (379084938467/10000000000000 : ℝ)) (φ₂ := (153798478441/5000000000000 : ℝ)) (χ := (368404470701111422520684461/50000000000000000000000000 : ℝ)) (γ := (73680894140223/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_10 half_6_10 half_8_09
  · have h := even_A_second_cross (u := 6) (v := 8) (w := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (379084938467/10000000000000 : ℝ)) (φ₂ := (153798478441/5000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_09 half_8_09
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_11 : AdmissibleExponent 16 6 (15037455093379/5000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
    (φ := (639130456533/170639130456533 : ℝ)) half_4_10 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_11 : AdmissibleExponent 16 8 (40638696018879/10000000000000 : ℝ) := by
  have h := admissible_eight_B_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
    (φ := (1632141261881/86632141261881 : ℝ)) half_3_11 half_6_10
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_11 : AdmissibleExponent 16 10 (51787972542327/10000000000000 : ℝ) := by
  apply first_stage_admissible_source (s := 3) (φ := (300763031933/10300763031933 : ℝ)) (χ := (51240222082745/10300763031933 : ℝ))
    (by norm_num : 0 < (16 : ℕ)) half_4_11 (by norm_num) (by norm_num)
  · have h := first_A_cross_power (u := 4) (v := 5) (w := 6)
      (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
      (φ := (300763031933/10300763031933 : ℝ)) (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
      (by norm_num) (by norm_num) half_5_10 half_6_10
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_11 : AdmissibleExponent 16 12 (63413106893789/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 4) (u := 3) (t := 6)
    (φ₁ := (168540345341/5000000000000 : ℝ)) (φ₂ := (8277217959/1000000000000 : ℝ)) (χ := (8431098518980976329147449/1562500000000000000000000 : ℝ)) (γ := (53959030521479/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_11 half_4_11 half_6_10
  · have h := even_B_second_cross (u := 4) (t := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (168540345341/5000000000000 : ℝ)) (φ₂ := (8277217959/1000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_10
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_7_11 : AdmissibleExponent 16 14 (75458527071489/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 5) (u := 4) (t := 7)
    (φ₁ := (180732680787/5000000000000 : ℝ)) (φ₂ := (240676974053/10000000000000 : ℝ)) (χ := (1015812736293953026031714327/160000000000000000000000000 : ℝ)) (γ := (63488296018373/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_6_11 half_5_11 half_7_10
  · have h := even_B_second_cross (u := 5) (t := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (180732680787/5000000000000 : ℝ)) (φ₂ := (240676974053/10000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/8 : ℝ)) (c := (5/8 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_10
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_8_11 : AdmissibleExponent 16 16 (17580878167573/2000000000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 6) (u := 5) (t := 8)
    (φ₁ := (47370002097/1250000000000 : ℝ)) (φ₂ := (38420748347/1250000000000 : ℝ)) (χ := (92104832757755869665210133/12500000000000000000000000 : ℝ)) (γ := (14736773241241/2000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_11 half_6_11 half_8_10
  · have h := even_A_second_cross (u := 6) (v := 8) (w := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (47370002097/1250000000000 : ℝ)) (φ₂ := (38420748347/1250000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_10 half_8_10
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_12 : AdmissibleExponent 16 6 (7518714864617/2500000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
    (φ := (638696018879/170638696018879 : ℝ)) half_4_11 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_12 : AdmissibleExponent 16 8 (40638494655663/10000000000000 : ℝ) := by
  have h := admissible_eight_B_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
    (φ := (3263387976853/173263387976853 : ℝ)) half_3_12 half_6_11
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_12 : AdmissibleExponent 16 10 (6473457137393/1250000000000 : ℝ) := by
  apply first_stage_admissible_source (s := 3) (φ := (4811691118597/164811691118597 : ℝ)) (χ := (819839296727802/164811691118597 : ℝ))
    (by norm_num : 0 < (16 : ℕ)) half_4_12 (by norm_num) (by norm_num)
  · have h := first_A_cross_power (u := 4) (v := 5) (w := 6)
      (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
      (φ := (4811691118597/164811691118597 : ℝ)) (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
      (by norm_num) (by norm_num) half_5_11 half_6_11
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_12 : AdmissibleExponent 16 12 (31706322519087/5000000000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 4) (u := 3) (t := 6)
    (φ₁ := (337048116987/10000000000000 : ℝ)) (φ₂ := (82645611509/10000000000000 : ℝ)) (χ := (13489961594529210209171237/2500000000000000000000000 : ℝ)) (γ := (26979923189059/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_12 half_4_12 half_6_11
  · have h := even_B_second_cross (u := 4) (t := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (337048116987/10000000000000 : ℝ)) (φ₂ := (82645611509/10000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_11
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_7_12 : AdmissibleExponent 16 14 (37728915626349/5000000000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 5) (u := 4) (t := 7)
    (φ₁ := (361421065873/10000000000000 : ℝ)) (φ₂ := (30069893493/1250000000000 : ℝ)) (χ := (203166034462813778304043859/32000000000000000000000000 : ℝ)) (γ := (63489385769631/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_6_12 half_5_12 half_7_11
  · have h := even_B_second_cross (u := 5) (t := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (361421065873/10000000000000 : ℝ)) (φ₂ := (30069893493/1250000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/8 : ℝ)) (c := (5/8 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_11
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_8_12 : AdmissibleExponent 16 16 (87903346064569/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 6) (u := 5) (t := 8)
    (φ₁ := (189450932571/5000000000000 : ℝ)) (φ₂ := (307258472667/10000000000000 : ℝ)) (χ := (589482010717057712230997329/80000000000000000000000000 : ℝ)) (γ := (18421312834909/2500000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_12 half_6_12 half_8_11
  · have h := even_A_second_cross (u := 6) (v := 8) (w := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (189450932571/5000000000000 : ℝ)) (φ₂ := (307258472667/10000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_11 half_8_11
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_13 : AdmissibleExponent 16 6 (30074835945659/10000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
    (φ := (638494655663/170638494655663 : ℝ)) half_4_12 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_13 : AdmissibleExponent 16 8 (40638401287701/10000000000000 : ℝ) := by
  have h := admissible_eight_B_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
    (φ := (407871643357/21657871643357 : ℝ)) half_3_13 half_6_12
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_13 : AdmissibleExponent 16 10 (51787510868167/10000000000000 : ℝ) := by
  apply first_stage_admissible_source (s := 3) (φ := (2405725680943/82405725680943 : ℝ)) (χ := (409918661663494/82405725680943 : ℝ))
    (by norm_num : 0 < (16 : ℕ)) half_4_13 (by norm_num) (by norm_num)
  · have h := first_A_cross_power (u := 4) (v := 5) (w := 6)
      (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
      (φ := (2405725680943/82405725680943 : ℝ)) (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
      (by norm_num) (by norm_num) half_5_12 half_6_12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_13 : AdmissibleExponent 16 12 (31706215413103/5000000000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 4) (u := 3) (t := 6)
    (φ₁ := (21064562151/625000000000 : ℝ)) (φ₂ := (82586795683/10000000000000 : ℝ)) (χ := (1079204508506225798519097669/200000000000000000000000000 : ℝ)) (γ := (26980112712657/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_13 half_4_13 half_6_12
  · have h := even_B_second_cross (u := 4) (t := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (21064562151/625000000000 : ℝ)) (φ₂ := (82586795683/10000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_7_13 : AdmissibleExponent 16 14 (75457508363351/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 5) (u := 4) (t := 7)
    (φ₁ := (361400492547/10000000000000 : ℝ)) (φ₂ := (240504379419/10000000000000 : ℝ)) (χ := (507919138796206303043013673/80000000000000000000000000 : ℝ)) (γ := (63489892349527/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_6_13 half_5_13 half_7_12
  · have h := even_B_second_cross (u := 5) (t := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (361400492547/10000000000000 : ℝ)) (φ₂ := (240504379419/10000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/8 : ℝ)) (c := (5/8 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_8_13 : AdmissibleExponent 16 16 (87902860911081/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 6) (u := 5) (t := 8)
    (φ₁ := (189437414463/5000000000000 : ℝ)) (φ₂ := (307208487799/10000000000000 : ℝ)) (χ := (117897433270128202936686017/16000000000000000000000000 : ℝ)) (γ := (9210736974229/1250000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_13 half_6_13 half_8_12
  · have h := even_A_second_cross (u := 6) (v := 8) (w := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (189437414463/5000000000000 : ℝ)) (φ₂ := (307208487799/10000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_12 half_8_12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_14 : AdmissibleExponent 16 6 (7518706260809/2500000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
    (φ := (638401287701/170638401287701 : ℝ)) half_4_13 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_14 : AdmissibleExponent 16 8 (40638357984733/10000000000000 : ℝ) := by
  have h := admissible_eight_B_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
    (φ := (1631390369867/86631390369867 : ℝ)) half_3_14 half_6_13
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_14 : AdmissibleExponent 16 10 (51787443057623/10000000000000 : ℝ) := by
  apply first_stage_admissible_source (s := 3) (φ := (1804252577951/61804252577951 : ℝ)) (χ := (307438653064300/61804252577951 : ℝ))
    (by norm_num : 0 < (16 : ℕ)) half_4_14 (by norm_num) (by norm_num)
  · have h := first_A_cross_power (u := 4) (v := 5) (w := 6)
      (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
      (φ := (1804252577951/61804252577951 : ℝ)) (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
      (by norm_num) (by norm_num) half_5_13 half_6_13
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_14 : AdmissibleExponent 16 12 (63412331460193/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 4) (u := 3) (t := 6)
    (φ₁ := (33702597531/1000000000000 : ℝ)) (φ₂ := (41279740199/5000000000000 : ℝ)) (χ := (269802007200299284637024913/50000000000000000000000000 : ℝ)) (γ := (2698020072003/500000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_14 half_4_14 half_6_13
  · have h := even_B_second_cross (u := 4) (t := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (33702597531/1000000000000 : ℝ)) (φ₂ := (41279740199/5000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_13
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_7_14 : AdmissibleExponent 16 14 (18864339634573/2500000000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 5) (u := 4) (t := 7)
    (φ₁ := (36139094097/1000000000000 : ℝ)) (φ₂ := (60119734861/2500000000000 : ℝ)) (χ := (507921021332054601721266233/80000000000000000000000000 : ℝ)) (γ := (31745063833257/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_6_14 half_5_14 half_7_13
  · have h := even_B_second_cross (u := 5) (t := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (36139094097/1000000000000 : ℝ)) (φ₂ := (60119734861/2500000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/8 : ℝ)) (c := (5/8 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_13
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_8_14 : AdmissibleExponent 16 16 (87902635696629/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 6) (u := 5) (t := 8)
    (φ₁ := (3030898151/80000000000 : ℝ)) (φ₂ := (76796316761/2500000000000 : ℝ)) (χ := (2947447812784046889762144683/400000000000000000000000000 : ℝ)) (γ := (36843097659801/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_14 half_6_14 half_8_13
  · have h := even_A_second_cross (u := 6) (v := 8) (w := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (3030898151/80000000000 : ℝ)) (φ₂ := (76796316761/2500000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_13 half_8_13
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_15 : AdmissibleExponent 16 6 (234959531147/78125000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
    (φ := (638357984733/170638357984733 : ℝ)) half_4_14 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_15 : AdmissibleExponent 16 8 (20319168949203/5000000000000 : ℝ) := by
  have h := admissible_eight_B_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
    (φ := (3262691486561/173262691486561 : ℝ)) half_3_15 half_6_14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_15 : AdmissibleExponent 16 10 (25893705803053/5000000000000 : ℝ) := by
  apply first_stage_admissible_source (s := 3) (φ := (962257732121/32962257732121 : ℝ)) (χ := (819835983695706/164811288660605 : ℝ))
    (by norm_num : 0 < (16 : ℕ)) half_4_15 (by norm_num) (by norm_num)
  · have h := first_A_cross_power (u := 4) (v := 5) (w := 6)
      (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
      (φ := (962257732121/32962257732121 : ℝ)) (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
      (by norm_num) (by norm_num) half_5_14 half_6_14
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_15 : AdmissibleExponent 16 12 (31706142681907/5000000000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 4) (u := 3) (t := 6)
    (φ₁ := (337022717891/10000000000000 : ℝ)) (φ₂ := (41273399663/5000000000000 : ℝ)) (χ := (1079209662962403539995638507/200000000000000000000000000 : ℝ)) (γ := (53960483148121/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_15 half_4_15 half_6_14
  · have h := even_B_second_cross (u := 4) (t := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (337022717891/10000000000000 : ℝ)) (φ₂ := (41273399663/5000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_14
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_7_15 : AdmissibleExponent 16 14 (75457289020139/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 5) (u := 4) (t := 7)
    (φ₁ := (361386507561/10000000000000 : ℝ)) (φ₂ := (240467127731/10000000000000 : ℝ)) (χ := (253960947706681377370042333/40000000000000000000000000 : ℝ)) (γ := (63490236926673/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_6_15 half_5_15 half_7_14
  · have h := even_B_second_cross (u := 5) (t := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (361386507561/10000000000000 : ℝ)) (φ₂ := (240467127731/10000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/8 : ℝ)) (c := (5/8 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_14
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_8_15 : AdmissibleExponent 16 16 (87902531170281/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 6) (u := 5) (t := 8)
    (φ₁ := (378856436771/10000000000000 : ℝ)) (φ₂ := (38396810613/1250000000000 : ℝ)) (χ := (117898135103650382172735971/16000000000000000000000000 : ℝ)) (γ := (18421583609947/2500000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_15 half_6_15 half_8_14
  · have h := even_A_second_cross (u := 6) (v := 8) (w := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (378856436771/10000000000000 : ℝ)) (φ₂ := (38396810613/1250000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_14 half_8_14
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_16 : AdmissibleExponent 16 6 (15037408820683/5000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
    (φ := (319168949203/85319168949203 : ℝ)) half_4_15 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_16 : AdmissibleExponent 16 8 (40638328580413/10000000000000 : ℝ) := by
  have h := admissible_eight_B_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
    (φ := (1631325040541/86631325040541 : ℝ)) half_3_16 half_6_15
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_16 : AdmissibleExponent 16 10 (25893698508317/5000000000000 : ℝ) := by
  apply first_stage_admissible_source (s := 3) (φ := (2405632375729/82405632375729 : ℝ)) (χ := (45546432599418/9156181375081 : ℝ))
    (by norm_num : 0 < (16 : ℕ)) half_4_16 (by norm_num) (by norm_num)
  · have h := first_A_cross_power (u := 4) (v := 5) (w := 6)
      (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
      (φ := (2405632375729/82405632375729 : ℝ)) (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
      (by norm_num) (by norm_num) half_5_15 half_6_15
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_16 : AdmissibleExponent 16 12 (31706131989209/5000000000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 4) (u := 3) (t := 6)
    (φ₁ := (337021206331/10000000000000 : ℝ)) (φ₂ := (82540913523/10000000000000 : ℝ)) (χ := (539605210703187296097570513/100000000000000000000000000 : ℝ)) (γ := (53960521070319/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_16 half_4_16 half_6_15
  · have h := even_B_second_cross (u := 4) (t := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (337021206331/10000000000000 : ℝ)) (φ₂ := (82540913523/10000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_15
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_7_16 : AdmissibleExponent 16 14 (7545725676483/1000000000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 5) (u := 4) (t := 7)
    (φ₁ := (90346112523/2500000000000 : ℝ)) (φ₂ := (240461645073/10000000000000 : ℝ)) (χ := (203168920457621336490841727/32000000000000000000000000 : ℝ)) (γ := (63490287643007/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_6_16 half_5_16 half_7_15
  · have h := even_B_second_cross (u := 5) (t := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (90346112523/2500000000000 : ℝ)) (φ₂ := (240461645073/10000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/8 : ℝ)) (c := (5/8 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_15
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_8_16 : AdmissibleExponent 16 16 (43951241331849/5000000000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 6) (u := 5) (t := 8)
    (φ₁ := (378853729529/10000000000000 : ℝ)) (φ₂ := (307169479911/10000000000000 : ℝ)) (χ := (18421599757540141048125263/2500000000000000000000000 : ℝ)) (γ := (73686399030161/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_16 half_6_16 half_8_15
  · have h := even_A_second_cross (u := 6) (v := 8) (w := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (378853729529/10000000000000 : ℝ)) (φ₂ := (307169479911/10000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_15 half_8_15
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_17 : AdmissibleExponent 16 6 (15037408276659/5000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
    (φ := (638328580413/170638328580413 : ℝ)) half_4_16 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_17 : AdmissibleExponent 16 8 (2031916212879/500000000000 : ℝ) := by
  have h := admissible_eight_B_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
    (φ := (95959731523/5095959731523 : ℝ)) half_3_17 half_6_16
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_17 : AdmissibleExponent 16 10 (6473423781059/1250000000000 : ℝ) := by
  apply first_stage_admissible_source (s := 3) (φ := (7216880490683/247216880490683 : ℝ)) (χ := (1229753543163286/247216880490683 : ℝ))
    (by norm_num : 0 < (16 : ℕ)) half_4_17 (by norm_num) (by norm_num)
  · have h := first_A_cross_power (u := 4) (v := 5) (w := 6)
      (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
      (φ := (7216880490683/247216880490683 : ℝ)) (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
      (by norm_num) (by norm_num) half_5_16 half_6_16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_17 : AdmissibleExponent 16 12 (31706127028417/5000000000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 4) (u := 3) (t := 6)
    (φ₁ := (168510252477/5000000000000 : ℝ)) (φ₂ := (41269091037/5000000000000 : ℝ)) (χ := (134901346671237166880111307/25000000000000000000000000 : ℝ)) (γ := (10792107733699/2000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_17 half_4_17 half_6_16
  · have h := even_B_second_cross (u := 4) (t := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (168510252477/5000000000000 : ℝ)) (φ₂ := (41269091037/5000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_7_17 : AdmissibleExponent 16 14 (18864310449779/2500000000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 5) (u := 4) (t := 7)
    (φ₁ := (361383495347/10000000000000 : ℝ)) (φ₂ := (24045910061/1000000000000 : ℝ)) (χ := (507922489443022403737265507/80000000000000000000000000 : ℝ)) (γ := (3174515559019/500000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_6_17 half_5_17 half_7_16
  · have h := even_B_second_cross (u := 5) (t := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (361383495347/10000000000000 : ℝ)) (φ₂ := (24045910061/1000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/8 : ℝ)) (c := (5/8 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_8_17 : AdmissibleExponent 16 16 (87902460155459/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 6) (u := 5) (t := 8)
    (φ₁ := (189426236537/5000000000000 : ℝ)) (φ₂ := (153583578531/5000000000000 : ℝ)) (χ := (184216072525923827368624451/25000000000000000000000000 : ℝ)) (γ := (73686429010371/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_17 half_6_17 half_8_16
  · have h := even_A_second_cross (u := 6) (v := 8) (w := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (189426236537/5000000000000 : ℝ)) (φ₂ := (153583578531/5000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_16 half_8_16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_18 : AdmissibleExponent 16 6 (30074816048547/10000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
    (φ := (1877424287/501877424287 : ℝ)) half_4_17 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_18 : AdmissibleExponent 16 8 (40638322252049/10000000000000 : ℝ) := by
  have h := admissible_eight_B_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
    (φ := (163131097987/8663131097987 : ℝ)) half_3_18 half_6_17
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_18 : AdmissibleExponent 16 10 (51787387108523/10000000000000 : ℝ) := by
  apply first_stage_admissible_source (s := 3) (φ := (2405624257597/82405624257597 : ℝ)) (χ := (409917826531586/82405624257597 : ℝ))
    (by norm_num : 0 < (16 : ℕ)) half_4_18 (by norm_num) (by norm_num)
  · have h := first_A_cross_power (u := 4) (v := 5) (w := 6)
      (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
      (φ := (2405624257597/82405624257597 : ℝ)) (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
      (by norm_num) (by norm_num) half_5_17 half_6_17
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_18 : AdmissibleExponent 16 12 (63412249453709/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 4) (u := 3) (t := 6)
    (φ₁ := (1053188061/31250000000 : ℝ)) (φ₂ := (82536914593/10000000000000 : ℝ)) (χ := (1079210936689431855726287133/200000000000000000000000000 : ℝ)) (γ := (53960546834473/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_18 half_4_18 half_6_17
  · have h := even_B_second_cross (u := 4) (t := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (1053188061/31250000000 : ℝ)) (φ₂ := (82536914593/10000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_17
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_7_18 : AdmissibleExponent 16 14 (37728617427719/5000000000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 5) (u := 4) (t := 7)
    (φ₁ := (22586440771/625000000000 : ℝ)) (φ₂ := (240457919867/10000000000000 : ℝ)) (χ := (1015845153645143084922293823/160000000000000000000000000 : ℝ)) (γ := (31745161051413/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_6_18 half_5_18 half_7_17
  · have h := even_B_second_cross (u := 5) (t := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (22586440771/625000000000 : ℝ)) (φ₂ := (240457919867/10000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/8 : ℝ)) (c := (5/8 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_17
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_8_18 : AdmissibleExponent 16 16 (17580489942319/2000000000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 6) (u := 5) (t := 8)
    (φ₁ := (378851890011/10000000000000 : ℝ)) (φ₂ := (153583039569/5000000000000 : ℝ)) (χ := (2947457716949573377982196827/400000000000000000000000000 : ℝ)) (γ := (36843221461871/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_18 half_6_18 half_8_17
  · have h := even_A_second_cross (u := 6) (v := 8) (w := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (378851890011/10000000000000 : ℝ)) (φ₂ := (153583039569/5000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_17 half_8_17
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_19 : AdmissibleExponent 16 6 (7518703953591/2500000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
    (φ := (638322252049/170638322252049 : ℝ)) half_4_18 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_19 : AdmissibleExponent 16 8 (8127664264317/2000000000000 : ℝ) := by
  have h := admissible_eight_B_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
    (φ := (3262617824981/173262617824981 : ℝ)) half_3_19 half_6_18
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_19 : AdmissibleExponent 16 10 (51787385651767/10000000000000 : ℝ) := by
  apply first_stage_admissible_source (s := 3) (φ := (2886747676883/98886747676883 : ℝ)) (χ := (491901380040982/98886747676883 : ℝ))
    (by norm_num : 0 < (16 : ℕ)) half_4_19 (by norm_num) (by norm_num)
  · have h := first_A_cross_power (u := 4) (v := 5) (w := 6)
      (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
      (φ := (2886747676883/98886747676883 : ℝ)) (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
      (by norm_num) (by norm_num) half_5_18 half_6_18
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_19 : AdmissibleExponent 16 12 (31706123659029/5000000000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 4) (u := 3) (t := 6)
    (φ₁ := (13480801141/400000000000 : ℝ)) (φ₂ := (82536326473/10000000000000 : ℝ)) (χ := (107921101246985820546319819/20000000000000000000000000 : ℝ)) (γ := (53960550623493/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_19 half_4_19 half_6_18
  · have h := even_B_second_cross (u := 4) (t := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (13480801141/400000000000 : ℝ)) (φ₂ := (82536326473/10000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_18
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_7_19 : AdmissibleExponent 16 14 (75457231633781/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 5) (u := 4) (t := 7)
    (φ₁ := (180691423391/5000000000000 : ℝ)) (φ₂ := (48091474397/2000000000000 : ℝ)) (χ := (203169046947263689828699327/32000000000000000000000000 : ℝ)) (γ := (3174516358551/500000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_6_19 half_5_19 half_7_18
  · have h := even_B_second_cross (u := 5) (t := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (180691423391/5000000000000 : ℝ)) (φ₂ := (48091474397/2000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/8 : ℝ)) (c := (5/8 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_18
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_8_19 : AdmissibleExponent 16 16 (8790244486577/1000000000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 6) (u := 5) (t := 8)
    (φ₁ := (189425809729/5000000000000 : ℝ)) (φ₂ := (307165578961/10000000000000 : ℝ)) (χ := (589491595040670738136019017/80000000000000000000000000 : ℝ)) (γ := (73686449380091/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_19 half_6_19 half_8_18
  · have h := even_A_second_cross (u := 6) (v := 8) (w := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (189425809729/5000000000000 : ℝ)) (φ₂ := (307165578961/10000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_18 half_8_18
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_20 : AdmissibleExponent 16 6 (7518703926429/2500000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
    (φ := (127664264317/34127664264317 : ℝ)) half_4_19 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_20 : AdmissibleExponent 16 8 (10159580222473/2500000000000 : ℝ) := by
  have h := admissible_eight_B_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
    (φ := (1631307953313/86631307953313 : ℝ)) half_3_20 half_6_19
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_20 : AdmissibleExponent 16 10 (51787384975903/10000000000000 : ℝ) := by
  apply first_stage_admissible_source (s := 3) (φ := (1804216882753/61804216882753 : ℝ)) (χ := (307438359104858/61804216882753 : ℝ))
    (by norm_num : 0 < (16 : ℕ)) half_4_20 (by norm_num) (by norm_num)
  · have h := first_A_cross_power (u := 4) (v := 5) (w := 6)
      (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
      (φ := (1804216882753/61804216882753 : ℝ)) (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
      (by norm_num) (by norm_num) half_5_19 half_6_19
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_20 : AdmissibleExponent 16 12 (15853061581801/2500000000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 4) (u := 3) (t := 6)
    (φ₁ := (337019958467/10000000000000 : ℝ)) (φ₂ := (82536053591/10000000000000 : ℝ)) (χ := (53960552381548466084427267/10000000000000000000000000 : ℝ)) (γ := (53960552381549/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_20 half_4_20 half_6_19
  · have h := even_B_second_cross (u := 4) (t := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (337019958467/10000000000000 : ℝ)) (φ₂ := (82536053591/10000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_19
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_7_20 : AdmissibleExponent 16 14 (75457230139037/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 5) (u := 4) (t := 7)
    (φ₁ := (361382751409/10000000000000 : ℝ)) (φ₂ := (240457117771/10000000000000 : ℝ)) (χ := (5079226361810414102700157/800000000000000000000000 : ℝ)) (γ := (7936291190329/1250000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_6_20 half_5_20 half_7_19
  · have h := even_B_second_cross (u := 5) (t := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (361382751409/10000000000000 : ℝ)) (φ₂ := (240457117771/10000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/8 : ℝ)) (c := (5/8 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_19
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_8_20 : AdmissibleExponent 16 16 (43951221308703/5000000000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 6) (u := 5) (t := 8)
    (φ₁ := (189425746961/5000000000000 : ℝ)) (φ₂ := (307165346879/10000000000000 : ℝ)) (χ := (294745809503615114628715469/40000000000000000000000000 : ℝ)) (γ := (14737290475181/2000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_20 half_6_20 half_8_19
  · have h := even_A_second_cross (u := 6) (v := 8) (w := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (189425746961/5000000000000 : ℝ)) (φ₂ := (307165346879/10000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_19 half_8_19
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_21 : AdmissibleExponent 16 6 (30074815655307/10000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
    (φ := (159580222473/42659580222473 : ℝ)) half_4_20 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_21 : AdmissibleExponent 16 8 (10159580172401/2500000000000 : ℝ) := by
  have h := admissible_eight_B_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
    (φ := (326261501659/17326261501659 : ℝ)) half_3_21 half_6_20
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_21 : AdmissibleExponent 16 10 (51787384662331/10000000000000 : ℝ) := by
  apply first_stage_admissible_source (s := 3) (φ := (7216866760297/247216866760297 : ℝ)) (χ := (1229753430071090/247216866760297 : ℝ))
    (by norm_num : 0 < (16 : ℕ)) half_4_21 (by norm_num) (by norm_num)
  · have h := first_A_cross_power (u := 4) (v := 5) (w := 6)
      (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
      (φ := (7216866760297/247216866760297 : ℝ)) (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
      (by norm_num) (by norm_num) half_5_20 half_6_20
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_21 : AdmissibleExponent 16 12 (12682449173497/2000000000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 4) (u := 3) (t := 6)
    (φ₁ := (168509962981/5000000000000 : ℝ)) (φ₂ := (82535926979/10000000000000 : ℝ)) (χ := (539605531972483458568554477/100000000000000000000000000 : ℝ)) (γ := (13490138299313/2500000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_21 half_4_21 half_6_20
  · have h := even_B_second_cross (u := 4) (t := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (168509962981/5000000000000 : ℝ)) (φ₂ := (82535926979/10000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_20
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_7_21 : AdmissibleExponent 16 14 (3018289177821/400000000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 5) (u := 4) (t := 7)
    (φ₁ := (180691353579/5000000000000 : ℝ)) (φ₂ := (240456999819/10000000000000 : ℝ)) (χ := (507922644910043908020079169/80000000000000000000000000 : ℝ)) (γ := (15872582653439/2500000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_6_21 half_5_21 half_7_20
  · have h := even_B_second_cross (u := 5) (t := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (180691353579/5000000000000 : ℝ)) (φ₂ := (240456999819/10000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/8 : ℝ)) (c := (5/8 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_20
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_8_21 : AdmissibleExponent 16 16 (43951220787113/5000000000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 6) (u := 5) (t := 8)
    (φ₁ := (15154057427/400000000000 : ℝ)) (φ₂ := (76791309799/2500000000000 : ℝ)) (χ := (1473729075318967380778893061/200000000000000000000000000 : ℝ)) (γ := (73686453765949/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_21 half_6_21 half_8_20
  · have h := even_A_second_cross (u := 6) (v := 8) (w := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (15154057427/400000000000 : ℝ)) (φ₂ := (76791309799/2500000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_20 half_8_20
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_22 : AdmissibleExponent 16 6 (375935195399/125000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
    (φ := (159580172401/42659580172401 : ℝ)) half_4_21 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_22 : AdmissibleExponent 16 8 (20319160298339/5000000000000 : ℝ) := by
  have h := admissible_eight_B_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
    (φ := (652522920729/34652522920729 : ℝ)) half_3_22 half_6_21
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_22 : AdmissibleExponent 16 10 (51787384516847/10000000000000 : ℝ) := by
  apply first_stage_admissible_source (s := 3) (φ := (2886746561087/98886746561087 : ℝ)) (χ := (2459506854251414/494433732805435 : ℝ))
    (by norm_num : 0 < (16 : ℕ)) half_4_22 (by norm_num) (by norm_num)
  · have h := first_A_cross_power (u := 4) (v := 5) (w := 6)
      (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
      (φ := (2886746561087/98886746561087 : ℝ)) (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
      (by norm_num) (by norm_num) half_5_21 half_6_21
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_22 : AdmissibleExponent 16 12 (12682449130839/2000000000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 4) (u := 3) (t := 6)
    (φ₁ := (337019910881/10000000000000 : ℝ)) (φ₂ := (41267934117/5000000000000 : ℝ)) (χ := (107921107151422484346691001/20000000000000000000000000 : ℝ)) (γ := (1686267299241/312500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_22 half_4_22 half_6_21
  · have h := even_B_second_cross (u := 4) (t := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (337019910881/10000000000000 : ℝ)) (φ₂ := (41267934117/5000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_21
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_7_22 : AdmissibleExponent 16 14 (37728614561881/5000000000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 5) (u := 4) (t := 7)
    (φ₁ := (180691343313/5000000000000 : ℝ)) (φ₂ := (60114236273/2500000000000 : ℝ)) (χ := (253961324480103702999774933/40000000000000000000000000 : ℝ)) (γ := (31745165560013/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_6_22 half_5_22 half_7_21
  · have h := even_B_second_cross (u := 5) (t := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (180691343313/5000000000000 : ℝ)) (φ₂ := (60114236273/2500000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/8 : ℝ)) (c := (5/8 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_21
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_8_22 : AdmissibleExponent 16 16 (43951220545111/5000000000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 6) (u := 5) (t := 8)
    (φ₁ := (378851408649/10000000000000 : ℝ)) (φ₂ := (153582594617/5000000000000 : ℝ)) (χ := (1473729088218175450991554663/200000000000000000000000000 : ℝ)) (γ := (73686454410913/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_22 half_6_22 half_8_21
  · have h := even_A_second_cross (u := 6) (v := 8) (w := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (378851408649/10000000000000 : ℝ)) (φ₂ := (153582594617/5000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_21 half_8_21
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_23 : AdmissibleExponent 16 6 (30074815621069/10000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
    (φ := (319160298339/85319160298339 : ℝ)) half_4_22 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_23 : AdmissibleExponent 16 8 (10159580138391/2500000000000 : ℝ) := by
  have h := admissible_eight_B_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
    (φ := (3262614412057/173262614412057 : ℝ)) half_3_23 half_6_22
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_23 : AdmissibleExponent 16 10 (12946846112337/2500000000000 : ℝ) := by
  apply first_stage_admissible_source (s := 3) (φ := (14433732473633/494433732473633 : ℝ)) (χ := (2459506851518338/494433732473633 : ℝ))
    (by norm_num : 0 < (16 : ℕ)) half_4_23 (by norm_num) (by norm_num)
  · have h := first_A_cross_power (u := 4) (v := 5) (w := 6)
      (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
      (φ := (14433732473633/494433732473633 : ℝ)) (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
      (by norm_num) (by norm_num) half_5_22 half_6_22
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_23 : AdmissibleExponent 16 12 (63412245555237/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 4) (u := 3) (t := 6)
    (φ₁ := (337019903883/10000000000000 : ℝ)) (φ₂ := (41267920489/5000000000000 : ℝ)) (χ := (539605537513180867943075429/100000000000000000000000000 : ℝ)) (γ := (26980276875661/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_23 half_4_23 half_6_22
  · have h := even_B_second_cross (u := 4) (t := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (337019903883/10000000000000 : ℝ)) (φ₂ := (41267920489/5000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_22
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_7_23 : AdmissibleExponent 16 14 (75457228974477/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 5) (u := 4) (t := 7)
    (φ₁ := (3613826771/100000000000 : ℝ)) (φ₂ := (240456919701/10000000000000 : ℝ)) (χ := (507922650839253568328210089/80000000000000000000000000 : ℝ)) (γ := (1984072854841/312500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_6_23 half_5_23 half_7_22
  · have h := even_B_second_cross (u := 5) (t := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (3613826771/100000000000 : ℝ)) (φ₂ := (240456919701/10000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/8 : ℝ)) (c := (5/8 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_22
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_8_23 : AdmissibleExponent 16 16 (87902440865661/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 6) (u := 5) (t := 8)
    (φ₁ := (37885139611/1000000000000 : ℝ)) (φ₂ := (76791291513/2500000000000 : ℝ)) (χ := (736864547101668632214965027/100000000000000000000000000 : ℝ)) (γ := (73686454710167/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_23 half_6_23 half_8_22
  · have h := even_A_second_cross (u := 6) (v := 8) (w := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (37885139611/1000000000000 : ℝ)) (φ₂ := (76791291513/2500000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_22 half_8_22
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_24 : AdmissibleExponent 16 6 (6014963123207/2000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
    (φ := (159580138391/42659580138391 : ℝ)) half_4_23 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_24 : AdmissibleExponent 16 8 (20319160266781/5000000000000 : ℝ) := by
  have h := admissible_eight_B_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
    (φ := (3262614323167/173262614323167 : ℝ)) half_3_24 half_6_23
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_24 : AdmissibleExponent 16 10 (3236711526127/625000000000 : ℝ) := by
  apply first_stage_admissible_source (s := 3) (φ := (2886746463937/98886746463937 : ℝ)) (χ := (2459506850250346/494433732319685 : ℝ))
    (by norm_num : 0 < (16 : ℕ)) half_4_24 (by norm_num) (by norm_num)
  · have h := first_A_cross_power (u := 4) (v := 5) (w := 6)
      (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
      (φ := (2886746463937/98886746463937 : ℝ)) (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
      (by norm_num) (by norm_num) half_5_23 half_6_23
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_24 : AdmissibleExponent 16 12 (63412245509321/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 4) (u := 3) (t := 6)
    (φ₁ := (337019900637/10000000000000 : ℝ)) (φ₂ := (20633957083/2500000000000 : ℝ)) (χ := (1079211076655713183744966491/200000000000000000000000000 : ℝ)) (γ := (26980276916393/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_24 half_4_24 half_6_23
  · have h := even_B_second_cross (u := 4) (t := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (337019900637/10000000000000 : ℝ)) (φ₂ := (20633957083/2500000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_23
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_7_24 : AdmissibleExponent 16 14 (9432153613151/1250000000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 5) (u := 4) (t := 7)
    (φ₁ := (361382672681/10000000000000 : ℝ)) (φ₂ := (3005711349/125000000000 : ℝ)) (χ := (1015845303422066380377357739/160000000000000000000000000 : ℝ)) (γ := (1587258286597/250000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_6_24 half_5_24 half_7_23
  · have h := even_B_second_cross (u := 5) (t := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (361382672681/10000000000000 : ℝ)) (φ₂ := (3005711349/125000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/8 : ℝ)) (c := (5/8 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_23
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_8_24 : AdmissibleExponent 16 16 (87902440761471/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 6) (u := 5) (t := 8)
    (φ₁ := (378851390293/10000000000000 : ℝ)) (φ₂ := (307165155297/10000000000000 : ℝ)) (χ := (294745819395955997458404503/40000000000000000000000000 : ℝ)) (γ := (73686454848989/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_24 half_6_24 half_8_23
  · have h := even_A_second_cross (u := 6) (v := 8) (w := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (378851390293/10000000000000 : ℝ)) (φ₂ := (307165155297/10000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_23 half_8_23
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_25 : AdmissibleExponent 16 6 (30074815613699/10000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
    (φ := (319160266781/85319160266781 : ℝ)) half_4_24 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_25 : AdmissibleExponent 16 8 (1015958013107/250000000000 : ℝ) := by
  have h := admissible_eight_B_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
    (φ := (3262614281923/173262614281923 : ℝ)) half_3_25 half_6_24
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_25 : AdmissibleExponent 16 10 (51787384403501/10000000000000 : ℝ) := by
  apply first_stage_admissible_source (s := 3) (φ := (962248816551/32962248816551 : ℝ)) (χ := (163967123310798/32962248816551 : ℝ))
    (by norm_num : 0 < (16 : ℕ)) half_4_25 (by norm_num) (by norm_num)
  · have h := first_A_cross_power (u := 4) (v := 5) (w := 6)
      (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
      (φ := (962248816551/32962248816551 : ℝ)) (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
      (by norm_num) (by norm_num) half_5_24 half_6_24
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_25 : AdmissibleExponent 16 12 (63412245488019/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 4) (u := 3) (t := 6)
    (φ₁ := (337019899131/10000000000000 : ℝ)) (φ₂ := (16507164493/2000000000000 : ℝ)) (χ := (269802769352895347720143071/50000000000000000000000000 : ℝ)) (γ := (2698027693529/500000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_25 half_4_25 half_6_24
  · have h := even_B_second_cross (u := 4) (t := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (337019899131/10000000000000 : ℝ)) (φ₂ := (16507164493/2000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_24
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_7_25 : AdmissibleExponent 16 14 (75457228873073/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 5) (u := 4) (t := 7)
    (φ₁ := (36138267063/1000000000000 : ℝ)) (φ₂ := (120228451227/5000000000000 : ℝ)) (χ := (253961326057796173371038359/40000000000000000000000000 : ℝ)) (γ := (63490331514451/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_6_25 half_5_25 half_7_24
  · have h := even_B_second_cross (u := 5) (t := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (36138267063/1000000000000 : ℝ)) (φ₂ := (120228451227/5000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/8 : ℝ)) (c := (5/8 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_24
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_8_25 : AdmissibleExponent 16 16 (8790244071313/1000000000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 6) (u := 5) (t := 8)
    (φ₁ := (378851387593/10000000000000 : ℝ)) (φ₂ := (307165150307/10000000000000 : ℝ)) (χ := (29474581965366974746062473/4000000000000000000000000 : ℝ)) (γ := (36843227456709/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_25 half_6_25 half_8_24
  · have h := even_A_second_cross (u := 6) (v := 8) (w := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (378851387593/10000000000000 : ℝ)) (φ₂ := (307165150307/10000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_24 half_8_24
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_26 : AdmissibleExponent 16 6 (6014963122523/2000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
    (φ := (15958013107/4265958013107 : ℝ)) half_4_25 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_26 : AdmissibleExponent 16 8 (20319160259987/5000000000000 : ℝ) := by
  have h := admissible_eight_B_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
    (φ := (3262614262789/173262614262789 : ℝ)) half_3_26 half_6_25
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_26 : AdmissibleExponent 16 10 (51787384396759/10000000000000 : ℝ) := by
  apply first_stage_admissible_source (s := 3) (φ := (115469857721/3955469857721 : ℝ)) (χ := (2459506849389002/494433732215125 : ℝ))
    (by norm_num : 0 < (16 : ℕ)) half_4_26 (by norm_num) (by norm_num)
  · have h := first_A_cross_power (u := 4) (v := 5) (w := 6)
      (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
      (φ := (115469857721/3955469857721 : ℝ)) (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
      (by norm_num) (by norm_num) half_5_25 half_6_25
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_26 : AdmissibleExponent 16 12 (31706122739067/5000000000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 4) (u := 3) (t := 6)
    (φ₁ := (5265935913/156250000000 : ℝ)) (φ₂ := (82535819743/10000000000000 : ℝ)) (χ := (4316844311049269534791449/800000000000000000000000 : ℝ)) (γ := (53960553888119/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_26 half_4_26 half_6_25
  · have h := even_B_second_cross (u := 4) (t := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (5265935913/156250000000 : ℝ)) (φ₂ := (82535819743/10000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_25
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_7_26 : AdmissibleExponent 16 14 (943215360727/125000000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 5) (u := 4) (t := 7)
    (φ₁ := (361382669679/10000000000000 : ℝ)) (φ₂ := (120228449959/5000000000000 : ℝ)) (χ := (101584530460643403105329139/16000000000000000000000000 : ℝ)) (γ := (63490331537903/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_6_26 half_5_26 half_7_25
  · have h := even_B_second_cross (u := 5) (t := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (361382669679/10000000000000 : ℝ)) (φ₂ := (120228449959/5000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/8 : ℝ)) (c := (5/8 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_25
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_8_26 : AdmissibleExponent 16 16 (43951220345349/5000000000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 6) (u := 5) (t := 8)
    (φ₁ := (378851386341/10000000000000 : ℝ)) (φ₂ := (38395643499/1250000000000 : ℝ)) (χ := (294745819773174966905332313/40000000000000000000000000 : ℝ)) (γ := (36843227471647/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_26 half_6_26 half_8_25
  · have h := even_A_second_cross (u := 6) (v := 8) (w := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (378851386341/10000000000000 : ℝ)) (φ₂ := (38395643499/1250000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_25 half_8_25
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_27 : AdmissibleExponent 16 6 (30074815612113/10000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
    (φ := (319160259987/85319160259987 : ℝ)) half_4_26 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_27 : AdmissibleExponent 16 8 (40638320517977/10000000000000 : ℝ) := by
  have h := admissible_eight_B_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
    (φ := (47979621381/2547979621381 : ℝ)) half_3_27 half_6_26
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_27 : AdmissibleExponent 16 10 (1618355762301/312500000000 : ℝ) := by
  apply first_stage_admissible_source (s := 3) (φ := (225527065621/7725527065621 : ℝ)) (χ := (153719178078899/30902108262484 : ℝ))
    (by norm_num : 0 < (16 : ℕ)) half_4_27 (by norm_num) (by norm_num)
  · have h := first_A_cross_power (u := 4) (v := 5) (w := 6)
      (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
      (φ := (225527065621/7725527065621 : ℝ)) (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
      (by norm_num) (by norm_num) half_5_26 half_6_26
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_27 : AdmissibleExponent 16 12 (63412245473553/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 4) (u := 3) (t := 6)
    (φ₁ := (337019898107/10000000000000 : ℝ)) (φ₂ := (82535818479/10000000000000 : ℝ)) (χ := (269802769481358958956370743/50000000000000000000000000 : ℝ)) (γ := (26980276948137/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_27 half_4_27 half_6_26
  · have h := even_B_second_cross (u := 4) (t := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (337019898107/10000000000000 : ℝ)) (φ₂ := (82535818479/10000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_26
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_7_27 : AdmissibleExponent 16 14 (37728614425623/5000000000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 5) (u := 4) (t := 7)
    (φ₁ := (361382669237/10000000000000 : ℝ)) (φ₂ := (240456898741/10000000000000 : ℝ)) (χ := (253961326195194636939182839/40000000000000000000000000 : ℝ)) (γ := (63490331548801/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_6_27 half_5_27 half_7_26
  · have h := even_B_second_cross (u := 5) (t := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (361382669237/10000000000000 : ℝ)) (φ₂ := (240456898741/10000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/8 : ℝ)) (c := (5/8 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_26
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_8_27 : AdmissibleExponent 16 16 (10987805085037/1250000000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 6) (u := 5) (t := 8)
    (φ₁ := (2367821161/62500000000 : ℝ)) (φ₂ := (307165146917/10000000000000 : ℝ)) (χ := (1473729099143427581549592181/200000000000000000000000000 : ℝ)) (γ := (18421613739293/2500000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_27 half_6_27 half_8_26
  · have h := even_A_second_cross (u := 6) (v := 8) (w := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (2367821161/62500000000 : ℝ)) (φ₂ := (307165146917/10000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_26 half_8_26
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_28 : AdmissibleExponent 16 6 (30074815611879/10000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
    (φ := (638320517977/170638320517977 : ℝ)) half_4_27 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_28 : AdmissibleExponent 16 8 (812766410341/200000000000 : ℝ) := by
  have h := admissible_eight_B_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
    (φ := (652522849959/34652522849959 : ℝ)) half_3_28 half_6_27
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_28 : AdmissibleExponent 16 10 (51787384392181/10000000000000 : ℝ) := by
  apply first_stage_admissible_source (s := 3) (φ := (14433732192617/494433732192617 : ℝ)) (χ := (2459506849203634/494433732192617 : ℝ))
    (by norm_num : 0 < (16 : ℕ)) half_4_28 (by norm_num) (by norm_num)
  · have h := first_A_cross_power (u := 4) (v := 5) (w := 6)
      (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
      (φ := (14433732192617/494433732192617 : ℝ)) (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
      (by norm_num) (by norm_num) half_5_27 half_6_27
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_28 : AdmissibleExponent 16 12 (990816335491/156250000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 4) (u := 3) (t := 6)
    (φ₁ := (337019897957/10000000000000 : ℝ)) (φ₂ := (41267908947/5000000000000 : ℝ)) (χ := (134901384750079793536178513/25000000000000000000000000 : ℝ)) (γ := (26980276950019/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_28 half_4_28 half_6_27
  · have h := even_B_second_cross (u := 4) (t := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (337019897957/10000000000000 : ℝ)) (φ₂ := (41267908947/5000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_27
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_7_28 : AdmissibleExponent 16 14 (75457228848037/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 5) (u := 4) (t := 7)
    (φ₁ := (361382669033/10000000000000 : ℝ)) (φ₂ := (48091379639/2000000000000 : ℝ)) (χ := (31745165776920178545408141/5000000000000000000000000 : ℝ)) (γ := (63490331553841/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_6_28 half_5_28 half_7_27
  · have h := even_B_second_cross (u := 5) (t := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (361382669033/10000000000000 : ℝ)) (φ₂ := (48091379639/2000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/8 : ℝ)) (c := (5/8 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_27
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_8_28 : AdmissibleExponent 16 16 (21975610168867/2500000000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 6) (u := 5) (t := 8)
    (φ₁ := (37885138549/1000000000000 : ℝ)) (φ₂ := (307165146419/10000000000000 : ℝ)) (χ := (368432274818041277293163101/50000000000000000000000000 : ℝ)) (γ := (73686454963609/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_28 half_6_28 half_8_27
  · have h := even_A_second_cross (u := 6) (v := 8) (w := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (37885138549/1000000000000 : ℝ)) (φ₂ := (307165146419/10000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_27 half_8_27
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_29 : AdmissibleExponent 16 6 (30074815611771/10000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
    (φ := (12766410341/3412766410341 : ℝ)) half_4_28 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_29 : AdmissibleExponent 16 8 (2031916025831/500000000000 : ℝ) := by
  have h := admissible_eight_B_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
    (φ := (1631307123941/86631307123941 : ℝ)) half_3_29 half_6_28
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_29 : AdmissibleExponent 16 10 (12946846097877/2500000000000 : ℝ) := by
  apply first_stage_admissible_source (s := 3) (φ := (2405622031551/82405622031551 : ℝ)) (χ := (409917808196062/82405622031551 : ℝ))
    (by norm_num : 0 < (16 : ℕ)) half_4_29 (by norm_num) (by norm_num)
  · have h := first_A_cross_power (u := 4) (v := 5) (w := 6)
      (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
      (φ := (2405622031551/82405622031551 : ℝ)) (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
      (by norm_num) (by norm_num) half_5_28 half_6_28
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_29 : AdmissibleExponent 16 12 (63412245470439/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 4) (u := 3) (t := 6)
    (φ₁ := (337019897887/10000000000000 : ℝ)) (φ₂ := (41267908811/5000000000000 : ℝ)) (χ := (269802769508936649499141697/50000000000000000000000000 : ℝ)) (γ := (26980276950897/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_29 half_4_29 half_6_28
  · have h := even_B_second_cross (u := 4) (t := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (337019897887/10000000000000 : ℝ)) (φ₂ := (41267908811/5000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_28
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_7_29 : AdmissibleExponent 16 14 (75457228846551/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 5) (u := 4) (t := 7)
    (φ₁ := (361382668937/10000000000000 : ℝ)) (φ₂ := (120228448971/5000000000000 : ℝ)) (χ := (253961326224774836669843907/40000000000000000000000000 : ℝ)) (γ := (63490331556197/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_6_29 half_5_29 half_7_28
  · have h := even_B_second_cross (u := 5) (t := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (361382668937/10000000000000 : ℝ)) (φ₂ := (120228448971/5000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/8 : ℝ)) (c := (5/8 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_28
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_8_29 : AdmissibleExponent 16 16 (8790244067323/1000000000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 6) (u := 5) (t := 8)
    (φ₁ := (75770277073/2000000000000 : ℝ)) (φ₂ := (76791286547/2500000000000 : ℝ)) (χ := (736864549665876572108718647/100000000000000000000000000 : ℝ)) (γ := (73686454966591/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_29 half_6_29 half_8_28
  · have h := even_A_second_cross (u := 6) (v := 8) (w := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (75770277073/2000000000000 : ℝ)) (φ₂ := (76791286547/2500000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_28 half_8_28
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_30 : AdmissibleExponent 16 6 (30074815611721/10000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
    (φ := (31916025831/8531916025831 : ℝ)) half_4_29 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_30 : AdmissibleExponent 16 8 (40638320516421/10000000000000 : ℝ) := by
  have h := admissible_eight_B_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
    (φ := (3262614246997/173262614246997 : ℝ)) half_3_30 half_6_29
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_30 : AdmissibleExponent 16 10 (12946846097799/2500000000000 : ℝ) := by
  apply first_stage_admissible_source (s := 3) (φ := (14433732187771/494433732187771 : ℝ)) (χ := (2459506849163750/494433732187771 : ℝ))
    (by norm_num : 0 < (16 : ℕ)) half_4_30 (by norm_num) (by norm_num)
  · have h := first_A_cross_power (u := 4) (v := 5) (w := 6)
      (by simp [SupportedFirstDegree] : SupportedFirstDegree 16)
      (φ := (14433732187771/494433732187771 : ℝ)) (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
      (by norm_num) (by norm_num) half_5_29 half_6_29
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_30 : AdmissibleExponent 16 12 (31706122734989/5000000000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 4) (u := 3) (t := 6)
    (φ₁ := (67403979571/2000000000000 : ℝ)) (φ₂ := (10316977187/1250000000000 : ℝ)) (χ := (107921107805189414931424627/20000000000000000000000000 : ℝ)) (γ := (53960553902599/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_30 half_4_30 half_6_29
  · have h := even_B_second_cross (u := 4) (t := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (67403979571/2000000000000 : ℝ)) (φ₂ := (10316977187/1250000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_29
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_7_30 : AdmissibleExponent 16 14 (2358038401433/312500000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 5) (u := 4) (t := 7)
    (φ₁ := (180691334447/5000000000000 : ℝ)) (φ₂ := (9618275913/400000000000 : ℝ)) (χ := (101584530491613065413776763/16000000000000000000000000 : ℝ)) (γ := (63490331557261/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_6_30 half_5_30 half_7_29
  · have h := even_B_second_cross (u := 5) (t := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (180691334447/5000000000000 : ℝ)) (φ₂ := (9618275913/400000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/8 : ℝ)) (c := (5/8 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_29
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_8_30 : AdmissibleExponent 16 16 (87902440672189/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 16) (s := 6) (u := 5) (t := 8)
    (φ₁ := (378851385307/10000000000000 : ℝ)) (φ₂ := (307165146081/10000000000000 : ℝ)) (χ := (73686454967968347789024257/10000000000000000000000000 : ℝ)) (γ := (73686454967971/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_30 half_6_30 half_8_29
  · have h := even_A_second_cross (u := 6) (v := 8) (w := 8)
      8 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (378851385307/10000000000000 : ℝ)) (φ₂ := (307165146081/10000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_29 half_8_29
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

theorem degree16_half_3 : AdmissibleExponent 16 6 (30074815611721/10000000000000 : ℝ) := half_3_30

theorem source16_entry_3 : AdmissibleExponent 16 6 (Certificate.coefficientSource8[3]! : ℝ) := by
  apply admissibleExponent_mono degree16_half_3
  norm_num [Certificate.coefficientSource8,Certificate.Q]

#print axioms source16_entry_3

theorem degree16_half_4 : AdmissibleExponent 16 8 (40638320516421/10000000000000 : ℝ) := half_4_30

theorem source16_entry_4 : AdmissibleExponent 16 8 (Certificate.coefficientSource8[4]! : ℝ) := by
  apply admissibleExponent_mono degree16_half_4
  norm_num [Certificate.coefficientSource8,Certificate.Q]

#print axioms source16_entry_4

theorem degree16_half_5 : AdmissibleExponent 16 10 (12946846097799/2500000000000 : ℝ) := half_5_30

theorem source16_entry_5 : AdmissibleExponent 16 10 (Certificate.coefficientSource8[5]! : ℝ) := by
  apply admissibleExponent_mono degree16_half_5
  norm_num [Certificate.coefficientSource8,Certificate.Q]

#print axioms source16_entry_5

theorem degree16_half_6 : AdmissibleExponent 16 12 (31706122734989/5000000000000 : ℝ) := half_6_30

theorem source16_entry_6 : AdmissibleExponent 16 12 (Certificate.coefficientSource8[6]! : ℝ) := by
  apply admissibleExponent_mono degree16_half_6
  norm_num [Certificate.coefficientSource8,Certificate.Q]

#print axioms source16_entry_6

theorem degree16_half_7 : AdmissibleExponent 16 14 (2358038401433/312500000000 : ℝ) := half_7_30

theorem source16_entry_7 : AdmissibleExponent 16 14 (Certificate.coefficientSource8[7]! : ℝ) := by
  apply admissibleExponent_mono degree16_half_7
  norm_num [Certificate.coefficientSource8,Certificate.Q]

#print axioms source16_entry_7

theorem degree16_half_8 : AdmissibleExponent 16 16 (87902440672189/10000000000000 : ℝ) := half_8_30

theorem source16_entry_8 : AdmissibleExponent 16 16 (Certificate.coefficientSource8[8]! : ℝ) := by
  apply admissibleExponent_mono degree16_half_8
  norm_num [Certificate.coefficientSource8,Certificate.Q]

#print axioms source16_entry_8

end Waring.SeedCompletionEven16SecondSeeds
