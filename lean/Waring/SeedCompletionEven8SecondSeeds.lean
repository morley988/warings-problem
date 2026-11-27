import Waring.SeedCompletionEvenSecondHolder
import Waring.SeedCompletionTwoStageUpdate
import Waring.SeedCompletionFirstGeneralA
import Waring.SeedCompletionFirstBGeneral
import Waring.CertificateData

/-! # Unconditional degree-8 source seeds through moment 12

Thirty exact finite A/B rounds start with proved endpoint moments.
Every auxiliary estimate is a theorem about the literal source sums.
All parameter balances and upward roundings are checked in Lean.
No published seed estimate or limiting recurrence value is assumed.
-/
noncomputable section
namespace Waring.SeedCompletionEven8SecondSeeds
open SmoothMoments FirstStageTransport SeedCompletionSecondScales
open SeedCompletionFirstGeneralA SeedCompletionSourceBounds

private theorem half_2_00 : AdmissibleExponent 8 4 2 :=
  FourthMomentSeed.admissibleExponent_four (by norm_num)

private theorem half_3_00 : AdmissibleExponent 8 6 (13/4 : ℝ) := by
  have h := endpoint_admissible (s := 1) (by norm_num : 0 < (8 : ℕ))
    half_2_00 (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_00 : AdmissibleExponent 8 8 (147/32 : ℝ) := by
  have h := endpoint_admissible (s := 2) (by norm_num : 0 < (8 : ℕ))
    half_3_00 (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_00 : AdmissibleExponent 8 10 (1541/256 : ℝ) := by
  have h := endpoint_admissible (s := 3) (by norm_num : 0 < (8 : ℕ))
    half_4_00 (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_6_00 : AdmissibleExponent 8 12 (15395/2048 : ℝ) := by
  have h := endpoint_admissible (s := 4) (by norm_num : 0 < (8 : ℕ))
    half_5_00 (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_3_01 : AdmissibleExponent 8 6 (31237785016287/10000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 8)
    (φ := (19/307 : ℝ)) half_4_00 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_01 : AdmissibleExponent 8 8 (43739268495751/10000000000000 : ℝ) := by
  have h := admissible_eight_A_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 8)
    (φ := (5715339983713/65715339983713 : ℝ)) half_3_01 half_4_00
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_01 : AdmissibleExponent 8 10 (14336367473061/2500000000000 : ℝ) := by
  apply two_stage_admissible (k := 8) (s := 3) (u := 2) (t := 5)
    (φ₁ := (124314969903/1250000000000 : ℝ)) (φ₂ := (408703655513/5000000000000 : ℝ)) (χ := (646078385097589/163840000000000 : ℝ)) (γ := (1971674759209/500000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_4_01 half_3_01 half_5_00
  · have h := even_B_second_cross (u := 3) (t := 6)
      4 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (124314969903/1250000000000 : ℝ)) (φ₂ := (408703655513/5000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_00
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_01 : AdmissibleExponent 8 12 (71771997565049/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 8) (s := 4) (u := 3) (t := 6)
    (φ₁ := (1037762615511/10000000000000 : ℝ)) (φ₂ := (389240674753/5000000000000 : ℝ)) (χ := (493092932927147578361951551/100000000000000000000000000 : ℝ)) (γ := (9861858658543/2000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_01 half_4_01 half_6_00
  · have h := even_A_second_cross (u := 4) (v := 5) (w := 6)
      4 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (1037762615511/10000000000000 : ℝ)) (φ₂ := (389240674753/5000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_5_01 half_6_00
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_02 : AdmissibleExponent 8 6 (30797801936319/10000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 8)
    (φ := (1246422831917/31246422831917 : ℝ)) half_4_01 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_02 : AdmissibleExponent 8 8 (42837964781089/10000000000000 : ℝ) := by
  have h := admissible_eight_A_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 8)
    (φ := (18026597741977/258026597741977 : ℝ)) half_3_02 half_4_01
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_02 : AdmissibleExponent 8 10 (14011442785383/2500000000000 : ℝ) := by
  apply two_stage_admissible (k := 8) (s := 3) (u := 2) (t := 5)
    (φ₁ := (107899309791/1250000000000 : ℝ)) (φ₂ := (266546546517/5000000000000 : ℝ)) (χ := (409882748741624177087736631/100000000000000000000000000 : ℝ)) (γ := (40988274874163/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_4_02 half_3_02 half_5_01
  · have h := even_B_second_cross (u := 3) (t := 6)
      4 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (107899309791/1250000000000 : ℝ)) (φ₂ := (266546546517/5000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_01
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_02 : AdmissibleExponent 8 12 (8764278443821/1250000000000 : ℝ) := by
  apply two_stage_admissible (k := 8) (s := 4) (u := 3) (t := 6)
    (φ₁ := (925612054789/10000000000000 : ℝ)) (φ₂ := (339658578387/5000000000000 : ℝ)) (χ := (2006512298009285770136669381/400000000000000000000000000 : ℝ)) (γ := (50162807450233/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_02 half_4_02 half_6_01
  · have h := even_A_second_cross (u := 4) (v := 5) (w := 6)
      4 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (925612054789/10000000000000 : ℝ)) (φ₂ := (339658578387/5000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_5_02 half_6_01
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_03 : AdmissibleExponent 8 6 (382642252789/125000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 8)
    (φ := (315329420121/10315329420121 : ℝ)) half_4_02 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_03 : AdmissibleExponent 8 8 (42455525641839/10000000000000 : ℝ) := by
  have h := admissible_eight_A_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 8)
    (φ := (16068373450787/256068373450787 : ℝ)) half_3_03 half_4_02
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_03 : AdmissibleExponent 8 10 (55440727609347/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 8) (s := 3) (u := 2) (t := 5)
    (φ₁ := (397555435059/5000000000000 : ℝ)) (φ₂ := (189615600333/5000000000000 : ℝ)) (χ := (204248106293370456739403/48828125000000000000000 : ℝ)) (γ := (41830012168883/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_4_03 half_3_03 half_5_02
  · have h := even_B_second_cross (u := 3) (t := 6)
      4 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (397555435059/5000000000000 : ℝ)) (φ₂ := (189615600333/5000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_02
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_03 : AdmissibleExponent 8 12 (34653365385601/5000000000000 : ℝ) := by
  apply two_stage_admissible (k := 8) (s := 4) (u := 3) (t := 6)
    (φ₁ := (867609131487/10000000000000 : ℝ)) (φ₂ := (155810305241/2500000000000 : ℝ)) (χ := (1013520388114623179795419419/200000000000000000000000000 : ℝ)) (γ := (12669004851433/2500000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_03 half_4_03 half_6_02
  · have h := even_A_second_cross (u := 4) (v := 5) (w := 6)
      4 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (867609131487/10000000000000 : ℝ)) (φ₂ := (155810305241/2500000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_5_03 half_6_02
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_04 : AdmissibleExponent 8 6 (30531179856433/10000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 8)
    (φ := (2455525641839/92455525641839 : ℝ)) half_4_03 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_04 : AdmissibleExponent 8 8 (330397819061/78125000000 : ℝ) := by
  have h := admissible_eight_A_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 8)
    (φ := (1016123833319/17016123833319 : ℝ)) half_3_04 half_4_03
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_04 : AdmissibleExponent 8 10 (27579147929443/5000000000000 : ℝ) := by
  apply two_stage_admissible (k := 8) (s := 3) (u := 2) (t := 5)
    (φ₁ := (152078761027/2000000000000 : ℝ)) (φ₂ := (299277281193/10000000000000 : ℝ)) (χ := (52840499561431134465104609/12500000000000000000000000 : ℝ)) (γ := (42272399649147/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_4_04 half_3_04 half_5_03
  · have h := even_B_second_cross (u := 3) (t := 6)
      4 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (152078761027/2000000000000 : ℝ)) (φ₂ := (299277281193/10000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_03
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_04 : AdmissibleExponent 8 12 (68916740035511/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 8) (s := 4) (u := 3) (t := 6)
    (φ₁ := (419079097083/5000000000000 : ℝ)) (φ₂ := (593184545447/10000000000000 : ℝ)) (χ := (1019274355530626280427236469/200000000000000000000000000 : ℝ)) (γ := (50963717776533/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_04 half_4_04 half_6_03
  · have h := even_A_second_cross (u := 4) (v := 5) (w := 6)
      4 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (419079097083/5000000000000 : ℝ)) (φ₂ := (593184545447/10000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_5_04 half_6_03
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_05 : AdmissibleExponent 8 6 (30496456383567/10000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 8)
    (φ := (5965939687/240340939687 : ℝ)) half_4_04 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_05 : AdmissibleExponent 8 8 (21109820786233/5000000000000 : ℝ) := by
  have h := admissible_eight_A_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 8)
    (φ := (3721734246289/63721734246289 : ℝ)) half_3_05 half_4_04
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_05 : AdmissibleExponent 8 10 (55027056040077/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 8) (s := 3) (u := 2) (t := 5)
    (φ₁ := (371544181217/5000000000000 : ℝ)) (φ₂ := (64760423823/2500000000000 : ℝ)) (χ := (424977379822107813140046007/100000000000000000000000000 : ℝ)) (γ := (42497737982211/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_4_05 half_3_05 half_5_04
  · have h := even_B_second_cross (u := 3) (t := 6)
      4 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (371544181217/5000000000000 : ℝ)) (φ₂ := (64760423823/2500000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_04
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_05 : AdmissibleExponent 8 12 (536957037281/78125000000 : ℝ) := by
  apply two_stage_admissible (k := 8) (s := 4) (u := 3) (t := 6)
    (φ₁ := (82348283341/1000000000000 : ℝ)) (φ₂ := (115540399049/2000000000000 : ℝ)) (χ := (81787538575326903709344777/16000000000000000000000000 : ℝ)) (γ := (25558605804791/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_05 half_4_05 half_6_04
  · have h := even_A_second_cross (u := 4) (v := 5) (w := 6)
      4 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (82348283341/1000000000000 : ℝ)) (φ₂ := (115540399049/2000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_5_05 half_6_04
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_06 : AdmissibleExponent 8 6 (6096276304467/2000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 8)
    (φ := (1109820786233/46109820786233 : ℝ)) half_4_05 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_06 : AdmissibleExponent 8 8 (42188694247417/10000000000000 : ℝ) := by
  have h := admissible_eight_A_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 8)
    (φ := (7366699314029/127366699314029 : ℝ)) half_3_06 half_4_05
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_06 : AdmissibleExponent 8 10 (27483244517777/5000000000000 : ℝ) := by
  apply two_stage_admissible (k := 8) (s := 3) (u := 2) (t := 5)
    (φ₁ := (183661654421/2500000000000 : ℝ)) (φ₂ := (239302849859/10000000000000 : ℝ)) (χ := (6657722737194125124529417/1562500000000000000000000 : ℝ)) (γ := (42609425518043/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_4_06 half_3_06 half_5_05
  · have h := even_B_second_cross (u := 3) (t := 6)
      4 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (183661654421/2500000000000 : ℝ)) (φ₂ := (239302849859/10000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_05
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_06 : AdmissibleExponent 8 12 (68642584612887/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 8) (s := 4) (u := 3) (t := 6)
    (φ₁ := (408151118867/5000000000000 : ℝ)) (φ₂ := (569968141209/10000000000000 : ℝ)) (χ := (511960530083416092562062833/100000000000000000000000000 : ℝ)) (γ := (25598026504171/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_06 half_4_06 half_6_05
  · have h := even_A_second_cross (u := 4) (v := 5) (w := 6)
      4 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (408151118867/5000000000000 : ℝ)) (φ₂ := (569968141209/10000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_5_06 half_6_05
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_07 : AdmissibleExponent 8 6 (15237414605477/5000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 8)
    (φ := (243188249713/10243188249713 : ℝ)) half_4_06 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_07 : AdmissibleExponent 8 8 (8435048511829/2000000000000 : ℝ) := by
  have h := admissible_eight_A_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 8)
    (φ := (977784393229/16977784393229 : ℝ)) half_3_07 half_4_06
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_07 : AdmissibleExponent 8 10 (1716835434379/312500000000 : ℝ) := by
  apply two_stage_admissible (k := 8) (s := 3) (u := 2) (t := 5)
    (φ₁ := (730603849953/10000000000000 : ℝ)) (φ₂ := (114906220897/5000000000000 : ℝ)) (χ := (853271249136741385952056411/200000000000000000000000000 : ℝ)) (γ := (21331781228419/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_4_07 half_3_07 half_5_06
  · have h := even_B_second_cross (u := 3) (t := 6)
      4 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (730603849953/10000000000000 : ℝ)) (φ₂ := (114906220897/5000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_06
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_07 : AdmissibleExponent 8 12 (13720304826441/2000000000000 : ℝ) := by
  apply two_stage_admissible (k := 8) (s := 4) (u := 3) (t := 6)
    (φ₁ := (203211679847/2500000000000 : ℝ)) (φ₂ := (566196609409/10000000000000 : ℝ)) (χ := (2049414537747224364566821029/400000000000000000000000000 : ℝ)) (γ := (51235363443681/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_07 half_4_07 half_6_06
  · have h := even_A_second_cross (u := 4) (v := 5) (w := 6)
      4 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (203211679847/2500000000000 : ℝ)) (φ₂ := (566196609409/10000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_5_07 half_6_06
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_08 : AdmissibleExponent 8 6 (3047197978519/1000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 8)
    (φ := (435048511829/18435048511829 : ℝ)) half_4_07 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_08 : AdmissibleExponent 8 8 (5271174088267/1250000000000 : ℝ) := by
  have h := admissible_eight_A_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 8)
    (φ := (195170780489/3395170780489 : ℝ)) half_3_08 half_4_07
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_08 : AdmissibleExponent 8 10 (27463048355541/5000000000000 : ℝ) := by
  apply two_stage_admissible (k := 8) (s := 3) (u := 2) (t := 5)
    (φ₁ := (182174183957/2500000000000 : ℝ)) (φ₂ := (225321765133/10000000000000 : ℝ)) (χ := (170757364607706783903290199/40000000000000000000000000 : ℝ)) (γ := (42689341151929/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_4_08 half_3_08 half_5_07
  · have h := even_B_second_cross (u := 3) (t := 6)
      4 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (182174183957/2500000000000 : ℝ)) (φ₂ := (225321765133/10000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_07
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_08 : AdmissibleExponent 8 12 (68582526757543/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 8) (s := 4) (u := 3) (t := 6)
    (φ₁ := (811207767613/10000000000000 : ℝ)) (φ₂ := (112878358319/2000000000000 : ℝ)) (χ := (256272551612898883978177531/50000000000000000000000000 : ℝ)) (γ := (2562725516129/500000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_08 half_4_08 half_6_07
  · have h := even_A_second_cross (u := 4) (v := 5) (w := 6)
      4 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (811207767613/10000000000000 : ℝ)) (φ₂ := (112878358319/2000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_5_08 half_6_07
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_09 : AdmissibleExponent 8 6 (30470740371059/10000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 8)
    (φ := (271174088267/11521174088267 : ℝ)) half_4_08 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_09 : AdmissibleExponent 8 8 (21083424091637/5000000000000 : ℝ) := by
  have h := admissible_eight_A_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 8)
    (φ := (3656304158543/63656304158543 : ℝ)) half_3_09 half_4_08
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_09 : AdmissibleExponent 8 10 (54920375199299/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 8) (s := 3) (u := 2) (t := 5)
    (φ₁ := (727807989501/10000000000000 : ℝ)) (φ₂ := (223223797477/10000000000000 : ℝ)) (χ := (427014439754638690284662473/100000000000000000000000000 : ℝ)) (γ := (21350721987733/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_4_09 half_3_09 half_5_08
  · have h := even_B_second_cross (u := 3) (t := 6)
      4 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (727807989501/10000000000000 : ℝ)) (φ₂ := (223223797477/10000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_08
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_09 : AdmissibleExponent 8 12 (17143452012277/2500000000000 : ℝ) := by
  apply two_stage_admissible (k := 8) (s := 4) (u := 3) (t := 6)
    (φ₁ := (1266312409/15625000000 : ℝ)) (φ₂ := (112708192983/2000000000000 : ℝ)) (χ := (82021864201629622931034353/16000000000000000000000000 : ℝ)) (γ := (51263665126021/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_09 half_4_09 half_6_08
  · have h := even_A_second_cross (u := 4) (v := 5) (w := 6)
      4 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (1266312409/15625000000 : ℝ)) (φ₂ := (112708192983/2000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_5_09 half_6_08
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_10 : AdmissibleExponent 8 6 (30470201211387/10000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 8)
    (φ := (361141363879/15361141363879 : ℝ)) half_4_09 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_10 : AdmissibleExponent 8 8 (42165741283459/10000000000000 : ℝ) := by
  have h := admissible_eight_A_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 8)
    (φ := (7309869852137/127309869852137 : ℝ)) half_3_10 half_4_09
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_10 : AdmissibleExponent 8 10 (2745889864483/500000000000 : ℝ) := by
  apply two_stage_admissible (k := 8) (s := 3) (u := 2) (t := 5)
    (φ₁ := (181849473173/2500000000000 : ℝ)) (φ₂ := (222253699397/10000000000000 : ℝ)) (χ := (213535310763852276175923347/50000000000000000000000000 : ℝ)) (γ := (21353531076387/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_4_10 half_3_10 half_5_09
  · have h := even_B_second_cross (u := 3) (t := 6)
      4 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (181849473173/2500000000000 : ℝ)) (φ₂ := (222253699397/10000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_09
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_10 : AdmissibleExponent 8 12 (68569834085481/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 8) (s := 4) (u := 3) (t := 6)
    (φ₁ := (8100839303/100000000000 : ℝ)) (φ₂ := (8799135219/156250000000 : ℝ)) (χ := (128169945761113785511466547/25000000000000000000000000 : ℝ)) (γ := (25633989152223/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_10 half_4_10 half_6_09
  · have h := even_A_second_cross (u := 4) (v := 5) (w := 6)
      4 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (8100839303/100000000000 : ℝ)) (φ₂ := (8799135219/156250000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_5_10 half_6_09
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_11 : AdmissibleExponent 8 6 (30469966660779/10000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 8)
    (φ := (721913761153/30721913761153 : ℝ)) half_4_10 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_11 : AdmissibleExponent 8 8 (105413149371/25000000000 : ℝ) := by
  have h := admissible_eight_A_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 8)
    (φ := (14617357207261/254617357207261 : ℝ)) half_3_11 half_4_10
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_11 : AdmissibleExponent 8 10 (13729160146239/2500000000000 : ℝ) := by
  apply two_stage_admissible (k := 8) (s := 3) (u := 2) (t := 5)
    (φ₁ := (363605091281/5000000000000 : ℝ)) (φ₂ := (221808879469/10000000000000 : ℝ)) (χ := (854192926885215528704528089/200000000000000000000000000 : ℝ)) (γ := (21354823172131/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_4_11 half_3_11 half_5_10
  · have h := even_B_second_cross (u := 3) (t := 6)
      4 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (363605091281/5000000000000 : ℝ)) (φ₂ := (221808879469/10000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_10
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_11 : AdmissibleExponent 8 12 (68568033306333/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 8) (s := 4) (u := 3) (t := 6)
    (φ₁ := (16198405659/200000000000 : ℝ)) (φ₂ := (140740460081/2500000000000 : ℝ)) (χ := (1025399729497934958690341659/200000000000000000000000000 : ℝ)) (γ := (51269986474897/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_11 half_4_11 half_6_10
  · have h := even_A_second_cross (u := 4) (v := 5) (w := 6)
      4 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (16198405659/200000000000 : ℝ)) (φ₂ := (140740460081/2500000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_5_11 half_6_10
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_12 : AdmissibleExponent 8 6 (15234932311189/5000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 8)
    (φ := (5413149371/230413149371 : ℝ)) half_4_11 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_12 : AdmissibleExponent 8 8 (21082525131157/5000000000000 : ℝ) := by
  have h := admissible_eight_A_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 8)
    (φ := (1827040094461/31827040094461 : ℝ)) half_3_12 half_4_11
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_12 : AdmissibleExponent 8 10 (429032214213/78125000000 : ℝ) := by
  apply two_stage_admissible (k := 8) (s := 3) (u := 2) (t := 5)
    (φ₁ := (727124834583/10000000000000 : ℝ)) (φ₂ := (221606325293/10000000000000 : ℝ)) (χ := (213554130525719123423426323/50000000000000000000000000 : ℝ)) (γ := (8542165221029/2000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_4_12 half_3_12 half_5_11
  · have h := even_B_second_cross (u := 3) (t := 6)
      4 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (727124834583/10000000000000 : ℝ)) (φ₂ := (221606325293/10000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_11
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_12 : AdmissibleExponent 8 12 (2142725666711/312500000000 : ℝ) := by
  apply two_stage_admissible (k := 8) (s := 4) (u := 3) (t := 6)
    (φ₁ := (6326918763/78125000000 : ℝ)) (φ₂ := (562878179471/10000000000000 : ℝ)) (χ := (410167300058852628508200553/80000000000000000000000000 : ℝ)) (γ := (51270912507357/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_12 half_4_12 half_6_11
  · have h := even_A_second_cross (u := 4) (v := 5) (w := 6)
      4 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (6326918763/78125000000 : ℝ)) (φ₂ := (562878179471/10000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_5_12 half_6_11
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_13 : AdmissibleExponent 8 6 (6093964046291/2000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 8)
    (φ := (1082525131157/46082525131157 : ℝ)) half_4_12 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_13 : AdmissibleExponent 8 8 (42164959127189/10000000000000 : ℝ) := by
  have h := admissible_eight_A_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 8)
    (φ := (2435978310187/42435978310187 : ℝ)) half_3_13 half_4_12
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_13 : AdmissibleExponent 8 10 (54915892902979/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 8) (s := 3) (u := 2) (t := 5)
    (φ₁ := (727086243949/10000000000000 : ℝ)) (φ₂ := (110757310973/5000000000000 : ℝ)) (χ := (5338920170029438344655731/1250000000000000000000000 : ℝ)) (γ := (10677840340059/2500000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_4_13 half_3_13 half_5_12
  · have h := even_B_second_cross (u := 3) (t := 6)
      4 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (727086243949/10000000000000 : ℝ)) (φ₂ := (110757310973/5000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_13 : AdmissibleExponent 8 12 (6856685676591/1000000000000 : ℝ) := by
  apply two_stage_admissible (k := 8) (s := 4) (u := 3) (t := 6)
    (φ₁ := (404905863509/5000000000000 : ℝ)) (φ₂ := (28142007281/500000000000 : ℝ)) (χ := (102542672346233224226755351/20000000000000000000000000 : ℝ)) (γ := (51271336173119/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_13 half_4_13 half_6_12
  · have h := even_A_second_cross (u := 4) (v := 5) (w := 6)
      4 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (404905863509/5000000000000 : ℝ)) (φ₂ := (28142007281/500000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_5_13 half_6_12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_14 : AdmissibleExponent 8 6 (15234900459751/5000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 8)
    (φ := (2164959127189/92164959127189 : ℝ)) half_4_13 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_14 : AdmissibleExponent 8 8 (21082459739751/5000000000000 : ℝ) := by
  have h := admissible_eight_A_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 8)
    (φ := (14615673703559/254615673703559 : ℝ)) half_3_14 half_4_13
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_14 : AdmissibleExponent 8 10 (54915790428603/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 8) (s := 3) (u := 2) (t := 5)
    (φ₁ := (727068876623/10000000000000 : ℝ)) (φ₂ := (221473306583/10000000000000 : ℝ)) (χ := (42711602941118531806234627/10000000000000000000000000 : ℝ)) (γ := (42711602941121/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_4_14 half_3_14 half_5_13
  · have h := even_B_second_cross (u := 3) (t := 6)
      4 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (727068876623/10000000000000 : ℝ)) (φ₂ := (221473306583/10000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_13
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_14 : AdmissibleExponent 8 12 (274266774689/40000000000 : ℝ) := by
  apply two_stage_admissible (k := 8) (s := 4) (u := 3) (t := 6)
    (φ₁ := (404898220281/5000000000000 : ℝ)) (φ₂ := (3517643437/62500000000 : ℝ)) (χ := (256357643689594677405802261/50000000000000000000000000 : ℝ)) (γ := (51271528737921/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_14 half_4_14 half_6_13
  · have h := even_A_second_cross (u := 4) (v := 5) (w := 6)
      4 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (404898220281/5000000000000 : ℝ)) (φ₂ := (3517643437/62500000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_5_14 half_6_13
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_15 : AdmissibleExponent 8 6 (15234896258981/5000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 8)
    (φ := (1082459739751/46082459739751 : ℝ)) half_4_14 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_15 : AdmissibleExponent 8 8 (42164902231033/10000000000000 : ℝ) := by
  have h := admissible_eight_A_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 8)
    (φ := (2435931394443/42435931394443 : ℝ)) half_3_15 half_4_14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_15 : AdmissibleExponent 8 10 (27457872490073/5000000000000 : ℝ) := by
  apply two_stage_admissible (k := 8) (s := 3) (u := 2) (t := 5)
    (φ₁ := (72706109177/1000000000000 : ℝ)) (φ₂ := (221454769653/10000000000000 : ℝ)) (χ := (3416936919637715312077553/800000000000000000000000 : ℝ)) (γ := (2669481968467/625000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_4_15 half_3_15 half_5_14
  · have h := even_B_second_cross (u := 3) (t := 6)
      4 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (72706109177/1000000000000 : ℝ)) (φ₂ := (221454769653/10000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_14
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_15 : AdmissibleExponent 8 12 (17141655234889/2500000000000 : ℝ) := by
  apply two_stage_admissible (k := 8) (s := 4) (u := 3) (t := 6)
    (φ₁ := (809789572391/10000000000000 : ℝ)) (φ₂ := (562815211667/10000000000000 : ℝ)) (χ := (512716157837988814517096141/100000000000000000000000000 : ℝ)) (γ := (51271615783799/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_15 half_4_15 half_6_14
  · have h := even_A_second_cross (u := 4) (v := 5) (w := 6)
      4 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (809789572391/10000000000000 : ℝ)) (φ₂ := (562815211667/10000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_5_15 half_6_14
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_16 : AdmissibleExponent 8 6 (1218791554517/400000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 8)
    (φ := (240544692337/10240544692337 : ℝ)) half_4_15 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_16 : AdmissibleExponent 8 8 (21082447363597/5000000000000 : ℝ) := by
  have h := admissible_eight_A_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 8)
    (φ := (14615551241399/254615551241399 : ℝ)) half_3_16 half_4_15
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_16 : AdmissibleExponent 8 10 (27457862432147/5000000000000 : ℝ) := by
  apply two_stage_admissible (k := 8) (s := 3) (u := 2) (t := 5)
    (φ₁ := (181764403539/2500000000000 : ℝ)) (φ₂ := (221446482187/10000000000000 : ℝ)) (χ := (213558800454495853649089073/50000000000000000000000000 : ℝ)) (γ := (42711760090901/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_4_16 half_3_16 half_5_15
  · have h := even_B_second_cross (u := 3) (t := 6)
      4 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (181764403539/2500000000000 : ℝ)) (φ₂ := (221446482187/10000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_15
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_16 : AdmissibleExponent 8 12 (4285411787017/625000000000 : ℝ) := by
  apply two_stage_admissible (k := 8) (s := 4) (u := 3) (t := 6)
    (φ₁ := (809786498061/10000000000000 : ℝ)) (φ₂ := (562811743187/10000000000000 : ℝ)) (χ := (4005598042926228768241399/781250000000000000000000 : ℝ)) (γ := (51271654949459/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_16 half_4_16 half_6_15
  · have h := even_A_second_cross (u := 4) (v := 5) (w := 6)
      4 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (809786498061/10000000000000 : ℝ)) (φ₂ := (562811743187/10000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_5_16 half_6_15
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_17 : AdmissibleExponent 8 6 (30469787272823/10000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 8)
    (φ := (1082447363597/46082447363597 : ℝ)) half_4_16 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_17 : AdmissibleExponent 8 8 (21082445731347/5000000000000 : ℝ) := by
  have h := admissible_eight_A_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 8)
    (φ := (1461553509029/25461553509029 : ℝ)) half_3_17 half_4_16
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_17 : AdmissibleExponent 8 10 (10983143195359/2000000000000 : ℝ) := by
  apply two_stage_admissible (k := 8) (s := 3) (u := 2) (t := 5)
    (φ₁ := (363528032619/5000000000000 : ℝ)) (φ₂ := (22144278837/1000000000000 : ℝ)) (χ := (6673715902301395605249083/1562500000000000000000000 : ℝ)) (γ := (10677945443683/2500000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_4_17 half_3_17 half_5_16
  · have h := even_B_second_cross (u := 3) (t := 6)
      4 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (363528032619/5000000000000 : ℝ)) (φ₂ := (22144278837/1000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_17 : AdmissibleExponent 8 12 (274266296961/40000000000 : ℝ) := by
  apply two_stage_admissible (k := 8) (s := 4) (u := 3) (t := 6)
    (φ₁ := (809785126359/10000000000000 : ℝ)) (φ₂ := (562810193823/10000000000000 : ℝ)) (χ := (512716725022354383423703279/100000000000000000000000000 : ℝ)) (γ := (51271672502237/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_17 half_4_17 half_6_16
  · have h := even_A_second_cross (u := 4) (v := 5) (w := 6)
      4 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (809785126359/10000000000000 : ℝ)) (φ₂ := (562810193823/10000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_5_17 half_6_16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_18 : AdmissibleExponent 8 6 (30469786581059/10000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 8)
    (φ := (1082445731347/46082445731347 : ℝ)) half_4_17 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_18 : AdmissibleExponent 8 8 (21082445021247/5000000000000 : ℝ) := by
  have h := admissible_eight_A_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 8)
    (φ := (7307764031923/127307764031923 : ℝ)) half_3_18 half_4_17
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_18 : AdmissibleExponent 8 10 (10983142411273/2000000000000 : ℝ) := by
  apply two_stage_admissible (k := 8) (s := 3) (u := 2) (t := 5)
    (φ₁ := (181763844281/2500000000000 : ℝ)) (φ₂ := (55360286591/2500000000000 : ℝ)) (χ := (106779478557997627515001/25000000000000000000000 : ℝ)) (γ := (53389739279/12500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_4_18 half_3_18 half_5_17
  · have h := even_B_second_cross (u := 3) (t := 6)
      4 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (181763844281/2500000000000 : ℝ)) (φ₂ := (55360286591/2500000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_17
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_18 : AdmissibleExponent 8 12 (68566567885719/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 8) (s := 4) (u := 3) (t := 6)
    (φ₁ := (404892258021/5000000000000 : ℝ)) (φ₂ := (562809503763/10000000000000 : ℝ)) (χ := (20508672136862674124992311/4000000000000000000000000 : ℝ)) (γ := (51271680342157/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_18 half_4_18 half_6_17
  · have h := even_A_second_cross (u := 4) (v := 5) (w := 6)
      4 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (404892258021/5000000000000 : ℝ)) (φ₂ := (562809503763/10000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_5_18 half_6_17
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_19 : AdmissibleExponent 8 6 (30469786280111/10000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 8)
    (φ := (1082445021247/46082445021247 : ℝ)) half_4_18 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_19 : AdmissibleExponent 8 8 (10541222356161/2500000000000 : ℝ) := by
  have h := admissible_eight_A_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 8)
    (φ := (7307762503519/127307762503519 : ℝ)) half_3_19 half_4_18
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_19 : AdmissibleExponent 8 10 (27457855164709/5000000000000 : ℝ) := by
  apply two_stage_admissible (k := 8) (s := 3) (u := 2) (t := 5)
    (φ₁ := (727055072111/10000000000000 : ℝ)) (φ₂ := (110720209069/5000000000000 : ℝ)) (χ := (854235914118303617689145969/200000000000000000000000000 : ℝ)) (γ := (42711795705919/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_4_19 half_3_19 half_5_18
  · have h := even_B_second_cross (u := 3) (t := 6)
      4 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (727055072111/10000000000000 : ℝ)) (φ₂ := (110720209069/5000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_18
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_19 : AdmissibleExponent 8 12 (34283282538661/5000000000000 : ℝ) := by
  apply two_stage_admissible (k := 8) (s := 4) (u := 3) (t := 6)
    (φ₁ := (16195684903/200000000000 : ℝ)) (φ₂ := (562809197209/10000000000000 : ℝ)) (χ := (410173470668773560860838951/80000000000000000000000000 : ℝ)) (γ := (25635841916799/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_19 half_4_19 half_6_18
  · have h := even_A_second_cross (u := 4) (v := 5) (w := 6)
      4 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (16195684903/200000000000 : ℝ)) (φ₂ := (562809197209/10000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_5_19 half_6_18
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_20 : AdmissibleExponent 8 6 (15234893074593/5000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 8)
    (φ := (541222356161/23041222356161 : ℝ)) half_4_19 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_20 : AdmissibleExponent 8 8 (10541222288963/2500000000000 : ℝ) := by
  have h := admissible_eight_A_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 8)
    (φ := (3653880919297/63653880919297 : ℝ)) half_3_20 half_4_19
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_20 : AdmissibleExponent 8 10 (54915709569643/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 8) (s := 3) (u := 2) (t := 5)
    (φ₁ := (727054937177/10000000000000 : ℝ)) (φ₂ := (110720047913/5000000000000 : ℝ)) (χ := (427117976028546561181571017/100000000000000000000000000 : ℝ)) (γ := (42711797602857/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_4_20 half_3_20 half_5_19
  · have h := even_B_second_cross (u := 3) (t := 6)
      4 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (727054937177/10000000000000 : ℝ)) (φ₂ := (110720047913/5000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_19
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_20 : AdmissibleExponent 8 12 (68566563838151/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 8) (s := 4) (u := 3) (t := 6)
    (φ₁ := (80978412517/1000000000000 : ℝ)) (φ₂ := (562809061329/10000000000000 : ℝ)) (χ := (64089606730638053657588269/12500000000000000000000000 : ℝ)) (γ := (51271685384511/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_20 half_4_20 half_6_19
  · have h := even_A_second_cross (u := 4) (v := 5) (w := 6)
      4 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (80978412517/1000000000000 : ℝ)) (φ₂ := (562809061329/10000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_5_20 half_6_19
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_21 : AdmissibleExponent 8 6 (30469786092227/10000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 8)
    (φ := (541222288963/23041222288963 : ℝ)) half_4_20 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_21 : AdmissibleExponent 8 8 (10541222259729/2500000000000 : ℝ) := by
  have h := admissible_eight_A_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 8)
    (φ := (1826940387331/31826940387331 : ℝ)) half_3_21 half_4_20
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_21 : AdmissibleExponent 8 10 (13728927308937/2500000000000 : ℝ) := by
  apply two_stage_admissible (k := 8) (s := 3) (u := 2) (t := 5)
    (φ₁ := (727054877587/10000000000000 : ℝ)) (φ₂ := (110719976713/5000000000000 : ℝ)) (χ := (854235968829790890572623037/200000000000000000000000000 : ℝ)) (γ := (4271179844149/1000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_4_21 half_3_21 half_5_20
  · have h := even_B_second_cross (u := 3) (t := 6)
      4 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (727054877587/10000000000000 : ℝ)) (φ₂ := (110719976713/5000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_20
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_21 : AdmissibleExponent 8 12 (13713312658433/2000000000000 : ℝ) := by
  apply two_stage_admissible (k := 8) (s := 4) (u := 3) (t := 6)
    (φ₁ := (809784072129/10000000000000 : ℝ)) (φ₂ := (281404500609/5000000000000 : ℝ)) (χ := (2050867442876297886863321491/400000000000000000000000000 : ℝ)) (γ := (12817921517977/2500000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_21 half_4_21 half_6_20
  · have h := even_A_second_cross (u := 4) (v := 5) (w := 6)
      4 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (809784072129/10000000000000 : ℝ)) (φ₂ := (281404500609/5000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_5_21 half_6_20
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_22 : AdmissibleExponent 8 6 (3808723258431/1250000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 8)
    (φ := (541222259729/23041222259729 : ℝ)) half_4_21 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_22 : AdmissibleExponent 8 8 (10541222247011/2500000000000 : ℝ) := by
  have h := admissible_eight_A_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 8)
    (φ := (3653880711739/63653880711739 : ℝ)) half_3_22 half_4_21
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_22 : AdmissibleExponent 8 10 (54915709089159/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 8) (s := 3) (u := 2) (t := 5)
    (φ₁ := (727054851311/10000000000000 : ℝ)) (φ₂ := (55359972653/2500000000000 : ℝ)) (χ := (170847195246538182615413341/40000000000000000000000000 : ℝ)) (γ := (8542359762327/2000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_4_22 half_3_22 half_5_21
  · have h := even_B_second_cross (u := 3) (t := 6)
      4 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (727054851311/10000000000000 : ℝ)) (φ₂ := (55359972653/2500000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_21
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_22 : AdmissibleExponent 8 12 (13713312610381/2000000000000 : ℝ) := by
  apply two_stage_admissible (k := 8) (s := 4) (u := 3) (t := 6)
    (φ₁ := (10122300609/125000000000 : ℝ)) (φ₂ := (562808974673/10000000000000 : ℝ)) (χ := (2050867455038521347041991181/400000000000000000000000000 : ℝ)) (γ := (10254337275193/2000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_22 half_4_22 half_6_21
  · have h := even_A_second_cross (u := 4) (v := 5) (w := 6)
      4 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (10122300609/125000000000 : ℝ)) (φ₂ := (562808974673/10000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_5_22 half_6_21
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_23 : AdmissibleExponent 8 6 (7617446514167/2500000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 8)
    (φ := (541222247011/23041222247011 : ℝ)) half_4_22 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_23 : AdmissibleExponent 8 8 (5270611120739/1250000000000 : ℝ) := by
  have h := admissible_eight_A_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 8)
    (φ := (730776136873/12730776136873 : ℝ)) half_3_23 half_4_22
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_23 : AdmissibleExponent 8 10 (2745785451243/500000000000 : ℝ) := by
  apply two_stage_admissible (k := 8) (s := 3) (u := 2) (t := 5)
    (φ₁ := (727054839741/10000000000000 : ℝ)) (φ₂ := (221439862943/10000000000000 : ℝ)) (χ := (42711798974759481368259349/10000000000000000000000000 : ℝ)) (γ := (1067794974369/250000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_4_23 half_3_23 half_5_22
  · have h := even_B_second_cross (u := 3) (t := 6)
      4 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (727054839741/10000000000000 : ℝ)) (φ₂ := (221439862943/10000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_22
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_23 : AdmissibleExponent 8 12 (68566562946299/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 8) (s := 4) (u := 3) (t := 6)
    (φ₁ := (809784038403/10000000000000 : ℝ)) (φ₂ := (70351120371/1250000000000 : ℝ)) (χ := (16406939683276268834277377/3200000000000000000000000 : ℝ)) (γ := (320448040689/62500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_23 half_4_23 half_6_22
  · have h := even_A_second_cross (u := 4) (v := 5) (w := 6)
      4 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (809784038403/10000000000000 : ℝ)) (φ₂ := (70351120371/1250000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_5_23 half_6_22
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_24 : AdmissibleExponent 8 6 (15234893025989/5000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 8)
    (φ := (90203706913/3840203706913 : ℝ)) half_4_23 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_24 : AdmissibleExponent 8 8 (10541222239071/2500000000000 : ℝ) := by
  have h := admissible_eight_A_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 8)
    (φ := (152245028019/2652245028019 : ℝ)) half_3_24 half_4_23
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_24 : AdmissibleExponent 8 10 (54915708996677/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 8) (s := 3) (u := 2) (t := 5)
    (φ₁ := (181763708663/2500000000000 : ℝ)) (φ₂ := (22143985077/1000000000000 : ℝ)) (χ := (427117990465616184257923411/100000000000000000000000000 : ℝ)) (γ := (21355899523281/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_4_24 half_3_24 half_5_23
  · have h := even_B_second_cross (u := 3) (t := 6)
      4 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (181763708663/2500000000000 : ℝ)) (φ₂ := (22143985077/1000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_23
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_24 : AdmissibleExponent 8 12 (68566562899927/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 8) (s := 4) (u := 3) (t := 6)
    (φ₁ := (404892016931/5000000000000 : ℝ)) (φ₂ := (562808957813/10000000000000 : ℝ)) (χ := (82034698511121682443744449/16000000000000000000000000 : ℝ)) (γ := (12817921642363/2500000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_24 half_4_24 half_6_23
  · have h := even_A_second_cross (u := 4) (v := 5) (w := 6)
      4 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (404892016931/5000000000000 : ℝ)) (φ₂ := (562808957813/10000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_5_24 half_6_23
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_25 : AdmissibleExponent 8 6 (15234893024969/5000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 8)
    (φ := (541222239071/23041222239071 : ℝ)) half_4_24 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_25 : AdmissibleExponent 8 8 (8432977790419/2000000000000 : ℝ) := by
  have h := admissible_eight_A_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 8)
    (φ := (48718408897/848718408897 : ℝ)) half_3_25 half_4_24
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_25 : AdmissibleExponent 8 10 (54915708984333/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 8) (s := 3) (u := 2) (t := 5)
    (φ₁ := (22720463513/312500000000 : ℝ)) (φ₂ := (221439845421/10000000000000 : ℝ)) (χ := (854235981562523343664182101/200000000000000000000000000 : ℝ)) (γ := (2669487442383/625000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_4_25 half_3_25 half_5_24
  · have h := even_B_second_cross (u := 3) (t := 6)
      4 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (22720463513/312500000000 : ℝ)) (φ₂ := (221439845421/10000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_24
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_25 : AdmissibleExponent 8 12 (34283281439791/5000000000000 : ℝ) := by
  apply two_stage_admissible (k := 8) (s := 4) (u := 3) (t := 6)
    (φ₁ := (404892015933/5000000000000 : ℝ)) (φ₂ := (562808955547/10000000000000 : ℝ)) (χ := (2050867463820330713543980091/400000000000000000000000000 : ℝ)) (γ := (51271686595511/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_25 half_4_25 half_6_24
  · have h := even_A_second_cross (u := 4) (v := 5) (w := 6)
      4 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (404892015933/5000000000000 : ℝ)) (φ₂ := (562808955547/10000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_5_25 half_6_24
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_26 : AdmissibleExponent 8 6 (609395720981/200000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 8)
    (φ := (432977790419/18432977790419 : ℝ)) half_4_25 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_26 : AdmissibleExponent 8 8 (42164888950273/10000000000000 : ℝ) := by
  have h := admissible_eight_A_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 8)
    (φ := (974368177339/16974368177339 : ℝ)) half_3_26 half_4_25
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_26 : AdmissibleExponent 8 10 (54915708978931/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 8) (s := 3) (u := 2) (t := 5)
    (φ₁ := (363527415717/5000000000000 : ℝ)) (φ₂ := (864999387/39062500000 : ℝ)) (χ := (213558995459983922209165877/50000000000000000000000000 : ℝ)) (γ := (21355899545999/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_4_26 half_3_26 half_5_25
  · have h := even_B_second_cross (u := 3) (t := 6)
      4 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (363527415717/5000000000000 : ℝ)) (φ₂ := (864999387/39062500000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_25
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_26 : AdmissibleExponent 8 12 (13713312574133/2000000000000 : ℝ) := by
  apply two_stage_admissible (k := 8) (s := 4) (u := 3) (t := 6)
    (φ₁ := (809784030989/10000000000000 : ℝ)) (φ₂ := (562808954551/10000000000000 : ℝ)) (χ := (25635843303488312882718003/5000000000000000000000000 : ℝ)) (γ := (2563584330349/500000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_26 half_4_26 half_6_25
  · have h := even_A_second_cross (u := 4) (v := 5) (w := 6)
      4 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (809784030989/10000000000000 : ℝ)) (φ₂ := (562808954551/10000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_5_26 half_6_25
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_27 : AdmissibleExponent 8 6 (3808723256083/1250000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 8)
    (φ := (240543216697/10240543216697 : ℝ)) half_4_26 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_27 : AdmissibleExponent 8 8 (1054122223737/250000000000 : ℝ) := by
  have h := admissible_eight_A_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 8)
    (φ := (14615522656163/254615522656163 : ℝ)) half_3_27 half_4_26
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_27 : AdmissibleExponent 8 10 (54915708976567/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 8) (s := 3) (u := 2) (t := 5)
    (φ₁ := (181763707751/2500000000000 : ℝ)) (φ₂ := (110719921021/5000000000000 : ℝ)) (χ := (85423598196153059764040441/20000000000000000000000000 : ℝ)) (γ := (21355899549039/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_4_27 half_3_27 half_5_26
  · have h := even_B_second_cross (u := 3) (t := 6)
      4 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (181763707751/2500000000000 : ℝ)) (φ₂ := (110719921021/5000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_26
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_27 : AdmissibleExponent 8 12 (68566562866761/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 8) (s := 4) (u := 3) (t := 6)
    (φ₁ := (202446007651/2500000000000 : ℝ)) (φ₂ := (281404477057/5000000000000 : ℝ)) (χ := (1025433732240303601071148159/200000000000000000000000000 : ℝ)) (γ := (2563584330601/500000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_27 half_4_27 half_6_26
  · have h := even_A_second_cross (u := 4) (v := 5) (w := 6)
      4 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (202446007651/2500000000000 : ℝ)) (φ₂ := (281404477057/5000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_5_27 half_6_26
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_28 : AdmissibleExponent 8 6 (1904361628031/625000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 8)
    (φ := (54122223737/2304122223737 : ℝ)) half_4_27 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_28 : AdmissibleExponent 8 8 (8432977789827/2000000000000 : ℝ) := by
  have h := admissible_eight_A_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 8)
    (φ := (1826940331807/31826940331807 : ℝ)) half_3_28 half_4_27
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_28 : AdmissibleExponent 8 10 (3432231810971/625000000000 : ℝ) := by
  apply two_stage_admissible (k := 8) (s := 3) (u := 2) (t := 5)
    (φ₁ := (145410966163/2000000000000 : ℝ)) (φ₂ := (221439841591/10000000000000 : ℝ)) (χ := (427117991007438060539351517/100000000000000000000000000 : ℝ)) (γ := (10677949775187/2500000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_4_28 half_3_28 half_5_27
  · have h := even_B_second_cross (u := 3) (t := 6)
      4 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (145410966163/2000000000000 : ℝ)) (φ₂ := (221439841591/10000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_27
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_28 : AdmissibleExponent 8 12 (68566562865051/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 8) (s := 4) (u := 3) (t := 6)
    (φ₁ := (202446007609/2500000000000 : ℝ)) (φ₂ := (281404476961/5000000000000 : ℝ)) (χ := (1025433732284479682491771893/200000000000000000000000000 : ℝ)) (γ := (3204480413389/625000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_28 half_4_28 half_6_27
  · have h := even_A_second_cross (u := 4) (v := 5) (w := 6)
      4 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (202446007609/2500000000000 : ℝ)) (φ₂ := (281404476961/5000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_5_28 half_6_27
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_29 : AdmissibleExponent 8 6 (30469786048423/10000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 8)
    (φ := (432977789827/18432977789827 : ℝ)) half_4_28 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_29 : AdmissibleExponent 8 8 (8432977789797/2000000000000 : ℝ) := by
  have h := admissible_eight_A_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 8)
    (φ := (4871840884571/84871840884571 : ℝ)) half_3_29 half_4_28
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_29 : AdmissibleExponent 8 10 (27457854487541/5000000000000 : ℝ) := by
  apply two_stage_admissible (k := 8) (s := 3) (u := 2) (t := 5)
    (φ₁ := (727054830733/10000000000000 : ℝ)) (φ₂ := (221439841393/10000000000000 : ℝ)) (χ := (427117991019098342285365787/100000000000000000000000000 : ℝ)) (γ := (42711799101911/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_4_29 half_3_29 half_5_28
  · have h := even_B_second_cross (u := 3) (t := 6)
      4 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (727054830733/10000000000000 : ℝ)) (φ₂ := (221439841393/10000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_28
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_29 : AdmissibleExponent 8 12 (68566562864301/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 8) (s := 4) (u := 3) (t := 6)
    (φ₁ := (404892015181/5000000000000 : ℝ)) (φ₂ := (281404476919/5000000000000 : ℝ)) (χ := (2050867464607739694385397/400000000000000000000000 : ℝ)) (γ := (10254337323039/2000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_29 half_4_29 half_6_28
  · have h := even_A_second_cross (u := 4) (v := 5) (w := 6)
      4 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (404892015181/5000000000000 : ℝ)) (φ₂ := (281404476919/5000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_5_29 half_6_28
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_30 : AdmissibleExponent 8 6 (30469786048391/10000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 8)
    (φ := (432977789797/18432977789797 : ℝ)) half_4_29 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_30 : AdmissibleExponent 8 8 (1054122223723/250000000000 : ℝ) := by
  have h := admissible_eight_A_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 8)
    (φ := (14615522653391/254615522653391 : ℝ)) half_3_30 half_4_29
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_30 : AdmissibleExponent 8 10 (10983141794977/2000000000000 : ℝ) := by
  apply two_stage_admissible (k := 8) (s := 3) (u := 2) (t := 5)
    (φ₁ := (727054830697/10000000000000 : ℝ)) (φ₂ := (110719920653/5000000000000 : ℝ)) (χ := (854235982048451742807135097/200000000000000000000000000 : ℝ)) (γ := (42711799102423/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_4_30 half_3_30 half_5_29
  · have h := even_B_second_cross (u := 3) (t := 6)
      4 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (727054830697/10000000000000 : ℝ)) (φ₂ := (110719920653/5000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_29
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_30 : AdmissibleExponent 8 12 (34283281431987/5000000000000 : ℝ) := by
  apply two_stage_admissible (k := 8) (s := 4) (u := 3) (t := 6)
    (φ₁ := (80978403033/1000000000000 : ℝ)) (φ₂ := (562808953801/10000000000000 : ℝ)) (χ := (2050867464624669401435492699/400000000000000000000000000 : ℝ)) (γ := (51271686615617/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_30 half_4_30 half_6_29
  · have h := even_A_second_cross (u := 4) (v := 5) (w := 6)
      4 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (80978403033/1000000000000 : ℝ)) (φ₂ := (562808953801/10000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_5_30 half_6_29
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

theorem degree8_half_3 : AdmissibleExponent 8 6 (30469786048391/10000000000000 : ℝ) := half_3_30

theorem source8_entry_3 : AdmissibleExponent 8 6 (Certificate.source8[3]! : ℝ) := by
  apply admissibleExponent_mono degree8_half_3
  norm_num [Certificate.source8,Certificate.Q]

#print axioms source8_entry_3

theorem degree8_half_4 : AdmissibleExponent 8 8 (1054122223723/250000000000 : ℝ) := half_4_30

theorem source8_entry_4 : AdmissibleExponent 8 8 (Certificate.source8[4]! : ℝ) := by
  apply admissibleExponent_mono degree8_half_4
  norm_num [Certificate.source8,Certificate.Q]

#print axioms source8_entry_4

theorem degree8_half_5 : AdmissibleExponent 8 10 (10983141794977/2000000000000 : ℝ) := half_5_30

theorem source8_entry_5 : AdmissibleExponent 8 10 (Certificate.source8[5]! : ℝ) := by
  apply admissibleExponent_mono degree8_half_5
  norm_num [Certificate.source8,Certificate.Q]

#print axioms source8_entry_5

theorem degree8_half_6 : AdmissibleExponent 8 12 (34283281431987/5000000000000 : ℝ) := half_6_30

theorem source8_entry_6 : AdmissibleExponent 8 12 (Certificate.source8[6]! : ℝ) := by
  apply admissibleExponent_mono degree8_half_6
  norm_num [Certificate.source8,Certificate.Q]

#print axioms source8_entry_6

end Waring.SeedCompletionEven8SecondSeeds
