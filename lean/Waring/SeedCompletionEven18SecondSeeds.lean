import Waring.SeedCompletionEvenSecondHolder
import Waring.SeedCompletionTwoStageUpdate
import Waring.SeedCompletionFirstGeneralA
import Waring.SeedCompletionFirstBGeneral
import Waring.CertificateData
import Waring.SeedCompletionFirstGeneralB

/-! # Unconditional degree-18 source seeds through moment 16

Thirty exact finite A/B rounds start with proved endpoint moments.
Every auxiliary estimate is a theorem about the literal source sums.
All parameter balances and upward roundings are checked in Lean.
No published seed estimate or limiting recurrence value is assumed.
-/
noncomputable section
namespace Waring.SeedCompletionEven18SecondSeeds
open SmoothMoments FirstStageTransport SeedCompletionSecondScales
open SeedCompletionFirstGeneralA SeedCompletionSourceBounds

open SeedCompletionFirstGeneralB

private theorem half_2_00 : AdmissibleExponent 18 4 2 :=
  FourthMomentSeed.admissibleExponent_four (by norm_num)

private theorem half_3_00 : AdmissibleExponent 18 6 (3888888888889/1250000000000 : ℝ) := by
  have h := endpoint_admissible (s := 1) (by norm_num : 0 < (18 : ℕ))
    half_2_00 (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_00 : AdmissibleExponent 18 8 (42716049382717/10000000000000 : ℝ) := by
  have h := endpoint_admissible (s := 2) (by norm_num : 0 < (18 : ℕ))
    half_3_00 (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_00 : AdmissibleExponent 18 10 (54787379972567/10000000000000 : ℝ) := by
  have h := endpoint_admissible (s := 3) (by norm_num : 0 < (18 : ℕ))
    half_4_00 (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_6_00 : AdmissibleExponent 18 12 (33649596098157/5000000000000 : ℝ) := by
  have h := endpoint_admissible (s := 4) (by norm_num : 0 < (18 : ℕ))
    half_5_00 (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_7_00 : AdmissibleExponent 18 14 (3209080594083/400000000000 : ℝ) := by
  have h := endpoint_admissible (s := 5) (by norm_num : 0 < (18 : ℕ))
    half_6_00 (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_8_00 : AdmissibleExponent 18 16 (46773868124591/5000000000000 : ℝ) := by
  have h := endpoint_admissible (s := 6) (by norm_num : 0 < (18 : ℕ))
    half_7_00 (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_3_01 : AdmissibleExponent 18 6 (30281870595773/10000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
    (φ := (2716049382717/192716049382717 : ℝ)) half_4_00 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_01 : AdmissibleExponent 18 8 (41299302906693/10000000000000 : ℝ) := by
  have h := admissible_eight_B_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
    (φ := (210482843899/6147982843899 : ℝ)) half_3_01 half_6_00
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_01 : AdmissibleExponent 18 10 (52895359103237/10000000000000 : ℝ) := by
  apply first_stage_admissible_source (s := 3) (φ := (215075009213/5215075009213 : ℝ)) (χ := (52159602943545/10430150018426 : ℝ))
    (by norm_num : 0 < (18 : ℕ)) half_4_01 (by norm_num) (by norm_num)
  · have h := first_B_cross_power (u := 4) (t := 6)
      (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
      (φ := (215075009213/5215075009213 : ℝ)) (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
      (by norm_num) (by norm_num) half_6_00
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_01 : AdmissibleExponent 18 12 (64737501994981/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 4) (u := 3) (t := 6)
    (φ₁ := (78214921361/2000000000000 : ℝ)) (φ₂ := (178383605043/5000000000000 : ℝ)) (χ := (519192672288860835803733419/100000000000000000000000000 : ℝ)) (γ := (51919267228887/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_01 half_4_01 half_6_00
  · have h := even_B_second_cross (u := 4) (t := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (78214921361/2000000000000 : ℝ)) (φ₂ := (178383605043/5000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_00
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_7_01 : AdmissibleExponent 18 14 (38570313545503/5000000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 5) (u := 4) (t := 7)
    (φ₁ := (434856400411/10000000000000 : ℝ)) (φ₂ := (459841880891/10000000000000 : ℝ)) (χ := (244920413957161015149151259/40000000000000000000000000 : ℝ)) (γ := (61230103489291/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_6_01 half_5_01 half_7_00
  · have h := even_B_second_cross (u := 5) (t := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (434856400411/10000000000000 : ℝ)) (φ₂ := (459841880891/10000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/8 : ℝ)) (c := (5/8 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_00
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_8_01 : AdmissibleExponent 18 16 (9003507451511/1000000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 6) (u := 5) (t := 8)
    (φ₁ := (28778995977/625000000000 : ℝ)) (φ₂ := (249453675283/5000000000000 : ℝ)) (χ := (711977923843903247325957473/100000000000000000000000000 : ℝ)) (γ := (71197792384391/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_01 half_6_01 half_8_00
  · have h := even_A_second_cross (u := 6) (v := 8) (w := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (28778995977/625000000000 : ℝ)) (φ₂ := (249453675283/5000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_00 half_8_00
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_02 : AdmissibleExponent 18 6 (30135839795227/10000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
    (φ := (1299302906693/191299302906693 : ℝ)) half_4_01 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_02 : AdmissibleExponent 18 8 (40821657149073/10000000000000 : ℝ) := by
  have h := admissible_eight_B_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
    (φ := (4465822404527/194465822404527 : ℝ)) half_3_02 half_6_01
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_02 : AdmissibleExponent 18 10 (26034861268623/5000000000000 : ℝ) := by
  apply first_stage_admissible_source (s := 3) (φ := (12010032542743/377010032542743 : ℝ)) (χ := (3758021102053301/754020065085486 : ℝ))
    (by norm_num : 0 < (18 : ℕ)) half_4_02 (by norm_num) (by norm_num)
  · have h := first_B_cross_power (u := 4) (t := 6)
      (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
      (φ := (12010032542743/377010032542743 : ℝ)) (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
      (by norm_num) (by norm_num) half_6_01
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_02 : AdmissibleExponent 18 12 (15921162797567/2500000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 4) (u := 3) (t := 6)
    (φ₁ := (336932882201/10000000000000 : ℝ)) (φ₂ := (12087426207/625000000000 : ℝ)) (χ := (106244590163044197027163857/20000000000000000000000000 : ℝ)) (γ := (13280573770381/2500000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_02 half_4_02 half_6_01
  · have h := even_B_second_cross (u := 4) (t := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (336932882201/10000000000000 : ℝ)) (φ₂ := (12087426207/625000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_01
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_7_02 : AdmissibleExponent 18 14 (75769483255137/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 5) (u := 4) (t := 7)
    (φ₁ := (185103360711/5000000000000 : ℝ)) (φ₂ := (324336017303/10000000000000 : ℝ)) (χ := (3998981089331264196821461/640000000000000000000000 : ℝ)) (γ := (62484079520809/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_6_02 half_5_02 half_7_01
  · have h := even_B_second_cross (u := 5) (t := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (185103360711/5000000000000 : ℝ)) (φ₂ := (324336017303/10000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/8 : ℝ)) (c := (5/8 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_01
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_8_02 : AdmissibleExponent 18 16 (88309121873743/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 6) (u := 5) (t := 8)
    (φ₁ := (395394393087/10000000000000 : ℝ)) (φ₂ := (94985869621/2500000000000 : ℝ)) (χ := (289620711182824468316318657/40000000000000000000000000 : ℝ)) (γ := (72405177795713/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_02 half_6_02 half_8_01
  · have h := even_A_second_cross (u := 6) (v := 8) (w := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (395394393087/10000000000000 : ℝ)) (φ₂ := (94985869621/2500000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_01 half_8_01
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_03 : AdmissibleExponent 18 6 (30086117808781/10000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
    (φ := (821657149073/190821657149073 : ℝ)) half_4_02 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_03 : AdmissibleExponent 18 8 (40629080312441/10000000000000 : ℝ) := by
  have h := admissible_eight_B_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
    (φ := (1756207786353/96756207786353 : ℝ)) half_3_03 half_6_02
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_03 : AdmissibleExponent 18 10 (25864084916967/5000000000000 : ℝ) := by
  apply first_stage_admissible_source (s := 3) (φ := (10482061443213/375482061443213 : ℝ)) (χ := (3737851108581045/750964122886426 : ℝ))
    (by norm_num : 0 < (18 : ℕ)) half_4_03 (by norm_num) (by norm_num)
  · have h := first_B_cross_power (u := 4) (t := 6)
      (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
      (φ := (10482061443213/375482061443213 : ℝ)) (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
      (by norm_num) (by norm_num) half_6_02
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_03 : AdmissibleExponent 18 12 (63237957699031/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 4) (u := 3) (t := 6)
    (φ₁ := (312767893801/10000000000000 : ℝ)) (φ₂ := (54490574417/5000000000000 : ℝ)) (χ := (214829918776658270481193439/40000000000000000000000000 : ℝ)) (γ := (53707479694167/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_03 half_4_03 half_6_02
  · have h := even_B_second_cross (u := 4) (t := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (312767893801/10000000000000 : ℝ)) (φ₂ := (54490574417/5000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_02
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_7_03 : AdmissibleExponent 18 14 (9395195350049/1250000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 5) (u := 4) (t := 7)
    (φ₁ := (84722334829/2500000000000 : ℝ)) (φ₂ := (62816352793/2500000000000 : ℝ)) (χ := (126331107921157102099545427/20000000000000000000000000 : ℝ)) (γ := (3158277698029/500000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_6_03 half_5_03 half_7_02
  · have h := even_B_second_cross (u := 5) (t := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (84722334829/2500000000000 : ℝ)) (φ₂ := (62816352793/2500000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/8 : ℝ)) (c := (5/8 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_02
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_8_03 : AdmissibleExponent 18 16 (43748256051339/5000000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 6) (u := 5) (t := 8)
    (φ₁ := (360118072417/10000000000000 : ℝ)) (φ₂ := (39295041131/1250000000000 : ℝ)) (χ := (585320377079319973482259903/80000000000000000000000000 : ℝ)) (γ := (14633009426983/2000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_03 half_6_03 half_8_02
  · have h := even_A_second_cross (u := 6) (v := 8) (w := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (360118072417/10000000000000 : ℝ)) (φ₂ := (39295041131/1250000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_02 half_8_02
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_04 : AdmissibleExponent 18 6 (1879125028507/625000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
    (φ := (629080312441/190629080312441 : ℝ)) half_4_03 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_04 : AdmissibleExponent 18 8 (10136866298721/2500000000000 : ℝ) := by
  have h := admissible_eight_B_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
    (φ := (3105956786807/193105956786807 : ℝ)) half_3_04 half_6_03
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_04 : AdmissibleExponent 18 10 (5158247743949/1000000000000 : ℝ) := by
  apply first_stage_admissible_source (s := 3) (φ := (983351981341/37483351981341 : ℝ)) (χ := (932324759620043/187416759906705 : ℝ))
    (by norm_num : 0 < (18 : ℕ)) half_4_04 (by norm_num) (by norm_num)
  · have h := first_B_cross_power (u := 4) (t := 6)
      (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
      (φ := (983351981341/37483351981341 : ℝ)) (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
      (by norm_num) (by norm_num) half_6_03
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_04 : AdmissibleExponent 18 12 (63044591730627/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 4) (u := 3) (t := 6)
    (φ₁ := (75495100421/2500000000000 : ℝ)) (φ₂ := (34162996757/5000000000000 : ℝ)) (χ := (269903128963494782644464939/50000000000000000000000000 : ℝ)) (γ := (53980625792699/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_04 half_4_04 half_6_03
  · have h := even_B_second_cross (u := 4) (t := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (75495100421/2500000000000 : ℝ)) (φ₂ := (34162996757/5000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_03
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_7_04 : AdmissibleExponent 18 14 (18722966196041/2500000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 5) (u := 4) (t := 7)
    (φ₁ := (40542090507/1250000000000 : ℝ)) (φ₂ := (215315580493/10000000000000 : ℝ)) (χ := (508003267428620173792758889/80000000000000000000000000 : ℝ)) (γ := (31750204214289/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_6_04 half_5_04 half_7_03
  · have h := even_B_second_cross (u := 5) (t := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (40542090507/1250000000000 : ℝ)) (φ₂ := (215315580493/10000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/8 : ℝ)) (c := (5/8 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_03
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_8_04 : AdmissibleExponent 18 16 (69698288807/8000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 6) (u := 5) (t := 8)
    (φ₁ := (342660132591/10000000000000 : ℝ)) (φ₂ := (70420999237/2500000000000 : ℝ)) (χ := (1471298027978057388248791837/200000000000000000000000000 : ℝ)) (γ := (73564901398909/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_04 half_6_04 half_8_03
  · have h := even_A_second_cross (u := 6) (v := 8) (w := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (342660132591/10000000000000 : ℝ)) (φ₂ := (70420999237/2500000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_03 half_8_03
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_05 : AdmissibleExponent 18 6 (15028731171749/5000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
    (φ := (136866298721/47636866298721 : ℝ)) half_4_04 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_05 : AdmissibleExponent 18 8 (40512144441483/10000000000000 : ℝ) := by
  have h := admissible_eight_B_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
    (φ := (2929667043631/192929667043631 : ℝ)) half_3_05 half_6_04
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_05 : AdmissibleExponent 18 10 (51519259240269/10000000000000 : ℝ) := by
  apply first_stage_admissible_source (s := 3) (φ := (1910550027361/74910550027361 : ℝ)) (χ := (3725597544775479/749105500273610 : ℝ))
    (by norm_num : 0 < (18 : ℕ)) half_4_05 (by norm_num) (by norm_num)
  · have h := first_B_cross_power (u := 4) (t := 6)
      (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
      (φ := (1910550027361/74910550027361 : ℝ)) (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
      (by norm_num) (by norm_num) half_6_04
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_05 : AdmissibleExponent 18 12 (62959942065509/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 4) (u := 3) (t := 6)
    (φ₁ := (297166009153/10000000000000 : ℝ)) (φ₂ := (24711180629/5000000000000 : ℝ)) (χ := (865690253356050628710323/160000000000000000000000 : ℝ)) (γ := (27052820417379/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_05 half_4_05 half_6_04
  · have h := even_B_second_cross (u := 4) (t := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (297166009153/10000000000000 : ℝ)) (φ₂ := (24711180629/5000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_04
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_7_05 : AdmissibleExponent 18 14 (18693040588581/2500000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 5) (u := 4) (t := 7)
    (φ₁ := (317710106623/10000000000000 : ℝ)) (φ₂ := (198415106249/10000000000000 : ℝ)) (χ := (101852101871510123759537/16000000000000000000000 : ℝ)) (γ := (31828781834847/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_6_05 half_5_05 half_7_04
  · have h := even_B_second_cross (u := 5) (t := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (317710106623/10000000000000 : ℝ)) (φ₂ := (198415106249/10000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/8 : ℝ)) (c := (5/8 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_04
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_8_05 : AdmissibleExponent 18 16 (43476738950979/5000000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 6) (u := 5) (t := 8)
    (φ₁ := (33441481833/1000000000000 : ℝ)) (φ₂ := (266209864389/10000000000000 : ℝ)) (χ := (2360306255858363187921301/320000000000000000000000 : ℝ)) (γ := (36879785247789/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_05 half_6_05 half_8_04
  · have h := even_A_second_cross (u := 6) (v := 8) (w := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (33441481833/1000000000000 : ℝ)) (φ₂ := (266209864389/10000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_04 half_8_04
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_06 : AdmissibleExponent 18 6 (15026882508881/5000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
    (φ := (512144441483/190512144441483 : ℝ)) half_4_05 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_06 : AdmissibleExponent 18 8 (5062086152609/1250000000000 : ℝ) := by
  have h := admissible_eight_B_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
    (φ := (570482405997/38570482405997 : ℝ)) half_3_06 half_6_05
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_06 : AdmissibleExponent 18 10 (51491559164871/10000000000000 : ℝ) := by
  apply first_stage_admissible_source (s := 3) (φ := (4714908234201/187214908234201 : ℝ)) (χ := (930994394749316/187214908234201 : ℝ))
    (by norm_num : 0 < (18 : ℕ)) half_4_06 (by norm_num) (by norm_num)
  · have h := first_B_cross_power (u := 4) (t := 6)
      (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
      (φ := (4714908234201/187214908234201 : ℝ)) (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
      (by norm_num) (by norm_num) half_6_05
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_06 : AdmissibleExponent 18 12 (3932666083459/625000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 4) (u := 3) (t := 6)
    (φ₁ := (147510221503/5000000000000 : ℝ)) (φ₂ := (40804830943/10000000000000 : ℝ)) (χ := (541621653455503318443253929/100000000000000000000000000 : ℝ)) (γ := (54162165345551/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_06 half_4_06 half_6_05
  · have h := even_B_second_cross (u := 4) (t := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (147510221503/5000000000000 : ℝ)) (φ₂ := (40804830943/10000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_05
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_7_06 : AdmissibleExponent 18 14 (2988761125653/400000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 5) (u := 4) (t := 7)
    (φ₁ := (6294514503/200000000000 : ℝ)) (φ₂ := (47666322647/2500000000000 : ℝ)) (χ := (254918199956324427300246249/40000000000000000000000000 : ℝ)) (γ := (63729549989083/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_6_06 half_5_06 half_7_05
  · have h := even_B_second_cross (u := 5) (t := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (6294514503/200000000000 : ℝ)) (φ₂ := (47666322647/2500000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/8 : ℝ)) (c := (5/8 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_05
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_8_06 : AdmissibleExponent 18 16 (8687735816437/1000000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 6) (u := 5) (t := 8)
    (φ₁ := (1322486453/40000000000 : ℝ)) (φ₂ := (259084058643/10000000000000 : ℝ)) (χ := (1477011783532244094444600259/200000000000000000000000000 : ℝ)) (γ := (36925294588307/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_06 half_6_06 half_8_05
  · have h := even_A_second_cross (u := 6) (v := 8) (w := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (1322486453/40000000000 : ℝ)) (φ₂ := (259084058643/10000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_05 half_8_05
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_07 : AdmissibleExponent 18 6 (30052146756241/10000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
    (φ := (62086152609/23812086152609 : ℝ)) half_4_06 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_07 : AdmissibleExponent 18 8 (40489884866249/10000000000000 : ℝ) := by
  have h := admissible_eight_B_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
    (φ := (1409181911431/96409181911431 : ℝ)) half_3_07 half_6_06
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_07 : AdmissibleExponent 18 10 (1029587093293/200000000000 : ℝ) := by
  apply first_stage_admissible_source (s := 3) (φ := (9375660071941/374375660071941 : ℝ)) (χ := (3723264235523941/748751320143882 : ℝ))
    (by norm_num : 0 < (18 : ℕ)) half_4_07 (by norm_num) (by norm_num)
  · have h := first_B_cross_power (u := 4) (t := 6)
      (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
      (φ := (9375660071941/374375660071941 : ℝ)) (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
      (by norm_num) (by norm_num) half_6_06
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_07 : AdmissibleExponent 18 12 (62906180137533/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 4) (u := 3) (t := 6)
    (φ₁ := (73516410541/2500000000000 : ℝ)) (φ₂ := (36921155667/10000000000000 : ℝ)) (χ := (108375056742958828954251853/20000000000000000000000000 : ℝ)) (γ := (27093764185743/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_07 half_4_07 half_6_06
  · have h := even_B_second_cross (u := 4) (t := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (73516410541/2500000000000 : ℝ)) (φ₂ := (36921155667/10000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_06
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_7_07 : AdmissibleExponent 18 14 (3734772199899/500000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 5) (u := 4) (t := 7)
    (φ₁ := (313390112057/10000000000000 : ℝ)) (φ₂ := (93580687281/5000000000000 : ℝ)) (χ := (102019323813576327954243497/16000000000000000000000000 : ℝ)) (γ := (31881038691743/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_6_07 half_5_07 half_7_06
  · have h := even_B_second_cross (u := 5) (t := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (313390112057/10000000000000 : ℝ)) (φ₂ := (93580687281/5000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/8 : ℝ)) (c := (5/8 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_06
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_8_07 : AdmissibleExponent 18 16 (8684333016101/1000000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 6) (u := 5) (t := 8)
    (φ₁ := (328902957851/10000000000000 : ℝ)) (φ₂ := (10234176413/400000000000 : ℝ)) (χ := (18473049757615611357217079/2500000000000000000000000 : ℝ)) (γ := (73892199030469/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_07 half_6_07 half_8_06
  · have h := even_A_second_cross (u := 6) (v := 8) (w := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (328902957851/10000000000000 : ℝ)) (φ₂ := (10234176413/400000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_06 half_8_06
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_08 : AdmissibleExponent 18 6 (15025717106533/5000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
    (φ := (489884866249/190489884866249 : ℝ)) half_4_07 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_08 : AdmissibleExponent 18 8 (40486878835179/10000000000000 : ℝ) := by
  have h := admissible_eight_B_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
    (φ := (2803311711401/192803311711401 : ℝ)) half_3_08 half_6_07
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_08 : AdmissibleExponent 18 10 (25736980345737/5000000000000 : ℝ) := by
  apply first_stage_admissible_source (s := 3) (φ := (9351723769529/374351723769529 : ℝ)) (χ := (3722949050046183/748703447539058 : ℝ))
    (by norm_num : 0 < (18 : ℕ)) half_4_08 (by norm_num) (by norm_num)
  · have h := first_B_cross_power (u := 4) (t := 6)
      (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
      (φ := (9351723769529/374351723769529 : ℝ)) (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
      (by norm_num) (by norm_num) half_6_07
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_08 : AdmissibleExponent 18 12 (12579777036707/2000000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 4) (u := 3) (t := 6)
    (φ₁ := (293641210443/10000000000000 : ℝ)) (φ₂ := (35182505497/10000000000000 : ℝ)) (χ := (5419885616860762066482503/1000000000000000000000000 : ℝ)) (γ := (1693714255269/312500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_08 half_4_08 half_6_07
  · have h := even_B_second_cross (u := 4) (t := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (293641210443/10000000000000 : ℝ)) (φ₂ := (35182505497/10000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_07
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_7_08 : AdmissibleExponent 18 14 (9335622124179/1250000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 5) (u := 4) (t := 7)
    (φ₁ := (78198640063/2500000000000 : ℝ)) (φ₂ := (185589918109/10000000000000 : ℝ)) (χ := (102042657248730293300909539/16000000000000000000000000 : ℝ)) (γ := (3188833039023/500000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_6_08 half_5_08 half_7_07
  · have h := even_B_second_cross (u := 5) (t := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (78198640063/2500000000000 : ℝ)) (φ₂ := (185589918109/10000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/8 : ℝ)) (c := (5/8 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_07
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_8_08 : AdmissibleExponent 18 16 (5426760393787/625000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 6) (u := 5) (t := 8)
    (φ₁ := (65626228347/2000000000000 : ℝ)) (φ₂ := (7950122799/312500000000 : ℝ)) (χ := (295643916188316820753851191/40000000000000000000000000 : ℝ)) (γ := (36955489523541/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_08 half_6_08 half_8_07
  · have h := even_A_second_cross (u := 6) (v := 8) (w := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (65626228347/2000000000000 : ℝ)) (φ₂ := (7950122799/312500000000 : ℝ)) (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_07 half_8_07
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_09 : AdmissibleExponent 18 6 (15025559704593/5000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
    (φ := (486878835179/190486878835179 : ℝ)) half_4_08 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_09 : AdmissibleExponent 18 8 (40485548273091/10000000000000 : ℝ) := by
  have h := admissible_eight_B_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
    (φ := (2796646365163/192796646365163 : ℝ)) half_3_09 half_6_08
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_09 : AdmissibleExponent 18 10 (51471572595141/10000000000000 : ℝ) := by
  apply first_stage_admissible_source (s := 3) (φ := (9341125547797/374341125547797 : ℝ)) (χ := (3722809526126831/748682251095594 : ℝ))
    (by norm_num : 0 < (18 : ℕ)) half_4_09 (by norm_num) (by norm_num)
  · have h := first_B_cross_power (u := 4) (t := 6)
      (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
      (φ := (9341125547797/374341125547797 : ℝ)) (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
      (by norm_num) (by norm_num) half_6_08
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_09 : AdmissibleExponent 18 12 (12579130459557/2000000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 4) (u := 3) (t := 6)
    (φ₁ := (146726339467/5000000000000 : ℝ)) (φ₂ := (17203566257/5000000000000 : ℝ)) (χ := (8469359600219314993665803/1562500000000000000000000 : ℝ)) (γ := (54203901441409/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_09 half_4_09 half_6_08
  · have h := even_B_second_cross (u := 4) (t := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (146726339467/5000000000000 : ℝ)) (φ₂ := (17203566257/5000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_08
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_7_09 : AdmissibleExponent 18 14 (74680331995253/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 5) (u := 4) (t := 7)
    (φ₁ := (78132391371/2500000000000 : ℝ)) (φ₂ := (92444202121/5000000000000 : ℝ)) (χ := (31891584936132126097753819/5000000000000000000000000 : ℝ)) (γ := (15945792468067/2500000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_6_09 half_5_09 half_7_08
  · have h := even_B_second_cross (u := 5) (t := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (78132391371/2500000000000 : ℝ)) (φ₂ := (92444202121/5000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/8 : ℝ)) (c := (5/8 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_08
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_8_09 : AdmissibleExponent 18 16 (21705355334491/2500000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 6) (u := 5) (t := 8)
    (φ₁ := (32778631737/1000000000000 : ℝ)) (φ₂ := (126877951233/5000000000000 : ℝ)) (χ := (46199620674643641888080801/6250000000000000000000000 : ℝ)) (γ := (73919393079433/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_09 half_6_09 half_8_08
  · have h := even_A_second_cross (u := 6) (v := 8) (w := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (32778631737/1000000000000 : ℝ)) (φ₂ := (126877951233/5000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_08 half_8_08
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_10 : AdmissibleExponent 18 6 (3756372508013/1250000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
    (φ := (485548273091/190485548273091 : ℝ)) half_4_09 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_10 : AdmissibleExponent 18 8 (1619398347781/400000000000 : ℝ) := by
  have h := admissible_eight_B_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
    (φ := (2793692169577/192793692169577 : ℝ)) half_3_10 half_6_09
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_10 : AdmissibleExponent 18 10 (51470514280883/10000000000000 : ℝ) := by
  apply first_stage_admissible_source (s := 3) (φ := (1867285702399/74867285702399 : ℝ)) (χ := (744549539749661/149734571404798 : ℝ))
    (by norm_num : 0 < (18 : ℕ)) half_4_10 (by norm_num) (by norm_num)
  · have h := first_B_cross_power (u := 4) (t := 6)
      (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
      (φ := (1867285702399/74867285702399 : ℝ)) (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
      (by norm_num) (by norm_num) half_6_09
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_10 : AdmissibleExponent 18 12 (62894218816589/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 4) (u := 3) (t := 6)
    (φ₁ := (293368972411/10000000000000 : ℝ)) (φ₂ := (34062108097/10000000000000 : ℝ)) (χ := (67757681118334382527449643/12500000000000000000000000 : ℝ)) (γ := (13551536223667/2500000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_10 half_4_10 half_6_09
  · have h := even_B_second_cross (u := 4) (t := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (293368972411/10000000000000 : ℝ)) (φ₂ := (34062108097/10000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_09
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_7_10 : AdmissibleExponent 18 14 (74678270797117/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 5) (u := 4) (t := 7)
    (φ₁ := (312411798517/10000000000000 : ℝ)) (φ₂ := (28840011/1562500000 : ℝ)) (χ := (255144270624162580203083753/40000000000000000000000000 : ℝ)) (γ := (63786067656043/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_6_10 half_5_10 half_7_09
  · have h := even_B_second_cross (u := 5) (t := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (312411798517/10000000000000 : ℝ)) (φ₂ := (28840011/1562500000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/8 : ℝ)) (c := (5/8 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_09
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_8_10 : AdmissibleExponent 18 16 (43409212183431/5000000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 6) (u := 5) (t := 8)
    (φ₁ := (163816359109/5000000000000 : ℝ)) (φ₂ := (253467251349/10000000000000 : ℝ)) (χ := (739231469941996576383693809/100000000000000000000000000 : ℝ)) (γ := (36961573497103/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_10 half_6_10 half_8_09
  · have h := even_A_second_cross (u := 6) (v := 8) (w := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (163816359109/5000000000000 : ℝ)) (φ₂ := (253467251349/10000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_09 half_8_09
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_11 : AdmissibleExponent 18 6 (6010183663799/2000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
    (φ := (19398347781/7619398347781 : ℝ)) half_4_10 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_11 : AdmissibleExponent 18 8 (40484697294111/10000000000000 : ℝ) := by
  have h := admissible_eight_B_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
    (φ := (2792382178599/192792382178599 : ℝ)) half_3_11 half_6_10
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_11 : AdmissibleExponent 18 10 (5147004502427/1000000000000 : ℝ) := by
  apply first_stage_admissible_source (s := 3) (φ := (1866869150169/74866869150169 : ℝ)) (χ := (3722720285473483/748668691501690 : ℝ))
    (by norm_num : 0 < (18 : ℕ)) half_4_11 (by norm_num) (by norm_num)
  · have h := first_B_cross_power (u := 4) (t := 6)
      (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
      (φ := (1866869150169/74866869150169 : ℝ)) (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
      (by norm_num) (by norm_num) half_6_10
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_11 : AdmissibleExponent 18 12 (251574332061/40000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 4) (u := 3) (t := 6)
    (φ₁ := (146665908889/5000000000000 : ℝ)) (φ₂ := (3390877289/1000000000000 : ℝ)) (χ := (135517853848047874399294523/25000000000000000000000000 : ℝ)) (γ := (54207141539221/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_11 half_4_11 half_6_10
  · have h := even_B_second_cross (u := 4) (t := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (146665908889/5000000000000 : ℝ)) (φ₂ := (3390877289/1000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_10
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_7_11 : AdmissibleExponent 18 14 (14935471238021/2000000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 5) (u := 4) (t := 7)
    (φ₁ := (156179749057/5000000000000 : ℝ)) (φ₂ := (36887443989/2000000000000 : ℝ)) (χ := (510298846653039721701719571/80000000000000000000000000 : ℝ)) (γ := (63787355831637/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_6_11 half_5_11 half_7_10
  · have h := even_B_second_cross (u := 5) (t := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (156179749057/5000000000000 : ℝ)) (φ₂ := (36887443989/2000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/8 : ℝ)) (c := (5/8 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_10
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_8_11 : AdmissibleExponent 18 16 (86817093553227/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 6) (u := 5) (t := 8)
    (φ₁ := (81891103847/2500000000000 : ℝ)) (φ₂ := (10133555851/400000000000 : ℝ)) (χ := (1478496355686754255247032741/200000000000000000000000000 : ℝ)) (γ := (36962408892169/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_11 half_6_11 half_8_10
  · have h := even_A_second_cross (u := 6) (v := 8) (w := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (81891103847/2500000000000 : ℝ)) (φ₂ := (10133555851/400000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_10 half_8_10
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_12 : AdmissibleExponent 18 6 (7512722735763/2500000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
    (φ := (484697294111/190484697294111 : ℝ)) half_4_11 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_12 : AdmissibleExponent 18 8 (40484581359307/10000000000000 : ℝ) := by
  have h := admissible_eight_B_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
    (φ := (73468450767/5073468450767 : ℝ)) half_3_12 half_6_11
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_12 : AdmissibleExponent 18 10 (51469836894019/10000000000000 : ℝ) := by
  apply first_stage_admissible_source (s := 3) (φ := (9333421952579/374333421952579 : ℝ)) (χ := (3722708127039727/748666843905158 : ℝ))
    (by norm_num : 0 < (18 : ℕ)) half_4_12 (by norm_num) (by norm_num)
  · have h := first_B_cross_power (u := 4) (t := 6)
      (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
      (φ := (9333421952579/374333421952579 : ℝ)) (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
      (by norm_num) (by norm_num) half_6_11
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_12 : AdmissibleExponent 18 12 (62893300968669/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 4) (u := 3) (t := 6)
    (φ₁ := (146657664383/5000000000000 : ℝ)) (φ₂ := (33840676553/10000000000000 : ℝ)) (χ := (1084151681107760346978385587/200000000000000000000000000 : ℝ)) (γ := (54207584055389/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_12 half_4_12 half_6_11
  · have h := even_B_second_cross (u := 4) (t := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (146657664383/5000000000000 : ℝ)) (φ₂ := (33840676553/10000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_11
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_7_12 : AdmissibleExponent 18 14 (2333654698961/312500000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 5) (u := 4) (t := 7)
    (φ₁ := (312336280739/10000000000000 : ℝ)) (φ₂ := (184375545503/10000000000000 : ℝ)) (χ := (510303423991642025998808533/80000000000000000000000000 : ℝ)) (γ := (63787927998959/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_6_12 half_5_12 half_7_11
  · have h := even_B_second_cross (u := 5) (t := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (312336280739/10000000000000 : ℝ)) (φ₂ := (184375545503/10000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/8 : ℝ)) (c := (5/8 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_11
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_8_12 : AdmissibleExponent 18 16 (17363300561939/2000000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 6) (u := 5) (t := 8)
    (φ₁ := (32753407181/1000000000000 : ℝ)) (φ₂ := (253281875419/10000000000000 : ℝ)) (χ := (2957022416226661251996026051/400000000000000000000000000 : ℝ)) (γ := (73925560405671/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_12 half_6_12 half_8_11
  · have h := even_A_second_cross (u := 6) (v := 8) (w := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (32753407181/1000000000000 : ℝ)) (φ₂ := (253281875419/10000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_11 half_8_11
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_13 : AdmissibleExponent 18 6 (58693122659/19531250000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
    (φ := (484581359307/190484581359307 : ℝ)) half_4_12 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_13 : AdmissibleExponent 18 8 (40484529931201/10000000000000 : ℝ) := by
  have h := admissible_eight_B_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
    (φ := (2791543365853/192791543365853 : ℝ)) half_3_13 half_6_12
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_13 : AdmissibleExponent 18 10 (25734872283221/5000000000000 : ℝ) := by
  apply first_stage_admissible_source (s := 3) (φ := (1866602428747/74866602428747 : ℝ)) (χ := (3722702733552613/748666024287470 : ℝ))
    (by norm_num : 0 < (18 : ℕ)) half_4_13 (by norm_num) (by norm_num)
  · have h := first_B_cross_power (u := 4) (t := 6)
      (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
      (φ := (1866602428747/74866602428747 : ℝ)) (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
      (by norm_num) (by norm_num) half_6_12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_13 : AdmissibleExponent 18 12 (31446587919749/5000000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 4) (u := 3) (t := 6)
    (φ₁ := (146654005871/5000000000000 : ℝ)) (φ₂ := (16905223537/5000000000000 : ℝ)) (χ := (3387986279685398868303059/625000000000000000000000 : ℝ)) (γ := (54207780474967/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_13 half_4_13 half_6_12
  · have h := even_B_second_cross (u := 4) (t := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (146654005871/5000000000000 : ℝ)) (φ₂ := (16905223537/5000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_7_13 : AdmissibleExponent 18 14 (74676770300613/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 5) (u := 4) (t := 7)
    (φ₁ := (78081494083/2500000000000 : ℝ)) (φ₂ := (92174082087/5000000000000 : ℝ)) (χ := (102061091229618800179099433/16000000000000000000000000 : ℝ)) (γ := (3986761376157/625000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_6_13 half_5_13 half_7_12
  · have h := even_B_second_cross (u := 5) (t := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (78081494083/2500000000000 : ℝ)) (φ₂ := (92174082087/5000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/8 : ℝ)) (c := (5/8 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_8_13 : AdmissibleExponent 18 16 (86816240632989/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 6) (u := 5) (t := 8)
    (φ₁ := (327520599061/10000000000000 : ℝ)) (φ₂ := (253256558069/10000000000000 : ℝ)) (χ := (59140712181464000829857479/8000000000000000000000000 : ℝ)) (γ := (18481472556709/2500000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_13 half_6_13 half_8_12
  · have h := even_A_second_cross (u := 6) (v := 8) (w := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (327520599061/10000000000000 : ℝ)) (φ₂ := (253256558069/10000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_12 half_8_12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_14 : AdmissibleExponent 18 6 (3005087341543/1000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
    (φ := (484529931201/190484529931201 : ℝ)) half_4_13 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_14 : AdmissibleExponent 18 8 (809690142313/200000000000 : ℝ) := by
  have h := admissible_eight_B_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
    (φ := (1395714504319/96395714504319 : ℝ)) half_3_14 half_6_13
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_14 : AdmissibleExponent 18 10 (25734851802881/5000000000000 : ℝ) := by
  apply first_stage_admissible_source (s := 3) (φ := (4666415166023/187166415166023 : ℝ)) (χ := (1861350170385317/374332830332046 : ℝ))
    (by norm_num : 0 < (18 : ℕ)) half_4_14 (by norm_num) (by norm_num)
  · have h := first_B_cross_power (u := 4) (t := 6)
      (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
      (φ := (4666415166023/187166415166023 : ℝ)) (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
      (by norm_num) (by norm_num) half_6_13
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_14 : AdmissibleExponent 18 12 (15723280080901/2500000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 4) (u := 3) (t := 6)
    (φ₁ := (146652382491/5000000000000 : ℝ)) (φ₂ := (8449257643/2500000000000 : ℝ)) (χ := (542078676445705582287034547/100000000000000000000000000 : ℝ)) (γ := (54207867644571/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_14 half_4_14 half_6_13
  · have h := even_B_second_cross (u := 4) (t := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (146652382491/5000000000000 : ℝ)) (φ₂ := (8449257643/2500000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_13
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_7_14 : AdmissibleExponent 18 14 (9334586300633/1250000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 5) (u := 4) (t := 7)
    (φ₁ := (312321403579/10000000000000 : ℝ)) (φ₂ := (92168005541/5000000000000 : ℝ)) (χ := (1020612716214152425111148271/160000000000000000000000000 : ℝ)) (γ := (12757658952677/2000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_6_14 half_5_14 half_7_13
  · have h := even_B_second_cross (u := 5) (t := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (312321403579/10000000000000 : ℝ)) (φ₂ := (92168005541/5000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/8 : ℝ)) (c := (5/8 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_13
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_8_14 : AdmissibleExponent 18 16 (86816124289943/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 6) (u := 5) (t := 8)
    (φ₁ := (327514618923/10000000000000 : ℝ)) (φ₂ := (253245320557/10000000000000 : ℝ)) (χ := (73926036647179564360137071/10000000000000000000000000 : ℝ)) (γ := (36963018323593/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_14 half_6_14 half_8_13
  · have h := even_A_second_cross (u := 6) (v := 8) (w := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (327514618923/10000000000000 : ℝ)) (φ₂ := (253245320557/10000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_13 half_8_13
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_15 : AdmissibleExponent 18 6 (6010174205199/2000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
    (φ := (9690142313/3809690142313 : ℝ)) half_4_14 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_15 : AdmissibleExponent 18 8 (101211242483/25000000000 : ℝ) := by
  have h := admissible_eight_B_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
    (φ := (1395689135807/96395689135807 : ℝ)) half_3_15 half_6_14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_15 : AdmissibleExponent 18 10 (51469685432843/10000000000000 : ℝ) := by
  apply first_stage_admissible_source (s := 3) (φ := (1166593708451/46791593708451 : ℝ)) (χ := (232668704948377/46791593708451 : ℝ))
    (by norm_num : 0 < (18 : ℕ)) half_4_15 (by norm_num) (by norm_num)
  · have h := first_B_cross_power (u := 4) (t := 6)
      (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
      (φ := (1166593708451/46791593708451 : ℝ)) (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
      (by norm_num) (by norm_num) half_6_14
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_15 : AdmissibleExponent 18 12 (62893095692283/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 4) (u := 3) (t := 6)
    (φ₁ := (4582864443/156250000000 : ℝ)) (φ₂ := (33791076791/10000000000000 : ℝ)) (χ := (1084158126520944838317395151/200000000000000000000000000 : ℝ)) (γ := (54207906326051/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_15 half_4_15 half_6_14
  · have h := even_B_second_cross (u := 4) (t := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (4582864443/156250000000 : ℝ)) (φ₂ := (33791076791/10000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_14
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_7_15 : AdmissibleExponent 18 14 (9334581869441/1250000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 5) (u := 4) (t := 7)
    (φ₁ := (31231937449/1000000000000 : ℝ)) (φ₂ := (46082654449/2500000000000 : ℝ)) (χ := (510306758375954695911310151/80000000000000000000000000 : ℝ)) (γ := (12757668959399/2000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_6_15 half_5_15 half_7_14
  · have h := even_B_second_cross (u := 5) (t := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (31231937449/1000000000000 : ℝ)) (φ₂ := (46082654449/2500000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/8 : ℝ)) (c := (5/8 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_14
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_8_15 : AdmissibleExponent 18 16 (86816072665021/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 6) (u := 5) (t := 8)
    (φ₁ := (65502392997/2000000000000 : ℝ)) (φ₂ := (253240333459/10000000000000 : ℝ)) (χ := (739261016330424218957188481/100000000000000000000000000 : ℝ)) (γ := (73926101633043/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_15 half_6_15 half_8_14
  · have h := even_A_second_cross (u := 6) (v := 8) (w := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (65502392997/2000000000000 : ℝ)) (φ₂ := (253240333459/10000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_14 half_8_14
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_16 : AdmissibleExponent 18 6 (30050869965887/10000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
    (φ := (1211242483/476211242483 : ℝ)) half_4_15 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_16 : AdmissibleExponent 18 8 (40484492502091/10000000000000 : ℝ) := by
  have h := admissible_eight_B_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
    (φ := (2791355760509/192791355760509 : ℝ)) half_3_16 half_6_15
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_16 : AdmissibleExponent 18 10 (25734838684943/5000000000000 : ℝ) := by
  apply first_stage_admissible_source (s := 3) (φ := (9332713878293/374332713878293 : ℝ)) (χ := (3722698808165815/748665427756586 : ℝ))
    (by norm_num : 0 < (18 : ℕ)) half_4_16 (by norm_num) (by norm_num)
  · have h := first_B_cross_power (u := 4) (t := 6)
      (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
      (φ := (9332713878293/374332713878293 : ℝ)) (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
      (by norm_num) (by norm_num) half_6_15
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_16 : AdmissibleExponent 18 12 (15723271190923/2500000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 4) (u := 3) (t := 6)
    (φ₁ := (293302685137/10000000000000 : ℝ)) (φ₂ := (16894217447/5000000000000 : ℝ)) (χ := (1084158469800245598033864349/200000000000000000000000000 : ℝ)) (γ := (54207923490017/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_16 half_4_16 half_6_15
  · have h := even_B_second_cross (u := 4) (t := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (293302685137/10000000000000 : ℝ)) (φ₂ := (16894217447/5000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_15
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_7_16 : AdmissibleExponent 18 14 (74676639226681/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 5) (u := 4) (t := 7)
    (φ₁ := (312318474147/10000000000000 : ℝ)) (φ₂ := (18432822457/1000000000000 : ℝ)) (χ := (1020613871983662136148521943/160000000000000000000000000 : ℝ)) (γ := (63788366998979/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_6_16 half_5_16 half_7_15
  · have h := even_B_second_cross (u := 5) (t := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (312318474147/10000000000000 : ℝ)) (φ₂ := (18432822457/1000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/8 : ℝ)) (c := (5/8 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_15
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_8_16 : AdmissibleExponent 18 16 (10852006219787/1250000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 6) (u := 5) (t := 8)
    (φ₁ := (327510787303/10000000000000 : ℝ)) (φ₂ := (50647624089/2000000000000 : ℝ)) (χ := (739261304718401041073387969/100000000000000000000000000 : ℝ)) (γ := (14785226094369/2000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_16 half_6_16 half_8_15
  · have h := even_A_second_cross (u := 6) (v := 8) (w := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (327510787303/10000000000000 : ℝ)) (φ₂ := (50647624089/2000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_15 half_8_15
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_17 : AdmissibleExponent 18 6 (30050869495541/10000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
    (φ := (484492502091/190484492502091 : ℝ)) half_4_16 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_17 : AdmissibleExponent 18 8 (40484490509451/10000000000000 : ℝ) := by
  have h := admissible_eight_B_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
    (φ := (279134577261/19279134577261 : ℝ)) half_3_17 half_6_16
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_17 : AdmissibleExponent 18 10 (51469673792463/10000000000000 : ℝ) := by
  apply first_stage_admissible_source (s := 3) (φ := (9332697999031/374332697999031 : ℝ)) (χ := (3722698599186047/748665395998062 : ℝ))
    (by norm_num : 0 < (18 : ℕ)) half_4_17 (by norm_num) (by norm_num)
  · have h := first_B_cross_power (u := 4) (t := 6)
      (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
      (φ := (9332697999031/374332697999031 : ℝ)) (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
      (by norm_num) (by norm_num) half_6_16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_17 : AdmissibleExponent 18 12 (7861634989347/1250000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 4) (u := 3) (t := 6)
    (φ₁ := (146651200759/5000000000000 : ℝ)) (φ₂ := (422340783/125000000000 : ℝ)) (χ := (67759913882320921517852827/12500000000000000000000000 : ℝ)) (γ := (54207931105857/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_17 half_4_17 half_6_16
  · have h := even_B_second_cross (u := 4) (t := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (146651200759/5000000000000 : ℝ)) (φ₂ := (422340783/125000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_7_17 : AdmissibleExponent 18 14 (74676632247851/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 5) (u := 4) (t := 7)
    (φ₁ := (312318074659/10000000000000 : ℝ)) (φ₂ := (92163581323/5000000000000 : ℝ)) (χ := (25515350740175459879689193/4000000000000000000000000 : ℝ)) (γ := (1594709421261/250000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_6_17 half_5_17 half_7_16
  · have h := even_B_second_cross (u := 5) (t := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (312318074659/10000000000000 : ℝ)) (φ₂ := (92163581323/5000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/8 : ℝ)) (c := (5/8 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_8_17 : AdmissibleExponent 18 16 (86816039594447/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 6) (u := 5) (t := 8)
    (φ₁ := (10234695773/312500000000 : ℝ)) (φ₂ := (253237138477/10000000000000 : ℝ)) (χ := (369630716343403375636073107/50000000000000000000000000 : ℝ)) (γ := (18481535817171/2500000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_17 half_6_17 half_8_16
  · have h := even_A_second_cross (u := 6) (v := 8) (w := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (10234695773/312500000000 : ℝ)) (φ₂ := (253237138477/10000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_16 half_8_16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_18 : AdmissibleExponent 18 6 (6010173857371/2000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
    (φ := (484490509451/190484490509451 : ℝ)) half_4_17 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_18 : AdmissibleExponent 18 8 (40484489625337/10000000000000 : ℝ) := by
  have h := admissible_eight_B_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
    (φ := (1395670670533/96395670670533 : ℝ)) half_3_18 half_6_17
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_18 : AdmissibleExponent 18 10 (25734836102597/5000000000000 : ℝ) := by
  apply first_stage_admissible_source (s := 3) (φ := (9332690953541/374332690953541 : ℝ)) (χ := (3722698506463765/748665381907082 : ℝ))
    (by norm_num : 0 < (18 : ℕ)) half_4_18 (by norm_num) (by norm_num)
  · have h := first_B_cross_power (u := 4) (t := 6)
      (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
      (φ := (9332690953541/374332690953541 : ℝ)) (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
      (by norm_num) (by norm_num) half_6_17
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_18 : AdmissibleExponent 18 12 (31446538881673/5000000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 4) (u := 3) (t := 6)
    (φ₁ := (73325568919/2500000000000 : ℝ)) (φ₂ := (33786742503/10000000000000 : ℝ)) (χ := (1084158689700903141429547987/200000000000000000000000000 : ℝ)) (γ := (27103967242523/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_18 half_4_18 half_6_17
  · have h := even_B_second_cross (u := 4) (t := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (73325568919/2500000000000 : ℝ)) (φ₂ := (33786742503/10000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_17
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_7_18 : AdmissibleExponent 18 14 (37338314575687/5000000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 5) (u := 4) (t := 7)
    (φ₁ := (156158948703/5000000000000 : ℝ)) (φ₂ := (9216334573/500000000000 : ℝ)) (χ := (510307049772945746154186449/80000000000000000000000000 : ℝ)) (γ := (63788381221619/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_6_18 half_5_18 half_7_17
  · have h := even_B_second_cross (u := 5) (t := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (156158948703/5000000000000 : ℝ)) (φ₂ := (9216334573/500000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/8 : ℝ)) (c := (5/8 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_17
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_8_18 : AdmissibleExponent 18 16 (1356500548199/156250000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 6) (u := 5) (t := 8)
    (φ₁ := (327510032867/10000000000000 : ℝ)) (φ₂ := (253236702767/10000000000000 : ℝ)) (χ := (1478522978937314217274863403/200000000000000000000000000 : ℝ)) (γ := (73926148946871/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_18 half_6_18 half_8_17
  · have h := even_A_second_cross (u := 6) (v := 8) (w := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (327510032867/10000000000000 : ℝ)) (φ₂ := (253236702767/10000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_17 half_8_17
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_19 : AdmissibleExponent 18 6 (30050869194263/10000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
    (φ := (484489625337/190484489625337 : ℝ)) half_4_18 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_19 : AdmissibleExponent 18 8 (20242244616531/5000000000000 : ℝ) := by
  have h := admissible_eight_B_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
    (φ := (139566968741/9639566968741 : ℝ)) half_3_19 half_6_18
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_19 : AdmissibleExponent 18 10 (25734835750467/5000000000000 : ℝ) := by
  apply first_stage_admissible_source (s := 3) (φ := (4666343913753/187166343913753 : ℝ)) (χ := (1861349232661775/374332687827506 : ℝ))
    (by norm_num : 0 < (18 : ℕ)) half_4_19 (by norm_num) (by norm_num)
  · have h := first_B_cross_power (u := 4) (t := 6)
      (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
      (φ := (4666343913753/187166343913753 : ℝ)) (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
      (by norm_num) (by norm_num) half_6_18
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_19 : AdmissibleExponent 18 12 (7861634601097/1250000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 4) (u := 3) (t := 6)
    (φ₁ := (916569437/31250000000 : ℝ)) (φ₂ := (33786511717/10000000000000 : ℝ)) (χ := (16939979995124932699184157/3125000000000000000000000 : ℝ)) (γ := (27103967992201/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_19 half_4_19 half_6_18
  · have h := even_B_second_cross (u := 4) (t := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (916569437/31250000000 : ℝ)) (φ₂ := (33786511717/10000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_18
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_7_19 : AdmissibleExponent 18 14 (18669156944371/2500000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 5) (u := 4) (t := 7)
    (φ₁ := (156158909379/5000000000000 : ℝ)) (φ₂ := (92163241197/5000000000000 : ℝ)) (χ := (498346743446325086024211/78125000000000000000000 : ℝ)) (γ := (15947095790283/2500000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_6_19 half_5_19 half_7_18
  · have h := even_B_second_cross (u := 5) (t := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (156158909379/5000000000000 : ℝ)) (φ₂ := (92163241197/5000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/8 : ℝ)) (c := (5/8 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_18
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_8_19 : AdmissibleExponent 18 16 (86816033083789/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 6) (u := 5) (t := 8)
    (φ₁ := (65501985997/2000000000000 : ℝ)) (φ₂ := (197841023/7812500000 : ℝ)) (χ := (1848153786658725668438531/250000000000000000000000 : ℝ)) (γ := (36963075733177/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_19 half_6_19 half_8_18
  · have h := even_A_second_cross (u := 6) (v := 8) (w := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (65501985997/2000000000000 : ℝ)) (φ₂ := (197841023/7812500000 : ℝ)) (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_18 half_8_18
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_20 : AdmissibleExponent 18 6 (30050869153181/10000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
    (φ := (242244616531/95242244616531 : ℝ)) half_4_19 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_20 : AdmissibleExponent 18 8 (40484489059013/10000000000000 : ℝ) := by
  have h := admissible_eight_B_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
    (φ := (1395669251207/96395669251207 : ℝ)) half_3_20 half_6_19
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_20 : AdmissibleExponent 18 10 (2573483559423/500000000000 : ℝ) := by
  apply first_stage_admissible_source (s := 3) (φ := (9332686440513/374332686440513 : ℝ)) (χ := (3722698447070001/748665372881026 : ℝ))
    (by norm_num : 0 < (18 : ℕ)) half_4_20 (by norm_num) (by norm_num)
  · have h := first_B_cross_power (u := 4) (t := 6)
      (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
      (φ := (9332686440513/374332686440513 : ℝ)) (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
      (by norm_num) (by norm_num) half_6_19
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_20 : AdmissibleExponent 18 12 (12578615277047/2000000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 4) (u := 3) (t := 6)
    (φ₁ := (293302195067/10000000000000 : ℝ)) (φ₂ := (16893204659/5000000000000 : ℝ)) (χ := (216831746598564293644437047/40000000000000000000000000 : ℝ)) (γ := (27103968324821/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_20 half_4_20 half_6_19
  · have h := even_B_second_cross (u := 4) (t := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (293302195067/10000000000000 : ℝ)) (φ₂ := (16893204659/5000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_19
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_7_20 : AdmissibleExponent 18 14 (14935325433579/2000000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 5) (u := 4) (t := 7)
    (φ₁ := (312317783863/10000000000000 : ℝ)) (φ₂ := (184326389631/10000000000000 : ℝ)) (χ := (510307072173491926022555617/80000000000000000000000000 : ℝ)) (γ := (63788384021687/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_6_20 half_5_20 half_7_19
  · have h := even_B_second_cross (u := 5) (t := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (312317783863/10000000000000 : ℝ)) (φ₂ := (184326389631/10000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/8 : ℝ)) (c := (5/8 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_19
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_8_20 : AdmissibleExponent 18 16 (86816032195971/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 6) (u := 5) (t := 8)
    (φ₁ := (327509884337/10000000000000 : ℝ)) (φ₂ := (253236423661/10000000000000 : ℝ)) (χ := (1478523051684680973497733367/200000000000000000000000000 : ℝ)) (γ := (14785230516847/2000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_20 half_6_20 half_8_19
  · have h := even_A_second_cross (u := 6) (v := 8) (w := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (327509884337/10000000000000 : ℝ)) (φ₂ := (253236423661/10000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_19 half_8_19
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_21 : AdmissibleExponent 18 6 (30050869134953/10000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
    (φ := (484489059013/190484489059013 : ℝ)) half_4_20 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_21 : AdmissibleExponent 18 8 (10121122245447/2500000000000 : ℝ) := by
  have h := admissible_eight_B_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
    (φ := (2791338115329/192791338115329 : ℝ)) half_3_21 half_6_20
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_21 : AdmissibleExponent 18 10 (6433708881227/1250000000000 : ℝ) := by
  apply first_stage_admissible_source (s := 3) (φ := (4666342912553/187166342912553 : ℝ)) (χ := (930674609742737/187166342912553 : ℝ))
    (by norm_num : 0 < (18 : ℕ)) half_4_21 (by norm_num) (by norm_num)
  · have h := first_B_cross_power (u := 4) (t := 6)
      (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
      (φ := (4666342912553/187166342912553 : ℝ)) (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
      (by norm_num) (by norm_num) half_6_20
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_21 : AdmissibleExponent 18 12 (15723269049329/2500000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 4) (u := 3) (t := 6)
    (φ₁ := (146651092037/5000000000000 : ℝ)) (φ₂ := (8446590971/2500000000000 : ℝ)) (χ := (542079369448197433756061391/100000000000000000000000000 : ℝ)) (γ := (54207936944827/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_21 half_4_21 half_6_20
  · have h := even_B_second_cross (u := 4) (t := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (146651092037/5000000000000 : ℝ)) (φ₂ := (8446590971/2500000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_20
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_7_21 : AdmissibleExponent 18 14 (7467662689743/1000000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 5) (u := 4) (t := 7)
    (φ₁ := (312317768379/10000000000000 : ℝ)) (φ₂ := (184326348473/10000000000000 : ℝ)) (χ := (255153537614076796128099177/40000000000000000000000000 : ℝ)) (γ := (63788384403527/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_6_21 half_5_21 half_7_20
  · have h := even_B_second_cross (u := 5) (t := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (312317768379/10000000000000 : ℝ)) (φ₂ := (184326348473/10000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/8 : ℝ)) (c := (5/8 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_20
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_8_21 : AdmissibleExponent 18 16 (86816031802059/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 6) (u := 5) (t := 8)
    (φ₁ := (163754932041/5000000000000 : ℝ)) (φ₂ := (253236385601/10000000000000 : ℝ)) (χ := (2957046123210293776542118421/400000000000000000000000000 : ℝ)) (γ := (36963076540131/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_21 half_6_21 half_8_20
  · have h := even_A_second_cross (u := 6) (v := 8) (w := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (163754932041/5000000000000 : ℝ)) (φ₂ := (253236385601/10000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_20 half_8_20
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_22 : AdmissibleExponent 18 6 (6010173825373/2000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
    (φ := (121122245447/47621122245447 : ℝ)) half_4_21 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_22 : AdmissibleExponent 18 8 (10121122236881/2500000000000 : ℝ) := by
  have h := admissible_eight_B_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
    (φ := (1395668971793/96395668971793 : ℝ)) half_3_22 half_6_21
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_22 : AdmissibleExponent 18 10 (51469670988301/10000000000000 : ℝ) := by
  apply first_stage_admissible_source (s := 3) (φ := (466634277603/18716634277603 : ℝ)) (χ := (930674608844373/187166342776030 : ℝ))
    (by norm_num : 0 < (18 : ℕ)) half_4_22 (by norm_num) (by norm_num)
  · have h := first_B_cross_power (u := 4) (t := 6)
      (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
      (φ := (466634277603/18716634277603 : ℝ)) (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
      (by norm_num) (by norm_num) half_6_21
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_22 : AdmissibleExponent 18 12 (3930817257121/625000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 4) (u := 3) (t := 6)
    (φ₁ := (293302179197/10000000000000 : ℝ)) (φ₂ := (1351453749/400000000000 : ℝ)) (χ := (542079370757882571905851801/100000000000000000000000000 : ℝ)) (γ := (54207937075791/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_22 half_4_22 half_6_21
  · have h := even_B_second_cross (u := 4) (t := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (293302179197/10000000000000 : ℝ)) (φ₂ := (1351453749/400000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_21
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_7_22 : AdmissibleExponent 18 14 (74676626777419/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 5) (u := 4) (t := 7)
    (φ₁ := (31231776151/1000000000000 : ℝ)) (φ₂ := (184326330211/10000000000000 : ℝ)) (χ := (1020614153166864957087346461/160000000000000000000000000 : ℝ)) (γ := (6378838457293/1000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_6_22 half_5_22 half_7_21
  · have h := even_B_second_cross (u := 5) (t := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (31231776151/1000000000000 : ℝ)) (φ₂ := (184326330211/10000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/8 : ℝ)) (c := (5/8 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_21
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_8_22 : AdmissibleExponent 18 16 (86816031627277/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 6) (u := 5) (t := 8)
    (φ₁ := (40938731887/1250000000000 : ℝ)) (φ₂ := (126618184357/5000000000000 : ℝ)) (χ := (295704613201302609910152563/40000000000000000000000000 : ℝ)) (γ := (36963076650163/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_22 half_6_22 half_8_21
  · have h := even_A_second_cross (u := 6) (v := 8) (w := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (40938731887/1250000000000 : ℝ)) (φ₂ := (126618184357/5000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_21 half_8_21
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_23 : AdmissibleExponent 18 6 (30050869123277/10000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
    (φ := (121122236881/47621122236881 : ℝ)) half_4_22 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_23 : AdmissibleExponent 18 8 (40484488932321/10000000000000 : ℝ) := by
  have h := admissible_eight_B_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
    (φ := (1395668933691/96395668933691 : ℝ)) half_3_23 half_6_22
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_23 : AdmissibleExponent 18 10 (51469670961007/10000000000000 : ℝ) := by
  apply first_stage_admissible_source (s := 3) (φ := (9332685430909/374332685430909 : ℝ)) (χ := (3722698433783069/748665370861818 : ℝ))
    (by norm_num : 0 < (18 : ℕ)) half_4_23 (by norm_num) (by norm_num)
  · have h := first_B_cross_power (u := 4) (t := 6)
      (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
      (φ := (9332685430909/374332685430909 : ℝ)) (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
      (by norm_num) (by norm_num) half_6_22
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_23 : AdmissibleExponent 18 12 (31446538038471/5000000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 4) (u := 3) (t := 6)
    (φ₁ := (293302177033/10000000000000 : ℝ)) (φ₂ := (33786334781/10000000000000 : ℝ)) (χ := (542079371338913404670424761/100000000000000000000000000 : ℝ)) (γ := (54207937133899/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_23 half_4_23 half_6_22
  · have h := even_B_second_cross (u := 4) (t := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (293302177033/10000000000000 : ℝ)) (φ₂ := (33786334781/10000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_22
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_7_23 : AdmissibleExponent 18 14 (74676626724173/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 5) (u := 4) (t := 7)
    (φ₁ := (156158879231/5000000000000 : ℝ)) (φ₂ := (46081580527/2500000000000 : ℝ)) (χ := (102061415436960497340229211/16000000000000000000000000 : ℝ)) (γ := (63788384648101/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_6_23 half_5_23 half_7_22
  · have h := even_B_second_cross (u := 5) (t := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (156158879231/5000000000000 : ℝ)) (φ₂ := (46081580527/2500000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/8 : ℝ)) (c := (5/8 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_22
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_8_23 : AdmissibleExponent 18 16 (21704007887431/2500000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 6) (u := 5) (t := 8)
    (φ₁ := (327509851109/10000000000000 : ℝ)) (φ₂ := (253236361221/10000000000000 : ℝ)) (χ := (295704613591882218781482377/40000000000000000000000000 : ℝ)) (γ := (73926153397971/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_23 half_6_23 half_8_22
  · have h := even_A_second_cross (u := 6) (v := 8) (w := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (327509851109/10000000000000 : ℝ)) (φ₂ := (253236361221/10000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_22 half_8_22
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_24 : AdmissibleExponent 18 6 (6010173824337/2000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
    (φ := (484488932321/190484488932321 : ℝ)) half_4_23 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_24 : AdmissibleExponent 18 8 (5060561115697/1250000000000 : ℝ) := by
  have h := admissible_eight_B_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
    (φ := (697834458393/48197834458393 : ℝ)) half_3_24 half_6_23
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_24 : AdmissibleExponent 18 10 (25734835474449/5000000000000 : ℝ) := by
  apply first_stage_admissible_source (s := 3) (φ := (2333171344289/93583171344289 : ℝ)) (χ := (465337304134459/93583171344289 : ℝ))
    (by norm_num : 0 < (18 : ℕ)) half_4_24 (by norm_num) (by norm_num)
  · have h := first_B_cross_power (u := 4) (t := 6)
      (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
      (φ := (2333171344289/93583171344289 : ℝ)) (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
      (by norm_num) (by norm_num) half_6_23
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_24 : AdmissibleExponent 18 12 (31446538030263/5000000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 4) (u := 3) (t := 6)
    (φ₁ := (293302176073/10000000000000 : ℝ)) (φ₂ := (8446582703/2500000000000 : ℝ)) (χ := (54207937159675486210307513/10000000000000000000000000 : ℝ)) (γ := (54207937159681/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_24 half_4_24 half_6_23
  · have h := even_B_second_cross (u := 4) (t := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (293302176073/10000000000000 : ℝ)) (φ₂ := (8446582703/2500000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_23
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_7_24 : AdmissibleExponent 18 14 (1493532534011/200000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 5) (u := 4) (t := 7)
    (φ₁ := (312317757109/10000000000000 : ℝ)) (φ₂ := (184326318513/10000000000000 : ℝ)) (χ := (127576769362914616986346459/20000000000000000000000000 : ℝ)) (γ := (3189419234073/500000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_6_24 half_5_24 half_7_23
  · have h := even_B_second_cross (u := 5) (t := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (312317757109/10000000000000 : ℝ)) (φ₂ := (184326318513/10000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/8 : ℝ)) (c := (5/8 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_23
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_8_24 : AdmissibleExponent 18 16 (86816031515321/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 6) (u := 5) (t := 8)
    (φ₁ := (327509849339/10000000000000 : ℝ)) (φ₂ := (253236357897/10000000000000 : ℝ)) (χ := (184815383603250663435761963/25000000000000000000000000 : ℝ)) (γ := (14785230688261/2000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_24 half_6_24 half_8_23
  · have h := even_A_second_cross (u := 6) (v := 8) (w := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (327509849339/10000000000000 : ℝ)) (φ₂ := (253236357897/10000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_23 half_8_23
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_25 : AdmissibleExponent 18 6 (15025434560489/5000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
    (φ := (60561115697/23810561115697 : ℝ)) half_4_24 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_25 : AdmissibleExponent 18 8 (40484488922583/10000000000000 : ℝ) := by
  have h := admissible_eight_B_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
    (φ := (279133781857/19279133781857 : ℝ)) half_3_25 half_6_24
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_25 : AdmissibleExponent 18 10 (12867417735881/2500000000000 : ℝ) := by
  apply first_stage_admissible_source (s := 3) (φ := (9332685353303/374332685353303 : ℝ)) (χ := (3722698432761771/748665370706606 : ℝ))
    (by norm_num : 0 < (18 : ℕ)) half_4_25 (by norm_num) (by norm_num)
  · have h := first_B_cross_power (u := 4) (t := 6)
      (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
      (φ := (9332685353303/374332685353303 : ℝ)) (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
      (by norm_num) (by norm_num) half_6_24
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_25 : AdmissibleExponent 18 12 (62893076053241/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 4) (u := 3) (t := 6)
    (φ₁ := (293302175647/10000000000000 : ℝ)) (φ₂ := (33786329051/10000000000000 : ℝ)) (χ := (542079371711194605516260971/100000000000000000000000000 : ℝ)) (γ := (677599214639/125000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_25 half_4_25 half_6_24
  · have h := even_B_second_cross (u := 4) (t := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (293302175647/10000000000000 : ℝ)) (φ₂ := (33786329051/10000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_24
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_7_25 : AdmissibleExponent 18 14 (18669156672517/2500000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 5) (u := 4) (t := 7)
    (φ₁ := (312317756509/10000000000000 : ℝ)) (φ₂ := (92163158459/5000000000000 : ℝ)) (χ := (1020614155140084171200524933/160000000000000000000000000 : ℝ)) (γ := (996693510879/156250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_6_25 half_5_25 half_7_24
  · have h := even_B_second_cross (u := 5) (t := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (312317756509/10000000000000 : ℝ)) (φ₂ := (92163158459/5000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/8 : ℝ)) (c := (5/8 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_24
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_8_25 : AdmissibleExponent 18 16 (21704007875013/2500000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 6) (u := 5) (t := 8)
    (φ₁ := (65501969711/2000000000000 : ℝ)) (φ₂ := (126618178211/5000000000000 : ℝ)) (χ := (2957046138420301095854142149/400000000000000000000000000 : ℝ)) (γ := (18481538365127/2500000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_25 half_6_25 half_8_24
  · have h := even_A_second_cross (u := 6) (v := 8) (w := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (65501969711/2000000000000 : ℝ)) (φ₂ := (126618178211/5000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_24 half_8_24
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_26 : AdmissibleExponent 18 6 (6010173824133/2000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
    (φ := (484488922583/190484488922583 : ℝ)) half_4_25 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_26 : AdmissibleExponent 18 8 (8096897784251/2000000000000 : ℝ) := by
  have h := admissible_eight_B_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
    (φ := (2791337811911/192791337811911 : ℝ)) half_3_26 half_6_25
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_26 : AdmissibleExponent 18 10 (2573483547057/500000000000 : ℝ) := by
  apply first_stage_admissible_source (s := 3) (φ := (9332685342717/374332685342717 : ℝ)) (χ := (3722698432622483/748665370685434 : ℝ))
    (by norm_num : 0 < (18 : ℕ)) half_4_26 (by norm_num) (by norm_num)
  · have h := first_B_cross_power (u := 4) (t := 6)
      (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
      (φ := (9332685342717/374332685342717 : ℝ)) (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
      (by norm_num) (by norm_num) half_6_25
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_26 : AdmissibleExponent 18 12 (62893076050009/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 4) (u := 3) (t := 6)
    (φ₁ := (146651087729/5000000000000 : ℝ)) (φ₂ := (3378632827/1000000000000 : ℝ)) (χ := (16939980367559454311965721/3125000000000000000000000 : ℝ)) (γ := (10841587435239/2000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_26 half_4_26 half_6_25
  · have h := even_B_second_cross (u := 4) (t := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (146651087729/5000000000000 : ℝ)) (φ₂ := (3378632827/1000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_25
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_7_26 : AdmissibleExponent 18 14 (14935325337083/2000000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 5) (u := 4) (t := 7)
    (φ₁ := (312317756243/10000000000000 : ℝ)) (φ₂ := (18432631621/1000000000000 : ℝ)) (χ := (255153538811279061059683111/40000000000000000000000000 : ℝ)) (γ := (3189419235141/500000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_6_26 half_5_26 half_7_25
  · have h := even_B_second_cross (u := 5) (t := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (312317756243/10000000000000 : ℝ)) (φ₂ := (18432631621/1000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/8 : ℝ)) (c := (5/8 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_25
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_8_26 : AdmissibleExponent 18 16 (86816031493279/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 6) (u := 5) (t := 8)
    (φ₁ := (163754924103/5000000000000 : ℝ)) (φ₂ := (31654544471/1250000000000 : ℝ)) (χ := (369630767345199097006147507/50000000000000000000000000 : ℝ)) (γ := (36963076734523/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_26 half_6_26 half_8_25
  · have h := even_A_second_cross (u := 6) (v := 8) (w := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (163754924103/5000000000000 : ℝ)) (φ₂ := (31654544471/1250000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_25 half_8_25
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_27 : AdmissibleExponent 18 6 (15025434560263/5000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
    (φ := (96897784251/38096897784251 : ℝ)) half_4_26 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_27 : AdmissibleExponent 18 8 (20242244460333/5000000000000 : ℝ) := by
  have h := admissible_eight_B_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
    (φ := (2791337808957/192791337808957 : ℝ)) half_3_27 half_6_26
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_27 : AdmissibleExponent 18 10 (25734835470041/5000000000000 : ℝ) := by
  apply first_stage_admissible_source (s := 3) (φ := (466634266901/18716634266901 : ℝ)) (χ := (1861349216280349/374332685338020 : ℝ))
    (by norm_num : 0 < (18 : ℕ)) half_4_27 (by norm_num) (by norm_num)
  · have h := first_B_cross_power (u := 4) (t := 6)
      (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
      (φ := (466634266901/18716634266901 : ℝ)) (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
      (by norm_num) (by norm_num) half_6_26
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_27 : AdmissibleExponent 18 12 (982704313259/156250000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 4) (u := 3) (t := 6)
    (φ₁ := (146651087687/5000000000000 : ℝ)) (φ₂ := (33786327923/10000000000000 : ℝ)) (χ := (1084158743568978155975159137/200000000000000000000000000 : ℝ)) (γ := (54207937178451/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_27 half_4_27 half_6_26
  · have h := even_B_second_cross (u := 4) (t := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (146651087687/5000000000000 : ℝ)) (φ₂ := (33786327923/10000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_26
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_7_27 : AdmissibleExponent 18 14 (74676626683349/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 5) (u := 4) (t := 7)
    (φ₁ := (2498542049/80000000000 : ℝ)) (φ₂ := (23040789487/1250000000000 : ℝ)) (χ := (1020614155291694540146553141/160000000000000000000000000 : ℝ)) (γ := (63788384705731/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_6_27 half_5_27 half_7_26
  · have h := even_B_second_cross (u := 5) (t := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (2498542049/80000000000 : ℝ)) (φ₂ := (23040789487/1250000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/8 : ℝ)) (c := (5/8 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_26
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_8_27 : AdmissibleExponent 18 16 (86816031490269/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 6) (u := 5) (t := 8)
    (φ₁ := (81877462013/2500000000000 : ℝ)) (φ₂ := (253236355477/10000000000000 : ℝ)) (χ := (2957046138913052360211255227/400000000000000000000000000 : ℝ)) (γ := (73926153472827/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_27 half_6_27 half_8_26
  · have h := even_A_second_cross (u := 6) (v := 8) (w := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (81877462013/2500000000000 : ℝ)) (φ₂ := (253236355477/10000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_26 half_8_26
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_28 : AdmissibleExponent 18 6 (1878179320029/625000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
    (φ := (242244460333/95242244460333 : ℝ)) half_4_27 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_28 : AdmissibleExponent 18 8 (10121122230101/2500000000000 : ℝ) := by
  have h := admissible_eight_B_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
    (φ := (4591016131/317091016131 : ℝ)) half_3_28 half_6_27
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_28 : AdmissibleExponent 18 10 (12867417734903/2500000000000 : ℝ) := by
  apply first_stage_admissible_source (s := 3) (φ := (466634266797/18716634266797 : ℝ)) (χ := (930674608133313/187166342667970 : ℝ))
    (by norm_num : 0 < (18 : ℕ)) half_4_28 (by norm_num) (by norm_num)
  · have h := first_B_cross_power (u := 4) (t := 6)
      (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
      (φ := (466634266797/18716634266797 : ℝ)) (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
      (by norm_num) (by norm_num) half_6_27
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_28 : AdmissibleExponent 18 12 (62893076047937/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 4) (u := 3) (t := 6)
    (φ₁ := (293302175337/10000000000000 : ℝ)) (φ₂ := (33786327769/10000000000000 : ℝ)) (χ := (542079371794457277192362243/100000000000000000000000000 : ℝ)) (γ := (27103968589723/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_28 half_4_28 half_6_27
  · have h := even_B_second_cross (u := 4) (t := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (293302175337/10000000000000 : ℝ)) (φ₂ := (33786327769/10000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_27
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_7_28 : AdmissibleExponent 18 14 (74676626682431/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 5) (u := 4) (t := 7)
    (φ₁ := (312317756073/10000000000000 : ℝ)) (φ₂ := (184326315757/10000000000000 : ℝ)) (χ := (102061415531214130081797773/16000000000000000000000000 : ℝ)) (γ := (63788384707009/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_6_28 half_5_28 half_7_27
  · have h := even_B_second_cross (u := 5) (t := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (312317756073/10000000000000 : ℝ)) (φ₂ := (184326315757/10000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/8 : ℝ)) (c := (5/8 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_27
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_8_28 : AdmissibleExponent 18 16 (10852003936117/1250000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 6) (u := 5) (t := 8)
    (φ₁ := (327509847983/10000000000000 : ℝ)) (φ₂ := (63309088837/2500000000000 : ℝ)) (χ := (2957046138980545221134341883/400000000000000000000000000 : ℝ)) (γ := (36963076737257/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_28 half_6_28 half_8_27
  · have h := even_A_second_cross (u := 6) (v := 8) (w := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (327509847983/10000000000000 : ℝ)) (φ₂ := (63309088837/2500000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_27 half_8_27
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_29 : AdmissibleExponent 18 6 (7512717280109/2500000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
    (φ := (121122230101/47621122230101 : ℝ)) half_4_28 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_29 : AdmissibleExponent 18 8 (40484488920287/10000000000000 : ℝ) := by
  have h := admissible_eight_B_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
    (φ := (558267561413/38558267561413 : ℝ)) half_3_29 half_6_28
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_29 : AdmissibleExponent 18 10 (51469670939403/10000000000000 : ℝ) := by
  apply first_stage_admissible_source (s := 3) (φ := (9332685335013/374332685335013 : ℝ)) (χ := (3722698432521003/748665370670026 : ℝ))
    (by norm_num : 0 < (18 : ℕ)) half_4_29 (by norm_num) (by norm_num)
  · have h := first_B_cross_power (u := 4) (t := 6)
      (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
      (φ := (9332685335013/374332685335013 : ℝ)) (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
      (by norm_num) (by norm_num) half_6_28
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_29 : AdmissibleExponent 18 12 (12578615209531/2000000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 4) (u := 3) (t := 6)
    (φ₁ := (293302175321/10000000000000 : ℝ)) (φ₂ := (33786327701/10000000000000 : ℝ)) (χ := (67759921474849569375277213/12500000000000000000000000 : ℝ)) (γ := (1355198429497/250000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_29 half_4_29 half_6_28
  · have h := even_B_second_cross (u := 4) (t := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (293302175321/10000000000000 : ℝ)) (φ₂ := (33786327701/10000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_28
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_7_29 : AdmissibleExponent 18 14 (74676626682027/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 5) (u := 4) (t := 7)
    (φ₁ := (312317756049/10000000000000 : ℝ)) (φ₂ := (36865263139/2000000000000 : ℝ)) (χ := (1993387022112420910300343/312500000000000000000000 : ℝ)) (γ := (63788384707599/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_6_29 half_5_29 half_7_28
  · have h := even_B_second_cross (u := 5) (t := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (312317756049/10000000000000 : ℝ)) (φ₂ := (36865263139/2000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/8 : ℝ)) (c := (5/8 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_28
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_8_29 : AdmissibleExponent 18 16 (43408015744171/5000000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 6) (u := 5) (t := 8)
    (φ₁ := (327509847953/10000000000000 : ℝ)) (φ₂ := (253236355291/10000000000000 : ℝ)) (χ := (92407691844059581544377339/12500000000000000000000000 : ℝ)) (γ := (4620384592203/625000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_29 half_6_29 half_8_28
  · have h := even_A_second_cross (u := 6) (v := 8) (w := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (327509847953/10000000000000 : ℝ)) (φ₂ := (253236355291/10000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_28 half_8_28
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_3_30 : AdmissibleExponent 18 6 (3756358640053/1250000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
    (φ := (484488920287/190484488920287 : ℝ)) half_4_29 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_30 : AdmissibleExponent 18 8 (10121122230059/2500000000000 : ℝ) := by
  have h := admissible_eight_B_supported (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
    (φ := (2791337806807/192791337806807 : ℝ)) half_3_30 half_6_29
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_30 : AdmissibleExponent 18 10 (51469670939311/10000000000000 : ℝ) := by
  apply first_stage_admissible_source (s := 3) (φ := (4666342667301/187166342667301 : ℝ)) (χ := (930674608128909/187166342667301 : ℝ))
    (by norm_num : 0 < (18 : ℕ)) half_4_30 (by norm_num) (by norm_num)
  · have h := first_B_cross_power (u := 4) (t := 6)
      (by simp [SupportedFirstDegree] : SupportedFirstDegree 18)
      (φ := (4666342667301/187166342667301 : ℝ)) (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
      (by norm_num) (by norm_num) half_6_29
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_30 : AdmissibleExponent 18 12 (62893076047531/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 4) (u := 3) (t := 6)
    (φ₁ := (293302175313/10000000000000 : ℝ)) (φ₂ := (3378632767/1000000000000 : ℝ)) (χ := (542079371800931612901637907/100000000000000000000000000 : ℝ)) (γ := (27103968590047/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_30 half_4_30 half_6_29
  · have h := even_B_second_cross (u := 4) (t := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (293302175313/10000000000000 : ℝ)) (φ₂ := (3378632767/1000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_29
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_7_30 : AdmissibleExponent 18 14 (14935325336369/2000000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 5) (u := 4) (t := 7)
    (φ₁ := (312317756039/10000000000000 : ℝ)) (φ₂ := (46081578917/2500000000000 : ℝ)) (χ := (510307077662708352908730103/80000000000000000000000000 : ℝ)) (γ := (12757676941569/2000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_6_30 half_5_30 half_7_29
  · have h := even_B_second_cross (u := 5) (t := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (312317756039/10000000000000 : ℝ)) (φ₂ := (46081578917/2500000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/8 : ℝ)) (c := (5/8 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_29
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_8_30 : AdmissibleExponent 18 16 (43408015744041/5000000000000 : ℝ) := by
  apply two_stage_admissible (k := 18) (s := 6) (u := 5) (t := 8)
    (φ₁ := (327509847939/10000000000000 : ℝ)) (φ₂ := (126618177633/5000000000000 : ℝ)) (χ := (295704613902316897483839167/40000000000000000000000000 : ℝ)) (γ := (36963076737793/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_30 half_6_30 half_8_29
  · have h := even_A_second_cross (u := 6) (v := 8) (w := 8)
      9 (by simp [FirstDifferenceSecond.supportedHalfDegree])
      (φ₁ := (327509847939/10000000000000 : ℝ)) (φ₂ := (126618177633/5000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_8_29 half_8_29
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

theorem degree18_half_3 : AdmissibleExponent 18 6 (3756358640053/1250000000000 : ℝ) := half_3_30

theorem source18_entry_3 : AdmissibleExponent 18 6 (Certificate.coefficientSource9[3]! : ℝ) := by
  apply admissibleExponent_mono degree18_half_3
  norm_num [Certificate.coefficientSource9,Certificate.Q]

#print axioms source18_entry_3

theorem degree18_half_4 : AdmissibleExponent 18 8 (10121122230059/2500000000000 : ℝ) := half_4_30

theorem source18_entry_4 : AdmissibleExponent 18 8 (Certificate.coefficientSource9[4]! : ℝ) := by
  apply admissibleExponent_mono degree18_half_4
  norm_num [Certificate.coefficientSource9,Certificate.Q]

#print axioms source18_entry_4

theorem degree18_half_5 : AdmissibleExponent 18 10 (51469670939311/10000000000000 : ℝ) := half_5_30

theorem source18_entry_5 : AdmissibleExponent 18 10 (Certificate.coefficientSource9[5]! : ℝ) := by
  apply admissibleExponent_mono degree18_half_5
  norm_num [Certificate.coefficientSource9,Certificate.Q]

#print axioms source18_entry_5

theorem degree18_half_6 : AdmissibleExponent 18 12 (62893076047531/10000000000000 : ℝ) := half_6_30

theorem source18_entry_6 : AdmissibleExponent 18 12 (Certificate.coefficientSource9[6]! : ℝ) := by
  apply admissibleExponent_mono degree18_half_6
  norm_num [Certificate.coefficientSource9,Certificate.Q]

#print axioms source18_entry_6

theorem degree18_half_7 : AdmissibleExponent 18 14 (14935325336369/2000000000000 : ℝ) := half_7_30

theorem source18_entry_7 : AdmissibleExponent 18 14 (Certificate.coefficientSource9[7]! : ℝ) := by
  apply admissibleExponent_mono degree18_half_7
  norm_num [Certificate.coefficientSource9,Certificate.Q]

#print axioms source18_entry_7

theorem degree18_half_8 : AdmissibleExponent 18 16 (43408015744041/5000000000000 : ℝ) := half_8_30

theorem source18_entry_8 : AdmissibleExponent 18 16 (Certificate.coefficientSource9[8]! : ℝ) := by
  apply admissibleExponent_mono degree18_half_8
  norm_num [Certificate.coefficientSource9,Certificate.Q]

#print axioms source18_entry_8

end Waring.SeedCompletionEven18SecondSeeds
