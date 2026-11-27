import Waring.SeedCompletionTwoStageUpdate
import Waring.NinthFirstSeeds

/-! # Unconditional degree-nine source seeds at moments 10, 12 and 14

Twenty first-stage refinements retain enough precision for the published
next entries. Twenty-three exact finite two-stage rounds then apply the
proved actual second/fourth terminal moments and absorbed recurrence.
Every seed, Holder weight, parameter range and rounding is kernel-checked.
No limiting exponent or published high-order seed estimate is assumed.
-/
noncomputable section
namespace Waring.SeedCompletionNinthSecondSeeds
open SmoothMoments FirstStageTransport SeedCompletionSecondScales

private theorem half_3_00 : AdmissibleExponent 9 6 (7589513/2500000 : ℝ) := NinthFirstSeeds.source9_six
private theorem half_4_00 : AdmissibleExponent 9 8 (20911447/5000000 : ℝ) := NinthFirstSeeds.source9_eight

private theorem half_3_01 : AdmissibleExponent 9 6 (30358051893517/10000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 9)
    (φ := (911447/50911447 : ℝ)) half_4_00 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_01 : AdmissibleExponent 9 8 (41822893503639/10000000000000 : ℝ) := by
  have h := admissible_eight_A_ninth (φ := (389902067387/7889902067387 : ℝ)) half_3_01 half_4_00
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_3_02 : AdmissibleExponent 9 6 (30358051797767/10000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 9)
    (φ := (1822893503639/101822893503639 : ℝ)) half_4_01 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_02 : AdmissibleExponent 9 8 (8364578660579/2000000000000 : ℝ) := by
  have h := admissible_eight_A_ninth (φ := (14036473319849/284036473319849 : ℝ)) half_3_02 half_4_01
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_3_03 : AdmissibleExponent 9 6 (30358051759043/10000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 9)
    (φ := (364578660579/20364578660579 : ℝ)) half_4_02 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_03 : AdmissibleExponent 9 8 (10455723305427/2500000000000 : ℝ) := by
  have h := admissible_eight_A_ninth (φ := (14036472872513/284036472872513 : ℝ)) half_3_03 half_4_02
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_3_04 : AdmissibleExponent 9 6 (15179025871691/5000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 9)
    (φ := (455723305427/25455723305427 : ℝ)) half_4_03 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_04 : AdmissibleExponent 9 8 (41822893188873/10000000000000 : ℝ) := by
  have h := admissible_eight_A_ninth (φ := (129967339737/2629967339737 : ℝ)) half_3_04 half_4_03
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_3_05 : AdmissibleExponent 9 6 (3794756467131/1250000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 9)
    (φ := (1822893188873/101822893188873 : ℝ)) half_4_04 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_05 : AdmissibleExponent 9 8 (20911446587797/5000000000000 : ℝ) := by
  have h := admissible_eight_A_ninth (φ := (14036472618427/284036472618427 : ℝ)) half_3_05 half_4_04
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_3_06 : AdmissibleExponent 9 6 (15179025867243/5000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 9)
    (φ := (911446587797/50911446587797 : ℝ)) half_4_05 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_06 : AdmissibleExponent 9 8 (41822893170223/10000000000000 : ℝ) := by
  have h := admissible_eight_A_ninth (φ := (7018236294419/142018236294419 : ℝ)) half_3_06 half_4_05
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_3_07 : AdmissibleExponent 9 6 (607161034669/200000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 9)
    (φ := (1822893170223/101822893170223 : ℝ)) half_4_06 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_07 : AdmissibleExponent 9 8 (41822893168051/10000000000000 : ℝ) := by
  have h := admissible_eight_A_ninth (φ := (14036472576869/284036472576869 : ℝ)) half_3_07 half_4_06
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_3_08 : AdmissibleExponent 9 6 (30358051733031/10000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 9)
    (φ := (1822893168051/101822893168051 : ℝ)) half_4_07 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_08 : AdmissibleExponent 9 8 (41822893167173/10000000000000 : ℝ) := by
  have h := admissible_eight_A_ninth (φ := (14036472572029/284036472572029 : ℝ)) half_3_08 half_4_07
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_3_09 : AdmissibleExponent 9 6 (15179025866431/5000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 9)
    (φ := (1822893167173/101822893167173 : ℝ)) half_4_08 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_09 : AdmissibleExponent 9 8 (20911446583409/5000000000000 : ℝ) := by
  have h := admissible_eight_A_ninth (φ := (14036472570071/284036472570071 : ℝ)) half_3_09 half_4_08
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_3_10 : AdmissibleExponent 9 6 (30358051732793/10000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 9)
    (φ := (911446583409/50911446583409 : ℝ)) half_4_09 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_10 : AdmissibleExponent 9 8 (20911446583337/5000000000000 : ℝ) := by
  have h := admissible_eight_A_ninth (φ := (7018236284641/142018236284641 : ℝ)) half_3_10 half_4_09
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_3_11 : AdmissibleExponent 9 6 (15179025866383/5000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 9)
    (φ := (911446583337/50911446583337 : ℝ)) half_4_10 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_11 : AdmissibleExponent 9 8 (5227861645827/1250000000000 : ℝ) := by
  have h := admissible_eight_A_ninth (φ := (7018236284479/142018236284479 : ℝ)) half_3_11 half_4_10
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_3_12 : AdmissibleExponent 9 6 (15179025866377/5000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 9)
    (φ := (227861645827/12727861645827 : ℝ)) half_4_11 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_12 : AdmissibleExponent 9 8 (10210667277/2441406250 : ℝ) := by
  have h := admissible_eight_A_ninth (φ := (13707492743/277379367743 : ℝ)) half_3_12 half_4_11
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_3_13 : AdmissibleExponent 9 6 (121432206931/40000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 9)
    (φ := (445042277/24859104777 : ℝ)) half_4_12 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_13 : AdmissibleExponent 9 8 (41822893166583/10000000000000 : ℝ) := by
  have h := admissible_eight_A_ninth (φ := (584853023699/11834853023699 : ℝ)) half_3_13 half_4_12
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_3_14 : AdmissibleExponent 9 6 (7589512933187/2500000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 9)
    (φ := (1822893166583/101822893166583 : ℝ)) half_4_13 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_14 : AdmissibleExponent 9 8 (41822893166579/10000000000000 : ℝ) := by
  have h := admissible_eight_A_ninth (φ := (14036472568757/284036472568757 : ℝ)) half_3_14 half_4_13
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_3_15 : AdmissibleExponent 9 6 (30358051732747/10000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 9)
    (φ := (1822893166579/101822893166579 : ℝ)) half_4_14 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_15 : AdmissibleExponent 9 8 (41822893166577/10000000000000 : ℝ) := by
  have h := admissible_eight_A_ninth (φ := (4678824189583/94678824189583 : ℝ)) half_3_15 half_4_14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_3_16 : AdmissibleExponent 9 6 (30358051732747/10000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 9)
    (φ := (1822893166577/101822893166577 : ℝ)) half_4_15 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_16 : AdmissibleExponent 9 8 (41822893166577/10000000000000 : ℝ) := by
  have h := admissible_eight_A_ninth (φ := (4678824189581/94678824189581 : ℝ)) half_3_16 half_4_15
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_3_17 : AdmissibleExponent 9 6 (30358051732747/10000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 9)
    (φ := (1822893166577/101822893166577 : ℝ)) half_4_16 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_17 : AdmissibleExponent 9 8 (41822893166577/10000000000000 : ℝ) := by
  have h := admissible_eight_A_ninth (φ := (4678824189581/94678824189581 : ℝ)) half_3_17 half_4_16
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_3_18 : AdmissibleExponent 9 6 (30358051732747/10000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 9)
    (φ := (1822893166577/101822893166577 : ℝ)) half_4_17 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_18 : AdmissibleExponent 9 8 (41822893166577/10000000000000 : ℝ) := by
  have h := admissible_eight_A_ninth (φ := (4678824189581/94678824189581 : ℝ)) half_3_18 half_4_17
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_3_19 : AdmissibleExponent 9 6 (30358051732747/10000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 9)
    (φ := (1822893166577/101822893166577 : ℝ)) half_4_18 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_19 : AdmissibleExponent 9 8 (41822893166577/10000000000000 : ℝ) := by
  have h := admissible_eight_A_ninth (φ := (4678824189581/94678824189581 : ℝ)) half_3_19 half_4_18
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_3_20 : AdmissibleExponent 9 6 (30358051732747/10000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 9)
    (φ := (1822893166577/101822893166577 : ℝ)) half_4_19 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_4_20 : AdmissibleExponent 9 8 (41822893166577/10000000000000 : ℝ) := by
  have h := admissible_eight_A_ninth (φ := (4678824189581/94678824189581 : ℝ)) half_3_20 half_4_19
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_00 : AdmissibleExponent 9 10 (56064793925847/10000000000000 : ℝ) := by
  have h := endpoint_admissible (s := 3) (by norm_num : 0 < (9 : ℕ))
    half_4_20 (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_6_00 : AdmissibleExponent 9 12 (35473241744821/5000000000000 : ℝ) := by
  have h := endpoint_admissible (s := 4) (by norm_num : 0 < (9 : ℕ))
    half_5_00 (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_7_00 : AdmissibleExponent 9 14 (10799609276627/1250000000000 : ℝ) := by
  have h := endpoint_admissible (s := 5) (by norm_num : 0 < (9 : ℕ))
    half_6_00 (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_5_01 : AdmissibleExponent 9 10 (54811370776931/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 9) (s := 3) (u := 2) (t := 5)
    (φ₁ := (782793107763/10000000000000 : ℝ)) (φ₂ := (103272759973/2000000000000 : ℝ)) (χ := (101670208523586967638901353/25000000000000000000000000 : ℝ)) (γ := (10167020852359/2500000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_4_20 half_3_20 half_5_00
  · have h := ninth_B_second_cross (u := 3) (t := 6)
      (φ₁ := (782793107763/10000000000000 : ℝ)) (φ₂ := (103272759973/2000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_00
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_01 : AdmissibleExponent 9 12 (6883471691269/1000000000000 : ℝ) := by
  apply two_stage_admissible (k := 9) (s := 4) (u := 3) (t := 6)
    (φ₁ := (890344806853/10000000000000 : ℝ)) (φ₂ := (41382528763/500000000000 : ℝ)) (χ := (362569736657509423266213227/75000000000000000000000000 : ℝ)) (γ := (9668526310867/2000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_01 half_4_20 half_6_00
  · have h := ninth_B_second_cross (u := 4) (t := 6)
      (φ₁ := (890344806853/10000000000000 : ℝ)) (φ₂ := (41382528763/500000000000 : ℝ)) (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_00
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_7_01 : AdmissibleExponent 9 14 (41886546845797/5000000000000 : ℝ) := by
  apply two_stage_admissible (k := 9) (s := 5) (u := 4) (t := 7)
    (φ₁ := (96518116991/1000000000000 : ℝ)) (φ₂ := (115516042299/1250000000000 : ℝ)) (χ := (576584853588468072074732489/100000000000000000000000000 : ℝ)) (γ := (57658485358851/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_6_01 half_5_01 half_7_00
  · have h := ninth_A_second_cross (u := 5) (v := 6) (w := 7)
      (φ₁ := (96518116991/1000000000000 : ℝ)) (φ₂ := (115516042299/1250000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_01 half_7_00
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_5_02 : AdmissibleExponent 9 10 (54419952855841/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 9) (s := 3) (u := 2) (t := 5)
    (φ₁ := (170066559823/2500000000000 : ℝ)) (φ₂ := (139127824609/5000000000000 : ℝ)) (χ := (8456858351958971444158081/2000000000000000000000000 : ℝ)) (γ := (8456858351959/2000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_4_20 half_3_20 half_5_01
  · have h := ninth_B_second_cross (u := 3) (t := 6)
      (φ₁ := (170066559823/2500000000000 : ℝ)) (φ₂ := (139127824609/5000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_01
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_02 : AdmissibleExponent 9 12 (67973568691199/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 9) (s := 4) (u := 3) (t := 6)
    (φ₁ := (779642860859/10000000000000 : ℝ)) (φ₂ := (617538453477/10000000000000 : ℝ)) (χ := (786873003887501351711121/156250000000000000000000 : ℝ)) (γ := (50359872248801/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_02 half_4_20 half_6_01
  · have h := ninth_B_second_cross (u := 4) (t := 6)
      (φ₁ := (779642860859/10000000000000 : ℝ)) (φ₂ := (617538453477/10000000000000 : ℝ)) (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_01
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_7_02 : AdmissibleExponent 9 14 (41242142404327/5000000000000 : ℝ) := by
  apply two_stage_admissible (k := 9) (s := 5) (u := 4) (t := 7)
    (φ₁ := (433502356781/5000000000000 : ℝ)) (φ₂ := (779923954677/10000000000000 : ℝ)) (χ := (2372050442150945687471705507/400000000000000000000000000 : ℝ)) (γ := (29650630526887/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_6_02 half_5_02 half_7_01
  · have h := ninth_A_second_cross (u := 5) (v := 6) (w := 7)
      (φ₁ := (433502356781/5000000000000 : ℝ)) (φ₂ := (779923954677/10000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_02 half_7_01
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_5_03 : AdmissibleExponent 9 10 (434259620737/80000000000 : ℝ) := by
  apply two_stage_admissible (k := 9) (s := 3) (u := 2) (t := 5)
    (φ₁ := (644249821307/10000000000000 : ℝ)) (φ₂ := (90618481641/5000000000000 : ℝ)) (χ := (857585461488932616426867789/200000000000000000000000000 : ℝ)) (γ := (2679954567153/625000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_4_20 half_3_20 half_5_02
  · have h := ninth_B_second_cross (u := 3) (t := 6)
      (φ₁ := (644249821307/10000000000000 : ℝ)) (φ₂ := (90618481641/5000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_02
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_03 : AdmissibleExponent 9 12 (8452865685397/1250000000000 : ℝ) := by
  apply two_stage_admissible (k := 9) (s := 4) (u := 3) (t := 6)
    (φ₁ := (730676311493/10000000000000 : ℝ)) (φ₂ := (526651710639/10000000000000 : ℝ)) (χ := (192171093115417780363595933/37500000000000000000000000 : ℝ)) (γ := (51245624830779/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_03 half_4_20 half_6_02
  · have h := ninth_B_second_cross (u := 4) (t := 6)
      (φ₁ := (730676311493/10000000000000 : ℝ)) (φ₂ := (526651710639/10000000000000 : ℝ)) (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_02
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_7_03 : AdmissibleExponent 9 14 (81871270507919/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 9) (s := 5) (u := 4) (t := 7)
    (φ₁ := (81110773443/1000000000000 : ℝ)) (φ₂ := (700477878167/10000000000000 : ℝ)) (χ := (602888111593810692197200763/100000000000000000000000000 : ℝ)) (γ := (30144405579691/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_6_03 half_5_03 half_7_02
  · have h := ninth_A_second_cross (u := 5) (v := 6) (w := 7)
      (φ₁ := (81110773443/1000000000000 : ℝ)) (φ₂ := (700477878167/10000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_03 half_7_02
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_5_04 : AdmissibleExponent 9 10 (27115355137069/5000000000000 : ℝ) := by
  apply two_stage_admissible (k := 9) (s := 3) (u := 2) (t := 5)
    (φ₁ := (630696589467/10000000000000 : ℝ)) (φ₂ := (141879049039/10000000000000 : ℝ)) (χ := (53886211182404477702451559/12500000000000000000000000 : ℝ)) (γ := (5388621118241/1250000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_4_20 half_3_20 half_5_03
  · have h := ninth_B_second_cross (u := 3) (t := 6)
      (φ₁ := (630696589467/10000000000000 : ℝ)) (φ₂ := (141879049039/10000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_03
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_04 : AdmissibleExponent 9 12 (67480384059007/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 9) (s := 4) (u := 3) (t := 6)
    (φ₁ := (710011845133/10000000000000 : ℝ)) (φ₂ := (488698253193/10000000000000 : ℝ)) (χ := (16130670068971881791275763/3125000000000000000000000 : ℝ)) (γ := (51618144220711/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_04 half_4_20 half_6_03
  · have h := ninth_B_second_cross (u := 4) (t := 6)
      (φ₁ := (710011845133/10000000000000 : ℝ)) (φ₂ := (488698253193/10000000000000 : ℝ)) (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_03
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_7_04 : AdmissibleExponent 9 14 (16317417362059/2000000000000 : ℝ) := by
  apply two_stage_admissible (k := 9) (s := 5) (u := 4) (t := 7)
    (φ₁ := (156387386987/2000000000000 : ℝ)) (φ₂ := (660462029487/10000000000000 : ℝ)) (χ := (243253779160858787515783541/40000000000000000000000000 : ℝ)) (γ := (60813444790217/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_6_04 half_5_04 half_7_03
  · have h := ninth_A_second_cross (u := 5) (v := 6) (w := 7)
      (φ₁ := (156387386987/2000000000000 : ℝ)) (φ₂ := (660462029487/10000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_04 half_7_03
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_5_05 : AdmissibleExponent 9 10 (54210506517731/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 9) (s := 3) (u := 2) (t := 5)
    (φ₁ := (12508089529/200000000000 : ℝ)) (φ₂ := (25185862937/2000000000000 : ℝ)) (χ := (172799368903394090229299411/40000000000000000000000000 : ℝ)) (γ := (43199842225849/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_4_20 half_3_20 half_5_04
  · have h := ninth_B_second_cross (u := 3) (t := 6)
      (φ₁ := (12508089529/200000000000 : ℝ)) (φ₂ := (25185862937/2000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_04
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_05 : AdmissibleExponent 9 12 (33711262258743/5000000000000 : ℝ) := by
  apply two_stage_admissible (k := 9) (s := 4) (u := 3) (t := 6)
    (φ₁ := (701474892051/10000000000000 : ℝ)) (φ₂ := (236551775967/5000000000000 : ℝ)) (χ := (51771770704248757301051807/10000000000000000000000000 : ℝ)) (γ := (51771770704249/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_05 half_4_20 half_6_04
  · have h := ninth_B_second_cross (u := 4) (t := 6)
      (φ₁ := (701474892051/10000000000000 : ℝ)) (φ₂ := (236551775967/5000000000000 : ℝ)) (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_04
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_7_05 : AdmissibleExponent 9 14 (8145815292937/1000000000000 : ℝ) := by
  apply two_stage_admissible (k := 9) (s := 5) (u := 4) (t := 7)
    (φ₁ := (767558422089/10000000000000 : ℝ)) (φ₂ := (641330667951/10000000000000 : ℝ)) (χ := (15268427672282359638022731/2500000000000000000000000 : ℝ)) (γ := (61073710689133/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_6_05 half_5_05 half_7_04
  · have h := ninth_A_second_cross (u := 5) (v := 6) (w := 7)
      (φ₁ := (767558422089/10000000000000 : ℝ)) (φ₂ := (641330667951/10000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_05 half_7_04
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_5_06 : AdmissibleExponent 9 10 (54202468580029/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 9) (s := 3) (u := 2) (t := 5)
    (φ₁ := (124659808499/2000000000000 : ℝ)) (φ₂ := (119468237933/10000000000000 : ℝ)) (χ := (108090577195647096356054499/25000000000000000000000000 : ℝ)) (γ := (43236230878259/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_4_20 half_3_20 half_5_05
  · have h := ninth_B_second_cross (u := 3) (t := 6)
      (φ₁ := (124659808499/2000000000000 : ℝ)) (φ₂ := (119468237933/10000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_05
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_06 : AdmissibleExponent 9 12 (67399063126439/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 9) (s := 4) (u := 3) (t := 6)
    (φ₁ := (348992014121/5000000000000 : ℝ)) (φ₂ := (466744688201/10000000000000 : ℝ)) (χ := (388758998709410916655388851/75000000000000000000000000 : ℝ)) (γ := (51834533161259/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_06 half_4_20 half_6_05
  · have h := ninth_B_second_cross (u := 4) (t := 6)
      (φ₁ := (348992014121/5000000000000 : ℝ)) (φ₂ := (466744688201/10000000000000 : ℝ)) (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_05
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_7_06 : AdmissibleExponent 9 14 (81400694850237/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 9) (s := 5) (u := 4) (t := 7)
    (φ₁ := (760752937427/10000000000000 : ℝ)) (φ₂ := (7906190867/125000000000 : ℝ)) (χ := (2447887645388823122269790127/400000000000000000000000000 : ℝ)) (γ := (61197191134721/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_6_06 half_5_06 half_7_05
  · have h := ninth_A_second_cross (u := 5) (v := 6) (w := 7)
      (φ₁ := (760752937427/10000000000000 : ℝ)) (φ₂ := (7906190867/125000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_06 half_7_05
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_5_07 : AdmissibleExponent 9 10 (27099620643867/5000000000000 : ℝ) := by
  apply two_stage_admissible (k := 9) (s := 3) (u := 2) (t := 5)
    (φ₁ := (124490738993/2000000000000 : ℝ)) (φ₂ := (11685145699/1000000000000 : ℝ)) (χ := (173003548900334675545392351/40000000000000000000000000 : ℝ)) (γ := (10812721806271/2500000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_4_20 half_3_20 half_5_06
  · have h := ninth_B_second_cross (u := 3) (t := 6)
      (φ₁ := (124490738993/2000000000000 : ℝ)) (φ₂ := (11685145699/1000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_06
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_07 : AdmissibleExponent 9 12 (2105923624549/312500000000 : ℝ) := by
  apply two_stage_admissible (k := 9) (s := 4) (u := 3) (t := 6)
    (φ₁ := (696563722421/10000000000000 : ℝ)) (φ₂ := (4641612801/100000000000 : ℝ)) (χ := (777900853345361053583247281/150000000000000000000000000 : ℝ)) (γ := (51860056889691/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_07 half_4_20 half_6_06
  · have h := ninth_B_second_cross (u := 4) (t := 6)
      (φ₁ := (696563722421/10000000000000 : ℝ)) (φ₂ := (4641612801/100000000000 : ℝ)) (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_06
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_7_07 : AdmissibleExponent 9 14 (81375463319887/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 9) (s := 5) (u := 4) (t := 7)
    (φ₁ := (189406657223/2500000000000 : ℝ)) (φ₂ := (314257127917/5000000000000 : ℝ)) (χ := (612539640854253782272701377/100000000000000000000000000 : ℝ)) (γ := (61253964085427/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_6_07 half_5_07 half_7_06
  · have h := ninth_A_second_cross (u := 5) (v := 6) (w := 7)
      (φ₁ := (189406657223/2500000000000 : ℝ)) (φ₂ := (314257127917/5000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_07 half_7_06
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_5_08 : AdmissibleExponent 9 10 (27098969887289/5000000000000 : ℝ) := by
  apply two_stage_admissible (k := 9) (s := 3) (u := 2) (t := 5)
    (φ₁ := (124422556081/2000000000000 : ℝ)) (φ₂ := (23158353347/2000000000000 : ℝ)) (χ := (1351775212957787138413007/312500000000000000000000 : ℝ)) (γ := (10814201703663/2500000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_4_20 half_3_20 half_5_07
  · have h := ninth_B_second_cross (u := 3) (t := 6)
      (φ₁ := (124422556081/2000000000000 : ℝ)) (φ₂ := (23158353347/2000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_07
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_08 : AdmissibleExponent 9 12 (33692852446823/5000000000000 : ℝ) := by
  apply two_stage_admissible (k := 9) (s := 4) (u := 3) (t := 6)
    (φ₁ := (173996819323/2500000000000 : ℝ)) (φ₂ := (463113562129/10000000000000 : ℝ)) (χ := (24314256305966239257453871/4687500000000000000000000 : ℝ)) (γ := (51870413452731/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_08 half_4_20 half_6_07
  · have h := ninth_B_second_cross (u := 4) (t := 6)
      (φ₁ := (173996819323/2500000000000 : ℝ)) (φ₂ := (463113562129/10000000000000 : ℝ)) (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_07
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_7_08 : AdmissibleExponent 9 14 (81364515795383/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 9) (s := 5) (u := 4) (t := 7)
    (φ₁ := (37811120473/500000000000 : ℝ)) (φ₂ := (156688289789/2500000000000 : ℝ)) (χ := (15319867750075359996830333/2500000000000000000000000 : ℝ)) (γ := (30639735500151/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_6_08 half_5_08 half_7_07
  · have h := ninth_A_second_cross (u := 5) (v := 6) (w := 7)
      (φ₁ := (37811120473/500000000000 : ℝ)) (φ₂ := (156688289789/2500000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_08 half_7_07
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_5_09 : AdmissibleExponent 9 10 (10839482757909/2000000000000 : ℝ) := by
  apply two_stage_admissible (k := 9) (s := 3) (u := 2) (t := 5)
    (φ₁ := (621975005421/10000000000000 : ℝ)) (φ₂ := (57681331729/5000000000000 : ℝ)) (χ := (432592008432045417870478583/100000000000000000000000000 : ℝ)) (γ := (8651840168641/2000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_4_20 half_3_20 half_5_08
  · have h := ninth_B_second_cross (u := 3) (t := 6)
      (φ₁ := (621975005421/10000000000000 : ℝ)) (φ₂ := (57681331729/5000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_08
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_09 : AdmissibleExponent 9 12 (13476829047199/2000000000000 : ℝ) := by
  apply two_stage_admissible (k := 9) (s := 4) (u := 3) (t := 6)
    (φ₁ := (695753604787/10000000000000 : ℝ)) (φ₂ := (462689010801/10000000000000 : ℝ)) (χ := (32421631977465984849926923/6250000000000000000000000 : ℝ)) (γ := (12968652790987/2500000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_09 half_4_20 half_6_08
  · have h := ninth_B_second_cross (u := 4) (t := 6)
      (φ₁ := (695753604787/10000000000000 : ℝ)) (φ₂ := (462689010801/10000000000000 : ℝ)) (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_08
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_7_09 : AdmissibleExponent 9 14 (20339953080467/2500000000000 : ℝ) := by
  apply two_stage_admissible (k := 9) (s := 5) (u := 4) (t := 7)
    (φ₁ := (30224099589/400000000000 : ℝ)) (φ₂ := (625985017071/10000000000000 : ℝ)) (χ := (612907319095894546799458061/100000000000000000000000000 : ℝ)) (γ := (6129073190959/1000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_6_09 half_5_09 half_7_08
  · have h := ninth_A_second_cross (u := 5) (v := 6) (w := 7)
      (φ₁ := (30224099589/400000000000 : ℝ)) (φ₂ := (625985017071/10000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_09 half_7_08
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_5_10 : AdmissibleExponent 9 10 (27098600504309/5000000000000 : ℝ) := by
  apply two_stage_admissible (k := 9) (s := 3) (u := 2) (t := 5)
    (φ₁ := (124383854041/2000000000000 : ℝ)) (φ₂ := (28797227937/2500000000000 : ℝ)) (χ := (173040678603269763883000353/40000000000000000000000000 : ℝ)) (γ := (43260169650819/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_4_20 half_3_20 half_5_09
  · have h := ninth_B_second_cross (u := 3) (t := 6)
      (φ₁ := (124383854041/2000000000000 : ℝ)) (φ₂ := (28797227937/2500000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_09
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_10 : AdmissibleExponent 9 12 (67383513656623/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 9) (s := 4) (u := 3) (t := 6)
    (φ₁ := (347829468741/5000000000000 : ℝ)) (φ₂ := (92503409097/2000000000000 : ℝ)) (χ := (155628935015500080136940567/30000000000000000000000000 : ℝ)) (γ := (25938155835917/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_10 half_4_20 half_6_09
  · have h := ninth_B_second_cross (u := 4) (t := 6)
      (φ₁ := (347829468741/5000000000000 : ℝ)) (φ₂ := (92503409097/2000000000000 : ℝ)) (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_09
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_7_10 : AdmissibleExponent 9 14 (5084862988059/625000000000 : ℝ) := by
  apply two_stage_admissible (k := 9) (s := 5) (u := 4) (t := 7)
    (φ₁ := (755332487689/10000000000000 : ℝ)) (φ₂ := (625653679389/10000000000000 : ℝ)) (χ := (1225912725955419142539309499/200000000000000000000000000 : ℝ)) (γ := (61295636297771/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_6_10 half_5_10 half_7_09
  · have h := ninth_A_second_cross (u := 5) (v := 6) (w := 7)
      (φ₁ := (755332487689/10000000000000 : ℝ)) (φ₂ := (625653679389/10000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_10 half_7_09
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_5_11 : AdmissibleExponent 9 10 (27098557444909/5000000000000 : ℝ) := by
  apply two_stage_admissible (k := 9) (s := 3) (u := 2) (t := 5)
    (φ₁ := (621896712497/10000000000000 : ℝ)) (φ₂ := (23023711573/2000000000000 : ℝ)) (χ := (432605618200846240211546237/100000000000000000000000000 : ℝ)) (γ := (43260561820089/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_4_20 half_3_20 half_5_10
  · have h := ninth_B_second_cross (u := 3) (t := 6)
      (φ₁ := (621896712497/10000000000000 : ℝ)) (φ₂ := (23023711573/2000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_10
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_11 : AdmissibleExponent 9 12 (33691628957179/5000000000000 : ℝ) := by
  apply two_stage_admissible (k := 9) (s := 4) (u := 3) (t := 6)
    (φ₁ := (347810298071/5000000000000 : ℝ)) (φ₂ := (28902962753/625000000000 : ℝ)) (χ := (25938500188164301601374721/5000000000000000000000000 : ℝ)) (γ := (12969250094083/2500000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_11 half_4_20 half_6_10
  · have h := ninth_B_second_cross (u := 4) (t := 6)
      (φ₁ := (347810298071/5000000000000 : ℝ)) (φ₂ := (28902962753/625000000000 : ℝ)) (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_10
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_7_11 : AdmissibleExponent 9 14 (10169619905403/1250000000000 : ℝ) := by
  apply two_stage_admissible (k := 9) (s := 5) (u := 4) (t := 7)
    (φ₁ := (377608074099/5000000000000 : ℝ)) (φ₂ := (39094501779/625000000000 : ℝ)) (χ := (612977493704855462239589287/100000000000000000000000000 : ℝ)) (γ := (30648874685243/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_6_11 half_5_11 half_7_10
  · have h := ninth_A_second_cross (u := 5) (v := 6) (w := 7)
      (φ₁ := (377608074099/5000000000000 : ℝ)) (φ₂ := (39094501779/625000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_11 half_7_10
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_5_12 : AdmissibleExponent 9 10 (13231708991/2441406250 : ℝ) := by
  apply two_stage_admissible (k := 9) (s := 3) (u := 2) (t := 5)
    (φ₁ := (155471895167/2500000000000 : ℝ)) (φ₂ := (115090071123/10000000000000 : ℝ)) (χ := (432607205906274562488342411/100000000000000000000000000 : ℝ)) (γ := (5407590073829/1250000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_4_20 half_3_20 half_5_11
  · have h := ninth_B_second_cross (u := 3) (t := 6)
      (φ₁ := (155471895167/2500000000000 : ℝ)) (φ₂ := (115090071123/10000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_11
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_12 : AdmissibleExponent 9 12 (67383154360831/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 9) (s := 4) (u := 3) (t := 6)
    (φ₁ := (695605069629/10000000000000 : ℝ)) (φ₂ := (231209601847/5000000000000 : ℝ)) (χ := (389079594498664644240964183/75000000000000000000000000 : ℝ)) (γ := (5187727926649/1000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_12 half_4_20 half_6_11
  · have h := ninth_B_second_cross (u := 4) (t := 6)
      (φ₁ := (695605069629/10000000000000 : ℝ)) (φ₂ := (231209601847/5000000000000 : ℝ)) (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_11
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_7_12 : AdmissibleExponent 9 14 (81356602033071/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 9) (s := 5) (u := 4) (t := 7)
    (φ₁ := (755166453627/10000000000000 : ℝ)) (φ₂ := (156362977883/2500000000000 : ℝ)) (χ := (2451946076292348337738447639/400000000000000000000000000 : ℝ)) (γ := (61298651907309/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_6_12 half_5_12 half_7_11
  · have h := ninth_A_second_cross (u := 5) (v := 6) (w := 7)
      (φ₁ := (755166453627/10000000000000 : ℝ)) (φ₂ := (156362977883/2500000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_12 half_7_11
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_5_13 : AdmissibleExponent 9 10 (10839413182499/2000000000000 : ℝ) := by
  apply two_stage_admissible (k := 9) (s := 3) (u := 2) (t := 5)
    (φ₁ := (621883883521/10000000000000 : ℝ)) (φ₂ := (57539268357/5000000000000 : ℝ)) (χ := (173043139493736678350836943/40000000000000000000000000 : ℝ)) (γ := (8652156974687/2000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_4_20 half_3_20 half_5_12
  · have h := ninth_B_second_cross (u := 3) (t := 6)
      (φ₁ := (621883883521/10000000000000 : ℝ)) (φ₂ := (57539268357/5000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_13 : AdmissibleExponent 9 12 (33691556215593/5000000000000 : ℝ) := by
  apply two_stage_admissible (k := 9) (s := 4) (u := 3) (t := 6)
    (φ₁ := (139119756503/2000000000000 : ℝ)) (φ₂ := (92481556969/2000000000000 : ℝ)) (χ := (810584253062744873805129/156250000000000000000000 : ℝ)) (γ := (3242337012251/625000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_13 half_4_20 half_6_12
  · have h := ninth_B_second_cross (u := 4) (t := 6)
      (φ₁ := (139119756503/2000000000000 : ℝ)) (φ₂ := (92481556969/2000000000000 : ℝ)) (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_7_13 : AdmissibleExponent 9 14 (81356452373863/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 9) (s := 5) (u := 4) (t := 7)
    (φ₁ := (377572688757/5000000000000 : ℝ)) (φ₂ := (625426551717/10000000000000 : ℝ)) (χ := (153247586648886069411462827/25000000000000000000000000 : ℝ)) (γ := (12259806931911/2000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_6_13 half_5_13 half_7_12
  · have h := ninth_A_second_cross (u := 5) (v := 6) (w := 7)
      (φ₁ := (377572688757/5000000000000 : ℝ)) (φ₂ := (625426551717/10000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_13 half_7_12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_5_14 : AdmissibleExponent 9 10 (27098530098851/5000000000000 : ℝ) := by
  apply two_stage_admissible (k := 9) (s := 3) (u := 2) (t := 5)
    (φ₁ := (124376477321/2000000000000 : ℝ)) (φ₂ := (14384233299/1250000000000 : ℝ)) (χ := (432608109009768797215617779/100000000000000000000000000 : ℝ)) (γ := (43260810900977/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_4_20 half_3_20 half_5_13
  · have h := ninth_B_second_cross (u := 3) (t := 6)
      (φ₁ := (124376477321/2000000000000 : ℝ)) (φ₂ := (14384233299/1250000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_13
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_14 : AdmissibleExponent 9 12 (33691547726829/5000000000000 : ℝ) := by
  apply two_stage_admissible (k := 9) (s := 4) (u := 3) (t := 6)
    (φ₁ := (695596236771/10000000000000 : ℝ)) (φ₂ := (231201580619/5000000000000 : ℝ)) (χ := (129693594806642307927015221/25000000000000000000000000 : ℝ)) (γ := (25938718961329/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_14 half_4_20 half_6_13
  · have h := ninth_B_second_cross (u := 4) (t := 6)
      (φ₁ := (695596236771/10000000000000 : ℝ)) (φ₂ := (231201580619/5000000000000 : ℝ)) (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_13
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_7_14 : AdmissibleExponent 9 14 (81356389924127/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 9) (s := 5) (u := 4) (t := 7)
    (φ₁ := (755136491727/10000000000000 : ℝ)) (φ₂ := (12508318161/200000000000 : ℝ)) (χ := (306495980101281280440413579/50000000000000000000000000 : ℝ)) (γ := (61299196020257/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_6_14 half_5_14 half_7_13
  · have h := ninth_A_second_cross (u := 5) (v := 6) (w := 7)
      (φ₁ := (755136491727/10000000000000 : ℝ)) (φ₂ := (12508318161/200000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_14 half_7_13
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_5_15 : AdmissibleExponent 9 10 (27098528941909/5000000000000 : ℝ) := by
  apply two_stage_admissible (k := 9) (s := 3) (u := 2) (t := 5)
    (φ₁ := (19433805641/312500000000 : ℝ)) (φ₂ := (23014395073/2000000000000 : ℝ)) (χ := (432608214394614166850675967/100000000000000000000000000 : ℝ)) (γ := (21630410719731/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_4_20 half_3_20 half_5_14
  · have h := ninth_B_second_cross (u := 3) (t := 6)
      (φ₁ := (19433805641/312500000000 : ℝ)) (φ₂ := (23014395073/2000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_14
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_15 : AdmissibleExponent 9 12 (67383088579393/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 9) (s := 4) (u := 3) (t := 6)
    (φ₁ := (695595205979/10000000000000 : ℝ)) (φ₂ := (462401289111/10000000000000 : ℝ)) (χ := (38908092328286456124023039/7500000000000000000000000 : ℝ)) (γ := (12969364109429/2500000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_15 half_4_20 half_6_14
  · have h := ninth_B_second_cross (u := 4) (t := 6)
      (φ₁ := (695595205979/10000000000000 : ℝ)) (φ₂ := (462401289111/10000000000000 : ℝ)) (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_14
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_7_15 : AdmissibleExponent 9 14 (5084772747197/625000000000 : ℝ) := by
  apply two_stage_admissible (k := 9) (s := 5) (u := 4) (t := 7)
    (φ₁ := (23597898877/312500000000 : ℝ)) (φ₂ := (156352865001/2500000000000 : ℝ)) (χ := (612992637090112863296498001/100000000000000000000000000 : ℝ)) (γ := (15324815927253/2500000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_6_15 half_5_15 half_7_14
  · have h := ninth_A_second_cross (u := 5) (v := 6) (w := 7)
      (φ₁ := (23597898877/312500000000 : ℝ)) (φ₂ := (156352865001/2500000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_15 half_7_14
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_5_16 : AdmissibleExponent 9 10 (54197056946929/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 9) (s := 3) (u := 2) (t := 5)
    (φ₁ := (621881535107/10000000000000 : ℝ)) (φ₂ := (28767802421/2500000000000 : ℝ)) (χ := (865216514129571243729308137/200000000000000000000000000 : ℝ)) (γ := (540760321331/125000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_4_20 half_3_20 half_5_15
  · have h := ninth_B_second_cross (u := 3) (t := 6)
      (φ₁ := (621881535107/10000000000000 : ℝ)) (φ₂ := (28767802421/2500000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_15
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_16 : AdmissibleExponent 9 12 (67383085795983/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 9) (s := 4) (u := 3) (t := 6)
    (φ₁ := (347797394303/5000000000000 : ℝ)) (φ₂ := (462400531079/10000000000000 : ℝ)) (χ := (51877463934551542030783253/10000000000000000000000000 : ℝ)) (γ := (6484682991819/1250000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_16 half_4_20 half_6_15
  · have h := ninth_B_second_cross (u := 4) (t := 6)
      (φ₁ := (347797394303/5000000000000 : ℝ)) (φ₂ := (462400531079/10000000000000 : ℝ)) (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_15
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_7_16 : AdmissibleExponent 9 14 (81356353188481/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 9) (s := 5) (u := 4) (t := 7)
    (φ₁ := (188782801719/2500000000000 : ℝ)) (φ₂ := (312704803979/5000000000000 : ℝ)) (χ := (1225985839679370139735669321/200000000000000000000000000 : ℝ)) (γ := (61299291983969/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_6_16 half_5_16 half_7_15
  · have h := ninth_A_second_cross (u := 5) (v := 6) (w := 7)
      (φ₁ := (188782801719/2500000000000 : ℝ)) (φ₂ := (312704803979/5000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_16 half_7_15
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_5_17 : AdmissibleExponent 9 10 (27098528283791/5000000000000 : ℝ) := by
  apply two_stage_admissible (k := 9) (s := 3) (u := 2) (t := 5)
    (φ₁ := (310940717871/5000000000000 : ℝ)) (φ₂ := (115070899657/10000000000000 : ℝ)) (χ := (865216548684169143297097783/200000000000000000000000000 : ℝ)) (γ := (43260827434209/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_4_20 half_3_20 half_5_16
  · have h := ninth_B_second_cross (u := 3) (t := 6)
      (φ₁ := (310940717871/5000000000000 : ℝ)) (φ₂ := (115070899657/10000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_17 : AdmissibleExponent 9 12 (16845771167243/2500000000000 : ℝ) := by
  apply two_stage_admissible (k := 9) (s := 4) (u := 3) (t := 6)
    (φ₁ := (69559461961/1000000000000 : ℝ)) (φ₂ := (9248004483/200000000000 : ℝ)) (χ := (3242341685627683294497433/625000000000000000000000 : ℝ)) (γ := (10375493394009/2000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_17 half_4_20 half_6_16
  · have h := ninth_B_second_cross (u := 4) (t := 6)
      (φ₁ := (69559461961/1000000000000 : ℝ)) (φ₂ := (9248004483/200000000000 : ℝ)) (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_7_17 : AdmissibleExponent 9 14 (20339087184053/2500000000000 : ℝ) := by
  apply two_stage_admissible (k := 9) (s := 5) (u := 4) (t := 7)
    (φ₁ := (377565279363/5000000000000 : ℝ)) (φ₂ := (625408839251/10000000000000 : ℝ)) (χ := (1225986075048632344243162241/200000000000000000000000000 : ℝ)) (γ := (3831206484527/625000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_6_17 half_5_17 half_7_16
  · have h := ninth_A_second_cross (u := 5) (v := 6) (w := 7)
      (φ₁ := (377565279363/5000000000000 : ℝ)) (φ₂ := (625408839251/10000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_17 half_7_16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_5_18 : AdmissibleExponent 9 10 (1693658012937/312500000000 : ℝ) := by
  apply two_stage_admissible (k := 9) (s := 3) (u := 2) (t := 5)
    (φ₁ := (621881395509/10000000000000 : ℝ)) (φ₂ := (115070774127/10000000000000 : ℝ)) (χ := (54076035167204674734391613/12500000000000000000000000 : ℝ)) (γ := (21630414066883/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_4_20 half_3_20 half_5_17
  · have h := ninth_B_second_cross (u := 3) (t := 6)
      (φ₁ := (621881395509/10000000000000 : ℝ)) (φ₂ := (115070774127/10000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_17
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_18 : AdmissibleExponent 9 12 (33691542106321/5000000000000 : ℝ) := by
  apply two_stage_admissible (k := 9) (s := 4) (u := 3) (t := 6)
    (φ₁ := (695594551183/10000000000000 : ℝ)) (φ₂ := (462400099873/10000000000000 : ℝ)) (χ := (12158781609170576024840087/2343750000000000000000000 : ℝ)) (γ := (6484683524891/1250000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_18 half_4_20 half_6_17
  · have h := ninth_B_second_cross (u := 4) (t := 6)
      (φ₁ := (695594551183/10000000000000 : ℝ)) (φ₂ := (462400099873/10000000000000 : ℝ)) (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_17
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_7_18 : AdmissibleExponent 9 14 (81356346899259/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 9) (s := 5) (u := 4) (t := 7)
    (φ₁ := (377565144893/5000000000000 : ℝ)) (φ₂ := (312704260533/5000000000000 : ℝ)) (χ := (306496543177077197949107971/50000000000000000000000000 : ℝ)) (γ := (30649654317709/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_6_18 half_5_18 half_7_17
  · have h := ninth_A_second_cross (u := 5) (v := 6) (w := 7)
      (φ₁ := (377565144893/5000000000000 : ℝ)) (φ₂ := (312704260533/5000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_18 half_7_17
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_5_19 : AdmissibleExponent 9 10 (54197056351793/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 9) (s := 3) (u := 2) (t := 5)
    (φ₁ := (310940689609/5000000000000 : ℝ)) (φ₂ := (115070723299/10000000000000 : ℝ)) (χ := (432608284170236704294290043/100000000000000000000000000 : ℝ)) (γ := (21630414208513/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_4_20 half_3_20 half_5_18
  · have h := ninth_B_second_cross (u := 3) (t := 6)
      (φ₁ := (310940689609/5000000000000 : ℝ)) (φ₂ := (115070723299/10000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_18
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_19 : AdmissibleExponent 9 12 (67383084027873/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 9) (s := 4) (u := 3) (t := 6)
    (φ₁ := (173898630869/2500000000000 : ℝ)) (φ₂ := (462400049553/10000000000000 : ℝ)) (χ := (389081015225952238282983691/75000000000000000000000000 : ℝ)) (γ := (12969367174199/2500000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_19 half_4_20 half_6_18
  · have h := ninth_B_second_cross (u := 4) (t := 6)
      (φ₁ := (173898630869/2500000000000 : ℝ)) (φ₂ := (462400049553/10000000000000 : ℝ)) (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_18
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_7_19 : AdmissibleExponent 9 14 (40678173071429/5000000000000 : ℝ) := by
  apply two_stage_admissible (k := 9) (s := 5) (u := 4) (t := 7)
    (φ₁ := (377565089247/5000000000000 : ℝ)) (φ₂ := (25016335587/400000000000 : ℝ)) (χ := (2451972426241171829799251921/400000000000000000000000000 : ℝ)) (γ := (6129931065603/1000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_6_19 half_5_19 half_7_18
  · have h := ninth_A_second_cross (u := 5) (v := 6) (w := 7)
      (φ₁ := (377565089247/5000000000000 : ℝ)) (φ₂ := (25016335587/400000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_19 half_7_18
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_5_20 : AdmissibleExponent 9 10 (13549264081653/2500000000000 : ℝ) := by
  apply two_stage_admissible (k := 9) (s := 3) (u := 2) (t := 5)
    (φ₁ := (310940686311/5000000000000 : ℝ)) (φ₂ := (115070702719/10000000000000 : ℝ)) (χ := (865216570634232003160020307/200000000000000000000000000 : ℝ)) (γ := (8652165706343/2000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_4_20 half_3_20 half_5_19
  · have h := ninth_B_second_cross (u := 3) (t := 6)
      (φ₁ := (310940686311/5000000000000 : ℝ)) (φ₂ := (115070702719/10000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_19
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_20 : AdmissibleExponent 9 12 (3369154197653/500000000000 : ℝ) := by
  apply two_stage_admissible (k := 9) (s := 4) (u := 3) (t := 6)
    (φ₁ := (347797256129/5000000000000 : ℝ)) (φ₂ := (231200014589/5000000000000 : ℝ)) (χ := (194540508368612437380638593/37500000000000000000000000 : ℝ)) (γ := (51877468898297/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_20 half_4_20 half_6_19
  · have h := ninth_B_second_cross (u := 4) (t := 6)
      (φ₁ := (347797256129/5000000000000 : ℝ)) (φ₂ := (231200014589/5000000000000 : ℝ)) (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_19
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_7_20 : AdmissibleExponent 9 14 (4067817291597/500000000000 : ℝ) := by
  apply two_stage_admissible (k := 9) (s := 5) (u := 4) (t := 7)
    (φ₁ := (188782533137/2500000000000 : ℝ)) (φ₂ := (156352083883/2500000000000 : ℝ)) (χ := (3831206968137815182290203/625000000000000000000000 : ℝ)) (γ := (30649655745103/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_6_20 half_5_20 half_7_19
  · have h := ninth_A_second_cross (u := 5) (v := 6) (w := 7)
      (φ₁ := (188782533137/2500000000000 : ℝ)) (φ₂ := (156352083883/2500000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_20 half_7_19
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_5_21 : AdmissibleExponent 9 10 (10839411263283/2000000000000 : ℝ) := by
  apply two_stage_admissible (k := 9) (s := 3) (u := 2) (t := 5)
    (φ₁ := (19433792811/312500000000 : ℝ)) (φ₂ := (57535347193/5000000000000 : ℝ)) (χ := (21630414289072291787700643/5000000000000000000000000 : ℝ)) (γ := (8652165715629/2000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_4_20 half_3_20 half_5_20
  · have h := ninth_B_second_cross (u := 3) (t := 6)
      (φ₁ := (19433792811/312500000000 : ℝ)) (φ₂ := (57535347193/5000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_20
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_21 : AdmissibleExponent 9 12 (4211442745173/625000000000 : ℝ) := by
  apply two_stage_admissible (k := 9) (s := 4) (u := 3) (t := 6)
    (φ₁ := (173898626929/2500000000000 : ℝ)) (φ₂ := (7225000327/156250000000 : ℝ)) (χ := (3242341811242821687827289/625000000000000000000000 : ℝ)) (γ := (25938734489943/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_21 half_4_20 half_6_20
  · have h := ninth_B_second_cross (u := 4) (t := 6)
      (φ₁ := (173898626929/2500000000000 : ℝ)) (φ₂ := (7225000327/156250000000 : ℝ)) (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_20
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_7_21 : AdmissibleExponent 9 14 (40678172852167/5000000000000 : ℝ) := by
  apply two_stage_admissible (k := 9) (s := 5) (u := 4) (t := 7)
    (φ₁ := (377565056809/5000000000000 : ℝ)) (φ₂ := (625408313263/10000000000000 : ℝ)) (χ := (306496559169335670646514389/50000000000000000000000000 : ℝ)) (γ := (6129931183387/1000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_6_21 half_5_21 half_7_20
  · have h := ninth_A_second_cross (u := 5) (v := 6) (w := 7)
      (φ₁ := (377565056809/5000000000000 : ℝ)) (φ₂ := (625408313263/10000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_21 half_7_20
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_5_22 : AdmissibleExponent 9 10 (27098528156143/5000000000000 : ℝ) := by
  apply two_stage_admissible (k := 9) (s := 3) (u := 2) (t := 5)
    (φ₁ := (62188136887/1000000000000 : ℝ)) (φ₂ := (28767672753/2500000000000 : ℝ)) (χ := (27038017873094826418775207/6250000000000000000000000 : ℝ)) (γ := (21630414298477/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_4_20 half_3_20 half_5_21
  · have h := ninth_B_second_cross (u := 3) (t := 6)
      (φ₁ := (62188136887/1000000000000 : ℝ)) (φ₂ := (28767672753/2500000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_21
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_22 : AdmissibleExponent 9 12 (67383083910503/10000000000000 : ℝ) := by
  apply two_stage_admissible (k := 9) (s := 4) (u := 3) (t := 6)
    (φ₁ := (173898626469/2500000000000 : ℝ)) (φ₂ := (115600004397/2500000000000 : ℝ)) (χ := (6079390899952183984845091/1171875000000000000000000 : ℝ)) (γ := (25938734506463/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_22 half_4_20 half_6_21
  · have h := ninth_B_second_cross (u := 4) (t := 6)
      (φ₁ := (173898626469/2500000000000 : ℝ)) (φ₂ := (115600004397/2500000000000 : ℝ)) (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_21
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_7_22 : AdmissibleExponent 9 14 (20339086413009/2500000000000 : ℝ) := by
  apply two_stage_admissible (k := 9) (s := 5) (u := 4) (t := 7)
    (φ₁ := (755130105833/10000000000000 : ℝ)) (φ₂ := (312704152059/5000000000000 : ℝ)) (χ := (2451972479007899118132529379/400000000000000000000000000 : ℝ)) (γ := (30649655987601/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_6_22 half_5_22 half_7_21
  · have h := ninth_A_second_cross (u := 5) (v := 6) (w := 7)
      (φ₁ := (755130105833/10000000000000 : ℝ)) (φ₂ := (312704152059/5000000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_22 half_7_21
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_5_23 : AdmissibleExponent 9 10 (10839411262123/2000000000000 : ℝ) := by
  apply two_stage_admissible (k := 9) (s := 3) (u := 2) (t := 5)
    (φ₁ := (38867585527/625000000000 : ℝ)) (φ₂ := (57535344823/5000000000000 : ℝ)) (χ := (432608286045651122894903383/100000000000000000000000000 : ℝ)) (γ := (43260828604569/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_4_20 half_3_20 half_5_22
  · have h := ninth_B_second_cross (u := 3) (t := 6)
      (φ₁ := (38867585527/625000000000 : ℝ)) (φ₂ := (57535344823/5000000000000 : ℝ)) (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_22
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_6_23 : AdmissibleExponent 9 12 (131607585753/19531250000 : ℝ) := by
  apply two_stage_admissible (k := 9) (s := 4) (u := 3) (t := 6)
    (φ₁ := (173898626283/2500000000000 : ℝ)) (φ₂ := (115600004059/2500000000000 : ℝ)) (χ := (32423418141431137365286329/6250000000000000000000000 : ℝ)) (γ := (12969367256573/2500000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_5_23 half_4_20 half_6_22
  · have h := ninth_B_second_cross (u := 4) (t := 6)
      (φ₁ := (173898626283/2500000000000 : ℝ)) (φ₂ := (115600004059/2500000000000 : ℝ)) (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_22
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

private theorem half_7_23 : AdmissibleExponent 9 14 (40678172815313/5000000000000 : ℝ) := by
  apply two_stage_admissible (k := 9) (s := 5) (u := 4) (t := 7)
    (φ₁ := (755130102637/10000000000000 : ℝ)) (φ₂ := (39088018773/625000000000 : ℝ)) (χ := (61299312033220257563698199/10000000000000000000000000 : ℝ)) (γ := (2451972481329/400000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_6_23 half_5_23 half_7_22
  · have h := ninth_A_second_cross (u := 5) (v := 6) (w := 7)
      (φ₁ := (755130102637/10000000000000 : ℝ)) (φ₂ := (39088018773/625000000000 : ℝ)) (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      half_6_23 half_7_22
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  all_goals norm_num

theorem ninth_half_5 : AdmissibleExponent 9 10 (10839411262123/2000000000000 : ℝ) := half_5_23

theorem source9_entry_5 : AdmissibleExponent 9 10 (Certificate.source9[5]! : ℝ) := by
  apply admissibleExponent_mono ninth_half_5
  norm_num [Certificate.source9,Certificate.Q]

#print axioms ninth_half_5
#print axioms source9_entry_5

theorem ninth_half_6 : AdmissibleExponent 9 12 (131607585753/19531250000 : ℝ) := half_6_23

theorem source9_entry_6 : AdmissibleExponent 9 12 (Certificate.source9[6]! : ℝ) := by
  apply admissibleExponent_mono ninth_half_6
  norm_num [Certificate.source9,Certificate.Q]

#print axioms ninth_half_6
#print axioms source9_entry_6

theorem ninth_half_7 : AdmissibleExponent 9 14 (40678172815313/5000000000000 : ℝ) := half_7_23

theorem source9_entry_7 : AdmissibleExponent 9 14 (Certificate.source9[7]! : ℝ) := by
  apply admissibleExponent_mono ninth_half_7
  norm_num [Certificate.source9,Certificate.Q]

#print axioms ninth_half_7
#print axioms source9_entry_7

end Waring.SeedCompletionNinthSecondSeeds
