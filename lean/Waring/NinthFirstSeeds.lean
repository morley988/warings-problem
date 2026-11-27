import Waring.FirstStageUpdates
import Waring.CertificateData

/-!
# Unconditional first two nontrivial degree-nine source seeds

Eighteen exact A/B rounds start from the proved empty-height endpoint.
Every extraction parameter, range, balance, and upward rounding is
checked by Lean arithmetic. No published seed estimate is assumed.
-/

noncomputable section
namespace Waring.NinthFirstSeeds
open SmoothMoments FirstStageTransport

private theorem sixth_00 : AdmissibleExponent 9 6 (29/9 : ℝ) := by
  convert admissible_six_endpoint (by norm_num : 2 ≤ (9 : ℕ)) using 1 <;> norm_num

private theorem eighth_00 : AdmissibleExponent 9 8 (367/81 : ℝ) := by
  convert admissible_eight_endpoint (by norm_num : 2 ≤ (9 : ℕ)) using 1 <;> norm_num

private theorem sixth_01 : AdmissibleExponent 9 6 (155041031653/50000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 9)
    (φ := (43/853 : ℝ)) eighth_00 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem eighth_01 : AdmissibleExponent 9 8 (1079567547627/250000000000 : ℝ) := by
  have h := admissible_eight_A_ninth (φ := (738892145369/9851392145369 : ℝ)) sixth_01 eighth_00
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem sixth_02 : AdmissibleExponent 9 6 (1530845304943/500000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 9)
    (φ := (79567547627/2579567547627 : ℝ)) eighth_01 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem eighth_02 : AdmissibleExponent 9 8 (4236511755577/1000000000000 : ℝ) := by
  have h := admissible_eight_A_ninth (φ := (85402406599/1435402406599 : ℝ)) sixth_02 eighth_01
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem sixth_03 : AdmissibleExponent 9 6 (23798511277/7812500000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 9)
    (φ := (236511755577/10236511755577 : ℝ)) eighth_02 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem eighth_03 : AdmissibleExponent 9 8 (65688984001/15625000000 : ℝ) := by
  have h := admissible_eight_A_ninth (φ := (1524697492907/28524697492907 : ℝ)) sixth_03 eighth_02
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem sixth_04 : AdmissibleExponent 9 6 (3040002563/1000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 9)
    (φ := (3188984001/159438984001 : ℝ)) eighth_03 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem eighth_04 : AdmissibleExponent 9 8 (4191088174547/1000000000000 : ℝ) := by
  have h := admissible_eight_A_ninth (φ := (45383583631/889133583631 : ℝ)) sixth_04 eighth_03
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem sixth_05 : AdmissibleExponent 9 6 (379687629311/125000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 9)
    (φ := (191088174547/10191088174547 : ℝ)) eighth_04 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem eighth_05 : AdmissibleExponent 9 8 (261615286689/62500000000 : ℝ) := by
  have h := admissible_eight_A_ninth (φ := (474420128563/9474420128563 : ℝ)) sixth_05 eighth_04
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem sixth_06 : AdmissibleExponent 9 6 (3036490756449/1000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 9)
    (φ := (11615286689/636615286689 : ℝ)) eighth_05 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem eighth_06 : AdmissibleExponent 9 8 (4183726647097/1000000000000 : ℝ) := by
  have h := admissible_eight_A_ninth (φ := (352892683819/7102892683819 : ℝ)) sixth_06 eighth_05
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem sixth_07 : AdmissibleExponent 9 6 (303608239959/100000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 9)
    (φ := (183726647097/10183726647097 : ℝ)) eighth_06 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem eighth_07 : AdmissibleExponent 9 8 (1045717632851/250000000000 : ℝ) := by
  have h := admissible_eight_A_ninth (φ := (1406850342931/28406850342931 : ℝ)) sixth_07 eighth_06
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem sixth_08 : AdmissibleExponent 9 6 (1517958642491/500000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 9)
    (φ := (45717632851/2545717632851 : ℝ)) eighth_07 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem eighth_08 : AdmissibleExponent 9 8 (4182524364051/1000000000000 : ℝ) := by
  have h := admissible_eight_A_ninth (φ := (117078537857/2367078537857 : ℝ)) sixth_08 eighth_07
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem sixth_09 : AdmissibleExponent 9 6 (3035850513591/1000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 9)
    (φ := (182524364051/10182524364051 : ℝ)) eighth_08 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem eighth_09 : AdmissibleExponent 9 8 (4182384374937/1000000000000 : ℝ) := by
  have h := admissible_eight_A_ninth (φ := (1404171037789/28404171037789 : ℝ)) sixth_09 eighth_08
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem sixth_10 : AdmissibleExponent 9 6 (3035823510137/1000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 9)
    (φ := (182384374937/10182384374937 : ℝ)) eighth_09 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem eighth_10 : AdmissibleExponent 9 8 (522790970107/125000000000 : ℝ) := by
  have h := admissible_eight_A_ninth (φ := (1403859084263/28403859084263 : ℝ)) sixth_10 eighth_09
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem sixth_11 : AdmissibleExponent 9 6 (3035812589251/1000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 9)
    (φ := (22790970107/1272790970107 : ℝ)) eighth_10 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem eighth_11 : AdmissibleExponent 9 8 (522788108081/125000000000 : ℝ) := by
  have h := admissible_eight_A_ninth (φ := (116977743797/2366977743797 : ℝ)) sixth_11 eighth_10
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem sixth_12 : AdmissibleExponent 9 6 (1517904086263/500000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 9)
    (φ := (22788108081/1272788108081 : ℝ)) eighth_11 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem eighth_12 : AdmissibleExponent 9 8 (1045573901187/250000000000 : ℝ) := by
  have h := admissible_eight_A_ninth (φ := (8773011899/177523011899 : ℝ)) sixth_12 eighth_11
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem sixth_13 : AdmissibleExponent 9 6 (1517903193133/500000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 9)
    (φ := (45573901187/2545573901187 : ℝ)) eighth_12 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem eighth_13 : AdmissibleExponent 9 8 (4182291859759/1000000000000 : ℝ) := by
  have h := admissible_eight_A_ninth (φ := (70183063459/1420183063459 : ℝ)) sixth_13 eighth_12
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem sixth_14 : AdmissibleExponent 9 6 (3035805663847/1000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 9)
    (φ := (182291859759/10182291859759 : ℝ)) eighth_13 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem eighth_14 : AdmissibleExponent 9 8 (4182290345169/1000000000000 : ℝ) := by
  have h := admissible_eight_A_ninth (φ := (467884307963/9467884307963 : ℝ)) sixth_14 eighth_13
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem sixth_15 : AdmissibleExponent 9 6 (1517902685839/500000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 9)
    (φ := (182290345169/10182290345169 : ℝ)) eighth_14 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem eighth_15 : AdmissibleExponent 9 8 (4182289732621/1000000000000 : ℝ) := by
  have h := admissible_eight_A_ninth (φ := (280729909759/5680729909759 : ℝ)) sixth_15 eighth_14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem sixth_16 : AdmissibleExponent 9 6 (758951313379/250000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 9)
    (φ := (182289732621/10182289732621 : ℝ)) eighth_15 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem eighth_16 : AdmissibleExponent 9 8 (4182289484887/1000000000000 : ℝ) := by
  have h := admissible_eight_A_ninth (φ := (155960909311/3155960909311 : ℝ)) sixth_16 eighth_15
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem sixth_17 : AdmissibleExponent 9 6 (3035805205727/1000000000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 9)
    (φ := (182289484887/10182289484887 : ℝ)) eighth_16 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem eighth_17 : AdmissibleExponent 9 8 (522786173087/125000000000 : ℝ) := by
  have h := admissible_eight_A_ninth (φ := (1403647631753/28403647631753 : ℝ)) sixth_17 eighth_16
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem sixth_18 : AdmissibleExponent 9 6 (3794756483/1250000000 : ℝ) := by
  have h := admissible_six_B (by simp [SupportedFirstDegree] : SupportedFirstDegree 9)
    (φ := (22786173087/1272786173087 : ℝ)) eighth_17 (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem eighth_18 : AdmissibleExponent 9 8 (167291573767/40000000000 : ℝ) := by
  have h := admissible_eight_A_ninth (φ := (58485308687/1183485308687 : ℝ)) sixth_18 eighth_17
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

theorem source9_six : AdmissibleExponent 9 6 (7589513/2500000 : ℝ) :=
  admissibleExponent_mono sixth_18 (by norm_num)

theorem source9_eight : AdmissibleExponent 9 8 (20911447/5000000 : ℝ) :=
  admissibleExponent_mono eighth_18 (by norm_num)

theorem source9_entry_three : AdmissibleExponent 9 6 (Certificate.source9[3]! : ℝ) := by
  simpa [Certificate.source9,Certificate.Q] using source9_six

theorem source9_entry_four : AdmissibleExponent 9 8 (Certificate.source9[4]! : ℝ) := by
  simpa [Certificate.source9,Certificate.Q] using source9_eight

#print axioms source9_six
#print axioms source9_eight
#print axioms source9_entry_three
#print axioms source9_entry_four
end Waring.NinthFirstSeeds
