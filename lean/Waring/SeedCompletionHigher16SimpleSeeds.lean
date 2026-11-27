import Waring.SeedCompletionEven16SecondSeeds
import Waring.SeedCompletionGeneralTerminal
import Waring.SeedCompletionNaturalChronological

/-! # Actual degree-16 higher seeds from condition(i)

Every finite stage uses the proved padded second/fourth moments,
literal full-box Holder and the actual all-depth recurrence.
LP calculations select rational witnesses only; all inequalities,
rounding and admissibility are checked by Lean. -/
noncomputable section
set_option maxHeartbeats 2000000
namespace Waring.SeedCompletionHigher16SimpleSeeds
open SmoothMoments FirstStageTransport SeedCompletionNaturalBox
open SeedCompletionSourceBounds SeedCompletionPaddedSource SeedCompletionGeneralTerminal
open PolicyCompletionMajorPowerRanges

private theorem half_9_00 : AdmissibleExponent 16 18 (51204269065089/5000000000000 : ℝ) := by
  have h := endpoint_admissible (s := 7) (by norm_num : 0 < (16 : ℕ))
    SeedCompletionEven16SecondSeeds.degree16_half_8 (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_10_00 : AdmissibleExponent 16 20 (58629002248521/5000000000000 : ℝ) := by
  have h := endpoint_admissible (s := 8) (by norm_num : 0 < (16 : ℕ))
    half_9_00 (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_11_00 : AdmissibleExponent 16 22 (132429379215977/10000000000000 : ℝ) := by
  have h := endpoint_admissible (s := 9) (by norm_num : 0 < (16 : ℕ))
    half_10_00 (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_12_00 : AdmissibleExponent 16 24 (147902543014979/10000000000000 : ℝ) := by
  have h := endpoint_admissible (s := 10) (by norm_num : 0 < (16 : ℕ))
    half_11_00 (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_13_00 : AdmissibleExponent 16 26 (163658634076543/10000000000000 : ℝ) := by
  have h := endpoint_admissible (s := 11) (by norm_num : 0 < (16 : ℕ))
    half_12_00 (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_14_00 : AdmissibleExponent 16 28 (4491999236169/250000000000 : ℝ) := by
  have h := endpoint_admissible (s := 12) (by norm_num : 0 < (16 : ℕ))
    half_13_00 (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private def half_9_01_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (450544876369/10000000000000 : ℝ)

private def half_9_01_φ2 : Fin 2 → ℝ := Fin.snoc half_9_01_φ1 (47437585081/1250000000000 : ℝ)

private def half_9_01_φ3 : Fin 3 → ℝ := Fin.snoc half_9_01_φ2 (314028031289/10000000000000 : ℝ)

private theorem half_9_01_hF2 : SourcePowerBound (paddedMoment 16 0 2 8 half_9_01_φ3) (5851668852623/1000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_01_φ3 (by norm_num [half_9_01_φ1, half_9_01_φ2, half_9_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_01_φ1, half_9_01_φ2, half_9_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_01_φ1, half_9_01_φ2, half_9_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_01_φ1, half_9_01_φ2, half_9_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_9_01_hF1 : SourcePowerBound (paddedMoment 16 0 1 8 half_9_01_φ3) (2283889617541/1000000000000 : ℝ) := by
  have h := padded_second_power (k := 16) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_01_φ3 (by norm_num [half_9_01_φ1, half_9_01_φ2, half_9_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_01_φ1, half_9_01_φ2, half_9_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_01_φ1, half_9_01_φ2, half_9_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_01_φ1, half_9_01_φ2, half_9_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_9_01_hx3 : SourcePowerBound (powerBoxCross 16 6 8 half_9_01_φ3) (2960830504971/400000000000 : ℝ) := by
  have h := full_B_cross_power (k := 16) (s := 6) (r := 1) (v := 2) (t := 9) (D := 8)
    (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
    (by norm_num) half_9_01_φ3 (by norm_num [half_9_01_φ1, half_9_01_φ2, half_9_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_01_φ1, half_9_01_φ2, half_9_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_9_01_hF1 half_9_01_hF2 half_9_00
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_9_01_φ1, half_9_01_φ2, half_9_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_01_hx2 : SourcePowerBound (powerBoxCross 16 7 4 half_9_01_φ2) (82815262626149/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 7) (u := 5) (t := 8)
    (D := 4) (ψ := (314028031289/10000000000000 : ℝ)) half_9_01_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_01_φ1, half_9_01_φ2, half_9_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_01_φ1, half_9_01_φ2, half_9_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_01_φ1, half_9_01_φ2, half_9_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_6 SeedCompletionEven16SecondSeeds.degree16_half_8
    (by simpa only [half_9_01_φ3, show (2:ℝ)*4=8 by norm_num] using half_9_01_hx3)
  exact h.weaken (by norm_num [half_9_01_φ1, half_9_01_φ2, half_9_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_01_hx1 : SourcePowerBound (powerBoxCross 16 8 2 half_9_01_φ1) (94392586122059/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 8) (u := 6) (t := 9)
    (D := 2) (ψ := (47437585081/1250000000000 : ℝ)) half_9_01_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_01_φ1, half_9_01_φ2, half_9_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_01_φ1, half_9_01_φ2, half_9_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_01_φ1, half_9_01_φ2, half_9_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_7 half_9_00
    (by simpa only [half_9_01_φ2, show (2:ℝ)*2=4 by norm_num] using half_9_01_hx2)
  exact h.weaken (by norm_num [half_9_01_φ1, half_9_01_φ2, half_9_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_01 : AdmissibleExponent 16 18 (50575379633797/5000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 7) (ψ := (450544876369/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8
    (by simpa only [half_9_01_φ1] using half_9_01_hx1)
  exact admissibleExponent_mono h (by norm_num [half_9_01_φ1, half_9_01_φ2, half_9_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_10_01_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (490632225861/10000000000000 : ℝ)

private def half_10_01_φ2 : Fin 2 → ℝ := Fin.snoc half_10_01_φ1 (413546973729/10000000000000 : ℝ)

private def half_10_01_φ3 : Fin 3 → ℝ := Fin.snoc half_10_01_φ2 (77561331473/2000000000000 : ℝ)

private theorem half_10_01_hF2 : SourcePowerBound (paddedMoment 16 0 2 8 half_10_01_φ3) (2074425457481/400000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_10_01_φ3 (by norm_num [half_10_01_φ1, half_10_01_φ2, half_10_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_01_φ1, half_10_01_φ2, half_10_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_01_φ1, half_10_01_φ2, half_10_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_10_01_φ1, half_10_01_φ2, half_10_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_10_01_hx3 : SourcePowerBound (powerBoxCross 16 7 8 half_10_01_φ3) (82533380261991/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 16) (s := 7) (r := 2) (v := 9) (w := 10) (D := 8)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_10_01_φ3 (by norm_num [half_10_01_φ1, half_10_01_φ2, half_10_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_01_φ1, half_10_01_φ2, half_10_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_10_01_hF2 half_9_01 half_10_00
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_10_01_φ1, half_10_01_φ2, half_10_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_10_01_hx2 : SourcePowerBound (powerBoxCross 16 8 4 half_10_01_φ2) (23252137103279/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 8) (u := 6) (t := 9)
    (D := 4) (ψ := (77561331473/2000000000000 : ℝ)) half_10_01_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_01_φ1, half_10_01_φ2, half_10_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_01_φ1, half_10_01_φ2, half_10_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_01_φ1, half_10_01_φ2, half_10_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_7 half_9_01
    (by simpa only [half_10_01_φ3, show (2:ℝ)*4=8 by norm_num] using half_10_01_hx3)
  exact h.weaken (by norm_num [half_10_01_φ1, half_10_01_φ2, half_10_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_10_01_hx1 : SourcePowerBound (powerBoxCross 16 9 2 half_10_01_φ1) (106678609276769/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 9) (u := 7) (t := 10)
    (D := 2) (ψ := (413546973729/10000000000000 : ℝ)) half_10_01_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_01_φ1, half_10_01_φ2, half_10_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_01_φ1, half_10_01_φ2, half_10_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_01_φ1, half_10_01_φ2, half_10_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8 half_10_00
    (by simpa only [half_10_01_φ2, show (2:ℝ)*2=4 by norm_num] using half_10_01_hx2)
  exact h.weaken (by norm_num [half_10_01_φ1, half_10_01_φ2, half_10_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_10_01 : AdmissibleExponent 16 20 (57509678558203/5000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 8) (ψ := (490632225861/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_9_01
    (by simpa only [half_10_01_φ1] using half_10_01_hx1)
  exact admissibleExponent_mono h (by norm_num [half_10_01_φ1, half_10_01_φ2, half_10_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_11_01_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (130108881521/2500000000000 : ℝ)

private def half_11_01_φ2 : Fin 2 → ℝ := Fin.snoc half_11_01_φ1 (209058505359/5000000000000 : ℝ)

private def half_11_01_φ3 : Fin 3 → ℝ := Fin.snoc half_11_01_φ2 (390815109767/10000000000000 : ℝ)

private def half_11_01_φ4 : Fin 4 → ℝ := Fin.snoc half_11_01_φ3 (70098445057/2500000000000 : ℝ)

private theorem half_11_01_hF2 : SourcePowerBound (paddedMoment 16 0 2 16 half_11_01_φ4) (13512147158827/2000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_11_01_φ4 (by norm_num [half_11_01_φ1, half_11_01_φ2, half_11_01_φ3, half_11_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_01_φ1, half_11_01_φ2, half_11_01_φ3, half_11_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_01_φ1, half_11_01_φ2, half_11_01_φ3, half_11_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_11_01_φ1, half_11_01_φ2, half_11_01_φ3, half_11_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_11_01_hF1 : SourcePowerBound (paddedMoment 16 0 1 16 half_11_01_φ4) (5170715719609/2000000000000 : ℝ) := by
  have h := padded_second_power (k := 16) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_11_01_φ4 (by norm_num [half_11_01_φ1, half_11_01_φ2, half_11_01_φ3, half_11_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_01_φ1, half_11_01_φ2, half_11_01_φ3, half_11_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_01_φ1, half_11_01_φ2, half_11_01_φ3, half_11_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_11_01_φ1, half_11_01_φ2, half_11_01_φ3, half_11_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_11_01_hx4 : SourcePowerBound (powerBoxCross 16 7 16 half_11_01_φ4) (10456286786331/1250000000000 : ℝ) := by
  have h := full_B_cross_power (k := 16) (s := 7) (r := 1) (v := 2) (t := 10) (D := 16)
    (a := (1/10 : ℝ)) (b := (1/5 : ℝ)) (c := (7/10 : ℝ))
    (by norm_num) half_11_01_φ4 (by norm_num [half_11_01_φ1, half_11_01_φ2, half_11_01_φ3, half_11_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_01_φ1, half_11_01_φ2, half_11_01_φ3, half_11_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_11_01_hF1 half_11_01_hF2 half_10_01
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_11_01_φ1, half_11_01_φ2, half_11_01_φ3, half_11_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_11_01_hx3 : SourcePowerBound (powerBoxCross 16 8 8 half_11_01_φ3) (3701180066461/400000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 8) (u := 6) (t := 9)
    (D := 8) (ψ := (70098445057/2500000000000 : ℝ)) half_11_01_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_01_φ1, half_11_01_φ2, half_11_01_φ3, half_11_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_01_φ1, half_11_01_φ2, half_11_01_φ3, half_11_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_01_φ1, half_11_01_φ2, half_11_01_φ3, half_11_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_7 half_9_01
    (by simpa only [half_11_01_φ4, show (2:ℝ)*8=16 by norm_num] using half_11_01_hx4)
  exact h.weaken (by norm_num [half_11_01_φ1, half_11_01_φ2, half_11_01_φ3, half_11_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_11_01_hx2 : SourcePowerBound (powerBoxCross 16 9 4 half_11_01_φ2) (104268813216057/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 9) (u := 7) (t := 10)
    (D := 4) (ψ := (390815109767/10000000000000 : ℝ)) half_11_01_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_01_φ1, half_11_01_φ2, half_11_01_φ3, half_11_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_01_φ1, half_11_01_φ2, half_11_01_φ3, half_11_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_01_φ1, half_11_01_φ2, half_11_01_φ3, half_11_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8 half_10_01
    (by simpa only [half_11_01_φ3, show (2:ℝ)*4=8 by norm_num] using half_11_01_hx3)
  exact h.weaken (by norm_num [half_11_01_φ1, half_11_01_φ2, half_11_01_φ3, half_11_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_11_01_hx1 : SourcePowerBound (powerBoxCross 16 10 2 half_11_01_φ1) (29888444169857/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 10) (u := 8) (t := 11)
    (D := 2) (ψ := (209058505359/5000000000000 : ℝ)) half_11_01_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_01_φ1, half_11_01_φ2, half_11_01_φ3, half_11_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_01_φ1, half_11_01_φ2, half_11_01_φ3, half_11_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_01_φ1, half_11_01_φ2, half_11_01_φ3, half_11_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_01 half_11_00
    (by simpa only [half_11_01_φ2, show (2:ℝ)*2=4 by norm_num] using half_11_01_hx2)
  exact h.weaken (by norm_num [half_11_01_φ1, half_11_01_φ2, half_11_01_φ3, half_11_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_11_01 : AdmissibleExponent 16 22 (8090128229689/625000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 9) (ψ := (130108881521/2500000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_10_01
    (by simpa only [half_11_01_φ1] using half_11_01_hx1)
  exact admissibleExponent_mono h (by norm_num [half_11_01_φ1, half_11_01_φ2, half_11_01_φ3, half_11_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_12_01_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (136563305547/2500000000000 : ℝ)

private def half_12_01_φ2 : Fin 2 → ℝ := Fin.snoc half_12_01_φ1 (86204861593/2000000000000 : ℝ)

private def half_12_01_φ3 : Fin 3 → ℝ := Fin.snoc half_12_01_φ2 (130503467/3125000000 : ℝ)

private def half_12_01_φ4 : Fin 4 → ℝ := Fin.snoc half_12_01_φ3 (7849912927/200000000000 : ℝ)

private theorem half_12_01_hF2 : SourcePowerBound (paddedMoment 16 0 2 16 half_12_01_φ4) (11913541561873/2000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_12_01_φ4 (by norm_num [half_12_01_φ1, half_12_01_φ2, half_12_01_φ3, half_12_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_01_φ1, half_12_01_φ2, half_12_01_φ3, half_12_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_01_φ1, half_12_01_φ2, half_12_01_φ3, half_12_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_12_01_φ1, half_12_01_φ2, half_12_01_φ3, half_12_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_12_01_hx4 : SourcePowerBound (powerBoxCross 16 8 16 half_12_01_φ4) (91660062967107/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 16) (s := 8) (r := 2) (v := 10) (w := 11) (D := 16)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_12_01_φ4 (by norm_num [half_12_01_φ1, half_12_01_φ2, half_12_01_φ3, half_12_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_01_φ1, half_12_01_φ2, half_12_01_φ3, half_12_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_12_01_hF2 half_10_01 half_11_01
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_12_01_φ1, half_12_01_φ2, half_12_01_φ3, half_12_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_12_01_hx3 : SourcePowerBound (powerBoxCross 16 9 8 half_12_01_φ3) (102799803062981/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 9) (u := 7) (t := 10)
    (D := 8) (ψ := (7849912927/200000000000 : ℝ)) half_12_01_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_01_φ1, half_12_01_φ2, half_12_01_φ3, half_12_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_01_φ1, half_12_01_φ2, half_12_01_φ3, half_12_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_01_φ1, half_12_01_φ2, half_12_01_φ3, half_12_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8 half_10_01
    (by simpa only [half_12_01_φ4, show (2:ℝ)*8=16 by norm_num] using half_12_01_hx4)
  exact h.weaken (by norm_num [half_12_01_φ1, half_12_01_φ2, half_12_01_φ3, half_12_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_12_01_hx2 : SourcePowerBound (powerBoxCross 16 10 4 half_12_01_φ2) (11601599976731/1000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 10) (u := 8) (t := 11)
    (D := 4) (ψ := (130503467/3125000000 : ℝ)) half_12_01_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_01_φ1, half_12_01_φ2, half_12_01_φ3, half_12_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_01_φ1, half_12_01_φ2, half_12_01_φ3, half_12_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_01_φ1, half_12_01_φ2, half_12_01_φ3, half_12_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_01 half_11_01
    (by simpa only [half_12_01_φ3, show (2:ℝ)*4=8 by norm_num] using half_12_01_hx3)
  exact h.weaken (by norm_num [half_12_01_φ1, half_12_01_φ2, half_12_01_φ3, half_12_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_12_01_hx1 : SourcePowerBound (powerBoxCross 16 11 2 half_12_01_φ1) (16614686389477/1250000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 11) (u := 9) (t := 12)
    (D := 2) (ψ := (86204861593/2000000000000 : ℝ)) half_12_01_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_01_φ1, half_12_01_φ2, half_12_01_φ3, half_12_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_01_φ1, half_12_01_φ2, half_12_01_φ3, half_12_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_01_φ1, half_12_01_φ2, half_12_01_φ3, half_12_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_01 half_12_00
    (by simpa only [half_12_01_φ2, show (2:ℝ)*2=4 by norm_num] using half_12_01_hx2)
  exact h.weaken (by norm_num [half_12_01_φ1, half_12_01_φ2, half_12_01_φ3, half_12_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_12_01 : AdmissibleExponent 16 24 (36097202195441/2500000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 10) (ψ := (136563305547/2500000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_11_01
    (by simpa only [half_12_01_φ1] using half_12_01_hx1)
  exact admissibleExponent_mono h (by norm_num [half_12_01_φ1, half_12_01_φ2, half_12_01_φ3, half_12_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_13_01_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (564792698969/10000000000000 : ℝ)

private def half_13_01_φ2 : Fin 2 → ℝ := Fin.snoc half_13_01_φ1 (441094568487/10000000000000 : ℝ)

private def half_13_01_φ3 : Fin 3 → ℝ := Fin.snoc half_13_01_φ2 (107191423373/2500000000000 : ℝ)

private def half_13_01_φ4 : Fin 4 → ℝ := Fin.snoc half_13_01_φ3 (411658894917/10000000000000 : ℝ)

private def half_13_01_φ5 : Fin 5 → ℝ := Fin.snoc half_13_01_φ4 (184980483581/5000000000000 : ℝ)

private theorem half_13_01_hF2 : SourcePowerBound (paddedMoment 16 0 2 32 half_13_01_φ5) (14053544592757/2000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_13_01_φ5 (by norm_num [half_13_01_φ1, half_13_01_φ2, half_13_01_φ3, half_13_01_φ4, half_13_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_01_φ1, half_13_01_φ2, half_13_01_φ3, half_13_01_φ4, half_13_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_01_φ1, half_13_01_φ2, half_13_01_φ3, half_13_01_φ4, half_13_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_13_01_φ1, half_13_01_φ2, half_13_01_φ3, half_13_01_φ4, half_13_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_13_01_hF1 : SourcePowerBound (paddedMoment 16 0 1 32 half_13_01_φ5) (5351181530919/2000000000000 : ℝ) := by
  have h := padded_second_power (k := 16) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_13_01_φ5 (by norm_num [half_13_01_φ1, half_13_01_φ2, half_13_01_φ3, half_13_01_φ4, half_13_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_01_φ1, half_13_01_φ2, half_13_01_φ3, half_13_01_φ4, half_13_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_01_φ1, half_13_01_φ2, half_13_01_φ3, half_13_01_φ4, half_13_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_13_01_φ1, half_13_01_φ2, half_13_01_φ3, half_13_01_φ4, half_13_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_13_01_hx5 : SourcePowerBound (powerBoxCross 16 8 32 half_13_01_φ5) (45548072383711/5000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 16) (s := 8) (r := 1) (v := 2) (t := 12) (D := 32)
    (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
    (by norm_num) half_13_01_φ5 (by norm_num [half_13_01_φ1, half_13_01_φ2, half_13_01_φ3, half_13_01_φ4, half_13_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_01_φ1, half_13_01_φ2, half_13_01_φ3, half_13_01_φ4, half_13_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_13_01_hF1 half_13_01_hF2 half_12_01
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_13_01_φ1, half_13_01_φ2, half_13_01_φ3, half_13_01_φ4, half_13_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_01_hx4 : SourcePowerBound (powerBoxCross 16 9 16 half_13_01_φ4) (6335439946359/625000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 4) (s := 9) (u := 7) (t := 10)
    (D := 16) (ψ := (184980483581/5000000000000 : ℝ)) half_13_01_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_01_φ1, half_13_01_φ2, half_13_01_φ3, half_13_01_φ4, half_13_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_01_φ1, half_13_01_φ2, half_13_01_φ3, half_13_01_φ4, half_13_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_01_φ1, half_13_01_φ2, half_13_01_φ3, half_13_01_φ4, half_13_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8 half_10_01
    (by simpa only [half_13_01_φ5, show (2:ℝ)*16=32 by norm_num] using half_13_01_hx5)
  exact h.weaken (by norm_num [half_13_01_φ1, half_13_01_φ2, half_13_01_φ3, half_13_01_φ4, half_13_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_01_hx3 : SourcePowerBound (powerBoxCross 16 10 8 half_13_01_φ3) (113858527672731/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 10) (u := 8) (t := 11)
    (D := 8) (ψ := (411658894917/10000000000000 : ℝ)) half_13_01_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_01_φ1, half_13_01_φ2, half_13_01_φ3, half_13_01_φ4, half_13_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_01_φ1, half_13_01_φ2, half_13_01_φ3, half_13_01_φ4, half_13_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_01_φ1, half_13_01_φ2, half_13_01_φ3, half_13_01_φ4, half_13_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_01 half_11_01
    (by simpa only [half_13_01_φ4, show (2:ℝ)*8=16 by norm_num] using half_13_01_hx4)
  exact h.weaken (by norm_num [half_13_01_φ1, half_13_01_φ2, half_13_01_φ3, half_13_01_φ4, half_13_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_01_hx2 : SourcePowerBound (powerBoxCross 16 11 4 half_13_01_φ2) (64195422296833/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 11) (u := 9) (t := 12)
    (D := 4) (ψ := (107191423373/2500000000000 : ℝ)) half_13_01_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_01_φ1, half_13_01_φ2, half_13_01_φ3, half_13_01_φ4, half_13_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_01_φ1, half_13_01_φ2, half_13_01_φ3, half_13_01_φ4, half_13_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_01_φ1, half_13_01_φ2, half_13_01_φ3, half_13_01_φ4, half_13_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_01 half_12_01
    (by simpa only [half_13_01_φ3, show (2:ℝ)*4=8 by norm_num] using half_13_01_hx3)
  exact h.weaken (by norm_num [half_13_01_φ1, half_13_01_φ2, half_13_01_φ3, half_13_01_φ4, half_13_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_01_hx1 : SourcePowerBound (powerBoxCross 16 12 2 half_13_01_φ1) (146798626979467/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 12) (u := 10) (t := 13)
    (D := 2) (ψ := (441094568487/10000000000000 : ℝ)) half_13_01_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_01_φ1, half_13_01_φ2, half_13_01_φ3, half_13_01_φ4, half_13_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_01_φ1, half_13_01_φ2, half_13_01_φ3, half_13_01_φ4, half_13_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_01_φ1, half_13_01_φ2, half_13_01_φ3, half_13_01_φ4, half_13_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_01 half_13_00
    (by simpa only [half_13_01_φ2, show (2:ℝ)*2=4 by norm_num] using half_13_01_hx2)
  exact h.weaken (by norm_num [half_13_01_φ1, half_13_01_φ2, half_13_01_φ3, half_13_01_φ4, half_13_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_01 : AdmissibleExponent 16 26 (79894429527877/5000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 11) (ψ := (564792698969/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_12_01
    (by simpa only [half_13_01_φ1] using half_13_01_hx1)
  exact admissibleExponent_mono h (by norm_num [half_13_01_φ1, half_13_01_φ2, half_13_01_φ3, half_13_01_φ4, half_13_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_14_01_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (144782098287/2500000000000 : ℝ)

private def half_14_01_φ2 : Fin 2 → ℝ := Fin.snoc half_14_01_φ1 (449857224017/10000000000000 : ℝ)

private def half_14_01_φ3 : Fin 3 → ℝ := Fin.snoc half_14_01_φ2 (440467268751/10000000000000 : ℝ)

private def half_14_01_φ4 : Fin 4 → ℝ := Fin.snoc half_14_01_φ3 (107315573597/2500000000000 : ℝ)

private def half_14_01_φ5 : Fin 5 → ℝ := Fin.snoc half_14_01_φ4 (416935390059/10000000000000 : ℝ)

private theorem half_14_01_hF2 : SourcePowerBound (paddedMoment 16 0 2 32 half_14_01_φ5) (13159144866733/2000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_14_01_φ5 (by norm_num [half_14_01_φ1, half_14_01_φ2, half_14_01_φ3, half_14_01_φ4, half_14_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_01_φ1, half_14_01_φ2, half_14_01_φ3, half_14_01_φ4, half_14_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_01_φ1, half_14_01_φ2, half_14_01_φ3, half_14_01_φ4, half_14_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_14_01_φ1, half_14_01_φ2, half_14_01_φ3, half_14_01_φ4, half_14_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_14_01_hx5 : SourcePowerBound (powerBoxCross 16 9 32 half_14_01_φ5) (3986559424561/400000000000 : ℝ) := by
  have h := full_A_cross_power (k := 16) (s := 9) (r := 2) (v := 12) (w := 12) (D := 32)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_14_01_φ5 (by norm_num [half_14_01_φ1, half_14_01_φ2, half_14_01_φ3, half_14_01_φ4, half_14_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_01_φ1, half_14_01_φ2, half_14_01_φ3, half_14_01_φ4, half_14_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_14_01_hF2 half_12_01 half_12_01
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_14_01_φ1, half_14_01_φ2, half_14_01_φ3, half_14_01_φ4, half_14_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_01_hx4 : SourcePowerBound (powerBoxCross 16 10 16 half_14_01_φ4) (22313585236699/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 4) (s := 10) (u := 8) (t := 11)
    (D := 16) (ψ := (416935390059/10000000000000 : ℝ)) half_14_01_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_01_φ1, half_14_01_φ2, half_14_01_φ3, half_14_01_φ4, half_14_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_01_φ1, half_14_01_φ2, half_14_01_φ3, half_14_01_φ4, half_14_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_01_φ1, half_14_01_φ2, half_14_01_φ3, half_14_01_φ4, half_14_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_01 half_11_01
    (by simpa only [half_14_01_φ5, show (2:ℝ)*16=32 by norm_num] using half_14_01_hx5)
  exact h.weaken (by norm_num [half_14_01_φ1, half_14_01_φ2, half_14_01_φ3, half_14_01_φ4, half_14_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_01_hx3 : SourcePowerBound (powerBoxCross 16 11 8 half_14_01_φ3) (125426835047029/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 11) (u := 9) (t := 12)
    (D := 8) (ψ := (107315573597/2500000000000 : ℝ)) half_14_01_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_01_φ1, half_14_01_φ2, half_14_01_φ3, half_14_01_φ4, half_14_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_01_φ1, half_14_01_φ2, half_14_01_φ3, half_14_01_φ4, half_14_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_01_φ1, half_14_01_φ2, half_14_01_φ3, half_14_01_φ4, half_14_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_01 half_12_01
    (by simpa only [half_14_01_φ4, show (2:ℝ)*8=16 by norm_num] using half_14_01_hx4)
  exact h.weaken (by norm_num [half_14_01_φ1, half_14_01_φ2, half_14_01_φ3, half_14_01_φ4, half_14_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_01_hx2 : SourcePowerBound (powerBoxCross 16 12 4 half_14_01_φ2) (141294339356961/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 12) (u := 10) (t := 13)
    (D := 4) (ψ := (440467268751/10000000000000 : ℝ)) half_14_01_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_01_φ1, half_14_01_φ2, half_14_01_φ3, half_14_01_φ4, half_14_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_01_φ1, half_14_01_φ2, half_14_01_φ3, half_14_01_φ4, half_14_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_01_φ1, half_14_01_φ2, half_14_01_φ3, half_14_01_φ4, half_14_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_01 half_13_01
    (by simpa only [half_14_01_φ3, show (2:ℝ)*4=8 by norm_num] using half_14_01_hx3)
  exact h.weaken (by norm_num [half_14_01_φ1, half_14_01_φ2, half_14_01_φ3, half_14_01_φ4, half_14_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_01_hx1 : SourcePowerBound (powerBoxCross 16 13 2 half_14_01_φ1) (161114160930117/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 13) (u := 11) (t := 14)
    (D := 2) (ψ := (449857224017/10000000000000 : ℝ)) half_14_01_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_01_φ1, half_14_01_φ2, half_14_01_φ3, half_14_01_φ4, half_14_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_01_φ1, half_14_01_φ2, half_14_01_φ3, half_14_01_φ4, half_14_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_01_φ1, half_14_01_φ2, half_14_01_φ3, half_14_01_φ4, half_14_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_01 half_14_00
    (by simpa only [half_14_01_φ2, show (2:ℝ)*2=4 by norm_num] using half_14_01_hx2)
  exact h.weaken (by norm_num [half_14_01_φ1, half_14_01_φ2, half_14_01_φ3, half_14_01_φ4, half_14_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_01 : AdmissibleExponent 16 28 (175592370758817/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 12) (ψ := (144782098287/2500000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_13_01
    (by simpa only [half_14_01_φ1] using half_14_01_hx1)
  exact admissibleExponent_mono h (by norm_num [half_14_01_φ1, half_14_01_φ2, half_14_01_φ3, half_14_01_φ4, half_14_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_9_02_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (400388617/9765625000 : ℝ)

private def half_9_02_φ2 : Fin 2 → ℝ := Fin.snoc half_9_02_φ1 (72812325941/2000000000000 : ℝ)

private def half_9_02_φ3 : Fin 3 → ℝ := Fin.snoc half_9_02_φ2 (226325249539/10000000000000 : ℝ)

private theorem half_9_02_hF2 : SourcePowerBound (paddedMoment 16 0 2 8 half_9_02_φ3) (3249134148133/500000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_02_φ3 (by norm_num [half_9_02_φ1, half_9_02_φ2, half_9_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_02_φ1, half_9_02_φ2, half_9_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_02_φ1, half_9_02_φ2, half_9_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_02_φ1, half_9_02_φ2, half_9_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_9_02_hF1 : SourcePowerBound (paddedMoment 16 0 1 8 half_9_02_φ3) (1249711382711/500000000000 : ℝ) := by
  have h := padded_second_power (k := 16) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_02_φ3 (by norm_num [half_9_02_φ1, half_9_02_φ2, half_9_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_02_φ1, half_9_02_φ2, half_9_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_02_φ1, half_9_02_φ2, half_9_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_02_φ1, half_9_02_φ2, half_9_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_9_02_hx3 : SourcePowerBound (powerBoxCross 16 6 8 half_9_02_φ3) (18921003080111/2500000000000 : ℝ) := by
  have h := full_B_cross_power (k := 16) (s := 6) (r := 1) (v := 2) (t := 9) (D := 8)
    (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
    (by norm_num) half_9_02_φ3 (by norm_num [half_9_02_φ1, half_9_02_φ2, half_9_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_02_φ1, half_9_02_φ2, half_9_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_9_02_hF1 half_9_02_hF2 half_9_01
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_9_02_φ1, half_9_02_φ2, half_9_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_02_hx2 : SourcePowerBound (powerBoxCross 16 7 4 half_9_02_φ2) (83830482280561/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 7) (u := 5) (t := 8)
    (D := 4) (ψ := (226325249539/10000000000000 : ℝ)) half_9_02_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_02_φ1, half_9_02_φ2, half_9_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_02_φ1, half_9_02_φ2, half_9_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_02_φ1, half_9_02_φ2, half_9_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_6 SeedCompletionEven16SecondSeeds.degree16_half_8
    (by simpa only [half_9_02_φ3, show (2:ℝ)*4=8 by norm_num] using half_9_02_hx3)
  exact h.weaken (by norm_num [half_9_02_φ1, half_9_02_φ2, half_9_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_02_hx1 : SourcePowerBound (powerBoxCross 16 8 2 half_9_02_φ1) (23677114155721/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 8) (u := 6) (t := 9)
    (D := 2) (ψ := (72812325941/2000000000000 : ℝ)) half_9_02_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_02_φ1, half_9_02_φ2, half_9_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_02_φ1, half_9_02_φ2, half_9_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_02_φ1, half_9_02_φ2, half_9_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_7 half_9_01
    (by simpa only [half_9_02_φ2, show (2:ℝ)*2=4 by norm_num] using half_9_02_hx2)
  exact h.weaken (by norm_num [half_9_02_φ1, half_9_02_φ2, half_9_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_02 : AdmissibleExponent 16 18 (25214606445001/2500000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 7) (ψ := (400388617/9765625000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8
    (by simpa only [half_9_02_φ1] using half_9_02_hx1)
  exact admissibleExponent_mono h (by norm_num [half_9_02_φ1, half_9_02_φ2, half_9_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_10_02_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (436702179839/10000000000000 : ℝ)

private def half_10_02_φ2 : Fin 2 → ℝ := Fin.snoc half_10_02_φ1 (391434025929/10000000000000 : ℝ)

private def half_10_02_φ3 : Fin 3 → ℝ := Fin.snoc half_10_02_φ2 (79691904151/2500000000000 : ℝ)

private theorem half_10_02_hF2 : SourcePowerBound (paddedMoment 16 0 2 8 half_10_02_φ3) (2919466399663/500000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_10_02_φ3 (by norm_num [half_10_02_φ1, half_10_02_φ2, half_10_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_02_φ1, half_10_02_φ2, half_10_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_02_φ1, half_10_02_φ2, half_10_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_10_02_φ1, half_10_02_φ2, half_10_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_10_02_hx3 : SourcePowerBound (powerBoxCross 16 7 8 half_10_02_φ3) (42349867478527/5000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 16) (s := 7) (r := 2) (v := 9) (w := 10) (D := 8)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_10_02_φ3 (by norm_num [half_10_02_φ1, half_10_02_φ2, half_10_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_02_φ1, half_10_02_φ2, half_10_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_10_02_hF2 half_9_02 half_10_01
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_10_02_φ1, half_10_02_φ2, half_10_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_10_02_hx2 : SourcePowerBound (powerBoxCross 16 8 4 half_10_02_φ2) (11807977828867/1250000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 8) (u := 6) (t := 9)
    (D := 4) (ψ := (79691904151/2500000000000 : ℝ)) half_10_02_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_02_φ1, half_10_02_φ2, half_10_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_02_φ1, half_10_02_φ2, half_10_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_02_φ1, half_10_02_φ2, half_10_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_7 half_9_02
    (by simpa only [half_10_02_φ3, show (2:ℝ)*4=8 by norm_num] using half_10_02_hx3)
  exact h.weaken (by norm_num [half_10_02_φ1, half_10_02_φ2, half_10_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_10_02_hx1 : SourcePowerBound (powerBoxCross 16 9 2 half_10_02_φ1) (53445309260263/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 9) (u := 7) (t := 10)
    (D := 2) (ψ := (391434025929/10000000000000 : ℝ)) half_10_02_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_02_φ1, half_10_02_φ2, half_10_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_02_φ1, half_10_02_φ2, half_10_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_02_φ1, half_10_02_φ2, half_10_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8 half_10_01
    (by simpa only [half_10_02_φ2, show (2:ℝ)*2=4 by norm_num] using half_10_02_hx2)
  exact h.weaken (by norm_num [half_10_02_φ1, half_10_02_φ2, half_10_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_10_02 : AdmissibleExponent 16 20 (114314555577789/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 8) (ψ := (436702179839/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_9_02
    (by simpa only [half_10_02_φ1] using half_10_02_hx1)
  exact admissibleExponent_mono h (by norm_num [half_10_02_φ1, half_10_02_φ2, half_10_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_11_02_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (231876259407/5000000000000 : ℝ)

private def half_11_02_φ2 : Fin 2 → ℝ := Fin.snoc half_11_02_φ1 (410179399099/10000000000000 : ℝ)

private def half_11_02_φ3 : Fin 3 → ℝ := Fin.snoc half_11_02_φ2 (370235185063/10000000000000 : ℝ)

private def half_11_02_φ4 : Fin 4 → ℝ := Fin.snoc half_11_02_φ3 (10847855979/500000000000 : ℝ)

private theorem half_11_02_hF2 : SourcePowerBound (paddedMoment 16 0 2 16 half_11_02_φ4) (3712470499249/500000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_11_02_φ4 (by norm_num [half_11_02_φ1, half_11_02_φ2, half_11_02_φ3, half_11_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_02_φ1, half_11_02_φ2, half_11_02_φ3, half_11_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_02_φ1, half_11_02_φ2, half_11_02_φ3, half_11_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_11_02_φ1, half_11_02_φ2, half_11_02_φ3, half_11_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_11_02_hF1 : SourcePowerBound (paddedMoment 16 0 1 16 half_11_02_φ4) (1404156833083/500000000000 : ℝ) := by
  have h := padded_second_power (k := 16) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_11_02_φ4 (by norm_num [half_11_02_φ1, half_11_02_φ2, half_11_02_φ3, half_11_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_02_φ1, half_11_02_φ2, half_11_02_φ3, half_11_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_02_φ1, half_11_02_φ2, half_11_02_φ3, half_11_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_11_02_φ1, half_11_02_φ2, half_11_02_φ3, half_11_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_11_02_hx4 : SourcePowerBound (powerBoxCross 16 7 16 half_11_02_φ4) (17197288187487/2000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 16) (s := 7) (r := 1) (v := 2) (t := 10) (D := 16)
    (a := (1/10 : ℝ)) (b := (1/5 : ℝ)) (c := (7/10 : ℝ))
    (by norm_num) half_11_02_φ4 (by norm_num [half_11_02_φ1, half_11_02_φ2, half_11_02_φ3, half_11_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_02_φ1, half_11_02_φ2, half_11_02_φ3, half_11_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_11_02_hF1 half_11_02_hF2 half_10_02
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_11_02_φ1, half_11_02_φ2, half_11_02_φ3, half_11_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_11_02_hx3 : SourcePowerBound (powerBoxCross 16 8 8 half_11_02_φ3) (94227164592999/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 8) (u := 6) (t := 9)
    (D := 8) (ψ := (10847855979/500000000000 : ℝ)) half_11_02_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_02_φ1, half_11_02_φ2, half_11_02_φ3, half_11_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_02_φ1, half_11_02_φ2, half_11_02_φ3, half_11_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_02_φ1, half_11_02_φ2, half_11_02_φ3, half_11_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_7 half_9_02
    (by simpa only [half_11_02_φ4, show (2:ℝ)*8=16 by norm_num] using half_11_02_hx4)
  exact h.weaken (by norm_num [half_11_02_φ1, half_11_02_φ2, half_11_02_φ3, half_11_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_11_02_hx2 : SourcePowerBound (powerBoxCross 16 9 4 half_11_02_φ2) (52748988824473/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 9) (u := 7) (t := 10)
    (D := 4) (ψ := (370235185063/10000000000000 : ℝ)) half_11_02_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_02_φ1, half_11_02_φ2, half_11_02_φ3, half_11_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_02_φ1, half_11_02_φ2, half_11_02_φ3, half_11_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_02_φ1, half_11_02_φ2, half_11_02_φ3, half_11_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8 half_10_02
    (by simpa only [half_11_02_φ3, show (2:ℝ)*4=8 by norm_num] using half_11_02_hx3)
  exact h.weaken (by norm_num [half_11_02_φ1, half_11_02_φ2, half_11_02_φ3, half_11_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_11_02_hx1 : SourcePowerBound (powerBoxCross 16 10 2 half_11_02_φ1) (23895388357597/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 10) (u := 8) (t := 11)
    (D := 2) (ψ := (410179399099/10000000000000 : ℝ)) half_11_02_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_02_φ1, half_11_02_φ2, half_11_02_φ3, half_11_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_02_φ1, half_11_02_φ2, half_11_02_φ3, half_11_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_02_φ1, half_11_02_φ2, half_11_02_φ3, half_11_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_02 half_11_01
    (by simpa only [half_11_02_φ2, show (2:ℝ)*2=4 by norm_num] using half_11_02_hx2)
  exact h.weaken (by norm_num [half_11_02_φ1, half_11_02_φ2, half_11_02_φ3, half_11_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_11_02 : AdmissibleExponent 16 22 (128288239645451/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 9) (ψ := (231876259407/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_10_02
    (by simpa only [half_11_02_φ1] using half_11_02_hx1)
  exact admissibleExponent_mono h (by norm_num [half_11_02_φ1, half_11_02_φ2, half_11_02_φ3, half_11_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_12_02_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (61217361363/1250000000000 : ℝ)

private def half_12_02_φ2 : Fin 2 → ℝ := Fin.snoc half_12_02_φ1 (425850772947/10000000000000 : ℝ)

private def half_12_02_φ3 : Fin 3 → ℝ := Fin.snoc half_12_02_φ2 (398912610667/10000000000000 : ℝ)

private def half_12_02_φ4 : Fin 4 → ℝ := Fin.snoc half_12_02_φ3 (64656917831/2000000000000 : ℝ)

private theorem half_12_02_hF2 : SourcePowerBound (paddedMoment 16 0 2 16 half_12_02_φ4) (13259918226943/2000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_12_02_φ4 (by norm_num [half_12_02_φ1, half_12_02_φ2, half_12_02_φ3, half_12_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_02_φ1, half_12_02_φ2, half_12_02_φ3, half_12_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_02_φ1, half_12_02_φ2, half_12_02_φ3, half_12_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_12_02_φ1, half_12_02_φ2, half_12_02_φ3, half_12_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_12_02_hx4 : SourcePowerBound (powerBoxCross 16 8 16 half_12_02_φ4) (94111644881801/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 16) (s := 8) (r := 2) (v := 10) (w := 11) (D := 16)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_12_02_φ4 (by norm_num [half_12_02_φ1, half_12_02_φ2, half_12_02_φ3, half_12_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_02_φ1, half_12_02_φ2, half_12_02_φ3, half_12_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_12_02_hF2 half_10_02 half_11_02
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_12_02_φ1, half_12_02_φ2, half_12_02_φ3, half_12_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_12_02_hx3 : SourcePowerBound (powerBoxCross 16 9 8 half_12_02_φ3) (52132815211849/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 9) (u := 7) (t := 10)
    (D := 8) (ψ := (64656917831/2000000000000 : ℝ)) half_12_02_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_02_φ1, half_12_02_φ2, half_12_02_φ3, half_12_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_02_φ1, half_12_02_φ2, half_12_02_φ3, half_12_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_02_φ1, half_12_02_φ2, half_12_02_φ3, half_12_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8 half_10_02
    (by simpa only [half_12_02_φ4, show (2:ℝ)*8=16 by norm_num] using half_12_02_hx4)
  exact h.weaken (by norm_num [half_12_02_φ1, half_12_02_φ2, half_12_02_φ3, half_12_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_12_02_hx2 : SourcePowerBound (powerBoxCross 16 10 4 half_12_02_φ2) (116927800435711/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 10) (u := 8) (t := 11)
    (D := 4) (ψ := (398912610667/10000000000000 : ℝ)) half_12_02_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_02_φ1, half_12_02_φ2, half_12_02_φ3, half_12_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_02_φ1, half_12_02_φ2, half_12_02_φ3, half_12_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_02_φ1, half_12_02_φ2, half_12_02_φ3, half_12_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_02 half_11_02
    (by simpa only [half_12_02_φ3, show (2:ℝ)*4=8 by norm_num] using half_12_02_hx3)
  exact h.weaken (by norm_num [half_12_02_φ1, half_12_02_φ2, half_12_02_φ3, half_12_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_12_02_hx1 : SourcePowerBound (powerBoxCross 16 11 2 half_12_02_φ1) (8280950282273/625000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 11) (u := 9) (t := 12)
    (D := 2) (ψ := (425850772947/10000000000000 : ℝ)) half_12_02_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_02_φ1, half_12_02_φ2, half_12_02_φ3, half_12_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_02_φ1, half_12_02_φ2, half_12_02_φ3, half_12_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_02_φ1, half_12_02_φ2, half_12_02_φ3, half_12_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_02 half_12_01
    (by simpa only [half_12_02_φ2, show (2:ℝ)*2=4 by norm_num] using half_12_02_hx2)
  exact h.weaken (by norm_num [half_12_02_φ1, half_12_02_φ2, half_12_02_φ3, half_12_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_12_02 : AdmissibleExponent 16 24 (17847465153169/1250000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 10) (ψ := (61217361363/1250000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_11_02
    (by simpa only [half_12_02_φ1] using half_12_02_hx1)
  exact admissibleExponent_mono h (by norm_num [half_12_02_φ1, half_12_02_φ2, half_12_02_φ3, half_12_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_13_02_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (513268563459/10000000000000 : ℝ)

private def half_13_02_φ2 : Fin 2 → ℝ := Fin.snoc half_13_02_φ1 (440091995323/10000000000000 : ℝ)

private def half_13_02_φ3 : Fin 3 → ℝ := Fin.snoc half_13_02_φ2 (421834902653/10000000000000 : ℝ)

private def half_13_02_φ4 : Fin 4 → ℝ := Fin.snoc half_13_02_φ3 (12052516619/312500000000 : ℝ)

private def half_13_02_φ5 : Fin 5 → ℝ := Fin.snoc half_13_02_φ4 (267651446687/10000000000000 : ℝ)

private theorem half_13_02_hF2 : SourcePowerBound (paddedMoment 16 0 2 32 half_13_02_φ5) (1574325304063/200000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_13_02_φ5 (by norm_num [half_13_02_φ1, half_13_02_φ2, half_13_02_φ3, half_13_02_φ4, half_13_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_02_φ1, half_13_02_φ2, half_13_02_φ3, half_13_02_φ4, half_13_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_02_φ1, half_13_02_φ2, half_13_02_φ3, half_13_02_φ4, half_13_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_13_02_φ1, half_13_02_φ2, half_13_02_φ3, half_13_02_φ4, half_13_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_13_02_hF1 : SourcePowerBound (paddedMoment 16 0 1 32 half_13_02_φ5) (591441768021/200000000000 : ℝ) := by
  have h := padded_second_power (k := 16) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_13_02_φ5 (by norm_num [half_13_02_φ1, half_13_02_φ2, half_13_02_φ3, half_13_02_φ4, half_13_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_02_φ1, half_13_02_φ2, half_13_02_φ3, half_13_02_φ4, half_13_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_02_φ1, half_13_02_φ2, half_13_02_φ3, half_13_02_φ4, half_13_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_13_02_φ1, half_13_02_φ2, half_13_02_φ3, half_13_02_φ4, half_13_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_13_02_hx5 : SourcePowerBound (powerBoxCross 16 8 32 half_13_02_φ5) (9392570092619/1000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 16) (s := 8) (r := 1) (v := 2) (t := 12) (D := 32)
    (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
    (by norm_num) half_13_02_φ5 (by norm_num [half_13_02_φ1, half_13_02_φ2, half_13_02_φ3, half_13_02_φ4, half_13_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_02_φ1, half_13_02_φ2, half_13_02_φ3, half_13_02_φ4, half_13_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_13_02_hF1 half_13_02_hF2 half_12_02
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_13_02_φ1, half_13_02_φ2, half_13_02_φ3, half_13_02_φ4, half_13_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_02_hx4 : SourcePowerBound (powerBoxCross 16 9 16 half_13_02_φ4) (12857032040383/1250000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 4) (s := 9) (u := 7) (t := 10)
    (D := 16) (ψ := (267651446687/10000000000000 : ℝ)) half_13_02_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_02_φ1, half_13_02_φ2, half_13_02_φ3, half_13_02_φ4, half_13_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_02_φ1, half_13_02_φ2, half_13_02_φ3, half_13_02_φ4, half_13_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_02_φ1, half_13_02_φ2, half_13_02_φ3, half_13_02_φ4, half_13_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8 half_10_02
    (by simpa only [half_13_02_φ5, show (2:ℝ)*16=32 by norm_num] using half_13_02_hx5)
  exact h.weaken (by norm_num [half_13_02_φ1, half_13_02_φ2, half_13_02_φ3, half_13_02_φ4, half_13_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_02_hx3 : SourcePowerBound (powerBoxCross 16 10 8 half_13_02_φ3) (28678874074517/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 10) (u := 8) (t := 11)
    (D := 8) (ψ := (12052516619/312500000000 : ℝ)) half_13_02_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_02_φ1, half_13_02_φ2, half_13_02_φ3, half_13_02_φ4, half_13_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_02_φ1, half_13_02_φ2, half_13_02_φ3, half_13_02_φ4, half_13_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_02_φ1, half_13_02_φ2, half_13_02_φ3, half_13_02_φ4, half_13_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_02 half_11_02
    (by simpa only [half_13_02_φ4, show (2:ℝ)*8=16 by norm_num] using half_13_02_hx4)
  exact h.weaken (by norm_num [half_13_02_φ1, half_13_02_φ2, half_13_02_φ3, half_13_02_φ4, half_13_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_02_hx2 : SourcePowerBound (powerBoxCross 16 11 4 half_13_02_φ2) (64399404202771/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 11) (u := 9) (t := 12)
    (D := 4) (ψ := (421834902653/10000000000000 : ℝ)) half_13_02_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_02_φ1, half_13_02_φ2, half_13_02_φ3, half_13_02_φ4, half_13_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_02_φ1, half_13_02_φ2, half_13_02_φ3, half_13_02_φ4, half_13_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_02_φ1, half_13_02_φ2, half_13_02_φ3, half_13_02_φ4, half_13_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_02 half_12_02
    (by simpa only [half_13_02_φ3, show (2:ℝ)*4=8 by norm_num] using half_13_02_hx3)
  exact h.weaken (by norm_num [half_13_02_φ1, half_13_02_φ2, half_13_02_φ3, half_13_02_φ4, half_13_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_02_hx1 : SourcePowerBound (powerBoxCross 16 12 2 half_13_02_φ1) (145964555548383/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 12) (u := 10) (t := 13)
    (D := 2) (ψ := (440091995323/10000000000000 : ℝ)) half_13_02_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_02_φ1, half_13_02_φ2, half_13_02_φ3, half_13_02_φ4, half_13_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_02_φ1, half_13_02_φ2, half_13_02_φ3, half_13_02_φ4, half_13_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_02_φ1, half_13_02_φ2, half_13_02_φ3, half_13_02_φ4, half_13_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_02 half_13_01
    (by simpa only [half_13_02_φ2, show (2:ℝ)*2=4 by norm_num] using half_13_02_hx2)
  exact h.weaken (by norm_num [half_13_02_φ1, half_13_02_φ2, half_13_02_φ3, half_13_02_φ4, half_13_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_02 : AdmissibleExponent 16 26 (7888486625397/500000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 11) (ψ := (513268563459/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_12_02
    (by simpa only [half_13_02_φ1] using half_13_02_hx1)
  exact admissibleExponent_mono h (by norm_num [half_13_02_φ1, half_13_02_φ2, half_13_02_φ3, half_13_02_φ4, half_13_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_14_02_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (533515682741/10000000000000 : ℝ)

private def half_14_02_φ2 : Fin 2 → ℝ := Fin.snoc half_14_02_φ1 (451654739717/10000000000000 : ℝ)

private def half_14_02_φ3 : Fin 3 → ℝ := Fin.snoc half_14_02_φ2 (436534597587/10000000000000 : ℝ)

private def half_14_02_φ4 : Fin 4 → ℝ := Fin.snoc half_14_02_φ3 (205689844207/5000000000000 : ℝ)

private def half_14_02_φ5 : Fin 5 → ℝ := Fin.snoc half_14_02_φ4 (69280093761/2000000000000 : ℝ)

private theorem half_14_02_hF2 : SourcePowerBound (paddedMoment 16 0 2 32 half_14_02_φ5) (899039587789/125000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_14_02_φ5 (by norm_num [half_14_02_φ1, half_14_02_φ2, half_14_02_φ3, half_14_02_φ4, half_14_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_02_φ1, half_14_02_φ2, half_14_02_φ3, half_14_02_φ4, half_14_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_02_φ1, half_14_02_φ2, half_14_02_φ3, half_14_02_φ4, half_14_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_14_02_φ1, half_14_02_φ2, half_14_02_φ3, half_14_02_φ4, half_14_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_14_02_hx5 : SourcePowerBound (powerBoxCross 16 9 32 half_14_02_φ5) (50863305611477/5000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 16) (s := 9) (r := 2) (v := 12) (w := 12) (D := 32)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_14_02_φ5 (by norm_num [half_14_02_φ1, half_14_02_φ2, half_14_02_φ3, half_14_02_φ4, half_14_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_02_φ1, half_14_02_φ2, half_14_02_φ3, half_14_02_φ4, half_14_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_14_02_hF2 half_12_02 half_12_02
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_14_02_φ1, half_14_02_φ2, half_14_02_φ3, half_14_02_φ4, half_14_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_02_hx4 : SourcePowerBound (powerBoxCross 16 10 16 half_14_02_φ4) (112445533587143/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 4) (s := 10) (u := 8) (t := 11)
    (D := 16) (ψ := (69280093761/2000000000000 : ℝ)) half_14_02_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_02_φ1, half_14_02_φ2, half_14_02_φ3, half_14_02_φ4, half_14_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_02_φ1, half_14_02_φ2, half_14_02_φ3, half_14_02_φ4, half_14_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_02_φ1, half_14_02_φ2, half_14_02_φ3, half_14_02_φ4, half_14_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_02 half_11_02
    (by simpa only [half_14_02_φ5, show (2:ℝ)*16=32 by norm_num] using half_14_02_hx5)
  exact h.weaken (by norm_num [half_14_02_φ1, half_14_02_φ2, half_14_02_φ3, half_14_02_φ4, half_14_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_02_hx3 : SourcePowerBound (powerBoxCross 16 11 8 half_14_02_φ3) (31427103618627/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 11) (u := 9) (t := 12)
    (D := 8) (ψ := (205689844207/5000000000000 : ℝ)) half_14_02_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_02_φ1, half_14_02_φ2, half_14_02_φ3, half_14_02_φ4, half_14_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_02_φ1, half_14_02_φ2, half_14_02_φ3, half_14_02_φ4, half_14_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_02_φ1, half_14_02_φ2, half_14_02_φ3, half_14_02_φ4, half_14_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_02 half_12_02
    (by simpa only [half_14_02_φ4, show (2:ℝ)*8=16 by norm_num] using half_14_02_hx4)
  exact h.weaken (by norm_num [half_14_02_φ1, half_14_02_φ2, half_14_02_φ3, half_14_02_φ4, half_14_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_02_hx2 : SourcePowerBound (powerBoxCross 16 12 4 half_14_02_φ2) (35290601224039/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 12) (u := 10) (t := 13)
    (D := 4) (ψ := (436534597587/10000000000000 : ℝ)) half_14_02_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_02_φ1, half_14_02_φ2, half_14_02_φ3, half_14_02_φ4, half_14_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_02_φ1, half_14_02_φ2, half_14_02_φ3, half_14_02_φ4, half_14_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_02_φ1, half_14_02_φ2, half_14_02_φ3, half_14_02_φ4, half_14_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_02 half_13_02
    (by simpa only [half_14_02_φ3, show (2:ℝ)*4=8 by norm_num] using half_14_02_hx3)
  exact h.weaken (by norm_num [half_14_02_φ1, half_14_02_φ2, half_14_02_φ3, half_14_02_φ4, half_14_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_02_hx1 : SourcePowerBound (powerBoxCross 16 13 2 half_14_02_φ1) (199857481919/12500000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 13) (u := 11) (t := 14)
    (D := 2) (ψ := (451654739717/10000000000000 : ℝ)) half_14_02_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_02_φ1, half_14_02_φ2, half_14_02_φ3, half_14_02_φ4, half_14_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_02_φ1, half_14_02_φ2, half_14_02_φ3, half_14_02_φ4, half_14_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_02_φ1, half_14_02_φ2, half_14_02_φ3, half_14_02_φ4, half_14_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_02 half_14_01
    (by simpa only [half_14_02_φ2, show (2:ℝ)*2=4 by norm_num] using half_14_02_hx2)
  exact h.weaken (by norm_num [half_14_02_φ1, half_14_02_φ2, half_14_02_φ3, half_14_02_φ4, half_14_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_02 : AdmissibleExponent 16 28 (6928955104149/400000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 12) (ψ := (533515682741/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_13_02
    (by simpa only [half_14_02_φ1] using half_14_02_hx1)
  exact admissibleExponent_mono h (by norm_num [half_14_02_φ1, half_14_02_φ2, half_14_02_φ3, half_14_02_φ4, half_14_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_9_03_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (400515928553/10000000000000 : ℝ)

private def half_9_03_φ2 : Fin 2 → ℝ := Fin.snoc half_9_03_φ1 (180205596547/5000000000000 : ℝ)

private def half_9_03_φ3 : Fin 3 → ℝ := Fin.snoc half_9_03_φ2 (25698673823/1250000000000 : ℝ)

private theorem half_9_03_hF2 : SourcePowerBound (paddedMoment 16 0 2 8 half_9_03_φ3) (13301351389921/2000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_03_φ3 (by norm_num [half_9_03_φ1, half_9_03_φ2, half_9_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_03_φ1, half_9_03_φ2, half_9_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_03_φ1, half_9_03_φ2, half_9_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_03_φ1, half_9_03_φ2, half_9_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_9_03_hF1 : SourcePowerBound (paddedMoment 16 0 1 8 half_9_03_φ3) (5100450463307/2000000000000 : ℝ) := by
  have h := padded_second_power (k := 16) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_03_φ3 (by norm_num [half_9_03_φ1, half_9_03_φ2, half_9_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_03_φ1, half_9_03_φ2, half_9_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_03_φ1, half_9_03_φ2, half_9_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_03_φ1, half_9_03_φ2, half_9_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_9_03_hx3 : SourcePowerBound (powerBoxCross 16 6 8 half_9_03_φ3) (76075029803427/10000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 16) (s := 6) (r := 1) (v := 2) (t := 9) (D := 8)
    (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
    (by norm_num) half_9_03_φ3 (by norm_num [half_9_03_φ1, half_9_03_φ2, half_9_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_03_φ1, half_9_03_φ2, half_9_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_9_03_hF1 half_9_03_hF2 half_9_02
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_9_03_φ1, half_9_03_φ2, half_9_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_03_hx2 : SourcePowerBound (powerBoxCross 16 7 4 half_9_03_φ2) (42034077957673/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 7) (u := 5) (t := 8)
    (D := 4) (ψ := (25698673823/1250000000000 : ℝ)) half_9_03_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_03_φ1, half_9_03_φ2, half_9_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_03_φ1, half_9_03_φ2, half_9_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_03_φ1, half_9_03_φ2, half_9_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_6 SeedCompletionEven16SecondSeeds.degree16_half_8
    (by simpa only [half_9_03_φ3, show (2:ℝ)*4=8 by norm_num] using half_9_03_hx3)
  exact h.weaken (by norm_num [half_9_03_φ1, half_9_03_φ2, half_9_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_03_hx1 : SourcePowerBound (powerBoxCross 16 8 2 half_9_03_φ1) (18956464767191/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 8) (u := 6) (t := 9)
    (D := 2) (ψ := (180205596547/5000000000000 : ℝ)) half_9_03_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_03_φ1, half_9_03_φ2, half_9_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_03_φ1, half_9_03_φ2, half_9_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_03_φ1, half_9_03_φ2, half_9_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_7 half_9_02
    (by simpa only [half_9_03_φ2, show (2:ℝ)*2=4 by norm_num] using half_9_03_hx2)
  exact h.weaken (by norm_num [half_9_03_φ1, half_9_03_φ2, half_9_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_03 : AdmissibleExponent 16 18 (403160251057/40000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 7) (ψ := (400515928553/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8
    (by simpa only [half_9_03_φ1] using half_9_03_hx1)
  exact admissibleExponent_mono h (by norm_num [half_9_03_φ1, half_9_03_φ2, half_9_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_10_03_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (83670951563/2000000000000 : ℝ)

private def half_10_03_φ2 : Fin 2 → ℝ := Fin.snoc half_10_03_φ1 (385189921013/10000000000000 : ℝ)

private def half_10_03_φ3 : Fin 3 → ℝ := Fin.snoc half_10_03_φ2 (74338954381/2500000000000 : ℝ)

private theorem half_10_03_hF2 : SourcePowerBound (paddedMoment 16 0 2 8 half_10_03_φ3) (377871735401/62500000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_10_03_φ3 (by norm_num [half_10_03_φ1, half_10_03_φ2, half_10_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_03_φ1, half_10_03_φ2, half_10_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_03_φ1, half_10_03_φ2, half_10_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_10_03_φ1, half_10_03_φ2, half_10_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_10_03_hx3 : SourcePowerBound (powerBoxCross 16 7 8 half_10_03_φ3) (85394324411991/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 16) (s := 7) (r := 2) (v := 9) (w := 10) (D := 8)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_10_03_φ3 (by norm_num [half_10_03_φ1, half_10_03_φ2, half_10_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_03_φ1, half_10_03_φ2, half_10_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_10_03_hF2 half_9_03 half_10_02
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_10_03_φ1, half_10_03_φ2, half_10_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_10_03_hx2 : SourcePowerBound (powerBoxCross 16 8 4 half_10_03_φ2) (94948955380169/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 8) (u := 6) (t := 9)
    (D := 4) (ψ := (74338954381/2500000000000 : ℝ)) half_10_03_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_03_φ1, half_10_03_φ2, half_10_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_03_φ1, half_10_03_φ2, half_10_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_03_φ1, half_10_03_φ2, half_10_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_7 half_9_03
    (by simpa only [half_10_03_φ3, show (2:ℝ)*4=8 by norm_num] using half_10_03_hx3)
  exact h.weaken (by norm_num [half_10_03_φ1, half_10_03_φ2, half_10_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_10_03_hx1 : SourcePowerBound (powerBoxCross 16 9 2 half_10_03_φ1) (106991817292291/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 9) (u := 7) (t := 10)
    (D := 2) (ψ := (385189921013/10000000000000 : ℝ)) half_10_03_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_03_φ1, half_10_03_φ2, half_10_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_03_φ1, half_10_03_φ2, half_10_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_03_φ1, half_10_03_φ2, half_10_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8 half_10_02
    (by simpa only [half_10_03_φ2, show (2:ℝ)*2=4 by norm_num] using half_10_03_hx2)
  exact h.weaken (by norm_num [half_10_03_φ1, half_10_03_φ2, half_10_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_10_03 : AdmissibleExponent 16 20 (57051924087573/5000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 8) (ψ := (83670951563/2000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_9_03
    (by simpa only [half_10_03_φ1] using half_10_03_hx1)
  exact admissibleExponent_mono h (by norm_num [half_10_03_φ1, half_10_03_φ2, half_10_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_11_03_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (54897376083/1250000000000 : ℝ)

private def half_11_03_φ2 : Fin 2 → ℝ := Fin.snoc half_11_03_φ1 (40668601957/1000000000000 : ℝ)

private def half_11_03_φ3 : Fin 3 → ℝ := Fin.snoc half_11_03_φ2 (14557147269/400000000000 : ℝ)

private def half_11_03_φ4 : Fin 4 → ℝ := Fin.snoc half_11_03_φ3 (97364123253/5000000000000 : ℝ)

private theorem half_11_03_hF2 : SourcePowerBound (paddedMoment 16 0 2 16 half_11_03_φ4) (3071860478363/400000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_11_03_φ4 (by norm_num [half_11_03_φ1, half_11_03_φ2, half_11_03_φ3, half_11_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_03_φ1, half_11_03_φ2, half_11_03_φ3, half_11_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_03_φ1, half_11_03_φ2, half_11_03_φ3, half_11_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_11_03_φ1, half_11_03_φ2, half_11_03_φ3, half_11_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_11_03_hF1 : SourcePowerBound (paddedMoment 16 0 1 16 half_11_03_φ4) (1157286826121/400000000000 : ℝ) := by
  have h := padded_second_power (k := 16) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_11_03_φ4 (by norm_num [half_11_03_φ1, half_11_03_φ2, half_11_03_φ3, half_11_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_03_φ1, half_11_03_φ2, half_11_03_φ3, half_11_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_03_φ1, half_11_03_φ2, half_11_03_φ3, half_11_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_11_03_φ1, half_11_03_φ2, half_11_03_φ3, half_11_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_11_03_hx4 : SourcePowerBound (powerBoxCross 16 7 16 half_11_03_φ4) (4345345898709/500000000000 : ℝ) := by
  have h := full_B_cross_power (k := 16) (s := 7) (r := 1) (v := 2) (t := 10) (D := 16)
    (a := (1/10 : ℝ)) (b := (1/5 : ℝ)) (c := (7/10 : ℝ))
    (by norm_num) half_11_03_φ4 (by norm_num [half_11_03_φ1, half_11_03_φ2, half_11_03_φ3, half_11_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_03_φ1, half_11_03_φ2, half_11_03_φ3, half_11_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_11_03_hF1 half_11_03_hF2 half_10_03
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_11_03_φ1, half_11_03_φ2, half_11_03_φ3, half_11_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_11_03_hx3 : SourcePowerBound (powerBoxCross 16 8 8 half_11_03_φ3) (23736002987221/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 8) (u := 6) (t := 9)
    (D := 8) (ψ := (97364123253/5000000000000 : ℝ)) half_11_03_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_03_φ1, half_11_03_φ2, half_11_03_φ3, half_11_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_03_φ1, half_11_03_φ2, half_11_03_φ3, half_11_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_03_φ1, half_11_03_φ2, half_11_03_φ3, half_11_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_7 half_9_03
    (by simpa only [half_11_03_φ4, show (2:ℝ)*8=16 by norm_num] using half_11_03_hx4)
  exact h.weaken (by norm_num [half_11_03_φ1, half_11_03_φ2, half_11_03_φ3, half_11_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_11_03_hx2 : SourcePowerBound (powerBoxCross 16 9 4 half_11_03_φ2) (26520896181321/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 9) (u := 7) (t := 10)
    (D := 4) (ψ := (14557147269/400000000000 : ℝ)) half_11_03_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_03_φ1, half_11_03_φ2, half_11_03_φ3, half_11_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_03_φ1, half_11_03_φ2, half_11_03_φ3, half_11_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_03_φ1, half_11_03_φ2, half_11_03_φ3, half_11_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8 half_10_03
    (by simpa only [half_11_03_φ3, show (2:ℝ)*4=8 by norm_num] using half_11_03_hx3)
  exact h.weaken (by norm_num [half_11_03_φ1, half_11_03_φ2, half_11_03_φ3, half_11_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_11_03_hx1 : SourcePowerBound (powerBoxCross 16 10 2 half_11_03_φ1) (29882956422799/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 10) (u := 8) (t := 11)
    (D := 2) (ψ := (40668601957/1000000000000 : ℝ)) half_11_03_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_03_φ1, half_11_03_φ2, half_11_03_φ3, half_11_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_03_φ1, half_11_03_φ2, half_11_03_φ3, half_11_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_03_φ1, half_11_03_φ2, half_11_03_φ3, half_11_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_03 half_11_02
    (by simpa only [half_11_03_φ2, show (2:ℝ)*2=4 by norm_num] using half_11_03_hx2)
  exact h.weaken (by norm_num [half_11_03_φ1, half_11_03_φ2, half_11_03_φ3, half_11_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_11_03 : AdmissibleExponent 16 22 (31969056713953/2500000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 9) (ψ := (54897376083/1250000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_10_03
    (by simpa only [half_11_03_φ1] using half_11_03_hx1)
  exact admissibleExponent_mono h (by norm_num [half_11_03_φ1, half_11_03_φ2, half_11_03_φ3, half_11_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_12_03_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (229785575611/5000000000000 : ℝ)

private def half_12_03_φ2 : Fin 2 → ℝ := Fin.snoc half_12_03_φ1 (42227083369/1000000000000 : ℝ)

private def half_12_03_φ3 : Fin 3 → ℝ := Fin.snoc half_12_03_φ2 (390672458059/10000000000000 : ℝ)

private def half_12_03_φ4 : Fin 4 → ℝ := Fin.snoc half_12_03_φ3 (295375496307/10000000000000 : ℝ)

private theorem half_12_03_hF2 : SourcePowerBound (paddedMoment 16 0 2 16 half_12_03_φ4) (6944495273249/1000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_12_03_φ4 (by norm_num [half_12_03_φ1, half_12_03_φ2, half_12_03_φ3, half_12_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_03_φ1, half_12_03_φ2, half_12_03_φ3, half_12_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_03_φ1, half_12_03_φ2, half_12_03_φ3, half_12_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_12_03_φ1, half_12_03_φ2, half_12_03_φ3, half_12_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_12_03_hx4 : SourcePowerBound (powerBoxCross 16 8 16 half_12_03_φ4) (19065592857429/2000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 16) (s := 8) (r := 2) (v := 10) (w := 11) (D := 16)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_12_03_φ4 (by norm_num [half_12_03_φ1, half_12_03_φ2, half_12_03_φ3, half_12_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_03_φ1, half_12_03_φ2, half_12_03_φ3, half_12_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_12_03_hF2 half_10_03 half_11_03
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_12_03_φ1, half_12_03_φ2, half_12_03_φ3, half_12_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_12_03_hx3 : SourcePowerBound (powerBoxCross 16 9 8 half_12_03_φ3) (52563712195547/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 9) (u := 7) (t := 10)
    (D := 8) (ψ := (295375496307/10000000000000 : ℝ)) half_12_03_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_03_φ1, half_12_03_φ2, half_12_03_φ3, half_12_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_03_φ1, half_12_03_φ2, half_12_03_φ3, half_12_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_03_φ1, half_12_03_φ2, half_12_03_φ3, half_12_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8 half_10_03
    (by simpa only [half_12_03_φ4, show (2:ℝ)*8=16 by norm_num] using half_12_03_hx4)
  exact h.weaken (by norm_num [half_12_03_φ1, half_12_03_φ2, half_12_03_φ3, half_12_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_12_03_hx2 : SourcePowerBound (powerBoxCross 16 10 4 half_12_03_φ2) (29392598836109/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 10) (u := 8) (t := 11)
    (D := 4) (ψ := (390672458059/10000000000000 : ℝ)) half_12_03_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_03_φ1, half_12_03_φ2, half_12_03_φ3, half_12_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_03_φ1, half_12_03_φ2, half_12_03_φ3, half_12_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_03_φ1, half_12_03_φ2, half_12_03_φ3, half_12_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_03 half_11_03
    (by simpa only [half_12_03_φ3, show (2:ℝ)*4=8 by norm_num] using half_12_03_hx3)
  exact h.weaken (by norm_num [half_12_03_φ1, half_12_03_φ2, half_12_03_φ3, half_12_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_12_03_hx1 : SourcePowerBound (powerBoxCross 16 11 2 half_12_03_φ1) (2649179510561/200000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 11) (u := 9) (t := 12)
    (D := 2) (ψ := (42227083369/1000000000000 : ℝ)) half_12_03_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_03_φ1, half_12_03_φ2, half_12_03_φ3, half_12_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_03_φ1, half_12_03_φ2, half_12_03_φ3, half_12_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_03_φ1, half_12_03_φ2, half_12_03_φ3, half_12_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_03 half_12_02
    (by simpa only [half_12_03_φ2, show (2:ℝ)*2=4 by norm_num] using half_12_03_hx2)
  exact h.weaken (by norm_num [half_12_03_φ1, half_12_03_φ2, half_12_03_φ3, half_12_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_12_03 : AdmissibleExponent 16 24 (4440936553241/312500000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 10) (ψ := (229785575611/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_11_03
    (by simpa only [half_12_03_φ1] using half_12_03_hx1)
  exact admissibleExponent_mono h (by norm_num [half_12_03_φ1, half_12_03_φ2, half_12_03_φ3, half_12_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_13_03_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (96177931399/2000000000000 : ℝ)

private def half_13_03_φ2 : Fin 2 → ℝ := Fin.snoc half_13_03_φ1 (17502647817/400000000000 : ℝ)

private def half_13_03_φ3 : Fin 3 → ℝ := Fin.snoc half_13_03_φ2 (417146551061/10000000000000 : ℝ)

private def half_13_03_φ4 : Fin 4 → ℝ := Fin.snoc half_13_03_φ3 (372597971231/10000000000000 : ℝ)

private def half_13_03_φ5 : Fin 5 → ℝ := Fin.snoc half_13_03_φ4 (217728451461/10000000000000 : ℝ)

private theorem half_13_03_hF2 : SourcePowerBound (paddedMoment 16 0 2 32 half_13_03_φ5) (16666640564443/2000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_13_03_φ5 (by norm_num [half_13_03_φ1, half_13_03_φ2, half_13_03_φ3, half_13_03_φ4, half_13_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_03_φ1, half_13_03_φ2, half_13_03_φ3, half_13_03_φ4, half_13_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_03_φ1, half_13_03_φ2, half_13_03_φ3, half_13_03_φ4, half_13_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_13_03_φ1, half_13_03_φ2, half_13_03_φ3, half_13_03_φ4, half_13_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_13_03_hF1 : SourcePowerBound (paddedMoment 16 0 1 32 half_13_03_φ5) (6222213521481/2000000000000 : ℝ) := by
  have h := padded_second_power (k := 16) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_13_03_φ5 (by norm_num [half_13_03_φ1, half_13_03_φ2, half_13_03_φ3, half_13_03_φ4, half_13_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_03_φ1, half_13_03_φ2, half_13_03_φ3, half_13_03_φ4, half_13_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_03_φ1, half_13_03_φ2, half_13_03_φ3, half_13_03_φ4, half_13_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_13_03_φ1, half_13_03_φ2, half_13_03_φ3, half_13_03_φ4, half_13_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_13_03_hx5 : SourcePowerBound (powerBoxCross 16 8 32 half_13_03_φ5) (19113555812963/2000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 16) (s := 8) (r := 1) (v := 2) (t := 12) (D := 32)
    (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
    (by norm_num) half_13_03_φ5 (by norm_num [half_13_03_φ1, half_13_03_φ2, half_13_03_φ3, half_13_03_φ4, half_13_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_03_φ1, half_13_03_φ2, half_13_03_φ3, half_13_03_φ4, half_13_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_13_03_hF1 half_13_03_hF2 half_12_03
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_13_03_φ1, half_13_03_φ2, half_13_03_φ3, half_13_03_φ4, half_13_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_03_hx4 : SourcePowerBound (powerBoxCross 16 9 16 half_13_03_φ4) (25977915596289/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 4) (s := 9) (u := 7) (t := 10)
    (D := 16) (ψ := (217728451461/10000000000000 : ℝ)) half_13_03_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_03_φ1, half_13_03_φ2, half_13_03_φ3, half_13_03_φ4, half_13_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_03_φ1, half_13_03_φ2, half_13_03_φ3, half_13_03_φ4, half_13_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_03_φ1, half_13_03_φ2, half_13_03_φ3, half_13_03_φ4, half_13_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8 half_10_03
    (by simpa only [half_13_03_φ5, show (2:ℝ)*16=32 by norm_num] using half_13_03_hx5)
  exact h.weaken (by norm_num [half_13_03_φ1, half_13_03_φ2, half_13_03_φ3, half_13_03_φ4, half_13_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_03_hx3 : SourcePowerBound (powerBoxCross 16 10 8 half_13_03_φ3) (23100883910601/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 10) (u := 8) (t := 11)
    (D := 8) (ψ := (372597971231/10000000000000 : ℝ)) half_13_03_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_03_φ1, half_13_03_φ2, half_13_03_φ3, half_13_03_φ4, half_13_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_03_φ1, half_13_03_φ2, half_13_03_φ3, half_13_03_φ4, half_13_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_03_φ1, half_13_03_φ2, half_13_03_φ3, half_13_03_φ4, half_13_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_03 half_11_03
    (by simpa only [half_13_03_φ4, show (2:ℝ)*8=16 by norm_num] using half_13_03_hx4)
  exact h.weaken (by norm_num [half_13_03_φ1, half_13_03_φ2, half_13_03_φ3, half_13_03_φ4, half_13_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_03_hx2 : SourcePowerBound (powerBoxCross 16 11 4 half_13_03_φ2) (2021180957847/156250000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 11) (u := 9) (t := 12)
    (D := 4) (ψ := (417146551061/10000000000000 : ℝ)) half_13_03_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_03_φ1, half_13_03_φ2, half_13_03_φ3, half_13_03_φ4, half_13_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_03_φ1, half_13_03_φ2, half_13_03_φ3, half_13_03_φ4, half_13_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_03_φ1, half_13_03_φ2, half_13_03_φ3, half_13_03_φ4, half_13_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_03 half_12_03
    (by simpa only [half_13_03_φ3, show (2:ℝ)*4=8 by norm_num] using half_13_03_hx3)
  exact h.weaken (by norm_num [half_13_03_φ1, half_13_03_φ2, half_13_03_φ3, half_13_03_φ4, half_13_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_03_hx1 : SourcePowerBound (powerBoxCross 16 12 2 half_13_03_φ1) (72878468951039/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 12) (u := 10) (t := 13)
    (D := 2) (ψ := (17502647817/400000000000 : ℝ)) half_13_03_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_03_φ1, half_13_03_φ2, half_13_03_φ3, half_13_03_φ4, half_13_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_03_φ1, half_13_03_φ2, half_13_03_φ3, half_13_03_φ4, half_13_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_03_φ1, half_13_03_φ2, half_13_03_φ3, half_13_03_φ4, half_13_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_03 half_13_02
    (by simpa only [half_13_03_φ2, show (2:ℝ)*2=4 by norm_num] using half_13_03_hx2)
  exact h.weaken (by norm_num [half_13_03_φ1, half_13_03_φ2, half_13_03_φ3, half_13_03_φ4, half_13_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_03 : AdmissibleExponent 16 26 (156817400012963/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 11) (ψ := (96177931399/2000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_12_03
    (by simpa only [half_13_03_φ1] using half_13_03_hx1)
  exact admissibleExponent_mono h (by norm_num [half_13_03_φ1, half_13_03_φ2, half_13_03_φ3, half_13_03_φ4, half_13_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_14_03_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (62588941763/1250000000000 : ℝ)

private def half_14_03_φ2 : Fin 2 → ℝ := Fin.snoc half_14_03_φ1 (450382439721/10000000000000 : ℝ)

private def half_14_03_φ3 : Fin 3 → ℝ := Fin.snoc half_14_03_φ2 (54052317371/1250000000000 : ℝ)

private def half_14_03_φ4 : Fin 4 → ℝ := Fin.snoc half_14_03_φ3 (80093445783/2000000000000 : ℝ)

private def half_14_03_φ5 : Fin 5 → ℝ := Fin.snoc half_14_03_φ4 (307811147303/10000000000000 : ℝ)

private theorem half_14_03_hF2 : SourcePowerBound (paddedMoment 16 0 2 32 half_14_03_φ5) (15173881998901/2000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_14_03_φ5 (by norm_num [half_14_03_φ1, half_14_03_φ2, half_14_03_φ3, half_14_03_φ4, half_14_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_03_φ1, half_14_03_φ2, half_14_03_φ3, half_14_03_φ4, half_14_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_03_φ1, half_14_03_φ2, half_14_03_φ3, half_14_03_φ4, half_14_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_14_03_φ1, half_14_03_φ2, half_14_03_φ3, half_14_03_φ4, half_14_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_14_03_hx5 : SourcePowerBound (powerBoxCross 16 9 32 half_14_03_φ5) (51627502143311/5000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 16) (s := 9) (r := 2) (v := 12) (w := 12) (D := 32)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_14_03_φ5 (by norm_num [half_14_03_φ1, half_14_03_φ2, half_14_03_φ3, half_14_03_φ4, half_14_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_03_φ1, half_14_03_φ2, half_14_03_φ3, half_14_03_φ4, half_14_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_14_03_hF2 half_12_03 half_12_03
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_14_03_φ1, half_14_03_φ2, half_14_03_φ3, half_14_03_φ4, half_14_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_03_hx4 : SourcePowerBound (powerBoxCross 16 10 16 half_14_03_φ4) (56697866176321/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 4) (s := 10) (u := 8) (t := 11)
    (D := 16) (ψ := (307811147303/10000000000000 : ℝ)) half_14_03_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_03_φ1, half_14_03_φ2, half_14_03_φ3, half_14_03_φ4, half_14_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_03_φ1, half_14_03_φ2, half_14_03_φ3, half_14_03_φ4, half_14_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_03_φ1, half_14_03_φ2, half_14_03_φ3, half_14_03_φ4, half_14_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_03 half_11_03
    (by simpa only [half_14_03_φ5, show (2:ℝ)*16=32 by norm_num] using half_14_03_hx5)
  exact h.weaken (by norm_num [half_14_03_φ1, half_14_03_φ2, half_14_03_φ3, half_14_03_φ4, half_14_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_03_hx3 : SourcePowerBound (powerBoxCross 16 11 8 half_14_03_φ3) (126350399793037/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 11) (u := 9) (t := 12)
    (D := 8) (ψ := (80093445783/2000000000000 : ℝ)) half_14_03_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_03_φ1, half_14_03_φ2, half_14_03_φ3, half_14_03_φ4, half_14_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_03_φ1, half_14_03_φ2, half_14_03_φ3, half_14_03_φ4, half_14_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_03_φ1, half_14_03_φ2, half_14_03_φ3, half_14_03_φ4, half_14_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_03 half_12_03
    (by simpa only [half_14_03_φ4, show (2:ℝ)*8=16 by norm_num] using half_14_03_hx4)
  exact h.weaken (by norm_num [half_14_03_φ1, half_14_03_φ2, half_14_03_φ3, half_14_03_φ4, half_14_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_03_hx2 : SourcePowerBound (powerBoxCross 16 12 4 half_14_03_φ2) (28306737110263/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 12) (u := 10) (t := 13)
    (D := 4) (ψ := (54052317371/1250000000000 : ℝ)) half_14_03_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_03_φ1, half_14_03_φ2, half_14_03_φ3, half_14_03_φ4, half_14_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_03_φ1, half_14_03_φ2, half_14_03_φ3, half_14_03_φ4, half_14_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_03_φ1, half_14_03_φ2, half_14_03_φ3, half_14_03_φ4, half_14_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_03 half_13_03
    (by simpa only [half_14_03_φ3, show (2:ℝ)*4=8 by norm_num] using half_14_03_hx3)
  exact h.weaken (by norm_num [half_14_03_φ1, half_14_03_φ2, half_14_03_φ3, half_14_03_φ4, half_14_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_03_hx1 : SourcePowerBound (powerBoxCross 16 13 2 half_14_03_φ1) (39866520863403/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 13) (u := 11) (t := 14)
    (D := 2) (ψ := (450382439721/10000000000000 : ℝ)) half_14_03_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_03_φ1, half_14_03_φ2, half_14_03_φ3, half_14_03_φ4, half_14_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_03_φ1, half_14_03_φ2, half_14_03_φ3, half_14_03_φ4, half_14_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_03_φ1, half_14_03_φ2, half_14_03_φ3, half_14_03_φ4, half_14_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_03 half_14_02
    (by simpa only [half_14_03_φ2, show (2:ℝ)*2=4 by norm_num] using half_14_03_hx2)
  exact h.weaken (by norm_num [half_14_03_φ1, half_14_03_φ2, half_14_03_φ3, half_14_03_φ4, half_14_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_03 : AdmissibleExponent 16 28 (42995967951553/2500000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 12) (ψ := (62588941763/1250000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_13_03
    (by simpa only [half_14_03_φ1] using half_14_03_hx1)
  exact admissibleExponent_mono h (by norm_num [half_14_03_φ1, half_14_03_φ2, half_14_03_φ3, half_14_03_φ4, half_14_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_9_04_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (398295346223/10000000000000 : ℝ)

private def half_9_04_φ2 : Fin 2 → ℝ := Fin.snoc half_9_04_φ1 (1797770507/50000000000 : ℝ)

private def half_9_04_φ3 : Fin 3 → ℝ := Fin.snoc half_9_04_φ2 (50180206601/2500000000000 : ℝ)

private theorem half_9_04_hF2 : SourcePowerBound (paddedMoment 16 0 2 8 half_9_04_φ3) (13372867533757/2000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_04_φ3 (by norm_num [half_9_04_φ1, half_9_04_φ2, half_9_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_04_φ1, half_9_04_φ2, half_9_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_04_φ1, half_9_04_φ2, half_9_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_04_φ1, half_9_04_φ2, half_9_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_9_04_hF1 : SourcePowerBound (paddedMoment 16 0 1 8 half_9_04_φ3) (5124289177919/2000000000000 : ℝ) := by
  have h := padded_second_power (k := 16) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_04_φ3 (by norm_num [half_9_04_φ1, half_9_04_φ2, half_9_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_04_φ1, half_9_04_φ2, half_9_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_04_φ1, half_9_04_φ2, half_9_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_04_φ1, half_9_04_φ2, half_9_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_9_04_hx3 : SourcePowerBound (powerBoxCross 16 6 8 half_9_04_φ3) (15233343046071/2000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 16) (s := 6) (r := 1) (v := 2) (t := 9) (D := 8)
    (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
    (by norm_num) half_9_04_φ3 (by norm_num [half_9_04_φ1, half_9_04_φ2, half_9_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_04_φ1, half_9_04_φ2, half_9_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_9_04_hF1 half_9_04_hF2 half_9_03
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_9_04_φ1, half_9_04_φ2, half_9_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_04_hx2 : SourcePowerBound (powerBoxCross 16 7 4 half_9_04_φ2) (16824766166783/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 7) (u := 5) (t := 8)
    (D := 4) (ψ := (50180206601/2500000000000 : ℝ)) half_9_04_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_04_φ1, half_9_04_φ2, half_9_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_04_φ1, half_9_04_φ2, half_9_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_04_φ1, half_9_04_φ2, half_9_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_6 SeedCompletionEven16SecondSeeds.degree16_half_8
    (by simpa only [half_9_04_φ3, show (2:ℝ)*4=8 by norm_num] using half_9_04_hx3)
  exact h.weaken (by norm_num [half_9_04_φ1, half_9_04_φ2, half_9_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_04_hx1 : SourcePowerBound (powerBoxCross 16 8 2 half_9_04_φ1) (23699905678571/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 8) (u := 6) (t := 9)
    (D := 2) (ψ := (1797770507/50000000000 : ℝ)) half_9_04_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_04_φ1, half_9_04_φ2, half_9_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_04_φ1, half_9_04_φ2, half_9_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_04_φ1, half_9_04_φ2, half_9_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_7 half_9_03
    (by simpa only [half_9_04_φ2, show (2:ℝ)*2=4 by norm_num] using half_9_04_hx2)
  exact h.weaken (by norm_num [half_9_04_φ1, half_9_04_φ2, half_9_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_04 : AdmissibleExponent 16 18 (100774052907629/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 7) (ψ := (398295346223/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8
    (by simpa only [half_9_04_φ1] using half_9_04_hx1)
  exact admissibleExponent_mono h (by norm_num [half_9_04_φ1, half_9_04_φ2, half_9_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_10_04_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (412624804837/10000000000000 : ℝ)

private def half_10_04_φ2 : Fin 2 → ℝ := Fin.snoc half_10_04_φ1 (11983400153/312500000000 : ℝ)

private def half_10_04_φ3 : Fin 3 → ℝ := Fin.snoc half_10_04_φ2 (58210912797/2000000000000 : ℝ)

private theorem half_10_04_hF2 : SourcePowerBound (paddedMoment 16 0 2 8 half_10_04_φ3) (6107833218269/1000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_10_04_φ3 (by norm_num [half_10_04_φ1, half_10_04_φ2, half_10_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_04_φ1, half_10_04_φ2, half_10_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_04_φ1, half_10_04_φ2, half_10_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_10_04_φ1, half_10_04_φ2, half_10_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_10_04_hx3 : SourcePowerBound (powerBoxCross 16 7 8 half_10_04_φ3) (42801780205247/5000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 16) (s := 7) (r := 2) (v := 9) (w := 10) (D := 8)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_10_04_φ3 (by norm_num [half_10_04_φ1, half_10_04_φ2, half_10_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_04_φ1, half_10_04_φ2, half_10_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_10_04_hF2 half_9_04 half_10_03
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_10_04_φ1, half_10_04_φ2, half_10_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_10_04_hx2 : SourcePowerBound (powerBoxCross 16 8 4 half_10_04_φ2) (47549340137317/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 8) (u := 6) (t := 9)
    (D := 4) (ψ := (58210912797/2000000000000 : ℝ)) half_10_04_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_04_φ1, half_10_04_φ2, half_10_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_04_φ1, half_10_04_φ2, half_10_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_04_φ1, half_10_04_φ2, half_10_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_7 half_9_04
    (by simpa only [half_10_04_φ3, show (2:ℝ)*4=8 by norm_num] using half_10_04_hx3)
  exact h.weaken (by norm_num [half_10_04_φ1, half_10_04_φ2, half_10_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_10_04_hx1 : SourcePowerBound (powerBoxCross 16 9 2 half_10_04_φ1) (13378561290139/1250000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 9) (u := 7) (t := 10)
    (D := 2) (ψ := (11983400153/312500000000 : ℝ)) half_10_04_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_04_φ1, half_10_04_φ2, half_10_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_04_φ1, half_10_04_φ2, half_10_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_04_φ1, half_10_04_φ2, half_10_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8 half_10_03
    (by simpa only [half_10_04_φ2, show (2:ℝ)*2=4 by norm_num] using half_10_04_hx2)
  exact h.weaken (by norm_num [half_10_04_φ1, half_10_04_φ2, half_10_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_10_04 : AdmissibleExponent 16 20 (114043112003341/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 8) (ψ := (412624804837/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_9_04
    (by simpa only [half_10_04_φ1] using half_10_04_hx1)
  exact admissibleExponent_mono h (by norm_num [half_10_04_φ1, half_10_04_φ2, half_10_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_11_04_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (5371884097/125000000000 : ℝ)

private def half_11_04_φ2 : Fin 2 → ℝ := Fin.snoc half_11_04_φ1 (405448970529/10000000000000 : ℝ)

private def half_11_04_φ3 : Fin 3 → ℝ := Fin.snoc half_11_04_φ2 (181012711857/5000000000000 : ℝ)

private def half_11_04_φ4 : Fin 4 → ℝ := Fin.snoc half_11_04_φ3 (187389363099/10000000000000 : ℝ)

private theorem half_11_04_hF2 : SourcePowerBound (paddedMoment 16 0 2 16 half_11_04_φ4) (7769234817041/1000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_11_04_φ4 (by norm_num [half_11_04_φ1, half_11_04_φ2, half_11_04_φ3, half_11_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_04_φ1, half_11_04_φ2, half_11_04_φ3, half_11_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_04_φ1, half_11_04_φ2, half_11_04_φ3, half_11_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_11_04_φ1, half_11_04_φ2, half_11_04_φ3, half_11_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_11_04_hF1 : SourcePowerBound (paddedMoment 16 0 1 16 half_11_04_φ4) (2923078272347/1000000000000 : ℝ) := by
  have h := padded_second_power (k := 16) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_11_04_φ4 (by norm_num [half_11_04_φ1, half_11_04_φ2, half_11_04_φ3, half_11_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_04_φ1, half_11_04_φ2, half_11_04_φ3, half_11_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_04_φ1, half_11_04_φ2, half_11_04_φ3, half_11_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_11_04_φ1, half_11_04_φ2, half_11_04_φ3, half_11_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_11_04_hx4 : SourcePowerBound (powerBoxCross 16 7 16 half_11_04_φ4) (87238324172353/10000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 16) (s := 7) (r := 1) (v := 2) (t := 10) (D := 16)
    (a := (1/10 : ℝ)) (b := (1/5 : ℝ)) (c := (7/10 : ℝ))
    (by norm_num) half_11_04_φ4 (by norm_num [half_11_04_φ1, half_11_04_φ2, half_11_04_φ3, half_11_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_04_φ1, half_11_04_φ2, half_11_04_φ3, half_11_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_11_04_hF1 half_11_04_hF2 half_10_04
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_11_04_φ1, half_11_04_φ2, half_11_04_φ3, half_11_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_11_04_hx3 : SourcePowerBound (powerBoxCross 16 8 8 half_11_04_φ3) (95212569595759/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 8) (u := 6) (t := 9)
    (D := 8) (ψ := (187389363099/10000000000000 : ℝ)) half_11_04_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_04_φ1, half_11_04_φ2, half_11_04_φ3, half_11_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_04_φ1, half_11_04_φ2, half_11_04_φ3, half_11_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_04_φ1, half_11_04_φ2, half_11_04_φ3, half_11_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_7 half_9_04
    (by simpa only [half_11_04_φ4, show (2:ℝ)*8=16 by norm_num] using half_11_04_hx4)
  exact h.weaken (by norm_num [half_11_04_φ1, half_11_04_φ2, half_11_04_φ3, half_11_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_11_04_hx2 : SourcePowerBound (powerBoxCross 16 9 4 half_11_04_φ2) (53158297551691/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 9) (u := 7) (t := 10)
    (D := 4) (ψ := (181012711857/5000000000000 : ℝ)) half_11_04_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_04_φ1, half_11_04_φ2, half_11_04_φ3, half_11_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_04_φ1, half_11_04_φ2, half_11_04_φ3, half_11_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_04_φ1, half_11_04_φ2, half_11_04_φ3, half_11_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8 half_10_04
    (by simpa only [half_11_04_φ3, show (2:ℝ)*4=8 by norm_num] using half_11_04_hx3)
  exact h.weaken (by norm_num [half_11_04_φ1, half_11_04_φ2, half_11_04_φ3, half_11_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_11_04_hx1 : SourcePowerBound (powerBoxCross 16 10 2 half_11_04_φ1) (11957185169317/1000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 10) (u := 8) (t := 11)
    (D := 2) (ψ := (405448970529/10000000000000 : ℝ)) half_11_04_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_04_φ1, half_11_04_φ2, half_11_04_φ3, half_11_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_04_φ1, half_11_04_φ2, half_11_04_φ3, half_11_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_04_φ1, half_11_04_φ2, half_11_04_φ3, half_11_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_04 half_11_03
    (by simpa only [half_11_04_φ2, show (2:ℝ)*2=4 by norm_num] using half_11_04_hx2)
  exact h.weaken (by norm_num [half_11_04_φ1, half_11_04_φ2, half_11_04_φ3, half_11_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_11_04 : AdmissibleExponent 16 22 (12773711552061/1000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 9) (ψ := (5371884097/125000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_10_04
    (by simpa only [half_11_04_φ1] using half_11_04_hx1)
  exact admissibleExponent_mono h (by norm_num [half_11_04_φ1, half_11_04_φ2, half_11_04_φ3, half_11_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_12_04_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (89148523229/2000000000000 : ℝ)

private def half_12_04_φ2 : Fin 2 → ℝ := Fin.snoc half_12_04_φ1 (420579711789/10000000000000 : ℝ)

private def half_12_04_φ3 : Fin 3 → ℝ := Fin.snoc half_12_04_φ2 (77510471063/2000000000000 : ℝ)

private def half_12_04_φ4 : Fin 4 → ℝ := Fin.snoc half_12_04_φ3 (71225135239/2500000000000 : ℝ)

private theorem half_12_04_hF2 : SourcePowerBound (paddedMoment 16 0 2 16 half_12_04_φ4) (2830204596431/400000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_12_04_φ4 (by norm_num [half_12_04_φ1, half_12_04_φ2, half_12_04_φ3, half_12_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_04_φ1, half_12_04_φ2, half_12_04_φ3, half_12_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_04_φ1, half_12_04_φ2, half_12_04_φ3, half_12_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_12_04_φ1, half_12_04_φ2, half_12_04_φ3, half_12_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_12_04_hx4 : SourcePowerBound (powerBoxCross 16 8 16 half_12_04_φ4) (95853011179059/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 16) (s := 8) (r := 2) (v := 10) (w := 11) (D := 16)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_12_04_φ4 (by norm_num [half_12_04_φ1, half_12_04_φ2, half_12_04_φ3, half_12_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_04_φ1, half_12_04_φ2, half_12_04_φ3, half_12_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_12_04_hF2 half_10_04 half_11_04
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_12_04_φ1, half_12_04_φ2, half_12_04_φ3, half_12_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_12_04_hx3 : SourcePowerBound (powerBoxCross 16 9 8 half_12_04_φ3) (105530966977007/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 9) (u := 7) (t := 10)
    (D := 8) (ψ := (71225135239/2500000000000 : ℝ)) half_12_04_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_04_φ1, half_12_04_φ2, half_12_04_φ3, half_12_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_04_φ1, half_12_04_φ2, half_12_04_φ3, half_12_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_04_φ1, half_12_04_φ2, half_12_04_φ3, half_12_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8 half_10_04
    (by simpa only [half_12_04_φ4, show (2:ℝ)*8=16 by norm_num] using half_12_04_hx4)
  exact h.weaken (by norm_num [half_12_04_φ1, half_12_04_φ2, half_12_04_φ3, half_12_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_12_04_hx2 : SourcePowerBound (powerBoxCross 16 10 4 half_12_04_φ2) (29474435761353/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 10) (u := 8) (t := 11)
    (D := 4) (ψ := (77510471063/2000000000000 : ℝ)) half_12_04_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_04_φ1, half_12_04_φ2, half_12_04_φ3, half_12_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_04_φ1, half_12_04_φ2, half_12_04_φ3, half_12_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_04_φ1, half_12_04_φ2, half_12_04_φ3, half_12_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_04 half_11_04
    (by simpa only [half_12_04_φ3, show (2:ℝ)*4=8 by norm_num] using half_12_04_hx3)
  exact h.weaken (by norm_num [half_12_04_φ1, half_12_04_φ2, half_12_04_φ3, half_12_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_12_04_hx1 : SourcePowerBound (powerBoxCross 16 11 2 half_12_04_φ1) (13248907053167/1000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 11) (u := 9) (t := 12)
    (D := 2) (ψ := (420579711789/10000000000000 : ℝ)) half_12_04_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_04_φ1, half_12_04_φ2, half_12_04_φ3, half_12_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_04_φ1, half_12_04_φ2, half_12_04_φ3, half_12_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_04_φ1, half_12_04_φ2, half_12_04_φ3, half_12_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_04 half_12_03
    (by simpa only [half_12_04_φ2, show (2:ℝ)*2=4 by norm_num] using half_12_04_hx2)
  exact h.weaken (by norm_num [half_12_04_φ1, half_12_04_φ2, half_12_04_φ3, half_12_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_12_04 : AdmissibleExponent 16 24 (28369933094143/2000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 10) (ψ := (89148523229/2000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_11_04
    (by simpa only [half_12_04_φ1] using half_12_04_hx1)
  exact admissibleExponent_mono h (by norm_num [half_12_04_φ1, half_12_04_φ2, half_12_04_φ3, half_12_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_13_04_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (463649200241/10000000000000 : ℝ)

private def half_13_04_φ2 : Fin 2 → ℝ := Fin.snoc half_13_04_φ1 (13620185691/312500000000 : ℝ)

private def half_13_04_φ3 : Fin 3 → ℝ := Fin.snoc half_13_04_φ2 (207439557561/5000000000000 : ℝ)

private def half_13_04_φ4 : Fin 4 → ℝ := Fin.snoc half_13_04_φ3 (36693040221/1000000000000 : ℝ)

private def half_13_04_φ5 : Fin 5 → ℝ := Fin.snoc half_13_04_φ4 (48931924653/2500000000000 : ℝ)

private theorem half_13_04_hF2 : SourcePowerBound (paddedMoment 16 0 2 32 half_13_04_φ5) (17106708775327/2000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_13_04_φ5 (by norm_num [half_13_04_φ1, half_13_04_φ2, half_13_04_φ3, half_13_04_φ4, half_13_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_04_φ1, half_13_04_φ2, half_13_04_φ3, half_13_04_φ4, half_13_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_04_φ1, half_13_04_φ2, half_13_04_φ3, half_13_04_φ4, half_13_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_13_04_φ1, half_13_04_φ2, half_13_04_φ3, half_13_04_φ4, half_13_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_13_04_hF1 : SourcePowerBound (paddedMoment 16 0 1 32 half_13_04_φ5) (6368902925109/2000000000000 : ℝ) := by
  have h := padded_second_power (k := 16) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_13_04_φ5 (by norm_num [half_13_04_φ1, half_13_04_φ2, half_13_04_φ3, half_13_04_φ4, half_13_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_04_φ1, half_13_04_φ2, half_13_04_φ3, half_13_04_φ4, half_13_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_04_φ1, half_13_04_φ2, half_13_04_φ3, half_13_04_φ4, half_13_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_13_04_φ1, half_13_04_φ2, half_13_04_φ3, half_13_04_φ4, half_13_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_13_04_hx5 : SourcePowerBound (powerBoxCross 16 8 32 half_13_04_φ5) (96379025924031/10000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 16) (s := 8) (r := 1) (v := 2) (t := 12) (D := 32)
    (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
    (by norm_num) half_13_04_φ5 (by norm_num [half_13_04_φ1, half_13_04_φ2, half_13_04_φ3, half_13_04_φ4, half_13_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_04_φ1, half_13_04_φ2, half_13_04_φ3, half_13_04_φ4, half_13_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_13_04_hF1 half_13_04_hF2 half_12_04
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_13_04_φ1, half_13_04_φ2, half_13_04_φ3, half_13_04_φ4, half_13_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_04_hx4 : SourcePowerBound (powerBoxCross 16 9 16 half_13_04_φ4) (104482180974829/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 4) (s := 9) (u := 7) (t := 10)
    (D := 16) (ψ := (48931924653/2500000000000 : ℝ)) half_13_04_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_04_φ1, half_13_04_φ2, half_13_04_φ3, half_13_04_φ4, half_13_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_04_φ1, half_13_04_φ2, half_13_04_φ3, half_13_04_φ4, half_13_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_04_φ1, half_13_04_φ2, half_13_04_φ3, half_13_04_φ4, half_13_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8 half_10_04
    (by simpa only [half_13_04_φ5, show (2:ℝ)*16=32 by norm_num] using half_13_04_hx5)
  exact h.weaken (by norm_num [half_13_04_φ1, half_13_04_φ2, half_13_04_φ3, half_13_04_φ4, half_13_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_04_hx3 : SourcePowerBound (powerBoxCross 16 10 8 half_13_04_φ3) (57988015458611/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 10) (u := 8) (t := 11)
    (D := 8) (ψ := (36693040221/1000000000000 : ℝ)) half_13_04_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_04_φ1, half_13_04_φ2, half_13_04_φ3, half_13_04_φ4, half_13_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_04_φ1, half_13_04_φ2, half_13_04_φ3, half_13_04_φ4, half_13_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_04_φ1, half_13_04_φ2, half_13_04_φ3, half_13_04_φ4, half_13_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_04 half_11_04
    (by simpa only [half_13_04_φ4, show (2:ℝ)*8=16 by norm_num] using half_13_04_hx4)
  exact h.weaken (by norm_num [half_13_04_φ1, half_13_04_φ2, half_13_04_φ3, half_13_04_φ4, half_13_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_04_hx2 : SourcePowerBound (powerBoxCross 16 11 4 half_13_04_φ2) (25945666393643/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 11) (u := 9) (t := 12)
    (D := 4) (ψ := (207439557561/5000000000000 : ℝ)) half_13_04_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_04_φ1, half_13_04_φ2, half_13_04_φ3, half_13_04_φ4, half_13_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_04_φ1, half_13_04_φ2, half_13_04_φ3, half_13_04_φ4, half_13_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_04_φ1, half_13_04_φ2, half_13_04_φ3, half_13_04_φ4, half_13_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_04 half_12_04
    (by simpa only [half_13_04_φ3, show (2:ℝ)*4=8 by norm_num] using half_13_04_hx3)
  exact h.weaken (by norm_num [half_13_04_φ1, half_13_04_φ2, half_13_04_φ3, half_13_04_φ4, half_13_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_04_hx1 : SourcePowerBound (powerBoxCross 16 12 2 half_13_04_φ1) (36434116568991/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 12) (u := 10) (t := 13)
    (D := 2) (ψ := (13620185691/312500000000 : ℝ)) half_13_04_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_04_φ1, half_13_04_φ2, half_13_04_φ3, half_13_04_φ4, half_13_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_04_φ1, half_13_04_φ2, half_13_04_φ3, half_13_04_φ4, half_13_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_04_φ1, half_13_04_φ2, half_13_04_φ3, half_13_04_φ4, half_13_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_04 half_13_03
    (by simpa only [half_13_04_φ2, show (2:ℝ)*2=4 by norm_num] using half_13_04_hx2)
  exact h.weaken (by norm_num [half_13_04_φ1, half_13_04_φ2, half_13_04_φ3, half_13_04_φ4, half_13_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_04 : AdmissibleExponent 16 26 (156400397881507/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 11) (ψ := (463649200241/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_12_04
    (by simpa only [half_13_04_φ1] using half_13_04_hx1)
  exact admissibleExponent_mono h (by norm_num [half_13_04_φ1, half_13_04_φ2, half_13_04_φ3, half_13_04_φ4, half_13_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_14_04_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (48090158377/1000000000000 : ℝ)

private def half_14_04_φ2 : Fin 2 → ℝ := Fin.snoc half_14_04_φ1 (448880168453/10000000000000 : ℝ)

private def half_14_04_φ3 : Fin 3 → ℝ := Fin.snoc half_14_04_φ2 (429937168971/10000000000000 : ℝ)

private def half_14_04_φ4 : Fin 4 → ℝ := Fin.snoc half_14_04_φ3 (197561452247/5000000000000 : ℝ)

private def half_14_04_φ5 : Fin 5 → ℝ := Fin.snoc half_14_04_φ4 (7237400217/250000000000 : ℝ)

private theorem half_14_04_hF2 : SourcePowerBound (paddedMoment 16 0 2 32 half_14_04_φ5) (121882496021/15625000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_14_04_φ5 (by norm_num [half_14_04_φ1, half_14_04_φ2, half_14_04_φ3, half_14_04_φ4, half_14_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_04_φ1, half_14_04_φ2, half_14_04_φ3, half_14_04_φ4, half_14_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_04_φ1, half_14_04_φ2, half_14_04_φ3, half_14_04_φ4, half_14_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_14_04_φ1, half_14_04_φ2, half_14_04_φ3, half_14_04_φ4, half_14_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_14_04_hx5 : SourcePowerBound (powerBoxCross 16 9 32 half_14_04_φ5) (10413930062283/1000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 16) (s := 9) (r := 2) (v := 12) (w := 12) (D := 32)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_14_04_φ5 (by norm_num [half_14_04_φ1, half_14_04_φ2, half_14_04_φ3, half_14_04_φ4, half_14_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_04_φ1, half_14_04_φ2, half_14_04_φ3, half_14_04_φ4, half_14_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_14_04_hF2 half_12_04 half_12_04
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_14_04_φ1, half_14_04_φ2, half_14_04_φ3, half_14_04_φ4, half_14_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_04_hx4 : SourcePowerBound (powerBoxCross 16 10 16 half_14_04_φ4) (4561187552097/400000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 4) (s := 10) (u := 8) (t := 11)
    (D := 16) (ψ := (7237400217/250000000000 : ℝ)) half_14_04_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_04_φ1, half_14_04_φ2, half_14_04_φ3, half_14_04_φ4, half_14_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_04_φ1, half_14_04_φ2, half_14_04_φ3, half_14_04_φ4, half_14_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_04_φ1, half_14_04_φ2, half_14_04_φ3, half_14_04_φ4, half_14_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_04 half_11_04
    (by simpa only [half_14_04_φ5, show (2:ℝ)*16=32 by norm_num] using half_14_04_hx5)
  exact h.weaken (by norm_num [half_14_04_φ1, half_14_04_φ2, half_14_04_φ3, half_14_04_φ4, half_14_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_04_hx3 : SourcePowerBound (powerBoxCross 16 11 8 half_14_04_φ3) (12685166911503/1000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 11) (u := 9) (t := 12)
    (D := 8) (ψ := (197561452247/5000000000000 : ℝ)) half_14_04_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_04_φ1, half_14_04_φ2, half_14_04_φ3, half_14_04_φ4, half_14_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_04_φ1, half_14_04_φ2, half_14_04_φ3, half_14_04_φ4, half_14_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_04_φ1, half_14_04_φ2, half_14_04_φ3, half_14_04_φ4, half_14_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_04 half_12_04
    (by simpa only [half_14_04_φ4, show (2:ℝ)*8=16 by norm_num] using half_14_04_hx4)
  exact h.weaken (by norm_num [half_14_04_φ1, half_14_04_φ2, half_14_04_φ3, half_14_04_φ4, half_14_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_04_hx2 : SourcePowerBound (powerBoxCross 16 12 4 half_14_04_φ2) (7094804941563/500000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 12) (u := 10) (t := 13)
    (D := 4) (ψ := (429937168971/10000000000000 : ℝ)) half_14_04_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_04_φ1, half_14_04_φ2, half_14_04_φ3, half_14_04_φ4, half_14_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_04_φ1, half_14_04_φ2, half_14_04_φ3, half_14_04_φ4, half_14_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_04_φ1, half_14_04_φ2, half_14_04_φ3, half_14_04_φ4, half_14_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_04 half_13_04
    (by simpa only [half_14_04_φ3, show (2:ℝ)*4=8 by norm_num] using half_14_04_hx3)
  exact h.weaken (by norm_num [half_14_04_φ1, half_14_04_φ2, half_14_04_φ3, half_14_04_φ4, half_14_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_04_hx1 : SourcePowerBound (powerBoxCross 16 13 2 half_14_04_φ1) (79679989780473/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 13) (u := 11) (t := 14)
    (D := 2) (ψ := (448880168453/10000000000000 : ℝ)) half_14_04_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_04_φ1, half_14_04_φ2, half_14_04_φ3, half_14_04_φ4, half_14_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_04_φ1, half_14_04_φ2, half_14_04_φ3, half_14_04_φ4, half_14_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_04_φ1, half_14_04_φ2, half_14_04_φ3, half_14_04_φ4, half_14_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_04 half_14_03
    (by simpa only [half_14_04_φ2, show (2:ℝ)*2=4 by norm_num] using half_14_04_hx2)
  exact h.weaken (by norm_num [half_14_04_φ1, half_14_04_φ2, half_14_04_φ3, half_14_04_φ4, half_14_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_04 : AdmissibleExponent 16 28 (42845629788799/2500000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 12) (ψ := (48090158377/1000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_13_04
    (by simpa only [half_14_04_φ1] using half_14_04_hx1)
  exact admissibleExponent_mono h (by norm_num [half_14_04_φ1, half_14_04_φ2, half_14_04_φ3, half_14_04_φ4, half_14_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_9_05_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (12430472991/312500000000 : ℝ)

private def half_9_05_φ2 : Fin 2 → ℝ := Fin.snoc half_9_05_φ1 (89838297933/2500000000000 : ℝ)

private def half_9_05_φ3 : Fin 3 → ℝ := Fin.snoc half_9_05_φ2 (199579595281/10000000000000 : ℝ)

private theorem half_9_05_hF2 : SourcePowerBound (paddedMoment 16 0 2 8 half_9_05_φ3) (535585147819/80000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_05_φ3 (by norm_num [half_9_05_φ1, half_9_05_φ2, half_9_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_05_φ1, half_9_05_φ2, half_9_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_05_φ1, half_9_05_φ2, half_9_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_05_φ1, half_9_05_φ2, half_9_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_9_05_hF1 : SourcePowerBound (paddedMoment 16 0 1 8 half_9_05_φ3) (205195049273/80000000000 : ℝ) := by
  have h := padded_second_power (k := 16) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_05_φ3 (by norm_num [half_9_05_φ1, half_9_05_φ2, half_9_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_05_φ1, half_9_05_φ2, half_9_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_05_φ1, half_9_05_φ2, half_9_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_05_φ1, half_9_05_φ2, half_9_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_9_05_hx3 : SourcePowerBound (powerBoxCross 16 6 8 half_9_05_φ3) (38094100194857/5000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 16) (s := 6) (r := 1) (v := 2) (t := 9) (D := 8)
    (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
    (by norm_num) half_9_05_φ3 (by norm_num [half_9_05_φ1, half_9_05_φ2, half_9_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_05_φ1, half_9_05_φ2, half_9_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_9_05_hF1 half_9_05_hF2 half_9_04
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_9_05_φ1, half_9_05_φ2, half_9_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_05_hx2 : SourcePowerBound (powerBoxCross 16 7 4 half_9_05_φ2) (84136874454949/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 7) (u := 5) (t := 8)
    (D := 4) (ψ := (199579595281/10000000000000 : ℝ)) half_9_05_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_05_φ1, half_9_05_φ2, half_9_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_05_φ1, half_9_05_φ2, half_9_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_05_φ1, half_9_05_φ2, half_9_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_6 SeedCompletionEven16SecondSeeds.degree16_half_8
    (by simpa only [half_9_05_φ3, show (2:ℝ)*4=8 by norm_num] using half_9_05_hx3)
  exact h.weaken (by norm_num [half_9_05_φ1, half_9_05_φ2, half_9_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_05_hx1 : SourcePowerBound (powerBoxCross 16 8 2 half_9_05_φ1) (11850459410141/1250000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 8) (u := 6) (t := 9)
    (D := 2) (ψ := (89838297933/2500000000000 : ℝ)) half_9_05_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_05_φ1, half_9_05_φ2, half_9_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_05_φ1, half_9_05_φ2, half_9_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_05_φ1, half_9_05_φ2, half_9_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_7 half_9_04
    (by simpa only [half_9_05_φ2, show (2:ℝ)*2=4 by norm_num] using half_9_05_hx2)
  exact h.weaken (by norm_num [half_9_05_φ1, half_9_05_φ2, half_9_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_05 : AdmissibleExponent 16 18 (12596287789601/1250000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 7) (ψ := (12430472991/312500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8
    (by simpa only [half_9_05_φ1] using half_9_05_hx1)
  exact admissibleExponent_mono h (by norm_num [half_9_05_φ1, half_9_05_φ2, half_9_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_10_05_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (51365859509/1250000000000 : ℝ)

private def half_10_05_φ2 : Fin 2 → ℝ := Fin.snoc half_10_05_φ1 (191501100837/5000000000000 : ℝ)

private def half_10_05_φ3 : Fin 3 → ℝ := Fin.snoc half_10_05_φ2 (57852366731/2000000000000 : ℝ)

private theorem half_10_05_hF2 : SourcePowerBound (paddedMoment 16 0 2 8 half_10_05_φ3) (12251281797391/2000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_10_05_φ3 (by norm_num [half_10_05_φ1, half_10_05_φ2, half_10_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_05_φ1, half_10_05_φ2, half_10_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_05_φ1, half_10_05_φ2, half_10_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_10_05_φ1, half_10_05_φ2, half_10_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_10_05_hx3 : SourcePowerBound (powerBoxCross 16 7 8 half_10_05_φ3) (21416024016199/2500000000000 : ℝ) := by
  have h := full_A_cross_power (k := 16) (s := 7) (r := 2) (v := 9) (w := 10) (D := 8)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_10_05_φ3 (by norm_num [half_10_05_φ1, half_10_05_φ2, half_10_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_05_φ1, half_10_05_φ2, half_10_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_10_05_hF2 half_9_05 half_10_04
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_10_05_φ1, half_10_05_φ2, half_10_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_10_05_hx2 : SourcePowerBound (powerBoxCross 16 8 4 half_10_05_φ2) (95142709367337/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 8) (u := 6) (t := 9)
    (D := 4) (ψ := (57852366731/2000000000000 : ℝ)) half_10_05_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_05_φ1, half_10_05_φ2, half_10_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_05_φ1, half_10_05_φ2, half_10_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_05_φ1, half_10_05_φ2, half_10_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_7 half_9_05
    (by simpa only [half_10_05_φ3, show (2:ℝ)*4=8 by norm_num] using half_10_05_hx3)
  exact h.weaken (by norm_num [half_10_05_φ1, half_10_05_φ2, half_10_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_10_05_hx1 : SourcePowerBound (powerBoxCross 16 9 2 half_10_05_φ1) (107040306639701/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 9) (u := 7) (t := 10)
    (D := 2) (ψ := (191501100837/5000000000000 : ℝ)) half_10_05_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_05_φ1, half_10_05_φ2, half_10_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_05_φ1, half_10_05_φ2, half_10_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_05_φ1, half_10_05_φ2, half_10_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8 half_10_04
    (by simpa only [half_10_05_φ2, show (2:ℝ)*2=4 by norm_num] using half_10_05_hx2)
  exact h.weaken (by norm_num [half_10_05_φ1, half_10_05_φ2, half_10_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_10_05 : AdmissibleExponent 16 20 (4561042541317/400000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 8) (ψ := (51365859509/1250000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_9_05
    (by simpa only [half_10_05_φ1] using half_10_05_hx1)
  exact admissibleExponent_mono h (by norm_num [half_10_05_φ1, half_10_05_φ2, half_10_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_11_05_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (21320459831/500000000000 : ℝ)

private def half_11_05_φ2 : Fin 2 → ℝ := Fin.snoc half_11_05_φ1 (405052351749/10000000000000 : ℝ)

private def half_11_05_φ3 : Fin 3 → ℝ := Fin.snoc half_11_05_φ2 (361458566227/10000000000000 : ℝ)

private def half_11_05_φ4 : Fin 4 → ℝ := Fin.snoc half_11_05_φ3 (92531125221/5000000000000 : ℝ)

private theorem half_11_05_hF2 : SourcePowerBound (paddedMoment 16 0 2 16 half_11_05_φ4) (7799079357329/1000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_11_05_φ4 (by norm_num [half_11_05_φ1, half_11_05_φ2, half_11_05_φ3, half_11_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_05_φ1, half_11_05_φ2, half_11_05_φ3, half_11_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_05_φ1, half_11_05_φ2, half_11_05_φ3, half_11_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_11_05_φ1, half_11_05_φ2, half_11_05_φ3, half_11_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_11_05_hF1 : SourcePowerBound (paddedMoment 16 0 1 16 half_11_05_φ4) (2933026452443/1000000000000 : ℝ) := by
  have h := padded_second_power (k := 16) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_11_05_φ4 (by norm_num [half_11_05_φ1, half_11_05_φ2, half_11_05_φ3, half_11_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_05_φ1, half_11_05_φ2, half_11_05_φ3, half_11_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_05_φ1, half_11_05_φ2, half_11_05_φ3, half_11_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_11_05_φ1, half_11_05_φ2, half_11_05_φ3, half_11_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_11_05_hx4 : SourcePowerBound (powerBoxCross 16 7 16 half_11_05_φ4) (43675308155467/5000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 16) (s := 7) (r := 1) (v := 2) (t := 10) (D := 16)
    (a := (1/10 : ℝ)) (b := (1/5 : ℝ)) (c := (7/10 : ℝ))
    (by norm_num) half_11_05_φ4 (by norm_num [half_11_05_φ1, half_11_05_φ2, half_11_05_φ3, half_11_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_05_φ1, half_11_05_φ2, half_11_05_φ3, half_11_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_11_05_hF1 half_11_05_hF2 half_10_05
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_11_05_φ1, half_11_05_φ2, half_11_05_φ3, half_11_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_11_05_hx3 : SourcePowerBound (powerBoxCross 16 8 8 half_11_05_φ3) (95305917052893/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 8) (u := 6) (t := 9)
    (D := 8) (ψ := (92531125221/5000000000000 : ℝ)) half_11_05_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_05_φ1, half_11_05_φ2, half_11_05_φ3, half_11_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_05_φ1, half_11_05_φ2, half_11_05_φ3, half_11_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_05_φ1, half_11_05_φ2, half_11_05_φ3, half_11_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_7 half_9_05
    (by simpa only [half_11_05_φ4, show (2:ℝ)*8=16 by norm_num] using half_11_05_hx4)
  exact h.weaken (by norm_num [half_11_05_φ1, half_11_05_φ2, half_11_05_φ3, half_11_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_11_05_hx2 : SourcePowerBound (powerBoxCross 16 9 4 half_11_05_φ2) (106400553559869/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 9) (u := 7) (t := 10)
    (D := 4) (ψ := (361458566227/10000000000000 : ℝ)) half_11_05_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_05_φ1, half_11_05_φ2, half_11_05_φ3, half_11_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_05_φ1, half_11_05_φ2, half_11_05_φ3, half_11_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_05_φ1, half_11_05_φ2, half_11_05_φ3, half_11_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8 half_10_05
    (by simpa only [half_11_05_φ3, show (2:ℝ)*4=8 by norm_num] using half_11_05_hx3)
  exact h.weaken (by norm_num [half_11_05_φ1, half_11_05_φ2, half_11_05_φ3, half_11_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_11_05_hx1 : SourcePowerBound (powerBoxCross 16 10 2 half_11_05_φ1) (233574797881/19531250000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 10) (u := 8) (t := 11)
    (D := 2) (ψ := (405052351749/10000000000000 : ℝ)) half_11_05_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_05_φ1, half_11_05_φ2, half_11_05_φ3, half_11_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_05_φ1, half_11_05_φ2, half_11_05_φ3, half_11_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_05_φ1, half_11_05_φ2, half_11_05_φ3, half_11_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_05 half_11_04
    (by simpa only [half_11_05_φ2, show (2:ℝ)*2=4 by norm_num] using half_11_05_hx2)
  exact h.weaken (by norm_num [half_11_05_φ1, half_11_05_φ2, half_11_05_φ3, half_11_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_11_05 : AdmissibleExponent 16 22 (31923017812713/2500000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 9) (ψ := (21320459831/500000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_10_05
    (by simpa only [half_11_05_φ1] using half_11_05_hx1)
  exact admissibleExponent_mono h (by norm_num [half_11_05_φ1, half_11_05_φ2, half_11_05_φ3, half_11_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_12_05_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (220000290111/5000000000000 : ℝ)

private def half_12_05_φ2 : Fin 2 → ℝ := Fin.snoc half_12_05_φ1 (419901896801/10000000000000 : ℝ)

private def half_12_05_φ3 : Fin 3 → ℝ := Fin.snoc half_12_05_φ2 (386457538483/10000000000000 : ℝ)

private def half_12_05_φ4 : Fin 4 → ℝ := Fin.snoc half_12_05_φ3 (281159019869/10000000000000 : ℝ)

private theorem half_12_05_hF2 : SourcePowerBound (paddedMoment 16 0 2 16 half_12_05_φ4) (114018629453/16000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_12_05_φ4 (by norm_num [half_12_05_φ1, half_12_05_φ2, half_12_05_φ3, half_12_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_05_φ1, half_12_05_φ2, half_12_05_φ3, half_12_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_05_φ1, half_12_05_φ2, half_12_05_φ3, half_12_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_12_05_φ1, half_12_05_φ2, half_12_05_φ3, half_12_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_12_05_hx4 : SourcePowerBound (powerBoxCross 16 8 16 half_12_05_φ4) (96060934321197/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 16) (s := 8) (r := 2) (v := 10) (w := 11) (D := 16)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_12_05_φ4 (by norm_num [half_12_05_φ1, half_12_05_φ2, half_12_05_φ3, half_12_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_05_φ1, half_12_05_φ2, half_12_05_φ3, half_12_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_12_05_hF2 half_10_05 half_11_05
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_12_05_φ1, half_12_05_φ2, half_12_05_φ3, half_12_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_12_05_hx3 : SourcePowerBound (powerBoxCross 16 9 8 half_12_05_φ3) (13212326893017/1250000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 9) (u := 7) (t := 10)
    (D := 8) (ψ := (281159019869/10000000000000 : ℝ)) half_12_05_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_05_φ1, half_12_05_φ2, half_12_05_φ3, half_12_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_05_φ1, half_12_05_φ2, half_12_05_φ3, half_12_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_05_φ1, half_12_05_φ2, half_12_05_φ3, half_12_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8 half_10_05
    (by simpa only [half_12_05_φ4, show (2:ℝ)*8=16 by norm_num] using half_12_05_hx4)
  exact h.weaken (by norm_num [half_12_05_φ1, half_12_05_φ2, half_12_05_φ3, half_12_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_12_05_hx2 : SourcePowerBound (powerBoxCross 16 10 4 half_12_05_φ2) (118040827278687/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 10) (u := 8) (t := 11)
    (D := 4) (ψ := (386457538483/10000000000000 : ℝ)) half_12_05_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_05_φ1, half_12_05_φ2, half_12_05_φ3, half_12_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_05_φ1, half_12_05_φ2, half_12_05_φ3, half_12_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_05_φ1, half_12_05_φ2, half_12_05_φ3, half_12_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_05 half_11_05
    (by simpa only [half_12_05_φ3, show (2:ℝ)*4=8 by norm_num] using half_12_05_hx3)
  exact h.weaken (by norm_num [half_12_05_φ1, half_12_05_φ2, half_12_05_φ3, half_12_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_12_05_hx1 : SourcePowerBound (powerBoxCross 16 11 2 half_12_05_φ1) (5300544531483/400000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 11) (u := 9) (t := 12)
    (D := 2) (ψ := (419901896801/10000000000000 : ℝ)) half_12_05_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_05_φ1, half_12_05_φ2, half_12_05_φ3, half_12_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_05_φ1, half_12_05_φ2, half_12_05_φ3, half_12_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_05_φ1, half_12_05_φ2, half_12_05_φ3, half_12_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_05 half_12_04
    (by simpa only [half_12_05_φ2, show (2:ℝ)*2=4 by norm_num] using half_12_05_hx2)
  exact h.weaken (by norm_num [half_12_05_φ1, half_12_05_φ2, half_12_05_φ3, half_12_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_12_05 : AdmissibleExponent 16 24 (141753625471737/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 10) (ψ := (220000290111/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_11_05
    (by simpa only [half_12_05_φ1] using half_12_05_hx1)
  exact admissibleExponent_mono h (by norm_num [half_12_05_φ1, half_12_05_φ2, half_12_05_φ3, half_12_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_13_05_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (227714036039/5000000000000 : ℝ)

private def half_13_05_φ2 : Fin 2 → ℝ := Fin.snoc half_13_05_φ1 (17398863353/400000000000 : ℝ)

private def half_13_05_φ3 : Fin 3 → ℝ := Fin.snoc half_13_05_φ2 (103483793249/2500000000000 : ℝ)

private def half_13_05_φ4 : Fin 4 → ℝ := Fin.snoc half_13_05_φ3 (364659843297/10000000000000 : ℝ)

private def half_13_05_φ5 : Fin 5 → ℝ := Fin.snoc half_13_05_φ4 (186685327267/10000000000000 : ℝ)

private theorem half_13_05_hF2 : SourcePowerBound (paddedMoment 16 0 2 32 half_13_05_φ5) (17298880004833/2000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_13_05_φ5 (by norm_num [half_13_05_φ1, half_13_05_φ2, half_13_05_φ3, half_13_05_φ4, half_13_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_05_φ1, half_13_05_φ2, half_13_05_φ3, half_13_05_φ4, half_13_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_05_φ1, half_13_05_φ2, half_13_05_φ3, half_13_05_φ4, half_13_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_13_05_φ1, half_13_05_φ2, half_13_05_φ3, half_13_05_φ4, half_13_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_13_05_hF1 : SourcePowerBound (paddedMoment 16 0 1 32 half_13_05_φ5) (6432960001611/2000000000000 : ℝ) := by
  have h := padded_second_power (k := 16) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_13_05_φ5 (by norm_num [half_13_05_φ1, half_13_05_φ2, half_13_05_φ3, half_13_05_φ4, half_13_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_05_φ1, half_13_05_φ2, half_13_05_φ3, half_13_05_φ4, half_13_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_05_φ1, half_13_05_φ2, half_13_05_φ3, half_13_05_φ4, half_13_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_13_05_φ1, half_13_05_φ2, half_13_05_φ3, half_13_05_φ4, half_13_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_13_05_hx5 : SourcePowerBound (powerBoxCross 16 8 32 half_13_05_φ5) (96742325810577/10000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 16) (s := 8) (r := 1) (v := 2) (t := 12) (D := 32)
    (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
    (by norm_num) half_13_05_φ5 (by norm_num [half_13_05_φ1, half_13_05_φ2, half_13_05_φ3, half_13_05_φ4, half_13_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_05_φ1, half_13_05_φ2, half_13_05_φ3, half_13_05_φ4, half_13_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_13_05_hF1 half_13_05_hF2 half_12_05
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_13_05_φ1, half_13_05_φ2, half_13_05_φ3, half_13_05_φ4, half_13_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_05_hx4 : SourcePowerBound (powerBoxCross 16 9 16 half_13_05_φ4) (104751429958389/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 4) (s := 9) (u := 7) (t := 10)
    (D := 16) (ψ := (186685327267/10000000000000 : ℝ)) half_13_05_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_05_φ1, half_13_05_φ2, half_13_05_φ3, half_13_05_φ4, half_13_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_05_φ1, half_13_05_φ2, half_13_05_φ3, half_13_05_φ4, half_13_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_05_φ1, half_13_05_φ2, half_13_05_φ3, half_13_05_φ4, half_13_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8 half_10_05
    (by simpa only [half_13_05_φ5, show (2:ℝ)*16=32 by norm_num] using half_13_05_hx5)
  exact h.weaken (by norm_num [half_13_05_φ1, half_13_05_φ2, half_13_05_φ3, half_13_05_φ4, half_13_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_05_hx3 : SourcePowerBound (powerBoxCross 16 10 8 half_13_05_φ3) (58105593630283/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 10) (u := 8) (t := 11)
    (D := 8) (ψ := (364659843297/10000000000000 : ℝ)) half_13_05_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_05_φ1, half_13_05_φ2, half_13_05_φ3, half_13_05_φ4, half_13_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_05_φ1, half_13_05_φ2, half_13_05_φ3, half_13_05_φ4, half_13_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_05_φ1, half_13_05_φ2, half_13_05_φ3, half_13_05_φ4, half_13_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_05 half_11_05
    (by simpa only [half_13_05_φ4, show (2:ℝ)*8=16 by norm_num] using half_13_05_hx4)
  exact h.weaken (by norm_num [half_13_05_φ1, half_13_05_φ2, half_13_05_φ3, half_13_05_φ4, half_13_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_05_hx2 : SourcePowerBound (powerBoxCross 16 11 4 half_13_05_φ2) (12992592412319/1000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 11) (u := 9) (t := 12)
    (D := 4) (ψ := (103483793249/2500000000000 : ℝ)) half_13_05_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_05_φ1, half_13_05_φ2, half_13_05_φ3, half_13_05_φ4, half_13_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_05_φ1, half_13_05_φ2, half_13_05_φ3, half_13_05_φ4, half_13_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_05_φ1, half_13_05_φ2, half_13_05_φ3, half_13_05_φ4, half_13_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_05 half_12_05
    (by simpa only [half_13_05_φ3, show (2:ℝ)*4=8 by norm_num] using half_13_05_hx3)
  exact h.weaken (by norm_num [half_13_05_φ1, half_13_05_φ2, half_13_05_φ3, half_13_05_φ4, half_13_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_05_hx1 : SourcePowerBound (powerBoxCross 16 12 2 half_13_05_φ1) (36438298876989/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 12) (u := 10) (t := 13)
    (D := 2) (ψ := (17398863353/400000000000 : ℝ)) half_13_05_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_05_φ1, half_13_05_φ2, half_13_05_φ3, half_13_05_φ4, half_13_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_05_φ1, half_13_05_φ2, half_13_05_φ3, half_13_05_φ4, half_13_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_05_φ1, half_13_05_φ2, half_13_05_φ3, half_13_05_φ4, half_13_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_05 half_13_04
    (by simpa only [half_13_05_φ2, show (2:ℝ)*2=4 by norm_num] using half_13_05_hx2)
  exact h.weaken (by norm_num [half_13_05_φ1, half_13_05_φ2, half_13_05_φ3, half_13_05_φ4, half_13_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_05 : AdmissibleExponent 16 26 (624912164663/40000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 11) (ψ := (227714036039/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_12_05
    (by simpa only [half_13_05_φ1] using half_13_05_hx1)
  exact admissibleExponent_mono h (by norm_num [half_13_05_φ1, half_13_05_φ2, half_13_05_φ3, half_13_05_φ4, half_13_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_14_05_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (470263015201/10000000000000 : ℝ)

private def half_14_05_φ2 : Fin 2 → ℝ := Fin.snoc half_14_05_φ1 (223943887329/5000000000000 : ℝ)

private def half_14_05_φ3 : Fin 3 → ℝ := Fin.snoc half_14_05_φ2 (17148924381/400000000000 : ℝ)

private def half_14_05_φ4 : Fin 4 → ℝ := Fin.snoc half_14_05_φ3 (196389060843/5000000000000 : ℝ)

private def half_14_05_φ5 : Fin 5 → ℝ := Fin.snoc half_14_05_φ4 (281462894969/10000000000000 : ℝ)

private theorem half_14_05_hF2 : SourcePowerBound (paddedMoment 16 0 2 32 half_14_05_φ5) (15809965755649/2000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_14_05_φ5 (by norm_num [half_14_05_φ1, half_14_05_φ2, half_14_05_φ3, half_14_05_φ4, half_14_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_05_φ1, half_14_05_φ2, half_14_05_φ3, half_14_05_φ4, half_14_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_05_φ1, half_14_05_φ2, half_14_05_φ3, half_14_05_φ4, half_14_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_14_05_φ1, half_14_05_φ2, half_14_05_φ3, half_14_05_φ4, half_14_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_14_05_hx5 : SourcePowerBound (powerBoxCross 16 9 32 half_14_05_φ5) (104590148785099/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 16) (s := 9) (r := 2) (v := 12) (w := 12) (D := 32)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_14_05_φ5 (by norm_num [half_14_05_φ1, half_14_05_φ2, half_14_05_φ3, half_14_05_φ4, half_14_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_05_φ1, half_14_05_φ2, half_14_05_φ3, half_14_05_φ4, half_14_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_14_05_hF2 half_12_05 half_12_05
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_14_05_φ1, half_14_05_φ2, half_14_05_φ3, half_14_05_φ4, half_14_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_05_hx4 : SourcePowerBound (powerBoxCross 16 10 16 half_14_05_φ4) (114379165975881/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 4) (s := 10) (u := 8) (t := 11)
    (D := 16) (ψ := (281462894969/10000000000000 : ℝ)) half_14_05_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_05_φ1, half_14_05_φ2, half_14_05_φ3, half_14_05_φ4, half_14_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_05_φ1, half_14_05_φ2, half_14_05_φ3, half_14_05_φ4, half_14_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_05_φ1, half_14_05_φ2, half_14_05_φ3, half_14_05_φ4, half_14_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_05 half_11_05
    (by simpa only [half_14_05_φ5, show (2:ℝ)*16=32 by norm_num] using half_14_05_hx5)
  exact h.weaken (by norm_num [half_14_05_φ1, half_14_05_φ2, half_14_05_φ3, half_14_05_φ4, half_14_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_05_hx3 : SourcePowerBound (powerBoxCross 16 11 8 half_14_05_φ3) (1271500207199/100000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 11) (u := 9) (t := 12)
    (D := 8) (ψ := (196389060843/5000000000000 : ℝ)) half_14_05_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_05_φ1, half_14_05_φ2, half_14_05_φ3, half_14_05_φ4, half_14_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_05_φ1, half_14_05_φ2, half_14_05_φ3, half_14_05_φ4, half_14_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_05_φ1, half_14_05_φ2, half_14_05_φ3, half_14_05_φ4, half_14_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_05 half_12_05
    (by simpa only [half_14_05_φ4, show (2:ℝ)*8=16 by norm_num] using half_14_05_hx4)
  exact h.weaken (by norm_num [half_14_05_φ1, half_14_05_φ2, half_14_05_φ3, half_14_05_φ4, half_14_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_05_hx2 : SourcePowerBound (powerBoxCross 16 12 4 half_14_05_φ2) (142132447699173/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 12) (u := 10) (t := 13)
    (D := 4) (ψ := (17148924381/400000000000 : ℝ)) half_14_05_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_05_φ1, half_14_05_φ2, half_14_05_φ3, half_14_05_φ4, half_14_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_05_φ1, half_14_05_φ2, half_14_05_φ3, half_14_05_φ4, half_14_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_05_φ1, half_14_05_φ2, half_14_05_φ3, half_14_05_φ4, half_14_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_05 half_13_05
    (by simpa only [half_14_05_φ3, show (2:ℝ)*4=8 by norm_num] using half_14_05_hx3)
  exact h.weaken (by norm_num [half_14_05_φ1, half_14_05_φ2, half_14_05_φ3, half_14_05_φ4, half_14_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_05_hx1 : SourcePowerBound (powerBoxCross 16 13 2 half_14_05_φ1) (159351477211211/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 13) (u := 11) (t := 14)
    (D := 2) (ψ := (223943887329/5000000000000 : ℝ)) half_14_05_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_05_φ1, half_14_05_φ2, half_14_05_φ3, half_14_05_φ4, half_14_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_05_φ1, half_14_05_φ2, half_14_05_φ3, half_14_05_φ4, half_14_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_05_φ1, half_14_05_φ2, half_14_05_φ3, half_14_05_φ4, half_14_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_05 half_14_04
    (by simpa only [half_14_05_φ2, show (2:ℝ)*2=4 by norm_num] using half_14_05_hx2)
  exact h.weaken (by norm_num [half_14_05_φ1, half_14_05_φ2, half_14_05_φ3, half_14_05_φ4, half_14_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_05 : AdmissibleExponent 16 28 (42777013147809/2500000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 12) (ψ := (470263015201/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_13_05
    (by simpa only [half_14_05_φ1] using half_14_05_hx1)
  exact admissibleExponent_mono h (by norm_num [half_14_05_φ1, half_14_05_φ2, half_14_05_φ3, half_14_05_φ4, half_14_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_9_06_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (397653257641/10000000000000 : ℝ)

private def half_9_06_φ2 : Fin 2 → ℝ := Fin.snoc half_9_06_φ1 (179653057381/5000000000000 : ℝ)

private def half_9_06_φ3 : Fin 3 → ℝ := Fin.snoc half_9_06_φ2 (199312183173/10000000000000 : ℝ)

private theorem half_9_06_hF2 : SourcePowerBound (paddedMoment 16 0 2 8 half_9_06_φ3) (1674194499977/250000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_06_φ3 (by norm_num [half_9_06_φ1, half_9_06_φ2, half_9_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_06_φ1, half_9_06_φ2, half_9_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_06_φ1, half_9_06_φ2, half_9_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_06_φ1, half_9_06_φ2, half_9_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_9_06_hF1 : SourcePowerBound (paddedMoment 16 0 1 8 half_9_06_φ3) (641398166659/250000000000 : ℝ) := by
  have h := padded_second_power (k := 16) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_06_φ3 (by norm_num [half_9_06_φ1, half_9_06_φ2, half_9_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_06_φ1, half_9_06_φ2, half_9_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_06_φ1, half_9_06_φ2, half_9_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_06_φ1, half_9_06_φ2, half_9_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_9_06_hx3 : SourcePowerBound (powerBoxCross 16 6 8 half_9_06_φ3) (76193234405289/10000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 16) (s := 6) (r := 1) (v := 2) (t := 9) (D := 8)
    (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
    (by norm_num) half_9_06_φ3 (by norm_num [half_9_06_φ1, half_9_06_φ2, half_9_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_06_φ1, half_9_06_φ2, half_9_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_9_06_hF1 half_9_06_hF2 half_9_05
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_9_06_φ1, half_9_06_φ2, half_9_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_06_hx2 : SourcePowerBound (powerBoxCross 16 7 4 half_9_06_φ2) (42069965218487/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 7) (u := 5) (t := 8)
    (D := 4) (ψ := (199312183173/10000000000000 : ℝ)) half_9_06_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_06_φ1, half_9_06_φ2, half_9_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_06_φ1, half_9_06_φ2, half_9_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_06_φ1, half_9_06_φ2, half_9_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_6 SeedCompletionEven16SecondSeeds.degree16_half_8
    (by simpa only [half_9_06_φ3, show (2:ℝ)*4=8 by norm_num] using half_9_06_hx3)
  exact h.weaken (by norm_num [half_9_06_φ1, half_9_06_φ2, half_9_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_06_hx1 : SourcePowerBound (powerBoxCross 16 8 2 half_9_06_φ1) (1896092494821/200000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 8) (u := 6) (t := 9)
    (D := 2) (ψ := (179653057381/5000000000000 : ℝ)) half_9_06_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_06_φ1, half_9_06_φ2, half_9_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_06_φ1, half_9_06_φ2, half_9_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_06_φ1, half_9_06_φ2, half_9_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_7 half_9_05
    (by simpa only [half_9_06_φ2, show (2:ℝ)*2=4 by norm_num] using half_9_06_hx2)
  exact h.weaken (by norm_num [half_9_06_φ1, half_9_06_φ2, half_9_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_06 : AdmissibleExponent 16 18 (20153884721133/2000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 7) (ψ := (397653257641/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8
    (by simpa only [half_9_06_φ1] using half_9_06_hx1)
  exact admissibleExponent_mono h (by norm_num [half_9_06_φ1, half_9_06_φ2, half_9_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_10_06_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (82088221853/2000000000000 : ℝ)

private def half_10_06_φ2 : Fin 2 → ℝ := Fin.snoc half_10_06_φ1 (382877264269/10000000000000 : ℝ)

private def half_10_06_φ3 : Fin 3 → ℝ := Fin.snoc half_10_06_φ2 (144381872131/5000000000000 : ℝ)

private theorem half_10_06_hF2 : SourcePowerBound (paddedMoment 16 0 2 8 half_10_06_φ3) (3065315234959/500000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_10_06_φ3 (by norm_num [half_10_06_φ1, half_10_06_φ2, half_10_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_06_φ1, half_10_06_φ2, half_10_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_06_φ1, half_10_06_φ2, half_10_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_10_06_φ1, half_10_06_φ2, half_10_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_10_06_hx3 : SourcePowerBound (powerBoxCross 16 7 8 half_10_06_φ3) (85681125187853/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 16) (s := 7) (r := 2) (v := 9) (w := 10) (D := 8)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_10_06_φ3 (by norm_num [half_10_06_φ1, half_10_06_φ2, half_10_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_06_φ1, half_10_06_φ2, half_10_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_10_06_hF2 half_9_06 half_10_05
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_10_06_φ1, half_10_06_φ2, half_10_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_10_06_hx2 : SourcePowerBound (powerBoxCross 16 8 4 half_10_06_φ2) (47577619585559/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 8) (u := 6) (t := 9)
    (D := 4) (ψ := (144381872131/5000000000000 : ℝ)) half_10_06_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_06_φ1, half_10_06_φ2, half_10_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_06_φ1, half_10_06_φ2, half_10_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_06_φ1, half_10_06_φ2, half_10_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_7 half_9_06
    (by simpa only [half_10_06_φ3, show (2:ℝ)*4=8 by norm_num] using half_10_06_hx3)
  exact h.weaken (by norm_num [half_10_06_φ1, half_10_06_φ2, half_10_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_10_06_hx1 : SourcePowerBound (powerBoxCross 16 9 2 half_10_06_φ1) (107043873314473/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 9) (u := 7) (t := 10)
    (D := 2) (ψ := (382877264269/10000000000000 : ℝ)) half_10_06_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_06_φ1, half_10_06_φ2, half_10_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_06_φ1, half_10_06_φ2, half_10_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_06_φ1, half_10_06_φ2, half_10_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8 half_10_05
    (by simpa only [half_10_06_φ2, show (2:ℝ)*2=4 by norm_num] using half_10_06_hx2)
  exact h.weaken (by norm_num [half_10_06_φ1, half_10_06_φ2, half_10_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_10_06 : AdmissibleExponent 16 20 (57010686085989/5000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 8) (ψ := (82088221853/2000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_9_06
    (by simpa only [half_10_06_φ1] using half_10_06_hx1)
  exact admissibleExponent_mono h (by norm_num [half_10_06_φ1, half_10_06_φ2, half_10_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_11_06_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (26580552017/625000000000 : ℝ)

private def half_11_06_φ2 : Fin 2 → ℝ := Fin.snoc half_11_06_φ1 (404932193833/10000000000000 : ℝ)

private def half_11_06_φ3 : Fin 3 → ℝ := Fin.snoc half_11_06_φ2 (180645867237/5000000000000 : ℝ)

private def half_11_06_φ4 : Fin 4 → ℝ := Fin.snoc half_11_06_φ3 (184345812921/10000000000000 : ℝ)

private theorem half_11_06_hF2 : SourcePowerBound (paddedMoment 16 0 2 16 half_11_06_φ4) (31234545677/4000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_11_06_φ4 (by norm_num [half_11_06_φ1, half_11_06_φ2, half_11_06_φ3, half_11_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_06_φ1, half_11_06_φ2, half_11_06_φ3, half_11_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_06_φ1, half_11_06_φ2, half_11_06_φ3, half_11_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_11_06_φ1, half_11_06_φ2, half_11_06_φ3, half_11_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_11_06_hF1 : SourcePowerBound (paddedMoment 16 0 1 16 half_11_06_φ4) (11744848559/4000000000 : ℝ) := by
  have h := padded_second_power (k := 16) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_11_06_φ4 (by norm_num [half_11_06_φ1, half_11_06_φ2, half_11_06_φ3, half_11_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_06_φ1, half_11_06_φ2, half_11_06_φ3, half_11_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_06_φ1, half_11_06_φ2, half_11_06_φ3, half_11_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_11_06_φ1, half_11_06_φ2, half_11_06_φ3, half_11_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_11_06_hx4 : SourcePowerBound (powerBoxCross 16 7 16 half_11_06_φ4) (43693517863041/5000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 16) (s := 7) (r := 1) (v := 2) (t := 10) (D := 16)
    (a := (1/10 : ℝ)) (b := (1/5 : ℝ)) (c := (7/10 : ℝ))
    (by norm_num) half_11_06_φ4 (by norm_num [half_11_06_φ1, half_11_06_φ2, half_11_06_φ3, half_11_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_06_φ1, half_11_06_φ2, half_11_06_φ3, half_11_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_11_06_hF1 half_11_06_hF2 half_10_06
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_11_06_φ1, half_11_06_φ2, half_11_06_φ3, half_11_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_11_06_hx3 : SourcePowerBound (powerBoxCross 16 8 8 half_11_06_φ3) (95336729040401/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 8) (u := 6) (t := 9)
    (D := 8) (ψ := (184345812921/10000000000000 : ℝ)) half_11_06_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_06_φ1, half_11_06_φ2, half_11_06_φ3, half_11_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_06_φ1, half_11_06_φ2, half_11_06_φ3, half_11_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_06_φ1, half_11_06_φ2, half_11_06_φ3, half_11_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_7 half_9_06
    (by simpa only [half_11_06_φ4, show (2:ℝ)*8=16 by norm_num] using half_11_06_hx4)
  exact h.weaken (by norm_num [half_11_06_φ1, half_11_06_φ2, half_11_06_φ3, half_11_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_11_06_hx2 : SourcePowerBound (powerBoxCross 16 9 4 half_11_06_φ2) (1662952092013/156250000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 9) (u := 7) (t := 10)
    (D := 4) (ψ := (180645867237/5000000000000 : ℝ)) half_11_06_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_06_φ1, half_11_06_φ2, half_11_06_φ3, half_11_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_06_φ1, half_11_06_φ2, half_11_06_φ3, half_11_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_06_φ1, half_11_06_φ2, half_11_06_φ3, half_11_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8 half_10_06
    (by simpa only [half_11_06_φ3, show (2:ℝ)*4=8 by norm_num] using half_11_06_hx3)
  exact h.weaken (by norm_num [half_11_06_φ1, half_11_06_φ2, half_11_06_φ3, half_11_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_11_06_hx1 : SourcePowerBound (powerBoxCross 16 10 2 half_11_06_φ1) (478389837527/40000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 10) (u := 8) (t := 11)
    (D := 2) (ψ := (404932193833/10000000000000 : ℝ)) half_11_06_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_06_φ1, half_11_06_φ2, half_11_06_φ3, half_11_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_06_φ1, half_11_06_φ2, half_11_06_φ3, half_11_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_06_φ1, half_11_06_φ2, half_11_06_φ3, half_11_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_06 half_11_05
    (by simpa only [half_11_06_φ2, show (2:ℝ)*2=4 by norm_num] using half_11_06_hx2)
  exact h.weaken (by norm_num [half_11_06_φ1, half_11_06_φ2, half_11_06_φ3, half_11_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_11_06 : AdmissibleExponent 16 22 (63838973597459/5000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 9) (ψ := (26580552017/625000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_10_06
    (by simpa only [half_11_06_φ1] using half_11_06_hx1)
  exact admissibleExponent_mono h (by norm_num [half_11_06_φ1, half_11_06_φ2, half_11_06_φ3, half_11_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_12_06_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (87555556067/2000000000000 : ℝ)

private def half_12_06_φ2 : Fin 2 → ℝ := Fin.snoc half_12_06_φ1 (104913663349/2500000000000 : ℝ)

private def half_12_06_φ3 : Fin 3 → ℝ := Fin.snoc half_12_06_φ2 (386090392877/10000000000000 : ℝ)

private def half_12_06_φ4 : Fin 4 → ℝ := Fin.snoc half_12_06_φ3 (279870541143/10000000000000 : ℝ)

private theorem half_12_06_hF2 : SourcePowerBound (paddedMoment 16 0 2 16 half_12_06_φ4) (14289459690241/2000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_12_06_φ4 (by norm_num [half_12_06_φ1, half_12_06_φ2, half_12_06_φ3, half_12_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_06_φ1, half_12_06_φ2, half_12_06_φ3, half_12_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_06_φ1, half_12_06_φ2, half_12_06_φ3, half_12_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_12_06_φ1, half_12_06_φ2, half_12_06_φ3, half_12_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_12_06_hx4 : SourcePowerBound (powerBoxCross 16 8 16 half_12_06_φ4) (96138469301299/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 16) (s := 8) (r := 2) (v := 10) (w := 11) (D := 16)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_12_06_φ4 (by norm_num [half_12_06_φ1, half_12_06_φ2, half_12_06_φ3, half_12_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_06_φ1, half_12_06_φ2, half_12_06_φ3, half_12_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_12_06_hF2 half_10_06 half_11_06
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_12_06_φ1, half_12_06_φ2, half_12_06_φ3, half_12_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_12_06_hx3 : SourcePowerBound (powerBoxCross 16 9 8 half_12_06_φ3) (33050974889/3125000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 9) (u := 7) (t := 10)
    (D := 8) (ψ := (279870541143/10000000000000 : ℝ)) half_12_06_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_06_φ1, half_12_06_φ2, half_12_06_φ3, half_12_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_06_φ1, half_12_06_φ2, half_12_06_φ3, half_12_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_06_φ1, half_12_06_φ2, half_12_06_φ3, half_12_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8 half_10_06
    (by simpa only [half_12_06_φ4, show (2:ℝ)*8=16 by norm_num] using half_12_06_hx4)
  exact h.weaken (by norm_num [half_12_06_φ1, half_12_06_φ2, half_12_06_φ3, half_12_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_12_06_hx2 : SourcePowerBound (powerBoxCross 16 10 4 half_12_06_φ2) (29524449464119/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 10) (u := 8) (t := 11)
    (D := 4) (ψ := (386090392877/10000000000000 : ℝ)) half_12_06_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_06_φ1, half_12_06_φ2, half_12_06_φ3, half_12_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_06_φ1, half_12_06_φ2, half_12_06_φ3, half_12_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_06_φ1, half_12_06_φ2, half_12_06_φ3, half_12_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_06 half_11_06
    (by simpa only [half_12_06_φ3, show (2:ℝ)*4=8 by norm_num] using half_12_06_hx3)
  exact h.weaken (by norm_num [half_12_06_φ1, half_12_06_φ2, half_12_06_φ3, half_12_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_12_06_hx1 : SourcePowerBound (powerBoxCross 16 11 2 half_12_06_φ1) (8282891758949/625000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 11) (u := 9) (t := 12)
    (D := 2) (ψ := (104913663349/2500000000000 : ℝ)) half_12_06_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_06_φ1, half_12_06_φ2, half_12_06_φ3, half_12_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_06_φ1, half_12_06_φ2, half_12_06_φ3, half_12_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_06_φ1, half_12_06_φ2, half_12_06_φ3, half_12_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_06 half_12_05
    (by simpa only [half_12_06_φ2, show (2:ℝ)*2=4 by norm_num] using half_12_06_hx2)
  exact h.weaken (by norm_num [half_12_06_φ1, half_12_06_φ2, half_12_06_φ3, half_12_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_12_06 : AdmissibleExponent 16 24 (141719601530219/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 10) (ψ := (87555556067/2000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_11_06
    (by simpa only [half_12_06_φ1] using half_12_06_hx1)
  exact admissibleExponent_mono h (by norm_num [half_12_06_φ1, half_12_06_φ2, half_12_06_φ3, half_12_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_13_06_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (451809296187/10000000000000 : ℝ)

private def half_13_06_φ2 : Fin 2 → ℝ := Fin.snoc half_13_06_φ1 (4345876039/100000000000 : ℝ)

private def half_13_06_φ3 : Fin 3 → ℝ := Fin.snoc half_13_06_φ2 (51696820087/1250000000000 : ℝ)

private def half_13_06_φ4 : Fin 4 → ℝ := Fin.snoc half_13_06_φ3 (363793866133/10000000000000 : ℝ)

private def half_13_06_φ5 : Fin 5 → ℝ := Fin.snoc half_13_06_φ4 (91576423873/5000000000000 : ℝ)

private theorem half_13_06_hF2 : SourcePowerBound (paddedMoment 16 0 2 32 half_13_06_φ5) (8688868214021/1000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_13_06_φ5 (by norm_num [half_13_06_φ1, half_13_06_φ2, half_13_06_φ3, half_13_06_φ4, half_13_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_06_φ1, half_13_06_φ2, half_13_06_φ3, half_13_06_φ4, half_13_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_06_φ1, half_13_06_φ2, half_13_06_φ3, half_13_06_φ4, half_13_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_13_06_φ1, half_13_06_φ2, half_13_06_φ3, half_13_06_φ4, half_13_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_13_06_hF1 : SourcePowerBound (paddedMoment 16 0 1 32 half_13_06_φ5) (3229622738007/1000000000000 : ℝ) := by
  have h := padded_second_power (k := 16) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_13_06_φ5 (by norm_num [half_13_06_φ1, half_13_06_φ2, half_13_06_φ3, half_13_06_φ4, half_13_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_06_φ1, half_13_06_φ2, half_13_06_φ3, half_13_06_φ4, half_13_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_06_φ1, half_13_06_φ2, half_13_06_φ3, half_13_06_φ4, half_13_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_13_06_φ1, half_13_06_φ2, half_13_06_φ3, half_13_06_φ4, half_13_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_13_06_hx5 : SourcePowerBound (powerBoxCross 16 8 32 half_13_06_φ5) (3875770083549/400000000000 : ℝ) := by
  have h := full_B_cross_power (k := 16) (s := 8) (r := 1) (v := 2) (t := 12) (D := 32)
    (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
    (by norm_num) half_13_06_φ5 (by norm_num [half_13_06_φ1, half_13_06_φ2, half_13_06_φ3, half_13_06_φ4, half_13_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_06_φ1, half_13_06_φ2, half_13_06_φ3, half_13_06_φ4, half_13_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_13_06_hF1 half_13_06_hF2 half_12_06
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_13_06_φ1, half_13_06_φ2, half_13_06_φ3, half_13_06_φ4, half_13_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_06_hx4 : SourcePowerBound (powerBoxCross 16 9 16 half_13_06_φ4) (4194719130369/400000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 4) (s := 9) (u := 7) (t := 10)
    (D := 16) (ψ := (91576423873/5000000000000 : ℝ)) half_13_06_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_06_φ1, half_13_06_φ2, half_13_06_φ3, half_13_06_φ4, half_13_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_06_φ1, half_13_06_φ2, half_13_06_φ3, half_13_06_φ4, half_13_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_06_φ1, half_13_06_φ2, half_13_06_φ3, half_13_06_φ4, half_13_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8 half_10_06
    (by simpa only [half_13_06_φ5, show (2:ℝ)*16=32 by norm_num] using half_13_06_hx5)
  exact h.weaken (by norm_num [half_13_06_φ1, half_13_06_φ2, half_13_06_φ3, half_13_06_φ4, half_13_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_06_hx3 : SourcePowerBound (powerBoxCross 16 10 8 half_13_06_φ3) (29079135064273/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 10) (u := 8) (t := 11)
    (D := 8) (ψ := (363793866133/10000000000000 : ℝ)) half_13_06_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_06_φ1, half_13_06_φ2, half_13_06_φ3, half_13_06_φ4, half_13_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_06_φ1, half_13_06_φ2, half_13_06_φ3, half_13_06_φ4, half_13_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_06_φ1, half_13_06_φ2, half_13_06_φ3, half_13_06_φ4, half_13_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_06 half_11_06
    (by simpa only [half_13_06_φ4, show (2:ℝ)*8=16 by norm_num] using half_13_06_hx4)
  exact h.weaken (by norm_num [half_13_06_φ1, half_13_06_φ2, half_13_06_φ3, half_13_06_φ4, half_13_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_06_hx2 : SourcePowerBound (powerBoxCross 16 11 4 half_13_06_φ2) (65009030847859/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 11) (u := 9) (t := 12)
    (D := 4) (ψ := (51696820087/1250000000000 : ℝ)) half_13_06_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_06_φ1, half_13_06_φ2, half_13_06_φ3, half_13_06_φ4, half_13_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_06_φ1, half_13_06_φ2, half_13_06_φ3, half_13_06_φ4, half_13_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_06_φ1, half_13_06_φ2, half_13_06_φ3, half_13_06_φ4, half_13_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_06 half_12_06
    (by simpa only [half_13_06_φ3, show (2:ℝ)*4=8 by norm_num] using half_13_06_hx3)
  exact h.weaken (by norm_num [half_13_06_φ1, half_13_06_φ2, half_13_06_φ3, half_13_06_φ4, half_13_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_06_hx1 : SourcePowerBound (powerBoxCross 16 12 2 half_13_06_φ1) (145768387484093/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 12) (u := 10) (t := 13)
    (D := 2) (ψ := (4345876039/100000000000 : ℝ)) half_13_06_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_06_φ1, half_13_06_φ2, half_13_06_φ3, half_13_06_φ4, half_13_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_06_φ1, half_13_06_φ2, half_13_06_φ3, half_13_06_φ4, half_13_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_06_φ1, half_13_06_φ2, half_13_06_φ3, half_13_06_φ4, half_13_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_06 half_13_05
    (by simpa only [half_13_06_φ2, show (2:ℝ)*2=4 by norm_num] using half_13_06_hx2)
  exact h.weaken (by norm_num [half_13_06_φ1, half_13_06_φ2, half_13_06_φ3, half_13_06_φ4, half_13_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_06 : AdmissibleExponent 16 26 (78080000648197/5000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 11) (ψ := (451809296187/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_12_06
    (by simpa only [half_13_06_φ1] using half_13_06_hx1)
  exact admissibleExponent_mono h (by norm_num [half_13_06_φ1, half_13_06_φ2, half_13_06_φ3, half_13_06_φ4, half_13_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_14_06_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (29063912623/625000000000 : ℝ)

private def half_14_06_φ2 : Fin 2 → ℝ := Fin.snoc half_14_06_φ1 (89472137807/2000000000000 : ℝ)

private def half_14_06_φ3 : Fin 3 → ℝ := Fin.snoc half_14_06_φ2 (85638855831/2000000000000 : ℝ)

private def half_14_06_φ4 : Fin 4 → ℝ := Fin.snoc half_14_06_φ3 (195906853517/5000000000000 : ℝ)

private def half_14_06_φ5 : Fin 5 → ℝ := Fin.snoc half_14_06_φ4 (69528375381/2500000000000 : ℝ)

private theorem half_14_06_hF2 : SourcePowerBound (paddedMoment 16 0 2 32 half_14_06_φ5) (3976364247889/500000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_14_06_φ5 (by norm_num [half_14_06_φ1, half_14_06_φ2, half_14_06_φ3, half_14_06_φ4, half_14_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_06_φ1, half_14_06_φ2, half_14_06_φ3, half_14_06_φ4, half_14_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_06_φ1, half_14_06_φ2, half_14_06_φ3, half_14_06_φ4, half_14_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_14_06_φ1, half_14_06_φ2, half_14_06_φ3, half_14_06_φ4, half_14_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_14_06_hx5 : SourcePowerBound (powerBoxCross 16 9 32 half_14_06_φ5) (52400963589271/5000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 16) (s := 9) (r := 2) (v := 12) (w := 12) (D := 32)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_14_06_φ5 (by norm_num [half_14_06_φ1, half_14_06_φ2, half_14_06_φ3, half_14_06_φ4, half_14_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_06_φ1, half_14_06_φ2, half_14_06_φ3, half_14_06_φ4, half_14_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_14_06_hF2 half_12_06 half_12_06
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_14_06_φ1, half_14_06_φ2, half_14_06_φ3, half_14_06_φ4, half_14_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_06_hx4 : SourcePowerBound (powerBoxCross 16 10 16 half_14_06_φ4) (114551559270233/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 4) (s := 10) (u := 8) (t := 11)
    (D := 16) (ψ := (69528375381/2500000000000 : ℝ)) half_14_06_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_06_φ1, half_14_06_φ2, half_14_06_φ3, half_14_06_φ4, half_14_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_06_φ1, half_14_06_φ2, half_14_06_φ3, half_14_06_φ4, half_14_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_06_φ1, half_14_06_φ2, half_14_06_φ3, half_14_06_φ4, half_14_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_06 half_11_06
    (by simpa only [half_14_06_φ5, show (2:ℝ)*16=32 by norm_num] using half_14_06_hx5)
  exact h.weaken (by norm_num [half_14_06_φ1, half_14_06_φ2, half_14_06_φ3, half_14_06_φ4, half_14_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_06_hx3 : SourcePowerBound (powerBoxCross 16 11 8 half_14_06_φ3) (127304172887707/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 11) (u := 9) (t := 12)
    (D := 8) (ψ := (195906853517/5000000000000 : ℝ)) half_14_06_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_06_φ1, half_14_06_φ2, half_14_06_φ3, half_14_06_φ4, half_14_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_06_φ1, half_14_06_φ2, half_14_06_φ3, half_14_06_φ4, half_14_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_06_φ1, half_14_06_φ2, half_14_06_φ3, half_14_06_φ4, half_14_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_06 half_12_06
    (by simpa only [half_14_06_φ4, show (2:ℝ)*8=16 by norm_num] using half_14_06_hx4)
  exact h.weaken (by norm_num [half_14_06_φ1, half_14_06_φ2, half_14_06_φ3, half_14_06_φ4, half_14_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_06_hx2 : SourcePowerBound (powerBoxCross 16 12 4 half_14_06_φ2) (35565340886341/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 12) (u := 10) (t := 13)
    (D := 4) (ψ := (85638855831/2000000000000 : ℝ)) half_14_06_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_06_φ1, half_14_06_φ2, half_14_06_φ3, half_14_06_φ4, half_14_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_06_φ1, half_14_06_φ2, half_14_06_φ3, half_14_06_φ4, half_14_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_06_φ1, half_14_06_φ2, half_14_06_φ3, half_14_06_φ4, half_14_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_06 half_13_06
    (by simpa only [half_14_06_φ3, show (2:ℝ)*4=8 by norm_num] using half_14_06_hx3)
  exact h.weaken (by norm_num [half_14_06_φ1, half_14_06_φ2, half_14_06_φ3, half_14_06_φ4, half_14_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_06_hx1 : SourcePowerBound (powerBoxCross 16 13 2 half_14_06_φ1) (249005048259/15625000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 13) (u := 11) (t := 14)
    (D := 2) (ψ := (89472137807/2000000000000 : ℝ)) half_14_06_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_06_φ1, half_14_06_φ2, half_14_06_φ3, half_14_06_φ4, half_14_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_06_φ1, half_14_06_φ2, half_14_06_φ3, half_14_06_φ4, half_14_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_06_φ1, half_14_06_φ2, half_14_06_φ3, half_14_06_φ4, half_14_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_06 half_14_05
    (by simpa only [half_14_06_φ2, show (2:ℝ)*2=4 by norm_num] using half_14_06_hx2)
  exact h.weaken (by norm_num [half_14_06_φ1, half_14_06_φ2, half_14_06_φ3, half_14_06_φ4, half_14_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_06 : AdmissibleExponent 16 28 (2137359949187/125000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 12) (ψ := (29063912623/625000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_13_06
    (by simpa only [half_14_06_φ1] using half_14_06_hx1)
  exact admissibleExponent_mono h (by norm_num [half_14_06_φ1, half_14_06_φ2, half_14_06_φ3, half_14_06_φ4, half_14_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_9_07_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (397624702781/10000000000000 : ℝ)

private def half_9_07_φ2 : Fin 2 → ℝ := Fin.snoc half_9_07_φ1 (359295084717/10000000000000 : ℝ)

private def half_9_07_φ3 : Fin 3 → ℝ := Fin.snoc half_9_07_φ2 (7969981161/400000000000 : ℝ)

private theorem half_9_07_hF2 : SourcePowerBound (paddedMoment 16 0 2 8 half_9_07_φ3) (13394476151293/2000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_07_φ3 (by norm_num [half_9_07_φ1, half_9_07_φ2, half_9_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_07_φ1, half_9_07_φ2, half_9_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_07_φ1, half_9_07_φ2, half_9_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_07_φ1, half_9_07_φ2, half_9_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_9_07_hF1 : SourcePowerBound (paddedMoment 16 0 1 8 half_9_07_φ3) (5131492050431/2000000000000 : ℝ) := by
  have h := padded_second_power (k := 16) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_07_φ3 (by norm_num [half_9_07_φ1, half_9_07_φ2, half_9_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_07_φ1, half_9_07_φ2, half_9_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_07_φ1, half_9_07_φ2, half_9_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_07_φ1, half_9_07_φ2, half_9_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_9_07_hx3 : SourcePowerBound (powerBoxCross 16 6 8 half_9_07_φ3) (76194413845517/10000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 16) (s := 6) (r := 1) (v := 2) (t := 9) (D := 8)
    (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
    (by norm_num) half_9_07_φ3 (by norm_num [half_9_07_φ1, half_9_07_φ2, half_9_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_07_φ1, half_9_07_φ2, half_9_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_9_07_hF1 half_9_07_hF2 half_9_06
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_9_07_φ1, half_9_07_φ2, half_9_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_07_hx2 : SourcePowerBound (powerBoxCross 16 7 4 half_9_07_φ2) (84140646426549/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 7) (u := 5) (t := 8)
    (D := 4) (ψ := (7969981161/400000000000 : ℝ)) half_9_07_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_07_φ1, half_9_07_φ2, half_9_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_07_φ1, half_9_07_φ2, half_9_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_07_φ1, half_9_07_φ2, half_9_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_6 SeedCompletionEven16SecondSeeds.degree16_half_8
    (by simpa only [half_9_07_φ3, show (2:ℝ)*4=8 by norm_num] using half_9_07_hx3)
  exact h.weaken (by norm_num [half_9_07_φ1, half_9_07_φ2, half_9_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_07_hx1 : SourcePowerBound (powerBoxCross 16 8 2 half_9_07_φ1) (4740242359519/500000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 8) (u := 6) (t := 9)
    (D := 2) (ψ := (359295084717/10000000000000 : ℝ)) half_9_07_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_07_φ1, half_9_07_φ2, half_9_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_07_φ1, half_9_07_φ2, half_9_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_07_φ1, half_9_07_φ2, half_9_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_7 half_9_06
    (by simpa only [half_9_07_φ2, show (2:ℝ)*2=4 by norm_num] using half_9_07_hx2)
  exact h.weaken (by norm_num [half_9_07_φ1, half_9_07_φ2, half_9_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_07 : AdmissibleExponent 16 18 (20153843546419/2000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 7) (ψ := (397624702781/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8
    (by simpa only [half_9_07_φ1] using half_9_07_hx1)
  exact admissibleExponent_mono h (by norm_num [half_9_07_φ1, half_9_07_φ2, half_9_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_10_07_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (41030556019/1000000000000 : ℝ)

private def half_10_07_φ2 : Fin 2 → ℝ := Fin.snoc half_10_07_φ1 (191422068931/5000000000000 : ℝ)

private def half_10_07_φ3 : Fin 3 → ℝ := Fin.snoc half_10_07_φ2 (288627770159/10000000000000 : ℝ)

private theorem half_10_07_hF2 : SourcePowerBound (paddedMoment 16 0 2 8 half_10_07_φ3) (12264002786101/2000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_10_07_φ3 (by norm_num [half_10_07_φ1, half_10_07_φ2, half_10_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_07_φ1, half_10_07_φ2, half_10_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_07_φ1, half_10_07_φ2, half_10_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_10_07_φ1, half_10_07_φ2, half_10_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_10_07_hx3 : SourcePowerBound (powerBoxCross 16 7 8 half_10_07_φ3) (21421454536831/2500000000000 : ℝ) := by
  have h := full_A_cross_power (k := 16) (s := 7) (r := 2) (v := 9) (w := 10) (D := 8)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_10_07_φ3 (by norm_num [half_10_07_φ1, half_10_07_φ2, half_10_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_07_φ1, half_10_07_φ2, half_10_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_10_07_hF2 half_9_07 half_10_06
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_10_07_φ1, half_10_07_φ2, half_10_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_10_07_hx2 : SourcePowerBound (powerBoxCross 16 8 4 half_10_07_φ2) (95158721979497/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 8) (u := 6) (t := 9)
    (D := 4) (ψ := (288627770159/10000000000000 : ℝ)) half_10_07_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_07_φ1, half_10_07_φ2, half_10_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_07_φ1, half_10_07_φ2, half_10_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_07_φ1, half_10_07_φ2, half_10_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_7 half_9_07
    (by simpa only [half_10_07_φ3, show (2:ℝ)*4=8 by norm_num] using half_10_07_hx3)
  exact h.weaken (by norm_num [half_10_07_φ1, half_10_07_φ2, half_10_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_10_07_hx1 : SourcePowerBound (powerBoxCross 16 9 2 half_10_07_φ1) (21408981251829/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 9) (u := 7) (t := 10)
    (D := 2) (ψ := (191422068931/5000000000000 : ℝ)) half_10_07_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_07_φ1, half_10_07_φ2, half_10_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_07_φ1, half_10_07_φ2, half_10_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_07_φ1, half_10_07_φ2, half_10_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8 half_10_06
    (by simpa only [half_10_07_φ2, show (2:ℝ)*2=4 by norm_num] using half_10_07_hx2)
  exact h.weaken (by norm_num [half_10_07_φ1, half_10_07_φ2, half_10_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_10_07 : AdmissibleExponent 16 20 (912160806259/80000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 8) (ψ := (41030556019/1000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_9_07
    (by simpa only [half_10_07_φ1] using half_10_07_hx1)
  exact admissibleExponent_mono h (by norm_num [half_10_07_φ1, half_10_07_φ2, half_10_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_11_07_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (42492817753/1000000000000 : ℝ)

private def half_11_07_φ2 : Fin 2 → ℝ := Fin.snoc half_11_07_φ1 (101224273157/2500000000000 : ℝ)

private def half_11_07_φ3 : Fin 3 → ℝ := Fin.snoc half_11_07_φ2 (361243166029/10000000000000 : ℝ)

private def half_11_07_φ4 : Fin 4 → ℝ := Fin.snoc half_11_07_φ3 (184130207373/10000000000000 : ℝ)

private theorem half_11_07_hF2 : SourcePowerBound (paddedMoment 16 0 2 16 half_11_07_φ4) (390580305199/50000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_11_07_φ4 (by norm_num [half_11_07_φ1, half_11_07_φ2, half_11_07_φ3, half_11_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_07_φ1, half_11_07_φ2, half_11_07_φ3, half_11_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_07_φ1, half_11_07_φ2, half_11_07_φ3, half_11_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_11_07_φ1, half_11_07_φ2, half_11_07_φ3, half_11_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_11_07_hF1 : SourcePowerBound (paddedMoment 16 0 1 16 half_11_07_φ4) (146860101733/50000000000 : ℝ) := by
  have h := padded_second_power (k := 16) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_11_07_φ4 (by norm_num [half_11_07_φ1, half_11_07_φ2, half_11_07_φ3, half_11_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_07_φ1, half_11_07_φ2, half_11_07_φ3, half_11_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_07_φ1, half_11_07_φ2, half_11_07_φ3, half_11_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_11_07_φ1, half_11_07_φ2, half_11_07_φ3, half_11_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_11_07_hx4 : SourcePowerBound (powerBoxCross 16 7 16 half_11_07_φ4) (21849616158717/2500000000000 : ℝ) := by
  have h := full_B_cross_power (k := 16) (s := 7) (r := 1) (v := 2) (t := 10) (D := 16)
    (a := (1/10 : ℝ)) (b := (1/5 : ℝ)) (c := (7/10 : ℝ))
    (by norm_num) half_11_07_φ4 (by norm_num [half_11_07_φ1, half_11_07_φ2, half_11_07_φ3, half_11_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_07_φ1, half_11_07_φ2, half_11_07_φ3, half_11_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_11_07_hF1 half_11_07_hF2 half_10_07
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_11_07_φ1, half_11_07_φ2, half_11_07_φ3, half_11_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_11_07_hx3 : SourcePowerBound (powerBoxCross 16 8 8 half_11_07_φ3) (47673261265503/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 8) (u := 6) (t := 9)
    (D := 8) (ψ := (184130207373/10000000000000 : ℝ)) half_11_07_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_07_φ1, half_11_07_φ2, half_11_07_φ3, half_11_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_07_φ1, half_11_07_φ2, half_11_07_φ3, half_11_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_07_φ1, half_11_07_φ2, half_11_07_φ3, half_11_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_7 half_9_07
    (by simpa only [half_11_07_φ4, show (2:ℝ)*8=16 by norm_num] using half_11_07_hx4)
  exact h.weaken (by norm_num [half_11_07_φ1, half_11_07_φ2, half_11_07_φ3, half_11_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_11_07_hx2 : SourcePowerBound (powerBoxCross 16 9 4 half_11_07_φ2) (21287621565793/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 9) (u := 7) (t := 10)
    (D := 4) (ψ := (361243166029/10000000000000 : ℝ)) half_11_07_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_07_φ1, half_11_07_φ2, half_11_07_φ3, half_11_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_07_φ1, half_11_07_φ2, half_11_07_φ3, half_11_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_07_φ1, half_11_07_φ2, half_11_07_φ3, half_11_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8 half_10_07
    (by simpa only [half_11_07_φ3, show (2:ℝ)*4=8 by norm_num] using half_11_07_hx3)
  exact h.weaken (by norm_num [half_11_07_φ1, half_11_07_φ2, half_11_07_φ3, half_11_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_11_07_hx1 : SourcePowerBound (powerBoxCross 16 10 2 half_11_07_φ1) (11959999359719/1000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 10) (u := 8) (t := 11)
    (D := 2) (ψ := (101224273157/2500000000000 : ℝ)) half_11_07_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_07_φ1, half_11_07_φ2, half_11_07_φ3, half_11_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_07_φ1, half_11_07_φ2, half_11_07_φ3, half_11_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_07_φ1, half_11_07_φ2, half_11_07_φ3, half_11_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_07 half_11_06
    (by simpa only [half_11_07_φ2, show (2:ℝ)*2=4 by norm_num] using half_11_07_hx2)
  exact h.weaken (by norm_num [half_11_07_φ1, half_11_07_φ2, half_11_07_φ3, half_11_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_11_07 : AdmissibleExponent 16 22 (6383681448513/500000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 9) (ψ := (42492817753/1000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_10_07
    (by simpa only [half_11_07_φ1] using half_11_07_hx1)
  exact admissibleExponent_mono h (by norm_num [half_11_07_φ1, half_11_07_φ2, half_11_07_φ3, half_11_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_12_07_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (436961043653/10000000000000 : ℝ)

private def half_12_07_φ2 : Fin 2 → ℝ := Fin.snoc half_12_07_φ1 (209784923447/5000000000000 : ℝ)

private def half_12_07_φ3 : Fin 3 → ℝ := Fin.snoc half_12_07_φ2 (192985458133/5000000000000 : ℝ)

private def half_12_07_φ4 : Fin 4 → ℝ := Fin.snoc half_12_07_φ3 (139719609627/5000000000000 : ℝ)

private theorem half_12_07_hF2 : SourcePowerBound (paddedMoment 16 0 2 16 half_12_07_φ4) (14302530765397/2000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_12_07_φ4 (by norm_num [half_12_07_φ1, half_12_07_φ2, half_12_07_φ3, half_12_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_07_φ1, half_12_07_φ2, half_12_07_φ3, half_12_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_07_φ1, half_12_07_φ2, half_12_07_φ3, half_12_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_12_07_φ1, half_12_07_φ2, half_12_07_φ3, half_12_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_12_07_hx4 : SourcePowerBound (powerBoxCross 16 8 16 half_12_07_φ4) (96166119714211/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 16) (s := 8) (r := 2) (v := 10) (w := 11) (D := 16)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_12_07_φ4 (by norm_num [half_12_07_φ1, half_12_07_φ2, half_12_07_φ3, half_12_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_07_φ1, half_12_07_φ2, half_12_07_φ3, half_12_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_12_07_hF2 half_10_07 half_11_07
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_12_07_φ1, half_12_07_φ2, half_12_07_φ3, half_12_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_12_07_hx3 : SourcePowerBound (powerBoxCross 16 9 8 half_12_07_φ3) (52893315889923/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 9) (u := 7) (t := 10)
    (D := 8) (ψ := (139719609627/5000000000000 : ℝ)) half_12_07_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_07_φ1, half_12_07_φ2, half_12_07_φ3, half_12_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_07_φ1, half_12_07_φ2, half_12_07_φ3, half_12_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_07_φ1, half_12_07_φ2, half_12_07_φ3, half_12_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8 half_10_07
    (by simpa only [half_12_07_φ4, show (2:ℝ)*8=16 by norm_num] using half_12_07_hx4)
  exact h.weaken (by norm_num [half_12_07_φ1, half_12_07_φ2, half_12_07_φ3, half_12_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_12_07_hx2 : SourcePowerBound (powerBoxCross 16 10 4 half_12_07_φ2) (118119081128149/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 10) (u := 8) (t := 11)
    (D := 4) (ψ := (192985458133/5000000000000 : ℝ)) half_12_07_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_07_φ1, half_12_07_φ2, half_12_07_φ3, half_12_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_07_φ1, half_12_07_φ2, half_12_07_φ3, half_12_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_07_φ1, half_12_07_φ2, half_12_07_φ3, half_12_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_07 half_11_07
    (by simpa only [half_12_07_φ3, show (2:ℝ)*4=8 by norm_num] using half_12_07_hx3)
  exact h.weaken (by norm_num [half_12_07_φ1, half_12_07_φ2, half_12_07_φ3, half_12_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_12_07_hx1 : SourcePowerBound (powerBoxCross 16 11 2 half_12_07_φ1) (132531749797743/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 11) (u := 9) (t := 12)
    (D := 2) (ψ := (209784923447/5000000000000 : ℝ)) half_12_07_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_07_φ1, half_12_07_φ2, half_12_07_φ3, half_12_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_07_φ1, half_12_07_φ2, half_12_07_φ3, half_12_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_07_φ1, half_12_07_φ2, half_12_07_φ3, half_12_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_07 half_12_06
    (by simpa only [half_12_07_φ2, show (2:ℝ)*2=4 by norm_num] using half_12_07_hx2)
  exact h.weaken (by norm_num [half_12_07_φ1, half_12_07_φ2, half_12_07_φ3, half_12_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_12_07 : AdmissibleExponent 16 24 (17713491464307/1250000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 10) (ψ := (436961043653/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_11_07
    (by simpa only [half_12_07_φ1] using half_12_07_hx1)
  exact admissibleExponent_mono h (by norm_num [half_12_07_φ1, half_12_07_φ2, half_12_07_φ3, half_12_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_13_07_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (225155031873/5000000000000 : ℝ)

private def half_13_07_φ2 : Fin 2 → ℝ := Fin.snoc half_13_07_φ1 (54304198499/1250000000000 : ℝ)

private def half_13_07_φ3 : Fin 3 → ℝ := Fin.snoc half_13_07_φ2 (10336104947/250000000000 : ℝ)

private def half_13_07_φ4 : Fin 4 → ℝ := Fin.snoc half_13_07_φ3 (363474903903/10000000000000 : ℝ)

private def half_13_07_φ5 : Fin 5 → ℝ := Fin.snoc half_13_07_φ4 (90912675029/5000000000000 : ℝ)

private theorem half_13_07_hF2 : SourcePowerBound (paddedMoment 16 0 2 32 half_13_07_φ5) (17408607067789/2000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_13_07_φ5 (by norm_num [half_13_07_φ1, half_13_07_φ2, half_13_07_φ3, half_13_07_φ4, half_13_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_07_φ1, half_13_07_φ2, half_13_07_φ3, half_13_07_φ4, half_13_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_07_φ1, half_13_07_φ2, half_13_07_φ3, half_13_07_φ4, half_13_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_13_07_φ1, half_13_07_φ2, half_13_07_φ3, half_13_07_φ4, half_13_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_13_07_hF1 : SourcePowerBound (paddedMoment 16 0 1 32 half_13_07_φ5) (6469535689263/2000000000000 : ℝ) := by
  have h := padded_second_power (k := 16) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_13_07_φ5 (by norm_num [half_13_07_φ1, half_13_07_φ2, half_13_07_φ3, half_13_07_φ4, half_13_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_07_φ1, half_13_07_φ2, half_13_07_φ3, half_13_07_φ4, half_13_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_07_φ1, half_13_07_φ2, half_13_07_φ3, half_13_07_φ4, half_13_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_13_07_φ1, half_13_07_φ2, half_13_07_φ3, half_13_07_φ4, half_13_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_13_07_hx5 : SourcePowerBound (powerBoxCross 16 8 32 half_13_07_φ5) (24238653588489/2500000000000 : ℝ) := by
  have h := full_B_cross_power (k := 16) (s := 8) (r := 1) (v := 2) (t := 12) (D := 32)
    (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
    (by norm_num) half_13_07_φ5 (by norm_num [half_13_07_φ1, half_13_07_φ2, half_13_07_φ3, half_13_07_φ4, half_13_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_07_φ1, half_13_07_φ2, half_13_07_φ3, half_13_07_φ4, half_13_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_13_07_hF1 half_13_07_hF2 half_12_07
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_13_07_φ1, half_13_07_φ2, half_13_07_φ3, half_13_07_φ4, half_13_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_07_hx4 : SourcePowerBound (powerBoxCross 16 9 16 half_13_07_φ4) (20983085862211/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 4) (s := 9) (u := 7) (t := 10)
    (D := 16) (ψ := (90912675029/5000000000000 : ℝ)) half_13_07_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_07_φ1, half_13_07_φ2, half_13_07_φ3, half_13_07_φ4, half_13_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_07_φ1, half_13_07_φ2, half_13_07_φ3, half_13_07_φ4, half_13_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_07_φ1, half_13_07_φ2, half_13_07_φ3, half_13_07_φ4, half_13_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8 half_10_07
    (by simpa only [half_13_07_φ5, show (2:ℝ)*16=32 by norm_num] using half_13_07_hx5)
  exact h.weaken (by norm_num [half_13_07_φ1, half_13_07_φ2, half_13_07_φ3, half_13_07_φ4, half_13_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_07_hx3 : SourcePowerBound (powerBoxCross 16 10 8 half_13_07_φ3) (116360439259407/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 10) (u := 8) (t := 11)
    (D := 8) (ψ := (363474903903/10000000000000 : ℝ)) half_13_07_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_07_φ1, half_13_07_φ2, half_13_07_φ3, half_13_07_φ4, half_13_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_07_φ1, half_13_07_φ2, half_13_07_φ3, half_13_07_φ4, half_13_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_07_φ1, half_13_07_φ2, half_13_07_φ3, half_13_07_φ4, half_13_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_07 half_11_07
    (by simpa only [half_13_07_φ4, show (2:ℝ)*8=16 by norm_num] using half_13_07_hx4)
  exact h.weaken (by norm_num [half_13_07_φ1, half_13_07_φ2, half_13_07_φ3, half_13_07_φ4, half_13_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_07_hx2 : SourcePowerBound (powerBoxCross 16 11 4 half_13_07_φ2) (130057568329493/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 11) (u := 9) (t := 12)
    (D := 4) (ψ := (10336104947/250000000000 : ℝ)) half_13_07_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_07_φ1, half_13_07_φ2, half_13_07_φ3, half_13_07_φ4, half_13_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_07_φ1, half_13_07_φ2, half_13_07_φ3, half_13_07_φ4, half_13_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_07_φ1, half_13_07_φ2, half_13_07_φ3, half_13_07_φ4, half_13_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_07 half_12_07
    (by simpa only [half_13_07_φ3, show (2:ℝ)*4=8 by norm_num] using half_13_07_hx3)
  exact h.weaken (by norm_num [half_13_07_φ1, half_13_07_φ2, half_13_07_φ3, half_13_07_φ4, half_13_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_07_hx1 : SourcePowerBound (powerBoxCross 16 12 2 half_13_07_φ1) (145776991001847/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 12) (u := 10) (t := 13)
    (D := 2) (ψ := (54304198499/1250000000000 : ℝ)) half_13_07_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_07_φ1, half_13_07_φ2, half_13_07_φ3, half_13_07_φ4, half_13_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_07_φ1, half_13_07_φ2, half_13_07_φ3, half_13_07_φ4, half_13_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_07_φ1, half_13_07_φ2, half_13_07_φ3, half_13_07_φ4, half_13_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_07 half_13_06
    (by simpa only [half_13_07_φ2, show (2:ℝ)*2=4 by norm_num] using half_13_07_hx2)
  exact h.weaken (by norm_num [half_13_07_φ1, half_13_07_φ2, half_13_07_φ3, half_13_07_φ4, half_13_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_07 : AdmissibleExponent 16 26 (31226824493601/2000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 11) (ψ := (225155031873/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_12_07
    (by simpa only [half_13_07_φ1] using half_13_07_hx1)
  exact admissibleExponent_mono h (by norm_num [half_13_07_φ1, half_13_07_φ2, half_13_07_φ3, half_13_07_φ4, half_13_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_14_07_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (462607189219/10000000000000 : ℝ)

private def half_14_07_φ2 : Fin 2 → ℝ := Fin.snoc half_14_07_φ1 (447113316123/10000000000000 : ℝ)

private def half_14_07_φ3 : Fin 3 → ℝ := Fin.snoc half_14_07_φ2 (106995133631/2500000000000 : ℝ)

private def half_14_07_φ4 : Fin 4 → ℝ := Fin.snoc half_14_07_φ3 (391433210679/10000000000000 : ℝ)

private def half_14_07_φ5 : Fin 5 → ℝ := Fin.snoc half_14_07_φ4 (11070648509/400000000000 : ℝ)

private theorem half_14_07_hF2 : SourcePowerBound (paddedMoment 16 0 2 32 half_14_07_φ5) (1594689583057/200000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_14_07_φ5 (by norm_num [half_14_07_φ1, half_14_07_φ2, half_14_07_φ3, half_14_07_φ4, half_14_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_07_φ1, half_14_07_φ2, half_14_07_φ3, half_14_07_φ4, half_14_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_07_φ1, half_14_07_φ2, half_14_07_φ3, half_14_07_φ4, half_14_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_14_07_φ1, half_14_07_φ2, half_14_07_φ3, half_14_07_φ4, half_14_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_14_07_hx5 : SourcePowerBound (powerBoxCross 16 9 32 half_14_07_φ5) (4195826725337/400000000000 : ℝ) := by
  have h := full_A_cross_power (k := 16) (s := 9) (r := 2) (v := 12) (w := 12) (D := 32)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_14_07_φ5 (by norm_num [half_14_07_φ1, half_14_07_φ2, half_14_07_φ3, half_14_07_φ4, half_14_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_07_φ1, half_14_07_φ2, half_14_07_φ3, half_14_07_φ4, half_14_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_14_07_hF2 half_12_07 half_12_07
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_14_07_φ1, half_14_07_φ2, half_14_07_φ3, half_14_07_φ4, half_14_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_07_hx4 : SourcePowerBound (powerBoxCross 16 10 16 half_14_07_φ4) (114630412243727/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 4) (s := 10) (u := 8) (t := 11)
    (D := 16) (ψ := (11070648509/400000000000 : ℝ)) half_14_07_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_07_φ1, half_14_07_φ2, half_14_07_φ3, half_14_07_φ4, half_14_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_07_φ1, half_14_07_φ2, half_14_07_φ3, half_14_07_φ4, half_14_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_07_φ1, half_14_07_φ2, half_14_07_φ3, half_14_07_φ4, half_14_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_07 half_11_07
    (by simpa only [half_14_07_φ5, show (2:ℝ)*16=32 by norm_num] using half_14_07_hx5)
  exact h.weaken (by norm_num [half_14_07_φ1, half_14_07_φ2, half_14_07_φ3, half_14_07_φ4, half_14_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_07_hx3 : SourcePowerBound (powerBoxCross 16 11 8 half_14_07_φ3) (127376887300963/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 11) (u := 9) (t := 12)
    (D := 8) (ψ := (391433210679/10000000000000 : ℝ)) half_14_07_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_07_φ1, half_14_07_φ2, half_14_07_φ3, half_14_07_φ4, half_14_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_07_φ1, half_14_07_φ2, half_14_07_φ3, half_14_07_φ4, half_14_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_07_φ1, half_14_07_φ2, half_14_07_φ3, half_14_07_φ4, half_14_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_07 half_12_07
    (by simpa only [half_14_07_φ4, show (2:ℝ)*8=16 by norm_num] using half_14_07_hx4)
  exact h.weaken (by norm_num [half_14_07_φ1, half_14_07_φ2, half_14_07_φ3, half_14_07_φ4, half_14_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_07_hx2 : SourcePowerBound (powerBoxCross 16 12 4 half_14_07_φ2) (28464895213457/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 12) (u := 10) (t := 13)
    (D := 4) (ψ := (106995133631/2500000000000 : ℝ)) half_14_07_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_07_φ1, half_14_07_φ2, half_14_07_φ3, half_14_07_φ4, half_14_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_07_φ1, half_14_07_φ2, half_14_07_φ3, half_14_07_φ4, half_14_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_07_φ1, half_14_07_φ2, half_14_07_φ3, half_14_07_φ4, half_14_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_07 half_13_07
    (by simpa only [half_14_07_φ3, show (2:ℝ)*4=8 by norm_num] using half_14_07_hx3)
  exact h.weaken (by norm_num [half_14_07_φ1, half_14_07_φ2, half_14_07_φ3, half_14_07_φ4, half_14_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_07_hx1 : SourcePowerBound (powerBoxCross 16 13 2 half_14_07_φ1) (19921731612953/1250000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 13) (u := 11) (t := 14)
    (D := 2) (ψ := (447113316123/10000000000000 : ℝ)) half_14_07_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_07_φ1, half_14_07_φ2, half_14_07_φ3, half_14_07_φ4, half_14_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_07_φ1, half_14_07_φ2, half_14_07_φ3, half_14_07_φ4, half_14_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_07_φ1, half_14_07_φ2, half_14_07_φ3, half_14_07_φ4, half_14_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_07 half_14_06
    (by simpa only [half_14_07_φ2, show (2:ℝ)*2=4 by norm_num] using half_14_07_hx2)
  exact h.weaken (by norm_num [half_14_07_φ1, half_14_07_φ2, half_14_07_φ3, half_14_07_φ4, half_14_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_07 : AdmissibleExponent 16 28 (170939032634099/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 12) (ψ := (462607189219/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_13_07
    (by simpa only [half_14_07_φ1] using half_14_07_hx1)
  exact admissibleExponent_mono h (by norm_num [half_14_07_φ1, half_14_07_φ2, half_14_07_φ3, half_14_07_φ4, half_14_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_9_08_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (397618012623/10000000000000 : ℝ)

private def half_9_08_φ2 : Fin 2 → ℝ := Fin.snoc half_9_08_φ1 (89823125113/2500000000000 : ℝ)

private def half_9_08_φ3 : Fin 3 → ℝ := Fin.snoc half_9_08_φ2 (39846969917/2000000000000 : ℝ)

private theorem half_9_08_hF2 : SourcePowerBound (paddedMoment 16 0 2 8 half_9_08_φ3) (669734586803/100000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_08_φ3 (by norm_num [half_9_08_φ1, half_9_08_φ2, half_9_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_08_φ1, half_9_08_φ2, half_9_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_08_φ1, half_9_08_φ2, half_9_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_08_φ1, half_9_08_φ2, half_9_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_9_08_hF1 : SourcePowerBound (paddedMoment 16 0 1 8 half_9_08_φ3) (256578195601/100000000000 : ℝ) := by
  have h := padded_second_power (k := 16) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_08_φ3 (by norm_num [half_9_08_φ1, half_9_08_φ2, half_9_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_08_φ1, half_9_08_φ2, half_9_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_08_φ1, half_9_08_φ2, half_9_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_08_φ1, half_9_08_φ2, half_9_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_9_08_hx3 : SourcePowerBound (powerBoxCross 16 6 8 half_9_08_φ3) (19048672544809/2500000000000 : ℝ) := by
  have h := full_B_cross_power (k := 16) (s := 6) (r := 1) (v := 2) (t := 9) (D := 8)
    (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
    (by norm_num) half_9_08_φ3 (by norm_num [half_9_08_φ1, half_9_08_φ2, half_9_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_08_φ1, half_9_08_φ2, half_9_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_9_08_hF1 half_9_08_hF2 half_9_07
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_9_08_φ1, half_9_08_φ2, half_9_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_08_hx2 : SourcePowerBound (powerBoxCross 16 7 4 half_9_08_φ2) (21035203544221/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 7) (u := 5) (t := 8)
    (D := 4) (ψ := (39846969917/2000000000000 : ℝ)) half_9_08_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_08_φ1, half_9_08_φ2, half_9_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_08_φ1, half_9_08_φ2, half_9_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_08_φ1, half_9_08_φ2, half_9_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_6 SeedCompletionEven16SecondSeeds.degree16_half_8
    (by simpa only [half_9_08_φ3, show (2:ℝ)*4=8 by norm_num] using half_9_08_hx3)
  exact h.weaken (by norm_num [half_9_08_φ1, half_9_08_φ2, half_9_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_08_hx1 : SourcePowerBound (powerBoxCross 16 8 2 half_9_08_φ1) (18960979861669/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 8) (u := 6) (t := 9)
    (D := 2) (ψ := (89823125113/2500000000000 : ℝ)) half_9_08_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_08_φ1, half_9_08_φ2, half_9_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_08_φ1, half_9_08_φ2, half_9_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_08_φ1, half_9_08_φ2, half_9_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_7 half_9_07
    (by simpa only [half_9_08_φ2, show (2:ℝ)*2=4 by norm_num] using half_9_08_hx2)
  exact h.weaken (by norm_num [half_9_08_φ1, half_9_08_φ2, half_9_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_08 : AdmissibleExponent 16 18 (10076916949769/1000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 7) (ψ := (397618012623/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8
    (by simpa only [half_9_08_φ1] using half_9_08_hx1)
  exact admissibleExponent_mono h (by norm_num [half_9_08_φ1, half_9_08_φ2, half_9_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_10_08_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (205134215933/5000000000000 : ℝ)

private def half_10_08_φ2 : Fin 2 → ℝ := Fin.snoc half_10_08_φ1 (38283542471/1000000000000 : ℝ)

private def half_10_08_φ3 : Fin 3 → ℝ := Fin.snoc half_10_08_φ2 (57718230377/2000000000000 : ℝ)

private theorem half_10_08_hF2 : SourcePowerBound (paddedMoment 16 0 2 8 half_10_08_φ3) (12264744923851/2000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_10_08_φ3 (by norm_num [half_10_08_φ1, half_10_08_φ2, half_10_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_08_φ1, half_10_08_φ2, half_10_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_08_φ1, half_10_08_φ2, half_10_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_10_08_φ1, half_10_08_φ2, half_10_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_10_08_hx3 : SourcePowerBound (powerBoxCross 16 7 8 half_10_08_φ3) (4284354568481/500000000000 : ℝ) := by
  have h := full_A_cross_power (k := 16) (s := 7) (r := 2) (v := 9) (w := 10) (D := 8)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_10_08_φ3 (by norm_num [half_10_08_φ1, half_10_08_φ2, half_10_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_08_φ1, half_10_08_φ2, half_10_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_10_08_hF2 half_9_08 half_10_07
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_10_08_φ1, half_10_08_φ2, half_10_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_10_08_hx2 : SourcePowerBound (powerBoxCross 16 8 4 half_10_08_φ2) (95159673148959/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 8) (u := 6) (t := 9)
    (D := 4) (ψ := (57718230377/2000000000000 : ℝ)) half_10_08_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_08_φ1, half_10_08_φ2, half_10_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_08_φ1, half_10_08_φ2, half_10_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_08_φ1, half_10_08_φ2, half_10_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_7 half_9_08
    (by simpa only [half_10_08_φ3, show (2:ℝ)*4=8 by norm_num] using half_10_08_hx3)
  exact h.weaken (by norm_num [half_10_08_φ1, half_10_08_φ2, half_10_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_10_08_hx1 : SourcePowerBound (powerBoxCross 16 9 2 half_10_08_φ1) (53522598507269/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 9) (u := 7) (t := 10)
    (D := 2) (ψ := (38283542471/1000000000000 : ℝ)) half_10_08_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_08_φ1, half_10_08_φ2, half_10_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_08_φ1, half_10_08_φ2, half_10_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_08_φ1, half_10_08_φ2, half_10_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8 half_10_07
    (by simpa only [half_10_08_φ2, show (2:ℝ)*2=4 by norm_num] using half_10_08_hx2)
  exact h.weaken (by norm_num [half_10_08_φ1, half_10_08_φ2, half_10_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_10_08 : AdmissibleExponent 16 20 (5700988017813/500000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 8) (ψ := (205134215933/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_9_08
    (by simpa only [half_10_08_φ1] using half_10_08_hx1)
  exact admissibleExponent_mono h (by norm_num [half_10_08_φ1, half_10_08_φ2, half_10_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_11_08_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (42481562379/1000000000000 : ℝ)

private def half_11_08_φ2 : Fin 2 → ℝ := Fin.snoc half_11_08_φ1 (404887094413/10000000000000 : ℝ)

private def half_11_08_φ3 : Fin 3 → ℝ := Fin.snoc half_11_08_φ2 (361229166377/10000000000000 : ℝ)

private def half_11_08_φ4 : Fin 4 → ℝ := Fin.snoc half_11_08_φ3 (92033244551/5000000000000 : ℝ)

private theorem half_11_08_hF2 : SourcePowerBound (paddedMoment 16 0 2 16 half_11_08_φ4) (7812507318431/1000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_11_08_φ4 (by norm_num [half_11_08_φ1, half_11_08_φ2, half_11_08_φ3, half_11_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_08_φ1, half_11_08_φ2, half_11_08_φ3, half_11_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_08_φ1, half_11_08_φ2, half_11_08_φ3, half_11_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_11_08_φ1, half_11_08_φ2, half_11_08_φ3, half_11_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_11_08_hF1 : SourcePowerBound (paddedMoment 16 0 1 16 half_11_08_φ4) (2937502439477/1000000000000 : ℝ) := by
  have h := padded_second_power (k := 16) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_11_08_φ4 (by norm_num [half_11_08_φ1, half_11_08_φ2, half_11_08_φ3, half_11_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_08_φ1, half_11_08_φ2, half_11_08_φ3, half_11_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_08_φ1, half_11_08_φ2, half_11_08_φ3, half_11_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_11_08_φ1, half_11_08_φ2, half_11_08_φ3, half_11_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_11_08_hx4 : SourcePowerBound (powerBoxCross 16 7 16 half_11_08_φ4) (87401960371699/10000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 16) (s := 7) (r := 1) (v := 2) (t := 10) (D := 16)
    (a := (1/10 : ℝ)) (b := (1/5 : ℝ)) (c := (7/10 : ℝ))
    (by norm_num) half_11_08_φ4 (by norm_num [half_11_08_φ1, half_11_08_φ2, half_11_08_φ3, half_11_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_08_φ1, half_11_08_φ2, half_11_08_φ3, half_11_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_11_08_hF1 half_11_08_hF2 half_10_08
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_11_08_φ1, half_11_08_φ2, half_11_08_φ3, half_11_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_11_08_hx3 : SourcePowerBound (powerBoxCross 16 8 8 half_11_08_φ3) (23837386783159/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 8) (u := 6) (t := 9)
    (D := 8) (ψ := (92033244551/5000000000000 : ℝ)) half_11_08_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_08_φ1, half_11_08_φ2, half_11_08_φ3, half_11_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_08_φ1, half_11_08_φ2, half_11_08_φ3, half_11_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_08_φ1, half_11_08_φ2, half_11_08_φ3, half_11_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_7 half_9_08
    (by simpa only [half_11_08_φ4, show (2:ℝ)*8=16 by norm_num] using half_11_08_hx4)
  exact h.weaken (by norm_num [half_11_08_φ1, half_11_08_φ2, half_11_08_φ3, half_11_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_11_08_hx2 : SourcePowerBound (powerBoxCross 16 9 4 half_11_08_φ2) (106440976850931/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 9) (u := 7) (t := 10)
    (D := 4) (ψ := (361229166377/10000000000000 : ℝ)) half_11_08_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_08_φ1, half_11_08_φ2, half_11_08_φ3, half_11_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_08_φ1, half_11_08_φ2, half_11_08_φ3, half_11_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_08_φ1, half_11_08_φ2, half_11_08_φ3, half_11_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8 half_10_08
    (by simpa only [half_11_08_φ3, show (2:ℝ)*4=8 by norm_num] using half_11_08_hx3)
  exact h.weaken (by norm_num [half_11_08_φ1, half_11_08_φ2, half_11_08_φ3, half_11_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_11_08_hx1 : SourcePowerBound (powerBoxCross 16 10 2 half_11_08_φ1) (23920167683611/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 10) (u := 8) (t := 11)
    (D := 2) (ψ := (404887094413/10000000000000 : ℝ)) half_11_08_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_08_φ1, half_11_08_φ2, half_11_08_φ3, half_11_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_08_φ1, half_11_08_φ2, half_11_08_φ3, half_11_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_08_φ1, half_11_08_φ2, half_11_08_φ3, half_11_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_08 half_11_07
    (by simpa only [half_11_08_φ2, show (2:ℝ)*2=4 by norm_num] using half_11_08_hx2)
  exact h.weaken (by norm_num [half_11_08_φ1, half_11_08_φ2, half_11_08_φ3, half_11_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_11_08 : AdmissibleExponent 16 22 (25534467054013/2000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 9) (ψ := (42481562379/1000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_10_08
    (by simpa only [half_11_08_φ1] using half_11_08_hx1)
  exact admissibleExponent_mono h (by norm_num [half_11_08_φ1, half_11_08_φ2, half_11_08_φ3, half_11_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_12_08_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (436672753843/10000000000000 : ℝ)

private def half_12_08_φ2 : Fin 2 → ℝ := Fin.snoc half_12_08_φ1 (419541991743/10000000000000 : ℝ)

private def half_12_08_φ3 : Fin 3 → ℝ := Fin.snoc half_12_08_φ2 (24120804117/625000000000 : ℝ)

private def half_12_08_φ4 : Fin 4 → ℝ := Fin.snoc half_12_08_φ3 (279298082259/10000000000000 : ℝ)

private theorem half_12_08_hF2 : SourcePowerBound (paddedMoment 16 0 2 16 half_12_08_φ4) (14306988756547/2000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_12_08_φ4 (by norm_num [half_12_08_φ1, half_12_08_φ2, half_12_08_φ3, half_12_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_08_φ1, half_12_08_φ2, half_12_08_φ3, half_12_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_08_φ1, half_12_08_φ2, half_12_08_φ3, half_12_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_12_08_φ1, half_12_08_φ2, half_12_08_φ3, half_12_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_12_08_hx4 : SourcePowerBound (powerBoxCross 16 8 16 half_12_08_φ4) (96175645599793/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 16) (s := 8) (r := 2) (v := 10) (w := 11) (D := 16)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_12_08_φ4 (by norm_num [half_12_08_φ1, half_12_08_φ2, half_12_08_φ3, half_12_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_08_φ1, half_12_08_φ2, half_12_08_φ3, half_12_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_12_08_hF2 half_10_08 half_11_08
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_12_08_φ1, half_12_08_φ2, half_12_08_φ3, half_12_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_12_08_hx3 : SourcePowerBound (powerBoxCross 16 9 8 half_12_08_φ3) (105794862859757/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 9) (u := 7) (t := 10)
    (D := 8) (ψ := (279298082259/10000000000000 : ℝ)) half_12_08_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_08_φ1, half_12_08_φ2, half_12_08_φ3, half_12_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_08_φ1, half_12_08_φ2, half_12_08_φ3, half_12_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_08_φ1, half_12_08_φ2, half_12_08_φ3, half_12_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8 half_10_08
    (by simpa only [half_12_08_φ4, show (2:ℝ)*8=16 by norm_num] using half_12_08_hx4)
  exact h.weaken (by norm_num [half_12_08_φ1, half_12_08_φ2, half_12_08_φ3, half_12_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_12_08_hx2 : SourcePowerBound (powerBoxCross 16 10 4 half_12_08_φ2) (118126671029847/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 10) (u := 8) (t := 11)
    (D := 4) (ψ := (24120804117/625000000000 : ℝ)) half_12_08_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_08_φ1, half_12_08_φ2, half_12_08_φ3, half_12_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_08_φ1, half_12_08_φ2, half_12_08_φ3, half_12_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_08_φ1, half_12_08_φ2, half_12_08_φ3, half_12_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_08 half_11_08
    (by simpa only [half_12_08_φ3, show (2:ℝ)*4=8 by norm_num] using half_12_08_hx3)
  exact h.weaken (by norm_num [half_12_08_φ1, half_12_08_φ2, half_12_08_φ3, half_12_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_12_08_hx1 : SourcePowerBound (powerBoxCross 16 11 2 half_12_08_φ1) (132533905000731/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 11) (u := 9) (t := 12)
    (D := 2) (ψ := (419541991743/10000000000000 : ℝ)) half_12_08_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_08_φ1, half_12_08_φ2, half_12_08_φ3, half_12_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_08_φ1, half_12_08_φ2, half_12_08_φ3, half_12_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_08_φ1, half_12_08_φ2, half_12_08_φ3, half_12_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_08 half_12_07
    (by simpa only [half_12_08_φ2, show (2:ℝ)*2=4 by norm_num] using half_12_08_hx2)
  exact h.weaken (by norm_num [half_12_08_φ1, half_12_08_φ2, half_12_08_φ3, half_12_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_12_08 : AdmissibleExponent 16 24 (70852016415717/5000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 10) (ψ := (436672753843/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_11_08
    (by simpa only [half_12_08_φ1] using half_12_08_hx1)
  exact admissibleExponent_mono h (by norm_num [half_12_08_φ1, half_12_08_φ2, half_12_08_φ3, half_12_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_13_08_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (56214702071/1250000000000 : ℝ)

private def half_13_08_φ2 : Fin 2 → ℝ := Fin.snoc half_13_08_φ1 (108593888413/2500000000000 : ℝ)

private def half_13_08_φ3 : Fin 3 → ℝ := Fin.snoc half_13_08_φ2 (413398829587/10000000000000 : ℝ)

private def half_13_08_φ4 : Fin 4 → ℝ := Fin.snoc half_13_08_φ3 (363360523031/10000000000000 : ℝ)

private def half_13_08_φ5 : Fin 5 → ℝ := Fin.snoc half_13_08_φ4 (36268315841/2000000000000 : ℝ)

private theorem half_13_08_hF2 : SourcePowerBound (paddedMoment 16 0 2 32 half_13_08_φ5) (17420253081613/2000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_13_08_φ5 (by norm_num [half_13_08_φ1, half_13_08_φ2, half_13_08_φ3, half_13_08_φ4, half_13_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_08_φ1, half_13_08_φ2, half_13_08_φ3, half_13_08_φ4, half_13_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_08_φ1, half_13_08_φ2, half_13_08_φ3, half_13_08_φ4, half_13_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_13_08_φ1, half_13_08_φ2, half_13_08_φ3, half_13_08_φ4, half_13_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_13_08_hF1 : SourcePowerBound (paddedMoment 16 0 1 32 half_13_08_φ5) (6473417693871/2000000000000 : ℝ) := by
  have h := padded_second_power (k := 16) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_13_08_φ5 (by norm_num [half_13_08_φ1, half_13_08_φ2, half_13_08_φ3, half_13_08_φ4, half_13_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_08_φ1, half_13_08_φ2, half_13_08_φ3, half_13_08_φ4, half_13_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_08_φ1, half_13_08_φ2, half_13_08_φ3, half_13_08_φ4, half_13_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_13_08_φ1, half_13_08_φ2, half_13_08_φ3, half_13_08_φ4, half_13_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_13_08_hx5 : SourcePowerBound (powerBoxCross 16 8 32 half_13_08_φ5) (3879106345307/400000000000 : ℝ) := by
  have h := full_B_cross_power (k := 16) (s := 8) (r := 1) (v := 2) (t := 12) (D := 32)
    (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
    (by norm_num) half_13_08_φ5 (by norm_num [half_13_08_φ1, half_13_08_φ2, half_13_08_φ3, half_13_08_φ4, half_13_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_08_φ1, half_13_08_φ2, half_13_08_φ3, half_13_08_φ4, half_13_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_13_08_hF1 half_13_08_hF2 half_12_08
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_13_08_φ1, half_13_08_φ2, half_13_08_φ3, half_13_08_φ4, half_13_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_08_hx4 : SourcePowerBound (powerBoxCross 16 9 16 half_13_08_φ4) (104933877085167/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 4) (s := 9) (u := 7) (t := 10)
    (D := 16) (ψ := (36268315841/2000000000000 : ℝ)) half_13_08_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_08_φ1, half_13_08_φ2, half_13_08_φ3, half_13_08_φ4, half_13_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_08_φ1, half_13_08_φ2, half_13_08_φ3, half_13_08_φ4, half_13_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_08_φ1, half_13_08_φ2, half_13_08_φ3, half_13_08_φ4, half_13_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8 half_10_08
    (by simpa only [half_13_08_φ5, show (2:ℝ)*16=32 by norm_num] using half_13_08_hx5)
  exact h.weaken (by norm_num [half_13_08_φ1, half_13_08_φ2, half_13_08_φ3, half_13_08_φ4, half_13_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_08_hx3 : SourcePowerBound (powerBoxCross 16 10 8 half_13_08_φ3) (29094447236087/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 10) (u := 8) (t := 11)
    (D := 8) (ψ := (363360523031/10000000000000 : ℝ)) half_13_08_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_08_φ1, half_13_08_φ2, half_13_08_φ3, half_13_08_φ4, half_13_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_08_φ1, half_13_08_φ2, half_13_08_φ3, half_13_08_φ4, half_13_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_08_φ1, half_13_08_φ2, half_13_08_φ3, half_13_08_φ4, half_13_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_08 half_11_08
    (by simpa only [half_13_08_φ4, show (2:ℝ)*8=16 by norm_num] using half_13_08_hx4)
  exact h.weaken (by norm_num [half_13_08_φ1, half_13_08_φ2, half_13_08_φ3, half_13_08_φ4, half_13_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_08_hx2 : SourcePowerBound (powerBoxCross 16 11 4 half_13_08_φ2) (130073522611373/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 11) (u := 9) (t := 12)
    (D := 4) (ψ := (413398829587/10000000000000 : ℝ)) half_13_08_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_08_φ1, half_13_08_φ2, half_13_08_φ3, half_13_08_φ4, half_13_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_08_φ1, half_13_08_φ2, half_13_08_φ3, half_13_08_φ4, half_13_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_08_φ1, half_13_08_φ2, half_13_08_φ3, half_13_08_φ4, half_13_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_08 half_12_08
    (by simpa only [half_13_08_φ3, show (2:ℝ)*4=8 by norm_num] using half_13_08_hx3)
  exact h.weaken (by norm_num [half_13_08_φ1, half_13_08_φ2, half_13_08_φ3, half_13_08_φ4, half_13_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_08_hx1 : SourcePowerBound (powerBoxCross 16 12 2 half_13_08_φ1) (145781070457713/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 12) (u := 10) (t := 13)
    (D := 2) (ψ := (108593888413/2500000000000 : ℝ)) half_13_08_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_08_φ1, half_13_08_φ2, half_13_08_φ3, half_13_08_φ4, half_13_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_08_φ1, half_13_08_φ2, half_13_08_φ3, half_13_08_φ4, half_13_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_08_φ1, half_13_08_φ2, half_13_08_φ3, half_13_08_φ4, half_13_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_08 half_13_07
    (by simpa only [half_13_08_φ2, show (2:ℝ)*2=4 by norm_num] using half_13_08_hx2)
  exact h.weaken (by norm_num [half_13_08_φ1, half_13_08_φ2, half_13_08_φ3, half_13_08_φ4, half_13_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_08 : AdmissibleExponent 16 26 (156124575638777/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 11) (ψ := (56214702071/1250000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_12_08
    (by simpa only [half_13_08_φ1] using half_13_08_hx1)
  exact admissibleExponent_mono h (by norm_num [half_13_08_φ1, half_13_08_φ2, half_13_08_φ3, half_13_08_φ4, half_13_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_14_08_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (230775395417/5000000000000 : ℝ)

private def half_14_08_φ2 : Fin 2 → ℝ := Fin.snoc half_14_08_φ1 (447006361073/10000000000000 : ℝ)

private def half_14_08_φ3 : Fin 3 → ℝ := Fin.snoc half_14_08_φ2 (4278985213/100000000000 : ℝ)

private def half_14_08_φ4 : Fin 4 → ℝ := Fin.snoc half_14_08_φ3 (78257471933/2000000000000 : ℝ)

private def half_14_08_φ5 : Fin 5 → ℝ := Fin.snoc half_14_08_φ4 (276238928111/10000000000000 : ℝ)

private theorem half_14_08_hF2 : SourcePowerBound (paddedMoment 16 0 2 32 half_14_08_φ5) (15964162351153/2000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_14_08_φ5 (by norm_num [half_14_08_φ1, half_14_08_φ2, half_14_08_φ3, half_14_08_φ4, half_14_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_08_φ1, half_14_08_φ2, half_14_08_φ3, half_14_08_φ4, half_14_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_08_φ1, half_14_08_φ2, half_14_08_φ3, half_14_08_φ4, half_14_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_14_08_φ1, half_14_08_φ2, half_14_08_φ3, half_14_08_φ4, half_14_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_14_08_hx5 : SourcePowerBound (powerBoxCross 16 9 32 half_14_08_φ5) (52467651571531/5000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 16) (s := 9) (r := 2) (v := 12) (w := 12) (D := 32)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_14_08_φ5 (by norm_num [half_14_08_φ1, half_14_08_φ2, half_14_08_φ3, half_14_08_φ4, half_14_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_08_φ1, half_14_08_φ2, half_14_08_φ3, half_14_08_φ4, half_14_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_14_08_hF2 half_12_08 half_12_08
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_14_08_φ1, half_14_08_φ2, half_14_08_φ3, half_14_08_φ4, half_14_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_08_hx4 : SourcePowerBound (powerBoxCross 16 10 16 half_14_08_φ4) (1146645279613/100000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 4) (s := 10) (u := 8) (t := 11)
    (D := 16) (ψ := (276238928111/10000000000000 : ℝ)) half_14_08_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_08_φ1, half_14_08_φ2, half_14_08_φ3, half_14_08_φ4, half_14_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_08_φ1, half_14_08_φ2, half_14_08_φ3, half_14_08_φ4, half_14_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_08_φ1, half_14_08_φ2, half_14_08_φ3, half_14_08_φ4, half_14_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_08 half_11_08
    (by simpa only [half_14_08_φ5, show (2:ℝ)*16=32 by norm_num] using half_14_08_hx5)
  exact h.weaken (by norm_num [half_14_08_φ1, half_14_08_φ2, half_14_08_φ3, half_14_08_φ4, half_14_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_08_hx3 : SourcePowerBound (powerBoxCross 16 11 8 half_14_08_φ3) (63704517417219/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 11) (u := 9) (t := 12)
    (D := 8) (ψ := (78257471933/2000000000000 : ℝ)) half_14_08_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_08_φ1, half_14_08_φ2, half_14_08_φ3, half_14_08_φ4, half_14_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_08_φ1, half_14_08_φ2, half_14_08_φ3, half_14_08_φ4, half_14_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_08_φ1, half_14_08_φ2, half_14_08_φ3, half_14_08_φ4, half_14_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_08 half_12_08
    (by simpa only [half_14_08_φ4, show (2:ℝ)*8=16 by norm_num] using half_14_08_hx4)
  exact h.weaken (by norm_num [half_14_08_φ1, half_14_08_φ2, half_14_08_φ3, half_14_08_φ4, half_14_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_08_hx2 : SourcePowerBound (powerBoxCross 16 12 4 half_14_08_φ2) (142353156081703/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 12) (u := 10) (t := 13)
    (D := 4) (ψ := (4278985213/100000000000 : ℝ)) half_14_08_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_08_φ1, half_14_08_φ2, half_14_08_φ3, half_14_08_φ4, half_14_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_08_φ1, half_14_08_φ2, half_14_08_φ3, half_14_08_φ4, half_14_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_08_φ1, half_14_08_φ2, half_14_08_φ3, half_14_08_φ4, half_14_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_08 half_13_08
    (by simpa only [half_14_08_φ3, show (2:ℝ)*4=8 by norm_num] using half_14_08_hx3)
  exact h.weaken (by norm_num [half_14_08_φ1, half_14_08_φ2, half_14_08_φ3, half_14_08_φ4, half_14_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_08_hx1 : SourcePowerBound (powerBoxCross 16 13 2 half_14_08_φ1) (159380184294153/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 13) (u := 11) (t := 14)
    (D := 2) (ψ := (447006361073/10000000000000 : ℝ)) half_14_08_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_08_φ1, half_14_08_φ2, half_14_08_φ3, half_14_08_φ4, half_14_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_08_φ1, half_14_08_φ2, half_14_08_φ3, half_14_08_φ4, half_14_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_08_φ1, half_14_08_φ2, half_14_08_φ3, half_14_08_φ4, half_14_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_08 half_14_07
    (by simpa only [half_14_08_φ2, show (2:ℝ)*2=4 by norm_num] using half_14_08_hx2)
  exact h.weaken (by norm_num [half_14_08_φ1, half_14_08_φ2, half_14_08_φ3, half_14_08_φ4, half_14_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_08 : AdmissibleExponent 16 28 (170918954065003/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 12) (ψ := (230775395417/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_13_08
    (by simpa only [half_14_08_φ1] using half_14_08_hx1)
  exact admissibleExponent_mono h (by norm_num [half_14_08_φ1, half_14_08_φ2, half_14_08_φ3, half_14_08_φ4, half_14_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_9_09_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (15904657807/400000000000 : ℝ)

private def half_9_09_φ2 : Fin 2 → ℝ := Fin.snoc half_9_09_φ1 (17964594749/500000000000 : ℝ)

private def half_9_09_φ3 : Fin 3 → ℝ := Fin.snoc half_9_09_φ2 (49807852577/2500000000000 : ℝ)

private theorem half_9_09_hF2 : SourcePowerBound (paddedMoment 16 0 2 8 half_9_09_φ3) (13394742245833/2000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_09_φ3 (by norm_num [half_9_09_φ1, half_9_09_φ2, half_9_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_09_φ1, half_9_09_φ2, half_9_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_09_φ1, half_9_09_φ2, half_9_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_09_φ1, half_9_09_φ2, half_9_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_9_09_hF1 : SourcePowerBound (paddedMoment 16 0 1 8 half_9_09_φ3) (5131580748611/2000000000000 : ℝ) := by
  have h := padded_second_power (k := 16) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_09_φ3 (by norm_num [half_9_09_φ1, half_9_09_φ2, half_9_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_09_φ1, half_9_09_φ2, half_9_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_09_φ1, half_9_09_φ2, half_9_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_09_φ1, half_9_09_φ2, half_9_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_9_09_hx3 : SourcePowerBound (powerBoxCross 16 6 8 half_9_09_φ3) (76194754921971/10000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 16) (s := 6) (r := 1) (v := 2) (t := 9) (D := 8)
    (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
    (by norm_num) half_9_09_φ3 (by norm_num [half_9_09_φ1, half_9_09_φ2, half_9_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_09_φ1, half_9_09_φ2, half_9_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_9_09_hF1 half_9_09_hF2 half_9_08
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_9_09_φ1, half_9_09_φ2, half_9_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_09_hx2 : SourcePowerBound (powerBoxCross 16 7 4 half_9_09_φ2) (42070426739687/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 7) (u := 5) (t := 8)
    (D := 4) (ψ := (49807852577/2500000000000 : ℝ)) half_9_09_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_09_φ1, half_9_09_φ2, half_9_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_09_φ1, half_9_09_φ2, half_9_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_09_φ1, half_9_09_φ2, half_9_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_6 SeedCompletionEven16SecondSeeds.degree16_half_8
    (by simpa only [half_9_09_φ3, show (2:ℝ)*4=8 by norm_num] using half_9_09_hx3)
  exact h.weaken (by norm_num [half_9_09_φ1, half_9_09_φ2, half_9_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_09_hx1 : SourcePowerBound (powerBoxCross 16 8 2 half_9_09_φ1) (18960982303829/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 8) (u := 6) (t := 9)
    (D := 2) (ψ := (17964594749/500000000000 : ℝ)) half_9_09_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_09_φ1, half_9_09_φ2, half_9_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_09_φ1, half_9_09_φ2, half_9_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_09_φ1, half_9_09_φ2, half_9_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_7 half_9_08
    (by simpa only [half_9_09_φ2, show (2:ℝ)*2=4 by norm_num] using half_9_09_hx2)
  exact h.weaken (by norm_num [half_9_09_φ1, half_9_09_φ2, half_9_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_09 : AdmissibleExponent 16 18 (10076915819677/1000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 7) (ψ := (15904657807/400000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8
    (by simpa only [half_9_09_φ1] using half_9_09_hx1)
  exact admissibleExponent_mono h (by norm_num [half_9_09_φ1, half_9_09_φ2, half_9_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_10_09_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (410258406449/10000000000000 : ℝ)

private def half_10_09_φ2 : Fin 2 → ℝ := Fin.snoc half_10_09_φ1 (191416574089/5000000000000 : ℝ)

private def half_10_09_φ3 : Fin 3 → ℝ := Fin.snoc half_10_09_φ2 (288581396661/10000000000000 : ℝ)

private theorem half_10_09_hF2 : SourcePowerBound (paddedMoment 16 0 2 8 half_10_09_φ3) (1533117929801/250000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_10_09_φ3 (by norm_num [half_10_09_φ1, half_10_09_φ2, half_10_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_09_φ1, half_10_09_φ2, half_10_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_09_φ1, half_10_09_φ2, half_10_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_10_09_φ1, half_10_09_φ2, half_10_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_10_09_hx3 : SourcePowerBound (powerBoxCross 16 7 8 half_10_09_φ3) (42843716290471/5000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 16) (s := 7) (r := 2) (v := 9) (w := 10) (D := 8)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_10_09_φ3 (by norm_num [half_10_09_φ1, half_10_09_φ2, half_10_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_09_φ1, half_10_09_φ2, half_10_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_10_09_hF2 half_9_09 half_10_08
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_10_09_φ1, half_10_09_φ2, half_10_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_10_09_hx2 : SourcePowerBound (powerBoxCross 16 8 4 half_10_09_φ2) (47579964695407/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 8) (u := 6) (t := 9)
    (D := 4) (ψ := (288581396661/10000000000000 : ℝ)) half_10_09_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_09_φ1, half_10_09_φ2, half_10_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_09_φ1, half_10_09_φ2, half_10_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_09_φ1, half_10_09_φ2, half_10_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_7 half_9_09
    (by simpa only [half_10_09_φ3, show (2:ℝ)*4=8 by norm_num] using half_10_09_hx3)
  exact h.weaken (by norm_num [half_10_09_φ1, half_10_09_φ2, half_10_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_10_09_hx1 : SourcePowerBound (powerBoxCross 16 9 2 half_10_09_φ1) (26761319294283/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 9) (u := 7) (t := 10)
    (D := 2) (ψ := (191416574089/5000000000000 : ℝ)) half_10_09_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_09_φ1, half_10_09_φ2, half_10_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_09_φ1, half_10_09_φ2, half_10_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_09_φ1, half_10_09_φ2, half_10_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8 half_10_08
    (by simpa only [half_10_09_φ2, show (2:ℝ)*2=4 by norm_num] using half_10_09_hx2)
  exact h.weaken (by norm_num [half_10_09_φ1, half_10_09_φ2, half_10_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_10_09 : AdmissibleExponent 16 20 (22803934017353/2000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 8) (ψ := (410258406449/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_9_09
    (by simpa only [half_10_09_φ1] using half_10_09_hx1)
  exact admissibleExponent_mono h (by norm_num [half_10_09_φ1, half_10_09_φ2, half_10_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_11_09_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (424781342297/10000000000000 : ℝ)

private def half_11_09_φ2 : Fin 2 → ℝ := Fin.snoc half_11_09_φ1 (80976859737/2000000000000 : ℝ)

private def half_11_09_φ3 : Fin 3 → ℝ := Fin.snoc half_11_09_φ2 (72245033441/2000000000000 : ℝ)

private def half_11_09_φ4 : Fin 4 → ℝ := Fin.snoc half_11_09_φ3 (9202396777/500000000000 : ℝ)

private theorem half_11_09_hF2 : SourcePowerBound (paddedMoment 16 0 2 16 half_11_09_φ4) (15625551306457/2000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_11_09_φ4 (by norm_num [half_11_09_φ1, half_11_09_φ2, half_11_09_φ3, half_11_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_09_φ1, half_11_09_φ2, half_11_09_φ3, half_11_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_09_φ1, half_11_09_φ2, half_11_09_φ3, half_11_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_11_09_φ1, half_11_09_φ2, half_11_09_φ3, half_11_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_11_09_hF1 : SourcePowerBound (paddedMoment 16 0 1 16 half_11_09_φ4) (5875183768819/2000000000000 : ℝ) := by
  have h := padded_second_power (k := 16) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_11_09_φ4 (by norm_num [half_11_09_φ1, half_11_09_φ2, half_11_09_φ3, half_11_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_09_φ1, half_11_09_φ2, half_11_09_φ3, half_11_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_09_φ1, half_11_09_φ2, half_11_09_φ3, half_11_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_11_09_φ1, half_11_09_φ2, half_11_09_φ3, half_11_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_11_09_hx4 : SourcePowerBound (powerBoxCross 16 7 16 half_11_09_φ4) (43701503957577/5000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 16) (s := 7) (r := 1) (v := 2) (t := 10) (D := 16)
    (a := (1/10 : ℝ)) (b := (1/5 : ℝ)) (c := (7/10 : ℝ))
    (by norm_num) half_11_09_φ4 (by norm_num [half_11_09_φ1, half_11_09_φ2, half_11_09_φ3, half_11_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_09_φ1, half_11_09_φ2, half_11_09_φ3, half_11_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_11_09_hF1 half_11_09_hF2 half_10_09
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_11_09_φ1, half_11_09_φ2, half_11_09_φ3, half_11_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_11_09_hx3 : SourcePowerBound (powerBoxCross 16 8 8 half_11_09_φ3) (47675230181653/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 8) (u := 6) (t := 9)
    (D := 8) (ψ := (9202396777/500000000000 : ℝ)) half_11_09_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_09_φ1, half_11_09_φ2, half_11_09_φ3, half_11_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_09_φ1, half_11_09_φ2, half_11_09_φ3, half_11_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_09_φ1, half_11_09_φ2, half_11_09_φ3, half_11_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_7 half_9_09
    (by simpa only [half_11_09_φ4, show (2:ℝ)*8=16 by norm_num] using half_11_09_hx4)
  exact h.weaken (by norm_num [half_11_09_φ1, half_11_09_φ2, half_11_09_φ3, half_11_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_11_09_hx2 : SourcePowerBound (powerBoxCross 16 9 4 half_11_09_φ2) (53220925769177/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 9) (u := 7) (t := 10)
    (D := 4) (ψ := (72245033441/2000000000000 : ℝ)) half_11_09_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_09_φ1, half_11_09_φ2, half_11_09_φ3, half_11_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_09_φ1, half_11_09_φ2, half_11_09_φ3, half_11_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_09_φ1, half_11_09_φ2, half_11_09_φ3, half_11_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8 half_10_09
    (by simpa only [half_11_09_φ3, show (2:ℝ)*4=8 by norm_num] using half_11_09_hx3)
  exact h.weaken (by norm_num [half_11_09_φ1, half_11_09_φ2, half_11_09_φ3, half_11_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_11_09_hx1 : SourcePowerBound (powerBoxCross 16 10 2 half_11_09_φ1) (59800554289147/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 10) (u := 8) (t := 11)
    (D := 2) (ψ := (80976859737/2000000000000 : ℝ)) half_11_09_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_09_φ1, half_11_09_φ2, half_11_09_φ3, half_11_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_09_φ1, half_11_09_φ2, half_11_09_φ3, half_11_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_09_φ1, half_11_09_φ2, half_11_09_φ3, half_11_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_09 half_11_08
    (by simpa only [half_11_09_φ2, show (2:ℝ)*2=4 by norm_num] using half_11_09_hx2)
  exact h.weaken (by norm_num [half_11_09_φ1, half_11_09_φ2, half_11_09_φ3, half_11_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_11_09 : AdmissibleExponent 16 22 (127671954081937/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 9) (ψ := (424781342297/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_10_09
    (by simpa only [half_11_09_φ1] using half_11_09_hx1)
  exact admissibleExponent_mono h (by norm_num [half_11_09_φ1, half_11_09_φ2, half_11_09_φ3, half_11_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_12_09_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (436574175297/10000000000000 : ℝ)

private def half_12_09_φ2 : Fin 2 → ℝ := Fin.snoc half_12_09_φ1 (104883283101/2500000000000 : ℝ)

private def half_12_09_φ3 : Fin 3 → ℝ := Fin.snoc half_12_09_φ2 (385920945141/10000000000000 : ℝ)

private def half_12_09_φ4 : Fin 4 → ℝ := Fin.snoc half_12_09_φ3 (279252757293/10000000000000 : ℝ)

private theorem half_12_09_hF2 : SourcePowerBound (paddedMoment 16 0 2 16 half_12_09_φ4) (2861694181757/400000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_12_09_φ4 (by norm_num [half_12_09_φ1, half_12_09_φ2, half_12_09_φ3, half_12_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_09_φ1, half_12_09_φ2, half_12_09_φ3, half_12_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_09_φ1, half_12_09_φ2, half_12_09_φ3, half_12_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_12_09_φ1, half_12_09_φ2, half_12_09_φ3, half_12_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_12_09_hx4 : SourcePowerBound (powerBoxCross 16 8 16 half_12_09_φ4) (12022354782867/1250000000000 : ℝ) := by
  have h := full_A_cross_power (k := 16) (s := 8) (r := 2) (v := 10) (w := 11) (D := 16)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_12_09_φ4 (by norm_num [half_12_09_φ1, half_12_09_φ2, half_12_09_φ3, half_12_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_09_φ1, half_12_09_φ2, half_12_09_φ3, half_12_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_12_09_hF2 half_10_09 half_11_09
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_12_09_φ1, half_12_09_φ2, half_12_09_φ3, half_12_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_12_09_hx3 : SourcePowerBound (powerBoxCross 16 9 8 half_12_09_φ3) (105797655376861/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 9) (u := 7) (t := 10)
    (D := 8) (ψ := (279252757293/10000000000000 : ℝ)) half_12_09_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_09_φ1, half_12_09_φ2, half_12_09_φ3, half_12_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_09_φ1, half_12_09_φ2, half_12_09_φ3, half_12_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_09_φ1, half_12_09_φ2, half_12_09_φ3, half_12_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8 half_10_09
    (by simpa only [half_12_09_φ4, show (2:ℝ)*8=16 by norm_num] using half_12_09_hx4)
  exact h.weaken (by norm_num [half_12_09_φ1, half_12_09_φ2, half_12_09_φ3, half_12_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_12_09_hx2 : SourcePowerBound (powerBoxCross 16 10 4 half_12_09_φ2) (1476616041393/125000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 10) (u := 8) (t := 11)
    (D := 4) (ψ := (385920945141/10000000000000 : ℝ)) half_12_09_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_09_φ1, half_12_09_φ2, half_12_09_φ3, half_12_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_09_φ1, half_12_09_φ2, half_12_09_φ3, half_12_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_09_φ1, half_12_09_φ2, half_12_09_φ3, half_12_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_09 half_11_09
    (by simpa only [half_12_09_φ3, show (2:ℝ)*4=8 by norm_num] using half_12_09_hx3)
  exact h.weaken (by norm_num [half_12_09_φ1, half_12_09_φ2, half_12_09_φ3, half_12_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_12_09_hx1 : SourcePowerBound (powerBoxCross 16 11 2 half_12_09_φ1) (66267350225533/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 11) (u := 9) (t := 12)
    (D := 2) (ψ := (104883283101/2500000000000 : ℝ)) half_12_09_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_09_φ1, half_12_09_φ2, half_12_09_φ3, half_12_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_09_φ1, half_12_09_φ2, half_12_09_φ3, half_12_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_09_φ1, half_12_09_φ2, half_12_09_φ3, half_12_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_09 half_12_08
    (by simpa only [half_12_09_φ2, show (2:ℝ)*2=4 by norm_num] using half_12_09_hx2)
  exact h.weaken (by norm_num [half_12_09_φ1, half_12_09_φ2, half_12_09_φ3, half_12_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_12_09 : AdmissibleExponent 16 24 (141702758132303/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 10) (ψ := (436574175297/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_11_09
    (by simpa only [half_12_09_φ1] using half_12_09_hx1)
  exact admissibleExponent_mono h (by norm_num [half_12_09_φ1, half_12_09_φ2, half_12_09_φ3, half_12_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_13_09_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (224746085647/5000000000000 : ℝ)

private def half_13_09_φ2 : Fin 2 → ℝ := Fin.snoc half_13_09_φ1 (434354668093/10000000000000 : ℝ)

private def half_13_09_φ3 : Fin 3 → ℝ := Fin.snoc half_13_09_φ2 (206691734193/5000000000000 : ℝ)

private def half_13_09_φ4 : Fin 4 → ℝ := Fin.snoc half_13_09_φ3 (181660191463/5000000000000 : ℝ)

private def half_13_09_φ5 : Fin 5 → ℝ := Fin.snoc half_13_09_φ4 (181169640173/10000000000000 : ℝ)

private theorem half_13_09_hF2 : SourcePowerBound (paddedMoment 16 0 2 32 half_13_09_φ5) (2178064627769/250000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_13_09_φ5 (by norm_num [half_13_09_φ1, half_13_09_φ2, half_13_09_φ3, half_13_09_φ4, half_13_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_09_φ1, half_13_09_φ2, half_13_09_φ3, half_13_09_φ4, half_13_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_09_φ1, half_13_09_φ2, half_13_09_φ3, half_13_09_φ4, half_13_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_13_09_φ1, half_13_09_φ2, half_13_09_φ3, half_13_09_φ4, half_13_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_13_09_hF1 : SourcePowerBound (paddedMoment 16 0 1 32 half_13_09_φ5) (809354875923/250000000000 : ℝ) := by
  have h := padded_second_power (k := 16) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_13_09_φ5 (by norm_num [half_13_09_φ1, half_13_09_φ2, half_13_09_φ3, half_13_09_φ4, half_13_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_09_φ1, half_13_09_φ2, half_13_09_φ3, half_13_09_φ4, half_13_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_09_φ1, half_13_09_φ2, half_13_09_φ3, half_13_09_φ4, half_13_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_13_09_φ1, half_13_09_φ2, half_13_09_φ3, half_13_09_φ4, half_13_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_13_09_hx5 : SourcePowerBound (powerBoxCross 16 8 32 half_13_09_φ5) (24246544684989/2500000000000 : ℝ) := by
  have h := full_B_cross_power (k := 16) (s := 8) (r := 1) (v := 2) (t := 12) (D := 32)
    (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
    (by norm_num) half_13_09_φ5 (by norm_num [half_13_09_φ1, half_13_09_φ2, half_13_09_φ3, half_13_09_φ4, half_13_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_09_φ1, half_13_09_φ2, half_13_09_φ3, half_13_09_φ4, half_13_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_13_09_hF1 half_13_09_hF2 half_12_09
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_13_09_φ1, half_13_09_φ2, half_13_09_φ3, half_13_09_φ4, half_13_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_09_hx4 : SourcePowerBound (powerBoxCross 16 9 16 half_13_09_φ4) (3279399826207/312500000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 4) (s := 9) (u := 7) (t := 10)
    (D := 16) (ψ := (181169640173/10000000000000 : ℝ)) half_13_09_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_09_φ1, half_13_09_φ2, half_13_09_φ3, half_13_09_φ4, half_13_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_09_φ1, half_13_09_φ2, half_13_09_φ3, half_13_09_φ4, half_13_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_09_φ1, half_13_09_φ2, half_13_09_φ3, half_13_09_φ4, half_13_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8 half_10_09
    (by simpa only [half_13_09_φ5, show (2:ℝ)*16=32 by norm_num] using half_13_09_hx5)
  exact h.weaken (by norm_num [half_13_09_φ1, half_13_09_φ2, half_13_09_φ3, half_13_09_φ4, half_13_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_09_hx3 : SourcePowerBound (powerBoxCross 16 10 8 half_13_09_φ3) (11638437379247/1000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 10) (u := 8) (t := 11)
    (D := 8) (ψ := (181660191463/5000000000000 : ℝ)) half_13_09_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_09_φ1, half_13_09_φ2, half_13_09_φ3, half_13_09_φ4, half_13_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_09_φ1, half_13_09_φ2, half_13_09_φ3, half_13_09_φ4, half_13_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_09_φ1, half_13_09_φ2, half_13_09_φ3, half_13_09_φ4, half_13_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_09 half_11_09
    (by simpa only [half_13_09_φ4, show (2:ℝ)*8=16 by norm_num] using half_13_09_hx4)
  exact h.weaken (by norm_num [half_13_09_φ1, half_13_09_φ2, half_13_09_φ3, half_13_09_φ4, half_13_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_09_hx2 : SourcePowerBound (powerBoxCross 16 11 4 half_13_09_φ2) (130079680871269/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 11) (u := 9) (t := 12)
    (D := 4) (ψ := (206691734193/5000000000000 : ℝ)) half_13_09_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_09_φ1, half_13_09_φ2, half_13_09_φ3, half_13_09_φ4, half_13_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_09_φ1, half_13_09_φ2, half_13_09_φ3, half_13_09_φ4, half_13_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_09_φ1, half_13_09_φ2, half_13_09_φ3, half_13_09_φ4, half_13_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_09 half_12_09
    (by simpa only [half_13_09_φ3, show (2:ℝ)*4=8 by norm_num] using half_13_09_hx3)
  exact h.weaken (by norm_num [half_13_09_φ1, half_13_09_φ2, half_13_09_φ3, half_13_09_φ4, half_13_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_09_hx1 : SourcePowerBound (powerBoxCross 16 12 2 half_13_09_φ1) (36445705565121/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 12) (u := 10) (t := 13)
    (D := 2) (ψ := (434354668093/10000000000000 : ℝ)) half_13_09_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_09_φ1, half_13_09_φ2, half_13_09_φ3, half_13_09_φ4, half_13_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_09_φ1, half_13_09_φ2, half_13_09_φ3, half_13_09_φ4, half_13_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_09_φ1, half_13_09_φ2, half_13_09_φ3, half_13_09_φ4, half_13_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_09 half_13_08
    (by simpa only [half_13_09_φ2, show (2:ℝ)*2=4 by norm_num] using half_13_09_hx2)
  exact h.weaken (by norm_num [half_13_09_φ1, half_13_09_φ2, half_13_09_φ3, half_13_09_φ4, half_13_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_09 : AdmissibleExponent 16 26 (78060571100123/5000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 11) (ψ := (224746085647/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_12_09
    (by simpa only [half_13_09_φ1] using half_13_09_hx1)
  exact admissibleExponent_mono h (by norm_num [half_13_09_φ1, half_13_09_φ2, half_13_09_φ3, half_13_09_φ4, half_13_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_14_09_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (461107901731/10000000000000 : ℝ)

private def half_14_09_φ2 : Fin 2 → ℝ := Fin.snoc half_14_09_φ1 (89392554473/2000000000000 : ℝ)

private def half_14_09_φ3 : Fin 3 → ℝ := Fin.snoc half_14_09_φ2 (427868223963/10000000000000 : ℝ)

private def half_14_09_φ4 : Fin 4 → ℝ := Fin.snoc half_14_09_φ3 (391232632113/10000000000000 : ℝ)

private def half_14_09_φ5 : Fin 5 → ℝ := Fin.snoc half_14_09_φ4 (69009271101/2500000000000 : ℝ)

private theorem half_14_09_hF2 : SourcePowerBound (paddedMoment 16 0 2 32 half_14_09_φ5) (998195154301/125000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_14_09_φ5 (by norm_num [half_14_09_φ1, half_14_09_φ2, half_14_09_φ3, half_14_09_φ4, half_14_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_09_φ1, half_14_09_φ2, half_14_09_φ3, half_14_09_φ4, half_14_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_09_φ1, half_14_09_φ2, half_14_09_φ3, half_14_09_φ4, half_14_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_14_09_φ1, half_14_09_φ2, half_14_09_φ3, half_14_09_φ4, half_14_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_14_09_hx5 : SourcePowerBound (powerBoxCross 16 9 32 half_14_09_φ5) (52475728875131/5000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 16) (s := 9) (r := 2) (v := 12) (w := 12) (D := 32)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_14_09_φ5 (by norm_num [half_14_09_φ1, half_14_09_φ2, half_14_09_φ3, half_14_09_φ4, half_14_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_09_φ1, half_14_09_φ2, half_14_09_φ3, half_14_09_φ4, half_14_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_14_09_hF2 half_12_09 half_12_09
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_14_09_φ1, half_14_09_φ2, half_14_09_φ3, half_14_09_φ4, half_14_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_09_hx4 : SourcePowerBound (powerBoxCross 16 10 16 half_14_09_φ4) (114678666442657/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 4) (s := 10) (u := 8) (t := 11)
    (D := 16) (ψ := (69009271101/2500000000000 : ℝ)) half_14_09_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_09_φ1, half_14_09_φ2, half_14_09_φ3, half_14_09_φ4, half_14_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_09_φ1, half_14_09_φ2, half_14_09_φ3, half_14_09_φ4, half_14_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_09_φ1, half_14_09_φ2, half_14_09_φ3, half_14_09_φ4, half_14_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_09 half_11_09
    (by simpa only [half_14_09_φ5, show (2:ℝ)*16=32 by norm_num] using half_14_09_hx5)
  exact h.weaken (by norm_num [half_14_09_φ1, half_14_09_φ2, half_14_09_φ3, half_14_09_φ4, half_14_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_09_hx3 : SourcePowerBound (powerBoxCross 16 11 8 half_14_09_φ3) (7963910576847/625000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 11) (u := 9) (t := 12)
    (D := 8) (ψ := (391232632113/10000000000000 : ℝ)) half_14_09_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_09_φ1, half_14_09_φ2, half_14_09_φ3, half_14_09_φ4, half_14_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_09_φ1, half_14_09_φ2, half_14_09_φ3, half_14_09_φ4, half_14_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_09_φ1, half_14_09_φ2, half_14_09_φ3, half_14_09_φ4, half_14_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_09 half_12_09
    (by simpa only [half_14_09_φ4, show (2:ℝ)*8=16 by norm_num] using half_14_09_hx4)
  exact h.weaken (by norm_num [half_14_09_φ1, half_14_09_φ2, half_14_09_φ3, half_14_09_φ4, half_14_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_09_hx2 : SourcePowerBound (powerBoxCross 16 12 4 half_14_09_φ2) (14236549046887/1000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 12) (u := 10) (t := 13)
    (D := 4) (ψ := (427868223963/10000000000000 : ℝ)) half_14_09_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_09_φ1, half_14_09_φ2, half_14_09_φ3, half_14_09_φ4, half_14_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_09_φ1, half_14_09_φ2, half_14_09_φ3, half_14_09_φ4, half_14_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_09_φ1, half_14_09_φ2, half_14_09_φ3, half_14_09_φ4, half_14_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_09 half_13_09
    (by simpa only [half_14_09_φ3, show (2:ℝ)*4=8 by norm_num] using half_14_09_hx3)
  exact h.weaken (by norm_num [half_14_09_φ1, half_14_09_φ2, half_14_09_φ3, half_14_09_φ4, half_14_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_09_hx1 : SourcePowerBound (powerBoxCross 16 13 2 half_14_09_φ1) (159383380872403/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 13) (u := 11) (t := 14)
    (D := 2) (ψ := (89392554473/2000000000000 : ℝ)) half_14_09_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_09_φ1, half_14_09_φ2, half_14_09_φ3, half_14_09_φ4, half_14_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_09_φ1, half_14_09_φ2, half_14_09_φ3, half_14_09_φ4, half_14_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_09_φ1, half_14_09_φ2, half_14_09_φ3, half_14_09_φ4, half_14_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_09 half_14_08
    (by simpa only [half_14_09_φ2, show (2:ℝ)*2=4 by norm_num] using half_14_09_hx2)
  exact h.weaken (by norm_num [half_14_09_φ1, half_14_09_φ2, half_14_09_φ3, half_14_09_φ4, half_14_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_09 : AdmissibleExponent 16 28 (85455539207839/5000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 12) (ψ := (461107901731/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_13_09
    (by simpa only [half_14_09_φ1] using half_14_09_hx1)
  exact admissibleExponent_mono h (by norm_num [half_14_09_φ1, half_14_09_φ2, half_14_09_φ3, half_14_09_φ4, half_14_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_9_10_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (79523215587/2000000000000 : ℝ)

private def half_9_10_φ2 : Fin 2 → ℝ := Fin.snoc half_9_10_φ1 (179645876561/5000000000000 : ℝ)

private def half_9_10_φ3 : Fin 3 → ℝ := Fin.snoc half_9_10_φ2 (99615302257/5000000000000 : ℝ)

private theorem half_9_10_hF2 : SourcePowerBound (paddedMoment 16 0 2 8 half_9_10_φ3) (13394754079861/2000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_10_φ3 (by norm_num [half_9_10_φ1, half_9_10_φ2, half_9_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_10_φ1, half_9_10_φ2, half_9_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_10_φ1, half_9_10_φ2, half_9_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_10_φ1, half_9_10_φ2, half_9_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_9_10_hF1 : SourcePowerBound (paddedMoment 16 0 1 8 half_9_10_φ3) (5131584693287/2000000000000 : ℝ) := by
  have h := padded_second_power (k := 16) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_10_φ3 (by norm_num [half_9_10_φ1, half_9_10_φ2, half_9_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_10_φ1, half_9_10_φ2, half_9_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_10_φ1, half_9_10_φ2, half_9_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_10_φ1, half_9_10_φ2, half_9_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_9_10_hx3 : SourcePowerBound (powerBoxCross 16 6 8 half_9_10_φ3) (38097385045333/5000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 16) (s := 6) (r := 1) (v := 2) (t := 9) (D := 8)
    (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
    (by norm_num) half_9_10_φ3 (by norm_num [half_9_10_φ1, half_9_10_φ2, half_9_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_10_φ1, half_9_10_φ2, half_9_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_9_10_hF1 half_9_10_hF2 half_9_09
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_9_10_φ1, half_9_10_φ2, half_9_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_10_hx2 : SourcePowerBound (powerBoxCross 16 7 4 half_9_10_φ2) (84140862687637/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 7) (u := 5) (t := 8)
    (D := 4) (ψ := (99615302257/5000000000000 : ℝ)) half_9_10_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_10_φ1, half_9_10_φ2, half_9_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_10_φ1, half_9_10_φ2, half_9_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_10_φ1, half_9_10_φ2, half_9_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_6 SeedCompletionEven16SecondSeeds.degree16_half_8
    (by simpa only [half_9_10_φ3, show (2:ℝ)*4=8 by norm_num] using half_9_10_hx3)
  exact h.weaken (by norm_num [half_9_10_φ1, half_9_10_φ2, half_9_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_10_hx1 : SourcePowerBound (powerBoxCross 16 8 2 half_9_10_φ1) (47402457190017/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 8) (u := 6) (t := 9)
    (D := 2) (ψ := (179645876561/5000000000000 : ℝ)) half_9_10_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_10_φ1, half_9_10_φ2, half_9_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_10_φ1, half_9_10_φ2, half_9_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_10_φ1, half_9_10_φ2, half_9_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_7 half_9_09
    (by simpa only [half_9_10_φ2, show (2:ℝ)*2=4 by norm_num] using half_9_10_hx2)
  exact h.weaken (by norm_num [half_9_10_φ1, half_9_10_φ2, half_9_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_10 : AdmissibleExponent 16 18 (100769155549059/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 7) (ψ := (79523215587/2000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8
    (by simpa only [half_9_10_φ1] using half_9_10_hx1)
  exact admissibleExponent_mono h (by norm_num [half_9_10_φ1, half_9_10_φ2, half_9_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_10_10_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (205127864953/5000000000000 : ℝ)

private def half_10_10_φ2 : Fin 2 → ℝ := Fin.snoc half_10_10_φ1 (95708139183/2500000000000 : ℝ)

private def half_10_10_φ3 : Fin 3 → ℝ := Fin.snoc half_10_10_φ2 (288578820651/10000000000000 : ℝ)

private theorem half_10_10_hF2 : SourcePowerBound (paddedMoment 16 0 2 8 half_10_10_φ3) (12264996034399/2000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_10_10_φ3 (by norm_num [half_10_10_φ1, half_10_10_φ2, half_10_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_10_φ1, half_10_10_φ2, half_10_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_10_φ1, half_10_10_φ2, half_10_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_10_10_φ1, half_10_10_φ2, half_10_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_10_10_hx3 : SourcePowerBound (powerBoxCross 16 7 8 half_10_10_φ3) (17137504624393/2000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 16) (s := 7) (r := 2) (v := 9) (w := 10) (D := 8)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_10_10_φ3 (by norm_num [half_10_10_φ1, half_10_10_φ2, half_10_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_10_φ1, half_10_10_φ2, half_10_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_10_10_hF2 half_9_10 half_10_09
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_10_10_φ1, half_10_10_φ2, half_10_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_10_10_hx2 : SourcePowerBound (powerBoxCross 16 8 4 half_10_10_φ2) (95159997673941/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 8) (u := 6) (t := 9)
    (D := 4) (ψ := (288578820651/10000000000000 : ℝ)) half_10_10_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_10_φ1, half_10_10_φ2, half_10_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_10_φ1, half_10_10_φ2, half_10_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_10_φ1, half_10_10_φ2, half_10_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_7 half_9_10
    (by simpa only [half_10_10_φ3, show (2:ℝ)*4=8 by norm_num] using half_10_10_hx3)
  exact h.weaken (by norm_num [half_10_10_φ1, half_10_10_φ2, half_10_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_10_10_hx1 : SourcePowerBound (powerBoxCross 16 9 2 half_10_10_φ1) (53522649466397/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 9) (u := 7) (t := 10)
    (D := 2) (ψ := (95708139183/2500000000000 : ℝ)) half_10_10_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_10_φ1, half_10_10_φ2, half_10_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_10_φ1, half_10_10_φ2, half_10_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_10_φ1, half_10_10_φ2, half_10_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8 half_10_09
    (by simpa only [half_10_10_φ2, show (2:ℝ)*2=4 by norm_num] using half_10_10_hx2)
  exact h.weaken (by norm_num [half_10_10_φ1, half_10_10_φ2, half_10_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_10_10 : AdmissibleExponent 16 20 (28504911585299/2500000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 8) (ψ := (205127864953/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_9_10
    (by simpa only [half_10_10_φ1] using half_10_10_hx1)
  exact admissibleExponent_mono h (by norm_num [half_10_10_φ1, half_10_10_φ2, half_10_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_11_10_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (212385551677/5000000000000 : ℝ)

private def half_11_10_φ2 : Fin 2 → ℝ := Fin.snoc half_11_10_φ1 (404883527851/10000000000000 : ℝ)

private def half_11_10_φ3 : Fin 3 → ℝ := Fin.snoc half_11_10_φ2 (180612017023/5000000000000 : ℝ)

private def half_11_10_φ4 : Fin 4 → ℝ := Fin.snoc half_11_10_φ3 (9202129973/500000000000 : ℝ)

private theorem half_11_10_hF2 : SourcePowerBound (paddedMoment 16 0 2 16 half_11_10_φ4) (15625708617601/2000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_11_10_φ4 (by norm_num [half_11_10_φ1, half_11_10_φ2, half_11_10_φ3, half_11_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_10_φ1, half_11_10_φ2, half_11_10_φ3, half_11_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_10_φ1, half_11_10_φ2, half_11_10_φ3, half_11_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_11_10_φ1, half_11_10_φ2, half_11_10_φ3, half_11_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_11_10_hF1 : SourcePowerBound (paddedMoment 16 0 1 16 half_11_10_φ4) (5875236205867/2000000000000 : ℝ) := by
  have h := padded_second_power (k := 16) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_11_10_φ4 (by norm_num [half_11_10_φ1, half_11_10_φ2, half_11_10_φ3, half_11_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_10_φ1, half_11_10_φ2, half_11_10_φ3, half_11_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_10_φ1, half_11_10_φ2, half_11_10_φ3, half_11_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_11_10_φ1, half_11_10_φ2, half_11_10_φ3, half_11_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_11_10_hx4 : SourcePowerBound (powerBoxCross 16 7 16 half_11_10_φ4) (87403316614919/10000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 16) (s := 7) (r := 1) (v := 2) (t := 10) (D := 16)
    (a := (1/10 : ℝ)) (b := (1/5 : ℝ)) (c := (7/10 : ℝ))
    (by norm_num) half_11_10_φ4 (by norm_num [half_11_10_φ1, half_11_10_φ2, half_11_10_φ3, half_11_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_10_φ1, half_11_10_φ2, half_11_10_φ3, half_11_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_11_10_hF1 half_11_10_hF2 half_10_10
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_11_10_φ1, half_11_10_φ2, half_11_10_φ3, half_11_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_11_10_hx3 : SourcePowerBound (powerBoxCross 16 8 8 half_11_10_φ3) (148985517369/15625000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 8) (u := 6) (t := 9)
    (D := 8) (ψ := (9202129973/500000000000 : ℝ)) half_11_10_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_10_φ1, half_11_10_φ2, half_11_10_φ3, half_11_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_10_φ1, half_11_10_φ2, half_11_10_φ3, half_11_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_10_φ1, half_11_10_φ2, half_11_10_φ3, half_11_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_7 half_9_10
    (by simpa only [half_11_10_φ4, show (2:ℝ)*8=16 by norm_num] using half_11_10_hx4)
  exact h.weaken (by norm_num [half_11_10_φ1, half_11_10_φ2, half_11_10_φ3, half_11_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_11_10_hx2 : SourcePowerBound (powerBoxCross 16 9 4 half_11_10_φ2) (5322105643411/500000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 9) (u := 7) (t := 10)
    (D := 4) (ψ := (180612017023/5000000000000 : ℝ)) half_11_10_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_10_φ1, half_11_10_φ2, half_11_10_φ3, half_11_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_10_φ1, half_11_10_φ2, half_11_10_φ3, half_11_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_10_φ1, half_11_10_φ2, half_11_10_φ3, half_11_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8 half_10_10
    (by simpa only [half_11_10_φ3, show (2:ℝ)*4=8 by norm_num] using half_11_10_hx3)
  exact h.weaken (by norm_num [half_11_10_φ1, half_11_10_φ2, half_11_10_φ3, half_11_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_11_10_hx1 : SourcePowerBound (powerBoxCross 16 10 2 half_11_10_φ1) (2990029808663/250000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 10) (u := 8) (t := 11)
    (D := 2) (ψ := (404883527851/10000000000000 : ℝ)) half_11_10_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_10_φ1, half_11_10_φ2, half_11_10_φ3, half_11_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_10_φ1, half_11_10_φ2, half_11_10_φ3, half_11_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_10_φ1, half_11_10_φ2, half_11_10_φ3, half_11_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_10 half_11_09
    (by simpa only [half_11_10_φ2, show (2:ℝ)*2=4 by norm_num] using half_11_10_hx2)
  exact h.weaken (by norm_num [half_11_10_φ1, half_11_10_φ2, half_11_10_φ3, half_11_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_11_10 : AdmissibleExponent 16 22 (63835921655123/5000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 9) (ψ := (212385551677/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_10_10
    (by simpa only [half_11_10_φ1] using half_11_10_hx1)
  exact admissibleExponent_mono h (by norm_num [half_11_10_φ1, half_11_10_φ2, half_11_10_φ3, half_11_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_12_10_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (436541322819/10000000000000 : ℝ)

private def half_12_10_φ2 : Fin 2 → ℝ := Fin.snoc half_12_10_φ1 (209765191871/5000000000000 : ℝ)

private def half_12_10_φ3 : Fin 3 → ℝ := Fin.snoc half_12_10_φ2 (385917259027/10000000000000 : ℝ)

private def half_12_10_φ4 : Fin 4 → ℝ := Fin.snoc half_12_10_φ3 (17452401801/625000000000 : ℝ)

private theorem half_12_10_hF2 : SourcePowerBound (paddedMoment 16 0 2 16 half_12_10_φ4) (3577238362591/500000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_12_10_φ4 (by norm_num [half_12_10_φ1, half_12_10_φ2, half_12_10_φ3, half_12_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_10_φ1, half_12_10_φ2, half_12_10_φ3, half_12_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_10_φ1, half_12_10_φ2, half_12_10_φ3, half_12_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_12_10_φ1, half_12_10_φ2, half_12_10_φ3, half_12_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_12_10_hx4 : SourcePowerBound (powerBoxCross 16 8 16 half_12_10_φ4) (19235976907727/2000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 16) (s := 8) (r := 2) (v := 10) (w := 11) (D := 16)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_12_10_φ4 (by norm_num [half_12_10_φ1, half_12_10_φ2, half_12_10_φ3, half_12_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_10_φ1, half_12_10_φ2, half_12_10_φ3, half_12_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_12_10_hF2 half_10_10 half_11_10
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_12_10_φ1, half_12_10_φ2, half_12_10_φ3, half_12_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_12_10_hx3 : SourcePowerBound (powerBoxCross 16 9 8 half_12_10_φ3) (4231943171333/400000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 9) (u := 7) (t := 10)
    (D := 8) (ψ := (17452401801/625000000000 : ℝ)) half_12_10_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_10_φ1, half_12_10_φ2, half_12_10_φ3, half_12_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_10_φ1, half_12_10_φ2, half_12_10_φ3, half_12_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_10_φ1, half_12_10_φ2, half_12_10_φ3, half_12_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8 half_10_10
    (by simpa only [half_12_10_φ4, show (2:ℝ)*8=16 by norm_num] using half_12_10_hx4)
  exact h.weaken (by norm_num [half_12_10_φ1, half_12_10_φ2, half_12_10_φ3, half_12_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_12_10_hx2 : SourcePowerBound (powerBoxCross 16 10 4 half_12_10_φ2) (29532539390047/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 10) (u := 8) (t := 11)
    (D := 4) (ψ := (385917259027/10000000000000 : ℝ)) half_12_10_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_10_φ1, half_12_10_φ2, half_12_10_φ3, half_12_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_10_φ1, half_12_10_φ2, half_12_10_φ3, half_12_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_10_φ1, half_12_10_φ2, half_12_10_φ3, half_12_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_10 half_11_10
    (by simpa only [half_12_10_φ3, show (2:ℝ)*4=8 by norm_num] using half_12_10_hx3)
  exact h.weaken (by norm_num [half_12_10_φ1, half_12_10_φ2, half_12_10_φ3, half_12_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_12_10_hx1 : SourcePowerBound (powerBoxCross 16 11 2 half_12_10_φ1) (4141718159267/312500000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 11) (u := 9) (t := 12)
    (D := 2) (ψ := (209765191871/5000000000000 : ℝ)) half_12_10_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_10_φ1, half_12_10_φ2, half_12_10_φ3, half_12_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_10_φ1, half_12_10_φ2, half_12_10_φ3, half_12_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_10_φ1, half_12_10_φ2, half_12_10_φ3, half_12_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_10 half_12_09
    (by simpa only [half_12_10_φ2, show (2:ℝ)*2=4 by norm_num] using half_12_10_hx2)
  exact h.weaken (by norm_num [half_12_10_φ1, half_12_10_φ2, half_12_10_φ3, half_12_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_12_10 : AdmissibleExponent 16 24 (141702348875743/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 10) (ψ := (436541322819/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_11_10
    (by simpa only [half_12_10_φ1] using half_12_10_hx1)
  exact admissibleExponent_mono h (by norm_num [half_12_10_φ1, half_12_10_φ2, half_12_10_φ3, half_12_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_13_10_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (449408979849/10000000000000 : ℝ)

private def half_13_10_φ2 : Fin 2 → ℝ := Fin.snoc half_13_10_φ1 (43434741259/1000000000000 : ℝ)

private def half_13_10_φ3 : Fin 3 → ℝ := Fin.snoc half_13_10_φ2 (82675674599/2000000000000 : ℝ)

private def half_13_10_φ4 : Fin 4 → ℝ := Fin.snoc half_13_10_φ3 (181653274279/5000000000000 : ℝ)

private def half_13_10_φ5 : Fin 5 → ℝ := Fin.snoc half_13_10_φ4 (181109789193/10000000000000 : ℝ)

private theorem half_13_10_hF2 : SourcePowerBound (paddedMoment 16 0 2 32 half_13_10_φ5) (3485208014267/400000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_13_10_φ5 (by norm_num [half_13_10_φ1, half_13_10_φ2, half_13_10_φ3, half_13_10_φ4, half_13_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_10_φ1, half_13_10_φ2, half_13_10_φ3, half_13_10_φ4, half_13_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_10_φ1, half_13_10_φ2, half_13_10_φ3, half_13_10_φ4, half_13_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_13_10_φ1, half_13_10_φ2, half_13_10_φ3, half_13_10_φ4, half_13_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_13_10_hF1 : SourcePowerBound (paddedMoment 16 0 1 32 half_13_10_φ5) (1295069338089/400000000000 : ℝ) := by
  have h := padded_second_power (k := 16) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_13_10_φ5 (by norm_num [half_13_10_φ1, half_13_10_φ2, half_13_10_φ3, half_13_10_φ4, half_13_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_10_φ1, half_13_10_φ2, half_13_10_φ3, half_13_10_φ4, half_13_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_10_φ1, half_13_10_φ2, half_13_10_φ3, half_13_10_φ4, half_13_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_13_10_φ1, half_13_10_φ2, half_13_10_φ3, half_13_10_φ4, half_13_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_13_10_hx5 : SourcePowerBound (powerBoxCross 16 8 32 half_13_10_φ5) (24247311773061/2500000000000 : ℝ) := by
  have h := full_B_cross_power (k := 16) (s := 8) (r := 1) (v := 2) (t := 12) (D := 32)
    (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
    (by norm_num) half_13_10_φ5 (by norm_num [half_13_10_φ1, half_13_10_φ2, half_13_10_φ3, half_13_10_φ4, half_13_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_10_φ1, half_13_10_φ2, half_13_10_φ3, half_13_10_φ4, half_13_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_13_10_hF1 half_13_10_hF2 half_12_10
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_13_10_φ1, half_13_10_φ2, half_13_10_φ3, half_13_10_φ4, half_13_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_10_hx4 : SourcePowerBound (powerBoxCross 16 9 16 half_13_10_φ4) (104943313711147/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 4) (s := 9) (u := 7) (t := 10)
    (D := 16) (ψ := (181109789193/10000000000000 : ℝ)) half_13_10_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_10_φ1, half_13_10_φ2, half_13_10_φ3, half_13_10_φ4, half_13_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_10_φ1, half_13_10_φ2, half_13_10_φ3, half_13_10_φ4, half_13_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_10_φ1, half_13_10_φ2, half_13_10_φ3, half_13_10_φ4, half_13_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8 half_10_10
    (by simpa only [half_13_10_φ5, show (2:ℝ)*16=32 by norm_num] using half_13_10_hx5)
  exact h.weaken (by norm_num [half_13_10_φ1, half_13_10_φ2, half_13_10_φ3, half_13_10_φ4, half_13_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_10_hx3 : SourcePowerBound (powerBoxCross 16 10 8 half_13_10_φ3) (116386794106447/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 10) (u := 8) (t := 11)
    (D := 8) (ψ := (181653274279/5000000000000 : ℝ)) half_13_10_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_10_φ1, half_13_10_φ2, half_13_10_φ3, half_13_10_φ4, half_13_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_10_φ1, half_13_10_φ2, half_13_10_φ3, half_13_10_φ4, half_13_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_10_φ1, half_13_10_φ2, half_13_10_φ3, half_13_10_φ4, half_13_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_10 half_11_10
    (by simpa only [half_13_10_φ4, show (2:ℝ)*8=16 by norm_num] using half_13_10_hx4)
  exact h.weaken (by norm_num [half_13_10_φ1, half_13_10_φ2, half_13_10_φ3, half_13_10_φ4, half_13_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_10_hx2 : SourcePowerBound (powerBoxCross 16 11 4 half_13_10_φ2) (16260246907391/1250000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 11) (u := 9) (t := 12)
    (D := 4) (ψ := (82675674599/2000000000000 : ℝ)) half_13_10_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_10_φ1, half_13_10_φ2, half_13_10_φ3, half_13_10_φ4, half_13_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_10_φ1, half_13_10_φ2, half_13_10_φ3, half_13_10_φ4, half_13_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_10_φ1, half_13_10_φ2, half_13_10_φ3, half_13_10_φ4, half_13_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_10 half_12_10
    (by simpa only [half_13_10_φ3, show (2:ℝ)*4=8 by norm_num] using half_13_10_hx3)
  exact h.weaken (by norm_num [half_13_10_φ1, half_13_10_φ2, half_13_10_φ3, half_13_10_φ4, half_13_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_10_hx1 : SourcePowerBound (powerBoxCross 16 12 2 half_13_10_φ1) (145783527050561/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 12) (u := 10) (t := 13)
    (D := 2) (ψ := (43434741259/1000000000000 : ℝ)) half_13_10_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_10_φ1, half_13_10_φ2, half_13_10_φ3, half_13_10_φ4, half_13_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_10_φ1, half_13_10_φ2, half_13_10_φ3, half_13_10_φ4, half_13_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_10_φ1, half_13_10_φ2, half_13_10_φ3, half_13_10_φ4, half_13_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_10 half_13_09
    (by simpa only [half_13_10_φ2, show (2:ℝ)*2=4 by norm_num] using half_13_10_hx2)
  exact h.weaken (by norm_num [half_13_10_φ1, half_13_10_φ2, half_13_10_φ3, half_13_10_φ4, half_13_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_10 : AdmissibleExponent 16 26 (9757495849193/625000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 11) (ψ := (449408979849/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_12_10
    (by simpa only [half_13_10_φ1] using half_13_10_hx1)
  exact admissibleExponent_mono h (by norm_num [half_13_10_φ1, half_13_10_φ2, half_13_10_φ3, half_13_10_φ4, half_13_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_14_10_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (230464277887/5000000000000 : ℝ)

private def half_14_10_φ2 : Fin 2 → ℝ := Fin.snoc half_14_10_φ1 (223472894307/5000000000000 : ℝ)

private def half_14_10_φ3 : Fin 3 → ℝ := Fin.snoc half_14_10_φ2 (26741084153/625000000000 : ℝ)

private def half_14_10_φ4 : Fin 4 → ℝ := Fin.snoc half_14_10_φ3 (391212436899/10000000000000 : ℝ)

private def half_14_10_φ5 : Fin 5 → ℝ := Fin.snoc half_14_10_φ4 (275961241023/10000000000000 : ℝ)

private theorem half_14_10_hF2 : SourcePowerBound (paddedMoment 16 0 2 32 half_14_10_φ5) (7986925840589/1000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_14_10_φ5 (by norm_num [half_14_10_φ1, half_14_10_φ2, half_14_10_φ3, half_14_10_φ4, half_14_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_10_φ1, half_14_10_φ2, half_14_10_φ3, half_14_10_φ4, half_14_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_10_φ1, half_14_10_φ2, half_14_10_φ3, half_14_10_φ4, half_14_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_14_10_φ1, half_14_10_φ2, half_14_10_φ3, half_14_10_φ4, half_14_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_14_10_hx5 : SourcePowerBound (powerBoxCross 16 9 32 half_14_10_φ5) (104957846608617/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 16) (s := 9) (r := 2) (v := 12) (w := 12) (D := 32)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_14_10_φ5 (by norm_num [half_14_10_φ1, half_14_10_φ2, half_14_10_φ3, half_14_10_φ4, half_14_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_10_φ1, half_14_10_φ2, half_14_10_φ3, half_14_10_φ4, half_14_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_14_10_hF2 half_12_10 half_12_10
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_14_10_φ1, half_14_10_φ2, half_14_10_φ3, half_14_10_φ4, half_14_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_10_hx4 : SourcePowerBound (powerBoxCross 16 10 16 half_14_10_φ4) (28671081886507/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 4) (s := 10) (u := 8) (t := 11)
    (D := 16) (ψ := (275961241023/10000000000000 : ℝ)) half_14_10_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_10_φ1, half_14_10_φ2, half_14_10_φ3, half_14_10_φ4, half_14_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_10_φ1, half_14_10_φ2, half_14_10_φ3, half_14_10_φ4, half_14_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_10_φ1, half_14_10_φ2, half_14_10_φ3, half_14_10_φ4, half_14_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_10 half_11_10
    (by simpa only [half_14_10_φ5, show (2:ℝ)*16=32 by norm_num] using half_14_10_hx5)
  exact h.weaken (by norm_num [half_14_10_φ1, half_14_10_φ2, half_14_10_φ3, half_14_10_φ4, half_14_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_10_hx3 : SourcePowerBound (powerBoxCross 16 11 8 half_14_10_φ3) (25485610555439/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 11) (u := 9) (t := 12)
    (D := 8) (ψ := (391212436899/10000000000000 : ℝ)) half_14_10_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_10_φ1, half_14_10_φ2, half_14_10_φ3, half_14_10_φ4, half_14_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_10_φ1, half_14_10_φ2, half_14_10_φ3, half_14_10_φ4, half_14_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_10_φ1, half_14_10_φ2, half_14_10_φ3, half_14_10_φ4, half_14_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_10 half_12_10
    (by simpa only [half_14_10_φ4, show (2:ℝ)*8=16 by norm_num] using half_14_10_hx4)
  exact h.weaken (by norm_num [half_14_10_φ1, half_14_10_φ2, half_14_10_φ3, half_14_10_φ4, half_14_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_10_hx2 : SourcePowerBound (powerBoxCross 16 12 4 half_14_10_φ2) (35592643404843/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 12) (u := 10) (t := 13)
    (D := 4) (ψ := (26741084153/625000000000 : ℝ)) half_14_10_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_10_φ1, half_14_10_φ2, half_14_10_φ3, half_14_10_φ4, half_14_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_10_φ1, half_14_10_φ2, half_14_10_φ3, half_14_10_φ4, half_14_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_10_φ1, half_14_10_φ2, half_14_10_φ3, half_14_10_φ4, half_14_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_10 half_13_10
    (by simpa only [half_14_10_φ3, show (2:ℝ)*4=8 by norm_num] using half_14_10_hx3)
  exact h.weaken (by norm_num [half_14_10_φ1, half_14_10_φ2, half_14_10_φ3, half_14_10_φ4, half_14_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_10_hx1 : SourcePowerBound (powerBoxCross 16 13 2 half_14_10_φ1) (79692424295643/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 13) (u := 11) (t := 14)
    (D := 2) (ψ := (223472894307/5000000000000 : ℝ)) half_14_10_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_10_φ1, half_14_10_φ2, half_14_10_φ3, half_14_10_φ4, half_14_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_10_φ1, half_14_10_φ2, half_14_10_φ3, half_14_10_φ4, half_14_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_10_φ1, half_14_10_φ2, half_14_10_φ3, half_14_10_φ4, half_14_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_10 half_14_09
    (by simpa only [half_14_10_φ2, show (2:ℝ)*2=4 by norm_num] using half_14_10_hx2)
  exact h.weaken (by norm_num [half_14_10_φ1, half_14_10_φ2, half_14_10_φ3, half_14_10_φ4, half_14_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_10 : AdmissibleExponent 16 28 (42727015621409/2500000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 12) (ψ := (230464277887/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_13_10
    (by simpa only [half_14_10_φ1] using half_14_10_hx1)
  exact admissibleExponent_mono h (by norm_num [half_14_10_φ1, half_14_10_φ2, half_14_10_φ3, half_14_10_φ4, half_14_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_9_11_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (198807995947/5000000000000 : ℝ)

private def half_9_11_φ2 : Fin 2 → ℝ := Fin.snoc half_9_11_φ1 (179645859943/5000000000000 : ℝ)

private def half_9_11_φ3 : Fin 3 → ℝ := Fin.snoc half_9_11_φ2 (199230415723/10000000000000 : ℝ)

private theorem half_9_11_hF2 : SourcePowerBound (paddedMoment 16 0 2 8 half_9_11_φ3) (13394756852473/2000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_11_φ3 (by norm_num [half_9_11_φ1, half_9_11_φ2, half_9_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_11_φ1, half_9_11_φ2, half_9_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_11_φ1, half_9_11_φ2, half_9_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_11_φ1, half_9_11_φ2, half_9_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_9_11_hF1 : SourcePowerBound (paddedMoment 16 0 1 8 half_9_11_φ3) (5131585617491/2000000000000 : ℝ) := by
  have h := padded_second_power (k := 16) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_11_φ3 (by norm_num [half_9_11_φ1, half_9_11_φ2, half_9_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_11_φ1, half_9_11_φ2, half_9_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_11_φ1, half_9_11_φ2, half_9_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_11_φ1, half_9_11_φ2, half_9_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_9_11_hx3 : SourcePowerBound (powerBoxCross 16 6 8 half_9_11_φ3) (76194773644561/10000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 16) (s := 6) (r := 1) (v := 2) (t := 9) (D := 8)
    (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
    (by norm_num) half_9_11_φ3 (by norm_num [half_9_11_φ1, half_9_11_φ2, half_9_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_11_φ1, half_9_11_φ2, half_9_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_9_11_hF1 half_9_11_hF2 half_9_10
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_9_11_φ1, half_9_11_φ2, half_9_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_11_hx2 : SourcePowerBound (powerBoxCross 16 7 4 half_9_11_φ2) (84140864845049/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 7) (u := 5) (t := 8)
    (D := 4) (ψ := (199230415723/10000000000000 : ℝ)) half_9_11_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_11_φ1, half_9_11_φ2, half_9_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_11_φ1, half_9_11_φ2, half_9_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_11_φ1, half_9_11_φ2, half_9_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_6 SeedCompletionEven16SecondSeeds.degree16_half_8
    (by simpa only [half_9_11_φ3, show (2:ℝ)*4=8 by norm_num] using half_9_11_hx3)
  exact h.weaken (by norm_num [half_9_11_φ1, half_9_11_φ2, half_9_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_11_hx1 : SourcePowerBound (powerBoxCross 16 8 2 half_9_11_φ1) (94804915050311/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 8) (u := 6) (t := 9)
    (D := 2) (ψ := (179645859943/5000000000000 : ℝ)) half_9_11_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_11_φ1, half_9_11_φ2, half_9_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_11_φ1, half_9_11_φ2, half_9_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_11_φ1, half_9_11_φ2, half_9_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_7 half_9_10
    (by simpa only [half_9_11_φ2, show (2:ℝ)*2=4 by norm_num] using half_9_11_hx2)
  exact h.weaken (by norm_num [half_9_11_φ1, half_9_11_φ2, half_9_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_11 : AdmissibleExponent 16 18 (100769154928721/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 7) (ψ := (198807995947/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8
    (by simpa only [half_9_11_φ1] using half_9_11_hx1)
  exact admissibleExponent_mono h (by norm_num [half_9_11_φ1, half_9_11_φ2, half_9_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_10_11_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (410255021877/10000000000000 : ℝ)

private def half_10_11_φ2 : Fin 2 → ℝ := Fin.snoc half_10_11_φ1 (382832403817/10000000000000 : ℝ)

private def half_10_11_φ3 : Fin 3 → ℝ := Fin.snoc half_10_11_φ2 (72144536343/2500000000000 : ℝ)

private theorem half_10_11_hF2 : SourcePowerBound (paddedMoment 16 0 2 8 half_10_11_φ3) (6132504930203/1000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_10_11_φ3 (by norm_num [half_10_11_φ1, half_10_11_φ2, half_10_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_11_φ1, half_10_11_φ2, half_10_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_11_φ1, half_10_11_φ2, half_10_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_10_11_φ1, half_10_11_φ2, half_10_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_10_11_hx3 : SourcePowerBound (powerBoxCross 16 7 8 half_10_11_φ3) (85687546952767/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 16) (s := 7) (r := 2) (v := 9) (w := 10) (D := 8)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_10_11_φ3 (by norm_num [half_10_11_φ1, half_10_11_φ2, half_10_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_11_φ1, half_10_11_φ2, half_10_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_10_11_hF2 half_9_11 half_10_10
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_10_11_φ1, half_10_11_φ2, half_10_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_10_11_hx2 : SourcePowerBound (powerBoxCross 16 8 4 half_10_11_φ2) (95160015709369/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 8) (u := 6) (t := 9)
    (D := 4) (ψ := (72144536343/2500000000000 : ℝ)) half_10_11_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_11_φ1, half_10_11_φ2, half_10_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_11_φ1, half_10_11_φ2, half_10_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_11_φ1, half_10_11_φ2, half_10_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_7 half_9_11
    (by simpa only [half_10_11_φ3, show (2:ℝ)*4=8 by norm_num] using half_10_11_hx3)
  exact h.weaken (by norm_num [half_10_11_φ1, half_10_11_φ2, half_10_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_10_11_hx1 : SourcePowerBound (powerBoxCross 16 9 2 half_10_11_φ1) (107045304764627/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 9) (u := 7) (t := 10)
    (D := 2) (ψ := (382832403817/10000000000000 : ℝ)) half_10_11_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_11_φ1, half_10_11_φ2, half_10_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_11_φ1, half_10_11_φ2, half_10_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_11_φ1, half_10_11_φ2, half_10_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8 half_10_10
    (by simpa only [half_10_11_φ2, show (2:ℝ)*2=4 by norm_num] using half_10_11_hx2)
  exact h.weaken (by norm_num [half_10_11_φ1, half_10_11_φ2, half_10_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_10_11 : AdmissibleExponent 16 20 (14252455017067/1250000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 8) (ψ := (410255021877/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_9_11
    (by simpa only [half_10_11_φ1] using half_10_11_hx1)
  exact admissibleExponent_mono h (by norm_num [half_10_11_φ1, half_10_11_φ2, half_10_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_11_11_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (424768094051/10000000000000 : ℝ)

private def half_11_11_φ2 : Fin 2 → ℝ := Fin.snoc half_11_11_φ1 (80976663529/2000000000000 : ℝ)

private def half_11_11_φ3 : Fin 3 → ℝ := Fin.snoc half_11_11_φ2 (22576482207/625000000000 : ℝ)

private def half_11_11_φ4 : Fin 4 → ℝ := Fin.snoc half_11_11_φ3 (92020540377/5000000000000 : ℝ)

private theorem half_11_11_hF2 : SourcePowerBound (paddedMoment 16 0 2 16 half_11_11_φ4) (7812877065071/1000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_11_11_φ4 (by norm_num [half_11_11_φ1, half_11_11_φ2, half_11_11_φ3, half_11_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_11_φ1, half_11_11_φ2, half_11_11_φ3, half_11_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_11_φ1, half_11_11_φ2, half_11_11_φ3, half_11_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_11_11_φ1, half_11_11_φ2, half_11_11_φ3, half_11_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_11_11_hF1 : SourcePowerBound (paddedMoment 16 0 1 16 half_11_11_φ4) (2937625688357/1000000000000 : ℝ) := by
  have h := padded_second_power (k := 16) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_11_11_φ4 (by norm_num [half_11_11_φ1, half_11_11_φ2, half_11_11_φ3, half_11_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_11_φ1, half_11_11_φ2, half_11_11_φ3, half_11_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_11_φ1, half_11_11_φ2, half_11_11_φ3, half_11_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_11_11_φ1, half_11_11_φ2, half_11_11_φ3, half_11_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_11_11_hx4 : SourcePowerBound (powerBoxCross 16 7 16 half_11_11_φ4) (87403406328191/10000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 16) (s := 7) (r := 1) (v := 2) (t := 10) (D := 16)
    (a := (1/10 : ℝ)) (b := (1/5 : ℝ)) (c := (7/10 : ℝ))
    (by norm_num) half_11_11_φ4 (by norm_num [half_11_11_φ1, half_11_11_φ2, half_11_11_φ3, half_11_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_11_φ1, half_11_11_φ2, half_11_11_φ3, half_11_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_11_11_hF1 half_11_11_hF2 half_10_11
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_11_11_φ1, half_11_11_φ2, half_11_11_φ3, half_11_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_11_11_hx3 : SourcePowerBound (powerBoxCross 16 8 8 half_11_11_φ3) (95350810192087/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 8) (u := 6) (t := 9)
    (D := 8) (ψ := (92020540377/5000000000000 : ℝ)) half_11_11_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_11_φ1, half_11_11_φ2, half_11_11_φ3, half_11_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_11_φ1, half_11_11_φ2, half_11_11_φ3, half_11_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_11_φ1, half_11_11_φ2, half_11_11_φ3, half_11_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_7 half_9_11
    (by simpa only [half_11_11_φ4, show (2:ℝ)*8=16 by norm_num] using half_11_11_hx4)
  exact h.weaken (by norm_num [half_11_11_φ1, half_11_11_φ2, half_11_11_φ3, half_11_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_11_11_hx2 : SourcePowerBound (powerBoxCross 16 9 4 half_11_11_φ2) (21288437934283/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 9) (u := 7) (t := 10)
    (D := 4) (ψ := (22576482207/625000000000 : ℝ)) half_11_11_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_11_φ1, half_11_11_φ2, half_11_11_φ3, half_11_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_11_φ1, half_11_11_φ2, half_11_11_φ3, half_11_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_11_φ1, half_11_11_φ2, half_11_11_φ3, half_11_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8 half_10_11
    (by simpa only [half_11_11_φ3, show (2:ℝ)*4=8 by norm_num] using half_11_11_hx3)
  exact h.weaken (by norm_num [half_11_11_φ1, half_11_11_φ2, half_11_11_φ3, half_11_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_11_11_hx1 : SourcePowerBound (powerBoxCross 16 10 2 half_11_11_φ1) (119601217708087/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 10) (u := 8) (t := 11)
    (D := 2) (ψ := (80976663529/2000000000000 : ℝ)) half_11_11_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_11_φ1, half_11_11_φ2, half_11_11_φ3, half_11_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_11_φ1, half_11_11_φ2, half_11_11_φ3, half_11_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_11_φ1, half_11_11_φ2, half_11_11_φ3, half_11_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_11 half_11_10
    (by simpa only [half_11_11_φ2, show (2:ℝ)*2=4 by norm_num] using half_11_11_hx2)
  exact h.weaken (by norm_num [half_11_11_φ1, half_11_11_φ2, half_11_11_φ3, half_11_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_11_11 : AdmissibleExponent 16 22 (7979488218441/625000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 9) (ψ := (424768094051/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_10_11
    (by simpa only [half_11_11_φ1] using half_11_11_hx1)
  exact admissibleExponent_mono h (by norm_num [half_11_11_φ1, half_11_11_φ2, half_11_11_φ3, half_11_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_12_11_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (87306120841/2000000000000 : ℝ)

private def half_12_11_φ2 : Fin 2 → ℝ := Fin.snoc half_12_11_φ1 (209764773779/5000000000000 : ℝ)

private def half_12_11_φ3 : Fin 3 → ℝ := Fin.snoc half_12_11_φ2 (48239516427/1250000000000 : ℝ)

private def half_12_11_φ4 : Fin 4 → ℝ := Fin.snoc half_12_11_φ3 (279233959483/10000000000000 : ℝ)

private theorem half_12_11_hF2 : SourcePowerBound (paddedMoment 16 0 2 16 half_12_11_φ4) (7154553908021/1000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_12_11_φ4 (by norm_num [half_12_11_φ1, half_12_11_φ2, half_12_11_φ3, half_12_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_11_φ1, half_12_11_φ2, half_12_11_φ3, half_12_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_11_φ1, half_12_11_φ2, half_12_11_φ3, half_12_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_12_11_φ1, half_12_11_φ2, half_12_11_φ3, half_12_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_12_11_hx4 : SourcePowerBound (powerBoxCross 16 8 16 half_12_11_φ4) (12022527634179/1250000000000 : ℝ) := by
  have h := full_A_cross_power (k := 16) (s := 8) (r := 2) (v := 10) (w := 11) (D := 16)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_12_11_φ4 (by norm_num [half_12_11_φ1, half_12_11_φ2, half_12_11_φ3, half_12_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_11_φ1, half_12_11_φ2, half_12_11_φ3, half_12_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_12_11_hF2 half_10_11 half_11_11
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_12_11_φ1, half_12_11_φ2, half_12_11_φ3, half_12_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_12_11_hx3 : SourcePowerBound (powerBoxCross 16 9 8 half_12_11_φ3) (105798878733957/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 9) (u := 7) (t := 10)
    (D := 8) (ψ := (279233959483/10000000000000 : ℝ)) half_12_11_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_11_φ1, half_12_11_φ2, half_12_11_φ3, half_12_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_11_φ1, half_12_11_φ2, half_12_11_φ3, half_12_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_11_φ1, half_12_11_φ2, half_12_11_φ3, half_12_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8 half_10_11
    (by simpa only [half_12_11_φ4, show (2:ℝ)*8=16 by norm_num] using half_12_11_hx4)
  exact h.weaken (by norm_num [half_12_11_φ1, half_12_11_φ2, half_12_11_φ3, half_12_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_12_11_hx2 : SourcePowerBound (powerBoxCross 16 10 4 half_12_11_φ2) (23626088715421/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 10) (u := 8) (t := 11)
    (D := 4) (ψ := (48239516427/1250000000000 : ℝ)) half_12_11_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_11_φ1, half_12_11_φ2, half_12_11_φ3, half_12_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_11_φ1, half_12_11_φ2, half_12_11_φ3, half_12_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_11_φ1, half_12_11_φ2, half_12_11_φ3, half_12_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_11 half_11_11
    (by simpa only [half_12_11_φ3, show (2:ℝ)*4=8 by norm_num] using half_12_11_hx3)
  exact h.weaken (by norm_num [half_12_11_φ1, half_12_11_φ2, half_12_11_φ3, half_12_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_12_11_hx1 : SourcePowerBound (powerBoxCross 16 11 2 half_12_11_φ1) (16566884599761/1250000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 11) (u := 9) (t := 12)
    (D := 2) (ψ := (209764773779/5000000000000 : ℝ)) half_12_11_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_11_φ1, half_12_11_φ2, half_12_11_φ3, half_12_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_11_φ1, half_12_11_φ2, half_12_11_φ3, half_12_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_11_φ1, half_12_11_φ2, half_12_11_φ3, half_12_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_11 half_12_10
    (by simpa only [half_12_11_φ2, show (2:ℝ)*2=4 by norm_num] using half_12_11_hx2)
  exact h.weaken (by norm_num [half_12_11_φ1, half_12_11_φ2, half_12_11_φ3, half_12_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_12_11 : AdmissibleExponent 16 24 (141702219486393/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 10) (ψ := (87306120841/2000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_11_11
    (by simpa only [half_12_11_φ1] using half_12_11_hx1)
  exact admissibleExponent_mono h (by norm_num [half_12_11_φ1, half_12_11_φ2, half_12_11_φ3, half_12_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_13_11_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (449379054201/10000000000000 : ℝ)

private def half_13_11_φ2 : Fin 2 → ℝ := Fin.snoc half_13_11_φ1 (434344961741/10000000000000 : ℝ)

private def half_13_11_φ3 : Fin 3 → ℝ := Fin.snoc half_13_11_φ2 (206688354653/5000000000000 : ℝ)

private def half_13_11_φ4 : Fin 4 → ℝ := Fin.snoc half_13_11_φ3 (45412731687/1250000000000 : ℝ)

private def half_13_11_φ5 : Fin 5 → ℝ := Fin.snoc half_13_11_φ4 (90544659243/5000000000000 : ℝ)

private theorem half_13_11_hF2 : SourcePowerBound (paddedMoment 16 0 2 32 half_13_11_φ5) (1742657292493/200000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_13_11_φ5 (by norm_num [half_13_11_φ1, half_13_11_φ2, half_13_11_φ3, half_13_11_φ4, half_13_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_11_φ1, half_13_11_φ2, half_13_11_φ3, half_13_11_φ4, half_13_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_11_φ1, half_13_11_φ2, half_13_11_φ3, half_13_11_φ4, half_13_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_13_11_φ1, half_13_11_φ2, half_13_11_φ3, half_13_11_φ4, half_13_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_13_11_hF1 : SourcePowerBound (paddedMoment 16 0 1 32 half_13_11_φ5) (647552430831/200000000000 : ℝ) := by
  have h := padded_second_power (k := 16) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_13_11_φ5 (by norm_num [half_13_11_φ1, half_13_11_φ2, half_13_11_φ3, half_13_11_φ4, half_13_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_11_φ1, half_13_11_φ2, half_13_11_φ3, half_13_11_φ4, half_13_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_11_φ1, half_13_11_φ2, half_13_11_φ3, half_13_11_φ4, half_13_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_13_11_φ1, half_13_11_φ2, half_13_11_φ3, half_13_11_φ4, half_13_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_13_11_hx5 : SourcePowerBound (powerBoxCross 16 8 32 half_13_11_φ5) (96990328085049/10000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 16) (s := 8) (r := 1) (v := 2) (t := 12) (D := 32)
    (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
    (by norm_num) half_13_11_φ5 (by norm_num [half_13_11_φ1, half_13_11_φ2, half_13_11_φ3, half_13_11_φ4, half_13_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_11_φ1, half_13_11_φ2, half_13_11_φ3, half_13_11_φ4, half_13_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_13_11_hF1 half_13_11_hF2 half_12_11
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_13_11_φ1, half_13_11_φ2, half_13_11_φ3, half_13_11_φ4, half_13_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_11_hx4 : SourcePowerBound (powerBoxCross 16 9 16 half_13_11_φ4) (52472104716677/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 4) (s := 9) (u := 7) (t := 10)
    (D := 16) (ψ := (90544659243/5000000000000 : ℝ)) half_13_11_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_11_φ1, half_13_11_φ2, half_13_11_φ3, half_13_11_φ4, half_13_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_11_φ1, half_13_11_φ2, half_13_11_φ3, half_13_11_φ4, half_13_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_11_φ1, half_13_11_φ2, half_13_11_φ3, half_13_11_φ4, half_13_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8 half_10_11
    (by simpa only [half_13_11_φ5, show (2:ℝ)*16=32 by norm_num] using half_13_11_hx5)
  exact h.weaken (by norm_num [half_13_11_φ1, half_13_11_φ2, half_13_11_φ3, half_13_11_φ4, half_13_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_11_hx3 : SourcePowerBound (powerBoxCross 16 10 8 half_13_11_φ3) (116387660815363/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 10) (u := 8) (t := 11)
    (D := 8) (ψ := (45412731687/1250000000000 : ℝ)) half_13_11_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_11_φ1, half_13_11_φ2, half_13_11_φ3, half_13_11_φ4, half_13_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_11_φ1, half_13_11_φ2, half_13_11_φ3, half_13_11_φ4, half_13_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_11_φ1, half_13_11_φ2, half_13_11_φ3, half_13_11_φ4, half_13_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_11 half_11_11
    (by simpa only [half_13_11_φ4, show (2:ℝ)*8=16 by norm_num] using half_13_11_hx4)
  exact h.weaken (by norm_num [half_13_11_φ1, half_13_11_φ2, half_13_11_φ3, half_13_11_φ4, half_13_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_11_hx2 : SourcePowerBound (powerBoxCross 16 11 4 half_13_11_φ2) (1300828060461/100000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 11) (u := 9) (t := 12)
    (D := 4) (ψ := (206688354653/5000000000000 : ℝ)) half_13_11_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_11_φ1, half_13_11_φ2, half_13_11_φ3, half_13_11_φ4, half_13_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_11_φ1, half_13_11_φ2, half_13_11_φ3, half_13_11_φ4, half_13_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_11_φ1, half_13_11_φ2, half_13_11_φ3, half_13_11_φ4, half_13_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_11 half_12_11
    (by simpa only [half_13_11_φ3, show (2:ℝ)*4=8 by norm_num] using half_13_11_hx3)
  exact h.weaken (by norm_num [half_13_11_φ1, half_13_11_φ2, half_13_11_φ3, half_13_11_φ4, half_13_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_11_hx1 : SourcePowerBound (powerBoxCross 16 12 2 half_13_11_φ1) (145783797603503/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 12) (u := 10) (t := 13)
    (D := 2) (ψ := (434344961741/10000000000000 : ℝ)) half_13_11_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_11_φ1, half_13_11_φ2, half_13_11_φ3, half_13_11_φ4, half_13_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_11_φ1, half_13_11_φ2, half_13_11_φ3, half_13_11_φ4, half_13_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_11_φ1, half_13_11_φ2, half_13_11_φ3, half_13_11_φ4, half_13_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_11 half_13_10
    (by simpa only [half_13_11_φ2, show (2:ℝ)*2=4 by norm_num] using half_13_11_hx2)
  exact h.weaken (by norm_num [half_13_11_φ1, half_13_11_φ2, half_13_11_φ3, half_13_11_φ4, half_13_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_11 : AdmissibleExponent 16 26 (78059757925063/5000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 11) (ψ := (449379054201/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_12_11
    (by simpa only [half_13_11_φ1] using half_13_11_hx1)
  exact admissibleExponent_mono h (by norm_num [half_13_11_φ1, half_13_11_φ2, half_13_11_φ3, half_13_11_φ4, half_13_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_14_11_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (46085800077/1000000000000 : ℝ)

private def half_14_11_φ2 : Fin 2 → ℝ := Fin.snoc half_14_11_φ1 (446939401453/10000000000000 : ℝ)

private def half_14_11_φ3 : Fin 3 → ℝ := Fin.snoc half_14_11_φ2 (213926762997/5000000000000 : ℝ)

private def half_14_11_φ4 : Fin 4 → ℝ := Fin.snoc half_14_11_φ3 (391205086293/10000000000000 : ℝ)

private def half_14_11_φ5 : Fin 5 → ℝ := Fin.snoc half_14_11_φ4 (137966597683/5000000000000 : ℝ)

private theorem half_14_11_hF2 : SourcePowerBound (paddedMoment 16 0 2 32 half_14_11_φ5) (3993724277779/500000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_14_11_φ5 (by norm_num [half_14_11_φ1, half_14_11_φ2, half_14_11_φ3, half_14_11_φ4, half_14_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_11_φ1, half_14_11_φ2, half_14_11_φ3, half_14_11_φ4, half_14_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_11_φ1, half_14_11_φ2, half_14_11_φ3, half_14_11_φ4, half_14_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_14_11_φ1, half_14_11_φ2, half_14_11_φ3, half_14_11_φ4, half_14_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_14_11_hx5 : SourcePowerBound (powerBoxCross 16 9 32 half_14_11_φ5) (52480155144239/5000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 16) (s := 9) (r := 2) (v := 12) (w := 12) (D := 32)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_14_11_φ5 (by norm_num [half_14_11_φ1, half_14_11_φ2, half_14_11_φ3, half_14_11_φ4, half_14_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_11_φ1, half_14_11_φ2, half_14_11_φ3, half_14_11_φ4, half_14_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_14_11_hF2 half_12_11 half_12_11
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_14_11_φ1, half_14_11_φ2, half_14_11_φ3, half_14_11_φ4, half_14_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_11_hx4 : SourcePowerBound (powerBoxCross 16 10 16 half_14_11_φ4) (57343265582687/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 4) (s := 10) (u := 8) (t := 11)
    (D := 16) (ψ := (137966597683/5000000000000 : ℝ)) half_14_11_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_11_φ1, half_14_11_φ2, half_14_11_φ3, half_14_11_φ4, half_14_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_11_φ1, half_14_11_φ2, half_14_11_φ3, half_14_11_φ4, half_14_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_11_φ1, half_14_11_φ2, half_14_11_φ3, half_14_11_φ4, half_14_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_11 half_11_11
    (by simpa only [half_14_11_φ5, show (2:ℝ)*16=32 by norm_num] using half_14_11_hx5)
  exact h.weaken (by norm_num [half_14_11_φ1, half_14_11_φ2, half_14_11_φ3, half_14_11_φ4, half_14_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_11_hx3 : SourcePowerBound (powerBoxCross 16 11 8 half_14_11_φ3) (12743020663467/1000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 11) (u := 9) (t := 12)
    (D := 8) (ψ := (391205086293/10000000000000 : ℝ)) half_14_11_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_11_φ1, half_14_11_φ2, half_14_11_φ3, half_14_11_φ4, half_14_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_11_φ1, half_14_11_φ2, half_14_11_φ3, half_14_11_φ4, half_14_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_11_φ1, half_14_11_φ2, half_14_11_φ3, half_14_11_φ4, half_14_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_11 half_12_11
    (by simpa only [half_14_11_φ4, show (2:ℝ)*8=16 by norm_num] using half_14_11_hx4)
  exact h.weaken (by norm_num [half_14_11_φ1, half_14_11_φ2, half_14_11_φ3, half_14_11_φ4, half_14_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_11_hx2 : SourcePowerBound (powerBoxCross 16 12 4 half_14_11_φ2) (14237259820241/1000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 12) (u := 10) (t := 13)
    (D := 4) (ψ := (213926762997/5000000000000 : ℝ)) half_14_11_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_11_φ1, half_14_11_φ2, half_14_11_φ3, half_14_11_φ4, half_14_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_11_φ1, half_14_11_φ2, half_14_11_φ3, half_14_11_φ4, half_14_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_11_φ1, half_14_11_φ2, half_14_11_φ3, half_14_11_φ4, half_14_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_11 half_13_11
    (by simpa only [half_14_11_φ3, show (2:ℝ)*4=8 by norm_num] using half_14_11_hx3)
  exact h.weaken (by norm_num [half_14_11_φ1, half_14_11_φ2, half_14_11_φ3, half_14_11_φ4, half_14_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_11_hx1 : SourcePowerBound (powerBoxCross 16 13 2 half_14_11_φ1) (4980796282979/312500000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 13) (u := 11) (t := 14)
    (D := 2) (ψ := (446939401453/10000000000000 : ℝ)) half_14_11_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_11_φ1, half_14_11_φ2, half_14_11_φ3, half_14_11_φ4, half_14_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_11_φ1, half_14_11_φ2, half_14_11_φ3, half_14_11_φ4, half_14_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_11_φ1, half_14_11_φ2, half_14_11_φ3, half_14_11_φ4, half_14_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_11 half_14_10
    (by simpa only [half_14_11_φ2, show (2:ℝ)*2=4 by norm_num] using half_14_11_hx2)
  exact h.weaken (by norm_num [half_14_11_φ1, half_14_11_φ2, half_14_11_φ3, half_14_11_φ4, half_14_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_11 : AdmissibleExponent 16 28 (85453465537289/5000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 12) (ψ := (46085800077/1000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_13_11
    (by simpa only [half_14_11_φ1] using half_14_11_hx1)
  exact admissibleExponent_mono h (by norm_num [half_14_11_φ1, half_14_11_φ2, half_14_11_φ3, half_14_11_φ4, half_14_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_9_12_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (79523194347/2000000000000 : ℝ)

private def half_9_12_φ2 : Fin 2 → ℝ := Fin.snoc half_9_12_φ1 (359291712099/10000000000000 : ℝ)

private def half_9_12_φ3 : Fin 3 → ℝ := Fin.snoc half_9_12_φ2 (199230371491/10000000000000 : ℝ)

private theorem half_9_12_hF2 : SourcePowerBound (paddedMoment 16 0 2 8 half_9_12_φ3) (535790300083/80000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_12_φ3 (by norm_num [half_9_12_φ1, half_9_12_φ2, half_9_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_12_φ1, half_9_12_φ2, half_9_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_12_φ1, half_9_12_φ2, half_9_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_12_φ1, half_9_12_φ2, half_9_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_9_12_hF1 : SourcePowerBound (paddedMoment 16 0 1 8 half_9_12_φ3) (205263433361/80000000000 : ℝ) := by
  have h := padded_second_power (k := 16) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_12_φ3 (by norm_num [half_9_12_φ1, half_9_12_φ2, half_9_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_12_φ1, half_9_12_φ2, half_9_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_12_φ1, half_9_12_φ2, half_9_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_12_φ1, half_9_12_φ2, half_9_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_9_12_hx3 : SourcePowerBound (powerBoxCross 16 6 8 half_9_12_φ3) (19048693619303/2500000000000 : ℝ) := by
  have h := full_B_cross_power (k := 16) (s := 6) (r := 1) (v := 2) (t := 9) (D := 8)
    (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
    (by norm_num) half_9_12_φ3 (by norm_num [half_9_12_φ1, half_9_12_φ2, half_9_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_12_φ1, half_9_12_φ2, half_9_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_9_12_hF1 half_9_12_hF2 half_9_11
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_9_12_φ1, half_9_12_φ2, half_9_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_12_hx2 : SourcePowerBound (powerBoxCross 16 7 4 half_9_12_φ2) (2103521633763/250000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 7) (u := 5) (t := 8)
    (D := 4) (ψ := (199230371491/10000000000000 : ℝ)) half_9_12_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_12_φ1, half_9_12_φ2, half_9_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_12_φ1, half_9_12_φ2, half_9_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_12_φ1, half_9_12_φ2, half_9_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_6 SeedCompletionEven16SecondSeeds.degree16_half_8
    (by simpa only [half_9_12_φ3, show (2:ℝ)*4=8 by norm_num] using half_9_12_hx3)
  exact h.weaken (by norm_num [half_9_12_φ1, half_9_12_φ2, half_9_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_12_hx1 : SourcePowerBound (powerBoxCross 16 8 2 half_9_12_φ1) (94804915207357/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 8) (u := 6) (t := 9)
    (D := 2) (ψ := (359291712099/10000000000000 : ℝ)) half_9_12_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_12_φ1, half_9_12_φ2, half_9_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_12_φ1, half_9_12_φ2, half_9_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_12_φ1, half_9_12_φ2, half_9_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_7 half_9_11
    (by simpa only [half_9_12_φ2, show (2:ℝ)*2=4 by norm_num] using half_9_12_hx2)
  exact h.weaken (by norm_num [half_9_12_φ1, half_9_12_φ2, half_9_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_12 : AdmissibleExponent 16 18 (50384577391691/5000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 7) (ψ := (79523194347/2000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8
    (by simpa only [half_9_12_φ1] using half_9_12_hx1)
  exact admissibleExponent_mono h (by norm_num [half_9_12_φ1, half_9_12_φ2, half_9_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_10_12_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (102563709/2500000000 : ℝ)

private def half_10_12_φ2 : Fin 2 → ℝ := Fin.snoc half_10_12_φ1 (382832364447/10000000000000 : ℝ)

private def half_10_12_φ3 : Fin 3 → ℝ := Fin.snoc half_10_12_φ2 (1803612309/62500000000 : ℝ)

private theorem half_10_12_hF2 : SourcePowerBound (paddedMoment 16 0 2 8 half_10_12_φ3) (12265013471017/2000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_10_12_φ3 (by norm_num [half_10_12_φ1, half_10_12_φ2, half_10_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_12_φ1, half_10_12_φ2, half_10_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_12_φ1, half_10_12_φ2, half_10_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_10_12_φ1, half_10_12_φ2, half_10_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_10_12_hx3 : SourcePowerBound (powerBoxCross 16 7 8 half_10_12_φ3) (85687553182721/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 16) (s := 7) (r := 2) (v := 9) (w := 10) (D := 8)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_10_12_φ3 (by norm_num [half_10_12_φ1, half_10_12_φ2, half_10_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_12_φ1, half_10_12_φ2, half_10_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_10_12_hF2 half_9_12 half_10_11
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_10_12_φ1, half_10_12_φ2, half_10_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_10_12_hx2 : SourcePowerBound (powerBoxCross 16 8 4 half_10_12_φ2) (95160020438131/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 8) (u := 6) (t := 9)
    (D := 4) (ψ := (1803612309/62500000000 : ℝ)) half_10_12_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_12_φ1, half_10_12_φ2, half_10_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_12_φ1, half_10_12_φ2, half_10_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_12_φ1, half_10_12_φ2, half_10_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_7 half_9_12
    (by simpa only [half_10_12_φ3, show (2:ℝ)*4=8 by norm_num] using half_10_12_hx3)
  exact h.weaken (by norm_num [half_10_12_φ1, half_10_12_φ2, half_10_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_10_12_hx1 : SourcePowerBound (powerBoxCross 16 9 2 half_10_12_φ1) (107045306312437/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 9) (u := 7) (t := 10)
    (D := 2) (ψ := (382832364447/10000000000000 : ℝ)) half_10_12_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_12_φ1, half_10_12_φ2, half_10_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_12_φ1, half_10_12_φ2, half_10_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_12_φ1, half_10_12_φ2, half_10_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8 half_10_11
    (by simpa only [half_10_12_φ2, show (2:ℝ)*2=4 by norm_num] using half_10_12_hx2)
  exact h.weaken (by norm_num [half_10_12_φ1, half_10_12_φ2, half_10_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_10_12 : AdmissibleExponent 16 20 (114019638524437/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 8) (ψ := (102563709/2500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_9_12
    (by simpa only [half_10_12_φ1] using half_10_12_hx1)
  exact admissibleExponent_mono h (by norm_num [half_10_12_φ1, half_10_12_φ2, half_10_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_11_12_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (424767221397/10000000000000 : ℝ)

private def half_11_12_φ2 : Fin 2 → ℝ := Fin.snoc half_11_12_φ1 (202441630413/5000000000000 : ℝ)

private def half_11_12_φ3 : Fin 3 → ℝ := Fin.snoc half_11_12_φ2 (288978901/8000000000 : ℝ)

private def half_11_12_φ4 : Fin 4 → ℝ := Fin.snoc half_11_12_φ3 (184040652373/10000000000000 : ℝ)

private theorem half_11_12_hF2 : SourcePowerBound (paddedMoment 16 0 2 16 half_11_12_φ4) (7812883576193/1000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_11_12_φ4 (by norm_num [half_11_12_φ1, half_11_12_φ2, half_11_12_φ3, half_11_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_12_φ1, half_11_12_φ2, half_11_12_φ3, half_11_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_12_φ1, half_11_12_φ2, half_11_12_φ3, half_11_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_11_12_φ1, half_11_12_φ2, half_11_12_φ3, half_11_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_11_12_hF1 : SourcePowerBound (paddedMoment 16 0 1 16 half_11_12_φ4) (2937627858731/1000000000000 : ℝ) := by
  have h := padded_second_power (k := 16) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_11_12_φ4 (by norm_num [half_11_12_φ1, half_11_12_φ2, half_11_12_φ3, half_11_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_12_φ1, half_11_12_φ2, half_11_12_φ3, half_11_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_12_φ1, half_11_12_φ2, half_11_12_φ3, half_11_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_11_12_φ1, half_11_12_φ2, half_11_12_φ3, half_11_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_11_12_hx4 : SourcePowerBound (powerBoxCross 16 7 16 half_11_12_φ4) (87403432095873/10000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 16) (s := 7) (r := 1) (v := 2) (t := 10) (D := 16)
    (a := (1/10 : ℝ)) (b := (1/5 : ℝ)) (c := (7/10 : ℝ))
    (by norm_num) half_11_12_φ4 (by norm_num [half_11_12_φ1, half_11_12_φ2, half_11_12_φ3, half_11_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_12_φ1, half_11_12_φ2, half_11_12_φ3, half_11_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_11_12_hF1 half_11_12_hF2 half_10_12
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_11_12_φ1, half_11_12_φ2, half_11_12_φ3, half_11_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_11_12_hx3 : SourcePowerBound (powerBoxCross 16 8 8 half_11_12_φ3) (95350832998293/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 8) (u := 6) (t := 9)
    (D := 8) (ψ := (184040652373/10000000000000 : ℝ)) half_11_12_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_12_φ1, half_11_12_φ2, half_11_12_φ3, half_11_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_12_φ1, half_11_12_φ2, half_11_12_φ3, half_11_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_12_φ1, half_11_12_φ2, half_11_12_φ3, half_11_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_7 half_9_12
    (by simpa only [half_11_12_φ4, show (2:ℝ)*8=16 by norm_num] using half_11_12_hx4)
  exact h.weaken (by norm_num [half_11_12_φ1, half_11_12_φ2, half_11_12_φ3, half_11_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_11_12_hx2 : SourcePowerBound (powerBoxCross 16 9 4 half_11_12_φ2) (106442211937333/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 9) (u := 7) (t := 10)
    (D := 4) (ψ := (288978901/8000000000 : ℝ)) half_11_12_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_12_φ1, half_11_12_φ2, half_11_12_φ3, half_11_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_12_φ1, half_11_12_φ2, half_11_12_φ3, half_11_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_12_φ1, half_11_12_φ2, half_11_12_φ3, half_11_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8 half_10_12
    (by simpa only [half_11_12_φ3, show (2:ℝ)*4=8 by norm_num] using half_11_12_hx3)
  exact h.weaken (by norm_num [half_11_12_φ1, half_11_12_φ2, half_11_12_φ3, half_11_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_11_12_hx1 : SourcePowerBound (powerBoxCross 16 10 2 half_11_12_φ1) (23920245048353/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 10) (u := 8) (t := 11)
    (D := 2) (ψ := (202441630413/5000000000000 : ℝ)) half_11_12_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_12_φ1, half_11_12_φ2, half_11_12_φ3, half_11_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_12_φ1, half_11_12_φ2, half_11_12_φ3, half_11_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_12_φ1, half_11_12_φ2, half_11_12_φ3, half_11_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_12 half_11_11
    (by simpa only [half_11_12_φ2, show (2:ℝ)*2=4 by norm_num] using half_11_12_hx2)
  exact h.weaken (by norm_num [half_11_12_φ1, half_11_12_φ2, half_11_12_φ3, half_11_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_11_12 : AdmissibleExponent 16 22 (31917950612077/2500000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 9) (ψ := (424767221397/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_10_12
    (by simpa only [half_11_12_φ1] using half_11_12_hx1)
  exact admissibleExponent_mono h (by norm_num [half_11_12_φ1, half_11_12_φ2, half_11_12_φ3, half_11_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_12_12_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (436527168761/10000000000000 : ℝ)

private def half_12_12_φ2 : Fin 2 → ℝ := Fin.snoc half_12_12_φ1 (83905859439/2000000000000 : ℝ)

private def half_12_12_φ3 : Fin 3 → ℝ := Fin.snoc half_12_12_φ2 (77183157919/2000000000000 : ℝ)

private def half_12_12_φ4 : Fin 4 → ℝ := Fin.snoc half_12_12_φ3 (279232581413/10000000000000 : ℝ)

private theorem half_12_12_hF2 : SourcePowerBound (paddedMoment 16 0 2 16 half_12_12_φ4) (3577289116831/500000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_12_12_φ4 (by norm_num [half_12_12_φ1, half_12_12_φ2, half_12_12_φ3, half_12_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_12_φ1, half_12_12_φ2, half_12_12_φ3, half_12_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_12_φ1, half_12_12_φ2, half_12_12_φ3, half_12_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_12_12_φ1, half_12_12_φ2, half_12_12_φ3, half_12_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_12_12_hx4 : SourcePowerBound (powerBoxCross 16 8 16 half_12_12_φ4) (48090163813599/5000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 16) (s := 8) (r := 2) (v := 10) (w := 11) (D := 16)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_12_12_φ4 (by norm_num [half_12_12_φ1, half_12_12_φ2, half_12_12_φ3, half_12_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_12_φ1, half_12_12_φ2, half_12_12_φ3, half_12_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_12_12_hF2 half_10_12 half_11_12
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_12_12_φ1, half_12_12_φ2, half_12_12_φ3, half_12_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_12_12_hx3 : SourcePowerBound (powerBoxCross 16 9 8 half_12_12_φ3) (52899487069009/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 9) (u := 7) (t := 10)
    (D := 8) (ψ := (279232581413/10000000000000 : ℝ)) half_12_12_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_12_φ1, half_12_12_φ2, half_12_12_φ3, half_12_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_12_φ1, half_12_12_φ2, half_12_12_φ3, half_12_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_12_φ1, half_12_12_φ2, half_12_12_φ3, half_12_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8 half_10_12
    (by simpa only [half_12_12_φ4, show (2:ℝ)*8=16 by norm_num] using half_12_12_hx4)
  exact h.weaken (by norm_num [half_12_12_φ1, half_12_12_φ2, half_12_12_φ3, half_12_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_12_12_hx2 : SourcePowerBound (powerBoxCross 16 10 4 half_12_12_φ2) (7383158463109/625000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 10) (u := 8) (t := 11)
    (D := 4) (ψ := (77183157919/2000000000000 : ℝ)) half_12_12_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_12_φ1, half_12_12_φ2, half_12_12_φ3, half_12_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_12_φ1, half_12_12_φ2, half_12_12_φ3, half_12_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_12_φ1, half_12_12_φ2, half_12_12_φ3, half_12_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_12 half_11_12
    (by simpa only [half_12_12_φ3, show (2:ℝ)*4=8 by norm_num] using half_12_12_hx3)
  exact h.weaken (by norm_num [half_12_12_φ1, half_12_12_φ2, half_12_12_φ3, half_12_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_12_12_hx1 : SourcePowerBound (powerBoxCross 16 11 2 half_12_12_φ1) (132535108571737/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 11) (u := 9) (t := 12)
    (D := 2) (ψ := (83905859439/2000000000000 : ℝ)) half_12_12_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_12_φ1, half_12_12_φ2, half_12_12_φ3, half_12_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_12_φ1, half_12_12_φ2, half_12_12_φ3, half_12_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_12_φ1, half_12_12_φ2, half_12_12_φ3, half_12_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_12 half_12_11
    (by simpa only [half_12_12_φ2, show (2:ℝ)*2=4 by norm_num] using half_12_12_hx2)
  exact h.weaken (by norm_num [half_12_12_φ1, half_12_12_φ2, half_12_12_φ3, half_12_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_12_12 : AdmissibleExponent 16 24 (70851089557859/5000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 10) (ψ := (436527168761/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_11_12
    (by simpa only [half_12_12_φ1] using half_12_12_hx1)
  exact admissibleExponent_mono h (by norm_num [half_12_12_φ1, half_12_12_φ2, half_12_12_φ3, half_12_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_13_12_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (89873703573/2000000000000 : ℝ)

private def half_13_12_φ2 : Fin 2 → ℝ := Fin.snoc half_13_12_φ1 (217172076257/5000000000000 : ℝ)

private def half_13_12_φ3 : Fin 3 → ℝ := Fin.snoc half_13_12_φ2 (413376172801/10000000000000 : ℝ)

private def half_13_12_φ4 : Fin 4 → ℝ := Fin.snoc half_13_12_φ3 (363300281263/10000000000000 : ℝ)

private def half_13_12_φ5 : Fin 5 → ℝ := Fin.snoc half_13_12_φ4 (7243296859/400000000000 : ℝ)

private theorem half_13_12_hF2 : SourcePowerBound (paddedMoment 16 0 2 32 half_13_12_φ5) (8713378043369/1000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_13_12_φ5 (by norm_num [half_13_12_φ1, half_13_12_φ2, half_13_12_φ3, half_13_12_φ4, half_13_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_12_φ1, half_13_12_φ2, half_13_12_φ3, half_13_12_φ4, half_13_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_12_φ1, half_13_12_φ2, half_13_12_φ3, half_13_12_φ4, half_13_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_13_12_φ1, half_13_12_φ2, half_13_12_φ3, half_13_12_φ4, half_13_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_13_12_hF1 : SourcePowerBound (paddedMoment 16 0 1 32 half_13_12_φ5) (3237792681123/1000000000000 : ℝ) := by
  have h := padded_second_power (k := 16) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_13_12_φ5 (by norm_num [half_13_12_φ1, half_13_12_φ2, half_13_12_φ3, half_13_12_φ4, half_13_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_12_φ1, half_13_12_φ2, half_13_12_φ3, half_13_12_φ4, half_13_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_12_φ1, half_13_12_φ2, half_13_12_φ3, half_13_12_φ4, half_13_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_13_12_φ1, half_13_12_φ2, half_13_12_φ3, half_13_12_φ4, half_13_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_13_12_hx5 : SourcePowerBound (powerBoxCross 16 8 32 half_13_12_φ5) (48495350947777/5000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 16) (s := 8) (r := 1) (v := 2) (t := 12) (D := 32)
    (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
    (by norm_num) half_13_12_φ5 (by norm_num [half_13_12_φ1, half_13_12_φ2, half_13_12_φ3, half_13_12_φ4, half_13_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_12_φ1, half_13_12_φ2, half_13_12_φ3, half_13_12_φ4, half_13_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_13_12_hF1 half_13_12_hF2 half_12_12
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_13_12_φ1, half_13_12_φ2, half_13_12_φ3, half_13_12_φ4, half_13_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_12_hx4 : SourcePowerBound (powerBoxCross 16 9 16 half_13_12_φ4) (20988904309759/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 4) (s := 9) (u := 7) (t := 10)
    (D := 16) (ψ := (7243296859/400000000000 : ℝ)) half_13_12_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_12_φ1, half_13_12_φ2, half_13_12_φ3, half_13_12_φ4, half_13_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_12_φ1, half_13_12_φ2, half_13_12_φ3, half_13_12_φ4, half_13_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_12_φ1, half_13_12_φ2, half_13_12_φ3, half_13_12_φ4, half_13_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8 half_10_12
    (by simpa only [half_13_12_φ5, show (2:ℝ)*16=32 by norm_num] using half_13_12_hx5)
  exact h.weaken (by norm_num [half_13_12_φ1, half_13_12_φ2, half_13_12_φ3, half_13_12_φ4, half_13_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_12_hx3 : SourcePowerBound (powerBoxCross 16 10 8 half_13_12_φ3) (58193982269109/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 10) (u := 8) (t := 11)
    (D := 8) (ψ := (363300281263/10000000000000 : ℝ)) half_13_12_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_12_φ1, half_13_12_φ2, half_13_12_φ3, half_13_12_φ4, half_13_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_12_φ1, half_13_12_φ2, half_13_12_φ3, half_13_12_φ4, half_13_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_12_φ1, half_13_12_φ2, half_13_12_φ3, half_13_12_φ4, half_13_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_12 half_11_12
    (by simpa only [half_13_12_φ4, show (2:ℝ)*8=16 by norm_num] using half_13_12_hx4)
  exact h.weaken (by norm_num [half_13_12_φ1, half_13_12_φ2, half_13_12_φ3, half_13_12_φ4, half_13_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_12_hx2 : SourcePowerBound (powerBoxCross 16 11 4 half_13_12_φ2) (32520774971373/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 11) (u := 9) (t := 12)
    (D := 4) (ψ := (413376172801/10000000000000 : ℝ)) half_13_12_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_12_φ1, half_13_12_φ2, half_13_12_φ3, half_13_12_φ4, half_13_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_12_φ1, half_13_12_φ2, half_13_12_φ3, half_13_12_φ4, half_13_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_12_φ1, half_13_12_φ2, half_13_12_φ3, half_13_12_φ4, half_13_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_12 half_12_12
    (by simpa only [half_13_12_φ3, show (2:ℝ)*4=8 by norm_num] using half_13_12_hx3)
  exact h.weaken (by norm_num [half_13_12_φ1, half_13_12_φ2, half_13_12_φ3, half_13_12_φ4, half_13_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_12_hx1 : SourcePowerBound (powerBoxCross 16 12 2 half_13_12_φ1) (2915677956257/200000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 12) (u := 10) (t := 13)
    (D := 2) (ψ := (217172076257/5000000000000 : ℝ)) half_13_12_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_12_φ1, half_13_12_φ2, half_13_12_φ3, half_13_12_φ4, half_13_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_12_φ1, half_13_12_φ2, half_13_12_φ3, half_13_12_φ4, half_13_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_12_φ1, half_13_12_φ2, half_13_12_φ3, half_13_12_φ4, half_13_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_12 half_13_11
    (by simpa only [half_13_12_φ2, show (2:ℝ)*2=4 by norm_num] using half_13_12_hx2)
  exact h.weaken (by norm_num [half_13_12_φ1, half_13_12_φ2, half_13_12_φ3, half_13_12_φ4, half_13_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_12 : AdmissibleExponent 16 26 (31223874744749/2000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 11) (ψ := (89873703573/2000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_12_12
    (by simpa only [half_13_12_φ1] using half_13_12_hx1)
  exact admissibleExponent_mono h (by norm_num [half_13_12_φ1, half_13_12_φ2, half_13_12_φ3, half_13_12_φ4, half_13_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_14_12_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (11520772861/250000000000 : ℝ)

private def half_14_12_φ2 : Fin 2 → ℝ := Fin.snoc half_14_12_φ1 (111734266841/2500000000000 : ℝ)

private def half_14_12_φ3 : Fin 3 → ℝ := Fin.snoc half_14_12_φ2 (13370381469/312500000000 : ℝ)

private def half_14_12_φ4 : Fin 4 → ℝ := Fin.snoc half_14_12_φ3 (78240488423/2000000000000 : ℝ)

private def half_14_12_φ5 : Fin 5 → ℝ := Fin.snoc half_14_12_φ4 (275922969383/10000000000000 : ℝ)

private theorem half_14_12_hF2 : SourcePowerBound (paddedMoment 16 0 2 32 half_14_12_φ5) (1597528959721/200000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_14_12_φ5 (by norm_num [half_14_12_φ1, half_14_12_φ2, half_14_12_φ3, half_14_12_φ4, half_14_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_12_φ1, half_14_12_φ2, half_14_12_φ3, half_14_12_φ4, half_14_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_12_φ1, half_14_12_φ2, half_14_12_φ3, half_14_12_φ4, half_14_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_14_12_φ1, half_14_12_φ2, half_14_12_φ3, half_14_12_φ4, half_14_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_14_12_hx5 : SourcePowerBound (powerBoxCross 16 9 32 half_14_12_φ5) (52480620074963/5000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 16) (s := 9) (r := 2) (v := 12) (w := 12) (D := 32)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_14_12_φ5 (by norm_num [half_14_12_φ1, half_14_12_φ2, half_14_12_φ3, half_14_12_φ4, half_14_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_12_φ1, half_14_12_φ2, half_14_12_φ3, half_14_12_φ4, half_14_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_14_12_hF2 half_12_12 half_12_12
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_14_12_φ1, half_14_12_φ2, half_14_12_φ3, half_14_12_φ4, half_14_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_12_hx4 : SourcePowerBound (powerBoxCross 16 10 16 half_14_12_φ4) (28671842229243/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 4) (s := 10) (u := 8) (t := 11)
    (D := 16) (ψ := (275922969383/10000000000000 : ℝ)) half_14_12_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_12_φ1, half_14_12_φ2, half_14_12_φ3, half_14_12_φ4, half_14_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_12_φ1, half_14_12_φ2, half_14_12_φ3, half_14_12_φ4, half_14_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_12_φ1, half_14_12_φ2, half_14_12_φ3, half_14_12_φ4, half_14_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_12 half_11_12
    (by simpa only [half_14_12_φ5, show (2:ℝ)*16=32 by norm_num] using half_14_12_hx5)
  exact h.weaken (by norm_num [half_14_12_φ1, half_14_12_φ2, half_14_12_φ3, half_14_12_φ4, half_14_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_12_hx3 : SourcePowerBound (powerBoxCross 16 11 8 half_14_12_φ3) (31857757809767/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 11) (u := 9) (t := 12)
    (D := 8) (ψ := (78240488423/2000000000000 : ℝ)) half_14_12_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_12_φ1, half_14_12_φ2, half_14_12_φ3, half_14_12_φ4, half_14_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_12_φ1, half_14_12_φ2, half_14_12_φ3, half_14_12_φ4, half_14_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_12_φ1, half_14_12_φ2, half_14_12_φ3, half_14_12_φ4, half_14_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_12 half_12_12
    (by simpa only [half_14_12_φ4, show (2:ℝ)*8=16 by norm_num] using half_14_12_hx4)
  exact h.weaken (by norm_num [half_14_12_φ1, half_14_12_φ2, half_14_12_φ3, half_14_12_φ4, half_14_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_12_hx2 : SourcePowerBound (powerBoxCross 16 12 4 half_14_12_φ2) (17796672793897/1250000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 12) (u := 10) (t := 13)
    (D := 4) (ψ := (13370381469/312500000000 : ℝ)) half_14_12_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_12_φ1, half_14_12_φ2, half_14_12_φ3, half_14_12_φ4, half_14_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_12_φ1, half_14_12_φ2, half_14_12_φ3, half_14_12_φ4, half_14_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_12_φ1, half_14_12_φ2, half_14_12_φ3, half_14_12_φ4, half_14_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_12 half_13_12
    (by simpa only [half_14_12_φ3, show (2:ℝ)*4=8 by norm_num] using half_14_12_hx3)
  exact h.weaken (by norm_num [half_14_12_φ1, half_14_12_φ2, half_14_12_φ3, half_14_12_φ4, half_14_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_12_hx1 : SourcePowerBound (powerBoxCross 16 13 2 half_14_12_φ1) (79692870631351/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 13) (u := 11) (t := 14)
    (D := 2) (ψ := (111734266841/2500000000000 : ℝ)) half_14_12_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_12_φ1, half_14_12_φ2, half_14_12_φ3, half_14_12_φ4, half_14_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_12_φ1, half_14_12_φ2, half_14_12_φ3, half_14_12_φ4, half_14_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_12_φ1, half_14_12_φ2, half_14_12_φ3, half_14_12_φ4, half_14_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_12 half_14_11
    (by simpa only [half_14_12_φ2, show (2:ℝ)*2=4 by norm_num] using half_14_12_hx2)
  exact h.weaken (by norm_num [half_14_12_φ1, half_14_12_φ2, half_14_12_φ3, half_14_12_φ4, half_14_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_12 : AdmissibleExponent 16 28 (85453257061851/5000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 12) (ψ := (11520772861/250000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_13_12
    (by simpa only [half_14_12_φ1] using half_14_12_hx1)
  exact admissibleExponent_mono h (by norm_num [half_14_12_φ1, half_14_12_φ2, half_14_12_φ3, half_14_12_φ4, half_14_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_9_13_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (99403991753/2500000000000 : ℝ)

private def half_9_13_φ2 : Fin 2 → ℝ := Fin.snoc half_9_13_φ1 (14371668411/400000000000 : ℝ)

private def half_9_13_φ3 : Fin 3 → ℝ := Fin.snoc half_9_13_φ2 (24903795141/1250000000000 : ℝ)

private theorem half_9_13_hF2 : SourcePowerBound (paddedMoment 16 0 2 8 half_9_13_φ3) (2678951530853/400000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_13_φ3 (by norm_num [half_9_13_φ1, half_9_13_φ2, half_9_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_13_φ1, half_9_13_φ2, half_9_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_13_φ1, half_9_13_φ2, half_9_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_13_φ1, half_9_13_φ2, half_9_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_9_13_hF1 : SourcePowerBound (paddedMoment 16 0 1 8 half_9_13_φ3) (1026317176951/400000000000 : ℝ) := by
  have h := padded_second_power (k := 16) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_13_φ3 (by norm_num [half_9_13_φ1, half_9_13_φ2, half_9_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_13_φ1, half_9_13_φ2, half_9_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_13_φ1, half_9_13_φ2, half_9_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_13_φ1, half_9_13_φ2, half_9_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_9_13_hx3 : SourcePowerBound (powerBoxCross 16 6 8 half_9_13_φ3) (19048693668071/2500000000000 : ℝ) := by
  have h := full_B_cross_power (k := 16) (s := 6) (r := 1) (v := 2) (t := 9) (D := 8)
    (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
    (by norm_num) half_9_13_φ3 (by norm_num [half_9_13_φ1, half_9_13_φ2, half_9_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_13_φ1, half_9_13_φ2, half_9_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_9_13_hF1 half_9_13_hF2 half_9_12
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_9_13_φ1, half_9_13_φ2, half_9_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_13_hx2 : SourcePowerBound (powerBoxCross 16 7 4 half_9_13_φ2) (84140865468937/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 7) (u := 5) (t := 8)
    (D := 4) (ψ := (24903795141/1250000000000 : ℝ)) half_9_13_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_13_φ1, half_9_13_φ2, half_9_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_13_φ1, half_9_13_φ2, half_9_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_13_φ1, half_9_13_φ2, half_9_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_6 SeedCompletionEven16SecondSeeds.degree16_half_8
    (by simpa only [half_9_13_φ3, show (2:ℝ)*4=8 by norm_num] using half_9_13_hx3)
  exact h.weaken (by norm_num [half_9_13_φ1, half_9_13_φ2, half_9_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_13_hx1 : SourcePowerBound (powerBoxCross 16 8 2 half_9_13_φ1) (94804915244149/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 8) (u := 6) (t := 9)
    (D := 2) (ψ := (14371668411/400000000000 : ℝ)) half_9_13_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_13_φ1, half_9_13_φ2, half_9_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_13_φ1, half_9_13_φ2, half_9_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_13_φ1, half_9_13_φ2, half_9_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_7 half_9_12
    (by simpa only [half_9_13_φ2, show (2:ℝ)*2=4 by norm_num] using half_9_13_hx2)
  exact h.weaken (by norm_num [half_9_13_φ1, half_9_13_φ2, half_9_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_13 : AdmissibleExponent 16 18 (100769154749329/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 7) (ψ := (99403991753/2500000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8
    (by simpa only [half_9_13_φ1] using half_9_13_hx1)
  exact admissibleExponent_mono h (by norm_num [half_9_13_φ1, half_9_13_φ2, half_9_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_10_13_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (51281848439/1250000000000 : ℝ)

private def half_10_13_φ2 : Fin 2 → ℝ := Fin.snoc half_10_13_φ1 (95708088587/2500000000000 : ℝ)

private def half_10_13_φ3 : Fin 3 → ℝ := Fin.snoc half_10_13_φ2 (72144480961/2500000000000 : ℝ)

private theorem half_10_13_hF2 : SourcePowerBound (paddedMoment 16 0 2 8 half_10_13_φ3) (1533126801083/250000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_10_13_φ3 (by norm_num [half_10_13_φ1, half_10_13_φ2, half_10_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_13_φ1, half_10_13_φ2, half_10_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_13_φ1, half_10_13_φ2, half_10_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_10_13_φ1, half_10_13_φ2, half_10_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_10_13_hx3 : SourcePowerBound (powerBoxCross 16 7 8 half_10_13_φ3) (85687554802059/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 16) (s := 7) (r := 2) (v := 9) (w := 10) (D := 8)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_10_13_φ3 (by norm_num [half_10_13_φ1, half_10_13_φ2, half_10_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_13_φ1, half_10_13_φ2, half_10_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_10_13_hF2 half_9_13 half_10_12
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_10_13_φ1, half_10_13_φ2, half_10_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_10_13_hx2 : SourcePowerBound (powerBoxCross 16 8 4 half_10_13_φ2) (47580010835171/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 8) (u := 6) (t := 9)
    (D := 4) (ψ := (72144480961/2500000000000 : ℝ)) half_10_13_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_13_φ1, half_10_13_φ2, half_10_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_13_φ1, half_10_13_φ2, half_10_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_13_φ1, half_10_13_φ2, half_10_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_7 half_9_13
    (by simpa only [half_10_13_φ3, show (2:ℝ)*4=8 by norm_num] using half_10_13_hx3)
  exact h.weaken (by norm_num [half_10_13_φ1, half_10_13_φ2, half_10_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_10_13_hx1 : SourcePowerBound (powerBoxCross 16 9 2 half_10_13_φ1) (26761326679977/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 9) (u := 7) (t := 10)
    (D := 2) (ψ := (95708088587/2500000000000 : ℝ)) half_10_13_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_13_φ1, half_10_13_φ2, half_10_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_13_φ1, half_10_13_φ2, half_10_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_13_φ1, half_10_13_φ2, half_10_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8 half_10_12
    (by simpa only [half_10_13_φ2, show (2:ℝ)*2=4 by norm_num] using half_10_13_hx2)
  exact h.weaken (by norm_num [half_10_13_φ1, half_10_13_φ2, half_10_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_10_13 : AdmissibleExponent 16 20 (28504909526903/2500000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 8) (ψ := (51281848439/1250000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_9_13
    (by simpa only [half_10_13_φ1] using half_10_13_hx1)
  exact admissibleExponent_mono h (by norm_num [half_10_13_φ1, half_10_13_φ2, half_10_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_11_13_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (212383485601/5000000000000 : ℝ)

private def half_11_13_φ2 : Fin 2 → ℝ := Fin.snoc half_11_13_φ1 (404883245577/10000000000000 : ℝ)

private def half_11_13_φ3 : Fin 3 → ℝ := Fin.snoc half_11_13_φ2 (45152950189/1250000000000 : ℝ)

private def half_11_13_φ4 : Fin 4 → ℝ := Fin.snoc half_11_13_φ3 (46010133119/2500000000000 : ℝ)

private theorem half_11_13_hF2 : SourcePowerBound (paddedMoment 16 0 2 16 half_11_13_φ4) (15625770843097/2000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_11_13_φ4 (by norm_num [half_11_13_φ1, half_11_13_φ2, half_11_13_φ3, half_11_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_13_φ1, half_11_13_φ2, half_11_13_φ3, half_11_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_13_φ1, half_11_13_φ2, half_11_13_φ3, half_11_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_11_13_φ1, half_11_13_φ2, half_11_13_φ3, half_11_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_11_13_hF1 : SourcePowerBound (paddedMoment 16 0 1 16 half_11_13_φ4) (5875256947699/2000000000000 : ℝ) := by
  have h := padded_second_power (k := 16) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_11_13_φ4 (by norm_num [half_11_13_φ1, half_11_13_φ2, half_11_13_φ3, half_11_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_13_φ1, half_11_13_φ2, half_11_13_φ3, half_11_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_13_φ1, half_11_13_φ2, half_11_13_φ3, half_11_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_11_13_φ1, half_11_13_φ2, half_11_13_φ3, half_11_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_11_13_hx4 : SourcePowerBound (powerBoxCross 16 7 16 half_11_13_φ4) (21850859855759/2500000000000 : ℝ) := by
  have h := full_B_cross_power (k := 16) (s := 7) (r := 1) (v := 2) (t := 10) (D := 16)
    (a := (1/10 : ℝ)) (b := (1/5 : ℝ)) (c := (7/10 : ℝ))
    (by norm_num) half_11_13_φ4 (by norm_num [half_11_13_φ1, half_11_13_φ2, half_11_13_φ3, half_11_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_13_φ1, half_11_13_φ2, half_11_13_φ3, half_11_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_11_13_hF1 half_11_13_hF2 half_10_13
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_11_13_φ1, half_11_13_φ2, half_11_13_φ3, half_11_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_11_13_hx3 : SourcePowerBound (powerBoxCross 16 8 8 half_11_13_φ3) (47675419752991/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 8) (u := 6) (t := 9)
    (D := 8) (ψ := (46010133119/2500000000000 : ℝ)) half_11_13_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_13_φ1, half_11_13_φ2, half_11_13_φ3, half_11_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_13_φ1, half_11_13_φ2, half_11_13_φ3, half_11_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_13_φ1, half_11_13_φ2, half_11_13_φ3, half_11_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_7 half_9_13
    (by simpa only [half_11_13_φ4, show (2:ℝ)*8=16 by norm_num] using half_11_13_hx4)
  exact h.weaken (by norm_num [half_11_13_φ1, half_11_13_φ2, half_11_13_φ3, half_11_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_11_13_hx2 : SourcePowerBound (powerBoxCross 16 9 4 half_11_13_φ2) (106442218318643/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 9) (u := 7) (t := 10)
    (D := 4) (ψ := (45152950189/1250000000000 : ℝ)) half_11_13_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_13_φ1, half_11_13_φ2, half_11_13_φ3, half_11_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_13_φ1, half_11_13_φ2, half_11_13_φ3, half_11_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_13_φ1, half_11_13_φ2, half_11_13_φ3, half_11_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8 half_10_13
    (by simpa only [half_11_13_φ3, show (2:ℝ)*4=8 by norm_num] using half_11_13_hx3)
  exact h.weaken (by norm_num [half_11_13_φ1, half_11_13_φ2, half_11_13_φ3, half_11_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_11_13_hx1 : SourcePowerBound (powerBoxCross 16 10 2 half_11_13_φ1) (29900306861293/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 10) (u := 8) (t := 11)
    (D := 2) (ψ := (404883245577/10000000000000 : ℝ)) half_11_13_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_13_φ1, half_11_13_φ2, half_11_13_φ3, half_11_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_13_φ1, half_11_13_φ2, half_11_13_φ3, half_11_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_13_φ1, half_11_13_φ2, half_11_13_φ3, half_11_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_13 half_11_12
    (by simpa only [half_11_13_φ2, show (2:ℝ)*2=4 by norm_num] using half_11_13_hx2)
  exact h.weaken (by norm_num [half_11_13_φ1, half_11_13_φ2, half_11_13_φ3, half_11_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_11_13 : AdmissibleExponent 16 22 (12767179989801/1000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 9) (ψ := (212383485601/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_10_13
    (by simpa only [half_11_13_φ1] using half_11_13_hx1)
  exact admissibleExponent_mono h (by norm_num [half_11_13_φ1, half_11_13_φ2, half_11_13_φ3, half_11_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_12_13_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (27282880261/625000000000 : ℝ)

private def half_12_13_φ2 : Fin 2 → ℝ := Fin.snoc half_12_13_φ1 (419529223209/10000000000000 : ℝ)

private def half_12_13_φ3 : Fin 3 → ℝ := Fin.snoc half_12_13_φ2 (192957843393/5000000000000 : ℝ)

private def half_12_13_φ4 : Fin 4 → ℝ := Fin.snoc half_12_13_φ3 (69808040187/2500000000000 : ℝ)

private theorem half_12_13_hF2 : SourcePowerBound (paddedMoment 16 0 2 16 half_12_13_φ4) (14309171605729/2000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_12_13_φ4 (by norm_num [half_12_13_φ1, half_12_13_φ2, half_12_13_φ3, half_12_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_13_φ1, half_12_13_φ2, half_12_13_φ3, half_12_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_13_φ1, half_12_13_φ2, half_12_13_φ3, half_12_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_12_13_φ1, half_12_13_φ2, half_12_13_φ3, half_12_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_12_13_hx4 : SourcePowerBound (powerBoxCross 16 8 16 half_12_13_φ4) (96180360912817/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 16) (s := 8) (r := 2) (v := 10) (w := 11) (D := 16)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_12_13_φ4 (by norm_num [half_12_13_φ1, half_12_13_φ2, half_12_13_φ3, half_12_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_13_φ1, half_12_13_φ2, half_12_13_φ3, half_12_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_12_13_hF2 half_10_13 half_11_13
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_12_13_φ1, half_12_13_φ2, half_12_13_φ3, half_12_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_12_13_hx3 : SourcePowerBound (powerBoxCross 16 9 8 half_12_13_φ3) (52899502047383/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 9) (u := 7) (t := 10)
    (D := 8) (ψ := (69808040187/2500000000000 : ℝ)) half_12_13_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_13_φ1, half_12_13_φ2, half_12_13_φ3, half_12_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_13_φ1, half_12_13_φ2, half_12_13_φ3, half_12_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_13_φ1, half_12_13_φ2, half_12_13_φ3, half_12_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8 half_10_13
    (by simpa only [half_12_13_φ4, show (2:ℝ)*8=16 by norm_num] using half_12_13_hx4)
  exact h.weaken (by norm_num [half_12_13_φ1, half_12_13_φ2, half_12_13_φ3, half_12_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_12_13_hx2 : SourcePowerBound (powerBoxCross 16 10 4 half_12_13_φ2) (59065282216689/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 10) (u := 8) (t := 11)
    (D := 4) (ψ := (192957843393/5000000000000 : ℝ)) half_12_13_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_13_φ1, half_12_13_φ2, half_12_13_φ3, half_12_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_13_φ1, half_12_13_φ2, half_12_13_φ3, half_12_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_13_φ1, half_12_13_φ2, half_12_13_φ3, half_12_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_13 half_11_13
    (by simpa only [half_12_13_φ3, show (2:ℝ)*4=8 by norm_num] using half_12_13_hx3)
  exact h.weaken (by norm_num [half_12_13_φ1, half_12_13_φ2, half_12_13_φ3, half_12_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_12_13_hx1 : SourcePowerBound (powerBoxCross 16 11 2 half_12_13_φ1) (33133779723821/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 11) (u := 9) (t := 12)
    (D := 2) (ψ := (419529223209/10000000000000 : ℝ)) half_12_13_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_13_φ1, half_12_13_φ2, half_12_13_φ3, half_12_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_13_φ1, half_12_13_φ2, half_12_13_φ3, half_12_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_13_φ1, half_12_13_φ2, half_12_13_φ3, half_12_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_13 half_12_12
    (by simpa only [half_12_13_φ2, show (2:ℝ)*2=4 by norm_num] using half_12_13_hx2)
  exact h.weaken (by norm_num [half_12_13_φ1, half_12_13_φ2, half_12_13_φ3, half_12_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_12_13 : AdmissibleExponent 16 24 (7085108333149/500000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 10) (ψ := (27282880261/625000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_11_13
    (by simpa only [half_12_13_φ1] using half_12_13_hx1)
  exact admissibleExponent_mono h (by norm_num [half_12_13_φ1, half_12_13_φ2, half_12_13_φ3, half_12_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_13_13_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (449364875421/10000000000000 : ℝ)

private def half_13_13_φ2 : Fin 2 → ℝ := Fin.snoc half_13_13_φ1 (108585972579/2500000000000 : ℝ)

private def half_13_13_φ3 : Fin 3 → ℝ := Fin.snoc half_13_13_φ2 (12918000047/312500000000 : ℝ)

private def half_13_13_φ4 : Fin 4 → ℝ := Fin.snoc half_13_13_φ3 (45412470113/1250000000000 : ℝ)

private def half_13_13_φ5 : Fin 5 → ℝ := Fin.snoc half_13_13_φ4 (36216025553/2000000000000 : ℝ)

private theorem half_13_13_hF2 : SourcePowerBound (paddedMoment 16 0 2 32 half_13_13_φ5) (1742681809681/200000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_13_13_φ5 (by norm_num [half_13_13_φ1, half_13_13_φ2, half_13_13_φ3, half_13_13_φ4, half_13_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_13_φ1, half_13_13_φ2, half_13_13_φ3, half_13_13_φ4, half_13_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_13_φ1, half_13_13_φ2, half_13_13_φ3, half_13_13_φ4, half_13_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_13_13_φ1, half_13_13_φ2, half_13_13_φ3, half_13_13_φ4, half_13_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_13_13_hF1 : SourcePowerBound (paddedMoment 16 0 1 32 half_13_13_φ5) (647560603227/200000000000 : ℝ) := by
  have h := padded_second_power (k := 16) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_13_13_φ5 (by norm_num [half_13_13_φ1, half_13_13_φ2, half_13_13_φ3, half_13_13_φ4, half_13_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_13_φ1, half_13_13_φ2, half_13_13_φ3, half_13_13_φ4, half_13_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_13_φ1, half_13_13_φ2, half_13_13_φ3, half_13_13_φ4, half_13_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_13_13_φ1, half_13_13_φ2, half_13_13_φ3, half_13_13_φ4, half_13_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_13_13_hx5 : SourcePowerBound (powerBoxCross 16 8 32 half_13_13_φ5) (96990829111171/10000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 16) (s := 8) (r := 1) (v := 2) (t := 12) (D := 32)
    (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
    (by norm_num) half_13_13_φ5 (by norm_num [half_13_13_φ1, half_13_13_φ2, half_13_13_φ3, half_13_13_φ4, half_13_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_13_φ1, half_13_13_φ2, half_13_13_φ3, half_13_13_φ4, half_13_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_13_13_hF1 half_13_13_hF2 half_12_13
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_13_13_φ1, half_13_13_φ2, half_13_13_φ3, half_13_13_φ4, half_13_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_13_hx4 : SourcePowerBound (powerBoxCross 16 9 16 half_13_13_φ4) (52472314227807/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 4) (s := 9) (u := 7) (t := 10)
    (D := 16) (ψ := (36216025553/2000000000000 : ℝ)) half_13_13_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_13_φ1, half_13_13_φ2, half_13_13_φ3, half_13_13_φ4, half_13_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_13_φ1, half_13_13_φ2, half_13_13_φ3, half_13_13_φ4, half_13_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_13_φ1, half_13_13_φ2, half_13_13_φ3, half_13_13_φ4, half_13_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8 half_10_13
    (by simpa only [half_13_13_φ5, show (2:ℝ)*16=32 by norm_num] using half_13_13_hx5)
  exact h.weaken (by norm_num [half_13_13_φ1, half_13_13_φ2, half_13_13_φ3, half_13_13_φ4, half_13_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_13_hx3 : SourcePowerBound (powerBoxCross 16 10 8 half_13_13_φ3) (29097017261873/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 10) (u := 8) (t := 11)
    (D := 8) (ψ := (45412470113/1250000000000 : ℝ)) half_13_13_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_13_φ1, half_13_13_φ2, half_13_13_φ3, half_13_13_φ4, half_13_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_13_φ1, half_13_13_φ2, half_13_13_φ3, half_13_13_φ4, half_13_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_13_φ1, half_13_13_φ2, half_13_13_φ3, half_13_13_φ4, half_13_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_13 half_11_13
    (by simpa only [half_13_13_φ4, show (2:ℝ)*8=16 by norm_num] using half_13_13_hx4)
  exact h.weaken (by norm_num [half_13_13_φ1, half_13_13_φ2, half_13_13_φ3, half_13_13_φ4, half_13_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_13_hx2 : SourcePowerBound (powerBoxCross 16 11 4 half_13_13_φ2) (130083201786297/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 11) (u := 9) (t := 12)
    (D := 4) (ψ := (12918000047/312500000000 : ℝ)) half_13_13_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_13_φ1, half_13_13_φ2, half_13_13_φ3, half_13_13_φ4, half_13_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_13_φ1, half_13_13_φ2, half_13_13_φ3, half_13_13_φ4, half_13_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_13_φ1, half_13_13_φ2, half_13_13_φ3, half_13_13_φ4, half_13_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_13 half_12_13
    (by simpa only [half_13_13_φ3, show (2:ℝ)*4=8 by norm_num] using half_13_13_hx3)
  exact h.weaken (by norm_num [half_13_13_φ1, half_13_13_φ2, half_13_13_φ3, half_13_13_φ4, half_13_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_13_hx1 : SourcePowerBound (powerBoxCross 16 12 2 half_13_13_φ1) (145783933891473/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 12) (u := 10) (t := 13)
    (D := 2) (ψ := (108585972579/2500000000000 : ℝ)) half_13_13_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_13_φ1, half_13_13_φ2, half_13_13_φ3, half_13_13_φ4, half_13_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_13_φ1, half_13_13_φ2, half_13_13_φ3, half_13_13_φ4, half_13_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_13_φ1, half_13_13_φ2, half_13_13_φ3, half_13_13_φ4, half_13_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_13 half_13_12
    (by simpa only [half_13_13_φ2, show (2:ℝ)*2=4 by norm_num] using half_13_13_hx2)
  exact h.weaken (by norm_num [half_13_13_φ1, half_13_13_φ2, half_13_13_φ3, half_13_13_φ4, half_13_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_13 : AdmissibleExponent 16 26 (39029831506539/2500000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 11) (ψ := (449364875421/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_12_13
    (by simpa only [half_13_13_φ1] using half_13_13_hx1)
  exact admissibleExponent_mono h (by norm_num [half_13_13_φ1, half_13_13_φ2, half_13_13_φ3, half_13_13_φ4, half_13_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_14_13_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (460820730983/10000000000000 : ℝ)

private def half_14_13_φ2 : Fin 2 → ℝ := Fin.snoc half_14_13_φ1 (27933514651/625000000000 : ℝ)

private def half_14_13_φ3 : Fin 3 → ℝ := Fin.snoc half_14_13_φ2 (213925878891/5000000000000 : ℝ)

private def half_14_13_φ4 : Fin 4 → ℝ := Fin.snoc half_14_13_φ3 (97800375189/2500000000000 : ℝ)

private def half_14_13_φ5 : Fin 5 → ℝ := Fin.snoc half_14_13_φ4 (275919287181/10000000000000 : ℝ)

private theorem half_14_13_hF2 : SourcePowerBound (paddedMoment 16 0 2 32 half_14_13_φ5) (7987717199969/1000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_14_13_φ5 (by norm_num [half_14_13_φ1, half_14_13_φ2, half_14_13_φ3, half_14_13_φ4, half_14_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_13_φ1, half_14_13_φ2, half_14_13_φ3, half_14_13_φ4, half_14_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_13_φ1, half_14_13_φ2, half_14_13_φ3, half_14_13_φ4, half_14_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_14_13_φ1, half_14_13_φ2, half_14_13_φ3, half_14_13_φ4, half_14_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_14_13_hx5 : SourcePowerBound (powerBoxCross 16 9 32 half_14_13_φ5) (2624039616869/250000000000 : ℝ) := by
  have h := full_A_cross_power (k := 16) (s := 9) (r := 2) (v := 12) (w := 12) (D := 32)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_14_13_φ5 (by norm_num [half_14_13_φ1, half_14_13_φ2, half_14_13_φ3, half_14_13_φ4, half_14_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_13_φ1, half_14_13_φ2, half_14_13_φ3, half_14_13_φ4, half_14_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_14_13_hF2 half_12_13 half_12_13
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_14_13_φ1, half_14_13_φ2, half_14_13_φ3, half_14_13_φ4, half_14_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_13_hx4 : SourcePowerBound (powerBoxCross 16 10 16 half_14_13_φ4) (114687681079283/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 4) (s := 10) (u := 8) (t := 11)
    (D := 16) (ψ := (275919287181/10000000000000 : ℝ)) half_14_13_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_13_φ1, half_14_13_φ2, half_14_13_φ3, half_14_13_φ4, half_14_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_13_φ1, half_14_13_φ2, half_14_13_φ3, half_14_13_φ4, half_14_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_13_φ1, half_14_13_φ2, half_14_13_φ3, half_14_13_φ4, half_14_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_13 half_11_13
    (by simpa only [half_14_13_φ5, show (2:ℝ)*16=32 by norm_num] using half_14_13_hx5)
  exact h.weaken (by norm_num [half_14_13_φ1, half_14_13_φ2, half_14_13_φ3, half_14_13_φ4, half_14_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_13_hx3 : SourcePowerBound (powerBoxCross 16 11 8 half_14_13_φ3) (6371567010501/500000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 11) (u := 9) (t := 12)
    (D := 8) (ψ := (97800375189/2500000000000 : ℝ)) half_14_13_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_13_φ1, half_14_13_φ2, half_14_13_φ3, half_14_13_φ4, half_14_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_13_φ1, half_14_13_φ2, half_14_13_φ3, half_14_13_φ4, half_14_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_13_φ1, half_14_13_φ2, half_14_13_φ3, half_14_13_φ4, half_14_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_13 half_12_13
    (by simpa only [half_14_13_φ4, show (2:ℝ)*8=16 by norm_num] using half_14_13_hx4)
  exact h.weaken (by norm_num [half_14_13_φ1, half_14_13_φ2, half_14_13_φ3, half_14_13_φ4, half_14_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_13_hx2 : SourcePowerBound (powerBoxCross 16 12 4 half_14_13_φ2) (1138989432421/80000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 12) (u := 10) (t := 13)
    (D := 4) (ψ := (213925878891/5000000000000 : ℝ)) half_14_13_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_13_φ1, half_14_13_φ2, half_14_13_φ3, half_14_13_φ4, half_14_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_13_φ1, half_14_13_φ2, half_14_13_φ3, half_14_13_φ4, half_14_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_13_φ1, half_14_13_φ2, half_14_13_φ3, half_14_13_φ4, half_14_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_13 half_13_13
    (by simpa only [half_14_13_φ3, show (2:ℝ)*4=8 by norm_num] using half_14_13_hx3)
  exact h.weaken (by norm_num [half_14_13_φ1, half_14_13_φ2, half_14_13_φ3, half_14_13_φ4, half_14_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_13_hx1 : SourcePowerBound (powerBoxCross 16 13 2 half_14_13_φ1) (159385844563163/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 13) (u := 11) (t := 14)
    (D := 2) (ψ := (27933514651/625000000000 : ℝ)) half_14_13_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_13_φ1, half_14_13_φ2, half_14_13_φ3, half_14_13_φ4, half_14_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_13_φ1, half_14_13_φ2, half_14_13_φ3, half_14_13_φ4, half_14_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_13_φ1, half_14_13_φ2, half_14_13_φ3, half_14_13_φ4, half_14_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_13 half_14_12
    (by simpa only [half_14_13_φ2, show (2:ℝ)*2=4 by norm_num] using half_14_13_hx2)
  exact h.weaken (by norm_num [half_14_13_φ1, half_14_13_φ2, half_14_13_φ3, half_14_13_φ4, half_14_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_13 : AdmissibleExponent 16 28 (85453181418869/5000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 12) (ψ := (460820730983/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_13_13
    (by simpa only [half_14_13_φ1] using half_14_13_hx1)
  exact admissibleExponent_mono h (by norm_num [half_14_13_φ1, half_14_13_φ2, half_14_13_φ3, half_14_13_φ4, half_14_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_9_14_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (79523193181/2000000000000 : ℝ)

private def half_9_14_φ2 : Fin 2 → ℝ := Fin.snoc half_9_14_φ1 (44911463731/1250000000000 : ℝ)

private def half_9_14_φ3 : Fin 3 → ℝ := Fin.snoc half_9_14_φ2 (1992303587/100000000000 : ℝ)

private theorem half_9_14_hF2 : SourcePowerBound (paddedMoment 16 0 2 8 half_9_14_φ3) (13394757689923/2000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_14_φ3 (by norm_num [half_9_14_φ1, half_9_14_φ2, half_9_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_14_φ1, half_9_14_φ2, half_9_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_14_φ1, half_9_14_φ2, half_9_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_14_φ1, half_9_14_φ2, half_9_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_9_14_hF1 : SourcePowerBound (paddedMoment 16 0 1 8 half_9_14_φ3) (5131585896641/2000000000000 : ℝ) := by
  have h := padded_second_power (k := 16) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_14_φ3 (by norm_num [half_9_14_φ1, half_9_14_φ2, half_9_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_14_φ1, half_9_14_φ2, half_9_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_14_φ1, half_9_14_φ2, half_9_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_14_φ1, half_9_14_φ2, half_9_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_9_14_hx3 : SourcePowerBound (powerBoxCross 16 6 8 half_9_14_φ3) (76194774717989/10000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 16) (s := 6) (r := 1) (v := 2) (t := 9) (D := 8)
    (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
    (by norm_num) half_9_14_φ3 (by norm_num [half_9_14_φ1, half_9_14_φ2, half_9_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_14_φ1, half_9_14_φ2, half_9_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_9_14_hF1 half_9_14_hF2 half_9_13
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_9_14_φ1, half_9_14_φ2, half_9_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_14_hx2 : SourcePowerBound (powerBoxCross 16 7 4 half_9_14_φ2) (84140865496683/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 7) (u := 5) (t := 8)
    (D := 4) (ψ := (1992303587/100000000000 : ℝ)) half_9_14_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_14_φ1, half_9_14_φ2, half_9_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_14_φ1, half_9_14_φ2, half_9_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_14_φ1, half_9_14_φ2, half_9_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_6 SeedCompletionEven16SecondSeeds.degree16_half_8
    (by simpa only [half_9_14_φ3, show (2:ℝ)*4=8 by norm_num] using half_9_14_hx3)
  exact h.weaken (by norm_num [half_9_14_φ1, half_9_14_φ2, half_9_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_14_hx1 : SourcePowerBound (powerBoxCross 16 8 2 half_9_14_φ1) (94804915252777/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 8) (u := 6) (t := 9)
    (D := 2) (ψ := (44911463731/1250000000000 : ℝ)) half_9_14_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_14_φ1, half_9_14_φ2, half_9_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_14_φ1, half_9_14_φ2, half_9_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_14_φ1, half_9_14_φ2, half_9_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_7 half_9_13
    (by simpa only [half_9_14_φ2, show (2:ℝ)*2=4 by norm_num] using half_9_14_hx2)
  exact h.weaken (by norm_num [half_9_14_φ1, half_9_14_φ2, half_9_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_14 : AdmissibleExponent 16 18 (12596144342669/1250000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 7) (ψ := (79523193181/2000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8
    (by simpa only [half_9_14_φ1] using half_9_14_hx1)
  exact admissibleExponent_mono h (by norm_num [half_9_14_φ1, half_9_14_φ2, half_9_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_10_14_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (102563693733/2500000000000 : ℝ)

private def half_10_14_φ2 : Fin 2 → ℝ := Fin.snoc half_10_14_φ1 (191416175883/5000000000000 : ℝ)

private def half_10_14_φ3 : Fin 3 → ℝ := Fin.snoc half_10_14_φ2 (3607223901/125000000000 : ℝ)

private theorem half_10_14_hF2 : SourcePowerBound (paddedMoment 16 0 2 8 half_10_14_φ3) (6132507325499/1000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_10_14_φ3 (by norm_num [half_10_14_φ1, half_10_14_φ2, half_10_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_14_φ1, half_10_14_φ2, half_10_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_14_φ1, half_10_14_φ2, half_10_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_10_14_φ1, half_10_14_φ2, half_10_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_10_14_hx3 : SourcePowerBound (powerBoxCross 16 7 8 half_10_14_φ3) (42843777610451/5000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 16) (s := 7) (r := 2) (v := 9) (w := 10) (D := 8)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_10_14_φ3 (by norm_num [half_10_14_φ1, half_10_14_φ2, half_10_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_14_φ1, half_10_14_φ2, half_10_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_10_14_hF2 half_9_14 half_10_13
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_10_14_φ1, half_10_14_φ2, half_10_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_10_14_hx2 : SourcePowerBound (powerBoxCross 16 8 4 half_10_14_φ2) (95160021989733/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 8) (u := 6) (t := 9)
    (D := 4) (ψ := (3607223901/125000000000 : ℝ)) half_10_14_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_14_φ1, half_10_14_φ2, half_10_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_14_φ1, half_10_14_φ2, half_10_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_14_φ1, half_10_14_φ2, half_10_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_7 half_9_14
    (by simpa only [half_10_14_φ3, show (2:ℝ)*4=8 by norm_num] using half_10_14_hx3)
  exact h.weaken (by norm_num [half_10_14_φ1, half_10_14_φ2, half_10_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_10_14_hx1 : SourcePowerBound (powerBoxCross 16 9 2 half_10_14_φ1) (21409061365289/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 9) (u := 7) (t := 10)
    (D := 2) (ψ := (191416175883/5000000000000 : ℝ)) half_10_14_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_14_φ1, half_10_14_φ2, half_10_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_14_φ1, half_10_14_φ2, half_10_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_14_φ1, half_10_14_φ2, half_10_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8 half_10_13
    (by simpa only [half_10_14_φ2, show (2:ℝ)*2=4 by norm_num] using half_10_14_hx2)
  exact h.weaken (by norm_num [half_10_14_φ1, half_10_14_φ2, half_10_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_10_14 : AdmissibleExponent 16 20 (114019638000289/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 8) (ψ := (102563693733/2500000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_9_14
    (by simpa only [half_10_14_φ1] using half_10_14_hx1)
  exact admissibleExponent_mono h (by norm_num [half_10_14_φ1, half_10_14_φ2, half_10_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_11_14_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (212383450083/5000000000000 : ℝ)

private def half_11_14_φ2 : Fin 2 → ℝ := Fin.snoc half_11_14_φ1 (404883241509/10000000000000 : ℝ)

private def half_11_14_φ3 : Fin 3 → ℝ := Fin.snoc half_11_14_φ2 (361223594677/10000000000000 : ℝ)

private def half_11_14_φ4 : Fin 4 → ℝ := Fin.snoc half_11_14_φ3 (36808099829/2000000000000 : ℝ)

private theorem half_11_14_hF2 : SourcePowerBound (paddedMoment 16 0 2 16 half_11_14_φ4) (15625771880527/2000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_11_14_φ4 (by norm_num [half_11_14_φ1, half_11_14_φ2, half_11_14_φ3, half_11_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_14_φ1, half_11_14_φ2, half_11_14_φ3, half_11_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_14_φ1, half_11_14_φ2, half_11_14_φ3, half_11_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_11_14_φ1, half_11_14_φ2, half_11_14_φ3, half_11_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_11_14_hF1 : SourcePowerBound (paddedMoment 16 0 1 16 half_11_14_φ4) (5875257293509/2000000000000 : ℝ) := by
  have h := padded_second_power (k := 16) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_11_14_φ4 (by norm_num [half_11_14_φ1, half_11_14_φ2, half_11_14_φ3, half_11_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_14_φ1, half_11_14_φ2, half_11_14_φ3, half_11_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_14_φ1, half_11_14_φ2, half_11_14_φ3, half_11_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_11_14_φ1, half_11_14_φ2, half_11_14_φ3, half_11_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_11_14_hx4 : SourcePowerBound (powerBoxCross 16 7 16 half_11_14_φ4) (87403441488587/10000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 16) (s := 7) (r := 1) (v := 2) (t := 10) (D := 16)
    (a := (1/10 : ℝ)) (b := (1/5 : ℝ)) (c := (7/10 : ℝ))
    (by norm_num) half_11_14_φ4 (by norm_num [half_11_14_φ1, half_11_14_φ2, half_11_14_φ3, half_11_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_14_φ1, half_11_14_φ2, half_11_14_φ3, half_11_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_11_14_hF1 half_11_14_hF2 half_10_14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_11_14_φ1, half_11_14_φ2, half_11_14_φ3, half_11_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_11_14_hx3 : SourcePowerBound (powerBoxCross 16 8 8 half_11_14_φ3) (4767542067299/500000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 8) (u := 6) (t := 9)
    (D := 8) (ψ := (36808099829/2000000000000 : ℝ)) half_11_14_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_14_φ1, half_11_14_φ2, half_11_14_φ3, half_11_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_14_φ1, half_11_14_φ2, half_11_14_φ3, half_11_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_14_φ1, half_11_14_φ2, half_11_14_φ3, half_11_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_7 half_9_14
    (by simpa only [half_11_14_φ4, show (2:ℝ)*8=16 by norm_num] using half_11_14_hx4)
  exact h.weaken (by norm_num [half_11_14_φ1, half_11_14_φ2, half_11_14_φ3, half_11_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_11_14_hx2 : SourcePowerBound (powerBoxCross 16 9 4 half_11_14_φ2) (6652638758101/625000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 9) (u := 7) (t := 10)
    (D := 4) (ψ := (361223594677/10000000000000 : ℝ)) half_11_14_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_14_φ1, half_11_14_φ2, half_11_14_φ3, half_11_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_14_φ1, half_11_14_φ2, half_11_14_φ3, half_11_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_14_φ1, half_11_14_φ2, half_11_14_φ3, half_11_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8 half_10_14
    (by simpa only [half_11_14_φ3, show (2:ℝ)*4=8 by norm_num] using half_11_14_hx3)
  exact h.weaken (by norm_num [half_11_14_φ1, half_11_14_φ2, half_11_14_φ3, half_11_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_11_14_hx1 : SourcePowerBound (powerBoxCross 16 10 2 half_11_14_φ1) (11960122808133/1000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 10) (u := 8) (t := 11)
    (D := 2) (ψ := (404883241509/10000000000000 : ℝ)) half_11_14_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_14_φ1, half_11_14_φ2, half_11_14_φ3, half_11_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_14_φ1, half_11_14_φ2, half_11_14_φ3, half_11_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_14_φ1, half_11_14_φ2, half_11_14_φ3, half_11_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_14 half_11_13
    (by simpa only [half_11_14_φ2, show (2:ℝ)*2=4 by norm_num] using half_11_14_hx2)
  exact h.weaken (by norm_num [half_11_14_φ1, half_11_14_φ2, half_11_14_φ3, half_11_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_11_14 : AdmissibleExponent 16 22 (31917949796121/2500000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 9) (ψ := (212383450083/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_10_14
    (by simpa only [half_11_14_φ1] using half_11_14_hx1)
  exact admissibleExponent_mono h (by norm_num [half_11_14_φ1, half_11_14_φ2, half_11_14_φ3, half_11_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_12_14_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (218262873093/5000000000000 : ℝ)

private def half_12_14_φ2 : Fin 2 → ℝ := Fin.snoc half_12_14_φ1 (419529201583/10000000000000 : ℝ)

private def half_12_14_φ3 : Fin 3 → ℝ := Fin.snoc half_12_14_φ2 (96478914019/2500000000000 : ℝ)

private def half_12_14_φ4 : Fin 4 → ℝ := Fin.snoc half_12_14_φ3 (34904004183/1250000000000 : ℝ)

private theorem half_12_14_hF2 : SourcePowerBound (paddedMoment 16 0 2 16 half_12_14_φ4) (14309176264219/2000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_12_14_φ4 (by norm_num [half_12_14_φ1, half_12_14_φ2, half_12_14_φ3, half_12_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_14_φ1, half_12_14_φ2, half_12_14_φ3, half_12_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_14_φ1, half_12_14_φ2, half_12_14_φ3, half_12_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_12_14_φ1, half_12_14_φ2, half_12_14_φ3, half_12_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_12_14_hx4 : SourcePowerBound (powerBoxCross 16 8 16 half_12_14_φ4) (96180371190341/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 16) (s := 8) (r := 2) (v := 10) (w := 11) (D := 16)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_12_14_φ4 (by norm_num [half_12_14_φ1, half_12_14_φ2, half_12_14_φ3, half_12_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_14_φ1, half_12_14_φ2, half_12_14_φ3, half_12_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_12_14_hF2 half_10_14 half_11_14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_12_14_φ1, half_12_14_φ2, half_12_14_φ3, half_12_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_12_14_hx3 : SourcePowerBound (powerBoxCross 16 9 8 half_12_14_φ3) (26449753346147/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 9) (u := 7) (t := 10)
    (D := 8) (ψ := (34904004183/1250000000000 : ℝ)) half_12_14_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_14_φ1, half_12_14_φ2, half_12_14_φ3, half_12_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_14_φ1, half_12_14_φ2, half_12_14_φ3, half_12_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_14_φ1, half_12_14_φ2, half_12_14_φ3, half_12_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8 half_10_14
    (by simpa only [half_12_14_φ4, show (2:ℝ)*8=16 by norm_num] using half_12_14_hx4)
  exact h.weaken (by norm_num [half_12_14_φ1, half_12_14_φ2, half_12_14_φ3, half_12_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_12_14_hx2 : SourcePowerBound (powerBoxCross 16 10 4 half_12_14_φ2) (118130573483793/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 10) (u := 8) (t := 11)
    (D := 4) (ψ := (96478914019/2500000000000 : ℝ)) half_12_14_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_14_φ1, half_12_14_φ2, half_12_14_φ3, half_12_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_14_φ1, half_12_14_φ2, half_12_14_φ3, half_12_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_14_φ1, half_12_14_φ2, half_12_14_φ3, half_12_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_14 half_11_14
    (by simpa only [half_12_14_φ3, show (2:ℝ)*4=8 by norm_num] using half_12_14_hx3)
  exact h.weaken (by norm_num [half_12_14_φ1, half_12_14_φ2, half_12_14_φ3, half_12_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_12_14_hx1 : SourcePowerBound (powerBoxCross 16 11 2 half_12_14_φ1) (66267561095047/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 11) (u := 9) (t := 12)
    (D := 2) (ψ := (419529201583/10000000000000 : ℝ)) half_12_14_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_14_φ1, half_12_14_φ2, half_12_14_φ3, half_12_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_14_φ1, half_12_14_φ2, half_12_14_φ3, half_12_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_14_φ1, half_12_14_φ2, half_12_14_φ3, half_12_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_14 half_12_13
    (by simpa only [half_12_14_φ2, show (2:ℝ)*2=4 by norm_num] using half_12_14_hx2)
  exact h.weaken (by norm_num [half_12_14_φ1, half_12_14_φ2, half_12_14_φ3, half_12_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_12_14 : AdmissibleExponent 16 24 (7085108143/500000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 10) (ψ := (218262873093/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_11_14
    (by simpa only [half_12_14_φ1] using half_12_14_hx1)
  exact admissibleExponent_mono h (by norm_num [half_12_14_φ1, half_12_14_φ2, half_12_14_φ3, half_12_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_13_14_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (224681817951/5000000000000 : ℝ)

private def half_13_14_φ2 : Fin 2 → ℝ := Fin.snoc half_13_14_φ1 (434343806699/10000000000000 : ℝ)

private def half_13_14_φ3 : Fin 3 → ℝ := Fin.snoc half_13_14_φ2 (206687973627/5000000000000 : ℝ)

private def half_13_14_φ4 : Fin 4 → ℝ := Fin.snoc half_13_14_φ3 (181649795227/5000000000000 : ℝ)

private def half_13_14_φ5 : Fin 5 → ℝ := Fin.snoc half_13_14_φ4 (90539686783/5000000000000 : ℝ)

private theorem half_13_14_hF2 : SourcePowerBound (paddedMoment 16 0 2 32 half_13_14_φ5) (139414710521/16000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_13_14_φ5 (by norm_num [half_13_14_φ1, half_13_14_φ2, half_13_14_φ3, half_13_14_φ4, half_13_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_14_φ1, half_13_14_φ2, half_13_14_φ3, half_13_14_φ4, half_13_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_14_φ1, half_13_14_φ2, half_13_14_φ3, half_13_14_φ4, half_13_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_13_14_φ1, half_13_14_φ2, half_13_14_φ3, half_13_14_φ4, half_13_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_13_14_hF1 : SourcePowerBound (paddedMoment 16 0 1 32 half_13_14_φ5) (51804903507/16000000000 : ℝ) := by
  have h := padded_second_power (k := 16) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_13_14_φ5 (by norm_num [half_13_14_φ1, half_13_14_φ2, half_13_14_φ3, half_13_14_φ4, half_13_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_14_φ1, half_13_14_φ2, half_13_14_φ3, half_13_14_φ4, half_13_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_14_φ1, half_13_14_φ2, half_13_14_φ3, half_13_14_φ4, half_13_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_13_14_φ1, half_13_14_φ2, half_13_14_φ3, half_13_14_φ4, half_13_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_13_14_hx5 : SourcePowerBound (powerBoxCross 16 8 32 half_13_14_φ5) (2424771795249/250000000000 : ℝ) := by
  have h := full_B_cross_power (k := 16) (s := 8) (r := 1) (v := 2) (t := 12) (D := 32)
    (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
    (by norm_num) half_13_14_φ5 (by norm_num [half_13_14_φ1, half_13_14_φ2, half_13_14_φ3, half_13_14_φ4, half_13_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_14_φ1, half_13_14_φ2, half_13_14_φ3, half_13_14_φ4, half_13_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_13_14_hF1 half_13_14_hF2 half_12_14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_13_14_φ1, half_13_14_φ2, half_13_14_φ3, half_13_14_φ4, half_13_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_14_hx4 : SourcePowerBound (powerBoxCross 16 9 16 half_13_14_φ4) (104944664536721/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 4) (s := 9) (u := 7) (t := 10)
    (D := 16) (ψ := (90539686783/5000000000000 : ℝ)) half_13_14_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_14_φ1, half_13_14_φ2, half_13_14_φ3, half_13_14_φ4, half_13_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_14_φ1, half_13_14_φ2, half_13_14_φ3, half_13_14_φ4, half_13_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_14_φ1, half_13_14_φ2, half_13_14_φ3, half_13_14_φ4, half_13_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8 half_10_14
    (by simpa only [half_13_14_φ5, show (2:ℝ)*16=32 by norm_num] using half_13_14_hx5)
  exact h.weaken (by norm_num [half_13_14_φ1, half_13_14_φ2, half_13_14_φ3, half_13_14_φ4, half_13_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_14_hx3 : SourcePowerBound (powerBoxCross 16 10 8 half_13_14_φ3) (23277620890359/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 10) (u := 8) (t := 11)
    (D := 8) (ψ := (181649795227/5000000000000 : ℝ)) half_13_14_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_14_φ1, half_13_14_φ2, half_13_14_φ3, half_13_14_φ4, half_13_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_14_φ1, half_13_14_φ2, half_13_14_φ3, half_13_14_φ4, half_13_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_14_φ1, half_13_14_φ2, half_13_14_φ3, half_13_14_φ4, half_13_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_14 half_11_14
    (by simpa only [half_13_14_φ4, show (2:ℝ)*8=16 by norm_num] using half_13_14_hx4)
  exact h.weaken (by norm_num [half_13_14_φ1, half_13_14_φ2, half_13_14_φ3, half_13_14_φ4, half_13_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_14_hx2 : SourcePowerBound (powerBoxCross 16 11 4 half_13_14_φ2) (130083236537701/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 11) (u := 9) (t := 12)
    (D := 4) (ψ := (206687973627/5000000000000 : ℝ)) half_13_14_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_14_φ1, half_13_14_φ2, half_13_14_φ3, half_13_14_φ4, half_13_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_14_φ1, half_13_14_φ2, half_13_14_φ3, half_13_14_φ4, half_13_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_14_φ1, half_13_14_φ2, half_13_14_φ3, half_13_14_φ4, half_13_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_14 half_12_14
    (by simpa only [half_13_14_φ3, show (2:ℝ)*4=8 by norm_num] using half_13_14_hx3)
  exact h.weaken (by norm_num [half_13_14_φ1, half_13_14_φ2, half_13_14_φ3, half_13_14_φ4, half_13_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_14_hx1 : SourcePowerBound (powerBoxCross 16 12 2 half_13_14_φ1) (145783946584119/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 12) (u := 10) (t := 13)
    (D := 2) (ψ := (434343806699/10000000000000 : ℝ)) half_13_14_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_14_φ1, half_13_14_φ2, half_13_14_φ3, half_13_14_φ4, half_13_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_14_φ1, half_13_14_φ2, half_13_14_φ3, half_13_14_φ4, half_13_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_14_φ1, half_13_14_φ2, half_13_14_φ3, half_13_14_φ4, half_13_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_14 half_13_13
    (by simpa only [half_13_14_φ2, show (2:ℝ)*2=4 by norm_num] using half_13_14_hx2)
  exact h.weaken (by norm_num [half_13_14_φ1, half_13_14_φ2, half_13_14_φ3, half_13_14_φ4, half_13_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_14 : AdmissibleExponent 16 26 (31223862041973/2000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 11) (ψ := (224681817951/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_12_14
    (by simpa only [half_13_14_φ1] using half_13_14_hx1)
  exact admissibleExponent_mono h (by norm_num [half_13_14_φ1, half_13_14_φ2, half_13_14_φ3, half_13_14_φ4, half_13_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_14_14_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (460816970911/10000000000000 : ℝ)

private def half_14_14_φ2 : Fin 2 → ℝ := Fin.snoc half_14_14_φ1 (111733985761/2500000000000 : ℝ)

private def half_14_14_φ3 : Fin 3 → ℝ := Fin.snoc half_14_14_φ2 (427851606433/10000000000000 : ℝ)

private def half_14_14_φ4 : Fin 4 → ℝ := Fin.snoc half_14_14_φ3 (12225036523/312500000000 : ℝ)

private def half_14_14_φ5 : Fin 5 → ℝ := Fin.snoc half_14_14_φ4 (275917976113/10000000000000 : ℝ)

private theorem half_14_14_hF2 : SourcePowerBound (paddedMoment 16 0 2 32 half_14_14_φ5) (15975487012867/2000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_14_14_φ5 (by norm_num [half_14_14_φ1, half_14_14_φ2, half_14_14_φ3, half_14_14_φ4, half_14_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_14_φ1, half_14_14_φ2, half_14_14_φ3, half_14_14_φ4, half_14_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_14_φ1, half_14_14_φ2, half_14_14_φ3, half_14_14_φ4, half_14_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_14_14_φ1, half_14_14_φ2, half_14_14_φ3, half_14_14_φ4, half_14_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_14_14_hx5 : SourcePowerBound (powerBoxCross 16 9 32 half_14_14_φ5) (2624042757199/250000000000 : ℝ) := by
  have h := full_A_cross_power (k := 16) (s := 9) (r := 2) (v := 12) (w := 12) (D := 32)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_14_14_φ5 (by norm_num [half_14_14_φ1, half_14_14_φ2, half_14_14_φ3, half_14_14_φ4, half_14_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_14_φ1, half_14_14_φ2, half_14_14_φ3, half_14_14_φ4, half_14_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_14_14_hF2 half_12_14 half_12_14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_14_14_φ1, half_14_14_φ2, half_14_14_φ3, half_14_14_φ4, half_14_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_14_hx4 : SourcePowerBound (powerBoxCross 16 10 16 half_14_14_φ4) (114687795406131/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 4) (s := 10) (u := 8) (t := 11)
    (D := 16) (ψ := (275917976113/10000000000000 : ℝ)) half_14_14_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_14_φ1, half_14_14_φ2, half_14_14_φ3, half_14_14_φ4, half_14_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_14_φ1, half_14_14_φ2, half_14_14_φ3, half_14_14_φ4, half_14_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_14_φ1, half_14_14_φ2, half_14_14_φ3, half_14_14_φ4, half_14_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_14 half_11_14
    (by simpa only [half_14_14_φ5, show (2:ℝ)*16=32 by norm_num] using half_14_14_hx5)
  exact h.weaken (by norm_num [half_14_14_φ1, half_14_14_φ2, half_14_14_φ3, half_14_14_φ4, half_14_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_14_hx3 : SourcePowerBound (powerBoxCross 16 11 8 half_14_14_φ3) (127431453869919/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 11) (u := 9) (t := 12)
    (D := 8) (ψ := (12225036523/312500000000 : ℝ)) half_14_14_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_14_φ1, half_14_14_φ2, half_14_14_φ3, half_14_14_φ4, half_14_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_14_φ1, half_14_14_φ2, half_14_14_φ3, half_14_14_φ4, half_14_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_14_φ1, half_14_14_φ2, half_14_14_φ3, half_14_14_φ4, half_14_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_14 half_12_14
    (by simpa only [half_14_14_φ4, show (2:ℝ)*8=16 by norm_num] using half_14_14_hx4)
  exact h.weaken (by norm_num [half_14_14_φ1, half_14_14_φ2, half_14_14_φ3, half_14_14_φ4, half_14_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_14_hx2 : SourcePowerBound (powerBoxCross 16 12 4 half_14_14_φ2) (71186894557197/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 12) (u := 10) (t := 13)
    (D := 4) (ψ := (427851606433/10000000000000 : ℝ)) half_14_14_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_14_φ1, half_14_14_φ2, half_14_14_φ3, half_14_14_φ4, half_14_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_14_φ1, half_14_14_φ2, half_14_14_φ3, half_14_14_φ4, half_14_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_14_φ1, half_14_14_φ2, half_14_14_φ3, half_14_14_φ4, half_14_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_14 half_13_14
    (by simpa only [half_14_14_φ3, show (2:ℝ)*4=8 by norm_num] using half_14_14_hx3)
  exact h.weaken (by norm_num [half_14_14_φ1, half_14_14_φ2, half_14_14_φ3, half_14_14_φ4, half_14_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_14_hx1 : SourcePowerBound (powerBoxCross 16 13 2 half_14_14_φ1) (1275087075341/80000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 13) (u := 11) (t := 14)
    (D := 2) (ψ := (111733985761/2500000000000 : ℝ)) half_14_14_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_14_φ1, half_14_14_φ2, half_14_14_φ3, half_14_14_φ4, half_14_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_14_φ1, half_14_14_φ2, half_14_14_φ3, half_14_14_φ4, half_14_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_14_φ1, half_14_14_φ2, half_14_14_φ3, half_14_14_φ4, half_14_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_14 half_14_13
    (by simpa only [half_14_14_φ2, show (2:ℝ)*2=4 by norm_num] using half_14_14_hx2)
  exact h.weaken (by norm_num [half_14_14_φ1, half_14_14_φ2, half_14_14_φ3, half_14_14_φ4, half_14_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_14 : AdmissibleExponent 16 28 (213632885863/12500000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 12) (ψ := (460816970911/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_13_14
    (by simpa only [half_14_14_φ1] using half_14_14_hx1)
  exact admissibleExponent_mono h (by norm_num [half_14_14_φ1, half_14_14_φ2, half_14_14_φ3, half_14_14_φ4, half_14_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_9_15_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (198807982823/5000000000000 : ℝ)

private def half_9_15_φ2 : Fin 2 → ℝ := Fin.snoc half_9_15_φ1 (359291709747/10000000000000 : ℝ)

private def half_9_15_φ3 : Fin 3 → ℝ := Fin.snoc half_9_15_φ2 (199230358131/10000000000000 : ℝ)

private theorem half_9_15_hF2 : SourcePowerBound (paddedMoment 16 0 2 8 half_9_15_φ3) (3348689424571/500000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_15_φ3 (by norm_num [half_9_15_φ1, half_9_15_φ2, half_9_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_15_φ1, half_9_15_φ2, half_9_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_15_φ1, half_9_15_φ2, half_9_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_15_φ1, half_9_15_φ2, half_9_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_9_15_hF1 : SourcePowerBound (paddedMoment 16 0 1 8 half_9_15_φ3) (1282896474857/500000000000 : ℝ) := by
  have h := padded_second_power (k := 16) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_15_φ3 (by norm_num [half_9_15_φ1, half_9_15_φ2, half_9_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_15_φ1, half_9_15_φ2, half_9_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_15_φ1, half_9_15_φ2, half_9_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_15_φ1, half_9_15_φ2, half_9_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_9_15_hx3 : SourcePowerBound (powerBoxCross 16 6 8 half_9_15_φ3) (7619477472871/1000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 16) (s := 6) (r := 1) (v := 2) (t := 9) (D := 8)
    (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
    (by norm_num) half_9_15_φ3 (by norm_num [half_9_15_φ1, half_9_15_φ2, half_9_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_15_φ1, half_9_15_φ2, half_9_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_9_15_hF1 half_9_15_hF2 half_9_14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_9_15_φ1, half_9_15_φ2, half_9_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_15_hx2 : SourcePowerBound (powerBoxCross 16 7 4 half_9_15_φ2) (84140865503197/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 7) (u := 5) (t := 8)
    (D := 4) (ψ := (199230358131/10000000000000 : ℝ)) half_9_15_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_15_φ1, half_9_15_φ2, half_9_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_15_φ1, half_9_15_φ2, half_9_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_15_φ1, half_9_15_φ2, half_9_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_6 SeedCompletionEven16SecondSeeds.degree16_half_8
    (by simpa only [half_9_15_φ3, show (2:ℝ)*4=8 by norm_num] using half_9_15_hx3)
  exact h.weaken (by norm_num [half_9_15_φ1, half_9_15_φ2, half_9_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_15_hx1 : SourcePowerBound (powerBoxCross 16 8 2 half_9_15_φ1) (18960983050959/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 8) (u := 6) (t := 9)
    (D := 2) (ψ := (359291709747/10000000000000 : ℝ)) half_9_15_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_15_φ1, half_9_15_φ2, half_9_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_15_φ1, half_9_15_φ2, half_9_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_15_φ1, half_9_15_φ2, half_9_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_7 half_9_14
    (by simpa only [half_9_15_φ2, show (2:ℝ)*2=4 by norm_num] using half_9_15_hx2)
  exact h.weaken (by norm_num [half_9_15_φ1, half_9_15_φ2, half_9_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_15 : AdmissibleExponent 16 18 (20153830947897/2000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 7) (ψ := (198807982823/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8
    (by simpa only [half_9_15_φ1] using half_9_15_hx1)
  exact admissibleExponent_mono h (by norm_num [half_9_15_φ1, half_9_15_φ2, half_9_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_10_15_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (410254771683/10000000000000 : ℝ)

private def half_10_15_φ2 : Fin 2 → ℝ := Fin.snoc half_10_15_φ1 (382832351107/10000000000000 : ℝ)

private def half_10_15_φ3 : Fin 3 → ℝ := Fin.snoc half_10_15_φ2 (4509029829/156250000000 : ℝ)

private theorem half_10_15_hF2 : SourcePowerBound (paddedMoment 16 0 2 8 half_10_15_φ3) (6132507356693/1000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_10_15_φ3 (by norm_num [half_10_15_φ1, half_10_15_φ2, half_10_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_15_φ1, half_10_15_φ2, half_10_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_15_φ1, half_10_15_φ2, half_10_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_10_15_φ1, half_10_15_φ2, half_10_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_10_15_hx3 : SourcePowerBound (powerBoxCross 16 7 8 half_10_15_φ3) (21421888832203/2500000000000 : ℝ) := by
  have h := full_A_cross_power (k := 16) (s := 7) (r := 2) (v := 9) (w := 10) (D := 8)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_10_15_φ3 (by norm_num [half_10_15_φ1, half_10_15_φ2, half_10_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_15_φ1, half_10_15_φ2, half_10_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_10_15_hF2 half_9_15 half_10_14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_10_15_φ1, half_10_15_φ2, half_10_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_10_15_hx2 : SourcePowerBound (powerBoxCross 16 8 4 half_10_15_φ2) (23790005518043/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 8) (u := 6) (t := 9)
    (D := 4) (ψ := (4509029829/156250000000 : ℝ)) half_10_15_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_15_φ1, half_10_15_φ2, half_10_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_15_φ1, half_10_15_φ2, half_10_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_15_φ1, half_10_15_φ2, half_10_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_7 half_9_15
    (by simpa only [half_10_15_φ3, show (2:ℝ)*4=8 by norm_num] using half_10_15_hx3)
  exact h.weaken (by norm_num [half_10_15_φ1, half_10_15_φ2, half_10_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_10_15_hx1 : SourcePowerBound (powerBoxCross 16 9 2 half_10_15_φ1) (13380663356769/1250000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 9) (u := 7) (t := 10)
    (D := 2) (ψ := (382832351107/10000000000000 : ℝ)) half_10_15_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_15_φ1, half_10_15_φ2, half_10_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_15_φ1, half_10_15_φ2, half_10_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_15_φ1, half_10_15_φ2, half_10_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8 half_10_14
    (by simpa only [half_10_15_φ2, show (2:ℝ)*2=4 by norm_num] using half_10_15_hx2)
  exact h.weaken (by norm_num [half_10_15_φ1, half_10_15_φ2, half_10_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_10_15 : AdmissibleExponent 16 20 (114019637972763/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 8) (ψ := (410254771683/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_9_15
    (by simpa only [half_10_15_φ1] using half_10_15_hx1)
  exact admissibleExponent_mono h (by norm_num [half_10_15_φ1, half_10_15_φ2, half_10_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_11_15_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (424766880167/10000000000000 : ℝ)

private def half_11_15_φ2 : Fin 2 → ℝ := Fin.snoc half_11_15_φ1 (404883240429/10000000000000 : ℝ)

private def half_11_15_φ3 : Fin 3 → ℝ := Fin.snoc half_11_15_φ2 (361223592799/10000000000000 : ℝ)

private def half_11_15_φ4 : Fin 4 → ℝ := Fin.snoc half_11_15_φ3 (36808097987/2000000000000 : ℝ)

private theorem half_11_15_hF2 : SourcePowerBound (paddedMoment 16 0 2 16 half_11_15_φ4) (1562577217003/200000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_11_15_φ4 (by norm_num [half_11_15_φ1, half_11_15_φ2, half_11_15_φ3, half_11_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_15_φ1, half_11_15_φ2, half_11_15_φ3, half_11_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_15_φ1, half_11_15_φ2, half_11_15_φ3, half_11_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_11_15_φ1, half_11_15_φ2, half_11_15_φ3, half_11_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_11_15_hF1 : SourcePowerBound (paddedMoment 16 0 1 16 half_11_15_φ4) (587525739001/200000000000 : ℝ) := by
  have h := padded_second_power (k := 16) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_11_15_φ4 (by norm_num [half_11_15_φ1, half_11_15_φ2, half_11_15_φ3, half_11_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_15_φ1, half_11_15_φ2, half_11_15_φ3, half_11_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_15_φ1, half_11_15_φ2, half_11_15_φ3, half_11_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_11_15_φ1, half_11_15_φ2, half_11_15_φ3, half_11_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_11_15_hx4 : SourcePowerBound (powerBoxCross 16 7 16 half_11_15_φ4) (87403442066459/10000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 16) (s := 7) (r := 1) (v := 2) (t := 10) (D := 16)
    (a := (1/10 : ℝ)) (b := (1/5 : ℝ)) (c := (7/10 : ℝ))
    (by norm_num) half_11_15_φ4 (by norm_num [half_11_15_φ1, half_11_15_φ2, half_11_15_φ3, half_11_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_15_φ1, half_11_15_φ2, half_11_15_φ3, half_11_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_11_15_hF1 half_11_15_hF2 half_10_15
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_11_15_φ1, half_11_15_φ2, half_11_15_φ3, half_11_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_11_15_hx3 : SourcePowerBound (powerBoxCross 16 8 8 half_11_15_φ3) (95350841862073/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 8) (u := 6) (t := 9)
    (D := 8) (ψ := (36808097987/2000000000000 : ℝ)) half_11_15_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_15_φ1, half_11_15_φ2, half_11_15_φ3, half_11_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_15_φ1, half_11_15_φ2, half_11_15_φ3, half_11_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_15_φ1, half_11_15_φ2, half_11_15_φ3, half_11_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_7 half_9_15
    (by simpa only [half_11_15_φ4, show (2:ℝ)*8=16 by norm_num] using half_11_15_hx4)
  exact h.weaken (by norm_num [half_11_15_φ1, half_11_15_φ2, half_11_15_φ3, half_11_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_11_15_hx2 : SourcePowerBound (powerBoxCross 16 9 4 half_11_15_φ2) (5322111031961/500000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 9) (u := 7) (t := 10)
    (D := 4) (ψ := (361223592799/10000000000000 : ℝ)) half_11_15_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_15_φ1, half_11_15_φ2, half_11_15_φ3, half_11_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_15_φ1, half_11_15_φ2, half_11_15_φ3, half_11_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_15_φ1, half_11_15_φ2, half_11_15_φ3, half_11_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8 half_10_15
    (by simpa only [half_11_15_φ3, show (2:ℝ)*4=8 by norm_num] using half_11_15_hx3)
  exact h.weaken (by norm_num [half_11_15_φ1, half_11_15_φ2, half_11_15_φ3, half_11_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_11_15_hx1 : SourcePowerBound (powerBoxCross 16 10 2 half_11_15_φ1) (119601228263001/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 10) (u := 8) (t := 11)
    (D := 2) (ψ := (404883240429/10000000000000 : ℝ)) half_11_15_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_15_φ1, half_11_15_φ2, half_11_15_φ3, half_11_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_15_φ1, half_11_15_φ2, half_11_15_φ3, half_11_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_15_φ1, half_11_15_φ2, half_11_15_φ3, half_11_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_15 half_11_14
    (by simpa only [half_11_15_φ2, show (2:ℝ)*2=4 by norm_num] using half_11_15_hx2)
  exact h.weaken (by norm_num [half_11_15_φ1, half_11_15_φ2, half_11_15_φ3, half_11_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_11_15 : AdmissibleExponent 16 22 (63835899493087/5000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 9) (ψ := (424766880167/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_10_15
    (by simpa only [half_11_15_φ1] using half_11_15_hx1)
  exact admissibleExponent_mono h (by norm_num [half_11_15_φ1, half_11_15_φ2, half_11_15_φ3, half_11_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_12_15_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (218262821019/5000000000000 : ℝ)

private def half_12_15_φ2 : Fin 2 → ℝ := Fin.snoc half_12_15_φ1 (419529195319/10000000000000 : ℝ)

private def half_12_15_φ3 : Fin 3 → ℝ := Fin.snoc half_12_15_φ2 (192957823479/5000000000000 : ℝ)

private def half_12_15_φ4 : Fin 4 → ℝ := Fin.snoc half_12_15_φ3 (1116927981/40000000000 : ℝ)

private theorem half_12_15_hF2 : SourcePowerBound (paddedMoment 16 0 2 16 half_12_15_φ4) (2861835536783/400000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_12_15_φ4 (by norm_num [half_12_15_φ1, half_12_15_φ2, half_12_15_φ3, half_12_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_15_φ1, half_12_15_φ2, half_12_15_φ3, half_12_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_15_φ1, half_12_15_φ2, half_12_15_φ3, half_12_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_12_15_φ1, half_12_15_φ2, half_12_15_φ3, half_12_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_12_15_hx4 : SourcePowerBound (powerBoxCross 16 8 16 half_12_15_φ4) (24045093582919/2500000000000 : ℝ) := by
  have h := full_A_cross_power (k := 16) (s := 8) (r := 2) (v := 10) (w := 11) (D := 16)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_12_15_φ4 (by norm_num [half_12_15_φ1, half_12_15_φ2, half_12_15_φ3, half_12_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_15_φ1, half_12_15_φ2, half_12_15_φ3, half_12_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_12_15_hF2 half_10_15 half_11_15
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_12_15_φ1, half_12_15_φ2, half_12_15_φ3, half_12_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_12_15_hx3 : SourcePowerBound (powerBoxCross 16 9 8 half_12_15_φ3) (105799016234511/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 9) (u := 7) (t := 10)
    (D := 8) (ψ := (1116927981/40000000000 : ℝ)) half_12_15_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_15_φ1, half_12_15_φ2, half_12_15_φ3, half_12_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_15_φ1, half_12_15_φ2, half_12_15_φ3, half_12_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_15_φ1, half_12_15_φ2, half_12_15_φ3, half_12_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8 half_10_15
    (by simpa only [half_12_15_φ4, show (2:ℝ)*8=16 by norm_num] using half_12_15_hx4)
  exact h.weaken (by norm_num [half_12_15_φ1, half_12_15_φ2, half_12_15_φ3, half_12_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_12_15_hx2 : SourcePowerBound (powerBoxCross 16 10 4 half_12_15_φ2) (118130576273499/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 10) (u := 8) (t := 11)
    (D := 4) (ψ := (192957823479/5000000000000 : ℝ)) half_12_15_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_15_φ1, half_12_15_φ2, half_12_15_φ3, half_12_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_15_φ1, half_12_15_φ2, half_12_15_φ3, half_12_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_15_φ1, half_12_15_φ2, half_12_15_φ3, half_12_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_15 half_11_15
    (by simpa only [half_12_15_φ3, show (2:ℝ)*4=8 by norm_num] using half_12_15_hx3)
  exact h.weaken (by norm_num [half_12_15_φ1, half_12_15_φ2, half_12_15_φ3, half_12_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_12_15_hx1 : SourcePowerBound (powerBoxCross 16 11 2 half_12_15_φ1) (33133780806491/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 11) (u := 9) (t := 12)
    (D := 2) (ψ := (419529195319/10000000000000 : ℝ)) half_12_15_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_15_φ1, half_12_15_φ2, half_12_15_φ3, half_12_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_15_φ1, half_12_15_φ2, half_12_15_φ3, half_12_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_15_φ1, half_12_15_φ2, half_12_15_φ3, half_12_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_15 half_12_14
    (by simpa only [half_12_15_φ2, show (2:ℝ)*2=4 by norm_num] using half_12_15_hx2)
  exact h.weaken (by norm_num [half_12_15_φ1, half_12_15_φ2, half_12_15_φ3, half_12_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_12_15 : AdmissibleExponent 16 24 (70851080854381/5000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 10) (ψ := (218262821019/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_11_15
    (by simpa only [half_12_15_φ1] using half_12_15_hx1)
  exact admissibleExponent_mono h (by norm_num [half_12_15_φ1, half_12_15_φ2, half_12_15_φ3, half_12_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_13_15_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (89872643967/2000000000000 : ℝ)

private def half_13_15_φ2 : Fin 2 → ℝ := Fin.snoc half_13_15_φ1 (43434378039/1000000000000 : ℝ)

private def half_13_15_φ3 : Fin 3 → ℝ := Fin.snoc half_13_15_φ2 (413375930189/10000000000000 : ℝ)

private def half_13_15_φ4 : Fin 4 → ℝ := Fin.snoc half_13_15_φ3 (363299535133/10000000000000 : ℝ)

private def half_13_15_φ5 : Fin 5 → ℝ := Fin.snoc half_13_15_φ4 (181079128039/10000000000000 : ℝ)

private theorem half_13_15_hF2 : SourcePowerBound (paddedMoment 16 0 2 32 half_13_15_φ5) (8713422828863/1000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_13_15_φ5 (by norm_num [half_13_15_φ1, half_13_15_φ2, half_13_15_φ3, half_13_15_φ4, half_13_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_15_φ1, half_13_15_φ2, half_13_15_φ3, half_13_15_φ4, half_13_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_15_φ1, half_13_15_φ2, half_13_15_φ3, half_13_15_φ4, half_13_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_13_15_φ1, half_13_15_φ2, half_13_15_φ3, half_13_15_φ4, half_13_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_13_15_hF1 : SourcePowerBound (paddedMoment 16 0 1 32 half_13_15_φ5) (3237807609621/1000000000000 : ℝ) := by
  have h := padded_second_power (k := 16) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_13_15_φ5 (by norm_num [half_13_15_φ1, half_13_15_φ2, half_13_15_φ3, half_13_15_φ4, half_13_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_15_φ1, half_13_15_φ2, half_13_15_φ3, half_13_15_φ4, half_13_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_15_φ1, half_13_15_φ2, half_13_15_φ3, half_13_15_φ4, half_13_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_13_15_φ1, half_13_15_φ2, half_13_15_φ3, half_13_15_φ4, half_13_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_13_15_hx5 : SourcePowerBound (powerBoxCross 16 8 32 half_13_15_φ5) (19398177193799/2000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 16) (s := 8) (r := 1) (v := 2) (t := 12) (D := 32)
    (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
    (by norm_num) half_13_15_φ5 (by norm_num [half_13_15_φ1, half_13_15_φ2, half_13_15_φ3, half_13_15_φ4, half_13_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_15_φ1, half_13_15_φ2, half_13_15_φ3, half_13_15_φ4, half_13_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_13_15_hF1 half_13_15_hF2 half_12_15
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_13_15_φ1, half_13_15_φ2, half_13_15_φ3, half_13_15_φ4, half_13_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_15_hx4 : SourcePowerBound (powerBoxCross 16 9 16 half_13_15_φ4) (10494467655867/1000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 4) (s := 9) (u := 7) (t := 10)
    (D := 16) (ψ := (181079128039/10000000000000 : ℝ)) half_13_15_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_15_φ1, half_13_15_φ2, half_13_15_φ3, half_13_15_φ4, half_13_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_15_φ1, half_13_15_φ2, half_13_15_φ3, half_13_15_φ4, half_13_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_15_φ1, half_13_15_φ2, half_13_15_φ3, half_13_15_φ4, half_13_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8 half_10_15
    (by simpa only [half_13_15_φ5, show (2:ℝ)*16=32 by norm_num] using half_13_15_hx5)
  exact h.weaken (by norm_num [half_13_15_φ1, half_13_15_φ2, half_13_15_φ3, half_13_15_φ4, half_13_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_15_hx3 : SourcePowerBound (powerBoxCross 16 10 8 half_13_15_φ3) (116388116284937/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 10) (u := 8) (t := 11)
    (D := 8) (ψ := (363299535133/10000000000000 : ℝ)) half_13_15_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_15_φ1, half_13_15_φ2, half_13_15_φ3, half_13_15_φ4, half_13_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_15_φ1, half_13_15_φ2, half_13_15_φ3, half_13_15_φ4, half_13_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_15_φ1, half_13_15_φ2, half_13_15_φ3, half_13_15_φ4, half_13_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_15 half_11_15
    (by simpa only [half_13_15_φ4, show (2:ℝ)*8=16 by norm_num] using half_13_15_hx4)
  exact h.weaken (by norm_num [half_13_15_φ1, half_13_15_φ2, half_13_15_φ3, half_13_15_φ4, half_13_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_15_hx2 : SourcePowerBound (powerBoxCross 16 11 4 half_13_15_φ2) (65041624109753/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 11) (u := 9) (t := 12)
    (D := 4) (ψ := (413375930189/10000000000000 : ℝ)) half_13_15_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_15_φ1, half_13_15_φ2, half_13_15_φ3, half_13_15_φ4, half_13_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_15_φ1, half_13_15_φ2, half_13_15_φ3, half_13_15_φ4, half_13_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_15_φ1, half_13_15_φ2, half_13_15_φ3, half_13_15_φ4, half_13_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_15 half_12_15
    (by simpa only [half_13_15_φ3, show (2:ℝ)*4=8 by norm_num] using half_13_15_hx3)
  exact h.weaken (by norm_num [half_13_15_φ1, half_13_15_φ2, half_13_15_φ3, half_13_15_φ4, half_13_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_15_hx1 : SourcePowerBound (powerBoxCross 16 12 2 half_13_15_φ1) (72891975482151/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 12) (u := 10) (t := 13)
    (D := 2) (ψ := (43434378039/1000000000000 : ℝ)) half_13_15_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_15_φ1, half_13_15_φ2, half_13_15_φ3, half_13_15_φ4, half_13_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_15_φ1, half_13_15_φ2, half_13_15_φ3, half_13_15_φ4, half_13_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_15_φ1, half_13_15_φ2, half_13_15_φ3, half_13_15_φ4, half_13_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_15 half_13_14
    (by simpa only [half_13_15_φ2, show (2:ℝ)*2=4 by norm_num] using half_13_15_hx2)
  exact h.weaken (by norm_num [half_13_15_φ1, half_13_15_φ2, half_13_15_φ3, half_13_15_φ4, half_13_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_15 : AdmissibleExponent 16 26 (156119305020507/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 11) (ψ := (89872643967/2000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_12_15
    (by simpa only [half_13_15_φ1] using half_13_15_hx1)
  exact admissibleExponent_mono h (by norm_num [half_13_15_φ1, half_13_15_φ2, half_13_15_φ3, half_13_15_φ4, half_13_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_14_15_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (230407802129/5000000000000 : ℝ)

private def half_14_15_φ2 : Fin 2 → ℝ := Fin.snoc half_14_15_φ1 (446935842837/10000000000000 : ℝ)

private def half_14_15_φ3 : Fin 3 → ℝ := Fin.snoc half_14_15_φ2 (85570311177/2000000000000 : ℝ)

private def half_14_15_φ4 : Fin 4 → ℝ := Fin.snoc half_14_15_φ3 (3129608421/80000000000 : ℝ)

private def half_14_15_φ5 : Fin 5 → ℝ := Fin.snoc half_14_15_φ4 (137958757013/5000000000000 : ℝ)

private theorem half_14_15_hF2 : SourcePowerBound (paddedMoment 16 0 2 32 half_14_15_φ5) (15975505873321/2000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_14_15_φ5 (by norm_num [half_14_15_φ1, half_14_15_φ2, half_14_15_φ3, half_14_15_φ4, half_14_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_15_φ1, half_14_15_φ2, half_14_15_φ3, half_14_15_φ4, half_14_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_15_φ1, half_14_15_φ2, half_14_15_φ3, half_14_15_φ4, half_14_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_14_15_φ1, half_14_15_φ2, half_14_15_φ3, half_14_15_φ4, half_14_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_14_15_hx5 : SourcePowerBound (powerBoxCross 16 9 32 half_14_15_φ5) (26240438861103/2500000000000 : ℝ) := by
  have h := full_A_cross_power (k := 16) (s := 9) (r := 2) (v := 12) (w := 12) (D := 32)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_14_15_φ5 (by norm_num [half_14_15_φ1, half_14_15_φ2, half_14_15_φ3, half_14_15_φ4, half_14_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_15_φ1, half_14_15_φ2, half_14_15_φ3, half_14_15_φ4, half_14_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_14_15_hF2 half_12_15 half_12_15
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_14_15_φ1, half_14_15_φ2, half_14_15_φ3, half_14_15_φ4, half_14_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_15_hx4 : SourcePowerBound (powerBoxCross 16 10 16 half_14_15_φ4) (114687836653691/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 4) (s := 10) (u := 8) (t := 11)
    (D := 16) (ψ := (137958757013/5000000000000 : ℝ)) half_14_15_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_15_φ1, half_14_15_φ2, half_14_15_φ3, half_14_15_φ4, half_14_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_15_φ1, half_14_15_φ2, half_14_15_φ3, half_14_15_φ4, half_14_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_15_φ1, half_14_15_φ2, half_14_15_φ3, half_14_15_φ4, half_14_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_15 half_11_15
    (by simpa only [half_14_15_φ5, show (2:ℝ)*16=32 by norm_num] using half_14_15_hx5)
  exact h.weaken (by norm_num [half_14_15_φ1, half_14_15_φ2, half_14_15_φ3, half_14_15_φ4, half_14_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_15_hx3 : SourcePowerBound (powerBoxCross 16 11 8 half_14_15_φ3) (25486299004693/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 11) (u := 9) (t := 12)
    (D := 8) (ψ := (3129608421/80000000000 : ℝ)) half_14_15_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_15_φ1, half_14_15_φ2, half_14_15_φ3, half_14_15_φ4, half_14_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_15_φ1, half_14_15_φ2, half_14_15_φ3, half_14_15_φ4, half_14_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_15_φ1, half_14_15_φ2, half_14_15_φ3, half_14_15_φ4, half_14_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_15 half_12_15
    (by simpa only [half_14_15_φ4, show (2:ℝ)*8=16 by norm_num] using half_14_15_hx4)
  exact h.weaken (by norm_num [half_14_15_φ1, half_14_15_φ2, half_14_15_φ3, half_14_15_φ4, half_14_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_15_hx2 : SourcePowerBound (powerBoxCross 16 12 4 half_14_15_φ2) (5694953170119/400000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 12) (u := 10) (t := 13)
    (D := 4) (ψ := (85570311177/2000000000000 : ℝ)) half_14_15_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_15_φ1, half_14_15_φ2, half_14_15_φ3, half_14_15_φ4, half_14_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_15_φ1, half_14_15_φ2, half_14_15_φ3, half_14_15_φ4, half_14_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_15_φ1, half_14_15_φ2, half_14_15_φ3, half_14_15_φ4, half_14_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_15 half_13_15
    (by simpa only [half_14_15_φ3, show (2:ℝ)*4=8 by norm_num] using half_14_15_hx3)
  exact h.weaken (by norm_num [half_14_15_φ1, half_14_15_φ2, half_14_15_φ3, half_14_15_φ4, half_14_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_15_hx1 : SourcePowerBound (powerBoxCross 16 13 2 half_14_15_φ1) (31877179887369/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 13) (u := 11) (t := 14)
    (D := 2) (ψ := (446935842837/10000000000000 : ℝ)) half_14_15_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_15_φ1, half_14_15_φ2, half_14_15_φ3, half_14_15_φ4, half_14_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_15_φ1, half_14_15_φ2, half_14_15_φ3, half_14_15_φ4, half_14_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_15_φ1, half_14_15_φ2, half_14_15_φ3, half_14_15_φ4, half_14_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_15 half_14_14
    (by simpa only [half_14_15_φ2, show (2:ℝ)*2=4 by norm_num] using half_14_15_hx2)
  exact h.weaken (by norm_num [half_14_15_φ1, half_14_15_φ2, half_14_15_φ3, half_14_15_φ4, half_14_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_15 : AdmissibleExponent 16 28 (34181257908659/2000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 12) (ψ := (230407802129/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_13_15
    (by simpa only [half_14_15_φ1] using half_14_15_hx1)
  exact admissibleExponent_mono h (by norm_num [half_14_15_φ1, half_14_15_φ2, half_14_15_φ3, half_14_15_φ4, half_14_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_9_16_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (79523193117/2000000000000 : ℝ)

private def half_9_16_φ2 : Fin 2 → ℝ := Fin.snoc half_9_16_φ1 (89822927431/2500000000000 : ℝ)

private def half_9_16_φ3 : Fin 3 → ℝ := Fin.snoc half_9_16_φ2 (99615178999/5000000000000 : ℝ)

private theorem half_9_16_hF2 : SourcePowerBound (paddedMoment 16 0 2 8 half_9_16_φ3) (13394757700237/2000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_16_φ3 (by norm_num [half_9_16_φ1, half_9_16_φ2, half_9_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_16_φ1, half_9_16_φ2, half_9_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_16_φ1, half_9_16_φ2, half_9_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_16_φ1, half_9_16_φ2, half_9_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_9_16_hF1 : SourcePowerBound (paddedMoment 16 0 1 8 half_9_16_φ3) (5131585900079/2000000000000 : ℝ) := by
  have h := padded_second_power (k := 16) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_16_φ3 (by norm_num [half_9_16_φ1, half_9_16_φ2, half_9_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_16_φ1, half_9_16_φ2, half_9_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_16_φ1, half_9_16_φ2, half_9_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_16_φ1, half_9_16_φ2, half_9_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_9_16_hx3 : SourcePowerBound (powerBoxCross 16 6 8 half_9_16_φ3) (76194774731213/10000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 16) (s := 6) (r := 1) (v := 2) (t := 9) (D := 8)
    (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
    (by norm_num) half_9_16_φ3 (by norm_num [half_9_16_φ1, half_9_16_φ2, half_9_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_16_φ1, half_9_16_φ2, half_9_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_9_16_hF1 half_9_16_hF2 half_9_15
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_9_16_φ1, half_9_16_φ2, half_9_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_16_hx2 : SourcePowerBound (powerBoxCross 16 7 4 half_9_16_φ2) (21035216376179/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 7) (u := 5) (t := 8)
    (D := 4) (ψ := (99615178999/5000000000000 : ℝ)) half_9_16_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_16_φ1, half_9_16_φ2, half_9_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_16_φ1, half_9_16_φ2, half_9_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_16_φ1, half_9_16_φ2, half_9_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_6 SeedCompletionEven16SecondSeeds.degree16_half_8
    (by simpa only [half_9_16_φ3, show (2:ℝ)*4=8 by norm_num] using half_9_16_hx3)
  exact h.weaken (by norm_num [half_9_16_φ1, half_9_16_φ2, half_9_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_16_hx1 : SourcePowerBound (powerBoxCross 16 8 2 half_9_16_φ1) (94804915255273/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 8) (u := 6) (t := 9)
    (D := 2) (ψ := (89822927431/2500000000000 : ℝ)) half_9_16_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_16_φ1, half_9_16_φ2, half_9_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_16_φ1, half_9_16_φ2, half_9_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_16_φ1, half_9_16_φ2, half_9_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_7 half_9_15
    (by simpa only [half_9_16_φ2, show (2:ℝ)*2=4 by norm_num] using half_9_16_hx2)
  exact h.weaken (by norm_num [half_9_16_φ1, half_9_16_φ2, half_9_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_16 : AdmissibleExponent 16 18 (12596144342381/1250000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 7) (ψ := (79523193117/2000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8
    (by simpa only [half_9_16_φ1] using half_9_16_hx1)
  exact admissibleExponent_mono h (by norm_num [half_9_16_φ1, half_9_16_φ2, half_9_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_10_16_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (12820461589/312500000000 : ℝ)

private def half_10_16_φ2 : Fin 2 → ℝ := Fin.snoc half_10_16_φ1 (19141617547/500000000000 : ℝ)

private def half_10_16_φ3 : Fin 3 → ℝ := Fin.snoc half_10_16_φ2 (144288954141/5000000000000 : ℝ)

private theorem half_10_16_hF2 : SourcePowerBound (paddedMoment 16 0 2 8 half_10_16_φ3) (1226501472937/200000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_10_16_φ3 (by norm_num [half_10_16_φ1, half_10_16_φ2, half_10_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_16_φ1, half_10_16_φ2, half_10_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_16_φ1, half_10_16_φ2, half_10_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_10_16_φ1, half_10_16_φ2, half_10_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_10_16_hx3 : SourcePowerBound (powerBoxCross 16 7 8 half_10_16_φ3) (85687555356471/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 16) (s := 7) (r := 2) (v := 9) (w := 10) (D := 8)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_10_16_φ3 (by norm_num [half_10_16_φ1, half_10_16_φ2, half_10_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_16_φ1, half_10_16_φ2, half_10_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_10_16_hF2 half_9_16 half_10_15
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_10_16_φ1, half_10_16_φ2, half_10_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_10_16_hx2 : SourcePowerBound (powerBoxCross 16 8 4 half_10_16_φ2) (95160022093333/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 8) (u := 6) (t := 9)
    (D := 4) (ψ := (144288954141/5000000000000 : ℝ)) half_10_16_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_16_φ1, half_10_16_φ2, half_10_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_16_φ1, half_10_16_φ2, half_10_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_16_φ1, half_10_16_φ2, half_10_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_7 half_9_16
    (by simpa only [half_10_16_φ3, show (2:ℝ)*4=8 by norm_num] using half_10_16_hx3)
  exact h.weaken (by norm_num [half_10_16_φ1, half_10_16_φ2, half_10_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_10_16_hx1 : SourcePowerBound (powerBoxCross 16 9 2 half_10_16_φ1) (13380663357663/1250000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 9) (u := 7) (t := 10)
    (D := 2) (ψ := (19141617547/500000000000 : ℝ)) half_10_16_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_16_φ1, half_10_16_φ2, half_10_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_16_φ1, half_10_16_φ2, half_10_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_16_φ1, half_10_16_φ2, half_10_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8 half_10_15
    (by simpa only [half_10_16_φ2, show (2:ℝ)*2=4 by norm_num] using half_10_16_hx2)
  exact h.weaken (by norm_num [half_10_16_φ1, half_10_16_φ2, half_10_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_10_16 : AdmissibleExponent 16 20 (2850490949143/250000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 8) (ψ := (12820461589/312500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_9_16
    (by simpa only [half_10_16_φ1] using half_10_16_hx1)
  exact admissibleExponent_mono h (by norm_num [half_10_16_φ1, half_10_16_φ2, half_10_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_11_16_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (424766874579/10000000000000 : ℝ)

private def half_11_16_φ2 : Fin 2 → ℝ := Fin.snoc half_11_16_φ1 (404883240143/10000000000000 : ℝ)

private def half_11_16_φ3 : Fin 3 → ℝ := Fin.snoc half_11_16_φ2 (90305898071/2500000000000 : ℝ)

private def half_11_16_φ4 : Fin 4 → ℝ := Fin.snoc half_11_16_φ3 (184040487403/10000000000000 : ℝ)

private theorem half_11_16_hF2 : SourcePowerBound (paddedMoment 16 0 2 16 half_11_16_φ4) (15625772250319/2000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_11_16_φ4 (by norm_num [half_11_16_φ1, half_11_16_φ2, half_11_16_φ3, half_11_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_16_φ1, half_11_16_φ2, half_11_16_φ3, half_11_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_16_φ1, half_11_16_φ2, half_11_16_φ3, half_11_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_11_16_φ1, half_11_16_φ2, half_11_16_φ3, half_11_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_11_16_hF1 : SourcePowerBound (paddedMoment 16 0 1 16 half_11_16_φ4) (5875257416773/2000000000000 : ℝ) := by
  have h := padded_second_power (k := 16) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_11_16_φ4 (by norm_num [half_11_16_φ1, half_11_16_φ2, half_11_16_φ3, half_11_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_16_φ1, half_11_16_φ2, half_11_16_φ3, half_11_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_16_φ1, half_11_16_φ2, half_11_16_φ3, half_11_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_11_16_φ1, half_11_16_φ2, half_11_16_φ3, half_11_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_11_16_hx4 : SourcePowerBound (powerBoxCross 16 7 16 half_11_16_φ4) (87403442227079/10000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 16) (s := 7) (r := 1) (v := 2) (t := 10) (D := 16)
    (a := (1/10 : ℝ)) (b := (1/5 : ℝ)) (c := (7/10 : ℝ))
    (by norm_num) half_11_16_φ4 (by norm_num [half_11_16_φ1, half_11_16_φ2, half_11_16_φ3, half_11_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_16_φ1, half_11_16_φ2, half_11_16_φ3, half_11_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_11_16_hF1 half_11_16_hF2 half_10_16
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_11_16_φ1, half_11_16_φ2, half_11_16_φ3, half_11_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_11_16_hx3 : SourcePowerBound (powerBoxCross 16 8 8 half_11_16_φ3) (95350842005841/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 8) (u := 6) (t := 9)
    (D := 8) (ψ := (184040487403/10000000000000 : ℝ)) half_11_16_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_16_φ1, half_11_16_φ2, half_11_16_φ3, half_11_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_16_φ1, half_11_16_φ2, half_11_16_φ3, half_11_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_16_φ1, half_11_16_φ2, half_11_16_φ3, half_11_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_7 half_9_16
    (by simpa only [half_11_16_φ4, show (2:ℝ)*8=16 by norm_num] using half_11_16_hx4)
  exact h.weaken (by norm_num [half_11_16_φ1, half_11_16_φ2, half_11_16_φ3, half_11_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_11_16_hx2 : SourcePowerBound (powerBoxCross 16 9 4 half_11_16_φ2) (21288444156311/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 9) (u := 7) (t := 10)
    (D := 4) (ψ := (90305898071/2500000000000 : ℝ)) half_11_16_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_16_φ1, half_11_16_φ2, half_11_16_φ3, half_11_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_16_φ1, half_11_16_φ2, half_11_16_φ3, half_11_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_16_φ1, half_11_16_φ2, half_11_16_φ3, half_11_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8 half_10_16
    (by simpa only [half_11_16_φ3, show (2:ℝ)*4=8 by norm_num] using half_11_16_hx3)
  exact h.weaken (by norm_num [half_11_16_φ1, half_11_16_φ2, half_11_16_φ3, half_11_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_11_16_hx1 : SourcePowerBound (powerBoxCross 16 10 2 half_11_16_φ1) (14950153539297/1250000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 10) (u := 8) (t := 11)
    (D := 2) (ψ := (404883240143/10000000000000 : ℝ)) half_11_16_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_16_φ1, half_11_16_φ2, half_11_16_φ3, half_11_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_16_φ1, half_11_16_φ2, half_11_16_φ3, half_11_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_16_φ1, half_11_16_φ2, half_11_16_φ3, half_11_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_16 half_11_15
    (by simpa only [half_11_16_φ2, show (2:ℝ)*2=4 by norm_num] using half_11_16_hx2)
  exact h.weaken (by norm_num [half_11_16_φ1, half_11_16_φ2, half_11_16_φ3, half_11_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_11_16 : AdmissibleExponent 16 22 (127671798931377/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 9) (ψ := (424766874579/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_10_16
    (by simpa only [half_11_16_φ1] using half_11_16_hx1)
  exact admissibleExponent_mono h (by norm_num [half_11_16_φ1, half_11_16_φ2, half_11_16_φ3, half_11_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_12_16_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (21826280513/500000000000 : ℝ)

private def half_12_16_φ2 : Fin 2 → ℝ := Fin.snoc half_12_16_φ1 (5244114919/125000000000 : ℝ)

private def half_12_16_φ3 : Fin 3 → ℝ := Fin.snoc half_12_16_φ2 (77183128853/2000000000000 : ℝ)

private def half_12_16_φ4 : Fin 4 → ℝ := Fin.snoc half_12_16_φ3 (55846396771/2000000000000 : ℝ)

private theorem half_12_16_hF2 : SourcePowerBound (paddedMoment 16 0 2 16 half_12_16_φ4) (143091781129/20000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_12_16_φ4 (by norm_num [half_12_16_φ1, half_12_16_φ2, half_12_16_φ3, half_12_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_16_φ1, half_12_16_φ2, half_12_16_φ3, half_12_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_16_φ1, half_12_16_φ2, half_12_16_φ3, half_12_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_12_16_φ1, half_12_16_φ2, half_12_16_φ3, half_12_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_12_16_hx4 : SourcePowerBound (powerBoxCross 16 8 16 half_12_16_φ4) (48090187641663/5000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 16) (s := 8) (r := 2) (v := 10) (w := 11) (D := 16)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_12_16_φ4 (by norm_num [half_12_16_φ1, half_12_16_φ2, half_12_16_φ3, half_12_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_16_φ1, half_12_16_φ2, half_12_16_φ3, half_12_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_12_16_hF2 half_10_16 half_11_16
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_12_16_φ1, half_12_16_φ2, half_12_16_φ3, half_12_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_12_16_hx3 : SourcePowerBound (powerBoxCross 16 9 8 half_12_16_φ3) (26449754275147/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 9) (u := 7) (t := 10)
    (D := 8) (ψ := (55846396771/2000000000000 : ℝ)) half_12_16_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_16_φ1, half_12_16_φ2, half_12_16_φ3, half_12_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_16_φ1, half_12_16_φ2, half_12_16_φ3, half_12_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_16_φ1, half_12_16_φ2, half_12_16_φ3, half_12_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8 half_10_16
    (by simpa only [half_12_16_φ4, show (2:ℝ)*8=16 by norm_num] using half_12_16_hx4)
  exact h.weaken (by norm_num [half_12_16_φ1, half_12_16_φ2, half_12_16_φ3, half_12_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_12_16_hx2 : SourcePowerBound (powerBoxCross 16 10 4 half_12_16_φ2) (29532644281191/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 10) (u := 8) (t := 11)
    (D := 4) (ψ := (77183128853/2000000000000 : ℝ)) half_12_16_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_16_φ1, half_12_16_φ2, half_12_16_φ3, half_12_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_16_φ1, half_12_16_φ2, half_12_16_φ3, half_12_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_16_φ1, half_12_16_φ2, half_12_16_φ3, half_12_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_16 half_11_16
    (by simpa only [half_12_16_φ3, show (2:ℝ)*4=8 by norm_num] using half_12_16_hx3)
  exact h.weaken (by norm_num [half_12_16_φ1, half_12_16_φ2, half_12_16_φ3, half_12_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_12_16_hx1 : SourcePowerBound (powerBoxCross 16 11 2 half_12_16_φ1) (53014049419/4000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 11) (u := 9) (t := 12)
    (D := 2) (ψ := (5244114919/125000000000 : ℝ)) half_12_16_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_16_φ1, half_12_16_φ2, half_12_16_φ3, half_12_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_16_φ1, half_12_16_φ2, half_12_16_φ3, half_12_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_16_φ1, half_12_16_φ2, half_12_16_φ3, half_12_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_16 half_12_15
    (by simpa only [half_12_16_φ2, show (2:ℝ)*2=4 by norm_num] using half_12_16_hx2)
  exact h.weaken (by norm_num [half_12_16_φ1, half_12_16_φ2, half_12_16_φ3, half_12_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_12_16 : AdmissibleExponent 16 24 (1771277017037/125000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 10) (ψ := (21826280513/500000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_11_16
    (by simpa only [half_12_16_φ1] using half_12_16_hx1)
  exact admissibleExponent_mono h (by norm_num [half_12_16_φ1, half_12_16_φ2, half_12_16_φ3, half_12_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_13_16_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (449363081841/10000000000000 : ℝ)

private def half_13_16_φ2 : Fin 2 → ℝ := Fin.snoc half_13_16_φ1 (27146485763/625000000000 : ℝ)

private def half_13_16_φ3 : Fin 3 → ℝ := Fin.snoc half_13_16_φ2 (413375924851/10000000000000 : ℝ)

private def half_13_16_φ4 : Fin 4 → ℝ := Fin.snoc half_13_16_φ3 (14531980693/400000000000 : ℝ)

private def half_13_16_φ5 : Fin 5 → ℝ := Fin.snoc half_13_16_φ4 (45269762203/2500000000000 : ℝ)

private theorem half_13_16_hF2 : SourcePowerBound (paddedMoment 16 0 2 32 half_13_16_φ5) (17426847894667/2000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_13_16_φ5 (by norm_num [half_13_16_φ1, half_13_16_φ2, half_13_16_φ3, half_13_16_φ4, half_13_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_16_φ1, half_13_16_φ2, half_13_16_φ3, half_13_16_φ4, half_13_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_16_φ1, half_13_16_φ2, half_13_16_φ3, half_13_16_φ4, half_13_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_13_16_φ1, half_13_16_φ2, half_13_16_φ3, half_13_16_φ4, half_13_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_13_16_hF1 : SourcePowerBound (paddedMoment 16 0 1 32 half_13_16_φ5) (6475615964889/2000000000000 : ℝ) := by
  have h := padded_second_power (k := 16) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_13_16_φ5 (by norm_num [half_13_16_φ1, half_13_16_φ2, half_13_16_φ3, half_13_16_φ4, half_13_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_16_φ1, half_13_16_φ2, half_13_16_φ3, half_13_16_φ4, half_13_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_16_φ1, half_13_16_φ2, half_13_16_φ3, half_13_16_φ4, half_13_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_13_16_φ1, half_13_16_φ2, half_13_16_φ3, half_13_16_φ4, half_13_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_13_16_hx5 : SourcePowerBound (powerBoxCross 16 8 32 half_13_16_φ5) (48495445307199/5000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 16) (s := 8) (r := 1) (v := 2) (t := 12) (D := 32)
    (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
    (by norm_num) half_13_16_φ5 (by norm_num [half_13_16_φ1, half_13_16_φ2, half_13_16_φ3, half_13_16_φ4, half_13_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_16_φ1, half_13_16_φ2, half_13_16_φ3, half_13_16_φ4, half_13_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_13_16_hF1 half_13_16_hF2 half_12_16
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_13_16_φ1, half_13_16_φ2, half_13_16_φ3, half_13_16_φ4, half_13_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_16_hx4 : SourcePowerBound (powerBoxCross 16 9 16 half_13_16_φ4) (104944680519451/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 4) (s := 9) (u := 7) (t := 10)
    (D := 16) (ψ := (45269762203/2500000000000 : ℝ)) half_13_16_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_16_φ1, half_13_16_φ2, half_13_16_φ3, half_13_16_φ4, half_13_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_16_φ1, half_13_16_φ2, half_13_16_φ3, half_13_16_φ4, half_13_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_16_φ1, half_13_16_φ2, half_13_16_φ3, half_13_16_φ4, half_13_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8 half_10_16
    (by simpa only [half_13_16_φ5, show (2:ℝ)*16=32 by norm_num] using half_13_16_hx5)
  exact h.weaken (by norm_num [half_13_16_φ1, half_13_16_φ2, half_13_16_φ3, half_13_16_φ4, half_13_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_16_hx3 : SourcePowerBound (powerBoxCross 16 10 8 half_13_16_φ3) (116388120193673/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 10) (u := 8) (t := 11)
    (D := 8) (ψ := (14531980693/400000000000 : ℝ)) half_13_16_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_16_φ1, half_13_16_φ2, half_13_16_φ3, half_13_16_φ4, half_13_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_16_φ1, half_13_16_φ2, half_13_16_φ3, half_13_16_φ4, half_13_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_16_φ1, half_13_16_φ2, half_13_16_φ3, half_13_16_φ4, half_13_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_16 half_11_16
    (by simpa only [half_13_16_φ4, show (2:ℝ)*8=16 by norm_num] using half_13_16_hx4)
  exact h.weaken (by norm_num [half_13_16_φ1, half_13_16_φ2, half_13_16_φ3, half_13_16_φ4, half_13_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_16_hx2 : SourcePowerBound (powerBoxCross 16 11 4 half_13_16_φ2) (65041626048767/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 11) (u := 9) (t := 12)
    (D := 4) (ψ := (413375924851/10000000000000 : ℝ)) half_13_16_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_16_φ1, half_13_16_φ2, half_13_16_φ3, half_13_16_φ4, half_13_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_16_φ1, half_13_16_φ2, half_13_16_φ3, half_13_16_φ4, half_13_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_16_φ1, half_13_16_φ2, half_13_16_φ3, half_13_16_φ4, half_13_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_16 half_12_16
    (by simpa only [half_13_16_φ3, show (2:ℝ)*4=8 by norm_num] using half_13_16_hx3)
  exact h.weaken (by norm_num [half_13_16_φ1, half_13_16_φ2, half_13_16_φ3, half_13_16_φ4, half_13_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_16_hx1 : SourcePowerBound (powerBoxCross 16 12 2 half_13_16_φ1) (145783952451453/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 12) (u := 10) (t := 13)
    (D := 2) (ψ := (27146485763/625000000000 : ℝ)) half_13_16_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_16_φ1, half_13_16_φ2, half_13_16_φ3, half_13_16_φ4, half_13_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_16_φ1, half_13_16_φ2, half_13_16_φ3, half_13_16_φ4, half_13_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_16_φ1, half_13_16_φ2, half_13_16_φ3, half_13_16_φ4, half_13_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_16 half_13_15
    (by simpa only [half_13_16_φ2, show (2:ℝ)*2=4 by norm_num] using half_13_16_hx2)
  exact h.weaken (by norm_num [half_13_16_φ1, half_13_16_φ2, half_13_16_φ3, half_13_16_φ4, half_13_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_16 : AdmissibleExponent 16 26 (39029825833449/2500000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 11) (ψ := (449363081841/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_12_16
    (by simpa only [half_13_16_φ1] using half_13_16_hx1)
  exact admissibleExponent_mono h (by norm_num [half_13_16_φ1, half_13_16_φ2, half_13_16_φ3, half_13_16_φ4, half_13_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_14_16_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (230407557177/5000000000000 : ℝ)

private def half_14_16_φ2 : Fin 2 → ℝ := Fin.snoc half_14_16_φ1 (3575486471/80000000000 : ℝ)

private def half_14_16_φ3 : Fin 3 → ℝ := Fin.snoc half_14_16_φ2 (213925769561/5000000000000 : ℝ)

private def half_14_16_φ4 : Fin 4 → ℝ := Fin.snoc half_14_16_φ3 (195600506169/5000000000000 : ℝ)

private def half_14_16_φ5 : Fin 5 → ℝ := Fin.snoc half_14_16_φ4 (34489669083/1250000000000 : ℝ)

private theorem half_14_16_hF2 : SourcePowerBound (paddedMoment 16 0 2 32 half_14_16_φ5) (15975512553823/2000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_14_16_φ5 (by norm_num [half_14_16_φ1, half_14_16_φ2, half_14_16_φ3, half_14_16_φ4, half_14_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_16_φ1, half_14_16_φ2, half_14_16_φ3, half_14_16_φ4, half_14_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_16_φ1, half_14_16_φ2, half_14_16_φ3, half_14_16_φ4, half_14_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_14_16_φ1, half_14_16_φ2, half_14_16_φ3, half_14_16_φ4, half_14_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_14_16_hx5 : SourcePowerBound (powerBoxCross 16 9 32 half_14_16_φ5) (104961771476309/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 16) (s := 9) (r := 2) (v := 12) (w := 12) (D := 32)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_14_16_φ5 (by norm_num [half_14_16_φ1, half_14_16_φ2, half_14_16_φ3, half_14_16_φ4, half_14_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_16_φ1, half_14_16_φ2, half_14_16_φ3, half_14_16_φ4, half_14_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_14_16_hF2 half_12_16 half_12_16
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_14_16_φ1, half_14_16_φ2, half_14_16_φ3, half_14_16_φ4, half_14_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_16_hx4 : SourcePowerBound (powerBoxCross 16 10 16 half_14_16_φ4) (114687851340597/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 4) (s := 10) (u := 8) (t := 11)
    (D := 16) (ψ := (34489669083/1250000000000 : ℝ)) half_14_16_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_16_φ1, half_14_16_φ2, half_14_16_φ3, half_14_16_φ4, half_14_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_16_φ1, half_14_16_φ2, half_14_16_φ3, half_14_16_φ4, half_14_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_16_φ1, half_14_16_φ2, half_14_16_φ3, half_14_16_φ4, half_14_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_16 half_11_16
    (by simpa only [half_14_16_φ5, show (2:ℝ)*16=32 by norm_num] using half_14_16_hx5)
  exact h.weaken (by norm_num [half_14_16_φ1, half_14_16_φ2, half_14_16_φ3, half_14_16_φ4, half_14_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_16_hx3 : SourcePowerBound (powerBoxCross 16 11 8 half_14_16_φ3) (31857877429879/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 11) (u := 9) (t := 12)
    (D := 8) (ψ := (195600506169/5000000000000 : ℝ)) half_14_16_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_16_φ1, half_14_16_φ2, half_14_16_φ3, half_14_16_φ4, half_14_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_16_φ1, half_14_16_φ2, half_14_16_φ3, half_14_16_φ4, half_14_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_16_φ1, half_14_16_φ2, half_14_16_φ3, half_14_16_φ4, half_14_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_16 half_12_16
    (by simpa only [half_14_16_φ4, show (2:ℝ)*8=16 by norm_num] using half_14_16_hx4)
  exact h.weaken (by norm_num [half_14_16_φ1, half_14_16_φ2, half_14_16_φ3, half_14_16_φ4, half_14_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_16_hx2 : SourcePowerBound (powerBoxCross 16 12 4 half_14_16_φ2) (8898365229779/625000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 12) (u := 10) (t := 13)
    (D := 4) (ψ := (213925769561/5000000000000 : ℝ)) half_14_16_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_16_φ1, half_14_16_φ2, half_14_16_φ3, half_14_16_φ4, half_14_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_16_φ1, half_14_16_φ2, half_14_16_φ3, half_14_16_φ4, half_14_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_16_φ1, half_14_16_φ2, half_14_16_φ3, half_14_16_φ4, half_14_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_16 half_13_16
    (by simpa only [half_14_16_φ3, show (2:ℝ)*4=8 by norm_num] using half_14_16_hx3)
  exact h.weaken (by norm_num [half_14_16_φ1, half_14_16_φ2, half_14_16_φ3, half_14_16_φ4, half_14_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_16_hx1 : SourcePowerBound (powerBoxCross 16 13 2 half_14_16_φ1) (79692952493151/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 13) (u := 11) (t := 14)
    (D := 2) (ψ := (3575486471/80000000000 : ℝ)) half_14_16_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_16_φ1, half_14_16_φ2, half_14_16_φ3, half_14_16_φ4, half_14_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_16_φ1, half_14_16_φ2, half_14_16_φ3, half_14_16_φ4, half_14_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_16_φ1, half_14_16_φ2, half_14_16_φ3, half_14_16_φ4, half_14_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_16 half_14_15
    (by simpa only [half_14_16_φ2, show (2:ℝ)*2=4 by norm_num] using half_14_16_hx2)
  exact h.weaken (by norm_num [half_14_16_φ1, half_14_16_φ2, half_14_16_φ3, half_14_16_φ4, half_14_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_16 : AdmissibleExponent 16 28 (5340821338911/312500000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 12) (ψ := (230407557177/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_13_16
    (by simpa only [half_14_16_φ1] using half_14_16_hx1)
  exact admissibleExponent_mono h (by norm_num [half_14_16_φ1, half_14_16_φ2, half_14_16_φ3, half_14_16_φ4, half_14_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_9_17_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (397615965571/10000000000000 : ℝ)

private def half_9_17_φ2 : Fin 2 → ℝ := Fin.snoc half_9_17_φ1 (359291709719/10000000000000 : ℝ)

private def half_9_17_φ3 : Fin 3 → ℝ := Fin.snoc half_9_17_φ2 (99615178983/5000000000000 : ℝ)

private theorem half_9_17_hF2 : SourcePowerBound (paddedMoment 16 0 2 8 half_9_17_φ3) (1674344712587/250000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_17_φ3 (by norm_num [half_9_17_φ1, half_9_17_φ2, half_9_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_17_φ1, half_9_17_φ2, half_9_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_17_φ1, half_9_17_φ2, half_9_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_17_φ1, half_9_17_φ2, half_9_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_9_17_hF1 : SourcePowerBound (paddedMoment 16 0 1 8 half_9_17_φ3) (641448237529/250000000000 : ℝ) := by
  have h := padded_second_power (k := 16) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_17_φ3 (by norm_num [half_9_17_φ1, half_9_17_φ2, half_9_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_17_φ1, half_9_17_φ2, half_9_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_17_φ1, half_9_17_φ2, half_9_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_17_φ1, half_9_17_φ2, half_9_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_9_17_hx3 : SourcePowerBound (powerBoxCross 16 6 8 half_9_17_φ3) (38097387365901/5000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 16) (s := 6) (r := 1) (v := 2) (t := 9) (D := 8)
    (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
    (by norm_num) half_9_17_φ3 (by norm_num [half_9_17_φ1, half_9_17_φ2, half_9_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_17_φ1, half_9_17_φ2, half_9_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_9_17_hF1 half_9_17_hF2 half_9_16
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_9_17_φ1, half_9_17_φ2, half_9_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_17_hx2 : SourcePowerBound (powerBoxCross 16 7 4 half_9_17_φ2) (84140865505059/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 7) (u := 5) (t := 8)
    (D := 4) (ψ := (99615178983/5000000000000 : ℝ)) half_9_17_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_17_φ1, half_9_17_φ2, half_9_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_17_φ1, half_9_17_φ2, half_9_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_17_φ1, half_9_17_φ2, half_9_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_6 SeedCompletionEven16SecondSeeds.degree16_half_8
    (by simpa only [half_9_17_φ3, show (2:ℝ)*4=8 by norm_num] using half_9_17_hx3)
  exact h.weaken (by norm_num [half_9_17_φ1, half_9_17_φ2, half_9_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_17_hx1 : SourcePowerBound (powerBoxCross 16 8 2 half_9_17_φ1) (47402457627689/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 8) (u := 6) (t := 9)
    (D := 2) (ψ := (359291709719/10000000000000 : ℝ)) half_9_17_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_17_φ1, half_9_17_φ2, half_9_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_17_φ1, half_9_17_φ2, half_9_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_17_φ1, half_9_17_φ2, half_9_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_7 half_9_16
    (by simpa only [half_9_17_φ2, show (2:ℝ)*2=4 by norm_num] using half_9_17_hx2)
  exact h.weaken (by norm_num [half_9_17_φ1, half_9_17_φ2, half_9_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_17 : AdmissibleExponent 16 18 (100769154738943/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 7) (ψ := (397615965571/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8
    (by simpa only [half_9_17_φ1] using half_9_17_hx1)
  exact admissibleExponent_mono h (by norm_num [half_9_17_φ1, half_9_17_φ2, half_9_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_10_17_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (205127385317/5000000000000 : ℝ)

private def half_10_17_φ2 : Fin 2 → ℝ := Fin.snoc half_10_17_φ1 (382832350897/10000000000000 : ℝ)

private def half_10_17_φ3 : Fin 3 → ℝ := Fin.snoc half_10_17_φ2 (72144477021/2500000000000 : ℝ)

private theorem half_10_17_hF2 : SourcePowerBound (paddedMoment 16 0 2 8 half_10_17_φ3) (2453002946693/400000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_10_17_φ3 (by norm_num [half_10_17_φ1, half_10_17_φ2, half_10_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_17_φ1, half_10_17_φ2, half_10_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_17_φ1, half_10_17_φ2, half_10_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_10_17_φ1, half_10_17_φ2, half_10_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_10_17_hx3 : SourcePowerBound (powerBoxCross 16 7 8 half_10_17_φ3) (42843777681781/5000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 16) (s := 7) (r := 2) (v := 9) (w := 10) (D := 8)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_10_17_φ3 (by norm_num [half_10_17_φ1, half_10_17_φ2, half_10_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_17_φ1, half_10_17_φ2, half_10_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_10_17_hF2 half_9_17 half_10_16
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_10_17_φ1, half_10_17_φ2, half_10_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_10_17_hx2 : SourcePowerBound (powerBoxCross 16 8 4 half_10_17_φ2) (19032004419753/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 8) (u := 6) (t := 9)
    (D := 4) (ψ := (72144477021/2500000000000 : ℝ)) half_10_17_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_17_φ1, half_10_17_φ2, half_10_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_17_φ1, half_10_17_φ2, half_10_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_17_φ1, half_10_17_φ2, half_10_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_7 half_9_17
    (by simpa only [half_10_17_φ3, show (2:ℝ)*4=8 by norm_num] using half_10_17_hx3)
  exact h.weaken (by norm_num [half_10_17_φ1, half_10_17_φ2, half_10_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_10_17_hx1 : SourcePowerBound (powerBoxCross 16 9 2 half_10_17_φ1) (53522653431573/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 9) (u := 7) (t := 10)
    (D := 2) (ψ := (382832350897/10000000000000 : ℝ)) half_10_17_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_17_φ1, half_10_17_φ2, half_10_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_17_φ1, half_10_17_φ2, half_10_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_17_φ1, half_10_17_φ2, half_10_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8 half_10_16
    (by simpa only [half_10_17_φ2, show (2:ℝ)*2=4 by norm_num] using half_10_17_hx2)
  exact h.weaken (by norm_num [half_10_17_φ1, half_10_17_φ2, half_10_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_10_17 : AdmissibleExponent 16 20 (28504909490981/2500000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 8) (ψ := (205127385317/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_9_17
    (by simpa only [half_10_17_φ1] using half_10_17_hx1)
  exact admissibleExponent_mono h (by norm_num [half_10_17_φ1, half_10_17_φ2, half_10_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_11_17_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (424766873027/10000000000000 : ℝ)

private def half_11_17_φ2 : Fin 2 → ℝ := Fin.snoc half_11_17_φ1 (101220810017/2500000000000 : ℝ)

private def half_11_17_φ3 : Fin 3 → ℝ := Fin.snoc half_11_17_φ2 (22576474509/625000000000 : ℝ)

private def half_11_17_φ4 : Fin 4 → ℝ := Fin.snoc half_11_17_φ3 (184040486711/10000000000000 : ℝ)

private theorem half_11_17_hF2 : SourcePowerBound (paddedMoment 16 0 2 16 half_11_17_φ4) (312515445449/40000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_11_17_φ4 (by norm_num [half_11_17_φ1, half_11_17_φ2, half_11_17_φ3, half_11_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_17_φ1, half_11_17_φ2, half_11_17_φ3, half_11_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_17_φ1, half_11_17_φ2, half_11_17_φ3, half_11_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_11_17_φ1, half_11_17_φ2, half_11_17_φ3, half_11_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_11_17_hF1 : SourcePowerBound (paddedMoment 16 0 1 16 half_11_17_φ4) (117505148483/40000000000 : ℝ) := by
  have h := padded_second_power (k := 16) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_11_17_φ4 (by norm_num [half_11_17_φ1, half_11_17_φ2, half_11_17_φ3, half_11_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_17_φ1, half_11_17_φ2, half_11_17_φ3, half_11_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_17_φ1, half_11_17_φ2, half_11_17_φ3, half_11_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_11_17_φ1, half_11_17_φ2, half_11_17_φ3, half_11_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_11_17_hx4 : SourcePowerBound (powerBoxCross 16 7 16 half_11_17_φ4) (1092543028393/125000000000 : ℝ) := by
  have h := full_B_cross_power (k := 16) (s := 7) (r := 1) (v := 2) (t := 10) (D := 16)
    (a := (1/10 : ℝ)) (b := (1/5 : ℝ)) (c := (7/10 : ℝ))
    (by norm_num) half_11_17_φ4 (by norm_num [half_11_17_φ1, half_11_17_φ2, half_11_17_φ3, half_11_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_17_φ1, half_11_17_φ2, half_11_17_φ3, half_11_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_11_17_hF1 half_11_17_hF2 half_10_17
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_11_17_φ1, half_11_17_φ2, half_11_17_φ3, half_11_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_11_17_hx3 : SourcePowerBound (powerBoxCross 16 8 8 half_11_17_φ3) (47675421022817/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 8) (u := 6) (t := 9)
    (D := 8) (ψ := (184040486711/10000000000000 : ℝ)) half_11_17_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_17_φ1, half_11_17_φ2, half_11_17_φ3, half_11_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_17_φ1, half_11_17_φ2, half_11_17_φ3, half_11_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_17_φ1, half_11_17_φ2, half_11_17_φ3, half_11_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_7 half_9_17
    (by simpa only [half_11_17_φ4, show (2:ℝ)*8=16 by norm_num] using half_11_17_hx4)
  exact h.weaken (by norm_num [half_11_17_φ1, half_11_17_φ2, half_11_17_φ3, half_11_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_11_17_hx2 : SourcePowerBound (powerBoxCross 16 9 4 half_11_17_φ2) (1663159700329/156250000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 9) (u := 7) (t := 10)
    (D := 4) (ψ := (22576474509/625000000000 : ℝ)) half_11_17_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_17_φ1, half_11_17_φ2, half_11_17_φ3, half_11_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_17_φ1, half_11_17_φ2, half_11_17_φ3, half_11_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_17_φ1, half_11_17_φ2, half_11_17_φ3, half_11_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8 half_10_17
    (by simpa only [half_11_17_φ3, show (2:ℝ)*4=8 by norm_num] using half_11_17_hx3)
  exact h.weaken (by norm_num [half_11_17_φ1, half_11_17_φ2, half_11_17_φ3, half_11_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_11_17_hx1 : SourcePowerBound (powerBoxCross 16 10 2 half_11_17_φ1) (59800614164401/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 10) (u := 8) (t := 11)
    (D := 2) (ψ := (101220810017/2500000000000 : ℝ)) half_11_17_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_17_φ1, half_11_17_φ2, half_11_17_φ3, half_11_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_17_φ1, half_11_17_φ2, half_11_17_φ3, half_11_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_17_φ1, half_11_17_φ2, half_11_17_φ3, half_11_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_17 half_11_16
    (by simpa only [half_11_17_φ2, show (2:ℝ)*2=4 by norm_num] using half_11_17_hx2)
  exact h.weaken (by norm_num [half_11_17_φ1, half_11_17_φ2, half_11_17_φ3, half_11_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_11_17 : AdmissibleExponent 16 22 (25534359783263/2000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 9) (ψ := (424766873027/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_10_17
    (by simpa only [half_11_17_φ1] using half_11_17_hx1)
  exact admissibleExponent_mono h (by norm_num [half_11_17_φ1, half_11_17_φ2, half_11_17_φ3, half_11_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_12_17_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (54565700081/1250000000000 : ℝ)

private def half_12_17_φ2 : Fin 2 → ℝ := Fin.snoc half_12_17_φ1 (209764596503/5000000000000 : ℝ)

private def half_12_17_φ3 : Fin 3 → ℝ := Fin.snoc half_12_17_φ2 (192957821737/5000000000000 : ℝ)

private def half_12_17_φ4 : Fin 4 → ℝ := Fin.snoc half_12_17_φ3 (279231980479/10000000000000 : ℝ)

private theorem half_12_17_hF2 : SourcePowerBound (paddedMoment 16 0 2 16 half_12_17_φ4) (14309178241537/2000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_12_17_φ4 (by norm_num [half_12_17_φ1, half_12_17_φ2, half_12_17_φ3, half_12_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_17_φ1, half_12_17_φ2, half_12_17_φ3, half_12_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_17_φ1, half_12_17_φ2, half_12_17_φ3, half_12_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_12_17_φ1, half_12_17_φ2, half_12_17_φ3, half_12_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_12_17_hx4 : SourcePowerBound (powerBoxCross 16 8 16 half_12_17_φ4) (96180375569339/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 16) (s := 8) (r := 2) (v := 10) (w := 11) (D := 16)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_12_17_φ4 (by norm_num [half_12_17_φ1, half_12_17_φ2, half_12_17_φ3, half_12_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_17_φ1, half_12_17_φ2, half_12_17_φ3, half_12_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_12_17_hF2 half_10_17 half_11_17
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_12_17_φ1, half_12_17_φ2, half_12_17_φ3, half_12_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_12_17_hx3 : SourcePowerBound (powerBoxCross 16 9 8 half_12_17_φ3) (105799017361603/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 9) (u := 7) (t := 10)
    (D := 8) (ψ := (279231980479/10000000000000 : ℝ)) half_12_17_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_17_φ1, half_12_17_φ2, half_12_17_φ3, half_12_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_17_φ1, half_12_17_φ2, half_12_17_φ3, half_12_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_17_φ1, half_12_17_φ2, half_12_17_φ3, half_12_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8 half_10_17
    (by simpa only [half_12_17_φ4, show (2:ℝ)*8=16 by norm_num] using half_12_17_hx4)
  exact h.weaken (by norm_num [half_12_17_φ1, half_12_17_φ2, half_12_17_φ3, half_12_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_12_17_hx2 : SourcePowerBound (powerBoxCross 16 10 4 half_12_17_φ2) (59065288691123/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 10) (u := 8) (t := 11)
    (D := 4) (ψ := (192957821737/5000000000000 : ℝ)) half_12_17_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_17_φ1, half_12_17_φ2, half_12_17_φ3, half_12_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_17_φ1, half_12_17_φ2, half_12_17_φ3, half_12_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_17_φ1, half_12_17_φ2, half_12_17_φ3, half_12_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_17 half_11_17
    (by simpa only [half_12_17_φ3, show (2:ℝ)*4=8 by norm_num] using half_12_17_hx3)
  exact h.weaken (by norm_num [half_12_17_φ1, half_12_17_φ2, half_12_17_φ3, half_12_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_12_17_hx1 : SourcePowerBound (powerBoxCross 16 11 2 half_12_17_φ1) (33133780911549/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 11) (u := 9) (t := 12)
    (D := 2) (ψ := (209764596503/5000000000000 : ℝ)) half_12_17_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_17_φ1, half_12_17_φ2, half_12_17_φ3, half_12_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_17_φ1, half_12_17_φ2, half_12_17_φ3, half_12_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_17_φ1, half_12_17_φ2, half_12_17_φ3, half_12_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_17 half_12_16
    (by simpa only [half_12_17_φ2, show (2:ℝ)*2=4 by norm_num] using half_12_17_hx2)
  exact h.weaken (by norm_num [half_12_17_φ1, half_12_17_φ2, half_12_17_φ3, half_12_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_12_17 : AdmissibleExponent 16 24 (35425540314951/2500000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 10) (ψ := (54565700081/1250000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_11_17
    (by simpa only [half_12_17_φ1] using half_12_17_hx1)
  exact admissibleExponent_mono h (by norm_num [half_12_17_φ1, half_12_17_φ2, half_12_17_φ3, half_12_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_13_17_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (112340759139/2500000000000 : ℝ)

private def half_13_17_φ2 : Fin 2 → ℝ := Fin.snoc half_13_17_φ1 (54292971211/1250000000000 : ℝ)

private def half_13_17_φ3 : Fin 3 → ℝ := Fin.snoc half_13_17_φ2 (41337592319/1000000000000 : ℝ)

private def half_13_17_φ4 : Fin 4 → ℝ := Fin.snoc half_13_17_φ3 (72659902327/2000000000000 : ℝ)

private def half_13_17_φ5 : Fin 5 → ℝ := Fin.snoc half_13_17_φ4 (90539511723/5000000000000 : ℝ)

private theorem half_13_17_hF2 : SourcePowerBound (paddedMoment 16 0 2 32 half_13_17_φ5) (3485369723873/400000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_13_17_φ5 (by norm_num [half_13_17_φ1, half_13_17_φ2, half_13_17_φ3, half_13_17_φ4, half_13_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_17_φ1, half_13_17_φ2, half_13_17_φ3, half_13_17_φ4, half_13_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_17_φ1, half_13_17_φ2, half_13_17_φ3, half_13_17_φ4, half_13_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_13_17_φ1, half_13_17_φ2, half_13_17_φ3, half_13_17_φ4, half_13_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_13_17_hF1 : SourcePowerBound (paddedMoment 16 0 1 32 half_13_17_φ5) (1295123241291/400000000000 : ℝ) := by
  have h := padded_second_power (k := 16) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_13_17_φ5 (by norm_num [half_13_17_φ1, half_13_17_φ2, half_13_17_φ3, half_13_17_φ4, half_13_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_17_φ1, half_13_17_φ2, half_13_17_φ3, half_13_17_φ4, half_13_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_17_φ1, half_13_17_φ2, half_13_17_φ3, half_13_17_φ4, half_13_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_13_17_φ1, half_13_17_φ2, half_13_17_φ3, half_13_17_φ4, half_13_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_13_17_hx5 : SourcePowerBound (powerBoxCross 16 8 32 half_13_17_φ5) (96990892124187/10000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 16) (s := 8) (r := 1) (v := 2) (t := 12) (D := 32)
    (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
    (by norm_num) half_13_17_φ5 (by norm_num [half_13_17_φ1, half_13_17_φ2, half_13_17_φ3, half_13_17_φ4, half_13_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_17_φ1, half_13_17_φ2, half_13_17_φ3, half_13_17_φ4, half_13_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_13_17_hF1 half_13_17_hF2 half_12_17
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_13_17_φ1, half_13_17_φ2, half_13_17_φ3, half_13_17_φ4, half_13_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_17_hx4 : SourcePowerBound (powerBoxCross 16 9 16 half_13_17_φ4) (104944681811463/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 4) (s := 9) (u := 7) (t := 10)
    (D := 16) (ψ := (90539511723/5000000000000 : ℝ)) half_13_17_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_17_φ1, half_13_17_φ2, half_13_17_φ3, half_13_17_φ4, half_13_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_17_φ1, half_13_17_φ2, half_13_17_φ3, half_13_17_φ4, half_13_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_17_φ1, half_13_17_φ2, half_13_17_φ3, half_13_17_φ4, half_13_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8 half_10_17
    (by simpa only [half_13_17_φ5, show (2:ℝ)*16=32 by norm_num] using half_13_17_hx5)
  exact h.weaken (by norm_num [half_13_17_φ1, half_13_17_φ2, half_13_17_φ3, half_13_17_φ4, half_13_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_17_hx3 : SourcePowerBound (powerBoxCross 16 10 8 half_13_17_φ3) (58194060735763/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 10) (u := 8) (t := 11)
    (D := 8) (ψ := (72659902327/2000000000000 : ℝ)) half_13_17_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_17_φ1, half_13_17_φ2, half_13_17_φ3, half_13_17_φ4, half_13_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_17_φ1, half_13_17_φ2, half_13_17_φ3, half_13_17_φ4, half_13_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_17_φ1, half_13_17_φ2, half_13_17_φ3, half_13_17_φ4, half_13_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_17 half_11_17
    (by simpa only [half_13_17_φ4, show (2:ℝ)*8=16 by norm_num] using half_13_17_hx4)
  exact h.weaken (by norm_num [half_13_17_φ1, half_13_17_φ2, half_13_17_φ3, half_13_17_φ4, half_13_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_17_hx2 : SourcePowerBound (powerBoxCross 16 11 4 half_13_17_φ2) (65041626685451/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 11) (u := 9) (t := 12)
    (D := 4) (ψ := (41337592319/1000000000000 : ℝ)) half_13_17_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_17_φ1, half_13_17_φ2, half_13_17_φ3, half_13_17_φ4, half_13_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_17_φ1, half_13_17_φ2, half_13_17_φ3, half_13_17_φ4, half_13_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_17_φ1, half_13_17_φ2, half_13_17_φ3, half_13_17_φ4, half_13_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_17 half_12_17
    (by simpa only [half_13_17_φ3, show (2:ℝ)*4=8 by norm_num] using half_13_17_hx3)
  exact h.weaken (by norm_num [half_13_17_φ1, half_13_17_φ2, half_13_17_φ3, half_13_17_φ4, half_13_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_17_hx1 : SourcePowerBound (powerBoxCross 16 12 2 half_13_17_φ1) (145783952949349/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 12) (u := 10) (t := 13)
    (D := 2) (ψ := (54292971211/1250000000000 : ℝ)) half_13_17_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_17_φ1, half_13_17_φ2, half_13_17_φ3, half_13_17_φ4, half_13_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_17_φ1, half_13_17_φ2, half_13_17_φ3, half_13_17_φ4, half_13_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_17_φ1, half_13_17_φ2, half_13_17_φ3, half_13_17_φ4, half_13_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_17 half_13_16
    (by simpa only [half_13_17_φ2, show (2:ℝ)*2=4 by norm_num] using half_13_17_hx2)
  exact h.weaken (by norm_num [half_13_17_φ1, half_13_17_φ2, half_13_17_φ3, half_13_17_φ4, half_13_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_17 : AdmissibleExponent 16 26 (156119302790137/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 11) (ψ := (112340759139/2500000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_12_17
    (by simpa only [half_13_17_φ1] using half_13_17_hx1)
  exact admissibleExponent_mono h (by norm_num [half_13_17_φ1, half_13_17_φ2, half_13_17_φ3, half_13_17_φ4, half_13_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_14_17_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (230407470437/5000000000000 : ℝ)

private def half_14_17_φ2 : Fin 2 → ℝ := Fin.snoc half_14_17_φ1 (446935797511/10000000000000 : ℝ)

private def half_14_17_φ3 : Fin 3 → ℝ := Fin.snoc half_14_17_φ2 (213925766797/5000000000000 : ℝ)

private def half_14_17_φ4 : Fin 4 → ℝ := Fin.snoc half_14_17_φ3 (391200998461/10000000000000 : ℝ)

private def half_14_17_φ5 : Fin 5 → ℝ := Fin.snoc half_14_17_φ4 (275917296789/10000000000000 : ℝ)

private theorem half_14_17_hF2 : SourcePowerBound (paddedMoment 16 0 2 32 half_14_17_φ5) (15975514894939/2000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_14_17_φ5 (by norm_num [half_14_17_φ1, half_14_17_φ2, half_14_17_φ3, half_14_17_φ4, half_14_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_17_φ1, half_14_17_φ2, half_14_17_φ3, half_14_17_φ4, half_14_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_17_φ1, half_14_17_φ2, half_14_17_φ3, half_14_17_φ4, half_14_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_14_17_φ1, half_14_17_φ2, half_14_17_φ3, half_14_17_φ4, half_14_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_14_17_hx5 : SourcePowerBound (powerBoxCross 16 9 32 half_14_17_φ5) (52480888552671/5000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 16) (s := 9) (r := 2) (v := 12) (w := 12) (D := 32)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_14_17_φ5 (by norm_num [half_14_17_φ1, half_14_17_φ2, half_14_17_φ3, half_14_17_φ4, half_14_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_17_φ1, half_14_17_φ2, half_14_17_φ3, half_14_17_φ4, half_14_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_14_17_hF2 half_12_17 half_12_17
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_14_17_φ1, half_14_17_φ2, half_14_17_φ3, half_14_17_φ4, half_14_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_17_hx4 : SourcePowerBound (powerBoxCross 16 10 16 half_14_17_φ4) (114687856509653/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 4) (s := 10) (u := 8) (t := 11)
    (D := 16) (ψ := (275917296789/10000000000000 : ℝ)) half_14_17_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_17_φ1, half_14_17_φ2, half_14_17_φ3, half_14_17_φ4, half_14_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_17_φ1, half_14_17_φ2, half_14_17_φ3, half_14_17_φ4, half_14_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_17_φ1, half_14_17_φ2, half_14_17_φ3, half_14_17_φ4, half_14_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_17 half_11_17
    (by simpa only [half_14_17_φ5, show (2:ℝ)*16=32 by norm_num] using half_14_17_hx5)
  exact h.weaken (by norm_num [half_14_17_φ1, half_14_17_φ2, half_14_17_φ3, half_14_17_φ4, half_14_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_17_hx3 : SourcePowerBound (powerBoxCross 16 11 8 half_14_17_φ3) (3185787872603/250000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 11) (u := 9) (t := 12)
    (D := 8) (ψ := (391200998461/10000000000000 : ℝ)) half_14_17_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_17_φ1, half_14_17_φ2, half_14_17_φ3, half_14_17_φ4, half_14_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_17_φ1, half_14_17_φ2, half_14_17_φ3, half_14_17_φ4, half_14_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_17_φ1, half_14_17_φ2, half_14_17_φ3, half_14_17_φ4, half_14_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_17 half_12_17
    (by simpa only [half_14_17_φ4, show (2:ℝ)*8=16 by norm_num] using half_14_17_hx4)
  exact h.weaken (by norm_num [half_14_17_φ1, half_14_17_φ2, half_14_17_φ3, half_14_17_φ4, half_14_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_17_hx2 : SourcePowerBound (powerBoxCross 16 12 4 half_14_17_φ2) (8898365549549/625000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 12) (u := 10) (t := 13)
    (D := 4) (ψ := (213925766797/5000000000000 : ℝ)) half_14_17_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_17_φ1, half_14_17_φ2, half_14_17_φ3, half_14_17_φ4, half_14_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_17_φ1, half_14_17_φ2, half_14_17_φ3, half_14_17_φ4, half_14_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_17_φ1, half_14_17_φ2, half_14_17_φ3, half_14_17_φ4, half_14_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_17 half_13_17
    (by simpa only [half_14_17_φ3, show (2:ℝ)*4=8 by norm_num] using half_14_17_hx3)
  exact h.weaken (by norm_num [half_14_17_φ1, half_14_17_φ2, half_14_17_φ3, half_14_17_φ4, half_14_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_17_hx1 : SourcePowerBound (powerBoxCross 16 13 2 half_14_17_φ1) (9961619187661/625000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 13) (u := 11) (t := 14)
    (D := 2) (ψ := (446935797511/10000000000000 : ℝ)) half_14_17_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_17_φ1, half_14_17_φ2, half_14_17_φ3, half_14_17_φ4, half_14_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_17_φ1, half_14_17_φ2, half_14_17_φ3, half_14_17_φ4, half_14_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_17_φ1, half_14_17_φ2, half_14_17_φ3, half_14_17_φ4, half_14_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_17 half_14_16
    (by simpa only [half_14_17_φ2, show (2:ℝ)*2=4 by norm_num] using half_14_17_hx2)
  exact h.weaken (by norm_num [half_14_17_φ1, half_14_17_φ2, half_14_17_φ3, half_14_17_φ4, half_14_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_17 : AdmissibleExponent 16 28 (85453140262213/5000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 12) (ψ := (230407470437/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_13_17
    (by simpa only [half_14_17_φ1] using half_14_17_hx1)
  exact admissibleExponent_mono h (by norm_num [half_14_17_φ1, half_14_17_φ2, half_14_17_φ3, half_14_17_φ4, half_14_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_9_18_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (3106374731/78125000000 : ℝ)

private def half_9_18_φ2 : Fin 2 → ℝ := Fin.snoc half_9_18_φ1 (359291709717/10000000000000 : ℝ)

private def half_9_18_φ3 : Fin 3 → ℝ := Fin.snoc half_9_18_φ2 (199230357959/10000000000000 : ℝ)

private theorem half_9_18_hF2 : SourcePowerBound (paddedMoment 16 0 2 8 half_9_18_φ3) (3348689425201/500000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_18_φ3 (by norm_num [half_9_18_φ1, half_9_18_φ2, half_9_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_18_φ1, half_9_18_φ2, half_9_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_18_φ1, half_9_18_φ2, half_9_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_18_φ1, half_9_18_φ2, half_9_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_9_18_hF1 : SourcePowerBound (paddedMoment 16 0 1 8 half_9_18_φ3) (1282896475067/500000000000 : ℝ) := by
  have h := padded_second_power (k := 16) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_18_φ3 (by norm_num [half_9_18_φ1, half_9_18_φ2, half_9_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_18_φ1, half_9_18_φ2, half_9_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_18_φ1, half_9_18_φ2, half_9_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_18_φ1, half_9_18_φ2, half_9_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_9_18_hx3 : SourcePowerBound (powerBoxCross 16 6 8 half_9_18_φ3) (76194774731939/10000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 16) (s := 6) (r := 1) (v := 2) (t := 9) (D := 8)
    (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
    (by norm_num) half_9_18_φ3 (by norm_num [half_9_18_φ1, half_9_18_φ2, half_9_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_18_φ1, half_9_18_φ2, half_9_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_9_18_hF1 half_9_18_hF2 half_9_17
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_9_18_φ1, half_9_18_φ2, half_9_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_18_hx2 : SourcePowerBound (powerBoxCross 16 7 4 half_9_18_φ2) (21035216376287/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 7) (u := 5) (t := 8)
    (D := 4) (ψ := (199230357959/10000000000000 : ℝ)) half_9_18_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_18_φ1, half_9_18_φ2, half_9_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_18_φ1, half_9_18_φ2, half_9_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_18_φ1, half_9_18_φ2, half_9_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_6 SeedCompletionEven16SecondSeeds.degree16_half_8
    (by simpa only [half_9_18_φ3, show (2:ℝ)*4=8 by norm_num] using half_9_18_hx3)
  exact h.weaken (by norm_num [half_9_18_φ1, half_9_18_φ2, half_9_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_18_hx1 : SourcePowerBound (powerBoxCross 16 8 2 half_9_18_φ1) (94804915255397/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 8) (u := 6) (t := 9)
    (D := 2) (ψ := (359291709717/10000000000000 : ℝ)) half_9_18_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_18_φ1, half_9_18_φ2, half_9_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_18_φ1, half_9_18_φ2, half_9_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_18_φ1, half_9_18_φ2, half_9_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_7 half_9_17
    (by simpa only [half_9_18_φ2, show (2:ℝ)*2=4 by norm_num] using half_9_18_hx2)
  exact h.weaken (by norm_num [half_9_18_φ1, half_9_18_φ2, half_9_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_18 : AdmissibleExponent 16 18 (100769154738917/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 7) (ψ := (3106374731/78125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8
    (by simpa only [half_9_18_φ1] using half_9_18_hx1)
  exact admissibleExponent_mono h (by norm_num [half_9_18_φ1, half_9_18_φ2, half_9_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_10_18_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (410254770579/10000000000000 : ℝ)

private def half_10_18_φ2 : Fin 2 → ℝ := Fin.snoc half_10_18_φ1 (191416175443/5000000000000 : ℝ)

private def half_10_18_φ3 : Fin 3 → ℝ := Fin.snoc half_10_18_φ2 (144288954017/5000000000000 : ℝ)

private theorem half_10_18_hF2 : SourcePowerBound (paddedMoment 16 0 2 8 half_10_18_φ3) (12265014734509/2000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_10_18_φ3 (by norm_num [half_10_18_φ1, half_10_18_φ2, half_10_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_18_φ1, half_10_18_φ2, half_10_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_18_φ1, half_10_18_φ2, half_10_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_10_18_φ1, half_10_18_φ2, half_10_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_10_18_hx3 : SourcePowerBound (powerBoxCross 16 7 8 half_10_18_φ3) (8568755536537/1000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 16) (s := 7) (r := 2) (v := 9) (w := 10) (D := 8)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_10_18_φ3 (by norm_num [half_10_18_φ1, half_10_18_φ2, half_10_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_18_φ1, half_10_18_φ2, half_10_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_10_18_hF2 half_9_18 half_10_17
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_10_18_φ1, half_10_18_φ2, half_10_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_10_18_hx2 : SourcePowerBound (powerBoxCross 16 8 4 half_10_18_φ2) (297375069063/31250000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 8) (u := 6) (t := 9)
    (D := 4) (ψ := (144288954017/5000000000000 : ℝ)) half_10_18_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_18_φ1, half_10_18_φ2, half_10_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_18_φ1, half_10_18_φ2, half_10_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_18_φ1, half_10_18_φ2, half_10_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_7 half_9_18
    (by simpa only [half_10_18_φ3, show (2:ℝ)*4=8 by norm_num] using half_10_18_hx3)
  exact h.weaken (by norm_num [half_10_18_φ1, half_10_18_φ2, half_10_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_10_18_hx1 : SourcePowerBound (powerBoxCross 16 9 2 half_10_18_φ1) (856362454909/80000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 9) (u := 7) (t := 10)
    (D := 2) (ψ := (191416175443/5000000000000 : ℝ)) half_10_18_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_18_φ1, half_10_18_φ2, half_10_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_18_φ1, half_10_18_φ2, half_10_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_18_φ1, half_10_18_φ2, half_10_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8 half_10_17
    (by simpa only [half_10_18_φ2, show (2:ℝ)*2=4 by norm_num] using half_10_18_hx2)
  exact h.weaken (by norm_num [half_10_18_φ1, half_10_18_φ2, half_10_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_10_18 : AdmissibleExponent 16 20 (28504909490867/2500000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 8) (ψ := (410254770579/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_9_18
    (by simpa only [half_10_18_φ1] using half_10_18_hx1)
  exact admissibleExponent_mono h (by norm_num [half_10_18_φ1, half_10_18_φ2, half_10_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_11_18_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (212383436299/5000000000000 : ℝ)

private def half_11_18_φ2 : Fin 2 → ℝ := Fin.snoc half_11_18_φ1 (404883240049/10000000000000 : ℝ)

private def half_11_18_φ3 : Fin 3 → ℝ := Fin.snoc half_11_18_φ2 (180611796053/5000000000000 : ℝ)

private def half_11_18_φ4 : Fin 4 → ℝ := Fin.snoc half_11_18_φ3 (92020243261/5000000000000 : ℝ)

private theorem half_11_18_hF2 : SourcePowerBound (paddedMoment 16 0 2 16 half_11_18_φ4) (625030891141/80000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_11_18_φ4 (by norm_num [half_11_18_φ1, half_11_18_φ2, half_11_18_φ3, half_11_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_18_φ1, half_11_18_φ2, half_11_18_φ3, half_11_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_18_φ1, half_11_18_φ2, half_11_18_φ3, half_11_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_11_18_φ1, half_11_18_φ2, half_11_18_φ3, half_11_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_11_18_hF1 : SourcePowerBound (paddedMoment 16 0 1 16 half_11_18_φ4) (235010297047/80000000000 : ℝ) := by
  have h := padded_second_power (k := 16) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_11_18_φ4 (by norm_num [half_11_18_φ1, half_11_18_φ2, half_11_18_φ3, half_11_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_18_φ1, half_11_18_φ2, half_11_18_φ3, half_11_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_18_φ1, half_11_18_φ2, half_11_18_φ3, half_11_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_11_18_φ1, half_11_18_φ2, half_11_18_φ3, half_11_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_11_18_hx4 : SourcePowerBound (powerBoxCross 16 7 16 half_11_18_φ4) (2185086057091/250000000000 : ℝ) := by
  have h := full_B_cross_power (k := 16) (s := 7) (r := 1) (v := 2) (t := 10) (D := 16)
    (a := (1/10 : ℝ)) (b := (1/5 : ℝ)) (c := (7/10 : ℝ))
    (by norm_num) half_11_18_φ4 (by norm_num [half_11_18_φ1, half_11_18_φ2, half_11_18_φ3, half_11_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_18_φ1, half_11_18_φ2, half_11_18_φ3, half_11_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_11_18_hF1 half_11_18_hF2 half_10_18
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_11_18_φ1, half_11_18_φ2, half_11_18_φ3, half_11_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_11_18_hx3 : SourcePowerBound (powerBoxCross 16 8 8 half_11_18_φ3) (47675421028293/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 8) (u := 6) (t := 9)
    (D := 8) (ψ := (92020243261/5000000000000 : ℝ)) half_11_18_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_18_φ1, half_11_18_φ2, half_11_18_φ3, half_11_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_18_φ1, half_11_18_φ2, half_11_18_φ3, half_11_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_18_φ1, half_11_18_φ2, half_11_18_φ3, half_11_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_7 half_9_18
    (by simpa only [half_11_18_φ4, show (2:ℝ)*8=16 by norm_num] using half_11_18_hx4)
  exact h.weaken (by norm_num [half_11_18_φ1, half_11_18_φ2, half_11_18_φ3, half_11_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_11_18_hx2 : SourcePowerBound (powerBoxCross 16 9 4 half_11_18_φ2) (6652638801997/625000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 9) (u := 7) (t := 10)
    (D := 4) (ψ := (180611796053/5000000000000 : ℝ)) half_11_18_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_18_φ1, half_11_18_φ2, half_11_18_φ3, half_11_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_18_φ1, half_11_18_φ2, half_11_18_φ3, half_11_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_18_φ1, half_11_18_φ2, half_11_18_φ3, half_11_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8 half_10_18
    (by simpa only [half_11_18_φ3, show (2:ℝ)*4=8 by norm_num] using half_11_18_hx3)
  exact h.weaken (by norm_num [half_11_18_φ1, half_11_18_φ2, half_11_18_φ3, half_11_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_11_18_hx1 : SourcePowerBound (powerBoxCross 16 10 2 half_11_18_φ1) (119601228332833/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 10) (u := 8) (t := 11)
    (D := 2) (ψ := (404883240049/10000000000000 : ℝ)) half_11_18_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_18_φ1, half_11_18_φ2, half_11_18_φ3, half_11_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_18_φ1, half_11_18_φ2, half_11_18_φ3, half_11_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_18_φ1, half_11_18_φ2, half_11_18_φ3, half_11_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_18 half_11_17
    (by simpa only [half_11_18_φ2, show (2:ℝ)*2=4 by norm_num] using half_11_18_hx2)
  exact h.weaken (by norm_num [half_11_18_φ1, half_11_18_φ2, half_11_18_φ3, half_11_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_11_18 : AdmissibleExponent 16 22 (25534359782439/2000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 9) (ψ := (212383436299/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_10_18
    (by simpa only [half_11_18_φ1] using half_11_18_hx1)
  exact admissibleExponent_mono h (by norm_num [half_11_18_φ1, half_11_18_φ2, half_11_18_φ3, half_11_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_12_18_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (218262798881/5000000000000 : ℝ)

private def half_12_18_φ2 : Fin 2 → ℝ := Fin.snoc half_12_18_φ1 (20976459643/500000000000 : ℝ)

private def half_12_18_φ3 : Fin 3 → ℝ := Fin.snoc half_12_18_φ2 (385915643243/10000000000000 : ℝ)

private def half_12_18_φ4 : Fin 4 → ℝ := Fin.snoc half_12_18_φ3 (69807994871/2500000000000 : ℝ)

private theorem half_12_18_hF2 : SourcePowerBound (paddedMoment 16 0 2 16 half_12_18_φ4) (14309178279859/2000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_12_18_φ4 (by norm_num [half_12_18_φ1, half_12_18_φ2, half_12_18_φ3, half_12_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_18_φ1, half_12_18_φ2, half_12_18_φ3, half_12_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_18_φ1, half_12_18_φ2, half_12_18_φ3, half_12_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_12_18_φ1, half_12_18_φ2, half_12_18_φ3, half_12_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_12_18_hx4 : SourcePowerBound (powerBoxCross 16 8 16 half_12_18_φ4) (96180375654717/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 16) (s := 8) (r := 2) (v := 10) (w := 11) (D := 16)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_12_18_φ4 (by norm_num [half_12_18_φ1, half_12_18_φ2, half_12_18_φ3, half_12_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_18_φ1, half_12_18_φ2, half_12_18_φ3, half_12_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_12_18_hF2 half_10_18 half_11_18
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_12_18_φ1, half_12_18_φ2, half_12_18_φ3, half_12_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_12_18_hx3 : SourcePowerBound (powerBoxCross 16 9 8 half_12_18_φ3) (21159803487941/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 9) (u := 7) (t := 10)
    (D := 8) (ψ := (69807994871/2500000000000 : ℝ)) half_12_18_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_18_φ1, half_12_18_φ2, half_12_18_φ3, half_12_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_18_φ1, half_12_18_φ2, half_12_18_φ3, half_12_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_18_φ1, half_12_18_φ2, half_12_18_φ3, half_12_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8 half_10_18
    (by simpa only [half_12_18_φ4, show (2:ℝ)*8=16 by norm_num] using half_12_18_hx4)
  exact h.weaken (by norm_num [half_12_18_φ1, half_12_18_φ2, half_12_18_φ3, half_12_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_12_18_hx2 : SourcePowerBound (powerBoxCross 16 10 4 half_12_18_φ2) (23626115491909/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 10) (u := 8) (t := 11)
    (D := 4) (ψ := (385915643243/10000000000000 : ℝ)) half_12_18_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_18_φ1, half_12_18_φ2, half_12_18_φ3, half_12_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_18_φ1, half_12_18_φ2, half_12_18_φ3, half_12_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_18_φ1, half_12_18_φ2, half_12_18_φ3, half_12_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_18 half_11_18
    (by simpa only [half_12_18_φ3, show (2:ℝ)*4=8 by norm_num] using half_12_18_hx3)
  exact h.weaken (by norm_num [half_12_18_φ1, half_12_18_φ2, half_12_18_φ3, half_12_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_12_18_hx1 : SourcePowerBound (powerBoxCross 16 11 2 half_12_18_φ1) (5301404947049/400000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 11) (u := 9) (t := 12)
    (D := 2) (ψ := (20976459643/500000000000 : ℝ)) half_12_18_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_18_φ1, half_12_18_φ2, half_12_18_φ3, half_12_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_18_φ1, half_12_18_φ2, half_12_18_φ3, half_12_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_18_φ1, half_12_18_φ2, half_12_18_φ3, half_12_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_18 half_12_17
    (by simpa only [half_12_18_φ2, show (2:ℝ)*2=4 by norm_num] using half_12_18_hx2)
  exact h.weaken (by norm_num [half_12_18_φ1, half_12_18_φ2, half_12_18_φ3, half_12_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_12_18 : AdmissibleExponent 16 24 (141702161229227/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 10) (ψ := (218262798881/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_11_18
    (by simpa only [half_12_18_φ1] using half_12_18_hx1)
  exact admissibleExponent_mono h (by norm_num [half_12_18_φ1, half_12_18_φ2, half_12_18_φ3, half_12_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_13_18_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (224681510917/5000000000000 : ℝ)

private def half_13_18_φ2 : Fin 2 → ℝ := Fin.snoc half_13_18_φ1 (10858594223/250000000000 : ℝ)

private def half_13_18_φ3 : Fin 3 → ℝ := Fin.snoc half_13_18_φ2 (16535036907/400000000000 : ℝ)

private def half_13_18_φ4 : Fin 4 → ℝ := Fin.snoc half_13_18_φ3 (363299509829/10000000000000 : ℝ)

private def half_13_18_φ5 : Fin 5 → ℝ := Fin.snoc half_13_18_φ4 (181079015383/10000000000000 : ℝ)

private theorem half_13_18_hF2 : SourcePowerBound (paddedMoment 16 0 2 32 half_13_18_φ5) (17426848852231/2000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_13_18_φ5 (by norm_num [half_13_18_φ1, half_13_18_φ2, half_13_18_φ3, half_13_18_φ4, half_13_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_18_φ1, half_13_18_φ2, half_13_18_φ3, half_13_18_φ4, half_13_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_18_φ1, half_13_18_φ2, half_13_18_φ3, half_13_18_φ4, half_13_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_13_18_φ1, half_13_18_φ2, half_13_18_φ3, half_13_18_φ4, half_13_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_13_18_hF1 : SourcePowerBound (paddedMoment 16 0 1 32 half_13_18_φ5) (6475616284077/2000000000000 : ℝ) := by
  have h := padded_second_power (k := 16) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_13_18_φ5 (by norm_num [half_13_18_φ1, half_13_18_φ2, half_13_18_φ3, half_13_18_φ4, half_13_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_18_φ1, half_13_18_φ2, half_13_18_φ3, half_13_18_φ4, half_13_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_18_φ1, half_13_18_φ2, half_13_18_φ3, half_13_18_φ4, half_13_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_13_18_φ1, half_13_18_φ2, half_13_18_φ3, half_13_18_φ4, half_13_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_13_18_hx5 : SourcePowerBound (powerBoxCross 16 8 32 half_13_18_φ5) (96990892610723/10000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 16) (s := 8) (r := 1) (v := 2) (t := 12) (D := 32)
    (a := (1/6 : ℝ)) (b := (1/6 : ℝ)) (c := (2/3 : ℝ))
    (by norm_num) half_13_18_φ5 (by norm_num [half_13_18_φ1, half_13_18_φ2, half_13_18_φ3, half_13_18_φ4, half_13_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_18_φ1, half_13_18_φ2, half_13_18_φ3, half_13_18_φ4, half_13_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_13_18_hF1 half_13_18_hF2 half_12_18
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_13_18_φ1, half_13_18_φ2, half_13_18_φ3, half_13_18_φ4, half_13_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_18_hx4 : SourcePowerBound (powerBoxCross 16 9 16 half_13_18_φ4) (104944682229191/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 4) (s := 9) (u := 7) (t := 10)
    (D := 16) (ψ := (181079015383/10000000000000 : ℝ)) half_13_18_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_18_φ1, half_13_18_φ2, half_13_18_φ3, half_13_18_φ4, half_13_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_18_φ1, half_13_18_φ2, half_13_18_φ3, half_13_18_φ4, half_13_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_18_φ1, half_13_18_φ2, half_13_18_φ3, half_13_18_φ4, half_13_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven16SecondSeeds.degree16_half_8 half_10_18
    (by simpa only [half_13_18_φ5, show (2:ℝ)*16=32 by norm_num] using half_13_18_hx5)
  exact h.weaken (by norm_num [half_13_18_φ1, half_13_18_φ2, half_13_18_φ3, half_13_18_φ4, half_13_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_18_hx3 : SourcePowerBound (powerBoxCross 16 10 8 half_13_18_φ3) (116388121885453/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 10) (u := 8) (t := 11)
    (D := 8) (ψ := (363299509829/10000000000000 : ℝ)) half_13_18_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_18_φ1, half_13_18_φ2, half_13_18_φ3, half_13_18_φ4, half_13_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_18_φ1, half_13_18_φ2, half_13_18_φ3, half_13_18_φ4, half_13_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_18_φ1, half_13_18_φ2, half_13_18_φ3, half_13_18_φ4, half_13_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_18 half_11_18
    (by simpa only [half_13_18_φ4, show (2:ℝ)*8=16 by norm_num] using half_13_18_hx4)
  exact h.weaken (by norm_num [half_13_18_φ1, half_13_18_φ2, half_13_18_φ3, half_13_18_φ4, half_13_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_18_hx2 : SourcePowerBound (powerBoxCross 16 11 4 half_13_18_φ2) (130083253784959/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 11) (u := 9) (t := 12)
    (D := 4) (ψ := (16535036907/400000000000 : ℝ)) half_13_18_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_18_φ1, half_13_18_φ2, half_13_18_φ3, half_13_18_φ4, half_13_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_18_φ1, half_13_18_φ2, half_13_18_φ3, half_13_18_φ4, half_13_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_18_φ1, half_13_18_φ2, half_13_18_φ3, half_13_18_φ4, half_13_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_18 half_12_18
    (by simpa only [half_13_18_φ3, show (2:ℝ)*4=8 by norm_num] using half_13_18_hx3)
  exact h.weaken (by norm_num [half_13_18_φ1, half_13_18_φ2, half_13_18_φ3, half_13_18_φ4, half_13_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_18_hx1 : SourcePowerBound (powerBoxCross 16 12 2 half_13_18_φ1) (72891976557017/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 12) (u := 10) (t := 13)
    (D := 2) (ψ := (10858594223/250000000000 : ℝ)) half_13_18_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_18_φ1, half_13_18_φ2, half_13_18_φ3, half_13_18_φ4, half_13_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_18_φ1, half_13_18_φ2, half_13_18_φ3, half_13_18_φ4, half_13_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_18_φ1, half_13_18_φ2, half_13_18_φ3, half_13_18_φ4, half_13_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_18 half_13_17
    (by simpa only [half_13_18_φ2, show (2:ℝ)*2=4 by norm_num] using half_13_18_hx2)
  exact h.weaken (by norm_num [half_13_18_φ1, half_13_18_φ2, half_13_18_φ3, half_13_18_φ4, half_13_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_13_18 : AdmissibleExponent 16 26 (19514912827027/1250000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 11) (ψ := (224681510917/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_12_18
    (by simpa only [half_13_18_φ1] using half_13_18_hx1)
  exact admissibleExponent_mono h (by norm_num [half_13_18_φ1, half_13_18_φ2, half_13_18_φ3, half_13_18_φ4, half_13_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_14_18_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (460814880109/10000000000000 : ℝ)

private def half_14_18_φ2 : Fin 2 → ℝ := Fin.snoc half_14_18_φ1 (71509727/1600000000 : ℝ)

private def half_14_18_φ3 : Fin 3 → ℝ := Fin.snoc half_14_18_φ2 (21392576589/500000000000 : ℝ)

private def half_14_18_φ4 : Fin 4 → ℝ := Fin.snoc half_14_18_φ3 (391200993713/10000000000000 : ℝ)

private def half_14_18_φ5 : Fin 5 → ℝ := Fin.snoc half_14_18_φ4 (34489659699/1250000000000 : ℝ)

private theorem half_14_18_hF2 : SourcePowerBound (paddedMoment 16 0 2 32 half_14_18_φ5) (998469731719/125000000000 : ℝ) := by
  have h := padded_fourth_power (k := 16) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_14_18_φ5 (by norm_num [half_14_18_φ1, half_14_18_φ2, half_14_18_φ3, half_14_18_φ4, half_14_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_18_φ1, half_14_18_φ2, half_14_18_φ3, half_14_18_φ4, half_14_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_18_φ1, half_14_18_φ2, half_14_18_φ3, half_14_18_φ4, half_14_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_14_18_φ1, half_14_18_φ2, half_14_18_φ3, half_14_18_φ4, half_14_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_14_18_hx5 : SourcePowerBound (powerBoxCross 16 9 32 half_14_18_φ5) (52480889531113/5000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 16) (s := 9) (r := 2) (v := 12) (w := 12) (D := 32)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_14_18_φ5 (by norm_num [half_14_18_φ1, half_14_18_φ2, half_14_18_φ3, half_14_18_φ4, half_14_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_18_φ1, half_14_18_φ2, half_14_18_φ3, half_14_18_φ4, half_14_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_14_18_hF2 half_12_18 half_12_18
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_14_18_φ1, half_14_18_φ2, half_14_18_φ3, half_14_18_φ4, half_14_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_18_hx4 : SourcePowerBound (powerBoxCross 16 10 16 half_14_18_φ4) (3583995572193/312500000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 4) (s := 10) (u := 8) (t := 11)
    (D := 16) (ψ := (34489659699/1250000000000 : ℝ)) half_14_18_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_18_φ1, half_14_18_φ2, half_14_18_φ3, half_14_18_φ4, half_14_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_18_φ1, half_14_18_φ2, half_14_18_φ3, half_14_18_φ4, half_14_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_18_φ1, half_14_18_φ2, half_14_18_φ3, half_14_18_φ4, half_14_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_18 half_11_18
    (by simpa only [half_14_18_φ5, show (2:ℝ)*16=32 by norm_num] using half_14_18_hx5)
  exact h.weaken (by norm_num [half_14_18_φ1, half_14_18_φ2, half_14_18_φ3, half_14_18_φ4, half_14_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_18_hx3 : SourcePowerBound (powerBoxCross 16 11 8 half_14_18_φ3) (25486303342721/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 11) (u := 9) (t := 12)
    (D := 8) (ψ := (391200993713/10000000000000 : ℝ)) half_14_18_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_18_φ1, half_14_18_φ2, half_14_18_φ3, half_14_18_φ4, half_14_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_18_φ1, half_14_18_φ2, half_14_18_φ3, half_14_18_φ4, half_14_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_18_φ1, half_14_18_φ2, half_14_18_φ3, half_14_18_φ4, half_14_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_18 half_12_18
    (by simpa only [half_14_18_φ4, show (2:ℝ)*8=16 by norm_num] using half_14_18_hx4)
  exact h.weaken (by norm_num [half_14_18_φ1, half_14_18_φ2, half_14_18_φ3, half_14_18_φ4, half_14_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_18_hx2 : SourcePowerBound (powerBoxCross 16 12 4 half_14_18_φ2) (28474770117409/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 12) (u := 10) (t := 13)
    (D := 4) (ψ := (21392576589/500000000000 : ℝ)) half_14_18_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_18_φ1, half_14_18_φ2, half_14_18_φ3, half_14_18_φ4, half_14_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_18_φ1, half_14_18_φ2, half_14_18_φ3, half_14_18_φ4, half_14_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_18_φ1, half_14_18_φ2, half_14_18_φ3, half_14_18_φ4, half_14_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_18 half_13_18
    (by simpa only [half_14_18_φ3, show (2:ℝ)*4=8 by norm_num] using half_14_18_hx3)
  exact h.weaken (by norm_num [half_14_18_φ1, half_14_18_φ2, half_14_18_φ3, half_14_18_φ4, half_14_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_18_hx1 : SourcePowerBound (powerBoxCross 16 13 2 half_14_18_φ1) (159385907724557/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 13) (u := 11) (t := 14)
    (D := 2) (ψ := (71509727/1600000000 : ℝ)) half_14_18_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_18_φ1, half_14_18_φ2, half_14_18_φ3, half_14_18_φ4, half_14_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_18_φ1, half_14_18_φ2, half_14_18_φ3, half_14_18_φ4, half_14_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_18_φ1, half_14_18_φ2, half_14_18_φ3, half_14_18_φ4, half_14_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_18 half_14_17
    (by simpa only [half_14_18_φ2, show (2:ℝ)*2=4 by norm_num] using half_14_18_hx2)
  exact h.weaken (by norm_num [half_14_18_φ1, half_14_18_φ2, half_14_18_φ3, half_14_18_φ4, half_14_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_14_18 : AdmissibleExponent 16 28 (85453139863641/5000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 12) (ψ := (460814880109/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_13_18
    (by simpa only [half_14_18_φ1] using half_14_18_hx1)
  exact admissibleExponent_mono h (by norm_num [half_14_18_φ1, half_14_18_φ2, half_14_18_φ3, half_14_18_φ4, half_14_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem degree16_half_9 : AdmissibleExponent 16 18 (100769154738917/10000000000000 : ℝ) := half_9_18

theorem source16_entry_9 : AdmissibleExponent 16 18 (Certificate.coefficientSource8[9]! : ℝ) := by
  apply admissibleExponent_mono degree16_half_9
  norm_num [Certificate.coefficientSource8,Certificate.Q]

#print axioms source16_entry_9

theorem degree16_half_10 : AdmissibleExponent 16 20 (28504909490867/2500000000000 : ℝ) := half_10_18

theorem source16_entry_10 : AdmissibleExponent 16 20 (Certificate.coefficientSource8[10]! : ℝ) := by
  apply admissibleExponent_mono degree16_half_10
  norm_num [Certificate.coefficientSource8,Certificate.Q]

#print axioms source16_entry_10

theorem degree16_half_11 : AdmissibleExponent 16 22 (25534359782439/2000000000000 : ℝ) := half_11_18

theorem source16_entry_11 : AdmissibleExponent 16 22 (Certificate.coefficientSource8[11]! : ℝ) := by
  apply admissibleExponent_mono degree16_half_11
  norm_num [Certificate.coefficientSource8,Certificate.Q]

#print axioms source16_entry_11

theorem degree16_half_12 : AdmissibleExponent 16 24 (141702161229227/10000000000000 : ℝ) := half_12_18

theorem source16_entry_12 : AdmissibleExponent 16 24 (Certificate.coefficientSource8[12]! : ℝ) := by
  apply admissibleExponent_mono degree16_half_12
  norm_num [Certificate.coefficientSource8,Certificate.Q]

#print axioms source16_entry_12

theorem degree16_half_13 : AdmissibleExponent 16 26 (19514912827027/1250000000000 : ℝ) := half_13_18

theorem source16_entry_13 : AdmissibleExponent 16 26 (Certificate.coefficientSource8[13]! : ℝ) := by
  apply admissibleExponent_mono degree16_half_13
  norm_num [Certificate.coefficientSource8,Certificate.Q]

#print axioms source16_entry_13

theorem degree16_half_14 : AdmissibleExponent 16 28 (85453139863641/5000000000000 : ℝ) := half_14_18

theorem source16_entry_14 : AdmissibleExponent 16 28 (Certificate.coefficientSource8[14]! : ℝ) := by
  apply admissibleExponent_mono degree16_half_14
  norm_num [Certificate.coefficientSource8,Certificate.Q]

#print axioms source16_entry_14

end Waring.SeedCompletionHigher16SimpleSeeds
