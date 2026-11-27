import Waring.SeedCompletionHigher18SimpleSeedsC07

noncomputable section
set_option maxHeartbeats 2000000
namespace Waring.SeedCompletionHigher18SimpleSeeds
open SmoothMoments FirstStageTransport SeedCompletionNaturalBox
open SeedCompletionSourceBounds SeedCompletionPaddedSource SeedCompletionGeneralTerminal
open PolicyCompletionMajorPowerRanges

def half_9_08_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (343841027493/10000000000000 : ℝ)

def half_9_08_φ2 : Fin 2 → ℝ := Fin.snoc half_9_08_φ1 (308347748157/10000000000000 : ℝ)

def half_9_08_φ3 : Fin 3 → ℝ := Fin.snoc half_9_08_φ2 (134462359077/10000000000000 : ℝ)

theorem half_9_08_hF2 : SourcePowerBound (paddedMoment 18 0 2 8 half_9_08_φ3) (69880792128923/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_08_φ3 (by norm_num [half_9_08_φ1, half_9_08_φ2, half_9_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_08_φ1, half_9_08_φ2, half_9_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_08_φ1, half_9_08_φ2, half_9_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_08_φ1, half_9_08_φ2, half_9_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_9_08_hF1 : SourcePowerBound (paddedMoment 18 0 1 8 half_9_08_φ3) (26626930709641/10000000000000 : ℝ) := by
  have h := padded_second_power (k := 18) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_08_φ3 (by norm_num [half_9_08_φ1, half_9_08_φ2, half_9_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_08_φ1, half_9_08_φ2, half_9_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_08_φ1, half_9_08_φ2, half_9_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_08_φ1, half_9_08_φ2, half_9_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_9_08_hx3 : SourcePowerBound (powerBoxCross 18 6 8 half_9_08_φ3) (38496419128311/5000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 18) (s := 6) (r := 1) (v := 2) (t := 10) (D := 8)
    (a := (3/10 : ℝ)) (b := (1/10 : ℝ)) (c := (3/5 : ℝ))
    (by norm_num) half_9_08_φ3 (by norm_num [half_9_08_φ1, half_9_08_φ2, half_9_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_08_φ1, half_9_08_φ2, half_9_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_9_08_hF1 half_9_08_hF2 half_10_07
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_9_08_φ1, half_9_08_φ2, half_9_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_9_08_hx2 : SourcePowerBound (powerBoxCross 18 7 4 half_9_08_φ2) (42134675595053/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 7) (u := 5) (t := 8)
    (D := 4) (ψ := (134462359077/10000000000000 : ℝ)) half_9_08_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_08_φ1, half_9_08_φ2, half_9_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_08_φ1, half_9_08_φ2, half_9_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_08_φ1, half_9_08_φ2, half_9_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_6 SeedCompletionEven18SecondSeeds.degree18_half_8
    (by simpa only [half_9_08_φ3, show (2:ℝ)*4=8 by norm_num] using half_9_08_hx3)
  exact h.weaken (by norm_num [half_9_08_φ1, half_9_08_φ2, half_9_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_9_08_hx1 : SourcePowerBound (powerBoxCross 18 8 2 half_9_08_φ1) (94174781168623/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 8) (u := 6) (t := 9)
    (D := 2) (ψ := (308347748157/10000000000000 : ℝ)) half_9_08_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_08_φ1, half_9_08_φ2, half_9_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_08_φ1, half_9_08_φ2, half_9_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_08_φ1, half_9_08_φ2, half_9_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_7 half_9_07
    (by simpa only [half_9_08_φ2, show (2:ℝ)*2=4 by norm_num] using half_9_08_hx2)
  exact h.weaken (by norm_num [half_9_08_φ1, half_9_08_φ2, half_9_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_9_08 : AdmissibleExponent 18 18 (49666198290509/5000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 7) (ψ := (343841027493/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_8
    (by simpa only [half_9_08_φ1] using half_9_08_hx1)
  exact admissibleExponent_mono h (by norm_num [half_9_08_φ1, half_9_08_φ2, half_9_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_10_08_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (176878075303/5000000000000 : ℝ)

def half_10_08_φ2 : Fin 2 → ℝ := Fin.snoc half_10_08_φ1 (329258386649/10000000000000 : ℝ)

def half_10_08_φ3 : Fin 3 → ℝ := Fin.snoc half_10_08_φ2 (114973285361/5000000000000 : ℝ)

theorem half_10_08_hF2 : SourcePowerBound (paddedMoment 18 0 2 8 half_10_08_φ3) (63438983493173/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_10_08_φ3 (by norm_num [half_10_08_φ1, half_10_08_φ2, half_10_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_08_φ1, half_10_08_φ2, half_10_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_08_φ1, half_10_08_φ2, half_10_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_10_08_φ1, half_10_08_φ2, half_10_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_10_08_hx3 : SourcePowerBound (powerBoxCross 18 7 8 half_10_08_φ3) (86477640535697/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 7) (r := 2) (v := 9) (w := 10) (D := 8)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_10_08_φ3 (by norm_num [half_10_08_φ1, half_10_08_φ2, half_10_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_08_φ1, half_10_08_φ2, half_10_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_10_08_hF2 half_9_08 half_10_07
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_10_08_φ1, half_10_08_φ2, half_10_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_08_hx2 : SourcePowerBound (powerBoxCross 18 8 4 half_10_08_φ2) (95201774157123/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 8) (u := 6) (t := 9)
    (D := 4) (ψ := (114973285361/5000000000000 : ℝ)) half_10_08_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_08_φ1, half_10_08_φ2, half_10_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_08_φ1, half_10_08_φ2, half_10_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_08_φ1, half_10_08_φ2, half_10_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_7 half_9_08
    (by simpa only [half_10_08_φ3, show (2:ℝ)*4=8 by norm_num] using half_10_08_hx3)
  exact h.weaken (by norm_num [half_10_08_φ1, half_10_08_φ2, half_10_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_08_hx1 : SourcePowerBound (powerBoxCross 18 9 2 half_10_08_φ1) (21234441621427/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 9) (u := 7) (t := 10)
    (D := 2) (ψ := (329258386649/10000000000000 : ℝ)) half_10_08_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_08_φ1, half_10_08_φ2, half_10_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_08_φ1, half_10_08_φ2, half_10_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_08_φ1, half_10_08_φ2, half_10_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_8 half_10_07
    (by simpa only [half_10_08_φ2, show (2:ℝ)*2=4 by norm_num] using half_10_08_hx2)
  exact h.weaken (by norm_num [half_10_08_φ1, half_10_08_φ2, half_10_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_08 : AdmissibleExponent 18 20 (112186062667437/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 8) (ψ := (176878075303/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_9_08
    (by simpa only [half_10_08_φ1] using half_10_08_hx1)
  exact admissibleExponent_mono h (by norm_num [half_10_08_φ1, half_10_08_φ2, half_10_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_11_08_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (182391893283/5000000000000 : ℝ)

def half_11_08_φ2 : Fin 2 → ℝ := Fin.snoc half_11_08_φ1 (34640761863/1000000000000 : ℝ)

def half_11_08_φ3 : Fin 3 → ℝ := Fin.snoc half_11_08_φ2 (5895722459/200000000000 : ℝ)

theorem half_11_08_hF2 : SourcePowerBound (paddedMoment 18 0 2 8 half_11_08_φ3) (29347573032277/5000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_11_08_φ3 (by norm_num [half_11_08_φ1, half_11_08_φ2, half_11_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_08_φ1, half_11_08_φ2, half_11_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_08_φ1, half_11_08_φ2, half_11_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_11_08_φ1, half_11_08_φ2, half_11_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_11_08_hx3 : SourcePowerBound (powerBoxCross 18 8 8 half_11_08_φ3) (3851482641869/400000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 8) (r := 2) (v := 10) (w := 11) (D := 8)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_11_08_φ3 (by norm_num [half_11_08_φ1, half_11_08_φ2, half_11_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_08_φ1, half_11_08_φ2, half_11_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_11_08_hF2 half_10_08 half_11_07
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_11_08_φ1, half_11_08_φ2, half_11_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_08_hx2 : SourcePowerBound (powerBoxCross 18 9 4 half_11_08_φ2) (106413045157447/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 9) (u := 7) (t := 10)
    (D := 4) (ψ := (5895722459/200000000000 : ℝ)) half_11_08_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_08_φ1, half_11_08_φ2, half_11_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_08_φ1, half_11_08_φ2, half_11_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_08_φ1, half_11_08_φ2, half_11_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_8 half_10_08
    (by simpa only [half_11_08_φ3, show (2:ℝ)*4=8 by norm_num] using half_11_08_hx3)
  exact h.weaken (by norm_num [half_11_08_φ1, half_11_08_φ2, half_11_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_08_hx1 : SourcePowerBound (powerBoxCross 18 10 2 half_11_08_φ1) (23691696156007/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 10) (u := 8) (t := 11)
    (D := 2) (ψ := (34640761863/1000000000000 : ℝ)) half_11_08_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_08_φ1, half_11_08_φ2, half_11_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_08_φ1, half_11_08_φ2, half_11_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_08_φ1, half_11_08_φ2, half_11_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_08 half_11_07
    (by simpa only [half_11_08_φ2, show (2:ℝ)*2=4 by norm_num] using half_11_08_hx2)
  exact h.weaken (by norm_num [half_11_08_φ1, half_11_08_φ2, half_11_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_08 : AdmissibleExponent 18 22 (125389372724789/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 9) (ψ := (182391893283/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_10_08
    (by simpa only [half_11_08_φ1] using half_11_08_hx1)
  exact admissibleExponent_mono h (by norm_num [half_11_08_φ1, half_11_08_φ2, half_11_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_12_08_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (375030341569/10000000000000 : ℝ)

def half_12_08_φ2 : Fin 2 → ℝ := Fin.snoc half_12_08_φ1 (90148940751/2500000000000 : ℝ)

def half_12_08_φ3 : Fin 3 → ℝ := Fin.snoc half_12_08_φ2 (329441325613/10000000000000 : ℝ)

def half_12_08_φ4 : Fin 4 → ℝ := Fin.snoc half_12_08_φ3 (212958054959/10000000000000 : ℝ)

theorem half_12_08_hF2 : SourcePowerBound (paddedMoment 18 0 2 16 half_12_08_φ4) (14964140051521/2000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_12_08_φ4 (by norm_num [half_12_08_φ1, half_12_08_φ2, half_12_08_φ3, half_12_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_08_φ1, half_12_08_φ2, half_12_08_φ3, half_12_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_08_φ1, half_12_08_φ2, half_12_08_φ3, half_12_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_12_08_φ1, half_12_08_φ2, half_12_08_φ3, half_12_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_12_08_hF1 : SourcePowerBound (paddedMoment 18 0 1 16 half_12_08_φ4) (5654713350507/2000000000000 : ℝ) := by
  have h := padded_second_power (k := 18) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_12_08_φ4 (by norm_num [half_12_08_φ1, half_12_08_φ2, half_12_08_φ3, half_12_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_08_φ1, half_12_08_φ2, half_12_08_φ3, half_12_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_08_φ1, half_12_08_φ2, half_12_08_φ3, half_12_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_12_08_φ1, half_12_08_φ2, half_12_08_φ3, half_12_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_12_08_hx4 : SourcePowerBound (powerBoxCross 18 8 16 half_12_08_φ4) (97827533153791/10000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 18) (s := 8) (r := 1) (v := 2) (t := 11) (D := 16)
    (a := (1/22 : ℝ)) (b := (5/22 : ℝ)) (c := (8/11 : ℝ))
    (by norm_num) half_12_08_φ4 (by norm_num [half_12_08_φ1, half_12_08_φ2, half_12_08_φ3, half_12_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_08_φ1, half_12_08_φ2, half_12_08_φ3, half_12_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_12_08_hF1 half_12_08_hF2 half_11_08
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_12_08_φ1, half_12_08_φ2, half_12_08_φ3, half_12_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_08_hx3 : SourcePowerBound (powerBoxCross 18 9 8 half_12_08_φ3) (106576624092831/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 9) (u := 7) (t := 10)
    (D := 8) (ψ := (212958054959/10000000000000 : ℝ)) half_12_08_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_08_φ1, half_12_08_φ2, half_12_08_φ3, half_12_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_08_φ1, half_12_08_φ2, half_12_08_φ3, half_12_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_08_φ1, half_12_08_φ2, half_12_08_φ3, half_12_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_8 half_10_08
    (by simpa only [half_12_08_φ4, show (2:ℝ)*8=16 by norm_num] using half_12_08_hx4)
  exact h.weaken (by norm_num [half_12_08_φ1, half_12_08_φ2, half_12_08_φ3, half_12_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_08_hx2 : SourcePowerBound (powerBoxCross 18 10 4 half_12_08_φ2) (117918442997031/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 10) (u := 8) (t := 11)
    (D := 4) (ψ := (329441325613/10000000000000 : ℝ)) half_12_08_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_08_φ1, half_12_08_φ2, half_12_08_φ3, half_12_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_08_φ1, half_12_08_φ2, half_12_08_φ3, half_12_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_08_φ1, half_12_08_φ2, half_12_08_φ3, half_12_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_08 half_11_08
    (by simpa only [half_12_08_φ3, show (2:ℝ)*4=8 by norm_num] using half_12_08_hx3)
  exact h.weaken (by norm_num [half_12_08_φ1, half_12_08_φ2, half_12_08_φ3, half_12_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_08_hx1 : SourcePowerBound (powerBoxCross 18 11 2 half_12_08_φ1) (16382740142269/1250000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 11) (u := 9) (t := 12)
    (D := 2) (ψ := (90148940751/2500000000000 : ℝ)) half_12_08_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_08_φ1, half_12_08_φ2, half_12_08_φ3, half_12_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_08_φ1, half_12_08_φ2, half_12_08_φ3, half_12_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_08_φ1, half_12_08_φ2, half_12_08_φ3, half_12_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_08 half_12_07
    (by simpa only [half_12_08_φ2, show (2:ℝ)*2=4 by norm_num] using half_12_08_hx2)
  exact h.weaken (by norm_num [half_12_08_φ1, half_12_08_φ2, half_12_08_φ3, half_12_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_08 : AdmissibleExponent 18 24 (138937558311101/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 10) (ψ := (375030341569/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_11_08
    (by simpa only [half_12_08_φ1] using half_12_08_hx1)
  exact admissibleExponent_mono h (by norm_num [half_12_08_φ1, half_12_08_φ2, half_12_08_φ3, half_12_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_13_08_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (76965274101/2000000000000 : ℝ)

def half_13_08_φ2 : Fin 2 → ℝ := Fin.snoc half_13_08_φ1 (92997407701/2500000000000 : ℝ)

def half_13_08_φ3 : Fin 3 → ℝ := Fin.snoc half_13_08_φ2 (174963793061/5000000000000 : ℝ)

def half_13_08_φ4 : Fin 4 → ℝ := Fin.snoc half_13_08_φ3 (283440396743/10000000000000 : ℝ)

theorem half_13_08_hF2 : SourcePowerBound (paddedMoment 18 0 2 16 half_13_08_φ4) (34550308403563/5000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_13_08_φ4 (by norm_num [half_13_08_φ1, half_13_08_φ2, half_13_08_φ3, half_13_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_08_φ1, half_13_08_φ2, half_13_08_φ3, half_13_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_08_φ1, half_13_08_φ2, half_13_08_φ3, half_13_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_13_08_φ1, half_13_08_φ2, half_13_08_φ3, half_13_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_13_08_hx4 : SourcePowerBound (powerBoxCross 18 9 16 half_13_08_φ4) (106992165307783/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 9) (r := 2) (v := 12) (w := 12) (D := 16)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_13_08_φ4 (by norm_num [half_13_08_φ1, half_13_08_φ2, half_13_08_φ3, half_13_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_08_φ1, half_13_08_φ2, half_13_08_φ3, half_13_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_13_08_hF2 half_12_08 half_12_08
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_13_08_φ1, half_13_08_φ2, half_13_08_φ3, half_13_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_08_hx3 : SourcePowerBound (powerBoxCross 18 10 8 half_13_08_φ3) (117253997685681/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 10) (u := 8) (t := 11)
    (D := 8) (ψ := (283440396743/10000000000000 : ℝ)) half_13_08_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_08_φ1, half_13_08_φ2, half_13_08_φ3, half_13_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_08_φ1, half_13_08_φ2, half_13_08_φ3, half_13_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_08_φ1, half_13_08_φ2, half_13_08_φ3, half_13_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_08 half_11_08
    (by simpa only [half_13_08_φ4, show (2:ℝ)*8=16 by norm_num] using half_13_08_hx4)
  exact h.weaken (by norm_num [half_13_08_φ1, half_13_08_φ2, half_13_08_φ3, half_13_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_08_hx2 : SourcePowerBound (powerBoxCross 18 11 4 half_13_08_φ2) (2027025713903/156250000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 11) (u := 9) (t := 12)
    (D := 4) (ψ := (174963793061/5000000000000 : ℝ)) half_13_08_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_08_φ1, half_13_08_φ2, half_13_08_φ3, half_13_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_08_φ1, half_13_08_φ2, half_13_08_φ3, half_13_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_08_φ1, half_13_08_φ2, half_13_08_φ3, half_13_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_08 half_12_08
    (by simpa only [half_13_08_φ3, show (2:ℝ)*4=8 by norm_num] using half_13_08_hx3)
  exact h.weaken (by norm_num [half_13_08_φ1, half_13_08_φ2, half_13_08_φ3, half_13_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_08_hx1 : SourcePowerBound (powerBoxCross 18 12 2 half_13_08_φ1) (35993925263113/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 12) (u := 10) (t := 13)
    (D := 2) (ψ := (92997407701/2500000000000 : ℝ)) half_13_08_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_08_φ1, half_13_08_φ2, half_13_08_φ3, half_13_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_08_φ1, half_13_08_φ2, half_13_08_φ3, half_13_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_08_φ1, half_13_08_φ2, half_13_08_φ3, half_13_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_08 half_13_07
    (by simpa only [half_13_08_φ2, show (2:ℝ)*2=4 by norm_num] using half_13_08_hx2)
  exact h.weaken (by norm_num [half_13_08_φ1, half_13_08_φ2, half_13_08_φ3, half_13_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_08 : AdmissibleExponent 18 26 (152826707574067/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 11) (ψ := (76965274101/2000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_12_08
    (by simpa only [half_13_08_φ1] using half_13_08_hx1)
  exact admissibleExponent_mono h (by norm_num [half_13_08_φ1, half_13_08_φ2, half_13_08_φ3, half_13_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_14_08_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (4935347277/125000000000 : ℝ)

def half_14_08_φ2 : Fin 2 → ℝ := Fin.snoc half_14_08_φ1 (383037542621/10000000000000 : ℝ)

def half_14_08_φ3 : Fin 3 → ℝ := Fin.snoc half_14_08_φ2 (91821350833/2500000000000 : ℝ)

def half_14_08_φ4 : Fin 4 → ℝ := Fin.snoc half_14_08_φ3 (332167367267/10000000000000 : ℝ)

def half_14_08_φ5 : Fin 5 → ℝ := Fin.snoc half_14_08_φ4 (2057870467/100000000000 : ℝ)

theorem half_14_08_hF2 : SourcePowerBound (paddedMoment 18 0 2 32 half_14_08_φ5) (263005117981/31250000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_14_08_φ5 (by norm_num [half_14_08_φ1, half_14_08_φ2, half_14_08_φ3, half_14_08_φ4, half_14_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_08_φ1, half_14_08_φ2, half_14_08_φ3, half_14_08_φ4, half_14_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_08_φ1, half_14_08_φ2, half_14_08_φ3, half_14_08_φ4, half_14_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_14_08_φ1, half_14_08_φ2, half_14_08_φ3, half_14_08_φ4, half_14_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_14_08_hx5 : SourcePowerBound (powerBoxCross 18 9 32 half_14_08_φ5) (107705089260197/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 9) (r := 2) (v := 12) (w := 12) (D := 32)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_14_08_φ5 (by norm_num [half_14_08_φ1, half_14_08_φ2, half_14_08_φ3, half_14_08_φ4, half_14_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_08_φ1, half_14_08_φ2, half_14_08_φ3, half_14_08_φ4, half_14_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_14_08_hF2 half_12_08 half_12_08
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_14_08_φ1, half_14_08_φ2, half_14_08_φ3, half_14_08_φ4, half_14_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_08_hx4 : SourcePowerBound (powerBoxCross 18 10 16 half_14_08_φ4) (5823860880699/500000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 10) (u := 8) (t := 11)
    (D := 16) (ψ := (2057870467/100000000000 : ℝ)) half_14_08_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_08_φ1, half_14_08_φ2, half_14_08_φ3, half_14_08_φ4, half_14_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_08_φ1, half_14_08_φ2, half_14_08_φ3, half_14_08_φ4, half_14_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_08_φ1, half_14_08_φ2, half_14_08_φ3, half_14_08_φ4, half_14_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_08 half_11_08
    (by simpa only [half_14_08_φ5, show (2:ℝ)*16=32 by norm_num] using half_14_08_hx5)
  exact h.weaken (by norm_num [half_14_08_φ1, half_14_08_φ2, half_14_08_φ3, half_14_08_φ4, half_14_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_08_hx3 : SourcePowerBound (powerBoxCross 18 11 8 half_14_08_φ3) (128173974459507/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 11) (u := 9) (t := 12)
    (D := 8) (ψ := (332167367267/10000000000000 : ℝ)) half_14_08_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_08_φ1, half_14_08_φ2, half_14_08_φ3, half_14_08_φ4, half_14_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_08_φ1, half_14_08_φ2, half_14_08_φ3, half_14_08_φ4, half_14_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_08_φ1, half_14_08_φ2, half_14_08_φ3, half_14_08_φ4, half_14_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_08 half_12_08
    (by simpa only [half_14_08_φ4, show (2:ℝ)*8=16 by norm_num] using half_14_08_hx4)
  exact h.weaken (by norm_num [half_14_08_φ1, half_14_08_φ2, half_14_08_φ3, half_14_08_φ4, half_14_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_08_hx2 : SourcePowerBound (powerBoxCross 18 12 4 half_14_08_φ2) (141801052665019/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 12) (u := 10) (t := 13)
    (D := 4) (ψ := (91821350833/2500000000000 : ℝ)) half_14_08_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_08_φ1, half_14_08_φ2, half_14_08_φ3, half_14_08_φ4, half_14_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_08_φ1, half_14_08_φ2, half_14_08_φ3, half_14_08_φ4, half_14_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_08_φ1, half_14_08_φ2, half_14_08_φ3, half_14_08_φ4, half_14_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_08 half_13_08
    (by simpa only [half_14_08_φ3, show (2:ℝ)*4=8 by norm_num] using half_14_08_hx3)
  exact h.weaken (by norm_num [half_14_08_φ1, half_14_08_φ2, half_14_08_φ3, half_14_08_φ4, half_14_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_08_hx1 : SourcePowerBound (powerBoxCross 18 13 2 half_14_08_φ1) (31437502471123/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 13) (u := 11) (t := 14)
    (D := 2) (ψ := (383037542621/10000000000000 : ℝ)) half_14_08_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_08_φ1, half_14_08_φ2, half_14_08_φ3, half_14_08_φ4, half_14_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_08_φ1, half_14_08_φ2, half_14_08_φ3, half_14_08_φ4, half_14_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_08_φ1, half_14_08_φ2, half_14_08_φ3, half_14_08_φ4, half_14_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_08 half_14_07
    (by simpa only [half_14_08_φ2, show (2:ℝ)*2=4 by norm_num] using half_14_08_hx2)
  exact h.weaken (by norm_num [half_14_08_φ1, half_14_08_φ2, half_14_08_φ3, half_14_08_φ4, half_14_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_08 : AdmissibleExponent 18 28 (33411641381923/2000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 12) (ψ := (4935347277/125000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_13_08
    (by simpa only [half_14_08_φ1] using half_14_08_hx1)
  exact admissibleExponent_mono h (by norm_num [half_14_08_φ1, half_14_08_φ2, half_14_08_φ3, half_14_08_φ4, half_14_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_15_08_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (404532291299/10000000000000 : ℝ)

def half_15_08_φ2 : Fin 2 → ℝ := Fin.snoc half_15_08_φ1 (196536410703/5000000000000 : ℝ)

def half_15_08_φ3 : Fin 3 → ℝ := Fin.snoc half_15_08_φ2 (75905102841/2000000000000 : ℝ)

def half_15_08_φ4 : Fin 4 → ℝ := Fin.snoc half_15_08_φ3 (177680394381/5000000000000 : ℝ)

def half_15_08_φ5 : Fin 5 → ℝ := Fin.snoc half_15_08_φ4 (284802711417/10000000000000 : ℝ)

theorem half_15_08_hF2 : SourcePowerBound (paddedMoment 18 0 2 32 half_15_08_φ5) (77317999518461/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_15_08_φ5 (by norm_num [half_15_08_φ1, half_15_08_φ2, half_15_08_φ3, half_15_08_φ4, half_15_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_08_φ1, half_15_08_φ2, half_15_08_φ3, half_15_08_φ4, half_15_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_08_φ1, half_15_08_φ2, half_15_08_φ3, half_15_08_φ4, half_15_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_15_08_φ1, half_15_08_φ2, half_15_08_φ3, half_15_08_φ4, half_15_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_15_08_hx5 : SourcePowerBound (powerBoxCross 18 10 32 half_15_08_φ5) (58015502014873/5000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 10) (r := 2) (v := 13) (w := 14) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_15_08_φ5 (by norm_num [half_15_08_φ1, half_15_08_φ2, half_15_08_φ3, half_15_08_φ4, half_15_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_08_φ1, half_15_08_φ2, half_15_08_φ3, half_15_08_φ4, half_15_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_15_08_hF2 half_13_08 half_14_08
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_15_08_φ1, half_15_08_φ2, half_15_08_φ3, half_15_08_φ4, half_15_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_08_hx4 : SourcePowerBound (powerBoxCross 18 11 16 half_15_08_φ4) (126517699124367/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 11) (u := 9) (t := 12)
    (D := 16) (ψ := (284802711417/10000000000000 : ℝ)) half_15_08_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_08_φ1, half_15_08_φ2, half_15_08_φ3, half_15_08_φ4, half_15_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_08_φ1, half_15_08_φ2, half_15_08_φ3, half_15_08_φ4, half_15_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_08_φ1, half_15_08_φ2, half_15_08_φ3, half_15_08_φ4, half_15_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_08 half_12_08
    (by simpa only [half_15_08_φ5, show (2:ℝ)*16=32 by norm_num] using half_15_08_hx5)
  exact h.weaken (by norm_num [half_15_08_φ1, half_15_08_φ2, half_15_08_φ3, half_15_08_φ4, half_15_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_08_hx3 : SourcePowerBound (powerBoxCross 18 12 8 half_15_08_φ3) (139403031397721/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 12) (u := 10) (t := 13)
    (D := 8) (ψ := (177680394381/5000000000000 : ℝ)) half_15_08_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_08_φ1, half_15_08_φ2, half_15_08_φ3, half_15_08_φ4, half_15_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_08_φ1, half_15_08_φ2, half_15_08_φ3, half_15_08_φ4, half_15_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_08_φ1, half_15_08_φ2, half_15_08_φ3, half_15_08_φ4, half_15_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_08 half_13_08
    (by simpa only [half_15_08_φ4, show (2:ℝ)*8=16 by norm_num] using half_15_08_hx4)
  exact h.weaken (by norm_num [half_15_08_φ1, half_15_08_φ2, half_15_08_φ3, half_15_08_φ4, half_15_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_08_hx2 : SourcePowerBound (powerBoxCross 18 13 4 half_15_08_φ2) (19269149388939/1250000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 13) (u := 11) (t := 14)
    (D := 4) (ψ := (75905102841/2000000000000 : ℝ)) half_15_08_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_08_φ1, half_15_08_φ2, half_15_08_φ3, half_15_08_φ4, half_15_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_08_φ1, half_15_08_φ2, half_15_08_φ3, half_15_08_φ4, half_15_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_08_φ1, half_15_08_φ2, half_15_08_φ3, half_15_08_φ4, half_15_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_08 half_14_08
    (by simpa only [half_15_08_φ3, show (2:ℝ)*4=8 by norm_num] using half_15_08_hx3)
  exact h.weaken (by norm_num [half_15_08_φ1, half_15_08_φ2, half_15_08_φ3, half_15_08_φ4, half_15_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_08_hx1 : SourcePowerBound (powerBoxCross 18 14 2 half_15_08_φ1) (85352347639393/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 14) (u := 12) (t := 15)
    (D := 2) (ψ := (196536410703/5000000000000 : ℝ)) half_15_08_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_08_φ1, half_15_08_φ2, half_15_08_φ3, half_15_08_φ4, half_15_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_08_φ1, half_15_08_φ2, half_15_08_φ3, half_15_08_φ4, half_15_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_08_φ1, half_15_08_φ2, half_15_08_φ3, half_15_08_φ4, half_15_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_13_08 half_15_07
    (by simpa only [half_15_08_φ2, show (2:ℝ)*2=4 by norm_num] using half_15_08_hx2)
  exact h.weaken (by norm_num [half_15_08_φ1, half_15_08_φ2, half_15_08_φ3, half_15_08_φ4, half_15_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_08 : AdmissibleExponent 18 30 (181627067143859/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 13) (ψ := (404532291299/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_14_08
    (by simpa only [half_15_08_φ1] using half_15_08_hx1)
  exact admissibleExponent_mono h (by norm_num [half_15_08_φ1, half_15_08_φ2, half_15_08_φ3, half_15_08_φ4, half_15_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_16_08_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (207211319243/5000000000000 : ℝ)

def half_16_08_φ2 : Fin 2 → ℝ := Fin.snoc half_16_08_φ1 (201419634233/5000000000000 : ℝ)

def half_16_08_φ3 : Fin 3 → ℝ := Fin.snoc half_16_08_φ2 (391181785343/10000000000000 : ℝ)

def half_16_08_φ4 : Fin 4 → ℝ := Fin.snoc half_16_08_φ3 (187090536067/5000000000000 : ℝ)

def half_16_08_φ5 : Fin 5 → ℝ := Fin.snoc half_16_08_φ4 (67297232197/2000000000000 : ℝ)

def half_16_08_φ6 : Fin 6 → ℝ := Fin.snoc half_16_08_φ5 (10447155439/500000000000 : ℝ)

theorem half_16_08_hF2 : SourcePowerBound (paddedMoment 18 0 2 64 half_16_08_φ6) (45734622128053/5000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 6) (r := 0) (D := 64)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_16_08_φ6 (by norm_num [half_16_08_φ1, half_16_08_φ2, half_16_08_φ3, half_16_08_φ4, half_16_08_φ5, half_16_08_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_08_φ1, half_16_08_φ2, half_16_08_φ3, half_16_08_φ4, half_16_08_φ5, half_16_08_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_08_φ1, half_16_08_φ2, half_16_08_φ3, half_16_08_φ4, half_16_08_φ5, half_16_08_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_16_08_φ1, half_16_08_φ2, half_16_08_φ3, half_16_08_φ4, half_16_08_φ5, half_16_08_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_16_08_hx6 : SourcePowerBound (powerBoxCross 18 10 64 half_16_08_φ6) (23179263944041/2000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 10) (r := 2) (v := 13) (w := 14) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_16_08_φ6 (by norm_num [half_16_08_φ1, half_16_08_φ2, half_16_08_φ3, half_16_08_φ4, half_16_08_φ5, half_16_08_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_08_φ1, half_16_08_φ2, half_16_08_φ3, half_16_08_φ4, half_16_08_φ5, half_16_08_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_16_08_hF2 half_13_08 half_14_08
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_16_08_φ1, half_16_08_φ2, half_16_08_φ3, half_16_08_φ4, half_16_08_φ5, half_16_08_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_08_hx5 : SourcePowerBound (powerBoxCross 18 11 32 half_16_08_φ5) (62378813188893/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 5) (s := 11) (u := 9) (t := 12)
    (D := 32) (ψ := (10447155439/500000000000 : ℝ)) half_16_08_φ5
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_08_φ1, half_16_08_φ2, half_16_08_φ3, half_16_08_φ4, half_16_08_φ5, half_16_08_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_08_φ1, half_16_08_φ2, half_16_08_φ3, half_16_08_φ4, half_16_08_φ5, half_16_08_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_08_φ1, half_16_08_φ2, half_16_08_φ3, half_16_08_φ4, half_16_08_φ5, half_16_08_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_08 half_12_08
    (by simpa only [half_16_08_φ6, show (2:ℝ)*32=64 by norm_num] using half_16_08_hx6)
  exact h.weaken (by norm_num [half_16_08_φ1, half_16_08_φ2, half_16_08_φ3, half_16_08_φ4, half_16_08_φ5, half_16_08_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_08_hx4 : SourcePowerBound (powerBoxCross 18 12 16 half_16_08_φ4) (6838979728249/500000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 12) (u := 10) (t := 13)
    (D := 16) (ψ := (67297232197/2000000000000 : ℝ)) half_16_08_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_08_φ1, half_16_08_φ2, half_16_08_φ3, half_16_08_φ4, half_16_08_φ5, half_16_08_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_08_φ1, half_16_08_φ2, half_16_08_φ3, half_16_08_φ4, half_16_08_φ5, half_16_08_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_08_φ1, half_16_08_φ2, half_16_08_φ3, half_16_08_φ4, half_16_08_φ5, half_16_08_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_08 half_13_08
    (by simpa only [half_16_08_φ5, show (2:ℝ)*16=32 by norm_num] using half_16_08_hx5)
  exact h.weaken (by norm_num [half_16_08_φ1, half_16_08_φ2, half_16_08_φ3, half_16_08_φ4, half_16_08_φ5, half_16_08_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_08_hx3 : SourcePowerBound (powerBoxCross 18 13 8 half_16_08_φ3) (15085618986303/1000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 13) (u := 11) (t := 14)
    (D := 8) (ψ := (187090536067/5000000000000 : ℝ)) half_16_08_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_08_φ1, half_16_08_φ2, half_16_08_φ3, half_16_08_φ4, half_16_08_φ5, half_16_08_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_08_φ1, half_16_08_φ2, half_16_08_φ3, half_16_08_φ4, half_16_08_φ5, half_16_08_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_08_φ1, half_16_08_φ2, half_16_08_φ3, half_16_08_φ4, half_16_08_φ5, half_16_08_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_08 half_14_08
    (by simpa only [half_16_08_φ4, show (2:ℝ)*8=16 by norm_num] using half_16_08_hx4)
  exact h.weaken (by norm_num [half_16_08_φ1, half_16_08_φ2, half_16_08_φ3, half_16_08_φ4, half_16_08_φ5, half_16_08_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_08_hx2 : SourcePowerBound (powerBoxCross 18 14 4 half_16_08_φ2) (5211338451523/312500000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 14) (u := 12) (t := 15)
    (D := 4) (ψ := (391181785343/10000000000000 : ℝ)) half_16_08_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_08_φ1, half_16_08_φ2, half_16_08_φ3, half_16_08_φ4, half_16_08_φ5, half_16_08_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_08_φ1, half_16_08_φ2, half_16_08_φ3, half_16_08_φ4, half_16_08_φ5, half_16_08_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_08_φ1, half_16_08_φ2, half_16_08_φ3, half_16_08_φ4, half_16_08_φ5, half_16_08_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_13_08 half_15_08
    (by simpa only [half_16_08_φ3, show (2:ℝ)*4=8 by norm_num] using half_16_08_hx3)
  exact h.weaken (by norm_num [half_16_08_φ1, half_16_08_φ2, half_16_08_φ3, half_16_08_φ4, half_16_08_φ5, half_16_08_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_08_hx1 : SourcePowerBound (powerBoxCross 18 15 2 half_16_08_φ1) (184514452943739/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 15) (u := 13) (t := 16)
    (D := 2) (ψ := (201419634233/5000000000000 : ℝ)) half_16_08_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_08_φ1, half_16_08_φ2, half_16_08_φ3, half_16_08_φ4, half_16_08_φ5, half_16_08_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_08_φ1, half_16_08_φ2, half_16_08_φ3, half_16_08_φ4, half_16_08_φ5, half_16_08_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_08_φ1, half_16_08_φ2, half_16_08_φ3, half_16_08_φ4, half_16_08_φ5, half_16_08_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_14_08 half_16_07
    (by simpa only [half_16_08_φ2, show (2:ℝ)*2=4 by norm_num] using half_16_08_hx2)
  exact h.weaken (by norm_num [half_16_08_φ1, half_16_08_φ2, half_16_08_φ3, half_16_08_φ4, half_16_08_φ5, half_16_08_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_08 : AdmissibleExponent 18 32 (196532709459833/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 14) (ψ := (207211319243/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_15_08
    (by simpa only [half_16_08_φ1] using half_16_08_hx1)
  exact admissibleExponent_mono h (by norm_num [half_16_08_φ1, half_16_08_φ2, half_16_08_φ3, half_16_08_φ4, half_16_08_φ5, half_16_08_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_17_08_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (84852889279/2000000000000 : ℝ)

def half_17_08_φ2 : Fin 2 → ℝ := Fin.snoc half_17_08_φ1 (412244946301/10000000000000 : ℝ)

def half_17_08_φ3 : Fin 3 → ℝ := Fin.snoc half_17_08_φ2 (100321767491/2500000000000 : ℝ)

def half_17_08_φ4 : Fin 4 → ℝ := Fin.snoc half_17_08_φ3 (387291641301/10000000000000 : ℝ)

def half_17_08_φ5 : Fin 5 → ℝ := Fin.snoc half_17_08_φ4 (180867583259/5000000000000 : ℝ)

def half_17_08_φ6 : Fin 6 → ℝ := Fin.snoc half_17_08_φ5 (72646325627/2500000000000 : ℝ)

theorem half_17_08_hF2 : SourcePowerBound (paddedMoment 18 0 2 64 half_17_08_φ6) (83852162777663/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 6) (r := 0) (D := 64)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_17_08_φ6 (by norm_num [half_17_08_φ1, half_17_08_φ2, half_17_08_φ3, half_17_08_φ4, half_17_08_φ5, half_17_08_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_08_φ1, half_17_08_φ2, half_17_08_φ3, half_17_08_φ4, half_17_08_φ5, half_17_08_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_08_φ1, half_17_08_φ2, half_17_08_φ3, half_17_08_φ4, half_17_08_φ5, half_17_08_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_17_08_φ1, half_17_08_φ2, half_17_08_φ3, half_17_08_φ4, half_17_08_φ5, half_17_08_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_17_08_hx6 : SourcePowerBound (powerBoxCross 18 11 64 half_17_08_φ6) (123347679188659/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 11) (r := 2) (v := 14) (w := 15) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_17_08_φ6 (by norm_num [half_17_08_φ1, half_17_08_φ2, half_17_08_φ3, half_17_08_φ4, half_17_08_φ5, half_17_08_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_08_φ1, half_17_08_φ2, half_17_08_φ3, half_17_08_φ4, half_17_08_φ5, half_17_08_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_17_08_hF2 half_14_08 half_15_08
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_17_08_φ1, half_17_08_φ2, half_17_08_φ3, half_17_08_φ4, half_17_08_φ5, half_17_08_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_08_hx5 : SourcePowerBound (powerBoxCross 18 12 32 half_17_08_φ5) (67034179155343/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 5) (s := 12) (u := 10) (t := 13)
    (D := 32) (ψ := (72646325627/2500000000000 : ℝ)) half_17_08_φ5
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_08_φ1, half_17_08_φ2, half_17_08_φ3, half_17_08_φ4, half_17_08_φ5, half_17_08_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_08_φ1, half_17_08_φ2, half_17_08_φ3, half_17_08_φ4, half_17_08_φ5, half_17_08_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_08_φ1, half_17_08_φ2, half_17_08_φ3, half_17_08_φ4, half_17_08_φ5, half_17_08_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_08 half_13_08
    (by simpa only [half_17_08_φ6, show (2:ℝ)*32=64 by norm_num] using half_17_08_hx6)
  exact h.weaken (by norm_num [half_17_08_φ1, half_17_08_φ2, half_17_08_φ3, half_17_08_φ4, half_17_08_φ5, half_17_08_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_08_hx4 : SourcePowerBound (powerBoxCross 18 13 16 half_17_08_φ4) (73667886452773/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 13) (u := 11) (t := 14)
    (D := 16) (ψ := (180867583259/5000000000000 : ℝ)) half_17_08_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_08_φ1, half_17_08_φ2, half_17_08_φ3, half_17_08_φ4, half_17_08_φ5, half_17_08_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_08_φ1, half_17_08_φ2, half_17_08_φ3, half_17_08_φ4, half_17_08_φ5, half_17_08_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_08_φ1, half_17_08_φ2, half_17_08_φ3, half_17_08_φ4, half_17_08_φ5, half_17_08_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_08 half_14_08
    (by simpa only [half_17_08_φ5, show (2:ℝ)*16=32 by norm_num] using half_17_08_hx5)
  exact h.weaken (by norm_num [half_17_08_φ1, half_17_08_φ2, half_17_08_φ3, half_17_08_φ4, half_17_08_φ5, half_17_08_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_08_hx3 : SourcePowerBound (powerBoxCross 18 14 8 half_17_08_φ3) (162560428546657/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 14) (u := 12) (t := 15)
    (D := 8) (ψ := (387291641301/10000000000000 : ℝ)) half_17_08_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_08_φ1, half_17_08_φ2, half_17_08_φ3, half_17_08_φ4, half_17_08_φ5, half_17_08_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_08_φ1, half_17_08_φ2, half_17_08_φ3, half_17_08_φ4, half_17_08_φ5, half_17_08_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_08_φ1, half_17_08_φ2, half_17_08_φ3, half_17_08_φ4, half_17_08_φ5, half_17_08_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_13_08 half_15_08
    (by simpa only [half_17_08_φ4, show (2:ℝ)*8=16 by norm_num] using half_17_08_hx4)
  exact h.weaken (by norm_num [half_17_08_φ1, half_17_08_φ2, half_17_08_φ3, half_17_08_φ4, half_17_08_φ5, half_17_08_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_08_hx2 : SourcePowerBound (powerBoxCross 18 15 4 half_17_08_φ2) (89816770869043/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 15) (u := 13) (t := 16)
    (D := 4) (ψ := (100321767491/2500000000000 : ℝ)) half_17_08_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_08_φ1, half_17_08_φ2, half_17_08_φ3, half_17_08_φ4, half_17_08_φ5, half_17_08_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_08_φ1, half_17_08_φ2, half_17_08_φ3, half_17_08_φ4, half_17_08_φ5, half_17_08_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_08_φ1, half_17_08_φ2, half_17_08_φ3, half_17_08_φ4, half_17_08_φ5, half_17_08_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_14_08 half_16_08
    (by simpa only [half_17_08_φ3, show (2:ℝ)*4=8 by norm_num] using half_17_08_hx3)
  exact h.weaken (by norm_num [half_17_08_φ1, half_17_08_φ2, half_17_08_φ3, half_17_08_φ4, half_17_08_φ5, half_17_08_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_08_hx1 : SourcePowerBound (powerBoxCross 18 16 2 half_17_08_φ1) (39723757957699/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 16) (u := 14) (t := 17)
    (D := 2) (ψ := (412244946301/10000000000000 : ℝ)) half_17_08_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_08_φ1, half_17_08_φ2, half_17_08_φ3, half_17_08_φ4, half_17_08_φ5, half_17_08_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_08_φ1, half_17_08_φ2, half_17_08_φ3, half_17_08_φ4, half_17_08_φ5, half_17_08_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_08_φ1, half_17_08_φ2, half_17_08_φ3, half_17_08_φ4, half_17_08_φ5, half_17_08_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_15_08 half_17_07
    (by simpa only [half_17_08_φ2, show (2:ℝ)*2=4 by norm_num] using half_17_08_hx2)
  exact h.weaken (by norm_num [half_17_08_φ1, half_17_08_φ2, half_17_08_φ3, half_17_08_φ4, half_17_08_φ5, half_17_08_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_08 : AdmissibleExponent 18 34 (10588549381337/500000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 15) (ψ := (84852889279/2000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_16_08
    (by simpa only [half_17_08_φ1] using half_17_08_hx1)
  exact admissibleExponent_mono h (by norm_num [half_17_08_φ1, half_17_08_φ2, half_17_08_φ3, half_17_08_φ4, half_17_08_φ5, half_17_08_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])


end Waring.SeedCompletionHigher18SimpleSeeds
