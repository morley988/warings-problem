import Waring.SeedCompletionHigher18SimpleSeedsC08

noncomputable section
set_option maxHeartbeats 2000000
namespace Waring.SeedCompletionHigher18SimpleSeeds
open SmoothMoments FirstStageTransport SeedCompletionNaturalBox
open SeedCompletionSourceBounds SeedCompletionPaddedSource SeedCompletionGeneralTerminal
open PolicyCompletionMajorPowerRanges

def half_9_09_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (343839381693/10000000000000 : ℝ)

def half_9_09_φ2 : Fin 2 → ℝ := Fin.snoc half_9_09_φ1 (61669161623/2000000000000 : ℝ)

def half_9_09_φ3 : Fin 3 → ℝ := Fin.snoc half_9_09_φ2 (134450106773/10000000000000 : ℝ)

theorem half_9_09_hF2 : SourcePowerBound (paddedMoment 18 0 2 8 half_9_09_φ3) (69881599874369/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_09_φ3 (by norm_num [half_9_09_φ1, half_9_09_φ2, half_9_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_09_φ1, half_9_09_φ2, half_9_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_09_φ1, half_9_09_φ2, half_9_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_09_φ1, half_9_09_φ2, half_9_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_9_09_hF1 : SourcePowerBound (paddedMoment 18 0 1 8 half_9_09_φ3) (26627199958123/10000000000000 : ℝ) := by
  have h := padded_second_power (k := 18) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_09_φ3 (by norm_num [half_9_09_φ1, half_9_09_φ2, half_9_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_09_φ1, half_9_09_φ2, half_9_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_09_φ1, half_9_09_φ2, half_9_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_09_φ1, half_9_09_φ2, half_9_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_9_09_hx3 : SourcePowerBound (powerBoxCross 18 6 8 half_9_09_φ3) (76992986574617/10000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 18) (s := 6) (r := 1) (v := 2) (t := 10) (D := 8)
    (a := (3/10 : ℝ)) (b := (1/10 : ℝ)) (c := (3/5 : ℝ))
    (by norm_num) half_9_09_φ3 (by norm_num [half_9_09_φ1, half_9_09_φ2, half_9_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_09_φ1, half_9_09_φ2, half_9_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_9_09_hF1 half_9_09_hF2 half_10_08
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_9_09_φ1, half_9_09_φ2, half_9_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_9_09_hx2 : SourcePowerBound (powerBoxCross 18 7 4 half_9_09_φ2) (5266837750407/625000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 7) (u := 5) (t := 8)
    (D := 4) (ψ := (134450106773/10000000000000 : ℝ)) half_9_09_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_09_φ1, half_9_09_φ2, half_9_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_09_φ1, half_9_09_φ2, half_9_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_09_φ1, half_9_09_φ2, half_9_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_6 SeedCompletionEven18SecondSeeds.degree18_half_8
    (by simpa only [half_9_09_φ3, show (2:ℝ)*4=8 by norm_num] using half_9_09_hx3)
  exact h.weaken (by norm_num [half_9_09_φ1, half_9_09_φ2, half_9_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_9_09_hx1 : SourcePowerBound (powerBoxCross 18 8 2 half_9_09_φ1) (94174793810997/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 8) (u := 6) (t := 9)
    (D := 2) (ψ := (61669161623/2000000000000 : ℝ)) half_9_09_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_09_φ1, half_9_09_φ2, half_9_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_09_φ1, half_9_09_φ2, half_9_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_09_φ1, half_9_09_φ2, half_9_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_7 half_9_08
    (by simpa only [half_9_09_φ2, show (2:ℝ)*2=4 by norm_num] using half_9_09_hx2)
  exact h.weaken (by norm_num [half_9_09_φ1, half_9_09_φ2, half_9_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_9_09 : AdmissibleExponent 18 18 (12416548067049/1250000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 7) (ψ := (343839381693/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_8
    (by simpa only [half_9_09_φ1] using half_9_09_hx1)
  exact admissibleExponent_mono h (by norm_num [half_9_09_φ1, half_9_09_φ2, half_9_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_10_09_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (176875358213/5000000000000 : ℝ)

def half_10_09_φ2 : Fin 2 → ℝ := Fin.snoc half_10_09_φ1 (329257029453/10000000000000 : ℝ)

def half_10_09_φ3 : Fin 3 → ℝ := Fin.snoc half_10_09_φ2 (229940769877/10000000000000 : ℝ)

theorem half_10_09_hF2 : SourcePowerBound (paddedMoment 18 0 2 8 half_10_09_φ3) (15859906424111/2500000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_10_09_φ3 (by norm_num [half_10_09_φ1, half_10_09_φ2, half_10_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_09_φ1, half_10_09_φ2, half_10_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_09_φ1, half_10_09_φ2, half_10_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_10_09_φ1, half_10_09_φ2, half_10_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_10_09_hx3 : SourcePowerBound (powerBoxCross 18 7 8 half_10_09_φ3) (43238922111349/5000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 7) (r := 2) (v := 9) (w := 10) (D := 8)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_10_09_φ3 (by norm_num [half_10_09_φ1, half_10_09_φ2, half_10_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_09_φ1, half_10_09_φ2, half_10_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_10_09_hF2 half_9_09 half_10_08
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_10_09_φ1, half_10_09_φ2, half_10_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_09_hx2 : SourcePowerBound (powerBoxCross 18 8 4 half_10_09_φ2) (3808076965641/400000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 8) (u := 6) (t := 9)
    (D := 4) (ψ := (229940769877/10000000000000 : ℝ)) half_10_09_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_09_φ1, half_10_09_φ2, half_10_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_09_φ1, half_10_09_φ2, half_10_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_09_φ1, half_10_09_φ2, half_10_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_7 half_9_09
    (by simpa only [half_10_09_φ3, show (2:ℝ)*4=8 by norm_num] using half_10_09_hx3)
  exact h.weaken (by norm_num [half_10_09_φ1, half_10_09_φ2, half_10_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_09_hx1 : SourcePowerBound (powerBoxCross 18 9 2 half_10_09_φ1) (106172245033427/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 9) (u := 7) (t := 10)
    (D := 2) (ψ := (329257029453/10000000000000 : ℝ)) half_10_09_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_09_φ1, half_10_09_φ2, half_10_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_09_φ1, half_10_09_φ2, half_10_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_09_φ1, half_10_09_φ2, half_10_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_8 half_10_08
    (by simpa only [half_10_09_φ2, show (2:ℝ)*2=4 by norm_num] using half_10_09_hx2)
  exact h.weaken (by norm_num [half_10_09_φ1, half_10_09_φ2, half_10_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_09 : AdmissibleExponent 18 20 (112186007212669/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 8) (ψ := (176875358213/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_9_09
    (by simpa only [half_10_09_φ1] using half_10_09_hx1)
  exact admissibleExponent_mono h (by norm_num [half_10_09_φ1, half_10_09_φ2, half_10_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_11_09_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (72951662623/2000000000000 : ℝ)

def half_11_09_φ2 : Fin 2 → ℝ := Fin.snoc half_11_09_φ1 (346398437703/10000000000000 : ℝ)

def half_11_09_φ3 : Fin 3 → ℝ := Fin.snoc half_11_09_φ2 (29474478229/1000000000000 : ℝ)

theorem half_11_09_hF2 : SourcePowerBound (paddedMoment 18 0 2 8 half_11_09_φ3) (14674755452873/2500000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_11_09_φ3 (by norm_num [half_11_09_φ1, half_11_09_φ2, half_11_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_09_φ1, half_11_09_φ2, half_11_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_09_φ1, half_11_09_φ2, half_11_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_11_09_φ1, half_11_09_φ2, half_11_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_11_09_hx3 : SourcePowerBound (powerBoxCross 18 8 8 half_11_09_φ3) (96288273589257/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 8) (r := 2) (v := 10) (w := 11) (D := 8)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_11_09_φ3 (by norm_num [half_11_09_φ1, half_11_09_φ2, half_11_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_09_φ1, half_11_09_φ2, half_11_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_11_09_hF2 half_10_09 half_11_08
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_11_09_φ1, half_11_09_φ2, half_11_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_09_hx2 : SourcePowerBound (powerBoxCross 18 9 4 half_11_09_φ2) (21282760413471/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 9) (u := 7) (t := 10)
    (D := 4) (ψ := (29474478229/1000000000000 : ℝ)) half_11_09_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_09_φ1, half_11_09_φ2, half_11_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_09_φ1, half_11_09_φ2, half_11_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_09_φ1, half_11_09_φ2, half_11_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_8 half_10_09
    (by simpa only [half_11_09_φ3, show (2:ℝ)*4=8 by norm_num] using half_11_09_hx3)
  exact h.weaken (by norm_num [half_11_09_φ1, half_11_09_φ2, half_11_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_09_hx1 : SourcePowerBound (powerBoxCross 18 10 2 half_11_09_φ1) (29614671912797/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 10) (u := 8) (t := 11)
    (D := 2) (ψ := (346398437703/10000000000000 : ℝ)) half_11_09_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_09_φ1, half_11_09_φ2, half_11_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_09_φ1, half_11_09_φ2, half_11_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_09_φ1, half_11_09_φ2, half_11_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_09 half_11_08
    (by simpa only [half_11_09_φ2, show (2:ℝ)*2=4 by norm_num] using half_11_09_hx2)
  exact h.weaken (by norm_num [half_11_09_φ1, half_11_09_φ2, half_11_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_09 : AdmissibleExponent 18 22 (125389095600373/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 9) (ψ := (72951662623/2000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_10_09
    (by simpa only [half_11_09_φ1] using half_11_09_hx1)
  exact admissibleExponent_mono h (by norm_num [half_11_09_φ1, half_11_09_φ2, half_11_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_12_09_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (187484777473/5000000000000 : ℝ)

def half_12_09_φ2 : Fin 2 → ℝ := Fin.snoc half_12_09_φ1 (36058947329/1000000000000 : ℝ)

def half_12_09_φ3 : Fin 3 → ℝ := Fin.snoc half_12_09_φ2 (329433388809/10000000000000 : ℝ)

def half_12_09_φ4 : Fin 4 → ℝ := Fin.snoc half_12_09_φ3 (212922496617/10000000000000 : ℝ)

theorem half_12_09_hF2 : SourcePowerBound (paddedMoment 18 0 2 16 half_12_09_φ4) (37413169701619/5000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_12_09_φ4 (by norm_num [half_12_09_φ1, half_12_09_φ2, half_12_09_φ3, half_12_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_09_φ1, half_12_09_φ2, half_12_09_φ3, half_12_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_09_φ1, half_12_09_φ2, half_12_09_φ3, half_12_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_12_09_φ1, half_12_09_φ2, half_12_09_φ3, half_12_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_12_09_hF1 : SourcePowerBound (paddedMoment 18 0 1 16 half_12_09_φ4) (14137723233873/5000000000000 : ℝ) := by
  have h := padded_second_power (k := 18) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_12_09_φ4 (by norm_num [half_12_09_φ1, half_12_09_φ2, half_12_09_φ3, half_12_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_09_φ1, half_12_09_φ2, half_12_09_φ3, half_12_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_09_φ1, half_12_09_φ2, half_12_09_φ3, half_12_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_12_09_φ1, half_12_09_φ2, half_12_09_φ3, half_12_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_12_09_hx4 : SourcePowerBound (powerBoxCross 18 8 16 half_12_09_φ4) (48914866378287/5000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 18) (s := 8) (r := 1) (v := 2) (t := 11) (D := 16)
    (a := (1/22 : ℝ)) (b := (5/22 : ℝ)) (c := (8/11 : ℝ))
    (by norm_num) half_12_09_φ4 (by norm_num [half_12_09_φ1, half_12_09_φ2, half_12_09_φ3, half_12_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_09_φ1, half_12_09_φ2, half_12_09_φ3, half_12_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_12_09_hF1 half_12_09_hF2 half_11_09
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_12_09_φ1, half_12_09_φ2, half_12_09_φ3, half_12_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_09_hx3 : SourcePowerBound (powerBoxCross 18 9 8 half_12_09_φ3) (53289245407683/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 9) (u := 7) (t := 10)
    (D := 8) (ψ := (212922496617/10000000000000 : ℝ)) half_12_09_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_09_φ1, half_12_09_φ2, half_12_09_φ3, half_12_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_09_φ1, half_12_09_φ2, half_12_09_φ3, half_12_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_09_φ1, half_12_09_φ2, half_12_09_φ3, half_12_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_8 half_10_09
    (by simpa only [half_12_09_φ4, show (2:ℝ)*8=16 by norm_num] using half_12_09_hx4)
  exact h.weaken (by norm_num [half_12_09_φ1, half_12_09_φ2, half_12_09_φ3, half_12_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_09_hx2 : SourcePowerBound (powerBoxCross 18 10 4 half_12_09_φ2) (5896008560359/500000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 10) (u := 8) (t := 11)
    (D := 4) (ψ := (329433388809/10000000000000 : ℝ)) half_12_09_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_09_φ1, half_12_09_φ2, half_12_09_φ3, half_12_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_09_φ1, half_12_09_φ2, half_12_09_φ3, half_12_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_09_φ1, half_12_09_φ2, half_12_09_φ3, half_12_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_09 half_11_09
    (by simpa only [half_12_09_φ3, show (2:ℝ)*4=8 by norm_num] using half_12_09_hx3)
  exact h.weaken (by norm_num [half_12_09_φ1, half_12_09_φ2, half_12_09_φ3, half_12_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_09_hx1 : SourcePowerBound (powerBoxCross 18 11 2 half_12_09_φ1) (26212471163619/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 11) (u := 9) (t := 12)
    (D := 2) (ψ := (36058947329/1000000000000 : ℝ)) half_12_09_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_09_φ1, half_12_09_φ2, half_12_09_φ3, half_12_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_09_φ1, half_12_09_φ2, half_12_09_φ3, half_12_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_09_φ1, half_12_09_φ2, half_12_09_φ3, half_12_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_09 half_12_08
    (by simpa only [half_12_09_φ2, show (2:ℝ)*2=4 by norm_num] using half_12_09_hx2)
  exact h.weaken (by norm_num [half_12_09_φ1, half_12_09_φ2, half_12_09_φ3, half_12_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_09 : AdmissibleExponent 18 24 (138936716471961/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 10) (ψ := (187484777473/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_11_09
    (by simpa only [half_12_09_φ1] using half_12_09_hx1)
  exact admissibleExponent_mono h (by norm_num [half_12_09_φ1, half_12_09_φ2, half_12_09_φ3, half_12_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_13_09_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (76936065897/2000000000000 : ℝ)

def half_13_09_φ2 : Fin 2 → ℝ := Fin.snoc half_13_09_φ1 (371975298471/10000000000000 : ℝ)

def half_13_09_φ3 : Fin 3 → ℝ := Fin.snoc half_13_09_φ2 (87476021983/2500000000000 : ℝ)

def half_13_09_φ4 : Fin 4 → ℝ := Fin.snoc half_13_09_φ3 (283354343481/10000000000000 : ℝ)

theorem half_13_09_hF2 : SourcePowerBound (paddedMoment 18 0 2 16 half_13_09_φ4) (69114382972181/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_13_09_φ4 (by norm_num [half_13_09_φ1, half_13_09_φ2, half_13_09_φ3, half_13_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_09_φ1, half_13_09_φ2, half_13_09_φ3, half_13_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_09_φ1, half_13_09_φ2, half_13_09_φ3, half_13_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_13_09_φ1, half_13_09_φ2, half_13_09_φ3, half_13_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_13_09_hx4 : SourcePowerBound (powerBoxCross 18 9 16 half_13_09_φ4) (26749468981999/2500000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 9) (r := 2) (v := 12) (w := 12) (D := 16)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_13_09_φ4 (by norm_num [half_13_09_φ1, half_13_09_φ2, half_13_09_φ3, half_13_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_09_φ1, half_13_09_φ2, half_13_09_φ3, half_13_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_13_09_hF2 half_12_09 half_12_09
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_13_09_φ1, half_13_09_φ2, half_13_09_φ3, half_13_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_09_hx3 : SourcePowerBound (powerBoxCross 18 10 8 half_13_09_φ3) (117258713998577/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 10) (u := 8) (t := 11)
    (D := 8) (ψ := (283354343481/10000000000000 : ℝ)) half_13_09_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_09_φ1, half_13_09_φ2, half_13_09_φ3, half_13_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_09_φ1, half_13_09_φ2, half_13_09_φ3, half_13_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_09_φ1, half_13_09_φ2, half_13_09_φ3, half_13_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_09 half_11_09
    (by simpa only [half_13_09_φ4, show (2:ℝ)*8=16 by norm_num] using half_13_09_hx4)
  exact h.weaken (by norm_num [half_13_09_φ1, half_13_09_φ2, half_13_09_φ3, half_13_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_09_hx2 : SourcePowerBound (powerBoxCross 18 11 4 half_13_09_φ2) (64866934405293/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 11) (u := 9) (t := 12)
    (D := 4) (ψ := (87476021983/2500000000000 : ℝ)) half_13_09_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_09_φ1, half_13_09_φ2, half_13_09_φ3, half_13_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_09_φ1, half_13_09_φ2, half_13_09_φ3, half_13_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_09_φ1, half_13_09_φ2, half_13_09_φ3, half_13_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_09 half_12_09
    (by simpa only [half_13_09_φ3, show (2:ℝ)*4=8 by norm_num] using half_13_09_hx3)
  exact h.weaken (by norm_num [half_13_09_φ1, half_13_09_φ2, half_13_09_φ3, half_13_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_09_hx1 : SourcePowerBound (powerBoxCross 18 12 2 half_13_09_φ1) (28795354922893/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 12) (u := 10) (t := 13)
    (D := 2) (ψ := (371975298471/10000000000000 : ℝ)) half_13_09_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_09_φ1, half_13_09_φ2, half_13_09_φ3, half_13_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_09_φ1, half_13_09_φ2, half_13_09_φ3, half_13_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_09_φ1, half_13_09_φ2, half_13_09_φ3, half_13_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_09 half_13_08
    (by simpa only [half_13_09_φ2, show (2:ℝ)*2=4 by norm_num] using half_13_09_hx2)
  exact h.weaken (by norm_num [half_13_09_φ1, half_13_09_φ2, half_13_09_φ3, half_13_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_09 : AdmissibleExponent 18 26 (7641221109631/500000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 11) (ψ := (76936065897/2000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_12_09
    (by simpa only [half_13_09_φ1] using half_13_09_hx1)
  exact admissibleExponent_mono h (by norm_num [half_13_09_φ1, half_13_09_φ2, half_13_09_φ3, half_13_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_14_09_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (49316886069/1250000000000 : ℝ)

def half_14_09_φ2 : Fin 2 → ℝ := Fin.snoc half_14_09_φ1 (383011325889/10000000000000 : ℝ)

def half_14_09_φ3 : Fin 3 → ℝ := Fin.snoc half_14_09_φ2 (183634544057/5000000000000 : ℝ)

def half_14_09_φ4 : Fin 4 → ℝ := Fin.snoc half_14_09_φ3 (166066774129/5000000000000 : ℝ)

def half_14_09_φ5 : Fin 5 → ℝ := Fin.snoc half_14_09_φ4 (12853332789/625000000000 : ℝ)

theorem half_14_09_hF2 : SourcePowerBound (paddedMoment 18 0 2 32 half_14_09_φ5) (84187278852713/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_14_09_φ5 (by norm_num [half_14_09_φ1, half_14_09_φ2, half_14_09_φ3, half_14_09_φ4, half_14_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_09_φ1, half_14_09_φ2, half_14_09_φ3, half_14_09_φ4, half_14_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_09_φ1, half_14_09_φ2, half_14_09_φ3, half_14_09_φ4, half_14_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_14_09_φ1, half_14_09_φ2, half_14_09_φ3, half_14_09_φ4, half_14_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_14_09_hx5 : SourcePowerBound (powerBoxCross 18 9 32 half_14_09_φ5) (53858106689657/5000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 9) (r := 2) (v := 12) (w := 12) (D := 32)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_14_09_φ5 (by norm_num [half_14_09_φ1, half_14_09_φ2, half_14_09_φ3, half_14_09_φ4, half_14_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_09_φ1, half_14_09_φ2, half_14_09_φ3, half_14_09_φ4, half_14_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_14_09_hF2 half_12_09 half_12_09
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_14_09_φ1, half_14_09_φ2, half_14_09_φ3, half_14_09_φ4, half_14_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_09_hx4 : SourcePowerBound (powerBoxCross 18 10 16 half_14_09_φ4) (116486975530777/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 10) (u := 8) (t := 11)
    (D := 16) (ψ := (12853332789/625000000000 : ℝ)) half_14_09_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_09_φ1, half_14_09_φ2, half_14_09_φ3, half_14_09_φ4, half_14_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_09_φ1, half_14_09_φ2, half_14_09_φ3, half_14_09_φ4, half_14_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_09_φ1, half_14_09_φ2, half_14_09_φ3, half_14_09_φ4, half_14_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_09 half_11_09
    (by simpa only [half_14_09_φ5, show (2:ℝ)*16=32 by norm_num] using half_14_09_hx5)
  exact h.weaken (by norm_num [half_14_09_φ1, half_14_09_φ2, half_14_09_φ3, half_14_09_φ4, half_14_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_09_hx3 : SourcePowerBound (powerBoxCross 18 11 8 half_14_09_φ3) (16022917199193/1250000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 11) (u := 9) (t := 12)
    (D := 8) (ψ := (166066774129/5000000000000 : ℝ)) half_14_09_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_09_φ1, half_14_09_φ2, half_14_09_φ3, half_14_09_φ4, half_14_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_09_φ1, half_14_09_φ2, half_14_09_φ3, half_14_09_φ4, half_14_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_09_φ1, half_14_09_φ2, half_14_09_φ3, half_14_09_φ4, half_14_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_09 half_12_09
    (by simpa only [half_14_09_φ4, show (2:ℝ)*8=16 by norm_num] using half_14_09_hx4)
  exact h.weaken (by norm_num [half_14_09_φ1, half_14_09_φ2, half_14_09_φ3, half_14_09_φ4, half_14_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_09_hx2 : SourcePowerBound (powerBoxCross 18 12 4 half_14_09_φ2) (141809656719787/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 12) (u := 10) (t := 13)
    (D := 4) (ψ := (183634544057/5000000000000 : ℝ)) half_14_09_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_09_φ1, half_14_09_φ2, half_14_09_φ3, half_14_09_φ4, half_14_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_09_φ1, half_14_09_φ2, half_14_09_φ3, half_14_09_φ4, half_14_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_09_φ1, half_14_09_φ2, half_14_09_φ3, half_14_09_φ4, half_14_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_09 half_13_09
    (by simpa only [half_14_09_φ3, show (2:ℝ)*4=8 by norm_num] using half_14_09_hx3)
  exact h.weaken (by norm_num [half_14_09_φ1, half_14_09_φ2, half_14_09_φ3, half_14_09_φ4, half_14_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_09_hx1 : SourcePowerBound (powerBoxCross 18 13 2 half_14_09_φ1) (4912171799591/312500000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 13) (u := 11) (t := 14)
    (D := 2) (ψ := (383011325889/10000000000000 : ℝ)) half_14_09_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_09_φ1, half_14_09_φ2, half_14_09_φ3, half_14_09_φ4, half_14_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_09_φ1, half_14_09_φ2, half_14_09_φ3, half_14_09_φ4, half_14_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_09_φ1, half_14_09_φ2, half_14_09_φ3, half_14_09_φ4, half_14_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_09 half_14_08
    (by simpa only [half_14_09_φ2, show (2:ℝ)*2=4 by norm_num] using half_14_09_hx2)
  exact h.weaken (by norm_num [half_14_09_φ1, half_14_09_φ2, half_14_09_φ3, half_14_09_φ4, half_14_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_09 : AdmissibleExponent 18 28 (20881609350089/1250000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 12) (ψ := (49316886069/1250000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_13_09
    (by simpa only [half_14_09_φ1] using half_14_09_hx1)
  exact admissibleExponent_mono h (by norm_num [half_14_09_φ1, half_14_09_φ2, half_14_09_φ3, half_14_09_φ4, half_14_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_15_09_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (403999976817/10000000000000 : ℝ)

def half_15_09_φ2 : Fin 2 → ℝ := Fin.snoc half_15_09_φ1 (393021190187/10000000000000 : ℝ)

def half_15_09_φ3 : Fin 3 → ℝ := Fin.snoc half_15_09_φ2 (94870611601/2500000000000 : ℝ)

def half_15_09_φ4 : Fin 4 → ℝ := Fin.snoc half_15_09_φ3 (355275572959/10000000000000 : ℝ)

def half_15_09_φ5 : Fin 5 → ℝ := Fin.snoc half_15_09_φ4 (56896693389/2000000000000 : ℝ)

theorem half_15_09_hF2 : SourcePowerBound (paddedMoment 18 0 2 32 half_15_09_φ5) (604457849071/78125000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_15_09_φ5 (by norm_num [half_15_09_φ1, half_15_09_φ2, half_15_09_φ3, half_15_09_φ4, half_15_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_09_φ1, half_15_09_φ2, half_15_09_φ3, half_15_09_φ4, half_15_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_09_φ1, half_15_09_φ2, half_15_09_φ3, half_15_09_φ4, half_15_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_15_09_φ1, half_15_09_φ2, half_15_09_φ3, half_15_09_φ4, half_15_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_15_09_hx5 : SourcePowerBound (powerBoxCross 18 10 32 half_15_09_φ5) (23210863799783/2000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 10) (r := 2) (v := 13) (w := 14) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_15_09_φ5 (by norm_num [half_15_09_φ1, half_15_09_φ2, half_15_09_φ3, half_15_09_φ4, half_15_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_09_φ1, half_15_09_φ2, half_15_09_φ3, half_15_09_φ4, half_15_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_15_09_hF2 half_13_09 half_14_09
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_15_09_φ1, half_15_09_φ2, half_15_09_φ3, half_15_09_φ4, half_15_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_09_hx4 : SourcePowerBound (powerBoxCross 18 11 16 half_15_09_φ4) (63268484530801/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 11) (u := 9) (t := 12)
    (D := 16) (ψ := (56896693389/2000000000000 : ℝ)) half_15_09_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_09_φ1, half_15_09_φ2, half_15_09_φ3, half_15_09_φ4, half_15_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_09_φ1, half_15_09_φ2, half_15_09_φ3, half_15_09_φ4, half_15_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_09_φ1, half_15_09_φ2, half_15_09_φ3, half_15_09_φ4, half_15_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_09 half_12_09
    (by simpa only [half_15_09_φ5, show (2:ℝ)*16=32 by norm_num] using half_15_09_hx5)
  exact h.weaken (by norm_num [half_15_09_φ1, half_15_09_φ2, half_15_09_φ3, half_15_09_φ4, half_15_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_09_hx3 : SourcePowerBound (powerBoxCross 18 12 8 half_15_09_φ3) (139420884182883/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 12) (u := 10) (t := 13)
    (D := 8) (ψ := (355275572959/10000000000000 : ℝ)) half_15_09_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_09_φ1, half_15_09_φ2, half_15_09_φ3, half_15_09_φ4, half_15_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_09_φ1, half_15_09_φ2, half_15_09_φ3, half_15_09_φ4, half_15_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_09_φ1, half_15_09_φ2, half_15_09_φ3, half_15_09_φ4, half_15_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_09 half_13_09
    (by simpa only [half_15_09_φ4, show (2:ℝ)*8=16 by norm_num] using half_15_09_hx4)
  exact h.weaken (by norm_num [half_15_09_φ1, half_15_09_φ2, half_15_09_φ3, half_15_09_φ4, half_15_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_09_hx2 : SourcePowerBound (powerBoxCross 18 13 4 half_15_09_φ2) (77084506922329/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 13) (u := 11) (t := 14)
    (D := 4) (ψ := (94870611601/2500000000000 : ℝ)) half_15_09_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_09_φ1, half_15_09_φ2, half_15_09_φ3, half_15_09_φ4, half_15_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_09_φ1, half_15_09_φ2, half_15_09_φ3, half_15_09_φ4, half_15_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_09_φ1, half_15_09_φ2, half_15_09_φ3, half_15_09_φ4, half_15_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_09 half_14_09
    (by simpa only [half_15_09_φ3, show (2:ℝ)*4=8 by norm_num] using half_15_09_hx3)
  exact h.weaken (by norm_num [half_15_09_φ1, half_15_09_φ2, half_15_09_φ3, half_15_09_φ4, half_15_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_09_hx1 : SourcePowerBound (powerBoxCross 18 14 2 half_15_09_φ1) (170707939022879/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 14) (u := 12) (t := 15)
    (D := 2) (ψ := (393021190187/10000000000000 : ℝ)) half_15_09_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_09_φ1, half_15_09_φ2, half_15_09_φ3, half_15_09_φ4, half_15_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_09_φ1, half_15_09_φ2, half_15_09_φ3, half_15_09_φ4, half_15_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_09_φ1, half_15_09_φ2, half_15_09_φ3, half_15_09_φ4, half_15_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_13_09 half_15_08
    (by simpa only [half_15_09_φ2, show (2:ℝ)*2=4 by norm_num] using half_15_09_hx2)
  exact h.weaken (by norm_num [half_15_09_φ1, half_15_09_φ2, half_15_09_φ3, half_15_09_φ4, half_15_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_09 : AdmissibleExponent 18 30 (90807969198469/5000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 13) (ψ := (403999976817/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_14_09
    (by simpa only [half_15_09_φ1] using half_15_09_hx1)
  exact admissibleExponent_mono h (by norm_num [half_15_09_φ1, half_15_09_φ2, half_15_09_φ3, half_15_09_φ4, half_15_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_16_09_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (51694818861/1250000000000 : ℝ)

def half_16_09_φ2 : Fin 2 → ℝ := Fin.snoc half_16_09_φ1 (201378664221/5000000000000 : ℝ)

def half_16_09_φ3 : Fin 3 → ℝ := Fin.snoc half_16_09_φ2 (391130866551/10000000000000 : ℝ)

def half_16_09_φ4 : Fin 4 → ℝ := Fin.snoc half_16_09_φ3 (374132676919/10000000000000 : ℝ)

def half_16_09_φ5 : Fin 5 → ℝ := Fin.snoc half_16_09_φ4 (168187729531/5000000000000 : ℝ)

def half_16_09_φ6 : Fin 6 → ℝ := Fin.snoc half_16_09_φ5 (208516178367/10000000000000 : ℝ)

theorem half_16_09_hF2 : SourcePowerBound (paddedMoment 18 0 2 64 half_16_09_φ6) (91549975928321/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 6) (r := 0) (D := 64)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_16_09_φ6 (by norm_num [half_16_09_φ1, half_16_09_φ2, half_16_09_φ3, half_16_09_φ4, half_16_09_φ5, half_16_09_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_09_φ1, half_16_09_φ2, half_16_09_φ3, half_16_09_φ4, half_16_09_φ5, half_16_09_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_09_φ1, half_16_09_φ2, half_16_09_φ3, half_16_09_φ4, half_16_09_φ5, half_16_09_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_16_09_φ1, half_16_09_φ2, half_16_09_φ3, half_16_09_φ4, half_16_09_φ5, half_16_09_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_16_09_hx6 : SourcePowerBound (powerBoxCross 18 10 64 half_16_09_φ6) (115933260629333/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 10) (r := 2) (v := 13) (w := 14) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_16_09_φ6 (by norm_num [half_16_09_φ1, half_16_09_φ2, half_16_09_φ3, half_16_09_φ4, half_16_09_φ5, half_16_09_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_09_φ1, half_16_09_φ2, half_16_09_φ3, half_16_09_φ4, half_16_09_φ5, half_16_09_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_16_09_hF2 half_13_09 half_14_09
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_16_09_φ1, half_16_09_φ2, half_16_09_φ3, half_16_09_φ4, half_16_09_φ5, half_16_09_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_09_hx5 : SourcePowerBound (powerBoxCross 18 11 32 half_16_09_φ5) (124789558067949/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 5) (s := 11) (u := 9) (t := 12)
    (D := 32) (ψ := (208516178367/10000000000000 : ℝ)) half_16_09_φ5
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_09_φ1, half_16_09_φ2, half_16_09_φ3, half_16_09_φ4, half_16_09_φ5, half_16_09_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_09_φ1, half_16_09_φ2, half_16_09_φ3, half_16_09_φ4, half_16_09_φ5, half_16_09_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_09_φ1, half_16_09_φ2, half_16_09_φ3, half_16_09_φ4, half_16_09_φ5, half_16_09_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_09 half_12_09
    (by simpa only [half_16_09_φ6, show (2:ℝ)*32=64 by norm_num] using half_16_09_hx6)
  exact h.weaken (by norm_num [half_16_09_φ1, half_16_09_φ2, half_16_09_φ3, half_16_09_φ4, half_16_09_φ5, half_16_09_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_09_hx4 : SourcePowerBound (powerBoxCross 18 12 16 half_16_09_φ4) (136810309284579/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 12) (u := 10) (t := 13)
    (D := 16) (ψ := (168187729531/5000000000000 : ℝ)) half_16_09_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_09_φ1, half_16_09_φ2, half_16_09_φ3, half_16_09_φ4, half_16_09_φ5, half_16_09_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_09_φ1, half_16_09_φ2, half_16_09_φ3, half_16_09_φ4, half_16_09_φ5, half_16_09_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_09_φ1, half_16_09_φ2, half_16_09_φ3, half_16_09_φ4, half_16_09_φ5, half_16_09_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_09 half_13_09
    (by simpa only [half_16_09_φ5, show (2:ℝ)*16=32 by norm_num] using half_16_09_hx5)
  exact h.weaken (by norm_num [half_16_09_φ1, half_16_09_φ2, half_16_09_φ3, half_16_09_φ4, half_16_09_φ5, half_16_09_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_09_hx3 : SourcePowerBound (powerBoxCross 18 13 8 half_16_09_φ3) (150885447983817/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 13) (u := 11) (t := 14)
    (D := 8) (ψ := (374132676919/10000000000000 : ℝ)) half_16_09_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_09_φ1, half_16_09_φ2, half_16_09_φ3, half_16_09_φ4, half_16_09_φ5, half_16_09_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_09_φ1, half_16_09_φ2, half_16_09_φ3, half_16_09_φ4, half_16_09_φ5, half_16_09_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_09_φ1, half_16_09_φ2, half_16_09_φ3, half_16_09_φ4, half_16_09_φ5, half_16_09_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_09 half_14_09
    (by simpa only [half_16_09_φ4, show (2:ℝ)*8=16 by norm_num] using half_16_09_hx4)
  exact h.weaken (by norm_num [half_16_09_φ1, half_16_09_φ2, half_16_09_φ3, half_16_09_φ4, half_16_09_φ5, half_16_09_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_09_hx2 : SourcePowerBound (powerBoxCross 18 14 4 half_16_09_φ2) (166788345325319/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 14) (u := 12) (t := 15)
    (D := 4) (ψ := (391130866551/10000000000000 : ℝ)) half_16_09_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_09_φ1, half_16_09_φ2, half_16_09_φ3, half_16_09_φ4, half_16_09_φ5, half_16_09_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_09_φ1, half_16_09_φ2, half_16_09_φ3, half_16_09_φ4, half_16_09_φ5, half_16_09_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_09_φ1, half_16_09_φ2, half_16_09_φ3, half_16_09_φ4, half_16_09_φ5, half_16_09_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_13_09 half_15_09
    (by simpa only [half_16_09_φ3, show (2:ℝ)*4=8 by norm_num] using half_16_09_hx3)
  exact h.weaken (by norm_num [half_16_09_φ1, half_16_09_φ2, half_16_09_φ3, half_16_09_φ4, half_16_09_φ5, half_16_09_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_09_hx1 : SourcePowerBound (powerBoxCross 18 15 2 half_16_09_φ1) (2306482681471/125000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 15) (u := 13) (t := 16)
    (D := 2) (ψ := (201378664221/5000000000000 : ℝ)) half_16_09_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_09_φ1, half_16_09_φ2, half_16_09_φ3, half_16_09_φ4, half_16_09_φ5, half_16_09_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_09_φ1, half_16_09_φ2, half_16_09_φ3, half_16_09_φ4, half_16_09_φ5, half_16_09_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_09_φ1, half_16_09_φ2, half_16_09_φ3, half_16_09_φ4, half_16_09_φ5, half_16_09_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_14_09 half_16_08
    (by simpa only [half_16_09_φ2, show (2:ℝ)*2=4 by norm_num] using half_16_09_hx2)
  exact h.weaken (by norm_num [half_16_09_φ1, half_16_09_φ2, half_16_09_φ3, half_16_09_φ4, half_16_09_φ5, half_16_09_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_09 : AdmissibleExponent 18 32 (24563976561679/1250000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 14) (ψ := (51694818861/1250000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_15_09
    (by simpa only [half_16_09_φ1] using half_16_09_hx1)
  exact admissibleExponent_mono h (by norm_num [half_16_09_φ1, half_16_09_φ2, half_16_09_φ3, half_16_09_φ4, half_16_09_φ5, half_16_09_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_17_09_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (52870843899/1250000000000 : ℝ)

def half_17_09_φ2 : Fin 2 → ℝ := Fin.snoc half_17_09_φ1 (412122068289/10000000000000 : ℝ)

def half_17_09_φ3 : Fin 3 → ℝ := Fin.snoc half_17_09_φ2 (16047780173/400000000000 : ℝ)

def half_17_09_φ4 : Fin 4 → ℝ := Fin.snoc half_17_09_φ3 (387192553653/10000000000000 : ℝ)

def half_17_09_φ5 : Fin 5 → ℝ := Fin.snoc half_17_09_φ4 (361506607717/10000000000000 : ℝ)

def half_17_09_φ6 : Fin 6 → ℝ := Fin.snoc half_17_09_φ5 (144891294139/5000000000000 : ℝ)

theorem half_17_09_hF2 : SourcePowerBound (paddedMoment 18 0 2 64 half_17_09_φ6) (41993490626923/5000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 6) (r := 0) (D := 64)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_17_09_φ6 (by norm_num [half_17_09_φ1, half_17_09_φ2, half_17_09_φ3, half_17_09_φ4, half_17_09_φ5, half_17_09_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_09_φ1, half_17_09_φ2, half_17_09_φ3, half_17_09_φ4, half_17_09_φ5, half_17_09_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_09_φ1, half_17_09_φ2, half_17_09_φ3, half_17_09_φ4, half_17_09_φ5, half_17_09_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_17_09_φ1, half_17_09_φ2, half_17_09_φ3, half_17_09_φ4, half_17_09_φ5, half_17_09_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_17_09_hx6 : SourcePowerBound (powerBoxCross 18 11 64 half_17_09_φ6) (61705551207147/5000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 11) (r := 2) (v := 14) (w := 15) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_17_09_φ6 (by norm_num [half_17_09_φ1, half_17_09_φ2, half_17_09_φ3, half_17_09_φ4, half_17_09_φ5, half_17_09_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_09_φ1, half_17_09_φ2, half_17_09_φ3, half_17_09_φ4, half_17_09_φ5, half_17_09_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_17_09_hF2 half_14_09 half_15_09
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_17_09_φ1, half_17_09_φ2, half_17_09_φ3, half_17_09_φ4, half_17_09_φ5, half_17_09_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_09_hx5 : SourcePowerBound (powerBoxCross 18 12 32 half_17_09_φ5) (67060219144203/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 5) (s := 12) (u := 10) (t := 13)
    (D := 32) (ψ := (144891294139/5000000000000 : ℝ)) half_17_09_φ5
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_09_φ1, half_17_09_φ2, half_17_09_φ3, half_17_09_φ4, half_17_09_φ5, half_17_09_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_09_φ1, half_17_09_φ2, half_17_09_φ3, half_17_09_φ4, half_17_09_φ5, half_17_09_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_09_φ1, half_17_09_φ2, half_17_09_φ3, half_17_09_φ4, half_17_09_φ5, half_17_09_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_09 half_13_09
    (by simpa only [half_17_09_φ6, show (2:ℝ)*32=64 by norm_num] using half_17_09_hx6)
  exact h.weaken (by norm_num [half_17_09_φ1, half_17_09_φ2, half_17_09_φ3, half_17_09_φ4, half_17_09_φ5, half_17_09_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_09_hx4 : SourcePowerBound (powerBoxCross 18 13 16 half_17_09_φ4) (147384121949947/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 13) (u := 11) (t := 14)
    (D := 16) (ψ := (361506607717/10000000000000 : ℝ)) half_17_09_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_09_φ1, half_17_09_φ2, half_17_09_φ3, half_17_09_φ4, half_17_09_φ5, half_17_09_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_09_φ1, half_17_09_φ2, half_17_09_φ3, half_17_09_φ4, half_17_09_φ5, half_17_09_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_09_φ1, half_17_09_φ2, half_17_09_φ3, half_17_09_φ4, half_17_09_φ5, half_17_09_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_09 half_14_09
    (by simpa only [half_17_09_φ5, show (2:ℝ)*16=32 by norm_num] using half_17_09_hx5)
  exact h.weaken (by norm_num [half_17_09_φ1, half_17_09_φ2, half_17_09_φ3, half_17_09_φ4, half_17_09_φ5, half_17_09_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_09_hx3 : SourcePowerBound (powerBoxCross 18 14 8 half_17_09_φ3) (162605091042879/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 14) (u := 12) (t := 15)
    (D := 8) (ψ := (387192553653/10000000000000 : ℝ)) half_17_09_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_09_φ1, half_17_09_φ2, half_17_09_φ3, half_17_09_φ4, half_17_09_φ5, half_17_09_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_09_φ1, half_17_09_φ2, half_17_09_φ3, half_17_09_φ4, half_17_09_φ5, half_17_09_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_09_φ1, half_17_09_φ2, half_17_09_φ3, half_17_09_φ4, half_17_09_φ5, half_17_09_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_13_09 half_15_09
    (by simpa only [half_17_09_φ4, show (2:ℝ)*8=16 by norm_num] using half_17_09_hx4)
  exact h.weaken (by norm_num [half_17_09_φ1, half_17_09_φ2, half_17_09_φ3, half_17_09_φ4, half_17_09_φ5, half_17_09_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_09_hx2 : SourcePowerBound (powerBoxCross 18 15 4 half_17_09_φ2) (89835540867747/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 15) (u := 13) (t := 16)
    (D := 4) (ψ := (16047780173/400000000000 : ℝ)) half_17_09_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_09_φ1, half_17_09_φ2, half_17_09_φ3, half_17_09_φ4, half_17_09_φ5, half_17_09_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_09_φ1, half_17_09_φ2, half_17_09_φ3, half_17_09_φ4, half_17_09_φ5, half_17_09_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_09_φ1, half_17_09_φ2, half_17_09_φ3, half_17_09_φ4, half_17_09_φ5, half_17_09_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_14_09 half_16_09
    (by simpa only [half_17_09_φ3, show (2:ℝ)*4=8 by norm_num] using half_17_09_hx3)
  exact h.weaken (by norm_num [half_17_09_φ1, half_17_09_φ2, half_17_09_φ3, half_17_09_φ4, half_17_09_φ5, half_17_09_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_09_hx1 : SourcePowerBound (powerBoxCross 18 16 2 half_17_09_φ1) (49655745738629/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 16) (u := 14) (t := 17)
    (D := 2) (ψ := (412122068289/10000000000000 : ℝ)) half_17_09_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_09_φ1, half_17_09_φ2, half_17_09_φ3, half_17_09_φ4, half_17_09_φ5, half_17_09_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_09_φ1, half_17_09_φ2, half_17_09_φ3, half_17_09_φ4, half_17_09_φ5, half_17_09_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_09_φ1, half_17_09_φ2, half_17_09_φ3, half_17_09_φ4, half_17_09_φ5, half_17_09_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_15_09 half_17_08
    (by simpa only [half_17_09_φ2, show (2:ℝ)*2=4 by norm_num] using half_17_09_hx2)
  exact h.weaken (by norm_num [half_17_09_φ1, half_17_09_φ2, half_17_09_φ3, half_17_09_φ4, half_17_09_φ5, half_17_09_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_09 : AdmissibleExponent 18 34 (52933738060367/2500000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 15) (ψ := (52870843899/1250000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_16_09
    (by simpa only [half_17_09_φ1] using half_17_09_hx1)
  exact admissibleExponent_mono h (by norm_num [half_17_09_φ1, half_17_09_φ2, half_17_09_φ3, half_17_09_φ4, half_17_09_φ5, half_17_09_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])


end Waring.SeedCompletionHigher18SimpleSeeds
