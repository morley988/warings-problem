import Waring.SeedCompletionHigher18SimpleSeedsC10

noncomputable section
set_option maxHeartbeats 2000000
namespace Waring.SeedCompletionHigher18SimpleSeeds
open SmoothMoments FirstStageTransport SeedCompletionNaturalBox
open SeedCompletionSourceBounds SeedCompletionPaddedSource SeedCompletionGeneralTerminal
open PolicyCompletionMajorPowerRanges

def half_9_11_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (171919432681/5000000000000 : ℝ)

def half_9_11_φ2 : Fin 2 → ℝ := Fin.snoc half_9_11_φ1 (154172593177/5000000000000 : ℝ)

def half_9_11_φ3 : Fin 3 → ℝ := Fin.snoc half_9_11_φ2 (1075569441/80000000000 : ℝ)

theorem half_9_11_hF2 : SourcePowerBound (paddedMoment 18 0 2 8 half_9_11_φ3) (69881858176109/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_11_φ3 (by norm_num [half_9_11_φ1, half_9_11_φ2, half_9_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_11_φ1, half_9_11_φ2, half_9_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_11_φ1, half_9_11_φ2, half_9_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_11_φ1, half_9_11_φ2, half_9_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_9_11_hF1 : SourcePowerBound (paddedMoment 18 0 1 8 half_9_11_φ3) (26627286058703/10000000000000 : ℝ) := by
  have h := padded_second_power (k := 18) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_11_φ3 (by norm_num [half_9_11_φ1, half_9_11_φ2, half_9_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_11_φ1, half_9_11_φ2, half_9_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_11_φ1, half_9_11_φ2, half_9_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_11_φ1, half_9_11_φ2, half_9_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_9_11_hx3 : SourcePowerBound (powerBoxCross 18 6 8 half_9_11_φ3) (38496516924617/5000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 18) (s := 6) (r := 1) (v := 2) (t := 10) (D := 8)
    (a := (3/10 : ℝ)) (b := (1/10 : ℝ)) (c := (3/5 : ℝ))
    (by norm_num) half_9_11_φ3 (by norm_num [half_9_11_φ1, half_9_11_φ2, half_9_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_11_φ1, half_9_11_φ2, half_9_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_9_11_hF1 half_9_11_hF2 half_10_10
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_9_11_φ1, half_9_11_φ2, half_9_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_9_11_hx2 : SourcePowerBound (powerBoxCross 18 7 4 half_9_11_φ2) (10533677582659/1250000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 7) (u := 5) (t := 8)
    (D := 4) (ψ := (1075569441/80000000000 : ℝ)) half_9_11_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_11_φ1, half_9_11_φ2, half_9_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_11_φ1, half_9_11_φ2, half_9_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_11_φ1, half_9_11_φ2, half_9_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_6 SeedCompletionEven18SecondSeeds.degree18_half_8
    (by simpa only [half_9_11_φ3, show (2:ℝ)*4=8 by norm_num] using half_9_11_hx3)
  exact h.weaken (by norm_num [half_9_11_φ1, half_9_11_φ2, half_9_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_9_11_hx1 : SourcePowerBound (powerBoxCross 18 8 2 half_9_11_φ1) (94174797777249/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 8) (u := 6) (t := 9)
    (D := 2) (ψ := (154172593177/5000000000000 : ℝ)) half_9_11_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_11_φ1, half_9_11_φ2, half_9_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_11_φ1, half_9_11_φ2, half_9_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_11_φ1, half_9_11_φ2, half_9_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_7 half_9_10
    (by simpa only [half_9_11_φ2, show (2:ℝ)*2=4 by norm_num] using half_9_11_hx2)
  exact h.weaken (by norm_num [half_9_11_φ1, half_9_11_φ2, half_9_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_9_11 : AdmissibleExponent 18 18 (99332380757679/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 7) (ψ := (171919432681/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_8
    (by simpa only [half_9_11_φ1] using half_9_11_hx1)
  exact admissibleExponent_mono h (by norm_num [half_9_11_φ1, half_9_11_φ2, half_9_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_10_11_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (176874483743/5000000000000 : ℝ)

def half_10_11_φ2 : Fin 2 → ℝ := Fin.snoc half_10_11_φ1 (329256596433/10000000000000 : ℝ)

def half_10_11_φ3 : Fin 3 → ℝ := Fin.snoc half_10_11_φ2 (45987781969/2000000000000 : ℝ)

theorem half_10_11_hF2 : SourcePowerBound (paddedMoment 18 0 2 8 half_10_11_φ3) (15859957959509/2500000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_10_11_φ3 (by norm_num [half_10_11_φ1, half_10_11_φ2, half_10_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_11_φ1, half_10_11_φ2, half_10_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_11_φ1, half_10_11_φ2, half_10_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_10_11_φ1, half_10_11_φ2, half_10_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_10_11_hx3 : SourcePowerBound (powerBoxCross 18 7 8 half_10_11_φ3) (86477909640223/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 7) (r := 2) (v := 9) (w := 10) (D := 8)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_10_11_φ3 (by norm_num [half_10_11_φ1, half_10_11_φ2, half_10_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_11_φ1, half_10_11_φ2, half_10_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_10_11_hF2 half_9_11 half_10_10
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_10_11_φ1, half_10_11_φ2, half_10_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_11_hx2 : SourcePowerBound (powerBoxCross 18 8 4 half_10_11_φ2) (23800493095723/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 8) (u := 6) (t := 9)
    (D := 4) (ψ := (45987781969/2000000000000 : ℝ)) half_10_11_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_11_φ1, half_10_11_φ2, half_10_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_11_φ1, half_10_11_φ2, half_10_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_11_φ1, half_10_11_φ2, half_10_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_7 half_9_11
    (by simpa only [half_10_11_φ3, show (2:ℝ)*4=8 by norm_num] using half_10_11_hx3)
  exact h.weaken (by norm_num [half_10_11_φ1, half_10_11_φ2, half_10_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_11_hx1 : SourcePowerBound (powerBoxCross 18 9 2 half_10_11_φ1) (106172257012081/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 9) (u := 7) (t := 10)
    (D := 2) (ψ := (329256596433/10000000000000 : ℝ)) half_10_11_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_11_φ1, half_10_11_φ2, half_10_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_11_φ1, half_10_11_φ2, half_10_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_11_φ1, half_10_11_φ2, half_10_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_8 half_10_10
    (by simpa only [half_10_11_φ2, show (2:ℝ)*2=4 by norm_num] using half_10_11_hx2)
  exact h.weaken (by norm_num [half_10_11_φ1, half_10_11_φ2, half_10_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_11 : AdmissibleExponent 18 20 (112185989459343/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 8) (ψ := (176874483743/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_9_11
    (by simpa only [half_10_11_φ1] using half_10_11_hx1)
  exact admissibleExponent_mono h (by norm_num [half_10_11_φ1, half_10_11_φ2, half_10_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_11_11_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (91187233521/2500000000000 : ℝ)

def half_11_11_φ2 : Fin 2 → ℝ := Fin.snoc half_11_11_φ1 (86598782817/2500000000000 : ℝ)

def half_11_11_φ3 : Fin 3 → ℝ := Fin.snoc half_11_11_φ2 (294729753227/10000000000000 : ℝ)

theorem half_11_11_hF2 : SourcePowerBound (paddedMoment 18 0 2 8 half_11_11_φ3) (58700435252471/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_11_11_φ3 (by norm_num [half_11_11_φ1, half_11_11_φ2, half_11_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_11_φ1, half_11_11_φ2, half_11_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_11_φ1, half_11_11_φ2, half_11_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_11_11_φ1, half_11_11_φ2, half_11_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_11_11_hx3 : SourcePowerBound (powerBoxCross 18 8 8 half_11_11_φ3) (48144357409821/5000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 8) (r := 2) (v := 10) (w := 11) (D := 8)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_11_11_φ3 (by norm_num [half_11_11_φ1, half_11_11_φ2, half_11_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_11_φ1, half_11_11_φ2, half_11_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_11_11_hF2 half_10_11 half_11_10
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_11_11_φ1, half_11_11_φ2, half_11_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_11_hx2 : SourcePowerBound (powerBoxCross 18 9 4 half_11_11_φ2) (106414080702223/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 9) (u := 7) (t := 10)
    (D := 4) (ψ := (294729753227/10000000000000 : ℝ)) half_11_11_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_11_φ1, half_11_11_φ2, half_11_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_11_φ1, half_11_11_φ2, half_11_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_11_φ1, half_11_11_φ2, half_11_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_8 half_10_11
    (by simpa only [half_11_11_φ3, show (2:ℝ)*4=8 by norm_num] using half_11_11_hx3)
  exact h.weaken (by norm_num [half_11_11_φ1, half_11_11_φ2, half_11_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_11_hx1 : SourcePowerBound (powerBoxCross 18 10 2 half_11_11_φ1) (118458766385993/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 10) (u := 8) (t := 11)
    (D := 2) (ψ := (86598782817/2500000000000 : ℝ)) half_11_11_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_11_φ1, half_11_11_φ2, half_11_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_11_φ1, half_11_11_φ2, half_11_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_11_φ1, half_11_11_φ2, half_11_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_11 half_11_10
    (by simpa only [half_11_11_φ2, show (2:ℝ)*2=4 by norm_num] using half_11_11_hx2)
  exact h.weaken (by norm_num [half_11_11_φ1, half_11_11_φ2, half_11_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_11 : AdmissibleExponent 18 22 (125388996133589/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 9) (ψ := (91187233521/2500000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_10_11
    (by simpa only [half_11_11_φ1] using half_11_11_hx1)
  exact admissibleExponent_mono h (by norm_num [half_11_11_φ1, half_11_11_φ2, half_11_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_12_11_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (374944503777/10000000000000 : ℝ)

def half_12_11_φ2 : Fin 2 → ℝ := Fin.snoc half_12_11_φ1 (360587079131/10000000000000 : ℝ)

def half_12_11_φ3 : Fin 3 → ℝ := Fin.snoc half_12_11_φ2 (329430349561/10000000000000 : ℝ)

def half_12_11_φ4 : Fin 4 → ℝ := Fin.snoc half_12_11_φ3 (106454325277/5000000000000 : ℝ)

theorem half_12_11_hF2 : SourcePowerBound (paddedMoment 18 0 2 16 half_12_11_φ4) (74828600265827/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_12_11_φ4 (by norm_num [half_12_11_φ1, half_12_11_φ2, half_12_11_φ3, half_12_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_11_φ1, half_12_11_φ2, half_12_11_φ3, half_12_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_11_φ1, half_12_11_φ2, half_12_11_φ3, half_12_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_12_11_φ1, half_12_11_φ2, half_12_11_φ3, half_12_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_12_11_hF1 : SourcePowerBound (paddedMoment 18 0 1 16 half_12_11_φ4) (28276200088609/10000000000000 : ℝ) := by
  have h := padded_second_power (k := 18) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_12_11_φ4 (by norm_num [half_12_11_φ1, half_12_11_φ2, half_12_11_φ3, half_12_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_11_φ1, half_12_11_φ2, half_12_11_φ3, half_12_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_11_φ1, half_12_11_φ2, half_12_11_φ3, half_12_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_12_11_φ1, half_12_11_φ2, half_12_11_φ3, half_12_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_12_11_hx4 : SourcePowerBound (powerBoxCross 18 8 16 half_12_11_φ4) (24457655502329/2500000000000 : ℝ) := by
  have h := full_B_cross_power (k := 18) (s := 8) (r := 1) (v := 2) (t := 11) (D := 16)
    (a := (1/22 : ℝ)) (b := (5/22 : ℝ)) (c := (8/11 : ℝ))
    (by norm_num) half_12_11_φ4 (by norm_num [half_12_11_φ1, half_12_11_φ2, half_12_11_φ3, half_12_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_11_φ1, half_12_11_φ2, half_12_11_φ3, half_12_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_12_11_hF1 half_12_11_hF2 half_11_11
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_12_11_φ1, half_12_11_φ2, half_12_11_φ3, half_12_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_11_hx3 : SourcePowerBound (powerBoxCross 18 9 8 half_12_11_φ3) (106579253780973/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 9) (u := 7) (t := 10)
    (D := 8) (ψ := (106454325277/5000000000000 : ℝ)) half_12_11_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_11_φ1, half_12_11_φ2, half_12_11_φ3, half_12_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_11_φ1, half_12_11_φ2, half_12_11_φ3, half_12_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_11_φ1, half_12_11_φ2, half_12_11_φ3, half_12_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_8 half_10_11
    (by simpa only [half_12_11_φ4, show (2:ℝ)*8=16 by norm_num] using half_12_11_hx4)
  exact h.weaken (by norm_num [half_12_11_φ1, half_12_11_φ2, half_12_11_φ3, half_12_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_11_hx2 : SourcePowerBound (powerBoxCross 18 10 4 half_12_11_φ2) (117920886133563/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 10) (u := 8) (t := 11)
    (D := 4) (ψ := (329430349561/10000000000000 : ℝ)) half_12_11_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_11_φ1, half_12_11_φ2, half_12_11_φ3, half_12_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_11_φ1, half_12_11_φ2, half_12_11_φ3, half_12_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_11_φ1, half_12_11_φ2, half_12_11_φ3, half_12_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_11 half_11_11
    (by simpa only [half_12_11_φ3, show (2:ℝ)*4=8 by norm_num] using half_12_11_hx3)
  exact h.weaken (by norm_num [half_12_11_φ1, half_12_11_φ2, half_12_11_φ3, half_12_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_11_hx1 : SourcePowerBound (powerBoxCross 18 11 2 half_12_11_φ1) (131062549143947/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 11) (u := 9) (t := 12)
    (D := 2) (ψ := (360587079131/10000000000000 : ℝ)) half_12_11_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_11_φ1, half_12_11_φ2, half_12_11_φ3, half_12_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_11_φ1, half_12_11_φ2, half_12_11_φ3, half_12_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_11_φ1, half_12_11_φ2, half_12_11_φ3, half_12_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_11 half_12_10
    (by simpa only [half_12_11_φ2, show (2:ℝ)*2=4 by norm_num] using half_12_11_hx2)
  exact h.weaken (by norm_num [half_12_11_φ1, half_12_11_φ2, half_12_11_φ3, half_12_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_11 : AdmissibleExponent 18 24 (542720248919/39062500000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 10) (ψ := (374944503777/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_11_11
    (by simpa only [half_12_11_φ1] using half_12_11_hx1)
  exact admissibleExponent_mono h (by norm_num [half_12_11_φ1, half_12_11_φ2, half_12_11_φ3, half_12_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_13_11_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (192306359923/5000000000000 : ℝ)

def half_13_11_φ2 : Fin 2 → ℝ := Fin.snoc half_13_11_φ1 (371969085369/10000000000000 : ℝ)

def half_13_11_φ3 : Fin 3 → ℝ := Fin.snoc half_13_11_φ2 (349894210779/10000000000000 : ℝ)

def half_13_11_φ4 : Fin 4 → ℝ := Fin.snoc half_13_11_φ3 (283317356409/10000000000000 : ℝ)

theorem half_13_11_hF2 : SourcePowerBound (paddedMoment 18 0 2 16 half_13_11_φ4) (69120538007447/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_13_11_φ4 (by norm_num [half_13_11_φ1, half_13_11_φ2, half_13_11_φ3, half_13_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_11_φ1, half_13_11_φ2, half_13_11_φ3, half_13_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_11_φ1, half_13_11_φ2, half_13_11_φ3, half_13_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_13_11_φ1, half_13_11_φ2, half_13_11_φ3, half_13_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_13_11_hx4 : SourcePowerBound (powerBoxCross 18 9 16 half_13_11_φ4) (107000457397993/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 9) (r := 2) (v := 12) (w := 12) (D := 16)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_13_11_φ4 (by norm_num [half_13_11_φ1, half_13_11_φ2, half_13_11_φ3, half_13_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_11_φ1, half_13_11_φ2, half_13_11_φ3, half_13_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_13_11_hF2 half_12_11 half_12_11
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_13_11_φ1, half_13_11_φ2, half_13_11_φ3, half_13_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_11_hx3 : SourcePowerBound (powerBoxCross 18 10 8 half_13_11_φ3) (469043529259/40000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 10) (u := 8) (t := 11)
    (D := 8) (ψ := (283317356409/10000000000000 : ℝ)) half_13_11_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_11_φ1, half_13_11_φ2, half_13_11_φ3, half_13_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_11_φ1, half_13_11_φ2, half_13_11_φ3, half_13_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_11_φ1, half_13_11_φ2, half_13_11_φ3, half_13_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_11 half_11_11
    (by simpa only [half_13_11_φ4, show (2:ℝ)*8=16 by norm_num] using half_13_11_hx4)
  exact h.weaken (by norm_num [half_13_11_φ1, half_13_11_φ2, half_13_11_φ3, half_13_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_11_hx2 : SourcePowerBound (powerBoxCross 18 11 4 half_13_11_φ2) (129735845676711/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 11) (u := 9) (t := 12)
    (D := 4) (ψ := (349894210779/10000000000000 : ℝ)) half_13_11_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_11_φ1, half_13_11_φ2, half_13_11_φ3, half_13_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_11_φ1, half_13_11_φ2, half_13_11_φ3, half_13_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_11_φ1, half_13_11_φ2, half_13_11_φ3, half_13_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_11 half_12_11
    (by simpa only [half_13_11_φ3, show (2:ℝ)*4=8 by norm_num] using half_13_11_hx3)
  exact h.weaken (by norm_num [half_13_11_φ1, half_13_11_φ2, half_13_11_φ3, half_13_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_11_hx1 : SourcePowerBound (powerBoxCross 18 12 2 half_13_11_φ1) (7198866320009/500000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 12) (u := 10) (t := 13)
    (D := 2) (ψ := (371969085369/10000000000000 : ℝ)) half_13_11_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_11_φ1, half_13_11_φ2, half_13_11_φ3, half_13_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_11_φ1, half_13_11_φ2, half_13_11_φ3, half_13_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_11_φ1, half_13_11_φ2, half_13_11_φ3, half_13_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_11 half_13_10
    (by simpa only [half_13_11_φ2, show (2:ℝ)*2=4 by norm_num] using half_13_11_hx2)
  exact h.weaken (by norm_num [half_13_11_φ1, half_13_11_φ2, half_13_11_φ3, half_13_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_11 : AdmissibleExponent 18 26 (76411709478319/5000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 11) (ψ := (192306359923/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_12_11
    (by simpa only [half_13_11_φ1] using half_13_11_hx1)
  exact admissibleExponent_mono h (by norm_num [half_13_11_φ1, half_13_11_φ2, half_13_11_φ3, half_13_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_14_11_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (394383210481/10000000000000 : ℝ)

def half_14_11_φ2 : Fin 2 → ℝ := Fin.snoc half_14_11_φ1 (382998439547/10000000000000 : ℝ)

def half_14_11_φ3 : Fin 3 → ℝ := Fin.snoc half_14_11_φ2 (367261695003/10000000000000 : ℝ)

def half_14_11_φ4 : Fin 4 → ℝ := Fin.snoc half_14_11_φ3 (6642355631/200000000000 : ℝ)

def half_14_11_φ5 : Fin 5 → ℝ := Fin.snoc half_14_11_φ4 (51397323771/2500000000000 : ℝ)

theorem half_14_11_hF2 : SourcePowerBound (paddedMoment 18 0 2 32 half_14_11_φ5) (16840025699017/2000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_14_11_φ5 (by norm_num [half_14_11_φ1, half_14_11_φ2, half_14_11_φ3, half_14_11_φ4, half_14_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_11_φ1, half_14_11_φ2, half_14_11_φ3, half_14_11_φ4, half_14_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_11_φ1, half_14_11_φ2, half_14_11_φ3, half_14_11_φ4, half_14_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_14_11_φ1, half_14_11_φ2, half_14_11_φ3, half_14_11_φ4, half_14_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_14_11_hx5 : SourcePowerBound (powerBoxCross 18 9 32 half_14_11_φ5) (107721843635611/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 9) (r := 2) (v := 12) (w := 12) (D := 32)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_14_11_φ5 (by norm_num [half_14_11_φ1, half_14_11_φ2, half_14_11_φ3, half_14_11_φ4, half_14_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_11_φ1, half_14_11_φ2, half_14_11_φ3, half_14_11_φ4, half_14_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_14_11_hF2 half_12_11 half_12_11
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_14_11_φ1, half_14_11_φ2, half_14_11_φ3, half_14_11_φ4, half_14_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_11_hx4 : SourcePowerBound (powerBoxCross 18 10 16 half_14_11_φ4) (4659679182293/400000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 10) (u := 8) (t := 11)
    (D := 16) (ψ := (51397323771/2500000000000 : ℝ)) half_14_11_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_11_φ1, half_14_11_φ2, half_14_11_φ3, half_14_11_φ4, half_14_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_11_φ1, half_14_11_φ2, half_14_11_φ3, half_14_11_φ4, half_14_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_11_φ1, half_14_11_φ2, half_14_11_φ3, half_14_11_φ4, half_14_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_11 half_11_11
    (by simpa only [half_14_11_φ5, show (2:ℝ)*16=32 by norm_num] using half_14_11_hx5)
  exact h.weaken (by norm_num [half_14_11_φ1, half_14_11_φ2, half_14_11_φ3, half_14_11_φ4, half_14_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_11_hx3 : SourcePowerBound (powerBoxCross 18 11 8 half_14_11_φ3) (128188201781681/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 11) (u := 9) (t := 12)
    (D := 8) (ψ := (6642355631/200000000000 : ℝ)) half_14_11_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_11_φ1, half_14_11_φ2, half_14_11_φ3, half_14_11_φ4, half_14_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_11_φ1, half_14_11_φ2, half_14_11_φ3, half_14_11_φ4, half_14_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_11_φ1, half_14_11_φ2, half_14_11_φ3, half_14_11_φ4, half_14_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_11 half_12_11
    (by simpa only [half_14_11_φ4, show (2:ℝ)*8=16 by norm_num] using half_14_11_hx4)
  exact h.weaken (by norm_num [half_14_11_φ1, half_14_11_φ2, half_14_11_φ3, half_14_11_φ4, half_14_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_11_hx2 : SourcePowerBound (powerBoxCross 18 12 4 half_14_11_φ2) (70907104030941/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 12) (u := 10) (t := 13)
    (D := 4) (ψ := (367261695003/10000000000000 : ℝ)) half_14_11_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_11_φ1, half_14_11_φ2, half_14_11_φ3, half_14_11_φ4, half_14_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_11_φ1, half_14_11_φ2, half_14_11_φ3, half_14_11_φ4, half_14_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_11_φ1, half_14_11_φ2, half_14_11_φ3, half_14_11_φ4, half_14_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_11 half_13_11
    (by simpa only [half_14_11_φ3, show (2:ℝ)*4=8 by norm_num] using half_14_11_hx3)
  exact h.weaken (by norm_num [half_14_11_φ1, half_14_11_φ2, half_14_11_φ3, half_14_11_φ4, half_14_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_11_hx1 : SourcePowerBound (powerBoxCross 18 13 2 half_14_11_φ1) (4912209472083/312500000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 13) (u := 11) (t := 14)
    (D := 2) (ψ := (382998439547/10000000000000 : ℝ)) half_14_11_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_11_φ1, half_14_11_φ2, half_14_11_φ3, half_14_11_φ4, half_14_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_11_φ1, half_14_11_φ2, half_14_11_φ3, half_14_11_φ4, half_14_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_11_φ1, half_14_11_φ2, half_14_11_φ3, half_14_11_φ4, half_14_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_11 half_14_10
    (by simpa only [half_14_11_φ2, show (2:ℝ)*2=4 by norm_num] using half_14_11_hx2)
  exact h.weaken (by norm_num [half_14_11_φ1, half_14_11_φ2, half_14_11_φ3, half_14_11_φ4, half_14_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_11 : AdmissibleExponent 18 28 (167050283368681/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 12) (ψ := (394383210481/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_13_11
    (by simpa only [half_14_11_φ1] using half_14_11_hx1)
  exact admissibleExponent_mono h (by norm_num [half_14_11_φ1, half_14_11_φ2, half_14_11_φ3, half_14_11_φ4, half_14_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_15_11_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (403692309021/10000000000000 : ℝ)

def half_15_11_φ2 : Fin 2 → ℝ := Fin.snoc half_15_11_φ1 (39299227531/1000000000000 : ℝ)

def half_15_11_φ3 : Fin 3 → ℝ := Fin.snoc half_15_11_φ2 (94865158713/2500000000000 : ℝ)

def half_15_11_φ4 : Fin 4 → ℝ := Fin.snoc half_15_11_φ3 (355231692813/10000000000000 : ℝ)

def half_15_11_φ5 : Fin 5 → ℝ := Fin.snoc half_15_11_φ4 (35539569779/1250000000000 : ℝ)

theorem half_15_11_hF2 : SourcePowerBound (paddedMoment 18 0 2 32 half_15_11_φ5) (19349908254593/2500000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_15_11_φ5 (by norm_num [half_15_11_φ1, half_15_11_φ2, half_15_11_φ3, half_15_11_φ4, half_15_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_11_φ1, half_15_11_φ2, half_15_11_φ3, half_15_11_φ4, half_15_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_11_φ1, half_15_11_φ2, half_15_11_φ3, half_15_11_φ4, half_15_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_15_11_φ1, half_15_11_φ2, half_15_11_φ3, half_15_11_φ4, half_15_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_15_11_hx5 : SourcePowerBound (powerBoxCross 18 10 32 half_15_11_φ5) (58033680831201/5000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 10) (r := 2) (v := 13) (w := 14) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_15_11_φ5 (by norm_num [half_15_11_φ1, half_15_11_φ2, half_15_11_φ3, half_15_11_φ4, half_15_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_11_φ1, half_15_11_φ2, half_15_11_φ3, half_15_11_φ4, half_15_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_15_11_hF2 half_13_11 half_14_11
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_15_11_φ1, half_15_11_φ2, half_15_11_φ3, half_15_11_φ4, half_15_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_11_hx4 : SourcePowerBound (powerBoxCross 18 11 16 half_15_11_φ4) (126547977730571/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 11) (u := 9) (t := 12)
    (D := 16) (ψ := (35539569779/1250000000000 : ℝ)) half_15_11_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_11_φ1, half_15_11_φ2, half_15_11_φ3, half_15_11_φ4, half_15_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_11_φ1, half_15_11_φ2, half_15_11_φ3, half_15_11_φ4, half_15_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_11_φ1, half_15_11_φ2, half_15_11_φ3, half_15_11_φ4, half_15_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_11 half_12_11
    (by simpa only [half_15_11_φ5, show (2:ℝ)*16=32 by norm_num] using half_15_11_hx5)
  exact h.weaken (by norm_num [half_15_11_φ1, half_15_11_φ2, half_15_11_φ3, half_15_11_φ4, half_15_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_11_hx3 : SourcePowerBound (powerBoxCross 18 12 8 half_15_11_φ3) (139431270075833/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 12) (u := 10) (t := 13)
    (D := 8) (ψ := (355231692813/10000000000000 : ℝ)) half_15_11_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_11_φ1, half_15_11_φ2, half_15_11_φ3, half_15_11_φ4, half_15_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_11_φ1, half_15_11_φ2, half_15_11_φ3, half_15_11_φ4, half_15_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_11_φ1, half_15_11_φ2, half_15_11_φ3, half_15_11_φ4, half_15_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_11 half_13_11
    (by simpa only [half_15_11_φ4, show (2:ℝ)*8=16 by norm_num] using half_15_11_hx4)
  exact h.weaken (by norm_num [half_15_11_φ1, half_15_11_φ2, half_15_11_φ3, half_15_11_φ4, half_15_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_11_hx2 : SourcePowerBound (powerBoxCross 18 13 4 half_15_11_φ2) (38544608944461/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 13) (u := 11) (t := 14)
    (D := 4) (ψ := (94865158713/2500000000000 : ℝ)) half_15_11_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_11_φ1, half_15_11_φ2, half_15_11_φ3, half_15_11_φ4, half_15_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_11_φ1, half_15_11_φ2, half_15_11_φ3, half_15_11_φ4, half_15_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_11_φ1, half_15_11_φ2, half_15_11_φ3, half_15_11_φ4, half_15_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_11 half_14_11
    (by simpa only [half_15_11_φ3, show (2:ℝ)*4=8 by norm_num] using half_15_11_hx3)
  exact h.weaken (by norm_num [half_15_11_φ1, half_15_11_φ2, half_15_11_φ3, half_15_11_φ4, half_15_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_11_hx1 : SourcePowerBound (powerBoxCross 18 14 2 half_15_11_φ1) (34142056843229/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 14) (u := 12) (t := 15)
    (D := 2) (ψ := (39299227531/1000000000000 : ℝ)) half_15_11_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_11_φ1, half_15_11_φ2, half_15_11_φ3, half_15_11_φ4, half_15_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_11_φ1, half_15_11_φ2, half_15_11_φ3, half_15_11_φ4, half_15_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_11_φ1, half_15_11_φ2, half_15_11_φ3, half_15_11_φ4, half_15_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_13_11 half_15_10
    (by simpa only [half_15_11_φ2, show (2:ℝ)*2=4 by norm_num] using half_15_11_hx2)
  exact h.weaken (by norm_num [half_15_11_φ1, half_15_11_φ2, half_15_11_φ3, half_15_11_φ4, half_15_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_11 : AdmissibleExponent 18 30 (5675311767491/312500000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 13) (ψ := (403692309021/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_14_11
    (by simpa only [half_15_11_φ1] using half_15_11_hx1)
  exact admissibleExponent_mono h (by norm_num [half_15_11_φ1, half_15_11_φ2, half_15_11_φ3, half_15_11_φ4, half_15_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_16_11_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (41300544369/1000000000000 : ℝ)

def half_16_11_φ2 : Fin 2 → ℝ := Fin.snoc half_16_11_φ1 (100676237397/2500000000000 : ℝ)

def half_16_11_φ3 : Fin 3 → ℝ := Fin.snoc half_16_11_φ2 (195551050183/5000000000000 : ℝ)

def half_16_11_φ4 : Fin 4 → ℝ := Fin.snoc half_16_11_φ3 (187053342423/5000000000000 : ℝ)

def half_16_11_φ5 : Fin 5 → ℝ := Fin.snoc half_16_11_φ4 (84078184041/2500000000000 : ℝ)

def half_16_11_φ6 : Fin 6 → ℝ := Fin.snoc half_16_11_φ5 (13016882097/625000000000 : ℝ)

theorem half_16_11_hF2 : SourcePowerBound (paddedMoment 18 0 2 64 half_16_11_φ6) (45799698280747/5000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 6) (r := 0) (D := 64)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_16_11_φ6 (by norm_num [half_16_11_φ1, half_16_11_φ2, half_16_11_φ3, half_16_11_φ4, half_16_11_φ5, half_16_11_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_11_φ1, half_16_11_φ2, half_16_11_φ3, half_16_11_φ4, half_16_11_φ5, half_16_11_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_11_φ1, half_16_11_φ2, half_16_11_φ3, half_16_11_φ4, half_16_11_φ5, half_16_11_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_16_11_φ1, half_16_11_φ2, half_16_11_φ3, half_16_11_φ4, half_16_11_φ5, half_16_11_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_16_11_hx6 : SourcePowerBound (powerBoxCross 18 10 64 half_16_11_φ6) (23191232442113/2000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 10) (r := 2) (v := 13) (w := 14) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_16_11_φ6 (by norm_num [half_16_11_φ1, half_16_11_φ2, half_16_11_φ3, half_16_11_φ4, half_16_11_φ5, half_16_11_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_11_φ1, half_16_11_φ2, half_16_11_φ3, half_16_11_φ4, half_16_11_φ5, half_16_11_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_16_11_hF2 half_13_11 half_14_11
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_16_11_φ1, half_16_11_φ2, half_16_11_φ3, half_16_11_φ4, half_16_11_φ5, half_16_11_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_11_hx5 : SourcePowerBound (powerBoxCross 18 11 32 half_16_11_φ5) (124809704322057/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 5) (s := 11) (u := 9) (t := 12)
    (D := 32) (ψ := (13016882097/625000000000 : ℝ)) half_16_11_φ5
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_11_φ1, half_16_11_φ2, half_16_11_φ3, half_16_11_φ4, half_16_11_φ5, half_16_11_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_11_φ1, half_16_11_φ2, half_16_11_φ3, half_16_11_φ4, half_16_11_φ5, half_16_11_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_11_φ1, half_16_11_φ2, half_16_11_φ3, half_16_11_φ4, half_16_11_φ5, half_16_11_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_11 half_12_11
    (by simpa only [half_16_11_φ6, show (2:ℝ)*32=64 by norm_num] using half_16_11_hx6)
  exact h.weaken (by norm_num [half_16_11_φ1, half_16_11_φ2, half_16_11_φ3, half_16_11_φ4, half_16_11_φ5, half_16_11_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_11_hx4 : SourcePowerBound (powerBoxCross 18 12 16 half_16_11_φ4) (136829958654357/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 12) (u := 10) (t := 13)
    (D := 16) (ψ := (84078184041/2500000000000 : ℝ)) half_16_11_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_11_φ1, half_16_11_φ2, half_16_11_φ3, half_16_11_φ4, half_16_11_φ5, half_16_11_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_11_φ1, half_16_11_φ2, half_16_11_φ3, half_16_11_φ4, half_16_11_φ5, half_16_11_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_11_φ1, half_16_11_φ2, half_16_11_φ3, half_16_11_φ4, half_16_11_φ5, half_16_11_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_11 half_13_11
    (by simpa only [half_16_11_φ5, show (2:ℝ)*16=32 by norm_num] using half_16_11_hx5)
  exact h.weaken (by norm_num [half_16_11_φ1, half_16_11_φ2, half_16_11_φ3, half_16_11_φ4, half_16_11_φ5, half_16_11_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_11_hx3 : SourcePowerBound (powerBoxCross 18 13 8 half_16_11_φ3) (15090452323947/1000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 13) (u := 11) (t := 14)
    (D := 8) (ψ := (187053342423/5000000000000 : ℝ)) half_16_11_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_11_φ1, half_16_11_φ2, half_16_11_φ3, half_16_11_φ4, half_16_11_φ5, half_16_11_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_11_φ1, half_16_11_φ2, half_16_11_φ3, half_16_11_φ4, half_16_11_φ5, half_16_11_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_11_φ1, half_16_11_φ2, half_16_11_φ3, half_16_11_φ4, half_16_11_φ5, half_16_11_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_11 half_14_11
    (by simpa only [half_16_11_φ4, show (2:ℝ)*8=16 by norm_num] using half_16_11_hx4)
  exact h.weaken (by norm_num [half_16_11_φ1, half_16_11_φ2, half_16_11_φ3, half_16_11_φ4, half_16_11_φ5, half_16_11_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_11_hx2 : SourcePowerBound (powerBoxCross 18 14 4 half_16_11_φ2) (166805430541167/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 14) (u := 12) (t := 15)
    (D := 4) (ψ := (195551050183/5000000000000 : ℝ)) half_16_11_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_11_φ1, half_16_11_φ2, half_16_11_φ3, half_16_11_φ4, half_16_11_φ5, half_16_11_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_11_φ1, half_16_11_φ2, half_16_11_φ3, half_16_11_φ4, half_16_11_φ5, half_16_11_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_11_φ1, half_16_11_φ2, half_16_11_φ3, half_16_11_φ4, half_16_11_φ5, half_16_11_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_13_11 half_15_11
    (by simpa only [half_16_11_φ3, show (2:ℝ)*4=8 by norm_num] using half_16_11_hx3)
  exact h.weaken (by norm_num [half_16_11_φ1, half_16_11_φ2, half_16_11_φ3, half_16_11_φ4, half_16_11_φ5, half_16_11_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_11_hx1 : SourcePowerBound (powerBoxCross 18 15 2 half_16_11_φ1) (184522391108651/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 15) (u := 13) (t := 16)
    (D := 2) (ψ := (100676237397/2500000000000 : ℝ)) half_16_11_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_11_φ1, half_16_11_φ2, half_16_11_φ3, half_16_11_φ4, half_16_11_φ5, half_16_11_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_11_φ1, half_16_11_φ2, half_16_11_φ3, half_16_11_φ4, half_16_11_φ5, half_16_11_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_11_φ1, half_16_11_φ2, half_16_11_φ3, half_16_11_φ4, half_16_11_φ5, half_16_11_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_14_11 half_16_10
    (by simpa only [half_16_11_φ2, show (2:ℝ)*2=4 by norm_num] using half_16_11_hx2)
  exact h.weaken (by norm_num [half_16_11_φ1, half_16_11_φ2, half_16_11_φ3, half_16_11_φ4, half_16_11_φ5, half_16_11_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_11 : AdmissibleExponent 18 32 (196499548975661/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 14) (ψ := (41300544369/1000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_15_11
    (by simpa only [half_16_11_φ1] using half_16_11_hx1)
  exact admissibleExponent_mono h (by norm_num [half_16_11_φ1, half_16_11_φ2, half_16_11_φ3, half_16_11_φ4, half_16_11_φ5, half_16_11_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_17_11_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (422053097327/10000000000000 : ℝ)

def half_17_11_φ2 : Fin 2 → ℝ := Fin.snoc half_17_11_φ1 (412032780647/10000000000000 : ℝ)

def half_17_11_φ3 : Fin 3 → ℝ := Fin.snoc half_17_11_φ2 (200567817867/5000000000000 : ℝ)

def half_17_11_φ4 : Fin 4 → ℝ := Fin.snoc half_17_11_φ3 (96783406269/2500000000000 : ℝ)

def half_17_11_φ5 : Fin 5 → ℝ := Fin.snoc half_17_11_φ4 (361367801791/10000000000000 : ℝ)

def half_17_11_φ6 : Fin 6 → ℝ := Fin.snoc half_17_11_φ5 (289286635931/10000000000000 : ℝ)

theorem half_17_11_hF2 : SourcePowerBound (paddedMoment 18 0 2 64 half_17_11_φ6) (42038255799097/5000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 6) (r := 0) (D := 64)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_17_11_φ6 (by norm_num [half_17_11_φ1, half_17_11_φ2, half_17_11_φ3, half_17_11_φ4, half_17_11_φ5, half_17_11_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_11_φ1, half_17_11_φ2, half_17_11_φ3, half_17_11_φ4, half_17_11_φ5, half_17_11_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_11_φ1, half_17_11_φ2, half_17_11_φ3, half_17_11_φ4, half_17_11_φ5, half_17_11_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_17_11_φ1, half_17_11_φ2, half_17_11_φ3, half_17_11_φ4, half_17_11_φ5, half_17_11_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_17_11_hx6 : SourcePowerBound (powerBoxCross 18 11 64 half_17_11_φ6) (15431744234967/1250000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 11) (r := 2) (v := 14) (w := 15) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_17_11_φ6 (by norm_num [half_17_11_φ1, half_17_11_φ2, half_17_11_φ3, half_17_11_φ4, half_17_11_φ5, half_17_11_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_11_φ1, half_17_11_φ2, half_17_11_φ3, half_17_11_φ4, half_17_11_φ5, half_17_11_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_17_11_hF2 half_14_11 half_15_11
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_17_11_φ1, half_17_11_φ2, half_17_11_φ3, half_17_11_φ4, half_17_11_φ5, half_17_11_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_11_hx5 : SourcePowerBound (powerBoxCross 18 12 32 half_17_11_φ5) (67078292499253/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 5) (s := 12) (u := 10) (t := 13)
    (D := 32) (ψ := (289286635931/10000000000000 : ℝ)) half_17_11_φ5
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_11_φ1, half_17_11_φ2, half_17_11_φ3, half_17_11_φ4, half_17_11_φ5, half_17_11_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_11_φ1, half_17_11_φ2, half_17_11_φ3, half_17_11_φ4, half_17_11_φ5, half_17_11_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_11_φ1, half_17_11_φ2, half_17_11_φ3, half_17_11_φ4, half_17_11_φ5, half_17_11_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_11 half_13_11
    (by simpa only [half_17_11_φ6, show (2:ℝ)*32=64 by norm_num] using half_17_11_hx6)
  exact h.weaken (by norm_num [half_17_11_φ1, half_17_11_φ2, half_17_11_φ3, half_17_11_φ4, half_17_11_φ5, half_17_11_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_11_hx4 : SourcePowerBound (powerBoxCross 18 13 16 half_17_11_φ4) (147418400941601/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 13) (u := 11) (t := 14)
    (D := 16) (ψ := (361367801791/10000000000000 : ℝ)) half_17_11_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_11_φ1, half_17_11_φ2, half_17_11_φ3, half_17_11_φ4, half_17_11_φ5, half_17_11_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_11_φ1, half_17_11_φ2, half_17_11_φ3, half_17_11_φ4, half_17_11_φ5, half_17_11_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_11_φ1, half_17_11_φ2, half_17_11_φ3, half_17_11_φ4, half_17_11_φ5, half_17_11_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_11 half_14_11
    (by simpa only [half_17_11_φ5, show (2:ℝ)*16=32 by norm_num] using half_17_11_hx5)
  exact h.weaken (by norm_num [half_17_11_φ1, half_17_11_φ2, half_17_11_φ3, half_17_11_φ4, half_17_11_φ5, half_17_11_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_11_hx3 : SourcePowerBound (powerBoxCross 18 14 8 half_17_11_φ3) (162637548690061/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 14) (u := 12) (t := 15)
    (D := 8) (ψ := (96783406269/2500000000000 : ℝ)) half_17_11_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_11_φ1, half_17_11_φ2, half_17_11_φ3, half_17_11_φ4, half_17_11_φ5, half_17_11_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_11_φ1, half_17_11_φ2, half_17_11_φ3, half_17_11_φ4, half_17_11_φ5, half_17_11_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_11_φ1, half_17_11_φ2, half_17_11_φ3, half_17_11_φ4, half_17_11_φ5, half_17_11_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_13_11 half_15_11
    (by simpa only [half_17_11_φ4, show (2:ℝ)*8=16 by norm_num] using half_17_11_hx4)
  exact h.weaken (by norm_num [half_17_11_φ1, half_17_11_φ2, half_17_11_φ3, half_17_11_φ4, half_17_11_φ5, half_17_11_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_11_hx2 : SourcePowerBound (powerBoxCross 18 15 4 half_17_11_φ2) (179699275011049/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 15) (u := 13) (t := 16)
    (D := 4) (ψ := (200567817867/5000000000000 : ℝ)) half_17_11_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_11_φ1, half_17_11_φ2, half_17_11_φ3, half_17_11_φ4, half_17_11_φ5, half_17_11_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_11_φ1, half_17_11_φ2, half_17_11_φ3, half_17_11_φ4, half_17_11_φ5, half_17_11_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_11_φ1, half_17_11_φ2, half_17_11_φ3, half_17_11_φ4, half_17_11_φ5, half_17_11_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_14_11 half_16_11
    (by simpa only [half_17_11_φ3, show (2:ℝ)*4=8 by norm_num] using half_17_11_hx3)
  exact h.weaken (by norm_num [half_17_11_φ1, half_17_11_φ2, half_17_11_φ3, half_17_11_φ4, half_17_11_φ5, half_17_11_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_11_hx1 : SourcePowerBound (powerBoxCross 18 16 2 half_17_11_φ1) (39725655549229/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 16) (u := 14) (t := 17)
    (D := 2) (ψ := (412032780647/10000000000000 : ℝ)) half_17_11_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_11_φ1, half_17_11_φ2, half_17_11_φ3, half_17_11_φ4, half_17_11_φ5, half_17_11_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_11_φ1, half_17_11_φ2, half_17_11_φ3, half_17_11_φ4, half_17_11_φ5, half_17_11_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_11_φ1, half_17_11_φ2, half_17_11_φ3, half_17_11_φ4, half_17_11_φ5, half_17_11_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_15_11 half_17_10
    (by simpa only [half_17_11_φ2, show (2:ℝ)*2=4 by norm_num] using half_17_11_hx2)
  exact h.weaken (by norm_num [half_17_11_φ1, half_17_11_φ2, half_17_11_φ3, half_17_11_φ4, half_17_11_φ5, half_17_11_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_11 : AdmissibleExponent 18 34 (105855961881641/5000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 15) (ψ := (422053097327/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_16_11
    (by simpa only [half_17_11_φ1] using half_17_11_hx1)
  exact admissibleExponent_mono h (by norm_num [half_17_11_φ1, half_17_11_φ2, half_17_11_φ3, half_17_11_φ4, half_17_11_φ5, half_17_11_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])


end Waring.SeedCompletionHigher18SimpleSeeds
