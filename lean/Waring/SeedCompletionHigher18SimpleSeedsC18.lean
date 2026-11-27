import Waring.SeedCompletionHigher18SimpleSeedsC17

noncomputable section
set_option maxHeartbeats 2000000
namespace Waring.SeedCompletionHigher18SimpleSeeds
open SmoothMoments FirstStageTransport SeedCompletionNaturalBox
open SeedCompletionSourceBounds SeedCompletionPaddedSource SeedCompletionGeneralTerminal
open PolicyCompletionMajorPowerRanges

def half_9_18_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (343838830331/10000000000000 : ℝ)

def half_9_18_φ2 : Fin 2 → ℝ := Fin.snoc half_9_18_φ1 (15417257163/500000000000 : ℝ)

def half_9_18_φ3 : Fin 3 → ℝ := Fin.snoc half_9_18_φ2 (33611476993/2500000000000 : ℝ)

theorem half_9_18_hF2 : SourcePowerBound (paddedMoment 18 0 2 8 half_9_18_φ3) (69881876040287/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_18_φ3 (by norm_num [half_9_18_φ1, half_9_18_φ2, half_9_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_18_φ1, half_9_18_φ2, half_9_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_18_φ1, half_9_18_φ2, half_9_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_18_φ1, half_9_18_φ2, half_9_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_9_18_hF1 : SourcePowerBound (paddedMoment 18 0 1 8 half_9_18_φ3) (26627292013429/10000000000000 : ℝ) := by
  have h := padded_second_power (k := 18) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_18_φ3 (by norm_num [half_9_18_φ1, half_9_18_φ2, half_9_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_18_φ1, half_9_18_φ2, half_9_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_18_φ1, half_9_18_φ2, half_9_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_18_φ1, half_9_18_φ2, half_9_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_9_18_hx3 : SourcePowerBound (powerBoxCross 18 6 8 half_9_18_φ3) (38496518554111/5000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 18) (s := 6) (r := 1) (v := 2) (t := 10) (D := 8)
    (a := (3/10 : ℝ)) (b := (1/10 : ℝ)) (c := (3/5 : ℝ))
    (by norm_num) half_9_18_φ3 (by norm_num [half_9_18_φ1, half_9_18_φ2, half_9_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_18_φ1, half_9_18_φ2, half_9_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_9_18_hF1 half_9_18_hF2 half_10_17
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_9_18_φ1, half_9_18_φ2, half_9_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_9_18_hx2 : SourcePowerBound (powerBoxCross 18 7 4 half_9_18_φ2) (8426942179711/1000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 7) (u := 5) (t := 8)
    (D := 4) (ψ := (33611476993/2500000000000 : ℝ)) half_9_18_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_18_φ1, half_9_18_φ2, half_9_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_18_φ1, half_9_18_φ2, half_9_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_18_φ1, half_9_18_φ2, half_9_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_6 SeedCompletionEven18SecondSeeds.degree18_half_8
    (by simpa only [half_9_18_φ3, show (2:ℝ)*4=8 by norm_num] using half_9_18_hx3)
  exact h.weaken (by norm_num [half_9_18_φ1, half_9_18_φ2, half_9_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_9_18_hx1 : SourcePowerBound (powerBoxCross 18 8 2 half_9_18_φ1) (23543699511583/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 8) (u := 6) (t := 9)
    (D := 2) (ψ := (15417257163/500000000000 : ℝ)) half_9_18_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_18_φ1, half_9_18_φ2, half_9_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_18_φ1, half_9_18_φ2, half_9_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_18_φ1, half_9_18_φ2, half_9_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_7 half_9_17
    (by simpa only [half_9_18_φ2, show (2:ℝ)*2=4 by norm_num] using half_9_18_hx2)
  exact h.weaken (by norm_num [half_9_18_φ1, half_9_18_φ2, half_9_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_9_18 : AdmissibleExponent 18 18 (99332380501297/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 7) (ψ := (343838830331/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_8
    (by simpa only [half_9_18_φ1] using half_9_18_hx1)
  exact admissibleExponent_mono h (by norm_num [half_9_18_φ1, half_9_18_φ2, half_9_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_10_18_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (353748845767/10000000000000 : ℝ)

def half_10_18_φ2 : Fin 2 → ℝ := Fin.snoc half_10_18_φ1 (41157070819/1250000000000 : ℝ)

def half_10_18_φ3 : Fin 3 → ℝ := Fin.snoc half_10_18_φ2 (114969390431/5000000000000 : ℝ)

theorem half_10_18_hF2 : SourcePowerBound (paddedMoment 18 0 2 8 half_10_18_φ3) (63439846147769/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_10_18_φ3 (by norm_num [half_10_18_φ1, half_10_18_φ2, half_10_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_18_φ1, half_10_18_φ2, half_10_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_18_φ1, half_10_18_φ2, half_10_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_10_18_φ1, half_10_18_φ2, half_10_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_10_18_hx3 : SourcePowerBound (powerBoxCross 18 7 8 half_10_18_φ3) (43238957091869/5000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 7) (r := 2) (v := 9) (w := 10) (D := 8)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_10_18_φ3 (by norm_num [half_10_18_φ1, half_10_18_φ2, half_10_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_18_φ1, half_10_18_φ2, half_10_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_10_18_hF2 half_9_18 half_10_17
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_10_18_φ1, half_10_18_φ2, half_10_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_18_hx2 : SourcePowerBound (powerBoxCross 18 8 4 half_10_18_φ2) (23800493934591/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 8) (u := 6) (t := 9)
    (D := 4) (ψ := (114969390431/5000000000000 : ℝ)) half_10_18_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_18_φ1, half_10_18_φ2, half_10_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_18_φ1, half_10_18_φ2, half_10_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_18_φ1, half_10_18_φ2, half_10_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_7 half_9_18
    (by simpa only [half_10_18_φ3, show (2:ℝ)*4=8 by norm_num] using half_10_18_hx3)
  exact h.weaken (by norm_num [half_10_18_φ1, half_10_18_φ2, half_10_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_18_hx1 : SourcePowerBound (powerBoxCross 18 9 2 half_10_18_φ1) (53086128926061/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 9) (u := 7) (t := 10)
    (D := 2) (ψ := (41157070819/1250000000000 : ℝ)) half_10_18_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_18_φ1, half_10_18_φ2, half_10_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_18_φ1, half_10_18_φ2, half_10_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_18_φ1, half_10_18_φ2, half_10_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_8 half_10_17
    (by simpa only [half_10_18_φ2, show (2:ℝ)*2=4 by norm_num] using half_10_18_hx2)
  exact h.weaken (by norm_num [half_10_18_φ1, half_10_18_φ2, half_10_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_18 : AdmissibleExponent 18 20 (112185988230161/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 8) (ψ := (353748845767/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_9_18
    (by simpa only [half_10_18_φ1] using half_10_18_hx1)
  exact admissibleExponent_mono h (by norm_num [half_10_18_φ1, half_10_18_φ2, half_10_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_11_18_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (364748133641/10000000000000 : ℝ)

def half_11_18_φ2 : Fin 2 → ℝ := Fin.snoc half_11_18_φ1 (346394857263/10000000000000 : ℝ)

def half_11_18_φ3 : Fin 3 → ℝ := Fin.snoc half_11_18_φ2 (18420530709/625000000000 : ℝ)

theorem half_11_18_hF2 : SourcePowerBound (paddedMoment 18 0 2 8 half_11_18_φ3) (7337569300669/1250000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_11_18_φ3 (by norm_num [half_11_18_φ1, half_11_18_φ2, half_11_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_18_φ1, half_11_18_φ2, half_11_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_18_φ1, half_11_18_φ2, half_11_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_11_18_φ1, half_11_18_φ2, half_11_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_11_18_hx3 : SourcePowerBound (powerBoxCross 18 8 8 half_11_18_φ3) (96288752106487/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 8) (r := 2) (v := 10) (w := 11) (D := 8)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_11_18_φ3 (by norm_num [half_11_18_φ1, half_11_18_φ2, half_11_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_18_φ1, half_11_18_φ2, half_11_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_11_18_hF2 half_10_18 half_11_17
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_11_18_φ1, half_11_18_φ2, half_11_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_18_hx2 : SourcePowerBound (powerBoxCross 18 9 4 half_11_18_φ2) (21282820894069/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 9) (u := 7) (t := 10)
    (D := 4) (ψ := (18420530709/625000000000 : ℝ)) half_11_18_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_18_φ1, half_11_18_φ2, half_11_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_18_φ1, half_11_18_φ2, half_11_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_18_φ1, half_11_18_φ2, half_11_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_8 half_10_18
    (by simpa only [half_11_18_φ3, show (2:ℝ)*4=8 by norm_num] using half_11_18_hx3)
  exact h.weaken (by norm_num [half_11_18_φ1, half_11_18_φ2, half_11_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_18_hx1 : SourcePowerBound (powerBoxCross 18 10 2 half_11_18_φ1) (2369175467621/200000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 10) (u := 8) (t := 11)
    (D := 2) (ψ := (346394857263/10000000000000 : ℝ)) half_11_18_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_18_φ1, half_11_18_φ2, half_11_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_18_φ1, half_11_18_φ2, half_11_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_18_φ1, half_11_18_φ2, half_11_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_18 half_11_17
    (by simpa only [half_11_18_φ2, show (2:ℝ)*2=4 by norm_num] using half_11_18_hx2)
  exact h.weaken (by norm_num [half_11_18_φ1, half_11_18_φ2, half_11_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_18 : AdmissibleExponent 18 22 (125388987920229/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 9) (ψ := (364748133641/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_10_18
    (by simpa only [half_11_18_φ1] using half_11_18_hx1)
  exact admissibleExponent_mono h (by norm_num [half_11_18_φ1, half_11_18_φ2, half_11_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_12_18_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (187470977281/5000000000000 : ℝ)

def half_12_18_φ2 : Fin 2 → ℝ := Fin.snoc half_12_18_φ1 (180293432313/5000000000000 : ℝ)

def half_12_18_φ3 : Fin 3 → ℝ := Fin.snoc half_12_18_φ2 (6588601393/200000000000 : ℝ)

def half_12_18_φ4 : Fin 4 → ℝ := Fin.snoc half_12_18_φ3 (5322683677/250000000000 : ℝ)

theorem half_12_18_hF2 : SourcePowerBound (paddedMoment 18 0 2 16 half_12_18_φ4) (37414410984091/5000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_12_18_φ4 (by norm_num [half_12_18_φ1, half_12_18_φ2, half_12_18_φ3, half_12_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_18_φ1, half_12_18_φ2, half_12_18_φ3, half_12_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_18_φ1, half_12_18_φ2, half_12_18_φ3, half_12_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_12_18_φ1, half_12_18_φ2, half_12_18_φ3, half_12_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_12_18_hF1 : SourcePowerBound (paddedMoment 18 0 1 16 half_12_18_φ4) (14138136994697/5000000000000 : ℝ) := by
  have h := padded_second_power (k := 18) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_12_18_φ4 (by norm_num [half_12_18_φ1, half_12_18_φ2, half_12_18_φ3, half_12_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_18_φ1, half_12_18_φ2, half_12_18_φ3, half_12_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_18_φ1, half_12_18_φ2, half_12_18_φ3, half_12_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_12_18_φ1, half_12_18_φ2, half_12_18_φ3, half_12_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_12_18_hx4 : SourcePowerBound (powerBoxCross 18 8 16 half_12_18_φ4) (48915355093711/5000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 18) (s := 8) (r := 1) (v := 2) (t := 11) (D := 16)
    (a := (1/22 : ℝ)) (b := (5/22 : ℝ)) (c := (8/11 : ℝ))
    (by norm_num) half_12_18_φ4 (by norm_num [half_12_18_φ1, half_12_18_φ2, half_12_18_φ3, half_12_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_18_φ1, half_12_18_φ2, half_12_18_φ3, half_12_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_12_18_hF1 half_12_18_hF2 half_11_18
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_12_18_φ1, half_12_18_φ2, half_12_18_φ3, half_12_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_18_hx3 : SourcePowerBound (powerBoxCross 18 9 8 half_12_18_φ3) (10657933048833/1000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 9) (u := 7) (t := 10)
    (D := 8) (ψ := (5322683677/250000000000 : ℝ)) half_12_18_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_18_φ1, half_12_18_φ2, half_12_18_φ3, half_12_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_18_φ1, half_12_18_φ2, half_12_18_φ3, half_12_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_18_φ1, half_12_18_φ2, half_12_18_φ3, half_12_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_8 half_10_18
    (by simpa only [half_12_18_φ4, show (2:ℝ)*8=16 by norm_num] using half_12_18_hx4)
  exact h.weaken (by norm_num [half_12_18_φ1, half_12_18_φ2, half_12_18_φ3, half_12_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_18_hx2 : SourcePowerBound (powerBoxCross 18 10 4 half_12_18_φ2) (58960479561/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 10) (u := 8) (t := 11)
    (D := 4) (ψ := (6588601393/200000000000 : ℝ)) half_12_18_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_18_φ1, half_12_18_φ2, half_12_18_φ3, half_12_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_18_φ1, half_12_18_φ2, half_12_18_φ3, half_12_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_18_φ1, half_12_18_φ2, half_12_18_φ3, half_12_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_18 half_11_18
    (by simpa only [half_12_18_φ3, show (2:ℝ)*4=8 by norm_num] using half_12_18_hx3)
  exact h.weaken (by norm_num [half_12_18_φ1, half_12_18_φ2, half_12_18_φ3, half_12_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_18_hx1 : SourcePowerBound (powerBoxCross 18 11 2 half_12_18_φ1) (26212514130733/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 11) (u := 9) (t := 12)
    (D := 2) (ψ := (180293432313/5000000000000 : ℝ)) half_12_18_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_18_φ1, half_12_18_φ2, half_12_18_φ3, half_12_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_18_φ1, half_12_18_φ2, half_12_18_φ3, half_12_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_18_φ1, half_12_18_φ2, half_12_18_φ3, half_12_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_18 half_12_17
    (by simpa only [half_12_18_φ2, show (2:ℝ)*2=4 by norm_num] using half_12_18_hx2)
  exact h.weaken (by norm_num [half_12_18_φ1, half_12_18_φ2, half_12_18_φ3, half_12_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_18 : AdmissibleExponent 18 24 (138936351699467/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 10) (ψ := (187470977281/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_11_18
    (by simpa only [half_12_18_φ1] using half_12_18_hx1)
  exact admissibleExponent_mono h (by norm_num [half_12_18_φ1, half_12_18_φ2, half_12_18_φ3, half_12_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_13_18_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (48075551289/1250000000000 : ℝ)

def half_13_18_φ2 : Fin 2 → ℝ := Fin.snoc half_13_18_φ1 (37196840567/1000000000000 : ℝ)

def half_13_18_φ3 : Fin 3 → ℝ := Fin.snoc half_13_18_φ2 (174946577653/5000000000000 : ℝ)

def half_13_18_φ4 : Fin 4 → ℝ := Fin.snoc half_13_18_φ3 (28331326443/1000000000000 : ℝ)

theorem half_13_18_hF2 : SourcePowerBound (paddedMoment 18 0 2 16 half_13_18_φ4) (34560629489191/5000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_13_18_φ4 (by norm_num [half_13_18_φ1, half_13_18_φ2, half_13_18_φ3, half_13_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_18_φ1, half_13_18_φ2, half_13_18_φ3, half_13_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_18_φ1, half_13_18_φ2, half_13_18_φ3, half_13_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_13_18_φ1, half_13_18_φ2, half_13_18_φ3, half_13_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_13_18_hx4 : SourcePowerBound (powerBoxCross 18 9 16 half_13_18_φ4) (107000764268321/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 9) (r := 2) (v := 12) (w := 12) (D := 16)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_13_18_φ4 (by norm_num [half_13_18_φ1, half_13_18_φ2, half_13_18_φ3, half_13_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_18_φ1, half_13_18_φ2, half_13_18_φ3, half_13_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_13_18_hF2 half_12_18 half_12_18
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_13_18_φ1, half_13_18_φ2, half_13_18_φ3, half_13_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_18_hx3 : SourcePowerBound (powerBoxCross 18 10 8 half_13_18_φ3) (14657643208823/1250000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 10) (u := 8) (t := 11)
    (D := 8) (ψ := (28331326443/1000000000000 : ℝ)) half_13_18_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_18_φ1, half_13_18_φ2, half_13_18_φ3, half_13_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_18_φ1, half_13_18_φ2, half_13_18_φ3, half_13_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_18_φ1, half_13_18_φ2, half_13_18_φ3, half_13_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_18 half_11_18
    (by simpa only [half_13_18_φ4, show (2:ℝ)*8=16 by norm_num] using half_13_18_hx4)
  exact h.weaken (by norm_num [half_13_18_φ1, half_13_18_φ2, half_13_18_φ3, half_13_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_18_hx2 : SourcePowerBound (powerBoxCross 18 11 4 half_13_18_φ2) (129736091382209/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 11) (u := 9) (t := 12)
    (D := 4) (ψ := (174946577653/5000000000000 : ℝ)) half_13_18_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_18_φ1, half_13_18_φ2, half_13_18_φ3, half_13_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_18_φ1, half_13_18_φ2, half_13_18_φ3, half_13_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_18_φ1, half_13_18_φ2, half_13_18_φ3, half_13_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_18 half_12_18
    (by simpa only [half_13_18_φ3, show (2:ℝ)*4=8 by norm_num] using half_13_18_hx3)
  exact h.weaken (by norm_num [half_13_18_φ1, half_13_18_φ2, half_13_18_φ3, half_13_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_18_hx1 : SourcePowerBound (powerBoxCross 18 12 2 half_13_18_φ1) (143977402748171/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 12) (u := 10) (t := 13)
    (D := 2) (ψ := (37196840567/1000000000000 : ℝ)) half_13_18_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_18_φ1, half_13_18_φ2, half_13_18_φ3, half_13_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_18_φ1, half_13_18_φ2, half_13_18_φ3, half_13_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_18_φ1, half_13_18_φ2, half_13_18_φ3, half_13_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_18 half_13_17
    (by simpa only [half_13_18_φ2, show (2:ℝ)*2=4 by norm_num] using half_13_18_hx2)
  exact h.weaken (by norm_num [half_13_18_φ1, half_13_18_φ2, half_13_18_φ3, half_13_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_18 : AdmissibleExponent 18 26 (152823304185347/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 11) (ψ := (48075551289/1250000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_12_18
    (by simpa only [half_13_18_φ1] using half_13_18_hx1)
  exact admissibleExponent_mono h (by norm_num [half_13_18_φ1, half_13_18_φ2, half_13_18_φ3, half_13_18_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_14_18_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (394360680189/10000000000000 : ℝ)

def half_14_18_φ2 : Fin 2 → ℝ := Fin.snoc half_14_18_φ1 (76599345653/2000000000000 : ℝ)

def half_14_18_φ3 : Fin 3 → ℝ := Fin.snoc half_14_18_φ2 (183630404867/5000000000000 : ℝ)

def half_14_18_φ4 : Fin 4 → ℝ := Fin.snoc half_14_18_φ3 (16605787297/500000000000 : ℝ)

def half_14_18_φ5 : Fin 5 → ℝ := Fin.snoc half_14_18_φ4 (82232291/4000000000 : ℝ)

theorem half_14_18_hF2 : SourcePowerBound (paddedMoment 18 0 2 32 half_14_18_φ5) (21050487681743/2500000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_14_18_φ5 (by norm_num [half_14_18_φ1, half_14_18_φ2, half_14_18_φ3, half_14_18_φ4, half_14_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_18_φ1, half_14_18_φ2, half_14_18_φ3, half_14_18_φ4, half_14_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_18_φ1, half_14_18_φ2, half_14_18_φ3, half_14_18_φ4, half_14_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_14_18_φ1, half_14_18_φ2, half_14_18_φ3, half_14_18_φ4, half_14_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_14_18_hx5 : SourcePowerBound (powerBoxCross 18 9 32 half_14_18_φ5) (107722651531453/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 9) (r := 2) (v := 12) (w := 12) (D := 32)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_14_18_φ5 (by norm_num [half_14_18_φ1, half_14_18_φ2, half_14_18_φ3, half_14_18_φ4, half_14_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_18_φ1, half_14_18_φ2, half_14_18_φ3, half_14_18_φ4, half_14_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_14_18_hF2 half_12_18 half_12_18
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_14_18_φ1, half_14_18_φ2, half_14_18_φ3, half_14_18_φ4, half_14_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_18_hx4 : SourcePowerBound (powerBoxCross 18 10 16 half_14_18_φ4) (14561588544379/1250000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 10) (u := 8) (t := 11)
    (D := 16) (ψ := (82232291/4000000000 : ℝ)) half_14_18_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_18_φ1, half_14_18_φ2, half_14_18_φ3, half_14_18_φ4, half_14_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_18_φ1, half_14_18_φ2, half_14_18_φ3, half_14_18_φ4, half_14_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_18_φ1, half_14_18_φ2, half_14_18_φ3, half_14_18_φ4, half_14_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_18 half_11_18
    (by simpa only [half_14_18_φ5, show (2:ℝ)*16=32 by norm_num] using half_14_18_hx5)
  exact h.weaken (by norm_num [half_14_18_φ1, half_14_18_φ2, half_14_18_φ3, half_14_18_φ4, half_14_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_18_hx3 : SourcePowerBound (powerBoxCross 18 11 8 half_14_18_φ3) (128188920792893/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 11) (u := 9) (t := 12)
    (D := 8) (ψ := (16605787297/500000000000 : ℝ)) half_14_18_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_18_φ1, half_14_18_φ2, half_14_18_φ3, half_14_18_φ4, half_14_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_18_φ1, half_14_18_φ2, half_14_18_φ3, half_14_18_φ4, half_14_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_18_φ1, half_14_18_φ2, half_14_18_φ3, half_14_18_φ4, half_14_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_18 half_12_18
    (by simpa only [half_14_18_φ4, show (2:ℝ)*8=16 by norm_num] using half_14_18_hx4)
  exact h.weaken (by norm_num [half_14_18_φ1, half_14_18_φ2, half_14_18_φ3, half_14_18_φ4, half_14_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_18_hx2 : SourcePowerBound (powerBoxCross 18 12 4 half_14_18_φ2) (17726862079353/1250000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 12) (u := 10) (t := 13)
    (D := 4) (ψ := (183630404867/5000000000000 : ℝ)) half_14_18_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_18_φ1, half_14_18_φ2, half_14_18_φ3, half_14_18_φ4, half_14_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_18_φ1, half_14_18_φ2, half_14_18_φ3, half_14_18_φ4, half_14_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_18_φ1, half_14_18_φ2, half_14_18_φ3, half_14_18_φ4, half_14_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_18 half_13_18
    (by simpa only [half_14_18_φ3, show (2:ℝ)*4=8 by norm_num] using half_14_18_hx3)
  exact h.weaken (by norm_num [half_14_18_φ1, half_14_18_φ2, half_14_18_φ3, half_14_18_φ4, half_14_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_18_hx1 : SourcePowerBound (powerBoxCross 18 13 2 half_14_18_φ1) (157190914646817/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 13) (u := 11) (t := 14)
    (D := 2) (ψ := (76599345653/2000000000000 : ℝ)) half_14_18_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_18_φ1, half_14_18_φ2, half_14_18_φ3, half_14_18_φ4, half_14_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_18_φ1, half_14_18_φ2, half_14_18_φ3, half_14_18_φ4, half_14_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_18_φ1, half_14_18_φ2, half_14_18_φ3, half_14_18_φ4, half_14_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_18 half_14_17
    (by simpa only [half_14_18_φ2, show (2:ℝ)*2=4 by norm_num] using half_14_18_hx2)
  exact h.weaken (by norm_num [half_14_18_φ1, half_14_18_φ2, half_14_18_φ3, half_14_18_φ4, half_14_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_18 : AdmissibleExponent 18 28 (83524965825771/5000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 12) (ψ := (394360680189/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_13_18
    (by simpa only [half_14_18_φ1] using half_14_18_hx1)
  exact admissibleExponent_mono h (by norm_num [half_14_18_φ1, half_14_18_φ2, half_14_18_φ3, half_14_18_φ4, half_14_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_15_18_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (403637631117/10000000000000 : ℝ)

def half_15_18_φ2 : Fin 2 → ℝ := Fin.snoc half_15_18_φ1 (392987547539/10000000000000 : ℝ)

def half_15_18_φ3 : Fin 3 → ℝ := Fin.snoc half_15_18_φ2 (94864379027/2500000000000 : ℝ)

def half_15_18_φ4 : Fin 4 → ℝ := Fin.snoc half_15_18_φ3 (177612533653/5000000000000 : ℝ)

def half_15_18_φ5 : Fin 5 → ℝ := Fin.snoc half_15_18_φ4 (284290744017/10000000000000 : ℝ)

theorem half_15_18_hF2 : SourcePowerBound (paddedMoment 18 0 2 32 half_15_18_φ5) (77404476189563/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_15_18_φ5 (by norm_num [half_15_18_φ1, half_15_18_φ2, half_15_18_φ3, half_15_18_φ4, half_15_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_18_φ1, half_15_18_φ2, half_15_18_φ3, half_15_18_φ4, half_15_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_18_φ1, half_15_18_φ2, half_15_18_φ3, half_15_18_φ4, half_15_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_15_18_φ1, half_15_18_φ2, half_15_18_φ3, half_15_18_φ4, half_15_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_15_18_hx5 : SourcePowerBound (powerBoxCross 18 10 32 half_15_18_φ5) (116069575755529/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 10) (r := 2) (v := 13) (w := 14) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_15_18_φ5 (by norm_num [half_15_18_φ1, half_15_18_φ2, half_15_18_φ3, half_15_18_φ4, half_15_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_18_φ1, half_15_18_φ2, half_15_18_φ3, half_15_18_φ4, half_15_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_15_18_hF2 half_13_18 half_14_18
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_15_18_φ1, half_15_18_φ2, half_15_18_φ3, half_15_18_φ4, half_15_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_18_hx4 : SourcePowerBound (powerBoxCross 18 11 16 half_15_18_φ4) (988671047879/78125000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 11) (u := 9) (t := 12)
    (D := 16) (ψ := (284290744017/10000000000000 : ℝ)) half_15_18_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_18_φ1, half_15_18_φ2, half_15_18_φ3, half_15_18_φ4, half_15_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_18_φ1, half_15_18_φ2, half_15_18_φ3, half_15_18_φ4, half_15_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_18_φ1, half_15_18_φ2, half_15_18_φ3, half_15_18_φ4, half_15_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_18 half_12_18
    (by simpa only [half_15_18_φ5, show (2:ℝ)*16=32 by norm_num] using half_15_18_hx5)
  exact h.weaken (by norm_num [half_15_18_φ1, half_15_18_φ2, half_15_18_φ3, half_15_18_φ4, half_15_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_18_hx3 : SourcePowerBound (powerBoxCross 18 12 8 half_15_18_φ3) (139433117287697/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 12) (u := 10) (t := 13)
    (D := 8) (ψ := (177612533653/5000000000000 : ℝ)) half_15_18_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_18_φ1, half_15_18_φ2, half_15_18_φ3, half_15_18_φ4, half_15_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_18_φ1, half_15_18_φ2, half_15_18_φ3, half_15_18_φ4, half_15_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_18_φ1, half_15_18_φ2, half_15_18_φ3, half_15_18_φ4, half_15_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_18 half_13_18
    (by simpa only [half_15_18_φ4, show (2:ℝ)*8=16 by norm_num] using half_15_18_hx4)
  exact h.weaken (by norm_num [half_15_18_φ1, half_15_18_φ2, half_15_18_φ3, half_15_18_φ4, half_15_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_18_hx2 : SourcePowerBound (powerBoxCross 18 13 4 half_15_18_φ2) (154180162803967/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 13) (u := 11) (t := 14)
    (D := 4) (ψ := (94864379027/2500000000000 : ℝ)) half_15_18_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_18_φ1, half_15_18_φ2, half_15_18_φ3, half_15_18_φ4, half_15_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_18_φ1, half_15_18_φ2, half_15_18_φ3, half_15_18_φ4, half_15_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_18_φ1, half_15_18_φ2, half_15_18_φ3, half_15_18_φ4, half_15_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_18 half_14_18
    (by simpa only [half_15_18_φ3, show (2:ℝ)*4=8 by norm_num] using half_15_18_hx3)
  exact h.weaken (by norm_num [half_15_18_φ1, half_15_18_φ2, half_15_18_φ3, half_15_18_φ4, half_15_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_18_hx1 : SourcePowerBound (powerBoxCross 18 14 2 half_15_18_φ1) (170710805413671/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 14) (u := 12) (t := 15)
    (D := 2) (ψ := (392987547539/10000000000000 : ℝ)) half_15_18_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_18_φ1, half_15_18_φ2, half_15_18_φ3, half_15_18_φ4, half_15_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_18_φ1, half_15_18_φ2, half_15_18_φ3, half_15_18_φ4, half_15_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_18_φ1, half_15_18_φ2, half_15_18_φ3, half_15_18_φ4, half_15_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_13_18 half_15_17
    (by simpa only [half_15_18_φ2, show (2:ℝ)*2=4 by norm_num] using half_15_18_hx2)
  exact h.weaken (by norm_num [half_15_18_φ1, half_15_18_φ2, half_15_18_φ3, half_15_18_φ4, half_15_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_18 : AdmissibleExponent 18 30 (18160902145383/1000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 13) (ψ := (403637631117/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_14_18
    (by simpa only [half_15_18_φ1] using half_15_18_hx1)
  exact admissibleExponent_mono h (by norm_num [half_15_18_φ1, half_15_18_φ2, half_15_18_φ3, half_15_18_φ4, half_15_18_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_16_18_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (412888575681/10000000000000 : ℝ)

def half_16_18_φ2 : Fin 2 → ℝ := Fin.snoc half_16_18_φ1 (402694416231/10000000000000 : ℝ)

def half_16_18_φ3 : Fin 3 → ℝ := Fin.snoc half_16_18_φ2 (97774326757/2500000000000 : ℝ)

def half_16_18_φ4 : Fin 4 → ℝ := Fin.snoc half_16_18_φ3 (374102463839/10000000000000 : ℝ)

def half_16_18_φ5 : Fin 5 → ℝ := Fin.snoc half_16_18_φ4 (336301400757/10000000000000 : ℝ)

def half_16_18_φ6 : Fin 6 → ℝ := Fin.snoc half_16_18_φ5 (104112304827/5000000000000 : ℝ)

theorem half_16_18_hF2 : SourcePowerBound (paddedMoment 18 0 2 64 half_16_18_φ6) (9160925256731/1000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 6) (r := 0) (D := 64)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_16_18_φ6 (by norm_num [half_16_18_φ1, half_16_18_φ2, half_16_18_φ3, half_16_18_φ4, half_16_18_φ5, half_16_18_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_18_φ1, half_16_18_φ2, half_16_18_φ3, half_16_18_φ4, half_16_18_φ5, half_16_18_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_18_φ1, half_16_18_φ2, half_16_18_φ3, half_16_18_φ4, half_16_18_φ5, half_16_18_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_16_18_φ1, half_16_18_φ2, half_16_18_φ3, half_16_18_φ4, half_16_18_φ5, half_16_18_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_16_18_hx6 : SourcePowerBound (powerBoxCross 18 10 64 half_16_18_φ6) (57980397779121/5000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 10) (r := 2) (v := 13) (w := 14) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_16_18_φ6 (by norm_num [half_16_18_φ1, half_16_18_φ2, half_16_18_φ3, half_16_18_φ4, half_16_18_φ5, half_16_18_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_18_φ1, half_16_18_φ2, half_16_18_φ3, half_16_18_φ4, half_16_18_φ5, half_16_18_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_16_18_hF2 half_13_18 half_14_18
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_16_18_φ1, half_16_18_φ2, half_16_18_φ3, half_16_18_φ4, half_16_18_φ5, half_16_18_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_18_hx5 : SourcePowerBound (powerBoxCross 18 11 32 half_16_18_φ5) (124813858051389/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 5) (s := 11) (u := 9) (t := 12)
    (D := 32) (ψ := (104112304827/5000000000000 : ℝ)) half_16_18_φ5
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_18_φ1, half_16_18_φ2, half_16_18_φ3, half_16_18_φ4, half_16_18_φ5, half_16_18_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_18_φ1, half_16_18_φ2, half_16_18_φ3, half_16_18_φ4, half_16_18_φ5, half_16_18_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_18_φ1, half_16_18_φ2, half_16_18_φ3, half_16_18_φ4, half_16_18_φ5, half_16_18_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_18 half_12_18
    (by simpa only [half_16_18_φ6, show (2:ℝ)*32=64 by norm_num] using half_16_18_hx6)
  exact h.weaken (by norm_num [half_16_18_φ1, half_16_18_φ2, half_16_18_φ3, half_16_18_φ4, half_16_18_φ5, half_16_18_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_18_hx4 : SourcePowerBound (powerBoxCross 18 12 16 half_16_18_φ4) (136834070092339/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 12) (u := 10) (t := 13)
    (D := 16) (ψ := (336301400757/10000000000000 : ℝ)) half_16_18_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_18_φ1, half_16_18_φ2, half_16_18_φ3, half_16_18_φ4, half_16_18_φ5, half_16_18_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_18_φ1, half_16_18_φ2, half_16_18_φ3, half_16_18_φ4, half_16_18_φ5, half_16_18_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_18_φ1, half_16_18_φ2, half_16_18_φ3, half_16_18_φ4, half_16_18_φ5, half_16_18_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_18 half_13_18
    (by simpa only [half_16_18_φ5, show (2:ℝ)*16=32 by norm_num] using half_16_18_hx5)
  exact h.weaken (by norm_num [half_16_18_φ1, half_16_18_φ2, half_16_18_φ3, half_16_18_φ4, half_16_18_φ5, half_16_18_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_18_hx3 : SourcePowerBound (powerBoxCross 18 13 8 half_16_18_φ3) (7545430179597/500000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 13) (u := 11) (t := 14)
    (D := 8) (ψ := (374102463839/10000000000000 : ℝ)) half_16_18_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_18_φ1, half_16_18_φ2, half_16_18_φ3, half_16_18_φ4, half_16_18_φ5, half_16_18_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_18_φ1, half_16_18_φ2, half_16_18_φ3, half_16_18_φ4, half_16_18_φ5, half_16_18_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_18_φ1, half_16_18_φ2, half_16_18_φ3, half_16_18_φ4, half_16_18_φ5, half_16_18_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_18 half_14_18
    (by simpa only [half_16_18_φ4, show (2:ℝ)*8=16 by norm_num] using half_16_18_hx4)
  exact h.weaken (by norm_num [half_16_18_φ1, half_16_18_φ2, half_16_18_φ3, half_16_18_φ4, half_16_18_φ5, half_16_18_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_18_hx2 : SourcePowerBound (powerBoxCross 18 14 4 half_16_18_φ2) (166809211975707/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 14) (u := 12) (t := 15)
    (D := 4) (ψ := (97774326757/2500000000000 : ℝ)) half_16_18_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_18_φ1, half_16_18_φ2, half_16_18_φ3, half_16_18_φ4, half_16_18_φ5, half_16_18_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_18_φ1, half_16_18_φ2, half_16_18_φ3, half_16_18_φ4, half_16_18_φ5, half_16_18_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_18_φ1, half_16_18_φ2, half_16_18_φ3, half_16_18_φ4, half_16_18_φ5, half_16_18_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_13_18 half_15_18
    (by simpa only [half_16_18_φ3, show (2:ℝ)*4=8 by norm_num] using half_16_18_hx3)
  exact h.weaken (by norm_num [half_16_18_φ1, half_16_18_φ2, half_16_18_φ3, half_16_18_φ4, half_16_18_φ5, half_16_18_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_18_hx1 : SourcePowerBound (powerBoxCross 18 15 2 half_16_18_φ1) (184523481009627/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 15) (u := 13) (t := 16)
    (D := 2) (ψ := (402694416231/10000000000000 : ℝ)) half_16_18_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_18_φ1, half_16_18_φ2, half_16_18_φ3, half_16_18_φ4, half_16_18_φ5, half_16_18_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_18_φ1, half_16_18_φ2, half_16_18_φ3, half_16_18_φ4, half_16_18_φ5, half_16_18_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_18_φ1, half_16_18_φ2, half_16_18_φ3, half_16_18_φ4, half_16_18_φ5, half_16_18_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_14_18 half_16_17
    (by simpa only [half_16_18_φ2, show (2:ℝ)*2=4 by norm_num] using half_16_18_hx2)
  exact h.weaken (by norm_num [half_16_18_φ1, half_16_18_φ2, half_16_18_φ3, half_16_18_φ4, half_16_18_φ5, half_16_18_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_18 : AdmissibleExponent 18 32 (24562156213047/1250000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 14) (ψ := (412888575681/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_15_18
    (by simpa only [half_16_18_φ1] using half_16_18_hx1)
  exact admissibleExponent_mono h (by norm_num [half_16_18_φ1, half_16_18_φ2, half_16_18_φ3, half_16_18_φ4, half_16_18_φ5, half_16_18_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_17_18_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (84365130157/2000000000000 : ℝ)

def half_17_18_φ2 : Fin 2 → ℝ := Fin.snoc half_17_18_φ1 (412010809137/10000000000000 : ℝ)

def half_17_18_φ3 : Fin 3 → ℝ := Fin.snoc half_17_18_φ2 (200561872639/5000000000000 : ℝ)

def half_17_18_φ4 : Fin 4 → ℝ := Fin.snoc half_17_18_φ3 (193561213931/5000000000000 : ℝ)

def half_17_18_φ5 : Fin 5 → ℝ := Fin.snoc half_17_18_φ4 (3613396679/100000000000 : ℝ)

def half_17_18_φ6 : Fin 6 → ℝ := Fin.snoc half_17_18_φ5 (289183474419/10000000000000 : ℝ)

theorem half_17_18_hF2 : SourcePowerBound (paddedMoment 18 0 2 64 half_17_18_φ6) (84097105455569/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 6) (r := 0) (D := 64)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_17_18_φ6 (by norm_num [half_17_18_φ1, half_17_18_φ2, half_17_18_φ3, half_17_18_φ4, half_17_18_φ5, half_17_18_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_18_φ1, half_17_18_φ2, half_17_18_φ3, half_17_18_φ4, half_17_18_φ5, half_17_18_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_18_φ1, half_17_18_φ2, half_17_18_φ3, half_17_18_φ4, half_17_18_φ5, half_17_18_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_17_18_φ1, half_17_18_φ2, half_17_18_φ3, half_17_18_φ4, half_17_18_φ5, half_17_18_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_17_18_hx6 : SourcePowerBound (powerBoxCross 18 11 64 half_17_18_φ6) (123464018466623/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 11) (r := 2) (v := 14) (w := 15) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_17_18_φ6 (by norm_num [half_17_18_φ1, half_17_18_φ2, half_17_18_φ3, half_17_18_φ4, half_17_18_φ5, half_17_18_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_18_φ1, half_17_18_φ2, half_17_18_φ3, half_17_18_φ4, half_17_18_φ5, half_17_18_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_17_18_hF2 half_14_18 half_15_18
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_17_18_φ1, half_17_18_φ2, half_17_18_φ3, half_17_18_φ4, half_17_18_φ5, half_17_18_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_18_hx5 : SourcePowerBound (powerBoxCross 18 12 32 half_17_18_φ5) (134165340767813/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 5) (s := 12) (u := 10) (t := 13)
    (D := 32) (ψ := (289183474419/10000000000000 : ℝ)) half_17_18_φ5
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_18_φ1, half_17_18_φ2, half_17_18_φ3, half_17_18_φ4, half_17_18_φ5, half_17_18_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_18_φ1, half_17_18_φ2, half_17_18_φ3, half_17_18_φ4, half_17_18_φ5, half_17_18_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_18_φ1, half_17_18_φ2, half_17_18_φ3, half_17_18_φ4, half_17_18_φ5, half_17_18_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_18 half_13_18
    (by simpa only [half_17_18_φ6, show (2:ℝ)*32=64 by norm_num] using half_17_18_hx6)
  exact h.weaken (by norm_num [half_17_18_φ1, half_17_18_φ2, half_17_18_φ3, half_17_18_φ4, half_17_18_φ5, half_17_18_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_18_hx4 : SourcePowerBound (powerBoxCross 18 13 16 half_17_18_φ4) (147426900360193/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 13) (u := 11) (t := 14)
    (D := 16) (ψ := (3613396679/100000000000 : ℝ)) half_17_18_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_18_φ1, half_17_18_φ2, half_17_18_φ3, half_17_18_φ4, half_17_18_φ5, half_17_18_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_18_φ1, half_17_18_φ2, half_17_18_φ3, half_17_18_φ4, half_17_18_φ5, half_17_18_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_18_φ1, half_17_18_φ2, half_17_18_φ3, half_17_18_φ4, half_17_18_φ5, half_17_18_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_18 half_14_18
    (by simpa only [half_17_18_φ5, show (2:ℝ)*16=32 by norm_num] using half_17_18_hx5)
  exact h.weaken (by norm_num [half_17_18_φ1, half_17_18_φ2, half_17_18_φ3, half_17_18_φ4, half_17_18_φ5, half_17_18_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_18_hx3 : SourcePowerBound (powerBoxCross 18 14 8 half_17_18_φ3) (162645833791047/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 14) (u := 12) (t := 15)
    (D := 8) (ψ := (193561213931/5000000000000 : ℝ)) half_17_18_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_18_φ1, half_17_18_φ2, half_17_18_φ3, half_17_18_φ4, half_17_18_φ5, half_17_18_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_18_φ1, half_17_18_φ2, half_17_18_φ3, half_17_18_φ4, half_17_18_φ5, half_17_18_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_18_φ1, half_17_18_φ2, half_17_18_φ3, half_17_18_φ4, half_17_18_φ5, half_17_18_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_13_18 half_15_18
    (by simpa only [half_17_18_φ4, show (2:ℝ)*8=16 by norm_num] using half_17_18_hx4)
  exact h.weaken (by norm_num [half_17_18_φ1, half_17_18_φ2, half_17_18_φ3, half_17_18_φ4, half_17_18_φ5, half_17_18_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_18_hx2 : SourcePowerBound (powerBoxCross 18 15 4 half_17_18_φ2) (179706773845733/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 15) (u := 13) (t := 16)
    (D := 4) (ψ := (200561872639/5000000000000 : ℝ)) half_17_18_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_18_φ1, half_17_18_φ2, half_17_18_φ3, half_17_18_φ4, half_17_18_φ5, half_17_18_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_18_φ1, half_17_18_φ2, half_17_18_φ3, half_17_18_φ4, half_17_18_φ5, half_17_18_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_18_φ1, half_17_18_φ2, half_17_18_φ3, half_17_18_φ4, half_17_18_φ5, half_17_18_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_14_18 half_16_18
    (by simpa only [half_17_18_φ3, show (2:ℝ)*4=8 by norm_num] using half_17_18_hx3)
  exact h.weaken (by norm_num [half_17_18_φ1, half_17_18_φ2, half_17_18_φ3, half_17_18_φ4, half_17_18_φ5, half_17_18_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_18_hx1 : SourcePowerBound (powerBoxCross 18 16 2 half_17_18_φ1) (198630317331777/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 16) (u := 14) (t := 17)
    (D := 2) (ψ := (412010809137/10000000000000 : ℝ)) half_17_18_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_18_φ1, half_17_18_φ2, half_17_18_φ3, half_17_18_φ4, half_17_18_φ5, half_17_18_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_18_φ1, half_17_18_φ2, half_17_18_φ3, half_17_18_φ4, half_17_18_φ5, half_17_18_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_18_φ1, half_17_18_φ2, half_17_18_φ3, half_17_18_φ4, half_17_18_φ5, half_17_18_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_15_18 half_17_17
    (by simpa only [half_17_18_φ2, show (2:ℝ)*2=4 by norm_num] using half_17_18_hx2)
  exact h.weaken (by norm_num [half_17_18_φ1, half_17_18_φ2, half_17_18_φ3, half_17_18_φ4, half_17_18_φ5, half_17_18_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_18 : AdmissibleExponent 18 34 (826980126977/39062500000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 15) (ψ := (84365130157/2000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_16_18
    (by simpa only [half_17_18_φ1] using half_17_18_hx1)
  exact admissibleExponent_mono h (by norm_num [half_17_18_φ1, half_17_18_φ2, half_17_18_φ3, half_17_18_φ4, half_17_18_φ5, half_17_18_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])


end Waring.SeedCompletionHigher18SimpleSeeds
