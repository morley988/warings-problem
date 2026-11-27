import Waring.SeedCompletionHigher18SimpleSeedsC06

noncomputable section
set_option maxHeartbeats 2000000
namespace Waring.SeedCompletionHigher18SimpleSeeds
open SmoothMoments FirstStageTransport SeedCompletionNaturalBox
open SeedCompletionSourceBounds SeedCompletionPaddedSource SeedCompletionGeneralTerminal
open PolicyCompletionMajorPowerRanges

def half_9_07_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (343847627101/10000000000000 : ℝ)

def half_9_07_φ2 : Fin 2 → ℝ := Fin.snoc half_9_07_φ1 (308355321689/10000000000000 : ℝ)

def half_9_07_φ3 : Fin 3 → ℝ := Fin.snoc half_9_07_φ2 (134510190669/10000000000000 : ℝ)

theorem half_9_07_hF2 : SourcePowerBound (paddedMoment 18 0 2 8 half_9_07_φ3) (69877629887591/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_07_φ3 (by norm_num [half_9_07_φ1, half_9_07_φ2, half_9_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_07_φ1, half_9_07_φ2, half_9_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_07_φ1, half_9_07_φ2, half_9_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_07_φ1, half_9_07_φ2, half_9_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_9_07_hF1 : SourcePowerBound (paddedMoment 18 0 1 8 half_9_07_φ3) (26625876629197/10000000000000 : ℝ) := by
  have h := padded_second_power (k := 18) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_07_φ3 (by norm_num [half_9_07_φ1, half_9_07_φ2, half_9_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_07_φ1, half_9_07_φ2, half_9_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_07_φ1, half_9_07_φ2, half_9_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_07_φ1, half_9_07_φ2, half_9_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_9_07_hx3 : SourcePowerBound (powerBoxCross 18 6 8 half_9_07_φ3) (2406007974313/312500000000 : ℝ) := by
  have h := full_B_cross_power (k := 18) (s := 6) (r := 1) (v := 2) (t := 10) (D := 8)
    (a := (3/10 : ℝ)) (b := (1/10 : ℝ)) (c := (3/5 : ℝ))
    (by norm_num) half_9_07_φ3 (by norm_num [half_9_07_φ1, half_9_07_φ2, half_9_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_07_φ1, half_9_07_φ2, half_9_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_9_07_hF1 half_9_07_hF2 half_10_06
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_9_07_φ1, half_9_07_φ2, half_9_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_9_07_hx2 : SourcePowerBound (powerBoxCross 18 7 4 half_9_07_φ2) (3370765629203/400000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 7) (u := 5) (t := 8)
    (D := 4) (ψ := (134510190669/10000000000000 : ℝ)) half_9_07_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_07_φ1, half_9_07_φ2, half_9_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_07_φ1, half_9_07_φ2, half_9_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_07_φ1, half_9_07_φ2, half_9_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_6 SeedCompletionEven18SecondSeeds.degree18_half_8
    (by simpa only [half_9_07_φ3, show (2:ℝ)*4=8 by norm_num] using half_9_07_hx3)
  exact h.weaken (by norm_num [half_9_07_φ1, half_9_07_φ2, half_9_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_9_07_hx1 : SourcePowerBound (powerBoxCross 18 8 2 half_9_07_φ1) (94174730473041/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 8) (u := 6) (t := 9)
    (D := 2) (ψ := (308355321689/10000000000000 : ℝ)) half_9_07_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_07_φ1, half_9_07_φ2, half_9_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_07_φ1, half_9_07_φ2, half_9_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_07_φ1, half_9_07_φ2, half_9_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_7 half_9_06
    (by simpa only [half_9_07_φ2, show (2:ℝ)*2=4 by norm_num] using half_9_07_hx2)
  exact h.weaken (by norm_num [half_9_07_φ1, half_9_07_φ2, half_9_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_9_07 : AdmissibleExponent 18 18 (24833111219889/2500000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 7) (ψ := (343847627101/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_8
    (by simpa only [half_9_07_φ1] using half_9_07_hx1)
  exact admissibleExponent_mono h (by norm_num [half_9_07_φ1, half_9_07_φ2, half_9_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_10_07_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (14151089969/400000000000 : ℝ)

def half_10_07_φ2 : Fin 2 → ℝ := Fin.snoc half_10_07_φ1 (1646318577/50000000000 : ℝ)

def half_10_07_φ3 : Fin 3 → ℝ := Fin.snoc half_10_07_φ2 (114984600737/5000000000000 : ℝ)

theorem half_10_07_hF2 : SourcePowerBound (paddedMoment 18 0 2 8 half_10_07_φ3) (63436481528951/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_10_07_φ3 (by norm_num [half_10_07_φ1, half_10_07_φ2, half_10_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_07_φ1, half_10_07_φ2, half_10_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_07_φ1, half_10_07_φ2, half_10_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_10_07_φ1, half_10_07_φ2, half_10_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_10_07_hx3 : SourcePowerBound (powerBoxCross 18 7 8 half_10_07_φ3) (86476847551649/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 7) (r := 2) (v := 9) (w := 10) (D := 8)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_10_07_φ3 (by norm_num [half_10_07_φ1, half_10_07_φ2, half_10_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_07_φ1, half_10_07_φ2, half_10_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_10_07_hF2 half_9_07 half_10_06
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_10_07_φ1, half_10_07_φ2, half_10_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_07_hx2 : SourcePowerBound (powerBoxCross 18 8 4 half_10_07_φ2) (95201191377417/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 8) (u := 6) (t := 9)
    (D := 4) (ψ := (114984600737/5000000000000 : ℝ)) half_10_07_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_07_φ1, half_10_07_φ2, half_10_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_07_φ1, half_10_07_φ2, half_10_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_07_φ1, half_10_07_φ2, half_10_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_7 half_9_07
    (by simpa only [half_10_07_φ3, show (2:ℝ)*4=8 by norm_num] using half_10_07_hx3)
  exact h.weaken (by norm_num [half_10_07_φ1, half_10_07_φ2, half_10_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_07_hx1 : SourcePowerBound (powerBoxCross 18 9 2 half_10_07_φ1) (106172066217961/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 9) (u := 7) (t := 10)
    (D := 2) (ψ := (1646318577/50000000000 : ℝ)) half_10_07_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_07_φ1, half_10_07_φ2, half_10_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_07_φ1, half_10_07_φ2, half_10_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_07_φ1, half_10_07_φ2, half_10_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_8 half_10_06
    (by simpa only [half_10_07_φ2, show (2:ℝ)*2=4 by norm_num] using half_10_07_hx2)
  exact h.weaken (by norm_num [half_10_07_φ1, half_10_07_φ2, half_10_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_07 : AdmissibleExponent 18 20 (56093139727393/5000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 8) (ψ := (14151089969/400000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_9_07
    (by simpa only [half_10_07_φ1] using half_10_07_hx1)
  exact admissibleExponent_mono h (by norm_num [half_10_07_φ1, half_10_07_φ2, half_10_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_11_07_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (72974208847/2000000000000 : ℝ)

def half_11_07_φ2 : Fin 2 → ℝ := Fin.snoc half_11_07_φ1 (43304973201/1250000000000 : ℝ)

def half_11_07_φ3 : Fin 3 → ℝ := Fin.snoc half_11_07_φ2 (36866206429/1250000000000 : ℝ)

theorem half_11_07_hF2 : SourcePowerBound (paddedMoment 18 0 2 8 half_11_07_φ3) (2347269418199/400000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_11_07_φ3 (by norm_num [half_11_07_φ1, half_11_07_φ2, half_11_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_07_φ1, half_11_07_φ2, half_11_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_07_φ1, half_11_07_φ2, half_11_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_11_07_φ1, half_11_07_φ2, half_11_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_11_07_hx3 : SourcePowerBound (powerBoxCross 18 8 8 half_11_07_φ3) (96282896501491/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 8) (r := 2) (v := 10) (w := 11) (D := 8)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_11_07_φ3 (by norm_num [half_11_07_φ1, half_11_07_φ2, half_11_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_07_φ1, half_11_07_φ2, half_11_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_11_07_hF2 half_10_07 half_11_06
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_11_07_φ1, half_11_07_φ2, half_11_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_07_hx2 : SourcePowerBound (powerBoxCross 18 9 4 half_11_07_φ2) (53205226266707/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 9) (u := 7) (t := 10)
    (D := 4) (ψ := (36866206429/1250000000000 : ℝ)) half_11_07_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_07_φ1, half_11_07_φ2, half_11_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_07_φ1, half_11_07_φ2, half_11_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_07_φ1, half_11_07_φ2, half_11_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_8 half_10_07
    (by simpa only [half_11_07_φ3, show (2:ℝ)*4=8 by norm_num] using half_11_07_hx3)
  exact h.weaken (by norm_num [half_11_07_φ1, half_11_07_φ2, half_11_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_07_hx1 : SourcePowerBound (powerBoxCross 18 10 2 half_11_07_φ1) (118457798005683/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 10) (u := 8) (t := 11)
    (D := 2) (ψ := (43304973201/1250000000000 : ℝ)) half_11_07_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_07_φ1, half_11_07_φ2, half_11_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_07_φ1, half_11_07_φ2, half_11_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_07_φ1, half_11_07_φ2, half_11_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_07 half_11_06
    (by simpa only [half_11_07_φ2, show (2:ℝ)*2=4 by norm_num] using half_11_07_hx2)
  exact h.weaken (by norm_num [half_11_07_φ1, half_11_07_φ2, half_11_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_07 : AdmissibleExponent 18 22 (31347586961537/2500000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 9) (ψ := (72974208847/2000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_10_07
    (by simpa only [half_11_07_φ1] using half_11_07_hx1)
  exact admissibleExponent_mono h (by norm_num [half_11_07_φ1, half_11_07_φ2, half_11_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_12_07_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (187609278607/5000000000000 : ℝ)

def half_12_07_φ2 : Fin 2 → ℝ := Fin.snoc half_12_07_φ1 (36061661891/1000000000000 : ℝ)

def half_12_07_φ3 : Fin 3 → ℝ := Fin.snoc half_12_07_φ2 (329467763941/10000000000000 : ℝ)

def half_12_07_φ4 : Fin 4 → ℝ := Fin.snoc half_12_07_φ3 (213074519973/10000000000000 : ℝ)

theorem half_12_07_hF2 : SourcePowerBound (paddedMoment 18 0 2 16 half_12_07_φ4) (37401374769031/5000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_12_07_φ4 (by norm_num [half_12_07_φ1, half_12_07_φ2, half_12_07_φ3, half_12_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_07_φ1, half_12_07_φ2, half_12_07_φ3, half_12_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_07_φ1, half_12_07_φ2, half_12_07_φ3, half_12_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_12_07_φ1, half_12_07_φ2, half_12_07_φ3, half_12_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_12_07_hF1 : SourcePowerBound (paddedMoment 18 0 1 16 half_12_07_φ4) (14133791589677/5000000000000 : ℝ) := by
  have h := padded_second_power (k := 18) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_12_07_φ4 (by norm_num [half_12_07_φ1, half_12_07_φ2, half_12_07_φ3, half_12_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_07_φ1, half_12_07_φ2, half_12_07_φ3, half_12_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_07_φ1, half_12_07_φ2, half_12_07_φ3, half_12_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_12_07_φ1, half_12_07_φ2, half_12_07_φ3, half_12_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_12_07_hx4 : SourcePowerBound (powerBoxCross 18 8 16 half_12_07_φ4) (97820590244523/10000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 18) (s := 8) (r := 1) (v := 2) (t := 11) (D := 16)
    (a := (1/22 : ℝ)) (b := (5/22 : ℝ)) (c := (8/11 : ℝ))
    (by norm_num) half_12_07_φ4 (by norm_num [half_12_07_φ1, half_12_07_φ2, half_12_07_φ3, half_12_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_07_φ1, half_12_07_φ2, half_12_07_φ3, half_12_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_12_07_hF1 half_12_07_hF2 half_11_07
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_12_07_φ1, half_12_07_φ2, half_12_07_φ3, half_12_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_07_hx3 : SourcePowerBound (powerBoxCross 18 9 8 half_12_07_φ3) (106570800091993/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 9) (u := 7) (t := 10)
    (D := 8) (ψ := (213074519973/10000000000000 : ℝ)) half_12_07_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_07_φ1, half_12_07_φ2, half_12_07_φ3, half_12_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_07_φ1, half_12_07_φ2, half_12_07_φ3, half_12_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_07_φ1, half_12_07_φ2, half_12_07_φ3, half_12_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_8 half_10_07
    (by simpa only [half_12_07_φ4, show (2:ℝ)*8=16 by norm_num] using half_12_07_hx4)
  exact h.weaken (by norm_num [half_12_07_φ1, half_12_07_φ2, half_12_07_φ3, half_12_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_07_hx2 : SourcePowerBound (powerBoxCross 18 10 4 half_12_07_φ2) (23582623906187/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 10) (u := 8) (t := 11)
    (D := 4) (ψ := (329467763941/10000000000000 : ℝ)) half_12_07_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_07_φ1, half_12_07_φ2, half_12_07_φ3, half_12_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_07_φ1, half_12_07_φ2, half_12_07_φ3, half_12_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_07_φ1, half_12_07_φ2, half_12_07_φ3, half_12_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_07 half_11_07
    (by simpa only [half_12_07_φ3, show (2:ℝ)*4=8 by norm_num] using half_12_07_hx3)
  exact h.weaken (by norm_num [half_12_07_φ1, half_12_07_φ2, half_12_07_φ3, half_12_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_07_hx1 : SourcePowerBound (powerBoxCross 18 11 2 half_12_07_φ1) (131060687862631/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 11) (u := 9) (t := 12)
    (D := 2) (ψ := (36061661891/1000000000000 : ℝ)) half_12_07_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_07_φ1, half_12_07_φ2, half_12_07_φ3, half_12_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_07_φ1, half_12_07_φ2, half_12_07_φ3, half_12_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_07_φ1, half_12_07_φ2, half_12_07_φ3, half_12_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_07 half_12_06
    (by simpa only [half_12_07_φ2, show (2:ℝ)*2=4 by norm_num] using half_12_07_hx2)
  exact h.weaken (by norm_num [half_12_07_φ1, half_12_07_φ2, half_12_07_φ3, half_12_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_07 : AdmissibleExponent 18 24 (1111522220513/80000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 10) (ψ := (187609278607/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_11_07
    (by simpa only [half_12_07_φ1] using half_12_07_hx1)
  exact admissibleExponent_mono h (by norm_num [half_12_07_φ1, half_12_07_φ2, half_12_07_φ3, half_12_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_13_07_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (96308877083/2500000000000 : ℝ)

def half_13_07_φ2 : Fin 2 → ℝ := Fin.snoc half_13_07_φ1 (372031859923/10000000000000 : ℝ)

def half_13_07_φ3 : Fin 3 → ℝ := Fin.snoc half_13_07_φ2 (349999585623/10000000000000 : ℝ)

def half_13_07_φ4 : Fin 4 → ℝ := Fin.snoc half_13_07_φ3 (886559773/31250000000 : ℝ)

theorem half_13_07_hF2 : SourcePowerBound (paddedMoment 18 0 2 16 half_13_07_φ4) (34530364928431/5000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_13_07_φ4 (by norm_num [half_13_07_φ1, half_13_07_φ2, half_13_07_φ3, half_13_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_07_φ1, half_13_07_φ2, half_13_07_φ3, half_13_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_07_φ1, half_13_07_φ2, half_13_07_φ3, half_13_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_13_07_φ1, half_13_07_φ2, half_13_07_φ3, half_13_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_13_07_hx4 : SourcePowerBound (powerBoxCross 18 9 16 half_13_07_φ4) (53487899815799/5000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 9) (r := 2) (v := 12) (w := 12) (D := 16)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_13_07_φ4 (by norm_num [half_13_07_φ1, half_13_07_φ2, half_13_07_φ3, half_13_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_07_φ1, half_13_07_φ2, half_13_07_φ3, half_13_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_13_07_hF2 half_12_07 half_12_07
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_13_07_φ1, half_13_07_φ2, half_13_07_φ3, half_13_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_07_hx3 : SourcePowerBound (powerBoxCross 18 10 8 half_13_07_φ3) (58620358894103/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 10) (u := 8) (t := 11)
    (D := 8) (ψ := (886559773/31250000000 : ℝ)) half_13_07_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_07_φ1, half_13_07_φ2, half_13_07_φ3, half_13_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_07_φ1, half_13_07_φ2, half_13_07_φ3, half_13_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_07_φ1, half_13_07_φ2, half_13_07_φ3, half_13_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_07 half_11_07
    (by simpa only [half_13_07_φ4, show (2:ℝ)*8=16 by norm_num] using half_13_07_hx4)
  exact h.weaken (by norm_num [half_13_07_φ1, half_13_07_φ2, half_13_07_φ3, half_13_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_07_hx2 : SourcePowerBound (powerBoxCross 18 11 4 half_13_07_φ2) (129717974192637/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 11) (u := 9) (t := 12)
    (D := 4) (ψ := (349999585623/10000000000000 : ℝ)) half_13_07_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_07_φ1, half_13_07_φ2, half_13_07_φ3, half_13_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_07_φ1, half_13_07_φ2, half_13_07_φ3, half_13_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_07_φ1, half_13_07_φ2, half_13_07_φ3, half_13_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_07 half_12_07
    (by simpa only [half_13_07_φ3, show (2:ℝ)*4=8 by norm_num] using half_13_07_hx3)
  exact h.weaken (by norm_num [half_13_07_φ1, half_13_07_φ2, half_13_07_φ3, half_13_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_07_hx1 : SourcePowerBound (powerBoxCross 18 12 2 half_13_07_φ1) (143973040226947/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 12) (u := 10) (t := 13)
    (D := 2) (ψ := (372031859923/10000000000000 : ℝ)) half_13_07_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_07_φ1, half_13_07_φ2, half_13_07_φ3, half_13_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_07_φ1, half_13_07_φ2, half_13_07_φ3, half_13_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_07_φ1, half_13_07_φ2, half_13_07_φ3, half_13_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_07 half_13_06
    (by simpa only [half_13_07_φ2, show (2:ℝ)*2=4 by norm_num] using half_13_07_hx2)
  exact h.weaken (by norm_num [half_13_07_φ1, half_13_07_φ2, half_13_07_φ3, half_13_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_07 : AdmissibleExponent 18 26 (152833456918583/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 11) (ψ := (96308877083/2500000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_12_07
    (by simpa only [half_13_07_φ1] using half_13_07_hx1)
  exact admissibleExponent_mono h (by norm_num [half_13_07_φ1, half_13_07_φ2, half_13_07_φ3, half_13_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_14_07_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (79114566239/2000000000000 : ℝ)

def half_14_07_φ2 : Fin 2 → ℝ := Fin.snoc half_14_07_φ1 (47888321093/1250000000000 : ℝ)

def half_14_07_φ3 : Fin 3 → ℝ := Fin.snoc half_14_07_φ2 (91832992229/2500000000000 : ℝ)

def half_14_07_φ4 : Fin 4 → ℝ := Fin.snoc half_14_07_φ3 (332263072047/10000000000000 : ℝ)

def half_14_07_φ5 : Fin 5 → ℝ := Fin.snoc half_14_07_φ4 (206156111333/10000000000000 : ℝ)

theorem half_14_07_hF2 : SourcePowerBound (paddedMoment 18 0 2 32 half_14_07_φ5) (16818808367203/2000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_14_07_φ5 (by norm_num [half_14_07_φ1, half_14_07_φ2, half_14_07_φ3, half_14_07_φ4, half_14_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_07_φ1, half_14_07_φ2, half_14_07_φ3, half_14_07_φ4, half_14_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_07_φ1, half_14_07_φ2, half_14_07_φ3, half_14_07_φ4, half_14_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_14_07_φ1, half_14_07_φ2, half_14_07_φ3, half_14_07_φ4, half_14_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_14_07_hx5 : SourcePowerBound (powerBoxCross 18 9 32 half_14_07_φ5) (107676074997221/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 9) (r := 2) (v := 12) (w := 12) (D := 32)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_14_07_φ5 (by norm_num [half_14_07_φ1, half_14_07_φ2, half_14_07_φ3, half_14_07_φ4, half_14_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_07_φ1, half_14_07_φ2, half_14_07_φ3, half_14_07_φ4, half_14_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_14_07_hF2 half_12_07 half_12_07
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_14_07_φ1, half_14_07_φ2, half_14_07_φ3, half_14_07_φ4, half_14_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_07_hx4 : SourcePowerBound (powerBoxCross 18 10 16 half_14_07_φ4) (116452138302511/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 10) (u := 8) (t := 11)
    (D := 16) (ψ := (206156111333/10000000000000 : ℝ)) half_14_07_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_07_φ1, half_14_07_φ2, half_14_07_φ3, half_14_07_φ4, half_14_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_07_φ1, half_14_07_φ2, half_14_07_φ3, half_14_07_φ4, half_14_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_07_φ1, half_14_07_φ2, half_14_07_φ3, half_14_07_φ4, half_14_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_07 half_11_07
    (by simpa only [half_14_07_φ5, show (2:ℝ)*16=32 by norm_num] using half_14_07_hx5)
  exact h.weaken (by norm_num [half_14_07_φ1, half_14_07_φ2, half_14_07_φ3, half_14_07_φ4, half_14_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_07_hx3 : SourcePowerBound (powerBoxCross 18 11 8 half_14_07_φ3) (1601878169981/125000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 11) (u := 9) (t := 12)
    (D := 8) (ψ := (332263072047/10000000000000 : ℝ)) half_14_07_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_07_φ1, half_14_07_φ2, half_14_07_φ3, half_14_07_φ4, half_14_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_07_φ1, half_14_07_φ2, half_14_07_φ3, half_14_07_φ4, half_14_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_07_φ1, half_14_07_φ2, half_14_07_φ3, half_14_07_φ4, half_14_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_07 half_12_07
    (by simpa only [half_14_07_φ4, show (2:ℝ)*8=16 by norm_num] using half_14_07_hx4)
  exact h.weaken (by norm_num [half_14_07_φ1, half_14_07_φ2, half_14_07_φ3, half_14_07_φ4, half_14_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_07_hx2 : SourcePowerBound (powerBoxCross 18 12 4 half_14_07_φ2) (14177965280647/1000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 12) (u := 10) (t := 13)
    (D := 4) (ψ := (91832992229/2500000000000 : ℝ)) half_14_07_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_07_φ1, half_14_07_φ2, half_14_07_φ3, half_14_07_φ4, half_14_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_07_φ1, half_14_07_φ2, half_14_07_φ3, half_14_07_φ4, half_14_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_07_φ1, half_14_07_φ2, half_14_07_φ3, half_14_07_φ4, half_14_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_07 half_13_07
    (by simpa only [half_14_07_φ3, show (2:ℝ)*4=8 by norm_num] using half_14_07_hx3)
  exact h.weaken (by norm_num [half_14_07_φ1, half_14_07_φ2, half_14_07_φ3, half_14_07_φ4, half_14_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_07_hx1 : SourcePowerBound (powerBoxCross 18 13 2 half_14_07_φ1) (157183353424331/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 13) (u := 11) (t := 14)
    (D := 2) (ψ := (47888321093/1250000000000 : ℝ)) half_14_07_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_07_φ1, half_14_07_φ2, half_14_07_φ3, half_14_07_φ4, half_14_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_07_φ1, half_14_07_φ2, half_14_07_φ3, half_14_07_φ4, half_14_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_07_φ1, half_14_07_φ2, half_14_07_φ3, half_14_07_φ4, half_14_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_07 half_14_06
    (by simpa only [half_14_07_φ2, show (2:ℝ)*2=4 by norm_num] using half_14_07_hx2)
  exact h.weaken (by norm_num [half_14_07_φ1, half_14_07_φ2, half_14_07_φ3, half_14_07_φ4, half_14_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_07 : AdmissibleExponent 18 28 (83536337102103/5000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 12) (ψ := (79114566239/2000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_13_07
    (by simpa only [half_14_07_φ1] using half_14_07_hx1)
  exact admissibleExponent_mono h (by norm_num [half_14_07_φ1, half_14_07_φ2, half_14_07_φ3, half_14_07_φ4, half_14_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_15_07_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (405772391703/10000000000000 : ℝ)

def half_15_07_φ2 : Fin 2 → ℝ := Fin.snoc half_15_07_φ1 (393194262273/10000000000000 : ℝ)

def half_15_07_φ3 : Fin 3 → ℝ := Fin.snoc half_15_07_φ2 (47454647299/1250000000000 : ℝ)

def half_15_07_φ4 : Fin 4 → ℝ := Fin.snoc half_15_07_φ3 (177790756163/5000000000000 : ℝ)

def half_15_07_φ5 : Fin 5 → ℝ := Fin.snoc half_15_07_φ4 (142809952671/5000000000000 : ℝ)

theorem half_15_07_hF2 : SourcePowerBound (paddedMoment 18 0 2 32 half_15_07_φ5) (19297483062041/2500000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_15_07_φ5 (by norm_num [half_15_07_φ1, half_15_07_φ2, half_15_07_φ3, half_15_07_φ4, half_15_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_07_φ1, half_15_07_φ2, half_15_07_φ3, half_15_07_φ4, half_15_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_07_φ1, half_15_07_φ2, half_15_07_φ3, half_15_07_φ4, half_15_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_15_07_φ1, half_15_07_φ2, half_15_07_φ3, half_15_07_φ4, half_15_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_15_07_hx5 : SourcePowerBound (powerBoxCross 18 10 32 half_15_07_φ5) (57987515233473/5000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 10) (r := 2) (v := 13) (w := 14) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_15_07_φ5 (by norm_num [half_15_07_φ1, half_15_07_φ2, half_15_07_φ3, half_15_07_φ4, half_15_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_07_φ1, half_15_07_φ2, half_15_07_φ3, half_15_07_φ4, half_15_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_15_07_hF2 half_13_07 half_14_07
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_15_07_φ1, half_15_07_φ2, half_15_07_φ3, half_15_07_φ4, half_15_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_07_hx4 : SourcePowerBound (powerBoxCross 18 11 16 half_15_07_φ4) (126472460805057/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 11) (u := 9) (t := 12)
    (D := 16) (ψ := (142809952671/5000000000000 : ℝ)) half_15_07_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_07_φ1, half_15_07_φ2, half_15_07_φ3, half_15_07_φ4, half_15_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_07_φ1, half_15_07_φ2, half_15_07_φ3, half_15_07_φ4, half_15_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_07_φ1, half_15_07_φ2, half_15_07_φ3, half_15_07_φ4, half_15_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_07 half_12_07
    (by simpa only [half_15_07_φ5, show (2:ℝ)*16=32 by norm_num] using half_15_07_hx5)
  exact h.weaken (by norm_num [half_15_07_φ1, half_15_07_φ2, half_15_07_φ3, half_15_07_φ4, half_15_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_07_hx3 : SourcePowerBound (powerBoxCross 18 12 8 half_15_07_φ3) (139361927264201/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 12) (u := 10) (t := 13)
    (D := 8) (ψ := (177790756163/5000000000000 : ℝ)) half_15_07_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_07_φ1, half_15_07_φ2, half_15_07_φ3, half_15_07_φ4, half_15_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_07_φ1, half_15_07_φ2, half_15_07_φ3, half_15_07_φ4, half_15_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_07_φ1, half_15_07_φ2, half_15_07_φ3, half_15_07_φ4, half_15_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_07 half_13_07
    (by simpa only [half_15_07_φ4, show (2:ℝ)*8=16 by norm_num] using half_15_07_hx4)
  exact h.weaken (by norm_num [half_15_07_φ1, half_15_07_φ2, half_15_07_φ3, half_15_07_φ4, half_15_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_07_hx2 : SourcePowerBound (powerBoxCross 18 13 4 half_15_07_φ2) (4816176154779/312500000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 13) (u := 11) (t := 14)
    (D := 4) (ψ := (47454647299/1250000000000 : ℝ)) half_15_07_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_07_φ1, half_15_07_φ2, half_15_07_φ3, half_15_07_φ4, half_15_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_07_φ1, half_15_07_φ2, half_15_07_φ3, half_15_07_φ4, half_15_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_07_φ1, half_15_07_φ2, half_15_07_φ3, half_15_07_φ4, half_15_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_07 half_14_07
    (by simpa only [half_15_07_φ3, show (2:ℝ)*4=8 by norm_num] using half_15_07_hx3)
  exact h.weaken (by norm_num [half_15_07_φ1, half_15_07_φ2, half_15_07_φ3, half_15_07_φ4, half_15_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_07_hx1 : SourcePowerBound (powerBoxCross 18 14 2 half_15_07_φ1) (85349549367959/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 14) (u := 12) (t := 15)
    (D := 2) (ψ := (393194262273/10000000000000 : ℝ)) half_15_07_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_07_φ1, half_15_07_φ2, half_15_07_φ3, half_15_07_φ4, half_15_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_07_φ1, half_15_07_φ2, half_15_07_φ3, half_15_07_φ4, half_15_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_07_φ1, half_15_07_φ2, half_15_07_φ3, half_15_07_φ4, half_15_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_13_07 half_15_06
    (by simpa only [half_15_07_φ2, show (2:ℝ)*2=4 by norm_num] using half_15_07_hx2)
  exact h.weaken (by norm_num [half_15_07_φ1, half_15_07_φ2, half_15_07_φ3, half_15_07_φ4, half_15_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_07 : AdmissibleExponent 18 30 (181654953311899/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 13) (ψ := (405772391703/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_14_07
    (by simpa only [half_15_07_φ1] using half_15_07_hx1)
  exact admissibleExponent_mono h (by norm_num [half_15_07_φ1, half_15_07_φ2, half_15_07_φ3, half_15_07_φ4, half_15_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_16_07_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (208138159489/5000000000000 : ℝ)

def half_16_07_φ2 : Fin 2 → ℝ := Fin.snoc half_16_07_φ1 (403010857623/10000000000000 : ℝ)

def half_16_07_φ3 : Fin 3 → ℝ := Fin.snoc half_16_07_φ2 (19565041229/500000000000 : ℝ)

def half_16_07_φ4 : Fin 4 → ℝ := Fin.snoc half_16_07_φ3 (7486034197/200000000000 : ℝ)

def half_16_07_φ5 : Fin 5 → ℝ := Fin.snoc half_16_07_φ4 (168376752653/5000000000000 : ℝ)

def half_16_07_φ6 : Fin 6 → ℝ := Fin.snoc half_16_07_φ5 (104979441719/5000000000000 : ℝ)

theorem half_16_07_hF2 : SourcePowerBound (paddedMoment 18 0 2 64 half_16_07_φ6) (3651531716459/400000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 6) (r := 0) (D := 64)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_16_07_φ6 (by norm_num [half_16_07_φ1, half_16_07_φ2, half_16_07_φ3, half_16_07_φ4, half_16_07_φ5, half_16_07_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_07_φ1, half_16_07_φ2, half_16_07_φ3, half_16_07_φ4, half_16_07_φ5, half_16_07_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_07_φ1, half_16_07_φ2, half_16_07_φ3, half_16_07_φ4, half_16_07_φ5, half_16_07_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_16_07_φ1, half_16_07_φ2, half_16_07_φ3, half_16_07_φ4, half_16_07_φ5, half_16_07_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_16_07_hx6 : SourcePowerBound (powerBoxCross 18 10 64 half_16_07_φ6) (57907326387659/5000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 10) (r := 2) (v := 13) (w := 14) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_16_07_φ6 (by norm_num [half_16_07_φ1, half_16_07_φ2, half_16_07_φ3, half_16_07_φ4, half_16_07_φ5, half_16_07_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_07_φ1, half_16_07_φ2, half_16_07_φ3, half_16_07_φ4, half_16_07_φ5, half_16_07_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_16_07_hF2 half_13_07 half_14_07
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_16_07_φ1, half_16_07_φ2, half_16_07_φ3, half_16_07_φ4, half_16_07_φ5, half_16_07_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_07_hx5 : SourcePowerBound (powerBoxCross 18 11 32 half_16_07_φ5) (24937685026133/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 5) (s := 11) (u := 9) (t := 12)
    (D := 32) (ψ := (104979441719/5000000000000 : ℝ)) half_16_07_φ5
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_07_φ1, half_16_07_φ2, half_16_07_φ3, half_16_07_φ4, half_16_07_φ5, half_16_07_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_07_φ1, half_16_07_φ2, half_16_07_φ3, half_16_07_φ4, half_16_07_φ5, half_16_07_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_07_φ1, half_16_07_φ2, half_16_07_φ3, half_16_07_φ4, half_16_07_φ5, half_16_07_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_07 half_12_07
    (by simpa only [half_16_07_φ6, show (2:ℝ)*32=64 by norm_num] using half_16_07_hx6)
  exact h.weaken (by norm_num [half_16_07_φ1, half_16_07_φ2, half_16_07_φ3, half_16_07_φ4, half_16_07_φ5, half_16_07_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_07_hx4 : SourcePowerBound (powerBoxCross 18 12 16 half_16_07_φ4) (34178520404499/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 12) (u := 10) (t := 13)
    (D := 16) (ψ := (168376752653/5000000000000 : ℝ)) half_16_07_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_07_φ1, half_16_07_φ2, half_16_07_φ3, half_16_07_φ4, half_16_07_φ5, half_16_07_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_07_φ1, half_16_07_φ2, half_16_07_φ3, half_16_07_φ4, half_16_07_φ5, half_16_07_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_07_φ1, half_16_07_φ2, half_16_07_φ3, half_16_07_φ4, half_16_07_φ5, half_16_07_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_07 half_13_07
    (by simpa only [half_16_07_φ5, show (2:ℝ)*16=32 by norm_num] using half_16_07_hx5)
  exact h.weaken (by norm_num [half_16_07_φ1, half_16_07_φ2, half_16_07_φ3, half_16_07_φ4, half_16_07_φ5, half_16_07_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_07_hx3 : SourcePowerBound (powerBoxCross 18 13 8 half_16_07_φ3) (9424690051781/625000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 13) (u := 11) (t := 14)
    (D := 8) (ψ := (7486034197/200000000000 : ℝ)) half_16_07_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_07_φ1, half_16_07_φ2, half_16_07_φ3, half_16_07_φ4, half_16_07_φ5, half_16_07_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_07_φ1, half_16_07_φ2, half_16_07_φ3, half_16_07_φ4, half_16_07_φ5, half_16_07_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_07_φ1, half_16_07_φ2, half_16_07_φ3, half_16_07_φ4, half_16_07_φ5, half_16_07_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_07 half_14_07
    (by simpa only [half_16_07_φ4, show (2:ℝ)*8=16 by norm_num] using half_16_07_hx4)
  exact h.weaken (by norm_num [half_16_07_φ1, half_16_07_φ2, half_16_07_φ3, half_16_07_φ4, half_16_07_φ5, half_16_07_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_07_hx2 : SourcePowerBound (powerBoxCross 18 14 4 half_16_07_φ2) (33342187537123/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 14) (u := 12) (t := 15)
    (D := 4) (ψ := (19565041229/500000000000 : ℝ)) half_16_07_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_07_φ1, half_16_07_φ2, half_16_07_φ3, half_16_07_φ4, half_16_07_φ5, half_16_07_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_07_φ1, half_16_07_φ2, half_16_07_φ3, half_16_07_φ4, half_16_07_φ5, half_16_07_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_07_φ1, half_16_07_φ2, half_16_07_φ3, half_16_07_φ4, half_16_07_φ5, half_16_07_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_13_07 half_15_07
    (by simpa only [half_16_07_φ3, show (2:ℝ)*4=8 by norm_num] using half_16_07_hx3)
  exact h.weaken (by norm_num [half_16_07_φ1, half_16_07_φ2, half_16_07_φ3, half_16_07_φ4, half_16_07_φ5, half_16_07_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_07_hx1 : SourcePowerBound (powerBoxCross 18 15 2 half_16_07_φ1) (184509364102017/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 15) (u := 13) (t := 16)
    (D := 2) (ψ := (403010857623/10000000000000 : ℝ)) half_16_07_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_07_φ1, half_16_07_φ2, half_16_07_φ3, half_16_07_φ4, half_16_07_φ5, half_16_07_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_07_φ1, half_16_07_φ2, half_16_07_φ3, half_16_07_φ4, half_16_07_φ5, half_16_07_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_07_φ1, half_16_07_φ2, half_16_07_φ3, half_16_07_φ4, half_16_07_φ5, half_16_07_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_14_07 half_16_06
    (by simpa only [half_16_07_φ2, show (2:ℝ)*2=4 by norm_num] using half_16_07_hx2)
  exact h.weaken (by norm_num [half_16_07_φ1, half_16_07_φ2, half_16_07_φ3, half_16_07_φ4, half_16_07_φ5, half_16_07_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_07 : AdmissibleExponent 18 32 (196581377352379/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 14) (ψ := (208138159489/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_15_07
    (by simpa only [half_16_07_φ1] using half_16_07_hx1)
  exact admissibleExponent_mono h (by norm_num [half_16_07_φ1, half_16_07_φ2, half_16_07_φ3, half_16_07_φ4, half_16_07_φ5, half_16_07_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_17_07_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (426845757567/10000000000000 : ℝ)

def half_17_07_φ2 : Fin 2 → ℝ := Fin.snoc half_17_07_φ1 (103118746413/2500000000000 : ℝ)

def half_17_07_φ3 : Fin 3 → ℝ := Fin.snoc half_17_07_φ2 (401482928673/10000000000000 : ℝ)

def half_17_07_φ4 : Fin 4 → ℝ := Fin.snoc half_17_07_φ3 (24219842357/625000000000 : ℝ)

def half_17_07_φ5 : Fin 5 → ℝ := Fin.snoc half_17_07_φ4 (362254839657/10000000000000 : ℝ)

def half_17_07_φ6 : Fin 6 → ℝ := Fin.snoc half_17_07_φ5 (292385710833/10000000000000 : ℝ)

theorem half_17_07_hF2 : SourcePowerBound (paddedMoment 18 0 2 64 half_17_07_φ6) (41784476647603/5000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 6) (r := 0) (D := 64)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_17_07_φ6 (by norm_num [half_17_07_φ1, half_17_07_φ2, half_17_07_φ3, half_17_07_φ4, half_17_07_φ5, half_17_07_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_07_φ1, half_17_07_φ2, half_17_07_φ3, half_17_07_φ4, half_17_07_φ5, half_17_07_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_07_φ1, half_17_07_φ2, half_17_07_φ3, half_17_07_φ4, half_17_07_φ5, half_17_07_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_17_07_φ1, half_17_07_φ2, half_17_07_φ3, half_17_07_φ4, half_17_07_φ5, half_17_07_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_17_07_hx6 : SourcePowerBound (powerBoxCross 18 11 64 half_17_07_φ6) (123216805570119/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 11) (r := 2) (v := 14) (w := 15) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_17_07_φ6 (by norm_num [half_17_07_φ1, half_17_07_φ2, half_17_07_φ3, half_17_07_φ4, half_17_07_φ5, half_17_07_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_07_φ1, half_17_07_φ2, half_17_07_φ3, half_17_07_φ4, half_17_07_φ5, half_17_07_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_17_07_hF2 half_14_07 half_15_07
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_17_07_φ1, half_17_07_φ2, half_17_07_φ3, half_17_07_φ4, half_17_07_φ5, half_17_07_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_07_hx5 : SourcePowerBound (powerBoxCross 18 12 32 half_17_07_φ5) (133963954814487/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 5) (s := 12) (u := 10) (t := 13)
    (D := 32) (ψ := (292385710833/10000000000000 : ℝ)) half_17_07_φ5
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_07_φ1, half_17_07_φ2, half_17_07_φ3, half_17_07_φ4, half_17_07_φ5, half_17_07_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_07_φ1, half_17_07_φ2, half_17_07_φ3, half_17_07_φ4, half_17_07_φ5, half_17_07_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_07_φ1, half_17_07_φ2, half_17_07_φ3, half_17_07_φ4, half_17_07_φ5, half_17_07_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_07 half_13_07
    (by simpa only [half_17_07_φ6, show (2:ℝ)*32=64 by norm_num] using half_17_07_hx6)
  exact h.weaken (by norm_num [half_17_07_φ1, half_17_07_φ2, half_17_07_φ3, half_17_07_φ4, half_17_07_φ5, half_17_07_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_07_hx4 : SourcePowerBound (powerBoxCross 18 13 16 half_17_07_φ4) (36810279236847/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 13) (u := 11) (t := 14)
    (D := 16) (ψ := (362254839657/10000000000000 : ℝ)) half_17_07_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_07_φ1, half_17_07_φ2, half_17_07_φ3, half_17_07_φ4, half_17_07_φ5, half_17_07_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_07_φ1, half_17_07_φ2, half_17_07_φ3, half_17_07_φ4, half_17_07_φ5, half_17_07_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_07_φ1, half_17_07_φ2, half_17_07_φ3, half_17_07_φ4, half_17_07_φ5, half_17_07_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_07 half_14_07
    (by simpa only [half_17_07_φ5, show (2:ℝ)*16=32 by norm_num] using half_17_07_hx5)
  exact h.weaken (by norm_num [half_17_07_φ1, half_17_07_φ2, half_17_07_φ3, half_17_07_φ4, half_17_07_φ5, half_17_07_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_07_hx3 : SourcePowerBound (powerBoxCross 18 14 8 half_17_07_φ3) (162475265735623/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 14) (u := 12) (t := 15)
    (D := 8) (ψ := (24219842357/625000000000 : ℝ)) half_17_07_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_07_φ1, half_17_07_φ2, half_17_07_φ3, half_17_07_φ4, half_17_07_φ5, half_17_07_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_07_φ1, half_17_07_φ2, half_17_07_φ3, half_17_07_φ4, half_17_07_φ5, half_17_07_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_07_φ1, half_17_07_φ2, half_17_07_φ3, half_17_07_φ4, half_17_07_φ5, half_17_07_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_13_07 half_15_07
    (by simpa only [half_17_07_φ4, show (2:ℝ)*8=16 by norm_num] using half_17_07_hx4)
  exact h.weaken (by norm_num [half_17_07_φ1, half_17_07_φ2, half_17_07_φ3, half_17_07_φ4, half_17_07_φ5, half_17_07_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_07_hx2 : SourcePowerBound (powerBoxCross 18 15 4 half_17_07_φ2) (35912874675321/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 15) (u := 13) (t := 16)
    (D := 4) (ψ := (401482928673/10000000000000 : ℝ)) half_17_07_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_07_φ1, half_17_07_φ2, half_17_07_φ3, half_17_07_φ4, half_17_07_φ5, half_17_07_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_07_φ1, half_17_07_φ2, half_17_07_φ3, half_17_07_φ4, half_17_07_φ5, half_17_07_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_07_φ1, half_17_07_φ2, half_17_07_φ3, half_17_07_φ4, half_17_07_φ5, half_17_07_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_14_07 half_16_07
    (by simpa only [half_17_07_φ3, show (2:ℝ)*4=8 by norm_num] using half_17_07_hx3)
  exact h.weaken (by norm_num [half_17_07_φ1, half_17_07_φ2, half_17_07_φ3, half_17_07_φ4, half_17_07_φ5, half_17_07_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_07_hx1 : SourcePowerBound (powerBoxCross 18 16 2 half_17_07_φ1) (12413576901/625000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 16) (u := 14) (t := 17)
    (D := 2) (ψ := (103118746413/2500000000000 : ℝ)) half_17_07_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_07_φ1, half_17_07_φ2, half_17_07_φ3, half_17_07_φ4, half_17_07_φ5, half_17_07_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_07_φ1, half_17_07_φ2, half_17_07_φ3, half_17_07_φ4, half_17_07_φ5, half_17_07_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_07_φ1, half_17_07_φ2, half_17_07_φ3, half_17_07_φ4, half_17_07_φ5, half_17_07_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_15_07 half_17_06
    (by simpa only [half_17_07_φ2, show (2:ℝ)*2=4 by norm_num] using half_17_07_hx2)
  exact h.weaken (by norm_num [half_17_07_φ1, half_17_07_φ2, half_17_07_φ3, half_17_07_φ4, half_17_07_φ5, half_17_07_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_07 : AdmissibleExponent 18 34 (211849448900577/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 15) (ψ := (426845757567/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_16_07
    (by simpa only [half_17_07_φ1] using half_17_07_hx1)
  exact admissibleExponent_mono h (by norm_num [half_17_07_φ1, half_17_07_φ2, half_17_07_φ3, half_17_07_φ4, half_17_07_φ5, half_17_07_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])


end Waring.SeedCompletionHigher18SimpleSeeds
