import Waring.SeedCompletionHigher18SimpleSeedsC15

noncomputable section
set_option maxHeartbeats 2000000
namespace Waring.SeedCompletionHigher18SimpleSeeds
open SmoothMoments FirstStageTransport SeedCompletionNaturalBox
open SeedCompletionSourceBounds SeedCompletionPaddedSource SeedCompletionGeneralTerminal
open PolicyCompletionMajorPowerRanges

def half_9_16_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (85959707591/2500000000000 : ℝ)

def half_9_16_φ2 : Fin 2 → ℝ := Fin.snoc half_9_16_φ1 (154172571651/5000000000000 : ℝ)

def half_9_16_φ3 : Fin 3 → ℝ := Fin.snoc half_9_16_φ2 (134445908241/10000000000000 : ℝ)

theorem half_9_16_hF2 : SourcePowerBound (paddedMoment 18 0 2 8 half_9_16_φ3) (69881876022743/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_16_φ3 (by norm_num [half_9_16_φ1, half_9_16_φ2, half_9_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_16_φ1, half_9_16_φ2, half_9_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_16_φ1, half_9_16_φ2, half_9_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_16_φ1, half_9_16_φ2, half_9_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_9_16_hF1 : SourcePowerBound (paddedMoment 18 0 1 8 half_9_16_φ3) (26627292007581/10000000000000 : ℝ) := by
  have h := padded_second_power (k := 18) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_16_φ3 (by norm_num [half_9_16_φ1, half_9_16_φ2, half_9_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_16_φ1, half_9_16_φ2, half_9_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_16_φ1, half_9_16_φ2, half_9_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_16_φ1, half_9_16_φ2, half_9_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_9_16_hx3 : SourcePowerBound (powerBoxCross 18 6 8 half_9_16_φ3) (38496518552519/5000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 18) (s := 6) (r := 1) (v := 2) (t := 10) (D := 8)
    (a := (3/10 : ℝ)) (b := (1/10 : ℝ)) (c := (3/5 : ℝ))
    (by norm_num) half_9_16_φ3 (by norm_num [half_9_16_φ1, half_9_16_φ2, half_9_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_16_φ1, half_9_16_φ2, half_9_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_9_16_hF1 half_9_16_hF2 half_10_15
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_9_16_φ1, half_9_16_φ2, half_9_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_9_16_hx2 : SourcePowerBound (powerBoxCross 18 7 4 half_9_16_φ2) (84269421796039/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 7) (u := 5) (t := 8)
    (D := 4) (ψ := (134445908241/10000000000000 : ℝ)) half_9_16_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_16_φ1, half_9_16_φ2, half_9_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_16_φ1, half_9_16_φ2, half_9_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_16_φ1, half_9_16_φ2, half_9_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_6 SeedCompletionEven18SecondSeeds.degree18_half_8
    (by simpa only [half_9_16_φ3, show (2:ℝ)*4=8 by norm_num] using half_9_16_hx3)
  exact h.weaken (by norm_num [half_9_16_φ1, half_9_16_φ2, half_9_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_9_16_hx1 : SourcePowerBound (powerBoxCross 18 8 2 half_9_16_φ1) (94174798046097/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 8) (u := 6) (t := 9)
    (D := 2) (ψ := (154172571651/5000000000000 : ℝ)) half_9_16_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_16_φ1, half_9_16_φ2, half_9_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_16_φ1, half_9_16_φ2, half_9_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_16_φ1, half_9_16_φ2, half_9_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_7 half_9_15
    (by simpa only [half_9_16_φ2, show (2:ℝ)*2=4 by norm_num] using half_9_16_hx2)
  exact h.weaken (by norm_num [half_9_16_φ1, half_9_16_φ2, half_9_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_9_16 : AdmissibleExponent 18 18 (99332380501557/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 7) (ψ := (85959707591/2500000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_8
    (by simpa only [half_9_16_φ1] using half_9_16_hx1)
  exact admissibleExponent_mono h (by norm_num [half_9_16_φ1, half_9_16_φ2, half_9_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_10_16_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (353748845887/10000000000000 : ℝ)

def half_10_16_φ2 : Fin 2 → ℝ := Fin.snoc half_10_16_φ1 (164628283291/5000000000000 : ℝ)

def half_10_16_φ3 : Fin 3 → ℝ := Fin.snoc half_10_16_φ2 (22993878099/1000000000000 : ℝ)

theorem half_10_16_hF2 : SourcePowerBound (paddedMoment 18 0 2 8 half_10_16_φ3) (63439846133591/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_10_16_φ3 (by norm_num [half_10_16_φ1, half_10_16_φ2, half_10_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_16_φ1, half_10_16_φ2, half_10_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_16_φ1, half_10_16_φ2, half_10_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_10_16_φ1, half_10_16_φ2, half_10_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_10_16_hx3 : SourcePowerBound (powerBoxCross 18 7 8 half_10_16_φ3) (86477914179237/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 7) (r := 2) (v := 9) (w := 10) (D := 8)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_10_16_φ3 (by norm_num [half_10_16_φ1, half_10_16_φ2, half_10_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_16_φ1, half_10_16_φ2, half_10_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_10_16_hF2 half_9_16 half_10_15
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_10_16_φ1, half_10_16_φ2, half_10_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_16_hx2 : SourcePowerBound (powerBoxCross 18 8 4 half_10_16_φ2) (47600987867523/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 8) (u := 6) (t := 9)
    (D := 4) (ψ := (22993878099/1000000000000 : ℝ)) half_10_16_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_16_φ1, half_10_16_φ2, half_10_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_16_φ1, half_10_16_φ2, half_10_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_16_φ1, half_10_16_φ2, half_10_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_7 half_9_16
    (by simpa only [half_10_16_φ3, show (2:ℝ)*4=8 by norm_num] using half_10_16_hx3)
  exact h.weaken (by norm_num [half_10_16_φ1, half_10_16_φ2, half_10_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_16_hx1 : SourcePowerBound (powerBoxCross 18 9 2 half_10_16_φ1) (106172257851299/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 9) (u := 7) (t := 10)
    (D := 2) (ψ := (164628283291/5000000000000 : ℝ)) half_10_16_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_16_φ1, half_10_16_φ2, half_10_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_16_φ1, half_10_16_φ2, half_10_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_16_φ1, half_10_16_φ2, half_10_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_8 half_10_15
    (by simpa only [half_10_16_φ2, show (2:ℝ)*2=4 by norm_num] using half_10_16_hx2)
  exact h.weaken (by norm_num [half_10_16_φ1, half_10_16_φ2, half_10_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_16 : AdmissibleExponent 18 20 (56092994115689/5000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 8) (ψ := (353748845887/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_9_16
    (by simpa only [half_10_16_φ1] using half_10_16_hx1)
  exact admissibleExponent_mono h (by norm_num [half_10_16_φ1, half_10_16_φ2, half_10_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_11_16_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (22796758423/625000000000 : ℝ)

def half_11_16_φ2 : Fin 2 → ℝ := Fin.snoc half_11_16_φ1 (346394857633/10000000000000 : ℝ)

def half_11_16_φ3 : Fin 3 → ℝ := Fin.snoc half_11_16_φ2 (73682123271/2500000000000 : ℝ)

theorem half_11_16_hF2 : SourcePowerBound (paddedMoment 18 0 2 8 half_11_16_φ3) (11740110848053/2000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_11_16_φ3 (by norm_num [half_11_16_φ1, half_11_16_φ2, half_11_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_16_φ1, half_11_16_φ2, half_11_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_16_φ1, half_11_16_φ2, half_11_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_11_16_φ1, half_11_16_φ2, half_11_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_11_16_hx3 : SourcePowerBound (powerBoxCross 18 8 8 half_11_16_φ3) (96288752054663/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 8) (r := 2) (v := 10) (w := 11) (D := 8)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_11_16_φ3 (by norm_num [half_11_16_φ1, half_11_16_φ2, half_11_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_16_φ1, half_11_16_φ2, half_11_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_11_16_hF2 half_10_16 half_11_15
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_11_16_φ1, half_11_16_φ2, half_11_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_16_hx2 : SourcePowerBound (powerBoxCross 18 9 4 half_11_16_φ2) (1662720381827/156250000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 9) (u := 7) (t := 10)
    (D := 4) (ψ := (73682123271/2500000000000 : ℝ)) half_11_16_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_16_φ1, half_11_16_φ2, half_11_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_16_φ1, half_11_16_φ2, half_11_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_16_φ1, half_11_16_φ2, half_11_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_8 half_10_16
    (by simpa only [half_11_16_φ3, show (2:ℝ)*4=8 by norm_num] using half_11_16_hx3)
  exact h.weaken (by norm_num [half_11_16_φ1, half_11_16_φ2, half_11_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_16_hx1 : SourcePowerBound (powerBoxCross 18 10 2 half_11_16_φ1) (11845877337071/1000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 10) (u := 8) (t := 11)
    (D := 2) (ψ := (346394857633/10000000000000 : ℝ)) half_11_16_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_16_φ1, half_11_16_φ2, half_11_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_16_φ1, half_11_16_φ2, half_11_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_16_φ1, half_11_16_φ2, half_11_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_16 half_11_15
    (by simpa only [half_11_16_φ2, show (2:ℝ)*2=4 by norm_num] using half_11_16_hx2)
  exact h.weaken (by norm_num [half_11_16_φ1, half_11_16_φ2, half_11_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_16 : AdmissibleExponent 18 22 (62694493965651/5000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 9) (ψ := (22796758423/625000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_10_16
    (by simpa only [half_11_16_φ1] using half_11_16_hx1)
  exact admissibleExponent_mono h (by norm_num [half_11_16_φ1, half_11_16_φ2, half_11_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_12_16_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (187470979743/5000000000000 : ℝ)

def half_12_16_φ2 : Fin 2 → ℝ := Fin.snoc half_12_16_φ1 (180293432477/5000000000000 : ℝ)

def half_12_16_φ3 : Fin 3 → ℝ := Fin.snoc half_12_16_φ2 (329430070119/10000000000000 : ℝ)

def half_12_16_φ4 : Fin 4 → ℝ := Fin.snoc half_12_16_φ3 (21290734933/1000000000000 : ℝ)

theorem half_12_16_hF2 : SourcePowerBound (paddedMoment 18 0 2 16 half_12_16_φ4) (74828821561661/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_12_16_φ4 (by norm_num [half_12_16_φ1, half_12_16_φ2, half_12_16_φ3, half_12_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_16_φ1, half_12_16_φ2, half_12_16_φ3, half_12_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_16_φ1, half_12_16_φ2, half_12_16_φ3, half_12_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_12_16_φ1, half_12_16_φ2, half_12_16_φ3, half_12_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_12_16_hF1 : SourcePowerBound (paddedMoment 18 0 1 16 half_12_16_φ4) (28276273853887/10000000000000 : ℝ) := by
  have h := padded_second_power (k := 18) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_12_16_φ4 (by norm_num [half_12_16_φ1, half_12_16_φ2, half_12_16_φ3, half_12_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_16_φ1, half_12_16_φ2, half_12_16_φ3, half_12_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_16_φ1, half_12_16_φ2, half_12_16_φ3, half_12_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_12_16_φ1, half_12_16_φ2, half_12_16_φ3, half_12_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_12_16_hx4 : SourcePowerBound (powerBoxCross 18 8 16 half_12_16_φ4) (48915355011603/5000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 18) (s := 8) (r := 1) (v := 2) (t := 11) (D := 16)
    (a := (1/22 : ℝ)) (b := (5/22 : ℝ)) (c := (8/11 : ℝ))
    (by norm_num) half_12_16_φ4 (by norm_num [half_12_16_φ1, half_12_16_φ2, half_12_16_φ3, half_12_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_16_φ1, half_12_16_φ2, half_12_16_φ3, half_12_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_12_16_hF1 half_12_16_hF2 half_11_16
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_12_16_φ1, half_12_16_φ2, half_12_16_φ3, half_12_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_16_hx3 : SourcePowerBound (powerBoxCross 18 9 8 half_12_16_φ3) (106579330342921/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 9) (u := 7) (t := 10)
    (D := 8) (ψ := (21290734933/1000000000000 : ℝ)) half_12_16_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_16_φ1, half_12_16_φ2, half_12_16_φ3, half_12_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_16_φ1, half_12_16_φ2, half_12_16_φ3, half_12_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_16_φ1, half_12_16_φ2, half_12_16_φ3, half_12_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_8 half_10_16
    (by simpa only [half_12_16_φ4, show (2:ℝ)*8=16 by norm_num] using half_12_16_hx4)
  exact h.weaken (by norm_num [half_12_16_φ1, half_12_16_φ2, half_12_16_φ3, half_12_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_16_hx2 : SourcePowerBound (powerBoxCross 18 10 4 half_12_16_φ2) (58960479490421/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 10) (u := 8) (t := 11)
    (D := 4) (ψ := (329430070119/10000000000000 : ℝ)) half_12_16_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_16_φ1, half_12_16_φ2, half_12_16_φ3, half_12_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_16_φ1, half_12_16_φ2, half_12_16_φ3, half_12_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_16_φ1, half_12_16_φ2, half_12_16_φ3, half_12_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_16 half_11_16
    (by simpa only [half_12_16_φ3, show (2:ℝ)*4=8 by norm_num] using half_12_16_hx3)
  exact h.weaken (by norm_num [half_12_16_φ1, half_12_16_φ2, half_12_16_φ3, half_12_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_16_hx1 : SourcePowerBound (powerBoxCross 18 11 2 half_12_16_φ1) (131062570607503/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 11) (u := 9) (t := 12)
    (D := 2) (ψ := (180293432477/5000000000000 : ℝ)) half_12_16_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_16_φ1, half_12_16_φ2, half_12_16_φ3, half_12_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_16_φ1, half_12_16_φ2, half_12_16_φ3, half_12_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_16_φ1, half_12_16_φ2, half_12_16_φ3, half_12_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_16 half_12_15
    (by simpa only [half_12_16_φ2, show (2:ℝ)*2=4 by norm_num] using half_12_16_hx2)
  exact h.weaken (by norm_num [half_12_16_φ1, half_12_16_φ2, half_12_16_φ3, half_12_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_16 : AdmissibleExponent 18 24 (138936351756709/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 10) (ψ := (187470979743/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_11_16
    (by simpa only [half_12_16_φ1] using half_12_16_hx1)
  exact admissibleExponent_mono h (by norm_num [half_12_16_φ1, half_12_16_φ2, half_12_16_φ3, half_12_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_13_16_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (76920886659/2000000000000 : ℝ)

def half_13_16_φ2 : Fin 2 → ℝ := Fin.snoc half_13_16_φ1 (371968407153/10000000000000 : ℝ)

def half_13_16_φ3 : Fin 3 → ℝ := Fin.snoc half_13_16_φ2 (349893157667/10000000000000 : ℝ)

def half_13_16_φ4 : Fin 4 → ℝ := Fin.snoc half_13_16_φ3 (141656637051/5000000000000 : ℝ)

theorem half_13_16_hF2 : SourcePowerBound (paddedMoment 18 0 2 16 half_13_16_φ4) (69121257116933/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_13_16_φ4 (by norm_num [half_13_16_φ1, half_13_16_φ2, half_13_16_φ3, half_13_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_16_φ1, half_13_16_φ2, half_13_16_φ3, half_13_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_16_φ1, half_13_16_φ2, half_13_16_φ3, half_13_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_13_16_φ1, half_13_16_φ2, half_13_16_φ3, half_13_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_13_16_hx4 : SourcePowerBound (powerBoxCross 18 9 16 half_13_16_φ4) (26750190864899/2500000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 9) (r := 2) (v := 12) (w := 12) (D := 16)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_13_16_φ4 (by norm_num [half_13_16_φ1, half_13_16_φ2, half_13_16_φ3, half_13_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_16_φ1, half_13_16_φ2, half_13_16_φ3, half_13_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_13_16_hF2 half_12_16 half_12_16
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_13_16_φ1, half_13_16_φ2, half_13_16_φ3, half_13_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_16_hx3 : SourcePowerBound (powerBoxCross 18 10 8 half_13_16_φ3) (117261144957139/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 10) (u := 8) (t := 11)
    (D := 8) (ψ := (141656637051/5000000000000 : ℝ)) half_13_16_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_16_φ1, half_13_16_φ2, half_13_16_φ3, half_13_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_16_φ1, half_13_16_φ2, half_13_16_φ3, half_13_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_16_φ1, half_13_16_φ2, half_13_16_φ3, half_13_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_16 half_11_16
    (by simpa only [half_13_16_φ4, show (2:ℝ)*8=16 by norm_num] using half_13_16_hx4)
  exact h.weaken (by norm_num [half_13_16_φ1, half_13_16_φ2, half_13_16_φ3, half_13_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_16_hx2 : SourcePowerBound (powerBoxCross 18 11 4 half_13_16_φ2) (2594721813929/200000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 11) (u := 9) (t := 12)
    (D := 4) (ψ := (349893157667/10000000000000 : ℝ)) half_13_16_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_16_φ1, half_13_16_φ2, half_13_16_φ3, half_13_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_16_φ1, half_13_16_φ2, half_13_16_φ3, half_13_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_16_φ1, half_13_16_φ2, half_13_16_φ3, half_13_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_16 half_12_16
    (by simpa only [half_13_16_φ3, show (2:ℝ)*4=8 by norm_num] using half_13_16_hx3)
  exact h.weaken (by norm_num [half_13_16_φ1, half_13_16_φ2, half_13_16_φ3, half_13_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_16_hx1 : SourcePowerBound (powerBoxCross 18 12 2 half_13_16_φ1) (143977402506879/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 12) (u := 10) (t := 13)
    (D := 2) (ψ := (371968407153/10000000000000 : ℝ)) half_13_16_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_16_φ1, half_13_16_φ2, half_13_16_φ3, half_13_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_16_φ1, half_13_16_φ2, half_13_16_φ3, half_13_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_16_φ1, half_13_16_φ2, half_13_16_φ3, half_13_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_16 half_13_15
    (by simpa only [half_13_16_φ2, show (2:ℝ)*2=4 by norm_num] using half_13_16_hx2)
  exact h.weaken (by norm_num [half_13_16_φ1, half_13_16_φ2, half_13_16_φ3, half_13_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_16 : AdmissibleExponent 18 26 (19102913059083/1250000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 11) (ψ := (76920886659/2000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_12_16
    (by simpa only [half_13_16_φ1] using half_13_16_hx1)
  exact admissibleExponent_mono h (by norm_num [half_13_16_φ1, half_13_16_φ2, half_13_16_φ3, half_13_16_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_14_16_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (394360769343/10000000000000 : ℝ)

def half_14_16_φ2 : Fin 2 → ℝ := Fin.snoc half_14_16_φ1 (382996733523/10000000000000 : ℝ)

def half_14_16_φ3 : Fin 3 → ℝ := Fin.snoc half_14_16_φ2 (73452162439/2000000000000 : ℝ)

def half_14_16_φ4 : Fin 4 → ℝ := Fin.snoc half_14_16_φ3 (332115752749/10000000000000 : ℝ)

def half_14_16_φ5 : Fin 5 → ℝ := Fin.snoc half_14_16_φ4 (102790378699/5000000000000 : ℝ)

theorem half_14_16_hF2 : SourcePowerBound (paddedMoment 18 0 2 32 half_14_16_φ5) (10525242989299/1250000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_14_16_φ5 (by norm_num [half_14_16_φ1, half_14_16_φ2, half_14_16_φ3, half_14_16_φ4, half_14_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_16_φ1, half_14_16_φ2, half_14_16_φ3, half_14_16_φ4, half_14_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_16_φ1, half_14_16_φ2, half_14_16_φ3, half_14_16_φ4, half_14_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_14_16_φ1, half_14_16_φ2, half_14_16_φ3, half_14_16_φ4, half_14_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_14_16_hx5 : SourcePowerBound (powerBoxCross 18 9 32 half_14_16_φ5) (107722648472083/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 9) (r := 2) (v := 12) (w := 12) (D := 32)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_14_16_φ5 (by norm_num [half_14_16_φ1, half_14_16_φ2, half_14_16_φ3, half_14_16_φ4, half_14_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_16_φ1, half_14_16_φ2, half_14_16_φ3, half_14_16_φ4, half_14_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_14_16_hF2 half_12_16 half_12_16
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_14_16_φ1, half_14_16_φ2, half_14_16_φ3, half_14_16_φ4, half_14_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_16_hx4 : SourcePowerBound (powerBoxCross 18 10 16 half_14_16_φ4) (931941644423/80000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 10) (u := 8) (t := 11)
    (D := 16) (ψ := (102790378699/5000000000000 : ℝ)) half_14_16_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_16_φ1, half_14_16_φ2, half_14_16_φ3, half_14_16_φ4, half_14_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_16_φ1, half_14_16_φ2, half_14_16_φ3, half_14_16_φ4, half_14_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_16_φ1, half_14_16_φ2, half_14_16_φ3, half_14_16_φ4, half_14_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_16 half_11_16
    (by simpa only [half_14_16_φ5, show (2:ℝ)*16=32 by norm_num] using half_14_16_hx5)
  exact h.weaken (by norm_num [half_14_16_φ1, half_14_16_φ2, half_14_16_φ3, half_14_16_φ4, half_14_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_16_hx3 : SourcePowerBound (powerBoxCross 18 11 8 half_14_16_φ3) (25637783597093/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 11) (u := 9) (t := 12)
    (D := 8) (ψ := (332115752749/10000000000000 : ℝ)) half_14_16_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_16_φ1, half_14_16_φ2, half_14_16_φ3, half_14_16_φ4, half_14_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_16_φ1, half_14_16_φ2, half_14_16_φ3, half_14_16_φ4, half_14_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_16_φ1, half_14_16_φ2, half_14_16_φ3, half_14_16_φ4, half_14_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_16 half_12_16
    (by simpa only [half_14_16_φ4, show (2:ℝ)*8=16 by norm_num] using half_14_16_hx4)
  exact h.weaken (by norm_num [half_14_16_φ1, half_14_16_φ2, half_14_16_φ3, half_14_16_φ4, half_14_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_16_hx2 : SourcePowerBound (powerBoxCross 18 12 4 half_14_16_φ2) (141814893865521/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 12) (u := 10) (t := 13)
    (D := 4) (ψ := (73452162439/2000000000000 : ℝ)) half_14_16_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_16_φ1, half_14_16_φ2, half_14_16_φ3, half_14_16_φ4, half_14_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_16_φ1, half_14_16_φ2, half_14_16_φ3, half_14_16_φ4, half_14_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_16_φ1, half_14_16_φ2, half_14_16_φ3, half_14_16_φ4, half_14_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_16 half_13_16
    (by simpa only [half_14_16_φ3, show (2:ℝ)*4=8 by norm_num] using half_14_16_hx3)
  exact h.weaken (by norm_num [half_14_16_φ1, half_14_16_φ2, half_14_16_φ3, half_14_16_φ4, half_14_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_16_hx1 : SourcePowerBound (powerBoxCross 18 13 2 half_14_16_φ1) (31438182729897/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 13) (u := 11) (t := 14)
    (D := 2) (ψ := (382996733523/10000000000000 : ℝ)) half_14_16_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_16_φ1, half_14_16_φ2, half_14_16_φ3, half_14_16_φ4, half_14_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_16_φ1, half_14_16_φ2, half_14_16_φ3, half_14_16_φ4, half_14_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_16_φ1, half_14_16_φ2, half_14_16_φ3, half_14_16_φ4, half_14_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_16 half_14_15
    (by simpa only [half_14_16_φ2, show (2:ℝ)*2=4 by norm_num] using half_14_16_hx2)
  exact h.weaken (by norm_num [half_14_16_φ1, half_14_16_φ2, half_14_16_φ3, half_14_16_φ4, half_14_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_16 : AdmissibleExponent 18 28 (8352496644153/500000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 12) (ψ := (394360769343/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_13_16
    (by simpa only [half_14_16_φ1] using half_14_16_hx1)
  exact admissibleExponent_mono h (by norm_num [half_14_16_φ1, half_14_16_φ2, half_14_16_φ3, half_14_16_φ4, half_14_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_15_16_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (403637935263/10000000000000 : ℝ)

def half_15_16_φ2 : Fin 2 → ℝ := Fin.snoc half_15_16_φ1 (392987568781/10000000000000 : ℝ)

def half_15_16_φ3 : Fin 3 → ℝ := Fin.snoc half_15_16_φ2 (7589150561/200000000000 : ℝ)

def half_15_16_φ4 : Fin 4 → ℝ := Fin.snoc half_15_16_φ3 (71045019369/2000000000000 : ℝ)

def half_15_16_φ5 : Fin 5 → ℝ := Fin.snoc half_15_16_φ4 (17768178941/625000000000 : ℝ)

theorem half_15_16_hF2 : SourcePowerBound (paddedMoment 18 0 2 32 half_15_16_φ5) (15480890281651/2000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_15_16_φ5 (by norm_num [half_15_16_φ1, half_15_16_φ2, half_15_16_φ3, half_15_16_φ4, half_15_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_16_φ1, half_15_16_φ2, half_15_16_φ3, half_15_16_φ4, half_15_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_16_φ1, half_15_16_φ2, half_15_16_φ3, half_15_16_φ4, half_15_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_15_16_φ1, half_15_16_φ2, half_15_16_φ3, half_15_16_φ4, half_15_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_15_16_hx5 : SourcePowerBound (powerBoxCross 18 10 32 half_15_16_φ5) (116069564187583/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 10) (r := 2) (v := 13) (w := 14) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_15_16_φ5 (by norm_num [half_15_16_φ1, half_15_16_φ2, half_15_16_φ3, half_15_16_φ4, half_15_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_16_φ1, half_15_16_φ2, half_15_16_φ3, half_15_16_φ4, half_15_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_15_16_hF2 half_13_16 half_14_16
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_15_16_φ1, half_15_16_φ2, half_15_16_φ3, half_15_16_φ4, half_15_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_16_hx4 : SourcePowerBound (powerBoxCross 18 11 16 half_15_16_φ4) (12654988383269/1000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 11) (u := 9) (t := 12)
    (D := 16) (ψ := (17768178941/625000000000 : ℝ)) half_15_16_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_16_φ1, half_15_16_φ2, half_15_16_φ3, half_15_16_φ4, half_15_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_16_φ1, half_15_16_φ2, half_15_16_φ3, half_15_16_φ4, half_15_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_16_φ1, half_15_16_φ2, half_15_16_φ3, half_15_16_φ4, half_15_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_16 half_12_16
    (by simpa only [half_15_16_φ5, show (2:ℝ)*16=32 by norm_num] using half_15_16_hx5)
  exact h.weaken (by norm_num [half_15_16_φ1, half_15_16_φ2, half_15_16_φ3, half_15_16_φ4, half_15_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_16_hx3 : SourcePowerBound (powerBoxCross 18 12 8 half_15_16_φ3) (139433107131809/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 12) (u := 10) (t := 13)
    (D := 8) (ψ := (71045019369/2000000000000 : ℝ)) half_15_16_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_16_φ1, half_15_16_φ2, half_15_16_φ3, half_15_16_φ4, half_15_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_16_φ1, half_15_16_φ2, half_15_16_φ3, half_15_16_φ4, half_15_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_16_φ1, half_15_16_φ2, half_15_16_φ3, half_15_16_φ4, half_15_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_16 half_13_16
    (by simpa only [half_15_16_φ4, show (2:ℝ)*8=16 by norm_num] using half_15_16_hx4)
  exact h.weaken (by norm_num [half_15_16_φ1, half_15_16_φ2, half_15_16_φ3, half_15_16_φ4, half_15_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_16_hx2 : SourcePowerBound (powerBoxCross 18 13 4 half_15_16_φ2) (77090076473231/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 13) (u := 11) (t := 14)
    (D := 4) (ψ := (7589150561/200000000000 : ℝ)) half_15_16_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_16_φ1, half_15_16_φ2, half_15_16_φ3, half_15_16_φ4, half_15_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_16_φ1, half_15_16_φ2, half_15_16_φ3, half_15_16_φ4, half_15_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_16_φ1, half_15_16_φ2, half_15_16_φ3, half_15_16_φ4, half_15_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_16 half_14_16
    (by simpa only [half_15_16_φ3, show (2:ℝ)*4=8 by norm_num] using half_15_16_hx3)
  exact h.weaken (by norm_num [half_15_16_φ1, half_15_16_φ2, half_15_16_φ3, half_15_16_φ4, half_15_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_16_hx1 : SourcePowerBound (powerBoxCross 18 14 2 half_15_16_φ1) (42677700454717/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 14) (u := 12) (t := 15)
    (D := 2) (ψ := (392987568781/10000000000000 : ℝ)) half_15_16_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_16_φ1, half_15_16_φ2, half_15_16_φ3, half_15_16_φ4, half_15_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_16_φ1, half_15_16_φ2, half_15_16_φ3, half_15_16_φ4, half_15_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_16_φ1, half_15_16_φ2, half_15_16_φ3, half_15_16_φ4, half_15_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_13_16 half_15_15
    (by simpa only [half_15_16_φ2, show (2:ℝ)*2=4 by norm_num] using half_15_16_hx2)
  exact h.weaken (by norm_num [half_15_16_φ1, half_15_16_φ2, half_15_16_φ3, half_15_16_φ4, half_15_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_16 : AdmissibleExponent 18 30 (181609026070969/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 13) (ψ := (403637935263/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_14_16
    (by simpa only [half_15_16_φ1] using half_15_16_hx1)
  exact admissibleExponent_mono h (by norm_num [half_15_16_φ1, half_15_16_φ2, half_15_16_φ3, half_15_16_φ4, half_15_16_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_16_16_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (51611183671/1250000000000 : ℝ)

def half_16_16_φ2 : Fin 2 → ℝ := Fin.snoc half_16_16_φ1 (80538896819/2000000000000 : ℝ)

def half_16_16_φ3 : Fin 3 → ℝ := Fin.snoc half_16_16_φ2 (391097329793/10000000000000 : ℝ)

def half_16_16_φ4 : Fin 4 → ℝ := Fin.snoc half_16_16_φ3 (187051243159/5000000000000 : ℝ)

def half_16_16_φ5 : Fin 5 → ℝ := Fin.snoc half_16_16_φ4 (336301473579/10000000000000 : ℝ)

def half_16_16_φ6 : Fin 6 → ℝ := Fin.snoc half_16_16_φ5 (104112454543/5000000000000 : ℝ)

theorem half_16_16_hF2 : SourcePowerBound (paddedMoment 18 0 2 64 half_16_16_φ6) (91609182235811/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 6) (r := 0) (D := 64)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_16_16_φ6 (by norm_num [half_16_16_φ1, half_16_16_φ2, half_16_16_φ3, half_16_16_φ4, half_16_16_φ5, half_16_16_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_16_φ1, half_16_16_φ2, half_16_16_φ3, half_16_16_φ4, half_16_16_φ5, half_16_16_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_16_φ1, half_16_16_φ2, half_16_16_φ3, half_16_16_φ4, half_16_16_φ5, half_16_16_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_16_16_φ1, half_16_16_φ2, half_16_16_φ3, half_16_16_φ4, half_16_16_φ5, half_16_16_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_16_16_hx6 : SourcePowerBound (powerBoxCross 18 10 64 half_16_16_φ6) (115960762034147/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 10) (r := 2) (v := 13) (w := 14) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_16_16_φ6 (by norm_num [half_16_16_φ1, half_16_16_φ2, half_16_16_φ3, half_16_16_φ4, half_16_16_φ5, half_16_16_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_16_φ1, half_16_16_φ2, half_16_16_φ3, half_16_16_φ4, half_16_16_φ5, half_16_16_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_16_16_hF2 half_13_16 half_14_16
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_16_16_φ1, half_16_16_φ2, half_16_16_φ3, half_16_16_φ4, half_16_16_φ5, half_16_16_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_16_hx5 : SourcePowerBound (powerBoxCross 18 11 32 half_16_16_φ5) (7800864217527/625000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 5) (s := 11) (u := 9) (t := 12)
    (D := 32) (ψ := (104112454543/5000000000000 : ℝ)) half_16_16_φ5
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_16_φ1, half_16_16_φ2, half_16_16_φ3, half_16_16_φ4, half_16_16_φ5, half_16_16_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_16_φ1, half_16_16_φ2, half_16_16_φ3, half_16_16_φ4, half_16_16_φ5, half_16_16_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_16_φ1, half_16_16_φ2, half_16_16_φ3, half_16_16_φ4, half_16_16_φ5, half_16_16_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_16 half_12_16
    (by simpa only [half_16_16_φ6, show (2:ℝ)*32=64 by norm_num] using half_16_16_hx6)
  exact h.weaken (by norm_num [half_16_16_φ1, half_16_16_φ2, half_16_16_φ3, half_16_16_φ4, half_16_16_φ5, half_16_16_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_16_hx4 : SourcePowerBound (powerBoxCross 18 12 16 half_16_16_φ4) (34208509860399/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 12) (u := 10) (t := 13)
    (D := 16) (ψ := (336301473579/10000000000000 : ℝ)) half_16_16_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_16_φ1, half_16_16_φ2, half_16_16_φ3, half_16_16_φ4, half_16_16_φ5, half_16_16_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_16_φ1, half_16_16_φ2, half_16_16_φ3, half_16_16_φ4, half_16_16_φ5, half_16_16_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_16_φ1, half_16_16_φ2, half_16_16_φ3, half_16_16_φ4, half_16_16_φ5, half_16_16_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_16 half_13_16
    (by simpa only [half_16_16_φ5, show (2:ℝ)*16=32 by norm_num] using half_16_16_hx5)
  exact h.weaken (by norm_num [half_16_16_φ1, half_16_16_φ2, half_16_16_φ3, half_16_16_φ4, half_16_16_φ5, half_16_16_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_16_hx3 : SourcePowerBound (powerBoxCross 18 13 8 half_16_16_φ3) (9431785779897/625000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 13) (u := 11) (t := 14)
    (D := 8) (ψ := (187051243159/5000000000000 : ℝ)) half_16_16_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_16_φ1, half_16_16_φ2, half_16_16_φ3, half_16_16_φ4, half_16_16_φ5, half_16_16_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_16_φ1, half_16_16_φ2, half_16_16_φ3, half_16_16_φ4, half_16_16_φ5, half_16_16_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_16_φ1, half_16_16_φ2, half_16_16_φ3, half_16_16_φ4, half_16_16_φ5, half_16_16_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_16 half_14_16
    (by simpa only [half_16_16_φ4, show (2:ℝ)*8=16 by norm_num] using half_16_16_hx4)
  exact h.weaken (by norm_num [half_16_16_φ1, half_16_16_φ2, half_16_16_φ3, half_16_16_φ4, half_16_16_φ5, half_16_16_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_16_hx2 : SourcePowerBound (powerBoxCross 18 14 4 half_16_16_φ2) (83404590959631/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 14) (u := 12) (t := 15)
    (D := 4) (ψ := (391097329793/10000000000000 : ℝ)) half_16_16_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_16_φ1, half_16_16_φ2, half_16_16_φ3, half_16_16_φ4, half_16_16_φ5, half_16_16_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_16_φ1, half_16_16_φ2, half_16_16_φ3, half_16_16_φ4, half_16_16_φ5, half_16_16_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_16_φ1, half_16_16_φ2, half_16_16_φ3, half_16_16_φ4, half_16_16_φ5, half_16_16_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_13_16 half_15_16
    (by simpa only [half_16_16_φ3, show (2:ℝ)*4=8 by norm_num] using half_16_16_hx3)
  exact h.weaken (by norm_num [half_16_16_φ1, half_16_16_φ2, half_16_16_φ3, half_16_16_φ4, half_16_16_φ5, half_16_16_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_16_hx1 : SourcePowerBound (powerBoxCross 18 15 2 half_16_16_φ1) (184523470099659/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 15) (u := 13) (t := 16)
    (D := 2) (ψ := (80538896819/2000000000000 : ℝ)) half_16_16_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_16_φ1, half_16_16_φ2, half_16_16_φ3, half_16_16_φ4, half_16_16_φ5, half_16_16_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_16_φ1, half_16_16_φ2, half_16_16_φ3, half_16_16_φ4, half_16_16_φ5, half_16_16_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_16_φ1, half_16_16_φ2, half_16_16_φ3, half_16_16_φ4, half_16_16_φ5, half_16_16_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_14_16 half_16_15
    (by simpa only [half_16_16_φ2, show (2:ℝ)*2=4 by norm_num] using half_16_16_hx2)
  exact h.weaken (by norm_num [half_16_16_φ1, half_16_16_φ2, half_16_16_φ3, half_16_16_φ4, half_16_16_φ5, half_16_16_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_16 : AdmissibleExponent 18 32 (196497264711331/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 14) (ψ := (51611183671/1250000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_15_16
    (by simpa only [half_16_16_φ1] using half_16_16_hx1)
  exact admissibleExponent_mono h (by norm_num [half_16_16_φ1, half_16_16_φ2, half_16_16_φ3, half_16_16_φ4, half_16_16_φ5, half_16_16_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_17_16_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (421827984157/10000000000000 : ℝ)

def half_17_16_φ2 : Fin 2 → ℝ := Fin.snoc half_17_16_φ1 (412011008791/10000000000000 : ℝ)

def half_17_16_φ3 : Fin 3 → ℝ := Fin.snoc half_17_16_φ2 (100280956243/2500000000000 : ℝ)

def half_17_16_φ4 : Fin 4 → ℝ := Fin.snoc half_17_16_φ3 (387122505031/10000000000000 : ℝ)

def half_17_16_φ5 : Fin 5 → ℝ := Fin.snoc half_17_16_φ4 (36133989283/1000000000000 : ℝ)

def half_17_16_φ6 : Fin 6 → ℝ := Fin.snoc half_17_16_φ5 (72296081301/2500000000000 : ℝ)

theorem half_17_16_hF2 : SourcePowerBound (paddedMoment 18 0 2 64 half_17_16_φ6) (16819382681953/2000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 6) (r := 0) (D := 64)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_17_16_φ6 (by norm_num [half_17_16_φ1, half_17_16_φ2, half_17_16_φ3, half_17_16_φ4, half_17_16_φ5, half_17_16_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_16_φ1, half_17_16_φ2, half_17_16_φ3, half_17_16_φ4, half_17_16_φ5, half_17_16_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_16_φ1, half_17_16_φ2, half_17_16_φ3, half_17_16_φ4, half_17_16_φ5, half_17_16_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_17_16_φ1, half_17_16_φ2, half_17_16_φ3, half_17_16_φ4, half_17_16_φ5, half_17_16_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_17_16_hx6 : SourcePowerBound (powerBoxCross 18 11 64 half_17_16_φ6) (30865980639381/2500000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 11) (r := 2) (v := 14) (w := 15) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_17_16_φ6 (by norm_num [half_17_16_φ1, half_17_16_φ2, half_17_16_φ3, half_17_16_φ4, half_17_16_φ5, half_17_16_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_16_φ1, half_17_16_φ2, half_17_16_φ3, half_17_16_φ4, half_17_16_φ5, half_17_16_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_17_16_hF2 half_14_16 half_15_16
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_17_16_φ1, half_17_16_φ2, half_17_16_φ3, half_17_16_φ4, half_17_16_φ5, half_17_16_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_16_hx5 : SourcePowerBound (powerBoxCross 18 12 32 half_17_16_φ5) (26833050962619/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 5) (s := 12) (u := 10) (t := 13)
    (D := 32) (ψ := (72296081301/2500000000000 : ℝ)) half_17_16_φ5
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_16_φ1, half_17_16_φ2, half_17_16_φ3, half_17_16_φ4, half_17_16_φ5, half_17_16_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_16_φ1, half_17_16_φ2, half_17_16_φ3, half_17_16_φ4, half_17_16_φ5, half_17_16_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_16_φ1, half_17_16_φ2, half_17_16_φ3, half_17_16_φ4, half_17_16_φ5, half_17_16_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_16 half_13_16
    (by simpa only [half_17_16_φ6, show (2:ℝ)*32=64 by norm_num] using half_17_16_hx6)
  exact h.weaken (by norm_num [half_17_16_φ1, half_17_16_φ2, half_17_16_φ3, half_17_16_φ4, half_17_16_φ5, half_17_16_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_16_hx4 : SourcePowerBound (powerBoxCross 18 13 16 half_17_16_φ4) (147426815154061/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 13) (u := 11) (t := 14)
    (D := 16) (ψ := (36133989283/1000000000000 : ℝ)) half_17_16_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_16_φ1, half_17_16_φ2, half_17_16_φ3, half_17_16_φ4, half_17_16_φ5, half_17_16_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_16_φ1, half_17_16_φ2, half_17_16_φ3, half_17_16_φ4, half_17_16_φ5, half_17_16_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_16_φ1, half_17_16_φ2, half_17_16_φ3, half_17_16_φ4, half_17_16_φ5, half_17_16_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_16 half_14_16
    (by simpa only [half_17_16_φ5, show (2:ℝ)*16=32 by norm_num] using half_17_16_hx5)
  exact h.weaken (by norm_num [half_17_16_φ1, half_17_16_φ2, half_17_16_φ3, half_17_16_φ4, half_17_16_φ5, half_17_16_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_16_hx3 : SourcePowerBound (powerBoxCross 18 14 8 half_17_16_φ3) (162645748243267/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 14) (u := 12) (t := 15)
    (D := 8) (ψ := (387122505031/10000000000000 : ℝ)) half_17_16_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_16_φ1, half_17_16_φ2, half_17_16_φ3, half_17_16_φ4, half_17_16_φ5, half_17_16_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_16_φ1, half_17_16_φ2, half_17_16_φ3, half_17_16_φ4, half_17_16_φ5, half_17_16_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_16_φ1, half_17_16_φ2, half_17_16_φ3, half_17_16_φ4, half_17_16_φ5, half_17_16_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_13_16 half_15_16
    (by simpa only [half_17_16_φ4, show (2:ℝ)*8=16 by norm_num] using half_17_16_hx4)
  exact h.weaken (by norm_num [half_17_16_φ1, half_17_16_φ2, half_17_16_φ3, half_17_16_φ4, half_17_16_φ5, half_17_16_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_16_hx2 : SourcePowerBound (powerBoxCross 18 15 4 half_17_16_φ2) (179706692608167/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 15) (u := 13) (t := 16)
    (D := 4) (ψ := (100280956243/2500000000000 : ℝ)) half_17_16_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_16_φ1, half_17_16_φ2, half_17_16_φ3, half_17_16_φ4, half_17_16_φ5, half_17_16_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_16_φ1, half_17_16_φ2, half_17_16_φ3, half_17_16_φ4, half_17_16_φ5, half_17_16_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_16_φ1, half_17_16_φ2, half_17_16_φ3, half_17_16_φ4, half_17_16_φ5, half_17_16_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_14_16 half_16_16
    (by simpa only [half_17_16_φ3, show (2:ℝ)*4=8 by norm_num] using half_17_16_hx3)
  exact h.weaken (by norm_num [half_17_16_φ1, half_17_16_φ2, half_17_16_φ3, half_17_16_φ4, half_17_16_φ5, half_17_16_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_16_hx1 : SourcePowerBound (powerBoxCross 18 16 2 half_17_16_φ1) (198630288188939/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 16) (u := 14) (t := 17)
    (D := 2) (ψ := (412011008791/10000000000000 : ℝ)) half_17_16_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_16_φ1, half_17_16_φ2, half_17_16_φ3, half_17_16_φ4, half_17_16_φ5, half_17_16_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_16_φ1, half_17_16_φ2, half_17_16_φ3, half_17_16_φ4, half_17_16_φ5, half_17_16_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_16_φ1, half_17_16_φ2, half_17_16_φ3, half_17_16_φ4, half_17_16_φ5, half_17_16_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_15_16 half_17_15
    (by simpa only [half_17_16_φ2, show (2:ℝ)*2=4 by norm_num] using half_17_16_hx2)
  exact h.weaken (by norm_num [half_17_16_φ1, half_17_16_φ2, half_17_16_φ3, half_17_16_φ4, half_17_16_φ5, half_17_16_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_16 : AdmissibleExponent 18 34 (105853477848903/5000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 15) (ψ := (421827984157/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_16_16
    (by simpa only [half_17_16_φ1] using half_17_16_hx1)
  exact admissibleExponent_mono h (by norm_num [half_17_16_φ1, half_17_16_φ2, half_17_16_φ3, half_17_16_φ4, half_17_16_φ5, half_17_16_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])


end Waring.SeedCompletionHigher18SimpleSeeds
