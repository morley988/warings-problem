import Waring.SeedCompletionHigher18SimpleSeedsC12

noncomputable section
set_option maxHeartbeats 2000000
namespace Waring.SeedCompletionHigher18SimpleSeeds
open SmoothMoments FirstStageTransport SeedCompletionNaturalBox
open SeedCompletionSourceBounds SeedCompletionPaddedSource SeedCompletionGeneralTerminal
open PolicyCompletionMajorPowerRanges

def half_9_13_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (343838832569/10000000000000 : ℝ)

def half_9_13_φ2 : Fin 2 → ℝ := Fin.snoc half_9_13_φ1 (7708628651/250000000000 : ℝ)

def half_9_13_φ3 : Fin 3 → ℝ := Fin.snoc half_9_13_φ2 (33611481383/2500000000000 : ℝ)

theorem half_9_13_hF2 : SourcePowerBound (paddedMoment 18 0 2 8 half_9_13_φ3) (69881874888809/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_13_φ3 (by norm_num [half_9_13_φ1, half_9_13_φ2, half_9_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_13_φ1, half_9_13_φ2, half_9_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_13_φ1, half_9_13_φ2, half_9_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_13_φ1, half_9_13_φ2, half_9_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_9_13_hF1 : SourcePowerBound (paddedMoment 18 0 1 8 half_9_13_φ3) (26627291629603/10000000000000 : ℝ) := by
  have h := padded_second_power (k := 18) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_13_φ3 (by norm_num [half_9_13_φ1, half_9_13_φ2, half_9_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_13_φ1, half_9_13_φ2, half_9_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_13_φ1, half_9_13_φ2, half_9_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_13_φ1, half_9_13_φ2, half_9_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_9_13_hx3 : SourcePowerBound (powerBoxCross 18 6 8 half_9_13_φ3) (76993036898469/10000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 18) (s := 6) (r := 1) (v := 2) (t := 10) (D := 8)
    (a := (3/10 : ℝ)) (b := (1/10 : ℝ)) (c := (3/5 : ℝ))
    (by norm_num) half_9_13_φ3 (by norm_num [half_9_13_φ1, half_9_13_φ2, half_9_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_13_φ1, half_9_13_φ2, half_9_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_9_13_hF1 half_9_13_hF2 half_10_12
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_9_13_φ1, half_9_13_φ2, half_9_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_9_13_hx2 : SourcePowerBound (powerBoxCross 18 7 4 half_9_13_φ2) (84269421724379/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 7) (u := 5) (t := 8)
    (D := 4) (ψ := (33611481383/2500000000000 : ℝ)) half_9_13_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_13_φ1, half_9_13_φ2, half_9_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_13_φ1, half_9_13_φ2, half_9_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_13_φ1, half_9_13_φ2, half_9_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_6 SeedCompletionEven18SecondSeeds.degree18_half_8
    (by simpa only [half_9_13_φ3, show (2:ℝ)*4=8 by norm_num] using half_9_13_hx3)
  exact h.weaken (by norm_num [half_9_13_φ1, half_9_13_φ2, half_9_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_9_13_hx1 : SourcePowerBound (powerBoxCross 18 8 2 half_9_13_φ1) (47087399014577/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 8) (u := 6) (t := 9)
    (D := 2) (ψ := (7708628651/250000000000 : ℝ)) half_9_13_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_13_φ1, half_9_13_φ2, half_9_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_13_φ1, half_9_13_φ2, half_9_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_13_φ1, half_9_13_φ2, half_9_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_7 half_9_12
    (by simpa only [half_9_13_φ2, show (2:ℝ)*2=4 by norm_num] using half_9_13_hx2)
  exact h.weaken (by norm_num [half_9_13_φ1, half_9_13_φ2, half_9_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_9_13 : AdmissibleExponent 18 18 (99332380517689/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 7) (ψ := (343838832569/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_8
    (by simpa only [half_9_13_φ1] using half_9_13_hx1)
  exact admissibleExponent_mono h (by norm_num [half_9_13_φ1, half_9_13_φ2, half_9_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_10_13_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (70749770727/2000000000000 : ℝ)

def half_10_13_φ2 : Fin 2 → ℝ := Fin.snoc half_10_13_φ1 (82314142119/2500000000000 : ℝ)

def half_10_13_φ3 : Fin 3 → ℝ := Fin.snoc half_10_13_φ2 (229938789187/10000000000000 : ℝ)

theorem half_10_13_hF2 : SourcePowerBound (paddedMoment 18 0 2 8 half_10_13_φ3) (31719922611901/5000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_10_13_φ3 (by norm_num [half_10_13_φ1, half_10_13_φ2, half_10_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_13_φ1, half_10_13_φ2, half_10_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_13_φ1, half_10_13_φ2, half_10_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_10_13_φ1, half_10_13_φ2, half_10_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_10_13_hx3 : SourcePowerBound (powerBoxCross 18 7 8 half_10_13_φ3) (864779138903/100000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 7) (r := 2) (v := 9) (w := 10) (D := 8)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_10_13_φ3 (by norm_num [half_10_13_φ1, half_10_13_φ2, half_10_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_13_φ1, half_10_13_φ2, half_10_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_10_13_hF2 half_9_13 half_10_12
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_10_13_φ1, half_10_13_φ2, half_10_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_13_hx2 : SourcePowerBound (powerBoxCross 18 8 4 half_10_13_φ2) (11900246940191/1250000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 8) (u := 6) (t := 9)
    (D := 4) (ψ := (229938789187/10000000000000 : ℝ)) half_10_13_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_13_φ1, half_10_13_φ2, half_10_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_13_φ1, half_10_13_φ2, half_10_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_13_φ1, half_10_13_φ2, half_10_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_7 half_9_13
    (by simpa only [half_10_13_φ3, show (2:ℝ)*4=8 by norm_num] using half_10_13_hx3)
  exact h.weaken (by norm_num [half_10_13_φ1, half_10_13_φ2, half_10_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_13_hx1 : SourcePowerBound (powerBoxCross 18 9 2 half_10_13_φ1) (106172257797643/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 9) (u := 7) (t := 10)
    (D := 2) (ψ := (82314142119/2500000000000 : ℝ)) half_10_13_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_13_φ1, half_10_13_φ2, half_10_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_13_φ1, half_10_13_φ2, half_10_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_13_φ1, half_10_13_φ2, half_10_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_8 half_10_12
    (by simpa only [half_10_13_φ2, show (2:ℝ)*2=4 by norm_num] using half_10_13_hx2)
  exact h.weaken (by norm_num [half_10_13_φ1, half_10_13_φ2, half_10_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_13 : AdmissibleExponent 18 20 (56092994154719/5000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 8) (ψ := (70749770727/2000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_9_13
    (by simpa only [half_10_13_φ1] using half_10_13_hx1)
  exact admissibleExponent_mono h (by norm_num [half_10_13_φ1, half_10_13_φ2, half_10_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_11_13_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (45593524291/1250000000000 : ℝ)

def half_11_13_φ2 : Fin 2 → ℝ := Fin.snoc half_11_13_φ1 (34639487763/1000000000000 : ℝ)

def half_11_13_φ3 : Fin 3 → ℝ := Fin.snoc half_11_13_φ2 (147364293001/5000000000000 : ℝ)

theorem half_11_13_hF2 : SourcePowerBound (paddedMoment 18 0 2 8 half_11_13_φ3) (1467513636101/250000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_11_13_φ3 (by norm_num [half_11_13_φ1, half_11_13_φ2, half_11_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_13_φ1, half_11_13_φ2, half_11_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_13_φ1, half_11_13_φ2, half_11_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_11_13_φ1, half_11_13_φ2, half_11_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_11_13_hx3 : SourcePowerBound (powerBoxCross 18 8 8 half_11_13_φ3) (48144374648877/5000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 8) (r := 2) (v := 10) (w := 11) (D := 8)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_11_13_φ3 (by norm_num [half_11_13_φ1, half_11_13_φ2, half_11_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_13_φ1, half_11_13_φ2, half_11_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_11_13_hF2 half_10_13 half_11_12
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_11_13_φ1, half_11_13_φ2, half_11_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_13_hx2 : SourcePowerBound (powerBoxCross 18 9 4 half_11_13_φ2) (53207051334559/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 9) (u := 7) (t := 10)
    (D := 4) (ψ := (147364293001/5000000000000 : ℝ)) half_11_13_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_13_φ1, half_11_13_φ2, half_11_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_13_φ1, half_11_13_φ2, half_11_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_13_φ1, half_11_13_φ2, half_11_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_8 half_10_13
    (by simpa only [half_11_13_φ3, show (2:ℝ)*4=8 by norm_num] using half_11_13_hx3)
  exact h.weaken (by norm_num [half_11_13_φ1, half_11_13_φ2, half_11_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_13_hx1 : SourcePowerBound (powerBoxCross 18 10 2 half_11_13_φ1) (59229386418653/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 10) (u := 8) (t := 11)
    (D := 2) (ψ := (34639487763/1000000000000 : ℝ)) half_11_13_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_13_φ1, half_11_13_φ2, half_11_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_13_φ1, half_11_13_φ2, half_11_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_13_φ1, half_11_13_φ2, half_11_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_13 half_11_12
    (by simpa only [half_11_13_φ2, show (2:ℝ)*2=4 by norm_num] using half_11_13_hx2)
  exact h.weaken (by norm_num [half_11_13_φ1, half_11_13_φ2, half_11_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_13 : AdmissibleExponent 18 22 (62694494264769/5000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 9) (ψ := (45593524291/1250000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_10_13
    (by simpa only [half_11_13_φ1] using half_11_13_hx1)
  exact admissibleExponent_mono h (by norm_num [half_11_13_φ1, half_11_13_φ2, half_11_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_12_13_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (374942177063/10000000000000 : ℝ)

def half_12_13_φ2 : Fin 2 → ℝ := Fin.snoc half_12_13_φ1 (360586881513/10000000000000 : ℝ)

def half_12_13_φ3 : Fin 3 → ℝ := Fin.snoc half_12_13_φ2 (82357523117/2500000000000 : ℝ)

def half_12_13_φ4 : Fin 4 → ℝ := Fin.snoc half_12_13_φ3 (212907454857/10000000000000 : ℝ)

theorem half_12_13_hF2 : SourcePowerBound (paddedMoment 18 0 2 16 half_12_13_φ4) (74828803099049/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_12_13_φ4 (by norm_num [half_12_13_φ1, half_12_13_φ2, half_12_13_φ3, half_12_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_13_φ1, half_12_13_φ2, half_12_13_φ3, half_12_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_13_φ1, half_12_13_φ2, half_12_13_φ3, half_12_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_12_13_φ1, half_12_13_φ2, half_12_13_φ3, half_12_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_12_13_hF1 : SourcePowerBound (paddedMoment 18 0 1 16 half_12_13_φ4) (28276267699683/10000000000000 : ℝ) := by
  have h := padded_second_power (k := 18) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_12_13_φ4 (by norm_num [half_12_13_φ1, half_12_13_φ2, half_12_13_φ3, half_12_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_13_φ1, half_12_13_φ2, half_12_13_φ3, half_12_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_13_φ1, half_12_13_φ2, half_12_13_φ3, half_12_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_12_13_φ1, half_12_13_φ2, half_12_13_φ3, half_12_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_12_13_hx4 : SourcePowerBound (powerBoxCross 18 8 16 half_12_13_φ4) (19566140525129/2000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 18) (s := 8) (r := 1) (v := 2) (t := 11) (D := 16)
    (a := (1/22 : ℝ)) (b := (5/22 : ℝ)) (c := (8/11 : ℝ))
    (by norm_num) half_12_13_φ4 (by norm_num [half_12_13_φ1, half_12_13_φ2, half_12_13_φ3, half_12_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_13_φ1, half_12_13_φ2, half_12_13_φ3, half_12_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_12_13_hF1 half_12_13_hF2 half_11_13
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_12_13_φ1, half_12_13_φ2, half_12_13_φ3, half_12_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_13_hx3 : SourcePowerBound (powerBoxCross 18 9 8 half_12_13_φ3) (106579323851643/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 9) (u := 7) (t := 10)
    (D := 8) (ψ := (212907454857/10000000000000 : ℝ)) half_12_13_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_13_φ1, half_12_13_φ2, half_12_13_φ3, half_12_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_13_φ1, half_12_13_φ2, half_12_13_φ3, half_12_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_13_φ1, half_12_13_φ2, half_12_13_φ3, half_12_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_8 half_10_13
    (by simpa only [half_12_13_φ4, show (2:ℝ)*8=16 by norm_num] using half_12_13_hx4)
  exact h.weaken (by norm_num [half_12_13_φ1, half_12_13_φ2, half_12_13_φ3, half_12_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_13_hx2 : SourcePowerBound (powerBoxCross 18 10 4 half_12_13_φ2) (117920952744227/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 10) (u := 8) (t := 11)
    (D := 4) (ψ := (82357523117/2500000000000 : ℝ)) half_12_13_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_13_φ1, half_12_13_φ2, half_12_13_φ3, half_12_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_13_φ1, half_12_13_φ2, half_12_13_φ3, half_12_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_13_φ1, half_12_13_φ2, half_12_13_φ3, half_12_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_13 half_11_13
    (by simpa only [half_12_13_φ3, show (2:ℝ)*4=8 by norm_num] using half_12_13_hx3)
  exact h.weaken (by norm_num [half_12_13_φ1, half_12_13_φ2, half_12_13_φ3, half_12_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_13_hx1 : SourcePowerBound (powerBoxCross 18 11 2 half_12_13_φ1) (16382821084089/1250000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 11) (u := 9) (t := 12)
    (D := 2) (ψ := (360586881513/10000000000000 : ℝ)) half_12_13_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_13_φ1, half_12_13_φ2, half_12_13_φ3, half_12_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_13_φ1, half_12_13_φ2, half_12_13_φ3, half_12_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_13_φ1, half_12_13_φ2, half_12_13_φ3, half_12_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_13 half_12_12
    (by simpa only [half_12_13_φ2, show (2:ℝ)*2=4 by norm_num] using half_12_13_hx2)
  exact h.weaken (by norm_num [half_12_13_φ1, half_12_13_φ2, half_12_13_φ3, half_12_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_13 : AdmissibleExponent 18 24 (27787270878207/2000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 10) (ψ := (374942177063/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_11_13
    (by simpa only [half_12_13_φ1] using half_12_13_hx1)
  exact admissibleExponent_mono h (by norm_num [half_12_13_φ1, half_12_13_φ2, half_12_13_φ3, half_12_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_13_13_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (192302628891/5000000000000 : ℝ)

def half_13_13_φ2 : Fin 2 → ℝ := Fin.snoc half_13_13_φ1 (14878738733/400000000000 : ℝ)

def half_13_13_φ3 : Fin 3 → ℝ := Fin.snoc half_13_13_φ2 (349893252659/10000000000000 : ℝ)

def half_13_13_φ4 : Fin 4 → ℝ := Fin.snoc half_13_13_φ3 (283313651813/10000000000000 : ℝ)

theorem half_13_13_hF2 : SourcePowerBound (paddedMoment 18 0 2 16 half_13_13_φ4) (69121187840471/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_13_13_φ4 (by norm_num [half_13_13_φ1, half_13_13_φ2, half_13_13_φ3, half_13_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_13_φ1, half_13_13_φ2, half_13_13_φ3, half_13_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_13_φ1, half_13_13_φ2, half_13_13_φ3, half_13_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_13_13_φ1, half_13_13_φ2, half_13_13_φ3, half_13_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_13_13_hx4 : SourcePowerBound (powerBoxCross 18 9 16 half_13_13_φ4) (133750917109/12500000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 9) (r := 2) (v := 12) (w := 12) (D := 16)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_13_13_φ4 (by norm_num [half_13_13_φ1, half_13_13_φ2, half_13_13_φ3, half_13_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_13_φ1, half_13_13_φ2, half_13_13_φ3, half_13_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_13_13_hF2 half_12_13 half_12_13
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_13_13_φ1, half_13_13_φ2, half_13_13_φ3, half_13_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_13_hx3 : SourcePowerBound (powerBoxCross 18 10 8 half_13_13_φ3) (11726111906383/1000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 10) (u := 8) (t := 11)
    (D := 8) (ψ := (283313651813/10000000000000 : ℝ)) half_13_13_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_13_φ1, half_13_13_φ2, half_13_13_φ3, half_13_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_13_φ1, half_13_13_φ2, half_13_13_φ3, half_13_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_13_φ1, half_13_13_φ2, half_13_13_φ3, half_13_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_13 half_11_13
    (by simpa only [half_13_13_φ4, show (2:ℝ)*8=16 by norm_num] using half_13_13_hx4)
  exact h.weaken (by norm_num [half_13_13_φ1, half_13_13_φ2, half_13_13_φ3, half_13_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_13_hx2 : SourcePowerBound (powerBoxCross 18 11 4 half_13_13_φ2) (129736066189117/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 11) (u := 9) (t := 12)
    (D := 4) (ψ := (349893252659/10000000000000 : ℝ)) half_13_13_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_13_φ1, half_13_13_φ2, half_13_13_φ3, half_13_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_13_φ1, half_13_13_φ2, half_13_13_φ3, half_13_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_13_φ1, half_13_13_φ2, half_13_13_φ3, half_13_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_13 half_12_13
    (by simpa only [half_13_13_φ3, show (2:ℝ)*4=8 by norm_num] using half_13_13_hx3)
  exact h.weaken (by norm_num [half_13_13_φ1, half_13_13_φ2, half_13_13_φ3, half_13_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_13_hx1 : SourcePowerBound (powerBoxCross 18 12 2 half_13_13_φ1) (35994348602311/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 12) (u := 10) (t := 13)
    (D := 2) (ψ := (14878738733/400000000000 : ℝ)) half_13_13_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_13_φ1, half_13_13_φ2, half_13_13_φ3, half_13_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_13_φ1, half_13_13_φ2, half_13_13_φ3, half_13_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_13_φ1, half_13_13_φ2, half_13_13_φ3, half_13_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_13 half_13_12
    (by simpa only [half_13_13_φ2, show (2:ℝ)*2=4 by norm_num] using half_13_13_hx2)
  exact h.weaken (by norm_num [half_13_13_φ1, half_13_13_φ2, half_13_13_φ3, half_13_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_13 : AdmissibleExponent 18 26 (15282331533823/1000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 11) (ψ := (192302628891/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_12_13
    (by simpa only [half_13_13_φ1] using half_13_13_hx1)
  exact admissibleExponent_mono h (by norm_num [half_13_13_φ1, half_13_13_φ2, half_13_13_φ3, half_13_13_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_14_13_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (394363361509/10000000000000 : ℝ)

def half_14_13_φ2 : Fin 2 → ℝ := Fin.snoc half_14_13_φ1 (23937306993/625000000000 : ℝ)

def half_14_13_φ3 : Fin 3 → ℝ := Fin.snoc half_14_13_φ2 (367260899249/10000000000000 : ℝ)

def half_14_13_φ4 : Fin 4 → ℝ := Fin.snoc half_14_13_φ3 (332115968269/10000000000000 : ℝ)

def half_14_13_φ5 : Fin 5 → ℝ := Fin.snoc half_14_13_φ4 (12848855259/625000000000 : ℝ)

theorem half_14_13_hF2 : SourcePowerBound (paddedMoment 18 0 2 32 half_14_13_φ5) (84201739921991/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_14_13_φ5 (by norm_num [half_14_13_φ1, half_14_13_φ2, half_14_13_φ3, half_14_13_φ4, half_14_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_13_φ1, half_14_13_φ2, half_14_13_φ3, half_14_13_φ4, half_14_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_13_φ1, half_14_13_φ2, half_14_13_φ3, half_14_13_φ4, half_14_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_14_13_φ1, half_14_13_φ2, half_14_13_φ3, half_14_13_φ4, half_14_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_14_13_hx5 : SourcePowerBound (powerBoxCross 18 9 32 half_14_13_φ5) (107722557437991/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 9) (r := 2) (v := 12) (w := 12) (D := 32)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_14_13_φ5 (by norm_num [half_14_13_φ1, half_14_13_φ2, half_14_13_φ3, half_14_13_φ4, half_14_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_13_φ1, half_14_13_φ2, half_14_13_φ3, half_14_13_φ4, half_14_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_14_13_hF2 half_12_13 half_12_13
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_14_13_φ1, half_14_13_φ2, half_14_13_φ3, half_14_13_φ4, half_14_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_13_hx4 : SourcePowerBound (powerBoxCross 18 10 16 half_14_13_φ4) (116492622780047/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 10) (u := 8) (t := 11)
    (D := 16) (ψ := (12848855259/625000000000 : ℝ)) half_14_13_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_13_φ1, half_14_13_φ2, half_14_13_φ3, half_14_13_φ4, half_14_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_13_φ1, half_14_13_φ2, half_14_13_φ3, half_14_13_φ4, half_14_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_13_φ1, half_14_13_φ2, half_14_13_φ3, half_14_13_φ4, half_14_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_13 half_11_13
    (by simpa only [half_14_13_φ5, show (2:ℝ)*16=32 by norm_num] using half_14_13_hx5)
  exact h.weaken (by norm_num [half_14_13_φ1, half_14_13_φ2, half_14_13_φ3, half_14_13_φ4, half_14_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_13_hx3 : SourcePowerBound (powerBoxCross 18 11 8 half_14_13_φ3) (25637767134459/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 11) (u := 9) (t := 12)
    (D := 8) (ψ := (332115968269/10000000000000 : ℝ)) half_14_13_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_13_φ1, half_14_13_φ2, half_14_13_φ3, half_14_13_φ4, half_14_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_13_φ1, half_14_13_φ2, half_14_13_φ3, half_14_13_φ4, half_14_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_13_φ1, half_14_13_φ2, half_14_13_φ3, half_14_13_φ4, half_14_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_13 half_12_13
    (by simpa only [half_14_13_φ4, show (2:ℝ)*8=16 by norm_num] using half_14_13_hx4)
  exact h.weaken (by norm_num [half_14_13_φ1, half_14_13_φ2, half_14_13_φ3, half_14_13_φ4, half_14_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_13_hx2 : SourcePowerBound (powerBoxCross 18 12 4 half_14_13_φ2) (28362962782773/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 12) (u := 10) (t := 13)
    (D := 4) (ψ := (367260899249/10000000000000 : ℝ)) half_14_13_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_13_φ1, half_14_13_φ2, half_14_13_φ3, half_14_13_φ4, half_14_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_13_φ1, half_14_13_φ2, half_14_13_φ3, half_14_13_φ4, half_14_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_13_φ1, half_14_13_φ2, half_14_13_φ3, half_14_13_φ4, half_14_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_13 half_13_13
    (by simpa only [half_14_13_φ3, show (2:ℝ)*4=8 by norm_num] using half_14_13_hx3)
  exact h.weaken (by norm_num [half_14_13_φ1, half_14_13_φ2, half_14_13_φ3, half_14_13_φ4, half_14_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_13_hx1 : SourcePowerBound (powerBoxCross 18 13 2 half_14_13_φ1) (157190887064377/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 13) (u := 11) (t := 14)
    (D := 2) (ψ := (23937306993/625000000000 : ℝ)) half_14_13_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_13_φ1, half_14_13_φ2, half_14_13_φ3, half_14_13_φ4, half_14_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_13_φ1, half_14_13_φ2, half_14_13_φ3, half_14_13_φ4, half_14_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_13_φ1, half_14_13_φ2, half_14_13_φ3, half_14_13_φ4, half_14_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_13 half_14_12
    (by simpa only [half_14_13_φ2, show (2:ℝ)*2=4 by norm_num] using half_14_13_hx2)
  exact h.weaken (by norm_num [half_14_13_φ1, half_14_13_φ2, half_14_13_φ3, half_14_13_φ4, half_14_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_13 : AdmissibleExponent 18 28 (83524985551051/5000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 12) (ψ := (394363361509/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_13_13
    (by simpa only [half_14_13_φ1] using half_14_13_hx1)
  exact admissibleExponent_mono h (by norm_num [half_14_13_φ1, half_14_13_φ2, half_14_13_φ3, half_14_13_φ4, half_14_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_15_13_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (403645163751/10000000000000 : ℝ)

def half_15_13_φ2 : Fin 2 → ℝ := Fin.snoc half_15_13_φ1 (392988146071/10000000000000 : ℝ)

def half_15_13_φ3 : Fin 3 → ℝ := Fin.snoc half_15_13_φ2 (18972893959/500000000000 : ℝ)

def half_15_13_φ4 : Fin 4 → ℝ := Fin.snoc half_15_13_φ3 (71045177329/2000000000000 : ℝ)

def half_15_13_φ5 : Fin 5 → ℝ := Fin.snoc half_15_13_φ4 (56858798009/2000000000000 : ℝ)

theorem half_15_13_hF2 : SourcePowerBound (paddedMoment 18 0 2 32 half_15_13_φ5) (19350958912427/2500000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_15_13_φ5 (by norm_num [half_15_13_φ1, half_15_13_φ2, half_15_13_φ3, half_15_13_φ4, half_15_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_13_φ1, half_15_13_φ2, half_15_13_φ3, half_15_13_φ4, half_15_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_13_φ1, half_15_13_φ2, half_15_13_φ3, half_15_13_φ4, half_15_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_15_13_φ1, half_15_13_φ2, half_15_13_φ3, half_15_13_φ4, half_15_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_15_13_hx5 : SourcePowerBound (powerBoxCross 18 10 32 half_15_13_φ5) (3627164994827/312500000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 10) (r := 2) (v := 13) (w := 14) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_15_13_φ5 (by norm_num [half_15_13_φ1, half_15_13_φ2, half_15_13_φ3, half_15_13_φ4, half_15_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_13_φ1, half_15_13_φ2, half_15_13_φ3, half_15_13_φ4, half_15_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_15_13_hF2 half_13_13 half_14_13
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_15_13_φ1, half_15_13_φ2, half_15_13_φ3, half_15_13_φ4, half_15_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_13_hx4 : SourcePowerBound (powerBoxCross 18 11 16 half_15_13_φ4) (126549634279821/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 11) (u := 9) (t := 12)
    (D := 16) (ψ := (56858798009/2000000000000 : ℝ)) half_15_13_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_13_φ1, half_15_13_φ2, half_15_13_φ3, half_15_13_φ4, half_15_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_13_φ1, half_15_13_φ2, half_15_13_φ3, half_15_13_φ4, half_15_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_13_φ1, half_15_13_φ2, half_15_13_φ3, half_15_13_φ4, half_15_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_13 half_12_13
    (by simpa only [half_15_13_φ5, show (2:ℝ)*16=32 by norm_num] using half_15_13_hx5)
  exact h.weaken (by norm_num [half_15_13_φ1, half_15_13_φ2, half_15_13_φ3, half_15_13_φ4, half_15_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_13_hx3 : SourcePowerBound (powerBoxCross 18 12 8 half_15_13_φ3) (139432863780113/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 12) (u := 10) (t := 13)
    (D := 8) (ψ := (71045177329/2000000000000 : ℝ)) half_15_13_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_13_φ1, half_15_13_φ2, half_15_13_φ3, half_15_13_φ4, half_15_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_13_φ1, half_15_13_φ2, half_15_13_φ3, half_15_13_φ4, half_15_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_13_φ1, half_15_13_φ2, half_15_13_φ3, half_15_13_φ4, half_15_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_13 half_13_13
    (by simpa only [half_15_13_φ4, show (2:ℝ)*8=16 by norm_num] using half_15_13_hx4)
  exact h.weaken (by norm_num [half_15_13_φ1, half_15_13_φ2, half_15_13_φ3, half_15_13_φ4, half_15_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_13_hx2 : SourcePowerBound (powerBoxCross 18 13 4 half_15_13_φ2) (77089960674477/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 13) (u := 11) (t := 14)
    (D := 4) (ψ := (18972893959/500000000000 : ℝ)) half_15_13_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_13_φ1, half_15_13_φ2, half_15_13_φ3, half_15_13_φ4, half_15_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_13_φ1, half_15_13_φ2, half_15_13_φ3, half_15_13_φ4, half_15_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_13_φ1, half_15_13_φ2, half_15_13_φ3, half_15_13_φ4, half_15_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_13 half_14_13
    (by simpa only [half_15_13_φ3, show (2:ℝ)*4=8 by norm_num] using half_15_13_hx3)
  exact h.weaken (by norm_num [half_15_13_φ1, half_15_13_φ2, half_15_13_φ3, half_15_13_φ4, half_15_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_13_hx1 : SourcePowerBound (powerBoxCross 18 14 2 half_15_13_φ1) (42677681242963/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 14) (u := 12) (t := 15)
    (D := 2) (ψ := (392988146071/10000000000000 : ℝ)) half_15_13_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_13_φ1, half_15_13_φ2, half_15_13_φ3, half_15_13_φ4, half_15_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_13_φ1, half_15_13_φ2, half_15_13_φ3, half_15_13_φ4, half_15_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_13_φ1, half_15_13_φ2, half_15_13_φ3, half_15_13_φ4, half_15_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_13_13 half_15_12
    (by simpa only [half_15_13_φ2, show (2:ℝ)*2=4 by norm_num] using half_15_13_hx2)
  exact h.weaken (by norm_num [half_15_13_φ1, half_15_13_φ2, half_15_13_φ3, half_15_13_φ4, half_15_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_13 : AdmissibleExponent 18 30 (181609144393129/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 13) (ψ := (403645163751/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_14_13
    (by simpa only [half_15_13_φ1] using half_15_13_hx1)
  exact admissibleExponent_mono h (by norm_num [half_15_13_φ1, half_15_13_φ2, half_15_13_φ3, half_15_13_φ4, half_15_13_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_16_13_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (412907039437/10000000000000 : ℝ)

def half_16_13_φ2 : Fin 2 → ℝ := Fin.snoc half_16_13_φ1 (100673994493/2500000000000 : ℝ)

def half_16_13_φ3 : Fin 3 → ℝ := Fin.snoc half_16_13_φ2 (78219585219/2000000000000 : ℝ)

def half_16_13_φ4 : Fin 4 → ℝ := Fin.snoc half_16_13_φ3 (374103022463/10000000000000 : ℝ)

def half_16_13_φ5 : Fin 5 → ℝ := Fin.snoc half_16_13_φ4 (336303036967/10000000000000 : ℝ)

def half_16_13_φ6 : Fin 6 → ℝ := Fin.snoc half_16_13_φ5 (104115632147/5000000000000 : ℝ)

theorem half_16_13_hF2 : SourcePowerBound (paddedMoment 18 0 2 64 half_16_13_φ6) (22901937092843/2500000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 6) (r := 0) (D := 64)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_16_13_φ6 (by norm_num [half_16_13_φ1, half_16_13_φ2, half_16_13_φ3, half_16_13_φ4, half_16_13_φ5, half_16_13_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_13_φ1, half_16_13_φ2, half_16_13_φ3, half_16_13_φ4, half_16_13_φ5, half_16_13_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_13_φ1, half_16_13_φ2, half_16_13_φ3, half_16_13_φ4, half_16_13_φ5, half_16_13_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_16_13_φ1, half_16_13_φ2, half_16_13_φ3, half_16_13_φ4, half_16_13_φ5, half_16_13_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_16_13_hx6 : SourcePowerBound (powerBoxCross 18 10 64 half_16_13_φ6) (115960083123769/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 10) (r := 2) (v := 13) (w := 14) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_16_13_φ6 (by norm_num [half_16_13_φ1, half_16_13_φ2, half_16_13_φ3, half_16_13_φ4, half_16_13_φ5, half_16_13_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_13_φ1, half_16_13_φ2, half_16_13_φ3, half_16_13_φ4, half_16_13_φ5, half_16_13_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_16_13_hF2 half_13_13 half_14_13
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_16_13_φ1, half_16_13_φ2, half_16_13_φ3, half_16_13_φ4, half_16_13_φ5, half_16_13_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_13_hx5 : SourcePowerBound (powerBoxCross 18 11 32 half_16_13_φ5) (62406606672499/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 5) (s := 11) (u := 9) (t := 12)
    (D := 32) (ψ := (104115632147/5000000000000 : ℝ)) half_16_13_φ5
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_13_φ1, half_16_13_φ2, half_16_13_φ3, half_16_13_φ4, half_16_13_φ5, half_16_13_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_13_φ1, half_16_13_φ2, half_16_13_φ3, half_16_13_φ4, half_16_13_φ5, half_16_13_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_13_φ1, half_16_13_φ2, half_16_13_φ3, half_16_13_φ4, half_16_13_φ5, half_16_13_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_13 half_12_13
    (by simpa only [half_16_13_φ6, show (2:ℝ)*32=64 by norm_num] using half_16_13_hx6)
  exact h.weaken (by norm_num [half_16_13_φ1, half_16_13_φ2, half_16_13_φ3, half_16_13_φ4, half_16_13_φ5, half_16_13_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_13_hx4 : SourcePowerBound (powerBoxCross 18 12 16 half_16_13_φ4) (17104178421263/1250000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 12) (u := 10) (t := 13)
    (D := 16) (ψ := (336303036967/10000000000000 : ℝ)) half_16_13_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_13_φ1, half_16_13_φ2, half_16_13_φ3, half_16_13_φ4, half_16_13_φ5, half_16_13_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_13_φ1, half_16_13_φ2, half_16_13_φ3, half_16_13_φ4, half_16_13_φ5, half_16_13_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_13_φ1, half_16_13_φ2, half_16_13_φ3, half_16_13_φ4, half_16_13_φ5, half_16_13_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_13 half_13_13
    (by simpa only [half_16_13_φ5, show (2:ℝ)*16=32 by norm_num] using half_16_13_hx5)
  exact h.weaken (by norm_num [half_16_13_φ1, half_16_13_φ2, half_16_13_φ3, half_16_13_φ4, half_16_13_φ5, half_16_13_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_13_hx3 : SourcePowerBound (powerBoxCross 18 13 8 half_16_13_φ3) (150907958087583/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 13) (u := 11) (t := 14)
    (D := 8) (ψ := (374103022463/10000000000000 : ℝ)) half_16_13_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_13_φ1, half_16_13_φ2, half_16_13_φ3, half_16_13_φ4, half_16_13_φ5, half_16_13_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_13_φ1, half_16_13_φ2, half_16_13_φ3, half_16_13_φ4, half_16_13_φ5, half_16_13_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_13_φ1, half_16_13_φ2, half_16_13_φ3, half_16_13_φ4, half_16_13_φ5, half_16_13_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_13 half_14_13
    (by simpa only [half_16_13_φ4, show (2:ℝ)*8=16 by norm_num] using half_16_13_hx4)
  exact h.weaken (by norm_num [half_16_13_φ1, half_16_13_φ2, half_16_13_φ3, half_16_13_φ4, half_16_13_φ5, half_16_13_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_13_hx2 : SourcePowerBound (powerBoxCross 18 14 4 half_16_13_φ2) (83404300680381/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 14) (u := 12) (t := 15)
    (D := 4) (ψ := (78219585219/2000000000000 : ℝ)) half_16_13_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_13_φ1, half_16_13_φ2, half_16_13_φ3, half_16_13_φ4, half_16_13_φ5, half_16_13_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_13_φ1, half_16_13_φ2, half_16_13_φ3, half_16_13_φ4, half_16_13_φ5, half_16_13_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_13_φ1, half_16_13_φ2, half_16_13_φ3, half_16_13_φ4, half_16_13_φ5, half_16_13_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_13_13 half_15_13
    (by simpa only [half_16_13_φ3, show (2:ℝ)*4=8 by norm_num] using half_16_13_hx3)
  exact h.weaken (by norm_num [half_16_13_φ1, half_16_13_φ2, half_16_13_φ3, half_16_13_φ4, half_16_13_φ5, half_16_13_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_13_hx1 : SourcePowerBound (powerBoxCross 18 15 2 half_16_13_φ1) (46130820504493/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 15) (u := 13) (t := 16)
    (D := 2) (ψ := (100673994493/2500000000000 : ℝ)) half_16_13_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_13_φ1, half_16_13_φ2, half_16_13_φ3, half_16_13_φ4, half_16_13_φ5, half_16_13_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_13_φ1, half_16_13_φ2, half_16_13_φ3, half_16_13_φ4, half_16_13_φ5, half_16_13_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_13_φ1, half_16_13_φ2, half_16_13_φ3, half_16_13_φ4, half_16_13_φ5, half_16_13_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_14_13 half_16_12
    (by simpa only [half_16_13_φ2, show (2:ℝ)*2=4 by norm_num] using half_16_13_hx2)
  exact h.weaken (by norm_num [half_16_13_φ1, half_16_13_φ2, half_16_13_φ3, half_16_13_φ4, half_16_13_φ5, half_16_13_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_13 : AdmissibleExponent 18 32 (39299517232329/2000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 14) (ψ := (412907039437/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_15_13
    (by simpa only [half_16_13_φ1] using half_16_13_hx1)
  exact admissibleExponent_mono h (by norm_num [half_16_13_φ1, half_16_13_φ2, half_16_13_φ3, half_16_13_φ4, half_16_13_φ5, half_16_13_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_17_13_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (105466608519/2500000000000 : ℝ)

def half_17_13_φ2 : Fin 2 → ℝ := Fin.snoc half_17_13_φ1 (412014594929/10000000000000 : ℝ)

def half_17_13_φ3 : Fin 3 → ℝ := Fin.snoc half_17_13_φ2 (401125529391/10000000000000 : ℝ)

def half_17_13_φ4 : Fin 4 → ℝ := Fin.snoc half_17_13_φ3 (387124091093/10000000000000 : ℝ)

def half_17_13_φ5 : Fin 5 → ℝ := Fin.snoc half_17_13_φ4 (90336029787/2500000000000 : ℝ)

def half_17_13_φ6 : Fin 6 → ℝ := Fin.snoc half_17_13_φ5 (144600030669/5000000000000 : ℝ)

theorem half_17_13_hF2 : SourcePowerBound (paddedMoment 18 0 2 64 half_17_13_φ6) (3363743346851/400000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 6) (r := 0) (D := 64)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_17_13_φ6 (by norm_num [half_17_13_φ1, half_17_13_φ2, half_17_13_φ3, half_17_13_φ4, half_17_13_φ5, half_17_13_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_13_φ1, half_17_13_φ2, half_17_13_φ3, half_17_13_φ4, half_17_13_φ5, half_17_13_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_13_φ1, half_17_13_φ2, half_17_13_φ3, half_17_13_φ4, half_17_13_φ5, half_17_13_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_17_13_φ1, half_17_13_φ2, half_17_13_φ3, half_17_13_φ4, half_17_13_φ5, half_17_13_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_17_13_hx6 : SourcePowerBound (powerBoxCross 18 11 64 half_17_13_φ6) (15432784713167/1250000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 11) (r := 2) (v := 14) (w := 15) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_17_13_φ6 (by norm_num [half_17_13_φ1, half_17_13_φ2, half_17_13_φ3, half_17_13_φ4, half_17_13_φ5, half_17_13_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_13_φ1, half_17_13_φ2, half_17_13_φ3, half_17_13_φ4, half_17_13_φ5, half_17_13_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_17_13_hF2 half_14_13 half_15_13
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_17_13_φ1, half_17_13_φ2, half_17_13_φ3, half_17_13_φ4, half_17_13_φ5, half_17_13_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_13_hx5 : SourcePowerBound (powerBoxCross 18 12 32 half_17_13_φ5) (16770475266347/1250000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 5) (s := 12) (u := 10) (t := 13)
    (D := 32) (ψ := (144600030669/5000000000000 : ℝ)) half_17_13_φ5
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_13_φ1, half_17_13_φ2, half_17_13_φ3, half_17_13_φ4, half_17_13_φ5, half_17_13_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_13_φ1, half_17_13_φ2, half_17_13_φ3, half_17_13_φ4, half_17_13_φ5, half_17_13_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_13_φ1, half_17_13_φ2, half_17_13_φ3, half_17_13_φ4, half_17_13_φ5, half_17_13_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_13 half_13_13
    (by simpa only [half_17_13_φ6, show (2:ℝ)*32=64 by norm_num] using half_17_13_hx6)
  exact h.weaken (by norm_num [half_17_13_φ1, half_17_13_φ2, half_17_13_φ3, half_17_13_φ4, half_17_13_φ5, half_17_13_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_13_hx4 : SourcePowerBound (powerBoxCross 18 13 16 half_17_13_φ4) (1151760855937/78125000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 13) (u := 11) (t := 14)
    (D := 16) (ψ := (90336029787/2500000000000 : ℝ)) half_17_13_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_13_φ1, half_17_13_φ2, half_17_13_φ3, half_17_13_φ4, half_17_13_φ5, half_17_13_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_13_φ1, half_17_13_φ2, half_17_13_φ3, half_17_13_φ4, half_17_13_φ5, half_17_13_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_13_φ1, half_17_13_φ2, half_17_13_φ3, half_17_13_φ4, half_17_13_φ5, half_17_13_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_13 half_14_13
    (by simpa only [half_17_13_φ5, show (2:ℝ)*16=32 by norm_num] using half_17_13_hx5)
  exact h.weaken (by norm_num [half_17_13_φ1, half_17_13_φ2, half_17_13_φ3, half_17_13_φ4, half_17_13_φ5, half_17_13_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_13_hx3 : SourcePowerBound (powerBoxCross 18 14 8 half_17_13_φ3) (162644338149319/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 14) (u := 12) (t := 15)
    (D := 8) (ψ := (387124091093/10000000000000 : ℝ)) half_17_13_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_13_φ1, half_17_13_φ2, half_17_13_φ3, half_17_13_φ4, half_17_13_φ5, half_17_13_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_13_φ1, half_17_13_φ2, half_17_13_φ3, half_17_13_φ4, half_17_13_φ5, half_17_13_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_13_φ1, half_17_13_φ2, half_17_13_φ3, half_17_13_φ4, half_17_13_φ5, half_17_13_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_13_13 half_15_13
    (by simpa only [half_17_13_φ4, show (2:ℝ)*8=16 by norm_num] using half_17_13_hx4)
  exact h.weaken (by norm_num [half_17_13_φ1, half_17_13_φ2, half_17_13_φ3, half_17_13_φ4, half_17_13_φ5, half_17_13_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_13_hx2 : SourcePowerBound (powerBoxCross 18 15 4 half_17_13_φ2) (35941077517689/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 15) (u := 13) (t := 16)
    (D := 4) (ψ := (401125529391/10000000000000 : ℝ)) half_17_13_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_13_φ1, half_17_13_φ2, half_17_13_φ3, half_17_13_φ4, half_17_13_φ5, half_17_13_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_13_φ1, half_17_13_φ2, half_17_13_φ3, half_17_13_φ4, half_17_13_φ5, half_17_13_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_13_φ1, half_17_13_φ2, half_17_13_φ3, half_17_13_φ4, half_17_13_φ5, half_17_13_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_14_13 half_16_13
    (by simpa only [half_17_13_φ3, show (2:ℝ)*4=8 by norm_num] using half_17_13_hx3)
  exact h.weaken (by norm_num [half_17_13_φ1, half_17_13_φ2, half_17_13_φ3, half_17_13_φ4, half_17_13_φ5, half_17_13_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_13_hx1 : SourcePowerBound (powerBoxCross 18 16 2 half_17_13_φ1) (198629878997869/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 16) (u := 14) (t := 17)
    (D := 2) (ψ := (412014594929/10000000000000 : ℝ)) half_17_13_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_13_φ1, half_17_13_φ2, half_17_13_φ3, half_17_13_φ4, half_17_13_φ5, half_17_13_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_13_φ1, half_17_13_φ2, half_17_13_φ3, half_17_13_φ4, half_17_13_φ5, half_17_13_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_13_φ1, half_17_13_φ2, half_17_13_φ3, half_17_13_φ4, half_17_13_φ5, half_17_13_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_15_13 half_17_12
    (by simpa only [half_17_13_φ2, show (2:ℝ)*2=4 by norm_num] using half_17_13_hx2)
  exact h.weaken (by norm_num [half_17_13_φ1, half_17_13_φ2, half_17_13_φ3, half_17_13_φ4, half_17_13_φ5, half_17_13_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_13 : AdmissibleExponent 18 34 (8468309538169/400000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 15) (ψ := (105466608519/2500000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_16_13
    (by simpa only [half_17_13_φ1] using half_17_13_hx1)
  exact admissibleExponent_mono h (by norm_num [half_17_13_φ1, half_17_13_φ2, half_17_13_φ3, half_17_13_φ4, half_17_13_φ5, half_17_13_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])


end Waring.SeedCompletionHigher18SimpleSeeds
