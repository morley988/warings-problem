import Waring.SeedCompletionHigher18SimpleSeedsC20

noncomputable section
set_option maxHeartbeats 2000000
namespace Waring.SeedCompletionHigher18SimpleSeeds
open SmoothMoments FirstStageTransport SeedCompletionNaturalBox
open SeedCompletionSourceBounds SeedCompletionPaddedSource SeedCompletionGeneralTerminal
open PolicyCompletionMajorPowerRanges

def half_9_21_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (42979853791/1250000000000 : ℝ)

def half_9_21_φ2 : Fin 2 → ℝ := Fin.snoc half_9_21_φ1 (308345143257/10000000000000 : ℝ)

def half_9_21_φ3 : Fin 3 → ℝ := Fin.snoc half_9_21_φ2 (67222953977/5000000000000 : ℝ)

theorem half_9_21_hF2 : SourcePowerBound (paddedMoment 18 0 2 8 half_9_21_φ3) (69881876041511/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_21_φ3 (by norm_num [half_9_21_φ1, half_9_21_φ2, half_9_21_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_21_φ1, half_9_21_φ2, half_9_21_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_21_φ1, half_9_21_φ2, half_9_21_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_21_φ1, half_9_21_φ2, half_9_21_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_9_21_hF1 : SourcePowerBound (paddedMoment 18 0 1 8 half_9_21_φ3) (26627292013837/10000000000000 : ℝ) := by
  have h := padded_second_power (k := 18) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_21_φ3 (by norm_num [half_9_21_φ1, half_9_21_φ2, half_9_21_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_21_φ1, half_9_21_φ2, half_9_21_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_21_φ1, half_9_21_φ2, half_9_21_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_21_φ1, half_9_21_φ2, half_9_21_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_9_21_hx3 : SourcePowerBound (powerBoxCross 18 6 8 half_9_21_φ3) (76993037108447/10000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 18) (s := 6) (r := 1) (v := 2) (t := 10) (D := 8)
    (a := (3/10 : ℝ)) (b := (1/10 : ℝ)) (c := (3/5 : ℝ))
    (by norm_num) half_9_21_φ3 (by norm_num [half_9_21_φ1, half_9_21_φ2, half_9_21_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_21_φ1, half_9_21_φ2, half_9_21_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_9_21_hF1 half_9_21_hF2 half_10_20
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_9_21_φ1, half_9_21_φ2, half_9_21_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_9_21_hx2 : SourcePowerBound (powerBoxCross 18 7 4 half_9_21_φ2) (42134710898601/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 7) (u := 5) (t := 8)
    (D := 4) (ψ := (67222953977/5000000000000 : ℝ)) half_9_21_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_21_φ1, half_9_21_φ2, half_9_21_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_21_φ1, half_9_21_φ2, half_9_21_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_21_φ1, half_9_21_φ2, half_9_21_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_6 SeedCompletionEven18SecondSeeds.degree18_half_8
    (by simpa only [half_9_21_φ3, show (2:ℝ)*4=8 by norm_num] using half_9_21_hx3)
  exact h.weaken (by norm_num [half_9_21_φ1, half_9_21_φ2, half_9_21_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_9_21_hx1 : SourcePowerBound (powerBoxCross 18 8 2 half_9_21_φ1) (47087399023183/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 8) (u := 6) (t := 9)
    (D := 2) (ψ := (308345143257/10000000000000 : ℝ)) half_9_21_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_21_φ1, half_9_21_φ2, half_9_21_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_21_φ1, half_9_21_φ2, half_9_21_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_21_φ1, half_9_21_φ2, half_9_21_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_7 half_9_20
    (by simpa only [half_9_21_φ2, show (2:ℝ)*2=4 by norm_num] using half_9_21_hx2)
  exact h.weaken (by norm_num [half_9_21_φ1, half_9_21_φ2, half_9_21_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_9_21 : AdmissibleExponent 18 18 (49666190250643/5000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 7) (ψ := (42979853791/1250000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_8
    (by simpa only [half_9_21_φ1] using half_9_21_hx1)
  exact admissibleExponent_mono h (by norm_num [half_9_21_φ1, half_9_21_φ2, half_9_21_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_10_21_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (353748845759/10000000000000 : ℝ)

def half_10_21_φ2 : Fin 2 → ℝ := Fin.snoc half_10_21_φ1 (6585131331/200000000000 : ℝ)

def half_10_21_φ3 : Fin 3 → ℝ := Fin.snoc half_10_21_φ2 (114969390427/5000000000000 : ℝ)

theorem half_10_21_hF2 : SourcePowerBound (paddedMoment 18 0 2 8 half_10_21_φ3) (63439846148687/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_10_21_φ3 (by norm_num [half_10_21_φ1, half_10_21_φ2, half_10_21_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_21_φ1, half_10_21_φ2, half_10_21_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_21_φ1, half_10_21_φ2, half_10_21_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_10_21_φ1, half_10_21_φ2, half_10_21_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_10_21_hx3 : SourcePowerBound (powerBoxCross 18 7 8 half_10_21_φ3) (21619478546007/2500000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 7) (r := 2) (v := 9) (w := 10) (D := 8)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_10_21_φ3 (by norm_num [half_10_21_φ1, half_10_21_φ2, half_10_21_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_21_φ1, half_10_21_φ2, half_10_21_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_10_21_hF2 half_9_21 half_10_20
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_10_21_φ1, half_10_21_φ2, half_10_21_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_21_hx2 : SourcePowerBound (powerBoxCross 18 8 4 half_10_21_φ2) (47600987869293/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 8) (u := 6) (t := 9)
    (D := 4) (ψ := (114969390427/5000000000000 : ℝ)) half_10_21_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_21_φ1, half_10_21_φ2, half_10_21_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_21_φ1, half_10_21_φ2, half_10_21_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_21_φ1, half_10_21_φ2, half_10_21_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_7 half_9_21
    (by simpa only [half_10_21_φ3, show (2:ℝ)*4=8 by norm_num] using half_10_21_hx3)
  exact h.weaken (by norm_num [half_10_21_φ1, half_10_21_φ2, half_10_21_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_21_hx1 : SourcePowerBound (powerBoxCross 18 9 2 half_10_21_φ1) (26543064463043/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 9) (u := 7) (t := 10)
    (D := 2) (ψ := (6585131331/200000000000 : ℝ)) half_10_21_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_21_φ1, half_10_21_φ2, half_10_21_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_21_φ1, half_10_21_φ2, half_10_21_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_21_φ1, half_10_21_φ2, half_10_21_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_8 half_10_20
    (by simpa only [half_10_21_φ2, show (2:ℝ)*2=4 by norm_num] using half_10_21_hx2)
  exact h.weaken (by norm_num [half_10_21_φ1, half_10_21_φ2, half_10_21_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_21 : AdmissibleExponent 18 20 (4487439529203/400000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 8) (ψ := (353748845759/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_9_21
    (by simpa only [half_10_21_φ1] using half_10_21_hx1)
  exact admissibleExponent_mono h (by norm_num [half_10_21_φ1, half_10_21_φ2, half_10_21_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_11_21_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (72949626711/2000000000000 : ℝ)

def half_11_21_φ2 : Fin 2 → ℝ := Fin.snoc half_11_21_φ1 (69278971447/2000000000000 : ℝ)

def half_11_21_φ3 : Fin 3 → ℝ := Fin.snoc half_11_21_φ2 (73682122803/2500000000000 : ℝ)

theorem half_11_21_hF2 : SourcePowerBound (paddedMoment 18 0 2 8 half_11_21_φ3) (29350277208949/5000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_11_21_φ3 (by norm_num [half_11_21_φ1, half_11_21_φ2, half_11_21_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_21_φ1, half_11_21_φ2, half_11_21_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_21_φ1, half_11_21_φ2, half_11_21_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_11_21_φ1, half_11_21_φ2, half_11_21_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_11_21_hx3 : SourcePowerBound (powerBoxCross 18 8 8 half_11_21_φ3) (24072188027607/2500000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 8) (r := 2) (v := 10) (w := 11) (D := 8)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_11_21_φ3 (by norm_num [half_11_21_φ1, half_11_21_φ2, half_11_21_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_21_φ1, half_11_21_φ2, half_11_21_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_11_21_hF2 half_10_21 half_11_20
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_11_21_φ1, half_11_21_φ2, half_11_21_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_21_hx2 : SourcePowerBound (powerBoxCross 18 9 4 half_11_21_φ2) (53207052236447/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 9) (u := 7) (t := 10)
    (D := 4) (ψ := (73682122803/2500000000000 : ℝ)) half_11_21_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_21_φ1, half_11_21_φ2, half_11_21_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_21_φ1, half_11_21_φ2, half_11_21_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_21_φ1, half_11_21_φ2, half_11_21_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_8 half_10_21
    (by simpa only [half_11_21_φ3, show (2:ℝ)*4=8 by norm_num] using half_11_21_hx3)
  exact h.weaken (by norm_num [half_11_21_φ1, half_11_21_φ2, half_11_21_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_21_hx1 : SourcePowerBound (powerBoxCross 18 10 2 half_11_21_φ1) (14807346672731/1250000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 10) (u := 8) (t := 11)
    (D := 2) (ψ := (69278971447/2000000000000 : ℝ)) half_11_21_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_21_φ1, half_11_21_φ2, half_11_21_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_21_φ1, half_11_21_φ2, half_11_21_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_21_φ1, half_11_21_φ2, half_11_21_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_21 half_11_20
    (by simpa only [half_11_21_φ2, show (2:ℝ)*2=4 by norm_num] using half_11_21_hx2)
  exact h.weaken (by norm_num [half_11_21_φ1, half_11_21_φ2, half_11_21_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_21 : AdmissibleExponent 18 22 (125388987919393/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 9) (ψ := (72949626711/2000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_10_21
    (by simpa only [half_11_21_φ1] using half_11_21_hx1)
  exact admissibleExponent_mono h (by norm_num [half_11_21_φ1, half_11_21_φ2, half_11_21_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_12_21_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (187470977071/5000000000000 : ℝ)

def half_12_21_φ2 : Fin 2 → ℝ := Fin.snoc half_12_21_φ1 (1802934323/50000000000 : ℝ)

def half_12_21_φ3 : Fin 3 → ℝ := Fin.snoc half_12_21_φ2 (329430069611/10000000000000 : ℝ)

def half_12_21_φ4 : Fin 4 → ℝ := Fin.snoc half_12_21_φ3 (106453673447/5000000000000 : ℝ)

theorem half_12_21_hF2 : SourcePowerBound (paddedMoment 18 0 2 16 half_12_21_φ4) (74828822002403/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_12_21_φ4 (by norm_num [half_12_21_φ1, half_12_21_φ2, half_12_21_φ3, half_12_21_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_21_φ1, half_12_21_φ2, half_12_21_φ3, half_12_21_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_21_φ1, half_12_21_φ2, half_12_21_φ3, half_12_21_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_12_21_φ1, half_12_21_φ2, half_12_21_φ3, half_12_21_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_12_21_hF1 : SourcePowerBound (paddedMoment 18 0 1 16 half_12_21_φ4) (28276274000801/10000000000000 : ℝ) := by
  have h := padded_second_power (k := 18) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_12_21_φ4 (by norm_num [half_12_21_φ1, half_12_21_φ2, half_12_21_φ3, half_12_21_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_21_φ1, half_12_21_φ2, half_12_21_φ3, half_12_21_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_21_φ1, half_12_21_φ2, half_12_21_φ3, half_12_21_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_12_21_φ1, half_12_21_φ2, half_12_21_φ3, half_12_21_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_12_21_hx4 : SourcePowerBound (powerBoxCross 18 8 16 half_12_21_φ4) (48915355100653/5000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 18) (s := 8) (r := 1) (v := 2) (t := 11) (D := 16)
    (a := (1/22 : ℝ)) (b := (5/22 : ℝ)) (c := (8/11 : ℝ))
    (by norm_num) half_12_21_φ4 (by norm_num [half_12_21_φ1, half_12_21_φ2, half_12_21_φ3, half_12_21_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_21_φ1, half_12_21_φ2, half_12_21_φ3, half_12_21_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_12_21_hF1 half_12_21_hF2 half_11_21
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_12_21_φ1, half_12_21_φ2, half_12_21_φ3, half_12_21_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_21_hx3 : SourcePowerBound (powerBoxCross 18 9 8 half_12_21_φ3) (106579330500681/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 9) (u := 7) (t := 10)
    (D := 8) (ψ := (106453673447/5000000000000 : ℝ)) half_12_21_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_21_φ1, half_12_21_φ2, half_12_21_φ3, half_12_21_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_21_φ1, half_12_21_φ2, half_12_21_φ3, half_12_21_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_21_φ1, half_12_21_φ2, half_12_21_φ3, half_12_21_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_8 half_10_21
    (by simpa only [half_12_21_φ4, show (2:ℝ)*8=16 by norm_num] using half_12_21_hx4)
  exact h.weaken (by norm_num [half_12_21_φ1, half_12_21_φ2, half_12_21_φ3, half_12_21_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_21_hx2 : SourcePowerBound (powerBoxCross 18 10 4 half_12_21_φ2) (29480239783511/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 10) (u := 8) (t := 11)
    (D := 4) (ψ := (329430069611/10000000000000 : ℝ)) half_12_21_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_21_φ1, half_12_21_φ2, half_12_21_φ3, half_12_21_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_21_φ1, half_12_21_φ2, half_12_21_φ3, half_12_21_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_21_φ1, half_12_21_φ2, half_12_21_φ3, half_12_21_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_21 half_11_21
    (by simpa only [half_12_21_φ3, show (2:ℝ)*4=8 by norm_num] using half_12_21_hx3)
  exact h.weaken (by norm_num [half_12_21_φ1, half_12_21_φ2, half_12_21_φ3, half_12_21_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_21_hx1 : SourcePowerBound (powerBoxCross 18 11 2 half_12_21_φ1) (65531285328851/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 11) (u := 9) (t := 12)
    (D := 2) (ψ := (1802934323/50000000000 : ℝ)) half_12_21_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_21_φ1, half_12_21_φ2, half_12_21_φ3, half_12_21_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_21_φ1, half_12_21_φ2, half_12_21_φ3, half_12_21_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_21_φ1, half_12_21_φ2, half_12_21_φ3, half_12_21_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_21 half_12_20
    (by simpa only [half_12_21_φ2, show (2:ℝ)*2=4 by norm_num] using half_12_21_hx2)
  exact h.weaken (by norm_num [half_12_21_φ1, half_12_21_φ2, half_12_21_φ3, half_12_21_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_21 : AdmissibleExponent 18 24 (34734087923671/2500000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 10) (ψ := (187470977071/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_11_21
    (by simpa only [half_12_21_φ1] using half_12_21_hx1)
  exact admissibleExponent_mono h (by norm_num [half_12_21_φ1, half_12_21_φ2, half_12_21_φ3, half_12_21_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_13_21_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (192302204027/5000000000000 : ℝ)

def half_13_21_φ2 : Fin 2 → ℝ := Fin.snoc half_13_21_φ1 (371968405537/10000000000000 : ℝ)

def half_13_21_φ3 : Fin 3 → ℝ := Fin.snoc half_13_21_φ2 (349893155089/10000000000000 : ℝ)

def half_13_21_φ4 : Fin 4 → ℝ := Fin.snoc half_13_21_φ3 (11332530541/400000000000 : ℝ)

theorem half_13_21_hF2 : SourcePowerBound (paddedMoment 18 0 2 16 half_13_21_φ4) (13824251831509/2000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_13_21_φ4 (by norm_num [half_13_21_φ1, half_13_21_φ2, half_13_21_φ3, half_13_21_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_21_φ1, half_13_21_φ2, half_13_21_φ3, half_13_21_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_21_φ1, half_13_21_φ2, half_13_21_φ3, half_13_21_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_13_21_φ1, half_13_21_φ2, half_13_21_φ3, half_13_21_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_13_21_hx4 : SourcePowerBound (powerBoxCross 18 9 16 half_13_21_φ4) (10700076434663/1000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 9) (r := 2) (v := 12) (w := 12) (D := 16)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_13_21_φ4 (by norm_num [half_13_21_φ1, half_13_21_φ2, half_13_21_φ3, half_13_21_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_21_φ1, half_13_21_φ2, half_13_21_φ3, half_13_21_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_13_21_hF2 half_12_21 half_12_21
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_13_21_φ1, half_13_21_φ2, half_13_21_φ3, half_13_21_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_21_hx3 : SourcePowerBound (powerBoxCross 18 10 8 half_13_21_φ3) (23452229148039/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 10) (u := 8) (t := 11)
    (D := 8) (ψ := (11332530541/400000000000 : ℝ)) half_13_21_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_21_φ1, half_13_21_φ2, half_13_21_φ3, half_13_21_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_21_φ1, half_13_21_φ2, half_13_21_φ3, half_13_21_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_21_φ1, half_13_21_φ2, half_13_21_φ3, half_13_21_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_21 half_11_21
    (by simpa only [half_13_21_φ4, show (2:ℝ)*8=16 by norm_num] using half_13_21_hx4)
  exact h.weaken (by norm_num [half_13_21_φ1, half_13_21_φ2, half_13_21_φ3, half_13_21_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_21_hx2 : SourcePowerBound (powerBoxCross 18 11 4 half_13_21_φ2) (32434022862419/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 11) (u := 9) (t := 12)
    (D := 4) (ψ := (349893155089/10000000000000 : ℝ)) half_13_21_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_21_φ1, half_13_21_φ2, half_13_21_φ3, half_13_21_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_21_φ1, half_13_21_φ2, half_13_21_φ3, half_13_21_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_21_φ1, half_13_21_φ2, half_13_21_φ3, half_13_21_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_21 half_12_21
    (by simpa only [half_13_21_φ3, show (2:ℝ)*4=8 by norm_num] using half_13_21_hx3)
  exact h.weaken (by norm_num [half_13_21_φ1, half_13_21_φ2, half_13_21_φ3, half_13_21_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_21_hx1 : SourcePowerBound (powerBoxCross 18 12 2 half_13_21_φ1) (143977402772687/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 12) (u := 10) (t := 13)
    (D := 2) (ψ := (371968405537/10000000000000 : ℝ)) half_13_21_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_21_φ1, half_13_21_φ2, half_13_21_φ3, half_13_21_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_21_φ1, half_13_21_φ2, half_13_21_φ3, half_13_21_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_21_φ1, half_13_21_φ2, half_13_21_φ3, half_13_21_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_21 half_13_20
    (by simpa only [half_13_21_φ2, show (2:ℝ)*2=4 by norm_num] using half_13_21_hx2)
  exact h.weaken (by norm_num [half_13_21_φ1, half_13_21_φ2, half_13_21_φ3, half_13_21_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_21 : AdmissibleExponent 18 26 (152823304157929/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 11) (ψ := (192302204027/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_12_21
    (by simpa only [half_13_21_φ1] using half_13_21_hx1)
  exact admissibleExponent_mono h (by norm_num [half_13_21_φ1, half_13_21_φ2, half_13_21_φ3, half_13_21_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_14_21_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (394360670053/10000000000000 : ℝ)

def half_14_21_φ2 : Fin 2 → ℝ := Fin.snoc half_14_21_φ1 (95749181933/2500000000000 : ℝ)

def half_14_21_φ3 : Fin 3 → ℝ := Fin.snoc half_14_21_φ2 (73452161897/2000000000000 : ℝ)

def half_14_21_φ4 : Fin 4 → ℝ := Fin.snoc half_14_21_φ3 (166057872599/5000000000000 : ℝ)

def half_14_21_φ5 : Fin 5 → ℝ := Fin.snoc half_14_21_φ4 (205580724209/10000000000000 : ℝ)

theorem half_14_21_hF2 : SourcePowerBound (paddedMoment 18 0 2 32 half_14_21_φ5) (84201951489473/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_14_21_φ5 (by norm_num [half_14_21_φ1, half_14_21_φ2, half_14_21_φ3, half_14_21_φ4, half_14_21_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_21_φ1, half_14_21_φ2, half_14_21_φ3, half_14_21_φ4, half_14_21_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_21_φ1, half_14_21_φ2, half_14_21_φ3, half_14_21_φ4, half_14_21_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_14_21_φ1, half_14_21_φ2, half_14_21_φ3, half_14_21_φ4, half_14_21_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_14_21_hx5 : SourcePowerBound (powerBoxCross 18 9 32 half_14_21_φ5) (107722651874887/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 9) (r := 2) (v := 12) (w := 12) (D := 32)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_14_21_φ5 (by norm_num [half_14_21_φ1, half_14_21_φ2, half_14_21_φ3, half_14_21_φ4, half_14_21_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_21_φ1, half_14_21_φ2, half_14_21_φ3, half_14_21_φ4, half_14_21_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_14_21_hF2 half_12_21 half_12_21
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_14_21_φ1, half_14_21_φ2, half_14_21_φ3, half_14_21_φ4, half_14_21_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_21_hx4 : SourcePowerBound (powerBoxCross 18 10 16 half_14_21_φ4) (116492708670631/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 10) (u := 8) (t := 11)
    (D := 16) (ψ := (205580724209/10000000000000 : ℝ)) half_14_21_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_21_φ1, half_14_21_φ2, half_14_21_φ3, half_14_21_φ4, half_14_21_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_21_φ1, half_14_21_φ2, half_14_21_φ3, half_14_21_φ4, half_14_21_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_21_φ1, half_14_21_φ2, half_14_21_φ3, half_14_21_φ4, half_14_21_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_21 half_11_21
    (by simpa only [half_14_21_φ5, show (2:ℝ)*16=32 by norm_num] using half_14_21_hx5)
  exact h.weaken (by norm_num [half_14_21_φ1, half_14_21_φ2, half_14_21_φ3, half_14_21_φ4, half_14_21_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_21_hx3 : SourcePowerBound (powerBoxCross 18 11 8 half_14_21_φ3) (64094460555087/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 11) (u := 9) (t := 12)
    (D := 8) (ψ := (166057872599/5000000000000 : ℝ)) half_14_21_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_21_φ1, half_14_21_φ2, half_14_21_φ3, half_14_21_φ4, half_14_21_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_21_φ1, half_14_21_φ2, half_14_21_φ3, half_14_21_φ4, half_14_21_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_21_φ1, half_14_21_φ2, half_14_21_φ3, half_14_21_φ4, half_14_21_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_21 half_12_21
    (by simpa only [half_14_21_φ4, show (2:ℝ)*8=16 by norm_num] using half_14_21_hx4)
  exact h.weaken (by norm_num [half_14_21_φ1, half_14_21_φ2, half_14_21_φ3, half_14_21_φ4, half_14_21_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_21_hx2 : SourcePowerBound (powerBoxCross 18 12 4 half_14_21_φ2) (8863431059401/625000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 12) (u := 10) (t := 13)
    (D := 4) (ψ := (73452161897/2000000000000 : ℝ)) half_14_21_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_21_φ1, half_14_21_φ2, half_14_21_φ3, half_14_21_φ4, half_14_21_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_21_φ1, half_14_21_φ2, half_14_21_φ3, half_14_21_φ4, half_14_21_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_21_φ1, half_14_21_φ2, half_14_21_φ3, half_14_21_φ4, half_14_21_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_21 half_13_21
    (by simpa only [half_14_21_φ3, show (2:ℝ)*4=8 by norm_num] using half_14_21_hx3)
  exact h.weaken (by norm_num [half_14_21_φ1, half_14_21_φ2, half_14_21_φ3, half_14_21_φ4, half_14_21_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_21_hx1 : SourcePowerBound (powerBoxCross 18 13 2 half_14_21_φ1) (157190914765253/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 13) (u := 11) (t := 14)
    (D := 2) (ψ := (95749181933/2500000000000 : ℝ)) half_14_21_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_21_φ1, half_14_21_φ2, half_14_21_φ3, half_14_21_φ4, half_14_21_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_21_φ1, half_14_21_φ2, half_14_21_φ3, half_14_21_φ4, half_14_21_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_21_φ1, half_14_21_φ2, half_14_21_φ3, half_14_21_φ4, half_14_21_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_21 half_14_20
    (by simpa only [half_14_21_φ2, show (2:ℝ)*2=4 by norm_num] using half_14_21_hx2)
  exact h.weaken (by norm_num [half_14_21_φ1, half_14_21_φ2, half_14_21_φ3, half_14_21_φ4, half_14_21_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_21 : AdmissibleExponent 18 28 (83524965758289/5000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 12) (ψ := (394360670053/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_13_21
    (by simpa only [half_14_21_φ1] using half_14_21_hx1)
  exact admissibleExponent_mono h (by norm_num [half_14_21_φ1, half_14_21_φ2, half_14_21_φ3, half_14_21_φ4, half_14_21_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_15_21_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (201818795611/5000000000000 : ℝ)

def half_15_21_φ2 : Fin 2 → ℝ := Fin.snoc half_15_21_φ1 (392987545029/10000000000000 : ℝ)

def half_15_21_φ3 : Fin 3 → ℝ := Fin.snoc half_15_21_φ2 (189728757369/5000000000000 : ℝ)

def half_15_21_φ4 : Fin 4 → ℝ := Fin.snoc half_15_21_φ3 (177612531837/5000000000000 : ℝ)

def half_15_21_φ5 : Fin 5 → ℝ := Fin.snoc half_15_21_φ4 (71072682313/2500000000000 : ℝ)

theorem half_15_21_hF2 : SourcePowerBound (paddedMoment 18 0 2 32 half_15_21_φ5) (15480895872067/2000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_15_21_φ5 (by norm_num [half_15_21_φ1, half_15_21_φ2, half_15_21_φ3, half_15_21_φ4, half_15_21_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_21_φ1, half_15_21_φ2, half_15_21_φ3, half_15_21_φ4, half_15_21_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_21_φ1, half_15_21_φ2, half_15_21_φ3, half_15_21_φ4, half_15_21_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_15_21_φ1, half_15_21_φ2, half_15_21_φ3, half_15_21_φ4, half_15_21_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_15_21_hx5 : SourcePowerBound (powerBoxCross 18 10 32 half_15_21_φ5) (116069577244099/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 10) (r := 2) (v := 13) (w := 14) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_15_21_φ5 (by norm_num [half_15_21_φ1, half_15_21_φ2, half_15_21_φ3, half_15_21_φ4, half_15_21_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_21_φ1, half_15_21_φ2, half_15_21_φ3, half_15_21_φ4, half_15_21_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_15_21_hF2 half_13_21 half_14_21
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_15_21_φ1, half_15_21_φ2, half_15_21_φ3, half_15_21_φ4, half_15_21_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_21_hx4 : SourcePowerBound (powerBoxCross 18 11 16 half_15_21_φ4) (12654989546279/1000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 11) (u := 9) (t := 12)
    (D := 16) (ψ := (71072682313/2500000000000 : ℝ)) half_15_21_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_21_φ1, half_15_21_φ2, half_15_21_φ3, half_15_21_φ4, half_15_21_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_21_φ1, half_15_21_φ2, half_15_21_φ3, half_15_21_φ4, half_15_21_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_21_φ1, half_15_21_φ2, half_15_21_φ3, half_15_21_φ4, half_15_21_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_21 half_12_21
    (by simpa only [half_15_21_φ5, show (2:ℝ)*16=32 by norm_num] using half_15_21_hx5)
  exact h.weaken (by norm_num [half_15_21_φ1, half_15_21_φ2, half_15_21_φ3, half_15_21_φ4, half_15_21_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_21_hx3 : SourcePowerBound (powerBoxCross 18 12 8 half_15_21_φ3) (139433118611183/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 12) (u := 10) (t := 13)
    (D := 8) (ψ := (177612531837/5000000000000 : ℝ)) half_15_21_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_21_φ1, half_15_21_φ2, half_15_21_φ3, half_15_21_φ4, half_15_21_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_21_φ1, half_15_21_φ2, half_15_21_φ3, half_15_21_φ4, half_15_21_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_21_φ1, half_15_21_φ2, half_15_21_φ3, half_15_21_φ4, half_15_21_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_21 half_13_21
    (by simpa only [half_15_21_φ4, show (2:ℝ)*8=16 by norm_num] using half_15_21_hx4)
  exact h.weaken (by norm_num [half_15_21_φ1, half_15_21_φ2, half_15_21_φ3, half_15_21_φ4, half_15_21_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_21_hx2 : SourcePowerBound (powerBoxCross 18 13 4 half_15_21_φ2) (154180164102479/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 13) (u := 11) (t := 14)
    (D := 4) (ψ := (189728757369/5000000000000 : ℝ)) half_15_21_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_21_φ1, half_15_21_φ2, half_15_21_φ3, half_15_21_φ4, half_15_21_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_21_φ1, half_15_21_φ2, half_15_21_φ3, half_15_21_φ4, half_15_21_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_21_φ1, half_15_21_φ2, half_15_21_φ3, half_15_21_φ4, half_15_21_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_21 half_14_21
    (by simpa only [half_15_21_φ3, show (2:ℝ)*4=8 by norm_num] using half_15_21_hx3)
  exact h.weaken (by norm_num [half_15_21_φ1, half_15_21_φ2, half_15_21_φ3, half_15_21_φ4, half_15_21_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_21_hx1 : SourcePowerBound (powerBoxCross 18 14 2 half_15_21_φ1) (170710805910701/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 14) (u := 12) (t := 15)
    (D := 2) (ψ := (392987545029/10000000000000 : ℝ)) half_15_21_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_21_φ1, half_15_21_φ2, half_15_21_φ3, half_15_21_φ4, half_15_21_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_21_φ1, half_15_21_φ2, half_15_21_φ3, half_15_21_φ4, half_15_21_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_21_φ1, half_15_21_φ2, half_15_21_φ3, half_15_21_φ4, half_15_21_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_13_21 half_15_20
    (by simpa only [half_15_21_φ2, show (2:ℝ)*2=4 by norm_num] using half_15_21_hx2)
  exact h.weaken (by norm_num [half_15_21_φ1, half_15_21_φ2, half_15_21_φ3, half_15_21_φ4, half_15_21_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_21 : AdmissibleExponent 18 30 (36321804174739/2000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 13) (ψ := (201818795611/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_14_21
    (by simpa only [half_15_21_φ1] using half_15_21_hx1)
  exact admissibleExponent_mono h (by norm_num [half_15_21_φ1, half_15_21_φ2, half_15_21_φ3, half_15_21_φ4, half_15_21_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_16_21_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (4128884413/100000000000 : ℝ)

def half_16_21_φ2 : Fin 2 → ℝ := Fin.snoc half_16_21_φ1 (8053888139/200000000000 : ℝ)

def half_16_21_φ3 : Fin 3 → ℝ := Fin.snoc half_16_21_φ2 (391097304241/10000000000000 : ℝ)

def half_16_21_φ4 : Fin 4 → ℝ := Fin.snoc half_16_21_φ3 (93525615197/2500000000000 : ℝ)

def half_16_21_φ5 : Fin 5 → ℝ := Fin.snoc half_16_21_φ4 (168150695137/5000000000000 : ℝ)

def half_16_21_φ6 : Fin 6 → ℝ := Fin.snoc half_16_21_φ5 (41644913269/2000000000000 : ℝ)

theorem half_16_21_hF2 : SourcePowerBound (paddedMoment 18 0 2 64 half_16_21_φ6) (45804631467601/5000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 6) (r := 0) (D := 64)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_16_21_φ6 (by norm_num [half_16_21_φ1, half_16_21_φ2, half_16_21_φ3, half_16_21_φ4, half_16_21_φ5, half_16_21_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_21_φ1, half_16_21_φ2, half_16_21_φ3, half_16_21_φ4, half_16_21_φ5, half_16_21_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_21_φ1, half_16_21_φ2, half_16_21_φ3, half_16_21_φ4, half_16_21_φ5, half_16_21_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_16_21_φ1, half_16_21_φ2, half_16_21_φ3, half_16_21_φ4, half_16_21_φ5, half_16_21_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_16_21_hx6 : SourcePowerBound (powerBoxCross 18 10 64 half_16_21_φ6) (23192160103047/2000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 10) (r := 2) (v := 13) (w := 14) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_16_21_φ6 (by norm_num [half_16_21_φ1, half_16_21_φ2, half_16_21_φ3, half_16_21_φ4, half_16_21_φ5, half_16_21_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_21_φ1, half_16_21_φ2, half_16_21_φ3, half_16_21_φ4, half_16_21_φ5, half_16_21_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_16_21_hF2 half_13_21 half_14_21
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_16_21_φ1, half_16_21_φ2, half_16_21_φ3, half_16_21_φ4, half_16_21_φ5, half_16_21_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_21_hx5 : SourcePowerBound (powerBoxCross 18 11 32 half_16_21_φ5) (62406931293871/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 5) (s := 11) (u := 9) (t := 12)
    (D := 32) (ψ := (41644913269/2000000000000 : ℝ)) half_16_21_φ5
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_21_φ1, half_16_21_φ2, half_16_21_φ3, half_16_21_φ4, half_16_21_φ5, half_16_21_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_21_φ1, half_16_21_φ2, half_16_21_φ3, half_16_21_φ4, half_16_21_φ5, half_16_21_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_21_φ1, half_16_21_φ2, half_16_21_φ3, half_16_21_φ4, half_16_21_φ5, half_16_21_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_21 half_12_21
    (by simpa only [half_16_21_φ6, show (2:ℝ)*32=64 by norm_num] using half_16_21_hx6)
  exact h.weaken (by norm_num [half_16_21_φ1, half_16_21_φ2, half_16_21_φ3, half_16_21_φ4, half_16_21_φ5, half_16_21_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_21_hx4 : SourcePowerBound (powerBoxCross 18 12 16 half_16_21_φ4) (68417037326003/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 12) (u := 10) (t := 13)
    (D := 16) (ψ := (168150695137/5000000000000 : ℝ)) half_16_21_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_21_φ1, half_16_21_φ2, half_16_21_φ3, half_16_21_φ4, half_16_21_φ5, half_16_21_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_21_φ1, half_16_21_φ2, half_16_21_φ3, half_16_21_φ4, half_16_21_φ5, half_16_21_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_21_φ1, half_16_21_φ2, half_16_21_φ3, half_16_21_φ4, half_16_21_φ5, half_16_21_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_21 half_13_21
    (by simpa only [half_16_21_φ5, show (2:ℝ)*16=32 by norm_num] using half_16_21_hx5)
  exact h.weaken (by norm_num [half_16_21_φ1, half_16_21_φ2, half_16_21_φ3, half_16_21_φ4, half_16_21_φ5, half_16_21_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_21_hx3 : SourcePowerBound (powerBoxCross 18 13 8 half_16_21_φ3) (150908608245379/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 13) (u := 11) (t := 14)
    (D := 8) (ψ := (93525615197/2500000000000 : ℝ)) half_16_21_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_21_φ1, half_16_21_φ2, half_16_21_φ3, half_16_21_φ4, half_16_21_φ5, half_16_21_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_21_φ1, half_16_21_φ2, half_16_21_φ3, half_16_21_φ4, half_16_21_φ5, half_16_21_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_21_φ1, half_16_21_φ2, half_16_21_φ3, half_16_21_φ4, half_16_21_φ5, half_16_21_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_21 half_14_21
    (by simpa only [half_16_21_φ4, show (2:ℝ)*8=16 by norm_num] using half_16_21_hx4)
  exact h.weaken (by norm_num [half_16_21_φ1, half_16_21_φ2, half_16_21_φ3, half_16_21_φ4, half_16_21_φ5, half_16_21_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_21_hx2 : SourcePowerBound (powerBoxCross 18 14 4 half_16_21_φ2) (83404608263411/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 14) (u := 12) (t := 15)
    (D := 4) (ψ := (391097304241/10000000000000 : ℝ)) half_16_21_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_21_φ1, half_16_21_φ2, half_16_21_φ3, half_16_21_φ4, half_16_21_φ5, half_16_21_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_21_φ1, half_16_21_φ2, half_16_21_φ3, half_16_21_φ4, half_16_21_φ5, half_16_21_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_21_φ1, half_16_21_φ2, half_16_21_φ3, half_16_21_φ4, half_16_21_φ5, half_16_21_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_13_21 half_15_21
    (by simpa only [half_16_21_φ3, show (2:ℝ)*4=8 by norm_num] using half_16_21_hx3)
  exact h.weaken (by norm_num [half_16_21_φ1, half_16_21_φ2, half_16_21_φ3, half_16_21_φ4, half_16_21_φ5, half_16_21_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_21_hx1 : SourcePowerBound (powerBoxCross 18 15 2 half_16_21_φ1) (184523482759549/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 15) (u := 13) (t := 16)
    (D := 2) (ψ := (8053888139/200000000000 : ℝ)) half_16_21_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_21_φ1, half_16_21_φ2, half_16_21_φ3, half_16_21_φ4, half_16_21_φ5, half_16_21_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_21_φ1, half_16_21_φ2, half_16_21_φ3, half_16_21_φ4, half_16_21_φ5, half_16_21_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_21_φ1, half_16_21_φ2, half_16_21_φ3, half_16_21_φ4, half_16_21_φ5, half_16_21_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_14_21 half_16_20
    (by simpa only [half_16_21_φ2, show (2:ℝ)*2=4 by norm_num] using half_16_21_hx2)
  exact h.weaken (by norm_num [half_16_21_φ1, half_16_21_φ2, half_16_21_φ3, half_16_21_φ4, half_16_21_φ5, half_16_21_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_21 : AdmissibleExponent 18 32 (196497247557249/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 14) (ψ := (4128884413/100000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_15_21
    (by simpa only [half_16_21_φ1] using half_16_21_hx1)
  exact admissibleExponent_mono h (by norm_num [half_16_21_φ1, half_16_21_φ2, half_16_21_φ3, half_16_21_φ4, half_16_21_φ5, half_16_21_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_17_21_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (16873010063/400000000000 : ℝ)

def half_17_21_φ2 : Fin 2 → ℝ := Fin.snoc half_17_21_φ1 (41201077759/1000000000000 : ℝ)

def half_17_21_φ3 : Fin 3 → ℝ := Fin.snoc half_17_21_φ2 (100280933509/2500000000000 : ℝ)

def half_17_21_φ4 : Fin 4 → ℝ := Fin.snoc half_17_21_φ3 (387122416241/10000000000000 : ℝ)

def half_17_21_φ5 : Fin 5 → ℝ := Fin.snoc half_17_21_φ4 (90334908001/2500000000000 : ℝ)

def half_17_21_φ6 : Fin 6 → ℝ := Fin.snoc half_17_21_φ5 (289183337657/10000000000000 : ℝ)

theorem half_17_21_hF2 : SourcePowerBound (paddedMoment 18 0 2 64 half_17_21_φ6) (84097137395747/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 6) (r := 0) (D := 64)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_17_21_φ6 (by norm_num [half_17_21_φ1, half_17_21_φ2, half_17_21_φ3, half_17_21_φ4, half_17_21_φ5, half_17_21_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_21_φ1, half_17_21_φ2, half_17_21_φ3, half_17_21_φ4, half_17_21_φ5, half_17_21_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_21_φ1, half_17_21_φ2, half_17_21_φ3, half_17_21_φ4, half_17_21_φ5, half_17_21_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_17_21_φ1, half_17_21_φ2, half_17_21_φ3, half_17_21_φ4, half_17_21_φ5, half_17_21_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_17_21_hx6 : SourcePowerBound (powerBoxCross 18 11 64 half_17_21_φ6) (123464034503827/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 11) (r := 2) (v := 14) (w := 15) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_17_21_φ6 (by norm_num [half_17_21_φ1, half_17_21_φ2, half_17_21_φ3, half_17_21_φ4, half_17_21_φ5, half_17_21_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_21_φ1, half_17_21_φ2, half_17_21_φ3, half_17_21_φ4, half_17_21_φ5, half_17_21_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_17_21_hF2 half_14_21 half_15_21
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_17_21_φ1, half_17_21_φ2, half_17_21_φ3, half_17_21_φ4, half_17_21_φ5, half_17_21_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_21_hx5 : SourcePowerBound (powerBoxCross 18 12 32 half_17_21_φ5) (67082677620391/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 5) (s := 12) (u := 10) (t := 13)
    (D := 32) (ψ := (289183337657/10000000000000 : ℝ)) half_17_21_φ5
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_21_φ1, half_17_21_φ2, half_17_21_φ3, half_17_21_φ4, half_17_21_φ5, half_17_21_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_21_φ1, half_17_21_φ2, half_17_21_φ3, half_17_21_φ4, half_17_21_φ5, half_17_21_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_21_φ1, half_17_21_φ2, half_17_21_φ3, half_17_21_φ4, half_17_21_φ5, half_17_21_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_21 half_13_21
    (by simpa only [half_17_21_φ6, show (2:ℝ)*32=64 by norm_num] using half_17_21_hx6)
  exact h.weaken (by norm_num [half_17_21_φ1, half_17_21_φ2, half_17_21_φ3, half_17_21_φ4, half_17_21_φ5, half_17_21_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_21_hx4 : SourcePowerBound (powerBoxCross 18 13 16 half_17_21_φ4) (147426914771967/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 13) (u := 11) (t := 14)
    (D := 16) (ψ := (90334908001/2500000000000 : ℝ)) half_17_21_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_21_φ1, half_17_21_φ2, half_17_21_φ3, half_17_21_φ4, half_17_21_φ5, half_17_21_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_21_φ1, half_17_21_φ2, half_17_21_φ3, half_17_21_φ4, half_17_21_φ5, half_17_21_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_21_φ1, half_17_21_φ2, half_17_21_φ3, half_17_21_φ4, half_17_21_φ5, half_17_21_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_21 half_14_21
    (by simpa only [half_17_21_φ5, show (2:ℝ)*16=32 by norm_num] using half_17_21_hx5)
  exact h.weaken (by norm_num [half_17_21_φ1, half_17_21_φ2, half_17_21_φ3, half_17_21_φ4, half_17_21_φ5, half_17_21_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_21_hx3 : SourcePowerBound (powerBoxCross 18 14 8 half_17_21_φ3) (5082682761499/312500000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 14) (u := 12) (t := 15)
    (D := 8) (ψ := (387122416241/10000000000000 : ℝ)) half_17_21_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_21_φ1, half_17_21_φ2, half_17_21_φ3, half_17_21_φ4, half_17_21_φ5, half_17_21_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_21_φ1, half_17_21_φ2, half_17_21_φ3, half_17_21_φ4, half_17_21_φ5, half_17_21_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_21_φ1, half_17_21_φ2, half_17_21_φ3, half_17_21_φ4, half_17_21_φ5, half_17_21_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_13_21 half_15_21
    (by simpa only [half_17_21_φ4, show (2:ℝ)*8=16 by norm_num] using half_17_21_hx4)
  exact h.weaken (by norm_num [half_17_21_φ1, half_17_21_φ2, half_17_21_φ3, half_17_21_φ4, half_17_21_φ5, half_17_21_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_21_hx2 : SourcePowerBound (powerBoxCross 18 15 4 half_17_21_φ2) (179706787891943/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 15) (u := 13) (t := 16)
    (D := 4) (ψ := (100280933509/2500000000000 : ℝ)) half_17_21_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_21_φ1, half_17_21_φ2, half_17_21_φ3, half_17_21_φ4, half_17_21_φ5, half_17_21_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_21_φ1, half_17_21_φ2, half_17_21_φ3, half_17_21_φ4, half_17_21_φ5, half_17_21_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_21_φ1, half_17_21_φ2, half_17_21_φ3, half_17_21_φ4, half_17_21_φ5, half_17_21_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_14_21 half_16_21
    (by simpa only [half_17_21_φ3, show (2:ℝ)*4=8 by norm_num] using half_17_21_hx3)
  exact h.weaken (by norm_num [half_17_21_φ1, half_17_21_φ2, half_17_21_φ3, half_17_21_φ4, half_17_21_φ5, half_17_21_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_21_hx1 : SourcePowerBound (powerBoxCross 18 16 2 half_17_21_φ1) (198630322720377/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 16) (u := 14) (t := 17)
    (D := 2) (ψ := (41201077759/1000000000000 : ℝ)) half_17_21_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_21_φ1, half_17_21_φ2, half_17_21_φ3, half_17_21_φ4, half_17_21_φ5, half_17_21_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_21_φ1, half_17_21_φ2, half_17_21_φ3, half_17_21_φ4, half_17_21_φ5, half_17_21_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_21_φ1, half_17_21_φ2, half_17_21_φ3, half_17_21_φ4, half_17_21_φ5, half_17_21_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_15_21 half_17_20
    (by simpa only [half_17_21_φ2, show (2:ℝ)*2=4 by norm_num] using half_17_21_hx2)
  exact h.weaken (by norm_num [half_17_21_φ1, half_17_21_φ2, half_17_21_φ3, half_17_21_φ4, half_17_21_φ5, half_17_21_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_21 : AdmissibleExponent 18 34 (105853452759601/5000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 15) (ψ := (16873010063/400000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_16_21
    (by simpa only [half_17_21_φ1] using half_17_21_hx1)
  exact admissibleExponent_mono h (by norm_num [half_17_21_φ1, half_17_21_φ2, half_17_21_φ3, half_17_21_φ4, half_17_21_φ5, half_17_21_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])


end Waring.SeedCompletionHigher18SimpleSeeds
