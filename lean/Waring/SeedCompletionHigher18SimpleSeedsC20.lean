import Waring.SeedCompletionHigher18SimpleSeedsC19

noncomputable section
set_option maxHeartbeats 2000000
namespace Waring.SeedCompletionHigher18SimpleSeeds
open SmoothMoments FirstStageTransport SeedCompletionNaturalBox
open SeedCompletionSourceBounds SeedCompletionPaddedSource SeedCompletionGeneralTerminal
open PolicyCompletionMajorPowerRanges

def half_9_20_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (42979853791/1250000000000 : ℝ)

def half_9_20_φ2 : Fin 2 → ℝ := Fin.snoc half_9_20_φ1 (308345143257/10000000000000 : ℝ)

def half_9_20_φ3 : Fin 3 → ℝ := Fin.snoc half_9_20_φ2 (67222953977/5000000000000 : ℝ)

theorem half_9_20_hF2 : SourcePowerBound (paddedMoment 18 0 2 8 half_9_20_φ3) (69881876041511/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_20_φ3 (by norm_num [half_9_20_φ1, half_9_20_φ2, half_9_20_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_20_φ1, half_9_20_φ2, half_9_20_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_20_φ1, half_9_20_φ2, half_9_20_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_20_φ1, half_9_20_φ2, half_9_20_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_9_20_hF1 : SourcePowerBound (paddedMoment 18 0 1 8 half_9_20_φ3) (26627292013837/10000000000000 : ℝ) := by
  have h := padded_second_power (k := 18) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_20_φ3 (by norm_num [half_9_20_φ1, half_9_20_φ2, half_9_20_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_20_φ1, half_9_20_φ2, half_9_20_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_20_φ1, half_9_20_φ2, half_9_20_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_20_φ1, half_9_20_φ2, half_9_20_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_9_20_hx3 : SourcePowerBound (powerBoxCross 18 6 8 half_9_20_φ3) (76993037108453/10000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 18) (s := 6) (r := 1) (v := 2) (t := 10) (D := 8)
    (a := (3/10 : ℝ)) (b := (1/10 : ℝ)) (c := (3/5 : ℝ))
    (by norm_num) half_9_20_φ3 (by norm_num [half_9_20_φ1, half_9_20_φ2, half_9_20_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_20_φ1, half_9_20_φ2, half_9_20_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_9_20_hF1 half_9_20_hF2 half_10_19
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_9_20_φ1, half_9_20_φ2, half_9_20_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_9_20_hx2 : SourcePowerBound (powerBoxCross 18 7 4 half_9_20_φ2) (21067355449301/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 7) (u := 5) (t := 8)
    (D := 4) (ψ := (67222953977/5000000000000 : ℝ)) half_9_20_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_20_φ1, half_9_20_φ2, half_9_20_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_20_φ1, half_9_20_φ2, half_9_20_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_20_φ1, half_9_20_φ2, half_9_20_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_6 SeedCompletionEven18SecondSeeds.degree18_half_8
    (by simpa only [half_9_20_φ3, show (2:ℝ)*4=8 by norm_num] using half_9_20_hx3)
  exact h.weaken (by norm_num [half_9_20_φ1, half_9_20_φ2, half_9_20_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_9_20_hx1 : SourcePowerBound (powerBoxCross 18 8 2 half_9_20_φ1) (94174798046369/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 8) (u := 6) (t := 9)
    (D := 2) (ψ := (308345143257/10000000000000 : ℝ)) half_9_20_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_20_φ1, half_9_20_φ2, half_9_20_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_20_φ1, half_9_20_φ2, half_9_20_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_20_φ1, half_9_20_φ2, half_9_20_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_7 half_9_19
    (by simpa only [half_9_20_φ2, show (2:ℝ)*2=4 by norm_num] using half_9_20_hx2)
  exact h.weaken (by norm_num [half_9_20_φ1, half_9_20_φ2, half_9_20_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_9_20 : AdmissibleExponent 18 18 (99332380501289/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 7) (ψ := (42979853791/1250000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_8
    (by simpa only [half_9_20_φ1] using half_9_20_hx1)
  exact admissibleExponent_mono h (by norm_num [half_9_20_φ1, half_9_20_φ2, half_9_20_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_10_20_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (353748845759/10000000000000 : ℝ)

def half_10_20_φ2 : Fin 2 → ℝ := Fin.snoc half_10_20_φ1 (6585131331/200000000000 : ℝ)

def half_10_20_φ3 : Fin 3 → ℝ := Fin.snoc half_10_20_φ2 (114969390427/5000000000000 : ℝ)

theorem half_10_20_hF2 : SourcePowerBound (paddedMoment 18 0 2 8 half_10_20_φ3) (63439846148687/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_10_20_φ3 (by norm_num [half_10_20_φ1, half_10_20_φ2, half_10_20_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_20_φ1, half_10_20_φ2, half_10_20_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_20_φ1, half_10_20_φ2, half_10_20_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_10_20_φ1, half_10_20_φ2, half_10_20_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_10_20_hx3 : SourcePowerBound (powerBoxCross 18 7 8 half_10_20_φ3) (2702434818251/312500000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 7) (r := 2) (v := 9) (w := 10) (D := 8)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_10_20_φ3 (by norm_num [half_10_20_φ1, half_10_20_φ2, half_10_20_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_20_φ1, half_10_20_φ2, half_10_20_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_10_20_hF2 half_9_20 half_10_19
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_10_20_φ1, half_10_20_φ2, half_10_20_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_20_hx2 : SourcePowerBound (powerBoxCross 18 8 4 half_10_20_φ2) (9520197573859/1000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 8) (u := 6) (t := 9)
    (D := 4) (ψ := (114969390427/5000000000000 : ℝ)) half_10_20_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_20_φ1, half_10_20_φ2, half_10_20_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_20_φ1, half_10_20_φ2, half_10_20_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_20_φ1, half_10_20_φ2, half_10_20_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_7 half_9_20
    (by simpa only [half_10_20_φ3, show (2:ℝ)*4=8 by norm_num] using half_10_20_hx3)
  exact h.weaken (by norm_num [half_10_20_φ1, half_10_20_φ2, half_10_20_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_20_hx1 : SourcePowerBound (powerBoxCross 18 9 2 half_10_20_φ1) (5308612892609/500000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 9) (u := 7) (t := 10)
    (D := 2) (ψ := (6585131331/200000000000 : ℝ)) half_10_20_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_20_φ1, half_10_20_φ2, half_10_20_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_20_φ1, half_10_20_φ2, half_10_20_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_20_φ1, half_10_20_φ2, half_10_20_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_8 half_10_19
    (by simpa only [half_10_20_φ2, show (2:ℝ)*2=4 by norm_num] using half_10_20_hx2)
  exact h.weaken (by norm_num [half_10_20_φ1, half_10_20_φ2, half_10_20_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_20 : AdmissibleExponent 18 20 (112185988230083/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 8) (ψ := (353748845759/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_9_20
    (by simpa only [half_10_20_φ1] using half_10_20_hx1)
  exact admissibleExponent_mono h (by norm_num [half_10_20_φ1, half_10_20_φ2, half_10_20_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_11_20_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (9118703339/250000000000 : ℝ)

def half_11_20_φ2 : Fin 2 → ℝ := Fin.snoc half_11_20_φ1 (86598714309/2500000000000 : ℝ)

def half_11_20_φ3 : Fin 3 → ℝ := Fin.snoc half_11_20_φ2 (294728491219/10000000000000 : ℝ)

theorem half_11_20_hF2 : SourcePowerBound (paddedMoment 18 0 2 8 half_11_20_φ3) (11740110883447/2000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_11_20_φ3 (by norm_num [half_11_20_φ1, half_11_20_φ2, half_11_20_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_20_φ1, half_11_20_φ2, half_11_20_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_20_φ1, half_11_20_φ2, half_11_20_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_11_20_φ1, half_11_20_φ2, half_11_20_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_11_20_hx3 : SourcePowerBound (powerBoxCross 18 8 8 half_11_20_φ3) (48144376055111/5000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 8) (r := 2) (v := 10) (w := 11) (D := 8)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_11_20_φ3 (by norm_num [half_11_20_φ1, half_11_20_φ2, half_11_20_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_20_φ1, half_11_20_φ2, half_11_20_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_11_20_hF2 half_10_20 half_11_19
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_11_20_φ1, half_11_20_φ2, half_11_20_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_20_hx2 : SourcePowerBound (powerBoxCross 18 9 4 half_11_20_φ2) (53207052236381/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 9) (u := 7) (t := 10)
    (D := 4) (ψ := (294728491219/10000000000000 : ℝ)) half_11_20_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_20_φ1, half_11_20_φ2, half_11_20_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_20_φ1, half_11_20_φ2, half_11_20_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_20_φ1, half_11_20_φ2, half_11_20_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_8 half_10_20
    (by simpa only [half_11_20_φ3, show (2:ℝ)*4=8 by norm_num] using half_11_20_hx3)
  exact h.weaken (by norm_num [half_11_20_φ1, half_11_20_φ2, half_11_20_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_20_hx1 : SourcePowerBound (powerBoxCross 18 10 2 half_11_20_φ1) (118458773381797/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 10) (u := 8) (t := 11)
    (D := 2) (ψ := (86598714309/2500000000000 : ℝ)) half_11_20_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_20_φ1, half_11_20_φ2, half_11_20_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_20_φ1, half_11_20_φ2, half_11_20_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_20_φ1, half_11_20_φ2, half_11_20_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_20 half_11_19
    (by simpa only [half_11_20_φ2, show (2:ℝ)*2=4 by norm_num] using half_11_20_hx2)
  exact h.weaken (by norm_num [half_11_20_φ1, half_11_20_φ2, half_11_20_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_20 : AdmissibleExponent 18 22 (125388987919437/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 9) (ψ := (9118703339/250000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_10_20
    (by simpa only [half_11_20_φ1] using half_11_20_hx1)
  exact admissibleExponent_mono h (by norm_num [half_11_20_φ1, half_11_20_φ2, half_11_20_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_12_20_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (187470977083/5000000000000 : ℝ)

def half_12_20_φ2 : Fin 2 → ℝ := Fin.snoc half_12_20_φ1 (360586864601/10000000000000 : ℝ)

def half_12_20_φ3 : Fin 3 → ℝ := Fin.snoc half_12_20_φ2 (329430069613/10000000000000 : ℝ)

def half_12_20_φ4 : Fin 4 → ℝ := Fin.snoc half_12_20_φ3 (42581469381/2000000000000 : ℝ)

theorem half_12_20_hF2 : SourcePowerBound (paddedMoment 18 0 2 16 half_12_20_φ4) (14965764400093/2000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_12_20_φ4 (by norm_num [half_12_20_φ1, half_12_20_φ2, half_12_20_φ3, half_12_20_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_20_φ1, half_12_20_φ2, half_12_20_φ3, half_12_20_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_20_φ1, half_12_20_φ2, half_12_20_φ3, half_12_20_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_12_20_φ1, half_12_20_φ2, half_12_20_φ3, half_12_20_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_12_20_hF1 : SourcePowerBound (paddedMoment 18 0 1 16 half_12_20_φ4) (5655254800031/2000000000000 : ℝ) := by
  have h := padded_second_power (k := 18) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_12_20_φ4 (by norm_num [half_12_20_φ1, half_12_20_φ2, half_12_20_φ3, half_12_20_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_20_φ1, half_12_20_φ2, half_12_20_φ3, half_12_20_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_20_φ1, half_12_20_φ2, half_12_20_φ3, half_12_20_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_12_20_φ1, half_12_20_φ2, half_12_20_φ3, half_12_20_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_12_20_hx4 : SourcePowerBound (powerBoxCross 18 8 16 half_12_20_φ4) (48915355100259/5000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 18) (s := 8) (r := 1) (v := 2) (t := 11) (D := 16)
    (a := (1/22 : ℝ)) (b := (5/22 : ℝ)) (c := (8/11 : ℝ))
    (by norm_num) half_12_20_φ4 (by norm_num [half_12_20_φ1, half_12_20_φ2, half_12_20_φ3, half_12_20_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_20_φ1, half_12_20_φ2, half_12_20_φ3, half_12_20_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_12_20_hF1 half_12_20_hF2 half_11_20
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_12_20_φ1, half_12_20_φ2, half_12_20_φ3, half_12_20_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_20_hx3 : SourcePowerBound (powerBoxCross 18 9 8 half_12_20_φ3) (53289665249997/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 9) (u := 7) (t := 10)
    (D := 8) (ψ := (42581469381/2000000000000 : ℝ)) half_12_20_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_20_φ1, half_12_20_φ2, half_12_20_φ3, half_12_20_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_20_φ1, half_12_20_φ2, half_12_20_φ3, half_12_20_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_20_φ1, half_12_20_φ2, half_12_20_φ3, half_12_20_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_8 half_10_20
    (by simpa only [half_12_20_φ4, show (2:ℝ)*8=16 by norm_num] using half_12_20_hx4)
  exact h.weaken (by norm_num [half_12_20_φ1, half_12_20_φ2, half_12_20_φ3, half_12_20_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_20_hx2 : SourcePowerBound (powerBoxCross 18 10 4 half_12_20_φ2) (14740119891671/1250000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 10) (u := 8) (t := 11)
    (D := 4) (ψ := (329430069613/10000000000000 : ℝ)) half_12_20_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_20_φ1, half_12_20_φ2, half_12_20_φ3, half_12_20_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_20_φ1, half_12_20_φ2, half_12_20_φ3, half_12_20_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_20_φ1, half_12_20_φ2, half_12_20_φ3, half_12_20_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_20 half_11_20
    (by simpa only [half_12_20_φ3, show (2:ℝ)*4=8 by norm_num] using half_12_20_hx3)
  exact h.weaken (by norm_num [half_12_20_φ1, half_12_20_φ2, half_12_20_φ3, half_12_20_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_20_hx1 : SourcePowerBound (powerBoxCross 18 11 2 half_12_20_φ1) (65531285328737/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 11) (u := 9) (t := 12)
    (D := 2) (ψ := (360586864601/10000000000000 : ℝ)) half_12_20_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_20_φ1, half_12_20_φ2, half_12_20_φ3, half_12_20_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_20_φ1, half_12_20_φ2, half_12_20_φ3, half_12_20_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_20_φ1, half_12_20_φ2, half_12_20_φ3, half_12_20_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_20 half_12_19
    (by simpa only [half_12_20_φ2, show (2:ℝ)*2=4 by norm_num] using half_12_20_hx2)
  exact h.weaken (by norm_num [half_12_20_φ1, half_12_20_φ2, half_12_20_φ3, half_12_20_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_20 : AdmissibleExponent 18 24 (1736704396187/125000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 10) (ψ := (187470977083/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_11_20
    (by simpa only [half_12_20_φ1] using half_12_20_hx1)
  exact admissibleExponent_mono h (by norm_num [half_12_20_φ1, half_12_20_φ2, half_12_20_φ3, half_12_20_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_13_20_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1923022041/50000000000 : ℝ)

def half_13_20_φ2 : Fin 2 → ℝ := Fin.snoc half_13_20_φ1 (74393681109/2000000000000 : ℝ)

def half_13_20_φ3 : Fin 3 → ℝ := Fin.snoc half_13_20_φ2 (174946577551/5000000000000 : ℝ)

def half_13_20_φ4 : Fin 4 → ℝ := Fin.snoc half_13_20_φ3 (283313263581/10000000000000 : ℝ)

theorem half_13_20_hF2 : SourcePowerBound (paddedMoment 18 0 2 16 half_13_20_φ4) (17280314786543/2500000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_13_20_φ4 (by norm_num [half_13_20_φ1, half_13_20_φ2, half_13_20_φ3, half_13_20_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_20_φ1, half_13_20_φ2, half_13_20_φ3, half_13_20_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_20_φ1, half_13_20_φ2, half_13_20_φ3, half_13_20_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_13_20_φ1, half_13_20_φ2, half_13_20_φ3, half_13_20_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_13_20_hx4 : SourcePowerBound (powerBoxCross 18 9 16 half_13_20_φ4) (107000764341641/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 9) (r := 2) (v := 12) (w := 12) (D := 16)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_13_20_φ4 (by norm_num [half_13_20_φ1, half_13_20_φ2, half_13_20_φ3, half_13_20_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_20_φ1, half_13_20_φ2, half_13_20_φ3, half_13_20_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_13_20_hF2 half_12_20 half_12_20
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_13_20_φ1, half_13_20_φ2, half_13_20_φ3, half_13_20_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_20_hx3 : SourcePowerBound (powerBoxCross 18 10 8 half_13_20_φ3) (117261145735727/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 10) (u := 8) (t := 11)
    (D := 8) (ψ := (283313263581/10000000000000 : ℝ)) half_13_20_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_20_φ1, half_13_20_φ2, half_13_20_φ3, half_13_20_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_20_φ1, half_13_20_φ2, half_13_20_φ3, half_13_20_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_20_φ1, half_13_20_φ2, half_13_20_φ3, half_13_20_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_20 half_11_20
    (by simpa only [half_13_20_φ4, show (2:ℝ)*8=16 by norm_num] using half_13_20_hx4)
  exact h.weaken (by norm_num [half_13_20_φ1, half_13_20_φ2, half_13_20_φ3, half_13_20_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_20_hx2 : SourcePowerBound (powerBoxCross 18 11 4 half_13_20_φ2) (64868045722657/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 11) (u := 9) (t := 12)
    (D := 4) (ψ := (174946577551/5000000000000 : ℝ)) half_13_20_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_20_φ1, half_13_20_φ2, half_13_20_φ3, half_13_20_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_20_φ1, half_13_20_φ2, half_13_20_φ3, half_13_20_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_20_φ1, half_13_20_φ2, half_13_20_φ3, half_13_20_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_20 half_12_20
    (by simpa only [half_13_20_φ3, show (2:ℝ)*4=8 by norm_num] using half_13_20_hx3)
  exact h.weaken (by norm_num [half_13_20_φ1, half_13_20_φ2, half_13_20_φ3, half_13_20_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_20_hx1 : SourcePowerBound (powerBoxCross 18 12 2 half_13_20_φ1) (143977402771057/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 12) (u := 10) (t := 13)
    (D := 2) (ψ := (74393681109/2000000000000 : ℝ)) half_13_20_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_20_φ1, half_13_20_φ2, half_13_20_φ3, half_13_20_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_20_φ1, half_13_20_φ2, half_13_20_φ3, half_13_20_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_20_φ1, half_13_20_φ2, half_13_20_φ3, half_13_20_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_20 half_13_19
    (by simpa only [half_13_20_φ2, show (2:ℝ)*2=4 by norm_num] using half_13_20_hx2)
  exact h.weaken (by norm_num [half_13_20_φ1, half_13_20_φ2, half_13_20_φ3, half_13_20_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_20 : AdmissibleExponent 18 26 (152823304159657/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 11) (ψ := (1923022041/50000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_12_20
    (by simpa only [half_13_20_φ1] using half_13_20_hx1)
  exact admissibleExponent_mono h (by norm_num [half_13_20_φ1, half_13_20_φ2, half_13_20_φ3, half_13_20_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_14_20_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (394360670781/10000000000000 : ℝ)

def half_14_20_φ2 : Fin 2 → ℝ := Fin.snoc half_14_20_φ1 (382996727767/10000000000000 : ℝ)

def half_14_20_φ3 : Fin 3 → ℝ := Fin.snoc half_14_20_φ2 (183630404751/5000000000000 : ℝ)

def half_14_20_φ4 : Fin 4 → ℝ := Fin.snoc half_14_20_φ3 (332115745249/10000000000000 : ℝ)

def half_14_20_φ5 : Fin 5 → ℝ := Fin.snoc half_14_20_φ4 (205580724441/10000000000000 : ℝ)

theorem half_14_20_hF2 : SourcePowerBound (paddedMoment 18 0 2 32 half_14_20_φ5) (4210097571763/500000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_14_20_φ5 (by norm_num [half_14_20_φ1, half_14_20_φ2, half_14_20_φ3, half_14_20_φ4, half_14_20_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_20_φ1, half_14_20_φ2, half_14_20_φ3, half_14_20_φ4, half_14_20_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_20_φ1, half_14_20_φ2, half_14_20_φ3, half_14_20_φ4, half_14_20_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_14_20_φ1, half_14_20_φ2, half_14_20_φ3, half_14_20_φ4, half_14_20_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_14_20_hx5 : SourcePowerBound (powerBoxCross 18 9 32 half_14_20_φ5) (10772265185043/1000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 9) (r := 2) (v := 12) (w := 12) (D := 32)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_14_20_φ5 (by norm_num [half_14_20_φ1, half_14_20_φ2, half_14_20_φ3, half_14_20_φ4, half_14_20_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_20_φ1, half_14_20_φ2, half_14_20_φ3, half_14_20_φ4, half_14_20_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_14_20_hF2 half_12_20 half_12_20
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_14_20_φ1, half_14_20_φ2, half_14_20_φ3, half_14_20_φ4, half_14_20_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_20_hx4 : SourcePowerBound (powerBoxCross 18 10 16 half_14_20_φ4) (116492708648119/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 10) (u := 8) (t := 11)
    (D := 16) (ψ := (205580724441/10000000000000 : ℝ)) half_14_20_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_20_φ1, half_14_20_φ2, half_14_20_φ3, half_14_20_φ4, half_14_20_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_20_φ1, half_14_20_φ2, half_14_20_φ3, half_14_20_φ4, half_14_20_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_20_φ1, half_14_20_φ2, half_14_20_φ3, half_14_20_φ4, half_14_20_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_20 half_11_20
    (by simpa only [half_14_20_φ5, show (2:ℝ)*16=32 by norm_num] using half_14_20_hx5)
  exact h.weaken (by norm_num [half_14_20_φ1, half_14_20_φ2, half_14_20_φ3, half_14_20_φ4, half_14_20_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_20_hx3 : SourcePowerBound (powerBoxCross 18 11 8 half_14_20_φ3) (32047230271869/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 11) (u := 9) (t := 12)
    (D := 8) (ψ := (332115745249/10000000000000 : ℝ)) half_14_20_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_20_φ1, half_14_20_φ2, half_14_20_φ3, half_14_20_φ4, half_14_20_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_20_φ1, half_14_20_φ2, half_14_20_φ3, half_14_20_φ4, half_14_20_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_20_φ1, half_14_20_φ2, half_14_20_φ3, half_14_20_φ4, half_14_20_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_20 half_12_20
    (by simpa only [half_14_20_φ4, show (2:ℝ)*8=16 by norm_num] using half_14_20_hx4)
  exact h.weaken (by norm_num [half_14_20_φ1, half_14_20_φ2, half_14_20_φ3, half_14_20_φ4, half_14_20_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_20_hx2 : SourcePowerBound (powerBoxCross 18 12 4 half_14_20_φ2) (141814896927727/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 12) (u := 10) (t := 13)
    (D := 4) (ψ := (183630404751/5000000000000 : ℝ)) half_14_20_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_20_φ1, half_14_20_φ2, half_14_20_φ3, half_14_20_φ4, half_14_20_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_20_φ1, half_14_20_φ2, half_14_20_φ3, half_14_20_φ4, half_14_20_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_20_φ1, half_14_20_φ2, half_14_20_φ3, half_14_20_φ4, half_14_20_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_20 half_13_20
    (by simpa only [half_14_20_φ3, show (2:ℝ)*4=8 by norm_num] using half_14_20_hx3)
  exact h.weaken (by norm_num [half_14_20_φ1, half_14_20_φ2, half_14_20_φ3, half_14_20_φ4, half_14_20_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_20_hx1 : SourcePowerBound (powerBoxCross 18 13 2 half_14_20_φ1) (3929772868913/250000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 13) (u := 11) (t := 14)
    (D := 2) (ψ := (382996727767/10000000000000 : ℝ)) half_14_20_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_20_φ1, half_14_20_φ2, half_14_20_φ3, half_14_20_φ4, half_14_20_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_20_φ1, half_14_20_φ2, half_14_20_φ3, half_14_20_φ4, half_14_20_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_20_φ1, half_14_20_φ2, half_14_20_φ3, half_14_20_φ4, half_14_20_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_20 half_14_19
    (by simpa only [half_14_20_φ2, show (2:ℝ)*2=4 by norm_num] using half_14_20_hx2)
  exact h.weaken (by norm_num [half_14_20_φ1, half_14_20_φ2, half_14_20_φ3, half_14_20_φ4, half_14_20_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_20 : AdmissibleExponent 18 28 (33409986305209/2000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 12) (ψ := (394360670781/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_13_20
    (by simpa only [half_14_20_φ1] using half_14_20_hx1)
  exact admissibleExponent_mono h (by norm_num [half_14_20_φ1, half_14_20_φ2, half_14_20_φ3, half_14_20_φ4, half_14_20_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_15_20_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (50454699301/1250000000000 : ℝ)

def half_15_20_φ2 : Fin 2 → ℝ := Fin.snoc half_15_20_φ1 (196493772607/5000000000000 : ℝ)

def half_15_20_φ3 : Fin 3 → ℝ := Fin.snoc half_15_20_φ2 (189728757419/5000000000000 : ℝ)

def half_15_20_φ4 : Fin 4 → ℝ := Fin.snoc half_15_20_φ3 (355225063953/10000000000000 : ℝ)

def half_15_20_φ5 : Fin 5 → ℝ := Fin.snoc half_15_20_φ4 (28429073039/1000000000000 : ℝ)

theorem half_15_20_hF2 : SourcePowerBound (paddedMoment 18 0 2 32 half_15_20_φ5) (77404479111047/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_15_20_φ5 (by norm_num [half_15_20_φ1, half_15_20_φ2, half_15_20_φ3, half_15_20_φ4, half_15_20_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_20_φ1, half_15_20_φ2, half_15_20_φ3, half_15_20_φ4, half_15_20_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_20_φ1, half_15_20_φ2, half_15_20_φ3, half_15_20_φ4, half_15_20_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_15_20_φ1, half_15_20_φ2, half_15_20_φ3, half_15_20_φ4, half_15_20_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_15_20_hx5 : SourcePowerBound (powerBoxCross 18 10 32 half_15_20_φ5) (58034788563329/5000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 10) (r := 2) (v := 13) (w := 14) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_15_20_φ5 (by norm_num [half_15_20_φ1, half_15_20_φ2, half_15_20_φ3, half_15_20_φ4, half_15_20_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_20_φ1, half_15_20_φ2, half_15_20_φ3, half_15_20_φ4, half_15_20_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_15_20_hF2 half_13_20 half_14_20
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_15_20_φ1, half_15_20_φ2, half_15_20_φ3, half_15_20_φ4, half_15_20_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_20_hx4 : SourcePowerBound (powerBoxCross 18 11 16 half_15_20_φ4) (7909368459817/625000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 11) (u := 9) (t := 12)
    (D := 16) (ψ := (28429073039/1000000000000 : ℝ)) half_15_20_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_20_φ1, half_15_20_φ2, half_15_20_φ3, half_15_20_φ4, half_15_20_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_20_φ1, half_15_20_φ2, half_15_20_φ3, half_15_20_φ4, half_15_20_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_20_φ1, half_15_20_φ2, half_15_20_φ3, half_15_20_φ4, half_15_20_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_20 half_12_20
    (by simpa only [half_15_20_φ5, show (2:ℝ)*16=32 by norm_num] using half_15_20_hx5)
  exact h.weaken (by norm_num [half_15_20_φ1, half_15_20_φ2, half_15_20_φ3, half_15_20_φ4, half_15_20_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_20_hx3 : SourcePowerBound (powerBoxCross 18 12 8 half_15_20_φ3) (13943311850599/1000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 12) (u := 10) (t := 13)
    (D := 8) (ψ := (355225063953/10000000000000 : ℝ)) half_15_20_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_20_φ1, half_15_20_φ2, half_15_20_φ3, half_15_20_φ4, half_15_20_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_20_φ1, half_15_20_φ2, half_15_20_φ3, half_15_20_φ4, half_15_20_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_20_φ1, half_15_20_φ2, half_15_20_φ3, half_15_20_φ4, half_15_20_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_20 half_13_20
    (by simpa only [half_15_20_φ4, show (2:ℝ)*8=16 by norm_num] using half_15_20_hx4)
  exact h.weaken (by norm_num [half_15_20_φ1, half_15_20_φ2, half_15_20_φ3, half_15_20_φ4, half_15_20_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_20_hx2 : SourcePowerBound (powerBoxCross 18 13 4 half_15_20_φ2) (154180163998579/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 13) (u := 11) (t := 14)
    (D := 4) (ψ := (189728757419/5000000000000 : ℝ)) half_15_20_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_20_φ1, half_15_20_φ2, half_15_20_φ3, half_15_20_φ4, half_15_20_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_20_φ1, half_15_20_φ2, half_15_20_φ3, half_15_20_φ4, half_15_20_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_20_φ1, half_15_20_φ2, half_15_20_φ3, half_15_20_φ4, half_15_20_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_20 half_14_20
    (by simpa only [half_15_20_φ3, show (2:ℝ)*4=8 by norm_num] using half_15_20_hx3)
  exact h.weaken (by norm_num [half_15_20_φ1, half_15_20_φ2, half_15_20_φ3, half_15_20_φ4, half_15_20_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_20_hx1 : SourcePowerBound (powerBoxCross 18 14 2 half_15_20_φ1) (170710805869739/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 14) (u := 12) (t := 15)
    (D := 2) (ψ := (196493772607/5000000000000 : ℝ)) half_15_20_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_20_φ1, half_15_20_φ2, half_15_20_φ3, half_15_20_φ4, half_15_20_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_20_φ1, half_15_20_φ2, half_15_20_φ3, half_15_20_φ4, half_15_20_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_20_φ1, half_15_20_φ2, half_15_20_φ3, half_15_20_φ4, half_15_20_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_13_20 half_15_19
    (by simpa only [half_15_20_φ2, show (2:ℝ)*2=4 by norm_num] using half_15_20_hx2)
  exact h.weaken (by norm_num [half_15_20_φ1, half_15_20_φ2, half_15_20_φ3, half_15_20_φ4, half_15_20_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_20 : AdmissibleExponent 18 30 (36321804183751/2000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 13) (ψ := (50454699301/1250000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_14_20
    (by simpa only [half_15_20_φ1] using half_15_20_hx1)
  exact admissibleExponent_mono h (by norm_num [half_15_20_φ1, half_15_20_φ2, half_15_20_φ3, half_15_20_φ4, half_15_20_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_16_20_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (51611056643/1250000000000 : ℝ)

def half_16_20_φ2 : Fin 2 → ℝ := Fin.snoc half_16_20_φ1 (402694407711/10000000000000 : ℝ)

def half_16_20_φ3 : Fin 3 → ℝ := Fin.snoc half_16_20_φ2 (391097304453/10000000000000 : ℝ)

def half_16_20_φ4 : Fin 4 → ℝ := Fin.snoc half_16_20_φ3 (374102461041/10000000000000 : ℝ)

def half_16_20_φ5 : Fin 5 → ℝ := Fin.snoc half_16_20_φ4 (42037673897/1250000000000 : ℝ)

def half_16_20_φ6 : Fin 6 → ℝ := Fin.snoc half_16_20_φ5 (208224570077/10000000000000 : ℝ)

theorem half_16_20_hF2 : SourcePowerBound (paddedMoment 18 0 2 64 half_16_20_φ6) (45804631016149/5000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 6) (r := 0) (D := 64)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_16_20_φ6 (by norm_num [half_16_20_φ1, half_16_20_φ2, half_16_20_φ3, half_16_20_φ4, half_16_20_φ5, half_16_20_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_20_φ1, half_16_20_φ2, half_16_20_φ3, half_16_20_φ4, half_16_20_φ5, half_16_20_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_20_φ1, half_16_20_φ2, half_16_20_φ3, half_16_20_φ4, half_16_20_φ5, half_16_20_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_16_20_φ1, half_16_20_φ2, half_16_20_φ3, half_16_20_φ4, half_16_20_φ5, half_16_20_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_16_20_hx6 : SourcePowerBound (powerBoxCross 18 10 64 half_16_20_φ6) (115960800082837/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 10) (r := 2) (v := 13) (w := 14) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_16_20_φ6 (by norm_num [half_16_20_φ1, half_16_20_φ2, half_16_20_φ3, half_16_20_φ4, half_16_20_φ5, half_16_20_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_20_φ1, half_16_20_φ2, half_16_20_φ3, half_16_20_φ4, half_16_20_φ5, half_16_20_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_16_20_hF2 half_13_20 half_14_20
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_16_20_φ1, half_16_20_φ2, half_16_20_φ3, half_16_20_φ4, half_16_20_φ5, half_16_20_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_20_hx5 : SourcePowerBound (powerBoxCross 18 11 32 half_16_20_φ5) (62406931095643/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 5) (s := 11) (u := 9) (t := 12)
    (D := 32) (ψ := (208224570077/10000000000000 : ℝ)) half_16_20_φ5
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_20_φ1, half_16_20_φ2, half_16_20_φ3, half_16_20_φ4, half_16_20_φ5, half_16_20_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_20_φ1, half_16_20_φ2, half_16_20_φ3, half_16_20_φ4, half_16_20_φ5, half_16_20_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_20_φ1, half_16_20_φ2, half_16_20_φ3, half_16_20_φ4, half_16_20_φ5, half_16_20_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_20 half_12_20
    (by simpa only [half_16_20_φ6, show (2:ℝ)*32=64 by norm_num] using half_16_20_hx6)
  exact h.weaken (by norm_num [half_16_20_φ1, half_16_20_φ2, half_16_20_φ3, half_16_20_φ4, half_16_20_φ5, half_16_20_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_20_hx4 : SourcePowerBound (powerBoxCross 18 12 16 half_16_20_φ4) (34208518563253/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 12) (u := 10) (t := 13)
    (D := 16) (ψ := (42037673897/1250000000000 : ℝ)) half_16_20_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_20_φ1, half_16_20_φ2, half_16_20_φ3, half_16_20_φ4, half_16_20_φ5, half_16_20_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_20_φ1, half_16_20_φ2, half_16_20_φ3, half_16_20_φ4, half_16_20_φ5, half_16_20_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_20_φ1, half_16_20_φ2, half_16_20_φ3, half_16_20_φ4, half_16_20_φ5, half_16_20_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_20 half_13_20
    (by simpa only [half_16_20_φ5, show (2:ℝ)*16=32 by norm_num] using half_16_20_hx5)
  exact h.weaken (by norm_num [half_16_20_φ1, half_16_20_φ2, half_16_20_φ3, half_16_20_φ4, half_16_20_φ5, half_16_20_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_20_hx3 : SourcePowerBound (powerBoxCross 18 13 8 half_16_20_φ3) (37727151959239/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 13) (u := 11) (t := 14)
    (D := 8) (ψ := (374102461041/10000000000000 : ℝ)) half_16_20_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_20_φ1, half_16_20_φ2, half_16_20_φ3, half_16_20_φ4, half_16_20_φ5, half_16_20_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_20_φ1, half_16_20_φ2, half_16_20_φ3, half_16_20_φ4, half_16_20_φ5, half_16_20_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_20_φ1, half_16_20_φ2, half_16_20_φ3, half_16_20_φ4, half_16_20_φ5, half_16_20_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_20 half_14_20
    (by simpa only [half_16_20_φ4, show (2:ℝ)*8=16 by norm_num] using half_16_20_hx4)
  exact h.weaken (by norm_num [half_16_20_φ1, half_16_20_φ2, half_16_20_φ3, half_16_20_φ4, half_16_20_φ5, half_16_20_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_20_hx2 : SourcePowerBound (powerBoxCross 18 14 4 half_16_20_φ2) (166809216124351/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 14) (u := 12) (t := 15)
    (D := 4) (ψ := (391097304453/10000000000000 : ℝ)) half_16_20_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_20_φ1, half_16_20_φ2, half_16_20_φ3, half_16_20_φ4, half_16_20_φ5, half_16_20_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_20_φ1, half_16_20_φ2, half_16_20_φ3, half_16_20_φ4, half_16_20_φ5, half_16_20_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_20_φ1, half_16_20_φ2, half_16_20_φ3, half_16_20_φ4, half_16_20_φ5, half_16_20_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_13_20 half_15_20
    (by simpa only [half_16_20_φ3, show (2:ℝ)*4=8 by norm_num] using half_16_20_hx3)
  exact h.weaken (by norm_num [half_16_20_φ1, half_16_20_φ2, half_16_20_φ3, half_16_20_φ4, half_16_20_φ5, half_16_20_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_20_hx1 : SourcePowerBound (powerBoxCross 18 15 2 half_16_20_φ1) (2883179415617/156250000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 15) (u := 13) (t := 16)
    (D := 2) (ψ := (402694407711/10000000000000 : ℝ)) half_16_20_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_20_φ1, half_16_20_φ2, half_16_20_φ3, half_16_20_φ4, half_16_20_φ5, half_16_20_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_20_φ1, half_16_20_φ2, half_16_20_φ3, half_16_20_φ4, half_16_20_φ5, half_16_20_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_20_φ1, half_16_20_φ2, half_16_20_φ3, half_16_20_φ4, half_16_20_φ5, half_16_20_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_14_20 half_16_19
    (by simpa only [half_16_20_φ2, show (2:ℝ)*2=4 by norm_num] using half_16_20_hx2)
  exact h.weaken (by norm_num [half_16_20_φ1, half_16_20_φ2, half_16_20_φ3, half_16_20_φ4, half_16_20_φ5, half_16_20_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_20 : AdmissibleExponent 18 32 (24562155967583/1250000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 14) (ψ := (51611056643/1250000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_15_20
    (by simpa only [half_16_20_φ1] using half_16_20_hx1)
  exact admissibleExponent_mono h (by norm_num [half_16_20_φ1, half_16_20_φ2, half_16_20_φ3, half_16_20_φ4, half_16_20_φ5, half_16_20_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_17_20_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (421825290131/10000000000000 : ℝ)

def half_17_20_φ2 : Fin 2 → ℝ := Fin.snoc half_17_20_φ1 (51501347557/1250000000000 : ℝ)

def half_17_20_φ3 : Fin 3 → ℝ := Fin.snoc half_17_20_φ2 (200561867491/5000000000000 : ℝ)

def half_17_20_φ4 : Fin 4 → ℝ := Fin.snoc half_17_20_φ3 (387122417281/10000000000000 : ℝ)

def half_17_20_φ5 : Fin 5 → ℝ := Fin.snoc half_17_20_φ4 (72267927067/2000000000000 : ℝ)

def half_17_20_φ6 : Fin 6 → ℝ := Fin.snoc half_17_20_φ5 (72295837599/2500000000000 : ℝ)

theorem half_17_20_hF2 : SourcePowerBound (paddedMoment 18 0 2 64 half_17_20_φ6) (84097134362369/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 6) (r := 0) (D := 64)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_17_20_φ6 (by norm_num [half_17_20_φ1, half_17_20_φ2, half_17_20_φ3, half_17_20_φ4, half_17_20_φ5, half_17_20_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_20_φ1, half_17_20_φ2, half_17_20_φ3, half_17_20_φ4, half_17_20_φ5, half_17_20_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_20_φ1, half_17_20_φ2, half_17_20_φ3, half_17_20_φ4, half_17_20_φ5, half_17_20_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_17_20_φ1, half_17_20_φ2, half_17_20_φ3, half_17_20_φ4, half_17_20_φ5, half_17_20_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_17_20_hx6 : SourcePowerBound (powerBoxCross 18 11 64 half_17_20_φ6) (123464032976239/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 11) (r := 2) (v := 14) (w := 15) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_17_20_φ6 (by norm_num [half_17_20_φ1, half_17_20_φ2, half_17_20_φ3, half_17_20_φ4, half_17_20_φ5, half_17_20_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_20_φ1, half_17_20_φ2, half_17_20_φ3, half_17_20_φ4, half_17_20_φ5, half_17_20_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_17_20_hF2 half_14_20 half_15_20
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_17_20_φ1, half_17_20_φ2, half_17_20_φ3, half_17_20_φ4, half_17_20_φ5, half_17_20_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_20_hx5 : SourcePowerBound (powerBoxCross 18 12 32 half_17_20_φ5) (67082676928511/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 5) (s := 12) (u := 10) (t := 13)
    (D := 32) (ψ := (72295837599/2500000000000 : ℝ)) half_17_20_φ5
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_20_φ1, half_17_20_φ2, half_17_20_φ3, half_17_20_φ4, half_17_20_φ5, half_17_20_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_20_φ1, half_17_20_φ2, half_17_20_φ3, half_17_20_φ4, half_17_20_φ5, half_17_20_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_20_φ1, half_17_20_φ2, half_17_20_φ3, half_17_20_φ4, half_17_20_φ5, half_17_20_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_20 half_13_20
    (by simpa only [half_17_20_φ6, show (2:ℝ)*32=64 by norm_num] using half_17_20_hx6)
  exact h.weaken (by norm_num [half_17_20_φ1, half_17_20_φ2, half_17_20_φ3, half_17_20_φ4, half_17_20_φ5, half_17_20_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_20_hx4 : SourcePowerBound (powerBoxCross 18 13 16 half_17_20_φ4) (73713456695413/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 13) (u := 11) (t := 14)
    (D := 16) (ψ := (72267927067/2000000000000 : ℝ)) half_17_20_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_20_φ1, half_17_20_φ2, half_17_20_φ3, half_17_20_φ4, half_17_20_φ5, half_17_20_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_20_φ1, half_17_20_φ2, half_17_20_φ3, half_17_20_φ4, half_17_20_φ5, half_17_20_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_20_φ1, half_17_20_φ2, half_17_20_φ3, half_17_20_φ4, half_17_20_φ5, half_17_20_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_20 half_14_20
    (by simpa only [half_17_20_φ5, show (2:ℝ)*16=32 by norm_num] using half_17_20_hx5)
  exact h.weaken (by norm_num [half_17_20_φ1, half_17_20_φ2, half_17_20_φ3, half_17_20_φ4, half_17_20_φ5, half_17_20_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_20_hx3 : SourcePowerBound (powerBoxCross 18 14 8 half_17_20_φ3) (162645846965297/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 14) (u := 12) (t := 15)
    (D := 8) (ψ := (387122417281/10000000000000 : ℝ)) half_17_20_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_20_φ1, half_17_20_φ2, half_17_20_φ3, half_17_20_φ4, half_17_20_φ5, half_17_20_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_20_φ1, half_17_20_φ2, half_17_20_φ3, half_17_20_φ4, half_17_20_φ5, half_17_20_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_20_φ1, half_17_20_φ2, half_17_20_φ3, half_17_20_φ4, half_17_20_φ5, half_17_20_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_13_20 half_15_20
    (by simpa only [half_17_20_φ4, show (2:ℝ)*8=16 by norm_num] using half_17_20_hx4)
  exact h.weaken (by norm_num [half_17_20_φ1, half_17_20_φ2, half_17_20_φ3, half_17_20_φ4, half_17_20_φ5, half_17_20_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_20_hx2 : SourcePowerBound (powerBoxCross 18 15 4 half_17_20_φ2) (179706786528387/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 15) (u := 13) (t := 16)
    (D := 4) (ψ := (200561867491/5000000000000 : ℝ)) half_17_20_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_20_φ1, half_17_20_φ2, half_17_20_φ3, half_17_20_φ4, half_17_20_φ5, half_17_20_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_20_φ1, half_17_20_φ2, half_17_20_φ3, half_17_20_φ4, half_17_20_φ5, half_17_20_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_20_φ1, half_17_20_φ2, half_17_20_φ3, half_17_20_φ4, half_17_20_φ5, half_17_20_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_14_20 half_16_20
    (by simpa only [half_17_20_φ3, show (2:ℝ)*4=8 by norm_num] using half_17_20_hx3)
  exact h.weaken (by norm_num [half_17_20_φ1, half_17_20_φ2, half_17_20_φ3, half_17_20_φ4, half_17_20_φ5, half_17_20_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_20_hx1 : SourcePowerBound (powerBoxCross 18 16 2 half_17_20_φ1) (19863032217699/1000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 16) (u := 14) (t := 17)
    (D := 2) (ψ := (51501347557/1250000000000 : ℝ)) half_17_20_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_20_φ1, half_17_20_φ2, half_17_20_φ3, half_17_20_φ4, half_17_20_φ5, half_17_20_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_20_φ1, half_17_20_φ2, half_17_20_φ3, half_17_20_φ4, half_17_20_φ5, half_17_20_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_20_φ1, half_17_20_φ2, half_17_20_φ3, half_17_20_φ4, half_17_20_φ5, half_17_20_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_15_20 half_17_19
    (by simpa only [half_17_20_φ2, show (2:ℝ)*2=4 by norm_num] using half_17_20_hx2)
  exact h.weaken (by norm_num [half_17_20_φ1, half_17_20_φ2, half_17_20_φ3, half_17_20_φ4, half_17_20_φ5, half_17_20_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_20 : AdmissibleExponent 18 34 (211706906171051/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 15) (ψ := (421825290131/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_16_20
    (by simpa only [half_17_20_φ1] using half_17_20_hx1)
  exact admissibleExponent_mono h (by norm_num [half_17_20_φ1, half_17_20_φ2, half_17_20_φ3, half_17_20_φ4, half_17_20_φ5, half_17_20_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])


end Waring.SeedCompletionHigher18SimpleSeeds
