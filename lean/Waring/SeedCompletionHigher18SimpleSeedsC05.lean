import Waring.SeedCompletionHigher18SimpleSeedsC04

noncomputable section
set_option maxHeartbeats 2000000
namespace Waring.SeedCompletionHigher18SimpleSeeds
open SmoothMoments FirstStageTransport SeedCompletionNaturalBox
open SeedCompletionSourceBounds SeedCompletionPaddedSource SeedCompletionGeneralTerminal
open PolicyCompletionMajorPowerRanges

def half_9_05_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (171991500627/5000000000000 : ℝ)

def half_9_05_φ2 : Fin 2 → ℝ := Fin.snoc half_9_05_φ1 (61699681303/2000000000000 : ℝ)

def half_9_05_φ3 : Fin 3 → ℝ := Fin.snoc half_9_05_φ2 (67706963727/5000000000000 : ℝ)

theorem half_9_05_hF2 : SourcePowerBound (paddedMoment 18 0 2 8 half_9_05_φ3) (69817337903627/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_05_φ3 (by norm_num [half_9_05_φ1, half_9_05_φ2, half_9_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_05_φ1, half_9_05_φ2, half_9_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_05_φ1, half_9_05_φ2, half_9_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_05_φ1, half_9_05_φ2, half_9_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_9_05_hF1 : SourcePowerBound (paddedMoment 18 0 1 8 half_9_05_φ3) (26605779301209/10000000000000 : ℝ) := by
  have h := padded_second_power (k := 18) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_05_φ3 (by norm_num [half_9_05_φ1, half_9_05_φ2, half_9_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_05_φ1, half_9_05_φ2, half_9_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_05_φ1, half_9_05_φ2, half_9_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_05_φ1, half_9_05_φ2, half_9_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_9_05_hx3 : SourcePowerBound (powerBoxCross 18 6 8 half_9_05_φ3) (76980989919343/10000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 18) (s := 6) (r := 1) (v := 2) (t := 10) (D := 8)
    (a := (3/10 : ℝ)) (b := (1/10 : ℝ)) (c := (3/5 : ℝ))
    (by norm_num) half_9_05_φ3 (by norm_num [half_9_05_φ1, half_9_05_φ2, half_9_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_05_φ1, half_9_05_φ2, half_9_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_9_05_hF1 half_9_05_hF2 half_10_04
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_9_05_φ1, half_9_05_φ2, half_9_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_9_05_hx2 : SourcePowerBound (powerBoxCross 18 7 4 half_9_05_φ2) (84264903016561/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 7) (u := 5) (t := 8)
    (D := 4) (ψ := (67706963727/5000000000000 : ℝ)) half_9_05_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_05_φ1, half_9_05_φ2, half_9_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_05_φ1, half_9_05_φ2, half_9_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_05_φ1, half_9_05_φ2, half_9_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_6 SeedCompletionEven18SecondSeeds.degree18_half_8
    (by simpa only [half_9_05_φ3, show (2:ℝ)*4=8 by norm_num] using half_9_05_hx3)
  exact h.weaken (by norm_num [half_9_05_φ1, half_9_05_φ2, half_9_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_9_05_hx1 : SourcePowerBound (powerBoxCross 18 8 2 half_9_05_φ1) (94173690582529/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 8) (u := 6) (t := 9)
    (D := 2) (ψ := (61699681303/2000000000000 : ℝ)) half_9_05_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_05_φ1, half_9_05_φ2, half_9_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_05_φ1, half_9_05_φ2, half_9_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_05_φ1, half_9_05_φ2, half_9_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_7 half_9_04
    (by simpa only [half_9_05_φ2, show (2:ℝ)*2=4 by norm_num] using half_9_05_hx2)
  exact h.weaken (by norm_num [half_9_05_φ1, half_9_05_φ2, half_9_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_9_05 : AdmissibleExponent 18 18 (99333435601339/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 7) (ψ := (171991500627/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_8
    (by simpa only [half_9_05_φ1] using half_9_05_hx1)
  exact admissibleExponent_mono h (by norm_num [half_9_05_φ1, half_9_05_φ2, half_9_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_10_05_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (70833767797/2000000000000 : ℝ)

def half_10_05_φ2 : Fin 2 → ℝ := Fin.snoc half_10_05_φ1 (164683129671/5000000000000 : ℝ)

def half_10_05_φ3 : Fin 3 → ℝ := Fin.snoc half_10_05_φ2 (230395880099/10000000000000 : ℝ)

theorem half_10_05_hF2 : SourcePowerBound (paddedMoment 18 0 2 8 half_10_05_φ3) (31694760050137/5000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_10_05_φ3 (by norm_num [half_10_05_φ1, half_10_05_φ2, half_10_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_05_φ1, half_10_05_φ2, half_10_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_05_φ1, half_10_05_φ2, half_10_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_10_05_φ1, half_10_05_φ2, half_10_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_10_05_hx3 : SourcePowerBound (powerBoxCross 18 7 8 half_10_05_φ3) (2701937426297/312500000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 7) (r := 2) (v := 9) (w := 10) (D := 8)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_10_05_φ3 (by norm_num [half_10_05_φ1, half_10_05_φ2, half_10_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_05_φ1, half_10_05_φ2, half_10_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_10_05_hF2 half_9_05 half_10_04
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_10_05_φ1, half_10_05_φ2, half_10_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_05_hx2 : SourcePowerBound (powerBoxCross 18 8 4 half_10_05_φ2) (4759517351137/500000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 8) (u := 6) (t := 9)
    (D := 4) (ψ := (230395880099/10000000000000 : ℝ)) half_10_05_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_05_φ1, half_10_05_φ2, half_10_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_05_φ1, half_10_05_φ2, half_10_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_05_φ1, half_10_05_φ2, half_10_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_7 half_9_05
    (by simpa only [half_10_05_φ3, show (2:ℝ)*4=8 by norm_num] using half_10_05_hx3)
  exact h.weaken (by norm_num [half_10_05_φ1, half_10_05_φ2, half_10_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_05_hx1 : SourcePowerBound (powerBoxCross 18 9 2 half_10_05_φ1) (106169523684401/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 9) (u := 7) (t := 10)
    (D := 2) (ψ := (164683129671/5000000000000 : ℝ)) half_10_05_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_05_φ1, half_10_05_φ2, half_10_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_05_φ1, half_10_05_φ2, half_10_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_05_φ1, half_10_05_φ2, half_10_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_8 half_10_04
    (by simpa only [half_10_05_φ2, show (2:ℝ)*2=4 by norm_num] using half_10_05_hx2)
  exact h.weaken (by norm_num [half_10_05_φ1, half_10_05_φ2, half_10_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_05 : AdmissibleExponent 18 20 (56095196973573/5000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 8) (ψ := (70833767797/2000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_9_05
    (by simpa only [half_10_05_φ1] using half_10_05_hx1)
  exact admissibleExponent_mono h (by norm_num [half_10_05_φ1, half_10_05_φ2, half_10_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_11_05_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (366115268037/10000000000000 : ℝ)

def half_11_05_φ2 : Fin 2 → ℝ := Fin.snoc half_11_05_φ1 (346923816243/10000000000000 : ℝ)

def half_11_05_φ3 : Fin 3 → ℝ := Fin.snoc half_11_05_φ2 (74261984569/2500000000000 : ℝ)

theorem half_11_05_hF2 : SourcePowerBound (paddedMoment 18 0 2 8 half_11_05_φ3) (14621390462411/2500000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_11_05_φ3 (by norm_num [half_11_05_φ1, half_11_05_φ2, half_11_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_05_φ1, half_11_05_φ2, half_11_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_05_φ1, half_11_05_φ2, half_11_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_11_05_φ1, half_11_05_φ2, half_11_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_11_05_hx3 : SourcePowerBound (powerBoxCross 18 8 8 half_11_05_φ3) (96222240318003/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 8) (r := 2) (v := 10) (w := 11) (D := 8)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_11_05_φ3 (by norm_num [half_11_05_φ1, half_11_05_φ2, half_11_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_05_φ1, half_11_05_φ2, half_11_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_11_05_hF2 half_10_05 half_11_04
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_11_05_φ1, half_11_05_φ2, half_11_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_05_hx2 : SourcePowerBound (powerBoxCross 18 9 4 half_11_05_φ2) (26593384416253/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 9) (u := 7) (t := 10)
    (D := 4) (ψ := (74261984569/2500000000000 : ℝ)) half_11_05_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_05_φ1, half_11_05_φ2, half_11_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_05_φ1, half_11_05_φ2, half_11_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_05_φ1, half_11_05_φ2, half_11_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_8 half_10_05
    (by simpa only [half_11_05_φ3, show (2:ℝ)*4=8 by norm_num] using half_11_05_hx3)
  exact h.weaken (by norm_num [half_11_05_φ1, half_11_05_φ2, half_11_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_05_hx1 : SourcePowerBound (powerBoxCross 18 10 2 half_11_05_φ1) (29612261900019/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 10) (u := 8) (t := 11)
    (D := 2) (ψ := (346923816243/10000000000000 : ℝ)) half_11_05_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_05_φ1, half_11_05_φ2, half_11_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_05_φ1, half_11_05_φ2, half_11_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_05_φ1, half_11_05_φ2, half_11_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_05 half_11_04
    (by simpa only [half_11_05_φ2, show (2:ℝ)*2=4 by norm_num] using half_11_05_hx2)
  exact h.weaken (by norm_num [half_11_05_φ1, half_11_05_φ2, half_11_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_05 : AdmissibleExponent 18 22 (125405237692779/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 9) (ψ := (366115268037/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_10_05
    (by simpa only [half_11_05_φ1] using half_11_05_hx1)
  exact admissibleExponent_mono h (by norm_num [half_11_05_φ1, half_11_05_φ2, half_11_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_12_05_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (75482476547/2000000000000 : ℝ)

def half_12_05_φ2 : Fin 2 → ℝ := Fin.snoc half_12_05_φ1 (360891849687/10000000000000 : ℝ)

def half_12_05_φ3 : Fin 3 → ℝ := Fin.snoc half_12_05_φ2 (329832321397/10000000000000 : ℝ)

def half_12_05_φ4 : Fin 4 → ℝ := Fin.snoc half_12_05_φ3 (10731027563/500000000000 : ℝ)

theorem half_12_05_hF2 : SourcePowerBound (paddedMoment 18 0 2 16 half_12_05_φ4) (74579387640971/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_12_05_φ4 (by norm_num [half_12_05_φ1, half_12_05_φ2, half_12_05_φ3, half_12_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_05_φ1, half_12_05_φ2, half_12_05_φ3, half_12_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_05_φ1, half_12_05_φ2, half_12_05_φ3, half_12_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_12_05_φ1, half_12_05_φ2, half_12_05_φ3, half_12_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_12_05_hF1 : SourcePowerBound (paddedMoment 18 0 1 16 half_12_05_φ4) (28193129213657/10000000000000 : ℝ) := by
  have h := padded_second_power (k := 18) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_12_05_φ4 (by norm_num [half_12_05_φ1, half_12_05_φ2, half_12_05_φ3, half_12_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_05_φ1, half_12_05_φ2, half_12_05_φ3, half_12_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_05_φ1, half_12_05_φ2, half_12_05_φ3, half_12_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_12_05_φ1, half_12_05_φ2, half_12_05_φ3, half_12_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_12_05_hx4 : SourcePowerBound (powerBoxCross 18 8 16 half_12_05_φ4) (48867971250903/5000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 18) (s := 8) (r := 1) (v := 2) (t := 11) (D := 16)
    (a := (1/22 : ℝ)) (b := (5/22 : ℝ)) (c := (8/11 : ℝ))
    (by norm_num) half_12_05_φ4 (by norm_num [half_12_05_φ1, half_12_05_φ2, half_12_05_φ3, half_12_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_05_φ1, half_12_05_φ2, half_12_05_φ3, half_12_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_12_05_hF1 half_12_05_hF2 half_11_05
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_12_05_φ1, half_12_05_φ2, half_12_05_φ3, half_12_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_05_hx3 : SourcePowerBound (powerBoxCross 18 9 8 half_12_05_φ3) (13312741076669/1250000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 9) (u := 7) (t := 10)
    (D := 8) (ψ := (10731027563/500000000000 : ℝ)) half_12_05_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_05_φ1, half_12_05_φ2, half_12_05_φ3, half_12_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_05_φ1, half_12_05_φ2, half_12_05_φ3, half_12_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_05_φ1, half_12_05_φ2, half_12_05_φ3, half_12_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_8 half_10_05
    (by simpa only [half_12_05_φ4, show (2:ℝ)*8=16 by norm_num] using half_12_05_hx4)
  exact h.weaken (by norm_num [half_12_05_φ1, half_12_05_φ2, half_12_05_φ3, half_12_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_05_hx2 : SourcePowerBound (powerBoxCross 18 10 4 half_12_05_φ2) (11785221102153/1000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 10) (u := 8) (t := 11)
    (D := 4) (ψ := (329832321397/10000000000000 : ℝ)) half_12_05_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_05_φ1, half_12_05_φ2, half_12_05_φ3, half_12_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_05_φ1, half_12_05_φ2, half_12_05_φ3, half_12_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_05_φ1, half_12_05_φ2, half_12_05_φ3, half_12_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_05 half_11_05
    (by simpa only [half_12_05_φ3, show (2:ℝ)*4=8 by norm_num] using half_12_05_hx3)
  exact h.weaken (by norm_num [half_12_05_φ1, half_12_05_φ2, half_12_05_φ3, half_12_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_05_hx1 : SourcePowerBound (powerBoxCross 18 11 2 half_12_05_φ1) (32762425279757/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 11) (u := 9) (t := 12)
    (D := 2) (ψ := (360891849687/10000000000000 : ℝ)) half_12_05_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_05_φ1, half_12_05_φ2, half_12_05_φ3, half_12_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_05_φ1, half_12_05_φ2, half_12_05_φ3, half_12_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_05_φ1, half_12_05_φ2, half_12_05_φ3, half_12_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_05 half_12_04
    (by simpa only [half_12_05_φ2, show (2:ℝ)*2=4 by norm_num] using half_12_05_hx2)
  exact h.weaken (by norm_num [half_12_05_φ1, half_12_05_φ2, half_12_05_φ3, half_12_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_05 : AdmissibleExponent 18 24 (138975361156463/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 10) (ψ := (75482476547/2000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_11_05
    (by simpa only [half_12_05_φ1] using half_12_05_hx1)
  exact admissibleExponent_mono h (by norm_num [half_12_05_φ1, half_12_05_φ2, half_12_05_φ3, half_12_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_13_05_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (48647267207/1250000000000 : ℝ)

def half_13_05_φ2 : Fin 2 → ℝ := Fin.snoc half_13_05_φ1 (186234460693/5000000000000 : ℝ)

def half_13_05_φ3 : Fin 3 → ℝ := Fin.snoc half_13_05_φ2 (10963568529/312500000000 : ℝ)

def half_13_05_φ4 : Fin 4 → ℝ := Fin.snoc half_13_05_φ3 (143303464241/5000000000000 : ℝ)

theorem half_13_05_hF2 : SourcePowerBound (paddedMoment 18 0 2 16 half_13_05_φ4) (17161625699237/2500000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_13_05_φ4 (by norm_num [half_13_05_φ1, half_13_05_φ2, half_13_05_φ3, half_13_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_05_φ1, half_13_05_φ2, half_13_05_φ3, half_13_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_05_φ1, half_13_05_φ2, half_13_05_φ3, half_13_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_13_05_φ1, half_13_05_φ2, half_13_05_φ3, half_13_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_13_05_hx4 : SourcePowerBound (powerBoxCross 18 9 16 half_13_05_φ4) (106810237678981/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 9) (r := 2) (v := 12) (w := 12) (D := 16)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_13_05_φ4 (by norm_num [half_13_05_φ1, half_13_05_φ2, half_13_05_φ3, half_13_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_05_φ1, half_13_05_φ2, half_13_05_φ3, half_13_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_13_05_hF2 half_12_05 half_12_05
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_13_05_φ1, half_13_05_φ2, half_13_05_φ3, half_13_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_05_hx3 : SourcePowerBound (powerBoxCross 18 10 8 half_13_05_φ3) (11711225714463/1000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 10) (u := 8) (t := 11)
    (D := 8) (ψ := (143303464241/5000000000000 : ℝ)) half_13_05_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_05_φ1, half_13_05_φ2, half_13_05_φ3, half_13_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_05_φ1, half_13_05_φ2, half_13_05_φ3, half_13_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_05_φ1, half_13_05_φ2, half_13_05_φ3, half_13_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_05 half_11_05
    (by simpa only [half_13_05_φ4, show (2:ℝ)*8=16 by norm_num] using half_13_05_hx4)
  exact h.weaken (by norm_num [half_13_05_φ1, half_13_05_φ2, half_13_05_φ3, half_13_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_05_hx2 : SourcePowerBound (powerBoxCross 18 11 4 half_13_05_φ2) (1296102252263/100000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 11) (u := 9) (t := 12)
    (D := 4) (ψ := (10963568529/312500000000 : ℝ)) half_13_05_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_05_φ1, half_13_05_φ2, half_13_05_φ3, half_13_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_05_φ1, half_13_05_φ2, half_13_05_φ3, half_13_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_05_φ1, half_13_05_φ2, half_13_05_φ3, half_13_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_05 half_12_05
    (by simpa only [half_13_05_φ3, show (2:ℝ)*4=8 by norm_num] using half_13_05_hx3)
  exact h.weaken (by norm_num [half_13_05_φ1, half_13_05_φ2, half_13_05_φ3, half_13_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_05_hx1 : SourcePowerBound (powerBoxCross 18 12 2 half_13_05_φ1) (17994490258829/1250000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 12) (u := 10) (t := 13)
    (D := 2) (ψ := (186234460693/5000000000000 : ℝ)) half_13_05_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_05_φ1, half_13_05_φ2, half_13_05_φ3, half_13_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_05_φ1, half_13_05_φ2, half_13_05_φ3, half_13_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_05_φ1, half_13_05_φ2, half_13_05_φ3, half_13_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_05 half_13_04
    (by simpa only [half_13_05_φ2, show (2:ℝ)*2=4 by norm_num] using half_13_05_hx2)
  exact h.weaken (by norm_num [half_13_05_φ1, half_13_05_φ2, half_13_05_φ3, half_13_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_05 : AdmissibleExponent 18 26 (1911337740459/125000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 11) (ψ := (48647267207/1250000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_12_05
    (by simpa only [half_13_05_φ1] using half_13_05_hx1)
  exact admissibleExponent_mono h (by norm_num [half_13_05_φ1, half_13_05_φ2, half_13_05_φ3, half_13_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_14_05_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (401587865663/10000000000000 : ℝ)

def half_14_05_φ2 : Fin 2 → ℝ := Fin.snoc half_14_05_φ1 (76734777343/2000000000000 : ℝ)

def half_14_05_φ3 : Fin 3 → ℝ := Fin.snoc half_14_05_φ2 (367791529993/10000000000000 : ℝ)

def half_14_05_φ4 : Fin 4 → ℝ := Fin.snoc half_14_05_φ3 (333241559523/10000000000000 : ℝ)

def half_14_05_φ5 : Fin 5 → ℝ := Fin.snoc half_14_05_φ4 (41950542409/2000000000000 : ℝ)

theorem half_14_05_hF2 : SourcePowerBound (paddedMoment 18 0 2 32 half_14_05_φ5) (83501574749111/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_14_05_φ5 (by norm_num [half_14_05_φ1, half_14_05_φ2, half_14_05_φ3, half_14_05_φ4, half_14_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_05_φ1, half_14_05_φ2, half_14_05_φ3, half_14_05_φ4, half_14_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_05_φ1, half_14_05_φ2, half_14_05_φ3, half_14_05_φ4, half_14_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_14_05_φ1, half_14_05_φ2, half_14_05_φ3, half_14_05_φ4, half_14_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_14_05_hx5 : SourcePowerBound (powerBoxCross 18 9 32 half_14_05_φ5) (21485750590717/2000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 9) (r := 2) (v := 12) (w := 12) (D := 32)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_14_05_φ5 (by norm_num [half_14_05_φ1, half_14_05_φ2, half_14_05_φ3, half_14_05_φ4, half_14_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_05_φ1, half_14_05_φ2, half_14_05_φ3, half_14_05_φ4, half_14_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_14_05_hF2 half_12_05 half_12_05
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_14_05_φ1, half_14_05_φ2, half_14_05_φ3, half_14_05_φ4, half_14_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_05_hx4 : SourcePowerBound (powerBoxCross 18 10 16 half_14_05_φ4) (116246929323003/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 10) (u := 8) (t := 11)
    (D := 16) (ψ := (41950542409/2000000000000 : ℝ)) half_14_05_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_05_φ1, half_14_05_φ2, half_14_05_φ3, half_14_05_φ4, half_14_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_05_φ1, half_14_05_φ2, half_14_05_φ3, half_14_05_φ4, half_14_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_05_φ1, half_14_05_φ2, half_14_05_φ3, half_14_05_φ4, half_14_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_05 half_11_05
    (by simpa only [half_14_05_φ5, show (2:ℝ)*16=32 by norm_num] using half_14_05_hx5)
  exact h.weaken (by norm_num [half_14_05_φ1, half_14_05_φ2, half_14_05_φ3, half_14_05_φ4, half_14_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_05_hx3 : SourcePowerBound (powerBoxCross 18 11 8 half_14_05_φ3) (127963687337541/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 11) (u := 9) (t := 12)
    (D := 8) (ψ := (333241559523/10000000000000 : ℝ)) half_14_05_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_05_φ1, half_14_05_φ2, half_14_05_φ3, half_14_05_φ4, half_14_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_05_φ1, half_14_05_φ2, half_14_05_φ3, half_14_05_φ4, half_14_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_05_φ1, half_14_05_φ2, half_14_05_φ3, half_14_05_φ4, half_14_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_05 half_12_05
    (by simpa only [half_14_05_φ4, show (2:ℝ)*8=16 by norm_num] using half_14_05_hx4)
  exact h.weaken (by norm_num [half_14_05_φ1, half_14_05_φ2, half_14_05_φ3, half_14_05_φ4, half_14_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_05_hx2 : SourcePowerBound (powerBoxCross 18 12 4 half_14_05_φ2) (2212794340047/156250000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 12) (u := 10) (t := 13)
    (D := 4) (ψ := (367791529993/10000000000000 : ℝ)) half_14_05_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_05_φ1, half_14_05_φ2, half_14_05_φ3, half_14_05_φ4, half_14_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_05_φ1, half_14_05_φ2, half_14_05_φ3, half_14_05_φ4, half_14_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_05_φ1, half_14_05_φ2, half_14_05_φ3, half_14_05_φ4, half_14_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_05 half_13_05
    (by simpa only [half_14_05_φ3, show (2:ℝ)*4=8 by norm_num] using half_14_05_hx3)
  exact h.weaken (by norm_num [half_14_05_φ1, half_14_05_φ2, half_14_05_φ3, half_14_05_φ4, half_14_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_05_hx1 : SourcePowerBound (powerBoxCross 18 13 2 half_14_05_φ1) (78584023376187/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 13) (u := 11) (t := 14)
    (D := 2) (ψ := (76734777343/2000000000000 : ℝ)) half_14_05_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_05_φ1, half_14_05_φ2, half_14_05_φ3, half_14_05_φ4, half_14_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_05_φ1, half_14_05_φ2, half_14_05_φ3, half_14_05_φ4, half_14_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_05_φ1, half_14_05_φ2, half_14_05_φ3, half_14_05_φ4, half_14_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_05 half_14_04
    (by simpa only [half_14_05_φ2, show (2:ℝ)*2=4 by norm_num] using half_14_05_hx2)
  exact h.weaken (by norm_num [half_14_05_φ1, half_14_05_φ2, half_14_05_φ3, half_14_05_φ4, half_14_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_05 : AdmissibleExponent 18 28 (167207743393949/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 12) (ψ := (401587865663/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_13_05
    (by simpa only [half_14_05_φ1] using half_14_05_hx1)
  exact admissibleExponent_mono h (by norm_num [half_14_05_φ1, half_14_05_φ2, half_14_05_φ3, half_14_05_φ4, half_14_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_15_05_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (207154814189/5000000000000 : ℝ)

def half_15_05_φ2 : Fin 2 → ℝ := Fin.snoc half_15_05_φ1 (78798730597/2000000000000 : ℝ)

def half_15_05_φ3 : Fin 3 → ℝ := Fin.snoc half_15_05_φ2 (15222176319/400000000000 : ℝ)

def half_15_05_φ4 : Fin 4 → ℝ := Fin.snoc half_15_05_φ3 (357462221899/10000000000000 : ℝ)

def half_15_05_φ5 : Fin 5 → ℝ := Fin.snoc half_15_05_φ4 (292484842603/10000000000000 : ℝ)

theorem half_15_05_hF2 : SourcePowerBound (paddedMoment 18 0 2 32 half_15_05_φ5) (952761969427/125000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_15_05_φ5 (by norm_num [half_15_05_φ1, half_15_05_φ2, half_15_05_φ3, half_15_05_φ4, half_15_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_05_φ1, half_15_05_φ2, half_15_05_φ3, half_15_05_φ4, half_15_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_05_φ1, half_15_05_φ2, half_15_05_φ3, half_15_05_φ4, half_15_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_15_05_φ1, half_15_05_φ2, half_15_05_φ3, half_15_05_φ4, half_15_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_15_05_hx5 : SourcePowerBound (powerBoxCross 18 10 32 half_15_05_φ5) (115565817326197/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 10) (r := 2) (v := 13) (w := 14) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_15_05_φ5 (by norm_num [half_15_05_φ1, half_15_05_φ2, half_15_05_φ3, half_15_05_φ4, half_15_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_05_φ1, half_15_05_φ2, half_15_05_φ3, half_15_05_φ4, half_15_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_15_05_hF2 half_13_05 half_14_05
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_15_05_φ1, half_15_05_φ2, half_15_05_φ3, half_15_05_φ4, half_15_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_05_hx4 : SourcePowerBound (powerBoxCross 18 11 16 half_15_05_φ4) (126160457594167/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 11) (u := 9) (t := 12)
    (D := 16) (ψ := (292484842603/10000000000000 : ℝ)) half_15_05_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_05_φ1, half_15_05_φ2, half_15_05_φ3, half_15_05_φ4, half_15_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_05_φ1, half_15_05_φ2, half_15_05_φ3, half_15_05_φ4, half_15_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_05_φ1, half_15_05_φ2, half_15_05_φ3, half_15_05_φ4, half_15_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_05 half_12_05
    (by simpa only [half_15_05_φ5, show (2:ℝ)*16=32 by norm_num] using half_15_05_hx5)
  exact h.weaken (by norm_num [half_15_05_φ1, half_15_05_φ2, half_15_05_φ3, half_15_05_φ4, half_15_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_05_hx3 : SourcePowerBound (powerBoxCross 18 12 8 half_15_05_φ3) (8693285444209/625000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 12) (u := 10) (t := 13)
    (D := 8) (ψ := (357462221899/10000000000000 : ℝ)) half_15_05_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_05_φ1, half_15_05_φ2, half_15_05_φ3, half_15_05_φ4, half_15_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_05_φ1, half_15_05_φ2, half_15_05_φ3, half_15_05_φ4, half_15_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_05_φ1, half_15_05_φ2, half_15_05_φ3, half_15_05_φ4, half_15_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_05 half_13_05
    (by simpa only [half_15_05_φ4, show (2:ℝ)*8=16 by norm_num] using half_15_05_hx4)
  exact h.weaken (by norm_num [half_15_05_φ1, half_15_05_φ2, half_15_05_φ3, half_15_05_φ4, half_15_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_05_hx2 : SourcePowerBound (powerBoxCross 18 13 4 half_15_05_φ2) (76949112334021/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 13) (u := 11) (t := 14)
    (D := 4) (ψ := (15222176319/400000000000 : ℝ)) half_15_05_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_05_φ1, half_15_05_φ2, half_15_05_φ3, half_15_05_φ4, half_15_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_05_φ1, half_15_05_φ2, half_15_05_φ3, half_15_05_φ4, half_15_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_05_φ1, half_15_05_φ2, half_15_05_φ3, half_15_05_φ4, half_15_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_05 half_14_05
    (by simpa only [half_15_05_φ3, show (2:ℝ)*4=8 by norm_num] using half_15_05_hx3)
  exact h.weaken (by norm_num [half_15_05_φ1, half_15_05_φ2, half_15_05_φ3, half_15_05_φ4, half_15_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_05_hx1 : SourcePowerBound (powerBoxCross 18 14 2 half_15_05_φ1) (170694475219587/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 14) (u := 12) (t := 15)
    (D := 2) (ψ := (78798730597/2000000000000 : ℝ)) half_15_05_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_05_φ1, half_15_05_φ2, half_15_05_φ3, half_15_05_φ4, half_15_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_05_φ1, half_15_05_φ2, half_15_05_φ3, half_15_05_φ4, half_15_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_05_φ1, half_15_05_φ2, half_15_05_φ3, half_15_05_φ4, half_15_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_13_05 half_15_04
    (by simpa only [half_15_05_φ2, show (2:ℝ)*2=4 by norm_num] using half_15_05_hx2)
  exact h.weaken (by norm_num [half_15_05_φ1, half_15_05_φ2, half_15_05_φ3, half_15_05_φ4, half_15_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_05 : AdmissibleExponent 18 30 (181880835185793/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 13) (ψ := (207154814189/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_14_05
    (by simpa only [half_15_05_φ1] using half_15_05_hx1)
  exact admissibleExponent_mono h (by norm_num [half_15_05_φ1, half_15_05_φ2, half_15_05_φ3, half_15_05_φ4, half_15_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_16_05_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (213657381133/5000000000000 : ℝ)

def half_16_05_φ2 : Fin 2 → ℝ := Fin.snoc half_16_05_φ1 (100974214631/2500000000000 : ℝ)

def half_16_05_φ3 : Fin 3 → ℝ := Fin.snoc half_16_05_φ2 (392077134547/10000000000000 : ℝ)

def half_16_05_φ4 : Fin 4 → ℝ := Fin.snoc half_16_05_φ3 (187620477951/5000000000000 : ℝ)

def half_16_05_φ5 : Fin 5 → ℝ := Fin.snoc half_16_05_φ4 (169403257663/5000000000000 : ℝ)

def half_16_05_φ6 : Fin 6 → ℝ := Fin.snoc half_16_05_φ5 (21758262523/1000000000000 : ℝ)

theorem half_16_05_hF2 : SourcePowerBound (paddedMoment 18 0 2 64 half_16_05_φ6) (18019827711691/2000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 6) (r := 0) (D := 64)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_16_05_φ6 (by norm_num [half_16_05_φ1, half_16_05_φ2, half_16_05_φ3, half_16_05_φ4, half_16_05_φ5, half_16_05_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_05_φ1, half_16_05_φ2, half_16_05_φ3, half_16_05_φ4, half_16_05_φ5, half_16_05_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_05_φ1, half_16_05_φ2, half_16_05_φ3, half_16_05_φ4, half_16_05_φ5, half_16_05_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_16_05_φ1, half_16_05_φ2, half_16_05_φ3, half_16_05_φ4, half_16_05_φ5, half_16_05_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_16_05_hx6 : SourcePowerBound (powerBoxCross 18 10 64 half_16_05_φ6) (115297141230069/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 10) (r := 2) (v := 13) (w := 14) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_16_05_φ6 (by norm_num [half_16_05_φ1, half_16_05_φ2, half_16_05_φ3, half_16_05_φ4, half_16_05_φ5, half_16_05_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_05_φ1, half_16_05_φ2, half_16_05_φ3, half_16_05_φ4, half_16_05_φ5, half_16_05_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_16_05_hF2 half_13_05 half_14_05
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_16_05_φ1, half_16_05_φ2, half_16_05_φ3, half_16_05_φ4, half_16_05_φ5, half_16_05_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_05_hx5 : SourcePowerBound (powerBoxCross 18 11 32 half_16_05_φ5) (124273828118731/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 5) (s := 11) (u := 9) (t := 12)
    (D := 32) (ψ := (21758262523/1000000000000 : ℝ)) half_16_05_φ5
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_05_φ1, half_16_05_φ2, half_16_05_φ3, half_16_05_φ4, half_16_05_φ5, half_16_05_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_05_φ1, half_16_05_φ2, half_16_05_φ3, half_16_05_φ4, half_16_05_φ5, half_16_05_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_05_φ1, half_16_05_φ2, half_16_05_φ3, half_16_05_φ4, half_16_05_φ5, half_16_05_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_05 half_12_05
    (by simpa only [half_16_05_φ6, show (2:ℝ)*32=64 by norm_num] using half_16_05_hx6)
  exact h.weaken (by norm_num [half_16_05_φ1, half_16_05_φ2, half_16_05_φ3, half_16_05_φ4, half_16_05_φ5, half_16_05_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_05_hx4 : SourcePowerBound (powerBoxCross 18 12 16 half_16_05_φ4) (136339068877773/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 12) (u := 10) (t := 13)
    (D := 16) (ψ := (169403257663/5000000000000 : ℝ)) half_16_05_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_05_φ1, half_16_05_φ2, half_16_05_φ3, half_16_05_φ4, half_16_05_φ5, half_16_05_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_05_φ1, half_16_05_φ2, half_16_05_φ3, half_16_05_φ4, half_16_05_φ5, half_16_05_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_05_φ1, half_16_05_φ2, half_16_05_φ3, half_16_05_φ4, half_16_05_φ5, half_16_05_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_05 half_13_05
    (by simpa only [half_16_05_φ5, show (2:ℝ)*16=32 by norm_num] using half_16_05_hx5)
  exact h.weaken (by norm_num [half_16_05_φ1, half_16_05_φ2, half_16_05_φ3, half_16_05_φ4, half_16_05_φ5, half_16_05_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_05_hx3 : SourcePowerBound (powerBoxCross 18 13 8 half_16_05_φ3) (30092711018683/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 13) (u := 11) (t := 14)
    (D := 8) (ψ := (187620477951/5000000000000 : ℝ)) half_16_05_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_05_φ1, half_16_05_φ2, half_16_05_φ3, half_16_05_φ4, half_16_05_φ5, half_16_05_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_05_φ1, half_16_05_φ2, half_16_05_φ3, half_16_05_φ4, half_16_05_φ5, half_16_05_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_05_φ1, half_16_05_φ2, half_16_05_φ3, half_16_05_φ4, half_16_05_φ5, half_16_05_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_05 half_14_05
    (by simpa only [half_16_05_φ4, show (2:ℝ)*8=16 by norm_num] using half_16_05_hx4)
  exact h.weaken (by norm_num [half_16_05_φ1, half_16_05_φ2, half_16_05_φ3, half_16_05_φ4, half_16_05_φ5, half_16_05_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_05_hx2 : SourcePowerBound (powerBoxCross 18 14 4 half_16_05_φ2) (20806098419307/1250000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 14) (u := 12) (t := 15)
    (D := 4) (ψ := (392077134547/10000000000000 : ℝ)) half_16_05_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_05_φ1, half_16_05_φ2, half_16_05_φ3, half_16_05_φ4, half_16_05_φ5, half_16_05_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_05_φ1, half_16_05_φ2, half_16_05_φ3, half_16_05_φ4, half_16_05_φ5, half_16_05_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_05_φ1, half_16_05_φ2, half_16_05_φ3, half_16_05_φ4, half_16_05_φ5, half_16_05_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_13_05 half_15_05
    (by simpa only [half_16_05_φ3, show (2:ℝ)*4=8 by norm_num] using half_16_05_hx3)
  exact h.weaken (by norm_num [half_16_05_φ1, half_16_05_φ2, half_16_05_φ3, half_16_05_φ4, half_16_05_φ5, half_16_05_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_05_hx1 : SourcePowerBound (powerBoxCross 18 15 2 half_16_05_φ1) (184536113363261/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 15) (u := 13) (t := 16)
    (D := 2) (ψ := (100974214631/2500000000000 : ℝ)) half_16_05_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_05_φ1, half_16_05_φ2, half_16_05_φ3, half_16_05_φ4, half_16_05_φ5, half_16_05_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_05_φ1, half_16_05_φ2, half_16_05_φ3, half_16_05_φ4, half_16_05_φ5, half_16_05_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_05_φ1, half_16_05_φ2, half_16_05_φ3, half_16_05_φ4, half_16_05_φ5, half_16_05_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_14_05 half_16_04
    (by simpa only [half_16_05_φ2, show (2:ℝ)*2=4 by norm_num] using half_16_05_hx2)
  exact h.weaken (by norm_num [half_16_05_φ1, half_16_05_φ2, half_16_05_φ3, half_16_05_φ4, half_16_05_φ5, half_16_05_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_05 : AdmissibleExponent 18 32 (7877129658759/400000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 14) (ψ := (213657381133/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_15_05
    (by simpa only [half_16_05_φ1] using half_16_05_hx1)
  exact admissibleExponent_mono h (by norm_num [half_16_05_φ1, half_16_05_φ2, half_16_05_φ3, half_16_05_φ4, half_16_05_φ5, half_16_05_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_17_05_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (110085898241/2500000000000 : ℝ)

def half_17_05_φ2 : Fin 2 → ℝ := Fin.snoc half_17_05_φ1 (413407865193/10000000000000 : ℝ)

def half_17_05_φ3 : Fin 3 → ℝ := Fin.snoc half_17_05_φ2 (80507757297/2000000000000 : ℝ)

def half_17_05_φ4 : Fin 4 → ℝ := Fin.snoc half_17_05_φ3 (194494953443/5000000000000 : ℝ)

def half_17_05_φ5 : Fin 5 → ℝ := Fin.snoc half_17_05_φ4 (5715332669/156250000000 : ℝ)

def half_17_05_φ6 : Fin 6 → ℝ := Fin.snoc half_17_05_φ5 (60876492849/2000000000000 : ℝ)

theorem half_17_05_hF2 : SourcePowerBound (paddedMoment 18 0 2 64 half_17_05_φ6) (81912360763961/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 6) (r := 0) (D := 64)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_17_05_φ6 (by norm_num [half_17_05_φ1, half_17_05_φ2, half_17_05_φ3, half_17_05_φ4, half_17_05_φ5, half_17_05_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_05_φ1, half_17_05_φ2, half_17_05_φ3, half_17_05_φ4, half_17_05_φ5, half_17_05_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_05_φ1, half_17_05_φ2, half_17_05_φ3, half_17_05_φ4, half_17_05_φ5, half_17_05_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_17_05_φ1, half_17_05_φ2, half_17_05_φ3, half_17_05_φ4, half_17_05_φ5, half_17_05_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_17_05_hx6 : SourcePowerBound (powerBoxCross 18 11 64 half_17_05_φ6) (122484696290161/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 11) (r := 2) (v := 14) (w := 15) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_17_05_φ6 (by norm_num [half_17_05_φ1, half_17_05_φ2, half_17_05_φ3, half_17_05_φ4, half_17_05_φ5, half_17_05_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_05_φ1, half_17_05_φ2, half_17_05_φ3, half_17_05_φ4, half_17_05_φ5, half_17_05_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_17_05_hF2 half_14_05 half_15_05
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_17_05_φ1, half_17_05_φ2, half_17_05_φ3, half_17_05_φ4, half_17_05_φ5, half_17_05_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_05_hx5 : SourcePowerBound (powerBoxCross 18 12 32 half_17_05_φ5) (33355645211389/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 5) (s := 12) (u := 10) (t := 13)
    (D := 32) (ψ := (60876492849/2000000000000 : ℝ)) half_17_05_φ5
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_05_φ1, half_17_05_φ2, half_17_05_φ3, half_17_05_φ4, half_17_05_φ5, half_17_05_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_05_φ1, half_17_05_φ2, half_17_05_φ3, half_17_05_φ4, half_17_05_φ5, half_17_05_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_05_φ1, half_17_05_φ2, half_17_05_φ3, half_17_05_φ4, half_17_05_φ5, half_17_05_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_05 half_13_05
    (by simpa only [half_17_05_φ6, show (2:ℝ)*32=64 by norm_num] using half_17_05_hx6)
  exact h.weaken (by norm_num [half_17_05_φ1, half_17_05_φ2, half_17_05_φ3, half_17_05_φ4, half_17_05_φ5, half_17_05_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_05_hx4 : SourcePowerBound (powerBoxCross 18 13 16 half_17_05_φ4) (36695396651689/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 13) (u := 11) (t := 14)
    (D := 16) (ψ := (5715332669/156250000000 : ℝ)) half_17_05_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_05_φ1, half_17_05_φ2, half_17_05_φ3, half_17_05_φ4, half_17_05_φ5, half_17_05_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_05_φ1, half_17_05_φ2, half_17_05_φ3, half_17_05_φ4, half_17_05_φ5, half_17_05_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_05_φ1, half_17_05_φ2, half_17_05_φ3, half_17_05_φ4, half_17_05_φ5, half_17_05_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_05 half_14_05
    (by simpa only [half_17_05_φ5, show (2:ℝ)*16=32 by norm_num] using half_17_05_hx5)
  exact h.weaken (by norm_num [half_17_05_φ1, half_17_05_φ2, half_17_05_φ3, half_17_05_φ4, half_17_05_φ5, half_17_05_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_05_hx3 : SourcePowerBound (powerBoxCross 18 14 8 half_17_05_φ3) (16209036170633/1000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 14) (u := 12) (t := 15)
    (D := 8) (ψ := (194494953443/5000000000000 : ℝ)) half_17_05_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_05_φ1, half_17_05_φ2, half_17_05_φ3, half_17_05_φ4, half_17_05_φ5, half_17_05_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_05_φ1, half_17_05_φ2, half_17_05_φ3, half_17_05_φ4, half_17_05_φ5, half_17_05_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_05_φ1, half_17_05_φ2, half_17_05_φ3, half_17_05_φ4, half_17_05_φ5, half_17_05_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_13_05 half_15_05
    (by simpa only [half_17_05_φ4, show (2:ℝ)*8=16 by norm_num] using half_17_05_hx4)
  exact h.weaken (by norm_num [half_17_05_φ1, half_17_05_φ2, half_17_05_φ3, half_17_05_φ4, half_17_05_φ5, half_17_05_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_05_hx2 : SourcePowerBound (powerBoxCross 18 15 4 half_17_05_φ2) (22410037393193/1250000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 15) (u := 13) (t := 16)
    (D := 4) (ψ := (80507757297/2000000000000 : ℝ)) half_17_05_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_05_φ1, half_17_05_φ2, half_17_05_φ3, half_17_05_φ4, half_17_05_φ5, half_17_05_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_05_φ1, half_17_05_φ2, half_17_05_φ3, half_17_05_φ4, half_17_05_φ5, half_17_05_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_05_φ1, half_17_05_φ2, half_17_05_φ3, half_17_05_φ4, half_17_05_φ5, half_17_05_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_14_05 half_16_05
    (by simpa only [half_17_05_φ3, show (2:ℝ)*4=8 by norm_num] using half_17_05_hx3)
  exact h.weaken (by norm_num [half_17_05_φ1, half_17_05_φ2, half_17_05_φ3, half_17_05_φ4, half_17_05_φ5, half_17_05_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_05_hx1 : SourcePowerBound (powerBoxCross 18 16 2 half_17_05_φ1) (198696976121491/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 16) (u := 14) (t := 17)
    (D := 2) (ψ := (413407865193/10000000000000 : ℝ)) half_17_05_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_05_φ1, half_17_05_φ2, half_17_05_φ3, half_17_05_φ4, half_17_05_φ5, half_17_05_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_05_φ1, half_17_05_φ2, half_17_05_φ3, half_17_05_φ4, half_17_05_φ5, half_17_05_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_05_φ1, half_17_05_φ2, half_17_05_φ3, half_17_05_φ4, half_17_05_φ5, half_17_05_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_15_05 half_17_04
    (by simpa only [half_17_05_φ2, show (2:ℝ)*2=4 by norm_num] using half_17_05_hx2)
  exact h.weaken (by norm_num [half_17_05_φ1, half_17_05_φ2, half_17_05_φ3, half_17_05_φ4, half_17_05_φ5, half_17_05_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_05 : AdmissibleExponent 18 34 (1698781020027/80000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 15) (ψ := (110085898241/2500000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_16_05
    (by simpa only [half_17_05_φ1] using half_17_05_hx1)
  exact admissibleExponent_mono h (by norm_num [half_17_05_φ1, half_17_05_φ2, half_17_05_φ3, half_17_05_φ4, half_17_05_φ5, half_17_05_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])


end Waring.SeedCompletionHigher18SimpleSeeds
