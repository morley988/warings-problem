import Waring.SeedCompletionHigher18SimpleSeedsC13

noncomputable section
set_option maxHeartbeats 2000000
namespace Waring.SeedCompletionHigher18SimpleSeeds
open SmoothMoments FirstStageTransport SeedCompletionNaturalBox
open SeedCompletionSourceBounds SeedCompletionPaddedSource SeedCompletionGeneralTerminal
open PolicyCompletionMajorPowerRanges

def half_9_14_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (21489926931/625000000000 : ℝ)

def half_9_14_φ2 : Fin 2 → ℝ := Fin.snoc half_9_14_φ1 (77086285991/2500000000000 : ℝ)

def half_9_14_φ3 : Fin 3 → ℝ := Fin.snoc half_9_14_φ2 (67222956209/5000000000000 : ℝ)

theorem half_9_14_hF2 : SourcePowerBound (paddedMoment 18 0 2 8 half_9_14_φ3) (34940937874411/5000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_14_φ3 (by norm_num [half_9_14_φ1, half_9_14_φ2, half_9_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_14_φ1, half_9_14_φ2, half_9_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_14_φ1, half_9_14_φ2, half_9_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_14_φ1, half_9_14_φ2, half_9_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_9_14_hF1 : SourcePowerBound (paddedMoment 18 0 1 8 half_9_14_φ3) (13313645958137/5000000000000 : ℝ) := by
  have h := padded_second_power (k := 18) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_14_φ3 (by norm_num [half_9_14_φ1, half_9_14_φ2, half_9_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_14_φ1, half_9_14_φ2, half_9_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_14_φ1, half_9_14_φ2, half_9_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_14_φ1, half_9_14_φ2, half_9_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_9_14_hx3 : SourcePowerBound (powerBoxCross 18 6 8 half_9_14_φ3) (38496518527573/5000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 18) (s := 6) (r := 1) (v := 2) (t := 10) (D := 8)
    (a := (3/10 : ℝ)) (b := (1/10 : ℝ)) (c := (3/5 : ℝ))
    (by norm_num) half_9_14_φ3 (by norm_num [half_9_14_φ1, half_9_14_φ2, half_9_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_14_φ1, half_9_14_φ2, half_9_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_9_14_hF1 half_9_14_hF2 half_10_13
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_9_14_φ1, half_9_14_φ2, half_9_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_9_14_hx2 : SourcePowerBound (powerBoxCross 18 7 4 half_9_14_φ2) (8426942177873/1000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 7) (u := 5) (t := 8)
    (D := 4) (ψ := (67222956209/5000000000000 : ℝ)) half_9_14_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_14_φ1, half_9_14_φ2, half_9_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_14_φ1, half_9_14_φ2, half_9_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_14_φ1, half_9_14_φ2, half_9_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_6 SeedCompletionEven18SecondSeeds.degree18_half_8
    (by simpa only [half_9_14_φ3, show (2:ℝ)*4=8 by norm_num] using half_9_14_hx3)
  exact h.weaken (by norm_num [half_9_14_φ1, half_9_14_φ2, half_9_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_9_14_hx1 : SourcePowerBound (powerBoxCross 18 8 2 half_9_14_φ1) (47087399020997/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 8) (u := 6) (t := 9)
    (D := 2) (ψ := (77086285991/2500000000000 : ℝ)) half_9_14_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_14_φ1, half_9_14_φ2, half_9_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_14_φ1, half_9_14_φ2, half_9_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_14_φ1, half_9_14_φ2, half_9_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_7 half_9_13
    (by simpa only [half_9_14_φ2, show (2:ℝ)*2=4 by norm_num] using half_9_14_hx2)
  exact h.weaken (by norm_num [half_9_14_φ1, half_9_14_φ2, half_9_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_9_14 : AdmissibleExponent 18 18 (49666190252717/5000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 7) (ψ := (21489926931/625000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_8
    (by simpa only [half_9_14_φ1] using half_9_14_hx1)
  exact admissibleExponent_mono h (by norm_num [half_9_14_φ1, half_9_14_φ2, half_9_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_10_14_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (4421860597/125000000000 : ℝ)

def half_10_14_φ2 : Fin 2 → ℝ := Fin.snoc half_10_14_φ1 (329256567039/10000000000000 : ℝ)

def half_10_14_φ3 : Fin 3 → ℝ := Fin.snoc half_10_14_φ2 (22993878297/1000000000000 : ℝ)

theorem half_10_14_hF2 : SourcePowerBound (paddedMoment 18 0 2 8 half_10_14_φ3) (63439845913781/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_10_14_φ3 (by norm_num [half_10_14_φ1, half_10_14_φ2, half_10_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_14_φ1, half_10_14_φ2, half_10_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_14_φ1, half_10_14_φ2, half_10_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_10_14_φ1, half_10_14_φ2, half_10_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_10_14_hx3 : SourcePowerBound (powerBoxCross 18 7 8 half_10_14_φ3) (86477914109419/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 7) (r := 2) (v := 9) (w := 10) (D := 8)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_10_14_φ3 (by norm_num [half_10_14_φ1, half_10_14_φ2, half_10_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_14_φ1, half_10_14_φ2, half_10_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_10_14_hF2 half_9_14 half_10_13
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_10_14_φ1, half_10_14_φ2, half_10_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_14_hx2 : SourcePowerBound (powerBoxCross 18 8 4 half_10_14_φ2) (23800493920859/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 8) (u := 6) (t := 9)
    (D := 4) (ψ := (22993878297/1000000000000 : ℝ)) half_10_14_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_14_φ1, half_10_14_φ2, half_10_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_14_φ1, half_10_14_φ2, half_10_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_14_φ1, half_10_14_φ2, half_10_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_7 half_9_14
    (by simpa only [half_10_14_φ3, show (2:ℝ)*4=8 by norm_num] using half_10_14_hx3)
  exact h.weaken (by norm_num [half_10_14_φ1, half_10_14_φ2, half_10_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_14_hx1 : SourcePowerBound (powerBoxCross 18 9 2 half_10_14_φ1) (53086128919153/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 9) (u := 7) (t := 10)
    (D := 2) (ψ := (329256567039/10000000000000 : ℝ)) half_10_14_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_14_φ1, half_10_14_φ2, half_10_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_14_φ1, half_10_14_φ2, half_10_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_14_φ1, half_10_14_φ2, half_10_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_8 half_10_13
    (by simpa only [half_10_14_φ2, show (2:ℝ)*2=4 by norm_num] using half_10_14_hx2)
  exact h.weaken (by norm_num [half_10_14_φ1, half_10_14_φ2, half_10_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_14 : AdmissibleExponent 18 20 (56092994125113/5000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 8) (ψ := (4421860597/125000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_9_14
    (by simpa only [half_10_14_φ1] using half_10_14_hx1)
  exact admissibleExponent_mono h (by norm_num [half_10_14_φ1, half_10_14_φ2, half_10_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_11_14_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (364748150133/10000000000000 : ℝ)

def half_11_14_φ2 : Fin 2 → ℝ := Fin.snoc half_11_14_φ1 (173197431377/5000000000000 : ℝ)

def half_11_14_φ3 : Fin 3 → ℝ := Fin.snoc half_11_14_φ2 (1842053231/62500000000 : ℝ)

theorem half_11_14_hF2 : SourcePowerBound (paddedMoment 18 0 2 8 half_11_14_φ3) (58700551977803/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_11_14_φ3 (by norm_num [half_11_14_φ1, half_11_14_φ2, half_11_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_14_φ1, half_11_14_φ2, half_11_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_14_φ1, half_11_14_φ2, half_11_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_11_14_φ1, half_11_14_φ2, half_11_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_11_14_hx3 : SourcePowerBound (powerBoxCross 18 8 8 half_11_14_φ3) (188063967471/19531250000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 8) (r := 2) (v := 10) (w := 11) (D := 8)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_11_14_φ3 (by norm_num [half_11_14_φ1, half_11_14_φ2, half_11_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_14_φ1, half_11_14_φ2, half_11_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_11_14_hF2 half_10_14 half_11_13
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_11_14_φ1, half_11_14_φ2, half_11_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_14_hx2 : SourcePowerBound (powerBoxCross 18 9 4 half_11_14_φ2) (106414103980951/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 9) (u := 7) (t := 10)
    (D := 4) (ψ := (1842053231/62500000000 : ℝ)) half_11_14_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_14_φ1, half_11_14_φ2, half_11_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_14_φ1, half_11_14_φ2, half_11_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_14_φ1, half_11_14_φ2, half_11_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_8 half_10_14
    (by simpa only [half_11_14_φ3, show (2:ℝ)*4=8 by norm_num] using half_11_14_hx3)
  exact h.weaken (by norm_num [half_11_14_φ1, half_11_14_φ2, half_11_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_14_hx1 : SourcePowerBound (powerBoxCross 18 10 2 half_11_14_φ1) (14807346653983/1250000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 10) (u := 8) (t := 11)
    (D := 2) (ψ := (173197431377/5000000000000 : ℝ)) half_11_14_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_14_φ1, half_11_14_φ2, half_11_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_14_φ1, half_11_14_φ2, half_11_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_14_φ1, half_11_14_φ2, half_11_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_14 half_11_13
    (by simpa only [half_11_14_φ2, show (2:ℝ)*2=4 by norm_num] using half_11_14_hx2)
  exact h.weaken (by norm_num [half_11_14_φ1, half_11_14_φ2, half_11_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_14 : AdmissibleExponent 18 22 (125388988084391/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 9) (ψ := (364748150133/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_10_14
    (by simpa only [half_11_14_φ1] using half_11_14_hx1)
  exact admissibleExponent_mono h (by norm_num [half_11_14_φ1, half_11_14_φ2, half_11_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_12_14_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (374942019003/10000000000000 : ℝ)

def half_12_14_φ2 : Fin 2 → ℝ := Fin.snoc half_12_14_φ1 (360586869293/10000000000000 : ℝ)

def half_12_14_φ3 : Fin 3 → ℝ := Fin.snoc half_12_14_φ2 (329430076077/10000000000000 : ℝ)

def half_12_14_φ4 : Fin 4 → ℝ := Fin.snoc half_12_14_φ3 (106453688803/5000000000000 : ℝ)

theorem half_12_14_hF2 : SourcePowerBound (paddedMoment 18 0 2 16 half_12_14_φ4) (74828816559071/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_12_14_φ4 (by norm_num [half_12_14_φ1, half_12_14_φ2, half_12_14_φ3, half_12_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_14_φ1, half_12_14_φ2, half_12_14_φ3, half_12_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_14_φ1, half_12_14_φ2, half_12_14_φ3, half_12_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_12_14_φ1, half_12_14_φ2, half_12_14_φ3, half_12_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_12_14_hF1 : SourcePowerBound (paddedMoment 18 0 1 16 half_12_14_φ4) (28276272186357/10000000000000 : ℝ) := by
  have h := padded_second_power (k := 18) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_12_14_φ4 (by norm_num [half_12_14_φ1, half_12_14_φ2, half_12_14_φ3, half_12_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_14_φ1, half_12_14_φ2, half_12_14_φ3, half_12_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_14_φ1, half_12_14_φ2, half_12_14_φ3, half_12_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_12_14_φ1, half_12_14_φ2, half_12_14_φ3, half_12_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_12_14_hx4 : SourcePowerBound (powerBoxCross 18 8 16 half_12_14_φ4) (19566141602613/2000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 18) (s := 8) (r := 1) (v := 2) (t := 11) (D := 16)
    (a := (1/22 : ℝ)) (b := (5/22 : ℝ)) (c := (8/11 : ℝ))
    (by norm_num) half_12_14_φ4 (by norm_num [half_12_14_φ1, half_12_14_φ2, half_12_14_φ3, half_12_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_14_φ1, half_12_14_φ2, half_12_14_φ3, half_12_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_12_14_hF1 half_12_14_hF2 half_11_14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_12_14_φ1, half_12_14_φ2, half_12_14_φ3, half_12_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_14_hx3 : SourcePowerBound (powerBoxCross 18 9 8 half_12_14_φ3) (21315865714663/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 9) (u := 7) (t := 10)
    (D := 8) (ψ := (106453688803/5000000000000 : ℝ)) half_12_14_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_14_φ1, half_12_14_φ2, half_12_14_φ3, half_12_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_14_φ1, half_12_14_φ2, half_12_14_φ3, half_12_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_14_φ1, half_12_14_φ2, half_12_14_φ3, half_12_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_8 half_10_14
    (by simpa only [half_12_14_φ4, show (2:ℝ)*8=16 by norm_num] using half_12_14_hx4)
  exact h.weaken (by norm_num [half_12_14_φ1, half_12_14_φ2, half_12_14_φ3, half_12_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_14_hx2 : SourcePowerBound (powerBoxCross 18 10 4 half_12_14_φ2) (58960478637239/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 10) (u := 8) (t := 11)
    (D := 4) (ψ := (329430076077/10000000000000 : ℝ)) half_12_14_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_14_φ1, half_12_14_φ2, half_12_14_φ3, half_12_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_14_φ1, half_12_14_φ2, half_12_14_φ3, half_12_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_14_φ1, half_12_14_φ2, half_12_14_φ3, half_12_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_14 half_11_14
    (by simpa only [half_12_14_φ3, show (2:ℝ)*4=8 by norm_num] using half_12_14_hx3)
  exact h.weaken (by norm_num [half_12_14_φ1, half_12_14_φ2, half_12_14_φ3, half_12_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_14_hx1 : SourcePowerBound (powerBoxCross 18 11 2 half_12_14_φ1) (1310625700681/100000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 11) (u := 9) (t := 12)
    (D := 2) (ψ := (360586869293/10000000000000 : ℝ)) half_12_14_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_14_φ1, half_12_14_φ2, half_12_14_φ3, half_12_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_14_φ1, half_12_14_φ2, half_12_14_φ3, half_12_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_14_φ1, half_12_14_φ2, half_12_14_φ3, half_12_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_14 half_12_13
    (by simpa only [half_12_14_φ2, show (2:ℝ)*2=4 by norm_num] using half_12_14_hx2)
  exact h.weaken (by norm_num [half_12_14_φ1, half_12_14_φ2, half_12_14_φ3, half_12_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_14 : AdmissibleExponent 18 24 (138936352467163/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 10) (ψ := (374942019003/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_11_14
    (by simpa only [half_12_14_φ1] using half_12_14_hx1)
  exact admissibleExponent_mono h (by norm_num [half_12_14_φ1, half_12_14_φ2, half_12_14_φ3, half_12_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_13_14_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (38460467427/1000000000000 : ℝ)

def half_13_14_φ2 : Fin 2 → ℝ := Fin.snoc half_13_14_φ1 (185984212133/5000000000000 : ℝ)

def half_13_14_φ3 : Fin 3 → ℝ := Fin.snoc half_13_14_φ2 (349893184369/10000000000000 : ℝ)

def half_13_14_φ4 : Fin 4 → ℝ := Fin.snoc half_13_14_φ3 (141656690683/5000000000000 : ℝ)

theorem half_13_14_hF2 : SourcePowerBound (paddedMoment 18 0 2 16 half_13_14_φ4) (69121237122179/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_13_14_φ4 (by norm_num [half_13_14_φ1, half_13_14_φ2, half_13_14_φ3, half_13_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_14_φ1, half_13_14_φ2, half_13_14_φ3, half_13_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_14_φ1, half_13_14_φ2, half_13_14_φ3, half_13_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_13_14_φ1, half_13_14_φ2, half_13_14_φ3, half_13_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_13_14_hx4 : SourcePowerBound (powerBoxCross 18 9 16 half_13_14_φ4) (26750188708601/2500000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 9) (r := 2) (v := 12) (w := 12) (D := 16)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_13_14_φ4 (by norm_num [half_13_14_φ1, half_13_14_φ2, half_13_14_φ3, half_13_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_14_φ1, half_13_14_φ2, half_13_14_φ3, half_13_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_13_14_hF2 half_12_14 half_12_14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_13_14_φ1, half_13_14_φ2, half_13_14_φ3, half_13_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_14_hx3 : SourcePowerBound (powerBoxCross 18 10 8 half_13_14_φ3) (11726113741817/1000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 10) (u := 8) (t := 11)
    (D := 8) (ψ := (141656690683/5000000000000 : ℝ)) half_13_14_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_14_φ1, half_13_14_φ2, half_13_14_φ3, half_13_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_14_φ1, half_13_14_φ2, half_13_14_φ3, half_13_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_14_φ1, half_13_14_φ2, half_13_14_φ3, half_13_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_14 half_11_14
    (by simpa only [half_13_14_φ4, show (2:ℝ)*8=16 by norm_num] using half_13_14_hx4)
  exact h.weaken (by norm_num [half_13_14_φ1, half_13_14_φ2, half_13_14_φ3, half_13_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_14_hx2 : SourcePowerBound (powerBoxCross 18 11 4 half_13_14_φ2) (32434020880587/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 11) (u := 9) (t := 12)
    (D := 4) (ψ := (349893184369/10000000000000 : ℝ)) half_13_14_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_14_φ1, half_13_14_φ2, half_13_14_φ3, half_13_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_14_φ1, half_13_14_φ2, half_13_14_φ3, half_13_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_14_φ1, half_13_14_φ2, half_13_14_φ3, half_13_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_14 half_12_14
    (by simpa only [half_13_14_φ3, show (2:ℝ)*4=8 by norm_num] using half_13_14_hx3)
  exact h.weaken (by norm_num [half_13_14_φ1, half_13_14_φ2, half_13_14_φ3, half_13_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_14_hx1 : SourcePowerBound (powerBoxCross 18 12 2 half_13_14_φ1) (143977400082961/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 12) (u := 10) (t := 13)
    (D := 2) (ψ := (185984212133/5000000000000 : ℝ)) half_13_14_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_14_φ1, half_13_14_φ2, half_13_14_φ3, half_13_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_14_φ1, half_13_14_φ2, half_13_14_φ3, half_13_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_14_φ1, half_13_14_φ2, half_13_14_φ3, half_13_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_14 half_13_13
    (by simpa only [half_13_14_φ2, show (2:ℝ)*2=4 by norm_num] using half_13_14_hx2)
  exact h.weaken (by norm_num [half_13_14_φ1, half_13_14_φ2, half_13_14_φ3, half_13_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_14 : AdmissibleExponent 18 26 (152823307591171/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 11) (ψ := (38460467427/1000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_12_14
    (by simpa only [half_13_14_φ1] using half_13_14_hx1)
  exact admissibleExponent_mono h (by norm_num [half_13_14_φ1, half_13_14_φ2, half_13_14_φ3, half_13_14_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_14_14_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (78872315659/2000000000000 : ℝ)

def half_14_14_φ2 : Fin 2 → ℝ := Fin.snoc half_14_14_φ1 (11968649583/312500000000 : ℝ)

def half_14_14_φ3 : Fin 3 → ℝ := Fin.snoc half_14_14_φ2 (367260837653/10000000000000 : ℝ)

def half_14_14_φ4 : Fin 4 → ℝ := Fin.snoc half_14_14_φ3 (332115818001/10000000000000 : ℝ)

def half_14_14_φ5 : Fin 5 → ℝ := Fin.snoc half_14_14_φ4 (205581040137/10000000000000 : ℝ)

theorem half_14_14_hF2 : SourcePowerBound (paddedMoment 18 0 2 32 half_14_14_φ5) (42100940451079/5000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_14_14_φ5 (by norm_num [half_14_14_φ1, half_14_14_φ2, half_14_14_φ3, half_14_14_φ4, half_14_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_14_φ1, half_14_14_φ2, half_14_14_φ3, half_14_14_φ4, half_14_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_14_φ1, half_14_14_φ2, half_14_14_φ3, half_14_14_φ4, half_14_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_14_14_φ1, half_14_14_φ2, half_14_14_φ3, half_14_14_φ4, half_14_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_14_14_hx5 : SourcePowerBound (powerBoxCross 18 9 32 half_14_14_φ5) (107722620287681/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 9) (r := 2) (v := 12) (w := 12) (D := 32)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_14_14_φ5 (by norm_num [half_14_14_φ1, half_14_14_φ2, half_14_14_φ3, half_14_14_φ4, half_14_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_14_φ1, half_14_14_φ2, half_14_14_φ3, half_14_14_φ4, half_14_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_14_14_hF2 half_12_14 half_12_14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_14_14_φ1, half_14_14_φ2, half_14_14_φ3, half_14_14_φ4, half_14_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_14_hx4 : SourcePowerBound (powerBoxCross 18 10 16 half_14_14_φ4) (116492679856937/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 10) (u := 8) (t := 11)
    (D := 16) (ψ := (205581040137/10000000000000 : ℝ)) half_14_14_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_14_φ1, half_14_14_φ2, half_14_14_φ3, half_14_14_φ4, half_14_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_14_φ1, half_14_14_φ2, half_14_14_φ3, half_14_14_φ4, half_14_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_14_φ1, half_14_14_φ2, half_14_14_φ3, half_14_14_φ4, half_14_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_14 half_11_14
    (by simpa only [half_14_14_φ5, show (2:ℝ)*16=32 by norm_num] using half_14_14_hx5)
  exact h.weaken (by norm_num [half_14_14_φ1, half_14_14_φ2, half_14_14_φ3, half_14_14_φ4, half_14_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_14_hx3 : SourcePowerBound (powerBoxCross 18 11 8 half_14_14_φ3) (64094446181121/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 11) (u := 9) (t := 12)
    (D := 8) (ψ := (332115818001/10000000000000 : ℝ)) half_14_14_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_14_φ1, half_14_14_φ2, half_14_14_φ3, half_14_14_φ4, half_14_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_14_φ1, half_14_14_φ2, half_14_14_φ3, half_14_14_φ4, half_14_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_14_φ1, half_14_14_φ2, half_14_14_φ3, half_14_14_φ4, half_14_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_14 half_12_14
    (by simpa only [half_14_14_φ4, show (2:ℝ)*8=16 by norm_num] using half_14_14_hx4)
  exact h.weaken (by norm_num [half_14_14_φ1, half_14_14_φ2, half_14_14_φ3, half_14_14_φ4, half_14_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_14_hx2 : SourcePowerBound (powerBoxCross 18 12 4 half_14_14_φ2) (70907434422103/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 12) (u := 10) (t := 13)
    (D := 4) (ψ := (367260837653/10000000000000 : ℝ)) half_14_14_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_14_φ1, half_14_14_φ2, half_14_14_φ3, half_14_14_φ4, half_14_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_14_φ1, half_14_14_φ2, half_14_14_φ3, half_14_14_φ4, half_14_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_14_φ1, half_14_14_φ2, half_14_14_φ3, half_14_14_φ4, half_14_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_14 half_13_14
    (by simpa only [half_14_14_φ3, show (2:ℝ)*4=8 by norm_num] using half_14_14_hx3)
  exact h.weaken (by norm_num [half_14_14_φ1, half_14_14_φ2, half_14_14_φ3, half_14_14_φ4, half_14_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_14_hx1 : SourcePowerBound (powerBoxCross 18 13 2 half_14_14_φ1) (157190905091293/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 13) (u := 11) (t := 14)
    (D := 2) (ψ := (11968649583/312500000000 : ℝ)) half_14_14_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_14_φ1, half_14_14_φ2, half_14_14_φ3, half_14_14_φ4, half_14_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_14_φ1, half_14_14_φ2, half_14_14_φ3, half_14_14_φ4, half_14_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_14_φ1, half_14_14_φ2, half_14_14_φ3, half_14_14_φ4, half_14_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_14 half_14_13
    (by simpa only [half_14_14_φ2, show (2:ℝ)*2=4 by norm_num] using half_14_14_hx2)
  exact h.weaken (by norm_num [half_14_14_φ1, half_14_14_φ2, half_14_14_φ3, half_14_14_φ4, half_14_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_14 : AdmissibleExponent 18 28 (41762486137167/2500000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 12) (ψ := (78872315659/2000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_13_14
    (by simpa only [half_14_14_φ1] using half_14_14_hx1)
  exact admissibleExponent_mono h (by norm_num [half_14_14_φ1, half_14_14_φ2, half_14_14_φ3, half_14_14_φ4, half_14_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_15_14_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (201820167513/5000000000000 : ℝ)

def half_15_14_φ2 : Fin 2 → ℝ := Fin.snoc half_15_14_φ1 (392987753103/10000000000000 : ℝ)

def half_15_14_φ3 : Fin 3 → ℝ := Fin.snoc half_15_14_φ2 (379457636927/10000000000000 : ℝ)

def half_15_14_φ4 : Fin 4 → ℝ := Fin.snoc half_15_14_φ3 (355225348763/10000000000000 : ℝ)

def half_15_14_φ5 : Fin 5 → ℝ := Fin.snoc half_15_14_φ4 (142145933309/5000000000000 : ℝ)

theorem half_15_14_hF2 : SourcePowerBound (paddedMoment 18 0 2 32 half_15_14_φ5) (77404250037713/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_15_14_φ5 (by norm_num [half_15_14_φ1, half_15_14_φ2, half_15_14_φ3, half_15_14_φ4, half_15_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_14_φ1, half_15_14_φ2, half_15_14_φ3, half_15_14_φ4, half_15_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_14_φ1, half_15_14_φ2, half_15_14_φ3, half_15_14_φ4, half_15_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_15_14_φ1, half_15_14_φ2, half_15_14_φ3, half_15_14_φ4, half_15_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_15_14_hx5 : SourcePowerBound (powerBoxCross 18 10 32 half_15_14_φ5) (116069470847629/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 10) (r := 2) (v := 13) (w := 14) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_15_14_φ5 (by norm_num [half_15_14_φ1, half_15_14_φ2, half_15_14_φ3, half_15_14_φ4, half_15_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_14_φ1, half_15_14_φ2, half_15_14_φ3, half_15_14_φ4, half_15_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_15_14_hF2 half_13_14 half_14_14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_15_14_φ1, half_15_14_φ2, half_15_14_φ3, half_15_14_φ4, half_15_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_14_hx4 : SourcePowerBound (powerBoxCross 18 11 16 half_15_14_φ4) (126549801508357/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 11) (u := 9) (t := 12)
    (D := 16) (ψ := (142145933309/5000000000000 : ℝ)) half_15_14_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_14_φ1, half_15_14_φ2, half_15_14_φ3, half_15_14_φ4, half_15_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_14_φ1, half_15_14_φ2, half_15_14_φ3, half_15_14_φ4, half_15_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_14_φ1, half_15_14_φ2, half_15_14_φ3, half_15_14_φ4, half_15_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_14 half_12_14
    (by simpa only [half_15_14_φ5, show (2:ℝ)*16=32 by norm_num] using half_15_14_hx5)
  exact h.weaken (by norm_num [half_15_14_φ1, half_15_14_φ2, half_15_14_φ3, half_15_14_φ4, half_15_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_14_hx3 : SourcePowerBound (powerBoxCross 18 12 8 half_15_14_φ3) (139433026523109/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 12) (u := 10) (t := 13)
    (D := 8) (ψ := (355225348763/10000000000000 : ℝ)) half_15_14_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_14_φ1, half_15_14_φ2, half_15_14_φ3, half_15_14_φ4, half_15_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_14_φ1, half_15_14_φ2, half_15_14_φ3, half_15_14_φ4, half_15_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_14_φ1, half_15_14_φ2, half_15_14_φ3, half_15_14_φ4, half_15_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_14 half_13_14
    (by simpa only [half_15_14_φ4, show (2:ℝ)*8=16 by norm_num] using half_15_14_hx4)
  exact h.weaken (by norm_num [half_15_14_φ1, half_15_14_φ2, half_15_14_φ3, half_15_14_φ4, half_15_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_14_hx2 : SourcePowerBound (powerBoxCross 18 13 4 half_15_14_φ2) (7709003785703/500000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 13) (u := 11) (t := 14)
    (D := 4) (ψ := (379457636927/10000000000000 : ℝ)) half_15_14_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_14_φ1, half_15_14_φ2, half_15_14_φ3, half_15_14_φ4, half_15_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_14_φ1, half_15_14_φ2, half_15_14_φ3, half_15_14_φ4, half_15_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_14_φ1, half_15_14_φ2, half_15_14_φ3, half_15_14_φ4, half_15_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_14 half_14_14
    (by simpa only [half_15_14_φ3, show (2:ℝ)*4=8 by norm_num] using half_15_14_hx3)
  exact h.weaken (by norm_num [half_15_14_φ1, half_15_14_φ2, half_15_14_φ3, half_15_14_φ4, half_15_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_14_hx1 : SourcePowerBound (powerBoxCross 18 14 2 half_15_14_φ1) (17071077532533/1000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 14) (u := 12) (t := 15)
    (D := 2) (ψ := (392987753103/10000000000000 : ℝ)) half_15_14_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_14_φ1, half_15_14_φ2, half_15_14_φ3, half_15_14_φ4, half_15_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_14_φ1, half_15_14_φ2, half_15_14_φ3, half_15_14_φ4, half_15_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_14_φ1, half_15_14_φ2, half_15_14_φ3, half_15_14_φ4, half_15_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_13_14 half_15_13
    (by simpa only [half_15_14_φ2, show (2:ℝ)*2=4 by norm_num] using half_15_14_hx2)
  exact h.weaken (by norm_num [half_15_14_φ1, half_15_14_φ2, half_15_14_φ3, half_15_14_φ4, half_15_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_14 : AdmissibleExponent 18 30 (22701133046379/1250000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 13) (ψ := (201820167513/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_14_14
    (by simpa only [half_15_14_φ1] using half_15_14_hx1)
  exact admissibleExponent_mono h (by norm_num [half_15_14_φ1, half_15_14_φ2, half_15_14_φ3, half_15_14_φ4, half_15_14_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_16_14_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (412895646829/10000000000000 : ℝ)

def half_16_14_φ2 : Fin 2 → ℝ := Fin.snoc half_16_14_φ1 (201347496613/5000000000000 : ℝ)

def half_16_14_φ3 : Fin 3 → ℝ := Fin.snoc half_16_14_φ2 (195548761037/5000000000000 : ℝ)

def half_16_14_φ4 : Fin 4 → ℝ := Fin.snoc half_16_14_φ3 (7482053257/200000000000 : ℝ)

def half_16_14_φ5 : Fin 5 → ℝ := Fin.snoc half_16_14_φ4 (13452080259/400000000000 : ℝ)

def half_16_14_φ6 : Fin 6 → ℝ := Fin.snoc half_16_14_φ5 (208227084589/10000000000000 : ℝ)

theorem half_16_14_hF2 : SourcePowerBound (paddedMoment 18 0 2 64 half_16_14_φ6) (91608684281807/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 6) (r := 0) (D := 64)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_16_14_φ6 (by norm_num [half_16_14_φ1, half_16_14_φ2, half_16_14_φ3, half_16_14_φ4, half_16_14_φ5, half_16_14_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_14_φ1, half_16_14_φ2, half_16_14_φ3, half_16_14_φ4, half_16_14_φ5, half_16_14_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_14_φ1, half_16_14_φ2, half_16_14_φ3, half_16_14_φ4, half_16_14_φ5, half_16_14_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_16_14_φ1, half_16_14_φ2, half_16_14_φ3, half_16_14_φ4, half_16_14_φ5, half_16_14_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_16_14_hx6 : SourcePowerBound (powerBoxCross 18 10 64 half_16_14_φ6) (28990131421793/2500000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 10) (r := 2) (v := 13) (w := 14) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_16_14_φ6 (by norm_num [half_16_14_φ1, half_16_14_φ2, half_16_14_φ3, half_16_14_φ4, half_16_14_φ5, half_16_14_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_14_φ1, half_16_14_φ2, half_16_14_φ3, half_16_14_φ4, half_16_14_φ5, half_16_14_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_16_14_hF2 half_13_14 half_14_14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_16_14_φ1, half_16_14_φ2, half_16_14_φ3, half_16_14_φ4, half_16_14_φ5, half_16_14_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_14_hx5 : SourcePowerBound (powerBoxCross 18 11 32 half_16_14_φ5) (99850890437/8000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 5) (s := 11) (u := 9) (t := 12)
    (D := 32) (ψ := (208227084589/10000000000000 : ℝ)) half_16_14_φ5
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_14_φ1, half_16_14_φ2, half_16_14_φ3, half_16_14_φ4, half_16_14_φ5, half_16_14_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_14_φ1, half_16_14_φ2, half_16_14_φ3, half_16_14_φ4, half_16_14_φ5, half_16_14_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_14_φ1, half_16_14_φ2, half_16_14_φ3, half_16_14_φ4, half_16_14_φ5, half_16_14_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_14 half_12_14
    (by simpa only [half_16_14_φ6, show (2:ℝ)*32=64 by norm_num] using half_16_14_hx6)
  exact h.weaken (by norm_num [half_16_14_φ1, half_16_14_φ2, half_16_14_φ3, half_16_14_φ4, half_16_14_φ5, half_16_14_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_14_hx4 : SourcePowerBound (powerBoxCross 18 12 16 half_16_14_φ4) (8552114078139/625000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 12) (u := 10) (t := 13)
    (D := 16) (ψ := (13452080259/400000000000 : ℝ)) half_16_14_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_14_φ1, half_16_14_φ2, half_16_14_φ3, half_16_14_φ4, half_16_14_φ5, half_16_14_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_14_φ1, half_16_14_φ2, half_16_14_φ3, half_16_14_φ4, half_16_14_φ5, half_16_14_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_14_φ1, half_16_14_φ2, half_16_14_φ3, half_16_14_φ4, half_16_14_φ5, half_16_14_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_14 half_13_14
    (by simpa only [half_16_14_φ5, show (2:ℝ)*16=32 by norm_num] using half_16_14_hx5)
  exact h.weaken (by norm_num [half_16_14_φ1, half_16_14_φ2, half_16_14_φ3, half_16_14_φ4, half_16_14_φ5, half_16_14_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_14_hx3 : SourcePowerBound (powerBoxCross 18 13 8 half_16_14_φ3) (75454178307783/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 13) (u := 11) (t := 14)
    (D := 8) (ψ := (7482053257/200000000000 : ℝ)) half_16_14_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_14_φ1, half_16_14_φ2, half_16_14_φ3, half_16_14_φ4, half_16_14_φ5, half_16_14_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_14_φ1, half_16_14_φ2, half_16_14_φ3, half_16_14_φ4, half_16_14_φ5, half_16_14_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_14_φ1, half_16_14_φ2, half_16_14_φ3, half_16_14_φ4, half_16_14_φ5, half_16_14_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_14 half_14_14
    (by simpa only [half_16_14_φ4, show (2:ℝ)*8=16 by norm_num] using half_16_14_hx4)
  exact h.weaken (by norm_num [half_16_14_φ1, half_16_14_φ2, half_16_14_φ3, half_16_14_φ4, half_16_14_φ5, half_16_14_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_14_hx2 : SourcePowerBound (powerBoxCross 18 14 4 half_16_14_φ2) (166808976426249/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 14) (u := 12) (t := 15)
    (D := 4) (ψ := (195548761037/5000000000000 : ℝ)) half_16_14_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_14_φ1, half_16_14_φ2, half_16_14_φ3, half_16_14_φ4, half_16_14_φ5, half_16_14_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_14_φ1, half_16_14_φ2, half_16_14_φ3, half_16_14_φ4, half_16_14_φ5, half_16_14_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_14_φ1, half_16_14_φ2, half_16_14_φ3, half_16_14_φ4, half_16_14_φ5, half_16_14_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_13_14 half_15_14
    (by simpa only [half_16_14_φ3, show (2:ℝ)*4=8 by norm_num] using half_16_14_hx3)
  exact h.weaken (by norm_num [half_16_14_φ1, half_16_14_φ2, half_16_14_φ3, half_16_14_φ4, half_16_14_φ5, half_16_14_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_14_hx1 : SourcePowerBound (powerBoxCross 18 15 2 half_16_14_φ1) (7380936032301/400000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 15) (u := 13) (t := 16)
    (D := 2) (ψ := (201347496613/5000000000000 : ℝ)) half_16_14_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_14_φ1, half_16_14_φ2, half_16_14_φ3, half_16_14_φ4, half_16_14_φ5, half_16_14_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_14_φ1, half_16_14_φ2, half_16_14_φ3, half_16_14_φ4, half_16_14_φ5, half_16_14_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_14_φ1, half_16_14_φ2, half_16_14_φ3, half_16_14_φ4, half_16_14_φ5, half_16_14_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_14_14 half_16_13
    (by simpa only [half_16_14_φ2, show (2:ℝ)*2=4 by norm_num] using half_16_14_hx2)
  exact h.weaken (by norm_num [half_16_14_φ1, half_16_14_φ2, half_16_14_φ3, half_16_14_φ4, half_16_14_φ5, half_16_14_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_14 : AdmissibleExponent 18 32 (98248687282783/5000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 14) (ψ := (412895646829/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_15_14
    (by simpa only [half_16_14_φ1] using half_16_14_hx1)
  exact admissibleExponent_mono h (by norm_num [half_16_14_φ1, half_16_14_φ2, half_16_14_φ3, half_16_14_φ4, half_16_14_φ5, half_16_14_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_17_14_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (210921116423/5000000000000 : ℝ)

def half_17_14_φ2 : Fin 2 → ℝ := Fin.snoc half_17_14_φ1 (412012308829/10000000000000 : ℝ)

def half_17_14_φ3 : Fin 3 → ℝ := Fin.snoc half_17_14_φ2 (16044976397/400000000000 : ℝ)

def half_17_14_φ4 : Fin 4 → ℝ := Fin.snoc half_17_14_φ3 (387123051959/10000000000000 : ℝ)

def half_17_14_φ5 : Fin 5 → ℝ := Fin.snoc half_17_14_φ4 (72268278149/2000000000000 : ℝ)

def half_17_14_φ6 : Fin 6 → ℝ := Fin.snoc half_17_14_φ5 (72297483439/2500000000000 : ℝ)

theorem half_17_14_hF2 : SourcePowerBound (paddedMoment 18 0 2 64 half_17_14_φ6) (4204785013447/500000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 6) (r := 0) (D := 64)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_17_14_φ6 (by norm_num [half_17_14_φ1, half_17_14_φ2, half_17_14_φ3, half_17_14_φ4, half_17_14_φ5, half_17_14_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_14_φ1, half_17_14_φ2, half_17_14_φ3, half_17_14_φ4, half_17_14_φ5, half_17_14_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_14_φ1, half_17_14_φ2, half_17_14_φ3, half_17_14_φ4, half_17_14_φ5, half_17_14_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_17_14_φ1, half_17_14_φ2, half_17_14_φ3, half_17_14_φ4, half_17_14_φ5, half_17_14_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_17_14_hx6 : SourcePowerBound (powerBoxCross 18 11 64 half_17_14_φ6) (123463320985751/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 11) (r := 2) (v := 14) (w := 15) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_17_14_φ6 (by norm_num [half_17_14_φ1, half_17_14_φ2, half_17_14_φ3, half_17_14_φ4, half_17_14_φ5, half_17_14_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_14_φ1, half_17_14_φ2, half_17_14_φ3, half_17_14_φ4, half_17_14_φ5, half_17_14_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_17_14_hF2 half_14_14 half_15_14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_17_14_φ1, half_17_14_φ2, half_17_14_φ3, half_17_14_φ4, half_17_14_φ5, half_17_14_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_14_hx5 : SourcePowerBound (powerBoxCross 18 12 32 half_17_14_φ5) (67082360372223/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 5) (s := 12) (u := 10) (t := 13)
    (D := 32) (ψ := (72297483439/2500000000000 : ℝ)) half_17_14_φ5
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_14_φ1, half_17_14_φ2, half_17_14_φ3, half_17_14_φ4, half_17_14_φ5, half_17_14_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_14_φ1, half_17_14_φ2, half_17_14_φ3, half_17_14_φ4, half_17_14_φ5, half_17_14_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_14_φ1, half_17_14_φ2, half_17_14_φ3, half_17_14_φ4, half_17_14_φ5, half_17_14_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_14 half_13_14
    (by simpa only [half_17_14_φ6, show (2:ℝ)*32=64 by norm_num] using half_17_14_hx6)
  exact h.weaken (by norm_num [half_17_14_φ1, half_17_14_φ2, half_17_14_φ3, half_17_14_φ4, half_17_14_φ5, half_17_14_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_14_hx4 : SourcePowerBound (powerBoxCross 18 13 16 half_17_14_φ4) (147426289122533/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 13) (u := 11) (t := 14)
    (D := 16) (ψ := (72268278149/2000000000000 : ℝ)) half_17_14_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_14_φ1, half_17_14_φ2, half_17_14_φ3, half_17_14_φ4, half_17_14_φ5, half_17_14_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_14_φ1, half_17_14_φ2, half_17_14_φ3, half_17_14_φ4, half_17_14_φ5, half_17_14_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_14_φ1, half_17_14_φ2, half_17_14_φ3, half_17_14_φ4, half_17_14_φ5, half_17_14_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_14 half_14_14
    (by simpa only [half_17_14_φ5, show (2:ℝ)*16=32 by norm_num] using half_17_14_hx5)
  exact h.weaken (by norm_num [half_17_14_φ1, half_17_14_φ2, half_17_14_φ3, half_17_14_φ4, half_17_14_φ5, half_17_14_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_14_hx3 : SourcePowerBound (powerBoxCross 18 14 8 half_17_14_φ3) (162645225211771/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 14) (u := 12) (t := 15)
    (D := 8) (ψ := (387123051959/10000000000000 : ℝ)) half_17_14_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_14_φ1, half_17_14_φ2, half_17_14_φ3, half_17_14_φ4, half_17_14_φ5, half_17_14_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_14_φ1, half_17_14_φ2, half_17_14_φ3, half_17_14_φ4, half_17_14_φ5, half_17_14_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_14_φ1, half_17_14_φ2, half_17_14_φ3, half_17_14_φ4, half_17_14_φ5, half_17_14_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_13_14 half_15_14
    (by simpa only [half_17_14_φ4, show (2:ℝ)*8=16 by norm_num] using half_17_14_hx4)
  exact h.weaken (by norm_num [half_17_14_φ1, half_17_14_φ2, half_17_14_φ3, half_17_14_φ4, half_17_14_φ5, half_17_14_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_14_hx2 : SourcePowerBound (powerBoxCross 18 15 4 half_17_14_φ2) (179706204407983/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 15) (u := 13) (t := 16)
    (D := 4) (ψ := (16044976397/400000000000 : ℝ)) half_17_14_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_14_φ1, half_17_14_φ2, half_17_14_φ3, half_17_14_φ4, half_17_14_φ5, half_17_14_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_14_φ1, half_17_14_φ2, half_17_14_φ3, half_17_14_φ4, half_17_14_φ5, half_17_14_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_14_φ1, half_17_14_φ2, half_17_14_φ3, half_17_14_φ4, half_17_14_φ5, half_17_14_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_14_14 half_16_14
    (by simpa only [half_17_14_φ3, show (2:ℝ)*4=8 by norm_num] using half_17_14_hx3)
  exact h.weaken (by norm_num [half_17_14_φ1, half_17_14_φ2, half_17_14_φ3, half_17_14_φ4, half_17_14_φ5, half_17_14_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_14_hx1 : SourcePowerBound (powerBoxCross 18 16 2 half_17_14_φ1) (198630127674919/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 16) (u := 14) (t := 17)
    (D := 2) (ψ := (412012308829/10000000000000 : ℝ)) half_17_14_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_14_φ1, half_17_14_φ2, half_17_14_φ3, half_17_14_φ4, half_17_14_φ5, half_17_14_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_14_φ1, half_17_14_φ2, half_17_14_φ3, half_17_14_φ4, half_17_14_φ5, half_17_14_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_14_φ1, half_17_14_φ2, half_17_14_φ3, half_17_14_φ4, half_17_14_φ5, half_17_14_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_15_14 half_17_13
    (by simpa only [half_17_14_φ2, show (2:ℝ)*2=4 by norm_num] using half_17_14_hx2)
  exact h.weaken (by norm_num [half_17_14_φ1, half_17_14_φ2, half_17_14_φ3, half_17_14_φ4, half_17_14_φ5, half_17_14_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_14 : AdmissibleExponent 18 34 (42341447378629/2000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 15) (ψ := (210921116423/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_16_14
    (by simpa only [half_17_14_φ1] using half_17_14_hx1)
  exact admissibleExponent_mono h (by norm_num [half_17_14_φ1, half_17_14_φ2, half_17_14_φ3, half_17_14_φ4, half_17_14_φ5, half_17_14_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])


end Waring.SeedCompletionHigher18SimpleSeeds
