import Waring.SeedCompletionHigher18SimpleSeedsC01

noncomputable section
set_option maxHeartbeats 2000000
namespace Waring.SeedCompletionHigher18SimpleSeeds
open SmoothMoments FirstStageTransport SeedCompletionNaturalBox
open SeedCompletionSourceBounds SeedCompletionPaddedSource SeedCompletionGeneralTerminal
open PolicyCompletionMajorPowerRanges

def half_9_02_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (354453793843/10000000000000 : ℝ)

def half_9_02_φ2 : Fin 2 → ℝ := Fin.snoc half_9_02_φ1 (63311294703/2000000000000 : ℝ)

def half_9_02_φ3 : Fin 3 → ℝ := Fin.snoc half_9_02_φ2 (93163576437/5000000000000 : ℝ)

theorem half_9_02_hF2 : SourcePowerBound (paddedMoment 18 0 2 8 half_9_02_φ3) (8284473946021/1250000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_02_φ3 (by norm_num [half_9_02_φ1, half_9_02_φ2, half_9_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_02_φ1, half_9_02_φ2, half_9_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_02_φ1, half_9_02_φ2, half_9_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_02_φ1, half_9_02_φ2, half_9_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_9_02_hF1 : SourcePowerBound (paddedMoment 18 0 1 8 half_9_02_φ3) (3178157982007/1250000000000 : ℝ) := by
  have h := padded_second_power (k := 18) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_02_φ3 (by norm_num [half_9_02_φ1, half_9_02_φ2, half_9_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_02_φ1, half_9_02_φ2, half_9_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_02_φ1, half_9_02_φ2, half_9_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_02_φ1, half_9_02_φ2, half_9_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_9_02_hx3 : SourcePowerBound (powerBoxCross 18 6 8 half_9_02_φ3) (7628016989841/1000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 18) (s := 6) (r := 1) (v := 2) (t := 10) (D := 8)
    (a := (3/10 : ℝ)) (b := (1/10 : ℝ)) (c := (3/5 : ℝ))
    (by norm_num) half_9_02_φ3 (by norm_num [half_9_02_φ1, half_9_02_φ2, half_9_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_02_φ1, half_9_02_φ2, half_9_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_9_02_hF1 half_9_02_hF2 half_10_01
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_9_02_φ1, half_9_02_φ2, half_9_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_9_02_hx2 : SourcePowerBound (powerBoxCross 18 7 4 half_9_02_φ2) (20989147584131/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 7) (u := 5) (t := 8)
    (D := 4) (ψ := (93163576437/5000000000000 : ℝ)) half_9_02_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_02_φ1, half_9_02_φ2, half_9_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_02_φ1, half_9_02_φ2, half_9_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_02_φ1, half_9_02_φ2, half_9_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_6 SeedCompletionEven18SecondSeeds.degree18_half_8
    (by simpa only [half_9_02_φ3, show (2:ℝ)*4=8 by norm_num] using half_9_02_hx3)
  exact h.weaken (by norm_num [half_9_02_φ1, half_9_02_φ2, half_9_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_9_02_hx1 : SourcePowerBound (powerBoxCross 18 8 2 half_9_02_φ1) (94093258109213/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 8) (u := 6) (t := 9)
    (D := 2) (ψ := (63311294703/2000000000000 : ℝ)) half_9_02_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_02_φ1, half_9_02_φ2, half_9_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_02_φ1, half_9_02_φ2, half_9_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_02_φ1, half_9_02_φ2, half_9_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_7 half_9_01
    (by simpa only [half_9_02_φ2, show (2:ℝ)*2=4 by norm_num] using half_9_02_hx2)
  exact h.weaken (by norm_num [half_9_02_φ1, half_9_02_φ2, half_9_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_9_02 : AdmissibleExponent 18 18 (49705032508429/5000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 7) (ψ := (354453793843/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_8
    (by simpa only [half_9_02_φ1] using half_9_02_hx1)
  exact admissibleExponent_mono h (by norm_num [half_9_02_φ1, half_9_02_φ2, half_9_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_10_02_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (18723928237/500000000000 : ℝ)

def half_10_02_φ2 : Fin 2 → ℝ := Fin.snoc half_10_02_φ1 (167821276801/5000000000000 : ℝ)

def half_10_02_φ3 : Fin 3 → ℝ := Fin.snoc half_10_02_φ2 (63560226167/2500000000000 : ℝ)

theorem half_10_02_hF2 : SourcePowerBound (paddedMoment 18 0 2 8 half_10_02_φ3) (6081753682649/1000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_10_02_φ3 (by norm_num [half_10_02_φ1, half_10_02_φ2, half_10_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_02_φ1, half_10_02_φ2, half_10_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_02_φ1, half_10_02_φ2, half_10_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_10_02_φ1, half_10_02_φ2, half_10_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_10_02_hx3 : SourcePowerBound (powerBoxCross 18 7 8 half_10_02_φ3) (42828639148427/5000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 7) (r := 2) (v := 9) (w := 10) (D := 8)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_10_02_φ3 (by norm_num [half_10_02_φ1, half_10_02_φ2, half_10_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_02_φ1, half_10_02_φ2, half_10_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_10_02_hF2 half_9_02 half_10_01
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_10_02_φ1, half_10_02_φ2, half_10_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_02_hx2 : SourcePowerBound (powerBoxCross 18 8 4 half_10_02_φ2) (1182756858801/125000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 8) (u := 6) (t := 9)
    (D := 4) (ψ := (63560226167/2500000000000 : ℝ)) half_10_02_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_02_φ1, half_10_02_φ2, half_10_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_02_φ1, half_10_02_φ2, half_10_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_02_φ1, half_10_02_φ2, half_10_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_7 half_9_02
    (by simpa only [half_10_02_φ3, show (2:ℝ)*4=8 by norm_num] using half_10_02_hx3)
  exact h.weaken (by norm_num [half_10_02_φ1, half_10_02_φ2, half_10_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_02_hx1 : SourcePowerBound (powerBoxCross 18 9 2 half_10_02_φ1) (53030924867397/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 9) (u := 7) (t := 10)
    (D := 2) (ψ := (167821276801/5000000000000 : ℝ)) half_10_02_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_02_φ1, half_10_02_φ2, half_10_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_02_φ1, half_10_02_φ2, half_10_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_02_φ1, half_10_02_φ2, half_10_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_8 half_10_01
    (by simpa only [half_10_02_φ2, show (2:ℝ)*2=4 by norm_num] using half_10_02_hx2)
  exact h.weaken (by norm_num [half_10_02_φ1, half_10_02_φ2, half_10_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_02 : AdmissibleExponent 18 20 (56213992667687/5000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 8) (ψ := (18723928237/500000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_9_02
    (by simpa only [half_10_02_φ1] using half_10_02_hx1)
  exact admissibleExponent_mono h (by norm_num [half_10_02_φ1, half_10_02_φ2, half_10_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_11_02_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (401833808451/10000000000000 : ℝ)

def half_11_02_φ2 : Fin 2 → ℝ := Fin.snoc half_11_02_φ1 (181455300553/5000000000000 : ℝ)

def half_11_02_φ3 : Fin 3 → ℝ := Fin.snoc half_11_02_φ2 (365286470481/10000000000000 : ℝ)

theorem half_11_02_hF2 : SourcePowerBound (paddedMoment 18 0 2 8 half_11_02_φ3) (26184212559031/5000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_11_02_φ3 (by norm_num [half_11_02_φ1, half_11_02_φ2, half_11_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_02_φ1, half_11_02_φ2, half_11_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_02_φ1, half_11_02_φ2, half_11_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_11_02_φ1, half_11_02_φ2, half_11_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_11_02_hx3 : SourcePowerBound (powerBoxCross 18 8 8 half_11_02_φ3) (94370183349717/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 8) (r := 2) (v := 10) (w := 11) (D := 8)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_11_02_φ3 (by norm_num [half_11_02_φ1, half_11_02_φ2, half_11_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_02_φ1, half_11_02_φ2, half_11_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_11_02_hF2 half_10_02 half_11_01
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_11_02_φ1, half_11_02_φ2, half_11_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_02_hx2 : SourcePowerBound (powerBoxCross 18 9 4 half_11_02_φ2) (10533947172677/1000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 9) (u := 7) (t := 10)
    (D := 4) (ψ := (365286470481/10000000000000 : ℝ)) half_11_02_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_02_φ1, half_11_02_φ2, half_11_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_02_φ1, half_11_02_φ2, half_11_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_02_φ1, half_11_02_φ2, half_11_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_8 half_10_02
    (by simpa only [half_11_02_φ3, show (2:ℝ)*4=8 by norm_num] using half_11_02_hx3)
  exact h.weaken (by norm_num [half_11_02_φ1, half_11_02_φ2, half_11_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_02_hx1 : SourcePowerBound (powerBoxCross 18 10 2 half_11_02_φ1) (118312082591451/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 10) (u := 8) (t := 11)
    (D := 2) (ψ := (181455300553/5000000000000 : ℝ)) half_11_02_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_02_φ1, half_11_02_φ2, half_11_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_02_φ1, half_11_02_φ2, half_11_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_02_φ1, half_11_02_φ2, half_11_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_02 half_11_01
    (by simpa only [half_11_02_φ2, show (2:ℝ)*2=4 by norm_num] using half_11_02_hx2)
  exact h.weaken (by norm_num [half_11_02_φ1, half_11_02_φ2, half_11_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_02 : AdmissibleExponent 18 22 (6297346247601/500000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 9) (ψ := (401833808451/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_10_02
    (by simpa only [half_11_02_φ1] using half_11_02_hx1)
  exact admissibleExponent_mono h (by norm_num [half_11_02_φ1, half_11_02_φ2, half_11_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_12_02_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (209794018463/5000000000000 : ℝ)

def half_12_02_φ2 : Fin 2 → ℝ := Fin.snoc half_12_02_φ1 (183411203867/5000000000000 : ℝ)

def half_12_02_φ3 : Fin 3 → ℝ := Fin.snoc half_12_02_φ2 (340487687673/10000000000000 : ℝ)

def half_12_02_φ4 : Fin 4 → ℝ := Fin.snoc half_12_02_φ3 (257083310449/10000000000000 : ℝ)

theorem half_12_02_hF2 : SourcePowerBound (paddedMoment 18 0 2 16 half_12_02_φ4) (34708473209059/5000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_12_02_φ4 (by norm_num [half_12_02_φ1, half_12_02_φ2, half_12_02_φ3, half_12_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_02_φ1, half_12_02_φ2, half_12_02_φ3, half_12_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_02_φ1, half_12_02_φ2, half_12_02_φ3, half_12_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_12_02_φ1, half_12_02_φ2, half_12_02_φ3, half_12_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_12_02_hF1 : SourcePowerBound (paddedMoment 18 0 1 16 half_12_02_φ4) (13236157736353/5000000000000 : ℝ) := by
  have h := padded_second_power (k := 18) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_12_02_φ4 (by norm_num [half_12_02_φ1, half_12_02_φ2, half_12_02_φ3, half_12_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_02_φ1, half_12_02_φ2, half_12_02_φ3, half_12_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_02_φ1, half_12_02_φ2, half_12_02_φ3, half_12_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_12_02_φ1, half_12_02_φ2, half_12_02_φ3, half_12_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_12_02_hx4 : SourcePowerBound (powerBoxCross 18 8 16 half_12_02_φ4) (3836026755893/400000000000 : ℝ) := by
  have h := full_B_cross_power (k := 18) (s := 8) (r := 1) (v := 2) (t := 11) (D := 16)
    (a := (1/22 : ℝ)) (b := (5/22 : ℝ)) (c := (8/11 : ℝ))
    (by norm_num) half_12_02_φ4 (by norm_num [half_12_02_φ1, half_12_02_φ2, half_12_02_φ3, half_12_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_02_φ1, half_12_02_φ2, half_12_02_φ3, half_12_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_12_02_hF1 half_12_02_hF2 half_11_02
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_12_02_φ1, half_12_02_φ2, half_12_02_φ3, half_12_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_02_hx3 : SourcePowerBound (powerBoxCross 18 9 8 half_12_02_φ3) (105179073485067/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 9) (u := 7) (t := 10)
    (D := 8) (ψ := (257083310449/10000000000000 : ℝ)) half_12_02_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_02_φ1, half_12_02_φ2, half_12_02_φ3, half_12_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_02_φ1, half_12_02_φ2, half_12_02_φ3, half_12_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_02_φ1, half_12_02_φ2, half_12_02_φ3, half_12_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_8 half_10_02
    (by simpa only [half_12_02_φ4, show (2:ℝ)*8=16 by norm_num] using half_12_02_hx4)
  exact h.weaken (by norm_num [half_12_02_φ1, half_12_02_φ2, half_12_02_φ3, half_12_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_02_hx2 : SourcePowerBound (powerBoxCross 18 10 4 half_12_02_φ2) (116820356921401/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 10) (u := 8) (t := 11)
    (D := 4) (ψ := (340487687673/10000000000000 : ℝ)) half_12_02_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_02_φ1, half_12_02_φ2, half_12_02_φ3, half_12_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_02_φ1, half_12_02_φ2, half_12_02_φ3, half_12_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_02_φ1, half_12_02_φ2, half_12_02_φ3, half_12_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_02 half_11_02
    (by simpa only [half_12_02_φ3, show (2:ℝ)*4=8 by norm_num] using half_12_02_hx3)
  exact h.weaken (by norm_num [half_12_02_φ1, half_12_02_φ2, half_12_02_φ3, half_12_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_02_hx1 : SourcePowerBound (powerBoxCross 18 11 2 half_12_02_φ1) (6554096534461/500000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 11) (u := 9) (t := 12)
    (D := 2) (ψ := (183411203867/5000000000000 : ℝ)) half_12_02_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_02_φ1, half_12_02_φ2, half_12_02_φ3, half_12_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_02_φ1, half_12_02_φ2, half_12_02_φ3, half_12_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_02_φ1, half_12_02_φ2, half_12_02_φ3, half_12_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_02 half_12_01
    (by simpa only [half_12_02_φ2, show (2:ℝ)*2=4 by norm_num] using half_12_02_hx2)
  exact h.weaken (by norm_num [half_12_02_φ1, half_12_02_φ2, half_12_02_φ3, half_12_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_02 : AdmissibleExponent 18 24 (69946639732333/5000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 10) (ψ := (209794018463/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_11_02
    (by simpa only [half_12_02_φ1] using half_12_02_hx1)
  exact admissibleExponent_mono h (by norm_num [half_12_02_φ1, half_12_02_φ2, half_12_02_φ3, half_12_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_13_02_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (441883668113/10000000000000 : ℝ)

def half_13_02_φ2 : Fin 2 → ℝ := Fin.snoc half_13_02_φ1 (7557708073/200000000000 : ℝ)

def half_13_02_φ3 : Fin 3 → ℝ := Fin.snoc half_13_02_φ2 (733452987/20000000000 : ℝ)

def half_13_02_φ4 : Fin 4 → ℝ := Fin.snoc half_13_02_φ3 (171273260487/5000000000000 : ℝ)

theorem half_13_02_hF2 : SourcePowerBound (paddedMoment 18 0 2 16 half_13_02_φ4) (62018853601913/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_13_02_φ4 (by norm_num [half_13_02_φ1, half_13_02_φ2, half_13_02_φ3, half_13_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_02_φ1, half_13_02_φ2, half_13_02_φ3, half_13_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_02_φ1, half_13_02_φ2, half_13_02_φ3, half_13_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_13_02_φ1, half_13_02_φ2, half_13_02_φ3, half_13_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_13_02_hx4 : SourcePowerBound (powerBoxCross 18 9 16 half_13_02_φ4) (104381969607739/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 9) (r := 2) (v := 12) (w := 12) (D := 16)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_13_02_φ4 (by norm_num [half_13_02_φ1, half_13_02_φ2, half_13_02_φ3, half_13_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_02_φ1, half_13_02_φ2, half_13_02_φ3, half_13_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_13_02_hF2 half_12_02 half_12_02
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_13_02_φ1, half_13_02_φ2, half_13_02_φ3, half_13_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_02_hx3 : SourcePowerBound (powerBoxCross 18 10 8 half_13_02_φ3) (115519107007719/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 10) (u := 8) (t := 11)
    (D := 8) (ψ := (171273260487/5000000000000 : ℝ)) half_13_02_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_02_φ1, half_13_02_φ2, half_13_02_φ3, half_13_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_02_φ1, half_13_02_φ2, half_13_02_φ3, half_13_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_02_φ1, half_13_02_φ2, half_13_02_φ3, half_13_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_02 half_11_02
    (by simpa only [half_13_02_φ4, show (2:ℝ)*8=16 by norm_num] using half_13_02_hx4)
  exact h.weaken (by norm_num [half_13_02_φ1, half_13_02_φ2, half_13_02_φ3, half_13_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_02_hx2 : SourcePowerBound (powerBoxCross 18 11 4 half_13_02_φ2) (64244024310913/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 11) (u := 9) (t := 12)
    (D := 4) (ψ := (733452987/20000000000 : ℝ)) half_13_02_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_02_φ1, half_13_02_φ2, half_13_02_φ3, half_13_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_02_φ1, half_13_02_φ2, half_13_02_φ3, half_13_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_02_φ1, half_13_02_φ2, half_13_02_φ3, half_13_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_02 half_12_02
    (by simpa only [half_13_02_φ3, show (2:ℝ)*4=8 by norm_num] using half_13_02_hx3)
  exact h.weaken (by norm_num [half_13_02_φ1, half_13_02_φ2, half_13_02_φ3, half_13_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_02_hx1 : SourcePowerBound (powerBoxCross 18 12 2 half_13_02_φ1) (72076753792683/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 12) (u := 10) (t := 13)
    (D := 2) (ψ := (7557708073/200000000000 : ℝ)) half_13_02_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_02_φ1, half_13_02_φ2, half_13_02_φ3, half_13_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_02_φ1, half_13_02_φ2, half_13_02_φ3, half_13_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_02_φ1, half_13_02_φ2, half_13_02_φ3, half_13_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_02 half_13_01
    (by simpa only [half_13_02_φ2, show (2:ℝ)*2=4 by norm_num] using half_13_02_hx2)
  exact h.weaken (by norm_num [half_13_02_φ1, half_13_02_φ2, half_13_02_φ3, half_13_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_02 : AdmissibleExponent 18 26 (30863366390393/2000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 11) (ψ := (441883668113/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_12_02
    (by simpa only [half_13_02_φ1] using half_13_02_hx1)
  exact admissibleExponent_mono h (by norm_num [half_13_02_φ1, half_13_02_φ2, half_13_02_φ3, half_13_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_14_02_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (22998044661/500000000000 : ℝ)

def half_14_02_φ2 : Fin 2 → ℝ := Fin.snoc half_14_02_φ1 (387400989641/10000000000000 : ℝ)

def half_14_02_φ3 : Fin 3 → ℝ := Fin.snoc half_14_02_φ2 (373158834847/10000000000000 : ℝ)

def half_14_02_φ4 : Fin 4 → ℝ := Fin.snoc half_14_02_φ3 (349251989209/10000000000000 : ℝ)

def half_14_02_φ5 : Fin 5 → ℝ := Fin.snoc half_14_02_φ4 (133434836239/5000000000000 : ℝ)

theorem half_14_02_hF2 : SourcePowerBound (paddedMoment 18 0 2 32 half_14_02_φ5) (15266247730171/2000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_14_02_φ5 (by norm_num [half_14_02_φ1, half_14_02_φ2, half_14_02_φ3, half_14_02_φ4, half_14_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_02_φ1, half_14_02_φ2, half_14_02_φ3, half_14_02_φ4, half_14_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_02_φ1, half_14_02_φ2, half_14_02_φ3, half_14_02_φ4, half_14_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_14_02_φ1, half_14_02_φ2, half_14_02_φ3, half_14_02_φ4, half_14_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_14_02_hx5 : SourcePowerBound (powerBoxCross 18 9 32 half_14_02_φ5) (6545795302307/625000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 9) (r := 2) (v := 12) (w := 12) (D := 32)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_14_02_φ5 (by norm_num [half_14_02_φ1, half_14_02_φ2, half_14_02_φ3, half_14_02_φ4, half_14_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_02_φ1, half_14_02_φ2, half_14_02_φ3, half_14_02_φ4, half_14_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_14_02_hF2 half_12_02 half_12_02
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_14_02_φ1, half_14_02_φ2, half_14_02_φ3, half_14_02_φ4, half_14_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_02_hx4 : SourcePowerBound (powerBoxCross 18 10 16 half_14_02_φ4) (22875949367249/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 10) (u := 8) (t := 11)
    (D := 16) (ψ := (133434836239/5000000000000 : ℝ)) half_14_02_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_02_φ1, half_14_02_φ2, half_14_02_φ3, half_14_02_φ4, half_14_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_02_φ1, half_14_02_φ2, half_14_02_φ3, half_14_02_φ4, half_14_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_02_φ1, half_14_02_φ2, half_14_02_φ3, half_14_02_φ4, half_14_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_02 half_11_02
    (by simpa only [half_14_02_φ5, show (2:ℝ)*16=32 by norm_num] using half_14_02_hx5)
  exact h.weaken (by norm_num [half_14_02_φ1, half_14_02_φ2, half_14_02_φ3, half_14_02_φ4, half_14_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_02_hx3 : SourcePowerBound (powerBoxCross 18 11 8 half_14_02_φ3) (126542848654687/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 11) (u := 9) (t := 12)
    (D := 8) (ψ := (349251989209/10000000000000 : ℝ)) half_14_02_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_02_φ1, half_14_02_φ2, half_14_02_φ3, half_14_02_φ4, half_14_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_02_φ1, half_14_02_φ2, half_14_02_φ3, half_14_02_φ4, half_14_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_02_φ1, half_14_02_φ2, half_14_02_φ3, half_14_02_φ4, half_14_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_02 half_12_02
    (by simpa only [half_14_02_φ4, show (2:ℝ)*8=16 by norm_num] using half_14_02_hx4)
  exact h.weaken (by norm_num [half_14_02_φ1, half_14_02_φ2, half_14_02_φ3, half_14_02_φ4, half_14_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_02_hx2 : SourcePowerBound (powerBoxCross 18 12 4 half_14_02_φ2) (140607322000903/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 12) (u := 10) (t := 13)
    (D := 4) (ψ := (373158834847/10000000000000 : ℝ)) half_14_02_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_02_φ1, half_14_02_φ2, half_14_02_φ3, half_14_02_φ4, half_14_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_02_φ1, half_14_02_φ2, half_14_02_φ3, half_14_02_φ4, half_14_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_02_φ1, half_14_02_φ2, half_14_02_φ3, half_14_02_φ4, half_14_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_02 half_13_02
    (by simpa only [half_14_02_φ3, show (2:ℝ)*4=8 by norm_num] using half_14_02_hx3)
  exact h.weaken (by norm_num [half_14_02_φ1, half_14_02_φ2, half_14_02_φ3, half_14_02_φ4, half_14_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_02_hx1 : SourcePowerBound (powerBoxCross 18 13 2 half_14_02_φ1) (157678822058849/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 13) (u := 11) (t := 14)
    (D := 2) (ψ := (387400989641/10000000000000 : ℝ)) half_14_02_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_02_φ1, half_14_02_φ2, half_14_02_φ3, half_14_02_φ4, half_14_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_02_φ1, half_14_02_φ2, half_14_02_φ3, half_14_02_φ4, half_14_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_02_φ1, half_14_02_φ2, half_14_02_φ3, half_14_02_φ4, half_14_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_02 half_14_01
    (by simpa only [half_14_02_φ2, show (2:ℝ)*2=4 by norm_num] using half_14_02_hx2)
  exact h.weaken (by norm_num [half_14_02_φ1, half_14_02_φ2, half_14_02_φ3, half_14_02_φ4, half_14_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_02 : AdmissibleExponent 18 28 (169177844389349/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 12) (ψ := (22998044661/500000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_13_02
    (by simpa only [half_14_02_φ1] using half_14_02_hx1)
  exact admissibleExponent_mono h (by norm_num [half_14_02_φ1, half_14_02_φ2, half_14_02_φ3, half_14_02_φ4, half_14_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_15_02_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (238467702759/5000000000000 : ℝ)

def half_15_02_φ2 : Fin 2 → ℝ := Fin.snoc half_15_02_φ1 (396763110597/10000000000000 : ℝ)

def half_15_02_φ3 : Fin 3 → ℝ := Fin.snoc half_15_02_φ2 (388009198741/10000000000000 : ℝ)

def half_15_02_φ4 : Fin 4 → ℝ := Fin.snoc half_15_02_φ3 (377589102201/10000000000000 : ℝ)

def half_15_02_φ5 : Fin 5 → ℝ := Fin.snoc half_15_02_φ4 (369508316499/10000000000000 : ℝ)

theorem half_15_02_hF2 : SourcePowerBound (paddedMoment 18 0 2 32 half_15_02_φ5) (16887734547161/2500000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_15_02_φ5 (by norm_num [half_15_02_φ1, half_15_02_φ2, half_15_02_φ3, half_15_02_φ4, half_15_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_02_φ1, half_15_02_φ2, half_15_02_φ3, half_15_02_φ4, half_15_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_02_φ1, half_15_02_φ2, half_15_02_φ3, half_15_02_φ4, half_15_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_15_02_φ1, half_15_02_φ2, half_15_02_φ3, half_15_02_φ4, half_15_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_15_02_hx5 : SourcePowerBound (powerBoxCross 18 10 32 half_15_02_φ5) (112344856352189/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 10) (r := 2) (v := 13) (w := 14) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_15_02_φ5 (by norm_num [half_15_02_φ1, half_15_02_φ2, half_15_02_φ3, half_15_02_φ4, half_15_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_02_φ1, half_15_02_φ2, half_15_02_φ3, half_15_02_φ4, half_15_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_15_02_hF2 half_13_02 half_14_02
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_15_02_φ1, half_15_02_φ2, half_15_02_φ3, half_15_02_φ4, half_15_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_02_hx4 : SourcePowerBound (powerBoxCross 18 11 16 half_15_02_φ4) (31057260895621/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 11) (u := 9) (t := 12)
    (D := 16) (ψ := (369508316499/10000000000000 : ℝ)) half_15_02_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_02_φ1, half_15_02_φ2, half_15_02_φ3, half_15_02_φ4, half_15_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_02_φ1, half_15_02_φ2, half_15_02_φ3, half_15_02_φ4, half_15_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_02_φ1, half_15_02_φ2, half_15_02_φ3, half_15_02_φ4, half_15_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_02 half_12_02
    (by simpa only [half_15_02_φ5, show (2:ℝ)*16=32 by norm_num] using half_15_02_hx5)
  exact h.weaken (by norm_num [half_15_02_φ1, half_15_02_φ2, half_15_02_φ3, half_15_02_φ4, half_15_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_02_hx3 : SourcePowerBound (powerBoxCross 18 12 8 half_15_02_φ3) (137777970893763/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 12) (u := 10) (t := 13)
    (D := 8) (ψ := (377589102201/10000000000000 : ℝ)) half_15_02_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_02_φ1, half_15_02_φ2, half_15_02_φ3, half_15_02_φ4, half_15_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_02_φ1, half_15_02_φ2, half_15_02_φ3, half_15_02_φ4, half_15_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_02_φ1, half_15_02_φ2, half_15_02_φ3, half_15_02_φ4, half_15_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_02 half_13_02
    (by simpa only [half_15_02_φ4, show (2:ℝ)*8=16 by norm_num] using half_15_02_hx4)
  exact h.weaken (by norm_num [half_15_02_φ1, half_15_02_φ2, half_15_02_φ3, half_15_02_φ4, half_15_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_02_hx2 : SourcePowerBound (powerBoxCross 18 13 4 half_15_02_φ2) (6124922178399/400000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 13) (u := 11) (t := 14)
    (D := 4) (ψ := (388009198741/10000000000000 : ℝ)) half_15_02_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_02_φ1, half_15_02_φ2, half_15_02_φ3, half_15_02_φ4, half_15_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_02_φ1, half_15_02_φ2, half_15_02_φ3, half_15_02_φ4, half_15_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_02_φ1, half_15_02_φ2, half_15_02_φ3, half_15_02_φ4, half_15_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_02 half_14_02
    (by simpa only [half_15_02_φ3, show (2:ℝ)*4=8 by norm_num] using half_15_02_hx3)
  exact h.weaken (by norm_num [half_15_02_φ1, half_15_02_φ2, half_15_02_φ3, half_15_02_φ4, half_15_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_02_hx1 : SourcePowerBound (powerBoxCross 18 14 2 half_15_02_φ1) (34317217882607/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 14) (u := 12) (t := 15)
    (D := 2) (ψ := (396763110597/10000000000000 : ℝ)) half_15_02_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_02_φ1, half_15_02_φ2, half_15_02_φ3, half_15_02_φ4, half_15_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_02_φ1, half_15_02_φ2, half_15_02_φ3, half_15_02_φ4, half_15_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_02_φ1, half_15_02_φ2, half_15_02_φ3, half_15_02_φ4, half_15_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_13_02 half_15_01
    (by simpa only [half_15_02_φ2, show (2:ℝ)*2=4 by norm_num] using half_15_02_hx2)
  exact h.weaken (by norm_num [half_15_02_φ1, half_15_02_φ2, half_15_02_φ3, half_15_02_φ4, half_15_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_02 : AdmissibleExponent 18 30 (184463345362021/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 13) (ψ := (238467702759/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_14_02
    (by simpa only [half_15_02_φ1] using half_15_02_hx1)
  exact admissibleExponent_mono h (by norm_num [half_15_02_φ1, half_15_02_φ2, half_15_02_φ3, half_15_02_φ4, half_15_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_16_02_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (490652196293/10000000000000 : ℝ)

def half_16_02_φ2 : Fin 2 → ℝ := Fin.snoc half_16_02_φ1 (202193710543/5000000000000 : ℝ)

def half_16_02_φ3 : Fin 3 → ℝ := Fin.snoc half_16_02_φ2 (394712999853/10000000000000 : ℝ)

def half_16_02_φ4 : Fin 4 → ℝ := Fin.snoc half_16_02_φ3 (382454797813/10000000000000 : ℝ)

def half_16_02_φ5 : Fin 5 → ℝ := Fin.snoc half_16_02_φ4 (44801461091/1250000000000 : ℝ)

def half_16_02_φ6 : Fin 6 → ℝ := Fin.snoc half_16_02_φ5 (292581778933/10000000000000 : ℝ)

theorem half_16_02_hF2 : SourcePowerBound (paddedMoment 18 0 2 64 half_16_02_φ6) (40758377490997/5000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 6) (r := 0) (D := 64)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_16_02_φ6 (by norm_num [half_16_02_φ1, half_16_02_φ2, half_16_02_φ3, half_16_02_φ4, half_16_02_φ5, half_16_02_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_02_φ1, half_16_02_φ2, half_16_02_φ3, half_16_02_φ4, half_16_02_φ5, half_16_02_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_02_φ1, half_16_02_φ2, half_16_02_φ3, half_16_02_φ4, half_16_02_φ5, half_16_02_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_16_02_φ1, half_16_02_φ2, half_16_02_φ3, half_16_02_φ4, half_16_02_φ5, half_16_02_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_16_02_hx6 : SourcePowerBound (powerBoxCross 18 10 64 half_16_02_φ6) (14010095359121/1250000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 10) (r := 2) (v := 13) (w := 14) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_16_02_φ6 (by norm_num [half_16_02_φ1, half_16_02_φ2, half_16_02_φ3, half_16_02_φ4, half_16_02_φ5, half_16_02_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_02_φ1, half_16_02_φ2, half_16_02_φ3, half_16_02_φ4, half_16_02_φ5, half_16_02_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_16_02_hF2 half_13_02 half_14_02
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_16_02_φ1, half_16_02_φ2, half_16_02_φ3, half_16_02_φ4, half_16_02_φ5, half_16_02_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_02_hx5 : SourcePowerBound (powerBoxCross 18 11 32 half_16_02_φ5) (12230278739809/1000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 5) (s := 11) (u := 9) (t := 12)
    (D := 32) (ψ := (292581778933/10000000000000 : ℝ)) half_16_02_φ5
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_02_φ1, half_16_02_φ2, half_16_02_φ3, half_16_02_φ4, half_16_02_φ5, half_16_02_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_02_φ1, half_16_02_φ2, half_16_02_φ3, half_16_02_φ4, half_16_02_φ5, half_16_02_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_02_φ1, half_16_02_φ2, half_16_02_φ3, half_16_02_φ4, half_16_02_φ5, half_16_02_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_02 half_12_02
    (by simpa only [half_16_02_φ6, show (2:ℝ)*32=64 by norm_num] using half_16_02_hx6)
  exact h.weaken (by norm_num [half_16_02_φ1, half_16_02_φ2, half_16_02_φ3, half_16_02_φ4, half_16_02_φ5, half_16_02_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_02_hx4 : SourcePowerBound (powerBoxCross 18 12 16 half_16_02_φ4) (134956881845973/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 12) (u := 10) (t := 13)
    (D := 16) (ψ := (44801461091/1250000000000 : ℝ)) half_16_02_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_02_φ1, half_16_02_φ2, half_16_02_φ3, half_16_02_φ4, half_16_02_φ5, half_16_02_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_02_φ1, half_16_02_φ2, half_16_02_φ3, half_16_02_φ4, half_16_02_φ5, half_16_02_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_02_φ1, half_16_02_φ2, half_16_02_φ3, half_16_02_φ4, half_16_02_φ5, half_16_02_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_02 half_13_02
    (by simpa only [half_16_02_φ5, show (2:ℝ)*16=32 by norm_num] using half_16_02_hx5)
  exact h.weaken (by norm_num [half_16_02_φ1, half_16_02_φ2, half_16_02_φ3, half_16_02_φ4, half_16_02_φ5, half_16_02_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_02_hx3 : SourcePowerBound (powerBoxCross 18 13 8 half_16_02_φ3) (149592817667097/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 13) (u := 11) (t := 14)
    (D := 8) (ψ := (382454797813/10000000000000 : ℝ)) half_16_02_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_02_φ1, half_16_02_φ2, half_16_02_φ3, half_16_02_φ4, half_16_02_φ5, half_16_02_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_02_φ1, half_16_02_φ2, half_16_02_φ3, half_16_02_φ4, half_16_02_φ5, half_16_02_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_02_φ1, half_16_02_φ2, half_16_02_φ3, half_16_02_φ4, half_16_02_φ5, half_16_02_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_02 half_14_02
    (by simpa only [half_16_02_φ4, show (2:ℝ)*8=16 by norm_num] using half_16_02_hx4)
  exact h.weaken (by norm_num [half_16_02_φ1, half_16_02_φ2, half_16_02_φ3, half_16_02_φ4, half_16_02_φ5, half_16_02_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_02_hx2 : SourcePowerBound (powerBoxCross 18 14 4 half_16_02_φ2) (166099057162337/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 14) (u := 12) (t := 15)
    (D := 4) (ψ := (394712999853/10000000000000 : ℝ)) half_16_02_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_02_φ1, half_16_02_φ2, half_16_02_φ3, half_16_02_φ4, half_16_02_φ5, half_16_02_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_02_φ1, half_16_02_φ2, half_16_02_φ3, half_16_02_φ4, half_16_02_φ5, half_16_02_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_02_φ1, half_16_02_φ2, half_16_02_φ3, half_16_02_φ4, half_16_02_φ5, half_16_02_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_13_02 half_15_02
    (by simpa only [half_16_02_φ3, show (2:ℝ)*4=8 by norm_num] using half_16_02_hx3)
  exact h.weaken (by norm_num [half_16_02_φ1, half_16_02_φ2, half_16_02_φ3, half_16_02_φ4, half_16_02_φ5, half_16_02_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_02_hx1 : SourcePowerBound (powerBoxCross 18 15 2 half_16_02_φ1) (185903263004581/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 15) (u := 13) (t := 16)
    (D := 2) (ψ := (202193710543/5000000000000 : ℝ)) half_16_02_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_02_φ1, half_16_02_φ2, half_16_02_φ3, half_16_02_φ4, half_16_02_φ5, half_16_02_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_02_φ1, half_16_02_φ2, half_16_02_φ3, half_16_02_φ4, half_16_02_φ5, half_16_02_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_02_φ1, half_16_02_φ2, half_16_02_φ3, half_16_02_φ4, half_16_02_φ5, half_16_02_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_14_02 half_16_01
    (by simpa only [half_16_02_φ2, show (2:ℝ)*2=4 by norm_num] using half_16_02_hx2)
  exact h.weaken (by norm_num [half_16_02_φ1, half_16_02_φ2, half_16_02_φ3, half_16_02_φ4, half_16_02_φ5, half_16_02_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_02 : AdmissibleExponent 18 32 (100066088348539/5000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 14) (ψ := (490652196293/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_15_02
    (by simpa only [half_16_02_φ1] using half_16_02_hx1)
  exact admissibleExponent_mono h (by norm_num [half_16_02_φ1, half_16_02_φ2, half_16_02_φ3, half_16_02_φ4, half_16_02_φ5, half_16_02_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_17_02_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (251383470593/5000000000000 : ℝ)

def half_17_02_φ2 : Fin 2 → ℝ := Fin.snoc half_17_02_φ1 (205971163727/5000000000000 : ℝ)

def half_17_02_φ3 : Fin 3 → ℝ := Fin.snoc half_17_02_φ2 (80880163083/2000000000000 : ℝ)

def half_17_02_φ4 : Fin 4 → ℝ := Fin.snoc half_17_02_φ3 (396461953951/10000000000000 : ℝ)

def half_17_02_φ5 : Fin 5 → ℝ := Fin.snoc half_17_02_φ4 (4882564049/125000000000 : ℝ)

def half_17_02_φ6 : Fin 6 → ℝ := Fin.snoc half_17_02_φ5 (9795248141/250000000000 : ℝ)

theorem half_17_02_hF2 : SourcePowerBound (paddedMoment 18 0 2 64 half_17_02_φ6) (36301329267067/5000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 6) (r := 0) (D := 64)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_17_02_φ6 (by norm_num [half_17_02_φ1, half_17_02_φ2, half_17_02_φ3, half_17_02_φ4, half_17_02_φ5, half_17_02_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_02_φ1, half_17_02_φ2, half_17_02_φ3, half_17_02_φ4, half_17_02_φ5, half_17_02_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_02_φ1, half_17_02_φ2, half_17_02_φ3, half_17_02_φ4, half_17_02_φ5, half_17_02_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_17_02_φ1, half_17_02_φ2, half_17_02_φ3, half_17_02_φ4, half_17_02_φ5, half_17_02_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_17_02_hx6 : SourcePowerBound (powerBoxCross 18 11 64 half_17_02_φ6) (119072343900033/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 11) (r := 2) (v := 14) (w := 15) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_17_02_φ6 (by norm_num [half_17_02_φ1, half_17_02_φ2, half_17_02_φ3, half_17_02_φ4, half_17_02_φ5, half_17_02_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_02_φ1, half_17_02_φ2, half_17_02_φ3, half_17_02_φ4, half_17_02_φ5, half_17_02_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_17_02_hF2 half_14_02 half_15_02
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_17_02_φ1, half_17_02_φ2, half_17_02_φ3, half_17_02_φ4, half_17_02_φ5, half_17_02_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_02_hx5 : SourcePowerBound (powerBoxCross 18 12 32 half_17_02_φ5) (131655156910951/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 5) (s := 12) (u := 10) (t := 13)
    (D := 32) (ψ := (9795248141/250000000000 : ℝ)) half_17_02_φ5
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_02_φ1, half_17_02_φ2, half_17_02_φ3, half_17_02_φ4, half_17_02_φ5, half_17_02_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_02_φ1, half_17_02_φ2, half_17_02_φ3, half_17_02_φ4, half_17_02_φ5, half_17_02_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_02_φ1, half_17_02_φ2, half_17_02_φ3, half_17_02_φ4, half_17_02_φ5, half_17_02_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_02 half_13_02
    (by simpa only [half_17_02_φ6, show (2:ℝ)*32=64 by norm_num] using half_17_02_hx6)
  exact h.weaken (by norm_num [half_17_02_φ1, half_17_02_φ2, half_17_02_φ3, half_17_02_φ4, half_17_02_φ5, half_17_02_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_02_hx4 : SourcePowerBound (powerBoxCross 18 13 16 half_17_02_φ4) (29162851657591/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 13) (u := 11) (t := 14)
    (D := 16) (ψ := (4882564049/125000000000 : ℝ)) half_17_02_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_02_φ1, half_17_02_φ2, half_17_02_φ3, half_17_02_φ4, half_17_02_φ5, half_17_02_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_02_φ1, half_17_02_φ2, half_17_02_φ3, half_17_02_φ4, half_17_02_φ5, half_17_02_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_02_φ1, half_17_02_φ2, half_17_02_φ3, half_17_02_φ4, half_17_02_φ5, half_17_02_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_02 half_14_02
    (by simpa only [half_17_02_φ5, show (2:ℝ)*16=32 by norm_num] using half_17_02_hx5)
  exact h.weaken (by norm_num [half_17_02_φ1, half_17_02_φ2, half_17_02_φ3, half_17_02_φ4, half_17_02_φ5, half_17_02_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_02_hx3 : SourcePowerBound (powerBoxCross 18 14 8 half_17_02_φ3) (16171576758463/1000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 14) (u := 12) (t := 15)
    (D := 8) (ψ := (396461953951/10000000000000 : ℝ)) half_17_02_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_02_φ1, half_17_02_φ2, half_17_02_φ3, half_17_02_φ4, half_17_02_φ5, half_17_02_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_02_φ1, half_17_02_φ2, half_17_02_φ3, half_17_02_φ4, half_17_02_φ5, half_17_02_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_02_φ1, half_17_02_φ2, half_17_02_φ3, half_17_02_φ4, half_17_02_φ5, half_17_02_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_13_02 half_15_02
    (by simpa only [half_17_02_φ4, show (2:ℝ)*8=16 by norm_num] using half_17_02_hx4)
  exact h.weaken (by norm_num [half_17_02_φ1, half_17_02_φ2, half_17_02_φ3, half_17_02_φ4, half_17_02_φ5, half_17_02_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_02_hx2 : SourcePowerBound (powerBoxCross 18 15 4 half_17_02_φ2) (179455216516621/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 15) (u := 13) (t := 16)
    (D := 4) (ψ := (80880163083/2000000000000 : ℝ)) half_17_02_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_02_φ1, half_17_02_φ2, half_17_02_φ3, half_17_02_φ4, half_17_02_φ5, half_17_02_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_02_φ1, half_17_02_φ2, half_17_02_φ3, half_17_02_φ4, half_17_02_φ5, half_17_02_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_02_φ1, half_17_02_φ2, half_17_02_φ3, half_17_02_φ4, half_17_02_φ5, half_17_02_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_14_02 half_16_02
    (by simpa only [half_17_02_φ3, show (2:ℝ)*4=8 by norm_num] using half_17_02_hx3)
  exact h.weaken (by norm_num [half_17_02_φ1, half_17_02_φ2, half_17_02_φ3, half_17_02_φ4, half_17_02_φ5, half_17_02_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_02_hx1 : SourcePowerBound (powerBoxCross 18 16 2 half_17_02_φ1) (20057295940719/1000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 16) (u := 14) (t := 17)
    (D := 2) (ψ := (205971163727/5000000000000 : ℝ)) half_17_02_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_02_φ1, half_17_02_φ2, half_17_02_φ3, half_17_02_φ4, half_17_02_φ5, half_17_02_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_02_φ1, half_17_02_φ2, half_17_02_φ3, half_17_02_φ4, half_17_02_φ5, half_17_02_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_02_φ1, half_17_02_φ2, half_17_02_φ3, half_17_02_φ4, half_17_02_φ5, half_17_02_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_15_02 half_17_01
    (by simpa only [half_17_02_φ2, show (2:ℝ)*2=4 by norm_num] using half_17_02_hx2)
  exact h.weaken (by norm_num [half_17_02_φ1, half_17_02_φ2, half_17_02_φ3, half_17_02_φ4, half_17_02_φ5, half_17_02_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_02 : AdmissibleExponent 18 34 (54039683645989/2500000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 15) (ψ := (251383470593/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_16_02
    (by simpa only [half_17_02_φ1] using half_17_02_hx1)
  exact admissibleExponent_mono h (by norm_num [half_17_02_φ1, half_17_02_φ2, half_17_02_φ3, half_17_02_φ4, half_17_02_φ5, half_17_02_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])


end Waring.SeedCompletionHigher18SimpleSeeds
