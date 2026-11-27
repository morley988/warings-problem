import Waring.SeedCompletionHigher18SimpleSeedsC00

noncomputable section
set_option maxHeartbeats 2000000
namespace Waring.SeedCompletionHigher18SimpleSeeds
open SmoothMoments FirstStageTransport SeedCompletionNaturalBox
open SeedCompletionSourceBounds SeedCompletionPaddedSource SeedCompletionGeneralTerminal
open PolicyCompletionMajorPowerRanges

def half_9_01_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (39043182299/1000000000000 : ℝ)

def half_9_01_φ2 : Fin 2 → ℝ := Fin.snoc half_9_01_φ1 (16872873799/500000000000 : ℝ)

def half_9_01_φ3 : Fin 3 → ℝ := Fin.snoc half_9_01_φ2 (79610189181/2500000000000 : ℝ)

theorem half_9_01_hF2 : SourcePowerBound (paddedMoment 18 0 2 8 half_9_01_φ3) (28318583579803/5000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_01_φ3 (by norm_num [half_9_01_φ1, half_9_01_φ2, half_9_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_01_φ1, half_9_01_φ2, half_9_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_01_φ1, half_9_01_φ2, half_9_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_01_φ1, half_9_01_φ2, half_9_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_9_01_hF1 : SourcePowerBound (paddedMoment 18 0 1 8 half_9_01_φ3) (11106194526601/5000000000000 : ℝ) := by
  have h := padded_second_power (k := 18) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_01_φ3 (by norm_num [half_9_01_φ1, half_9_01_φ2, half_9_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_01_φ1, half_9_01_φ2, half_9_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_01_φ1, half_9_01_φ2, half_9_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_01_φ1, half_9_01_φ2, half_9_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_9_01_hx3 : SourcePowerBound (powerBoxCross 18 6 8 half_9_01_φ3) (37128353572703/5000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 18) (s := 6) (r := 1) (v := 2) (t := 10) (D := 8)
    (a := (3/10 : ℝ)) (b := (1/10 : ℝ)) (c := (3/5 : ℝ))
    (by norm_num) half_9_01_φ3 (by norm_num [half_9_01_φ1, half_9_01_φ2, half_9_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_01_φ1, half_9_01_φ2, half_9_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_9_01_hF1 half_9_01_hF2 half_10_00
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_9_01_φ1, half_9_01_φ2, half_9_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_9_01_hx2 : SourcePowerBound (powerBoxCross 18 7 4 half_9_01_φ2) (82941111422521/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 7) (u := 5) (t := 8)
    (D := 4) (ψ := (79610189181/2500000000000 : ℝ)) half_9_01_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_01_φ1, half_9_01_φ2, half_9_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_01_φ1, half_9_01_φ2, half_9_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_01_φ1, half_9_01_φ2, half_9_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_6 SeedCompletionEven18SecondSeeds.degree18_half_8
    (by simpa only [half_9_01_φ3, show (2:ℝ)*4=8 by norm_num] using half_9_01_hx3)
  exact h.weaken (by norm_num [half_9_01_φ1, half_9_01_φ2, half_9_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_9_01_hx1 : SourcePowerBound (powerBoxCross 18 8 2 half_9_01_φ1) (93816889167217/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 8) (u := 6) (t := 9)
    (D := 2) (ψ := (16872873799/500000000000 : ℝ)) half_9_01_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_01_φ1, half_9_01_φ2, half_9_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_01_φ1, half_9_01_φ2, half_9_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_01_φ1, half_9_01_φ2, half_9_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_7 half_9_00
    (by simpa only [half_9_01_φ2, show (2:ℝ)*2=4 by norm_num] using half_9_01_hx2)
  exact h.weaken (by norm_num [half_9_01_φ1, half_9_01_φ2, half_9_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_9_01 : AdmissibleExponent 18 18 (99673366512067/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 7) (ψ := (39043182299/1000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_8
    (by simpa only [half_9_01_φ1] using half_9_01_hx1)
  exact admissibleExponent_mono h (by norm_num [half_9_01_φ1, half_9_01_φ2, half_9_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_10_01_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (422707494581/10000000000000 : ℝ)

def half_10_01_φ2 : Fin 2 → ℝ := Fin.snoc half_10_01_φ1 (353493795979/10000000000000 : ℝ)

def half_10_01_φ3 : Fin 3 → ℝ := Fin.snoc half_10_01_φ2 (63180211579/2000000000000 : ℝ)

theorem half_10_01_hF2 : SourcePowerBound (paddedMoment 18 0 2 8 half_10_01_φ3) (10860556045759/2000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_10_01_φ3 (by norm_num [half_10_01_φ1, half_10_01_φ2, half_10_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_01_φ1, half_10_01_φ2, half_10_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_01_φ1, half_10_01_φ2, half_10_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_10_01_φ1, half_10_01_φ2, half_10_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_10_01_hx3 : SourcePowerBound (powerBoxCross 18 7 8 half_10_01_φ3) (83641653862833/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 7) (r := 2) (v := 9) (w := 10) (D := 8)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_10_01_φ3 (by norm_num [half_10_01_φ1, half_10_01_φ2, half_10_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_01_φ1, half_10_01_φ2, half_10_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_10_01_hF2 half_9_01 half_10_00
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_10_01_φ1, half_10_01_φ2, half_10_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_01_hx2 : SourcePowerBound (powerBoxCross 18 8 4 half_10_01_φ2) (5827801644247/625000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 8) (u := 6) (t := 9)
    (D := 4) (ψ := (63180211579/2000000000000 : ℝ)) half_10_01_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_01_φ1, half_10_01_φ2, half_10_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_01_φ1, half_10_01_φ2, half_10_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_01_φ1, half_10_01_φ2, half_10_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_7 half_9_01
    (by simpa only [half_10_01_φ3, show (2:ℝ)*4=8 by norm_num] using half_10_01_hx3)
  exact h.weaken (by norm_num [half_10_01_φ1, half_10_01_φ2, half_10_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_01_hx1 : SourcePowerBound (powerBoxCross 18 9 2 half_10_01_φ1) (21176561220637/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 9) (u := 7) (t := 10)
    (D := 2) (ψ := (353493795979/10000000000000 : ℝ)) half_10_01_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_01_φ1, half_10_01_φ2, half_10_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_01_φ1, half_10_01_φ2, half_10_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_01_φ1, half_10_01_φ2, half_10_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_8 half_10_00
    (by simpa only [half_10_01_φ2, show (2:ℝ)*2=4 by norm_num] using half_10_01_hx2)
  exact h.weaken (by norm_num [half_10_01_φ1, half_10_01_φ2, half_10_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_01 : AdmissibleExponent 18 20 (56534416755531/5000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 8) (ψ := (422707494581/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_9_01
    (by simpa only [half_10_01_φ1] using half_10_01_hx1)
  exact admissibleExponent_mono h (by norm_num [half_10_01_φ1, half_10_01_φ2, half_10_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_11_01_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (45816981117/1000000000000 : ℝ)

def half_11_01_φ2 : Fin 2 → ℝ := Fin.snoc half_11_01_φ1 (390355964703/10000000000000 : ℝ)

def half_11_01_φ3 : Fin 3 → ℝ := Fin.snoc half_11_01_φ2 (121623106531/2500000000000 : ℝ)

theorem half_11_01_hF2 : SourcePowerBound (paddedMoment 18 0 2 8 half_11_01_φ3) (41914071698153/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_11_01_φ3 (by norm_num [half_11_01_φ1, half_11_01_φ2, half_11_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_01_φ1, half_11_01_φ2, half_11_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_01_φ1, half_11_01_φ2, half_11_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_11_01_φ1, half_11_01_φ2, half_11_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_11_01_hx3 : SourcePowerBound (powerBoxCross 18 8 8 half_11_01_φ3) (45643743749097/5000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 8) (r := 2) (v := 10) (w := 11) (D := 8)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_11_01_φ3 (by norm_num [half_11_01_φ1, half_11_01_φ2, half_11_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_01_φ1, half_11_01_φ2, half_11_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_11_01_hF2 half_10_01 half_11_00
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_11_01_φ1, half_11_01_φ2, half_11_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_01_hx2 : SourcePowerBound (powerBoxCross 18 9 4 half_11_01_φ2) (103817293621537/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 9) (u := 7) (t := 10)
    (D := 4) (ψ := (121623106531/2500000000000 : ℝ)) half_11_01_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_01_φ1, half_11_01_φ2, half_11_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_01_φ1, half_11_01_φ2, half_11_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_01_φ1, half_11_01_φ2, half_11_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_8 half_10_01
    (by simpa only [half_11_01_φ3, show (2:ℝ)*4=8 by norm_num] using half_11_01_hx3)
  exact h.weaken (by norm_num [half_11_01_φ1, half_11_01_φ2, half_11_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_01_hx1 : SourcePowerBound (powerBoxCross 18 10 2 half_11_01_φ1) (118346530712341/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 10) (u := 8) (t := 11)
    (D := 2) (ψ := (390355964703/10000000000000 : ℝ)) half_11_01_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_01_φ1, half_11_01_φ2, half_11_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_01_φ1, half_11_01_φ2, half_11_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_01_φ1, half_11_01_φ2, half_11_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_01 half_11_00
    (by simpa only [half_11_01_φ2, show (2:ℝ)*2=4 by norm_num] using half_11_01_hx2)
  exact h.weaken (by norm_num [half_11_01_φ1, half_11_01_φ2, half_11_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_01 : AdmissibleExponent 18 22 (127051757124571/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 9) (ψ := (45816981117/1000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_10_01
    (by simpa only [half_11_01_φ1] using half_11_01_hx1)
  exact admissibleExponent_mono h (by norm_num [half_11_01_φ1, half_11_01_φ2, half_11_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_12_01_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (47228847109/1000000000000 : ℝ)

def half_12_01_φ2 : Fin 2 → ℝ := Fin.snoc half_12_01_φ1 (372555376029/10000000000000 : ℝ)

def half_12_01_φ3 : Fin 3 → ℝ := Fin.snoc half_12_01_φ2 (357810069759/10000000000000 : ℝ)

def half_12_01_φ4 : Fin 4 → ℝ := Fin.snoc half_12_01_φ3 (328999538837/10000000000000 : ℝ)

theorem half_12_01_hF2 : SourcePowerBound (paddedMoment 18 0 2 16 half_12_01_φ4) (12377134751707/2000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_12_01_φ4 (by norm_num [half_12_01_φ1, half_12_01_φ2, half_12_01_φ3, half_12_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_01_φ1, half_12_01_φ2, half_12_01_φ3, half_12_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_01_φ1, half_12_01_φ2, half_12_01_φ3, half_12_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_12_01_φ1, half_12_01_φ2, half_12_01_φ3, half_12_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_12_01_hF1 : SourcePowerBound (paddedMoment 18 0 1 16 half_12_01_φ4) (4792378250569/2000000000000 : ℝ) := by
  have h := padded_second_power (k := 18) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_12_01_φ4 (by norm_num [half_12_01_φ1, half_12_01_φ2, half_12_01_φ3, half_12_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_01_φ1, half_12_01_φ2, half_12_01_φ3, half_12_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_01_φ1, half_12_01_φ2, half_12_01_φ3, half_12_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_12_01_φ1, half_12_01_φ2, half_12_01_φ3, half_12_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_12_01_hx4 : SourcePowerBound (powerBoxCross 18 8 16 half_12_01_φ4) (3736108279039/400000000000 : ℝ) := by
  have h := full_B_cross_power (k := 18) (s := 8) (r := 1) (v := 2) (t := 11) (D := 16)
    (a := (1/22 : ℝ)) (b := (5/22 : ℝ)) (c := (8/11 : ℝ))
    (by norm_num) half_12_01_φ4 (by norm_num [half_12_01_φ1, half_12_01_φ2, half_12_01_φ3, half_12_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_01_φ1, half_12_01_φ2, half_12_01_φ3, half_12_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_12_01_hF1 half_12_01_hF2 half_11_01
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_12_01_φ1, half_12_01_φ2, half_12_01_φ3, half_12_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_01_hx3 : SourcePowerBound (powerBoxCross 18 9 8 half_12_01_φ3) (25920393679097/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 9) (u := 7) (t := 10)
    (D := 8) (ψ := (328999538837/10000000000000 : ℝ)) half_12_01_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_01_φ1, half_12_01_φ2, half_12_01_φ3, half_12_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_01_φ1, half_12_01_φ2, half_12_01_φ3, half_12_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_01_φ1, half_12_01_φ2, half_12_01_φ3, half_12_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_8 half_10_01
    (by simpa only [half_12_01_φ4, show (2:ℝ)*8=16 by norm_num] using half_12_01_hx4)
  exact h.weaken (by norm_num [half_12_01_φ1, half_12_01_φ2, half_12_01_φ3, half_12_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_01_hx2 : SourcePowerBound (powerBoxCross 18 10 4 half_12_01_φ2) (57929967024651/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 10) (u := 8) (t := 11)
    (D := 4) (ψ := (357810069759/10000000000000 : ℝ)) half_12_01_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_01_φ1, half_12_01_φ2, half_12_01_φ3, half_12_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_01_φ1, half_12_01_φ2, half_12_01_φ3, half_12_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_01_φ1, half_12_01_φ2, half_12_01_φ3, half_12_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_01 half_11_01
    (by simpa only [half_12_01_φ3, show (2:ℝ)*4=8 by norm_num] using half_12_01_hx3)
  exact h.weaken (by norm_num [half_12_01_φ1, half_12_01_φ2, half_12_01_φ3, half_12_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_01_hx1 : SourcePowerBound (powerBoxCross 18 11 2 half_12_01_φ1) (131523537583507/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 11) (u := 9) (t := 12)
    (D := 2) (ψ := (372555376029/10000000000000 : ℝ)) half_12_01_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_01_φ1, half_12_01_φ2, half_12_01_φ3, half_12_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_01_φ1, half_12_01_φ2, half_12_01_φ3, half_12_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_01_φ1, half_12_01_φ2, half_12_01_φ3, half_12_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_01 half_12_00
    (by simpa only [half_12_01_φ2, show (2:ℝ)*2=4 by norm_num] using half_12_01_hx2)
  exact h.weaken (by norm_num [half_12_01_φ1, half_12_01_φ2, half_12_01_φ3, half_12_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_01 : AdmissibleExponent 18 24 (141441595476397/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 10) (ψ := (47228847109/1000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_11_01
    (by simpa only [half_12_01_φ1] using half_12_01_hx1)
  exact admissibleExponent_mono h (by norm_num [half_12_01_φ1, half_12_01_φ2, half_12_01_φ3, half_12_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_13_01_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (246581501113/5000000000000 : ℝ)

def half_13_01_φ2 : Fin 2 → ℝ := Fin.snoc half_13_01_φ1 (76177881663/2000000000000 : ℝ)

def half_13_01_φ3 : Fin 3 → ℝ := Fin.snoc half_13_01_φ2 (384289153909/10000000000000 : ℝ)

def half_13_01_φ4 : Fin 4 → ℝ := Fin.snoc half_13_01_φ3 (413421413243/10000000000000 : ℝ)

theorem half_13_01_hF2 : SourcePowerBound (paddedMoment 18 0 2 16 half_13_01_φ4) (54740088137657/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_13_01_φ4 (by norm_num [half_13_01_φ1, half_13_01_φ2, half_13_01_φ3, half_13_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_01_φ1, half_13_01_φ2, half_13_01_φ3, half_13_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_01_φ1, half_13_01_φ2, half_13_01_φ3, half_13_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_13_01_φ1, half_13_01_φ2, half_13_01_φ3, half_13_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_13_01_hx4 : SourcePowerBound (powerBoxCross 18 9 16 half_13_01_φ4) (102031956929967/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 9) (r := 2) (v := 12) (w := 12) (D := 16)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_13_01_φ4 (by norm_num [half_13_01_φ1, half_13_01_φ2, half_13_01_φ3, half_13_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_01_φ1, half_13_01_φ2, half_13_01_φ3, half_13_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_13_01_hF2 half_12_01 half_12_01
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_13_01_φ1, half_13_01_φ2, half_13_01_φ3, half_13_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_01_hx3 : SourcePowerBound (powerBoxCross 18 10 8 half_13_01_φ3) (114366310400699/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 10) (u := 8) (t := 11)
    (D := 8) (ψ := (413421413243/10000000000000 : ℝ)) half_13_01_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_01_φ1, half_13_01_φ2, half_13_01_φ3, half_13_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_01_φ1, half_13_01_φ2, half_13_01_φ3, half_13_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_01_φ1, half_13_01_φ2, half_13_01_φ3, half_13_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_01 half_11_01
    (by simpa only [half_13_01_φ4, show (2:ℝ)*8=16 by norm_num] using half_13_01_hx4)
  exact h.weaken (by norm_num [half_13_01_φ1, half_13_01_φ2, half_13_01_φ3, half_13_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_01_hx2 : SourcePowerBound (powerBoxCross 18 11 4 half_13_01_φ2) (3198597150931/250000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 11) (u := 9) (t := 12)
    (D := 4) (ψ := (384289153909/10000000000000 : ℝ)) half_13_01_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_01_φ1, half_13_01_φ2, half_13_01_φ3, half_13_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_01_φ1, half_13_01_φ2, half_13_01_φ3, half_13_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_01_φ1, half_13_01_φ2, half_13_01_φ3, half_13_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_01 half_12_01
    (by simpa only [half_13_01_φ3, show (2:ℝ)*4=8 by norm_num] using half_13_01_hx3)
  exact h.weaken (by norm_num [half_13_01_φ1, half_13_01_φ2, half_13_01_φ3, half_13_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_01_hx1 : SourcePowerBound (powerBoxCross 18 12 2 half_13_01_φ1) (72479691146083/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 12) (u := 10) (t := 13)
    (D := 2) (ψ := (76177881663/2000000000000 : ℝ)) half_13_01_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_01_φ1, half_13_01_φ2, half_13_01_φ3, half_13_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_01_φ1, half_13_01_φ2, half_13_01_φ3, half_13_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_01_φ1, half_13_01_φ2, half_13_01_φ3, half_13_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_01 half_13_00
    (by simpa only [half_13_01_φ2, show (2:ℝ)*2=4 by norm_num] using half_13_01_hx2)
  exact h.weaken (by norm_num [half_13_01_φ1, half_13_01_φ2, half_13_01_φ3, half_13_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_01 : AdmissibleExponent 18 26 (39075532835841/2500000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 11) (ψ := (246581501113/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_12_01
    (by simpa only [half_13_01_φ1] using half_13_01_hx1)
  exact admissibleExponent_mono h (by norm_num [half_13_01_φ1, half_13_01_φ2, half_13_01_φ3, half_13_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_14_01_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (253039693921/5000000000000 : ℝ)

def half_14_01_φ2 : Fin 2 → ℝ := Fin.snoc half_14_01_φ1 (38677038883/1000000000000 : ℝ)

def half_14_01_φ3 : Fin 3 → ℝ := Fin.snoc half_14_01_φ2 (376022460647/10000000000000 : ℝ)

def half_14_01_φ4 : Fin 4 → ℝ := Fin.snoc half_14_01_φ3 (365982219603/10000000000000 : ℝ)

def half_14_01_φ5 : Fin 5 → ℝ := Fin.snoc half_14_01_φ4 (334128766651/10000000000000 : ℝ)

theorem half_14_01_hF2 : SourcePowerBound (paddedMoment 18 0 2 32 half_14_01_φ5) (69581855597777/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_14_01_φ5 (by norm_num [half_14_01_φ1, half_14_01_φ2, half_14_01_φ3, half_14_01_φ4, half_14_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_01_φ1, half_14_01_φ2, half_14_01_φ3, half_14_01_φ4, half_14_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_01_φ1, half_14_01_φ2, half_14_01_φ3, half_14_01_φ4, half_14_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_14_01_φ1, half_14_01_φ2, half_14_01_φ3, half_14_01_φ4, half_14_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_14_01_hx5 : SourcePowerBound (powerBoxCross 18 9 32 half_14_01_φ5) (102589450861111/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 9) (r := 2) (v := 12) (w := 12) (D := 32)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_14_01_φ5 (by norm_num [half_14_01_φ1, half_14_01_φ2, half_14_01_φ3, half_14_01_φ4, half_14_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_01_φ1, half_14_01_φ2, half_14_01_φ3, half_14_01_φ4, half_14_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_14_01_hF2 half_12_01 half_12_01
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_14_01_φ1, half_14_01_φ2, half_14_01_φ3, half_14_01_φ4, half_14_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_01_hx4 : SourcePowerBound (powerBoxCross 18 10 16 half_14_01_φ4) (28344719763949/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 10) (u := 8) (t := 11)
    (D := 16) (ψ := (334128766651/10000000000000 : ℝ)) half_14_01_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_01_φ1, half_14_01_φ2, half_14_01_φ3, half_14_01_φ4, half_14_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_01_φ1, half_14_01_φ2, half_14_01_φ3, half_14_01_φ4, half_14_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_01_φ1, half_14_01_φ2, half_14_01_φ3, half_14_01_φ4, half_14_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_01 half_11_01
    (by simpa only [half_14_01_φ5, show (2:ℝ)*16=32 by norm_num] using half_14_01_hx5)
  exact h.weaken (by norm_num [half_14_01_φ1, half_14_01_φ2, half_14_01_φ3, half_14_01_φ4, half_14_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_01_hx3 : SourcePowerBound (powerBoxCross 18 11 8 half_14_01_φ3) (126128088650009/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 11) (u := 9) (t := 12)
    (D := 8) (ψ := (365982219603/10000000000000 : ℝ)) half_14_01_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_01_φ1, half_14_01_φ2, half_14_01_φ3, half_14_01_φ4, half_14_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_01_φ1, half_14_01_φ2, half_14_01_φ3, half_14_01_φ4, half_14_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_01_φ1, half_14_01_φ2, half_14_01_φ3, half_14_01_φ4, half_14_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_01 half_12_01
    (by simpa only [half_14_01_φ4, show (2:ℝ)*8=16 by norm_num] using half_14_01_hx4)
  exact h.weaken (by norm_num [half_14_01_φ1, half_14_01_φ2, half_14_01_φ3, half_14_01_φ4, half_14_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_01_hx2 : SourcePowerBound (powerBoxCross 18 12 4 half_14_01_φ2) (35149101644651/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 12) (u := 10) (t := 13)
    (D := 4) (ψ := (376022460647/10000000000000 : ℝ)) half_14_01_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_01_φ1, half_14_01_φ2, half_14_01_φ3, half_14_01_φ4, half_14_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_01_φ1, half_14_01_φ2, half_14_01_φ3, half_14_01_φ4, half_14_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_01_φ1, half_14_01_φ2, half_14_01_φ3, half_14_01_φ4, half_14_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_01 half_13_01
    (by simpa only [half_14_01_φ3, show (2:ℝ)*4=8 by norm_num] using half_14_01_hx3)
  exact h.weaken (by norm_num [half_14_01_φ1, half_14_01_φ2, half_14_01_φ3, half_14_01_φ4, half_14_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_01_hx1 : SourcePowerBound (powerBoxCross 18 13 2 half_14_01_φ1) (158898082036361/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 13) (u := 11) (t := 14)
    (D := 2) (ψ := (38677038883/1000000000000 : ℝ)) half_14_01_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_01_φ1, half_14_01_φ2, half_14_01_φ3, half_14_01_φ4, half_14_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_01_φ1, half_14_01_φ2, half_14_01_φ3, half_14_01_φ4, half_14_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_01_φ1, half_14_01_φ2, half_14_01_φ3, half_14_01_φ4, half_14_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_01 half_14_00
    (by simpa only [half_14_01_φ2, show (2:ℝ)*2=4 by norm_num] using half_14_01_hx2)
  exact h.weaken (by norm_num [half_14_01_φ1, half_14_01_φ2, half_14_01_φ3, half_14_01_φ4, half_14_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_01 : AdmissibleExponent 18 28 (171550066732411/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 12) (ψ := (253039693921/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_13_01
    (by simpa only [half_14_01_φ1] using half_14_01_hx1)
  exact admissibleExponent_mono h (by norm_num [half_14_01_φ1, half_14_01_φ2, half_14_01_φ3, half_14_01_φ4, half_14_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_15_01_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (64712104599/1250000000000 : ℝ)

def half_15_01_φ2 : Fin 2 → ℝ := Fin.snoc half_15_01_φ1 (197217171597/5000000000000 : ℝ)

def half_15_01_φ3 : Fin 3 → ℝ := Fin.snoc half_15_01_φ2 (195192524161/5000000000000 : ℝ)

def half_15_01_φ4 : Fin 4 → ℝ := Fin.snoc half_15_01_φ3 (39209706681/1000000000000 : ℝ)

def half_15_01_φ5 : Fin 5 → ℝ := Fin.snoc half_15_01_φ4 (434543344117/10000000000000 : ℝ)

theorem half_15_01_hF2 : SourcePowerBound (paddedMoment 18 0 2 32 half_15_01_φ5) (12282602279803/2000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_15_01_φ5 (by norm_num [half_15_01_φ1, half_15_01_φ2, half_15_01_φ3, half_15_01_φ4, half_15_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_01_φ1, half_15_01_φ2, half_15_01_φ3, half_15_01_φ4, half_15_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_01_φ1, half_15_01_φ2, half_15_01_φ3, half_15_01_φ4, half_15_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_15_01_φ1, half_15_01_φ2, half_15_01_φ3, half_15_01_φ4, half_15_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_15_01_hx5 : SourcePowerBound (powerBoxCross 18 10 32 half_15_01_φ5) (110620825082111/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 10) (r := 2) (v := 13) (w := 14) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_15_01_φ5 (by norm_num [half_15_01_φ1, half_15_01_φ2, half_15_01_φ3, half_15_01_φ4, half_15_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_01_φ1, half_15_01_φ2, half_15_01_φ3, half_15_01_φ4, half_15_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_15_01_hF2 half_13_01 half_14_01
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_15_01_φ1, half_15_01_φ2, half_15_01_φ3, half_15_01_φ4, half_15_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_01_hx4 : SourcePowerBound (powerBoxCross 18 11 16 half_15_01_φ4) (123770718631013/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 11) (u := 9) (t := 12)
    (D := 16) (ψ := (434543344117/10000000000000 : ℝ)) half_15_01_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_01_φ1, half_15_01_φ2, half_15_01_φ3, half_15_01_φ4, half_15_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_01_φ1, half_15_01_φ2, half_15_01_φ3, half_15_01_φ4, half_15_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_01_φ1, half_15_01_φ2, half_15_01_φ3, half_15_01_φ4, half_15_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_01 half_12_01
    (by simpa only [half_15_01_φ5, show (2:ℝ)*16=32 by norm_num] using half_15_01_hx5)
  exact h.weaken (by norm_num [half_15_01_φ1, half_15_01_φ2, half_15_01_φ3, half_15_01_φ4, half_15_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_01_hx3 : SourcePowerBound (powerBoxCross 18 12 8 half_15_01_φ3) (137902753118383/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 12) (u := 10) (t := 13)
    (D := 8) (ψ := (39209706681/1000000000000 : ℝ)) half_15_01_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_01_φ1, half_15_01_φ2, half_15_01_φ3, half_15_01_φ4, half_15_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_01_φ1, half_15_01_φ2, half_15_01_φ3, half_15_01_φ4, half_15_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_01_φ1, half_15_01_φ2, half_15_01_φ3, half_15_01_φ4, half_15_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_01 half_13_01
    (by simpa only [half_15_01_φ4, show (2:ℝ)*8=16 by norm_num] using half_15_01_hx4)
  exact h.weaken (by norm_num [half_15_01_φ1, half_15_01_φ2, half_15_01_φ3, half_15_01_φ4, half_15_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_01_hx2 : SourcePowerBound (powerBoxCross 18 13 4 half_15_01_φ2) (76819457355727/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 13) (u := 11) (t := 14)
    (D := 4) (ψ := (195192524161/5000000000000 : ℝ)) half_15_01_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_01_φ1, half_15_01_φ2, half_15_01_φ3, half_15_01_φ4, half_15_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_01_φ1, half_15_01_φ2, half_15_01_φ3, half_15_01_φ4, half_15_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_01_φ1, half_15_01_φ2, half_15_01_φ3, half_15_01_φ4, half_15_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_01 half_14_01
    (by simpa only [half_15_01_φ3, show (2:ℝ)*4=8 by norm_num] using half_15_01_hx3)
  exact h.weaken (by norm_num [half_15_01_φ1, half_15_01_φ2, half_15_01_φ3, half_15_01_φ4, half_15_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_01_hx1 : SourcePowerBound (powerBoxCross 18 14 2 half_15_01_φ1) (173186670879341/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 14) (u := 12) (t := 15)
    (D := 2) (ψ := (197217171597/5000000000000 : ℝ)) half_15_01_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_01_φ1, half_15_01_φ2, half_15_01_φ3, half_15_01_φ4, half_15_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_01_φ1, half_15_01_φ2, half_15_01_φ3, half_15_01_φ4, half_15_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_01_φ1, half_15_01_φ2, half_15_01_φ3, half_15_01_φ4, half_15_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_13_01 half_15_00
    (by simpa only [half_15_01_φ2, show (2:ℝ)*2=4 by norm_num] using half_15_01_hx2)
  exact h.weaken (by norm_num [half_15_01_φ1, half_15_01_φ2, half_15_01_φ3, half_15_01_φ4, half_15_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_01 : AdmissibleExponent 18 30 (7486579418909/400000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 13) (ψ := (64712104599/1250000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_14_01
    (by simpa only [half_15_01_φ1] using half_15_01_hx1)
  exact admissibleExponent_mono h (by norm_num [half_15_01_φ1, half_15_01_φ2, half_15_01_φ3, half_15_01_φ4, half_15_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_16_01_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (65698629677/1250000000000 : ℝ)

def half_16_01_φ2 : Fin 2 → ℝ := Fin.snoc half_16_01_φ1 (400054993289/10000000000000 : ℝ)

def half_16_01_φ3 : Fin 3 → ℝ := Fin.snoc half_16_01_φ2 (392430410819/10000000000000 : ℝ)

def half_16_01_φ4 : Fin 4 → ℝ := Fin.snoc half_16_01_φ3 (384660996351/10000000000000 : ℝ)

def half_16_01_φ5 : Fin 5 → ℝ := Fin.snoc half_16_01_φ4 (371953850931/10000000000000 : ℝ)

def half_16_01_φ6 : Fin 6 → ℝ := Fin.snoc half_16_01_φ5 (352905198909/10000000000000 : ℝ)

theorem half_16_01_hF2 : SourcePowerBound (paddedMoment 18 0 2 64 half_16_01_φ6) (15238536225307/2000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 6) (r := 0) (D := 64)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_16_01_φ6 (by norm_num [half_16_01_φ1, half_16_01_φ2, half_16_01_φ3, half_16_01_φ4, half_16_01_φ5, half_16_01_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_01_φ1, half_16_01_φ2, half_16_01_φ3, half_16_01_φ4, half_16_01_φ5, half_16_01_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_01_φ1, half_16_01_φ2, half_16_01_φ3, half_16_01_φ4, half_16_01_φ5, half_16_01_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_16_01_φ1, half_16_01_φ2, half_16_01_φ3, half_16_01_φ4, half_16_01_φ5, half_16_01_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_16_01_hx6 : SourcePowerBound (powerBoxCross 18 10 64 half_16_01_φ6) (6918968318993/625000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 10) (r := 2) (v := 13) (w := 14) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_16_01_φ6 (by norm_num [half_16_01_φ1, half_16_01_φ2, half_16_01_φ3, half_16_01_φ4, half_16_01_φ5, half_16_01_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_01_φ1, half_16_01_φ2, half_16_01_φ3, half_16_01_φ4, half_16_01_φ5, half_16_01_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_16_01_hF2 half_13_01 half_14_01
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_16_01_φ1, half_16_01_φ2, half_16_01_φ3, half_16_01_φ4, half_16_01_φ5, half_16_01_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_01_hx5 : SourcePowerBound (powerBoxCross 18 11 32 half_16_01_φ5) (61058958284301/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 5) (s := 11) (u := 9) (t := 12)
    (D := 32) (ψ := (352905198909/10000000000000 : ℝ)) half_16_01_φ5
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_01_φ1, half_16_01_φ2, half_16_01_φ3, half_16_01_φ4, half_16_01_φ5, half_16_01_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_01_φ1, half_16_01_φ2, half_16_01_φ3, half_16_01_φ4, half_16_01_φ5, half_16_01_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_01_φ1, half_16_01_φ2, half_16_01_φ3, half_16_01_φ4, half_16_01_φ5, half_16_01_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_01 half_12_01
    (by simpa only [half_16_01_φ6, show (2:ℝ)*32=64 by norm_num] using half_16_01_hx6)
  exact h.weaken (by norm_num [half_16_01_φ1, half_16_01_φ2, half_16_01_φ3, half_16_01_φ4, half_16_01_φ5, half_16_01_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_01_hx4 : SourcePowerBound (powerBoxCross 18 12 16 half_16_01_φ4) (27067045853227/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 12) (u := 10) (t := 13)
    (D := 16) (ψ := (371953850931/10000000000000 : ℝ)) half_16_01_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_01_φ1, half_16_01_φ2, half_16_01_φ3, half_16_01_φ4, half_16_01_φ5, half_16_01_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_01_φ1, half_16_01_φ2, half_16_01_φ3, half_16_01_φ4, half_16_01_φ5, half_16_01_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_01_φ1, half_16_01_φ2, half_16_01_φ3, half_16_01_φ4, half_16_01_φ5, half_16_01_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_01 half_13_01
    (by simpa only [half_16_01_φ5, show (2:ℝ)*16=32 by norm_num] using half_16_01_hx5)
  exact h.weaken (by norm_num [half_16_01_φ1, half_16_01_φ2, half_16_01_φ3, half_16_01_φ4, half_16_01_φ5, half_16_01_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_01_hx3 : SourcePowerBound (powerBoxCross 18 13 8 half_16_01_φ3) (15035682878427/1000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 13) (u := 11) (t := 14)
    (D := 8) (ψ := (384660996351/10000000000000 : ℝ)) half_16_01_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_01_φ1, half_16_01_φ2, half_16_01_φ3, half_16_01_φ4, half_16_01_φ5, half_16_01_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_01_φ1, half_16_01_φ2, half_16_01_φ3, half_16_01_φ4, half_16_01_φ5, half_16_01_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_01_φ1, half_16_01_φ2, half_16_01_φ3, half_16_01_φ4, half_16_01_φ5, half_16_01_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_01 half_14_01
    (by simpa only [half_16_01_φ4, show (2:ℝ)*8=16 by norm_num] using half_16_01_hx4)
  exact h.weaken (by norm_num [half_16_01_φ1, half_16_01_φ2, half_16_01_φ3, half_16_01_φ4, half_16_01_φ5, half_16_01_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_01_hx2 : SourcePowerBound (powerBoxCross 18 14 4 half_16_01_φ2) (167135678565853/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 14) (u := 12) (t := 15)
    (D := 4) (ψ := (392430410819/10000000000000 : ℝ)) half_16_01_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_01_φ1, half_16_01_φ2, half_16_01_φ3, half_16_01_φ4, half_16_01_φ5, half_16_01_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_01_φ1, half_16_01_φ2, half_16_01_φ3, half_16_01_φ4, half_16_01_φ5, half_16_01_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_01_φ1, half_16_01_φ2, half_16_01_φ3, half_16_01_φ4, half_16_01_φ5, half_16_01_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_13_01 half_15_01
    (by simpa only [half_16_01_φ3, show (2:ℝ)*4=8 by norm_num] using half_16_01_hx3)
  exact h.weaken (by norm_num [half_16_01_φ1, half_16_01_φ2, half_16_01_φ3, half_16_01_φ4, half_16_01_φ5, half_16_01_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_01_hx1 : SourcePowerBound (powerBoxCross 18 15 2 half_16_01_φ1) (187852914334349/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 15) (u := 13) (t := 16)
    (D := 2) (ψ := (400054993289/10000000000000 : ℝ)) half_16_01_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_01_φ1, half_16_01_φ2, half_16_01_φ3, half_16_01_φ4, half_16_01_φ5, half_16_01_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_01_φ1, half_16_01_φ2, half_16_01_φ3, half_16_01_φ4, half_16_01_φ5, half_16_01_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_01_φ1, half_16_01_φ2, half_16_01_φ3, half_16_01_φ4, half_16_01_φ5, half_16_01_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_14_01 half_16_00
    (by simpa only [half_16_01_φ2, show (2:ℝ)*2=4 by norm_num] using half_16_01_hx2)
  exact h.weaken (by norm_num [half_16_01_φ1, half_16_01_φ2, half_16_01_φ3, half_16_01_φ4, half_16_01_φ5, half_16_01_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_01 : AdmissibleExponent 18 32 (203094996419413/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 14) (ψ := (65698629677/1250000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_15_01
    (by simpa only [half_16_01_φ1] using half_16_01_hx1)
  exact admissibleExponent_mono h (by norm_num [half_16_01_φ1, half_16_01_φ2, half_16_01_φ3, half_16_01_φ4, half_16_01_φ5, half_16_01_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_17_01_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (266156281731/5000000000000 : ℝ)

def half_17_01_φ2 : Fin 2 → ℝ := Fin.snoc half_17_01_φ1 (406500040369/10000000000000 : ℝ)

def half_17_01_φ3 : Fin 3 → ℝ := Fin.snoc half_17_01_φ2 (400884007087/10000000000000 : ℝ)

def half_17_01_φ4 : Fin 4 → ℝ := Fin.snoc half_17_01_φ3 (198385878493/5000000000000 : ℝ)

def half_17_01_φ5 : Fin 5 → ℝ := Fin.snoc half_17_01_φ4 (80432601363/2000000000000 : ℝ)

def half_17_01_φ6 : Fin 6 → ℝ := Fin.snoc half_17_01_φ5 (220974353603/5000000000000 : ℝ)

theorem half_17_01_hF2 : SourcePowerBound (paddedMoment 18 0 2 64 half_17_01_φ6) (2735616632873/400000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 6) (r := 0) (D := 64)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_17_01_φ6 (by norm_num [half_17_01_φ1, half_17_01_φ2, half_17_01_φ3, half_17_01_φ4, half_17_01_φ5, half_17_01_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_01_φ1, half_17_01_φ2, half_17_01_φ3, half_17_01_φ4, half_17_01_φ5, half_17_01_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_01_φ1, half_17_01_φ2, half_17_01_φ3, half_17_01_φ4, half_17_01_φ5, half_17_01_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_17_01_φ1, half_17_01_φ2, half_17_01_φ3, half_17_01_φ4, half_17_01_φ5, half_17_01_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_17_01_hx6 : SourcePowerBound (powerBoxCross 18 11 64 half_17_01_φ6) (189360398529/16000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 11) (r := 2) (v := 14) (w := 15) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_17_01_φ6 (by norm_num [half_17_01_φ1, half_17_01_φ2, half_17_01_φ3, half_17_01_φ4, half_17_01_φ5, half_17_01_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_01_φ1, half_17_01_φ2, half_17_01_φ3, half_17_01_φ4, half_17_01_φ5, half_17_01_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_17_01_hF2 half_14_01 half_15_01
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_17_01_φ1, half_17_01_φ2, half_17_01_φ3, half_17_01_φ4, half_17_01_φ5, half_17_01_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_01_hx5 : SourcePowerBound (powerBoxCross 18 12 32 half_17_01_φ5) (132074652851231/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 5) (s := 12) (u := 10) (t := 13)
    (D := 32) (ψ := (220974353603/5000000000000 : ℝ)) half_17_01_φ5
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_01_φ1, half_17_01_φ2, half_17_01_φ3, half_17_01_φ4, half_17_01_φ5, half_17_01_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_01_φ1, half_17_01_φ2, half_17_01_φ3, half_17_01_φ4, half_17_01_φ5, half_17_01_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_01_φ1, half_17_01_φ2, half_17_01_φ3, half_17_01_φ4, half_17_01_φ5, half_17_01_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_01 half_13_01
    (by simpa only [half_17_01_φ6, show (2:ℝ)*32=64 by norm_num] using half_17_01_hx6)
  exact h.weaken (by norm_num [half_17_01_φ1, half_17_01_φ2, half_17_01_φ3, half_17_01_φ4, half_17_01_φ5, half_17_01_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_01_hx4 : SourcePowerBound (powerBoxCross 18 13 16 half_17_01_φ4) (146782690023377/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 13) (u := 11) (t := 14)
    (D := 16) (ψ := (80432601363/2000000000000 : ℝ)) half_17_01_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_01_φ1, half_17_01_φ2, half_17_01_φ3, half_17_01_φ4, half_17_01_φ5, half_17_01_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_01_φ1, half_17_01_φ2, half_17_01_φ3, half_17_01_φ4, half_17_01_φ5, half_17_01_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_01_φ1, half_17_01_φ2, half_17_01_φ3, half_17_01_φ4, half_17_01_φ5, half_17_01_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_01 half_14_01
    (by simpa only [half_17_01_φ5, show (2:ℝ)*16=32 by norm_num] using half_17_01_hx5)
  exact h.weaken (by norm_num [half_17_01_φ1, half_17_01_φ2, half_17_01_φ3, half_17_01_φ4, half_17_01_φ5, half_17_01_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_01_hx3 : SourcePowerBound (powerBoxCross 18 14 8 half_17_01_φ3) (40752158043493/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 14) (u := 12) (t := 15)
    (D := 8) (ψ := (198385878493/5000000000000 : ℝ)) half_17_01_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_01_φ1, half_17_01_φ2, half_17_01_φ3, half_17_01_φ4, half_17_01_φ5, half_17_01_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_01_φ1, half_17_01_φ2, half_17_01_φ3, half_17_01_φ4, half_17_01_φ5, half_17_01_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_01_φ1, half_17_01_φ2, half_17_01_φ3, half_17_01_φ4, half_17_01_φ5, half_17_01_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_13_01 half_15_01
    (by simpa only [half_17_01_φ4, show (2:ℝ)*8=16 by norm_num] using half_17_01_hx4)
  exact h.weaken (by norm_num [half_17_01_φ1, half_17_01_φ2, half_17_01_φ3, half_17_01_φ4, half_17_01_φ5, half_17_01_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_01_hx2 : SourcePowerBound (powerBoxCross 18 15 4 half_17_01_φ2) (90475217069563/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 15) (u := 13) (t := 16)
    (D := 4) (ψ := (400884007087/10000000000000 : ℝ)) half_17_01_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_01_φ1, half_17_01_φ2, half_17_01_φ3, half_17_01_φ4, half_17_01_φ5, half_17_01_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_01_φ1, half_17_01_φ2, half_17_01_φ3, half_17_01_φ4, half_17_01_φ5, half_17_01_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_01_φ1, half_17_01_φ2, half_17_01_φ3, half_17_01_φ4, half_17_01_φ5, half_17_01_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_14_01 half_16_01
    (by simpa only [half_17_01_φ3, show (2:ℝ)*4=8 by norm_num] using half_17_01_hx3)
  exact h.weaken (by norm_num [half_17_01_φ1, half_17_01_φ2, half_17_01_φ3, half_17_01_φ4, half_17_01_φ5, half_17_01_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_01_hx1 : SourcePowerBound (powerBoxCross 18 16 2 half_17_01_φ1) (202816307165863/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 16) (u := 14) (t := 17)
    (D := 2) (ψ := (406500040369/10000000000000 : ℝ)) half_17_01_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_01_φ1, half_17_01_φ2, half_17_01_φ3, half_17_01_φ4, half_17_01_φ5, half_17_01_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_01_φ1, half_17_01_φ2, half_17_01_φ3, half_17_01_φ4, half_17_01_φ5, half_17_01_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_01_φ1, half_17_01_φ2, half_17_01_φ3, half_17_01_φ4, half_17_01_φ5, half_17_01_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_15_01 half_17_00
    (by simpa only [half_17_01_φ2, show (2:ℝ)*2=4 by norm_num] using half_17_01_hx2)
  exact h.weaken (by norm_num [half_17_01_φ1, half_17_01_φ2, half_17_01_φ3, half_17_01_φ4, half_17_01_φ5, half_17_01_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_01 : AdmissibleExponent 18 34 (43863599326637/2000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 15) (ψ := (266156281731/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_16_01
    (by simpa only [half_17_01_φ1] using half_17_01_hx1)
  exact admissibleExponent_mono h (by norm_num [half_17_01_φ1, half_17_01_φ2, half_17_01_φ3, half_17_01_φ4, half_17_01_φ5, half_17_01_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])


end Waring.SeedCompletionHigher18SimpleSeeds
