import Waring.SeedCompletionHigher18SimpleSeedsC03

noncomputable section
set_option maxHeartbeats 2000000
namespace Waring.SeedCompletionHigher18SimpleSeeds
open SmoothMoments FirstStageTransport SeedCompletionNaturalBox
open SeedCompletionSourceBounds SeedCompletionPaddedSource SeedCompletionGeneralTerminal
open PolicyCompletionMajorPowerRanges

def half_9_04_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (43054047657/1250000000000 : ℝ)

def half_9_04_φ2 : Fin 2 → ℝ := Fin.snoc half_9_04_φ1 (12357313013/400000000000 : ℝ)

def half_9_04_φ3 : Fin 3 → ℝ := Fin.snoc half_9_04_φ2 (34539498831/2500000000000 : ℝ)

theorem half_9_04_hF2 : SourcePowerBound (paddedMoment 18 0 2 8 half_9_04_φ3) (13926463340569/2000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_04_φ3 (by norm_num [half_9_04_φ1, half_9_04_φ2, half_9_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_04_φ1, half_9_04_φ2, half_9_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_04_φ1, half_9_04_φ2, half_9_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_04_φ1, half_9_04_φ2, half_9_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_9_04_hF1 : SourcePowerBound (paddedMoment 18 0 1 8 half_9_04_φ3) (5308821113523/2000000000000 : ℝ) := by
  have h := padded_second_power (k := 18) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_04_φ3 (by norm_num [half_9_04_φ1, half_9_04_φ2, half_9_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_04_φ1, half_9_04_φ2, half_9_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_04_φ1, half_9_04_φ2, half_9_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_04_φ1, half_9_04_φ2, half_9_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_9_04_hx3 : SourcePowerBound (powerBoxCross 18 6 8 half_9_04_φ3) (9618236579737/1250000000000 : ℝ) := by
  have h := full_B_cross_power (k := 18) (s := 6) (r := 1) (v := 2) (t := 10) (D := 8)
    (a := (3/10 : ℝ)) (b := (1/10 : ℝ)) (c := (3/5 : ℝ))
    (by norm_num) half_9_04_φ3 (by norm_num [half_9_04_φ1, half_9_04_φ2, half_9_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_04_φ1, half_9_04_φ2, half_9_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_9_04_hF1 half_9_04_hF2 half_10_03
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_9_04_φ1, half_9_04_φ2, half_9_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_9_04_hx2 : SourcePowerBound (powerBoxCross 18 7 4 half_9_04_φ2) (84251098063947/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 7) (u := 5) (t := 8)
    (D := 4) (ψ := (34539498831/2500000000000 : ℝ)) half_9_04_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_04_φ1, half_9_04_φ2, half_9_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_04_φ1, half_9_04_φ2, half_9_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_04_φ1, half_9_04_φ2, half_9_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_6 SeedCompletionEven18SecondSeeds.degree18_half_8
    (by simpa only [half_9_04_φ3, show (2:ℝ)*4=8 by norm_num] using half_9_04_hx3)
  exact h.weaken (by norm_num [half_9_04_φ1, half_9_04_φ2, half_9_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_9_04_hx1 : SourcePowerBound (powerBoxCross 18 8 2 half_9_04_φ1) (11771279827961/1250000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 8) (u := 6) (t := 9)
    (D := 2) (ψ := (12357313013/400000000000 : ℝ)) half_9_04_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_04_φ1, half_9_04_φ2, half_9_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_04_φ1, half_9_04_φ2, half_9_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_04_φ1, half_9_04_φ2, half_9_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_7 half_9_03
    (by simpa only [half_9_04_φ2, show (2:ℝ)*2=4 by norm_num] using half_9_04_hx2)
  exact h.weaken (by norm_num [half_9_04_φ1, half_9_04_φ2, half_9_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_9_04 : AdmissibleExponent 18 18 (388034079463/39062500000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 7) (ψ := (43054047657/1250000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_8
    (by simpa only [half_9_04_φ1] using half_9_04_hx1)
  exact admissibleExponent_mono h (by norm_num [half_9_04_φ1, half_9_04_φ2, half_9_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_10_04_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (355332883593/10000000000000 : ℝ)

def half_10_04_φ2 : Fin 2 → ℝ := Fin.snoc half_10_04_φ1 (41210539127/1250000000000 : ℝ)

def half_10_04_φ3 : Fin 3 → ℝ := Fin.snoc half_10_04_φ2 (115844148159/5000000000000 : ℝ)

theorem half_10_04_hF2 : SourcePowerBound (paddedMoment 18 0 2 8 half_10_04_φ3) (63248019860723/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_10_04_φ3 (by norm_num [half_10_04_φ1, half_10_04_φ2, half_10_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_04_φ1, half_10_04_φ2, half_10_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_04_φ1, half_10_04_φ2, half_10_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_10_04_φ1, half_10_04_φ2, half_10_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_10_04_hx3 : SourcePowerBound (powerBoxCross 18 7 8 half_10_04_φ3) (86417375248567/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 7) (r := 2) (v := 9) (w := 10) (D := 8)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_10_04_φ3 (by norm_num [half_10_04_φ1, half_10_04_φ2, half_10_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_04_φ1, half_10_04_φ2, half_10_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_10_04_hF2 half_9_04 half_10_03
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_10_04_φ1, half_10_04_φ2, half_10_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_04_hx2 : SourcePowerBound (powerBoxCross 18 8 4 half_10_04_φ2) (95158009328967/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 8) (u := 6) (t := 9)
    (D := 4) (ψ := (115844148159/5000000000000 : ℝ)) half_10_04_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_04_φ1, half_10_04_φ2, half_10_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_04_φ1, half_10_04_φ2, half_10_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_04_φ1, half_10_04_φ2, half_10_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_7 half_9_04
    (by simpa only [half_10_04_φ3, show (2:ℝ)*4=8 by norm_num] using half_10_04_hx3)
  exact h.weaken (by norm_num [half_10_04_φ1, half_10_04_φ2, half_10_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_04_hx1 : SourcePowerBound (powerBoxCross 18 9 2 half_10_04_φ1) (106162296755399/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 9) (u := 7) (t := 10)
    (D := 2) (ψ := (41210539127/1250000000000 : ℝ)) half_10_04_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_04_φ1, half_10_04_φ2, half_10_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_04_φ1, half_10_04_φ2, half_10_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_04_φ1, half_10_04_φ2, half_10_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_8 half_10_03
    (by simpa only [half_10_04_φ2, show (2:ℝ)*2=4 by norm_num] using half_10_04_hx2)
  exact h.weaken (by norm_num [half_10_04_φ1, half_10_04_φ2, half_10_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_04 : AdmissibleExponent 18 20 (701268473603/62500000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 8) (ψ := (355332883593/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_9_04
    (by simpa only [half_10_04_φ1] using half_10_04_hx1)
  exact admissibleExponent_mono h (by norm_num [half_10_04_φ1, half_10_04_φ2, half_10_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_11_04_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (92273440437/2500000000000 : ℝ)

def half_11_04_φ2 : Fin 2 → ℝ := Fin.snoc half_11_04_φ1 (13925690321/400000000000 : ℝ)

def half_11_04_φ3 : Fin 3 → ℝ := Fin.snoc half_11_04_φ2 (302301996729/10000000000000 : ℝ)

theorem half_11_04_hF2 : SourcePowerBound (paddedMoment 18 0 2 8 half_11_04_φ3) (29001780579199/5000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_11_04_φ3 (by norm_num [half_11_04_φ1, half_11_04_φ2, half_11_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_04_φ1, half_11_04_φ2, half_11_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_04_φ1, half_11_04_φ2, half_11_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_11_04_φ1, half_11_04_φ2, half_11_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_11_04_hx3 : SourcePowerBound (powerBoxCross 18 8 8 half_11_04_φ3) (48037048347137/5000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 8) (r := 2) (v := 10) (w := 11) (D := 8)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_11_04_φ3 (by norm_num [half_11_04_φ1, half_11_04_φ2, half_11_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_04_φ1, half_11_04_φ2, half_11_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_11_04_hF2 half_10_04 half_11_03
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_11_04_φ1, half_11_04_φ2, half_11_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_04_hx2 : SourcePowerBound (powerBoxCross 18 9 4 half_11_04_φ2) (106285484972381/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 9) (u := 7) (t := 10)
    (D := 4) (ψ := (302301996729/10000000000000 : ℝ)) half_11_04_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_04_φ1, half_11_04_φ2, half_11_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_04_φ1, half_11_04_φ2, half_11_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_04_φ1, half_11_04_φ2, half_11_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_8 half_10_04
    (by simpa only [half_11_04_φ3, show (2:ℝ)*4=8 by norm_num] using half_11_04_hx3)
  exact h.weaken (by norm_num [half_11_04_φ1, half_11_04_φ2, half_11_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_04_hx1 : SourcePowerBound (powerBoxCross 18 10 2 half_11_04_φ1) (118430708435571/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 10) (u := 8) (t := 11)
    (D := 2) (ψ := (13925690321/400000000000 : ℝ)) half_11_04_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_04_φ1, half_11_04_φ2, half_11_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_04_φ1, half_11_04_φ2, half_11_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_04_φ1, half_11_04_φ2, half_11_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_04 half_11_03
    (by simpa only [half_11_04_φ2, show (2:ℝ)*2=4 by norm_num] using half_11_04_hx2)
  exact h.weaken (by norm_num [half_11_04_φ1, half_11_04_φ2, half_11_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_04 : AdmissibleExponent 18 22 (125443489908783/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 9) (ψ := (92273440437/2500000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_10_04
    (by simpa only [half_11_04_φ1] using half_11_04_hx1)
  exact admissibleExponent_mono h (by norm_num [half_11_04_φ1, half_11_04_φ2, half_11_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_12_04_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (381872134267/10000000000000 : ℝ)

def half_12_04_φ2 : Fin 2 → ℝ := Fin.snoc half_12_04_φ1 (180750039229/5000000000000 : ℝ)

def half_12_04_φ3 : Fin 3 → ℝ := Fin.snoc half_12_04_φ2 (330698787883/10000000000000 : ℝ)

def half_12_04_φ4 : Fin 4 → ℝ := Fin.snoc half_12_04_φ3 (218180444919/10000000000000 : ℝ)

theorem half_12_04_hF2 : SourcePowerBound (paddedMoment 18 0 2 16 half_12_04_φ4) (74095176278123/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_12_04_φ4 (by norm_num [half_12_04_φ1, half_12_04_φ2, half_12_04_φ3, half_12_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_04_φ1, half_12_04_φ2, half_12_04_φ3, half_12_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_04_φ1, half_12_04_φ2, half_12_04_φ3, half_12_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_12_04_φ1, half_12_04_φ2, half_12_04_φ3, half_12_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_12_04_hF1 : SourcePowerBound (paddedMoment 18 0 1 16 half_12_04_φ4) (28031725426041/10000000000000 : ℝ) := by
  have h := padded_second_power (k := 18) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_12_04_φ4 (by norm_num [half_12_04_φ1, half_12_04_φ2, half_12_04_φ3, half_12_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_04_φ1, half_12_04_φ2, half_12_04_φ3, half_12_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_04_φ1, half_12_04_φ2, half_12_04_φ3, half_12_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_12_04_φ1, half_12_04_φ2, half_12_04_φ3, half_12_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_12_04_hx4 : SourcePowerBound (powerBoxCross 18 8 16 half_12_04_φ4) (97556190704121/10000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 18) (s := 8) (r := 1) (v := 2) (t := 11) (D := 16)
    (a := (1/22 : ℝ)) (b := (5/22 : ℝ)) (c := (8/11 : ℝ))
    (by norm_num) half_12_04_φ4 (by norm_num [half_12_04_φ1, half_12_04_φ2, half_12_04_φ3, half_12_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_04_φ1, half_12_04_φ2, half_12_04_φ3, half_12_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_12_04_hF1 half_12_04_hF2 half_11_04
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_12_04_φ1, half_12_04_φ2, half_12_04_φ3, half_12_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_04_hx3 : SourcePowerBound (powerBoxCross 18 9 8 half_12_04_φ3) (106360626022927/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 9) (u := 7) (t := 10)
    (D := 8) (ψ := (218180444919/10000000000000 : ℝ)) half_12_04_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_04_φ1, half_12_04_φ2, half_12_04_φ3, half_12_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_04_φ1, half_12_04_φ2, half_12_04_φ3, half_12_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_04_φ1, half_12_04_φ2, half_12_04_φ3, half_12_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_8 half_10_04
    (by simpa only [half_12_04_φ4, show (2:ℝ)*8=16 by norm_num] using half_12_04_hx4)
  exact h.weaken (by norm_num [half_12_04_φ1, half_12_04_φ2, half_12_04_φ3, half_12_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_04_hx2 : SourcePowerBound (powerBoxCross 18 10 4 half_12_04_φ2) (117731773621427/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 10) (u := 8) (t := 11)
    (D := 4) (ψ := (330698787883/10000000000000 : ℝ)) half_12_04_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_04_φ1, half_12_04_φ2, half_12_04_φ3, half_12_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_04_φ1, half_12_04_φ2, half_12_04_φ3, half_12_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_04_φ1, half_12_04_φ2, half_12_04_φ3, half_12_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_04 half_11_04
    (by simpa only [half_12_04_φ3, show (2:ℝ)*4=8 by norm_num] using half_12_04_hx3)
  exact h.weaken (by norm_num [half_12_04_φ1, half_12_04_φ2, half_12_04_φ3, half_12_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_04_hx1 : SourcePowerBound (powerBoxCross 18 11 2 half_12_04_φ1) (131035024720923/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 11) (u := 9) (t := 12)
    (D := 2) (ψ := (180750039229/5000000000000 : ℝ)) half_12_04_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_04_φ1, half_12_04_φ2, half_12_04_φ3, half_12_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_04_φ1, half_12_04_φ2, half_12_04_φ3, half_12_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_04_φ1, half_12_04_φ2, half_12_04_φ3, half_12_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_04 half_12_03
    (by simpa only [half_12_04_φ2, show (2:ℝ)*2=4 by norm_num] using half_12_04_hx2)
  exact h.weaken (by norm_num [half_12_04_φ1, half_12_04_φ2, half_12_04_φ3, half_12_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_04 : AdmissibleExponent 18 24 (13905433954053/1000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 10) (ψ := (381872134267/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_11_04
    (by simpa only [half_12_04_φ1] using half_12_04_hx1)
  exact admissibleExponent_mono h (by norm_num [half_12_04_φ1, half_12_04_φ2, half_12_04_φ3, half_12_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_13_04_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (79209342299/2000000000000 : ℝ)

def half_13_04_φ2 : Fin 2 → ℝ := Fin.snoc half_13_04_φ1 (9331244003/250000000000 : ℝ)

def half_13_04_φ3 : Fin 3 → ℝ := Fin.snoc half_13_04_φ2 (352536253693/10000000000000 : ℝ)

def half_13_04_φ4 : Fin 4 → ℝ := Fin.snoc half_13_04_φ3 (292449434639/10000000000000 : ℝ)

theorem half_13_04_hF2 : SourcePowerBound (paddedMoment 18 0 2 16 half_13_04_φ4) (67871609842703/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_13_04_φ4 (by norm_num [half_13_04_φ1, half_13_04_φ2, half_13_04_φ3, half_13_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_04_φ1, half_13_04_φ2, half_13_04_φ3, half_13_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_04_φ1, half_13_04_φ2, half_13_04_φ3, half_13_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_13_04_φ1, half_13_04_φ2, half_13_04_φ3, half_13_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_13_04_hx4 : SourcePowerBound (powerBoxCross 18 9 16 half_13_04_φ4) (5325450087021/500000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 9) (r := 2) (v := 12) (w := 12) (D := 16)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_13_04_φ4 (by norm_num [half_13_04_φ1, half_13_04_φ2, half_13_04_φ3, half_13_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_04_φ1, half_13_04_φ2, half_13_04_φ3, half_13_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_13_04_hF2 half_12_04 half_12_04
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_13_04_φ1, half_13_04_φ2, half_13_04_φ3, half_13_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_04_hx3 : SourcePowerBound (powerBoxCross 18 10 8 half_13_04_φ3) (11689015724609/1000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 10) (u := 8) (t := 11)
    (D := 8) (ψ := (292449434639/10000000000000 : ℝ)) half_13_04_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_04_φ1, half_13_04_φ2, half_13_04_φ3, half_13_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_04_φ1, half_13_04_φ2, half_13_04_φ3, half_13_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_04_φ1, half_13_04_φ2, half_13_04_φ3, half_13_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_04 half_11_04
    (by simpa only [half_13_04_φ4, show (2:ℝ)*8=16 by norm_num] using half_13_04_hx4)
  exact h.weaken (by norm_num [half_13_04_φ1, half_13_04_φ2, half_13_04_φ3, half_13_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_04_hx2 : SourcePowerBound (powerBoxCross 18 11 4 half_13_04_φ2) (64716811078051/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 11) (u := 9) (t := 12)
    (D := 4) (ψ := (352536253693/10000000000000 : ℝ)) half_13_04_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_04_φ1, half_13_04_φ2, half_13_04_φ3, half_13_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_04_φ1, half_13_04_φ2, half_13_04_φ3, half_13_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_04_φ1, half_13_04_φ2, half_13_04_φ3, half_13_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_04 half_12_04
    (by simpa only [half_13_04_φ3, show (2:ℝ)*4=8 by norm_num] using half_13_04_hx3)
  exact h.weaken (by norm_num [half_13_04_φ1, half_13_04_φ2, half_13_04_φ3, half_13_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_04_hx1 : SourcePowerBound (powerBoxCross 18 12 2 half_13_04_φ1) (1151545478901/80000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 12) (u := 10) (t := 13)
    (D := 2) (ψ := (9331244003/250000000000 : ℝ)) half_13_04_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_04_φ1, half_13_04_φ2, half_13_04_φ3, half_13_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_04_φ1, half_13_04_φ2, half_13_04_φ3, half_13_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_04_φ1, half_13_04_φ2, half_13_04_φ3, half_13_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_04 half_13_03
    (by simpa only [half_13_04_φ2, show (2:ℝ)*2=4 by norm_num] using half_13_04_hx2)
  exact h.weaken (by norm_num [half_13_04_φ1, half_13_04_φ2, half_13_04_φ3, half_13_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_04 : AdmissibleExponent 18 26 (15305225922701/1000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 11) (ψ := (79209342299/2000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_12_04
    (by simpa only [half_13_04_φ1] using half_13_04_hx1)
  exact admissibleExponent_mono h (by norm_num [half_13_04_φ1, half_13_04_φ2, half_13_04_φ3, half_13_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_14_04_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (410653161959/10000000000000 : ℝ)

def half_14_04_φ2 : Fin 2 → ℝ := Fin.snoc half_14_04_φ1 (3075895947/80000000000 : ℝ)

def half_14_04_φ3 : Fin 3 → ℝ := Fin.snoc half_14_04_φ2 (36858796901/1000000000000 : ℝ)

def half_14_04_φ4 : Fin 4 → ℝ := Fin.snoc half_14_04_φ3 (16754243079/500000000000 : ℝ)

def half_14_04_φ5 : Fin 5 → ℝ := Fin.snoc half_14_04_φ4 (216313220463/10000000000000 : ℝ)

theorem half_14_04_hF2 : SourcePowerBound (paddedMoment 18 0 2 32 half_14_04_φ5) (82528563474263/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_14_04_φ5 (by norm_num [half_14_04_φ1, half_14_04_φ2, half_14_04_φ3, half_14_04_φ4, half_14_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_04_φ1, half_14_04_φ2, half_14_04_φ3, half_14_04_φ4, half_14_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_04_φ1, half_14_04_φ2, half_14_04_φ3, half_14_04_φ4, half_14_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_14_04_φ1, half_14_04_φ2, half_14_04_φ3, half_14_04_φ4, half_14_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_14_04_hx5 : SourcePowerBound (powerBoxCross 18 9 32 half_14_04_φ5) (107035714884629/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 9) (r := 2) (v := 12) (w := 12) (D := 32)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_14_04_φ5 (by norm_num [half_14_04_φ1, half_14_04_φ2, half_14_04_φ3, half_14_04_φ4, half_14_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_04_φ1, half_14_04_φ2, half_14_04_φ3, half_14_04_φ4, half_14_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_14_04_hF2 half_12_04 half_12_04
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_14_04_φ1, half_14_04_φ2, half_14_04_φ3, half_14_04_φ4, half_14_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_04_hx4 : SourcePowerBound (powerBoxCross 18 10 16 half_14_04_φ4) (7246096112909/625000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 10) (u := 8) (t := 11)
    (D := 16) (ψ := (216313220463/10000000000000 : ℝ)) half_14_04_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_04_φ1, half_14_04_φ2, half_14_04_φ3, half_14_04_φ4, half_14_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_04_φ1, half_14_04_φ2, half_14_04_φ3, half_14_04_φ4, half_14_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_04_φ1, half_14_04_φ2, half_14_04_φ3, half_14_04_φ4, half_14_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_04 half_11_04
    (by simpa only [half_14_04_φ5, show (2:ℝ)*16=32 by norm_num] using half_14_04_hx5)
  exact h.weaken (by norm_num [half_14_04_φ1, half_14_04_φ2, half_14_04_φ3, half_14_04_φ4, half_14_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_04_hx3 : SourcePowerBound (powerBoxCross 18 11 8 half_14_04_φ3) (63848241757427/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 11) (u := 9) (t := 12)
    (D := 8) (ψ := (16754243079/500000000000 : ℝ)) half_14_04_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_04_φ1, half_14_04_φ2, half_14_04_φ3, half_14_04_φ4, half_14_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_04_φ1, half_14_04_φ2, half_14_04_φ3, half_14_04_φ4, half_14_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_04_φ1, half_14_04_φ2, half_14_04_φ3, half_14_04_φ4, half_14_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_04 half_12_04
    (by simpa only [half_14_04_φ4, show (2:ℝ)*8=16 by norm_num] using half_14_04_hx4)
  exact h.weaken (by norm_num [half_14_04_φ1, half_14_04_φ2, half_14_04_φ3, half_14_04_φ4, half_14_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_04_hx2 : SourcePowerBound (powerBoxCross 18 12 4 half_14_04_φ2) (141400953866399/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 12) (u := 10) (t := 13)
    (D := 4) (ψ := (36858796901/1000000000000 : ℝ)) half_14_04_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_04_φ1, half_14_04_φ2, half_14_04_φ3, half_14_04_φ4, half_14_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_04_φ1, half_14_04_φ2, half_14_04_φ3, half_14_04_φ4, half_14_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_04_φ1, half_14_04_φ2, half_14_04_φ3, half_14_04_φ4, half_14_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_04 half_13_04
    (by simpa only [half_14_04_φ3, show (2:ℝ)*4=8 by norm_num] using half_14_04_hx3)
  exact h.weaken (by norm_num [half_14_04_φ1, half_14_04_φ2, half_14_04_φ3, half_14_04_φ4, half_14_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_04_hx1 : SourcePowerBound (powerBoxCross 18 13 2 half_14_04_φ1) (157177772969329/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 13) (u := 11) (t := 14)
    (D := 2) (ψ := (3075895947/80000000000 : ℝ)) half_14_04_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_04_φ1, half_14_04_φ2, half_14_04_φ3, half_14_04_φ4, half_14_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_04_φ1, half_14_04_φ2, half_14_04_φ3, half_14_04_φ4, half_14_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_04_φ1, half_14_04_φ2, half_14_04_φ3, half_14_04_φ4, half_14_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_04 half_14_03
    (by simpa only [half_14_04_φ2, show (2:ℝ)*2=4 by norm_num] using half_14_04_hx2)
  exact h.weaken (by norm_num [half_14_04_φ1, half_14_04_φ2, half_14_04_φ3, half_14_04_φ4, half_14_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_04 : AdmissibleExponent 18 28 (654078523509/39062500000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 12) (ψ := (410653161959/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_13_04
    (by simpa only [half_14_04_φ1] using half_14_04_hx1)
  exact admissibleExponent_mono h (by norm_num [half_14_04_φ1, half_14_04_φ2, half_14_04_φ3, half_14_04_φ4, half_14_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_15_04_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (26598940521/625000000000 : ℝ)

def half_15_04_φ2 : Fin 2 → ℝ := Fin.snoc half_15_04_φ1 (98728170523/2500000000000 : ℝ)

def half_15_04_φ3 : Fin 3 → ℝ := Fin.snoc half_15_04_φ2 (190956929477/5000000000000 : ℝ)

def half_15_04_φ4 : Fin 4 → ℝ := Fin.snoc half_15_04_φ3 (90114645171/2500000000000 : ℝ)

def half_15_04_φ5 : Fin 5 → ℝ := Fin.snoc half_15_04_φ4 (303434911669/10000000000000 : ℝ)

theorem half_15_04_hF2 : SourcePowerBound (paddedMoment 18 0 2 32 half_15_04_φ5) (14963708566303/2000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_15_04_φ5 (by norm_num [half_15_04_φ1, half_15_04_φ2, half_15_04_φ3, half_15_04_φ4, half_15_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_04_φ1, half_15_04_φ2, half_15_04_φ3, half_15_04_φ4, half_15_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_04_φ1, half_15_04_φ2, half_15_04_φ3, half_15_04_φ4, half_15_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_15_04_φ1, half_15_04_φ2, half_15_04_φ3, half_15_04_φ4, half_15_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_15_04_hx5 : SourcePowerBound (powerBoxCross 18 10 32 half_15_04_φ5) (114997159582489/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 10) (r := 2) (v := 13) (w := 14) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_15_04_φ5 (by norm_num [half_15_04_φ1, half_15_04_φ2, half_15_04_φ3, half_15_04_φ4, half_15_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_04_φ1, half_15_04_φ2, half_15_04_φ3, half_15_04_φ4, half_15_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_15_04_hF2 half_13_04 half_14_04
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_15_04_φ1, half_15_04_φ2, half_15_04_φ3, half_15_04_φ4, half_15_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_04_hx4 : SourcePowerBound (powerBoxCross 18 11 16 half_15_04_φ4) (31439455429483/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 11) (u := 9) (t := 12)
    (D := 16) (ψ := (303434911669/10000000000000 : ℝ)) half_15_04_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_04_φ1, half_15_04_φ2, half_15_04_φ3, half_15_04_φ4, half_15_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_04_φ1, half_15_04_φ2, half_15_04_φ3, half_15_04_φ4, half_15_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_04_φ1, half_15_04_φ2, half_15_04_φ3, half_15_04_φ4, half_15_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_04 half_12_04
    (by simpa only [half_15_04_φ5, show (2:ℝ)*16=32 by norm_num] using half_15_04_hx5)
  exact h.weaken (by norm_num [half_15_04_φ1, half_15_04_φ2, half_15_04_φ3, half_15_04_φ4, half_15_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_04_hx3 : SourcePowerBound (powerBoxCross 18 12 8 half_15_04_φ3) (2775355977027/200000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 12) (u := 10) (t := 13)
    (D := 8) (ψ := (90114645171/2500000000000 : ℝ)) half_15_04_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_04_φ1, half_15_04_φ2, half_15_04_φ3, half_15_04_φ4, half_15_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_04_φ1, half_15_04_φ2, half_15_04_φ3, half_15_04_φ4, half_15_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_04_φ1, half_15_04_φ2, half_15_04_φ3, half_15_04_φ4, half_15_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_04 half_13_04
    (by simpa only [half_15_04_φ4, show (2:ℝ)*8=16 by norm_num] using half_15_04_hx4)
  exact h.weaken (by norm_num [half_15_04_φ1, half_15_04_φ2, half_15_04_φ3, half_15_04_φ4, half_15_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_04_hx2 : SourcePowerBound (powerBoxCross 18 13 4 half_15_04_φ2) (9603399222787/625000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 13) (u := 11) (t := 14)
    (D := 4) (ψ := (190956929477/5000000000000 : ℝ)) half_15_04_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_04_φ1, half_15_04_φ2, half_15_04_φ3, half_15_04_φ4, half_15_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_04_φ1, half_15_04_φ2, half_15_04_φ3, half_15_04_φ4, half_15_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_04_φ1, half_15_04_φ2, half_15_04_φ3, half_15_04_φ4, half_15_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_04 half_14_04
    (by simpa only [half_15_04_φ3, show (2:ℝ)*4=8 by norm_num] using half_15_04_hx3)
  exact h.weaken (by norm_num [half_15_04_φ1, half_15_04_φ2, half_15_04_φ3, half_15_04_φ4, half_15_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_04_hx1 : SourcePowerBound (powerBoxCross 18 14 2 half_15_04_φ1) (170743547930377/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 14) (u := 12) (t := 15)
    (D := 2) (ψ := (98728170523/2500000000000 : ℝ)) half_15_04_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_04_φ1, half_15_04_φ2, half_15_04_φ3, half_15_04_φ4, half_15_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_04_φ1, half_15_04_φ2, half_15_04_φ3, half_15_04_φ4, half_15_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_04_φ1, half_15_04_φ2, half_15_04_φ3, half_15_04_φ4, half_15_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_13_04 half_15_03
    (by simpa only [half_15_04_φ2, show (2:ℝ)*2=4 by norm_num] using half_15_04_hx2)
  exact h.weaken (by norm_num [half_15_04_φ1, half_15_04_φ2, half_15_04_φ3, half_15_04_φ4, half_15_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_04 : AdmissibleExponent 18 30 (182234290235449/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 13) (ψ := (26598940521/625000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_14_04
    (by simpa only [half_15_04_φ1] using half_15_04_hx1)
  exact admissibleExponent_mono h (by norm_num [half_15_04_φ1, half_15_04_φ2, half_15_04_φ3, half_15_04_φ4, half_15_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_16_04_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (440219101341/10000000000000 : ℝ)

def half_16_04_φ2 : Fin 2 → ℝ := Fin.snoc half_16_04_φ1 (404648310661/10000000000000 : ℝ)

def half_16_04_φ3 : Fin 3 → ℝ := Fin.snoc half_16_04_φ2 (39296282787/1000000000000 : ℝ)

def half_16_04_φ4 : Fin 4 → ℝ := Fin.snoc half_16_04_φ3 (2353679491/62500000000 : ℝ)

def half_16_04_φ5 : Fin 5 → ℝ := Fin.snoc half_16_04_φ4 (170935514317/5000000000000 : ℝ)

def half_16_04_φ6 : Fin 6 → ℝ := Fin.snoc half_16_04_φ5 (45775709183/2000000000000 : ℝ)

theorem half_16_04_hF2 : SourcePowerBound (paddedMoment 18 0 2 64 half_16_04_φ6) (88556404817969/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 6) (r := 0) (D := 64)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_16_04_φ6 (by norm_num [half_16_04_φ1, half_16_04_φ2, half_16_04_φ3, half_16_04_φ4, half_16_04_φ5, half_16_04_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_04_φ1, half_16_04_φ2, half_16_04_φ3, half_16_04_φ4, half_16_04_φ5, half_16_04_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_04_φ1, half_16_04_φ2, half_16_04_φ3, half_16_04_φ4, half_16_04_φ5, half_16_04_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_16_04_φ1, half_16_04_φ2, half_16_04_φ3, half_16_04_φ4, half_16_04_φ5, half_16_04_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_16_04_hx6 : SourcePowerBound (powerBoxCross 18 10 64 half_16_04_φ6) (114656667715257/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 10) (r := 2) (v := 13) (w := 14) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_16_04_φ6 (by norm_num [half_16_04_φ1, half_16_04_φ2, half_16_04_φ3, half_16_04_φ4, half_16_04_φ5, half_16_04_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_04_φ1, half_16_04_φ2, half_16_04_φ3, half_16_04_φ4, half_16_04_φ5, half_16_04_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_16_04_hF2 half_13_04 half_14_04
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_16_04_φ1, half_16_04_φ2, half_16_04_φ3, half_16_04_φ4, half_16_04_φ5, half_16_04_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_04_hx5 : SourcePowerBound (powerBoxCross 18 11 32 half_16_04_φ5) (24759970863793/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 5) (s := 11) (u := 9) (t := 12)
    (D := 32) (ψ := (45775709183/2000000000000 : ℝ)) half_16_04_φ5
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_04_φ1, half_16_04_φ2, half_16_04_φ3, half_16_04_φ4, half_16_04_φ5, half_16_04_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_04_φ1, half_16_04_φ2, half_16_04_φ3, half_16_04_φ4, half_16_04_φ5, half_16_04_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_04_φ1, half_16_04_φ2, half_16_04_φ3, half_16_04_φ4, half_16_04_φ5, half_16_04_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_04 half_12_04
    (by simpa only [half_16_04_φ6, show (2:ℝ)*32=64 by norm_num] using half_16_04_hx6)
  exact h.weaken (by norm_num [half_16_04_φ1, half_16_04_φ2, half_16_04_φ3, half_16_04_φ4, half_16_04_φ5, half_16_04_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_04_hx4 : SourcePowerBound (powerBoxCross 18 12 16 half_16_04_φ4) (67969308990313/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 12) (u := 10) (t := 13)
    (D := 16) (ψ := (170935514317/5000000000000 : ℝ)) half_16_04_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_04_φ1, half_16_04_φ2, half_16_04_φ3, half_16_04_φ4, half_16_04_φ5, half_16_04_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_04_φ1, half_16_04_φ2, half_16_04_φ3, half_16_04_φ4, half_16_04_φ5, half_16_04_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_04_φ1, half_16_04_φ2, half_16_04_φ3, half_16_04_φ4, half_16_04_φ5, half_16_04_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_04 half_13_04
    (by simpa only [half_16_04_φ5, show (2:ℝ)*16=32 by norm_num] using half_16_04_hx5)
  exact h.weaken (by norm_num [half_16_04_φ1, half_16_04_φ2, half_16_04_φ3, half_16_04_φ4, half_16_04_φ5, half_16_04_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_04_hx3 : SourcePowerBound (powerBoxCross 18 13 8 half_16_04_φ3) (15013720457567/1000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 13) (u := 11) (t := 14)
    (D := 8) (ψ := (2353679491/62500000000 : ℝ)) half_16_04_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_04_φ1, half_16_04_φ2, half_16_04_φ3, half_16_04_φ4, half_16_04_φ5, half_16_04_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_04_φ1, half_16_04_φ2, half_16_04_φ3, half_16_04_φ4, half_16_04_φ5, half_16_04_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_04_φ1, half_16_04_φ2, half_16_04_φ3, half_16_04_φ4, half_16_04_φ5, half_16_04_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_04 half_14_04
    (by simpa only [half_16_04_φ4, show (2:ℝ)*8=16 by norm_num] using half_16_04_hx4)
  exact h.weaken (by norm_num [half_16_04_φ1, half_16_04_φ2, half_16_04_φ3, half_16_04_φ4, half_16_04_φ5, half_16_04_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_04_hx2 : SourcePowerBound (powerBoxCross 18 14 4 half_16_04_φ2) (10388638693341/625000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 14) (u := 12) (t := 15)
    (D := 4) (ψ := (39296282787/1000000000000 : ℝ)) half_16_04_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_04_φ1, half_16_04_φ2, half_16_04_φ3, half_16_04_φ4, half_16_04_φ5, half_16_04_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_04_φ1, half_16_04_φ2, half_16_04_φ3, half_16_04_φ4, half_16_04_φ5, half_16_04_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_04_φ1, half_16_04_φ2, half_16_04_φ3, half_16_04_φ4, half_16_04_φ5, half_16_04_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_13_04 half_15_04
    (by simpa only [half_16_04_φ3, show (2:ℝ)*4=8 by norm_num] using half_16_04_hx3)
  exact h.weaken (by norm_num [half_16_04_φ1, half_16_04_φ2, half_16_04_φ3, half_16_04_φ4, half_16_04_φ5, half_16_04_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_04_hx1 : SourcePowerBound (powerBoxCross 18 15 2 half_16_04_φ1) (184652207788703/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 15) (u := 13) (t := 16)
    (D := 2) (ψ := (404648310661/10000000000000 : ℝ)) half_16_04_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_04_φ1, half_16_04_φ2, half_16_04_φ3, half_16_04_φ4, half_16_04_φ5, half_16_04_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_04_φ1, half_16_04_φ2, half_16_04_φ3, half_16_04_φ4, half_16_04_φ5, half_16_04_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_04_φ1, half_16_04_φ2, half_16_04_φ3, half_16_04_φ4, half_16_04_φ5, half_16_04_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_14_04 half_16_03
    (by simpa only [half_16_04_φ2, show (2:ℝ)*2=4 by norm_num] using half_16_04_hx2)
  exact h.weaken (by norm_num [half_16_04_φ1, half_16_04_φ2, half_16_04_φ3, half_16_04_φ4, half_16_04_φ5, half_16_04_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_04 : AdmissibleExponent 18 32 (24677320215949/1250000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 14) (ψ := (440219101341/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_15_04
    (by simpa only [half_16_04_φ1] using half_16_04_hx1)
  exact admissibleExponent_mono h (by norm_num [half_16_04_φ1, half_16_04_φ2, half_16_04_φ3, half_16_04_φ4, half_16_04_φ5, half_16_04_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_17_04_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (14202194967/312500000000 : ℝ)

def half_17_04_φ2 : Fin 2 → ℝ := Fin.snoc half_17_04_φ1 (129355707/3125000000 : ℝ)

def half_17_04_φ3 : Fin 3 → ℝ := Fin.snoc half_17_04_φ2 (403525428651/10000000000000 : ℝ)

def half_17_04_φ4 : Fin 4 → ℝ := Fin.snoc half_17_04_φ3 (390773744419/10000000000000 : ℝ)

def half_17_04_φ5 : Fin 5 → ℝ := Fin.snoc half_17_04_φ4 (370439855879/10000000000000 : ℝ)

def half_17_04_φ6 : Fin 6 → ℝ := Fin.snoc half_17_04_φ5 (64034973511/2000000000000 : ℝ)

theorem half_17_04_hF2 : SourcePowerBound (paddedMoment 18 0 2 64 half_17_04_φ6) (9997569713719/1250000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 6) (r := 0) (D := 64)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_17_04_φ6 (by norm_num [half_17_04_φ1, half_17_04_φ2, half_17_04_φ3, half_17_04_φ4, half_17_04_φ5, half_17_04_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_04_φ1, half_17_04_φ2, half_17_04_φ3, half_17_04_φ4, half_17_04_φ5, half_17_04_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_04_φ1, half_17_04_φ2, half_17_04_φ3, half_17_04_φ4, half_17_04_φ5, half_17_04_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_17_04_φ1, half_17_04_φ2, half_17_04_φ3, half_17_04_φ4, half_17_04_φ5, half_17_04_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_17_04_hx6 : SourcePowerBound (powerBoxCross 18 11 64 half_17_04_φ6) (30419814828677/2500000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 11) (r := 2) (v := 14) (w := 15) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_17_04_φ6 (by norm_num [half_17_04_φ1, half_17_04_φ2, half_17_04_φ3, half_17_04_φ4, half_17_04_φ5, half_17_04_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_04_φ1, half_17_04_φ2, half_17_04_φ3, half_17_04_φ4, half_17_04_φ5, half_17_04_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_17_04_hF2 half_14_04 half_15_04
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_17_04_φ1, half_17_04_φ2, half_17_04_φ3, half_17_04_φ4, half_17_04_φ5, half_17_04_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_04_hx5 : SourcePowerBound (powerBoxCross 18 12 32 half_17_04_φ5) (132886950230039/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 5) (s := 12) (u := 10) (t := 13)
    (D := 32) (ψ := (64034973511/2000000000000 : ℝ)) half_17_04_φ5
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_04_φ1, half_17_04_φ2, half_17_04_φ3, half_17_04_φ4, half_17_04_φ5, half_17_04_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_04_φ1, half_17_04_φ2, half_17_04_φ3, half_17_04_φ4, half_17_04_φ5, half_17_04_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_04_φ1, half_17_04_φ2, half_17_04_φ3, half_17_04_φ4, half_17_04_φ5, half_17_04_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_04 half_13_04
    (by simpa only [half_17_04_φ6, show (2:ℝ)*32=64 by norm_num] using half_17_04_hx6)
  exact h.weaken (by norm_num [half_17_04_φ1, half_17_04_φ2, half_17_04_φ3, half_17_04_φ4, half_17_04_φ5, half_17_04_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_04_hx4 : SourcePowerBound (powerBoxCross 18 13 16 half_17_04_φ4) (73186019780601/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 13) (u := 11) (t := 14)
    (D := 16) (ψ := (370439855879/10000000000000 : ℝ)) half_17_04_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_04_φ1, half_17_04_φ2, half_17_04_φ3, half_17_04_φ4, half_17_04_φ5, half_17_04_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_04_φ1, half_17_04_φ2, half_17_04_φ3, half_17_04_φ4, half_17_04_φ5, half_17_04_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_04_φ1, half_17_04_φ2, half_17_04_φ3, half_17_04_φ4, half_17_04_φ5, half_17_04_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_04 half_14_04
    (by simpa only [half_17_04_φ5, show (2:ℝ)*16=32 by norm_num] using half_17_04_hx5)
  exact h.weaken (by norm_num [half_17_04_φ1, half_17_04_φ2, half_17_04_φ3, half_17_04_φ4, half_17_04_φ5, half_17_04_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_04_hx3 : SourcePowerBound (powerBoxCross 18 14 8 half_17_04_φ3) (32357379890131/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 14) (u := 12) (t := 15)
    (D := 8) (ψ := (390773744419/10000000000000 : ℝ)) half_17_04_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_04_φ1, half_17_04_φ2, half_17_04_φ3, half_17_04_φ4, half_17_04_φ5, half_17_04_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_04_φ1, half_17_04_φ2, half_17_04_φ3, half_17_04_φ4, half_17_04_φ5, half_17_04_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_04_φ1, half_17_04_φ2, half_17_04_φ3, half_17_04_φ4, half_17_04_φ5, half_17_04_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_13_04 half_15_04
    (by simpa only [half_17_04_φ4, show (2:ℝ)*8=16 by norm_num] using half_17_04_hx4)
  exact h.weaken (by norm_num [half_17_04_φ1, half_17_04_φ2, half_17_04_φ3, half_17_04_φ4, half_17_04_φ5, half_17_04_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_04_hx2 : SourcePowerBound (powerBoxCross 18 15 4 half_17_04_φ2) (179096853748121/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 15) (u := 13) (t := 16)
    (D := 4) (ψ := (403525428651/10000000000000 : ℝ)) half_17_04_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_04_φ1, half_17_04_φ2, half_17_04_φ3, half_17_04_φ4, half_17_04_φ5, half_17_04_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_04_φ1, half_17_04_φ2, half_17_04_φ3, half_17_04_φ4, half_17_04_φ5, half_17_04_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_04_φ1, half_17_04_φ2, half_17_04_φ3, half_17_04_φ4, half_17_04_φ5, half_17_04_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_14_04 half_16_04
    (by simpa only [half_17_04_φ3, show (2:ℝ)*4=8 by norm_num] using half_17_04_hx3)
  exact h.weaken (by norm_num [half_17_04_φ1, half_17_04_φ2, half_17_04_φ3, half_17_04_φ4, half_17_04_φ5, half_17_04_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_04_hx1 : SourcePowerBound (powerBoxCross 18 16 2 half_17_04_φ1) (49725236468631/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 16) (u := 14) (t := 17)
    (D := 2) (ψ := (129355707/3125000000 : ℝ)) half_17_04_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_04_φ1, half_17_04_φ2, half_17_04_φ3, half_17_04_φ4, half_17_04_φ5, half_17_04_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_04_φ1, half_17_04_φ2, half_17_04_φ3, half_17_04_φ4, half_17_04_φ5, half_17_04_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_04_φ1, half_17_04_φ2, half_17_04_φ3, half_17_04_φ4, half_17_04_φ5, half_17_04_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_15_04 half_17_03
    (by simpa only [half_17_04_φ2, show (2:ℝ)*2=4 by norm_num] using half_17_04_hx2)
  exact h.weaken (by norm_num [half_17_04_φ1, half_17_04_φ2, half_17_04_φ3, half_17_04_φ4, half_17_04_φ5, half_17_04_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_04 : AdmissibleExponent 18 34 (53247380820447/2500000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 15) (ψ := (14202194967/312500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_16_04
    (by simpa only [half_17_04_φ1] using half_17_04_hx1)
  exact admissibleExponent_mono h (by norm_num [half_17_04_φ1, half_17_04_φ2, half_17_04_φ3, half_17_04_φ4, half_17_04_φ5, half_17_04_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])


end Waring.SeedCompletionHigher18SimpleSeeds
