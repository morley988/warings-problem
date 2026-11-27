import Waring.SeedCompletionHigher18SimpleSeedsC09

noncomputable section
set_option maxHeartbeats 2000000
namespace Waring.SeedCompletionHigher18SimpleSeeds
open SmoothMoments FirstStageTransport SeedCompletionNaturalBox
open SeedCompletionSourceBounds SeedCompletionPaddedSource SeedCompletionGeneralTerminal
open PolicyCompletionMajorPowerRanges

def half_9_10_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (6876779383/200000000000 : ℝ)

def half_9_10_φ2 : Fin 2 → ℝ := Fin.snoc half_9_10_φ1 (154172656319/5000000000000 : ℝ)

def half_9_10_φ3 : Fin 3 → ℝ := Fin.snoc half_9_10_φ2 (134446977647/10000000000000 : ℝ)

theorem half_9_10_hF2 : SourcePowerBound (paddedMoment 18 0 2 8 half_9_10_φ3) (13976361153763/2000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_10_φ3 (by norm_num [half_9_10_φ1, half_9_10_φ2, half_9_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_10_φ1, half_9_10_φ2, half_9_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_10_φ1, half_9_10_φ2, half_9_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_10_φ1, half_9_10_φ2, half_9_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_9_10_hF1 : SourcePowerBound (paddedMoment 18 0 1 8 half_9_10_φ3) (5325453717921/2000000000000 : ℝ) := by
  have h := padded_second_power (k := 18) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_10_φ3 (by norm_num [half_9_10_φ1, half_9_10_φ2, half_9_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_10_φ1, half_9_10_φ2, half_9_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_10_φ1, half_9_10_φ2, half_9_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_10_φ1, half_9_10_φ2, half_9_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_9_10_hx3 : SourcePowerBound (powerBoxCross 18 6 8 half_9_10_φ3) (19248256068171/2500000000000 : ℝ) := by
  have h := full_B_cross_power (k := 18) (s := 6) (r := 1) (v := 2) (t := 10) (D := 8)
    (a := (3/10 : ℝ)) (b := (1/10 : ℝ)) (c := (3/5 : ℝ))
    (by norm_num) half_9_10_φ3 (by norm_num [half_9_10_φ1, half_9_10_φ2, half_9_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_10_φ1, half_9_10_φ2, half_9_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_9_10_hF1 half_9_10_hF2 half_10_09
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_9_10_φ1, half_9_10_φ2, half_9_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_9_10_hx2 : SourcePowerBound (powerBoxCross 18 7 4 half_9_10_φ2) (84269417305057/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 7) (u := 5) (t := 8)
    (D := 4) (ψ := (134446977647/10000000000000 : ℝ)) half_9_10_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_10_φ1, half_9_10_φ2, half_9_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_10_φ1, half_9_10_φ2, half_9_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_10_φ1, half_9_10_φ2, half_9_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_6 SeedCompletionEven18SecondSeeds.degree18_half_8
    (by simpa only [half_9_10_φ3, show (2:ℝ)*4=8 by norm_num] using half_9_10_hx3)
  exact h.weaken (by norm_num [half_9_10_φ1, half_9_10_φ2, half_9_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_9_10_hx1 : SourcePowerBound (powerBoxCross 18 8 2 half_9_10_φ1) (94174796979987/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 8) (u := 6) (t := 9)
    (D := 2) (ψ := (154172656319/5000000000000 : ℝ)) half_9_10_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_10_φ1, half_9_10_φ2, half_9_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_10_φ1, half_9_10_φ2, half_9_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_10_φ1, half_9_10_φ2, half_9_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_7 half_9_09
    (by simpa only [half_9_10_φ2, show (2:ℝ)*2=4 by norm_num] using half_9_10_hx2)
  exact h.weaken (by norm_num [half_9_10_φ1, half_9_10_φ2, half_9_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_9_10 : AdmissibleExponent 18 18 (99332381517237/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 7) (ψ := (6876779383/200000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_8
    (by simpa only [half_9_10_φ1] using half_9_10_hx1)
  exact admissibleExponent_mono h (by norm_num [half_9_10_φ1, half_9_10_φ2, half_9_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_10_10_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (353749323423/10000000000000 : ℝ)

def half_10_10_φ2 : Fin 2 → ℝ := Fin.snoc half_10_10_φ1 (329256684193/10000000000000 : ℝ)

def half_10_10_φ3 : Fin 3 → ℝ := Fin.snoc half_10_10_φ2 (229939287721/10000000000000 : ℝ)

theorem half_10_10_hF2 : SourcePowerBound (paddedMoment 18 0 2 8 half_10_10_φ3) (63439789937813/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_10_10_φ3 (by norm_num [half_10_10_φ1, half_10_10_φ2, half_10_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_10_φ1, half_10_10_φ2, half_10_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_10_φ1, half_10_10_φ2, half_10_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_10_10_φ1, half_10_10_φ2, half_10_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_10_10_hx3 : SourcePowerBound (powerBoxCross 18 7 8 half_10_10_φ3) (43238948170007/5000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 7) (r := 2) (v := 9) (w := 10) (D := 8)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_10_10_φ3 (by norm_num [half_10_10_φ1, half_10_10_φ2, half_10_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_10_φ1, half_10_10_φ2, half_10_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_10_10_hF2 half_9_10 half_10_09
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_10_10_φ1, half_10_10_φ2, half_10_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_10_hx2 : SourcePowerBound (powerBoxCross 18 8 4 half_10_10_φ2) (95201962567723/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 8) (u := 6) (t := 9)
    (D := 4) (ψ := (229939287721/10000000000000 : ℝ)) half_10_10_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_10_φ1, half_10_10_φ2, half_10_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_10_φ1, half_10_10_φ2, half_10_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_10_φ1, half_10_10_φ2, half_10_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_7 half_9_10
    (by simpa only [half_10_10_φ3, show (2:ℝ)*4=8 by norm_num] using half_10_10_hx3)
  exact h.weaken (by norm_num [half_10_10_φ1, half_10_10_φ2, half_10_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_10_hx1 : SourcePowerBound (powerBoxCross 18 9 2 half_10_10_φ1) (53086127282549/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 9) (u := 7) (t := 10)
    (D := 2) (ψ := (329256684193/10000000000000 : ℝ)) half_10_10_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_10_φ1, half_10_10_φ2, half_10_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_10_φ1, half_10_10_φ2, half_10_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_10_φ1, half_10_10_φ2, half_10_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_8 half_10_09
    (by simpa only [half_10_10_φ2, show (2:ℝ)*2=4 by norm_num] using half_10_10_hx2)
  exact h.weaken (by norm_num [half_10_10_φ1, half_10_10_φ2, half_10_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_10 : AdmissibleExponent 18 20 (112185993063289/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 8) (ψ := (353749323423/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_9_10
    (by simpa only [half_10_10_φ1] using half_10_10_hx1)
  exact admissibleExponent_mono h (by norm_num [half_10_10_φ1, half_10_10_φ2, half_10_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_11_10_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (364751003173/10000000000000 : ℝ)

def half_11_10_φ2 : Fin 2 → ℝ := Fin.snoc half_11_10_φ1 (173197925929/5000000000000 : ℝ)

def half_11_10_φ3 : Fin 3 → ℝ := Fin.snoc half_11_10_φ2 (147366523063/5000000000000 : ℝ)

theorem half_11_10_hF2 : SourcePowerBound (paddedMoment 18 0 2 8 half_11_10_φ3) (58700125040993/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_11_10_φ3 (by norm_num [half_11_10_φ1, half_11_10_φ2, half_11_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_10_φ1, half_11_10_φ2, half_11_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_10_φ1, half_11_10_φ2, half_11_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_11_10_φ1, half_11_10_φ2, half_11_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_11_10_hx3 : SourcePowerBound (powerBoxCross 18 8 8 half_11_10_φ3) (48144308940741/5000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 8) (r := 2) (v := 10) (w := 11) (D := 8)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_11_10_φ3 (by norm_num [half_11_10_φ1, half_11_10_φ2, half_11_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_10_φ1, half_11_10_φ2, half_11_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_11_10_hF2 half_10_10 half_11_09
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_11_10_φ1, half_11_10_φ2, half_11_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_10_hx2 : SourcePowerBound (powerBoxCross 18 9 4 half_11_10_φ2) (106414019243293/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 9) (u := 7) (t := 10)
    (D := 4) (ψ := (147366523063/5000000000000 : ℝ)) half_11_10_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_10_φ1, half_11_10_φ2, half_11_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_10_φ1, half_11_10_φ2, half_11_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_10_φ1, half_11_10_φ2, half_11_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_8 half_10_10
    (by simpa only [half_11_10_φ3, show (2:ℝ)*4=8 by norm_num] using half_11_10_hx3)
  exact h.weaken (by norm_num [half_11_10_φ1, half_11_10_φ2, half_11_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_10_hx1 : SourcePowerBound (powerBoxCross 18 10 2 half_11_10_φ1) (3701835897353/312500000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 10) (u := 8) (t := 11)
    (D := 2) (ψ := (173197925929/5000000000000 : ℝ)) half_11_10_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_10_φ1, half_11_10_φ2, half_11_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_10_φ1, half_11_10_φ2, half_11_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_10_φ1, half_11_10_φ2, half_11_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_10 half_11_09
    (by simpa only [half_11_10_φ2, show (2:ℝ)*2=4 by norm_num] using half_11_10_hx2)
  exact h.weaken (by norm_num [half_11_10_φ1, half_11_10_φ2, half_11_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_10 : AdmissibleExponent 18 22 (125389017775583/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 9) (ψ := (364751003173/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_10_10
    (by simpa only [half_11_10_φ1] using half_11_10_hx1)
  exact admissibleExponent_mono h (by norm_num [half_11_10_φ1, half_11_10_φ2, half_11_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_12_10_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (187475205179/5000000000000 : ℝ)

def half_12_10_φ2 : Fin 2 → ℝ := Fin.snoc half_12_10_φ1 (7211752349/200000000000 : ℝ)

def half_12_10_φ3 : Fin 3 → ℝ := Fin.snoc half_12_10_φ2 (82357759503/2500000000000 : ℝ)

def half_12_10_φ4 : Fin 4 → ℝ := Fin.snoc half_12_10_φ3 (212911815457/10000000000000 : ℝ)

theorem half_12_10_hF2 : SourcePowerBound (paddedMoment 18 0 2 16 half_12_10_φ4) (74828075054873/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_12_10_φ4 (by norm_num [half_12_10_φ1, half_12_10_φ2, half_12_10_φ3, half_12_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_10_φ1, half_12_10_φ2, half_12_10_φ3, half_12_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_10_φ1, half_12_10_φ2, half_12_10_φ3, half_12_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_12_10_φ1, half_12_10_φ2, half_12_10_φ3, half_12_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_12_10_hF1 : SourcePowerBound (paddedMoment 18 0 1 16 half_12_10_φ4) (28276025018291/10000000000000 : ℝ) := by
  have h := padded_second_power (k := 18) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_12_10_φ4 (by norm_num [half_12_10_φ1, half_12_10_φ2, half_12_10_φ3, half_12_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_10_φ1, half_12_10_φ2, half_12_10_φ3, half_12_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_10_φ1, half_12_10_φ2, half_12_10_φ3, half_12_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_12_10_φ1, half_12_10_φ2, half_12_10_φ3, half_12_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_12_10_hx4 : SourcePowerBound (powerBoxCross 18 8 16 half_12_10_φ4) (97830414501907/10000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 18) (s := 8) (r := 1) (v := 2) (t := 11) (D := 16)
    (a := (1/22 : ℝ)) (b := (5/22 : ℝ)) (c := (8/11 : ℝ))
    (by norm_num) half_12_10_φ4 (by norm_num [half_12_10_φ1, half_12_10_φ2, half_12_10_φ3, half_12_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_10_φ1, half_12_10_φ2, half_12_10_φ3, half_12_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_12_10_hF1 half_12_10_hF2 half_11_10
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_12_10_φ1, half_12_10_φ2, half_12_10_φ3, half_12_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_10_hx3 : SourcePowerBound (powerBoxCross 18 9 8 half_12_10_φ3) (106579074727521/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 9) (u := 7) (t := 10)
    (D := 8) (ψ := (212911815457/10000000000000 : ℝ)) half_12_10_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_10_φ1, half_12_10_φ2, half_12_10_φ3, half_12_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_10_φ1, half_12_10_φ2, half_12_10_φ3, half_12_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_10_φ1, half_12_10_φ2, half_12_10_φ3, half_12_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_8 half_10_10
    (by simpa only [half_12_10_φ4, show (2:ℝ)*8=16 by norm_num] using half_12_10_hx4)
  exact h.weaken (by norm_num [half_12_10_φ1, half_12_10_φ2, half_12_10_φ3, half_12_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_10_hx2 : SourcePowerBound (powerBoxCross 18 10 4 half_12_10_φ2) (23584143459223/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 10) (u := 8) (t := 11)
    (D := 4) (ψ := (82357759503/2500000000000 : ℝ)) half_12_10_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_10_φ1, half_12_10_φ2, half_12_10_φ3, half_12_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_10_φ1, half_12_10_φ2, half_12_10_φ3, half_12_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_10_φ1, half_12_10_φ2, half_12_10_φ3, half_12_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_10 half_11_10
    (by simpa only [half_12_10_φ3, show (2:ℝ)*4=8 by norm_num] using half_12_10_hx3)
  exact h.weaken (by norm_num [half_12_10_φ1, half_12_10_φ2, half_12_10_φ3, half_12_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_10_hx1 : SourcePowerBound (powerBoxCross 18 11 2 half_12_10_φ1) (131062501819023/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 11) (u := 9) (t := 12)
    (D := 2) (ψ := (7211752349/200000000000 : ℝ)) half_12_10_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_10_φ1, half_12_10_φ2, half_12_10_φ3, half_12_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_10_φ1, half_12_10_φ2, half_12_10_φ3, half_12_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_10_φ1, half_12_10_φ2, half_12_10_φ3, half_12_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_10 half_12_09
    (by simpa only [half_12_10_φ2, show (2:ℝ)*2=4 by norm_num] using half_12_10_hx2)
  exact h.weaken (by norm_num [half_12_10_φ1, half_12_10_φ2, half_12_10_φ3, half_12_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_10 : AdmissibleExponent 18 24 (138936460436541/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 10) (ψ := (187475205179/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_11_10
    (by simpa only [half_12_10_φ1] using half_12_10_hx1)
  exact admissibleExponent_mono h (by norm_num [half_12_10_φ1, half_12_10_φ2, half_12_10_φ3, half_12_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_13_10_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (192314889143/5000000000000 : ℝ)

def half_13_10_φ2 : Fin 2 → ℝ := Fin.snoc half_13_10_φ1 (185985295727/5000000000000 : ℝ)

def half_13_10_φ3 : Fin 3 → ℝ := Fin.snoc half_13_10_φ2 (349896574091/10000000000000 : ℝ)

def half_13_10_φ4 : Fin 4 → ℝ := Fin.snoc half_13_10_φ3 (11333052861/400000000000 : ℝ)

theorem half_13_10_hF2 : SourcePowerBound (paddedMoment 18 0 2 16 half_13_10_φ4) (17279753366711/2500000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_13_10_φ4 (by norm_num [half_13_10_φ1, half_13_10_φ2, half_13_10_φ3, half_13_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_10_φ1, half_13_10_φ2, half_13_10_φ3, half_13_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_10_φ1, half_13_10_φ2, half_13_10_φ3, half_13_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_13_10_φ1, half_13_10_φ2, half_13_10_φ3, half_13_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_13_10_hx4 : SourcePowerBound (powerBoxCross 18 9 16 half_13_10_φ4) (3343744197189/312500000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 9) (r := 2) (v := 12) (w := 12) (D := 16)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_13_10_φ4 (by norm_num [half_13_10_φ1, half_13_10_φ2, half_13_10_φ3, half_13_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_10_φ1, half_13_10_φ2, half_13_10_φ3, half_13_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_13_10_hF2 half_12_10 half_12_10
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_13_10_φ1, half_13_10_φ2, half_13_10_φ3, half_13_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_10_hx3 : SourcePowerBound (powerBoxCross 18 10 8 half_13_10_φ3) (58630168752641/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 10) (u := 8) (t := 11)
    (D := 8) (ψ := (11333052861/400000000000 : ℝ)) half_13_10_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_10_φ1, half_13_10_φ2, half_13_10_φ3, half_13_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_10_φ1, half_13_10_φ2, half_13_10_φ3, half_13_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_10_φ1, half_13_10_φ2, half_13_10_φ3, half_13_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_10 half_11_10
    (by simpa only [half_13_10_φ4, show (2:ℝ)*8=16 by norm_num] using half_13_10_hx4)
  exact h.weaken (by norm_num [half_13_10_φ1, half_13_10_φ2, half_13_10_φ3, half_13_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_10_hx2 : SourcePowerBound (powerBoxCross 18 11 4 half_13_10_φ2) (64867672207577/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 11) (u := 9) (t := 12)
    (D := 4) (ψ := (349896574091/10000000000000 : ℝ)) half_13_10_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_10_φ1, half_13_10_φ2, half_13_10_φ3, half_13_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_10_φ1, half_13_10_φ2, half_13_10_φ3, half_13_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_10_φ1, half_13_10_φ2, half_13_10_φ3, half_13_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_10 half_12_10
    (by simpa only [half_13_10_φ3, show (2:ℝ)*4=8 by norm_num] using half_13_10_hx3)
  exact h.weaken (by norm_num [half_13_10_φ1, half_13_10_φ2, half_13_10_φ3, half_13_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_10_hx1 : SourcePowerBound (powerBoxCross 18 12 2 half_13_10_φ1) (35994295054373/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 12) (u := 10) (t := 13)
    (D := 2) (ψ := (185985295727/5000000000000 : ℝ)) half_13_10_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_10_φ1, half_13_10_φ2, half_13_10_φ3, half_13_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_10_φ1, half_13_10_φ2, half_13_10_φ3, half_13_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_10_φ1, half_13_10_φ2, half_13_10_φ3, half_13_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_10 half_13_09
    (by simpa only [half_13_10_φ2, show (2:ℝ)*2=4 by norm_num] using half_13_10_hx2)
  exact h.weaken (by norm_num [half_13_10_φ1, half_13_10_φ2, half_13_10_φ3, half_13_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_10 : AdmissibleExponent 18 26 (15282366511807/1000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 11) (ψ := (192314889143/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_12_10
    (by simpa only [half_13_10_φ1] using half_13_10_hx1)
  exact admissibleExponent_mono h (by norm_num [half_13_10_φ1, half_13_10_φ2, half_13_10_φ3, half_13_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_14_10_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (394424087821/10000000000000 : ℝ)

def half_14_10_φ2 : Fin 2 → ℝ := Fin.snoc half_14_10_φ1 (383001790581/10000000000000 : ℝ)

def half_14_10_φ3 : Fin 3 → ℝ := Fin.snoc half_14_10_φ2 (183631769663/5000000000000 : ℝ)

def half_14_10_φ4 : Fin 4 → ℝ := Fin.snoc half_14_10_φ3 (332121802313/10000000000000 : ℝ)

def half_14_10_φ5 : Fin 5 → ℝ := Fin.snoc half_14_10_φ4 (25700731543/1250000000000 : ℝ)

theorem half_14_10_hF2 : SourcePowerBound (paddedMoment 18 0 2 32 half_14_10_φ5) (16839345861673/2000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_14_10_φ5 (by norm_num [half_14_10_φ1, half_14_10_φ2, half_14_10_φ3, half_14_10_φ4, half_14_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_10_φ1, half_14_10_φ2, half_14_10_φ3, half_14_10_φ4, half_14_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_10_φ1, half_14_10_φ2, half_14_10_φ3, half_14_10_φ4, half_14_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_14_10_φ1, half_14_10_φ2, half_14_10_φ3, half_14_10_φ4, half_14_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_14_10_hx5 : SourcePowerBound (powerBoxCross 18 9 32 half_14_10_φ5) (107720347178359/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 9) (r := 2) (v := 12) (w := 12) (D := 32)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_14_10_φ5 (by norm_num [half_14_10_φ1, half_14_10_φ2, half_14_10_φ3, half_14_10_φ4, half_14_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_10_φ1, half_14_10_φ2, half_14_10_φ3, half_14_10_φ4, half_14_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_14_10_hF2 half_12_10 half_12_10
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_14_10_φ1, half_14_10_φ2, half_14_10_φ3, half_14_10_φ4, half_14_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_10_hx4 : SourcePowerBound (powerBoxCross 18 10 16 half_14_10_φ4) (58245320717751/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 10) (u := 8) (t := 11)
    (D := 16) (ψ := (25700731543/1250000000000 : ℝ)) half_14_10_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_10_φ1, half_14_10_φ2, half_14_10_φ3, half_14_10_φ4, half_14_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_10_φ1, half_14_10_φ2, half_14_10_φ3, half_14_10_φ4, half_14_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_10_φ1, half_14_10_φ2, half_14_10_φ3, half_14_10_φ4, half_14_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_10 half_11_10
    (by simpa only [half_14_10_φ5, show (2:ℝ)*16=32 by norm_num] using half_14_10_hx5)
  exact h.weaken (by norm_num [half_14_10_φ1, half_14_10_φ2, half_14_10_φ3, half_14_10_φ4, half_14_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_10_hx3 : SourcePowerBound (powerBoxCross 18 11 8 half_14_10_φ3) (128186893207393/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 11) (u := 9) (t := 12)
    (D := 8) (ψ := (332121802313/10000000000000 : ℝ)) half_14_10_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_10_φ1, half_14_10_φ2, half_14_10_φ3, half_14_10_φ4, half_14_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_10_φ1, half_14_10_φ2, half_14_10_φ3, half_14_10_φ4, half_14_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_10_φ1, half_14_10_φ2, half_14_10_φ3, half_14_10_φ4, half_14_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_10 half_12_10
    (by simpa only [half_14_10_φ4, show (2:ℝ)*8=16 by norm_num] using half_14_10_hx4)
  exact h.weaken (by norm_num [half_14_10_φ1, half_14_10_φ2, half_14_10_φ3, half_14_10_φ4, half_14_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_10_hx2 : SourcePowerBound (powerBoxCross 18 12 4 half_14_10_φ2) (141812972754487/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 12) (u := 10) (t := 13)
    (D := 4) (ψ := (183631769663/5000000000000 : ℝ)) half_14_10_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_10_φ1, half_14_10_φ2, half_14_10_φ3, half_14_10_φ4, half_14_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_10_φ1, half_14_10_φ2, half_14_10_φ3, half_14_10_φ4, half_14_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_10_φ1, half_14_10_φ2, half_14_10_φ3, half_14_10_φ4, half_14_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_10 half_13_10
    (by simpa only [half_14_10_φ3, show (2:ℝ)*4=8 by norm_num] using half_14_10_hx3)
  exact h.weaken (by norm_num [half_14_10_φ1, half_14_10_φ2, half_14_10_φ3, half_14_10_φ4, half_14_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_10_hx1 : SourcePowerBound (powerBoxCross 18 13 2 half_14_10_φ1) (78595177867373/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 13) (u := 11) (t := 14)
    (D := 2) (ψ := (383001790581/10000000000000 : ℝ)) half_14_10_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_10_φ1, half_14_10_φ2, half_14_10_φ3, half_14_10_φ4, half_14_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_10_φ1, half_14_10_φ2, half_14_10_φ3, half_14_10_φ4, half_14_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_10_φ1, half_14_10_φ2, half_14_10_φ3, half_14_10_φ4, half_14_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_10 half_14_09
    (by simpa only [half_14_10_φ2, show (2:ℝ)*2=4 by norm_num] using half_14_10_hx2)
  exact h.weaken (by norm_num [half_14_10_φ1, half_14_10_φ2, half_14_10_φ3, half_14_10_φ4, half_14_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_10 : AdmissibleExponent 18 28 (167050957930271/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 12) (ψ := (394424087821/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_13_10
    (by simpa only [half_14_10_φ1] using half_14_10_hx1)
  exact admissibleExponent_mono h (by norm_num [half_14_10_φ1, half_14_10_φ2, half_14_10_φ3, half_14_10_φ4, half_14_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_15_10_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (40378017237/1000000000000 : ℝ)

def half_15_10_φ2 : Fin 2 → ℝ := Fin.snoc half_15_10_φ1 (3930003497/100000000000 : ℝ)

def half_15_10_φ3 : Fin 3 → ℝ := Fin.snoc half_15_10_φ2 (379466426263/10000000000000 : ℝ)

def half_15_10_φ4 : Fin 4 → ℝ := Fin.snoc half_15_10_φ3 (4440543859/125000000000 : ℝ)

def half_15_10_φ5 : Fin 5 → ℝ := Fin.snoc half_15_10_φ4 (71090471001/2500000000000 : ℝ)

theorem half_15_10_hF2 : SourcePowerBound (paddedMoment 18 0 2 32 half_15_10_φ5) (77391530606093/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_15_10_φ5 (by norm_num [half_15_10_φ1, half_15_10_φ2, half_15_10_φ3, half_15_10_φ4, half_15_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_10_φ1, half_15_10_φ2, half_15_10_φ3, half_15_10_φ4, half_15_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_10_φ1, half_15_10_φ2, half_15_10_φ3, half_15_10_φ4, half_15_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_15_10_φ1, half_15_10_φ2, half_15_10_φ3, half_15_10_φ4, half_15_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_15_10_hx5 : SourcePowerBound (powerBoxCross 18 10 32 half_15_10_φ5) (116063697363611/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 10) (r := 2) (v := 13) (w := 14) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_15_10_φ5 (by norm_num [half_15_10_φ1, half_15_10_φ2, half_15_10_φ3, half_15_10_φ4, half_15_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_10_φ1, half_15_10_φ2, half_15_10_φ3, half_15_10_φ4, half_15_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_15_10_hF2 half_13_10 half_14_10
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_15_10_φ1, half_15_10_φ2, half_15_10_φ3, half_15_10_φ4, half_15_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_10_hx4 : SourcePowerBound (powerBoxCross 18 11 16 half_15_10_φ4) (126544854748401/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 11) (u := 9) (t := 12)
    (D := 16) (ψ := (71090471001/2500000000000 : ℝ)) half_15_10_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_10_φ1, half_15_10_φ2, half_15_10_φ3, half_15_10_φ4, half_15_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_10_φ1, half_15_10_φ2, half_15_10_φ3, half_15_10_φ4, half_15_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_10_φ1, half_15_10_φ2, half_15_10_φ3, half_15_10_φ4, half_15_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_10 half_12_10
    (by simpa only [half_15_10_φ5, show (2:ℝ)*16=32 by norm_num] using half_15_10_hx5)
  exact h.weaken (by norm_num [half_15_10_φ1, half_15_10_φ2, half_15_10_φ3, half_15_10_φ4, half_15_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_10_hx3 : SourcePowerBound (powerBoxCross 18 12 8 half_15_10_φ3) (34857074806889/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 12) (u := 10) (t := 13)
    (D := 8) (ψ := (4440543859/125000000000 : ℝ)) half_15_10_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_10_φ1, half_15_10_φ2, half_15_10_φ3, half_15_10_φ4, half_15_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_10_φ1, half_15_10_φ2, half_15_10_φ3, half_15_10_φ4, half_15_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_10_φ1, half_15_10_φ2, half_15_10_φ3, half_15_10_φ4, half_15_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_10 half_13_10
    (by simpa only [half_15_10_φ4, show (2:ℝ)*8=16 by norm_num] using half_15_10_hx4)
  exact h.weaken (by norm_num [half_15_10_φ1, half_15_10_φ2, half_15_10_φ3, half_15_10_φ4, half_15_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_10_hx2 : SourcePowerBound (powerBoxCross 18 13 4 half_15_10_φ2) (30835142113949/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 13) (u := 11) (t := 14)
    (D := 4) (ψ := (379466426263/10000000000000 : ℝ)) half_15_10_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_10_φ1, half_15_10_φ2, half_15_10_φ3, half_15_10_φ4, half_15_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_10_φ1, half_15_10_φ2, half_15_10_φ3, half_15_10_φ4, half_15_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_10_φ1, half_15_10_φ2, half_15_10_φ3, half_15_10_φ4, half_15_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_10 half_14_10
    (by simpa only [half_15_10_φ3, show (2:ℝ)*4=8 by norm_num] using half_15_10_hx3)
  exact h.weaken (by norm_num [half_15_10_φ1, half_15_10_φ2, half_15_10_φ3, half_15_10_φ4, half_15_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_10_hx1 : SourcePowerBound (powerBoxCross 18 14 2 half_15_10_φ1) (85354775821947/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 14) (u := 12) (t := 15)
    (D := 2) (ψ := (3930003497/100000000000 : ℝ)) half_15_10_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_10_φ1, half_15_10_φ2, half_15_10_φ3, half_15_10_φ4, half_15_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_10_φ1, half_15_10_φ2, half_15_10_φ3, half_15_10_φ4, half_15_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_10_φ1, half_15_10_φ2, half_15_10_φ3, half_15_10_φ4, half_15_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_13_10 half_15_09
    (by simpa only [half_15_10_φ2, show (2:ℝ)*2=4 by norm_num] using half_15_10_hx2)
  exact h.weaken (by norm_num [half_15_10_φ1, half_15_10_φ2, half_15_10_φ3, half_15_10_φ4, half_15_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_10 : AdmissibleExponent 18 30 (45402904074471/2500000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 13) (ψ := (40378017237/1000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_14_10
    (by simpa only [half_15_10_φ1] using half_15_10_hx1)
  exact admissibleExponent_mono h (by norm_num [half_15_10_φ1, half_15_10_φ2, half_15_10_φ3, half_15_10_φ4, half_15_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_16_10_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (413172216641/10000000000000 : ℝ)

def half_16_10_φ2 : Fin 2 → ℝ := Fin.snoc half_16_10_φ1 (20136030583/500000000000 : ℝ)

def half_16_10_φ3 : Fin 3 → ℝ := Fin.snoc half_16_10_φ2 (391110176099/10000000000000 : ℝ)

def half_16_10_φ4 : Fin 4 → ℝ := Fin.snoc half_16_10_φ3 (374113846081/10000000000000 : ℝ)

def half_16_10_φ5 : Fin 5 → ℝ := Fin.snoc half_16_10_φ4 (168165296941/5000000000000 : ℝ)

def half_16_10_φ6 : Fin 6 → ℝ := Fin.snoc half_16_10_φ5 (8333630711/400000000000 : ℝ)

theorem half_16_10_hF2 : SourcePowerBound (paddedMoment 18 0 2 64 half_16_10_φ6) (45792400590481/5000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 6) (r := 0) (D := 64)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_16_10_φ6 (by norm_num [half_16_10_φ1, half_16_10_φ2, half_16_10_φ3, half_16_10_φ4, half_16_10_φ5, half_16_10_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_10_φ1, half_16_10_φ2, half_16_10_φ3, half_16_10_φ4, half_16_10_φ5, half_16_10_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_10_φ1, half_16_10_φ2, half_16_10_φ3, half_16_10_φ4, half_16_10_φ5, half_16_10_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_16_10_φ1, half_16_10_φ2, half_16_10_φ3, half_16_10_φ4, half_16_10_φ5, half_16_10_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_16_10_hx6 : SourcePowerBound (powerBoxCross 18 10 64 half_16_10_φ6) (23189872222959/2000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 10) (r := 2) (v := 13) (w := 14) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_16_10_φ6 (by norm_num [half_16_10_φ1, half_16_10_φ2, half_16_10_φ3, half_16_10_φ4, half_16_10_φ5, half_16_10_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_10_φ1, half_16_10_φ2, half_16_10_φ3, half_16_10_φ4, half_16_10_φ5, half_16_10_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_16_10_hF2 half_13_10 half_14_10
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_16_10_φ1, half_16_10_φ2, half_16_10_φ3, half_16_10_φ4, half_16_10_φ5, half_16_10_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_10_hx5 : SourcePowerBound (powerBoxCross 18 11 32 half_16_10_φ5) (124803676742803/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 5) (s := 11) (u := 9) (t := 12)
    (D := 32) (ψ := (8333630711/400000000000 : ℝ)) half_16_10_φ5
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_10_φ1, half_16_10_φ2, half_16_10_φ3, half_16_10_φ4, half_16_10_φ5, half_16_10_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_10_φ1, half_16_10_φ2, half_16_10_φ3, half_16_10_φ4, half_16_10_φ5, half_16_10_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_10_φ1, half_16_10_φ2, half_16_10_φ3, half_16_10_φ4, half_16_10_φ5, half_16_10_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_10 half_12_10
    (by simpa only [half_16_10_φ6, show (2:ℝ)*32=64 by norm_num] using half_16_10_hx6)
  exact h.weaken (by norm_num [half_16_10_φ1, half_16_10_φ2, half_16_10_φ3, half_16_10_φ4, half_16_10_φ5, half_16_10_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_10_hx4 : SourcePowerBound (powerBoxCross 18 12 16 half_16_10_φ4) (136824045333587/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 12) (u := 10) (t := 13)
    (D := 16) (ψ := (168165296941/5000000000000 : ℝ)) half_16_10_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_10_φ1, half_16_10_φ2, half_16_10_φ3, half_16_10_φ4, half_16_10_φ5, half_16_10_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_10_φ1, half_16_10_φ2, half_16_10_φ3, half_16_10_φ4, half_16_10_φ5, half_16_10_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_10_φ1, half_16_10_φ2, half_16_10_φ3, half_16_10_φ4, half_16_10_φ5, half_16_10_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_10 half_13_10
    (by simpa only [half_16_10_φ5, show (2:ℝ)*16=32 by norm_num] using half_16_10_hx5)
  exact h.weaken (by norm_num [half_16_10_φ1, half_16_10_φ2, half_16_10_φ3, half_16_10_φ4, half_16_10_φ5, half_16_10_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_10_hx3 : SourcePowerBound (powerBoxCross 18 13 8 half_16_10_φ3) (75449367459487/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 13) (u := 11) (t := 14)
    (D := 8) (ψ := (374113846081/10000000000000 : ℝ)) half_16_10_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_10_φ1, half_16_10_φ2, half_16_10_φ3, half_16_10_φ4, half_16_10_φ5, half_16_10_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_10_φ1, half_16_10_φ2, half_16_10_φ3, half_16_10_φ4, half_16_10_φ5, half_16_10_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_10_φ1, half_16_10_φ2, half_16_10_φ3, half_16_10_φ4, half_16_10_φ5, half_16_10_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_10 half_14_10
    (by simpa only [half_16_10_φ4, show (2:ℝ)*8=16 by norm_num] using half_16_10_hx4)
  exact h.weaken (by norm_num [half_16_10_φ1, half_16_10_φ2, half_16_10_φ3, half_16_10_φ4, half_16_10_φ5, half_16_10_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_10_hx2 : SourcePowerBound (powerBoxCross 18 14 4 half_16_10_φ2) (166800183005429/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 14) (u := 12) (t := 15)
    (D := 4) (ψ := (391110176099/10000000000000 : ℝ)) half_16_10_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_10_φ1, half_16_10_φ2, half_16_10_φ3, half_16_10_φ4, half_16_10_φ5, half_16_10_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_10_φ1, half_16_10_φ2, half_16_10_φ3, half_16_10_φ4, half_16_10_φ5, half_16_10_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_10_φ1, half_16_10_φ2, half_16_10_φ3, half_16_10_φ4, half_16_10_φ5, half_16_10_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_13_10 half_15_10
    (by simpa only [half_16_10_φ3, show (2:ℝ)*4=8 by norm_num] using half_16_10_hx3)
  exact h.weaken (by norm_num [half_16_10_φ1, half_16_10_φ2, half_16_10_φ3, half_16_10_φ4, half_16_10_φ5, half_16_10_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_10_hx1 : SourcePowerBound (powerBoxCross 18 15 2 half_16_10_φ1) (18452110110719/1000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 15) (u := 13) (t := 16)
    (D := 2) (ψ := (20136030583/500000000000 : ℝ)) half_16_10_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_10_φ1, half_16_10_φ2, half_16_10_φ3, half_16_10_φ4, half_16_10_φ5, half_16_10_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_10_φ1, half_16_10_φ2, half_16_10_φ3, half_16_10_φ4, half_16_10_φ5, half_16_10_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_10_φ1, half_16_10_φ2, half_16_10_φ3, half_16_10_φ4, half_16_10_φ5, half_16_10_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_14_10 half_16_09
    (by simpa only [half_16_10_φ2, show (2:ℝ)*2=4 by norm_num] using half_16_10_hx2)
  exact h.weaken (by norm_num [half_16_10_φ1, half_16_10_φ2, half_16_10_φ3, half_16_10_φ4, half_16_10_φ5, half_16_10_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_10 : AdmissibleExponent 18 32 (196503095389779/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 14) (ψ := (413172216641/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_15_10
    (by simpa only [half_16_10_φ1] using half_16_10_hx1)
  exact admissibleExponent_mono h (by norm_num [half_16_10_φ1, half_16_10_φ2, half_16_10_φ3, half_16_10_φ4, half_16_10_φ5, half_16_10_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_17_10_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (84468491271/2000000000000 : ℝ)

def half_17_10_φ2 : Fin 2 → ℝ := Fin.snoc half_17_10_φ1 (103015306789/2500000000000 : ℝ)

def half_17_10_φ3 : Fin 3 → ℝ := Fin.snoc half_17_10_φ2 (80230645137/2000000000000 : ℝ)

def half_17_10_φ4 : Fin 4 → ℝ := Fin.snoc half_17_10_φ3 (19357537209/500000000000 : ℝ)

def half_17_10_φ5 : Fin 5 → ℝ := Fin.snoc half_17_10_φ4 (361408776779/10000000000000 : ℝ)

def half_17_10_φ6 : Fin 6 → ℝ := Fin.snoc half_17_10_φ5 (289434336251/10000000000000 : ℝ)

theorem half_17_10_hF2 : SourcePowerBound (paddedMoment 18 0 2 64 half_17_10_φ6) (42024455456647/5000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 6) (r := 0) (D := 64)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_17_10_φ6 (by norm_num [half_17_10_φ1, half_17_10_φ2, half_17_10_φ3, half_17_10_φ4, half_17_10_φ5, half_17_10_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_10_φ1, half_17_10_φ2, half_17_10_φ3, half_17_10_φ4, half_17_10_φ5, half_17_10_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_10_φ1, half_17_10_φ2, half_17_10_φ3, half_17_10_φ4, half_17_10_φ5, half_17_10_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_17_10_φ1, half_17_10_φ2, half_17_10_φ3, half_17_10_φ4, half_17_10_φ5, half_17_10_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_17_10_hx6 : SourcePowerBound (powerBoxCross 18 11 64 half_17_10_φ6) (123440643052939/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 11) (r := 2) (v := 14) (w := 15) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_17_10_φ6 (by norm_num [half_17_10_φ1, half_17_10_φ2, half_17_10_φ3, half_17_10_φ4, half_17_10_φ5, half_17_10_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_10_φ1, half_17_10_φ2, half_17_10_φ3, half_17_10_φ4, half_17_10_φ5, half_17_10_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_17_10_hF2 half_14_10 half_15_10
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_17_10_φ1, half_17_10_φ2, half_17_10_φ3, half_17_10_φ4, half_17_10_φ5, half_17_10_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_10_hx5 : SourcePowerBound (powerBoxCross 18 12 32 half_17_10_φ5) (134145227715961/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 5) (s := 12) (u := 10) (t := 13)
    (D := 32) (ψ := (289434336251/10000000000000 : ℝ)) half_17_10_φ5
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_10_φ1, half_17_10_φ2, half_17_10_φ3, half_17_10_φ4, half_17_10_φ5, half_17_10_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_10_φ1, half_17_10_φ2, half_17_10_φ3, half_17_10_φ4, half_17_10_φ5, half_17_10_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_10_φ1, half_17_10_φ2, half_17_10_φ3, half_17_10_φ4, half_17_10_φ5, half_17_10_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_10 half_13_10
    (by simpa only [half_17_10_φ6, show (2:ℝ)*32=64 by norm_num] using half_17_10_hx6)
  exact h.weaken (by norm_num [half_17_10_φ1, half_17_10_φ2, half_17_10_φ3, half_17_10_φ4, half_17_10_φ5, half_17_10_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_10_hx4 : SourcePowerBound (powerBoxCross 18 13 16 half_17_10_φ4) (147407535305517/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 13) (u := 11) (t := 14)
    (D := 16) (ψ := (361408776779/10000000000000 : ℝ)) half_17_10_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_10_φ1, half_17_10_φ2, half_17_10_φ3, half_17_10_φ4, half_17_10_φ5, half_17_10_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_10_φ1, half_17_10_φ2, half_17_10_φ3, half_17_10_φ4, half_17_10_φ5, half_17_10_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_10_φ1, half_17_10_φ2, half_17_10_φ3, half_17_10_φ4, half_17_10_φ5, half_17_10_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_10 half_14_10
    (by simpa only [half_17_10_φ5, show (2:ℝ)*16=32 by norm_num] using half_17_10_hx5)
  exact h.weaken (by norm_num [half_17_10_φ1, half_17_10_φ2, half_17_10_φ3, half_17_10_φ4, half_17_10_φ5, half_17_10_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_10_hx3 : SourcePowerBound (powerBoxCross 18 14 8 half_17_10_φ3) (16262715201043/1000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 14) (u := 12) (t := 15)
    (D := 8) (ψ := (19357537209/500000000000 : ℝ)) half_17_10_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_10_φ1, half_17_10_φ2, half_17_10_φ3, half_17_10_φ4, half_17_10_φ5, half_17_10_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_10_φ1, half_17_10_φ2, half_17_10_φ3, half_17_10_φ4, half_17_10_φ5, half_17_10_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_10_φ1, half_17_10_φ2, half_17_10_φ3, half_17_10_φ4, half_17_10_φ5, half_17_10_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_13_10 half_15_10
    (by simpa only [half_17_10_φ4, show (2:ℝ)*8=16 by norm_num] using half_17_10_hx4)
  exact h.weaken (by norm_num [half_17_10_φ1, half_17_10_φ2, half_17_10_φ3, half_17_10_φ4, half_17_10_φ5, half_17_10_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_10_hx2 : SourcePowerBound (powerBoxCross 18 15 4 half_17_10_φ2) (89845057803141/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 15) (u := 13) (t := 16)
    (D := 4) (ψ := (80230645137/2000000000000 : ℝ)) half_17_10_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_10_φ1, half_17_10_φ2, half_17_10_φ3, half_17_10_φ4, half_17_10_φ5, half_17_10_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_10_φ1, half_17_10_φ2, half_17_10_φ3, half_17_10_φ4, half_17_10_φ5, half_17_10_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_10_φ1, half_17_10_φ2, half_17_10_φ3, half_17_10_φ4, half_17_10_φ5, half_17_10_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_14_10 half_16_10
    (by simpa only [half_17_10_φ3, show (2:ℝ)*4=8 by norm_num] using half_17_10_hx3)
  exact h.weaken (by norm_num [half_17_10_φ1, half_17_10_φ2, half_17_10_φ3, half_17_10_φ4, half_17_10_φ5, half_17_10_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_10_hx1 : SourcePowerBound (powerBoxCross 18 16 2 half_17_10_φ1) (99313138923663/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 16) (u := 14) (t := 17)
    (D := 2) (ψ := (103015306789/2500000000000 : ℝ)) half_17_10_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_10_φ1, half_17_10_φ2, half_17_10_φ3, half_17_10_φ4, half_17_10_φ5, half_17_10_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_10_φ1, half_17_10_φ2, half_17_10_φ3, half_17_10_φ4, half_17_10_φ5, half_17_10_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_10_φ1, half_17_10_φ2, half_17_10_φ3, half_17_10_φ4, half_17_10_φ5, half_17_10_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_15_10 half_17_09
    (by simpa only [half_17_10_φ2, show (2:ℝ)*2=4 by norm_num] using half_17_10_hx2)
  exact h.weaken (by norm_num [half_17_10_φ1, half_17_10_φ2, half_17_10_φ3, half_17_10_φ4, half_17_10_φ5, half_17_10_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_10 : AdmissibleExponent 18 34 (211718893994331/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 15) (ψ := (84468491271/2000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_16_10
    (by simpa only [half_17_10_φ1] using half_17_10_hx1)
  exact admissibleExponent_mono h (by norm_num [half_17_10_φ1, half_17_10_φ2, half_17_10_φ3, half_17_10_φ4, half_17_10_φ5, half_17_10_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])


end Waring.SeedCompletionHigher18SimpleSeeds
