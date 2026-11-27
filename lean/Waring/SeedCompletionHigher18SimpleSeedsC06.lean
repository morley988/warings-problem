import Waring.SeedCompletionHigher18SimpleSeedsC05

noncomputable section
set_option maxHeartbeats 2000000
namespace Waring.SeedCompletionHigher18SimpleSeeds
open SmoothMoments FirstStageTransport SeedCompletionNaturalBox
open SeedCompletionSourceBounds SeedCompletionPaddedSource SeedCompletionGeneralTerminal
open PolicyCompletionMajorPowerRanges

def half_9_06_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (343874281739/10000000000000 : ℝ)

def half_9_06_φ2 : Fin 2 → ℝ := Fin.snoc half_9_06_φ1 (308384756831/10000000000000 : ℝ)

def half_9_06_φ3 : Fin 3 → ℝ := Fin.snoc half_9_06_φ2 (6734804913/500000000000 : ℝ)

theorem half_9_06_hF2 : SourcePowerBound (paddedMoment 18 0 2 8 half_9_06_φ3) (6986528802167/1000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_06_φ3 (by norm_num [half_9_06_φ1, half_9_06_φ2, half_9_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_06_φ1, half_9_06_φ2, half_9_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_06_φ1, half_9_06_φ2, half_9_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_06_φ1, half_9_06_φ2, half_9_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_9_06_hF1 : SourcePowerBound (paddedMoment 18 0 1 8 half_9_06_φ3) (2662176267389/1000000000000 : ℝ) := by
  have h := padded_second_power (k := 18) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_06_φ3 (by norm_num [half_9_06_φ1, half_9_06_φ2, half_9_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_06_φ1, half_9_06_φ2, half_9_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_06_φ1, half_9_06_φ2, half_9_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_06_φ1, half_9_06_φ2, half_9_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_9_06_hx3 : SourcePowerBound (powerBoxCross 18 6 8 half_9_06_φ3) (76989965563441/10000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 18) (s := 6) (r := 1) (v := 2) (t := 10) (D := 8)
    (a := (3/10 : ℝ)) (b := (1/10 : ℝ)) (c := (3/5 : ℝ))
    (by norm_num) half_9_06_φ3 (by norm_num [half_9_06_φ1, half_9_06_φ2, half_9_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_06_φ1, half_9_06_φ2, half_9_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_9_06_hF1 half_9_06_hF2 half_10_05
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_9_06_φ1, half_9_06_φ2, half_9_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_9_06_hx2 : SourcePowerBound (powerBoxCross 18 7 4 half_9_06_φ2) (84268298176803/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 7) (u := 5) (t := 8)
    (D := 4) (ψ := (6734804913/500000000000 : ℝ)) half_9_06_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_06_φ1, half_9_06_φ2, half_9_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_06_φ1, half_9_06_φ2, half_9_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_06_φ1, half_9_06_φ2, half_9_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_6 SeedCompletionEven18SecondSeeds.degree18_half_8
    (by simpa only [half_9_06_φ3, show (2:ℝ)*4=8 by norm_num] using half_9_06_hx3)
  exact h.weaken (by norm_num [half_9_06_φ1, half_9_06_φ2, half_9_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_9_06_hx1 : SourcePowerBound (powerBoxCross 18 8 2 half_9_06_φ1) (1471476964417/156250000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 8) (u := 6) (t := 9)
    (D := 2) (ψ := (308384756831/10000000000000 : ℝ)) half_9_06_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_06_φ1, half_9_06_φ2, half_9_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_06_φ1, half_9_06_φ2, half_9_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_06_φ1, half_9_06_φ2, half_9_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_7 half_9_05
    (by simpa only [half_9_06_φ2, show (2:ℝ)*2=4 by norm_num] using half_9_06_hx2)
  exact h.weaken (by norm_num [half_9_06_φ1, half_9_06_φ2, half_9_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_9_06 : AdmissibleExponent 18 18 (99332639948773/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 7) (ψ := (343874281739/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_8
    (by simpa only [half_9_06_φ1] using half_9_06_hx1)
  exact admissibleExponent_mono h (by norm_num [half_9_06_φ1, half_9_06_φ2, half_9_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_10_06_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (44232323617/1250000000000 : ℝ)

def half_10_06_φ2 : Fin 2 → ℝ := Fin.snoc half_10_06_φ1 (329284601651/10000000000000 : ℝ)

def half_10_06_φ3 : Fin 3 → ℝ := Fin.snoc half_10_06_φ2 (230057074439/10000000000000 : ℝ)

theorem half_10_06_hF2 : SourcePowerBound (paddedMoment 18 0 2 8 half_10_06_φ3) (31713393241837/5000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_10_06_φ3 (by norm_num [half_10_06_φ1, half_10_06_φ2, half_10_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_06_φ1, half_10_06_φ2, half_10_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_06_φ1, half_10_06_φ2, half_10_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_10_06_φ1, half_10_06_φ2, half_10_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_10_06_hx3 : SourcePowerBound (powerBoxCross 18 7 8 half_10_06_φ3) (86473777988597/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 7) (r := 2) (v := 9) (w := 10) (D := 8)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_10_06_φ3 (by norm_num [half_10_06_φ1, half_10_06_φ2, half_10_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_06_φ1, half_10_06_φ2, half_10_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_10_06_hF2 half_9_06 half_10_05
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_10_06_φ1, half_10_06_φ2, half_10_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_06_hx2 : SourcePowerBound (powerBoxCross 18 8 4 half_10_06_φ2) (23799735500837/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 8) (u := 6) (t := 9)
    (D := 4) (ψ := (230057074439/10000000000000 : ℝ)) half_10_06_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_06_φ1, half_10_06_φ2, half_10_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_06_φ1, half_10_06_φ2, half_10_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_06_φ1, half_10_06_φ2, half_10_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_7 half_9_06
    (by simpa only [half_10_06_φ3, show (2:ℝ)*4=8 by norm_num] using half_10_06_hx3)
  exact h.weaken (by norm_num [half_10_06_φ1, half_10_06_φ2, half_10_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_06_hx1 : SourcePowerBound (powerBoxCross 18 9 2 half_10_06_φ1) (53085763878479/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 9) (u := 7) (t := 10)
    (D := 2) (ψ := (329284601651/10000000000000 : ℝ)) half_10_06_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_06_φ1, half_10_06_φ2, half_10_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_06_φ1, half_10_06_φ2, half_10_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_06_φ1, half_10_06_φ2, half_10_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_8 half_10_05
    (by simpa only [half_10_06_φ2, show (2:ℝ)*2=4 by norm_num] using half_10_06_hx2)
  exact h.weaken (by norm_num [half_10_06_φ1, half_10_06_φ2, half_10_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_06 : AdmissibleExponent 18 20 (11218712376887/1000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 8) (ψ := (44232323617/1250000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_9_06
    (by simpa only [half_10_06_φ1] using half_10_06_hx1)
  exact admissibleExponent_mono h (by norm_num [half_10_06_φ1, half_10_06_φ2, half_10_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_11_06_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (365163439107/10000000000000 : ℝ)

def half_11_06_φ2 : Fin 2 → ℝ := Fin.snoc half_11_06_φ1 (173275296489/5000000000000 : ℝ)

def half_11_06_φ3 : Fin 3 → ℝ := Fin.snoc half_11_06_φ2 (295418941499/10000000000000 : ℝ)

theorem half_11_06_hF2 : SourcePowerBound (paddedMoment 18 0 2 8 half_11_06_φ3) (3664763646701/625000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_11_06_φ3 (by norm_num [half_11_06_φ1, half_11_06_φ2, half_11_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_06_φ1, half_11_06_φ2, half_11_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_06_φ1, half_11_06_φ2, half_11_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_11_06_φ1, half_11_06_φ2, half_11_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_11_06_hx3 : SourcePowerBound (powerBoxCross 18 8 8 half_11_06_φ3) (19253756617881/2000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 8) (r := 2) (v := 10) (w := 11) (D := 8)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_11_06_φ3 (by norm_num [half_11_06_φ1, half_11_06_φ2, half_11_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_06_φ1, half_11_06_φ2, half_11_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_11_06_hF2 half_10_06 half_11_05
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_11_06_φ1, half_11_06_φ2, half_11_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_06_hx2 : SourcePowerBound (powerBoxCross 18 9 4 half_11_06_φ2) (5320088435369/500000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 9) (u := 7) (t := 10)
    (D := 4) (ψ := (295418941499/10000000000000 : ℝ)) half_11_06_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_06_φ1, half_11_06_φ2, half_11_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_06_φ1, half_11_06_φ2, half_11_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_06_φ1, half_11_06_φ2, half_11_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_8 half_10_06
    (by simpa only [half_11_06_φ3, show (2:ℝ)*4=8 by norm_num] using half_11_06_hx3)
  exact h.weaken (by norm_num [half_11_06_φ1, half_11_06_φ2, half_11_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_06_hx1 : SourcePowerBound (powerBoxCross 18 10 2 half_11_06_φ1) (118455623614087/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 10) (u := 8) (t := 11)
    (D := 2) (ψ := (173275296489/5000000000000 : ℝ)) half_11_06_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_06_φ1, half_11_06_φ2, half_11_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_06_φ1, half_11_06_φ2, half_11_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_06_φ1, half_11_06_φ2, half_11_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_06 half_11_05
    (by simpa only [half_11_06_φ2, show (2:ℝ)*2=4 by norm_num] using half_11_06_hx2)
  exact h.weaken (by norm_num [half_11_06_φ1, half_11_06_φ2, half_11_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_06 : AdmissibleExponent 18 22 (391855402991/31250000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 9) (ψ := (365163439107/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_10_06
    (by simpa only [half_11_06_φ1] using half_11_06_hx1)
  exact admissibleExponent_mono h (by norm_num [half_11_06_φ1, half_11_06_φ2, half_11_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_12_06_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (93945849813/2500000000000 : ℝ)

def half_12_06_φ2 : Fin 2 → ℝ := Fin.snoc half_12_06_φ1 (360683807483/10000000000000 : ℝ)

def half_12_06_φ3 : Fin 3 → ℝ := Fin.snoc half_12_06_φ2 (65910878541/2000000000000 : ℝ)

def half_12_06_φ4 : Fin 4 → ℝ := Fin.snoc half_12_06_φ3 (213448526073/10000000000000 : ℝ)

theorem half_12_06_hF2 : SourcePowerBound (paddedMoment 18 0 2 16 half_12_06_φ4) (74747023598837/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_12_06_φ4 (by norm_num [half_12_06_φ1, half_12_06_φ2, half_12_06_φ3, half_12_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_06_φ1, half_12_06_φ2, half_12_06_φ3, half_12_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_06_φ1, half_12_06_φ2, half_12_06_φ3, half_12_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_12_06_φ1, half_12_06_φ2, half_12_06_φ3, half_12_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_12_06_hF1 : SourcePowerBound (paddedMoment 18 0 1 16 half_12_06_φ4) (28249007866279/10000000000000 : ℝ) := by
  have h := padded_second_power (k := 18) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_12_06_φ4 (by norm_num [half_12_06_φ1, half_12_06_φ2, half_12_06_φ3, half_12_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_06_φ1, half_12_06_φ2, half_12_06_φ3, half_12_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_06_φ1, half_12_06_φ2, half_12_06_φ3, half_12_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_12_06_φ1, half_12_06_φ2, half_12_06_φ3, half_12_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_12_06_hx4 : SourcePowerBound (powerBoxCross 18 8 16 half_12_06_φ4) (48899630476607/5000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 18) (s := 8) (r := 1) (v := 2) (t := 11) (D := 16)
    (a := (1/22 : ℝ)) (b := (5/22 : ℝ)) (c := (8/11 : ℝ))
    (by norm_num) half_12_06_φ4 (by norm_num [half_12_06_φ1, half_12_06_φ2, half_12_06_φ3, half_12_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_06_φ1, half_12_06_φ2, half_12_06_φ3, half_12_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_12_06_hF1 half_12_06_hF2 half_11_06
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_12_06_φ1, half_12_06_φ2, half_12_06_φ3, half_12_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_06_hx3 : SourcePowerBound (powerBoxCross 18 9 8 half_12_06_φ3) (106553177855517/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 9) (u := 7) (t := 10)
    (D := 8) (ψ := (213448526073/10000000000000 : ℝ)) half_12_06_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_06_φ1, half_12_06_φ2, half_12_06_φ3, half_12_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_06_φ1, half_12_06_φ2, half_12_06_φ3, half_12_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_06_φ1, half_12_06_φ2, half_12_06_φ3, half_12_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_8 half_10_06
    (by simpa only [half_12_06_φ4, show (2:ℝ)*8=16 by norm_num] using half_12_06_hx4)
  exact h.weaken (by norm_num [half_12_06_φ1, half_12_06_φ2, half_12_06_φ3, half_12_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_06_hx2 : SourcePowerBound (powerBoxCross 18 10 4 half_12_06_φ2) (117897276021707/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 10) (u := 8) (t := 11)
    (D := 4) (ψ := (65910878541/2000000000000 : ℝ)) half_12_06_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_06_φ1, half_12_06_φ2, half_12_06_φ3, half_12_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_06_φ1, half_12_06_φ2, half_12_06_φ3, half_12_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_06_φ1, half_12_06_φ2, half_12_06_φ3, half_12_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_06 half_11_06
    (by simpa only [half_12_06_φ3, show (2:ℝ)*4=8 by norm_num] using half_12_06_hx3)
  exact h.weaken (by norm_num [half_12_06_φ1, half_12_06_φ2, half_12_06_φ3, half_12_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_06_hx1 : SourcePowerBound (powerBoxCross 18 11 2 half_12_06_φ1) (131057424185149/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 11) (u := 9) (t := 12)
    (D := 2) (ψ := (360683807483/10000000000000 : ℝ)) half_12_06_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_06_φ1, half_12_06_φ2, half_12_06_φ3, half_12_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_06_φ1, half_12_06_φ2, half_12_06_φ3, half_12_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_06_φ1, half_12_06_φ2, half_12_06_φ3, half_12_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_06 half_12_05
    (by simpa only [half_12_06_φ2, show (2:ℝ)*2=4 by norm_num] using half_12_06_hx2)
  exact h.weaken (by norm_num [half_12_06_φ1, half_12_06_φ2, half_12_06_φ3, half_12_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_06 : AdmissibleExponent 18 24 (138948875569441/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 10) (ψ := (93945849813/2500000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_11_06
    (by simpa only [half_12_06_φ1] using half_12_06_hx1)
  exact admissibleExponent_mono h (by norm_num [half_12_06_φ1, half_12_06_φ2, half_12_06_φ3, half_12_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_13_06_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (386339177421/10000000000000 : ℝ)

def half_13_06_φ2 : Fin 2 → ℝ := Fin.snoc half_13_06_φ1 (186075544913/5000000000000 : ℝ)

def half_13_06_φ3 : Fin 3 → ℝ := Fin.snoc half_13_06_φ2 (350214509471/10000000000000 : ℝ)

def half_13_06_φ4 : Fin 4 → ℝ := Fin.snoc half_13_06_φ3 (284457162803/10000000000000 : ℝ)

theorem half_13_06_hF2 : SourcePowerBound (paddedMoment 18 0 2 16 half_13_06_φ4) (68948741084429/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_13_06_φ4 (by norm_num [half_13_06_φ1, half_13_06_φ2, half_13_06_φ3, half_13_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_06_φ1, half_13_06_φ2, half_13_06_φ3, half_13_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_06_φ1, half_13_06_φ2, half_13_06_φ3, half_13_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_13_06_φ1, half_13_06_φ2, half_13_06_φ3, half_13_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_13_06_hx4 : SourcePowerBound (powerBoxCross 18 9 16 half_13_06_φ4) (21386094114899/2000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 9) (r := 2) (v := 12) (w := 12) (D := 16)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_13_06_φ4 (by norm_num [half_13_06_φ1, half_13_06_φ2, half_13_06_φ3, half_13_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_06_φ1, half_13_06_φ2, half_13_06_φ3, half_13_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_13_06_hF2 half_12_06 half_12_06
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_13_06_φ1, half_13_06_φ2, half_13_06_φ3, half_13_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_06_hx3 : SourcePowerBound (powerBoxCross 18 10 8 half_13_06_φ3) (29301190933567/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 10) (u := 8) (t := 11)
    (D := 8) (ψ := (284457162803/10000000000000 : ℝ)) half_13_06_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_06_φ1, half_13_06_φ2, half_13_06_φ3, half_13_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_06_φ1, half_13_06_φ2, half_13_06_φ3, half_13_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_06_φ1, half_13_06_φ2, half_13_06_φ3, half_13_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_06 half_11_06
    (by simpa only [half_13_06_φ4, show (2:ℝ)*8=16 by norm_num] using half_13_06_hx4)
  exact h.weaken (by norm_num [half_13_06_φ1, half_13_06_φ2, half_13_06_φ3, half_13_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_06_hx2 : SourcePowerBound (powerBoxCross 18 11 4 half_13_06_φ2) (129687121732013/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 11) (u := 9) (t := 12)
    (D := 4) (ψ := (350214509471/10000000000000 : ℝ)) half_13_06_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_06_φ1, half_13_06_φ2, half_13_06_φ3, half_13_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_06_φ1, half_13_06_φ2, half_13_06_φ3, half_13_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_06_φ1, half_13_06_φ2, half_13_06_φ3, half_13_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_06 half_12_06
    (by simpa only [half_13_06_φ3, show (2:ℝ)*4=8 by norm_num] using half_13_06_hx3)
  exact h.weaken (by norm_num [half_13_06_φ1, half_13_06_φ2, half_13_06_φ3, half_13_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_06_hx1 : SourcePowerBound (powerBoxCross 18 12 2 half_13_06_φ1) (143967075317771/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 12) (u := 10) (t := 13)
    (D := 2) (ψ := (186075544913/5000000000000 : ℝ)) half_13_06_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_06_φ1, half_13_06_φ2, half_13_06_φ3, half_13_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_06_φ1, half_13_06_φ2, half_13_06_φ3, half_13_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_06_φ1, half_13_06_φ2, half_13_06_φ3, half_13_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_06 half_13_05
    (by simpa only [half_13_06_φ2, show (2:ℝ)*2=4 by norm_num] using half_13_06_hx2)
  exact h.weaken (by norm_num [half_13_06_φ1, half_13_06_φ2, half_13_06_φ3, half_13_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_06 : AdmissibleExponent 18 26 (76426438199227/5000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 11) (ψ := (386339177421/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_12_06
    (by simpa only [half_13_06_φ1] using half_13_06_hx1)
  exact admissibleExponent_mono h (by norm_num [half_13_06_φ1, half_13_06_φ2, half_13_06_φ3, half_13_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_14_06_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (397389437907/10000000000000 : ℝ)

def half_14_06_φ2 : Fin 2 → ℝ := Fin.snoc half_14_06_φ1 (383278322261/10000000000000 : ℝ)

def half_14_06_φ3 : Fin 3 → ℝ := Fin.snoc half_14_06_φ2 (367459711749/10000000000000 : ℝ)

def half_14_06_φ4 : Fin 4 → ℝ := Fin.snoc half_14_06_φ3 (332528135127/10000000000000 : ℝ)

def half_14_06_φ5 : Fin 5 → ℝ := Fin.snoc half_14_06_φ4 (51787629569/2500000000000 : ℝ)

theorem half_14_06_hF2 : SourcePowerBound (paddedMoment 18 0 2 32 half_14_06_φ5) (2098047190217/250000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_14_06_φ5 (by norm_num [half_14_06_φ1, half_14_06_φ2, half_14_06_φ3, half_14_06_φ4, half_14_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_06_φ1, half_14_06_φ2, half_14_06_φ3, half_14_06_φ4, half_14_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_06_φ1, half_14_06_φ2, half_14_06_φ3, half_14_06_φ4, half_14_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_14_06_φ1, half_14_06_φ2, half_14_06_φ3, half_14_06_φ4, half_14_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_14_06_hx5 : SourcePowerBound (powerBoxCross 18 9 32 half_14_06_φ5) (107603221332319/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 9) (r := 2) (v := 12) (w := 12) (D := 32)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_14_06_φ5 (by norm_num [half_14_06_φ1, half_14_06_φ2, half_14_06_φ3, half_14_06_φ4, half_14_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_06_φ1, half_14_06_φ2, half_14_06_φ3, half_14_06_φ4, half_14_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_14_06_hF2 half_12_06 half_12_06
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_14_06_φ1, half_14_06_φ2, half_14_06_φ3, half_14_06_φ4, half_14_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_06_hx4 : SourcePowerBound (powerBoxCross 18 10 16 half_14_06_φ4) (11639043549677/1000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 10) (u := 8) (t := 11)
    (D := 16) (ψ := (51787629569/2500000000000 : ℝ)) half_14_06_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_06_φ1, half_14_06_φ2, half_14_06_φ3, half_14_06_φ4, half_14_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_06_φ1, half_14_06_φ2, half_14_06_φ3, half_14_06_φ4, half_14_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_06_φ1, half_14_06_φ2, half_14_06_φ3, half_14_06_φ4, half_14_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_06 half_11_06
    (by simpa only [half_14_06_φ5, show (2:ℝ)*16=32 by norm_num] using half_14_06_hx5)
  exact h.weaken (by norm_num [half_14_06_φ1, half_14_06_φ2, half_14_06_φ3, half_14_06_φ4, half_14_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_06_hx3 : SourcePowerBound (powerBoxCross 18 11 8 half_14_06_φ3) (25618607648771/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 11) (u := 9) (t := 12)
    (D := 8) (ψ := (332528135127/10000000000000 : ℝ)) half_14_06_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_06_φ1, half_14_06_φ2, half_14_06_φ3, half_14_06_φ4, half_14_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_06_φ1, half_14_06_φ2, half_14_06_φ3, half_14_06_φ4, half_14_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_06_φ1, half_14_06_φ2, half_14_06_φ3, half_14_06_φ4, half_14_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_06 half_12_06
    (by simpa only [half_14_06_φ4, show (2:ℝ)*8=16 by norm_num] using half_14_06_hx4)
  exact h.weaken (by norm_num [half_14_06_φ1, half_14_06_φ2, half_14_06_φ3, half_14_06_φ4, half_14_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_06_hx2 : SourcePowerBound (powerBoxCross 18 12 4 half_14_06_φ2) (141729242700431/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 12) (u := 10) (t := 13)
    (D := 4) (ψ := (367459711749/10000000000000 : ℝ)) half_14_06_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_06_φ1, half_14_06_φ2, half_14_06_φ3, half_14_06_φ4, half_14_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_06_φ1, half_14_06_φ2, half_14_06_φ3, half_14_06_φ4, half_14_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_06_φ1, half_14_06_φ2, half_14_06_φ3, half_14_06_φ4, half_14_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_06 half_13_06
    (by simpa only [half_14_06_φ3, show (2:ℝ)*4=8 by norm_num] using half_14_06_hx3)
  exact h.weaken (by norm_num [half_14_06_φ1, half_14_06_φ2, half_14_06_φ3, half_14_06_φ4, half_14_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_06_hx1 : SourcePowerBound (powerBoxCross 18 13 2 half_14_06_φ1) (39294013493233/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 13) (u := 11) (t := 14)
    (D := 2) (ψ := (383278322261/10000000000000 : ℝ)) half_14_06_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_06_φ1, half_14_06_φ2, half_14_06_φ3, half_14_06_φ4, half_14_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_06_φ1, half_14_06_φ2, half_14_06_φ3, half_14_06_φ4, half_14_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_06_φ1, half_14_06_φ2, half_14_06_φ3, half_14_06_φ4, half_14_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_06 half_14_05
    (by simpa only [half_14_06_φ2, show (2:ℝ)*2=4 by norm_num] using half_14_06_hx2)
  exact h.weaken (by norm_num [half_14_06_φ1, half_14_06_φ2, half_14_06_φ3, half_14_06_φ4, half_14_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_06 : AdmissibleExponent 18 28 (167110789920607/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 12) (ψ := (397389437907/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_13_06
    (by simpa only [half_14_06_φ1] using half_14_06_hx1)
  exact admissibleExponent_mono h (by norm_num [half_14_06_φ1, half_14_06_φ2, half_14_06_φ3, half_14_06_φ4, half_14_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_15_06_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (204264323561/5000000000000 : ℝ)

def half_15_06_φ2 : Fin 2 → ℝ := Fin.snoc half_15_06_φ1 (393461015141/10000000000000 : ℝ)

def half_15_06_φ3 : Fin 3 → ℝ := Fin.snoc half_15_06_φ2 (1899566831/50000000000 : ℝ)

def half_15_06_φ4 : Fin 4 → ℝ := Fin.snoc half_15_06_φ3 (178067379409/5000000000000 : ℝ)

def half_15_06_φ5 : Fin 5 → ℝ := Fin.snoc half_15_06_φ4 (28764766511/1000000000000 : ℝ)

theorem half_15_06_hF2 : SourcePowerBound (paddedMoment 18 0 2 32 half_15_06_φ5) (76890041928059/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_15_06_φ5 (by norm_num [half_15_06_φ1, half_15_06_φ2, half_15_06_φ3, half_15_06_φ4, half_15_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_06_φ1, half_15_06_φ2, half_15_06_φ3, half_15_06_φ4, half_15_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_06_φ1, half_15_06_φ2, half_15_06_φ3, half_15_06_φ4, half_15_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_15_06_φ1, half_15_06_φ2, half_15_06_φ3, half_15_06_φ4, half_15_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_15_06_hx5 : SourcePowerBound (powerBoxCross 18 10 32 half_15_06_φ5) (23169257813833/2000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 10) (r := 2) (v := 13) (w := 14) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_15_06_φ5 (by norm_num [half_15_06_φ1, half_15_06_φ2, half_15_06_φ3, half_15_06_φ4, half_15_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_06_φ1, half_15_06_φ2, half_15_06_φ3, half_15_06_φ4, half_15_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_15_06_hF2 half_13_06 half_14_06
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_15_06_φ1, half_15_06_φ2, half_15_06_φ3, half_15_06_φ4, half_15_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_06_hx4 : SourcePowerBound (powerBoxCross 18 11 16 half_15_06_φ4) (6318574144483/500000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 11) (u := 9) (t := 12)
    (D := 16) (ψ := (28764766511/1000000000000 : ℝ)) half_15_06_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_06_φ1, half_15_06_φ2, half_15_06_φ3, half_15_06_φ4, half_15_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_06_φ1, half_15_06_φ2, half_15_06_φ3, half_15_06_φ4, half_15_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_06_φ1, half_15_06_φ2, half_15_06_φ3, half_15_06_φ4, half_15_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_06 half_12_06
    (by simpa only [half_15_06_φ5, show (2:ℝ)*16=32 by norm_num] using half_15_06_hx5)
  exact h.weaken (by norm_num [half_15_06_φ1, half_15_06_φ2, half_15_06_φ3, half_15_06_φ4, half_15_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_06_hx3 : SourcePowerBound (powerBoxCross 18 12 8 half_15_06_φ3) (3481813874837/250000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 12) (u := 10) (t := 13)
    (D := 8) (ψ := (178067379409/5000000000000 : ℝ)) half_15_06_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_06_φ1, half_15_06_φ2, half_15_06_φ3, half_15_06_φ4, half_15_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_06_φ1, half_15_06_φ2, half_15_06_φ3, half_15_06_φ4, half_15_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_06_φ1, half_15_06_φ2, half_15_06_φ3, half_15_06_φ4, half_15_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_06 half_13_06
    (by simpa only [half_15_06_φ4, show (2:ℝ)*8=16 by norm_num] using half_15_06_hx4)
  exact h.weaken (by norm_num [half_15_06_φ1, half_15_06_φ2, half_15_06_φ3, half_15_06_φ4, half_15_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_06_hx2 : SourcePowerBound (powerBoxCross 18 13 4 half_15_06_φ2) (77021353870331/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 13) (u := 11) (t := 14)
    (D := 4) (ψ := (1899566831/50000000000 : ℝ)) half_15_06_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_06_φ1, half_15_06_φ2, half_15_06_φ3, half_15_06_φ4, half_15_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_06_φ1, half_15_06_φ2, half_15_06_φ3, half_15_06_φ4, half_15_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_06_φ1, half_15_06_φ2, half_15_06_φ3, half_15_06_φ4, half_15_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_06 half_14_06
    (by simpa only [half_15_06_φ3, show (2:ℝ)*4=8 by norm_num] using half_15_06_hx3)
  exact h.weaken (by norm_num [half_15_06_φ1, half_15_06_φ2, half_15_06_φ3, half_15_06_φ4, half_15_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_06_hx1 : SourcePowerBound (powerBoxCross 18 14 2 half_15_06_φ1) (4267309101879/250000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 14) (u := 12) (t := 15)
    (D := 2) (ψ := (393461015141/10000000000000 : ℝ)) half_15_06_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_06_φ1, half_15_06_φ2, half_15_06_φ3, half_15_06_φ4, half_15_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_06_φ1, half_15_06_φ2, half_15_06_φ3, half_15_06_φ4, half_15_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_06_φ1, half_15_06_φ2, half_15_06_φ3, half_15_06_φ4, half_15_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_13_06 half_15_05
    (by simpa only [half_15_06_φ2, show (2:ℝ)*2=4 by norm_num] using half_15_06_hx2)
  exact h.weaken (by norm_num [half_15_06_φ1, half_15_06_φ2, half_15_06_φ3, half_15_06_φ4, half_15_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_06 : AdmissibleExponent 18 30 (90861318773727/5000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 13) (ψ := (204264323561/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_14_06
    (by simpa only [half_15_06_φ1] using half_15_06_hx1)
  exact admissibleExponent_mono h (by norm_num [half_15_06_φ1, half_15_06_φ2, half_15_06_φ3, half_15_06_φ4, half_15_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_16_06_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (420058125141/10000000000000 : ℝ)

def half_16_06_φ2 : Fin 2 → ℝ := Fin.snoc half_16_06_φ1 (100835089173/2500000000000 : ℝ)

def half_16_06_φ3 : Fin 3 → ℝ := Fin.snoc half_16_06_φ2 (391560825493/10000000000000 : ℝ)

def half_16_06_φ4 : Fin 4 → ℝ := Fin.snoc half_16_06_φ3 (9364754717/250000000000 : ℝ)

def half_16_06_φ5 : Fin 5 → ℝ := Fin.snoc half_16_06_φ4 (67476387031/2000000000000 : ℝ)

def half_16_06_φ6 : Fin 6 → ℝ := Fin.snoc half_16_06_φ5 (106155831813/5000000000000 : ℝ)

theorem half_16_06_hF2 : SourcePowerBound (paddedMoment 18 0 2 64 half_16_06_φ6) (90898602165863/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 6) (r := 0) (D := 64)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_16_06_φ6 (by norm_num [half_16_06_φ1, half_16_06_φ2, half_16_06_φ3, half_16_06_φ4, half_16_06_φ5, half_16_06_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_06_φ1, half_16_06_φ2, half_16_06_φ3, half_16_06_φ4, half_16_06_φ5, half_16_06_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_06_φ1, half_16_06_φ2, half_16_06_φ3, half_16_06_φ4, half_16_06_φ5, half_16_06_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_16_06_φ1, half_16_06_φ2, half_16_06_φ3, half_16_06_φ4, half_16_06_φ5, half_16_06_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_16_06_hx6 : SourcePowerBound (powerBoxCross 18 10 64 half_16_06_φ6) (115642048118107/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 10) (r := 2) (v := 13) (w := 14) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_16_06_φ6 (by norm_num [half_16_06_φ1, half_16_06_φ2, half_16_06_φ3, half_16_06_φ4, half_16_06_φ5, half_16_06_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_06_φ1, half_16_06_φ2, half_16_06_φ3, half_16_06_φ4, half_16_06_φ5, half_16_06_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_16_06_hF2 half_13_06 half_14_06
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_16_06_φ1, half_16_06_φ2, half_16_06_φ3, half_16_06_φ4, half_16_06_φ5, half_16_06_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_06_hx5 : SourcePowerBound (powerBoxCross 18 11 32 half_16_06_φ5) (124546257700391/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 5) (s := 11) (u := 9) (t := 12)
    (D := 32) (ψ := (106155831813/5000000000000 : ℝ)) half_16_06_φ5
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_06_φ1, half_16_06_φ2, half_16_06_φ3, half_16_06_φ4, half_16_06_φ5, half_16_06_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_06_φ1, half_16_06_φ2, half_16_06_φ3, half_16_06_φ4, half_16_06_φ5, half_16_06_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_06_φ1, half_16_06_φ2, half_16_06_φ3, half_16_06_φ4, half_16_06_φ5, half_16_06_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_06 half_12_06
    (by simpa only [half_16_06_φ6, show (2:ℝ)*32=64 by norm_num] using half_16_06_hx6)
  exact h.weaken (by norm_num [half_16_06_φ1, half_16_06_φ2, half_16_06_φ3, half_16_06_φ4, half_16_06_φ5, half_16_06_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_06_hx4 : SourcePowerBound (powerBoxCross 18 12 16 half_16_06_φ4) (34145636505097/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 12) (u := 10) (t := 13)
    (D := 16) (ψ := (67476387031/2000000000000 : ℝ)) half_16_06_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_06_φ1, half_16_06_φ2, half_16_06_φ3, half_16_06_φ4, half_16_06_φ5, half_16_06_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_06_φ1, half_16_06_φ2, half_16_06_φ3, half_16_06_φ4, half_16_06_φ5, half_16_06_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_06_φ1, half_16_06_φ2, half_16_06_φ3, half_16_06_φ4, half_16_06_φ5, half_16_06_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_06 half_13_06
    (by simpa only [half_16_06_φ5, show (2:ℝ)*16=32 by norm_num] using half_16_06_hx5)
  exact h.weaken (by norm_num [half_16_06_φ1, half_16_06_φ2, half_16_06_φ3, half_16_06_φ4, half_16_06_φ5, half_16_06_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_06_hx3 : SourcePowerBound (powerBoxCross 18 13 8 half_16_06_φ3) (30135132109923/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 13) (u := 11) (t := 14)
    (D := 8) (ψ := (9364754717/250000000000 : ℝ)) half_16_06_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_06_φ1, half_16_06_φ2, half_16_06_φ3, half_16_06_φ4, half_16_06_φ5, half_16_06_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_06_φ1, half_16_06_φ2, half_16_06_φ3, half_16_06_φ4, half_16_06_φ5, half_16_06_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_06_φ1, half_16_06_φ2, half_16_06_φ3, half_16_06_φ4, half_16_06_φ5, half_16_06_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_06 half_14_06
    (by simpa only [half_16_06_φ4, show (2:ℝ)*8=16 by norm_num] using half_16_06_hx4)
  exact h.weaken (by norm_num [half_16_06_φ1, half_16_06_φ2, half_16_06_φ3, half_16_06_φ4, half_16_06_φ5, half_16_06_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_06_hx2 : SourcePowerBound (powerBoxCross 18 14 4 half_16_06_φ2) (83306632539027/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 14) (u := 12) (t := 15)
    (D := 4) (ψ := (391560825493/10000000000000 : ℝ)) half_16_06_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_06_φ1, half_16_06_φ2, half_16_06_φ3, half_16_06_φ4, half_16_06_φ5, half_16_06_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_06_φ1, half_16_06_φ2, half_16_06_φ3, half_16_06_φ4, half_16_06_φ5, half_16_06_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_06_φ1, half_16_06_φ2, half_16_06_φ3, half_16_06_φ4, half_16_06_φ5, half_16_06_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_13_06 half_15_06
    (by simpa only [half_16_06_φ3, show (2:ℝ)*4=8 by norm_num] using half_16_06_hx3)
  exact h.weaken (by norm_num [half_16_06_φ1, half_16_06_φ2, half_16_06_φ3, half_16_06_φ4, half_16_06_φ5, half_16_06_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_06_hx1 : SourcePowerBound (powerBoxCross 18 15 2 half_16_06_φ1) (9225464431511/500000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 15) (u := 13) (t := 16)
    (D := 2) (ψ := (100835089173/2500000000000 : ℝ)) half_16_06_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_06_φ1, half_16_06_φ2, half_16_06_φ3, half_16_06_φ4, half_16_06_φ5, half_16_06_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_06_φ1, half_16_06_φ2, half_16_06_φ3, half_16_06_φ4, half_16_06_φ5, half_16_06_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_06_φ1, half_16_06_φ2, half_16_06_φ3, half_16_06_φ4, half_16_06_φ5, half_16_06_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_14_06 half_16_05
    (by simpa only [half_16_06_φ2, show (2:ℝ)*2=4 by norm_num] using half_16_06_hx2)
  exact h.weaken (by norm_num [half_16_06_φ1, half_16_06_φ2, half_16_06_φ3, half_16_06_φ4, half_16_06_φ5, half_16_06_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_06 : AdmissibleExponent 18 32 (196690974259309/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 14) (ψ := (420058125141/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_15_06
    (by simpa only [half_16_06_φ1] using half_16_06_hx1)
  exact admissibleExponent_mono h (by norm_num [half_16_06_φ1, half_16_06_φ2, half_16_06_φ3, half_16_06_φ4, half_16_06_φ5, half_16_06_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_17_06_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (43171720469/1000000000000 : ℝ)

def half_17_06_φ2 : Fin 2 → ℝ := Fin.snoc half_17_06_φ1 (412861645229/10000000000000 : ℝ)

def half_17_06_φ3 : Fin 3 → ℝ := Fin.snoc half_17_06_φ2 (803732873/20000000000 : ℝ)

def half_17_06_φ4 : Fin 4 → ℝ := Fin.snoc half_17_06_φ3 (194003040829/5000000000000 : ℝ)

def half_17_06_φ5 : Fin 5 → ℝ := Fin.snoc half_17_06_φ4 (181697708749/5000000000000 : ℝ)

def half_17_06_φ6 : Fin 6 → ℝ := Fin.snoc half_17_06_φ5 (296288661407/10000000000000 : ℝ)

theorem half_17_06_hF2 : SourcePowerBound (paddedMoment 18 0 2 64 half_17_06_φ6) (41499546101959/5000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 6) (r := 0) (D := 64)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_17_06_φ6 (by norm_num [half_17_06_φ1, half_17_06_φ2, half_17_06_φ3, half_17_06_φ4, half_17_06_φ5, half_17_06_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_06_φ1, half_17_06_φ2, half_17_06_φ3, half_17_06_φ4, half_17_06_φ5, half_17_06_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_06_φ1, half_17_06_φ2, half_17_06_φ3, half_17_06_φ4, half_17_06_φ5, half_17_06_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_17_06_φ1, half_17_06_φ2, half_17_06_φ3, half_17_06_φ4, half_17_06_φ5, half_17_06_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_17_06_hx6 : SourcePowerBound (powerBoxCross 18 11 64 half_17_06_φ6) (61479801210387/5000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 11) (r := 2) (v := 14) (w := 15) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_17_06_φ6 (by norm_num [half_17_06_φ1, half_17_06_φ2, half_17_06_φ3, half_17_06_φ4, half_17_06_φ5, half_17_06_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_06_φ1, half_17_06_φ2, half_17_06_φ3, half_17_06_φ4, half_17_06_φ5, half_17_06_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_17_06_hF2 half_14_06 half_15_06
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_17_06_φ1, half_17_06_φ2, half_17_06_φ3, half_17_06_φ4, half_17_06_φ5, half_17_06_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_06_hx5 : SourcePowerBound (powerBoxCross 18 12 32 half_17_06_φ5) (133766741288073/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 5) (s := 12) (u := 10) (t := 13)
    (D := 32) (ψ := (296288661407/10000000000000 : ℝ)) half_17_06_φ5
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_06_φ1, half_17_06_φ2, half_17_06_φ3, half_17_06_φ4, half_17_06_φ5, half_17_06_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_06_φ1, half_17_06_φ2, half_17_06_φ3, half_17_06_φ4, half_17_06_φ5, half_17_06_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_06_φ1, half_17_06_φ2, half_17_06_φ3, half_17_06_φ4, half_17_06_φ5, half_17_06_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_06 half_13_06
    (by simpa only [half_17_06_φ6, show (2:ℝ)*32=64 by norm_num] using half_17_06_hx6)
  exact h.weaken (by norm_num [half_17_06_φ1, half_17_06_φ2, half_17_06_φ3, half_17_06_φ4, half_17_06_φ5, half_17_06_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_06_hx4 : SourcePowerBound (powerBoxCross 18 13 16 half_17_06_φ4) (29413650663321/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 13) (u := 11) (t := 14)
    (D := 16) (ψ := (181697708749/5000000000000 : ℝ)) half_17_06_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_06_φ1, half_17_06_φ2, half_17_06_φ3, half_17_06_φ4, half_17_06_φ5, half_17_06_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_06_φ1, half_17_06_φ2, half_17_06_φ3, half_17_06_φ4, half_17_06_φ5, half_17_06_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_06_φ1, half_17_06_φ2, half_17_06_φ3, half_17_06_φ4, half_17_06_φ5, half_17_06_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_06 half_14_06
    (by simpa only [half_17_06_φ5, show (2:ℝ)*16=32 by norm_num] using half_17_06_hx5)
  exact h.weaken (by norm_num [half_17_06_φ1, half_17_06_φ2, half_17_06_φ3, half_17_06_φ4, half_17_06_φ5, half_17_06_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_06_hx3 : SourcePowerBound (powerBoxCross 18 14 8 half_17_06_φ3) (162325370267861/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 14) (u := 12) (t := 15)
    (D := 8) (ψ := (194003040829/5000000000000 : ℝ)) half_17_06_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_06_φ1, half_17_06_φ2, half_17_06_φ3, half_17_06_φ4, half_17_06_φ5, half_17_06_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_06_φ1, half_17_06_φ2, half_17_06_φ3, half_17_06_φ4, half_17_06_φ5, half_17_06_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_06_φ1, half_17_06_φ2, half_17_06_φ3, half_17_06_φ4, half_17_06_φ5, half_17_06_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_13_06 half_15_06
    (by simpa only [half_17_06_φ4, show (2:ℝ)*8=16 by norm_num] using half_17_06_hx4)
  exact h.weaken (by norm_num [half_17_06_φ1, half_17_06_φ2, half_17_06_φ3, half_17_06_φ4, half_17_06_φ5, half_17_06_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_06_hx2 : SourcePowerBound (powerBoxCross 18 15 4 half_17_06_φ2) (35889679418111/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 15) (u := 13) (t := 16)
    (D := 4) (ψ := (803732873/20000000000 : ℝ)) half_17_06_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_06_φ1, half_17_06_φ2, half_17_06_φ3, half_17_06_φ4, half_17_06_φ5, half_17_06_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_06_φ1, half_17_06_φ2, half_17_06_φ3, half_17_06_φ4, half_17_06_φ5, half_17_06_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_06_φ1, half_17_06_φ2, half_17_06_φ3, half_17_06_φ4, half_17_06_φ5, half_17_06_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_14_06 half_16_06
    (by simpa only [half_17_06_φ3, show (2:ℝ)*4=8 by norm_num] using half_17_06_hx3)
  exact h.weaken (by norm_num [half_17_06_φ1, half_17_06_φ2, half_17_06_φ3, half_17_06_φ4, half_17_06_φ5, half_17_06_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_06_hx1 : SourcePowerBound (powerBoxCross 18 16 2 half_17_06_φ1) (39726240740901/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 16) (u := 14) (t := 17)
    (D := 2) (ψ := (412861645229/10000000000000 : ℝ)) half_17_06_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_06_φ1, half_17_06_φ2, half_17_06_φ3, half_17_06_φ4, half_17_06_φ5, half_17_06_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_06_φ1, half_17_06_φ2, half_17_06_φ3, half_17_06_φ4, half_17_06_φ5, half_17_06_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_06_φ1, half_17_06_φ2, half_17_06_φ3, half_17_06_φ4, half_17_06_φ5, half_17_06_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_15_06 half_17_05
    (by simpa only [half_17_06_φ2, show (2:ℝ)*2=4 by norm_num] using half_17_06_hx2)
  exact h.weaken (by norm_num [half_17_06_φ1, half_17_06_φ2, half_17_06_φ3, half_17_06_φ4, half_17_06_φ5, half_17_06_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_06 : AdmissibleExponent 18 34 (42402887409979/2000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 15) (ψ := (43171720469/1000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_16_06
    (by simpa only [half_17_06_φ1] using half_17_06_hx1)
  exact admissibleExponent_mono h (by norm_num [half_17_06_φ1, half_17_06_φ2, half_17_06_φ3, half_17_06_φ4, half_17_06_φ5, half_17_06_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])


end Waring.SeedCompletionHigher18SimpleSeeds
