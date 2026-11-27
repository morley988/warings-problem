import Waring.SeedCompletionHigher18SimpleSeedsC02

noncomputable section
set_option maxHeartbeats 2000000
namespace Waring.SeedCompletionHigher18SimpleSeeds
open SmoothMoments FirstStageTransport SeedCompletionNaturalBox
open SeedCompletionSourceBounds SeedCompletionPaddedSource SeedCompletionGeneralTerminal
open PolicyCompletionMajorPowerRanges

def half_9_03_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (173161309861/5000000000000 : ℝ)

def half_9_03_φ2 : Fin 2 → ℝ := Fin.snoc half_9_03_φ1 (155283653111/5000000000000 : ℝ)

def half_9_03_φ3 : Fin 3 → ℝ := Fin.snoc half_9_03_φ2 (74241834043/5000000000000 : ℝ)

theorem half_9_03_hF2 : SourcePowerBound (paddedMoment 18 0 2 8 half_9_03_φ3) (6892594670447/1000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_03_φ3 (by norm_num [half_9_03_φ1, half_9_03_φ2, half_9_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_03_φ1, half_9_03_φ2, half_9_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_03_φ1, half_9_03_φ2, half_9_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_03_φ1, half_9_03_φ2, half_9_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_9_03_hF1 : SourcePowerBound (paddedMoment 18 0 1 8 half_9_03_φ3) (2630864890149/1000000000000 : ℝ) := by
  have h := padded_second_power (k := 18) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_03_φ3 (by norm_num [half_9_03_φ1, half_9_03_φ2, half_9_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_03_φ1, half_9_03_φ2, half_9_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_03_φ1, half_9_03_φ2, half_9_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_03_φ1, half_9_03_φ2, half_9_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_9_03_hx3 : SourcePowerBound (powerBoxCross 18 6 8 half_9_03_φ3) (76809188704973/10000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 18) (s := 6) (r := 1) (v := 2) (t := 10) (D := 8)
    (a := (3/10 : ℝ)) (b := (1/10 : ℝ)) (c := (3/5 : ℝ))
    (by norm_num) half_9_03_φ3 (by norm_num [half_9_03_φ1, half_9_03_φ2, half_9_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_03_φ1, half_9_03_φ2, half_9_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_9_03_hF1 half_9_03_hF2 half_10_02
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_9_03_φ1, half_9_03_φ2, half_9_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_9_03_hx2 : SourcePowerBound (powerBoxCross 18 7 4 half_9_03_φ2) (84194277075729/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 7) (u := 5) (t := 8)
    (D := 4) (ψ := (74241834043/5000000000000 : ℝ)) half_9_03_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_03_φ1, half_9_03_φ2, half_9_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_03_φ1, half_9_03_φ2, half_9_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_03_φ1, half_9_03_φ2, half_9_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_6 SeedCompletionEven18SecondSeeds.degree18_half_8
    (by simpa only [half_9_03_φ3, show (2:ℝ)*4=8 by norm_num] using half_9_03_hx3)
  exact h.weaken (by norm_num [half_9_03_φ1, half_9_03_φ2, half_9_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_9_03_hx1 : SourcePowerBound (powerBoxCross 18 8 2 half_9_03_φ1) (94155718561931/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 8) (u := 6) (t := 9)
    (D := 2) (ψ := (155283653111/5000000000000 : ℝ)) half_9_03_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_03_φ1, half_9_03_φ2, half_9_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_03_φ1, half_9_03_φ2, half_9_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_03_φ1, half_9_03_φ2, half_9_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_7 half_9_02
    (by simpa only [half_9_03_φ2, show (2:ℝ)*2=4 by norm_num] using half_9_03_hx2)
  exact h.weaken (by norm_num [half_9_03_φ1, half_9_03_φ2, half_9_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_9_03 : AdmissibleExponent 18 18 (99350557857761/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 7) (ψ := (173161309861/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_8
    (by simpa only [half_9_03_φ1] using half_9_03_hx1)
  exact admissibleExponent_mono h (by norm_num [half_9_03_φ1, half_9_03_φ2, half_9_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_10_03_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (89896902349/2500000000000 : ℝ)

def half_10_03_φ2 : Fin 2 → ℝ := Fin.snoc half_10_03_φ1 (330916036767/10000000000000 : ℝ)

def half_10_03_φ3 : Fin 3 → ℝ := Fin.snoc half_10_03_φ2 (118268467297/5000000000000 : ℝ)

theorem half_10_03_hF2 : SourcePowerBound (paddedMoment 18 0 2 8 half_10_03_φ3) (62720930381393/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_10_03_φ3 (by norm_num [half_10_03_φ1, half_10_03_φ2, half_10_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_03_φ1, half_10_03_φ2, half_10_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_03_φ1, half_10_03_φ2, half_10_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_10_03_φ1, half_10_03_φ2, half_10_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_10_03_hx3 : SourcePowerBound (powerBoxCross 18 7 8 half_10_03_φ3) (86251775294857/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 7) (r := 2) (v := 9) (w := 10) (D := 8)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_10_03_φ3 (by norm_num [half_10_03_φ1, half_10_03_φ2, half_10_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_03_φ1, half_10_03_φ2, half_10_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_10_03_hF2 half_9_03 half_10_02
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_10_03_φ1, half_10_03_φ2, half_10_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_03_hx2 : SourcePowerBound (powerBoxCross 18 8 4 half_10_03_φ2) (95039279536329/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 8) (u := 6) (t := 9)
    (D := 4) (ψ := (118268467297/5000000000000 : ℝ)) half_10_03_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_03_φ1, half_10_03_φ2, half_10_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_03_φ1, half_10_03_φ2, half_10_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_03_φ1, half_10_03_φ2, half_10_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_7 half_9_03
    (by simpa only [half_10_03_φ3, show (2:ℝ)*4=8 by norm_num] using half_10_03_hx3)
  exact h.weaken (by norm_num [half_10_03_φ1, half_10_03_φ2, half_10_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_03_hx1 : SourcePowerBound (powerBoxCross 18 9 2 half_10_03_φ1) (106137622507941/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 9) (u := 7) (t := 10)
    (D := 2) (ψ := (330916036767/10000000000000 : ℝ)) half_10_03_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_03_φ1, half_10_03_φ2, half_10_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_03_φ1, half_10_03_φ2, half_10_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_03_φ1, half_10_03_φ2, half_10_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_8 half_10_02
    (by simpa only [half_10_03_φ2, show (2:ℝ)*2=4 by norm_num] using half_10_03_hx2)
  exact h.weaken (by norm_num [half_10_03_φ1, half_10_03_φ2, half_10_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_03 : AdmissibleExponent 18 20 (112250611867673/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 8) (ψ := (89896902349/2500000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_9_03
    (by simpa only [half_10_03_φ1] using half_10_03_hx1)
  exact admissibleExponent_mono h (by norm_num [half_10_03_φ1, half_10_03_φ2, half_10_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_11_03_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (188951973229/5000000000000 : ℝ)

def half_11_03_φ2 : Fin 2 → ℝ := Fin.snoc half_11_03_φ1 (175969843519/5000000000000 : ℝ)

def half_11_03_φ3 : Fin 3 → ℝ := Fin.snoc half_11_03_φ2 (318509496361/10000000000000 : ℝ)

theorem half_11_03_hF2 : SourcePowerBound (paddedMoment 18 0 2 8 half_11_03_φ3) (56533990377293/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_11_03_φ3 (by norm_num [half_11_03_φ1, half_11_03_φ2, half_11_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_03_φ1, half_11_03_φ2, half_11_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_03_φ1, half_11_03_φ2, half_11_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_11_03_φ1, half_11_03_φ2, half_11_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_11_03_hx3 : SourcePowerBound (powerBoxCross 18 8 8 half_11_03_φ3) (9562581338179/1000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 8) (r := 2) (v := 10) (w := 11) (D := 8)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_11_03_φ3 (by norm_num [half_11_03_φ1, half_11_03_φ2, half_11_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_03_φ1, half_11_03_φ2, half_11_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_11_03_hF2 half_10_03 half_11_02
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_11_03_φ1, half_11_03_φ2, half_11_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_03_hx2 : SourcePowerBound (powerBoxCross 18 9 4 half_11_03_φ2) (106027093241341/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 9) (u := 7) (t := 10)
    (D := 4) (ψ := (318509496361/10000000000000 : ℝ)) half_11_03_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_03_φ1, half_11_03_φ2, half_11_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_03_φ1, half_11_03_φ2, half_11_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_03_φ1, half_11_03_φ2, half_11_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_8 half_10_03
    (by simpa only [half_11_03_φ3, show (2:ℝ)*4=8 by norm_num] using half_11_03_hx3)
  exact h.weaken (by norm_num [half_11_03_φ1, half_11_03_φ2, half_11_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_03_hx1 : SourcePowerBound (powerBoxCross 18 10 2 half_11_03_φ1) (11838652089243/1000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 10) (u := 8) (t := 11)
    (D := 2) (ψ := (175969843519/5000000000000 : ℝ)) half_11_03_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_03_φ1, half_11_03_φ2, half_11_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_03_φ1, half_11_03_φ2, half_11_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_03_φ1, half_11_03_φ2, half_11_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_03 half_11_02
    (by simpa only [half_11_03_φ2, show (2:ℝ)*2=4 by norm_num] using half_11_03_hx2)
  exact h.weaken (by norm_num [half_11_03_φ1, half_11_03_φ2, half_11_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_03 : AdmissibleExponent 18 22 (31391673968783/2500000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 9) (ψ := (188951973229/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_10_03
    (by simpa only [half_11_03_φ1] using half_11_03_hx1)
  exact admissibleExponent_mono h (by norm_num [half_11_03_φ1, half_11_03_φ2, half_11_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_12_03_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (15730180753/400000000000 : ℝ)

def half_12_03_φ2 : Fin 2 → ℝ := Fin.snoc half_12_03_φ1 (11347662631/312500000000 : ℝ)

def half_12_03_φ3 : Fin 3 → ℝ := Fin.snoc half_12_03_φ2 (333287490579/10000000000000 : ℝ)

def half_12_03_φ4 : Fin 4 → ℝ := Fin.snoc half_12_03_φ3 (114277238797/5000000000000 : ℝ)

theorem half_12_03_hF2 : SourcePowerBound (paddedMoment 18 0 2 16 half_12_03_φ4) (7277069374931/1000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_12_03_φ4 (by norm_num [half_12_03_φ1, half_12_03_φ2, half_12_03_φ3, half_12_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_03_φ1, half_12_03_φ2, half_12_03_φ3, half_12_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_03_φ1, half_12_03_φ2, half_12_03_φ3, half_12_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_12_03_φ1, half_12_03_φ2, half_12_03_φ3, half_12_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_12_03_hF1 : SourcePowerBound (paddedMoment 18 0 1 16 half_12_03_φ4) (2759023124977/1000000000000 : ℝ) := by
  have h := padded_second_power (k := 18) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_12_03_φ4 (by norm_num [half_12_03_φ1, half_12_03_φ2, half_12_03_φ3, half_12_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_03_φ1, half_12_03_φ2, half_12_03_φ3, half_12_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_03_φ1, half_12_03_φ2, half_12_03_φ3, half_12_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_12_03_φ1, half_12_03_φ2, half_12_03_φ3, half_12_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_12_03_hx4 : SourcePowerBound (powerBoxCross 18 8 16 half_12_03_φ4) (97075965749481/10000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 18) (s := 8) (r := 1) (v := 2) (t := 11) (D := 16)
    (a := (1/22 : ℝ)) (b := (5/22 : ℝ)) (c := (8/11 : ℝ))
    (by norm_num) half_12_03_φ4 (by norm_num [half_12_03_φ1, half_12_03_φ2, half_12_03_φ3, half_12_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_03_φ1, half_12_03_φ2, half_12_03_φ3, half_12_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_12_03_hF1 half_12_03_hF2 half_11_03
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_12_03_φ1, half_12_03_φ2, half_12_03_φ3, half_12_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_03_hx3 : SourcePowerBound (powerBoxCross 18 9 8 half_12_03_φ3) (26499871375513/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 9) (u := 7) (t := 10)
    (D := 8) (ψ := (114277238797/5000000000000 : ℝ)) half_12_03_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_03_φ1, half_12_03_φ2, half_12_03_φ3, half_12_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_03_φ1, half_12_03_φ2, half_12_03_φ3, half_12_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_03_φ1, half_12_03_φ2, half_12_03_φ3, half_12_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_8 half_10_03
    (by simpa only [half_12_03_φ4, show (2:ℝ)*8=16 by norm_num] using half_12_03_hx4)
  exact h.weaken (by norm_num [half_12_03_φ1, half_12_03_φ2, half_12_03_φ3, half_12_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_03_hx2 : SourcePowerBound (powerBoxCross 18 10 4 half_12_03_φ2) (1467975019757/125000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 10) (u := 8) (t := 11)
    (D := 4) (ψ := (333287490579/10000000000000 : ℝ)) half_12_03_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_03_φ1, half_12_03_φ2, half_12_03_φ3, half_12_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_03_φ1, half_12_03_φ2, half_12_03_φ3, half_12_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_03_φ1, half_12_03_φ2, half_12_03_φ3, half_12_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_03 half_11_03
    (by simpa only [half_12_03_φ3, show (2:ℝ)*4=8 by norm_num] using half_12_03_hx3)
  exact h.weaken (by norm_num [half_12_03_φ1, half_12_03_φ2, half_12_03_φ3, half_12_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_03_hx1 : SourcePowerBound (powerBoxCross 18 11 2 half_12_03_φ1) (131021983337289/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 11) (u := 9) (t := 12)
    (D := 2) (ψ := (11347662631/312500000000 : ℝ)) half_12_03_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_03_φ1, half_12_03_φ2, half_12_03_φ3, half_12_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_03_φ1, half_12_03_φ2, half_12_03_φ3, half_12_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_03_φ1, half_12_03_φ2, half_12_03_φ3, half_12_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_03 half_12_02
    (by simpa only [half_12_03_φ2, show (2:ℝ)*2=4 by norm_num] using half_12_03_hx2)
  exact h.weaken (by norm_num [half_12_03_φ1, half_12_03_φ2, half_12_03_φ3, half_12_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_03 : AdmissibleExponent 18 24 (69640164116307/5000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 10) (ψ := (15730180753/400000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_11_03
    (by simpa only [half_12_03_φ1] using half_12_03_hx1)
  exact admissibleExponent_mono h (by norm_num [half_12_03_φ1, half_12_03_φ2, half_12_03_φ3, half_12_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_13_03_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (411365438687/10000000000000 : ℝ)

def half_13_03_φ2 : Fin 2 → ℝ := Fin.snoc half_13_03_φ1 (374942168921/10000000000000 : ℝ)

def half_13_03_φ3 : Fin 3 → ℝ := Fin.snoc half_13_03_φ2 (71376663177/2000000000000 : ℝ)

def half_13_03_φ4 : Fin 4 → ℝ := Fin.snoc half_13_03_φ3 (307420545037/10000000000000 : ℝ)

theorem half_13_03_hF2 : SourcePowerBound (paddedMoment 18 0 2 16 half_13_03_φ4) (6601881510497/1000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_13_03_φ4 (by norm_num [half_13_03_φ1, half_13_03_φ2, half_13_03_φ3, half_13_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_03_φ1, half_13_03_φ2, half_13_03_φ3, half_13_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_03_φ1, half_13_03_φ2, half_13_03_φ3, half_13_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_13_03_φ1, half_13_03_φ2, half_13_03_φ3, half_13_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_13_03_hx4 : SourcePowerBound (powerBoxCross 18 9 16 half_13_03_φ4) (10581182684009/1000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 9) (r := 2) (v := 12) (w := 12) (D := 16)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_13_03_φ4 (by norm_num [half_13_03_φ1, half_13_03_φ2, half_13_03_φ3, half_13_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_03_φ1, half_13_03_φ2, half_13_03_φ3, half_13_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_13_03_hF2 half_12_03 half_12_03
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_13_03_φ1, half_13_03_φ2, half_13_03_φ3, half_13_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_03_hx3 : SourcePowerBound (powerBoxCross 18 10 8 half_13_03_φ3) (116407877789863/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 10) (u := 8) (t := 11)
    (D := 8) (ψ := (307420545037/10000000000000 : ℝ)) half_13_03_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_03_φ1, half_13_03_φ2, half_13_03_φ3, half_13_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_03_φ1, half_13_03_φ2, half_13_03_φ3, half_13_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_03_φ1, half_13_03_φ2, half_13_03_φ3, half_13_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_03 half_11_03
    (by simpa only [half_13_03_φ4, show (2:ℝ)*8=16 by norm_num] using half_13_03_hx4)
  exact h.weaken (by norm_num [half_13_03_φ1, half_13_03_φ2, half_13_03_φ3, half_13_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_03_hx2 : SourcePowerBound (powerBoxCross 18 11 4 half_13_03_φ2) (64537510381753/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 11) (u := 9) (t := 12)
    (D := 4) (ψ := (71376663177/2000000000000 : ℝ)) half_13_03_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_03_φ1, half_13_03_φ2, half_13_03_φ3, half_13_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_03_φ1, half_13_03_φ2, half_13_03_φ3, half_13_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_03_φ1, half_13_03_φ2, half_13_03_φ3, half_13_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_03 half_12_03
    (by simpa only [half_13_03_φ3, show (2:ℝ)*4=8 by norm_num] using half_13_03_hx3)
  exact h.weaken (by norm_num [half_13_03_φ1, half_13_03_φ2, half_13_03_φ3, half_13_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_03_hx1 : SourcePowerBound (powerBoxCross 18 12 2 half_13_03_φ1) (35990545584733/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 12) (u := 10) (t := 13)
    (D := 2) (ψ := (374942168921/10000000000000 : ℝ)) half_13_03_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_03_φ1, half_13_03_φ2, half_13_03_φ3, half_13_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_03_φ1, half_13_03_φ2, half_13_03_φ3, half_13_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_03_φ1, half_13_03_φ2, half_13_03_φ3, half_13_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_03 half_13_02
    (by simpa only [half_13_03_φ2, show (2:ℝ)*2=4 by norm_num] using half_13_03_hx2)
  exact h.weaken (by norm_num [half_13_03_φ1, half_13_03_φ2, half_13_03_φ3, half_13_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_03 : AdmissibleExponent 18 26 (153423587428733/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 11) (ψ := (411365438687/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_12_03
    (by simpa only [half_13_03_φ1] using half_13_03_hx1)
  exact admissibleExponent_mono h (by norm_num [half_13_03_φ1, half_13_03_φ2, half_13_03_φ3, half_13_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_14_03_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (53570897991/1250000000000 : ℝ)

def half_14_03_φ2 : Fin 2 → ℝ := Fin.snoc half_14_03_φ1 (192934650513/5000000000000 : ℝ)

def half_14_03_φ3 : Fin 3 → ℝ := Fin.snoc half_14_03_φ2 (370278092877/10000000000000 : ℝ)

def half_14_03_φ4 : Fin 4 → ℝ := Fin.snoc half_14_03_φ3 (339553493141/10000000000000 : ℝ)

def half_14_03_φ5 : Fin 5 → ℝ := Fin.snoc half_14_03_φ4 (116015054167/5000000000000 : ℝ)

theorem half_14_03_hF2 : SourcePowerBound (paddedMoment 18 0 2 32 half_14_03_φ5) (40214396427697/5000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_14_03_φ5 (by norm_num [half_14_03_φ1, half_14_03_φ2, half_14_03_φ3, half_14_03_φ4, half_14_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_03_φ1, half_14_03_φ2, half_14_03_φ3, half_14_03_φ4, half_14_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_03_φ1, half_14_03_φ2, half_14_03_φ3, half_14_03_φ4, half_14_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_14_03_φ1, half_14_03_φ2, half_14_03_φ3, half_14_03_φ4, half_14_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_14_03_hx5 : SourcePowerBound (powerBoxCross 18 9 32 half_14_03_φ5) (106221110371703/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 9) (r := 2) (v := 12) (w := 12) (D := 32)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_14_03_φ5 (by norm_num [half_14_03_φ1, half_14_03_φ2, half_14_03_φ3, half_14_03_φ4, half_14_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_03_φ1, half_14_03_φ2, half_14_03_φ3, half_14_03_φ4, half_14_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_14_03_hF2 half_12_03 half_12_03
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_14_03_φ1, half_14_03_φ2, half_14_03_φ3, half_14_03_φ4, half_14_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_03_hx4 : SourcePowerBound (powerBoxCross 18 10 16 half_14_03_φ4) (57670007588001/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 10) (u := 8) (t := 11)
    (D := 16) (ψ := (116015054167/5000000000000 : ℝ)) half_14_03_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_03_φ1, half_14_03_φ2, half_14_03_φ3, half_14_03_φ4, half_14_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_03_φ1, half_14_03_φ2, half_14_03_φ3, half_14_03_φ4, half_14_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_03_φ1, half_14_03_φ2, half_14_03_φ3, half_14_03_φ4, half_14_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_03 half_11_03
    (by simpa only [half_14_03_φ5, show (2:ℝ)*16=32 by norm_num] using half_14_03_hx5)
  exact h.weaken (by norm_num [half_14_03_φ1, half_14_03_φ2, half_14_03_φ3, half_14_03_φ4, half_14_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_03_hx3 : SourcePowerBound (powerBoxCross 18 11 8 half_14_03_φ3) (127215484214471/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 11) (u := 9) (t := 12)
    (D := 8) (ψ := (339553493141/10000000000000 : ℝ)) half_14_03_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_03_φ1, half_14_03_φ2, half_14_03_φ3, half_14_03_φ4, half_14_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_03_φ1, half_14_03_φ2, half_14_03_φ3, half_14_03_φ4, half_14_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_03_φ1, half_14_03_φ2, half_14_03_φ3, half_14_03_φ4, half_14_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_03 half_12_03
    (by simpa only [half_14_03_φ4, show (2:ℝ)*8=16 by norm_num] using half_14_03_hx4)
  exact h.weaken (by norm_num [half_14_03_φ1, half_14_03_φ2, half_14_03_φ3, half_14_03_φ4, half_14_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_03_hx2 : SourcePowerBound (powerBoxCross 18 12 4 half_14_03_φ2) (141037057311977/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 12) (u := 10) (t := 13)
    (D := 4) (ψ := (370278092877/10000000000000 : ℝ)) half_14_03_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_03_φ1, half_14_03_φ2, half_14_03_φ3, half_14_03_φ4, half_14_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_03_φ1, half_14_03_φ2, half_14_03_φ3, half_14_03_φ4, half_14_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_03_φ1, half_14_03_φ2, half_14_03_φ3, half_14_03_φ4, half_14_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_03 half_13_03
    (by simpa only [half_14_03_φ3, show (2:ℝ)*4=8 by norm_num] using half_14_03_hx3)
  exact h.weaken (by norm_num [half_14_03_φ1, half_14_03_φ2, half_14_03_φ3, half_14_03_φ4, half_14_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_03_hx1 : SourcePowerBound (powerBoxCross 18 13 2 half_14_03_φ1) (157276923131427/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 13) (u := 11) (t := 14)
    (D := 2) (ψ := (192934650513/5000000000000 : ℝ)) half_14_03_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_03_φ1, half_14_03_φ2, half_14_03_φ3, half_14_03_φ4, half_14_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_03_φ1, half_14_03_φ2, half_14_03_φ3, half_14_03_φ4, half_14_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_03_φ1, half_14_03_φ2, half_14_03_φ3, half_14_03_φ4, half_14_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_03 half_14_02
    (by simpa only [half_14_03_φ2, show (2:ℝ)*2=4 by norm_num] using half_14_03_hx2)
  exact h.weaken (by norm_num [half_14_03_φ1, half_14_03_φ2, half_14_03_φ3, half_14_03_φ4, half_14_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_03 : AdmissibleExponent 18 28 (167991102729627/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 12) (ψ := (53570897991/1250000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_13_03
    (by simpa only [half_14_03_φ1] using half_14_03_hx1)
  exact admissibleExponent_mono h (by norm_num [half_14_03_φ1, half_14_03_φ2, half_14_03_φ3, half_14_03_φ4, half_14_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_15_03_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (445599714391/10000000000000 : ℝ)

def half_15_03_φ2 : Fin 2 → ℝ := Fin.snoc half_15_03_φ1 (99030753621/2500000000000 : ℝ)

def half_15_03_φ3 : Fin 3 → ℝ := Fin.snoc half_15_03_φ2 (96105431773/2500000000000 : ℝ)

def half_15_03_φ4 : Fin 4 → ℝ := Fin.snoc half_15_03_φ3 (366632707117/10000000000000 : ℝ)

def half_15_03_φ5 : Fin 5 → ℝ := Fin.snoc half_15_03_φ4 (65289337293/2000000000000 : ℝ)

theorem half_15_03_hF2 : SourcePowerBound (paddedMoment 18 0 2 32 half_15_03_φ5) (72119583673001/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_15_03_φ5 (by norm_num [half_15_03_φ1, half_15_03_φ2, half_15_03_φ3, half_15_03_φ4, half_15_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_03_φ1, half_15_03_φ2, half_15_03_φ3, half_15_03_φ4, half_15_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_03_φ1, half_15_03_φ2, half_15_03_φ3, half_15_03_φ4, half_15_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_15_03_φ1, half_15_03_φ2, half_15_03_φ3, half_15_03_φ4, half_15_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_15_03_hx5 : SourcePowerBound (powerBoxCross 18 10 32 half_15_03_φ5) (56978220819713/5000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 10) (r := 2) (v := 13) (w := 14) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_15_03_φ5 (by norm_num [half_15_03_φ1, half_15_03_φ2, half_15_03_φ3, half_15_03_φ4, half_15_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_03_φ1, half_15_03_φ2, half_15_03_φ3, half_15_03_φ4, half_15_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_15_03_hF2 half_13_03 half_14_03
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_15_03_φ1, half_15_03_φ2, half_15_03_φ3, half_15_03_φ4, half_15_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_03_hx4 : SourcePowerBound (powerBoxCross 18 11 16 half_15_03_φ4) (31272224066859/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 11) (u := 9) (t := 12)
    (D := 16) (ψ := (65289337293/2000000000000 : ℝ)) half_15_03_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_03_φ1, half_15_03_φ2, half_15_03_φ3, half_15_03_φ4, half_15_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_03_φ1, half_15_03_φ2, half_15_03_φ3, half_15_03_φ4, half_15_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_03_φ1, half_15_03_φ2, half_15_03_φ3, half_15_03_φ4, half_15_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_03 half_12_03
    (by simpa only [half_15_03_φ5, show (2:ℝ)*16=32 by norm_num] using half_15_03_hx5)
  exact h.weaken (by norm_num [half_15_03_φ1, half_15_03_φ2, half_15_03_φ3, half_15_03_φ4, half_15_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_03_hx3 : SourcePowerBound (powerBoxCross 18 12 8 half_15_03_φ3) (138277683340079/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 12) (u := 10) (t := 13)
    (D := 8) (ψ := (366632707117/10000000000000 : ℝ)) half_15_03_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_03_φ1, half_15_03_φ2, half_15_03_φ3, half_15_03_φ4, half_15_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_03_φ1, half_15_03_φ2, half_15_03_φ3, half_15_03_φ4, half_15_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_03_φ1, half_15_03_φ2, half_15_03_φ3, half_15_03_φ4, half_15_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_03 half_13_03
    (by simpa only [half_15_03_φ4, show (2:ℝ)*8=16 by norm_num] using half_15_03_hx4)
  exact h.weaken (by norm_num [half_15_03_φ1, half_15_03_φ2, half_15_03_φ3, half_15_03_φ4, half_15_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_03_hx2 : SourcePowerBound (powerBoxCross 18 13 4 half_15_03_φ2) (153330503230159/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 13) (u := 11) (t := 14)
    (D := 4) (ψ := (96105431773/2500000000000 : ℝ)) half_15_03_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_03_φ1, half_15_03_φ2, half_15_03_φ3, half_15_03_φ4, half_15_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_03_φ1, half_15_03_φ2, half_15_03_φ3, half_15_03_φ4, half_15_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_03_φ1, half_15_03_φ2, half_15_03_φ3, half_15_03_φ4, half_15_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_03 half_14_03
    (by simpa only [half_15_03_φ3, show (2:ℝ)*4=8 by norm_num] using half_15_03_hx3)
  exact h.weaken (by norm_num [half_15_03_φ1, half_15_03_φ2, half_15_03_φ3, half_15_03_φ4, half_15_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_03_hx1 : SourcePowerBound (powerBoxCross 18 14 2 half_15_03_φ1) (170951023704371/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 14) (u := 12) (t := 15)
    (D := 2) (ψ := (99030753621/2500000000000 : ℝ)) half_15_03_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_03_φ1, half_15_03_φ2, half_15_03_φ3, half_15_03_φ4, half_15_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_03_φ1, half_15_03_φ2, half_15_03_φ3, half_15_03_φ4, half_15_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_03_φ1, half_15_03_φ2, half_15_03_φ3, half_15_03_φ4, half_15_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_13_03 half_15_02
    (by simpa only [half_15_03_φ2, show (2:ℝ)*2=4 by norm_num] using half_15_03_hx2)
  exact h.weaken (by norm_num [half_15_03_φ1, half_15_03_φ2, half_15_03_φ3, half_15_03_φ4, half_15_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_03 : AdmissibleExponent 18 30 (5718194249779/312500000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 13) (ψ := (445599714391/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_14_03
    (by simpa only [half_15_03_φ1] using half_15_03_hx1)
  exact admissibleExponent_mono h (by norm_num [half_15_03_φ1, half_15_03_φ2, half_15_03_φ3, half_15_03_φ4, half_15_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_16_03_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (461053976947/10000000000000 : ℝ)

def half_16_03_φ2 : Fin 2 → ℝ := Fin.snoc half_16_03_φ1 (81040530881/2000000000000 : ℝ)

def half_16_03_φ3 : Fin 3 → ℝ := Fin.snoc half_16_03_φ2 (394120232539/10000000000000 : ℝ)

def half_16_03_φ4 : Fin 4 → ℝ := Fin.snoc half_16_03_φ3 (379026704271/10000000000000 : ℝ)

def half_16_03_φ5 : Fin 5 → ℝ := Fin.snoc half_16_03_φ4 (347945856901/10000000000000 : ℝ)

def half_16_03_φ6 : Fin 6 → ℝ := Fin.snoc half_16_03_φ5 (125784879753/5000000000000 : ℝ)

theorem half_16_03_hF2 : SourcePowerBound (paddedMoment 18 0 2 64 half_16_03_φ6) (85815121586981/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 6) (r := 0) (D := 64)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_16_03_φ6 (by norm_num [half_16_03_φ1, half_16_03_φ2, half_16_03_φ3, half_16_03_φ4, half_16_03_φ5, half_16_03_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_03_φ1, half_16_03_φ2, half_16_03_φ3, half_16_03_φ4, half_16_03_φ5, half_16_03_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_03_φ1, half_16_03_φ2, half_16_03_φ3, half_16_03_φ4, half_16_03_φ5, half_16_03_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_16_03_φ1, half_16_03_φ2, half_16_03_φ3, half_16_03_φ4, half_16_03_φ5, half_16_03_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_16_03_hx6 : SourcePowerBound (powerBoxCross 18 10 64 half_16_03_φ6) (113585236562083/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 10) (r := 2) (v := 13) (w := 14) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_16_03_φ6 (by norm_num [half_16_03_φ1, half_16_03_φ2, half_16_03_φ3, half_16_03_φ4, half_16_03_φ5, half_16_03_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_03_φ1, half_16_03_φ2, half_16_03_φ3, half_16_03_φ4, half_16_03_φ5, half_16_03_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_16_03_hF2 half_13_03 half_14_03
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_16_03_φ1, half_16_03_φ2, half_16_03_φ3, half_16_03_φ4, half_16_03_φ5, half_16_03_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_03_hx5 : SourcePowerBound (powerBoxCross 18 11 32 half_16_03_φ5) (61545145493921/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 5) (s := 11) (u := 9) (t := 12)
    (D := 32) (ψ := (125784879753/5000000000000 : ℝ)) half_16_03_φ5
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_03_φ1, half_16_03_φ2, half_16_03_φ3, half_16_03_φ4, half_16_03_φ5, half_16_03_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_03_φ1, half_16_03_φ2, half_16_03_φ3, half_16_03_φ4, half_16_03_φ5, half_16_03_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_03_φ1, half_16_03_φ2, half_16_03_φ3, half_16_03_φ4, half_16_03_φ5, half_16_03_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_03 half_12_03
    (by simpa only [half_16_03_φ6, show (2:ℝ)*32=64 by norm_num] using half_16_03_hx6)
  exact h.weaken (by norm_num [half_16_03_φ1, half_16_03_φ2, half_16_03_φ3, half_16_03_φ4, half_16_03_φ5, half_16_03_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_03_hx4 : SourcePowerBound (powerBoxCross 18 12 16 half_16_03_φ4) (33849820385707/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 12) (u := 10) (t := 13)
    (D := 16) (ψ := (347945856901/10000000000000 : ℝ)) half_16_03_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_03_φ1, half_16_03_φ2, half_16_03_φ3, half_16_03_φ4, half_16_03_φ5, half_16_03_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_03_φ1, half_16_03_φ2, half_16_03_φ3, half_16_03_φ4, half_16_03_φ5, half_16_03_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_03_φ1, half_16_03_φ2, half_16_03_φ3, half_16_03_φ4, half_16_03_φ5, half_16_03_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_03 half_13_03
    (by simpa only [half_16_03_φ5, show (2:ℝ)*16=32 by norm_num] using half_16_03_hx5)
  exact h.weaken (by norm_num [half_16_03_φ1, half_16_03_φ2, half_16_03_φ3, half_16_03_φ4, half_16_03_φ5, half_16_03_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_03_hx3 : SourcePowerBound (powerBoxCross 18 13 8 half_16_03_φ3) (149754190931273/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 13) (u := 11) (t := 14)
    (D := 8) (ψ := (379026704271/10000000000000 : ℝ)) half_16_03_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_03_φ1, half_16_03_φ2, half_16_03_φ3, half_16_03_φ4, half_16_03_φ5, half_16_03_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_03_φ1, half_16_03_φ2, half_16_03_φ3, half_16_03_φ4, half_16_03_φ5, half_16_03_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_03_φ1, half_16_03_φ2, half_16_03_φ3, half_16_03_φ4, half_16_03_φ5, half_16_03_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_03 half_14_03
    (by simpa only [half_16_03_φ4, show (2:ℝ)*8=16 by norm_num] using half_16_03_hx4)
  exact h.weaken (by norm_num [half_16_03_φ1, half_16_03_φ2, half_16_03_φ3, half_16_03_φ4, half_16_03_φ5, half_16_03_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_03_hx2 : SourcePowerBound (powerBoxCross 18 14 4 half_16_03_φ2) (166006047101179/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 14) (u := 12) (t := 15)
    (D := 4) (ψ := (394120232539/10000000000000 : ℝ)) half_16_03_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_03_φ1, half_16_03_φ2, half_16_03_φ3, half_16_03_φ4, half_16_03_φ5, half_16_03_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_03_φ1, half_16_03_φ2, half_16_03_φ3, half_16_03_φ4, half_16_03_φ5, half_16_03_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_03_φ1, half_16_03_φ2, half_16_03_φ3, half_16_03_φ4, half_16_03_φ5, half_16_03_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_13_03 half_15_03
    (by simpa only [half_16_03_φ3, show (2:ℝ)*4=8 by norm_num] using half_16_03_hx3)
  exact h.weaken (by norm_num [half_16_03_φ1, half_16_03_φ2, half_16_03_φ3, half_16_03_φ4, half_16_03_φ5, half_16_03_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_03_hx1 : SourcePowerBound (powerBoxCross 18 15 2 half_16_03_φ1) (37001360426097/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 15) (u := 13) (t := 16)
    (D := 2) (ψ := (81040530881/2000000000000 : ℝ)) half_16_03_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_03_φ1, half_16_03_φ2, half_16_03_φ3, half_16_03_φ4, half_16_03_φ5, half_16_03_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_03_φ1, half_16_03_φ2, half_16_03_φ3, half_16_03_φ4, half_16_03_φ5, half_16_03_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_03_φ1, half_16_03_φ2, half_16_03_φ3, half_16_03_φ4, half_16_03_φ5, half_16_03_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_14_03 half_16_02
    (by simpa only [half_16_03_φ2, show (2:ℝ)*2=4 by norm_num] using half_16_03_hx2)
  exact h.weaken (by norm_num [half_16_03_φ1, half_16_03_φ2, half_16_03_φ3, half_16_03_φ4, half_16_03_φ5, half_16_03_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_03 : AdmissibleExponent 18 32 (49594341865487/2500000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 14) (ψ := (461053976947/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_15_03
    (by simpa only [half_16_03_φ1] using half_16_03_hx1)
  exact admissibleExponent_mono h (by norm_num [half_16_03_φ1, half_16_03_φ2, half_16_03_φ3, half_16_03_φ4, half_16_03_φ5, half_16_03_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_17_03_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (237718011149/5000000000000 : ℝ)

def half_17_03_φ2 : Fin 2 → ℝ := Fin.snoc half_17_03_φ1 (413862771261/10000000000000 : ℝ)

def half_17_03_φ3 : Fin 3 → ℝ := Fin.snoc half_17_03_φ2 (25282325439/625000000000 : ℝ)

def half_17_03_φ4 : Fin 4 → ℝ := Fin.snoc half_17_03_φ3 (196752131707/5000000000000 : ℝ)

def half_17_03_φ5 : Fin 5 → ℝ := Fin.snoc half_17_03_φ4 (4732793137/125000000000 : ℝ)

def half_17_03_φ6 : Fin 6 → ℝ := Fin.snoc half_17_03_φ5 (43543640577/1250000000000 : ℝ)

theorem half_17_03_hF2 : SourcePowerBound (paddedMoment 18 0 2 64 half_17_03_φ6) (76871065181777/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 6) (r := 0) (D := 64)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_17_03_φ6 (by norm_num [half_17_03_φ1, half_17_03_φ2, half_17_03_φ3, half_17_03_φ4, half_17_03_φ5, half_17_03_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_03_φ1, half_17_03_φ2, half_17_03_φ3, half_17_03_φ4, half_17_03_φ5, half_17_03_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_03_φ1, half_17_03_φ2, half_17_03_φ3, half_17_03_φ4, half_17_03_φ5, half_17_03_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_17_03_φ1, half_17_03_φ2, half_17_03_φ3, half_17_03_φ4, half_17_03_φ5, half_17_03_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_17_03_hx6 : SourcePowerBound (powerBoxCross 18 11 64 half_17_03_φ6) (60239262185733/5000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 11) (r := 2) (v := 14) (w := 15) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_17_03_φ6 (by norm_num [half_17_03_φ1, half_17_03_φ2, half_17_03_φ3, half_17_03_φ4, half_17_03_φ5, half_17_03_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_03_φ1, half_17_03_φ2, half_17_03_φ3, half_17_03_φ4, half_17_03_φ5, half_17_03_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_17_03_hF2 half_14_03 half_15_03
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_17_03_φ1, half_17_03_φ2, half_17_03_φ3, half_17_03_φ4, half_17_03_φ5, half_17_03_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_03_hx5 : SourcePowerBound (powerBoxCross 18 12 32 half_17_03_φ5) (66099987661353/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 5) (s := 12) (u := 10) (t := 13)
    (D := 32) (ψ := (43543640577/1250000000000 : ℝ)) half_17_03_φ5
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_03_φ1, half_17_03_φ2, half_17_03_φ3, half_17_03_φ4, half_17_03_φ5, half_17_03_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_03_φ1, half_17_03_φ2, half_17_03_φ3, half_17_03_φ4, half_17_03_φ5, half_17_03_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_03_φ1, half_17_03_φ2, half_17_03_φ3, half_17_03_φ4, half_17_03_φ5, half_17_03_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_03 half_13_03
    (by simpa only [half_17_03_φ6, show (2:ℝ)*32=64 by norm_num] using half_17_03_hx6)
  exact h.weaken (by norm_num [half_17_03_φ1, half_17_03_φ2, half_17_03_φ3, half_17_03_φ4, half_17_03_φ5, half_17_03_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_03_hx4 : SourcePowerBound (powerBoxCross 18 13 16 half_17_03_φ4) (145934746877887/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 13) (u := 11) (t := 14)
    (D := 16) (ψ := (4732793137/125000000000 : ℝ)) half_17_03_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_03_φ1, half_17_03_φ2, half_17_03_φ3, half_17_03_φ4, half_17_03_φ5, half_17_03_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_03_φ1, half_17_03_φ2, half_17_03_φ3, half_17_03_φ4, half_17_03_φ5, half_17_03_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_03_φ1, half_17_03_φ2, half_17_03_φ3, half_17_03_φ4, half_17_03_φ5, half_17_03_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_03 half_14_03
    (by simpa only [half_17_03_φ5, show (2:ℝ)*16=32 by norm_num] using half_17_03_hx5)
  exact h.weaken (by norm_num [half_17_03_φ1, half_17_03_φ2, half_17_03_φ3, half_17_03_φ4, half_17_03_φ5, half_17_03_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_03_hx3 : SourcePowerBound (powerBoxCross 18 14 8 half_17_03_φ3) (80771291389719/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 14) (u := 12) (t := 15)
    (D := 8) (ψ := (196752131707/5000000000000 : ℝ)) half_17_03_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_03_φ1, half_17_03_φ2, half_17_03_φ3, half_17_03_φ4, half_17_03_φ5, half_17_03_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_03_φ1, half_17_03_φ2, half_17_03_φ3, half_17_03_φ4, half_17_03_φ5, half_17_03_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_03_φ1, half_17_03_φ2, half_17_03_φ3, half_17_03_φ4, half_17_03_φ5, half_17_03_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_13_03 half_15_03
    (by simpa only [half_17_03_φ4, show (2:ℝ)*8=16 by norm_num] using half_17_03_hx4)
  exact h.weaken (by norm_num [half_17_03_φ1, half_17_03_φ2, half_17_03_φ3, half_17_03_φ4, half_17_03_φ5, half_17_03_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_03_hx2 : SourcePowerBound (powerBoxCross 18 15 4 half_17_03_φ2) (895205399963/50000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 15) (u := 13) (t := 16)
    (D := 4) (ψ := (25282325439/625000000000 : ℝ)) half_17_03_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_03_φ1, half_17_03_φ2, half_17_03_φ3, half_17_03_φ4, half_17_03_φ5, half_17_03_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_03_φ1, half_17_03_φ2, half_17_03_φ3, half_17_03_φ4, half_17_03_φ5, half_17_03_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_03_φ1, half_17_03_φ2, half_17_03_φ3, half_17_03_φ4, half_17_03_φ5, half_17_03_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_14_03 half_16_03
    (by simpa only [half_17_03_φ3, show (2:ℝ)*4=8 by norm_num] using half_17_03_hx3)
  exact h.weaken (by norm_num [half_17_03_φ1, half_17_03_φ2, half_17_03_φ3, half_17_03_φ4, half_17_03_φ5, half_17_03_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_03_hx1 : SourcePowerBound (powerBoxCross 18 16 2 half_17_03_φ1) (49855307208563/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 16) (u := 14) (t := 17)
    (D := 2) (ψ := (413862771261/10000000000000 : ℝ)) half_17_03_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_03_φ1, half_17_03_φ2, half_17_03_φ3, half_17_03_φ4, half_17_03_φ5, half_17_03_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_03_φ1, half_17_03_φ2, half_17_03_φ3, half_17_03_φ4, half_17_03_φ5, half_17_03_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_03_φ1, half_17_03_φ2, half_17_03_φ3, half_17_03_φ4, half_17_03_φ5, half_17_03_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_15_03 half_17_02
    (by simpa only [half_17_03_φ2, show (2:ℝ)*2=4 by norm_num] using half_17_03_hx2)
  exact h.weaken (by norm_num [half_17_03_φ1, half_17_03_φ2, half_17_03_φ3, half_17_03_φ4, half_17_03_φ5, half_17_03_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_03 : AdmissibleExponent 18 34 (21415974552549/1000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 15) (ψ := (237718011149/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_16_03
    (by simpa only [half_17_03_φ1] using half_17_03_hx1)
  exact admissibleExponent_mono h (by norm_num [half_17_03_φ1, half_17_03_φ2, half_17_03_φ3, half_17_03_φ4, half_17_03_φ5, half_17_03_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])


end Waring.SeedCompletionHigher18SimpleSeeds
