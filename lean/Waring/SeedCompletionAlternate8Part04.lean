import Waring.SeedCompletionAlternate8Part03
import Waring.SeedCompletionHigher8SimpleSeeds
import Waring.SeedCompletionAlternate8Data
import Waring.SeedCompletionPaddedGeneralPower
import Waring.SeedCompletionGeneralTerminal
import Waring.SeedCompletionNaturalChronological
import Waring.SmoothInterpolation

/-! Exact alternate degree-eight seed replay. Every source estimate is actual;
the finite rational choices and all upward roundings are kernel checked. -/
noncomputable section
set_option maxHeartbeats 2000000
namespace Waring.SeedCompletionAlternate8Seeds
open SmoothMoments FirstStageTransport SeedCompletionNaturalBox
open SeedCompletionSourceBounds SeedCompletionPaddedSource SeedCompletionGeneralTerminal
open PolicyCompletionMajorPowerRanges SeedCompletionDivisorPowerScales
open PolicyCompletionSharpResidualSource

theorem half_12_08_hx3 : SourcePowerBound (powerBoxCross 8 9 8 half_12_08_φ3) (18880298139/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 9) (u := 7) (t := 10)
    (D := 8) (ψ := (421012417/5000000000 : ℝ)) half_12_08_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_08_φ1, half_12_08_φ2, half_12_08_φ3, half_12_08_φ4, half_12_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_08_φ1, half_12_08_φ2, half_12_08_φ3, half_12_08_φ4, half_12_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_08_φ1, half_12_08_φ2, half_12_08_φ3, half_12_08_φ4, half_12_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_8) (half_10_08)
    (by simpa only [half_12_08_φ4, show (2:ℝ)*8=16 by norm_num] using half_12_08_hx4)
  exact h.weaken (by norm_num [half_12_08_φ1, half_12_08_φ2, half_12_08_φ3, half_12_08_φ4, half_12_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_08_hx2 : SourcePowerBound (powerBoxCross 8 10 4 half_12_08_φ2) (116189996059/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 10) (u := 8) (t := 11)
    (D := 4) (ψ := (977066677/10000000000 : ℝ)) half_12_08_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_08_φ1, half_12_08_φ2, half_12_08_φ3, half_12_08_φ4, half_12_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_08_φ1, half_12_08_φ2, half_12_08_φ3, half_12_08_φ4, half_12_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_08_φ1, half_12_08_φ2, half_12_08_φ3, half_12_08_φ4, half_12_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_9) (half_11_08)
    (by simpa only [half_12_08_φ3, show (2:ℝ)*4=8 by norm_num] using half_12_08_hx3)
  exact h.weaken (by norm_num [half_12_08_φ1, half_12_08_φ2, half_12_08_φ3, half_12_08_φ4, half_12_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_08_hx1 : SourcePowerBound (powerBoxCross 8 11 2 half_12_08_φ1) (14331062207/1000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 11) (u := 9) (t := 12)
    (D := 2) (ψ := (1055616851/10000000000 : ℝ)) half_12_08_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_08_φ1, half_12_08_φ2, half_12_08_φ3, half_12_08_φ4, half_12_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_08_φ1, half_12_08_φ2, half_12_08_φ3, half_12_08_φ4, half_12_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_08_φ1, half_12_08_φ2, half_12_08_φ3, half_12_08_φ4, half_12_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_10_08) (half_12_07)
    (by simpa only [half_12_08_φ2, show (2:ℝ)*2=4 by norm_num] using half_12_08_hx2)
  exact h.weaken (by norm_num [half_12_08_φ1, half_12_08_φ2, half_12_08_φ3, half_12_08_φ4, half_12_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_08 : AdmissibleExponent 8 24 (83283276601/5000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 10) (ψ := (276856323/2500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_11_08)
    (by simpa only [half_12_08_φ1] using half_12_08_hx1)
  exact admissibleExponent_mono h (by norm_num [half_12_08_φ1, half_12_08_φ2, half_12_08_φ3, half_12_08_φ4, half_12_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_13_08_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (568168547/5000000000 : ℝ)

def half_13_08_φ2 : Fin 2 → ℝ := Fin.snoc half_13_08_φ1 (272563387/2500000000 : ℝ)

def half_13_08_φ3 : Fin 3 → ℝ := Fin.snoc half_13_08_φ2 (1024907391/10000000000 : ℝ)

def half_13_08_φ4 : Fin 4 → ℝ := Fin.snoc half_13_08_φ3 (912474619/10000000000 : ℝ)

def half_13_08_φ5 : Fin 5 → ℝ := Fin.snoc half_13_08_φ4 (342524881/5000000000 : ℝ)

theorem half_13_08_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_13_08_φ5) (34085264653/5000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_13_08_φ5 (by norm_num [half_13_08_φ1, half_13_08_φ2, half_13_08_φ3, half_13_08_φ4, half_13_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_08_φ1, half_13_08_φ2, half_13_08_φ3, half_13_08_φ4, half_13_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_08_φ1, half_13_08_φ2, half_13_08_φ3, half_13_08_φ4, half_13_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_13_08_φ1, half_13_08_φ2, half_13_08_φ3, half_13_08_φ4, half_13_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_13_08_φ1, half_13_08_φ2, half_13_08_φ3, half_13_08_φ4, half_13_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_13_08_hx5 : SourcePowerBound (powerBoxCross 8 8 32 half_13_08_φ5) (36118801549/5000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 8) (r := 2) (v := 10) (w := 11) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_13_08_φ5 (by norm_num [half_13_08_φ1, half_13_08_φ2, half_13_08_φ3, half_13_08_φ4, half_13_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_08_φ1, half_13_08_φ2, half_13_08_φ3, half_13_08_φ4, half_13_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_13_08_hF2 (half_10_08) (half_11_08)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_13_08_φ1, half_13_08_φ2, half_13_08_φ3, half_13_08_φ4, half_13_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_08_hx4 : SourcePowerBound (powerBoxCross 8 9 16 half_13_08_φ4) (42495743341/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 9) (u := 7) (t := 10)
    (D := 16) (ψ := (342524881/5000000000 : ℝ)) half_13_08_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_08_φ1, half_13_08_φ2, half_13_08_φ3, half_13_08_φ4, half_13_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_08_φ1, half_13_08_φ2, half_13_08_φ3, half_13_08_φ4, half_13_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_08_φ1, half_13_08_φ2, half_13_08_φ3, half_13_08_φ4, half_13_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_8) (half_10_08)
    (by simpa only [half_13_08_φ5, show (2:ℝ)*16=32 by norm_num] using half_13_08_hx5)
  exact h.weaken (by norm_num [half_13_08_φ1, half_13_08_φ2, half_13_08_φ3, half_13_08_φ4, half_13_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_08_hx3 : SourcePowerBound (powerBoxCross 8 10 8 half_13_08_φ3) (4161419801/400000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 10) (u := 8) (t := 11)
    (D := 8) (ψ := (912474619/10000000000 : ℝ)) half_13_08_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_08_φ1, half_13_08_φ2, half_13_08_φ3, half_13_08_φ4, half_13_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_08_φ1, half_13_08_φ2, half_13_08_φ3, half_13_08_φ4, half_13_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_08_φ1, half_13_08_φ2, half_13_08_φ3, half_13_08_φ4, half_13_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_9) (half_11_08)
    (by simpa only [half_13_08_φ4, show (2:ℝ)*8=16 by norm_num] using half_13_08_hx4)
  exact h.weaken (by norm_num [half_13_08_φ1, half_13_08_φ2, half_13_08_φ3, half_13_08_φ4, half_13_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_08_hx2 : SourcePowerBound (powerBoxCross 8 11 4 half_13_08_φ2) (2574016013/200000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 11) (u := 9) (t := 12)
    (D := 4) (ψ := (1024907391/10000000000 : ℝ)) half_13_08_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_08_φ1, half_13_08_φ2, half_13_08_φ3, half_13_08_φ4, half_13_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_08_φ1, half_13_08_φ2, half_13_08_φ3, half_13_08_φ4, half_13_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_08_φ1, half_13_08_φ2, half_13_08_φ3, half_13_08_φ4, half_13_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_10_08) (half_12_08)
    (by simpa only [half_13_08_φ3, show (2:ℝ)*4=8 by norm_num] using half_13_08_hx3)
  exact h.weaken (by norm_num [half_13_08_φ1, half_13_08_φ2, half_13_08_φ3, half_13_08_φ4, half_13_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_08_hx1 : SourcePowerBound (powerBoxCross 8 12 2 half_13_08_φ1) (79387657499/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 12) (u := 10) (t := 13)
    (D := 2) (ψ := (272563387/2500000000 : ℝ)) half_13_08_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_08_φ1, half_13_08_φ2, half_13_08_φ3, half_13_08_φ4, half_13_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_08_φ1, half_13_08_φ2, half_13_08_φ3, half_13_08_φ4, half_13_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_08_φ1, half_13_08_φ2, half_13_08_φ3, half_13_08_φ4, half_13_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_11_08) (half_13_07)
    (by simpa only [half_13_08_φ2, show (2:ℝ)*2=4 by norm_num] using half_13_08_hx2)
  exact h.weaken (by norm_num [half_13_08_φ1, half_13_08_φ2, half_13_08_φ3, half_13_08_φ4, half_13_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_08 : AdmissibleExponent 8 26 (36115443/1953125 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 11) (ψ := (568168547/5000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_12_08)
    (by simpa only [half_13_08_φ1] using half_13_08_hx1)
  exact admissibleExponent_mono h (by norm_num [half_13_08_φ1, half_13_08_φ2, half_13_08_φ3, half_13_08_φ4, half_13_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_14_08_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1163090631/10000000000 : ℝ)

def half_14_08_φ2 : Fin 2 → ℝ := Fin.snoc half_14_08_φ1 (561837373/5000000000 : ℝ)

def half_14_08_φ3 : Fin 3 → ℝ := Fin.snoc half_14_08_φ2 (1070418893/10000000000 : ℝ)

def half_14_08_φ4 : Fin 4 → ℝ := Fin.snoc half_14_08_φ3 (37958947/400000000 : ℝ)

def half_14_08_φ5 : Fin 5 → ℝ := Fin.snoc half_14_08_φ4 (813406007/10000000000 : ℝ)

theorem half_14_08_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_14_08_φ5) (3905572313/625000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_14_08_φ5 (by norm_num [half_14_08_φ1, half_14_08_φ2, half_14_08_φ3, half_14_08_φ4, half_14_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_08_φ1, half_14_08_φ2, half_14_08_φ3, half_14_08_φ4, half_14_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_08_φ1, half_14_08_φ2, half_14_08_φ3, half_14_08_φ4, half_14_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_14_08_φ1, half_14_08_φ2, half_14_08_φ3, half_14_08_φ4, half_14_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_14_08_φ1, half_14_08_φ2, half_14_08_φ3, half_14_08_φ4, half_14_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_14_08_hx5 : SourcePowerBound (powerBoxCross 8 9 32 half_14_08_φ5) (1531821901/200000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 9) (r := 2) (v := 0) (w := 12) (D := 32)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_14_08_φ5 (by norm_num [half_14_08_φ1, half_14_08_φ2, half_14_08_φ3, half_14_08_φ4, half_14_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_08_φ1, half_14_08_φ2, half_14_08_φ3, half_14_08_φ4, half_14_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_14_08_hF2 (admissibleExponent_zero 8) (half_12_08)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_14_08_φ1, half_14_08_φ2, half_14_08_φ3, half_14_08_φ4, half_14_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_08_hx4 : SourcePowerBound (powerBoxCross 8 10 16 half_14_08_φ4) (46231126323/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 10) (u := 8) (t := 11)
    (D := 16) (ψ := (813406007/10000000000 : ℝ)) half_14_08_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_08_φ1, half_14_08_φ2, half_14_08_φ3, half_14_08_φ4, half_14_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_08_φ1, half_14_08_φ2, half_14_08_φ3, half_14_08_φ4, half_14_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_08_φ1, half_14_08_φ2, half_14_08_φ3, half_14_08_φ4, half_14_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_9) (half_11_08)
    (by simpa only [half_14_08_φ5, show (2:ℝ)*16=32 by norm_num] using half_14_08_hx5)
  exact h.weaken (by norm_num [half_14_08_φ1, half_14_08_φ2, half_14_08_φ3, half_14_08_φ4, half_14_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_08_hx3 : SourcePowerBound (powerBoxCross 8 11 8 half_14_08_φ3) (28454944319/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 11) (u := 9) (t := 12)
    (D := 8) (ψ := (37958947/400000000 : ℝ)) half_14_08_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_08_φ1, half_14_08_φ2, half_14_08_φ3, half_14_08_φ4, half_14_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_08_φ1, half_14_08_φ2, half_14_08_φ3, half_14_08_φ4, half_14_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_08_φ1, half_14_08_φ2, half_14_08_φ3, half_14_08_φ4, half_14_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_10_08) (half_12_08)
    (by simpa only [half_14_08_φ4, show (2:ℝ)*8=16 by norm_num] using half_14_08_hx4)
  exact h.weaken (by norm_num [half_14_08_φ1, half_14_08_φ2, half_14_08_φ3, half_14_08_φ4, half_14_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_08_hx2 : SourcePowerBound (powerBoxCross 8 12 4 half_14_08_φ2) (141458730851/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 12) (u := 10) (t := 13)
    (D := 4) (ψ := (1070418893/10000000000 : ℝ)) half_14_08_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_08_φ1, half_14_08_φ2, half_14_08_φ3, half_14_08_φ4, half_14_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_08_φ1, half_14_08_φ2, half_14_08_φ3, half_14_08_φ4, half_14_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_08_φ1, half_14_08_φ2, half_14_08_φ3, half_14_08_φ4, half_14_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_11_08) (half_13_08)
    (by simpa only [half_14_08_φ3, show (2:ℝ)*4=8 by norm_num] using half_14_08_hx3)
  exact h.weaken (by norm_num [half_14_08_φ1, half_14_08_φ2, half_14_08_φ3, half_14_08_φ4, half_14_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_08_hx1 : SourcePowerBound (powerBoxCross 8 13 2 half_14_08_φ1) (174567325703/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 13) (u := 11) (t := 14)
    (D := 2) (ψ := (561837373/5000000000 : ℝ)) half_14_08_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_08_φ1, half_14_08_φ2, half_14_08_φ3, half_14_08_φ4, half_14_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_08_φ1, half_14_08_φ2, half_14_08_φ3, half_14_08_φ4, half_14_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_08_φ1, half_14_08_φ2, half_14_08_φ3, half_14_08_φ4, half_14_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_12_08) (half_14_07)
    (by simpa only [half_14_08_φ2, show (2:ℝ)*2=4 by norm_num] using half_14_08_hx2)
  exact h.weaken (by norm_num [half_14_08_φ1, half_14_08_φ2, half_14_08_φ3, half_14_08_φ4, half_14_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_08 : AdmissibleExponent 8 28 (101822295739/5000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 12) (ψ := (1163090631/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_13_08)
    (by simpa only [half_14_08_φ1] using half_14_08_hx1)
  exact admissibleExponent_mono h (by norm_num [half_14_08_φ1, half_14_08_φ2, half_14_08_φ3, half_14_08_φ4, half_14_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_15_08_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1187468759/10000000000 : ℝ)

def half_15_08_φ2 : Fin 2 → ℝ := Fin.snoc half_15_08_φ1 (115702957/1000000000 : ℝ)

def half_15_08_φ3 : Fin 3 → ℝ := Fin.snoc half_15_08_φ2 (218728619/2000000000 : ℝ)

def half_15_08_φ4 : Fin 4 → ℝ := Fin.snoc half_15_08_φ3 (937408367/10000000000 : ℝ)

def half_15_08_φ5 : Fin 5 → ℝ := Fin.snoc half_15_08_φ4 (401746443/5000000000 : ℝ)

theorem half_15_08_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_15_08_φ5) (61240103783/10000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_15_08_φ5 (by norm_num [half_15_08_φ1, half_15_08_φ2, half_15_08_φ3, half_15_08_φ4, half_15_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_08_φ1, half_15_08_φ2, half_15_08_φ3, half_15_08_φ4, half_15_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_08_φ1, half_15_08_φ2, half_15_08_φ3, half_15_08_φ4, half_15_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_15_08_φ1, half_15_08_φ2, half_15_08_φ3, half_15_08_φ4, half_15_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_15_08_φ1, half_15_08_φ2, half_15_08_φ3, half_15_08_φ4, half_15_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_15_08_hx5 : SourcePowerBound (powerBoxCross 8 10 32 half_15_08_φ5) (21106622867/2500000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 10) (r := 2) (v := 13) (w := 14) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_15_08_φ5 (by norm_num [half_15_08_φ1, half_15_08_φ2, half_15_08_φ3, half_15_08_φ4, half_15_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_08_φ1, half_15_08_φ2, half_15_08_φ3, half_15_08_φ4, half_15_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_15_08_hF2 (half_13_08) (half_14_08)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_15_08_φ1, half_15_08_φ2, half_15_08_φ3, half_15_08_φ4, half_15_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_08_hx4 : SourcePowerBound (powerBoxCross 8 11 16 half_15_08_φ4) (101374268131/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 11) (u := 9) (t := 12)
    (D := 16) (ψ := (401746443/5000000000 : ℝ)) half_15_08_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_08_φ1, half_15_08_φ2, half_15_08_φ3, half_15_08_φ4, half_15_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_08_φ1, half_15_08_φ2, half_15_08_φ3, half_15_08_φ4, half_15_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_08_φ1, half_15_08_φ2, half_15_08_φ3, half_15_08_φ4, half_15_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_10_08) (half_12_08)
    (by simpa only [half_15_08_φ5, show (2:ℝ)*16=32 by norm_num] using half_15_08_hx5)
  exact h.weaken (by norm_num [half_15_08_φ1, half_15_08_φ2, half_15_08_φ3, half_15_08_φ4, half_15_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_08_hx3 : SourcePowerBound (powerBoxCross 8 12 8 half_15_08_φ3) (15520555107/1250000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 12) (u := 10) (t := 13)
    (D := 8) (ψ := (937408367/10000000000 : ℝ)) half_15_08_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_08_φ1, half_15_08_φ2, half_15_08_φ3, half_15_08_φ4, half_15_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_08_φ1, half_15_08_φ2, half_15_08_φ3, half_15_08_φ4, half_15_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_08_φ1, half_15_08_φ2, half_15_08_φ3, half_15_08_φ4, half_15_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_11_08) (half_13_08)
    (by simpa only [half_15_08_φ4, show (2:ℝ)*8=16 by norm_num] using half_15_08_hx4)
  exact h.weaken (by norm_num [half_15_08_φ1, half_15_08_φ2, half_15_08_φ3, half_15_08_φ4, half_15_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_08_hx2 : SourcePowerBound (powerBoxCross 8 13 4 half_15_08_φ2) (154403447387/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 13) (u := 11) (t := 14)
    (D := 4) (ψ := (218728619/2000000000 : ℝ)) half_15_08_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_08_φ1, half_15_08_φ2, half_15_08_φ3, half_15_08_φ4, half_15_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_08_φ1, half_15_08_φ2, half_15_08_φ3, half_15_08_φ4, half_15_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_08_φ1, half_15_08_φ2, half_15_08_φ3, half_15_08_φ4, half_15_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_12_08) (half_14_08)
    (by simpa only [half_15_08_φ3, show (2:ℝ)*4=8 by norm_num] using half_15_08_hx3)
  exact h.weaken (by norm_num [half_15_08_φ1, half_15_08_φ2, half_15_08_φ3, half_15_08_φ4, half_15_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_08_hx1 : SourcePowerBound (powerBoxCross 8 14 2 half_15_08_φ1) (190649901207/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 14) (u := 12) (t := 15)
    (D := 2) (ψ := (115702957/1000000000 : ℝ)) half_15_08_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_08_φ1, half_15_08_φ2, half_15_08_φ3, half_15_08_φ4, half_15_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_08_φ1, half_15_08_φ2, half_15_08_φ3, half_15_08_φ4, half_15_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_08_φ1, half_15_08_φ2, half_15_08_φ3, half_15_08_φ4, half_15_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_13_08) (half_15_07)
    (by simpa only [half_15_08_φ2, show (2:ℝ)*2=4 by norm_num] using half_15_08_hx2)
  exact h.weaken (by norm_num [half_15_08_φ1, half_15_08_φ2, half_15_08_φ3, half_15_08_φ4, half_15_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_08 : AdmissibleExponent 8 30 (2227115577/100000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 13) (ψ := (1187468759/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_14_08)
    (by simpa only [half_15_08_φ1] using half_15_08_hx1)
  exact admissibleExponent_mono h (by norm_num [half_15_08_φ1, half_15_08_φ2, half_15_08_φ3, half_15_08_φ4, half_15_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_16_08_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1205656147/10000000000 : ℝ)

def half_16_08_φ2 : Fin 2 → ℝ := Fin.snoc half_16_08_φ1 (1185172413/10000000000 : ℝ)

def half_16_08_φ3 : Fin 3 → ℝ := Fin.snoc half_16_08_φ2 (1087024491/10000000000 : ℝ)

def half_16_08_φ4 : Fin 4 → ℝ := Fin.snoc half_16_08_φ3 (465867639/5000000000 : ℝ)

def half_16_08_φ5 : Fin 5 → ℝ := Fin.snoc half_16_08_φ4 (399315119/5000000000 : ℝ)

theorem half_16_08_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_16_08_φ5) (60627410093/10000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_16_08_φ5 (by norm_num [half_16_08_φ1, half_16_08_φ2, half_16_08_φ3, half_16_08_φ4, half_16_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_08_φ1, half_16_08_φ2, half_16_08_φ3, half_16_08_φ4, half_16_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_08_φ1, half_16_08_φ2, half_16_08_φ3, half_16_08_φ4, half_16_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_16_08_φ1, half_16_08_φ2, half_16_08_φ3, half_16_08_φ4, half_16_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_16_08_φ1, half_16_08_φ2, half_16_08_φ3, half_16_08_φ4, half_16_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_16_08_hx5 : SourcePowerBound (powerBoxCross 8 11 32 half_16_08_φ5) (23227904297/2500000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 11) (r := 2) (v := 14) (w := 15) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_16_08_φ5 (by norm_num [half_16_08_φ1, half_16_08_φ2, half_16_08_φ3, half_16_08_φ4, half_16_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_08_φ1, half_16_08_φ2, half_16_08_φ3, half_16_08_φ4, half_16_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_16_08_hF2 (half_14_08) (half_15_08)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_16_08_φ1, half_16_08_φ2, half_16_08_φ3, half_16_08_φ4, half_16_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_08_hx4 : SourcePowerBound (powerBoxCross 8 12 16 half_16_08_φ4) (111094316619/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 12) (u := 10) (t := 13)
    (D := 16) (ψ := (399315119/5000000000 : ℝ)) half_16_08_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_08_φ1, half_16_08_φ2, half_16_08_φ3, half_16_08_φ4, half_16_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_08_φ1, half_16_08_φ2, half_16_08_φ3, half_16_08_φ4, half_16_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_08_φ1, half_16_08_φ2, half_16_08_φ3, half_16_08_φ4, half_16_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_11_08) (half_13_08)
    (by simpa only [half_16_08_φ5, show (2:ℝ)*16=32 by norm_num] using half_16_08_hx5)
  exact h.weaken (by norm_num [half_16_08_φ1, half_16_08_φ2, half_16_08_φ3, half_16_08_φ4, half_16_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_08_hx3 : SourcePowerBound (powerBoxCross 8 13 8 half_16_08_φ3) (67749812939/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 13) (u := 11) (t := 14)
    (D := 8) (ψ := (465867639/5000000000 : ℝ)) half_16_08_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_08_φ1, half_16_08_φ2, half_16_08_φ3, half_16_08_φ4, half_16_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_08_φ1, half_16_08_φ2, half_16_08_φ3, half_16_08_φ4, half_16_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_08_φ1, half_16_08_φ2, half_16_08_φ3, half_16_08_φ4, half_16_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_12_08) (half_14_08)
    (by simpa only [half_16_08_φ4, show (2:ℝ)*8=16 by norm_num] using half_16_08_hx4)
  exact h.weaken (by norm_num [half_16_08_φ1, half_16_08_φ2, half_16_08_φ3, half_16_08_φ4, half_16_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_08_hx2 : SourcePowerBound (powerBoxCross 8 14 4 half_16_08_φ2) (167702240327/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 14) (u := 12) (t := 15)
    (D := 4) (ψ := (1087024491/10000000000 : ℝ)) half_16_08_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_08_φ1, half_16_08_φ2, half_16_08_φ3, half_16_08_φ4, half_16_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_08_φ1, half_16_08_φ2, half_16_08_φ3, half_16_08_φ4, half_16_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_08_φ1, half_16_08_φ2, half_16_08_φ3, half_16_08_φ4, half_16_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_13_08) (half_15_08)
    (by simpa only [half_16_08_φ3, show (2:ℝ)*4=8 by norm_num] using half_16_08_hx3)
  exact h.weaken (by norm_num [half_16_08_φ1, half_16_08_φ2, half_16_08_φ3, half_16_08_φ4, half_16_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_08_hx1 : SourcePowerBound (powerBoxCross 8 15 2 half_16_08_φ1) (103532929/5000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 15) (u := 13) (t := 16)
    (D := 2) (ψ := (1185172413/10000000000 : ℝ)) half_16_08_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_08_φ1, half_16_08_φ2, half_16_08_φ3, half_16_08_φ4, half_16_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_08_φ1, half_16_08_φ2, half_16_08_φ3, half_16_08_φ4, half_16_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_08_φ1, half_16_08_φ2, half_16_08_φ3, half_16_08_φ4, half_16_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_14_08) (half_16_07)
    (by simpa only [half_16_08_φ2, show (2:ℝ)*2=4 by norm_num] using half_16_08_hx2)
  exact h.weaken (by norm_num [half_16_08_φ1, half_16_08_φ2, half_16_08_φ3, half_16_08_φ4, half_16_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_08 : AdmissibleExponent 8 32 (242029886263/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 14) (ψ := (1205656147/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_15_08)
    (by simpa only [half_16_08_φ1] using half_16_08_hx1)
  exact admissibleExponent_mono h (by norm_num [half_16_08_φ1, half_16_08_φ2, half_16_08_φ3, half_16_08_φ4, half_16_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_17_08_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1219238197/10000000000 : ℝ)

def half_17_08_φ2 : Fin 2 → ℝ := Fin.snoc half_17_08_φ1 (150755657/1250000000 : ℝ)

def half_17_08_φ3 : Fin 3 → ℝ := Fin.snoc half_17_08_φ2 (1082102363/10000000000 : ℝ)

def half_17_08_φ4 : Fin 4 → ℝ := Fin.snoc half_17_08_φ3 (927516311/10000000000 : ℝ)

def half_17_08_φ5 : Fin 5 → ℝ := Fin.snoc half_17_08_φ4 (795013981/10000000000 : ℝ)

theorem half_17_08_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_17_08_φ5) (15042940433/2500000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_17_08_φ5 (by norm_num [half_17_08_φ1, half_17_08_φ2, half_17_08_φ3, half_17_08_φ4, half_17_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_08_φ1, half_17_08_φ2, half_17_08_φ3, half_17_08_φ4, half_17_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_08_φ1, half_17_08_φ2, half_17_08_φ3, half_17_08_φ4, half_17_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_17_08_φ1, half_17_08_φ2, half_17_08_φ3, half_17_08_φ4, half_17_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_17_08_φ1, half_17_08_φ2, half_17_08_φ3, half_17_08_φ4, half_17_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_17_08_hx5 : SourcePowerBound (powerBoxCross 8 12 32 half_17_08_φ5) (3175957971/312500000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 12) (r := 2) (v := 0) (w := 16) (D := 32)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_17_08_φ5 (by norm_num [half_17_08_φ1, half_17_08_φ2, half_17_08_φ3, half_17_08_φ4, half_17_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_08_φ1, half_17_08_φ2, half_17_08_φ3, half_17_08_φ4, half_17_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_17_08_hF2 (admissibleExponent_zero 8) (half_16_08)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_17_08_φ1, half_17_08_φ2, half_17_08_φ3, half_17_08_φ4, half_17_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_08_hx4 : SourcePowerBound (powerBoxCross 8 13 16 half_17_08_φ4) (60550467509/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 13) (u := 11) (t := 14)
    (D := 16) (ψ := (795013981/10000000000 : ℝ)) half_17_08_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_08_φ1, half_17_08_φ2, half_17_08_φ3, half_17_08_φ4, half_17_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_08_φ1, half_17_08_φ2, half_17_08_φ3, half_17_08_φ4, half_17_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_08_φ1, half_17_08_φ2, half_17_08_φ3, half_17_08_φ4, half_17_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_12_08) (half_14_08)
    (by simpa only [half_17_08_φ5, show (2:ℝ)*16=32 by norm_num] using half_17_08_hx5)
  exact h.weaken (by norm_num [half_17_08_φ1, half_17_08_φ2, half_17_08_φ3, half_17_08_φ4, half_17_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_08_hx3 : SourcePowerBound (powerBoxCross 8 14 8 half_17_08_φ3) (36791895491/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 14) (u := 12) (t := 15)
    (D := 8) (ψ := (927516311/10000000000 : ℝ)) half_17_08_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_08_φ1, half_17_08_φ2, half_17_08_φ3, half_17_08_φ4, half_17_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_08_φ1, half_17_08_φ2, half_17_08_φ3, half_17_08_φ4, half_17_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_08_φ1, half_17_08_φ2, half_17_08_φ3, half_17_08_φ4, half_17_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_13_08) (half_15_08)
    (by simpa only [half_17_08_φ4, show (2:ℝ)*8=16 by norm_num] using half_17_08_hx4)
  exact h.weaken (by norm_num [half_17_08_φ1, half_17_08_φ2, half_17_08_φ3, half_17_08_φ4, half_17_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_08_hx2 : SourcePowerBound (powerBoxCross 8 15 4 half_17_08_φ2) (36273814003/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 15) (u := 13) (t := 16)
    (D := 4) (ψ := (1082102363/10000000000 : ℝ)) half_17_08_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_08_φ1, half_17_08_φ2, half_17_08_φ3, half_17_08_φ4, half_17_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_08_φ1, half_17_08_φ2, half_17_08_φ3, half_17_08_φ4, half_17_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_08_φ1, half_17_08_φ2, half_17_08_φ3, half_17_08_φ4, half_17_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_14_08) (half_16_08)
    (by simpa only [half_17_08_φ3, show (2:ℝ)*4=8 by norm_num] using half_17_08_hx3)
  exact h.weaken (by norm_num [half_17_08_φ1, half_17_08_φ2, half_17_08_φ3, half_17_08_φ4, half_17_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_08_hx1 : SourcePowerBound (powerBoxCross 8 16 2 half_17_08_φ1) (223739916253/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 16) (u := 14) (t := 17)
    (D := 2) (ψ := (150755657/1250000000 : ℝ)) half_17_08_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_08_φ1, half_17_08_φ2, half_17_08_φ3, half_17_08_φ4, half_17_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_08_φ1, half_17_08_φ2, half_17_08_φ3, half_17_08_φ4, half_17_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_08_φ1, half_17_08_φ2, half_17_08_φ3, half_17_08_φ4, half_17_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_15_08) (half_17_07)
    (by simpa only [half_17_08_φ2, show (2:ℝ)*2=4 by norm_num] using half_17_08_hx2)
  exact h.weaken (by norm_num [half_17_08_φ1, half_17_08_φ2, half_17_08_φ3, half_17_08_φ4, half_17_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_08 : AdmissibleExponent 8 34 (6538407509/250000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 15) (ψ := (1219238197/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_16_08)
    (by simpa only [half_17_08_φ1] using half_17_08_hx1)
  exact admissibleExponent_mono h (by norm_num [half_17_08_φ1, half_17_08_φ2, half_17_08_φ3, half_17_08_φ4, half_17_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_18_08_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (245934761/2000000000 : ℝ)

def half_18_08_φ2 : Fin 2 → ℝ := Fin.snoc half_18_08_φ1 (1222008283/10000000000 : ℝ)

def half_18_08_φ3 : Fin 3 → ℝ := Fin.snoc half_18_08_φ2 (107833113/1000000000 : ℝ)

def half_18_08_φ4 : Fin 4 → ℝ := Fin.snoc half_18_08_φ3 (36971353/400000000 : ℝ)

def half_18_08_φ5 : Fin 5 → ℝ := Fin.snoc half_18_08_φ4 (792243279/10000000000 : ℝ)

theorem half_18_08_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_18_08_φ5) (29911326619/5000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_18_08_φ5 (by norm_num [half_18_08_φ1, half_18_08_φ2, half_18_08_φ3, half_18_08_φ4, half_18_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_18_08_φ1, half_18_08_φ2, half_18_08_φ3, half_18_08_φ4, half_18_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_18_08_φ1, half_18_08_φ2, half_18_08_φ3, half_18_08_φ4, half_18_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_18_08_φ1, half_18_08_φ2, half_18_08_φ3, half_18_08_φ4, half_18_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_18_08_φ1, half_18_08_φ2, half_18_08_φ3, half_18_08_φ4, half_18_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_18_08_hx5 : SourcePowerBound (powerBoxCross 8 13 32 half_18_08_φ5) (110533793369/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 13) (r := 2) (v := 17) (w := 18) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_18_08_φ5 (by norm_num [half_18_08_φ1, half_18_08_φ2, half_18_08_φ3, half_18_08_φ4, half_18_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_18_08_φ1, half_18_08_φ2, half_18_08_φ3, half_18_08_φ4, half_18_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_18_08_hF2 (half_17_08) (half_18_07)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_18_08_φ1, half_18_08_φ2, half_18_08_φ3, half_18_08_φ4, half_18_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_18_08_hx4 : SourcePowerBound (powerBoxCross 8 14 16 half_18_08_φ4) (131334505227/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 14) (u := 12) (t := 15)
    (D := 16) (ψ := (792243279/10000000000 : ℝ)) half_18_08_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_18_08_φ1, half_18_08_φ2, half_18_08_φ3, half_18_08_φ4, half_18_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_18_08_φ1, half_18_08_φ2, half_18_08_φ3, half_18_08_φ4, half_18_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_18_08_φ1, half_18_08_φ2, half_18_08_φ3, half_18_08_φ4, half_18_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_13_08) (half_15_08)
    (by simpa only [half_18_08_φ5, show (2:ℝ)*16=32 by norm_num] using half_18_08_hx5)
  exact h.weaken (by norm_num [half_18_08_φ1, half_18_08_φ2, half_18_08_φ3, half_18_08_φ4, half_18_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_18_08_hx3 : SourcePowerBound (powerBoxCross 8 15 8 half_18_08_φ3) (159086546237/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 15) (u := 13) (t := 16)
    (D := 8) (ψ := (36971353/400000000 : ℝ)) half_18_08_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_18_08_φ1, half_18_08_φ2, half_18_08_φ3, half_18_08_φ4, half_18_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_18_08_φ1, half_18_08_φ2, half_18_08_φ3, half_18_08_φ4, half_18_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_18_08_φ1, half_18_08_φ2, half_18_08_φ3, half_18_08_φ4, half_18_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_14_08) (half_16_08)
    (by simpa only [half_18_08_φ4, show (2:ℝ)*8=16 by norm_num] using half_18_08_hx4)
  exact h.weaken (by norm_num [half_18_08_φ1, half_18_08_φ2, half_18_08_φ3, half_18_08_φ4, half_18_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_18_08_hx2 : SourcePowerBound (powerBoxCross 8 16 4 half_18_08_φ2) (48826536057/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 16) (u := 14) (t := 17)
    (D := 4) (ψ := (107833113/1000000000 : ℝ)) half_18_08_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_18_08_φ1, half_18_08_φ2, half_18_08_φ3, half_18_08_φ4, half_18_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_18_08_φ1, half_18_08_φ2, half_18_08_φ3, half_18_08_φ4, half_18_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_18_08_φ1, half_18_08_φ2, half_18_08_φ3, half_18_08_φ4, half_18_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_15_08) (half_17_08)
    (by simpa only [half_18_08_φ3, show (2:ℝ)*4=8 by norm_num] using half_18_08_hx3)
  exact h.weaken (by norm_num [half_18_08_φ1, half_18_08_φ2, half_18_08_φ3, half_18_08_φ4, half_18_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_18_08_hx1 : SourcePowerBound (powerBoxCross 8 17 2 half_18_08_φ1) (60151385103/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 17) (u := 15) (t := 18)
    (D := 2) (ψ := (1222008283/10000000000 : ℝ)) half_18_08_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_18_08_φ1, half_18_08_φ2, half_18_08_φ3, half_18_08_φ4, half_18_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_18_08_φ1, half_18_08_φ2, half_18_08_φ3, half_18_08_φ4, half_18_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_18_08_φ1, half_18_08_φ2, half_18_08_φ3, half_18_08_φ4, half_18_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_16_08) (half_18_07)
    (by simpa only [half_18_08_φ2, show (2:ℝ)*2=4 by norm_num] using half_18_08_hx2)
  exact h.weaken (by norm_num [half_18_08_φ1, half_18_08_φ2, half_18_08_φ3, half_18_08_φ4, half_18_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_18_08 : AdmissibleExponent 8 36 (281184775977/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 16) (ψ := (245934761/2000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_17_08)
    (by simpa only [half_18_08_φ1] using half_18_08_hx1)
  exact admissibleExponent_mono h (by norm_num [half_18_08_φ1, half_18_08_φ2, half_18_08_φ3, half_18_08_φ4, half_18_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_19_08_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (618618069/5000000000 : ℝ)

def half_19_08_φ2 : Fin 2 → ℝ := Fin.snoc half_19_08_φ1 (616987373/5000000000 : ℝ)

def half_19_08_φ3 : Fin 3 → ℝ := Fin.snoc half_19_08_φ2 (537770651/5000000000 : ℝ)

def half_19_08_φ4 : Fin 4 → ℝ := Fin.snoc half_19_08_φ3 (14404571/156250000 : ℝ)

def half_19_08_φ5 : Fin 5 → ℝ := Fin.snoc half_19_08_φ4 (790193609/10000000000 : ℝ)

theorem half_19_08_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_19_08_φ5) (59564394881/10000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_19_08_φ5 (by norm_num [half_19_08_φ1, half_19_08_φ2, half_19_08_φ3, half_19_08_φ4, half_19_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_19_08_φ1, half_19_08_φ2, half_19_08_φ3, half_19_08_φ4, half_19_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_19_08_φ1, half_19_08_φ2, half_19_08_φ3, half_19_08_φ4, half_19_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_19_08_φ1, half_19_08_φ2, half_19_08_φ3, half_19_08_φ4, half_19_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_19_08_φ1, half_19_08_φ2, half_19_08_φ3, half_19_08_φ4, half_19_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_19_08_hx5 : SourcePowerBound (powerBoxCross 8 14 32 half_19_08_φ5) (59782667391/5000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 14) (r := 2) (v := 18) (w := 19) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_19_08_φ5 (by norm_num [half_19_08_φ1, half_19_08_φ2, half_19_08_φ3, half_19_08_φ4, half_19_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_19_08_φ1, half_19_08_φ2, half_19_08_φ3, half_19_08_φ4, half_19_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_19_08_hF2 (half_18_08) (half_19_07)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_19_08_φ1, half_19_08_φ2, half_19_08_φ3, half_19_08_φ4, half_19_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_19_08_hx4 : SourcePowerBound (powerBoxCross 8 15 16 half_19_08_φ4) (70873844451/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 15) (u := 13) (t := 16)
    (D := 16) (ψ := (790193609/10000000000 : ℝ)) half_19_08_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_19_08_φ1, half_19_08_φ2, half_19_08_φ3, half_19_08_φ4, half_19_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_19_08_φ1, half_19_08_φ2, half_19_08_φ3, half_19_08_φ4, half_19_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_19_08_φ1, half_19_08_φ2, half_19_08_φ3, half_19_08_φ4, half_19_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_14_08) (half_16_08)
    (by simpa only [half_19_08_φ5, show (2:ℝ)*16=32 by norm_num] using half_19_08_hx5)
  exact h.weaken (by norm_num [half_19_08_φ1, half_19_08_φ2, half_19_08_φ3, half_19_08_φ4, half_19_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_19_08_hx3 : SourcePowerBound (powerBoxCross 8 16 8 half_19_08_φ3) (171215581617/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 16) (u := 14) (t := 17)
    (D := 8) (ψ := (14404571/156250000 : ℝ)) half_19_08_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_19_08_φ1, half_19_08_φ2, half_19_08_φ3, half_19_08_φ4, half_19_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_19_08_φ1, half_19_08_φ2, half_19_08_φ3, half_19_08_φ4, half_19_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_19_08_φ1, half_19_08_φ2, half_19_08_φ3, half_19_08_φ4, half_19_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_15_08) (half_17_08)
    (by simpa only [half_19_08_φ4, show (2:ℝ)*8=16 by norm_num] using half_19_08_hx4)
  exact h.weaken (by norm_num [half_19_08_φ1, half_19_08_φ2, half_19_08_φ3, half_19_08_φ4, half_19_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_19_08_hx2 : SourcePowerBound (powerBoxCross 8 17 4 half_19_08_φ2) (6546202717/312500000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 17) (u := 15) (t := 18)
    (D := 4) (ψ := (537770651/5000000000 : ℝ)) half_19_08_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_19_08_φ1, half_19_08_φ2, half_19_08_φ3, half_19_08_φ4, half_19_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_19_08_φ1, half_19_08_φ2, half_19_08_φ3, half_19_08_φ4, half_19_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_19_08_φ1, half_19_08_φ2, half_19_08_φ3, half_19_08_φ4, half_19_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_16_08) (half_18_08)
    (by simpa only [half_19_08_φ3, show (2:ℝ)*4=8 by norm_num] using half_19_08_hx3)
  exact h.weaken (by norm_num [half_19_08_φ1, half_19_08_φ2, half_19_08_φ3, half_19_08_φ4, half_19_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_19_08_hx1 : SourcePowerBound (powerBoxCross 8 18 2 half_19_08_φ1) (25763281549/1000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 18) (u := 16) (t := 19)
    (D := 2) (ψ := (616987373/5000000000 : ℝ)) half_19_08_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_19_08_φ1, half_19_08_φ2, half_19_08_φ3, half_19_08_φ4, half_19_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_19_08_φ1, half_19_08_φ2, half_19_08_φ3, half_19_08_φ4, half_19_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_19_08_φ1, half_19_08_φ2, half_19_08_φ3, half_19_08_φ4, half_19_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_17_08) (half_19_07)
    (by simpa only [half_19_08_φ2, show (2:ℝ)*2=4 by norm_num] using half_19_08_hx2)
  exact h.weaken (by norm_num [half_19_08_φ1, half_19_08_φ2, half_19_08_φ3, half_19_08_φ4, half_19_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_19_08 : AdmissibleExponent 8 38 (940425251/31250000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 17) (ψ := (618618069/5000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_18_08)
    (by simpa only [half_19_08_φ1] using half_19_08_hx1)
  exact admissibleExponent_mono h (by norm_num [half_19_08_φ1, half_19_08_φ2, half_19_08_φ3, half_19_08_φ4, half_19_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_20_08_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (310737673/2500000000 : ℝ)

def half_20_08_φ2 : Fin 2 → ℝ := Fin.snoc half_20_08_φ1 (621331443/5000000000 : ℝ)

def half_20_08_φ3 : Fin 3 → ℝ := Fin.snoc half_20_08_φ2 (536741887/5000000000 : ℝ)

def half_20_08_φ4 : Fin 4 → ℝ := Fin.snoc half_20_08_φ3 (920128949/10000000000 : ℝ)

def half_20_08_φ5 : Fin 5 → ℝ := Fin.snoc half_20_08_φ4 (197170489/2500000000 : ℝ)

theorem half_20_08_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_20_08_φ5) (59373926603/10000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_20_08_φ5 (by norm_num [half_20_08_φ1, half_20_08_φ2, half_20_08_φ3, half_20_08_φ4, half_20_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_20_08_φ1, half_20_08_φ2, half_20_08_φ3, half_20_08_φ4, half_20_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_20_08_φ1, half_20_08_φ2, half_20_08_φ3, half_20_08_φ4, half_20_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_20_08_φ1, half_20_08_φ2, half_20_08_φ3, half_20_08_φ4, half_20_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_20_08_φ1, half_20_08_φ2, half_20_08_φ3, half_20_08_φ4, half_20_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_20_08_hx5 : SourcePowerBound (powerBoxCross 8 15 32 half_20_08_φ5) (25739077439/2000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 15) (r := 2) (v := 0) (w := 20) (D := 32)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_20_08_φ5 (by norm_num [half_20_08_φ1, half_20_08_φ2, half_20_08_φ3, half_20_08_φ4, half_20_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_20_08_φ1, half_20_08_φ2, half_20_08_φ3, half_20_08_φ4, half_20_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_20_08_hF2 (admissibleExponent_zero 8) (half_20_07)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_20_08_φ1, half_20_08_φ2, half_20_08_φ3, half_20_08_φ4, half_20_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_20_08_hx4 : SourcePowerBound (powerBoxCross 8 16 16 half_20_08_φ4) (6092017053/400000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 16) (u := 14) (t := 17)
    (D := 16) (ψ := (197170489/2500000000 : ℝ)) half_20_08_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_20_08_φ1, half_20_08_φ2, half_20_08_φ3, half_20_08_φ4, half_20_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_20_08_φ1, half_20_08_φ2, half_20_08_φ3, half_20_08_φ4, half_20_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_20_08_φ1, half_20_08_φ2, half_20_08_φ3, half_20_08_φ4, half_20_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_15_08) (half_17_08)
    (by simpa only [half_20_08_φ5, show (2:ℝ)*16=32 by norm_num] using half_20_08_hx5)
  exact h.weaken (by norm_num [half_20_08_φ1, half_20_08_φ2, half_20_08_φ3, half_20_08_φ4, half_20_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_20_08_hx3 : SourcePowerBound (powerBoxCross 8 17 8 half_20_08_φ3) (183509559549/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 17) (u := 15) (t := 18)
    (D := 8) (ψ := (920128949/10000000000 : ℝ)) half_20_08_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_20_08_φ1, half_20_08_φ2, half_20_08_φ3, half_20_08_φ4, half_20_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_20_08_φ1, half_20_08_φ2, half_20_08_φ3, half_20_08_φ4, half_20_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_20_08_φ1, half_20_08_φ2, half_20_08_φ3, half_20_08_φ4, half_20_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_16_08) (half_18_08)
    (by simpa only [half_20_08_φ4, show (2:ℝ)*8=16 by norm_num] using half_20_08_hx4)
  exact h.weaken (by norm_num [half_20_08_φ1, half_20_08_φ2, half_20_08_φ3, half_20_08_φ4, half_20_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_20_08_hx2 : SourcePowerBound (powerBoxCross 8 18 4 half_20_08_φ2) (44767022863/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 18) (u := 16) (t := 19)
    (D := 4) (ψ := (536741887/5000000000 : ℝ)) half_20_08_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_20_08_φ1, half_20_08_φ2, half_20_08_φ3, half_20_08_φ4, half_20_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_20_08_φ1, half_20_08_φ2, half_20_08_φ3, half_20_08_φ4, half_20_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_20_08_φ1, half_20_08_φ2, half_20_08_φ3, half_20_08_φ4, half_20_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_17_08) (half_19_08)
    (by simpa only [half_20_08_φ3, show (2:ℝ)*4=8 by norm_num] using half_20_08_hx3)
  exact h.weaken (by norm_num [half_20_08_φ1, half_20_08_φ2, half_20_08_φ3, half_20_08_φ4, half_20_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_20_08_hx1 : SourcePowerBound (powerBoxCross 8 19 2 half_20_08_φ1) (274774160091/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 19) (u := 17) (t := 20)
    (D := 2) (ψ := (621331443/5000000000 : ℝ)) half_20_08_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_20_08_φ1, half_20_08_φ2, half_20_08_φ3, half_20_08_φ4, half_20_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_20_08_φ1, half_20_08_φ2, half_20_08_φ3, half_20_08_φ4, half_20_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_20_08_φ1, half_20_08_φ2, half_20_08_φ3, half_20_08_φ4, half_20_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_18_08) (half_20_07)
    (by simpa only [half_20_08_φ2, show (2:ℝ)*2=4 by norm_num] using half_20_08_hx2)
  exact h.weaken (by norm_num [half_20_08_φ1, half_20_08_φ2, half_20_08_φ3, half_20_08_φ4, half_20_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_20_08 : AdmissibleExponent 8 40 (64152667139/2000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 18) (ψ := (310737673/2500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_19_08)
    (by simpa only [half_20_08_φ1] using half_20_08_hx1)
  exact admissibleExponent_mono h (by norm_num [half_20_08_φ1, half_20_08_φ2, half_20_08_φ3, half_20_08_φ4, half_20_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_10_09_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (515812203/5000000000 : ℝ)

def half_10_09_φ2 : Fin 2 → ℝ := Fin.snoc half_10_09_φ1 (480702403/5000000000 : ℝ)

def half_10_09_φ3 : Fin 3 → ℝ := Fin.snoc half_10_09_φ2 (104572781/1250000000 : ℝ)

def half_10_09_φ4 : Fin 4 → ℝ := Fin.snoc half_10_09_φ3 (274503341/5000000000 : ℝ)

theorem half_10_09_hF2 : SourcePowerBound (paddedMoment 8 0 2 16 half_10_09_φ4) (34524509509/5000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 4) (r := 0) (n := 1) (D := 16)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_10_09_φ4 (by norm_num [half_10_09_φ1, half_10_09_φ2, half_10_09_φ3, half_10_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_09_φ1, half_10_09_φ2, half_10_09_φ3, half_10_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_09_φ1, half_10_09_φ2, half_10_09_φ3, half_10_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_10_09_φ1, half_10_09_φ2, half_10_09_φ3, half_10_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_10_09_φ1, half_10_09_φ2, half_10_09_φ3, half_10_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_10_09_hx4 : SourcePowerBound (powerBoxCross 8 6 16 half_10_09_φ4) (66142266007/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 6) (r := 2) (v := 0) (w := 8) (D := 16)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_10_09_φ4 (by norm_num [half_10_09_φ1, half_10_09_φ2, half_10_09_φ3, half_10_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_09_φ1, half_10_09_φ2, half_10_09_φ3, half_10_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_10_09_hF2 (admissibleExponent_zero 8) (SeedCompletionHigher8SimpleSeeds.degree8_half_8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_10_09_φ1, half_10_09_φ2, half_10_09_φ3, half_10_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_09_hx3 : SourcePowerBound (powerBoxCross 8 7 8 half_10_09_φ3) (2389862573/312500000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 7) (u := 5) (t := 8)
    (D := 8) (ψ := (274503341/5000000000 : ℝ)) half_10_09_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_09_φ1, half_10_09_φ2, half_10_09_φ3, half_10_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_09_φ1, half_10_09_φ2, half_10_09_φ3, half_10_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_09_φ1, half_10_09_φ2, half_10_09_φ3, half_10_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionEven8SecondSeeds.degree8_half_6) (SeedCompletionHigher8SimpleSeeds.degree8_half_8)
    (by simpa only [half_10_09_φ4, show (2:ℝ)*8=16 by norm_num] using half_10_09_hx4)
  exact h.weaken (by norm_num [half_10_09_φ1, half_10_09_φ2, half_10_09_φ3, half_10_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_09_hx2 : SourcePowerBound (powerBoxCross 8 8 4 half_10_09_φ2) (92551543031/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 8) (u := 6) (t := 9)
    (D := 4) (ψ := (104572781/1250000000 : ℝ)) half_10_09_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_09_φ1, half_10_09_φ2, half_10_09_φ3, half_10_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_09_φ1, half_10_09_φ2, half_10_09_φ3, half_10_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_09_φ1, half_10_09_φ2, half_10_09_φ3, half_10_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_7) (SeedCompletionHigher8SimpleSeeds.degree8_half_9)
    (by simpa only [half_10_09_φ3, show (2:ℝ)*4=8 by norm_num] using half_10_09_hx3)
  exact h.weaken (by norm_num [half_10_09_φ1, half_10_09_φ2, half_10_09_φ3, half_10_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_09_hx1 : SourcePowerBound (powerBoxCross 8 9 2 half_10_09_φ1) (22749125299/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 9) (u := 7) (t := 10)
    (D := 2) (ψ := (480702403/5000000000 : ℝ)) half_10_09_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_09_φ1, half_10_09_φ2, half_10_09_φ3, half_10_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_09_φ1, half_10_09_φ2, half_10_09_φ3, half_10_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_09_φ1, half_10_09_φ2, half_10_09_φ3, half_10_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_8) (half_10_08)
    (by simpa only [half_10_09_φ2, show (2:ℝ)*2=4 by norm_num] using half_10_09_hx2)
  exact h.weaken (by norm_num [half_10_09_φ1, half_10_09_φ2, half_10_09_φ3, half_10_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_09 : AdmissibleExponent 8 20 (131283241397/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 8) (ψ := (515812203/5000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_9)
    (by simpa only [half_10_09_φ1] using half_10_09_hx1)
  exact admissibleExponent_mono h (by norm_num [half_10_09_φ1, half_10_09_φ2, half_10_09_φ3, half_10_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_11_09_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1074326157/10000000000 : ℝ)

def half_11_09_φ2 : Fin 2 → ℝ := Fin.snoc half_11_09_φ1 (1012248707/10000000000 : ℝ)

def half_11_09_φ3 : Fin 3 → ℝ := Fin.snoc half_11_09_φ2 (461148919/5000000000 : ℝ)

def half_11_09_φ4 : Fin 4 → ℝ := Fin.snoc half_11_09_φ3 (740492387/10000000000 : ℝ)

theorem half_11_09_hF2 : SourcePowerBound (paddedMoment 8 0 2 16 half_11_09_φ4) (61263333131/10000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 4) (r := 0) (n := 1) (D := 16)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_11_09_φ4 (by norm_num [half_11_09_φ1, half_11_09_φ2, half_11_09_φ3, half_11_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_09_φ1, half_11_09_φ2, half_11_09_φ3, half_11_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_09_φ1, half_11_09_φ2, half_11_09_φ3, half_11_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_11_09_φ1, half_11_09_φ2, half_11_09_φ3, half_11_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_11_09_φ1, half_11_09_φ2, half_11_09_φ3, half_11_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_11_09_hx4 : SourcePowerBound (powerBoxCross 8 7 16 half_11_09_φ4) (1790622609/250000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 7) (r := 2) (v := 9) (w := 10) (D := 16)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_11_09_φ4 (by norm_num [half_11_09_φ1, half_11_09_φ2, half_11_09_φ3, half_11_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_09_φ1, half_11_09_φ2, half_11_09_φ3, half_11_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_11_09_hF2 (SeedCompletionHigher8SimpleSeeds.degree8_half_9) (half_10_09)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_11_09_φ1, half_11_09_φ2, half_11_09_φ3, half_11_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_09_hx3 : SourcePowerBound (powerBoxCross 8 8 8 half_11_09_φ3) (85128975497/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 8) (u := 6) (t := 9)
    (D := 8) (ψ := (740492387/10000000000 : ℝ)) half_11_09_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_09_φ1, half_11_09_φ2, half_11_09_φ3, half_11_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_09_φ1, half_11_09_φ2, half_11_09_φ3, half_11_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_09_φ1, half_11_09_φ2, half_11_09_φ3, half_11_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_7) (SeedCompletionHigher8SimpleSeeds.degree8_half_9)
    (by simpa only [half_11_09_φ4, show (2:ℝ)*8=16 by norm_num] using half_11_09_hx4)
  exact h.weaken (by norm_num [half_11_09_φ1, half_11_09_φ2, half_11_09_φ3, half_11_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_09_hx2 : SourcePowerBound (powerBoxCross 8 9 4 half_11_09_φ2) (10412371463/1000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 9) (u := 7) (t := 10)
    (D := 4) (ψ := (461148919/5000000000 : ℝ)) half_11_09_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_09_φ1, half_11_09_φ2, half_11_09_φ3, half_11_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_09_φ1, half_11_09_φ2, half_11_09_φ3, half_11_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_09_φ1, half_11_09_φ2, half_11_09_φ3, half_11_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_8) (half_10_09)
    (by simpa only [half_11_09_φ3, show (2:ℝ)*4=8 by norm_num] using half_11_09_hx3)
  exact h.weaken (by norm_num [half_11_09_φ1, half_11_09_φ2, half_11_09_φ3, half_11_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_09_hx1 : SourcePowerBound (powerBoxCross 8 10 2 half_11_09_φ1) (25650693107/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 10) (u := 8) (t := 11)
    (D := 2) (ψ := (1012248707/10000000000 : ℝ)) half_11_09_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_09_φ1, half_11_09_φ2, half_11_09_φ3, half_11_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_09_φ1, half_11_09_φ2, half_11_09_φ3, half_11_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_09_φ1, half_11_09_φ2, half_11_09_φ3, half_11_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_9) (half_11_08)
    (by simpa only [half_11_09_φ2, show (2:ℝ)*2=4 by norm_num] using half_11_09_hx2)
  exact h.weaken (by norm_num [half_11_09_φ1, half_11_09_φ2, half_11_09_φ3, half_11_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_09 : AdmissibleExponent 8 22 (74332831259/5000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 9) (ψ := (1074326157/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_10_09)
    (by simpa only [half_11_09_φ1] using half_11_09_hx1)
  exact admissibleExponent_mono h (by norm_num [half_11_09_φ1, half_11_09_φ2, half_11_09_φ3, half_11_09_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_12_09_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1107165353/10000000000 : ℝ)

def half_12_09_φ2 : Fin 2 → ℝ := Fin.snoc half_12_09_φ1 (131947057/1250000000 : ℝ)

def half_12_09_φ3 : Fin 3 → ℝ := Fin.snoc half_12_09_φ2 (977048053/10000000000 : ℝ)

def half_12_09_φ4 : Fin 4 → ℝ := Fin.snoc half_12_09_φ3 (13156347/156250000 : ℝ)

def half_12_09_φ5 : Fin 5 → ℝ := Fin.snoc half_12_09_φ4 (263997143/5000000000 : ℝ)

theorem half_12_09_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_12_09_φ5) (18823600631/2500000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_12_09_φ5 (by norm_num [half_12_09_φ1, half_12_09_φ2, half_12_09_φ3, half_12_09_φ4, half_12_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_09_φ1, half_12_09_φ2, half_12_09_φ3, half_12_09_φ4, half_12_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_09_φ1, half_12_09_φ2, half_12_09_φ3, half_12_09_φ4, half_12_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_12_09_φ1, half_12_09_φ2, half_12_09_φ3, half_12_09_φ4, half_12_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_12_09_φ1, half_12_09_φ2, half_12_09_φ3, half_12_09_φ4, half_12_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_12_09_hx5 : SourcePowerBound (powerBoxCross 8 7 32 half_12_09_φ5) (34141176569/5000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 7) (r := 2) (v := 9) (w := 10) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_12_09_φ5 (by norm_num [half_12_09_φ1, half_12_09_φ2, half_12_09_φ3, half_12_09_φ4, half_12_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_09_φ1, half_12_09_φ2, half_12_09_φ3, half_12_09_φ4, half_12_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_12_09_hF2 (SeedCompletionHigher8SimpleSeeds.degree8_half_9) (half_10_09)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_12_09_φ1, half_12_09_φ2, half_12_09_φ3, half_12_09_φ4, half_12_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_09_hx4 : SourcePowerBound (powerBoxCross 8 8 16 half_12_09_φ4) (78099828363/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 8) (u := 6) (t := 9)
    (D := 16) (ψ := (263997143/5000000000 : ℝ)) half_12_09_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_09_φ1, half_12_09_φ2, half_12_09_φ3, half_12_09_φ4, half_12_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_09_φ1, half_12_09_φ2, half_12_09_φ3, half_12_09_φ4, half_12_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_09_φ1, half_12_09_φ2, half_12_09_φ3, half_12_09_φ4, half_12_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_7) (SeedCompletionHigher8SimpleSeeds.degree8_half_9)
    (by simpa only [half_12_09_φ5, show (2:ℝ)*16=32 by norm_num] using half_12_09_hx5)
  exact h.weaken (by norm_num [half_12_09_φ1, half_12_09_φ2, half_12_09_φ3, half_12_09_φ4, half_12_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_09_hx3 : SourcePowerBound (powerBoxCross 8 9 8 half_12_09_φ3) (23601806851/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 9) (u := 7) (t := 10)
    (D := 8) (ψ := (13156347/156250000 : ℝ)) half_12_09_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_09_φ1, half_12_09_φ2, half_12_09_φ3, half_12_09_φ4, half_12_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_09_φ1, half_12_09_φ2, half_12_09_φ3, half_12_09_φ4, half_12_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_09_φ1, half_12_09_φ2, half_12_09_φ3, half_12_09_φ4, half_12_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_8) (half_10_09)
    (by simpa only [half_12_09_φ4, show (2:ℝ)*8=16 by norm_num] using half_12_09_hx4)
  exact h.weaken (by norm_num [half_12_09_φ1, half_12_09_φ2, half_12_09_φ3, half_12_09_φ4, half_12_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_09_hx2 : SourcePowerBound (powerBoxCross 8 10 4 half_12_09_φ2) (58097742443/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 10) (u := 8) (t := 11)
    (D := 4) (ψ := (977048053/10000000000 : ℝ)) half_12_09_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_09_φ1, half_12_09_φ2, half_12_09_φ3, half_12_09_φ4, half_12_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_09_φ1, half_12_09_φ2, half_12_09_φ3, half_12_09_φ4, half_12_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_09_φ1, half_12_09_φ2, half_12_09_φ3, half_12_09_φ4, half_12_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_9) (half_11_09)
    (by simpa only [half_12_09_φ3, show (2:ℝ)*4=8 by norm_num] using half_12_09_hx3)
  exact h.weaken (by norm_num [half_12_09_φ1, half_12_09_φ2, half_12_09_φ3, half_12_09_φ4, half_12_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_09_hx1 : SourcePowerBound (powerBoxCross 8 11 2 half_12_09_φ1) (143313080807/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 11) (u := 9) (t := 12)
    (D := 2) (ψ := (131947057/1250000000 : ℝ)) half_12_09_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_09_φ1, half_12_09_φ2, half_12_09_φ3, half_12_09_φ4, half_12_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_09_φ1, half_12_09_φ2, half_12_09_φ3, half_12_09_φ4, half_12_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_09_φ1, half_12_09_φ2, half_12_09_φ3, half_12_09_φ4, half_12_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_10_09) (half_12_08)
    (by simpa only [half_12_09_φ2, show (2:ℝ)*2=4 by norm_num] using half_12_09_hx2)
  exact h.weaken (by norm_num [half_12_09_φ1, half_12_09_φ2, half_12_09_φ3, half_12_09_φ4, half_12_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_09 : AdmissibleExponent 8 24 (8328177661/500000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 10) (ψ := (1107165353/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_11_09)
    (by simpa only [half_12_09_φ1] using half_12_09_hx1)
  exact admissibleExponent_mono h (by norm_num [half_12_09_φ1, half_12_09_φ2, half_12_09_φ3, half_12_09_φ4, half_12_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_13_09_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (567981947/5000000000 : ℝ)

def half_13_09_φ2 : Fin 2 → ℝ := Fin.snoc half_13_09_φ1 (545100301/5000000000 : ℝ)

def half_13_09_φ3 : Fin 3 → ℝ := Fin.snoc half_13_09_φ2 (256214503/2500000000 : ℝ)

def half_13_09_φ4 : Fin 4 → ℝ := Fin.snoc half_13_09_φ3 (28513151/312500000 : ℝ)

def half_13_09_φ5 : Fin 5 → ℝ := Fin.snoc half_13_09_φ4 (34246629/500000000 : ℝ)

theorem half_13_09_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_13_09_φ5) (852301321/125000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_13_09_φ5 (by norm_num [half_13_09_φ1, half_13_09_φ2, half_13_09_φ3, half_13_09_φ4, half_13_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_09_φ1, half_13_09_φ2, half_13_09_φ3, half_13_09_φ4, half_13_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_09_φ1, half_13_09_φ2, half_13_09_φ3, half_13_09_φ4, half_13_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_13_09_φ1, half_13_09_φ2, half_13_09_φ3, half_13_09_φ4, half_13_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_13_09_φ1, half_13_09_φ2, half_13_09_φ3, half_13_09_φ4, half_13_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_13_09_hx5 : SourcePowerBound (powerBoxCross 8 8 32 half_13_09_φ5) (72247554457/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 8) (r := 2) (v := 10) (w := 11) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_13_09_φ5 (by norm_num [half_13_09_φ1, half_13_09_φ2, half_13_09_φ3, half_13_09_φ4, half_13_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_09_φ1, half_13_09_φ2, half_13_09_φ3, half_13_09_φ4, half_13_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_13_09_hF2 (half_10_09) (half_11_09)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_13_09_φ1, half_13_09_φ2, half_13_09_φ3, half_13_09_φ4, half_13_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_09_hx4 : SourcePowerBound (powerBoxCross 8 9 16 half_13_09_φ4) (17000164747/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 9) (u := 7) (t := 10)
    (D := 16) (ψ := (34246629/500000000 : ℝ)) half_13_09_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_09_φ1, half_13_09_φ2, half_13_09_φ3, half_13_09_φ4, half_13_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_09_φ1, half_13_09_φ2, half_13_09_φ3, half_13_09_φ4, half_13_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_09_φ1, half_13_09_φ2, half_13_09_φ3, half_13_09_φ4, half_13_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_8) (half_10_09)
    (by simpa only [half_13_09_φ5, show (2:ℝ)*16=32 by norm_num] using half_13_09_hx5)
  exact h.weaken (by norm_num [half_13_09_φ1, half_13_09_φ2, half_13_09_φ3, half_13_09_φ4, half_13_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_09_hx3 : SourcePowerBound (powerBoxCross 8 10 8 half_13_09_φ3) (10404447067/1000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 10) (u := 8) (t := 11)
    (D := 8) (ψ := (28513151/312500000 : ℝ)) half_13_09_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_09_φ1, half_13_09_φ2, half_13_09_φ3, half_13_09_φ4, half_13_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_09_φ1, half_13_09_φ2, half_13_09_φ3, half_13_09_φ4, half_13_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_09_φ1, half_13_09_φ2, half_13_09_φ3, half_13_09_φ4, half_13_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_9) (half_11_09)
    (by simpa only [half_13_09_φ4, show (2:ℝ)*8=16 by norm_num] using half_13_09_hx4)
  exact h.weaken (by norm_num [half_13_09_φ1, half_13_09_φ2, half_13_09_φ3, half_13_09_φ4, half_13_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_09_hx2 : SourcePowerBound (powerBoxCross 8 11 4 half_13_09_φ2) (64354346949/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 11) (u := 9) (t := 12)
    (D := 4) (ψ := (256214503/2500000000 : ℝ)) half_13_09_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_09_φ1, half_13_09_φ2, half_13_09_φ3, half_13_09_φ4, half_13_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_09_φ1, half_13_09_φ2, half_13_09_φ3, half_13_09_φ4, half_13_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_09_φ1, half_13_09_φ2, half_13_09_φ3, half_13_09_φ4, half_13_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_10_09) (half_12_09)
    (by simpa only [half_13_09_φ3, show (2:ℝ)*4=8 by norm_num] using half_13_09_hx3)
  exact h.weaken (by norm_num [half_13_09_φ1, half_13_09_φ2, half_13_09_φ3, half_13_09_φ4, half_13_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_09_hx1 : SourcePowerBound (powerBoxCross 8 12 2 half_13_09_φ1) (15877849887/1000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 12) (u := 10) (t := 13)
    (D := 2) (ψ := (545100301/5000000000 : ℝ)) half_13_09_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_09_φ1, half_13_09_φ2, half_13_09_φ3, half_13_09_φ4, half_13_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_09_φ1, half_13_09_φ2, half_13_09_φ3, half_13_09_φ4, half_13_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_09_φ1, half_13_09_φ2, half_13_09_φ3, half_13_09_φ4, half_13_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_11_09) (half_13_08)
    (by simpa only [half_13_09_φ2, show (2:ℝ)*2=4 by norm_num] using half_13_09_hx2)
  exact h.weaken (by norm_num [half_13_09_φ1, half_13_09_φ2, half_13_09_φ3, half_13_09_φ4, half_13_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_09 : AdmissibleExponent 8 26 (11556604277/625000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 11) (ψ := (567981947/5000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_12_09)
    (by simpa only [half_13_09_φ1] using half_13_09_hx1)
  exact admissibleExponent_mono h (by norm_num [half_13_09_φ1, half_13_09_φ2, half_13_09_φ3, half_13_09_φ4, half_13_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_14_09_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (145328693/1250000000 : ℝ)

def half_14_09_φ2 : Fin 2 → ℝ := Fin.snoc half_14_09_φ1 (561805431/5000000000 : ℝ)

def half_14_09_φ3 : Fin 3 → ℝ := Fin.snoc half_14_09_φ2 (267581853/2500000000 : ℝ)

def half_14_09_φ4 : Fin 4 → ℝ := Fin.snoc half_14_09_φ3 (47453087/500000000 : ℝ)

def half_14_09_φ5 : Fin 5 → ℝ := Fin.snoc half_14_09_φ4 (813481491/10000000000 : ℝ)

theorem half_14_09_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_14_09_φ5) (62498667971/10000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_14_09_φ5 (by norm_num [half_14_09_φ1, half_14_09_φ2, half_14_09_φ3, half_14_09_φ4, half_14_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_09_φ1, half_14_09_φ2, half_14_09_φ3, half_14_09_φ4, half_14_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_09_φ1, half_14_09_φ2, half_14_09_φ3, half_14_09_φ4, half_14_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_14_09_φ1, half_14_09_φ2, half_14_09_φ3, half_14_09_φ4, half_14_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_14_09_φ1, half_14_09_φ2, half_14_09_φ3, half_14_09_φ4, half_14_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_14_09_hx5 : SourcePowerBound (powerBoxCross 8 9 32 half_14_09_φ5) (15319606497/2000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 9) (r := 2) (v := 0) (w := 12) (D := 32)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_14_09_φ5 (by norm_num [half_14_09_φ1, half_14_09_φ2, half_14_09_φ3, half_14_09_φ4, half_14_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_09_φ1, half_14_09_φ2, half_14_09_φ3, half_14_09_φ4, half_14_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_14_09_hF2 (admissibleExponent_zero 8) (half_12_09)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_14_09_φ1, half_14_09_φ2, half_14_09_φ3, half_14_09_φ4, half_14_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_09_hx4 : SourcePowerBound (powerBoxCross 8 10 16 half_14_09_φ4) (92471773183/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 10) (u := 8) (t := 11)
    (D := 16) (ψ := (813481491/10000000000 : ℝ)) half_14_09_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_09_φ1, half_14_09_φ2, half_14_09_φ3, half_14_09_φ4, half_14_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_09_φ1, half_14_09_φ2, half_14_09_φ3, half_14_09_φ4, half_14_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_09_φ1, half_14_09_φ2, half_14_09_φ3, half_14_09_φ4, half_14_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_9) (half_11_09)
    (by simpa only [half_14_09_φ5, show (2:ℝ)*16=32 by norm_num] using half_14_09_hx5)
  exact h.weaken (by norm_num [half_14_09_φ1, half_14_09_φ2, half_14_09_φ3, half_14_09_φ4, half_14_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_09_hx3 : SourcePowerBound (powerBoxCross 8 11 8 half_14_09_φ3) (455326677/40000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 11) (u := 9) (t := 12)
    (D := 8) (ψ := (47453087/500000000 : ℝ)) half_14_09_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_09_φ1, half_14_09_φ2, half_14_09_φ3, half_14_09_φ4, half_14_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_09_φ1, half_14_09_φ2, half_14_09_φ3, half_14_09_φ4, half_14_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_09_φ1, half_14_09_φ2, half_14_09_φ3, half_14_09_φ4, half_14_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_10_09) (half_12_09)
    (by simpa only [half_14_09_φ4, show (2:ℝ)*8=16 by norm_num] using half_14_09_hx4)
  exact h.weaken (by norm_num [half_14_09_φ1, half_14_09_φ2, half_14_09_φ3, half_14_09_φ4, half_14_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_09_hx2 : SourcePowerBound (powerBoxCross 8 12 4 half_14_09_φ2) (141468324723/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 12) (u := 10) (t := 13)
    (D := 4) (ψ := (267581853/2500000000 : ℝ)) half_14_09_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_09_φ1, half_14_09_φ2, half_14_09_φ3, half_14_09_φ4, half_14_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_09_φ1, half_14_09_φ2, half_14_09_φ3, half_14_09_φ4, half_14_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_09_φ1, half_14_09_φ2, half_14_09_φ3, half_14_09_φ4, half_14_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_11_09) (half_13_09)
    (by simpa only [half_14_09_φ3, show (2:ℝ)*4=8 by norm_num] using half_14_09_hx3)
  exact h.weaken (by norm_num [half_14_09_φ1, half_14_09_φ2, half_14_09_φ3, half_14_09_φ4, half_14_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_09_hx1 : SourcePowerBound (powerBoxCross 8 13 2 half_14_09_φ1) (43642654671/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 13) (u := 11) (t := 14)
    (D := 2) (ψ := (561805431/5000000000 : ℝ)) half_14_09_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_09_φ1, half_14_09_φ2, half_14_09_φ3, half_14_09_φ4, half_14_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_09_φ1, half_14_09_φ2, half_14_09_φ3, half_14_09_φ4, half_14_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_09_φ1, half_14_09_φ2, half_14_09_φ3, half_14_09_φ4, half_14_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_12_09) (half_14_08)
    (by simpa only [half_14_09_φ2, show (2:ℝ)*2=4 by norm_num] using half_14_09_hx2)
  exact h.weaken (by norm_num [half_14_09_φ1, half_14_09_φ2, half_14_09_φ3, half_14_09_φ4, half_14_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_09 : AdmissibleExponent 8 28 (50909089321/2500000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 12) (ψ := (145328693/1250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_13_09)
    (by simpa only [half_14_09_φ1] using half_14_09_hx1)
  exact admissibleExponent_mono h (by norm_num [half_14_09_φ1, half_14_09_φ2, half_14_09_φ3, half_14_09_φ4, half_14_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_15_09_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (593494649/5000000000 : ℝ)

def half_15_09_φ2 : Fin 2 → ℝ := Fin.snoc half_15_09_φ1 (57848643/500000000 : ℝ)

def half_15_09_φ3 : Fin 3 → ℝ := Fin.snoc half_15_09_φ2 (1093719691/10000000000 : ℝ)

def half_15_09_φ4 : Fin 4 → ℝ := Fin.snoc half_15_09_φ3 (937474021/10000000000 : ℝ)

def half_15_09_φ5 : Fin 5 → ℝ := Fin.snoc half_15_09_φ4 (803549161/10000000000 : ℝ)

theorem half_15_09_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_15_09_φ5) (61247194349/10000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_15_09_φ5 (by norm_num [half_15_09_φ1, half_15_09_φ2, half_15_09_φ3, half_15_09_φ4, half_15_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_09_φ1, half_15_09_φ2, half_15_09_φ3, half_15_09_φ4, half_15_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_09_φ1, half_15_09_φ2, half_15_09_φ3, half_15_09_φ4, half_15_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_15_09_φ1, half_15_09_φ2, half_15_09_φ3, half_15_09_φ4, half_15_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_15_09_φ1, half_15_09_φ2, half_15_09_φ3, half_15_09_φ4, half_15_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_15_09_hx5 : SourcePowerBound (powerBoxCross 8 10 32 half_15_09_φ5) (84430810657/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 10) (r := 2) (v := 13) (w := 14) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_15_09_φ5 (by norm_num [half_15_09_φ1, half_15_09_φ2, half_15_09_φ3, half_15_09_φ4, half_15_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_09_φ1, half_15_09_φ2, half_15_09_φ3, half_15_09_φ4, half_15_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_15_09_hF2 (half_13_09) (half_14_09)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_15_09_φ1, half_15_09_φ2, half_15_09_φ3, half_15_09_φ4, half_15_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_09_hx4 : SourcePowerBound (powerBoxCross 8 11 16 half_15_09_φ4) (25345194511/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 11) (u := 9) (t := 12)
    (D := 16) (ψ := (803549161/10000000000 : ℝ)) half_15_09_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_09_φ1, half_15_09_φ2, half_15_09_φ3, half_15_09_φ4, half_15_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_09_φ1, half_15_09_φ2, half_15_09_φ3, half_15_09_φ4, half_15_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_09_φ1, half_15_09_φ2, half_15_09_φ3, half_15_09_φ4, half_15_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_10_09) (half_12_09)
    (by simpa only [half_15_09_φ5, show (2:ℝ)*16=32 by norm_num] using half_15_09_hx5)
  exact h.weaken (by norm_num [half_15_09_φ1, half_15_09_φ2, half_15_09_φ3, half_15_09_φ4, half_15_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_09_hx3 : SourcePowerBound (powerBoxCross 8 12 8 half_15_09_φ3) (6208623549/500000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 12) (u := 10) (t := 13)
    (D := 8) (ψ := (937474021/10000000000 : ℝ)) half_15_09_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_09_φ1, half_15_09_φ2, half_15_09_φ3, half_15_09_φ4, half_15_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_09_φ1, half_15_09_φ2, half_15_09_φ3, half_15_09_φ4, half_15_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_09_φ1, half_15_09_φ2, half_15_09_φ3, half_15_09_φ4, half_15_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_11_09) (half_13_09)
    (by simpa only [half_15_09_φ4, show (2:ℝ)*8=16 by norm_num] using half_15_09_hx4)
  exact h.weaken (by norm_num [half_15_09_φ1, half_15_09_φ2, half_15_09_φ3, half_15_09_φ4, half_15_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_09_hx2 : SourcePowerBound (powerBoxCross 8 13 4 half_15_09_φ2) (154412527253/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 13) (u := 11) (t := 14)
    (D := 4) (ψ := (1093719691/10000000000 : ℝ)) half_15_09_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_09_φ1, half_15_09_φ2, half_15_09_φ3, half_15_09_φ4, half_15_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_09_φ1, half_15_09_φ2, half_15_09_φ3, half_15_09_φ4, half_15_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_09_φ1, half_15_09_φ2, half_15_09_φ3, half_15_09_φ4, half_15_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_12_09) (half_14_09)
    (by simpa only [half_15_09_φ3, show (2:ℝ)*4=8 by norm_num] using half_15_09_hx3)
  exact h.weaken (by norm_num [half_15_09_φ1, half_15_09_φ2, half_15_09_φ3, half_15_09_φ4, half_15_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_09_hx1 : SourcePowerBound (powerBoxCross 8 14 2 half_15_09_φ1) (190651928907/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 14) (u := 12) (t := 15)
    (D := 2) (ψ := (57848643/500000000 : ℝ)) half_15_09_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_09_φ1, half_15_09_φ2, half_15_09_φ3, half_15_09_φ4, half_15_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_09_φ1, half_15_09_φ2, half_15_09_φ3, half_15_09_φ4, half_15_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_09_φ1, half_15_09_φ2, half_15_09_φ3, half_15_09_φ4, half_15_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_13_09) (half_15_08)
    (by simpa only [half_15_09_φ2, show (2:ℝ)*2=4 by norm_num] using half_15_09_hx2)
  exact h.weaken (by norm_num [half_15_09_φ1, half_15_09_φ2, half_15_09_φ3, half_15_09_φ4, half_15_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_09 : AdmissibleExponent 8 30 (222700639953/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 13) (ψ := (593494649/5000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_14_09)
    (by simpa only [half_15_09_φ1] using half_15_09_hx1)
  exact admissibleExponent_mono h (by norm_num [half_15_09_φ1, half_15_09_φ2, half_15_09_φ3, half_15_09_φ4, half_15_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_16_09_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (602604771/5000000000 : ℝ)

def half_16_09_φ2 : Fin 2 → ℝ := Fin.snoc half_16_09_φ1 (148145151/1250000000 : ℝ)

def half_16_09_φ3 : Fin 3 → ℝ := Fin.snoc half_16_09_φ2 (271772473/2500000000 : ℝ)

def half_16_09_φ4 : Fin 4 → ℝ := Fin.snoc half_16_09_φ3 (116473917/1250000000 : ℝ)

def half_16_09_φ5 : Fin 5 → ℝ := Fin.snoc half_16_09_φ4 (49917393/625000000 : ℝ)

theorem half_16_09_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_16_09_φ5) (30316732207/5000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_16_09_φ5 (by norm_num [half_16_09_φ1, half_16_09_φ2, half_16_09_φ3, half_16_09_φ4, half_16_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_09_φ1, half_16_09_φ2, half_16_09_φ3, half_16_09_φ4, half_16_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_09_φ1, half_16_09_φ2, half_16_09_φ3, half_16_09_φ4, half_16_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_16_09_φ1, half_16_09_φ2, half_16_09_φ3, half_16_09_φ4, half_16_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_16_09_φ1, half_16_09_φ2, half_16_09_φ3, half_16_09_φ4, half_16_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_16_09_hx5 : SourcePowerBound (powerBoxCross 8 11 32 half_16_09_φ5) (92914206539/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 11) (r := 2) (v := 14) (w := 15) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_16_09_φ5 (by norm_num [half_16_09_φ1, half_16_09_φ2, half_16_09_φ3, half_16_09_φ4, half_16_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_09_φ1, half_16_09_φ2, half_16_09_φ3, half_16_09_φ4, half_16_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_16_09_hF2 (half_14_09) (half_15_09)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_16_09_φ1, half_16_09_φ2, half_16_09_φ3, half_16_09_φ4, half_16_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_09_hx4 : SourcePowerBound (powerBoxCross 8 12 16 half_16_09_φ4) (111098893373/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 12) (u := 10) (t := 13)
    (D := 16) (ψ := (49917393/625000000 : ℝ)) half_16_09_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_09_φ1, half_16_09_φ2, half_16_09_φ3, half_16_09_φ4, half_16_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_09_φ1, half_16_09_φ2, half_16_09_φ3, half_16_09_φ4, half_16_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_09_φ1, half_16_09_φ2, half_16_09_φ3, half_16_09_φ4, half_16_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_11_09) (half_13_09)
    (by simpa only [half_16_09_φ5, show (2:ℝ)*16=32 by norm_num] using half_16_09_hx5)
  exact h.weaken (by norm_num [half_16_09_φ1, half_16_09_φ2, half_16_09_φ3, half_16_09_φ4, half_16_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_09_hx3 : SourcePowerBound (powerBoxCross 8 13 8 half_16_09_φ3) (135505242559/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 13) (u := 11) (t := 14)
    (D := 8) (ψ := (116473917/1250000000 : ℝ)) half_16_09_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_09_φ1, half_16_09_φ2, half_16_09_φ3, half_16_09_φ4, half_16_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_09_φ1, half_16_09_φ2, half_16_09_φ3, half_16_09_φ4, half_16_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_09_φ1, half_16_09_φ2, half_16_09_φ3, half_16_09_φ4, half_16_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_12_09) (half_14_09)
    (by simpa only [half_16_09_φ4, show (2:ℝ)*8=16 by norm_num] using half_16_09_hx4)
  exact h.weaken (by norm_num [half_16_09_φ1, half_16_09_φ2, half_16_09_φ3, half_16_09_φ4, half_16_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_09_hx2 : SourcePowerBound (powerBoxCross 8 14 4 half_16_09_φ2) (83854206247/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 14) (u := 12) (t := 15)
    (D := 4) (ψ := (271772473/2500000000 : ℝ)) half_16_09_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_09_φ1, half_16_09_φ2, half_16_09_φ3, half_16_09_φ4, half_16_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_09_φ1, half_16_09_φ2, half_16_09_φ3, half_16_09_φ4, half_16_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_09_φ1, half_16_09_φ2, half_16_09_φ3, half_16_09_φ4, half_16_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_13_09) (half_15_09)
    (by simpa only [half_16_09_φ3, show (2:ℝ)*4=8 by norm_num] using half_16_09_hx3)
  exact h.weaken (by norm_num [half_16_09_φ1, half_16_09_φ2, half_16_09_φ3, half_16_09_φ4, half_16_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_09_hx1 : SourcePowerBound (powerBoxCross 8 15 2 half_16_09_φ1) (207065755871/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 15) (u := 13) (t := 16)
    (D := 2) (ψ := (148145151/1250000000 : ℝ)) half_16_09_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_09_φ1, half_16_09_φ2, half_16_09_φ3, half_16_09_φ4, half_16_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_09_φ1, half_16_09_φ2, half_16_09_φ3, half_16_09_φ4, half_16_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_09_φ1, half_16_09_φ2, half_16_09_φ3, half_16_09_φ4, half_16_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_14_09) (half_16_08)
    (by simpa only [half_16_09_φ2, show (2:ℝ)*2=4 by norm_num] using half_16_09_hx2)
  exact h.weaken (by norm_num [half_16_09_φ1, half_16_09_φ2, half_16_09_φ3, half_16_09_φ4, half_16_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_09 : AdmissibleExponent 8 32 (242016832589/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 14) (ψ := (602604771/5000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_15_09)
    (by simpa only [half_16_09_φ1] using half_16_09_hx1)
  exact admissibleExponent_mono h (by norm_num [half_16_09_φ1, half_16_09_φ2, half_16_09_φ3, half_16_09_φ4, half_16_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_17_09_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1218845007/10000000000 : ℝ)

def half_17_09_φ2 : Fin 2 → ℝ := Fin.snoc half_17_09_φ1 (603046459/5000000000 : ℝ)

def half_17_09_φ3 : Fin 3 → ℝ := Fin.snoc half_17_09_φ2 (270537931/2500000000 : ℝ)

def half_17_09_φ4 : Fin 4 → ℝ := Fin.snoc half_17_09_φ3 (927558621/10000000000 : ℝ)

def half_17_09_φ5 : Fin 5 → ℝ := Fin.snoc half_17_09_φ4 (397525123/5000000000 : ℝ)

theorem half_17_09_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_17_09_φ5) (15044082791/2500000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_17_09_φ5 (by norm_num [half_17_09_φ1, half_17_09_φ2, half_17_09_φ3, half_17_09_φ4, half_17_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_09_φ1, half_17_09_φ2, half_17_09_φ3, half_17_09_φ4, half_17_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_09_φ1, half_17_09_φ2, half_17_09_φ3, half_17_09_φ4, half_17_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_17_09_φ1, half_17_09_φ2, half_17_09_φ3, half_17_09_φ4, half_17_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_17_09_φ1, half_17_09_φ2, half_17_09_φ3, half_17_09_φ4, half_17_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_17_09_hx5 : SourcePowerBound (powerBoxCross 8 12 32 half_17_09_φ5) (20326215393/2000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 12) (r := 2) (v := 0) (w := 16) (D := 32)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_17_09_φ5 (by norm_num [half_17_09_φ1, half_17_09_φ2, half_17_09_φ3, half_17_09_φ4, half_17_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_09_φ1, half_17_09_φ2, half_17_09_φ3, half_17_09_φ4, half_17_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_17_09_hF2 (admissibleExponent_zero 8) (half_16_09)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_17_09_φ1, half_17_09_φ2, half_17_09_φ3, half_17_09_φ4, half_17_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_09_hx4 : SourcePowerBound (powerBoxCross 8 13 16 half_17_09_φ4) (15137843129/1250000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 13) (u := 11) (t := 14)
    (D := 16) (ψ := (397525123/5000000000 : ℝ)) half_17_09_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_09_φ1, half_17_09_φ2, half_17_09_φ3, half_17_09_φ4, half_17_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_09_φ1, half_17_09_φ2, half_17_09_φ3, half_17_09_φ4, half_17_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_09_φ1, half_17_09_φ2, half_17_09_φ3, half_17_09_φ4, half_17_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_12_09) (half_14_09)
    (by simpa only [half_17_09_φ5, show (2:ℝ)*16=32 by norm_num] using half_17_09_hx5)
  exact h.weaken (by norm_num [half_17_09_φ1, half_17_09_φ2, half_17_09_φ3, half_17_09_φ4, half_17_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_09_hx3 : SourcePowerBound (powerBoxCross 8 14 8 half_17_09_φ3) (18396225753/1250000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 14) (u := 12) (t := 15)
    (D := 8) (ψ := (927558621/10000000000 : ℝ)) half_17_09_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_09_φ1, half_17_09_φ2, half_17_09_φ3, half_17_09_φ4, half_17_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_09_φ1, half_17_09_φ2, half_17_09_φ3, half_17_09_φ4, half_17_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_09_φ1, half_17_09_φ2, half_17_09_φ3, half_17_09_φ4, half_17_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_13_09) (half_15_09)
    (by simpa only [half_17_09_φ4, show (2:ℝ)*8=16 by norm_num] using half_17_09_hx4)
  exact h.weaken (by norm_num [half_17_09_φ1, half_17_09_φ2, half_17_09_φ3, half_17_09_φ4, half_17_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_09_hx2 : SourcePowerBound (powerBoxCross 8 15 4 half_17_09_φ2) (45342823763/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 15) (u := 13) (t := 16)
    (D := 4) (ψ := (270537931/2500000000 : ℝ)) half_17_09_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_09_φ1, half_17_09_φ2, half_17_09_φ3, half_17_09_φ4, half_17_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_09_φ1, half_17_09_φ2, half_17_09_φ3, half_17_09_φ4, half_17_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_09_φ1, half_17_09_φ2, half_17_09_φ3, half_17_09_φ4, half_17_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_14_09) (half_16_09)
    (by simpa only [half_17_09_φ3, show (2:ℝ)*4=8 by norm_num] using half_17_09_hx3)
  exact h.weaken (by norm_num [half_17_09_φ1, half_17_09_φ2, half_17_09_φ3, half_17_09_φ4, half_17_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_09_hx1 : SourcePowerBound (powerBoxCross 8 16 2 half_17_09_φ1) (223737576801/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 16) (u := 14) (t := 17)
    (D := 2) (ψ := (603046459/5000000000 : ℝ)) half_17_09_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_09_φ1, half_17_09_φ2, half_17_09_φ3, half_17_09_φ4, half_17_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_09_φ1, half_17_09_φ2, half_17_09_φ3, half_17_09_φ4, half_17_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_09_φ1, half_17_09_φ2, half_17_09_φ3, half_17_09_φ4, half_17_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_15_09) (half_17_08)
    (by simpa only [half_17_09_φ2, show (2:ℝ)*2=4 by norm_num] using half_17_09_hx2)
  exact h.weaken (by norm_num [half_17_09_φ1, half_17_09_φ2, half_17_09_φ3, half_17_09_φ4, half_17_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_09 : AdmissibleExponent 8 34 (130760886009/5000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 15) (ψ := (1218845007/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_16_09)
    (by simpa only [half_17_09_φ1] using half_17_09_hx1)
  exact admissibleExponent_mono h (by norm_num [half_17_09_φ1, half_17_09_φ2, half_17_09_φ3, half_17_09_φ4, half_17_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_18_09_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (153663361/1250000000 : ℝ)

def half_18_09_φ2 : Fin 2 → ℝ := Fin.snoc half_18_09_φ1 (1222094071/10000000000 : ℝ)

def half_18_09_φ3 : Fin 3 → ℝ := Fin.snoc half_18_09_φ2 (1078371291/10000000000 : ℝ)

def half_18_09_φ4 : Fin 4 → ℝ := Fin.snoc half_18_09_φ3 (924318249/10000000000 : ℝ)

def half_18_09_φ5 : Fin 5 → ℝ := Fin.snoc half_18_09_φ4 (158454557/2000000000 : ℝ)

theorem half_18_09_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_18_09_φ5) (14956592759/2500000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_18_09_φ5 (by norm_num [half_18_09_φ1, half_18_09_φ2, half_18_09_φ3, half_18_09_φ4, half_18_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_18_09_φ1, half_18_09_φ2, half_18_09_φ3, half_18_09_φ4, half_18_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_18_09_φ1, half_18_09_φ2, half_18_09_φ3, half_18_09_φ4, half_18_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_18_09_φ1, half_18_09_φ2, half_18_09_φ3, half_18_09_φ4, half_18_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_18_09_φ1, half_18_09_φ2, half_18_09_φ3, half_18_09_φ4, half_18_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_18_09_hx5 : SourcePowerBound (powerBoxCross 8 13 32 half_18_09_φ5) (110531824511/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 13) (r := 2) (v := 17) (w := 18) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_18_09_φ5 (by norm_num [half_18_09_φ1, half_18_09_φ2, half_18_09_φ3, half_18_09_φ4, half_18_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_18_09_φ1, half_18_09_φ2, half_18_09_φ3, half_18_09_φ4, half_18_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_18_09_hF2 (half_17_09) (half_18_08)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_18_09_φ1, half_18_09_φ2, half_18_09_φ3, half_18_09_φ4, half_18_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_18_09_hx4 : SourcePowerBound (powerBoxCross 8 14 16 half_18_09_φ4) (8208367817/625000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 14) (u := 12) (t := 15)
    (D := 16) (ψ := (158454557/2000000000 : ℝ)) half_18_09_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_18_09_φ1, half_18_09_φ2, half_18_09_φ3, half_18_09_φ4, half_18_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_18_09_φ1, half_18_09_φ2, half_18_09_φ3, half_18_09_φ4, half_18_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_18_09_φ1, half_18_09_φ2, half_18_09_φ3, half_18_09_φ4, half_18_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_13_09) (half_15_09)
    (by simpa only [half_18_09_φ5, show (2:ℝ)*16=32 by norm_num] using half_18_09_hx5)
  exact h.weaken (by norm_num [half_18_09_φ1, half_18_09_φ2, half_18_09_φ3, half_18_09_φ4, half_18_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_18_09_hx3 : SourcePowerBound (powerBoxCross 8 15 8 half_18_09_φ3) (39771559333/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 15) (u := 13) (t := 16)
    (D := 8) (ψ := (924318249/10000000000 : ℝ)) half_18_09_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_18_09_φ1, half_18_09_φ2, half_18_09_φ3, half_18_09_φ4, half_18_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_18_09_φ1, half_18_09_φ2, half_18_09_φ3, half_18_09_φ4, half_18_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_18_09_φ1, half_18_09_φ2, half_18_09_φ3, half_18_09_φ4, half_18_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_14_09) (half_16_09)
    (by simpa only [half_18_09_φ4, show (2:ℝ)*8=16 by norm_num] using half_18_09_hx4)
  exact h.weaken (by norm_num [half_18_09_φ1, half_18_09_φ2, half_18_09_φ3, half_18_09_φ4, half_18_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_18_09_hx2 : SourcePowerBound (powerBoxCross 8 16 4 half_18_09_φ2) (97652874451/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 16) (u := 14) (t := 17)
    (D := 4) (ψ := (1078371291/10000000000 : ℝ)) half_18_09_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_18_09_φ1, half_18_09_φ2, half_18_09_φ3, half_18_09_φ4, half_18_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_18_09_φ1, half_18_09_φ2, half_18_09_φ3, half_18_09_φ4, half_18_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_18_09_φ1, half_18_09_φ2, half_18_09_φ3, half_18_09_φ4, half_18_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_15_09) (half_17_09)
    (by simpa only [half_18_09_φ3, show (2:ℝ)*4=8 by norm_num] using half_18_09_hx3)
  exact h.weaken (by norm_num [half_18_09_φ1, half_18_09_φ2, half_18_09_φ3, half_18_09_φ4, half_18_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_18_09_hx1 : SourcePowerBound (powerBoxCross 8 17 2 half_18_09_φ1) (240602027337/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 17) (u := 15) (t := 18)
    (D := 2) (ψ := (1222094071/10000000000 : ℝ)) half_18_09_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_18_09_φ1, half_18_09_φ2, half_18_09_φ3, half_18_09_φ4, half_18_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_18_09_φ1, half_18_09_φ2, half_18_09_φ3, half_18_09_φ4, half_18_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_18_09_φ1, half_18_09_φ2, half_18_09_φ3, half_18_09_φ4, half_18_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_16_09) (half_18_08)
    (by simpa only [half_18_09_φ2, show (2:ℝ)*2=4 by norm_num] using half_18_09_hx2)
  exact h.weaken (by norm_num [half_18_09_φ1, half_18_09_φ2, half_18_09_φ3, half_18_09_φ4, half_18_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_18_09 : AdmissibleExponent 8 36 (281169154641/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 16) (ψ := (153663361/1250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_17_09)
    (by simpa only [half_18_09_φ1] using half_18_09_hx1)
  exact admissibleExponent_mono h (by norm_num [half_18_09_φ1, half_18_09_φ2, half_18_09_φ3, half_18_09_φ4, half_18_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_19_09_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (618423109/5000000000 : ℝ)

def half_19_09_φ2 : Fin 2 → ℝ := Fin.snoc half_19_09_φ1 (1234072471/10000000000 : ℝ)

def half_19_09_φ3 : Fin 3 → ℝ := Fin.snoc half_19_09_φ2 (268895761/2500000000 : ℝ)

def half_19_09_φ4 : Fin 4 → ℝ := Fin.snoc half_19_09_φ3 (921928323/10000000000 : ℝ)

def half_19_09_φ5 : Fin 5 → ℝ := Fin.snoc half_19_09_φ4 (790224277/10000000000 : ℝ)

theorem half_19_09_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_19_09_φ5) (59568259007/10000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_19_09_φ5 (by norm_num [half_19_09_φ1, half_19_09_φ2, half_19_09_φ3, half_19_09_φ4, half_19_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_19_09_φ1, half_19_09_φ2, half_19_09_φ3, half_19_09_φ4, half_19_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_19_09_φ1, half_19_09_φ2, half_19_09_φ3, half_19_09_φ4, half_19_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_19_09_φ1, half_19_09_φ2, half_19_09_φ3, half_19_09_φ4, half_19_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_19_09_φ1, half_19_09_φ2, half_19_09_φ3, half_19_09_φ4, half_19_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_19_09_hx5 : SourcePowerBound (powerBoxCross 8 14 32 half_19_09_φ5) (59781083801/5000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 14) (r := 2) (v := 18) (w := 19) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_19_09_φ5 (by norm_num [half_19_09_φ1, half_19_09_φ2, half_19_09_φ3, half_19_09_φ4, half_19_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_19_09_φ1, half_19_09_φ2, half_19_09_φ3, half_19_09_φ4, half_19_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_19_09_hF2 (half_18_09) (half_19_08)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_19_09_φ1, half_19_09_φ2, half_19_09_φ3, half_19_09_φ4, half_19_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_19_09_hx4 : SourcePowerBound (powerBoxCross 8 15 16 half_19_09_φ4) (708731291/50000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 15) (u := 13) (t := 16)
    (D := 16) (ψ := (790224277/10000000000 : ℝ)) half_19_09_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_19_09_φ1, half_19_09_φ2, half_19_09_φ3, half_19_09_φ4, half_19_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_19_09_φ1, half_19_09_φ2, half_19_09_φ3, half_19_09_φ4, half_19_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_19_09_φ1, half_19_09_φ2, half_19_09_φ3, half_19_09_φ4, half_19_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_14_09) (half_16_09)
    (by simpa only [half_19_09_φ5, show (2:ℝ)*16=32 by norm_num] using half_19_09_hx5)
  exact h.weaken (by norm_num [half_19_09_φ1, half_19_09_φ2, half_19_09_φ3, half_19_09_φ4, half_19_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_19_09_hx3 : SourcePowerBound (powerBoxCross 8 16 8 half_19_09_φ3) (42803712211/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 16) (u := 14) (t := 17)
    (D := 8) (ψ := (921928323/10000000000 : ℝ)) half_19_09_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_19_09_φ1, half_19_09_φ2, half_19_09_φ3, half_19_09_φ4, half_19_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_19_09_φ1, half_19_09_φ2, half_19_09_φ3, half_19_09_φ4, half_19_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_19_09_φ1, half_19_09_φ2, half_19_09_φ3, half_19_09_φ4, half_19_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_15_09) (half_17_09)
    (by simpa only [half_19_09_φ4, show (2:ℝ)*8=16 by norm_num] using half_19_09_hx4)
  exact h.weaken (by norm_num [half_19_09_φ1, half_19_09_φ2, half_19_09_φ3, half_19_09_φ4, half_19_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_19_09_hx2 : SourcePowerBound (powerBoxCross 8 17 4 half_19_09_φ2) (41895603513/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 17) (u := 15) (t := 18)
    (D := 4) (ψ := (268895761/2500000000 : ℝ)) half_19_09_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_19_09_φ1, half_19_09_φ2, half_19_09_φ3, half_19_09_φ4, half_19_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_19_09_φ1, half_19_09_φ2, half_19_09_φ3, half_19_09_φ4, half_19_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_19_09_φ1, half_19_09_φ2, half_19_09_φ3, half_19_09_φ4, half_19_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_16_09) (half_18_09)
    (by simpa only [half_19_09_φ3, show (2:ℝ)*4=8 by norm_num] using half_19_09_hx3)
  exact h.weaken (by norm_num [half_19_09_φ1, half_19_09_φ2, half_19_09_φ3, half_19_09_φ4, half_19_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_19_09_hx1 : SourcePowerBound (powerBoxCross 8 18 2 half_19_09_φ1) (257629700311/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 18) (u := 16) (t := 19)
    (D := 2) (ψ := (1234072471/10000000000 : ℝ)) half_19_09_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_19_09_φ1, half_19_09_φ2, half_19_09_φ3, half_19_09_φ4, half_19_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_19_09_φ1, half_19_09_φ2, half_19_09_φ3, half_19_09_φ4, half_19_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_19_09_φ1, half_19_09_φ2, half_19_09_φ3, half_19_09_φ4, half_19_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_17_09) (half_19_08)
    (by simpa only [half_19_09_φ2, show (2:ℝ)*2=4 by norm_num] using half_19_09_hx2)
  exact h.weaken (by norm_num [half_19_09_φ1, half_19_09_φ2, half_19_09_φ3, half_19_09_φ4, half_19_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_19_09 : AdmissibleExponent 8 38 (300919317941/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 17) (ψ := (618423109/5000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_18_09)
    (by simpa only [half_19_09_φ1] using half_19_09_hx1)
  exact admissibleExponent_mono h (by norm_num [half_19_09_φ1, half_19_09_φ2, half_19_09_φ3, half_19_09_φ4, half_19_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_20_09_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (621211631/5000000000 : ℝ)

def half_20_09_φ2 : Fin 2 → ℝ := Fin.snoc half_20_09_φ1 (1242734159/10000000000 : ℝ)

def half_20_09_φ3 : Fin 3 → ℝ := Fin.snoc half_20_09_φ2 (1073548939/10000000000 : ℝ)

def half_20_09_φ4 : Fin 4 → ℝ := Fin.snoc half_20_09_φ3 (184036961/2000000000 : ℝ)

def half_20_09_φ5 : Fin 5 → ℝ := Fin.snoc half_20_09_φ4 (788729833/10000000000 : ℝ)

theorem half_20_09_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_20_09_φ5) (29689979521/5000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_20_09_φ5 (by norm_num [half_20_09_φ1, half_20_09_φ2, half_20_09_φ3, half_20_09_φ4, half_20_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_20_09_φ1, half_20_09_φ2, half_20_09_φ3, half_20_09_φ4, half_20_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_20_09_φ1, half_20_09_φ2, half_20_09_φ3, half_20_09_φ4, half_20_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_20_09_φ1, half_20_09_φ2, half_20_09_φ3, half_20_09_φ4, half_20_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_20_09_φ1, half_20_09_φ2, half_20_09_φ3, half_20_09_φ4, half_20_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_20_09_hx5 : SourcePowerBound (powerBoxCross 8 15 32 half_20_09_φ5) (25738603069/2000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 15) (r := 2) (v := 0) (w := 20) (D := 32)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_20_09_φ5 (by norm_num [half_20_09_φ1, half_20_09_φ2, half_20_09_φ3, half_20_09_φ4, half_20_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_20_09_φ1, half_20_09_φ2, half_20_09_φ3, half_20_09_φ4, half_20_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_20_09_hF2 (admissibleExponent_zero 8) (half_20_08)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_20_09_φ1, half_20_09_φ2, half_20_09_φ3, half_20_09_φ4, half_20_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_20_09_hx4 : SourcePowerBound (powerBoxCross 8 16 16 half_20_09_φ4) (38075369869/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 16) (u := 14) (t := 17)
    (D := 16) (ψ := (788729833/10000000000 : ℝ)) half_20_09_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_20_09_φ1, half_20_09_φ2, half_20_09_φ3, half_20_09_φ4, half_20_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_20_09_φ1, half_20_09_φ2, half_20_09_φ3, half_20_09_φ4, half_20_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_20_09_φ1, half_20_09_φ2, half_20_09_φ3, half_20_09_φ4, half_20_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_15_09) (half_17_09)
    (by simpa only [half_20_09_φ5, show (2:ℝ)*16=32 by norm_num] using half_20_09_hx5)
  exact h.weaken (by norm_num [half_20_09_φ1, half_20_09_φ2, half_20_09_φ3, half_20_09_φ4, half_20_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_20_09_hx3 : SourcePowerBound (powerBoxCross 8 17 8 half_20_09_φ3) (91756393167/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 17) (u := 15) (t := 18)
    (D := 8) (ψ := (184036961/2000000000 : ℝ)) half_20_09_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_20_09_φ1, half_20_09_φ2, half_20_09_φ3, half_20_09_φ4, half_20_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_20_09_φ1, half_20_09_φ2, half_20_09_φ3, half_20_09_φ4, half_20_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_20_09_φ1, half_20_09_φ2, half_20_09_φ3, half_20_09_φ4, half_20_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_16_09) (half_18_09)
    (by simpa only [half_20_09_φ4, show (2:ℝ)*8=16 by norm_num] using half_20_09_hx4)
  exact h.weaken (by norm_num [half_20_09_φ1, half_20_09_φ2, half_20_09_φ3, half_20_09_φ4, half_20_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_20_09_hx2 : SourcePowerBound (powerBoxCross 8 18 4 half_20_09_φ2) (223839964853/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 18) (u := 16) (t := 19)
    (D := 4) (ψ := (1073548939/10000000000 : ℝ)) half_20_09_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_20_09_φ1, half_20_09_φ2, half_20_09_φ3, half_20_09_φ4, half_20_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_20_09_φ1, half_20_09_φ2, half_20_09_φ3, half_20_09_φ4, half_20_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_20_09_φ1, half_20_09_φ2, half_20_09_φ3, half_20_09_φ4, half_20_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_17_09) (half_19_09)
    (by simpa only [half_20_09_φ3, show (2:ℝ)*4=8 by norm_num] using half_20_09_hx3)
  exact h.weaken (by norm_num [half_20_09_φ1, half_20_09_φ2, half_20_09_φ3, half_20_09_φ4, half_20_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_20_09_hx1 : SourcePowerBound (powerBoxCross 8 19 2 half_20_09_φ1) (274774825147/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 19) (u := 17) (t := 20)
    (D := 2) (ψ := (1242734159/10000000000 : ℝ)) half_20_09_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_20_09_φ1, half_20_09_φ2, half_20_09_φ3, half_20_09_φ4, half_20_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_20_09_φ1, half_20_09_φ2, half_20_09_φ3, half_20_09_φ4, half_20_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_20_09_φ1, half_20_09_φ2, half_20_09_φ3, half_20_09_φ4, half_20_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_18_09) (half_20_08)
    (by simpa only [half_20_09_φ2, show (2:ℝ)*2=4 by norm_num] using half_20_09_hx2)
  exact h.weaken (by norm_num [half_20_09_φ1, half_20_09_φ2, half_20_09_φ3, half_20_09_φ4, half_20_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_20_09 : AdmissibleExponent 8 40 (320744485841/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 18) (ψ := (621211631/5000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_19_09)
    (by simpa only [half_20_09_φ1] using half_20_09_hx1)
  exact admissibleExponent_mono h (by norm_num [half_20_09_φ1, half_20_09_φ2, half_20_09_φ3, half_20_09_φ4, half_20_09_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_10_10_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (515803847/5000000000 : ℝ)

def half_10_10_φ2 : Fin 2 → ℝ := Fin.snoc half_10_10_φ1 (19228091/200000000 : ℝ)

def half_10_10_φ3 : Fin 3 → ℝ := Fin.snoc half_10_10_φ2 (167316259/2000000000 : ℝ)

def half_10_10_φ4 : Fin 4 → ℝ := Fin.snoc half_10_10_φ3 (549003443/10000000000 : ℝ)

theorem half_10_10_hF2 : SourcePowerBound (paddedMoment 8 0 2 16 half_10_10_φ4) (34524731689/5000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 4) (r := 0) (n := 1) (D := 16)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_10_10_φ4 (by norm_num [half_10_10_φ1, half_10_10_φ2, half_10_10_φ3, half_10_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_10_φ1, half_10_10_φ2, half_10_10_φ3, half_10_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_10_φ1, half_10_10_φ2, half_10_10_φ3, half_10_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_10_10_φ1, half_10_10_φ2, half_10_10_φ3, half_10_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_10_10_φ1, half_10_10_φ2, half_10_10_φ3, half_10_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_10_10_hx4 : SourcePowerBound (powerBoxCross 8 6 16 half_10_10_φ4) (66142533303/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 6) (r := 2) (v := 0) (w := 8) (D := 16)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_10_10_φ4 (by norm_num [half_10_10_φ1, half_10_10_φ2, half_10_10_φ3, half_10_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_10_φ1, half_10_10_φ2, half_10_10_φ3, half_10_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_10_10_hF2 (admissibleExponent_zero 8) (SeedCompletionHigher8SimpleSeeds.degree8_half_8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_10_10_φ1, half_10_10_φ2, half_10_10_φ3, half_10_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_10_hx3 : SourcePowerBound (powerBoxCross 8 7 8 half_10_10_φ3) (7647586909/1000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 7) (u := 5) (t := 8)
    (D := 8) (ψ := (549003443/10000000000 : ℝ)) half_10_10_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_10_φ1, half_10_10_φ2, half_10_10_φ3, half_10_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_10_φ1, half_10_10_φ2, half_10_10_φ3, half_10_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_10_φ1, half_10_10_φ2, half_10_10_φ3, half_10_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionEven8SecondSeeds.degree8_half_6) (SeedCompletionHigher8SimpleSeeds.degree8_half_8)
    (by simpa only [half_10_10_φ4, show (2:ℝ)*8=16 by norm_num] using half_10_10_hx4)
  exact h.weaken (by norm_num [half_10_10_φ1, half_10_10_φ2, half_10_10_φ3, half_10_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_10_hx2 : SourcePowerBound (powerBoxCross 8 8 4 half_10_10_φ2) (5784489173/625000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 8) (u := 6) (t := 9)
    (D := 4) (ψ := (167316259/2000000000 : ℝ)) half_10_10_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_10_φ1, half_10_10_φ2, half_10_10_φ3, half_10_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_10_φ1, half_10_10_φ2, half_10_10_φ3, half_10_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_10_φ1, half_10_10_φ2, half_10_10_φ3, half_10_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_7) (SeedCompletionHigher8SimpleSeeds.degree8_half_9)
    (by simpa only [half_10_10_φ3, show (2:ℝ)*4=8 by norm_num] using half_10_10_hx3)
  exact h.weaken (by norm_num [half_10_10_φ1, half_10_10_φ2, half_10_10_φ3, half_10_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_10_hx1 : SourcePowerBound (powerBoxCross 8 9 2 half_10_10_φ1) (113745801183/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 9) (u := 7) (t := 10)
    (D := 2) (ψ := (19228091/200000000 : ℝ)) half_10_10_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_10_φ1, half_10_10_φ2, half_10_10_φ3, half_10_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_10_φ1, half_10_10_φ2, half_10_10_φ3, half_10_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_10_φ1, half_10_10_φ2, half_10_10_φ3, half_10_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_8) (half_10_09)
    (by simpa only [half_10_10_φ2, show (2:ℝ)*2=4 by norm_num] using half_10_10_hx2)
  exact h.weaken (by norm_num [half_10_10_φ1, half_10_10_φ2, half_10_10_φ3, half_10_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_10 : AdmissibleExponent 8 20 (131283131981/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 8) (ψ := (515803847/5000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_9)
    (by simpa only [half_10_10_φ1] using half_10_10_hx1)
  exact admissibleExponent_mono h (by norm_num [half_10_10_φ1, half_10_10_φ2, half_10_10_φ3, half_10_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_11_10_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (107426393/1000000000 : ℝ)

def half_11_10_φ2 : Fin 2 → ℝ := Fin.snoc half_11_10_φ1 (202448371/2000000000 : ℝ)

def half_11_10_φ3 : Fin 3 → ℝ := Fin.snoc half_11_10_φ2 (11528667/125000000 : ℝ)

def half_11_10_φ4 : Fin 4 → ℝ := Fin.snoc half_11_10_φ3 (185119697/2500000000 : ℝ)

theorem half_11_10_hF2 : SourcePowerBound (paddedMoment 8 0 2 16 half_11_10_φ4) (61265163407/10000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 4) (r := 0) (n := 1) (D := 16)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_11_10_φ4 (by norm_num [half_11_10_φ1, half_11_10_φ2, half_11_10_φ3, half_11_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_10_φ1, half_11_10_φ2, half_11_10_φ3, half_11_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_10_φ1, half_11_10_φ2, half_11_10_φ3, half_11_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_11_10_φ1, half_11_10_φ2, half_11_10_φ3, half_11_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_11_10_φ1, half_11_10_φ2, half_11_10_φ3, half_11_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_11_10_hx4 : SourcePowerBound (powerBoxCross 8 7 16 half_11_10_φ4) (71626129979/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 7) (r := 2) (v := 9) (w := 10) (D := 16)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_11_10_φ4 (by norm_num [half_11_10_φ1, half_11_10_φ2, half_11_10_φ3, half_11_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_10_φ1, half_11_10_φ2, half_11_10_φ3, half_11_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_11_10_hF2 (SeedCompletionHigher8SimpleSeeds.degree8_half_9) (half_10_10)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_11_10_φ1, half_11_10_φ2, half_11_10_φ3, half_11_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_10_hx3 : SourcePowerBound (powerBoxCross 8 8 8 half_11_10_φ3) (85130178583/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 8) (u := 6) (t := 9)
    (D := 8) (ψ := (185119697/2500000000 : ℝ)) half_11_10_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_10_φ1, half_11_10_φ2, half_11_10_φ3, half_11_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_10_φ1, half_11_10_φ2, half_11_10_φ3, half_11_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_10_φ1, half_11_10_φ2, half_11_10_φ3, half_11_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_7) (SeedCompletionHigher8SimpleSeeds.degree8_half_9)
    (by simpa only [half_11_10_φ4, show (2:ℝ)*8=16 by norm_num] using half_11_10_hx4)
  exact h.weaken (by norm_num [half_11_10_φ1, half_11_10_φ2, half_11_10_φ3, half_11_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_10_hx2 : SourcePowerBound (powerBoxCross 8 9 4 half_11_10_φ2) (104124934517/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 9) (u := 7) (t := 10)
    (D := 4) (ψ := (11528667/125000000 : ℝ)) half_11_10_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_10_φ1, half_11_10_φ2, half_11_10_φ3, half_11_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_10_φ1, half_11_10_φ2, half_11_10_φ3, half_11_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_10_φ1, half_11_10_φ2, half_11_10_φ3, half_11_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_8) (half_10_10)
    (by simpa only [half_11_10_φ3, show (2:ℝ)*4=8 by norm_num] using half_11_10_hx3)
  exact h.weaken (by norm_num [half_11_10_φ1, half_11_10_φ2, half_11_10_φ3, half_11_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_10_hx1 : SourcePowerBound (powerBoxCross 8 10 2 half_11_10_φ1) (128254122587/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 10) (u := 8) (t := 11)
    (D := 2) (ψ := (202448371/2000000000 : ℝ)) half_11_10_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_10_φ1, half_11_10_φ2, half_11_10_φ3, half_11_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_10_φ1, half_11_10_φ2, half_11_10_φ3, half_11_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_10_φ1, half_11_10_φ2, half_11_10_φ3, half_11_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_9) (half_11_09)
    (by simpa only [half_11_10_φ2, show (2:ℝ)*2=4 by norm_num] using half_11_10_hx2)
  exact h.weaken (by norm_num [half_11_10_φ1, half_11_10_φ2, half_11_10_φ3, half_11_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_10 : AdmissibleExponent 8 22 (148665137257/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 9) (ψ := (107426393/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_10_10)
    (by simpa only [half_11_10_φ1] using half_11_10_hx1)
  exact admissibleExponent_mono h (by norm_num [half_11_10_φ1, half_11_10_φ2, half_11_10_φ3, half_11_10_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_12_10_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1107044537/10000000000 : ℝ)

def half_12_10_φ2 : Fin 2 → ℝ := Fin.snoc half_12_10_φ1 (211111801/2000000000 : ℝ)

def half_12_10_φ3 : Fin 3 → ℝ := Fin.snoc half_12_10_φ2 (24426019/250000000 : ℝ)

def half_12_10_φ4 : Fin 4 → ℝ := Fin.snoc half_12_10_φ3 (420998951/5000000000 : ℝ)

def half_12_10_φ5 : Fin 5 → ℝ := Fin.snoc half_12_10_φ4 (263984413/5000000000 : ℝ)

theorem half_12_10_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_12_10_φ5) (7529816837/1000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_12_10_φ5 (by norm_num [half_12_10_φ1, half_12_10_φ2, half_12_10_φ3, half_12_10_φ4, half_12_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_10_φ1, half_12_10_φ2, half_12_10_φ3, half_12_10_φ4, half_12_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_10_φ1, half_12_10_φ2, half_12_10_φ3, half_12_10_φ4, half_12_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_12_10_φ1, half_12_10_φ2, half_12_10_φ3, half_12_10_φ4, half_12_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_12_10_φ1, half_12_10_φ2, half_12_10_φ3, half_12_10_φ4, half_12_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_12_10_hx5 : SourcePowerBound (powerBoxCross 8 7 32 half_12_10_φ5) (34142447523/5000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 7) (r := 2) (v := 9) (w := 10) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_12_10_φ5 (by norm_num [half_12_10_φ1, half_12_10_φ2, half_12_10_φ3, half_12_10_φ4, half_12_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_10_φ1, half_12_10_φ2, half_12_10_φ3, half_12_10_φ4, half_12_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_12_10_hF2 (SeedCompletionHigher8SimpleSeeds.degree8_half_9) (half_10_10)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_12_10_φ1, half_12_10_φ2, half_12_10_φ3, half_12_10_φ4, half_12_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_10_hx4 : SourcePowerBound (powerBoxCross 8 8 16 half_12_10_φ4) (15620470693/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 8) (u := 6) (t := 9)
    (D := 16) (ψ := (263984413/5000000000 : ℝ)) half_12_10_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_10_φ1, half_12_10_φ2, half_12_10_φ3, half_12_10_φ4, half_12_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_10_φ1, half_12_10_φ2, half_12_10_φ3, half_12_10_φ4, half_12_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_10_φ1, half_12_10_φ2, half_12_10_φ3, half_12_10_φ4, half_12_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_7) (SeedCompletionHigher8SimpleSeeds.degree8_half_9)
    (by simpa only [half_12_10_φ5, show (2:ℝ)*16=32 by norm_num] using half_12_10_hx5)
  exact h.weaken (by norm_num [half_12_10_φ1, half_12_10_φ2, half_12_10_φ3, half_12_10_φ4, half_12_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_10_hx3 : SourcePowerBound (powerBoxCross 8 9 8 half_12_10_φ3) (23602463767/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 9) (u := 7) (t := 10)
    (D := 8) (ψ := (420998951/5000000000 : ℝ)) half_12_10_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_10_φ1, half_12_10_φ2, half_12_10_φ3, half_12_10_φ4, half_12_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_10_φ1, half_12_10_φ2, half_12_10_φ3, half_12_10_φ4, half_12_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_10_φ1, half_12_10_φ2, half_12_10_φ3, half_12_10_φ4, half_12_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_8) (half_10_10)
    (by simpa only [half_12_10_φ4, show (2:ℝ)*8=16 by norm_num] using half_12_10_hx4)
  exact h.weaken (by norm_num [half_12_10_φ1, half_12_10_φ2, half_12_10_φ3, half_12_10_φ4, half_12_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_10_hx2 : SourcePowerBound (powerBoxCross 8 10 4 half_12_10_φ2) (58099021303/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 10) (u := 8) (t := 11)
    (D := 4) (ψ := (24426019/250000000 : ℝ)) half_12_10_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_10_φ1, half_12_10_φ2, half_12_10_φ3, half_12_10_φ4, half_12_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_10_φ1, half_12_10_φ2, half_12_10_φ3, half_12_10_φ4, half_12_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_10_φ1, half_12_10_φ2, half_12_10_φ3, half_12_10_φ4, half_12_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_9) (half_11_10)
    (by simpa only [half_12_10_φ3, show (2:ℝ)*4=8 by norm_num] using half_12_10_hx3)
  exact h.weaken (by norm_num [half_12_10_φ1, half_12_10_φ2, half_12_10_φ3, half_12_10_φ4, half_12_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_10_hx1 : SourcePowerBound (powerBoxCross 8 11 2 half_12_10_φ1) (143314288999/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 11) (u := 9) (t := 12)
    (D := 2) (ψ := (211111801/2000000000 : ℝ)) half_12_10_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_10_φ1, half_12_10_φ2, half_12_10_φ3, half_12_10_φ4, half_12_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_10_φ1, half_12_10_φ2, half_12_10_φ3, half_12_10_φ4, half_12_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_10_φ1, half_12_10_φ2, half_12_10_φ3, half_12_10_φ4, half_12_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_10_10) (half_12_09)
    (by simpa only [half_12_10_φ2, show (2:ℝ)*2=4 by norm_num] using half_12_10_hx2)
  exact h.weaken (by norm_num [half_12_10_φ1, half_12_10_φ2, half_12_10_φ3, half_12_10_φ4, half_12_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_10 : AdmissibleExponent 8 24 (41640556069/2500000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 10) (ψ := (1107044537/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_11_10)
    (by simpa only [half_12_10_φ1] using half_12_10_hx1)
  exact admissibleExponent_mono h (by norm_num [half_12_10_φ1, half_12_10_φ2, half_12_10_φ3, half_12_10_φ4, half_12_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_13_10_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (141971887/1250000000 : ℝ)

def half_13_10_φ2 : Fin 2 → ℝ := Fin.snoc half_13_10_φ1 (545086949/5000000000 : ℝ)

def half_13_10_φ3 : Fin 3 → ℝ := Fin.snoc half_13_10_φ2 (64052279/625000000 : ℝ)

def half_13_10_φ4 : Fin 4 → ℝ := Fin.snoc half_13_10_φ3 (912397487/10000000000 : ℝ)

def half_13_10_φ5 : Fin 5 → ℝ := Fin.snoc half_13_10_φ4 (171219881/2500000000 : ℝ)

theorem half_13_10_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_13_10_φ5) (68190688151/10000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_13_10_φ5 (by norm_num [half_13_10_φ1, half_13_10_φ2, half_13_10_φ3, half_13_10_φ4, half_13_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_10_φ1, half_13_10_φ2, half_13_10_φ3, half_13_10_φ4, half_13_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_10_φ1, half_13_10_φ2, half_13_10_φ3, half_13_10_φ4, half_13_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_13_10_φ1, half_13_10_φ2, half_13_10_φ3, half_13_10_φ4, half_13_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_13_10_φ1, half_13_10_φ2, half_13_10_φ3, half_13_10_φ4, half_13_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_13_10_hx5 : SourcePowerBound (powerBoxCross 8 8 32 half_13_10_φ5) (72252409419/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 8) (r := 2) (v := 10) (w := 11) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_13_10_φ5 (by norm_num [half_13_10_φ1, half_13_10_φ2, half_13_10_φ3, half_13_10_φ4, half_13_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_10_φ1, half_13_10_φ2, half_13_10_φ3, half_13_10_φ4, half_13_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_13_10_hF2 (half_10_10) (half_11_10)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_13_10_φ1, half_13_10_φ2, half_13_10_φ3, half_13_10_φ4, half_13_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_10_hx4 : SourcePowerBound (powerBoxCross 8 9 16 half_13_10_φ4) (42502721011/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 9) (u := 7) (t := 10)
    (D := 16) (ψ := (171219881/2500000000 : ℝ)) half_13_10_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_10_φ1, half_13_10_φ2, half_13_10_φ3, half_13_10_φ4, half_13_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_10_φ1, half_13_10_φ2, half_13_10_φ3, half_13_10_φ4, half_13_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_10_φ1, half_13_10_φ2, half_13_10_φ3, half_13_10_φ4, half_13_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_8) (half_10_10)
    (by simpa only [half_13_10_φ5, show (2:ℝ)*16=32 by norm_num] using half_13_10_hx5)
  exact h.weaken (by norm_num [half_13_10_φ1, half_13_10_φ2, half_13_10_φ3, half_13_10_φ4, half_13_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_10_hx3 : SourcePowerBound (powerBoxCross 8 10 8 half_13_10_φ3) (104048995861/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 10) (u := 8) (t := 11)
    (D := 8) (ψ := (912397487/10000000000 : ℝ)) half_13_10_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_10_φ1, half_13_10_φ2, half_13_10_φ3, half_13_10_φ4, half_13_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_10_φ1, half_13_10_φ2, half_13_10_φ3, half_13_10_φ4, half_13_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_10_φ1, half_13_10_φ2, half_13_10_φ3, half_13_10_φ4, half_13_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_9) (half_11_10)
    (by simpa only [half_13_10_φ4, show (2:ℝ)*8=16 by norm_num] using half_13_10_hx4)
  exact h.weaken (by norm_num [half_13_10_φ1, half_13_10_φ2, half_13_10_φ3, half_13_10_φ4, half_13_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_10_hx2 : SourcePowerBound (powerBoxCross 8 11 4 half_13_10_φ2) (6435639211/500000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 11) (u := 9) (t := 12)
    (D := 4) (ψ := (64052279/625000000 : ℝ)) half_13_10_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_10_φ1, half_13_10_φ2, half_13_10_φ3, half_13_10_φ4, half_13_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_10_φ1, half_13_10_φ2, half_13_10_φ3, half_13_10_φ4, half_13_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_10_φ1, half_13_10_φ2, half_13_10_φ3, half_13_10_φ4, half_13_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_10_10) (half_12_10)
    (by simpa only [half_13_10_φ3, show (2:ℝ)*4=8 by norm_num] using half_13_10_hx3)
  exact h.weaken (by norm_num [half_13_10_φ1, half_13_10_φ2, half_13_10_φ3, half_13_10_φ4, half_13_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_10_hx1 : SourcePowerBound (powerBoxCross 8 12 2 half_13_10_φ1) (79390138377/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 12) (u := 10) (t := 13)
    (D := 2) (ψ := (545086949/5000000000 : ℝ)) half_13_10_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_10_φ1, half_13_10_φ2, half_13_10_φ3, half_13_10_φ4, half_13_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_10_φ1, half_13_10_φ2, half_13_10_φ3, half_13_10_φ4, half_13_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_10_φ1, half_13_10_φ2, half_13_10_φ3, half_13_10_φ4, half_13_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_11_10) (half_13_09)
    (by simpa only [half_13_10_φ2, show (2:ℝ)*2=4 by norm_num] using half_13_10_hx2)
  exact h.weaken (by norm_num [half_13_10_φ1, half_13_10_φ2, half_13_10_φ3, half_13_10_φ4, half_13_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_10 : AdmissibleExponent 8 26 (92451551981/5000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 11) (ψ := (141971887/1250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_12_10)
    (by simpa only [half_13_10_φ1] using half_13_10_hx1)
  exact admissibleExponent_mono h (by norm_num [half_13_10_φ1, half_13_10_φ2, half_13_10_φ3, half_13_10_φ4, half_13_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_14_10_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (581188883/5000000000 : ℝ)

def half_14_10_φ2 : Fin 2 → ℝ := Fin.snoc half_14_10_φ1 (561787117/5000000000 : ℝ)

def half_14_10_φ3 : Fin 3 → ℝ := Fin.snoc half_14_10_φ2 (26757057/250000000 : ℝ)

def half_14_10_φ4 : Fin 4 → ℝ := Fin.snoc half_14_10_φ3 (237277347/2500000000 : ℝ)

def half_14_10_φ5 : Fin 5 → ℝ := Fin.snoc half_14_10_φ4 (203380583/2500000000 : ℝ)

theorem half_14_10_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_14_10_φ5) (31251907/5000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_14_10_φ5 (by norm_num [half_14_10_φ1, half_14_10_φ2, half_14_10_φ3, half_14_10_φ4, half_14_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_10_φ1, half_14_10_φ2, half_14_10_φ3, half_14_10_φ4, half_14_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_10_φ1, half_14_10_φ2, half_14_10_φ3, half_14_10_φ4, half_14_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_14_10_φ1, half_14_10_φ2, half_14_10_φ3, half_14_10_φ4, half_14_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_14_10_φ1, half_14_10_φ2, half_14_10_φ3, half_14_10_φ4, half_14_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_14_10_hx5 : SourcePowerBound (powerBoxCross 8 9 32 half_14_10_φ5) (76601893703/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 9) (r := 2) (v := 0) (w := 12) (D := 32)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_14_10_φ5 (by norm_num [half_14_10_φ1, half_14_10_φ2, half_14_10_φ3, half_14_10_φ4, half_14_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_10_φ1, half_14_10_φ2, half_14_10_φ3, half_14_10_φ4, half_14_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_14_10_hF2 (admissibleExponent_zero 8) (half_12_10)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_14_10_φ1, half_14_10_φ2, half_14_10_φ3, half_14_10_φ4, half_14_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_10_hx4 : SourcePowerBound (powerBoxCross 8 10 16 half_14_10_φ4) (92477027097/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 10) (u := 8) (t := 11)
    (D := 16) (ψ := (203380583/2500000000 : ℝ)) half_14_10_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_10_φ1, half_14_10_φ2, half_14_10_φ3, half_14_10_φ4, half_14_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_10_φ1, half_14_10_φ2, half_14_10_φ3, half_14_10_φ4, half_14_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_10_φ1, half_14_10_φ2, half_14_10_φ3, half_14_10_φ4, half_14_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_9) (half_11_10)
    (by simpa only [half_14_10_φ5, show (2:ℝ)*16=32 by norm_num] using half_14_10_hx5)
  exact h.weaken (by norm_num [half_14_10_φ1, half_14_10_φ2, half_14_10_φ3, half_14_10_φ4, half_14_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_10_hx3 : SourcePowerBound (powerBoxCross 8 11 8 half_14_10_φ3) (2276765051/200000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 11) (u := 9) (t := 12)
    (D := 8) (ψ := (237277347/2500000000 : ℝ)) half_14_10_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_10_φ1, half_14_10_φ2, half_14_10_φ3, half_14_10_φ4, half_14_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_10_φ1, half_14_10_φ2, half_14_10_φ3, half_14_10_φ4, half_14_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_10_φ1, half_14_10_φ2, half_14_10_φ3, half_14_10_φ4, half_14_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_10_10) (half_12_10)
    (by simpa only [half_14_10_φ4, show (2:ℝ)*8=16 by norm_num] using half_14_10_hx4)
  exact h.weaken (by norm_num [half_14_10_φ1, half_14_10_φ2, half_14_10_φ3, half_14_10_φ4, half_14_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_10_hx2 : SourcePowerBound (powerBoxCross 8 12 4 half_14_10_φ2) (141473829181/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 12) (u := 10) (t := 13)
    (D := 4) (ψ := (26757057/250000000 : ℝ)) half_14_10_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_10_φ1, half_14_10_φ2, half_14_10_φ3, half_14_10_φ4, half_14_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_10_φ1, half_14_10_φ2, half_14_10_φ3, half_14_10_φ4, half_14_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_10_φ1, half_14_10_φ2, half_14_10_φ3, half_14_10_φ4, half_14_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_11_10) (half_13_10)
    (by simpa only [half_14_10_φ3, show (2:ℝ)*4=8 by norm_num] using half_14_10_hx3)
  exact h.weaken (by norm_num [half_14_10_φ1, half_14_10_φ2, half_14_10_φ3, half_14_10_φ4, half_14_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_10_hx1 : SourcePowerBound (powerBoxCross 8 13 2 half_14_10_φ1) (4364318901/250000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 13) (u := 11) (t := 14)
    (D := 2) (ψ := (561787117/5000000000 : ℝ)) half_14_10_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_10_φ1, half_14_10_φ2, half_14_10_φ3, half_14_10_φ4, half_14_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_10_φ1, half_14_10_φ2, half_14_10_φ3, half_14_10_φ4, half_14_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_10_φ1, half_14_10_φ2, half_14_10_φ3, half_14_10_φ4, half_14_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_12_10) (half_14_09)
    (by simpa only [half_14_10_φ2, show (2:ℝ)*2=4 by norm_num] using half_14_10_hx2)
  exact h.weaken (by norm_num [half_14_10_φ1, half_14_10_φ2, half_14_10_φ3, half_14_10_φ4, half_14_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_10 : AdmissibleExponent 8 28 (20363220019/1000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 12) (ψ := (581188883/5000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_13_10)
    (by simpa only [half_14_10_φ1] using half_14_10_hx1)
  exact admissibleExponent_mono h (by norm_num [half_14_10_φ1, half_14_10_φ2, half_14_10_φ3, half_14_10_φ4, half_14_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_15_10_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1186705391/10000000000 : ℝ)

def half_15_10_φ2 : Fin 2 → ℝ := Fin.snoc half_15_10_φ1 (1156933677/10000000000 : ℝ)

def half_15_10_φ3 : Fin 3 → ℝ := Fin.snoc half_15_10_φ2 (1093765847/10000000000 : ℝ)

def half_15_10_φ4 : Fin 4 → ℝ := Fin.snoc half_15_10_φ3 (937513583/10000000000 : ℝ)

def half_15_10_φ5 : Fin 5 → ℝ := Fin.snoc half_15_10_φ4 (803583071/10000000000 : ℝ)

theorem half_15_10_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_15_10_φ5) (61251467051/10000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_15_10_φ5 (by norm_num [half_15_10_φ1, half_15_10_φ2, half_15_10_φ3, half_15_10_φ4, half_15_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_10_φ1, half_15_10_φ2, half_15_10_φ3, half_15_10_φ4, half_15_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_10_φ1, half_15_10_φ2, half_15_10_φ3, half_15_10_φ4, half_15_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_15_10_φ1, half_15_10_φ2, half_15_10_φ3, half_15_10_φ4, half_15_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_15_10_φ1, half_15_10_φ2, half_15_10_φ3, half_15_10_φ4, half_15_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_15_10_hx5 : SourcePowerBound (powerBoxCross 8 10 32 half_15_10_φ5) (21108419097/2500000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 10) (r := 2) (v := 13) (w := 14) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_15_10_φ5 (by norm_num [half_15_10_φ1, half_15_10_φ2, half_15_10_φ3, half_15_10_φ4, half_15_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_10_φ1, half_15_10_φ2, half_15_10_φ3, half_15_10_φ4, half_15_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_15_10_hF2 (half_13_10) (half_14_10)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_15_10_φ1, half_15_10_φ2, half_15_10_φ3, half_15_10_φ4, half_15_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_10_hx4 : SourcePowerBound (powerBoxCross 8 11 16 half_15_10_φ4) (101384966961/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 11) (u := 9) (t := 12)
    (D := 16) (ψ := (803583071/10000000000 : ℝ)) half_15_10_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_10_φ1, half_15_10_φ2, half_15_10_φ3, half_15_10_φ4, half_15_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_10_φ1, half_15_10_φ2, half_15_10_φ3, half_15_10_φ4, half_15_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_10_φ1, half_15_10_φ2, half_15_10_φ3, half_15_10_φ4, half_15_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_10_10) (half_12_10)
    (by simpa only [half_15_10_φ5, show (2:ℝ)*16=32 by norm_num] using half_15_10_hx5)
  exact h.weaken (by norm_num [half_15_10_φ1, half_15_10_φ2, half_15_10_φ3, half_15_10_φ4, half_15_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_10_hx3 : SourcePowerBound (powerBoxCross 8 12 8 half_15_10_φ3) (124177668963/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 12) (u := 10) (t := 13)
    (D := 8) (ψ := (937513583/10000000000 : ℝ)) half_15_10_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_10_φ1, half_15_10_φ2, half_15_10_φ3, half_15_10_φ4, half_15_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_10_φ1, half_15_10_φ2, half_15_10_φ3, half_15_10_φ4, half_15_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_10_φ1, half_15_10_φ2, half_15_10_φ3, half_15_10_φ4, half_15_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_11_10) (half_13_10)
    (by simpa only [half_15_10_φ4, show (2:ℝ)*8=16 by norm_num] using half_15_10_hx4)
  exact h.weaken (by norm_num [half_15_10_φ1, half_15_10_φ2, half_15_10_φ3, half_15_10_φ4, half_15_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_10_hx2 : SourcePowerBound (powerBoxCross 8 13 4 half_15_10_φ2) (77209243043/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 13) (u := 11) (t := 14)
    (D := 4) (ψ := (1093765847/10000000000 : ℝ)) half_15_10_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_10_φ1, half_15_10_φ2, half_15_10_φ3, half_15_10_φ4, half_15_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_10_φ1, half_15_10_φ2, half_15_10_φ3, half_15_10_φ4, half_15_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_10_φ1, half_15_10_φ2, half_15_10_φ3, half_15_10_φ4, half_15_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_12_10) (half_14_10)
    (by simpa only [half_15_10_φ3, show (2:ℝ)*4=8 by norm_num] using half_15_10_hx3)
  exact h.weaken (by norm_num [half_15_10_φ1, half_15_10_φ2, half_15_10_φ3, half_15_10_φ4, half_15_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_10_hx1 : SourcePowerBound (powerBoxCross 8 14 2 half_15_10_φ1) (190653762613/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 14) (u := 12) (t := 15)
    (D := 2) (ψ := (1156933677/10000000000 : ℝ)) half_15_10_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_10_φ1, half_15_10_φ2, half_15_10_φ3, half_15_10_φ4, half_15_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_10_φ1, half_15_10_φ2, half_15_10_φ3, half_15_10_φ4, half_15_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_10_φ1, half_15_10_φ2, half_15_10_φ3, half_15_10_φ4, half_15_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_13_10) (half_15_09)
    (by simpa only [half_15_10_φ2, show (2:ℝ)*2=4 by norm_num] using half_15_10_hx2)
  exact h.weaken (by norm_num [half_15_10_φ1, half_15_10_φ2, half_15_10_φ3, half_15_10_φ4, half_15_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_10 : AdmissibleExponent 8 30 (22269480817/1000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 13) (ψ := (1186705391/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_14_10)
    (by simpa only [half_15_10_φ1] using half_15_10_hx1)
  exact admissibleExponent_mono h (by norm_num [half_15_10_φ1, half_15_10_φ2, half_15_10_φ3, half_15_10_φ4, half_15_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_16_10_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1204925719/10000000000 : ℝ)

def half_16_10_φ2 : Fin 2 → ℝ := Fin.snoc half_16_10_φ1 (1185139921/10000000000 : ℝ)

def half_16_10_φ3 : Fin 3 → ℝ := Fin.snoc half_16_10_φ2 (1087133479/10000000000 : ℝ)

def half_16_10_φ4 : Fin 4 → ℝ := Fin.snoc half_16_10_φ3 (931828697/10000000000 : ℝ)

def half_16_10_φ5 : Fin 5 → ℝ := Fin.snoc half_16_10_φ4 (798710311/10000000000 : ℝ)

theorem half_16_10_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_16_10_φ5) (60637499333/10000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_16_10_φ5 (by norm_num [half_16_10_φ1, half_16_10_φ2, half_16_10_φ3, half_16_10_φ4, half_16_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_10_φ1, half_16_10_φ2, half_16_10_φ3, half_16_10_φ4, half_16_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_10_φ1, half_16_10_φ2, half_16_10_φ3, half_16_10_φ4, half_16_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_16_10_φ1, half_16_10_φ2, half_16_10_φ3, half_16_10_φ4, half_16_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_16_10_φ1, half_16_10_φ2, half_16_10_φ3, half_16_10_φ4, half_16_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_16_10_hx5 : SourcePowerBound (powerBoxCross 8 11 32 half_16_10_φ5) (46458218743/5000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 11) (r := 2) (v := 14) (w := 15) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_16_10_φ5 (by norm_num [half_16_10_φ1, half_16_10_φ2, half_16_10_φ3, half_16_10_φ4, half_16_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_10_φ1, half_16_10_φ2, half_16_10_φ3, half_16_10_φ4, half_16_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_16_10_hF2 (half_14_10) (half_15_10)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_16_10_φ1, half_16_10_φ2, half_16_10_φ3, half_16_10_φ4, half_16_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_10_hx4 : SourcePowerBound (powerBoxCross 8 12 16 half_16_10_φ4) (55551242601/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 12) (u := 10) (t := 13)
    (D := 16) (ψ := (798710311/10000000000 : ℝ)) half_16_10_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_10_φ1, half_16_10_φ2, half_16_10_φ3, half_16_10_φ4, half_16_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_10_φ1, half_16_10_φ2, half_16_10_φ3, half_16_10_φ4, half_16_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_10_φ1, half_16_10_φ2, half_16_10_φ3, half_16_10_φ4, half_16_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_11_10) (half_13_10)
    (by simpa only [half_16_10_φ5, show (2:ℝ)*16=32 by norm_num] using half_16_10_hx5)
  exact h.weaken (by norm_num [half_16_10_φ1, half_16_10_φ2, half_16_10_φ3, half_16_10_φ4, half_16_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_10_hx3 : SourcePowerBound (powerBoxCross 8 13 8 half_16_10_φ3) (3387742261/250000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 13) (u := 11) (t := 14)
    (D := 8) (ψ := (931828697/10000000000 : ℝ)) half_16_10_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_10_φ1, half_16_10_φ2, half_16_10_φ3, half_16_10_φ4, half_16_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_10_φ1, half_16_10_φ2, half_16_10_φ3, half_16_10_φ4, half_16_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_10_φ1, half_16_10_φ2, half_16_10_φ3, half_16_10_φ4, half_16_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_12_10) (half_14_10)
    (by simpa only [half_16_10_φ4, show (2:ℝ)*8=16 by norm_num] using half_16_10_hx4)
  exact h.weaken (by norm_num [half_16_10_φ1, half_16_10_φ2, half_16_10_φ3, half_16_10_φ4, half_16_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_10_hx2 : SourcePowerBound (powerBoxCross 8 14 4 half_16_10_φ2) (20964178449/1250000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 14) (u := 12) (t := 15)
    (D := 4) (ψ := (1087133479/10000000000 : ℝ)) half_16_10_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_10_φ1, half_16_10_φ2, half_16_10_φ3, half_16_10_φ4, half_16_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_10_φ1, half_16_10_φ2, half_16_10_φ3, half_16_10_φ4, half_16_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_10_φ1, half_16_10_φ2, half_16_10_φ3, half_16_10_φ4, half_16_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_13_10) (half_15_10)
    (by simpa only [half_16_10_φ3, show (2:ℝ)*4=8 by norm_num] using half_16_10_hx3)
  exact h.weaken (by norm_num [half_16_10_φ1, half_16_10_φ2, half_16_10_φ3, half_16_10_φ4, half_16_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_10_hx1 : SourcePowerBound (powerBoxCross 8 15 2 half_16_10_φ1) (207066663707/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 15) (u := 13) (t := 16)
    (D := 2) (ψ := (1185139921/10000000000 : ℝ)) half_16_10_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_10_φ1, half_16_10_φ2, half_16_10_φ3, half_16_10_φ4, half_16_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_10_φ1, half_16_10_φ2, half_16_10_φ3, half_16_10_φ4, half_16_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_10_φ1, half_16_10_φ2, half_16_10_φ3, half_16_10_φ4, half_16_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_14_10) (half_16_09)
    (by simpa only [half_16_10_φ2, show (2:ℝ)*2=4 by norm_num] using half_16_10_hx2)
  exact h.weaken (by norm_num [half_16_10_φ1, half_16_10_φ2, half_16_10_φ3, half_16_10_φ4, half_16_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_10 : AdmissibleExponent 8 32 (121004754779/5000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 14) (ψ := (1204925719/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_15_10)
    (by simpa only [half_16_10_φ1] using half_16_10_hx1)
  exact admissibleExponent_mono h (by norm_num [half_16_10_φ1, half_16_10_φ2, half_16_10_φ3, half_16_10_φ4, half_16_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_17_10_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (152322481/1250000000 : ℝ)

def half_17_10_φ2 : Fin 2 → ℝ := Fin.snoc half_17_10_φ1 (603050757/5000000000 : ℝ)

def half_17_10_φ3 : Fin 3 → ℝ := Fin.snoc half_17_10_φ2 (135273547/1250000000 : ℝ)

def half_17_10_φ4 : Fin 4 → ℝ := Fin.snoc half_17_10_φ3 (927590037/10000000000 : ℝ)

def half_17_10_φ5 : Fin 5 → ℝ := Fin.snoc half_17_10_φ4 (397538587/5000000000 : ℝ)

theorem half_17_10_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_17_10_φ5) (60179724071/10000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_17_10_φ5 (by norm_num [half_17_10_φ1, half_17_10_φ2, half_17_10_φ3, half_17_10_φ4, half_17_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_10_φ1, half_17_10_φ2, half_17_10_φ3, half_17_10_φ4, half_17_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_10_φ1, half_17_10_φ2, half_17_10_φ3, half_17_10_φ4, half_17_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_17_10_φ1, half_17_10_φ2, half_17_10_φ3, half_17_10_φ4, half_17_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_17_10_φ1, half_17_10_φ2, half_17_10_φ3, half_17_10_φ4, half_17_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_17_10_hx5 : SourcePowerBound (powerBoxCross 8 12 32 half_17_10_φ5) (101632237769/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 12) (r := 2) (v := 0) (w := 16) (D := 32)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_17_10_φ5 (by norm_num [half_17_10_φ1, half_17_10_φ2, half_17_10_φ3, half_17_10_φ4, half_17_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_10_φ1, half_17_10_φ2, half_17_10_φ3, half_17_10_φ4, half_17_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_17_10_hF2 (admissibleExponent_zero 8) (half_16_10)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_17_10_φ1, half_17_10_φ2, half_17_10_φ3, half_17_10_φ4, half_17_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_10_hx4 : SourcePowerBound (powerBoxCross 8 13 16 half_17_10_φ4) (121105057237/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 13) (u := 11) (t := 14)
    (D := 16) (ψ := (397538587/5000000000 : ℝ)) half_17_10_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_10_φ1, half_17_10_φ2, half_17_10_φ3, half_17_10_φ4, half_17_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_10_φ1, half_17_10_φ2, half_17_10_φ3, half_17_10_φ4, half_17_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_10_φ1, half_17_10_φ2, half_17_10_φ3, half_17_10_φ4, half_17_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_12_10) (half_14_10)
    (by simpa only [half_17_10_φ5, show (2:ℝ)*16=32 by norm_num] using half_17_10_hx5)
  exact h.weaken (by norm_num [half_17_10_φ1, half_17_10_φ2, half_17_10_φ3, half_17_10_φ4, half_17_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_10_hx3 : SourcePowerBound (powerBoxCross 8 14 8 half_17_10_φ3) (4599146247/312500000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 14) (u := 12) (t := 15)
    (D := 8) (ψ := (927590037/10000000000 : ℝ)) half_17_10_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_10_φ1, half_17_10_φ2, half_17_10_φ3, half_17_10_φ4, half_17_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_10_φ1, half_17_10_φ2, half_17_10_φ3, half_17_10_φ4, half_17_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_10_φ1, half_17_10_φ2, half_17_10_φ3, half_17_10_φ4, half_17_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_13_10) (half_15_10)
    (by simpa only [half_17_10_φ4, show (2:ℝ)*8=16 by norm_num] using half_17_10_hx4)
  exact h.weaken (by norm_num [half_17_10_φ1, half_17_10_φ2, half_17_10_φ3, half_17_10_φ4, half_17_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_10_hx2 : SourcePowerBound (powerBoxCross 8 15 4 half_17_10_φ2) (90687227839/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 15) (u := 13) (t := 16)
    (D := 4) (ψ := (135273547/1250000000 : ℝ)) half_17_10_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_10_φ1, half_17_10_φ2, half_17_10_φ3, half_17_10_φ4, half_17_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_10_φ1, half_17_10_φ2, half_17_10_φ3, half_17_10_φ4, half_17_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_10_φ1, half_17_10_φ2, half_17_10_φ3, half_17_10_φ4, half_17_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_14_10) (half_16_10)
    (by simpa only [half_17_10_φ3, show (2:ℝ)*4=8 by norm_num] using half_17_10_hx3)
  exact h.weaken (by norm_num [half_17_10_φ1, half_17_10_φ2, half_17_10_φ3, half_17_10_φ4, half_17_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_10_hx1 : SourcePowerBound (powerBoxCross 8 16 2 half_17_10_φ1) (111868649137/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 16) (u := 14) (t := 17)
    (D := 2) (ψ := (603050757/5000000000 : ℝ)) half_17_10_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_10_φ1, half_17_10_φ2, half_17_10_φ3, half_17_10_φ4, half_17_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_10_φ1, half_17_10_φ2, half_17_10_φ3, half_17_10_φ4, half_17_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_10_φ1, half_17_10_φ2, half_17_10_φ3, half_17_10_φ4, half_17_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_15_10) (half_17_09)
    (by simpa only [half_17_10_φ2, show (2:ℝ)*2=4 by norm_num] using half_17_10_hx2)
  exact h.weaken (by norm_num [half_17_10_φ1, half_17_10_φ2, half_17_10_φ3, half_17_10_φ4, half_17_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_10 : AdmissibleExponent 8 34 (130756636781/5000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 15) (ψ := (152322481/1250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_16_10)
    (by simpa only [half_17_10_φ1] using half_17_10_hx1)
  exact admissibleExponent_mono h (by norm_num [half_17_10_φ1, half_17_10_φ2, half_17_10_φ3, half_17_10_φ4, half_17_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_18_10_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1229051683/10000000000 : ℝ)

def half_18_10_φ2 : Fin 2 → ℝ := Fin.snoc half_18_10_φ1 (244424821/2000000000 : ℝ)

def half_18_10_φ3 : Fin 3 → ℝ := Fin.snoc half_18_10_φ2 (539201729/5000000000 : ℝ)

def half_18_10_φ4 : Fin 4 → ℝ := Fin.snoc half_18_10_φ3 (924345821/10000000000 : ℝ)

def half_18_10_φ5 : Fin 5 → ℝ := Fin.snoc half_18_10_φ4 (396148209/5000000000 : ℝ)

theorem half_18_10_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_18_10_φ5) (11965869763/2000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_18_10_φ5 (by norm_num [half_18_10_φ1, half_18_10_φ2, half_18_10_φ3, half_18_10_φ4, half_18_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_18_10_φ1, half_18_10_φ2, half_18_10_φ3, half_18_10_φ4, half_18_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_18_10_φ1, half_18_10_φ2, half_18_10_φ3, half_18_10_φ4, half_18_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_18_10_φ1, half_18_10_φ2, half_18_10_φ3, half_18_10_φ4, half_18_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_18_10_φ1, half_18_10_φ2, half_18_10_φ3, half_18_10_φ4, half_18_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_18_10_hx5 : SourcePowerBound (powerBoxCross 8 13 32 half_18_10_φ5) (110531543427/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 13) (r := 2) (v := 17) (w := 18) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_18_10_φ5 (by norm_num [half_18_10_φ1, half_18_10_φ2, half_18_10_φ3, half_18_10_φ4, half_18_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_18_10_φ1, half_18_10_φ2, half_18_10_φ3, half_18_10_φ4, half_18_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_18_10_hF2 (half_17_10) (half_18_09)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_18_10_φ1, half_18_10_φ2, half_18_10_φ3, half_18_10_φ4, half_18_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

end Waring.SeedCompletionAlternate8Seeds
