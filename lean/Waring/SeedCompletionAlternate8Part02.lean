import Waring.SeedCompletionAlternate8Part01
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

def half_12_03_φ4 : Fin 4 → ℝ := Fin.snoc half_12_03_φ3 (1318203/15625000 : ℝ)

def half_12_03_φ5 : Fin 5 → ℝ := Fin.snoc half_12_03_φ4 (532939187/10000000000 : ℝ)

theorem half_12_03_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_12_03_φ5) (74695394513/10000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_12_03_φ5 (by norm_num [half_12_03_φ1, half_12_03_φ2, half_12_03_φ3, half_12_03_φ4, half_12_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_03_φ1, half_12_03_φ2, half_12_03_φ3, half_12_03_φ4, half_12_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_03_φ1, half_12_03_φ2, half_12_03_φ3, half_12_03_φ4, half_12_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_12_03_φ1, half_12_03_φ2, half_12_03_φ3, half_12_03_φ4, half_12_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_12_03_φ1, half_12_03_φ2, half_12_03_φ3, half_12_03_φ4, half_12_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_12_03_hx5 : SourcePowerBound (powerBoxCross 8 7 32 half_12_03_φ5) (67885189891/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 7) (r := 2) (v := 9) (w := 10) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_12_03_φ5 (by norm_num [half_12_03_φ1, half_12_03_φ2, half_12_03_φ3, half_12_03_φ4, half_12_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_03_φ1, half_12_03_φ2, half_12_03_φ3, half_12_03_φ4, half_12_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_12_03_hF2 (SeedCompletionHigher8SimpleSeeds.degree8_half_9) (half_10_03)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_12_03_φ1, half_12_03_φ2, half_12_03_φ3, half_12_03_φ4, half_12_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_03_hx4 : SourcePowerBound (powerBoxCross 8 8 16 half_12_03_φ4) (38857917667/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 8) (u := 6) (t := 9)
    (D := 16) (ψ := (532939187/10000000000 : ℝ)) half_12_03_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_03_φ1, half_12_03_φ2, half_12_03_φ3, half_12_03_φ4, half_12_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_03_φ1, half_12_03_φ2, half_12_03_φ3, half_12_03_φ4, half_12_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_03_φ1, half_12_03_φ2, half_12_03_φ3, half_12_03_φ4, half_12_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_7) (SeedCompletionHigher8SimpleSeeds.degree8_half_9)
    (by simpa only [half_12_03_φ5, show (2:ℝ)*16=32 by norm_num] using half_12_03_hx5)
  exact h.weaken (by norm_num [half_12_03_φ1, half_12_03_φ2, half_12_03_φ3, half_12_03_φ4, half_12_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_03_hx3 : SourcePowerBound (powerBoxCross 8 9 8 half_12_03_φ3) (94030709483/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 9) (u := 7) (t := 10)
    (D := 8) (ψ := (1318203/15625000 : ℝ)) half_12_03_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_03_φ1, half_12_03_φ2, half_12_03_φ3, half_12_03_φ4, half_12_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_03_φ1, half_12_03_φ2, half_12_03_φ3, half_12_03_φ4, half_12_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_03_φ1, half_12_03_φ2, half_12_03_φ3, half_12_03_φ4, half_12_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_8) (half_10_03)
    (by simpa only [half_12_03_φ4, show (2:ℝ)*8=16 by norm_num] using half_12_03_hx4)
  exact h.weaken (by norm_num [half_12_03_φ1, half_12_03_φ2, half_12_03_φ3, half_12_03_φ4, half_12_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_03_hx2 : SourcePowerBound (powerBoxCross 8 10 4 half_12_03_φ2) (115903945173/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 10) (u := 8) (t := 11)
    (D := 4) (ψ := (980580219/10000000000 : ℝ)) half_12_03_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_03_φ1, half_12_03_φ2, half_12_03_φ3, half_12_03_φ4, half_12_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_03_φ1, half_12_03_φ2, half_12_03_φ3, half_12_03_φ4, half_12_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_03_φ1, half_12_03_φ2, half_12_03_φ3, half_12_03_φ4, half_12_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_9) (half_11_03)
    (by simpa only [half_12_03_φ3, show (2:ℝ)*4=8 by norm_num] using half_12_03_hx3)
  exact h.weaken (by norm_num [half_12_03_φ1, half_12_03_φ2, half_12_03_φ3, half_12_03_φ4, half_12_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_03_hx1 : SourcePowerBound (powerBoxCross 8 11 2 half_12_03_φ1) (143254040421/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 11) (u := 9) (t := 12)
    (D := 2) (ψ := (1058601939/10000000000 : ℝ)) half_12_03_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_03_φ1, half_12_03_φ2, half_12_03_φ3, half_12_03_φ4, half_12_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_03_φ1, half_12_03_φ2, half_12_03_φ3, half_12_03_φ4, half_12_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_03_φ1, half_12_03_φ2, half_12_03_φ3, half_12_03_φ4, half_12_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_10_03) (half_12_02)
    (by simpa only [half_12_03_φ2, show (2:ℝ)*2=4 by norm_num] using half_12_03_hx2)
  exact h.weaken (by norm_num [half_12_03_φ1, half_12_03_φ2, half_12_03_φ3, half_12_03_φ4, half_12_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_03 : AdmissibleExponent 8 24 (166827449343/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 10) (ψ := (561271641/5000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_11_03)
    (by simpa only [half_12_03_φ1] using half_12_03_hx1)
  exact admissibleExponent_mono h (by norm_num [half_12_03_φ1, half_12_03_φ2, half_12_03_φ3, half_12_03_φ4, half_12_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_13_03_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (575176103/5000000000 : ℝ)

def half_13_03_φ2 : Fin 2 → ℝ := Fin.snoc half_13_03_φ1 (1090771507/10000000000 : ℝ)

def half_13_03_φ3 : Fin 3 → ℝ := Fin.snoc half_13_03_φ2 (1028877381/10000000000 : ℝ)

def half_13_03_φ4 : Fin 4 → ℝ := Fin.snoc half_13_03_φ3 (459474887/5000000000 : ℝ)

def half_13_03_φ5 : Fin 5 → ℝ := Fin.snoc half_13_03_φ4 (69556853/1000000000 : ℝ)

theorem half_13_03_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_13_03_φ5) (33712546321/5000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_13_03_φ5 (by norm_num [half_13_03_φ1, half_13_03_φ2, half_13_03_φ3, half_13_03_φ4, half_13_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_03_φ1, half_13_03_φ2, half_13_03_φ3, half_13_03_φ4, half_13_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_03_φ1, half_13_03_φ2, half_13_03_φ3, half_13_03_φ4, half_13_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_13_03_φ1, half_13_03_φ2, half_13_03_φ3, half_13_03_φ4, half_13_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_13_03_φ1, half_13_03_φ2, half_13_03_φ3, half_13_03_φ4, half_13_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_13_03_hx5 : SourcePowerBound (powerBoxCross 8 8 32 half_13_03_φ5) (71723882443/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 8) (r := 2) (v := 10) (w := 11) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_13_03_φ5 (by norm_num [half_13_03_φ1, half_13_03_φ2, half_13_03_φ3, half_13_03_φ4, half_13_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_03_φ1, half_13_03_φ2, half_13_03_φ3, half_13_03_φ4, half_13_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_13_03_hF2 (half_10_03) (half_11_03)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_13_03_φ1, half_13_03_φ2, half_13_03_φ3, half_13_03_φ4, half_13_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_03_hx4 : SourcePowerBound (powerBoxCross 8 9 16 half_13_03_φ4) (84582367137/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 9) (u := 7) (t := 10)
    (D := 16) (ψ := (69556853/1000000000 : ℝ)) half_13_03_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_03_φ1, half_13_03_φ2, half_13_03_φ3, half_13_03_φ4, half_13_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_03_φ1, half_13_03_φ2, half_13_03_φ3, half_13_03_φ4, half_13_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_03_φ1, half_13_03_φ2, half_13_03_φ3, half_13_03_φ4, half_13_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_8) (half_10_03)
    (by simpa only [half_13_03_φ5, show (2:ℝ)*16=32 by norm_num] using half_13_03_hx5)
  exact h.weaken (by norm_num [half_13_03_φ1, half_13_03_φ2, half_13_03_φ3, half_13_03_φ4, half_13_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_03_hx3 : SourcePowerBound (powerBoxCross 8 10 8 half_13_03_φ3) (103741689129/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 10) (u := 8) (t := 11)
    (D := 8) (ψ := (459474887/5000000000 : ℝ)) half_13_03_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_03_φ1, half_13_03_φ2, half_13_03_φ3, half_13_03_φ4, half_13_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_03_φ1, half_13_03_φ2, half_13_03_φ3, half_13_03_φ4, half_13_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_03_φ1, half_13_03_φ2, half_13_03_φ3, half_13_03_φ4, half_13_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_9) (half_11_03)
    (by simpa only [half_13_03_φ4, show (2:ℝ)*8=16 by norm_num] using half_13_03_hx4)
  exact h.weaken (by norm_num [half_13_03_φ1, half_13_03_φ2, half_13_03_φ3, half_13_03_φ4, half_13_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_03_hx2 : SourcePowerBound (powerBoxCross 8 11 4 half_13_03_φ2) (5140836949/400000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 11) (u := 9) (t := 12)
    (D := 4) (ψ := (1028877381/10000000000 : ℝ)) half_13_03_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_03_φ1, half_13_03_φ2, half_13_03_φ3, half_13_03_φ4, half_13_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_03_φ1, half_13_03_φ2, half_13_03_φ3, half_13_03_φ4, half_13_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_03_φ1, half_13_03_φ2, half_13_03_φ3, half_13_03_φ4, half_13_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_10_03) (half_12_03)
    (by simpa only [half_13_03_φ3, show (2:ℝ)*4=8 by norm_num] using half_13_03_hx3)
  exact h.weaken (by norm_num [half_13_03_φ1, half_13_03_φ2, half_13_03_φ3, half_13_03_φ4, half_13_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_03_hx1 : SourcePowerBound (powerBoxCross 8 12 2 half_13_03_φ1) (79393384557/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 12) (u := 10) (t := 13)
    (D := 2) (ψ := (1090771507/10000000000 : ℝ)) half_13_03_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_03_φ1, half_13_03_φ2, half_13_03_φ3, half_13_03_φ4, half_13_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_03_φ1, half_13_03_φ2, half_13_03_φ3, half_13_03_φ4, half_13_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_03_φ1, half_13_03_φ2, half_13_03_φ3, half_13_03_φ4, half_13_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_11_03) (half_13_02)
    (by simpa only [half_13_03_φ2, show (2:ℝ)*2=4 by norm_num] using half_13_03_hx2)
  exact h.weaken (by norm_num [half_13_03_φ1, half_13_03_φ2, half_13_03_φ3, half_13_03_φ4, half_13_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_03 : AdmissibleExponent 8 26 (46311217463/2500000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 11) (ψ := (575176103/5000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_12_03)
    (by simpa only [half_13_03_φ1] using half_13_03_hx1)
  exact admissibleExponent_mono h (by norm_num [half_13_03_φ1, half_13_03_φ2, half_13_03_φ3, half_13_03_φ4, half_13_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem chord_44 : AdmissibleExponent 8 28 (102158191047/5000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 28) (t := (1/2 : ℝ))
    (half_13_03) (half_15_02) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1 <;> norm_num

def half_14_03_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (587340057/5000000000 : ℝ)

def half_14_03_φ2 : Fin 2 → ℝ := Fin.snoc half_14_03_φ1 (1123047493/10000000000 : ℝ)

def half_14_03_φ3 : Fin 3 → ℝ := Fin.snoc half_14_03_φ2 (268339271/2500000000 : ℝ)

def half_14_03_φ4 : Fin 4 → ℝ := Fin.snoc half_14_03_φ3 (946987901/10000000000 : ℝ)

def half_14_03_φ5 : Fin 5 → ℝ := Fin.snoc half_14_03_φ4 (162340783/2000000000 : ℝ)

theorem half_14_03_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_14_03_φ5) (62274693353/10000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_14_03_φ5 (by norm_num [half_14_03_φ1, half_14_03_φ2, half_14_03_φ3, half_14_03_φ4, half_14_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_03_φ1, half_14_03_φ2, half_14_03_φ3, half_14_03_φ4, half_14_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_03_φ1, half_14_03_φ2, half_14_03_φ3, half_14_03_φ4, half_14_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_14_03_φ1, half_14_03_φ2, half_14_03_φ3, half_14_03_φ4, half_14_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_14_03_φ1, half_14_03_φ2, half_14_03_φ3, half_14_03_φ4, half_14_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_14_03_hx5 : SourcePowerBound (powerBoxCross 8 9 32 half_14_03_φ5) (76505195569/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 9) (r := 2) (v := 0) (w := 12) (D := 32)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_14_03_φ5 (by norm_num [half_14_03_φ1, half_14_03_φ2, half_14_03_φ3, half_14_03_φ4, half_14_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_03_φ1, half_14_03_φ2, half_14_03_φ3, half_14_03_φ4, half_14_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_14_03_hF2 (admissibleExponent_zero 8) (half_12_03)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_14_03_φ1, half_14_03_φ2, half_14_03_φ3, half_14_03_φ4, half_14_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_03_hx4 : SourcePowerBound (powerBoxCross 8 10 16 half_14_03_φ4) (4616177439/500000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 10) (u := 8) (t := 11)
    (D := 16) (ψ := (162340783/2000000000 : ℝ)) half_14_03_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_03_φ1, half_14_03_φ2, half_14_03_φ3, half_14_03_φ4, half_14_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_03_φ1, half_14_03_φ2, half_14_03_φ3, half_14_03_φ4, half_14_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_03_φ1, half_14_03_φ2, half_14_03_φ3, half_14_03_φ4, half_14_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_9) (half_11_03)
    (by simpa only [half_14_03_φ5, show (2:ℝ)*16=32 by norm_num] using half_14_03_hx5)
  exact h.weaken (by norm_num [half_14_03_φ1, half_14_03_φ2, half_14_03_φ3, half_14_03_φ4, half_14_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_03_hx3 : SourcePowerBound (powerBoxCross 8 11 8 half_14_03_φ3) (113653614677/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 11) (u := 9) (t := 12)
    (D := 8) (ψ := (946987901/10000000000 : ℝ)) half_14_03_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_03_φ1, half_14_03_φ2, half_14_03_φ3, half_14_03_φ4, half_14_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_03_φ1, half_14_03_φ2, half_14_03_φ3, half_14_03_φ4, half_14_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_03_φ1, half_14_03_φ2, half_14_03_φ3, half_14_03_φ4, half_14_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_10_03) (half_12_03)
    (by simpa only [half_14_03_φ4, show (2:ℝ)*8=16 by norm_num] using half_14_03_hx4)
  exact h.weaken (by norm_num [half_14_03_φ1, half_14_03_φ2, half_14_03_φ3, half_14_03_φ4, half_14_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_03_hx2 : SourcePowerBound (powerBoxCross 8 12 4 half_14_03_φ2) (141395332447/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 12) (u := 10) (t := 13)
    (D := 4) (ψ := (268339271/2500000000 : ℝ)) half_14_03_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_03_φ1, half_14_03_φ2, half_14_03_φ3, half_14_03_φ4, half_14_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_03_φ1, half_14_03_φ2, half_14_03_φ3, half_14_03_φ4, half_14_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_03_φ1, half_14_03_φ2, half_14_03_φ3, half_14_03_φ4, half_14_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_11_03) (half_13_03)
    (by simpa only [half_14_03_φ3, show (2:ℝ)*4=8 by norm_num] using half_14_03_hx3)
  exact h.weaken (by norm_num [half_14_03_φ1, half_14_03_φ2, half_14_03_φ3, half_14_03_φ4, half_14_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_03_hx1 : SourcePowerBound (powerBoxCross 8 13 2 half_14_03_φ1) (174659203491/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 13) (u := 11) (t := 14)
    (D := 2) (ψ := (1123047493/10000000000 : ℝ)) half_14_03_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_03_φ1, half_14_03_φ2, half_14_03_φ3, half_14_03_φ4, half_14_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_03_φ1, half_14_03_φ2, half_14_03_φ3, half_14_03_φ4, half_14_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_03_φ1, half_14_03_φ2, half_14_03_φ3, half_14_03_φ4, half_14_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_12_03) (chord_44)
    (by simpa only [half_14_03_φ2, show (2:ℝ)*2=4 by norm_num] using half_14_03_hx2)
  exact h.weaken (by norm_num [half_14_03_φ1, half_14_03_φ2, half_14_03_φ3, half_14_03_φ4, half_14_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_03 : AdmissibleExponent 8 28 (204026206341/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 12) (ψ := (587340057/5000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_13_03)
    (by simpa only [half_14_03_φ1] using half_14_03_hx1)
  exact admissibleExponent_mono h (by norm_num [half_14_03_φ1, half_14_03_φ2, half_14_03_φ3, half_14_03_φ4, half_14_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem chord_45 : AdmissibleExponent 8 30 (111677073837/5000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 30) (t := (1/2 : ℝ))
    (half_14_03) (half_16_02) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1 <;> norm_num

def half_15_03_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (119449443/1000000000 : ℝ)

def half_15_03_φ2 : Fin 2 → ℝ := Fin.snoc half_15_03_φ1 (1154515773/10000000000 : ℝ)

def half_15_03_φ3 : Fin 3 → ℝ := Fin.snoc half_15_03_φ2 (546499271/5000000000 : ℝ)

def half_15_03_φ4 : Fin 4 → ℝ := Fin.snoc half_15_03_φ3 (936855893/10000000000 : ℝ)

def half_15_03_φ5 : Fin 5 → ℝ := Fin.snoc half_15_03_φ4 (803019337/10000000000 : ℝ)

theorem half_15_03_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_15_03_φ5) (2447217461/400000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_15_03_φ5 (by norm_num [half_15_03_φ1, half_15_03_φ2, half_15_03_φ3, half_15_03_φ4, half_15_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_03_φ1, half_15_03_φ2, half_15_03_φ3, half_15_03_φ4, half_15_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_03_φ1, half_15_03_φ2, half_15_03_φ3, half_15_03_φ4, half_15_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_15_03_φ1, half_15_03_φ2, half_15_03_φ3, half_15_03_φ4, half_15_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_15_03_φ1, half_15_03_φ2, half_15_03_φ3, half_15_03_φ4, half_15_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_15_03_hx5 : SourcePowerBound (powerBoxCross 8 10 32 half_15_03_φ5) (10562152661/1250000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 10) (r := 2) (v := 13) (w := 14) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_15_03_φ5 (by norm_num [half_15_03_φ1, half_15_03_φ2, half_15_03_φ3, half_15_03_φ4, half_15_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_03_φ1, half_15_03_φ2, half_15_03_φ3, half_15_03_φ4, half_15_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_15_03_hF2 (half_13_03) (half_14_03)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_15_03_φ1, half_15_03_φ2, half_15_03_φ3, half_15_03_φ4, half_15_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_03_hx4 : SourcePowerBound (powerBoxCross 8 11 16 half_15_03_φ4) (6339953241/625000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 11) (u := 9) (t := 12)
    (D := 16) (ψ := (803019337/10000000000 : ℝ)) half_15_03_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_03_φ1, half_15_03_φ2, half_15_03_φ3, half_15_03_φ4, half_15_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_03_φ1, half_15_03_φ2, half_15_03_φ3, half_15_03_φ4, half_15_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_03_φ1, half_15_03_φ2, half_15_03_φ3, half_15_03_φ4, half_15_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_10_03) (half_12_03)
    (by simpa only [half_15_03_φ5, show (2:ℝ)*16=32 by norm_num] using half_15_03_hx5)
  exact h.weaken (by norm_num [half_15_03_φ1, half_15_03_φ2, half_15_03_φ3, half_15_03_φ4, half_15_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_03_hx3 : SourcePowerBound (powerBoxCross 8 12 8 half_15_03_φ3) (15531411753/1250000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 12) (u := 10) (t := 13)
    (D := 8) (ψ := (936855893/10000000000 : ℝ)) half_15_03_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_03_φ1, half_15_03_φ2, half_15_03_φ3, half_15_03_φ4, half_15_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_03_φ1, half_15_03_φ2, half_15_03_φ3, half_15_03_φ4, half_15_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_03_φ1, half_15_03_φ2, half_15_03_φ3, half_15_03_φ4, half_15_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_11_03) (half_13_03)
    (by simpa only [half_15_03_φ4, show (2:ℝ)*8=16 by norm_num] using half_15_03_hx4)
  exact h.weaken (by norm_num [half_15_03_φ1, half_15_03_φ2, half_15_03_φ3, half_15_03_φ4, half_15_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_03_hx2 : SourcePowerBound (powerBoxCross 8 13 4 half_15_03_φ2) (154523715687/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 13) (u := 11) (t := 14)
    (D := 4) (ψ := (546499271/5000000000 : ℝ)) half_15_03_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_03_φ1, half_15_03_φ2, half_15_03_φ3, half_15_03_φ4, half_15_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_03_φ1, half_15_03_φ2, half_15_03_φ3, half_15_03_φ4, half_15_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_03_φ1, half_15_03_φ2, half_15_03_φ3, half_15_03_φ4, half_15_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_12_03) (half_14_03)
    (by simpa only [half_15_03_φ3, show (2:ℝ)*4=8 by norm_num] using half_15_03_hx3)
  exact h.weaken (by norm_num [half_15_03_φ1, half_15_03_φ2, half_15_03_φ3, half_15_03_φ4, half_15_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_03_hx1 : SourcePowerBound (powerBoxCross 8 14 2 half_15_03_φ1) (190849884073/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 14) (u := 12) (t := 15)
    (D := 2) (ψ := (1154515773/10000000000 : ℝ)) half_15_03_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_03_φ1, half_15_03_φ2, half_15_03_φ3, half_15_03_φ4, half_15_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_03_φ1, half_15_03_φ2, half_15_03_φ3, half_15_03_φ4, half_15_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_03_φ1, half_15_03_φ2, half_15_03_φ3, half_15_03_φ4, half_15_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_13_03) (chord_45)
    (by simpa only [half_15_03_φ2, show (2:ℝ)*2=4 by norm_num] using half_15_03_hx2)
  exact h.weaken (by norm_num [half_15_03_φ1, half_15_03_φ2, half_15_03_φ3, half_15_03_φ4, half_15_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_03 : AdmissibleExponent 8 30 (223101233683/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 13) (ψ := (119449443/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_14_03)
    (by simpa only [half_15_03_φ1] using half_15_03_hx1)
  exact admissibleExponent_mono h (by norm_num [half_15_03_φ1, half_15_03_φ2, half_15_03_φ3, half_15_03_φ4, half_15_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem chord_46 : AdmissibleExponent 8 32 (121316777133/5000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 32) (t := (1/2 : ℝ))
    (half_15_03) (half_17_02) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1 <;> norm_num

def half_16_03_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (242111561/2000000000 : ℝ)

def half_16_03_φ2 : Fin 2 → ℝ := Fin.snoc half_16_03_φ1 (29506851/250000000 : ℝ)

def half_16_03_φ3 : Fin 3 → ℝ := Fin.snoc half_16_03_φ2 (1087024021/10000000000 : ℝ)

def half_16_03_φ4 : Fin 4 → ℝ := Fin.snoc half_16_03_φ3 (7453879/80000000 : ℝ)

def half_16_03_φ5 : Fin 5 → ℝ := Fin.snoc half_16_03_φ4 (798629893/10000000000 : ℝ)

theorem half_16_03_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_16_03_φ5) (30313683343/5000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_16_03_φ5 (by norm_num [half_16_03_φ1, half_16_03_φ2, half_16_03_φ3, half_16_03_φ4, half_16_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_03_φ1, half_16_03_φ2, half_16_03_φ3, half_16_03_φ4, half_16_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_03_φ1, half_16_03_φ2, half_16_03_φ3, half_16_03_φ4, half_16_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_16_03_φ1, half_16_03_φ2, half_16_03_φ3, half_16_03_φ4, half_16_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_16_03_φ1, half_16_03_φ2, half_16_03_φ3, half_16_03_φ4, half_16_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_16_03_hx5 : SourcePowerBound (powerBoxCross 8 11 32 half_16_03_φ5) (46525325109/5000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 11) (r := 2) (v := 14) (w := 15) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_16_03_φ5 (by norm_num [half_16_03_φ1, half_16_03_φ2, half_16_03_φ3, half_16_03_φ4, half_16_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_03_φ1, half_16_03_φ2, half_16_03_φ3, half_16_03_φ4, half_16_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_16_03_hF2 (half_14_03) (half_15_03)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_16_03_φ1, half_16_03_φ2, half_16_03_φ3, half_16_03_φ4, half_16_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_03_hx4 : SourcePowerBound (powerBoxCross 8 12 16 half_16_03_φ4) (111257103173/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 12) (u := 10) (t := 13)
    (D := 16) (ψ := (798629893/10000000000 : ℝ)) half_16_03_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_03_φ1, half_16_03_φ2, half_16_03_φ3, half_16_03_φ4, half_16_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_03_φ1, half_16_03_φ2, half_16_03_φ3, half_16_03_φ4, half_16_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_03_φ1, half_16_03_φ2, half_16_03_φ3, half_16_03_φ4, half_16_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_11_03) (half_13_03)
    (by simpa only [half_16_03_φ5, show (2:ℝ)*16=32 by norm_num] using half_16_03_hx5)
  exact h.weaken (by norm_num [half_16_03_φ1, half_16_03_φ2, half_16_03_φ3, half_16_03_φ4, half_16_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_03_hx3 : SourcePowerBound (powerBoxCross 8 13 8 half_16_03_φ3) (67852711681/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 13) (u := 11) (t := 14)
    (D := 8) (ψ := (7453879/80000000 : ℝ)) half_16_03_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_03_φ1, half_16_03_φ2, half_16_03_φ3, half_16_03_φ4, half_16_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_03_φ1, half_16_03_φ2, half_16_03_φ3, half_16_03_φ4, half_16_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_03_φ1, half_16_03_φ2, half_16_03_φ3, half_16_03_φ4, half_16_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_12_03) (half_14_03)
    (by simpa only [half_16_03_φ4, show (2:ℝ)*8=16 by norm_num] using half_16_03_hx4)
  exact h.weaken (by norm_num [half_16_03_φ1, half_16_03_φ2, half_16_03_φ3, half_16_03_φ4, half_16_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_03_hx2 : SourcePowerBound (powerBoxCross 8 14 4 half_16_03_φ2) (167953340621/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 14) (u := 12) (t := 15)
    (D := 4) (ψ := (1087024021/10000000000 : ℝ)) half_16_03_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_03_φ1, half_16_03_φ2, half_16_03_φ3, half_16_03_φ4, half_16_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_03_φ1, half_16_03_φ2, half_16_03_φ3, half_16_03_φ4, half_16_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_03_φ1, half_16_03_φ2, half_16_03_φ3, half_16_03_φ4, half_16_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_13_03) (half_15_03)
    (by simpa only [half_16_03_φ3, show (2:ℝ)*4=8 by norm_num] using half_16_03_hx3)
  exact h.weaken (by norm_num [half_16_03_φ1, half_16_03_φ2, half_16_03_φ3, half_16_03_φ4, half_16_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_03_hx1 : SourcePowerBound (powerBoxCross 8 15 2 half_16_03_φ1) (207304097523/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 15) (u := 13) (t := 16)
    (D := 2) (ψ := (29506851/250000000 : ℝ)) half_16_03_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_03_φ1, half_16_03_φ2, half_16_03_φ3, half_16_03_φ4, half_16_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_03_φ1, half_16_03_φ2, half_16_03_φ3, half_16_03_φ4, half_16_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_03_φ1, half_16_03_φ2, half_16_03_φ3, half_16_03_φ4, half_16_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_14_03) (chord_46)
    (by simpa only [half_16_03_φ2, show (2:ℝ)*2=4 by norm_num] using half_16_03_hx2)
  exact h.weaken (by norm_num [half_16_03_φ1, half_16_03_φ2, half_16_03_φ3, half_16_03_φ4, half_16_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_03 : AdmissibleExponent 8 32 (60602568467/2500000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 14) (ψ := (242111561/2000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_15_03)
    (by simpa only [half_16_03_φ1] using half_16_03_hx1)
  exact admissibleExponent_mono h (by norm_num [half_16_03_φ1, half_16_03_φ2, half_16_03_φ3, half_16_03_φ4, half_16_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem chord_47 : AdmissibleExponent 8 34 (65527444253/2500000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 34) (t := (1/2 : ℝ))
    (half_16_03) (half_18_02) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1 <;> norm_num

def half_17_03_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1223399131/10000000000 : ℝ)

def half_17_03_φ2 : Fin 2 → ℝ := Fin.snoc half_17_03_φ1 (75031213/625000000 : ℝ)

def half_17_03_φ3 : Fin 3 → ℝ := Fin.snoc half_17_03_φ2 (67643763/625000000 : ℝ)

def half_17_03_φ4 : Fin 4 → ℝ := Fin.snoc half_17_03_φ3 (927685893/10000000000 : ℝ)

def half_17_03_φ5 : Fin 5 → ℝ := Fin.snoc half_17_03_φ4 (99394917/1250000000 : ℝ)

theorem half_17_03_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_17_03_φ5) (7523759563/1250000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_17_03_φ5 (by norm_num [half_17_03_φ1, half_17_03_φ2, half_17_03_φ3, half_17_03_φ4, half_17_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_03_φ1, half_17_03_φ2, half_17_03_φ3, half_17_03_φ4, half_17_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_03_φ1, half_17_03_φ2, half_17_03_φ3, half_17_03_φ4, half_17_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_17_03_φ1, half_17_03_φ2, half_17_03_φ3, half_17_03_φ4, half_17_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_17_03_φ1, half_17_03_φ2, half_17_03_φ3, half_17_03_φ4, half_17_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_17_03_hx5 : SourcePowerBound (powerBoxCross 8 12 32 half_17_03_φ5) (6361698491/625000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 12) (r := 2) (v := 0) (w := 16) (D := 32)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_17_03_φ5 (by norm_num [half_17_03_φ1, half_17_03_φ2, half_17_03_φ3, half_17_03_φ4, half_17_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_03_φ1, half_17_03_φ2, half_17_03_φ3, half_17_03_φ4, half_17_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_17_03_hF2 (admissibleExponent_zero 8) (half_16_03)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_17_03_φ1, half_17_03_φ2, half_17_03_φ3, half_17_03_φ4, half_17_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_03_hx4 : SourcePowerBound (powerBoxCross 8 13 16 half_17_03_φ4) (1213009941/100000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 13) (u := 11) (t := 14)
    (D := 16) (ψ := (99394917/1250000000 : ℝ)) half_17_03_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_03_φ1, half_17_03_φ2, half_17_03_φ3, half_17_03_φ4, half_17_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_03_φ1, half_17_03_φ2, half_17_03_φ3, half_17_03_φ4, half_17_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_03_φ1, half_17_03_φ2, half_17_03_φ3, half_17_03_φ4, half_17_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_12_03) (half_14_03)
    (by simpa only [half_17_03_φ5, show (2:ℝ)*16=32 by norm_num] using half_17_03_hx5)
  exact h.weaken (by norm_num [half_17_03_φ1, half_17_03_φ2, half_17_03_φ3, half_17_03_φ4, half_17_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_03_hx3 : SourcePowerBound (powerBoxCross 8 14 8 half_17_03_φ3) (921335179/62500000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 14) (u := 12) (t := 15)
    (D := 8) (ψ := (927685893/10000000000 : ℝ)) half_17_03_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_03_φ1, half_17_03_φ2, half_17_03_φ3, half_17_03_φ4, half_17_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_03_φ1, half_17_03_φ2, half_17_03_φ3, half_17_03_φ4, half_17_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_03_φ1, half_17_03_φ2, half_17_03_φ3, half_17_03_φ4, half_17_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_13_03) (half_15_03)
    (by simpa only [half_17_03_φ4, show (2:ℝ)*8=16 by norm_num] using half_17_03_hx4)
  exact h.weaken (by norm_num [half_17_03_φ1, half_17_03_φ2, half_17_03_φ3, half_17_03_φ4, half_17_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_03_hx2 : SourcePowerBound (powerBoxCross 8 15 4 half_17_03_φ2) (181660463743/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 15) (u := 13) (t := 16)
    (D := 4) (ψ := (67643763/625000000 : ℝ)) half_17_03_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_03_φ1, half_17_03_φ2, half_17_03_φ3, half_17_03_φ4, half_17_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_03_φ1, half_17_03_φ2, half_17_03_φ3, half_17_03_φ4, half_17_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_03_φ1, half_17_03_φ2, half_17_03_φ3, half_17_03_φ4, half_17_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_14_03) (half_16_03)
    (by simpa only [half_17_03_φ3, show (2:ℝ)*4=8 by norm_num] using half_17_03_hx3)
  exact h.weaken (by norm_num [half_17_03_φ1, half_17_03_φ2, half_17_03_φ3, half_17_03_φ4, half_17_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_03_hx1 : SourcePowerBound (powerBoxCross 8 16 2 half_17_03_φ1) (55994305291/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 16) (u := 14) (t := 17)
    (D := 2) (ψ := (75031213/625000000 : ℝ)) half_17_03_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_03_φ1, half_17_03_φ2, half_17_03_φ3, half_17_03_φ4, half_17_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_03_φ1, half_17_03_φ2, half_17_03_φ3, half_17_03_φ4, half_17_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_03_φ1, half_17_03_φ2, half_17_03_φ3, half_17_03_φ4, half_17_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_15_03) (chord_47)
    (by simpa only [half_17_03_φ2, show (2:ℝ)*2=4 by norm_num] using half_17_03_hx2)
  exact h.weaken (by norm_num [half_17_03_φ1, half_17_03_φ2, half_17_03_φ3, half_17_03_φ4, half_17_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_03 : AdmissibleExponent 8 34 (10476103769/400000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 15) (ψ := (1223399131/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_16_03)
    (by simpa only [half_17_03_φ1] using half_17_03_hx1)
  exact admissibleExponent_mono h (by norm_num [half_17_03_φ1, half_17_03_φ2, half_17_03_φ3, half_17_03_φ4, half_17_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem chord_48 : AdmissibleExponent 8 36 (140881376269/5000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 36) (t := (1/2 : ℝ))
    (half_17_03) (half_19_02) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1 <;> norm_num

def half_18_03_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (247049199/2000000000 : ℝ)

def half_18_03_φ2 : Fin 2 → ℝ := Fin.snoc half_18_03_φ1 (950667/7812500 : ℝ)

def half_18_03_φ3 : Fin 3 → ℝ := Fin.snoc half_18_03_φ2 (1078271463/10000000000 : ℝ)

def half_18_03_φ4 : Fin 4 → ℝ := Fin.snoc half_18_03_φ3 (462116341/5000000000 : ℝ)

def half_18_03_φ5 : Fin 5 → ℝ := Fin.snoc half_18_03_φ4 (396099721/5000000000 : ℝ)

theorem half_18_03_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_18_03_φ5) (29908564909/5000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_18_03_φ5 (by norm_num [half_18_03_φ1, half_18_03_φ2, half_18_03_φ3, half_18_03_φ4, half_18_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_18_03_φ1, half_18_03_φ2, half_18_03_φ3, half_18_03_φ4, half_18_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_18_03_φ1, half_18_03_φ2, half_18_03_φ3, half_18_03_φ4, half_18_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_18_03_φ1, half_18_03_φ2, half_18_03_φ3, half_18_03_φ4, half_18_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_18_03_φ1, half_18_03_φ2, half_18_03_φ3, half_18_03_φ4, half_18_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_18_03_hx5 : SourcePowerBound (powerBoxCross 8 13 32 half_18_03_φ5) (110679853577/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 13) (r := 2) (v := 17) (w := 18) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_18_03_φ5 (by norm_num [half_18_03_φ1, half_18_03_φ2, half_18_03_φ3, half_18_03_φ4, half_18_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_18_03_φ1, half_18_03_φ2, half_18_03_φ3, half_18_03_φ4, half_18_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_18_03_hF2 (half_17_03) (chord_48)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_18_03_φ1, half_18_03_φ2, half_18_03_φ3, half_18_03_φ4, half_18_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_18_03_hx4 : SourcePowerBound (powerBoxCross 8 14 16 half_18_03_φ4) (131510541723/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 14) (u := 12) (t := 15)
    (D := 16) (ψ := (396099721/5000000000 : ℝ)) half_18_03_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_18_03_φ1, half_18_03_φ2, half_18_03_φ3, half_18_03_φ4, half_18_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_18_03_φ1, half_18_03_φ2, half_18_03_φ3, half_18_03_φ4, half_18_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_18_03_φ1, half_18_03_φ2, half_18_03_φ3, half_18_03_φ4, half_18_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_13_03) (half_15_03)
    (by simpa only [half_18_03_φ5, show (2:ℝ)*16=32 by norm_num] using half_18_03_hx5)
  exact h.weaken (by norm_num [half_18_03_φ1, half_18_03_φ2, half_18_03_φ3, half_18_03_φ4, half_18_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_18_03_hx3 : SourcePowerBound (powerBoxCross 8 15 8 half_18_03_φ3) (159291337049/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 15) (u := 13) (t := 16)
    (D := 8) (ψ := (462116341/5000000000 : ℝ)) half_18_03_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_18_03_φ1, half_18_03_φ2, half_18_03_φ3, half_18_03_φ4, half_18_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_18_03_φ1, half_18_03_φ2, half_18_03_φ3, half_18_03_φ4, half_18_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_18_03_φ1, half_18_03_φ2, half_18_03_φ3, half_18_03_φ4, half_18_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_14_03) (half_16_03)
    (by simpa only [half_18_03_φ4, show (2:ℝ)*8=16 by norm_num] using half_18_03_hx4)
  exact h.weaken (by norm_num [half_18_03_φ1, half_18_03_φ2, half_18_03_φ3, half_18_03_φ4, half_18_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_18_03_hx2 : SourcePowerBound (powerBoxCross 8 16 4 half_18_03_φ2) (3055296693/156250000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 16) (u := 14) (t := 17)
    (D := 4) (ψ := (1078271463/10000000000 : ℝ)) half_18_03_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_18_03_φ1, half_18_03_φ2, half_18_03_φ3, half_18_03_φ4, half_18_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_18_03_φ1, half_18_03_φ2, half_18_03_φ3, half_18_03_φ4, half_18_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_18_03_φ1, half_18_03_φ2, half_18_03_φ3, half_18_03_φ4, half_18_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_15_03) (half_17_03)
    (by simpa only [half_18_03_φ3, show (2:ℝ)*4=8 by norm_num] using half_18_03_hx3)
  exact h.weaken (by norm_num [half_18_03_φ1, half_18_03_φ2, half_18_03_φ3, half_18_03_φ4, half_18_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_18_03_hx1 : SourcePowerBound (powerBoxCross 8 17 2 half_18_03_φ1) (120393213581/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 17) (u := 15) (t := 18)
    (D := 2) (ψ := (950667/7812500 : ℝ)) half_18_03_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_18_03_φ1, half_18_03_φ2, half_18_03_φ3, half_18_03_φ4, half_18_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_18_03_φ1, half_18_03_φ2, half_18_03_φ3, half_18_03_φ4, half_18_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_18_03_φ1, half_18_03_φ2, half_18_03_φ3, half_18_03_φ4, half_18_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_16_03) (chord_48)
    (by simpa only [half_18_03_φ2, show (2:ℝ)*2=4 by norm_num] using half_18_03_hx2)
  exact h.weaken (by norm_num [half_18_03_φ1, half_18_03_φ2, half_18_03_φ3, half_18_03_φ4, half_18_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_18_03 : AdmissibleExponent 8 36 (281549544997/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 16) (ψ := (247049199/2000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_17_03)
    (by simpa only [half_18_03_φ1] using half_18_03_hx1)
  exact admissibleExponent_mono h (by norm_num [half_18_03_φ1, half_18_03_φ2, half_18_03_φ3, half_18_03_φ4, half_18_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem chord_49 : AdmissibleExponent 8 38 (603202836947/20000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 38) (t := (1/2 : ℝ))
    (half_18_03) (half_20_02) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1 <;> norm_num

def half_19_03_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (623859603/5000000000 : ℝ)

def half_19_03_φ2 : Fin 2 → ℝ := Fin.snoc half_19_03_φ1 (246080071/2000000000 : ℝ)

def half_19_03_φ3 : Fin 3 → ℝ := Fin.snoc half_19_03_φ2 (268638587/2500000000 : ℝ)

def half_19_03_φ4 : Fin 4 → ℝ := Fin.snoc half_19_03_φ3 (115130823/1250000000 : ℝ)

def half_19_03_φ5 : Fin 5 → ℝ := Fin.snoc half_19_03_φ4 (1578937/20000000 : ℝ)

theorem half_19_03_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_19_03_φ5) (59473031147/10000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_19_03_φ5 (by norm_num [half_19_03_φ1, half_19_03_φ2, half_19_03_φ3, half_19_03_φ4, half_19_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_19_03_φ1, half_19_03_φ2, half_19_03_φ3, half_19_03_φ4, half_19_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_19_03_φ1, half_19_03_φ2, half_19_03_φ3, half_19_03_φ4, half_19_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_19_03_φ1, half_19_03_φ2, half_19_03_φ3, half_19_03_φ4, half_19_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_19_03_φ1, half_19_03_φ2, half_19_03_φ3, half_19_03_φ4, half_19_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_19_03_hx5 : SourcePowerBound (powerBoxCross 8 14 32 half_19_03_φ5) (119640878319/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 14) (r := 2) (v := 18) (w := 19) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_19_03_φ5 (by norm_num [half_19_03_φ1, half_19_03_φ2, half_19_03_φ3, half_19_03_φ4, half_19_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_19_03_φ1, half_19_03_φ2, half_19_03_φ3, half_19_03_φ4, half_19_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_19_03_hF2 (half_18_03) (chord_49)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_19_03_φ1, half_19_03_φ2, half_19_03_φ3, half_19_03_φ4, half_19_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_19_03_hx4 : SourcePowerBound (powerBoxCross 8 15 16 half_19_03_φ4) (141801588623/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 15) (u := 13) (t := 16)
    (D := 16) (ψ := (1578937/20000000 : ℝ)) half_19_03_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_19_03_φ1, half_19_03_φ2, half_19_03_φ3, half_19_03_φ4, half_19_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_19_03_φ1, half_19_03_φ2, half_19_03_φ3, half_19_03_φ4, half_19_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_19_03_φ1, half_19_03_φ2, half_19_03_φ3, half_19_03_φ4, half_19_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_14_03) (half_16_03)
    (by simpa only [half_19_03_φ5, show (2:ℝ)*16=32 by norm_num] using half_19_03_hx5)
  exact h.weaken (by norm_num [half_19_03_φ1, half_19_03_φ2, half_19_03_φ3, half_19_03_φ4, half_19_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_19_03_hx3 : SourcePowerBound (powerBoxCross 8 16 8 half_19_03_φ3) (171250182551/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 16) (u := 14) (t := 17)
    (D := 8) (ψ := (115130823/1250000000 : ℝ)) half_19_03_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_19_03_φ1, half_19_03_φ2, half_19_03_φ3, half_19_03_φ4, half_19_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_19_03_φ1, half_19_03_φ2, half_19_03_φ3, half_19_03_φ4, half_19_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_19_03_φ1, half_19_03_φ2, half_19_03_φ3, half_19_03_φ4, half_19_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_15_03) (half_17_03)
    (by simpa only [half_19_03_φ4, show (2:ℝ)*8=16 by norm_num] using half_19_03_hx4)
  exact h.weaken (by norm_num [half_19_03_φ1, half_19_03_φ2, half_19_03_φ3, half_19_03_φ4, half_19_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_19_03_hx2 : SourcePowerBound (powerBoxCross 8 17 4 half_19_03_φ2) (209496365963/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 17) (u := 15) (t := 18)
    (D := 4) (ψ := (268638587/2500000000 : ℝ)) half_19_03_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_19_03_φ1, half_19_03_φ2, half_19_03_φ3, half_19_03_φ4, half_19_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_19_03_φ1, half_19_03_φ2, half_19_03_φ3, half_19_03_φ4, half_19_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_19_03_φ1, half_19_03_φ2, half_19_03_φ3, half_19_03_φ4, half_19_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_16_03) (half_18_03)
    (by simpa only [half_19_03_φ3, show (2:ℝ)*4=8 by norm_num] using half_19_03_hx3)
  exact h.weaken (by norm_num [half_19_03_φ1, half_19_03_φ2, half_19_03_φ3, half_19_03_φ4, half_19_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_19_03_hx1 : SourcePowerBound (powerBoxCross 8 18 2 half_19_03_φ1) (16104236671/625000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 18) (u := 16) (t := 19)
    (D := 2) (ψ := (246080071/2000000000 : ℝ)) half_19_03_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_19_03_φ1, half_19_03_φ2, half_19_03_φ3, half_19_03_φ4, half_19_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_19_03_φ1, half_19_03_φ2, half_19_03_φ3, half_19_03_φ4, half_19_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_19_03_φ1, half_19_03_φ2, half_19_03_φ3, half_19_03_φ4, half_19_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_17_03) (chord_49)
    (by simpa only [half_19_03_φ2, show (2:ℝ)*2=4 by norm_num] using half_19_03_hx2)
  exact h.weaken (by norm_num [half_19_03_φ1, half_19_03_φ2, half_19_03_φ3, half_19_03_φ4, half_19_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_19_03 : AdmissibleExponent 8 38 (150668979473/5000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 17) (ψ := (623859603/5000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_18_03)
    (by simpa only [half_19_03_φ1] using half_19_03_hx1)
  exact admissibleExponent_mono h (by norm_num [half_19_03_φ1, half_19_03_φ2, half_19_03_φ3, half_19_03_φ4, half_19_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_20_03_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1/8 : ℝ)

def half_20_03_φ2 : Fin 2 → ℝ := Fin.snoc half_20_03_φ1 (1242549583/10000000000 : ℝ)

def half_20_03_φ3 : Fin 3 → ℝ := Fin.snoc half_20_03_φ2 (268123229/2500000000 : ℝ)

def half_20_03_φ4 : Fin 4 → ℝ := Fin.snoc half_20_03_φ3 (459639821/5000000000 : ℝ)

def half_20_03_φ5 : Fin 5 → ℝ := Fin.snoc half_20_03_φ4 (787953979/10000000000 : ℝ)

theorem half_20_03_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_20_03_φ5) (1482055037/250000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_20_03_φ5 (by norm_num [half_20_03_φ1, half_20_03_φ2, half_20_03_φ3, half_20_03_φ4, half_20_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_20_03_φ1, half_20_03_φ2, half_20_03_φ3, half_20_03_φ4, half_20_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_20_03_φ1, half_20_03_φ2, half_20_03_φ3, half_20_03_φ4, half_20_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_20_03_φ1, half_20_03_φ2, half_20_03_φ3, half_20_03_φ4, half_20_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_20_03_φ1, half_20_03_φ2, half_20_03_φ3, half_20_03_φ4, half_20_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_20_03_hx5 : SourcePowerBound (powerBoxCross 8 15 32 half_20_03_φ5) (64436073289/5000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 15) (r := 2) (v := 0) (w := 20) (D := 32)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_20_03_φ5 (by norm_num [half_20_03_φ1, half_20_03_φ2, half_20_03_φ3, half_20_03_φ4, half_20_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_20_03_φ1, half_20_03_φ2, half_20_03_φ3, half_20_03_φ4, half_20_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_20_03_hF2 (admissibleExponent_zero 8) (half_20_02)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_20_03_φ1, half_20_03_φ2, half_20_03_φ3, half_20_03_φ4, half_20_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_20_03_hx4 : SourcePowerBound (powerBoxCross 8 16 16 half_20_03_φ4) (152394795501/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 16) (u := 14) (t := 17)
    (D := 16) (ψ := (787953979/10000000000 : ℝ)) half_20_03_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_20_03_φ1, half_20_03_φ2, half_20_03_φ3, half_20_03_φ4, half_20_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_20_03_φ1, half_20_03_φ2, half_20_03_φ3, half_20_03_φ4, half_20_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_20_03_φ1, half_20_03_φ2, half_20_03_φ3, half_20_03_φ4, half_20_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_15_03) (half_17_03)
    (by simpa only [half_20_03_φ5, show (2:ℝ)*16=32 by norm_num] using half_20_03_hx5)
  exact h.weaken (by norm_num [half_20_03_φ1, half_20_03_φ2, half_20_03_φ3, half_20_03_φ4, half_20_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_20_03_hx3 : SourcePowerBound (powerBoxCross 8 17 8 half_20_03_φ3) (2294456891/125000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 17) (u := 15) (t := 18)
    (D := 8) (ψ := (459639821/5000000000 : ℝ)) half_20_03_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_20_03_φ1, half_20_03_φ2, half_20_03_φ3, half_20_03_φ4, half_20_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_20_03_φ1, half_20_03_φ2, half_20_03_φ3, half_20_03_φ4, half_20_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_20_03_φ1, half_20_03_φ2, half_20_03_φ3, half_20_03_φ4, half_20_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_16_03) (half_18_03)
    (by simpa only [half_20_03_φ4, show (2:ℝ)*8=16 by norm_num] using half_20_03_hx4)
  exact h.weaken (by norm_num [half_20_03_φ1, half_20_03_φ2, half_20_03_φ3, half_20_03_φ4, half_20_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_20_03_hx2 : SourcePowerBound (powerBoxCross 8 18 4 half_20_03_φ2) (223864474491/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 18) (u := 16) (t := 19)
    (D := 4) (ψ := (268123229/2500000000 : ℝ)) half_20_03_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_20_03_φ1, half_20_03_φ2, half_20_03_φ3, half_20_03_φ4, half_20_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_20_03_φ1, half_20_03_φ2, half_20_03_φ3, half_20_03_φ4, half_20_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_20_03_φ1, half_20_03_φ2, half_20_03_φ3, half_20_03_φ4, half_20_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_17_03) (half_19_03)
    (by simpa only [half_20_03_φ3, show (2:ℝ)*4=8 by norm_num] using half_20_03_hx3)
  exact h.weaken (by norm_num [half_20_03_φ1, half_20_03_φ2, half_20_03_φ3, half_20_03_φ4, half_20_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_20_03_hx1 : SourcePowerBound (powerBoxCross 8 19 2 half_20_03_φ1) (275025170177/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 19) (u := 17) (t := 20)
    (D := 2) (ψ := (1242549583/10000000000 : ℝ)) half_20_03_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_20_03_φ1, half_20_03_φ2, half_20_03_φ3, half_20_03_φ4, half_20_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_20_03_φ1, half_20_03_φ2, half_20_03_φ3, half_20_03_φ4, half_20_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_20_03_φ1, half_20_03_φ2, half_20_03_φ3, half_20_03_φ4, half_20_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_18_03) (half_20_02)
    (by simpa only [half_20_03_φ2, show (2:ℝ)*2=4 by norm_num] using half_20_03_hx2)
  exact h.weaken (by norm_num [half_20_03_φ1, half_20_03_φ2, half_20_03_φ3, half_20_03_φ4, half_20_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_20_03 : AdmissibleExponent 8 40 (321275170177/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 18) (ψ := (1/8 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_19_03)
    (by simpa only [half_20_03_φ1] using half_20_03_hx1)
  exact admissibleExponent_mono h (by norm_num [half_20_03_φ1, half_20_03_φ2, half_20_03_φ3, half_20_03_φ4, half_20_03_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_10_04_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (41421341/400000000 : ℝ)

def half_10_04_φ2 : Fin 2 → ℝ := Fin.snoc half_10_04_φ1 (60091551/625000000 : ℝ)

def half_10_04_φ3 : Fin 3 → ℝ := Fin.snoc half_10_04_φ2 (209201319/2500000000 : ℝ)

def half_10_04_φ4 : Fin 4 → ℝ := Fin.snoc half_10_04_φ3 (109952863/2000000000 : ℝ)

theorem half_10_04_hF2 : SourcePowerBound (paddedMoment 8 0 2 16 half_10_04_φ4) (17236268357/2500000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 4) (r := 0) (n := 1) (D := 16)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_10_04_φ4 (by norm_num [half_10_04_φ1, half_10_04_φ2, half_10_04_φ3, half_10_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_04_φ1, half_10_04_φ2, half_10_04_φ3, half_10_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_04_φ1, half_10_04_φ2, half_10_04_φ3, half_10_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_10_04_φ1, half_10_04_φ2, half_10_04_φ3, half_10_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_10_04_φ1, half_10_04_φ2, half_10_04_φ3, half_10_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_10_04_hx4 : SourcePowerBound (powerBoxCross 8 6 16 half_10_04_φ4) (33039869767/5000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 6) (r := 2) (v := 0) (w := 8) (D := 16)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_10_04_φ4 (by norm_num [half_10_04_φ1, half_10_04_φ2, half_10_04_φ3, half_10_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_04_φ1, half_10_04_φ2, half_10_04_φ3, half_10_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_10_04_hF2 (admissibleExponent_zero 8) (SeedCompletionHigher8SimpleSeeds.degree8_half_8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_10_04_φ1, half_10_04_φ2, half_10_04_φ3, half_10_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_04_hx3 : SourcePowerBound (powerBoxCross 8 7 8 half_10_04_φ3) (1910330053/250000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 7) (u := 5) (t := 8)
    (D := 8) (ψ := (109952863/2000000000 : ℝ)) half_10_04_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_04_φ1, half_10_04_φ2, half_10_04_φ3, half_10_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_04_φ1, half_10_04_φ2, half_10_04_φ3, half_10_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_04_φ1, half_10_04_φ2, half_10_04_φ3, half_10_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionEven8SecondSeeds.degree8_half_6) (SeedCompletionHigher8SimpleSeeds.degree8_half_8)
    (by simpa only [half_10_04_φ4, show (2:ℝ)*8=16 by norm_num] using half_10_04_hx4)
  exact h.weaken (by norm_num [half_10_04_φ1, half_10_04_φ2, half_10_04_φ3, half_10_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_04_hx2 : SourcePowerBound (powerBoxCross 8 8 4 half_10_04_φ2) (46242585807/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 8) (u := 6) (t := 9)
    (D := 4) (ψ := (209201319/2500000000 : ℝ)) half_10_04_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_04_φ1, half_10_04_φ2, half_10_04_φ3, half_10_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_04_φ1, half_10_04_φ2, half_10_04_φ3, half_10_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_04_φ1, half_10_04_φ2, half_10_04_φ3, half_10_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_7) (SeedCompletionHigher8SimpleSeeds.degree8_half_9)
    (by simpa only [half_10_04_φ3, show (2:ℝ)*4=8 by norm_num] using half_10_04_hx3)
  exact h.weaken (by norm_num [half_10_04_φ1, half_10_04_φ2, half_10_04_φ3, half_10_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_04_hx1 : SourcePowerBound (powerBoxCross 8 9 2 half_10_04_φ1) (56852382411/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 9) (u := 7) (t := 10)
    (D := 2) (ψ := (60091551/625000000 : ℝ)) half_10_04_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_04_φ1, half_10_04_φ2, half_10_04_φ3, half_10_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_04_φ1, half_10_04_φ2, half_10_04_φ3, half_10_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_04_φ1, half_10_04_φ2, half_10_04_φ3, half_10_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_8) (half_10_03)
    (by simpa only [half_10_04_φ2, show (2:ℝ)*2=4 by norm_num] using half_10_04_hx2)
  exact h.weaken (by norm_num [half_10_04_φ1, half_10_04_φ2, half_10_04_φ3, half_10_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_04 : AdmissibleExponent 8 20 (131308834747/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 8) (ψ := (41421341/400000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_9)
    (by simpa only [half_10_04_φ1] using half_10_04_hx1)
  exact admissibleExponent_mono h (by norm_num [half_10_04_φ1, half_10_04_φ2, half_10_04_φ3, half_10_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_11_04_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1081662163/10000000000 : ℝ)

def half_11_04_φ2 : Fin 2 → ℝ := Fin.snoc half_11_04_φ1 (253433649/2500000000 : ℝ)

def half_11_04_φ3 : Fin 3 → ℝ := Fin.snoc half_11_04_φ2 (184593407/2000000000 : ℝ)

def half_11_04_φ4 : Fin 4 → ℝ := Fin.snoc half_11_04_φ3 (742504097/10000000000 : ℝ)

theorem half_11_04_hF2 : SourcePowerBound (paddedMoment 8 0 2 16 half_11_04_φ4) (61021774289/10000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 4) (r := 0) (n := 1) (D := 16)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_11_04_φ4 (by norm_num [half_11_04_φ1, half_11_04_φ2, half_11_04_φ3, half_11_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_04_φ1, half_11_04_φ2, half_11_04_φ3, half_11_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_04_φ1, half_11_04_φ2, half_11_04_φ3, half_11_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_11_04_φ1, half_11_04_φ2, half_11_04_φ3, half_11_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_11_04_φ1, half_11_04_φ2, half_11_04_φ3, half_11_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_11_04_hx4 : SourcePowerBound (powerBoxCross 8 7 16 half_11_04_φ4) (4466555203/625000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 7) (r := 2) (v := 9) (w := 10) (D := 16)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_11_04_φ4 (by norm_num [half_11_04_φ1, half_11_04_φ2, half_11_04_φ3, half_11_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_04_φ1, half_11_04_φ2, half_11_04_φ3, half_11_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_11_04_hF2 (SeedCompletionHigher8SimpleSeeds.degree8_half_9) (half_10_04)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_11_04_φ1, half_11_04_φ2, half_11_04_φ3, half_11_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_04_hx3 : SourcePowerBound (powerBoxCross 8 8 8 half_11_04_φ3) (84974471921/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 8) (u := 6) (t := 9)
    (D := 8) (ψ := (742504097/10000000000 : ℝ)) half_11_04_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_04_φ1, half_11_04_φ2, half_11_04_φ3, half_11_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_04_φ1, half_11_04_φ2, half_11_04_φ3, half_11_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_04_φ1, half_11_04_φ2, half_11_04_φ3, half_11_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_7) (SeedCompletionHigher8SimpleSeeds.degree8_half_9)
    (by simpa only [half_11_04_φ4, show (2:ℝ)*8=16 by norm_num] using half_11_04_hx4)
  exact h.weaken (by norm_num [half_11_04_φ1, half_11_04_φ2, half_11_04_φ3, half_11_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_04_hx2 : SourcePowerBound (powerBoxCross 8 9 4 half_11_04_φ2) (103972812103/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 9) (u := 7) (t := 10)
    (D := 4) (ψ := (184593407/2000000000 : ℝ)) half_11_04_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_04_φ1, half_11_04_φ2, half_11_04_φ3, half_11_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_04_φ1, half_11_04_φ2, half_11_04_φ3, half_11_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_04_φ1, half_11_04_φ2, half_11_04_φ3, half_11_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_8) (half_10_04)
    (by simpa only [half_11_04_φ3, show (2:ℝ)*4=8 by norm_num] using half_11_04_hx3)
  exact h.weaken (by norm_num [half_11_04_φ1, half_11_04_φ2, half_11_04_φ3, half_11_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_04_hx1 : SourcePowerBound (powerBoxCross 8 10 2 half_11_04_φ1) (128187317093/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 10) (u := 8) (t := 11)
    (D := 2) (ψ := (253433649/2500000000 : ℝ)) half_11_04_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_04_φ1, half_11_04_φ2, half_11_04_φ3, half_11_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_04_φ1, half_11_04_φ2, half_11_04_φ3, half_11_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_04_φ1, half_11_04_φ2, half_11_04_φ3, half_11_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_9) (half_11_03)
    (by simpa only [half_11_04_φ2, show (2:ℝ)*2=4 by norm_num] using half_11_04_hx2)
  exact h.weaken (by norm_num [half_11_04_φ1, half_11_04_φ2, half_11_04_φ3, half_11_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_04 : AdmissibleExponent 8 22 (14873889819/1000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 9) (ψ := (1081662163/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_10_04)
    (by simpa only [half_11_04_φ1] using half_11_04_hx1)
  exact admissibleExponent_mono h (by norm_num [half_11_04_φ1, half_11_04_φ2, half_11_04_φ3, half_11_04_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_12_04_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1115427381/10000000000 : ℝ)

def half_12_04_φ2 : Fin 2 → ℝ := Fin.snoc half_12_04_φ1 (528583253/5000000000 : ℝ)

def half_12_04_φ3 : Fin 3 → ℝ := Fin.snoc half_12_04_φ2 (48919617/500000000 : ℝ)

def half_12_04_φ4 : Fin 4 → ℝ := Fin.snoc half_12_04_φ3 (421385711/5000000000 : ℝ)

def half_12_04_φ5 : Fin 5 → ℝ := Fin.snoc half_12_04_φ4 (132577449/2500000000 : ℝ)

theorem half_12_04_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_12_04_φ5) (14998916731/2000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_12_04_φ5 (by norm_num [half_12_04_φ1, half_12_04_φ2, half_12_04_φ3, half_12_04_φ4, half_12_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_04_φ1, half_12_04_φ2, half_12_04_φ3, half_12_04_φ4, half_12_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_04_φ1, half_12_04_φ2, half_12_04_φ3, half_12_04_φ4, half_12_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_12_04_φ1, half_12_04_φ2, half_12_04_φ3, half_12_04_φ4, half_12_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_12_04_φ1, half_12_04_φ2, half_12_04_φ3, half_12_04_φ4, half_12_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_12_04_hx5 : SourcePowerBound (powerBoxCross 8 7 32 half_12_04_φ5) (34041143217/5000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 7) (r := 2) (v := 9) (w := 10) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_12_04_φ5 (by norm_num [half_12_04_φ1, half_12_04_φ2, half_12_04_φ3, half_12_04_φ4, half_12_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_04_φ1, half_12_04_φ2, half_12_04_φ3, half_12_04_φ4, half_12_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_12_04_hF2 (SeedCompletionHigher8SimpleSeeds.degree8_half_9) (half_10_04)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_12_04_φ1, half_12_04_φ2, half_12_04_φ3, half_12_04_φ4, half_12_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_04_hx4 : SourcePowerBound (powerBoxCross 8 8 16 half_12_04_φ4) (38952241427/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 8) (u := 6) (t := 9)
    (D := 16) (ψ := (132577449/2500000000 : ℝ)) half_12_04_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_04_φ1, half_12_04_φ2, half_12_04_φ3, half_12_04_φ4, half_12_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_04_φ1, half_12_04_φ2, half_12_04_φ3, half_12_04_φ4, half_12_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_04_φ1, half_12_04_φ2, half_12_04_φ3, half_12_04_φ4, half_12_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_7) (SeedCompletionHigher8SimpleSeeds.degree8_half_9)
    (by simpa only [half_12_04_φ5, show (2:ℝ)*16=32 by norm_num] using half_12_04_hx5)
  exact h.weaken (by norm_num [half_12_04_φ1, half_12_04_φ2, half_12_04_φ3, half_12_04_φ4, half_12_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_04_hx3 : SourcePowerBound (powerBoxCross 8 9 8 half_12_04_φ3) (94211376183/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 9) (u := 7) (t := 10)
    (D := 8) (ψ := (421385711/5000000000 : ℝ)) half_12_04_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_04_φ1, half_12_04_φ2, half_12_04_φ3, half_12_04_φ4, half_12_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_04_φ1, half_12_04_φ2, half_12_04_φ3, half_12_04_φ4, half_12_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_04_φ1, half_12_04_φ2, half_12_04_φ3, half_12_04_φ4, half_12_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_8) (half_10_04)
    (by simpa only [half_12_04_φ4, show (2:ℝ)*8=16 by norm_num] using half_12_04_hx4)
  exact h.weaken (by norm_num [half_12_04_φ1, half_12_04_φ2, half_12_04_φ3, half_12_04_φ4, half_12_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_04_hx2 : SourcePowerBound (powerBoxCross 8 10 4 half_12_04_φ2) (14503741553/1250000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 10) (u := 8) (t := 11)
    (D := 4) (ψ := (48919617/500000000 : ℝ)) half_12_04_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_04_φ1, half_12_04_φ2, half_12_04_φ3, half_12_04_φ4, half_12_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_04_φ1, half_12_04_φ2, half_12_04_φ3, half_12_04_φ4, half_12_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_04_φ1, half_12_04_φ2, half_12_04_φ3, half_12_04_φ4, half_12_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_9) (half_11_04)
    (by simpa only [half_12_04_φ3, show (2:ℝ)*4=8 by norm_num] using half_12_04_hx3)
  exact h.weaken (by norm_num [half_12_04_φ1, half_12_04_φ2, half_12_04_φ3, half_12_04_φ4, half_12_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_04_hx1 : SourcePowerBound (powerBoxCross 8 11 2 half_12_04_φ1) (143263581613/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 11) (u := 9) (t := 12)
    (D := 2) (ψ := (528583253/5000000000 : ℝ)) half_12_04_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_04_φ1, half_12_04_φ2, half_12_04_φ3, half_12_04_φ4, half_12_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_04_φ1, half_12_04_φ2, half_12_04_φ3, half_12_04_φ4, half_12_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_04_φ1, half_12_04_φ2, half_12_04_φ3, half_12_04_φ4, half_12_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_10_04) (half_12_03)
    (by simpa only [half_12_04_φ2, show (2:ℝ)*2=4 by norm_num] using half_12_04_hx2)
  exact h.weaken (by norm_num [half_12_04_φ1, half_12_04_φ2, half_12_04_φ3, half_12_04_φ4, half_12_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_04 : AdmissibleExponent 8 24 (83343778307/5000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 10) (ψ := (1115427381/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_11_04)
    (by simpa only [half_12_04_φ1] using half_12_04_hx1)
  exact admissibleExponent_mono h (by norm_num [half_12_04_φ1, half_12_04_φ2, half_12_04_φ3, half_12_04_φ4, half_12_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_13_04_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (572303289/5000000000 : ℝ)

def half_13_04_φ2 : Fin 2 → ℝ := Fin.snoc half_13_04_φ1 (54550921/500000000 : ℝ)

def half_13_04_φ3 : Fin 3 → ℝ := Fin.snoc half_13_04_φ2 (513431247/5000000000 : ℝ)

def half_13_04_φ4 : Fin 4 → ℝ := Fin.snoc half_13_04_φ3 (915160449/10000000000 : ℝ)

def half_13_04_φ5 : Fin 5 → ℝ := Fin.snoc half_13_04_φ4 (689782401/10000000000 : ℝ)

theorem half_13_04_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_13_04_φ5) (33891981409/5000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_13_04_φ5 (by norm_num [half_13_04_φ1, half_13_04_φ2, half_13_04_φ3, half_13_04_φ4, half_13_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_04_φ1, half_13_04_φ2, half_13_04_φ3, half_13_04_φ4, half_13_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_04_φ1, half_13_04_φ2, half_13_04_φ3, half_13_04_φ4, half_13_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_13_04_φ1, half_13_04_φ2, half_13_04_φ3, half_13_04_φ4, half_13_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_13_04_φ1, half_13_04_φ2, half_13_04_φ3, half_13_04_φ4, half_13_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_13_04_hx5 : SourcePowerBound (powerBoxCross 8 8 32 half_13_04_φ5) (35982711011/5000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 8) (r := 2) (v := 10) (w := 11) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_13_04_φ5 (by norm_num [half_13_04_φ1, half_13_04_φ2, half_13_04_φ3, half_13_04_φ4, half_13_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_04_φ1, half_13_04_φ2, half_13_04_φ3, half_13_04_φ4, half_13_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_13_04_hF2 (half_10_04) (half_11_04)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_13_04_φ1, half_13_04_φ2, half_13_04_φ3, half_13_04_φ4, half_13_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_04_hx4 : SourcePowerBound (powerBoxCross 8 9 16 half_13_04_φ4) (84760624443/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 9) (u := 7) (t := 10)
    (D := 16) (ψ := (689782401/10000000000 : ℝ)) half_13_04_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_04_φ1, half_13_04_φ2, half_13_04_φ3, half_13_04_φ4, half_13_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_04_φ1, half_13_04_φ2, half_13_04_φ3, half_13_04_φ4, half_13_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_04_φ1, half_13_04_φ2, half_13_04_φ3, half_13_04_φ4, half_13_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_8) (half_10_04)
    (by simpa only [half_13_04_φ5, show (2:ℝ)*16=32 by norm_num] using half_13_04_hx5)
  exact h.weaken (by norm_num [half_13_04_φ1, half_13_04_φ2, half_13_04_φ3, half_13_04_φ4, half_13_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_04_hx3 : SourcePowerBound (powerBoxCross 8 10 8 half_13_04_φ3) (51923489583/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 10) (u := 8) (t := 11)
    (D := 8) (ψ := (915160449/10000000000 : ℝ)) half_13_04_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_04_φ1, half_13_04_φ2, half_13_04_φ3, half_13_04_φ4, half_13_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_04_φ1, half_13_04_φ2, half_13_04_φ3, half_13_04_φ4, half_13_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_04_φ1, half_13_04_φ2, half_13_04_φ3, half_13_04_φ4, half_13_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_9) (half_11_04)
    (by simpa only [half_13_04_φ4, show (2:ℝ)*8=16 by norm_num] using half_13_04_hx4)
  exact h.weaken (by norm_num [half_13_04_φ1, half_13_04_φ2, half_13_04_φ3, half_13_04_φ4, half_13_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_04_hx2 : SourcePowerBound (powerBoxCross 8 11 4 half_13_04_φ2) (128565230669/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 11) (u := 9) (t := 12)
    (D := 4) (ψ := (513431247/5000000000 : ℝ)) half_13_04_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_04_φ1, half_13_04_φ2, half_13_04_φ3, half_13_04_φ4, half_13_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_04_φ1, half_13_04_φ2, half_13_04_φ3, half_13_04_φ4, half_13_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_04_φ1, half_13_04_φ2, half_13_04_φ3, half_13_04_φ4, half_13_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_10_04) (half_12_04)
    (by simpa only [half_13_04_φ3, show (2:ℝ)*4=8 by norm_num] using half_13_04_hx3)
  exact h.weaken (by norm_num [half_13_04_φ1, half_13_04_φ2, half_13_04_φ3, half_13_04_φ4, half_13_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_04_hx1 : SourcePowerBound (powerBoxCross 8 12 2 half_13_04_φ1) (158752995819/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 12) (u := 10) (t := 13)
    (D := 2) (ψ := (54550921/500000000 : ℝ)) half_13_04_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_04_φ1, half_13_04_φ2, half_13_04_φ3, half_13_04_φ4, half_13_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_04_φ1, half_13_04_φ2, half_13_04_φ3, half_13_04_φ4, half_13_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_04_φ1, half_13_04_φ2, half_13_04_φ3, half_13_04_φ4, half_13_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_11_04) (half_13_03)
    (by simpa only [half_13_04_φ2, show (2:ℝ)*2=4 by norm_num] using half_13_04_hx2)
  exact h.weaken (by norm_num [half_13_04_φ1, half_13_04_φ2, half_13_04_φ3, half_13_04_φ4, half_13_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_04 : AdmissibleExponent 8 26 (185078947113/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 11) (ψ := (572303289/5000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_12_04)
    (by simpa only [half_13_04_φ1] using half_13_04_hx1)
  exact admissibleExponent_mono h (by norm_num [half_13_04_φ1, half_13_04_φ2, half_13_04_φ3, half_13_04_φ4, half_13_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_14_04_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1170670359/10000000000 : ℝ)

def half_14_04_φ2 : Fin 2 → ℝ := Fin.snoc half_14_04_φ1 (224789423/2000000000 : ℝ)

def half_14_04_φ3 : Fin 3 → ℝ := Fin.snoc half_14_04_φ2 (107239597/1000000000 : ℝ)

def half_14_04_φ4 : Fin 4 → ℝ := Fin.snoc half_14_04_φ3 (947569507/10000000000 : ℝ)

def half_14_04_φ5 : Fin 5 → ℝ := Fin.snoc half_14_04_φ4 (162440487/2000000000 : ℝ)

theorem half_14_04_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_14_04_φ5) (31168753447/5000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_14_04_φ5 (by norm_num [half_14_04_φ1, half_14_04_φ2, half_14_04_φ3, half_14_04_φ4, half_14_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_04_φ1, half_14_04_φ2, half_14_04_φ3, half_14_04_φ4, half_14_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_04_φ1, half_14_04_φ2, half_14_04_φ3, half_14_04_φ4, half_14_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_14_04_φ1, half_14_04_φ2, half_14_04_φ3, half_14_04_φ4, half_14_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_14_04_φ1, half_14_04_φ2, half_14_04_φ3, half_14_04_φ4, half_14_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_14_04_hx5 : SourcePowerBound (powerBoxCross 8 9 32 half_14_04_φ5) (76507194489/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 9) (r := 2) (v := 0) (w := 12) (D := 32)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_14_04_φ5 (by norm_num [half_14_04_φ1, half_14_04_φ2, half_14_04_φ3, half_14_04_φ4, half_14_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_04_φ1, half_14_04_φ2, half_14_04_φ3, half_14_04_φ4, half_14_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_14_04_hF2 (admissibleExponent_zero 8) (half_12_04)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_14_04_φ1, half_14_04_φ2, half_14_04_φ3, half_14_04_φ4, half_14_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_04_hx4 : SourcePowerBound (powerBoxCross 8 10 16 half_14_04_φ4) (18467682199/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 10) (u := 8) (t := 11)
    (D := 16) (ψ := (162440487/2000000000 : ℝ)) half_14_04_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_04_φ1, half_14_04_φ2, half_14_04_φ3, half_14_04_φ4, half_14_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_04_φ1, half_14_04_φ2, half_14_04_φ3, half_14_04_φ4, half_14_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_04_φ1, half_14_04_φ2, half_14_04_φ3, half_14_04_φ4, half_14_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_9) (half_11_04)
    (by simpa only [half_14_04_φ5, show (2:ℝ)*16=32 by norm_num] using half_14_04_hx5)
  exact h.weaken (by norm_num [half_14_04_φ1, half_14_04_φ2, half_14_04_φ3, half_14_04_φ4, half_14_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_04_hx3 : SourcePowerBound (powerBoxCross 8 11 8 half_14_04_φ3) (3552137027/312500000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 11) (u := 9) (t := 12)
    (D := 8) (ψ := (947569507/10000000000 : ℝ)) half_14_04_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_04_φ1, half_14_04_φ2, half_14_04_φ3, half_14_04_φ4, half_14_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_04_φ1, half_14_04_φ2, half_14_04_φ3, half_14_04_φ4, half_14_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_04_φ1, half_14_04_φ2, half_14_04_φ3, half_14_04_φ4, half_14_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_10_04) (half_12_04)
    (by simpa only [half_14_04_φ4, show (2:ℝ)*8=16 by norm_num] using half_14_04_hx4)
  exact h.weaken (by norm_num [half_14_04_φ1, half_14_04_φ2, half_14_04_φ3, half_14_04_φ4, half_14_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_04_hx2 : SourcePowerBound (powerBoxCross 8 12 4 half_14_04_φ2) (141368393209/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 12) (u := 10) (t := 13)
    (D := 4) (ψ := (107239597/1000000000 : ℝ)) half_14_04_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_04_φ1, half_14_04_φ2, half_14_04_φ3, half_14_04_φ4, half_14_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_04_φ1, half_14_04_φ2, half_14_04_φ3, half_14_04_φ4, half_14_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_04_φ1, half_14_04_φ2, half_14_04_φ3, half_14_04_φ4, half_14_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_11_04) (half_13_04)
    (by simpa only [half_14_04_φ3, show (2:ℝ)*4=8 by norm_num] using half_14_04_hx3)
  exact h.weaken (by norm_num [half_14_04_φ1, half_14_04_φ2, half_14_04_φ3, half_14_04_φ4, half_14_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_04_hx1 : SourcePowerBound (powerBoxCross 8 13 2 half_14_04_φ1) (17458297373/1000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 13) (u := 11) (t := 14)
    (D := 2) (ψ := (224789423/2000000000 : ℝ)) half_14_04_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_04_φ1, half_14_04_φ2, half_14_04_φ3, half_14_04_φ4, half_14_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_04_φ1, half_14_04_φ2, half_14_04_φ3, half_14_04_φ4, half_14_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_04_φ1, half_14_04_φ2, half_14_04_φ3, half_14_04_φ4, half_14_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_12_04) (half_14_03)
    (by simpa only [half_14_04_φ2, show (2:ℝ)*2=4 by norm_num] using half_14_04_hx2)
  exact h.weaken (by norm_num [half_14_04_φ1, half_14_04_φ2, half_14_04_φ3, half_14_04_φ4, half_14_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_04 : AdmissibleExponent 8 28 (40769946541/2000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 12) (ψ := (1170670359/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_13_04)
    (by simpa only [half_14_04_φ1] using half_14_04_hx1)
  exact admissibleExponent_mono h (by norm_num [half_14_04_φ1, half_14_04_φ2, half_14_04_φ3, half_14_04_φ4, half_14_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_15_04_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (596467631/5000000000 : ℝ)

def half_15_04_φ2 : Fin 2 → ℝ := Fin.snoc half_15_04_φ1 (1156363227/10000000000 : ℝ)

def half_15_04_φ3 : Fin 3 → ℝ := Fin.snoc half_15_04_φ2 (546478679/5000000000 : ℝ)

def half_15_04_φ4 : Fin 4 → ℝ := Fin.snoc half_15_04_φ3 (58551287/625000000 : ℝ)

def half_15_04_φ5 : Fin 5 → ℝ := Fin.snoc half_15_04_φ4 (802989079/10000000000 : ℝ)

theorem half_15_04_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_15_04_φ5) (30588312061/5000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_15_04_φ5 (by norm_num [half_15_04_φ1, half_15_04_φ2, half_15_04_φ3, half_15_04_φ4, half_15_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_04_φ1, half_15_04_φ2, half_15_04_φ3, half_15_04_φ4, half_15_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_04_φ1, half_15_04_φ2, half_15_04_φ3, half_15_04_φ4, half_15_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_15_04_φ1, half_15_04_φ2, half_15_04_φ3, half_15_04_φ4, half_15_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_15_04_φ1, half_15_04_φ2, half_15_04_φ3, half_15_04_φ4, half_15_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_15_04_hx5 : SourcePowerBound (powerBoxCross 8 10 32 half_15_04_φ5) (84432434499/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 10) (r := 2) (v := 13) (w := 14) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_15_04_φ5 (by norm_num [half_15_04_φ1, half_15_04_φ2, half_15_04_φ3, half_15_04_φ4, half_15_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_04_φ1, half_15_04_φ2, half_15_04_φ3, half_15_04_φ4, half_15_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_15_04_hF2 (half_13_04) (half_14_04)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_15_04_φ1, half_15_04_φ2, half_15_04_φ3, half_15_04_φ4, half_15_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_04_hx4 : SourcePowerBound (powerBoxCross 8 11 16 half_15_04_φ4) (101364746679/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 11) (u := 9) (t := 12)
    (D := 16) (ψ := (802989079/10000000000 : ℝ)) half_15_04_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_04_φ1, half_15_04_φ2, half_15_04_φ3, half_15_04_φ4, half_15_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_04_φ1, half_15_04_φ2, half_15_04_φ3, half_15_04_φ4, half_15_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_04_φ1, half_15_04_φ2, half_15_04_φ3, half_15_04_φ4, half_15_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_10_04) (half_12_04)
    (by simpa only [half_15_04_φ5, show (2:ℝ)*16=32 by norm_num] using half_15_04_hx5)
  exact h.weaken (by norm_num [half_15_04_φ1, half_15_04_φ2, half_15_04_φ3, half_15_04_φ4, half_15_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_04_hx3 : SourcePowerBound (powerBoxCross 8 12 8 half_15_04_φ3) (24831222651/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 12) (u := 10) (t := 13)
    (D := 8) (ψ := (58551287/625000000 : ℝ)) half_15_04_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_04_φ1, half_15_04_φ2, half_15_04_φ3, half_15_04_φ4, half_15_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_04_φ1, half_15_04_φ2, half_15_04_φ3, half_15_04_φ4, half_15_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_04_φ1, half_15_04_φ2, half_15_04_φ3, half_15_04_φ4, half_15_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_11_04) (half_13_04)
    (by simpa only [half_15_04_φ4, show (2:ℝ)*8=16 by norm_num] using half_15_04_hx4)
  exact h.weaken (by norm_num [half_15_04_φ1, half_15_04_φ2, half_15_04_φ3, half_15_04_φ4, half_15_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_04_hx2 : SourcePowerBound (powerBoxCross 8 13 4 half_15_04_φ2) (30880838887/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 13) (u := 11) (t := 14)
    (D := 4) (ψ := (546478679/5000000000 : ℝ)) half_15_04_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_04_φ1, half_15_04_φ2, half_15_04_φ3, half_15_04_φ4, half_15_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_04_φ1, half_15_04_φ2, half_15_04_φ3, half_15_04_φ4, half_15_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_04_φ1, half_15_04_φ2, half_15_04_φ3, half_15_04_φ4, half_15_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_12_04) (half_14_04)
    (by simpa only [half_15_04_φ3, show (2:ℝ)*4=8 by norm_num] using half_15_04_hx3)
  exact h.weaken (by norm_num [half_15_04_φ1, half_15_04_φ2, half_15_04_φ3, half_15_04_φ4, half_15_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_04_hx1 : SourcePowerBound (powerBoxCross 8 14 2 half_15_04_φ1) (190724714547/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 14) (u := 12) (t := 15)
    (D := 2) (ψ := (1156363227/10000000000 : ℝ)) half_15_04_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_04_φ1, half_15_04_φ2, half_15_04_φ3, half_15_04_φ4, half_15_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_04_φ1, half_15_04_φ2, half_15_04_φ3, half_15_04_φ4, half_15_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_04_φ1, half_15_04_φ2, half_15_04_φ3, half_15_04_φ4, half_15_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_13_04) (half_15_03)
    (by simpa only [half_15_04_φ2, show (2:ℝ)*2=4 by norm_num] using half_15_04_hx2)
  exact h.weaken (by norm_num [half_15_04_φ1, half_15_04_φ2, half_15_04_φ3, half_15_04_φ4, half_15_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_04 : AdmissibleExponent 8 30 (222933966621/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 13) (ψ := (596467631/5000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_14_04)
    (by simpa only [half_15_04_φ1] using half_15_04_hx1)
  exact admissibleExponent_mono h (by norm_num [half_15_04_φ1, half_15_04_φ2, half_15_04_φ3, half_15_04_φ4, half_15_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_16_04_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (3780103/31250000 : ℝ)

def half_16_04_φ2 : Fin 2 → ℝ := Fin.snoc half_16_04_φ1 (11831187/100000000 : ℝ)

def half_16_04_φ3 : Fin 3 → ℝ := Fin.snoc half_16_04_φ2 (543374881/5000000000 : ℝ)

def half_16_04_φ4 : Fin 4 → ℝ := Fin.snoc half_16_04_φ3 (232874949/2500000000 : ℝ)

def half_16_04_φ5 : Fin 5 → ℝ := Fin.snoc half_16_04_φ4 (798428397/10000000000 : ℝ)

theorem half_16_04_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_16_04_φ5) (12120395617/2000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_16_04_φ5 (by norm_num [half_16_04_φ1, half_16_04_φ2, half_16_04_φ3, half_16_04_φ4, half_16_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_04_φ1, half_16_04_φ2, half_16_04_φ3, half_16_04_φ4, half_16_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_04_φ1, half_16_04_φ2, half_16_04_φ3, half_16_04_φ4, half_16_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_16_04_φ1, half_16_04_φ2, half_16_04_φ3, half_16_04_φ4, half_16_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_16_04_φ1, half_16_04_φ2, half_16_04_φ3, half_16_04_φ4, half_16_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_16_04_hx5 : SourcePowerBound (powerBoxCross 8 11 32 half_16_04_φ5) (92963449749/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 11) (r := 2) (v := 14) (w := 15) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_16_04_φ5 (by norm_num [half_16_04_φ1, half_16_04_φ2, half_16_04_φ3, half_16_04_φ4, half_16_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_04_φ1, half_16_04_φ2, half_16_04_φ3, half_16_04_φ4, half_16_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_16_04_hF2 (half_14_04) (half_15_04)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_16_04_φ1, half_16_04_φ2, half_16_04_φ3, half_16_04_φ4, half_16_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_04_hx4 : SourcePowerBound (powerBoxCross 8 12 16 half_16_04_φ4) (1389337741/125000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 12) (u := 10) (t := 13)
    (D := 16) (ψ := (798428397/10000000000 : ℝ)) half_16_04_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_04_φ1, half_16_04_φ2, half_16_04_φ3, half_16_04_φ4, half_16_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_04_φ1, half_16_04_φ2, half_16_04_φ3, half_16_04_φ4, half_16_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_04_φ1, half_16_04_φ2, half_16_04_φ3, half_16_04_φ4, half_16_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_11_04) (half_13_04)
    (by simpa only [half_16_04_φ5, show (2:ℝ)*16=32 by norm_num] using half_16_04_hx5)
  exact h.weaken (by norm_num [half_16_04_φ1, half_16_04_φ2, half_16_04_φ3, half_16_04_φ4, half_16_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_04_hx3 : SourcePowerBound (powerBoxCross 8 13 8 half_16_04_φ3) (135567596929/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 13) (u := 11) (t := 14)
    (D := 8) (ψ := (232874949/2500000000 : ℝ)) half_16_04_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_04_φ1, half_16_04_φ2, half_16_04_φ3, half_16_04_φ4, half_16_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_04_φ1, half_16_04_φ2, half_16_04_φ3, half_16_04_φ4, half_16_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_04_φ1, half_16_04_φ2, half_16_04_φ3, half_16_04_φ4, half_16_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_12_04) (half_14_04)
    (by simpa only [half_16_04_φ4, show (2:ℝ)*8=16 by norm_num] using half_16_04_hx4)
  exact h.weaken (by norm_num [half_16_04_φ1, half_16_04_φ2, half_16_04_φ3, half_16_04_φ4, half_16_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_04_hx2 : SourcePowerBound (powerBoxCross 8 14 4 half_16_04_φ2) (33557848411/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 14) (u := 12) (t := 15)
    (D := 4) (ψ := (543374881/5000000000 : ℝ)) half_16_04_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_04_φ1, half_16_04_φ2, half_16_04_φ3, half_16_04_φ4, half_16_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_04_φ1, half_16_04_φ2, half_16_04_φ3, half_16_04_φ4, half_16_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_04_φ1, half_16_04_φ2, half_16_04_φ3, half_16_04_φ4, half_16_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_13_04) (half_15_04)
    (by simpa only [half_16_04_φ3, show (2:ℝ)*4=8 by norm_num] using half_16_04_hx3)
  exact h.weaken (by norm_num [half_16_04_φ1, half_16_04_φ2, half_16_04_φ3, half_16_04_φ4, half_16_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_04_hx1 : SourcePowerBound (powerBoxCross 8 15 2 half_16_04_φ1) (51794193049/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 15) (u := 13) (t := 16)
    (D := 2) (ψ := (11831187/100000000 : ℝ)) half_16_04_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_04_φ1, half_16_04_φ2, half_16_04_φ3, half_16_04_φ4, half_16_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_04_φ1, half_16_04_φ2, half_16_04_φ3, half_16_04_φ4, half_16_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_04_φ1, half_16_04_φ2, half_16_04_φ3, half_16_04_φ4, half_16_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_14_04) (half_16_03)
    (by simpa only [half_16_04_φ2, show (2:ℝ)*2=4 by norm_num] using half_16_04_hx2)
  exact h.weaken (by norm_num [half_16_04_φ1, half_16_04_φ2, half_16_04_φ3, half_16_04_φ4, half_16_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_04 : AdmissibleExponent 8 32 (60564032009/2500000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 14) (ψ := (3780103/31250000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_15_04)
    (by simpa only [half_16_04_φ1] using half_16_04_hx1)
  exact admissibleExponent_mono h (by norm_num [half_16_04_φ1, half_16_04_φ2, half_16_04_φ3, half_16_04_φ4, half_16_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_17_04_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (76397323/625000000 : ℝ)

def half_17_04_φ2 : Fin 2 → ℝ := Fin.snoc half_17_04_φ1 (30081513/250000000 : ℝ)

def half_17_04_φ3 : Fin 3 → ℝ := Fin.snoc half_17_04_φ2 (216410923/2000000000 : ℝ)

def half_17_04_φ4 : Fin 4 → ℝ := Fin.snoc half_17_04_φ3 (185495077/2000000000 : ℝ)

def half_17_04_φ5 : Fin 5 → ℝ := Fin.snoc half_17_04_φ4 (794978901/10000000000 : ℝ)

theorem half_17_04_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_17_04_φ5) (60167341631/10000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_17_04_φ5 (by norm_num [half_17_04_φ1, half_17_04_φ2, half_17_04_φ3, half_17_04_φ4, half_17_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_04_φ1, half_17_04_φ2, half_17_04_φ3, half_17_04_φ4, half_17_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_04_φ1, half_17_04_φ2, half_17_04_φ3, half_17_04_φ4, half_17_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_17_04_φ1, half_17_04_φ2, half_17_04_φ3, half_17_04_φ4, half_17_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_17_04_φ1, half_17_04_φ2, half_17_04_φ3, half_17_04_φ4, half_17_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_17_04_hx5 : SourcePowerBound (powerBoxCross 8 12 32 half_17_04_φ5) (101706665191/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 12) (r := 2) (v := 0) (w := 16) (D := 32)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_17_04_φ5 (by norm_num [half_17_04_φ1, half_17_04_φ2, half_17_04_φ3, half_17_04_φ4, half_17_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_04_φ1, half_17_04_φ2, half_17_04_φ3, half_17_04_φ4, half_17_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_17_04_hF2 (admissibleExponent_zero 8) (half_16_04)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_17_04_φ1, half_17_04_φ2, half_17_04_φ3, half_17_04_φ4, half_17_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_04_hx4 : SourcePowerBound (powerBoxCross 8 13 16 half_17_04_φ4) (121192255867/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 13) (u := 11) (t := 14)
    (D := 16) (ψ := (794978901/10000000000 : ℝ)) half_17_04_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_04_φ1, half_17_04_φ2, half_17_04_φ3, half_17_04_φ4, half_17_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_04_φ1, half_17_04_φ2, half_17_04_φ3, half_17_04_φ4, half_17_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_04_φ1, half_17_04_φ2, half_17_04_φ3, half_17_04_φ4, half_17_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_12_04) (half_14_04)
    (by simpa only [half_17_04_φ5, show (2:ℝ)*16=32 by norm_num] using half_17_04_hx5)
  exact h.weaken (by norm_num [half_17_04_φ1, half_17_04_φ2, half_17_04_φ3, half_17_04_φ4, half_17_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_04_hx3 : SourcePowerBound (powerBoxCross 8 14 8 half_17_04_φ3) (147280735491/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 14) (u := 12) (t := 15)
    (D := 8) (ψ := (185495077/2000000000 : ℝ)) half_17_04_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_04_φ1, half_17_04_φ2, half_17_04_φ3, half_17_04_φ4, half_17_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_04_φ1, half_17_04_φ2, half_17_04_φ3, half_17_04_φ4, half_17_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_04_φ1, half_17_04_φ2, half_17_04_φ3, half_17_04_φ4, half_17_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_13_04) (half_15_04)
    (by simpa only [half_17_04_φ4, show (2:ℝ)*8=16 by norm_num] using half_17_04_hx4)
  exact h.weaken (by norm_num [half_17_04_φ1, half_17_04_φ2, half_17_04_φ3, half_17_04_φ4, half_17_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_04_hx2 : SourcePowerBound (powerBoxCross 8 15 4 half_17_04_φ2) (181505469699/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 15) (u := 13) (t := 16)
    (D := 4) (ψ := (216410923/2000000000 : ℝ)) half_17_04_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_04_φ1, half_17_04_φ2, half_17_04_φ3, half_17_04_φ4, half_17_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_04_φ1, half_17_04_φ2, half_17_04_φ3, half_17_04_φ4, half_17_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_04_φ1, half_17_04_φ2, half_17_04_φ3, half_17_04_φ4, half_17_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_14_04) (half_16_04)
    (by simpa only [half_17_04_φ3, show (2:ℝ)*4=8 by norm_num] using half_17_04_hx3)
  exact h.weaken (by norm_num [half_17_04_φ1, half_17_04_φ2, half_17_04_φ3, half_17_04_φ4, half_17_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_04_hx1 : SourcePowerBound (powerBoxCross 8 16 2 half_17_04_φ1) (111933066873/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 16) (u := 14) (t := 17)
    (D := 2) (ψ := (30081513/250000000 : ℝ)) half_17_04_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_04_φ1, half_17_04_φ2, half_17_04_φ3, half_17_04_φ4, half_17_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_04_φ1, half_17_04_φ2, half_17_04_φ3, half_17_04_φ4, half_17_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_04_φ1, half_17_04_φ2, half_17_04_φ3, half_17_04_φ4, half_17_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_15_04) (half_17_03)
    (by simpa only [half_17_04_φ2, show (2:ℝ)*2=4 by norm_num] using half_17_04_hx2)
  exact h.weaken (by norm_num [half_17_04_φ1, half_17_04_φ2, half_17_04_φ3, half_17_04_φ4, half_17_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_04 : AdmissibleExponent 8 34 (130879602977/5000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 15) (ψ := (76397323/625000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_16_04)
    (by simpa only [half_17_04_φ1] using half_17_04_hx1)
  exact admissibleExponent_mono h (by norm_num [half_17_04_φ1, half_17_04_φ2, half_17_04_φ3, half_17_04_φ4, half_17_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem chord_50 : AdmissibleExponent 8 36 (5630971649/200000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 36) (t := (1/2 : ℝ))
    (half_17_04) (half_19_03) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1 <;> norm_num

def half_18_04_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (246613039/2000000000 : ℝ)

def half_18_04_φ2 : Fin 2 → ℝ := Fin.snoc half_18_04_φ1 (609568753/5000000000 : ℝ)

def half_18_04_φ3 : Fin 3 → ℝ := Fin.snoc half_18_04_φ2 (269564189/2500000000 : ℝ)

def half_18_04_φ4 : Fin 4 → ℝ := Fin.snoc half_18_04_φ3 (924220077/10000000000 : ℝ)

def half_18_04_φ5 : Fin 5 → ℝ := Fin.snoc half_18_04_φ4 (792188637/10000000000 : ℝ)

theorem half_18_04_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_18_04_φ5) (59815768409/10000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_18_04_φ5 (by norm_num [half_18_04_φ1, half_18_04_φ2, half_18_04_φ3, half_18_04_φ4, half_18_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_18_04_φ1, half_18_04_φ2, half_18_04_φ3, half_18_04_φ4, half_18_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_18_04_φ1, half_18_04_φ2, half_18_04_φ3, half_18_04_φ4, half_18_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_18_04_φ1, half_18_04_φ2, half_18_04_φ3, half_18_04_φ4, half_18_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_18_04_φ1, half_18_04_φ2, half_18_04_φ3, half_18_04_φ4, half_18_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_18_04_hx5 : SourcePowerBound (powerBoxCross 8 13 32 half_18_04_φ5) (110618680987/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 13) (r := 2) (v := 17) (w := 18) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_18_04_φ5 (by norm_num [half_18_04_φ1, half_18_04_φ2, half_18_04_φ3, half_18_04_φ4, half_18_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_18_04_φ1, half_18_04_φ2, half_18_04_φ3, half_18_04_φ4, half_18_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_18_04_hF2 (half_17_04) (chord_50)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_18_04_φ1, half_18_04_φ2, half_18_04_φ3, half_18_04_φ4, half_18_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_18_04_hx4 : SourcePowerBound (powerBoxCross 8 14 16 half_18_04_φ4) (131432334471/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 14) (u := 12) (t := 15)
    (D := 16) (ψ := (792188637/10000000000 : ℝ)) half_18_04_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_18_04_φ1, half_18_04_φ2, half_18_04_φ3, half_18_04_φ4, half_18_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_18_04_φ1, half_18_04_φ2, half_18_04_φ3, half_18_04_φ4, half_18_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_18_04_φ1, half_18_04_φ2, half_18_04_φ3, half_18_04_φ4, half_18_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_13_04) (half_15_04)
    (by simpa only [half_18_04_φ5, show (2:ℝ)*16=32 by norm_num] using half_18_04_hx5)
  exact h.weaken (by norm_num [half_18_04_φ1, half_18_04_φ2, half_18_04_φ3, half_18_04_φ4, half_18_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_18_04_hx3 : SourcePowerBound (powerBoxCross 8 15 8 half_18_04_φ3) (79600411141/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 15) (u := 13) (t := 16)
    (D := 8) (ψ := (924220077/10000000000 : ℝ)) half_18_04_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_18_04_φ1, half_18_04_φ2, half_18_04_φ3, half_18_04_φ4, half_18_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_18_04_φ1, half_18_04_φ2, half_18_04_φ3, half_18_04_φ4, half_18_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_18_04_φ1, half_18_04_φ2, half_18_04_φ3, half_18_04_φ4, half_18_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_14_04) (half_16_04)
    (by simpa only [half_18_04_φ4, show (2:ℝ)*8=16 by norm_num] using half_18_04_hx4)
  exact h.weaken (by norm_num [half_18_04_φ1, half_18_04_φ2, half_18_04_φ3, half_18_04_φ4, half_18_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_18_04_hx2 : SourcePowerBound (powerBoxCross 8 16 4 half_18_04_φ2) (97718848017/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 16) (u := 14) (t := 17)
    (D := 4) (ψ := (269564189/2500000000 : ℝ)) half_18_04_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_18_04_φ1, half_18_04_φ2, half_18_04_φ3, half_18_04_φ4, half_18_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_18_04_φ1, half_18_04_φ2, half_18_04_φ3, half_18_04_φ4, half_18_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_18_04_φ1, half_18_04_φ2, half_18_04_φ3, half_18_04_φ4, half_18_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_15_04) (half_17_04)
    (by simpa only [half_18_04_φ3, show (2:ℝ)*4=8 by norm_num] using half_18_04_hx3)
  exact h.weaken (by norm_num [half_18_04_φ1, half_18_04_φ2, half_18_04_φ3, half_18_04_φ4, half_18_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_18_04_hx1 : SourcePowerBound (powerBoxCross 8 17 2 half_18_04_φ1) (240715654517/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 17) (u := 15) (t := 18)
    (D := 2) (ψ := (609568753/5000000000 : ℝ)) half_18_04_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_18_04_φ1, half_18_04_φ2, half_18_04_φ3, half_18_04_φ4, half_18_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_18_04_φ1, half_18_04_φ2, half_18_04_φ3, half_18_04_φ4, half_18_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_18_04_φ1, half_18_04_φ2, half_18_04_φ3, half_18_04_φ4, half_18_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_16_04) (chord_50)
    (by simpa only [half_18_04_φ2, show (2:ℝ)*2=4 by norm_num] using half_18_04_hx2)
  exact h.weaken (by norm_num [half_18_04_φ1, half_18_04_φ2, half_18_04_φ3, half_18_04_φ4, half_18_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_18_04 : AdmissibleExponent 8 36 (4396981343/156250000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 16) (ψ := (246613039/2000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_17_04)
    (by simpa only [half_18_04_φ1] using half_18_04_hx1)
  exact admissibleExponent_mono h (by norm_num [half_18_04_φ1, half_18_04_φ2, half_18_04_φ3, half_18_04_φ4, half_18_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_19_04_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1242828891/10000000000 : ℝ)

def half_19_04_φ2 : Fin 2 → ℝ := Fin.snoc half_19_04_φ1 (1231704019/10000000000 : ℝ)

def half_19_04_φ3 : Fin 3 → ℝ := Fin.snoc half_19_04_φ2 (1075066727/10000000000 : ℝ)

def half_19_04_φ4 : Fin 4 → ℝ := Fin.snoc half_19_04_φ3 (460742883/5000000000 : ℝ)

def half_19_04_φ5 : Fin 5 → ℝ := Fin.snoc half_19_04_φ4 (394922471/5000000000 : ℝ)

theorem half_19_04_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_19_04_φ5) (11904092551/2000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_19_04_φ5 (by norm_num [half_19_04_φ1, half_19_04_φ2, half_19_04_φ3, half_19_04_φ4, half_19_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_19_04_φ1, half_19_04_φ2, half_19_04_φ3, half_19_04_φ4, half_19_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_19_04_φ1, half_19_04_φ2, half_19_04_φ3, half_19_04_φ4, half_19_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_19_04_φ1, half_19_04_φ2, half_19_04_φ3, half_19_04_φ4, half_19_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_19_04_φ1, half_19_04_φ2, half_19_04_φ3, half_19_04_φ4, half_19_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_19_04_hx5 : SourcePowerBound (powerBoxCross 8 14 32 half_19_04_φ5) (29905838979/2500000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 14) (r := 2) (v := 18) (w := 19) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_19_04_φ5 (by norm_num [half_19_04_φ1, half_19_04_φ2, half_19_04_φ3, half_19_04_φ4, half_19_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_19_04_φ1, half_19_04_φ2, half_19_04_φ3, half_19_04_φ4, half_19_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_19_04_hF2 (half_18_04) (half_19_03)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_19_04_φ1, half_19_04_φ2, half_19_04_φ3, half_19_04_φ4, half_19_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_19_04_hx4 : SourcePowerBound (powerBoxCross 8 15 16 half_19_04_φ4) (141796457891/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 15) (u := 13) (t := 16)
    (D := 16) (ψ := (394922471/5000000000 : ℝ)) half_19_04_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_19_04_φ1, half_19_04_φ2, half_19_04_φ3, half_19_04_φ4, half_19_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_19_04_φ1, half_19_04_φ2, half_19_04_φ3, half_19_04_φ4, half_19_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_19_04_φ1, half_19_04_φ2, half_19_04_φ3, half_19_04_φ4, half_19_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_14_04) (half_16_04)
    (by simpa only [half_19_04_φ5, show (2:ℝ)*16=32 by norm_num] using half_19_04_hx5)
  exact h.weaken (by norm_num [half_19_04_φ1, half_19_04_φ2, half_19_04_φ3, half_19_04_φ4, half_19_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_19_04_hx3 : SourcePowerBound (powerBoxCross 8 16 8 half_19_04_φ3) (171258757679/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 16) (u := 14) (t := 17)
    (D := 8) (ψ := (460742883/5000000000 : ℝ)) half_19_04_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_19_04_φ1, half_19_04_φ2, half_19_04_φ3, half_19_04_φ4, half_19_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_19_04_φ1, half_19_04_φ2, half_19_04_φ3, half_19_04_φ4, half_19_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_19_04_φ1, half_19_04_φ2, half_19_04_φ3, half_19_04_φ4, half_19_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_15_04) (half_17_04)
    (by simpa only [half_19_04_φ4, show (2:ℝ)*8=16 by norm_num] using half_19_04_hx4)
  exact h.weaken (by norm_num [half_19_04_φ1, half_19_04_φ2, half_19_04_φ3, half_19_04_φ4, half_19_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_19_04_hx2 : SourcePowerBound (powerBoxCross 8 17 4 half_19_04_φ2) (104758965389/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 17) (u := 15) (t := 18)
    (D := 4) (ψ := (1075066727/10000000000 : ℝ)) half_19_04_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_19_04_φ1, half_19_04_φ2, half_19_04_φ3, half_19_04_φ4, half_19_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_19_04_φ1, half_19_04_φ2, half_19_04_φ3, half_19_04_φ4, half_19_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_19_04_φ1, half_19_04_φ2, half_19_04_φ3, half_19_04_φ4, half_19_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_16_04) (half_18_04)
    (by simpa only [half_19_04_φ3, show (2:ℝ)*4=8 by norm_num] using half_19_04_hx3)
  exact h.weaken (by norm_num [half_19_04_φ1, half_19_04_φ2, half_19_04_φ3, half_19_04_φ4, half_19_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_19_04_hx1 : SourcePowerBound (powerBoxCross 8 18 2 half_19_04_φ1) (257675583991/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 18) (u := 16) (t := 19)
    (D := 2) (ψ := (1231704019/10000000000 : ℝ)) half_19_04_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_19_04_φ1, half_19_04_φ2, half_19_04_φ3, half_19_04_φ4, half_19_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_19_04_φ1, half_19_04_φ2, half_19_04_φ3, half_19_04_φ4, half_19_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_19_04_φ1, half_19_04_φ2, half_19_04_φ3, half_19_04_φ4, half_19_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_17_04) (half_19_03)
    (by simpa only [half_19_04_φ2, show (2:ℝ)*2=4 by norm_num] using half_19_04_hx2)
  exact h.weaken (by norm_num [half_19_04_φ1, half_19_04_φ2, half_19_04_φ3, half_19_04_φ4, half_19_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_19_04 : AdmissibleExponent 8 38 (37646824397/1250000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 17) (ψ := (1242828891/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_18_04)
    (by simpa only [half_19_04_φ1] using half_19_04_hx1)
  exact admissibleExponent_mono h (by norm_num [half_19_04_φ1, half_19_04_φ2, half_19_04_φ3, half_19_04_φ4, half_19_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_20_04_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1/8 : ℝ)

def half_20_04_φ2 : Fin 2 → ℝ := Fin.snoc half_20_04_φ1 (1242077843/10000000000 : ℝ)

def half_20_04_φ3 : Fin 3 → ℝ := Fin.snoc half_20_04_φ2 (268140077/2500000000 : ℝ)

def half_20_04_φ4 : Fin 4 → ℝ := Fin.snoc half_20_04_φ3 (459668703/5000000000 : ℝ)

def half_20_04_φ5 : Fin 5 → ℝ := Fin.snoc half_20_04_φ4 (788003491/10000000000 : ℝ)

theorem half_20_04_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_20_04_φ5) (7411054999/1250000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_20_04_φ5 (by norm_num [half_20_04_φ1, half_20_04_φ2, half_20_04_φ3, half_20_04_φ4, half_20_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_20_04_φ1, half_20_04_φ2, half_20_04_φ3, half_20_04_φ4, half_20_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_20_04_φ1, half_20_04_φ2, half_20_04_φ3, half_20_04_φ4, half_20_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_20_04_φ1, half_20_04_φ2, half_20_04_φ3, half_20_04_φ4, half_20_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_20_04_φ1, half_20_04_φ2, half_20_04_φ3, half_20_04_φ4, half_20_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_20_04_hx5 : SourcePowerBound (powerBoxCross 8 15 32 half_20_04_φ5) (25749358039/2000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 15) (r := 2) (v := 0) (w := 20) (D := 32)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_20_04_φ5 (by norm_num [half_20_04_φ1, half_20_04_φ2, half_20_04_φ3, half_20_04_φ4, half_20_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_20_04_φ1, half_20_04_φ2, half_20_04_φ3, half_20_04_φ4, half_20_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_20_04_hF2 (admissibleExponent_zero 8) (half_20_03)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_20_04_φ1, half_20_04_φ2, half_20_04_φ3, half_20_04_φ4, half_20_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_20_04_hx4 : SourcePowerBound (powerBoxCross 8 16 16 half_20_04_φ4) (152299040179/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 16) (u := 14) (t := 17)
    (D := 16) (ψ := (788003491/10000000000 : ℝ)) half_20_04_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_20_04_φ1, half_20_04_φ2, half_20_04_φ3, half_20_04_φ4, half_20_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_20_04_φ1, half_20_04_φ2, half_20_04_φ3, half_20_04_φ4, half_20_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_20_04_φ1, half_20_04_φ2, half_20_04_φ3, half_20_04_φ4, half_20_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_15_04) (half_17_04)
    (by simpa only [half_20_04_φ5, show (2:ℝ)*16=32 by norm_num] using half_20_04_hx5)
  exact h.weaken (by norm_num [half_20_04_φ1, half_20_04_φ2, half_20_04_φ3, half_20_04_φ4, half_20_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_20_04_hx3 : SourcePowerBound (powerBoxCross 8 17 8 half_20_04_φ3) (45867686877/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 17) (u := 15) (t := 18)
    (D := 8) (ψ := (459668703/5000000000 : ℝ)) half_20_04_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_20_04_φ1, half_20_04_φ2, half_20_04_φ3, half_20_04_φ4, half_20_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_20_04_φ1, half_20_04_φ2, half_20_04_φ3, half_20_04_φ4, half_20_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_20_04_φ1, half_20_04_φ2, half_20_04_φ3, half_20_04_φ4, half_20_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_16_04) (half_18_04)
    (by simpa only [half_20_04_φ4, show (2:ℝ)*8=16 by norm_num] using half_20_04_hx4)
  exact h.weaken (by norm_num [half_20_04_φ1, half_20_04_φ2, half_20_04_φ3, half_20_04_φ4, half_20_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_20_04_hx2 : SourcePowerBound (powerBoxCross 8 18 4 half_20_04_φ2) (111885058599/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 18) (u := 16) (t := 19)
    (D := 4) (ψ := (268140077/2500000000 : ℝ)) half_20_04_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_20_04_φ1, half_20_04_φ2, half_20_04_φ3, half_20_04_φ4, half_20_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_20_04_φ1, half_20_04_φ2, half_20_04_φ3, half_20_04_φ4, half_20_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_20_04_φ1, half_20_04_φ2, half_20_04_φ3, half_20_04_φ4, half_20_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_17_04) (half_19_04)
    (by simpa only [half_20_04_φ3, show (2:ℝ)*4=8 by norm_num] using half_20_04_hx3)
  exact h.weaken (by norm_num [half_20_04_φ1, half_20_04_φ2, half_20_04_φ3, half_20_04_φ4, half_20_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_20_04_hx1 : SourcePowerBound (powerBoxCross 8 19 2 half_20_04_φ1) (68701076951/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 19) (u := 17) (t := 20)
    (D := 2) (ψ := (1242077843/10000000000 : ℝ)) half_20_04_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_20_04_φ1, half_20_04_φ2, half_20_04_φ3, half_20_04_φ4, half_20_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_20_04_φ1, half_20_04_φ2, half_20_04_φ3, half_20_04_φ4, half_20_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_20_04_φ1, half_20_04_φ2, half_20_04_φ3, half_20_04_φ4, half_20_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_18_04) (half_20_03)
    (by simpa only [half_20_04_φ2, show (2:ℝ)*2=4 by norm_num] using half_20_04_hx2)
  exact h.weaken (by norm_num [half_20_04_φ1, half_20_04_φ2, half_20_04_φ3, half_20_04_φ4, half_20_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_20_04 : AdmissibleExponent 8 40 (80263576951/2500000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 18) (ψ := (1/8 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_19_04)
    (by simpa only [half_20_04_φ1] using half_20_04_hx1)
  exact admissibleExponent_mono h (by norm_num [half_20_04_φ1, half_20_04_φ2, half_20_04_φ3, half_20_04_φ4, half_20_04_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_10_05_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (258261163/2500000000 : ℝ)

def half_10_05_φ2 : Fin 2 → ℝ := Fin.snoc half_10_05_φ1 (961426609/10000000000 : ℝ)

def half_10_05_φ3 : Fin 3 → ℝ := Fin.snoc half_10_05_φ2 (418331639/5000000000 : ℝ)

def half_10_05_φ4 : Fin 4 → ℝ := Fin.snoc half_10_05_φ3 (549281943/10000000000 : ℝ)

theorem half_10_05_hF2 : SourcePowerBound (paddedMoment 8 0 2 16 half_10_05_φ4) (34505626939/5000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 4) (r := 0) (n := 1) (D := 16)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_10_05_φ4 (by norm_num [half_10_05_φ1, half_10_05_φ2, half_10_05_φ3, half_10_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_05_φ1, half_10_05_φ2, half_10_05_φ3, half_10_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_05_φ1, half_10_05_φ2, half_10_05_φ3, half_10_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_10_05_φ1, half_10_05_φ2, half_10_05_φ3, half_10_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_10_05_φ1, half_10_05_φ2, half_10_05_φ3, half_10_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_10_05_hx4 : SourcePowerBound (powerBoxCross 8 6 16 half_10_05_φ4) (66119549113/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 6) (r := 2) (v := 0) (w := 8) (D := 16)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_10_05_φ4 (by norm_num [half_10_05_φ1, half_10_05_φ2, half_10_05_φ3, half_10_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_05_φ1, half_10_05_φ2, half_10_05_φ3, half_10_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_10_05_hF2 (admissibleExponent_zero 8) (SeedCompletionHigher8SimpleSeeds.degree8_half_8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_10_05_φ1, half_10_05_φ2, half_10_05_φ3, half_10_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_05_hx3 : SourcePowerBound (powerBoxCross 8 7 8 half_10_05_φ3) (1911323283/250000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 7) (u := 5) (t := 8)
    (D := 8) (ψ := (549281943/10000000000 : ℝ)) half_10_05_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_05_φ1, half_10_05_φ2, half_10_05_φ3, half_10_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_05_φ1, half_10_05_φ2, half_10_05_φ3, half_10_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_05_φ1, half_10_05_φ2, half_10_05_φ3, half_10_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionEven8SecondSeeds.degree8_half_6) (SeedCompletionHigher8SimpleSeeds.degree8_half_8)
    (by simpa only [half_10_05_φ4, show (2:ℝ)*8=16 by norm_num] using half_10_05_hx4)
  exact h.weaken (by norm_num [half_10_05_φ1, half_10_05_φ2, half_10_05_φ3, half_10_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_05_hx2 : SourcePowerBound (powerBoxCross 8 8 4 half_10_05_φ2) (92527429217/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 8) (u := 6) (t := 9)
    (D := 4) (ψ := (418331639/5000000000 : ℝ)) half_10_05_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_05_φ1, half_10_05_φ2, half_10_05_φ3, half_10_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_05_φ1, half_10_05_φ2, half_10_05_φ3, half_10_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_05_φ1, half_10_05_φ2, half_10_05_φ3, half_10_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_7) (SeedCompletionHigher8SimpleSeeds.degree8_half_9)
    (by simpa only [half_10_05_φ3, show (2:ℝ)*4=8 by norm_num] using half_10_05_hx3)
  exact h.weaken (by norm_num [half_10_05_φ1, half_10_05_φ2, half_10_05_φ3, half_10_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_05_hx1 : SourcePowerBound (powerBoxCross 8 9 2 half_10_05_φ1) (113730780793/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 9) (u := 7) (t := 10)
    (D := 2) (ψ := (961426609/10000000000 : ℝ)) half_10_05_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_05_φ1, half_10_05_φ2, half_10_05_φ3, half_10_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_05_φ1, half_10_05_φ2, half_10_05_φ3, half_10_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_05_φ1, half_10_05_φ2, half_10_05_φ3, half_10_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_8) (half_10_04)
    (by simpa only [half_10_05_φ2, show (2:ℝ)*2=4 by norm_num] using half_10_05_hx2)
  exact h.weaken (by norm_num [half_10_05_φ1, half_10_05_φ2, half_10_05_φ3, half_10_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_05 : AdmissibleExponent 8 20 (131292539877/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 8) (ψ := (258261163/2500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_9)
    (by simpa only [half_10_05_φ1] using half_10_05_hx1)
  exact admissibleExponent_mono h (by norm_num [half_10_05_φ1, half_10_05_φ2, half_10_05_φ3, half_10_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_11_05_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (134689147/1250000000 : ℝ)

def half_11_05_φ2 : Fin 2 → ℝ := Fin.snoc half_11_05_φ1 (253199307/2500000000 : ℝ)

def half_11_05_φ3 : Fin 3 → ℝ := Fin.snoc half_11_05_φ2 (92256837/1000000000 : ℝ)

def half_11_05_φ4 : Fin 4 → ℝ := Fin.snoc half_11_05_φ3 (741307961/10000000000 : ℝ)

theorem half_11_05_hF2 : SourcePowerBound (paddedMoment 8 0 2 16 half_11_05_φ4) (12232415713/2000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 4) (r := 0) (n := 1) (D := 16)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_11_05_φ4 (by norm_num [half_11_05_φ1, half_11_05_φ2, half_11_05_φ3, half_11_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_05_φ1, half_11_05_φ2, half_11_05_φ3, half_11_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_05_φ1, half_11_05_φ2, half_11_05_φ3, half_11_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_11_05_φ1, half_11_05_φ2, half_11_05_φ3, half_11_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_11_05_φ1, half_11_05_φ2, half_11_05_φ3, half_11_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_11_05_hx4 : SourcePowerBound (powerBoxCross 8 7 16 half_11_05_φ4) (3577880333/500000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 7) (r := 2) (v := 9) (w := 10) (D := 16)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_11_05_φ4 (by norm_num [half_11_05_φ1, half_11_05_φ2, half_11_05_φ3, half_11_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_05_φ1, half_11_05_φ2, half_11_05_φ3, half_11_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_11_05_hF2 (SeedCompletionHigher8SimpleSeeds.degree8_half_9) (half_10_05)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_11_05_φ1, half_11_05_φ2, half_11_05_φ3, half_11_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_05_hx3 : SourcePowerBound (powerBoxCross 8 8 8 half_11_05_φ3) (42531833017/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 8) (u := 6) (t := 9)
    (D := 8) (ψ := (741307961/10000000000 : ℝ)) half_11_05_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_05_φ1, half_11_05_φ2, half_11_05_φ3, half_11_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_05_φ1, half_11_05_φ2, half_11_05_φ3, half_11_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_05_φ1, half_11_05_φ2, half_11_05_φ3, half_11_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_7) (SeedCompletionHigher8SimpleSeeds.degree8_half_9)
    (by simpa only [half_11_05_φ4, show (2:ℝ)*8=16 by norm_num] using half_11_05_hx4)
  exact h.weaken (by norm_num [half_11_05_φ1, half_11_05_φ2, half_11_05_φ3, half_11_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_05_hx2 : SourcePowerBound (powerBoxCross 8 9 4 half_11_05_φ2) (104059171213/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 9) (u := 7) (t := 10)
    (D := 4) (ψ := (92256837/1000000000 : ℝ)) half_11_05_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_05_φ1, half_11_05_φ2, half_11_05_φ3, half_11_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_05_φ1, half_11_05_φ2, half_11_05_φ3, half_11_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_05_φ1, half_11_05_φ2, half_11_05_φ3, half_11_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_8) (half_10_05)
    (by simpa only [half_11_05_φ3, show (2:ℝ)*4=8 by norm_num] using half_11_05_hx3)
  exact h.weaken (by norm_num [half_11_05_φ1, half_11_05_φ2, half_11_05_φ3, half_11_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_05_hx1 : SourcePowerBound (powerBoxCross 8 10 2 half_11_05_φ1) (25644621779/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 10) (u := 8) (t := 11)
    (D := 2) (ψ := (253199307/2500000000 : ℝ)) half_11_05_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_05_φ1, half_11_05_φ2, half_11_05_φ3, half_11_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_05_φ1, half_11_05_φ2, half_11_05_φ3, half_11_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_05_φ1, half_11_05_φ2, half_11_05_φ3, half_11_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_9) (half_11_04)
    (by simpa only [half_11_05_φ2, show (2:ℝ)*2=4 by norm_num] using half_11_05_hx2)
  exact h.weaken (by norm_num [half_11_05_φ1, half_11_05_φ2, half_11_05_φ3, half_11_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_05 : AdmissibleExponent 8 22 (148695859239/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 9) (ψ := (134689147/1250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_10_05)
    (by simpa only [half_11_05_φ1] using half_11_05_hx1)
  exact admissibleExponent_mono h (by norm_num [half_11_05_φ1, half_11_05_φ2, half_11_05_φ3, half_11_05_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_12_05_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1111299497/10000000000 : ℝ)

def half_12_05_φ2 : Fin 2 → ℝ := Fin.snoc half_12_05_φ1 (1056333671/10000000000 : ℝ)

def half_12_05_φ3 : Fin 3 → ℝ := Fin.snoc half_12_05_φ2 (488778903/5000000000 : ℝ)

def half_12_05_φ4 : Fin 4 → ℝ := Fin.snoc half_12_05_φ3 (842352987/10000000000 : ℝ)

def half_12_05_φ5 : Fin 5 → ℝ := Fin.snoc half_12_05_φ4 (529048099/10000000000 : ℝ)

theorem half_12_05_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_12_05_φ5) (3757578337/500000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_12_05_φ5 (by norm_num [half_12_05_φ1, half_12_05_φ2, half_12_05_φ3, half_12_05_φ4, half_12_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_05_φ1, half_12_05_φ2, half_12_05_φ3, half_12_05_φ4, half_12_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_05_φ1, half_12_05_φ2, half_12_05_φ3, half_12_05_φ4, half_12_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_12_05_φ1, half_12_05_φ2, half_12_05_φ3, half_12_05_φ4, half_12_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_12_05_φ1, half_12_05_φ2, half_12_05_φ3, half_12_05_φ4, half_12_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_12_05_hx5 : SourcePowerBound (powerBoxCross 8 7 32 half_12_05_φ5) (68186645479/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 7) (r := 2) (v := 9) (w := 10) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_12_05_φ5 (by norm_num [half_12_05_φ1, half_12_05_φ2, half_12_05_φ3, half_12_05_φ4, half_12_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_05_φ1, half_12_05_φ2, half_12_05_φ3, half_12_05_φ4, half_12_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_12_05_hF2 (SeedCompletionHigher8SimpleSeeds.degree8_half_9) (half_10_05)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_12_05_φ1, half_12_05_φ2, half_12_05_φ3, half_12_05_φ4, half_12_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_05_hx4 : SourcePowerBound (powerBoxCross 8 8 16 half_12_05_φ4) (78005791659/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 8) (u := 6) (t := 9)
    (D := 16) (ψ := (529048099/10000000000 : ℝ)) half_12_05_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_05_φ1, half_12_05_φ2, half_12_05_φ3, half_12_05_φ4, half_12_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_05_φ1, half_12_05_φ2, half_12_05_φ3, half_12_05_φ4, half_12_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_05_φ1, half_12_05_φ2, half_12_05_φ3, half_12_05_φ4, half_12_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_7) (SeedCompletionHigher8SimpleSeeds.degree8_half_9)
    (by simpa only [half_12_05_φ5, show (2:ℝ)*16=32 by norm_num] using half_12_05_hx5)
  exact h.weaken (by norm_num [half_12_05_φ1, half_12_05_φ2, half_12_05_φ3, half_12_05_φ4, half_12_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_05_hx3 : SourcePowerBound (powerBoxCross 8 9 8 half_12_05_φ3) (94311639193/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 9) (u := 7) (t := 10)
    (D := 8) (ψ := (842352987/10000000000 : ℝ)) half_12_05_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_05_φ1, half_12_05_φ2, half_12_05_φ3, half_12_05_φ4, half_12_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_05_φ1, half_12_05_φ2, half_12_05_φ3, half_12_05_φ4, half_12_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_05_φ1, half_12_05_φ2, half_12_05_φ3, half_12_05_φ4, half_12_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_8) (half_10_05)
    (by simpa only [half_12_05_φ4, show (2:ℝ)*8=16 by norm_num] using half_12_05_hx4)
  exact h.weaken (by norm_num [half_12_05_φ1, half_12_05_φ2, half_12_05_φ3, half_12_05_φ4, half_12_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_05_hx2 : SourcePowerBound (powerBoxCross 8 10 4 half_12_05_φ2) (58055185329/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 10) (u := 8) (t := 11)
    (D := 4) (ψ := (488778903/5000000000 : ℝ)) half_12_05_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_05_φ1, half_12_05_φ2, half_12_05_φ3, half_12_05_φ4, half_12_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_05_φ1, half_12_05_φ2, half_12_05_φ3, half_12_05_φ4, half_12_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_05_φ1, half_12_05_φ2, half_12_05_φ3, half_12_05_φ4, half_12_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_9) (half_11_05)
    (by simpa only [half_12_05_φ3, show (2:ℝ)*4=8 by norm_num] using half_12_05_hx3)
  exact h.weaken (by norm_num [half_12_05_φ1, half_12_05_φ2, half_12_05_φ3, half_12_05_φ4, half_12_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_05_hx1 : SourcePowerBound (powerBoxCross 8 11 2 half_12_05_φ1) (7164129769/500000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 11) (u := 9) (t := 12)
    (D := 2) (ψ := (1056333671/10000000000 : ℝ)) half_12_05_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_05_φ1, half_12_05_φ2, half_12_05_φ3, half_12_05_φ4, half_12_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_05_φ1, half_12_05_φ2, half_12_05_φ3, half_12_05_φ4, half_12_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_05_φ1, half_12_05_φ2, half_12_05_φ3, half_12_05_φ4, half_12_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_10_05) (half_12_04)
    (by simpa only [half_12_05_φ2, show (2:ℝ)*2=4 by norm_num] using half_12_05_hx2)
  exact h.weaken (by norm_num [half_12_05_φ1, half_12_05_φ2, half_12_05_φ3, half_12_05_φ4, half_12_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_05 : AdmissibleExponent 8 24 (166619884817/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 10) (ψ := (1111299497/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_11_05)
    (by simpa only [half_12_05_φ1] using half_12_05_hx1)
  exact admissibleExponent_mono h (by norm_num [half_12_05_φ1, half_12_05_φ2, half_12_05_φ3, half_12_05_φ4, half_12_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_13_05_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (570365803/5000000000 : ℝ)

def half_13_05_φ2 : Fin 2 → ℝ := Fin.snoc half_13_05_φ1 (1090778491/10000000000 : ℝ)

def half_13_05_φ3 : Fin 3 → ℝ := Fin.snoc half_13_05_φ2 (256447617/2500000000 : ℝ)

def half_13_05_φ4 : Fin 4 → ℝ := Fin.snoc half_13_05_φ3 (456782607/5000000000 : ℝ)

def half_13_05_φ5 : Fin 5 → ℝ := Fin.snoc half_13_05_φ4 (171776217/2500000000 : ℝ)

theorem half_13_05_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_13_05_φ5) (67982616413/10000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_13_05_φ5 (by norm_num [half_13_05_φ1, half_13_05_φ2, half_13_05_φ3, half_13_05_φ4, half_13_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_05_φ1, half_13_05_φ2, half_13_05_φ3, half_13_05_φ4, half_13_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_05_φ1, half_13_05_φ2, half_13_05_φ3, half_13_05_φ4, half_13_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_13_05_φ1, half_13_05_φ2, half_13_05_φ3, half_13_05_φ4, half_13_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_13_05_φ1, half_13_05_φ2, half_13_05_φ3, half_13_05_φ4, half_13_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_13_05_hx5 : SourcePowerBound (powerBoxCross 8 8 32 half_13_05_φ5) (14420666019/2000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 8) (r := 2) (v := 10) (w := 11) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_13_05_φ5 (by norm_num [half_13_05_φ1, half_13_05_φ2, half_13_05_φ3, half_13_05_φ4, half_13_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_05_φ1, half_13_05_φ2, half_13_05_φ3, half_13_05_φ4, half_13_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_13_05_hF2 (half_10_05) (half_11_05)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_13_05_φ1, half_13_05_φ2, half_13_05_φ3, half_13_05_φ4, half_13_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_05_hx4 : SourcePowerBound (powerBoxCross 8 9 16 half_13_05_φ4) (84873013189/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 9) (u := 7) (t := 10)
    (D := 16) (ψ := (171776217/2500000000 : ℝ)) half_13_05_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_05_φ1, half_13_05_φ2, half_13_05_φ3, half_13_05_φ4, half_13_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_05_φ1, half_13_05_φ2, half_13_05_φ3, half_13_05_φ4, half_13_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_05_φ1, half_13_05_φ2, half_13_05_φ3, half_13_05_φ4, half_13_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_8) (half_10_05)
    (by simpa only [half_13_05_φ5, show (2:ℝ)*16=32 by norm_num] using half_13_05_hx5)
  exact h.weaken (by norm_num [half_13_05_φ1, half_13_05_φ2, half_13_05_φ3, half_13_05_φ4, half_13_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_05_hx3 : SourcePowerBound (powerBoxCross 8 10 8 half_13_05_φ3) (2598295831/250000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 10) (u := 8) (t := 11)
    (D := 8) (ψ := (456782607/5000000000 : ℝ)) half_13_05_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_05_φ1, half_13_05_φ2, half_13_05_φ3, half_13_05_φ4, half_13_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_05_φ1, half_13_05_φ2, half_13_05_φ3, half_13_05_φ4, half_13_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_05_φ1, half_13_05_φ2, half_13_05_φ3, half_13_05_φ4, half_13_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_9) (half_11_05)
    (by simpa only [half_13_05_φ4, show (2:ℝ)*8=16 by norm_num] using half_13_05_hx4)
  exact h.weaken (by norm_num [half_13_05_φ1, half_13_05_φ2, half_13_05_φ3, half_13_05_φ4, half_13_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_05_hx2 : SourcePowerBound (powerBoxCross 8 11 4 half_13_05_φ2) (128619885369/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 11) (u := 9) (t := 12)
    (D := 4) (ψ := (256447617/2500000000 : ℝ)) half_13_05_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_05_φ1, half_13_05_φ2, half_13_05_φ3, half_13_05_φ4, half_13_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_05_φ1, half_13_05_φ2, half_13_05_φ3, half_13_05_φ4, half_13_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_05_φ1, half_13_05_φ2, half_13_05_φ3, half_13_05_φ4, half_13_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_10_05) (half_12_05)
    (by simpa only [half_13_05_φ3, show (2:ℝ)*4=8 by norm_num] using half_13_05_hx3)
  exact h.weaken (by norm_num [half_13_05_φ1, half_13_05_φ2, half_13_05_φ3, half_13_05_φ4, half_13_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_05_hx1 : SourcePowerBound (powerBoxCross 8 12 2 half_13_05_φ1) (158753759547/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 12) (u := 10) (t := 13)
    (D := 2) (ψ := (1090778491/10000000000 : ℝ)) half_13_05_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_05_φ1, half_13_05_φ2, half_13_05_φ3, half_13_05_φ4, half_13_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_05_φ1, half_13_05_φ2, half_13_05_φ3, half_13_05_φ4, half_13_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_05_φ1, half_13_05_φ2, half_13_05_φ3, half_13_05_φ4, half_13_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_11_05) (half_13_04)
    (by simpa only [half_13_05_φ2, show (2:ℝ)*2=4 by norm_num] using half_13_05_hx2)
  exact h.weaken (by norm_num [half_13_05_φ1, half_13_05_φ2, half_13_05_φ3, half_13_05_φ4, half_13_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_05 : AdmissibleExponent 8 26 (36998117297/2000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 11) (ψ := (570365803/5000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_12_05)
    (by simpa only [half_13_05_φ1] using half_13_05_hx1)
  exact admissibleExponent_mono h (by norm_num [half_13_05_φ1, half_13_05_φ2, half_13_05_φ3, half_13_05_φ4, half_13_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_14_05_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (583738991/5000000000 : ℝ)

def half_14_05_φ2 : Fin 2 → ℝ := Fin.snoc half_14_05_φ1 (562020649/5000000000 : ℝ)

def half_14_05_φ3 : Fin 3 → ℝ := Fin.snoc half_14_05_φ2 (1339393/12500000 : ℝ)

def half_14_05_φ4 : Fin 4 → ℝ := Fin.snoc half_14_05_φ3 (189627609/2000000000 : ℝ)

def half_14_05_φ5 : Fin 5 → ℝ := Fin.snoc half_14_05_φ4 (812689753/10000000000 : ℝ)

theorem half_14_05_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_14_05_φ5) (31199454481/5000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_14_05_φ5 (by norm_num [half_14_05_φ1, half_14_05_φ2, half_14_05_φ3, half_14_05_φ4, half_14_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_05_φ1, half_14_05_φ2, half_14_05_φ3, half_14_05_φ4, half_14_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_05_φ1, half_14_05_φ2, half_14_05_φ3, half_14_05_φ4, half_14_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_14_05_φ1, half_14_05_φ2, half_14_05_φ3, half_14_05_φ4, half_14_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_14_05_φ1, half_14_05_φ2, half_14_05_φ3, half_14_05_φ4, half_14_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_14_05_hx5 : SourcePowerBound (powerBoxCross 8 9 32 half_14_05_φ5) (38267175079/5000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 9) (r := 2) (v := 0) (w := 12) (D := 32)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_14_05_φ5 (by norm_num [half_14_05_φ1, half_14_05_φ2, half_14_05_φ3, half_14_05_φ4, half_14_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_05_φ1, half_14_05_φ2, half_14_05_φ3, half_14_05_φ4, half_14_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_14_05_hF2 (admissibleExponent_zero 8) (half_12_05)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_14_05_φ1, half_14_05_φ2, half_14_05_φ3, half_14_05_φ4, half_14_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_05_hx4 : SourcePowerBound (powerBoxCross 8 10 16 half_14_05_φ4) (92381197363/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 10) (u := 8) (t := 11)
    (D := 16) (ψ := (812689753/10000000000 : ℝ)) half_14_05_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_05_φ1, half_14_05_φ2, half_14_05_φ3, half_14_05_φ4, half_14_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_05_φ1, half_14_05_φ2, half_14_05_φ3, half_14_05_φ4, half_14_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_05_φ1, half_14_05_φ2, half_14_05_φ3, half_14_05_φ4, half_14_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_9) (half_11_05)
    (by simpa only [half_14_05_φ5, show (2:ℝ)*16=32 by norm_num] using half_14_05_hx5)
  exact h.weaken (by norm_num [half_14_05_φ1, half_14_05_φ2, half_14_05_φ3, half_14_05_φ4, half_14_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_05_hx3 : SourcePowerBound (powerBoxCross 8 11 8 half_14_05_φ3) (56859910209/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 11) (u := 9) (t := 12)
    (D := 8) (ψ := (189627609/2000000000 : ℝ)) half_14_05_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_05_φ1, half_14_05_φ2, half_14_05_φ3, half_14_05_φ4, half_14_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_05_φ1, half_14_05_φ2, half_14_05_φ3, half_14_05_φ4, half_14_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_05_φ1, half_14_05_φ2, half_14_05_φ3, half_14_05_φ4, half_14_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_10_05) (half_12_05)
    (by simpa only [half_14_05_φ4, show (2:ℝ)*8=16 by norm_num] using half_14_05_hx4)
  exact h.weaken (by norm_num [half_14_05_φ1, half_14_05_φ2, half_14_05_φ3, half_14_05_φ4, half_14_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_05_hx2 : SourcePowerBound (powerBoxCross 8 12 4 half_14_05_φ2) (28278062479/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 12) (u := 10) (t := 13)
    (D := 4) (ψ := (1339393/12500000 : ℝ)) half_14_05_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_05_φ1, half_14_05_φ2, half_14_05_φ3, half_14_05_φ4, half_14_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_05_φ1, half_14_05_φ2, half_14_05_φ3, half_14_05_φ4, half_14_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_05_φ1, half_14_05_φ2, half_14_05_φ3, half_14_05_φ4, half_14_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_11_05) (half_13_05)
    (by simpa only [half_14_05_φ3, show (2:ℝ)*4=8 by norm_num] using half_14_05_hx3)
  exact h.weaken (by norm_num [half_14_05_φ1, half_14_05_φ2, half_14_05_φ3, half_14_05_φ4, half_14_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_05_hx1 : SourcePowerBound (powerBoxCross 8 13 2 half_14_05_φ1) (43640205203/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 13) (u := 11) (t := 14)
    (D := 2) (ψ := (562020649/5000000000 : ℝ)) half_14_05_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_05_φ1, half_14_05_φ2, half_14_05_φ3, half_14_05_φ4, half_14_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_05_φ1, half_14_05_φ2, half_14_05_φ3, half_14_05_φ4, half_14_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_05_φ1, half_14_05_φ2, half_14_05_φ3, half_14_05_φ4, half_14_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_12_05) (half_14_04)
    (by simpa only [half_14_05_φ2, show (2:ℝ)*2=4 by norm_num] using half_14_05_hx2)
  exact h.weaken (by norm_num [half_14_05_φ1, half_14_05_φ2, half_14_05_φ3, half_14_05_φ4, half_14_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_05 : AdmissibleExponent 8 28 (101873885181/5000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 12) (ψ := (583738991/5000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_13_05)
    (by simpa only [half_14_05_φ1] using half_14_05_hx1)
  exact admissibleExponent_mono h (by norm_num [half_14_05_φ1, half_14_05_φ2, half_14_05_φ3, half_14_05_φ4, half_14_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_15_05_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (297757051/2500000000 : ℝ)

def half_15_05_φ2 : Fin 2 → ℝ := Fin.snoc half_15_05_φ1 (289248211/2500000000 : ℝ)

def half_15_05_φ3 : Fin 3 → ℝ := Fin.snoc half_15_05_φ2 (21862797/200000000 : ℝ)

def half_15_05_φ4 : Fin 4 → ℝ := Fin.snoc half_15_05_φ3 (468488507/5000000000 : ℝ)

def half_15_05_φ5 : Fin 5 → ℝ := Fin.snoc half_15_05_φ4 (160624631/2000000000 : ℝ)

theorem half_15_05_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_15_05_φ5) (61193517593/10000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_15_05_φ5 (by norm_num [half_15_05_φ1, half_15_05_φ2, half_15_05_φ3, half_15_05_φ4, half_15_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_05_φ1, half_15_05_φ2, half_15_05_φ3, half_15_05_φ4, half_15_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_05_φ1, half_15_05_φ2, half_15_05_φ3, half_15_05_φ4, half_15_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_15_05_φ1, half_15_05_φ2, half_15_05_φ3, half_15_05_φ4, half_15_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_15_05_φ1, half_15_05_φ2, half_15_05_φ3, half_15_05_φ4, half_15_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_15_05_hx5 : SourcePowerBound (powerBoxCross 8 10 32 half_15_05_φ5) (10551828663/1250000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 10) (r := 2) (v := 13) (w := 14) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_15_05_φ5 (by norm_num [half_15_05_φ1, half_15_05_φ2, half_15_05_φ3, half_15_05_φ4, half_15_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_05_φ1, half_15_05_φ2, half_15_05_φ3, half_15_05_φ4, half_15_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_15_05_hF2 (half_13_05) (half_14_05)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_15_05_φ1, half_15_05_φ2, half_15_05_φ3, half_15_05_φ4, half_15_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_05_hx4 : SourcePowerBound (powerBoxCross 8 11 16 half_15_05_φ4) (101349202611/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 11) (u := 9) (t := 12)
    (D := 16) (ψ := (160624631/2000000000 : ℝ)) half_15_05_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_05_φ1, half_15_05_φ2, half_15_05_φ3, half_15_05_φ4, half_15_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_05_φ1, half_15_05_φ2, half_15_05_φ3, half_15_05_φ4, half_15_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_05_φ1, half_15_05_φ2, half_15_05_φ3, half_15_05_φ4, half_15_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_10_05) (half_12_05)
    (by simpa only [half_15_05_φ5, show (2:ℝ)*16=32 by norm_num] using half_15_05_hx5)
  exact h.weaken (by norm_num [half_15_05_φ1, half_15_05_φ2, half_15_05_φ3, half_15_05_φ4, half_15_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_05_hx3 : SourcePowerBound (powerBoxCross 8 12 8 half_15_05_φ3) (124134971417/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 12) (u := 10) (t := 13)
    (D := 8) (ψ := (468488507/5000000000 : ℝ)) half_15_05_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_05_φ1, half_15_05_φ2, half_15_05_φ3, half_15_05_φ4, half_15_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_05_φ1, half_15_05_φ2, half_15_05_φ3, half_15_05_φ4, half_15_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_05_φ1, half_15_05_φ2, half_15_05_φ3, half_15_05_φ4, half_15_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_11_05) (half_13_05)
    (by simpa only [half_15_05_φ4, show (2:ℝ)*8=16 by norm_num] using half_15_05_hx4)
  exact h.weaken (by norm_num [half_15_05_φ1, half_15_05_φ2, half_15_05_φ3, half_15_05_φ4, half_15_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_05_hx2 : SourcePowerBound (powerBoxCross 8 13 4 half_15_05_φ2) (9648387677/625000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 13) (u := 11) (t := 14)
    (D := 4) (ψ := (21862797/200000000 : ℝ)) half_15_05_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_05_φ1, half_15_05_φ2, half_15_05_φ3, half_15_05_φ4, half_15_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_05_φ1, half_15_05_φ2, half_15_05_φ3, half_15_05_φ4, half_15_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_05_φ1, half_15_05_φ2, half_15_05_φ3, half_15_05_φ4, half_15_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_12_05) (half_14_05)
    (by simpa only [half_15_05_φ3, show (2:ℝ)*4=8 by norm_num] using half_15_05_hx3)
  exact h.weaken (by norm_num [half_15_05_φ1, half_15_05_φ2, half_15_05_φ3, half_15_05_φ4, half_15_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_05_hx1 : SourcePowerBound (powerBoxCross 8 14 2 half_15_05_φ1) (190671864469/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 14) (u := 12) (t := 15)
    (D := 2) (ψ := (289248211/2500000000 : ℝ)) half_15_05_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_05_φ1, half_15_05_φ2, half_15_05_φ3, half_15_05_φ4, half_15_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_05_φ1, half_15_05_φ2, half_15_05_φ3, half_15_05_φ4, half_15_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_05_φ1, half_15_05_φ2, half_15_05_φ3, half_15_05_φ4, half_15_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_13_05) (half_15_04)
    (by simpa only [half_15_05_φ2, show (2:ℝ)*2=4 by norm_num] using half_15_05_hx2)
  exact h.weaken (by norm_num [half_15_05_φ1, half_15_05_φ2, half_15_05_φ3, half_15_05_φ4, half_15_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_05 : AdmissibleExponent 8 30 (222829625977/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 13) (ψ := (297757051/2500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_14_05)
    (by simpa only [half_15_05_φ1] using half_15_05_hx1)
  exact admissibleExponent_mono h (by norm_num [half_15_05_φ1, half_15_05_φ2, half_15_05_φ3, half_15_05_φ4, half_15_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_16_05_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (37762681/312500000 : ℝ)

def half_16_05_φ2 : Fin 2 → ℝ := Fin.snoc half_16_05_φ1 (296105883/2500000000 : ℝ)

def half_16_05_φ3 : Fin 3 → ℝ := Fin.snoc half_16_05_φ2 (1086738667/10000000000 : ℝ)

def half_16_05_φ4 : Fin 4 → ℝ := Fin.snoc half_16_05_φ3 (465745143/5000000000 : ℝ)

def half_16_05_φ5 : Fin 5 → ℝ := Fin.snoc half_16_05_φ4 (159684049/2000000000 : ℝ)

theorem half_16_05_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_16_05_φ5) (30300475519/5000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_16_05_φ5 (by norm_num [half_16_05_φ1, half_16_05_φ2, half_16_05_φ3, half_16_05_φ4, half_16_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_05_φ1, half_16_05_φ2, half_16_05_φ3, half_16_05_φ4, half_16_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_05_φ1, half_16_05_φ2, half_16_05_φ3, half_16_05_φ4, half_16_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_16_05_φ1, half_16_05_φ2, half_16_05_φ3, half_16_05_φ4, half_16_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_16_05_φ1, half_16_05_φ2, half_16_05_φ3, half_16_05_φ4, half_16_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_16_05_hx5 : SourcePowerBound (powerBoxCross 8 11 32 half_16_05_φ5) (92925194969/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 11) (r := 2) (v := 14) (w := 15) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_16_05_φ5 (by norm_num [half_16_05_φ1, half_16_05_φ2, half_16_05_φ3, half_16_05_φ4, half_16_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_05_φ1, half_16_05_φ2, half_16_05_φ3, half_16_05_φ4, half_16_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_16_05_hF2 (half_14_05) (half_15_05)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_16_05_φ1, half_16_05_φ2, half_16_05_φ3, half_16_05_φ4, half_16_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_05_hx4 : SourcePowerBound (powerBoxCross 8 12 16 half_16_05_φ4) (55551193223/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 12) (u := 10) (t := 13)
    (D := 16) (ψ := (159684049/2000000000 : ℝ)) half_16_05_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_05_φ1, half_16_05_φ2, half_16_05_φ3, half_16_05_φ4, half_16_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_05_φ1, half_16_05_φ2, half_16_05_φ3, half_16_05_φ4, half_16_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_05_φ1, half_16_05_φ2, half_16_05_φ3, half_16_05_φ4, half_16_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_11_05) (half_13_05)
    (by simpa only [half_16_05_φ5, show (2:ℝ)*16=32 by norm_num] using half_16_05_hx5)
  exact h.weaken (by norm_num [half_16_05_φ1, half_16_05_φ2, half_16_05_φ3, half_16_05_φ4, half_16_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_05_hx3 : SourcePowerBound (powerBoxCross 8 13 8 half_16_05_φ3) (67755508863/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 13) (u := 11) (t := 14)
    (D := 8) (ψ := (465745143/5000000000 : ℝ)) half_16_05_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_05_φ1, half_16_05_φ2, half_16_05_φ3, half_16_05_φ4, half_16_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_05_φ1, half_16_05_φ2, half_16_05_φ3, half_16_05_φ4, half_16_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_05_φ1, half_16_05_φ2, half_16_05_φ3, half_16_05_φ4, half_16_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_12_05) (half_14_05)
    (by simpa only [half_16_05_φ4, show (2:ℝ)*8=16 by norm_num] using half_16_05_hx4)
  exact h.weaken (by norm_num [half_16_05_φ1, half_16_05_φ2, half_16_05_φ3, half_16_05_φ4, half_16_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_05_hx2 : SourcePowerBound (powerBoxCross 8 14 4 half_16_05_φ2) (167719989391/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 14) (u := 12) (t := 15)
    (D := 4) (ψ := (1086738667/10000000000 : ℝ)) half_16_05_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_05_φ1, half_16_05_φ2, half_16_05_φ3, half_16_05_φ4, half_16_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_05_φ1, half_16_05_φ2, half_16_05_φ3, half_16_05_φ4, half_16_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_05_φ1, half_16_05_φ2, half_16_05_φ3, half_16_05_φ4, half_16_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_13_05) (half_15_05)
    (by simpa only [half_16_05_φ3, show (2:ℝ)*4=8 by norm_num] using half_16_05_hx3)
  exact h.weaken (by norm_num [half_16_05_φ1, half_16_05_φ2, half_16_05_φ3, half_16_05_φ4, half_16_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_05_hx1 : SourcePowerBound (powerBoxCross 8 15 2 half_16_05_φ1) (207111170711/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 15) (u := 13) (t := 16)
    (D := 2) (ψ := (296105883/2500000000 : ℝ)) half_16_05_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_05_φ1, half_16_05_φ2, half_16_05_φ3, half_16_05_φ4, half_16_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_05_φ1, half_16_05_φ2, half_16_05_φ3, half_16_05_φ4, half_16_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_05_φ1, half_16_05_φ2, half_16_05_φ3, half_16_05_φ4, half_16_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_14_05) (half_16_04)
    (by simpa only [half_16_05_φ2, show (2:ℝ)*2=4 by norm_num] using half_16_05_hx2)
  exact h.weaken (by norm_num [half_16_05_φ1, half_16_05_φ2, half_16_05_φ3, half_16_05_φ4, half_16_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_05 : AdmissibleExponent 8 32 (242154938679/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 14) (ψ := (37762681/312500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_15_05)
    (by simpa only [half_16_05_φ1] using half_16_05_hx1)
  exact admissibleExponent_mono h (by norm_num [half_16_05_φ1, half_16_05_φ2, half_16_05_φ3, half_16_05_φ4, half_16_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_17_05_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (38168441/312500000 : ℝ)

def half_17_05_φ2 : Fin 2 → ℝ := Fin.snoc half_17_05_φ1 (301195847/2500000000 : ℝ)

def half_17_05_φ3 : Fin 3 → ℝ := Fin.snoc half_17_05_φ2 (540987607/5000000000 : ℝ)

def half_17_05_φ4 : Fin 4 → ℝ := Fin.snoc half_17_05_φ3 (463703663/5000000000 : ℝ)

def half_17_05_φ5 : Fin 5 → ℝ := Fin.snoc half_17_05_φ4 (158984113/2000000000 : ℝ)

theorem half_17_05_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_17_05_φ5) (12031998259/2000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_17_05_φ5 (by norm_num [half_17_05_φ1, half_17_05_φ2, half_17_05_φ3, half_17_05_φ4, half_17_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_05_φ1, half_17_05_φ2, half_17_05_φ3, half_17_05_φ4, half_17_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_05_φ1, half_17_05_φ2, half_17_05_φ3, half_17_05_φ4, half_17_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_17_05_φ1, half_17_05_φ2, half_17_05_φ3, half_17_05_φ4, half_17_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_17_05_φ1, half_17_05_φ2, half_17_05_φ3, half_17_05_φ4, half_17_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_17_05_hx5 : SourcePowerBound (powerBoxCross 8 12 32 half_17_05_φ5) (50831135609/5000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 12) (r := 2) (v := 0) (w := 16) (D := 32)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_17_05_φ5 (by norm_num [half_17_05_φ1, half_17_05_φ2, half_17_05_φ3, half_17_05_φ4, half_17_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_05_φ1, half_17_05_φ2, half_17_05_φ3, half_17_05_φ4, half_17_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_17_05_hF2 (admissibleExponent_zero 8) (half_16_05)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_17_05_φ1, half_17_05_φ2, half_17_05_φ3, half_17_05_φ4, half_17_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

end Waring.SeedCompletionAlternate8Seeds
