import Waring.SeedCompletionAlternate8Part02
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

theorem half_17_05_hx4 : SourcePowerBound (powerBoxCross 8 13 16 half_17_05_φ4) (4845417139/400000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 13) (u := 11) (t := 14)
    (D := 16) (ψ := (158984113/2000000000 : ℝ)) half_17_05_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_05_φ1, half_17_05_φ2, half_17_05_φ3, half_17_05_φ4, half_17_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_05_φ1, half_17_05_φ2, half_17_05_φ3, half_17_05_φ4, half_17_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_05_φ1, half_17_05_φ2, half_17_05_φ3, half_17_05_φ4, half_17_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_12_05) (half_14_05)
    (by simpa only [half_17_05_φ5, show (2:ℝ)*16=32 by norm_num] using half_17_05_hx5)
  exact h.weaken (by norm_num [half_17_05_φ1, half_17_05_φ2, half_17_05_φ3, half_17_05_φ4, half_17_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_05_hx3 : SourcePowerBound (powerBoxCross 8 14 8 half_17_05_φ3) (36802656253/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 14) (u := 12) (t := 15)
    (D := 8) (ψ := (463703663/5000000000 : ℝ)) half_17_05_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_05_φ1, half_17_05_φ2, half_17_05_φ3, half_17_05_φ4, half_17_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_05_φ1, half_17_05_φ2, half_17_05_φ3, half_17_05_φ4, half_17_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_05_φ1, half_17_05_φ2, half_17_05_φ3, half_17_05_φ4, half_17_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_13_05) (half_15_05)
    (by simpa only [half_17_05_φ4, show (2:ℝ)*8=16 by norm_num] using half_17_05_hx4)
  exact h.weaken (by norm_num [half_17_05_φ1, half_17_05_φ2, half_17_05_φ3, half_17_05_φ4, half_17_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_05_hx2 : SourcePowerBound (powerBoxCross 8 15 4 half_17_05_φ2) (181422345229/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 15) (u := 13) (t := 16)
    (D := 4) (ψ := (540987607/5000000000 : ℝ)) half_17_05_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_05_φ1, half_17_05_φ2, half_17_05_φ3, half_17_05_φ4, half_17_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_05_φ1, half_17_05_φ2, half_17_05_φ3, half_17_05_φ4, half_17_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_05_φ1, half_17_05_φ2, half_17_05_φ3, half_17_05_φ4, half_17_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_14_05) (half_16_05)
    (by simpa only [half_17_05_φ3, show (2:ℝ)*4=8 by norm_num] using half_17_05_hx3)
  exact h.weaken (by norm_num [half_17_05_φ1, half_17_05_φ2, half_17_05_φ3, half_17_05_φ4, half_17_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_05_hx1 : SourcePowerBound (powerBoxCross 8 16 2 half_17_05_φ1) (3496871313/156250000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 16) (u := 14) (t := 17)
    (D := 2) (ψ := (301195847/2500000000 : ℝ)) half_17_05_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_05_φ1, half_17_05_φ2, half_17_05_φ3, half_17_05_φ4, half_17_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_05_φ1, half_17_05_φ2, half_17_05_φ3, half_17_05_φ4, half_17_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_05_φ1, half_17_05_φ2, half_17_05_φ3, half_17_05_φ4, half_17_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_15_05) (half_17_04)
    (by simpa only [half_17_05_φ2, show (2:ℝ)*2=4 by norm_num] using half_17_05_hx2)
  exact h.weaken (by norm_num [half_17_05_φ1, half_17_05_φ2, half_17_05_φ3, half_17_05_φ4, half_17_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_05 : AdmissibleExponent 8 34 (8176964297/312500000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 15) (ψ := (38168441/312500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_16_05)
    (by simpa only [half_17_05_φ1] using half_17_05_hx1)
  exact admissibleExponent_mono h (by norm_num [half_17_05_φ1, half_17_05_φ2, half_17_05_φ3, half_17_05_φ4, half_17_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_18_05_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (76986263/625000000 : ℝ)

def half_18_05_φ2 : Fin 2 → ℝ := Fin.snoc half_18_05_φ1 (152571133/1250000000 : ℝ)

def half_18_05_φ3 : Fin 3 → ℝ := Fin.snoc half_18_05_φ2 (539117909/5000000000 : ℝ)

def half_18_05_φ4 : Fin 4 → ℝ := Fin.snoc half_18_05_φ3 (924202129/10000000000 : ℝ)

def half_18_05_φ5 : Fin 5 → ℝ := Fin.snoc half_18_05_φ4 (396086627/5000000000 : ℝ)

theorem half_18_05_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_18_05_φ5) (59813830067/10000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_18_05_φ5 (by norm_num [half_18_05_φ1, half_18_05_φ2, half_18_05_φ3, half_18_05_φ4, half_18_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_18_05_φ1, half_18_05_φ2, half_18_05_φ3, half_18_05_φ4, half_18_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_18_05_φ1, half_18_05_φ2, half_18_05_φ3, half_18_05_φ4, half_18_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_18_05_φ1, half_18_05_φ2, half_18_05_φ3, half_18_05_φ4, half_18_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_18_05_φ1, half_18_05_φ2, half_18_05_φ3, half_18_05_φ4, half_18_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_18_05_hx5 : SourcePowerBound (powerBoxCross 8 13 32 half_18_05_φ5) (110576594537/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 13) (r := 2) (v := 17) (w := 18) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_18_05_φ5 (by norm_num [half_18_05_φ1, half_18_05_φ2, half_18_05_φ3, half_18_05_φ4, half_18_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_18_05_φ1, half_18_05_φ2, half_18_05_φ3, half_18_05_φ4, half_18_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_18_05_hF2 (half_17_05) (half_18_04)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_18_05_φ1, half_18_05_φ2, half_18_05_φ3, half_18_05_φ4, half_18_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_18_05_hx4 : SourcePowerBound (powerBoxCross 8 14 16 half_18_05_φ4) (5255223687/400000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 14) (u := 12) (t := 15)
    (D := 16) (ψ := (396086627/5000000000 : ℝ)) half_18_05_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_18_05_φ1, half_18_05_φ2, half_18_05_φ3, half_18_05_φ4, half_18_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_18_05_φ1, half_18_05_φ2, half_18_05_φ3, half_18_05_φ4, half_18_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_18_05_φ1, half_18_05_φ2, half_18_05_φ3, half_18_05_φ4, half_18_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_13_05) (half_15_05)
    (by simpa only [half_18_05_φ5, show (2:ℝ)*16=32 by norm_num] using half_18_05_hx5)
  exact h.weaken (by norm_num [half_18_05_φ1, half_18_05_φ2, half_18_05_φ3, half_18_05_φ4, half_18_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_18_05_hx3 : SourcePowerBound (powerBoxCross 8 15 8 half_18_05_φ3) (39785003889/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 15) (u := 13) (t := 16)
    (D := 8) (ψ := (924202129/10000000000 : ℝ)) half_18_05_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_18_05_φ1, half_18_05_φ2, half_18_05_φ3, half_18_05_φ4, half_18_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_18_05_φ1, half_18_05_φ2, half_18_05_φ3, half_18_05_φ4, half_18_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_18_05_φ1, half_18_05_φ2, half_18_05_φ3, half_18_05_φ4, half_18_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_14_05) (half_16_05)
    (by simpa only [half_18_05_φ4, show (2:ℝ)*8=16 by norm_num] using half_18_05_hx4)
  exact h.weaken (by norm_num [half_18_05_φ1, half_18_05_φ2, half_18_05_φ3, half_18_05_φ4, half_18_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_18_05_hx2 : SourcePowerBound (powerBoxCross 8 16 4 half_18_05_φ2) (97684098767/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 16) (u := 14) (t := 17)
    (D := 4) (ψ := (539117909/5000000000 : ℝ)) half_18_05_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_18_05_φ1, half_18_05_φ2, half_18_05_φ3, half_18_05_φ4, half_18_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_18_05_φ1, half_18_05_φ2, half_18_05_φ3, half_18_05_φ4, half_18_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_18_05_φ1, half_18_05_φ2, half_18_05_φ3, half_18_05_φ4, half_18_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_15_05) (half_17_05)
    (by simpa only [half_18_05_φ3, show (2:ℝ)*4=8 by norm_num] using half_18_05_hx3)
  exact h.weaken (by norm_num [half_18_05_φ1, half_18_05_φ2, half_18_05_φ3, half_18_05_φ4, half_18_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_18_05_hx1 : SourcePowerBound (powerBoxCross 8 17 2 half_18_05_φ1) (240663524809/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 17) (u := 15) (t := 18)
    (D := 2) (ψ := (152571133/1250000000 : ℝ)) half_18_05_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_18_05_φ1, half_18_05_φ2, half_18_05_φ3, half_18_05_φ4, half_18_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_18_05_φ1, half_18_05_φ2, half_18_05_φ3, half_18_05_φ4, half_18_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_18_05_φ1, half_18_05_φ2, half_18_05_φ3, half_18_05_φ4, half_18_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_16_05) (half_18_04)
    (by simpa only [half_18_05_φ2, show (2:ℝ)*2=4 by norm_num] using half_18_05_hx2)
  exact h.weaken (by norm_num [half_18_05_φ1, half_18_05_φ2, half_18_05_φ3, half_18_05_φ4, half_18_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_18_05 : AdmissibleExponent 8 36 (281312271673/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 16) (ψ := (76986263/625000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_17_05)
    (by simpa only [half_18_05_φ1] using half_18_05_hx1)
  exact admissibleExponent_mono h (by norm_num [half_18_05_φ1, half_18_05_φ2, half_18_05_φ3, half_18_05_φ4, half_18_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_19_05_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1240205603/10000000000 : ℝ)

def half_19_05_φ2 : Fin 2 → ℝ := Fin.snoc half_19_05_φ1 (616360589/5000000000 : ℝ)

def half_19_05_φ3 : Fin 3 → ℝ := Fin.snoc half_19_05_φ2 (1075296173/10000000000 : ℝ)

def half_19_05_φ4 : Fin 4 → ℝ := Fin.snoc half_19_05_φ3 (460841217/5000000000 : ℝ)

def half_19_05_φ5 : Fin 5 → ℝ := Fin.snoc half_19_05_φ4 (158002703/2000000000 : ℝ)

theorem half_19_05_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_19_05_φ5) (59541703037/10000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_19_05_φ5 (by norm_num [half_19_05_φ1, half_19_05_φ2, half_19_05_φ3, half_19_05_φ4, half_19_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_19_05_φ1, half_19_05_φ2, half_19_05_φ3, half_19_05_φ4, half_19_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_19_05_φ1, half_19_05_φ2, half_19_05_φ3, half_19_05_φ4, half_19_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_19_05_φ1, half_19_05_φ2, half_19_05_φ3, half_19_05_φ4, half_19_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_19_05_φ1, half_19_05_φ2, half_19_05_φ3, half_19_05_φ4, half_19_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_19_05_hx5 : SourcePowerBound (powerBoxCross 8 14 32 half_19_05_φ5) (119601100567/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 14) (r := 2) (v := 18) (w := 19) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_19_05_φ5 (by norm_num [half_19_05_φ1, half_19_05_φ2, half_19_05_φ3, half_19_05_φ4, half_19_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_19_05_φ1, half_19_05_φ2, half_19_05_φ3, half_19_05_φ4, half_19_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_19_05_hF2 (half_18_05) (half_19_04)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_19_05_φ1, half_19_05_φ2, half_19_05_φ3, half_19_05_φ4, half_19_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_19_05_hx4 : SourcePowerBound (powerBoxCross 8 15 16 half_19_05_φ4) (141778049961/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 15) (u := 13) (t := 16)
    (D := 16) (ψ := (158002703/2000000000 : ℝ)) half_19_05_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_19_05_φ1, half_19_05_φ2, half_19_05_φ3, half_19_05_φ4, half_19_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_19_05_φ1, half_19_05_φ2, half_19_05_φ3, half_19_05_φ4, half_19_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_19_05_φ1, half_19_05_φ2, half_19_05_φ3, half_19_05_φ4, half_19_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_14_05) (half_16_05)
    (by simpa only [half_19_05_φ5, show (2:ℝ)*16=32 by norm_num] using half_19_05_hx5)
  exact h.weaken (by norm_num [half_19_05_φ1, half_19_05_φ2, half_19_05_φ3, half_19_05_φ4, half_19_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_19_05_hx3 : SourcePowerBound (powerBoxCross 8 16 8 half_19_05_φ3) (171244160827/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 16) (u := 14) (t := 17)
    (D := 8) (ψ := (460841217/5000000000 : ℝ)) half_19_05_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_19_05_φ1, half_19_05_φ2, half_19_05_φ3, half_19_05_φ4, half_19_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_19_05_φ1, half_19_05_φ2, half_19_05_φ3, half_19_05_φ4, half_19_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_19_05_φ1, half_19_05_φ2, half_19_05_φ3, half_19_05_φ4, half_19_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_15_05) (half_17_05)
    (by simpa only [half_19_05_φ4, show (2:ℝ)*8=16 by norm_num] using half_19_05_hx4)
  exact h.weaken (by norm_num [half_19_05_φ1, half_19_05_φ2, half_19_05_φ3, half_19_05_φ4, half_19_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_19_05_hx2 : SourcePowerBound (powerBoxCross 8 17 4 half_19_05_φ2) (52376707669/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 17) (u := 15) (t := 18)
    (D := 4) (ψ := (1075296173/10000000000 : ℝ)) half_19_05_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_19_05_φ1, half_19_05_φ2, half_19_05_φ3, half_19_05_φ4, half_19_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_19_05_φ1, half_19_05_φ2, half_19_05_φ3, half_19_05_φ4, half_19_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_19_05_φ1, half_19_05_φ2, half_19_05_φ3, half_19_05_φ4, half_19_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_16_05) (half_18_05)
    (by simpa only [half_19_05_φ3, show (2:ℝ)*4=8 by norm_num] using half_19_05_hx3)
  exact h.weaken (by norm_num [half_19_05_φ1, half_19_05_φ2, half_19_05_φ3, half_19_05_φ4, half_19_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_19_05_hx1 : SourcePowerBound (powerBoxCross 8 18 2 half_19_05_φ1) (64415992933/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 18) (u := 16) (t := 19)
    (D := 2) (ψ := (616360589/5000000000 : ℝ)) half_19_05_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_19_05_φ1, half_19_05_φ2, half_19_05_φ3, half_19_05_φ4, half_19_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_19_05_φ1, half_19_05_φ2, half_19_05_φ3, half_19_05_φ4, half_19_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_19_05_φ1, half_19_05_φ2, half_19_05_φ3, half_19_05_φ4, half_19_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_17_05) (half_19_04)
    (by simpa only [half_19_05_φ2, show (2:ℝ)*2=4 by norm_num] using half_19_05_hx2)
  exact h.weaken (by norm_num [half_19_05_φ1, half_19_05_φ2, half_19_05_φ3, half_19_05_φ4, half_19_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_19_05 : AdmissibleExponent 8 38 (301071167837/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 17) (ψ := (1240205603/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_18_05)
    (by simpa only [half_19_05_φ1] using half_19_05_hx1)
  exact admissibleExponent_mono h (by norm_num [half_19_05_φ1, half_19_05_φ2, half_19_05_φ3, half_19_05_φ4, half_19_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_20_05_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1248147967/10000000000 : ℝ)

def half_20_05_φ2 : Fin 2 → ℝ := Fin.snoc half_20_05_φ1 (1242139381/10000000000 : ℝ)

def half_20_05_φ3 : Fin 3 → ℝ := Fin.snoc half_20_05_φ2 (1072816093/10000000000 : ℝ)

def half_20_05_φ4 : Fin 4 → ℝ := Fin.snoc half_20_05_φ3 (919556651/10000000000 : ℝ)

def half_20_05_φ5 : Fin 5 → ℝ := Fin.snoc half_20_05_φ4 (157638283/2000000000 : ℝ)

theorem half_20_05_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_20_05_φ5) (59312118353/10000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_20_05_φ5 (by norm_num [half_20_05_φ1, half_20_05_φ2, half_20_05_φ3, half_20_05_φ4, half_20_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_20_05_φ1, half_20_05_φ2, half_20_05_φ3, half_20_05_φ4, half_20_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_20_05_φ1, half_20_05_φ2, half_20_05_φ3, half_20_05_φ4, half_20_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_20_05_φ1, half_20_05_φ2, half_20_05_φ3, half_20_05_φ4, half_20_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_20_05_φ1, half_20_05_φ2, half_20_05_φ3, half_20_05_φ4, half_20_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_20_05_hx5 : SourcePowerBound (powerBoxCross 8 15 32 half_20_05_φ5) (128701541783/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 15) (r := 2) (v := 0) (w := 20) (D := 32)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_20_05_φ5 (by norm_num [half_20_05_φ1, half_20_05_φ2, half_20_05_φ3, half_20_05_φ4, half_20_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_20_05_φ1, half_20_05_φ2, half_20_05_φ3, half_20_05_φ4, half_20_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_20_05_hF2 (admissibleExponent_zero 8) (half_20_04)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_20_05_φ1, half_20_05_φ2, half_20_05_φ3, half_20_05_φ4, half_20_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_20_05_hx4 : SourcePowerBound (powerBoxCross 8 16 16 half_20_05_φ4) (30454876479/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 16) (u := 14) (t := 17)
    (D := 16) (ψ := (157638283/2000000000 : ℝ)) half_20_05_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_20_05_φ1, half_20_05_φ2, half_20_05_φ3, half_20_05_φ4, half_20_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_20_05_φ1, half_20_05_φ2, half_20_05_φ3, half_20_05_φ4, half_20_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_20_05_φ1, half_20_05_φ2, half_20_05_φ3, half_20_05_φ4, half_20_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_15_05) (half_17_05)
    (by simpa only [half_20_05_φ5, show (2:ℝ)*16=32 by norm_num] using half_20_05_hx5)
  exact h.weaken (by norm_num [half_20_05_φ1, half_20_05_φ2, half_20_05_φ3, half_20_05_φ4, half_20_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_20_05_hx3 : SourcePowerBound (powerBoxCross 8 17 8 half_20_05_φ3) (91729178461/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 17) (u := 15) (t := 18)
    (D := 8) (ψ := (919556651/10000000000 : ℝ)) half_20_05_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_20_05_φ1, half_20_05_φ2, half_20_05_φ3, half_20_05_φ4, half_20_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_20_05_φ1, half_20_05_φ2, half_20_05_φ3, half_20_05_φ4, half_20_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_20_05_φ1, half_20_05_φ2, half_20_05_φ3, half_20_05_φ4, half_20_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_16_05) (half_18_05)
    (by simpa only [half_20_05_φ4, show (2:ℝ)*8=16 by norm_num] using half_20_05_hx4)
  exact h.weaken (by norm_num [half_20_05_φ1, half_20_05_φ2, half_20_05_φ3, half_20_05_φ4, half_20_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_20_05_hx2 : SourcePowerBound (powerBoxCross 8 18 4 half_20_05_φ2) (223762536191/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 18) (u := 16) (t := 19)
    (D := 4) (ψ := (1072816093/10000000000 : ℝ)) half_20_05_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_20_05_φ1, half_20_05_φ2, half_20_05_φ3, half_20_05_φ4, half_20_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_20_05_φ1, half_20_05_φ2, half_20_05_φ3, half_20_05_φ4, half_20_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_20_05_φ1, half_20_05_φ2, half_20_05_φ3, half_20_05_φ4, half_20_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_17_05) (half_19_05)
    (by simpa only [half_20_05_φ3, show (2:ℝ)*4=8 by norm_num] using half_20_05_hx3)
  exact h.weaken (by norm_num [half_20_05_φ1, half_20_05_φ2, half_20_05_φ3, half_20_05_φ4, half_20_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_20_05_hx1 : SourcePowerBound (powerBoxCross 8 19 2 half_20_05_φ1) (137370589601/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 19) (u := 17) (t := 20)
    (D := 2) (ψ := (1242139381/10000000000 : ℝ)) half_20_05_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_20_05_φ1, half_20_05_φ2, half_20_05_φ3, half_20_05_φ4, half_20_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_20_05_φ1, half_20_05_φ2, half_20_05_φ3, half_20_05_φ4, half_20_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_20_05_φ1, half_20_05_φ2, half_20_05_φ3, half_20_05_φ4, half_20_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_18_05) (half_20_04)
    (by simpa only [half_20_05_φ2, show (2:ℝ)*2=4 by norm_num] using half_20_05_hx2)
  exact h.weaken (by norm_num [half_20_05_φ1, half_20_05_φ2, half_20_05_φ3, half_20_05_φ4, half_20_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_20_05 : AdmissibleExponent 8 40 (320922653981/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 18) (ψ := (1248147967/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_19_05)
    (by simpa only [half_20_05_φ1] using half_20_05_hx1)
  exact admissibleExponent_mono h (by norm_num [half_20_05_φ1, half_20_05_φ2, half_20_05_φ3, half_20_05_φ4, half_20_05_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_10_06_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (516064909/5000000000 : ℝ)

def half_10_06_φ2 : Fin 2 → ℝ := Fin.snoc half_10_06_φ1 (192282513/2000000000 : ℝ)

def half_10_06_φ3 : Fin 3 → ℝ := Fin.snoc half_10_06_φ2 (836611083/10000000000 : ℝ)

def half_10_06_φ4 : Fin 4 → ℝ := Fin.snoc half_10_06_φ3 (549104637/10000000000 : ℝ)

theorem half_10_06_hF2 : SourcePowerBound (paddedMoment 8 0 2 16 half_10_06_φ4) (69035579837/10000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 4) (r := 0) (n := 1) (D := 16)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_10_06_φ4 (by norm_num [half_10_06_φ1, half_10_06_φ2, half_10_06_φ3, half_10_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_06_φ1, half_10_06_φ2, half_10_06_φ3, half_10_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_06_φ1, half_10_06_φ2, half_10_06_φ3, half_10_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_10_06_φ1, half_10_06_φ2, half_10_06_φ3, half_10_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_10_06_φ1, half_10_06_φ2, half_10_06_φ3, half_10_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_10_06_hx4 : SourcePowerBound (powerBoxCross 8 6 16 half_10_06_φ4) (33067090963/5000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 6) (r := 2) (v := 0) (w := 8) (D := 16)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_10_06_φ4 (by norm_num [half_10_06_φ1, half_10_06_φ2, half_10_06_φ3, half_10_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_06_φ1, half_10_06_φ2, half_10_06_φ3, half_10_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_10_06_hF2 (admissibleExponent_zero 8) (SeedCompletionHigher8SimpleSeeds.degree8_half_8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_10_06_φ1, half_10_06_φ2, half_10_06_φ3, half_10_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_06_hx3 : SourcePowerBound (powerBoxCross 8 7 8 half_10_06_φ3) (38233767291/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 7) (u := 5) (t := 8)
    (D := 8) (ψ := (549104637/10000000000 : ℝ)) half_10_06_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_06_φ1, half_10_06_φ2, half_10_06_φ3, half_10_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_06_φ1, half_10_06_φ2, half_10_06_φ3, half_10_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_06_φ1, half_10_06_φ2, half_10_06_φ3, half_10_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionEven8SecondSeeds.degree8_half_6) (SeedCompletionHigher8SimpleSeeds.degree8_half_8)
    (by simpa only [half_10_06_φ4, show (2:ℝ)*8=16 by norm_num] using half_10_06_hx4)
  exact h.weaken (by norm_num [half_10_06_φ1, half_10_06_φ2, half_10_06_φ3, half_10_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_06_hx2 : SourcePowerBound (powerBoxCross 8 8 4 half_10_06_φ2) (11567870229/1250000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 8) (u := 6) (t := 9)
    (D := 4) (ψ := (836611083/10000000000 : ℝ)) half_10_06_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_06_φ1, half_10_06_φ2, half_10_06_φ3, half_10_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_06_φ1, half_10_06_φ2, half_10_06_φ3, half_10_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_06_φ1, half_10_06_φ2, half_10_06_φ3, half_10_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_7) (SeedCompletionHigher8SimpleSeeds.degree8_half_9)
    (by simpa only [half_10_06_φ3, show (2:ℝ)*4=8 by norm_num] using half_10_06_hx3)
  exact h.weaken (by norm_num [half_10_06_φ1, half_10_06_φ2, half_10_06_φ3, half_10_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_06_hx1 : SourcePowerBound (powerBoxCross 8 9 2 half_10_06_φ1) (22748068693/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 9) (u := 7) (t := 10)
    (D := 2) (ψ := (192282513/2000000000 : ℝ)) half_10_06_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_06_φ1, half_10_06_φ2, half_10_06_φ3, half_10_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_06_φ1, half_10_06_φ2, half_10_06_φ3, half_10_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_06_φ1, half_10_06_φ2, half_10_06_φ3, half_10_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_8) (half_10_05)
    (by simpa only [half_10_06_φ2, show (2:ℝ)*2=4 by norm_num] using half_10_06_hx2)
  exact h.weaken (by norm_num [half_10_06_φ1, half_10_06_φ2, half_10_06_φ3, half_10_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_06 : AdmissibleExponent 8 20 (131286550371/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 8) (ψ := (516064909/5000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_9)
    (by simpa only [half_10_06_φ1] using half_10_06_hx1)
  exact admissibleExponent_mono h (by norm_num [half_10_06_φ1, half_10_06_φ2, half_10_06_φ3, half_10_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_11_06_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (537822683/5000000000 : ℝ)

def half_11_06_φ2 : Fin 2 → ℝ := Fin.snoc half_11_06_φ1 (202489383/2000000000 : ℝ)

def half_11_06_φ3 : Fin 3 → ℝ := Fin.snoc half_11_06_φ2 (92240381/1000000000 : ℝ)

def half_11_06_φ4 : Fin 4 → ℝ := Fin.snoc half_11_06_φ3 (740812601/10000000000 : ℝ)

theorem half_11_06_hF2 : SourcePowerBound (paddedMoment 8 0 2 16 half_11_06_φ4) (15305629367/2500000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 4) (r := 0) (n := 1) (D := 16)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_11_06_φ4 (by norm_num [half_11_06_φ1, half_11_06_φ2, half_11_06_φ3, half_11_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_06_φ1, half_11_06_φ2, half_11_06_φ3, half_11_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_06_φ1, half_11_06_φ2, half_11_06_φ3, half_11_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_11_06_φ1, half_11_06_φ2, half_11_06_φ3, half_11_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_11_06_φ1, half_11_06_φ2, half_11_06_φ3, half_11_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_11_06_hx4 : SourcePowerBound (powerBoxCross 8 7 16 half_11_06_φ4) (14319541669/2000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 7) (r := 2) (v := 9) (w := 10) (D := 16)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_11_06_φ4 (by norm_num [half_11_06_φ1, half_11_06_φ2, half_11_06_φ3, half_11_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_06_φ1, half_11_06_φ2, half_11_06_φ3, half_11_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_11_06_hF2 (SeedCompletionHigher8SimpleSeeds.degree8_half_9) (half_10_06)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_11_06_φ1, half_11_06_φ2, half_11_06_φ3, half_11_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_06_hx3 : SourcePowerBound (powerBoxCross 8 8 8 half_11_06_φ3) (17020496151/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 8) (u := 6) (t := 9)
    (D := 8) (ψ := (740812601/10000000000 : ℝ)) half_11_06_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_06_φ1, half_11_06_φ2, half_11_06_φ3, half_11_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_06_φ1, half_11_06_φ2, half_11_06_φ3, half_11_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_06_φ1, half_11_06_φ2, half_11_06_φ3, half_11_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_7) (SeedCompletionHigher8SimpleSeeds.degree8_half_9)
    (by simpa only [half_11_06_φ4, show (2:ℝ)*8=16 by norm_num] using half_11_06_hx4)
  exact h.weaken (by norm_num [half_11_06_φ1, half_11_06_φ2, half_11_06_φ3, half_11_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_06_hx2 : SourcePowerBound (powerBoxCross 8 9 4 half_11_06_φ2) (52048649767/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 9) (u := 7) (t := 10)
    (D := 4) (ψ := (92240381/1000000000 : ℝ)) half_11_06_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_06_φ1, half_11_06_φ2, half_11_06_φ3, half_11_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_06_φ1, half_11_06_φ2, half_11_06_φ3, half_11_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_06_φ1, half_11_06_φ2, half_11_06_φ3, half_11_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_8) (half_10_06)
    (by simpa only [half_11_06_φ3, show (2:ℝ)*4=8 by norm_num] using half_11_06_hx3)
  exact h.weaken (by norm_num [half_11_06_φ1, half_11_06_φ2, half_11_06_φ3, half_11_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_06_hx1 : SourcePowerBound (powerBoxCross 8 10 2 half_11_06_φ1) (128240418787/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 10) (u := 8) (t := 11)
    (D := 2) (ψ := (202489383/2000000000 : ℝ)) half_11_06_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_06_φ1, half_11_06_φ2, half_11_06_φ3, half_11_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_06_φ1, half_11_06_φ2, half_11_06_φ3, half_11_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_06_φ1, half_11_06_φ2, half_11_06_φ3, half_11_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_9) (half_11_05)
    (by simpa only [half_11_06_φ2, show (2:ℝ)*2=4 by norm_num] using half_11_06_hx2)
  exact h.weaken (by norm_num [half_11_06_φ1, half_11_06_φ2, half_11_06_φ3, half_11_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_06 : AdmissibleExponent 8 22 (148677680741/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 9) (ψ := (537822683/5000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_10_06)
    (by simpa only [half_11_06_φ1] using half_11_06_hx1)
  exact admissibleExponent_mono h (by norm_num [half_11_06_φ1, half_11_06_φ2, half_11_06_φ3, half_11_06_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_12_06_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (554546069/5000000000 : ℝ)

def half_12_06_φ2 : Fin 2 → ℝ := Fin.snoc half_12_06_φ1 (13198871/125000000 : ℝ)

def half_12_06_φ3 : Fin 3 → ℝ := Fin.snoc half_12_06_φ2 (39089513/400000000 : ℝ)

def half_12_06_φ4 : Fin 4 → ℝ := Fin.snoc half_12_06_φ3 (84215681/1000000000 : ℝ)

def half_12_06_φ5 : Fin 5 → ℝ := Fin.snoc half_12_06_φ4 (52845337/1000000000 : ℝ)

theorem half_12_06_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_12_06_φ5) (75230153717/10000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_12_06_φ5 (by norm_num [half_12_06_φ1, half_12_06_φ2, half_12_06_φ3, half_12_06_φ4, half_12_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_06_φ1, half_12_06_φ2, half_12_06_φ3, half_12_06_φ4, half_12_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_06_φ1, half_12_06_φ2, half_12_06_φ3, half_12_06_φ4, half_12_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_12_06_φ1, half_12_06_φ2, half_12_06_φ3, half_12_06_φ4, half_12_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_12_06_φ1, half_12_06_φ2, half_12_06_φ3, half_12_06_φ4, half_12_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_12_06_hx5 : SourcePowerBound (powerBoxCross 8 7 32 half_12_06_φ5) (34119591769/5000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 7) (r := 2) (v := 9) (w := 10) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_12_06_φ5 (by norm_num [half_12_06_φ1, half_12_06_φ2, half_12_06_φ3, half_12_06_φ4, half_12_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_06_φ1, half_12_06_φ2, half_12_06_φ3, half_12_06_φ4, half_12_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_12_06_hF2 (SeedCompletionHigher8SimpleSeeds.degree8_half_9) (half_10_06)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_12_06_φ1, half_12_06_φ2, half_12_06_φ3, half_12_06_φ4, half_12_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_06_hx4 : SourcePowerBound (powerBoxCross 8 8 16 half_12_06_φ4) (19514308823/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 8) (u := 6) (t := 9)
    (D := 16) (ψ := (52845337/1000000000 : ℝ)) half_12_06_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_06_φ1, half_12_06_φ2, half_12_06_φ3, half_12_06_φ4, half_12_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_06_φ1, half_12_06_φ2, half_12_06_φ3, half_12_06_φ4, half_12_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_06_φ1, half_12_06_φ2, half_12_06_φ3, half_12_06_φ4, half_12_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_7) (SeedCompletionHigher8SimpleSeeds.degree8_half_9)
    (by simpa only [half_12_06_φ5, show (2:ℝ)*16=32 by norm_num] using half_12_06_hx5)
  exact h.weaken (by norm_num [half_12_06_φ1, half_12_06_φ2, half_12_06_φ3, half_12_06_φ4, half_12_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_06_hx3 : SourcePowerBound (powerBoxCross 8 9 8 half_12_06_φ3) (47181769999/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 9) (u := 7) (t := 10)
    (D := 8) (ψ := (84215681/1000000000 : ℝ)) half_12_06_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_06_φ1, half_12_06_φ2, half_12_06_φ3, half_12_06_φ4, half_12_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_06_φ1, half_12_06_φ2, half_12_06_φ3, half_12_06_φ4, half_12_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_06_φ1, half_12_06_φ2, half_12_06_φ3, half_12_06_φ4, half_12_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_8) (half_10_06)
    (by simpa only [half_12_06_φ4, show (2:ℝ)*8=16 by norm_num] using half_12_06_hx4)
  exact h.weaken (by norm_num [half_12_06_φ1, half_12_06_φ2, half_12_06_φ3, half_12_06_φ4, half_12_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_06_hx2 : SourcePowerBound (powerBoxCross 8 10 4 half_12_06_φ2) (14519406633/1250000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 10) (u := 8) (t := 11)
    (D := 4) (ψ := (39089513/400000000 : ℝ)) half_12_06_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_06_φ1, half_12_06_φ2, half_12_06_φ3, half_12_06_φ4, half_12_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_06_φ1, half_12_06_φ2, half_12_06_φ3, half_12_06_φ4, half_12_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_06_φ1, half_12_06_φ2, half_12_06_φ3, half_12_06_φ4, half_12_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_9) (half_11_06)
    (by simpa only [half_12_06_φ3, show (2:ℝ)*4=8 by norm_num] using half_12_06_hx3)
  exact h.weaken (by norm_num [half_12_06_φ1, half_12_06_φ2, half_12_06_φ3, half_12_06_φ4, half_12_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_06_hx1 : SourcePowerBound (powerBoxCross 8 11 2 half_12_06_φ1) (35824262051/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 11) (u := 9) (t := 12)
    (D := 2) (ψ := (13198871/125000000 : ℝ)) half_12_06_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_06_φ1, half_12_06_φ2, half_12_06_φ3, half_12_06_φ4, half_12_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_06_φ1, half_12_06_φ2, half_12_06_φ3, half_12_06_φ4, half_12_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_06_φ1, half_12_06_φ2, half_12_06_φ3, half_12_06_φ4, half_12_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_10_06) (half_12_05)
    (by simpa only [half_12_06_φ2, show (2:ℝ)*2=4 by norm_num] using half_12_06_hx2)
  exact h.weaken (by norm_num [half_12_06_φ1, half_12_06_φ2, half_12_06_φ3, half_12_06_φ4, half_12_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_06 : AdmissibleExponent 8 24 (83293991551/5000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 10) (ψ := (554546069/5000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_11_06)
    (by simpa only [half_12_06_φ1] using half_12_06_hx1)
  exact admissibleExponent_mono h (by norm_num [half_12_06_φ1, half_12_06_φ2, half_12_06_φ3, half_12_06_φ4, half_12_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_13_06_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (569191737/5000000000 : ℝ)

def half_13_06_φ2 : Fin 2 → ℝ := Fin.snoc half_13_06_φ1 (272631253/2500000000 : ℝ)

def half_13_06_φ3 : Fin 3 → ℝ := Fin.snoc half_13_06_φ2 (51263231/500000000 : ℝ)

def half_13_06_φ4 : Fin 4 → ℝ := Fin.snoc half_13_06_φ3 (91288833/1000000000 : ℝ)

def half_13_06_φ5 : Fin 5 → ℝ := Fin.snoc half_13_06_φ4 (685872361/10000000000 : ℝ)

theorem half_13_06_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_13_06_φ5) (68088390263/10000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_13_06_φ5 (by norm_num [half_13_06_φ1, half_13_06_φ2, half_13_06_φ3, half_13_06_φ4, half_13_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_06_φ1, half_13_06_φ2, half_13_06_φ3, half_13_06_φ4, half_13_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_06_φ1, half_13_06_φ2, half_13_06_φ3, half_13_06_φ4, half_13_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_13_06_φ1, half_13_06_φ2, half_13_06_φ3, half_13_06_φ4, half_13_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_13_06_φ1, half_13_06_φ2, half_13_06_φ3, half_13_06_φ4, half_13_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_13_06_hx5 : SourcePowerBound (powerBoxCross 8 8 32 half_13_06_φ5) (4511144063/625000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 8) (r := 2) (v := 10) (w := 11) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_13_06_φ5 (by norm_num [half_13_06_φ1, half_13_06_φ2, half_13_06_φ3, half_13_06_φ4, half_13_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_06_φ1, half_13_06_φ2, half_13_06_φ3, half_13_06_φ4, half_13_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_13_06_hF2 (half_10_06) (half_11_06)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_13_06_φ1, half_13_06_φ2, half_13_06_φ3, half_13_06_φ4, half_13_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_06_hx4 : SourcePowerBound (powerBoxCross 8 9 16 half_13_06_φ4) (21234449829/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 9) (u := 7) (t := 10)
    (D := 16) (ψ := (685872361/10000000000 : ℝ)) half_13_06_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_06_φ1, half_13_06_φ2, half_13_06_φ3, half_13_06_φ4, half_13_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_06_φ1, half_13_06_φ2, half_13_06_φ3, half_13_06_φ4, half_13_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_06_φ1, half_13_06_φ2, half_13_06_φ3, half_13_06_φ4, half_13_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_8) (half_10_06)
    (by simpa only [half_13_06_φ5, show (2:ℝ)*16=32 by norm_num] using half_13_06_hx5)
  exact h.weaken (by norm_num [half_13_06_φ1, half_13_06_φ2, half_13_06_φ3, half_13_06_φ4, half_13_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_06_hx3 : SourcePowerBound (powerBoxCross 8 10 8 half_13_06_φ3) (103986539457/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 10) (u := 8) (t := 11)
    (D := 8) (ψ := (91288833/1000000000 : ℝ)) half_13_06_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_06_φ1, half_13_06_φ2, half_13_06_φ3, half_13_06_φ4, half_13_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_06_φ1, half_13_06_φ2, half_13_06_φ3, half_13_06_φ4, half_13_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_06_φ1, half_13_06_φ2, half_13_06_φ3, half_13_06_φ4, half_13_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_9) (half_11_06)
    (by simpa only [half_13_06_φ4, show (2:ℝ)*8=16 by norm_num] using half_13_06_hx4)
  exact h.weaken (by norm_num [half_13_06_φ1, half_13_06_φ2, half_13_06_φ3, half_13_06_φ4, half_13_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_06_hx2 : SourcePowerBound (powerBoxCross 8 11 4 half_13_06_φ2) (128660627009/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 11) (u := 9) (t := 12)
    (D := 4) (ψ := (51263231/500000000 : ℝ)) half_13_06_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_06_φ1, half_13_06_φ2, half_13_06_φ3, half_13_06_φ4, half_13_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_06_φ1, half_13_06_φ2, half_13_06_φ3, half_13_06_φ4, half_13_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_06_φ1, half_13_06_φ2, half_13_06_φ3, half_13_06_φ4, half_13_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_10_06) (half_12_06)
    (by simpa only [half_13_06_φ3, show (2:ℝ)*4=8 by norm_num] using half_13_06_hx3)
  exact h.weaken (by norm_num [half_13_06_φ1, half_13_06_φ2, half_13_06_φ3, half_13_06_φ4, half_13_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_06_hx1 : SourcePowerBound (powerBoxCross 8 12 2 half_13_06_φ1) (158762265889/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 12) (u := 10) (t := 13)
    (D := 2) (ψ := (272631253/2500000000 : ℝ)) half_13_06_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_06_φ1, half_13_06_φ2, half_13_06_φ3, half_13_06_φ4, half_13_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_06_φ1, half_13_06_φ2, half_13_06_φ3, half_13_06_φ4, half_13_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_06_φ1, half_13_06_φ2, half_13_06_φ3, half_13_06_φ4, half_13_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_11_06) (half_13_05)
    (by simpa only [half_13_06_φ2, show (2:ℝ)*2=4 by norm_num] using half_13_06_hx2)
  exact h.weaken (by norm_num [half_13_06_φ1, half_13_06_φ2, half_13_06_φ3, half_13_06_φ4, half_13_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_06 : AdmissibleExponent 8 26 (184945085791/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 11) (ψ := (569191737/5000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_12_06)
    (by simpa only [half_13_06_φ1] using half_13_06_hx1)
  exact admissibleExponent_mono h (by norm_num [half_13_06_φ1, half_13_06_φ2, half_13_06_φ3, half_13_06_φ4, half_13_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_14_06_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (291321191/2500000000 : ℝ)

def half_14_06_φ2 : Fin 2 → ℝ := Fin.snoc half_14_06_φ1 (35122389/312500000 : ℝ)

def half_14_06_φ3 : Fin 3 → ℝ := Fin.snoc half_14_06_φ2 (535466633/5000000000 : ℝ)

def half_14_06_φ4 : Fin 4 → ℝ := Fin.snoc half_14_06_φ3 (948552217/10000000000 : ℝ)

def half_14_06_φ5 : Fin 5 → ℝ := Fin.snoc half_14_06_φ4 (813044757/10000000000 : ℝ)

theorem half_14_06_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_14_06_φ5) (15610909877/2500000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_14_06_φ5 (by norm_num [half_14_06_φ1, half_14_06_φ2, half_14_06_φ3, half_14_06_φ4, half_14_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_06_φ1, half_14_06_φ2, half_14_06_φ3, half_14_06_φ4, half_14_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_06_φ1, half_14_06_φ2, half_14_06_φ3, half_14_06_φ4, half_14_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_14_06_φ1, half_14_06_φ2, half_14_06_φ3, half_14_06_φ4, half_14_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_14_06_φ1, half_14_06_φ2, half_14_06_φ3, half_14_06_φ4, half_14_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_14_06_hx5 : SourcePowerBound (powerBoxCross 8 9 32 half_14_06_φ5) (76560478761/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 9) (r := 2) (v := 0) (w := 12) (D := 32)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_14_06_φ5 (by norm_num [half_14_06_φ1, half_14_06_φ2, half_14_06_φ3, half_14_06_φ4, half_14_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_06_φ1, half_14_06_φ2, half_14_06_φ3, half_14_06_φ4, half_14_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_14_06_hF2 (admissibleExponent_zero 8) (half_12_06)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_14_06_φ1, half_14_06_φ2, half_14_06_φ3, half_14_06_φ4, half_14_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_06_hx4 : SourcePowerBound (powerBoxCross 8 10 16 half_14_06_φ4) (92419279511/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 10) (u := 8) (t := 11)
    (D := 16) (ψ := (813044757/10000000000 : ℝ)) half_14_06_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_06_φ1, half_14_06_φ2, half_14_06_φ3, half_14_06_φ4, half_14_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_06_φ1, half_14_06_φ2, half_14_06_φ3, half_14_06_φ4, half_14_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_06_φ1, half_14_06_φ2, half_14_06_φ3, half_14_06_φ4, half_14_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_9) (half_11_06)
    (by simpa only [half_14_06_φ5, show (2:ℝ)*16=32 by norm_num] using half_14_06_hx5)
  exact h.weaken (by norm_num [half_14_06_φ1, half_14_06_φ2, half_14_06_φ3, half_14_06_φ4, half_14_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_06_hx3 : SourcePowerBound (powerBoxCross 8 11 8 half_14_06_φ3) (113766505413/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 11) (u := 9) (t := 12)
    (D := 8) (ψ := (948552217/10000000000 : ℝ)) half_14_06_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_06_φ1, half_14_06_φ2, half_14_06_φ3, half_14_06_φ4, half_14_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_06_φ1, half_14_06_φ2, half_14_06_φ3, half_14_06_φ4, half_14_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_06_φ1, half_14_06_φ2, half_14_06_φ3, half_14_06_φ4, half_14_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_10_06) (half_12_06)
    (by simpa only [half_14_06_φ4, show (2:ℝ)*8=16 by norm_num] using half_14_06_hx4)
  exact h.weaken (by norm_num [half_14_06_φ1, half_14_06_φ2, half_14_06_φ3, half_14_06_φ4, half_14_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_06_hx2 : SourcePowerBound (powerBoxCross 8 12 4 half_14_06_φ2) (70709782463/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 12) (u := 10) (t := 13)
    (D := 4) (ψ := (535466633/5000000000 : ℝ)) half_14_06_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_06_φ1, half_14_06_φ2, half_14_06_φ3, half_14_06_φ4, half_14_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_06_φ1, half_14_06_φ2, half_14_06_φ3, half_14_06_φ4, half_14_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_06_φ1, half_14_06_φ2, half_14_06_φ3, half_14_06_φ4, half_14_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_11_06) (half_13_06)
    (by simpa only [half_14_06_φ3, show (2:ℝ)*4=8 by norm_num] using half_14_06_hx3)
  exact h.weaken (by norm_num [half_14_06_φ1, half_14_06_φ2, half_14_06_φ3, half_14_06_φ4, half_14_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_06_hx1 : SourcePowerBound (powerBoxCross 8 13 2 half_14_06_φ1) (174559001497/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 13) (u := 11) (t := 14)
    (D := 2) (ψ := (35122389/312500000 : ℝ)) half_14_06_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_06_φ1, half_14_06_φ2, half_14_06_φ3, half_14_06_φ4, half_14_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_06_φ1, half_14_06_φ2, half_14_06_φ3, half_14_06_φ4, half_14_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_06_φ1, half_14_06_φ2, half_14_06_φ3, half_14_06_φ4, half_14_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_12_06) (half_14_05)
    (by simpa only [half_14_06_φ2, show (2:ℝ)*2=4 by norm_num] using half_14_06_hx2)
  exact h.weaken (by norm_num [half_14_06_φ1, half_14_06_φ2, half_14_06_φ3, half_14_06_φ4, half_14_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_06 : AdmissibleExponent 8 28 (203691120597/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 12) (ψ := (291321191/2500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_13_06)
    (by simpa only [half_14_06_φ1] using half_14_06_hx1)
  exact admissibleExponent_mono h (by norm_num [half_14_06_φ1, half_14_06_φ2, half_14_06_φ3, half_14_06_φ4, half_14_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_15_06_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1189412261/10000000000 : ℝ)

def half_15_06_φ2 : Fin 2 → ℝ := Fin.snoc half_15_06_φ1 (1157126969/10000000000 : ℝ)

def half_15_06_φ3 : Fin 3 → ℝ := Fin.snoc half_15_06_φ2 (546675769/5000000000 : ℝ)

def half_15_06_φ4 : Fin 4 → ℝ := Fin.snoc half_15_06_φ3 (937158461/10000000000 : ℝ)

def half_15_06_φ5 : Fin 5 → ℝ := Fin.snoc half_15_06_φ4 (803278681/10000000000 : ℝ)

theorem half_15_06_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_15_06_φ5) (6121311389/1000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_15_06_φ5 (by norm_num [half_15_06_φ1, half_15_06_φ2, half_15_06_φ3, half_15_06_φ4, half_15_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_06_φ1, half_15_06_φ2, half_15_06_φ3, half_15_06_φ4, half_15_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_06_φ1, half_15_06_φ2, half_15_06_φ3, half_15_06_φ4, half_15_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_15_06_φ1, half_15_06_φ2, half_15_06_φ3, half_15_06_φ4, half_15_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_15_06_φ1, half_15_06_φ2, half_15_06_φ3, half_15_06_φ4, half_15_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_15_06_hx5 : SourcePowerBound (powerBoxCross 8 10 32 half_15_06_φ5) (16883024421/2000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 10) (r := 2) (v := 13) (w := 14) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_15_06_φ5 (by norm_num [half_15_06_φ1, half_15_06_φ2, half_15_06_φ3, half_15_06_φ4, half_15_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_06_φ1, half_15_06_φ2, half_15_06_φ3, half_15_06_φ4, half_15_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_15_06_hF2 (half_13_06) (half_14_06)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_15_06_φ1, half_15_06_φ2, half_15_06_φ3, half_15_06_φ4, half_15_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_06_hx4 : SourcePowerBound (powerBoxCross 8 11 16 half_15_06_φ4) (50677418811/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 11) (u := 9) (t := 12)
    (D := 16) (ψ := (803278681/10000000000 : ℝ)) half_15_06_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_06_φ1, half_15_06_φ2, half_15_06_φ3, half_15_06_φ4, half_15_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_06_φ1, half_15_06_φ2, half_15_06_φ3, half_15_06_φ4, half_15_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_06_φ1, half_15_06_φ2, half_15_06_φ3, half_15_06_φ4, half_15_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_10_06) (half_12_06)
    (by simpa only [half_15_06_φ5, show (2:ℝ)*16=32 by norm_num] using half_15_06_hx5)
  exact h.weaken (by norm_num [half_15_06_φ1, half_15_06_φ2, half_15_06_φ3, half_15_06_φ4, half_15_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_06_hx3 : SourcePowerBound (powerBoxCross 8 12 8 half_15_06_φ3) (38794051/3125000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 12) (u := 10) (t := 13)
    (D := 8) (ψ := (937158461/10000000000 : ℝ)) half_15_06_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_06_φ1, half_15_06_φ2, half_15_06_φ3, half_15_06_φ4, half_15_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_06_φ1, half_15_06_φ2, half_15_06_φ3, half_15_06_φ4, half_15_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_06_φ1, half_15_06_φ2, half_15_06_φ3, half_15_06_φ4, half_15_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_11_06) (half_13_06)
    (by simpa only [half_15_06_φ4, show (2:ℝ)*8=16 by norm_num] using half_15_06_hx4)
  exact h.weaken (by norm_num [half_15_06_φ1, half_15_06_φ2, half_15_06_φ3, half_15_06_φ4, half_15_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_06_hx2 : SourcePowerBound (powerBoxCross 8 13 4 half_15_06_φ2) (154378237017/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 13) (u := 11) (t := 14)
    (D := 4) (ψ := (546675769/5000000000 : ℝ)) half_15_06_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_06_φ1, half_15_06_φ2, half_15_06_φ3, half_15_06_φ4, half_15_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_06_φ1, half_15_06_φ2, half_15_06_φ3, half_15_06_φ4, half_15_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_06_φ1, half_15_06_φ2, half_15_06_φ3, half_15_06_φ4, half_15_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_12_06) (half_14_06)
    (by simpa only [half_15_06_φ3, show (2:ℝ)*4=8 by norm_num] using half_15_06_hx3)
  exact h.weaken (by norm_num [half_15_06_φ1, half_15_06_φ2, half_15_06_φ3, half_15_06_φ4, half_15_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_06_hx1 : SourcePowerBound (powerBoxCross 8 14 2 half_15_06_φ1) (95326630617/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 14) (u := 12) (t := 15)
    (D := 2) (ψ := (1157126969/10000000000 : ℝ)) half_15_06_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_06_φ1, half_15_06_φ2, half_15_06_φ3, half_15_06_φ4, half_15_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_06_φ1, half_15_06_φ2, half_15_06_φ3, half_15_06_φ4, half_15_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_06_φ1, half_15_06_φ2, half_15_06_φ3, half_15_06_φ4, half_15_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_13_06) (half_15_05)
    (by simpa only [half_15_06_φ2, show (2:ℝ)*2=4 by norm_num] using half_15_06_hx2)
  exact h.weaken (by norm_num [half_15_06_φ1, half_15_06_φ2, half_15_06_φ3, half_15_06_φ4, half_15_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_06 : AdmissibleExponent 8 30 (222767392281/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 13) (ψ := (1189412261/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_14_06)
    (by simpa only [half_15_06_φ1] using half_15_06_hx1)
  exact admissibleExponent_mono h (by norm_num [half_15_06_φ1, half_15_06_φ2, half_15_06_φ3, half_15_06_φ4, half_15_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_16_06_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (301811857/2500000000 : ℝ)

def half_16_06_φ2 : Fin 2 → ℝ := Fin.snoc half_16_06_φ1 (296238877/2500000000 : ℝ)

def half_16_06_φ3 : Fin 3 → ℝ := Fin.snoc half_16_06_φ2 (1086828151/10000000000 : ℝ)

def half_16_06_φ4 : Fin 4 → ℝ := Fin.snoc half_16_06_φ3 (931566987/10000000000 : ℝ)

def half_16_06_φ5 : Fin 5 → ℝ := Fin.snoc half_16_06_φ4 (798485989/10000000000 : ℝ)

theorem half_16_06_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_16_06_φ5) (60609234677/10000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_16_06_φ5 (by norm_num [half_16_06_φ1, half_16_06_φ2, half_16_06_φ3, half_16_06_φ4, half_16_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_06_φ1, half_16_06_φ2, half_16_06_φ3, half_16_06_φ4, half_16_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_06_φ1, half_16_06_φ2, half_16_06_φ3, half_16_06_φ4, half_16_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_16_06_φ1, half_16_06_φ2, half_16_06_φ3, half_16_06_φ4, half_16_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_16_06_φ1, half_16_06_φ2, half_16_06_φ3, half_16_06_φ4, half_16_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_16_06_hx5 : SourcePowerBound (powerBoxCross 8 11 32 half_16_06_φ5) (92911977063/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 11) (r := 2) (v := 14) (w := 15) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_16_06_φ5 (by norm_num [half_16_06_φ1, half_16_06_φ2, half_16_06_φ3, half_16_06_φ4, half_16_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_06_φ1, half_16_06_φ2, half_16_06_φ3, half_16_06_φ4, half_16_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_16_06_hF2 (half_14_06) (half_15_06)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_16_06_φ1, half_16_06_φ2, half_16_06_φ3, half_16_06_φ4, half_16_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_06_hx4 : SourcePowerBound (powerBoxCross 8 12 16 half_16_06_φ4) (55544809547/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 12) (u := 10) (t := 13)
    (D := 16) (ψ := (798485989/10000000000 : ℝ)) half_16_06_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_06_φ1, half_16_06_φ2, half_16_06_φ3, half_16_06_φ4, half_16_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_06_φ1, half_16_06_φ2, half_16_06_φ3, half_16_06_φ4, half_16_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_06_φ1, half_16_06_φ2, half_16_06_φ3, half_16_06_φ4, half_16_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_11_06) (half_13_06)
    (by simpa only [half_16_06_φ5, show (2:ℝ)*16=32 by norm_num] using half_16_06_hx5)
  exact h.weaken (by norm_num [half_16_06_φ1, half_16_06_φ2, half_16_06_φ3, half_16_06_φ4, half_16_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_06_hx3 : SourcePowerBound (powerBoxCross 8 13 8 half_16_06_φ3) (135494394357/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 13) (u := 11) (t := 14)
    (D := 8) (ψ := (931566987/10000000000 : ℝ)) half_16_06_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_06_φ1, half_16_06_φ2, half_16_06_φ3, half_16_06_φ4, half_16_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_06_φ1, half_16_06_φ2, half_16_06_φ3, half_16_06_φ4, half_16_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_06_φ1, half_16_06_φ2, half_16_06_φ3, half_16_06_φ4, half_16_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_12_06) (half_14_06)
    (by simpa only [half_16_06_φ4, show (2:ℝ)*8=16 by norm_num] using half_16_06_hx4)
  exact h.weaken (by norm_num [half_16_06_φ1, half_16_06_φ2, half_16_06_φ3, half_16_06_φ4, half_16_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_06_hx2 : SourcePowerBound (powerBoxCross 8 14 4 half_16_06_φ2) (83849147219/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 14) (u := 12) (t := 15)
    (D := 4) (ψ := (1086828151/10000000000 : ℝ)) half_16_06_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_06_φ1, half_16_06_φ2, half_16_06_φ3, half_16_06_φ4, half_16_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_06_φ1, half_16_06_φ2, half_16_06_φ3, half_16_06_φ4, half_16_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_06_φ1, half_16_06_φ2, half_16_06_φ3, half_16_06_φ4, half_16_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_13_06) (half_15_06)
    (by simpa only [half_16_06_φ3, show (2:ℝ)*4=8 by norm_num] using half_16_06_hx3)
  exact h.weaken (by norm_num [half_16_06_φ1, half_16_06_φ2, half_16_06_φ3, half_16_06_φ4, half_16_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_06_hx1 : SourcePowerBound (powerBoxCross 8 15 2 half_16_06_φ1) (103540551787/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 15) (u := 13) (t := 16)
    (D := 2) (ψ := (296238877/2500000000 : ℝ)) half_16_06_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_06_φ1, half_16_06_φ2, half_16_06_φ3, half_16_06_φ4, half_16_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_06_φ1, half_16_06_φ2, half_16_06_φ3, half_16_06_φ4, half_16_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_06_φ1, half_16_06_φ2, half_16_06_φ3, half_16_06_φ4, half_16_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_14_06) (half_16_05)
    (by simpa only [half_16_06_φ2, show (2:ℝ)*2=4 by norm_num] using half_16_06_hx2)
  exact h.weaken (by norm_num [half_16_06_φ1, half_16_06_φ2, half_16_06_φ3, half_16_06_φ4, half_16_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_06 : AdmissibleExponent 8 32 (121045639493/5000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 14) (ψ := (301811857/2500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_15_06)
    (by simpa only [half_16_06_φ1] using half_16_06_hx1)
  exact admissibleExponent_mono h (by norm_num [half_16_06_φ1, half_16_06_φ2, half_16_06_φ3, half_16_06_φ4, half_16_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_17_06_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (76282187/625000000 : ℝ)

def half_17_06_φ2 : Fin 2 → ℝ := Fin.snoc half_17_06_φ1 (301387571/2500000000 : ℝ)

def half_17_06_φ3 : Fin 3 → ℝ := Fin.snoc half_17_06_φ2 (540995337/5000000000 : ℝ)

def half_17_06_φ4 : Fin 4 → ℝ := Fin.snoc half_17_06_φ3 (463710289/5000000000 : ℝ)

def half_17_06_φ5 : Fin 5 → ℝ := Fin.snoc half_17_06_φ4 (198732981/2500000000 : ℝ)

theorem half_17_06_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_17_06_φ5) (15040355627/2500000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_17_06_φ5 (by norm_num [half_17_06_φ1, half_17_06_φ2, half_17_06_φ3, half_17_06_φ4, half_17_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_06_φ1, half_17_06_φ2, half_17_06_φ3, half_17_06_φ4, half_17_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_06_φ1, half_17_06_φ2, half_17_06_φ3, half_17_06_φ4, half_17_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_17_06_φ1, half_17_06_φ2, half_17_06_φ3, half_17_06_φ4, half_17_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_17_06_φ1, half_17_06_φ2, half_17_06_φ3, half_17_06_φ4, half_17_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_17_06_hx5 : SourcePowerBound (powerBoxCross 8 12 32 half_17_06_φ5) (20328218897/2000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 12) (r := 2) (v := 0) (w := 16) (D := 32)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_17_06_φ5 (by norm_num [half_17_06_φ1, half_17_06_φ2, half_17_06_φ3, half_17_06_φ4, half_17_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_06_φ1, half_17_06_φ2, half_17_06_φ3, half_17_06_φ4, half_17_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_17_06_hF2 (admissibleExponent_zero 8) (half_16_06)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_17_06_φ1, half_17_06_φ2, half_17_06_φ3, half_17_06_φ4, half_17_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_06_hx4 : SourcePowerBound (powerBoxCross 8 13 16 half_17_06_φ4) (121110297601/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 13) (u := 11) (t := 14)
    (D := 16) (ψ := (198732981/2500000000 : ℝ)) half_17_06_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_06_φ1, half_17_06_φ2, half_17_06_φ3, half_17_06_φ4, half_17_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_06_φ1, half_17_06_φ2, half_17_06_φ3, half_17_06_φ4, half_17_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_06_φ1, half_17_06_φ2, half_17_06_φ3, half_17_06_φ4, half_17_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_12_06) (half_14_06)
    (by simpa only [half_17_06_φ5, show (2:ℝ)*16=32 by norm_num] using half_17_06_hx5)
  exact h.weaken (by norm_num [half_17_06_φ1, half_17_06_φ2, half_17_06_φ3, half_17_06_φ4, half_17_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_06_hx3 : SourcePowerBound (powerBoxCross 8 14 8 half_17_06_φ3) (9198711409/625000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 14) (u := 12) (t := 15)
    (D := 8) (ψ := (463710289/5000000000 : ℝ)) half_17_06_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_06_φ1, half_17_06_φ2, half_17_06_φ3, half_17_06_φ4, half_17_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_06_φ1, half_17_06_φ2, half_17_06_φ3, half_17_06_φ4, half_17_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_06_φ1, half_17_06_φ2, half_17_06_φ3, half_17_06_φ4, half_17_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_13_06) (half_15_06)
    (by simpa only [half_17_06_φ4, show (2:ℝ)*8=16 by norm_num] using half_17_06_hx4)
  exact h.weaken (by norm_num [half_17_06_φ1, half_17_06_φ2, half_17_06_φ3, half_17_06_φ4, half_17_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_06_hx2 : SourcePowerBound (powerBoxCross 8 15 4 half_17_06_φ2) (4534612853/250000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 15) (u := 13) (t := 16)
    (D := 4) (ψ := (540995337/5000000000 : ℝ)) half_17_06_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_06_φ1, half_17_06_φ2, half_17_06_φ3, half_17_06_φ4, half_17_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_06_φ1, half_17_06_φ2, half_17_06_φ3, half_17_06_φ4, half_17_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_06_φ1, half_17_06_φ2, half_17_06_φ3, half_17_06_φ4, half_17_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_14_06) (half_16_06)
    (by simpa only [half_17_06_φ3, show (2:ℝ)*4=8 by norm_num] using half_17_06_hx3)
  exact h.weaken (by norm_num [half_17_06_φ1, half_17_06_φ2, half_17_06_φ3, half_17_06_φ4, half_17_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_06_hx1 : SourcePowerBound (powerBoxCross 8 16 2 half_17_06_φ1) (223764190437/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 16) (u := 14) (t := 17)
    (D := 2) (ψ := (301387571/2500000000 : ℝ)) half_17_06_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_06_φ1, half_17_06_φ2, half_17_06_φ3, half_17_06_φ4, half_17_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_06_φ1, half_17_06_φ2, half_17_06_φ3, half_17_06_φ4, half_17_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_06_φ1, half_17_06_φ2, half_17_06_φ3, half_17_06_φ4, half_17_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_15_06) (half_17_05)
    (by simpa only [half_17_06_φ2, show (2:ℝ)*2=4 by norm_num] using half_17_06_hx2)
  exact h.weaken (by norm_num [half_17_06_φ1, half_17_06_φ2, half_17_06_φ3, half_17_06_φ4, half_17_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_06 : AdmissibleExponent 8 34 (261600155189/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 15) (ψ := (76282187/625000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_16_06)
    (by simpa only [half_17_06_φ1] using half_17_06_hx1)
  exact admissibleExponent_mono h (by norm_num [half_17_06_φ1, half_17_06_φ2, half_17_06_φ3, half_17_06_φ4, half_17_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_18_06_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (615433039/5000000000 : ℝ)

def half_18_06_φ2 : Fin 2 → ℝ := Fin.snoc half_18_06_φ1 (1221382279/10000000000 : ℝ)

def half_18_06_φ3 : Fin 3 → ℝ := Fin.snoc half_18_06_φ2 (539125117/5000000000 : ℝ)

def half_18_06_φ4 : Fin 4 → ℝ := Fin.snoc half_18_06_φ3 (462107243/5000000000 : ℝ)

def half_18_06_φ5 : Fin 5 → ℝ := Fin.snoc half_18_06_φ4 (158436769/2000000000 : ℝ)

theorem half_18_06_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_18_06_φ5) (29907582319/5000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_18_06_φ5 (by norm_num [half_18_06_φ1, half_18_06_φ2, half_18_06_φ3, half_18_06_φ4, half_18_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_18_06_φ1, half_18_06_φ2, half_18_06_φ3, half_18_06_φ4, half_18_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_18_06_φ1, half_18_06_φ2, half_18_06_φ3, half_18_06_φ4, half_18_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_18_06_φ1, half_18_06_φ2, half_18_06_φ3, half_18_06_φ4, half_18_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_18_06_φ1, half_18_06_φ2, half_18_06_φ3, half_18_06_φ4, half_18_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_18_06_hx5 : SourcePowerBound (powerBoxCross 8 13 32 half_18_06_φ5) (110552071911/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 13) (r := 2) (v := 17) (w := 18) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_18_06_φ5 (by norm_num [half_18_06_φ1, half_18_06_φ2, half_18_06_φ3, half_18_06_φ4, half_18_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_18_06_φ1, half_18_06_φ2, half_18_06_φ3, half_18_06_φ4, half_18_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_18_06_hF2 (half_17_06) (half_18_05)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_18_06_φ1, half_18_06_φ2, half_18_06_φ3, half_18_06_φ4, half_18_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_18_06_hx4 : SourcePowerBound (powerBoxCross 8 14 16 half_18_06_φ4) (131352293613/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 14) (u := 12) (t := 15)
    (D := 16) (ψ := (158436769/2000000000 : ℝ)) half_18_06_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_18_06_φ1, half_18_06_φ2, half_18_06_φ3, half_18_06_φ4, half_18_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_18_06_φ1, half_18_06_φ2, half_18_06_φ3, half_18_06_φ4, half_18_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_18_06_φ1, half_18_06_φ2, half_18_06_φ3, half_18_06_φ4, half_18_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_13_06) (half_15_06)
    (by simpa only [half_18_06_φ5, show (2:ℝ)*16=32 by norm_num] using half_18_06_hx5)
  exact h.weaken (by norm_num [half_18_06_φ1, half_18_06_φ2, half_18_06_φ3, half_18_06_φ4, half_18_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_18_06_hx3 : SourcePowerBound (powerBoxCross 8 15 8 half_18_06_φ3) (6364271633/400000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 15) (u := 13) (t := 16)
    (D := 8) (ψ := (462107243/5000000000 : ℝ)) half_18_06_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_18_06_φ1, half_18_06_φ2, half_18_06_φ3, half_18_06_φ4, half_18_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_18_06_φ1, half_18_06_φ2, half_18_06_φ3, half_18_06_φ4, half_18_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_18_06_φ1, half_18_06_φ2, half_18_06_φ3, half_18_06_φ4, half_18_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_14_06) (half_16_06)
    (by simpa only [half_18_06_φ4, show (2:ℝ)*8=16 by norm_num] using half_18_06_hx4)
  exact h.weaken (by norm_num [half_18_06_φ1, half_18_06_φ2, half_18_06_φ3, half_18_06_φ4, half_18_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_18_06_hx2 : SourcePowerBound (powerBoxCross 8 16 4 half_18_06_φ2) (195329804613/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 16) (u := 14) (t := 17)
    (D := 4) (ψ := (539125117/5000000000 : ℝ)) half_18_06_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_18_06_φ1, half_18_06_φ2, half_18_06_φ3, half_18_06_φ4, half_18_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_18_06_φ1, half_18_06_φ2, half_18_06_φ3, half_18_06_φ4, half_18_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_18_06_φ1, half_18_06_φ2, half_18_06_φ3, half_18_06_φ4, half_18_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_15_06) (half_17_06)
    (by simpa only [half_18_06_φ3, show (2:ℝ)*4=8 by norm_num] using half_18_06_hx3)
  exact h.weaken (by norm_num [half_18_06_φ1, half_18_06_φ2, half_18_06_φ3, half_18_06_φ4, half_18_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_18_06_hx1 : SourcePowerBound (powerBoxCross 8 17 2 half_18_06_φ1) (240631545569/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 17) (u := 15) (t := 18)
    (D := 2) (ψ := (1221382279/10000000000 : ℝ)) half_18_06_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_18_06_φ1, half_18_06_φ2, half_18_06_φ3, half_18_06_φ4, half_18_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_18_06_φ1, half_18_06_φ2, half_18_06_φ3, half_18_06_φ4, half_18_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_18_06_φ1, half_18_06_φ2, half_18_06_φ3, half_18_06_φ4, half_18_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_16_06) (half_18_05)
    (by simpa only [half_18_06_φ2, show (2:ℝ)*2=4 by norm_num] using half_18_06_hx2)
  exact h.weaken (by norm_num [half_18_06_φ1, half_18_06_φ2, half_18_06_φ3, half_18_06_φ4, half_18_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_18_06 : AdmissibleExponent 8 36 (281250126143/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 16) (ψ := (615433039/5000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_17_06)
    (by simpa only [half_18_06_φ1] using half_18_06_hx1)
  exact admissibleExponent_mono h (by norm_num [half_18_06_φ1, half_18_06_φ2, half_18_06_φ3, half_18_06_φ4, half_18_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_19_06_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (619361981/5000000000 : ℝ)

def half_19_06_φ2 : Fin 2 → ℝ := Fin.snoc half_19_06_φ1 (1233383003/10000000000 : ℝ)

def half_19_06_φ3 : Fin 3 → ℝ := Fin.snoc half_19_06_φ2 (107541329/1000000000 : ℝ)

def half_19_06_φ4 : Fin 4 → ℝ := Fin.snoc half_19_06_φ3 (46089141/500000000 : ℝ)

def half_19_06_φ5 : Fin 5 → ℝ := Fin.snoc half_19_06_φ4 (19752489/250000000 : ℝ)

theorem half_19_06_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_19_06_φ5) (11910508933/2000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_19_06_φ5 (by norm_num [half_19_06_φ1, half_19_06_φ2, half_19_06_φ3, half_19_06_φ4, half_19_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_19_06_φ1, half_19_06_φ2, half_19_06_φ3, half_19_06_φ4, half_19_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_19_06_φ1, half_19_06_φ2, half_19_06_φ3, half_19_06_φ4, half_19_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_19_06_φ1, half_19_06_φ2, half_19_06_φ3, half_19_06_φ4, half_19_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_19_06_φ1, half_19_06_φ2, half_19_06_φ3, half_19_06_φ4, half_19_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_19_06_hx5 : SourcePowerBound (powerBoxCross 8 14 32 half_19_06_φ5) (59791667793/5000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 14) (r := 2) (v := 18) (w := 19) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_19_06_φ5 (by norm_num [half_19_06_φ1, half_19_06_φ2, half_19_06_φ3, half_19_06_φ4, half_19_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_19_06_φ1, half_19_06_φ2, half_19_06_φ3, half_19_06_φ4, half_19_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_19_06_hF2 (half_18_06) (half_19_05)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_19_06_φ1, half_19_06_φ2, half_19_06_φ3, half_19_06_φ4, half_19_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_19_06_hx4 : SourcePowerBound (powerBoxCross 8 15 16 half_19_06_φ4) (17720265713/1250000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 15) (u := 13) (t := 16)
    (D := 16) (ψ := (19752489/250000000 : ℝ)) half_19_06_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_19_06_φ1, half_19_06_φ2, half_19_06_φ3, half_19_06_φ4, half_19_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_19_06_φ1, half_19_06_φ2, half_19_06_φ3, half_19_06_φ4, half_19_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_19_06_φ1, half_19_06_φ2, half_19_06_φ3, half_19_06_φ4, half_19_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_14_06) (half_16_06)
    (by simpa only [half_19_06_φ5, show (2:ℝ)*16=32 by norm_num] using half_19_06_hx5)
  exact h.weaken (by norm_num [half_19_06_φ1, half_19_06_φ2, half_19_06_φ3, half_19_06_φ4, half_19_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_19_06_hx3 : SourcePowerBound (powerBoxCross 8 16 8 half_19_06_φ3) (85614538991/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 16) (u := 14) (t := 17)
    (D := 8) (ψ := (46089141/500000000 : ℝ)) half_19_06_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_19_06_φ1, half_19_06_φ2, half_19_06_φ3, half_19_06_φ4, half_19_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_19_06_φ1, half_19_06_φ2, half_19_06_φ3, half_19_06_φ4, half_19_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_19_06_φ1, half_19_06_φ2, half_19_06_φ3, half_19_06_φ4, half_19_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_15_06) (half_17_06)
    (by simpa only [half_19_06_φ4, show (2:ℝ)*8=16 by norm_num] using half_19_06_hx4)
  exact h.weaken (by norm_num [half_19_06_φ1, half_19_06_φ2, half_19_06_φ3, half_19_06_φ4, half_19_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_19_06_hx2 : SourcePowerBound (powerBoxCross 8 17 4 half_19_06_φ2) (209492113893/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 17) (u := 15) (t := 18)
    (D := 4) (ψ := (107541329/1000000000 : ℝ)) half_19_06_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_19_06_φ1, half_19_06_φ2, half_19_06_φ3, half_19_06_φ4, half_19_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_19_06_φ1, half_19_06_φ2, half_19_06_φ3, half_19_06_φ4, half_19_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_19_06_φ1, half_19_06_φ2, half_19_06_φ3, half_19_06_φ4, half_19_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_16_06) (half_18_06)
    (by simpa only [half_19_06_φ3, show (2:ℝ)*4=8 by norm_num] using half_19_06_hx3)
  exact h.weaken (by norm_num [half_19_06_φ1, half_19_06_φ2, half_19_06_φ3, half_19_06_φ4, half_19_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_19_06_hx1 : SourcePowerBound (powerBoxCross 8 18 2 half_19_06_φ1) (51529944611/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 18) (u := 16) (t := 19)
    (D := 2) (ψ := (1233383003/10000000000 : ℝ)) half_19_06_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_19_06_φ1, half_19_06_φ2, half_19_06_φ3, half_19_06_φ4, half_19_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_19_06_φ1, half_19_06_φ2, half_19_06_φ3, half_19_06_φ4, half_19_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_19_06_φ1, half_19_06_φ2, half_19_06_φ3, half_19_06_φ4, half_19_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_17_06) (half_19_05)
    (by simpa only [half_19_06_φ2, show (2:ℝ)*2=4 by norm_num] using half_19_06_hx2)
  exact h.weaken (by norm_num [half_19_06_φ1, half_19_06_φ2, half_19_06_φ3, half_19_06_φ4, half_19_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_19_06 : AdmissibleExponent 8 38 (12040202469/400000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 17) (ψ := (619361981/5000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_18_06)
    (by simpa only [half_19_06_φ1] using half_19_06_hx1)
  exact admissibleExponent_mono h (by norm_num [half_19_06_φ1, half_19_06_φ2, half_19_06_φ3, half_19_06_φ4, half_19_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_20_06_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1245366911/10000000000 : ℝ)

def half_20_06_φ2 : Fin 2 → ℝ := Fin.snoc half_20_06_φ1 (1242347467/10000000000 : ℝ)

def half_20_06_φ3 : Fin 3 → ℝ := Fin.snoc half_20_06_φ2 (53659183/500000000 : ℝ)

def half_20_06_φ4 : Fin 4 → ℝ := Fin.snoc half_20_06_φ3 (229967927/2500000000 : ℝ)

def half_20_06_φ5 : Fin 5 → ℝ := Fin.snoc half_20_06_φ4 (98557683/1250000000 : ℝ)

theorem half_20_06_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_20_06_φ5) (5934614459/1000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_20_06_φ5 (by norm_num [half_20_06_φ1, half_20_06_φ2, half_20_06_φ3, half_20_06_φ4, half_20_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_20_06_φ1, half_20_06_φ2, half_20_06_φ3, half_20_06_φ4, half_20_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_20_06_φ1, half_20_06_φ2, half_20_06_φ3, half_20_06_φ4, half_20_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_20_06_φ1, half_20_06_φ2, half_20_06_φ3, half_20_06_φ4, half_20_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_20_06_φ1, half_20_06_φ2, half_20_06_φ3, half_20_06_φ4, half_20_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_20_06_hx5 : SourcePowerBound (powerBoxCross 8 15 32 half_20_06_φ5) (128702351807/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 15) (r := 2) (v := 0) (w := 20) (D := 32)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_20_06_φ5 (by norm_num [half_20_06_φ1, half_20_06_φ2, half_20_06_φ3, half_20_06_φ4, half_20_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_20_06_φ1, half_20_06_φ2, half_20_06_φ3, half_20_06_φ4, half_20_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_20_06_hF2 (admissibleExponent_zero 8) (half_20_05)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_20_06_φ1, half_20_06_φ2, half_20_06_φ3, half_20_06_φ4, half_20_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_20_06_hx4 : SourcePowerBound (powerBoxCross 8 16 16 half_20_06_φ4) (15229274757/1000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 16) (u := 14) (t := 17)
    (D := 16) (ψ := (98557683/1250000000 : ℝ)) half_20_06_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_20_06_φ1, half_20_06_φ2, half_20_06_φ3, half_20_06_φ4, half_20_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_20_06_φ1, half_20_06_φ2, half_20_06_φ3, half_20_06_φ4, half_20_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_20_06_φ1, half_20_06_φ2, half_20_06_φ3, half_20_06_φ4, half_20_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_15_06) (half_17_06)
    (by simpa only [half_20_06_φ5, show (2:ℝ)*16=32 by norm_num] using half_20_06_hx5)
  exact h.weaken (by norm_num [half_20_06_φ1, half_20_06_φ2, half_20_06_φ3, half_20_06_φ4, half_20_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_20_06_hx3 : SourcePowerBound (powerBoxCross 8 17 8 half_20_06_φ3) (1146819713/62500000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 17) (u := 15) (t := 18)
    (D := 8) (ψ := (229967927/2500000000 : ℝ)) half_20_06_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_20_06_φ1, half_20_06_φ2, half_20_06_φ3, half_20_06_φ4, half_20_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_20_06_φ1, half_20_06_φ2, half_20_06_φ3, half_20_06_φ4, half_20_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_20_06_φ1, half_20_06_φ2, half_20_06_φ3, half_20_06_φ4, half_20_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_16_06) (half_18_06)
    (by simpa only [half_20_06_φ4, show (2:ℝ)*8=16 by norm_num] using half_20_06_hx4)
  exact h.weaken (by norm_num [half_20_06_φ1, half_20_06_φ2, half_20_06_φ3, half_20_06_φ4, half_20_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_20_06_hx2 : SourcePowerBound (powerBoxCross 8 18 4 half_20_06_φ2) (8952316279/400000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 18) (u := 16) (t := 19)
    (D := 4) (ψ := (53659183/500000000 : ℝ)) half_20_06_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_20_06_φ1, half_20_06_φ2, half_20_06_φ3, half_20_06_φ4, half_20_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_20_06_φ1, half_20_06_φ2, half_20_06_φ3, half_20_06_φ4, half_20_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_20_06_φ1, half_20_06_φ2, half_20_06_φ3, half_20_06_φ4, half_20_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_17_06) (half_19_06)
    (by simpa only [half_20_06_φ3, show (2:ℝ)*4=8 by norm_num] using half_20_06_hx3)
  exact h.weaken (by norm_num [half_20_06_φ1, half_20_06_φ2, half_20_06_φ3, half_20_06_φ4, half_20_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_20_06_hx1 : SourcePowerBound (powerBoxCross 8 19 2 half_20_06_φ1) (1099057017/40000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 19) (u := 17) (t := 20)
    (D := 2) (ψ := (1242347467/10000000000 : ℝ)) half_20_06_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_20_06_φ1, half_20_06_φ2, half_20_06_φ3, half_20_06_φ4, half_20_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_20_06_φ1, half_20_06_φ2, half_20_06_φ3, half_20_06_φ4, half_20_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_20_06_φ1, half_20_06_φ2, half_20_06_φ3, half_20_06_φ4, half_20_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_18_06) (half_20_05)
    (by simpa only [half_20_06_φ2, show (2:ℝ)*2=4 by norm_num] using half_20_06_hx2)
  exact h.weaken (by norm_num [half_20_06_φ1, half_20_06_φ2, half_20_06_φ3, half_20_06_φ4, half_20_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_20_06 : AdmissibleExponent 8 40 (320842829957/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 18) (ψ := (1245366911/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_19_06)
    (by simpa only [half_20_06_φ1] using half_20_06_hx1)
  exact admissibleExponent_mono h (by norm_num [half_20_06_φ1, half_20_06_φ2, half_20_06_φ3, half_20_06_φ4, half_20_06_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_10_07_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (206358701/2000000000 : ℝ)

def half_10_07_φ2 : Fin 2 → ℝ := Fin.snoc half_10_07_φ1 (480703701/5000000000 : ℝ)

def half_10_07_φ3 : Fin 3 → ℝ := Fin.snoc half_10_07_φ2 (104573987/1250000000 : ℝ)

def half_10_07_φ4 : Fin 4 → ℝ := Fin.snoc half_10_07_φ3 (17157483/312500000 : ℝ)

theorem half_10_07_hF2 : SourcePowerBound (paddedMoment 8 0 2 16 half_10_07_φ4) (69044522561/10000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 4) (r := 0) (n := 1) (D := 16)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_10_07_φ4 (by norm_num [half_10_07_φ1, half_10_07_φ2, half_10_07_φ3, half_10_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_07_φ1, half_10_07_φ2, half_10_07_φ3, half_10_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_07_φ1, half_10_07_φ2, half_10_07_φ3, half_10_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_10_07_φ1, half_10_07_φ2, half_10_07_φ3, half_10_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_10_07_φ1, half_10_07_φ2, half_10_07_φ3, half_10_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_10_07_hx4 : SourcePowerBound (powerBoxCross 8 6 16 half_10_07_φ4) (52911649/8000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 6) (r := 2) (v := 0) (w := 8) (D := 16)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_10_07_φ4 (by norm_num [half_10_07_φ1, half_10_07_φ2, half_10_07_φ3, half_10_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_07_φ1, half_10_07_φ2, half_10_07_φ3, half_10_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_10_07_hF2 (admissibleExponent_zero 8) (SeedCompletionHigher8SimpleSeeds.degree8_half_8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_10_07_φ1, half_10_07_φ2, half_10_07_φ3, half_10_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_07_hx3 : SourcePowerBound (powerBoxCross 8 7 8 half_10_07_φ3) (76472903047/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 7) (u := 5) (t := 8)
    (D := 8) (ψ := (17157483/312500000 : ℝ)) half_10_07_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_07_φ1, half_10_07_φ2, half_10_07_φ3, half_10_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_07_φ1, half_10_07_φ2, half_10_07_φ3, half_10_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_07_φ1, half_10_07_φ2, half_10_07_φ3, half_10_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionEven8SecondSeeds.degree8_half_6) (SeedCompletionHigher8SimpleSeeds.degree8_half_8)
    (by simpa only [half_10_07_φ4, show (2:ℝ)*8=16 by norm_num] using half_10_07_hx4)
  exact h.weaken (by norm_num [half_10_07_φ1, half_10_07_φ2, half_10_07_φ3, half_10_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_07_hx2 : SourcePowerBound (powerBoxCross 8 8 4 half_10_07_φ2) (46274335981/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 8) (u := 6) (t := 9)
    (D := 4) (ψ := (104573987/1250000000 : ℝ)) half_10_07_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_07_φ1, half_10_07_φ2, half_10_07_φ3, half_10_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_07_φ1, half_10_07_φ2, half_10_07_φ3, half_10_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_07_φ1, half_10_07_φ2, half_10_07_φ3, half_10_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_7) (SeedCompletionHigher8SimpleSeeds.degree8_half_9)
    (by simpa only [half_10_07_φ3, show (2:ℝ)*4=8 by norm_num] using half_10_07_hx3)
  exact h.weaken (by norm_num [half_10_07_φ1, half_10_07_φ2, half_10_07_φ3, half_10_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_07_hx1 : SourcePowerBound (powerBoxCross 8 9 2 half_10_07_φ1) (28435964729/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 9) (u := 7) (t := 10)
    (D := 2) (ψ := (480703701/5000000000 : ℝ)) half_10_07_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_07_φ1, half_10_07_φ2, half_10_07_φ3, half_10_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_07_φ1, half_10_07_φ2, half_10_07_φ3, half_10_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_07_φ1, half_10_07_φ2, half_10_07_φ3, half_10_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_8) (half_10_06)
    (by simpa only [half_10_07_φ2, show (2:ℝ)*2=4 by norm_num] using half_10_07_hx2)
  exact h.weaken (by norm_num [half_10_07_φ1, half_10_07_φ2, half_10_07_φ3, half_10_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_07 : AdmissibleExponent 8 20 (131284348501/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 8) (ψ := (206358701/2000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_9)
    (by simpa only [half_10_07_φ1] using half_10_07_hx1)
  exact admissibleExponent_mono h (by norm_num [half_10_07_φ1, half_10_07_φ2, half_10_07_φ3, half_10_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_11_07_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (537413367/5000000000 : ℝ)

def half_11_07_φ2 : Fin 2 → ℝ := Fin.snoc half_11_07_φ1 (1012315977/10000000000 : ℝ)

def half_11_07_φ3 : Fin 3 → ℝ := Fin.snoc half_11_07_φ2 (461168197/5000000000 : ℝ)

def half_11_07_φ4 : Fin 4 → ℝ := Fin.snoc half_11_07_φ3 (370304553/5000000000 : ℝ)

theorem half_11_07_hF2 : SourcePowerBound (paddedMoment 8 0 2 16 half_11_07_φ4) (61248147569/10000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 4) (r := 0) (n := 1) (D := 16)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_11_07_φ4 (by norm_num [half_11_07_φ1, half_11_07_φ2, half_11_07_φ3, half_11_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_07_φ1, half_11_07_φ2, half_11_07_φ3, half_11_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_07_φ1, half_11_07_φ2, half_11_07_φ3, half_11_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_11_07_φ1, half_11_07_φ2, half_11_07_φ3, half_11_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_11_07_φ1, half_11_07_φ2, half_11_07_φ3, half_11_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_11_07_hx4 : SourcePowerBound (powerBoxCross 8 7 16 half_11_07_φ4) (71614766681/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 7) (r := 2) (v := 9) (w := 10) (D := 16)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_11_07_φ4 (by norm_num [half_11_07_φ1, half_11_07_φ2, half_11_07_φ3, half_11_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_07_φ1, half_11_07_φ2, half_11_07_φ3, half_11_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_11_07_hF2 (SeedCompletionHigher8SimpleSeeds.degree8_half_9) (half_10_07)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_11_07_φ1, half_11_07_φ2, half_11_07_φ3, half_11_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_07_hx3 : SourcePowerBound (powerBoxCross 8 8 8 half_11_07_φ3) (85119070381/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 8) (u := 6) (t := 9)
    (D := 8) (ψ := (370304553/5000000000 : ℝ)) half_11_07_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_07_φ1, half_11_07_φ2, half_11_07_φ3, half_11_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_07_φ1, half_11_07_φ2, half_11_07_φ3, half_11_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_07_φ1, half_11_07_φ2, half_11_07_φ3, half_11_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_7) (SeedCompletionHigher8SimpleSeeds.degree8_half_9)
    (by simpa only [half_11_07_φ4, show (2:ℝ)*8=16 by norm_num] using half_11_07_hx4)
  exact h.weaken (by norm_num [half_11_07_φ1, half_11_07_φ2, half_11_07_φ3, half_11_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_07_hx2 : SourcePowerBound (powerBoxCross 8 9 4 half_11_07_φ2) (26028443589/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 9) (u := 7) (t := 10)
    (D := 4) (ψ := (461168197/5000000000 : ℝ)) half_11_07_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_07_φ1, half_11_07_φ2, half_11_07_φ3, half_11_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_07_φ1, half_11_07_φ2, half_11_07_φ3, half_11_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_07_φ1, half_11_07_φ2, half_11_07_φ3, half_11_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_8) (half_10_07)
    (by simpa only [half_11_07_φ3, show (2:ℝ)*4=8 by norm_num] using half_11_07_hx3)
  exact h.weaken (by norm_num [half_11_07_φ1, half_11_07_φ2, half_11_07_φ3, half_11_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_07_hx1 : SourcePowerBound (powerBoxCross 8 10 2 half_11_07_φ1) (32062095621/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 10) (u := 8) (t := 11)
    (D := 2) (ψ := (1012315977/10000000000 : ℝ)) half_11_07_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_07_φ1, half_11_07_φ2, half_11_07_φ3, half_11_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_07_φ1, half_11_07_φ2, half_11_07_φ3, half_11_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_07_φ1, half_11_07_φ2, half_11_07_φ3, half_11_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_9) (half_11_06)
    (by simpa only [half_11_07_φ2, show (2:ℝ)*2=4 by norm_num] using half_11_07_hx2)
  exact h.weaken (by norm_num [half_11_07_φ1, half_11_07_φ2, half_11_07_φ3, half_11_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_07 : AdmissibleExponent 8 22 (14867009043/1000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 9) (ψ := (537413367/5000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_10_07)
    (by simpa only [half_11_07_φ1] using half_11_07_hx1)
  exact admissibleExponent_mono h (by norm_num [half_11_07_φ1, half_11_07_φ2, half_11_07_φ3, half_11_07_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_12_07_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (553986211/5000000000 : ℝ)

def half_12_07_φ2 : Fin 2 → ℝ := Fin.snoc half_12_07_φ1 (1055708371/10000000000 : ℝ)

def half_12_07_φ3 : Fin 3 → ℝ := Fin.snoc half_12_07_φ2 (12213931/125000000 : ℝ)

def half_12_07_φ4 : Fin 4 → ℝ := Fin.snoc half_12_07_φ3 (842066167/10000000000 : ℝ)

def half_12_07_φ5 : Fin 5 → ℝ := Fin.snoc half_12_07_φ4 (528177471/10000000000 : ℝ)

theorem half_12_07_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_12_07_φ5) (75268182869/10000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_12_07_φ5 (by norm_num [half_12_07_φ1, half_12_07_φ2, half_12_07_φ3, half_12_07_φ4, half_12_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_07_φ1, half_12_07_φ2, half_12_07_φ3, half_12_07_φ4, half_12_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_07_φ1, half_12_07_φ2, half_12_07_φ3, half_12_07_φ4, half_12_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_12_07_φ1, half_12_07_φ2, half_12_07_φ3, half_12_07_φ4, half_12_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_12_07_φ1, half_12_07_φ2, half_12_07_φ3, half_12_07_φ4, half_12_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_12_07_hx5 : SourcePowerBound (powerBoxCross 8 7 32 half_12_07_φ5) (17066175623/2500000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 7) (r := 2) (v := 9) (w := 10) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_12_07_φ5 (by norm_num [half_12_07_φ1, half_12_07_φ2, half_12_07_φ3, half_12_07_φ4, half_12_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_07_φ1, half_12_07_φ2, half_12_07_φ3, half_12_07_φ4, half_12_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_12_07_hF2 (SeedCompletionHigher8SimpleSeeds.degree8_half_9) (half_10_07)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_12_07_φ1, half_12_07_φ2, half_12_07_φ3, half_12_07_φ4, half_12_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_07_hx4 : SourcePowerBound (powerBoxCross 8 8 16 half_12_07_φ4) (39041182077/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 8) (u := 6) (t := 9)
    (D := 16) (ψ := (528177471/10000000000 : ℝ)) half_12_07_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_07_φ1, half_12_07_φ2, half_12_07_φ3, half_12_07_φ4, half_12_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_07_φ1, half_12_07_φ2, half_12_07_φ3, half_12_07_φ4, half_12_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_07_φ1, half_12_07_φ2, half_12_07_φ3, half_12_07_φ4, half_12_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_7) (SeedCompletionHigher8SimpleSeeds.degree8_half_9)
    (by simpa only [half_12_07_φ5, show (2:ℝ)*16=32 by norm_num] using half_12_07_hx5)
  exact h.weaken (by norm_num [half_12_07_φ1, half_12_07_φ2, half_12_07_φ3, half_12_07_φ4, half_12_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_07_hx3 : SourcePowerBound (powerBoxCross 8 9 8 half_12_07_φ3) (18877841213/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 9) (u := 7) (t := 10)
    (D := 8) (ψ := (842066167/10000000000 : ℝ)) half_12_07_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_07_φ1, half_12_07_φ2, half_12_07_φ3, half_12_07_φ4, half_12_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_07_φ1, half_12_07_φ2, half_12_07_φ3, half_12_07_φ4, half_12_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_07_φ1, half_12_07_φ2, half_12_07_φ3, half_12_07_φ4, half_12_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_8) (half_10_07)
    (by simpa only [half_12_07_φ4, show (2:ℝ)*8=16 by norm_num] using half_12_07_hx4)
  exact h.weaken (by norm_num [half_12_07_φ1, half_12_07_φ2, half_12_07_φ3, half_12_07_φ4, half_12_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_07_hx2 : SourcePowerBound (powerBoxCross 8 10 4 half_12_07_φ2) (23235701519/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 10) (u := 8) (t := 11)
    (D := 4) (ψ := (12213931/125000000 : ℝ)) half_12_07_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_07_φ1, half_12_07_φ2, half_12_07_φ3, half_12_07_φ4, half_12_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_07_φ1, half_12_07_φ2, half_12_07_φ3, half_12_07_φ4, half_12_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_07_φ1, half_12_07_φ2, half_12_07_φ3, half_12_07_φ4, half_12_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_9) (half_11_07)
    (by simpa only [half_12_07_φ3, show (2:ℝ)*4=8 by norm_num] using half_12_07_hx3)
  exact h.weaken (by norm_num [half_12_07_φ1, half_12_07_φ2, half_12_07_φ3, half_12_07_φ4, half_12_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_07_hx1 : SourcePowerBound (powerBoxCross 8 11 2 half_12_07_φ1) (143305826841/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 11) (u := 9) (t := 12)
    (D := 2) (ψ := (1055708371/10000000000 : ℝ)) half_12_07_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_07_φ1, half_12_07_φ2, half_12_07_φ3, half_12_07_φ4, half_12_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_07_φ1, half_12_07_φ2, half_12_07_φ3, half_12_07_φ4, half_12_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_07_φ1, half_12_07_φ2, half_12_07_φ3, half_12_07_φ4, half_12_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_10_07) (half_12_06)
    (by simpa only [half_12_07_φ2, show (2:ℝ)*2=4 by norm_num] using half_12_07_hx2)
  exact h.weaken (by norm_num [half_12_07_φ1, half_12_07_φ2, half_12_07_φ3, half_12_07_φ4, half_12_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_07 : AdmissibleExponent 8 24 (166573247703/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 10) (ψ := (553986211/5000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_11_07)
    (by simpa only [half_12_07_φ1] using half_12_07_hx1)
  exact admissibleExponent_mono h (by norm_num [half_12_07_φ1, half_12_07_φ2, half_12_07_φ3, half_12_07_φ4, half_12_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_13_07_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (568527121/5000000000 : ℝ)

def half_13_07_φ2 : Fin 2 → ℝ := Fin.snoc half_13_07_φ1 (545176537/5000000000 : ℝ)

def half_13_07_φ3 : Fin 3 → ℝ := Fin.snoc half_13_07_φ2 (512509389/5000000000 : ℝ)

def half_13_07_φ4 : Fin 4 → ℝ := Fin.snoc half_13_07_φ3 (456299519/5000000000 : ℝ)

def half_13_07_φ5 : Fin 5 → ℝ := Fin.snoc half_13_07_φ4 (342653771/5000000000 : ℝ)

theorem half_13_07_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_13_07_φ5) (34071506923/5000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_13_07_φ5 (by norm_num [half_13_07_φ1, half_13_07_φ2, half_13_07_φ3, half_13_07_φ4, half_13_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_07_φ1, half_13_07_φ2, half_13_07_φ3, half_13_07_φ4, half_13_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_07_φ1, half_13_07_φ2, half_13_07_φ3, half_13_07_φ4, half_13_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_13_07_φ1, half_13_07_φ2, half_13_07_φ3, half_13_07_φ4, half_13_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_13_07_φ1, half_13_07_φ2, half_13_07_φ3, half_13_07_φ4, half_13_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_13_07_hx5 : SourcePowerBound (powerBoxCross 8 8 32 half_13_07_φ5) (72217596811/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 8) (r := 2) (v := 10) (w := 11) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_13_07_φ5 (by norm_num [half_13_07_φ1, half_13_07_φ2, half_13_07_φ3, half_13_07_φ4, half_13_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_07_φ1, half_13_07_φ2, half_13_07_φ3, half_13_07_φ4, half_13_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_13_07_hF2 (half_10_07) (half_11_07)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_13_07_φ1, half_13_07_φ2, half_13_07_φ3, half_13_07_φ4, half_13_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_07_hx4 : SourcePowerBound (powerBoxCross 8 9 16 half_13_07_φ4) (10621632589/1250000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 9) (u := 7) (t := 10)
    (D := 16) (ψ := (342653771/5000000000 : ℝ)) half_13_07_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_07_φ1, half_13_07_φ2, half_13_07_φ3, half_13_07_φ4, half_13_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_07_φ1, half_13_07_φ2, half_13_07_φ3, half_13_07_φ4, half_13_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_07_φ1, half_13_07_φ2, half_13_07_φ3, half_13_07_φ4, half_13_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_8) (half_10_07)
    (by simpa only [half_13_07_φ5, show (2:ℝ)*16=32 by norm_num] using half_13_07_hx5)
  exact h.weaken (by norm_num [half_13_07_φ1, half_13_07_φ2, half_13_07_φ3, half_13_07_φ4, half_13_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_07_hx3 : SourcePowerBound (powerBoxCross 8 10 8 half_13_07_φ3) (10401825199/1000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 10) (u := 8) (t := 11)
    (D := 8) (ψ := (456299519/5000000000 : ℝ)) half_13_07_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_07_φ1, half_13_07_φ2, half_13_07_φ3, half_13_07_φ4, half_13_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_07_φ1, half_13_07_φ2, half_13_07_φ3, half_13_07_φ4, half_13_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_07_φ1, half_13_07_φ2, half_13_07_φ3, half_13_07_φ4, half_13_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_9) (half_11_07)
    (by simpa only [half_13_07_φ4, show (2:ℝ)*8=16 by norm_num] using half_13_07_hx4)
  exact h.weaken (by norm_num [half_13_07_φ1, half_13_07_φ2, half_13_07_φ3, half_13_07_φ4, half_13_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_07_hx2 : SourcePowerBound (powerBoxCross 8 11 4 half_13_07_φ2) (128686179103/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 11) (u := 9) (t := 12)
    (D := 4) (ψ := (512509389/5000000000 : ℝ)) half_13_07_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_07_φ1, half_13_07_φ2, half_13_07_φ3, half_13_07_φ4, half_13_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_07_φ1, half_13_07_φ2, half_13_07_φ3, half_13_07_φ4, half_13_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_07_φ1, half_13_07_φ2, half_13_07_φ3, half_13_07_φ4, half_13_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_10_07) (half_12_07)
    (by simpa only [half_13_07_φ3, show (2:ℝ)*4=8 by norm_num] using half_13_07_hx3)
  exact h.weaken (by norm_num [half_13_07_φ1, half_13_07_φ2, half_13_07_φ3, half_13_07_φ4, half_13_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_07_hx1 : SourcePowerBound (powerBoxCross 8 12 2 half_13_07_φ1) (158770020161/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 12) (u := 10) (t := 13)
    (D := 2) (ψ := (545176537/5000000000 : ℝ)) half_13_07_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_07_φ1, half_13_07_φ2, half_13_07_φ3, half_13_07_φ4, half_13_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_07_φ1, half_13_07_φ2, half_13_07_φ3, half_13_07_φ4, half_13_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_07_φ1, half_13_07_φ2, half_13_07_φ3, half_13_07_φ4, half_13_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_11_07) (half_13_06)
    (by simpa only [half_13_07_φ2, show (2:ℝ)*2=4 by norm_num] using half_13_07_hx2)
  exact h.weaken (by norm_num [half_13_07_φ1, half_13_07_φ2, half_13_07_φ3, half_13_07_φ4, half_13_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_07 : AdmissibleExponent 8 26 (184922267727/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 11) (ψ := (568527121/5000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_12_07)
    (by simpa only [half_13_07_φ1] using half_13_07_hx1)
  exact admissibleExponent_mono h (by norm_num [half_13_07_φ1, half_13_07_φ2, half_13_07_φ3, half_13_07_φ4, half_13_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_14_07_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (581953039/5000000000 : ℝ)

def half_14_07_φ2 : Fin 2 → ℝ := Fin.snoc half_14_07_φ1 (1123776927/10000000000 : ℝ)

def half_14_07_φ3 : Fin 3 → ℝ := Fin.snoc half_14_07_φ2 (1070598211/10000000000 : ℝ)

def half_14_07_φ4 : Fin 4 → ℝ := Fin.snoc half_14_07_φ3 (118602121/1250000000 : ℝ)

def half_14_07_φ5 : Fin 5 → ℝ := Fin.snoc half_14_07_φ4 (813271687/10000000000 : ℝ)

theorem half_14_07_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_14_07_φ5) (62472232709/10000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_14_07_φ5 (by norm_num [half_14_07_φ1, half_14_07_φ2, half_14_07_φ3, half_14_07_φ4, half_14_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_07_φ1, half_14_07_φ2, half_14_07_φ3, half_14_07_φ4, half_14_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_07_φ1, half_14_07_φ2, half_14_07_φ3, half_14_07_φ4, half_14_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_14_07_φ1, half_14_07_φ2, half_14_07_φ3, half_14_07_φ4, half_14_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_14_07_φ1, half_14_07_φ2, half_14_07_φ3, half_14_07_φ4, half_14_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_14_07_hx5 : SourcePowerBound (powerBoxCross 8 9 32 half_14_07_φ5) (76579246041/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 9) (r := 2) (v := 0) (w := 12) (D := 32)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_14_07_φ5 (by norm_num [half_14_07_φ1, half_14_07_φ2, half_14_07_φ3, half_14_07_φ4, half_14_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_07_φ1, half_14_07_φ2, half_14_07_φ3, half_14_07_φ4, half_14_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_14_07_hF2 (admissibleExponent_zero 8) (half_12_07)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_14_07_φ1, half_14_07_φ2, half_14_07_φ3, half_14_07_φ4, half_14_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_07_hx4 : SourcePowerBound (powerBoxCross 8 10 16 half_14_07_φ4) (46222900053/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 10) (u := 8) (t := 11)
    (D := 16) (ψ := (813271687/10000000000 : ℝ)) half_14_07_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_07_φ1, half_14_07_φ2, half_14_07_φ3, half_14_07_φ4, half_14_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_07_φ1, half_14_07_φ2, half_14_07_φ3, half_14_07_φ4, half_14_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_07_φ1, half_14_07_φ2, half_14_07_φ3, half_14_07_φ4, half_14_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_9) (half_11_07)
    (by simpa only [half_14_07_φ5, show (2:ℝ)*16=32 by norm_num] using half_14_07_hx5)
  exact h.weaken (by norm_num [half_14_07_φ1, half_14_07_φ2, half_14_07_φ3, half_14_07_φ4, half_14_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_07_hx3 : SourcePowerBound (powerBoxCross 8 11 8 half_14_07_φ3) (113799310403/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 11) (u := 9) (t := 12)
    (D := 8) (ψ := (118602121/1250000000 : ℝ)) half_14_07_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_07_φ1, half_14_07_φ2, half_14_07_φ3, half_14_07_φ4, half_14_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_07_φ1, half_14_07_φ2, half_14_07_φ3, half_14_07_φ4, half_14_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_07_φ1, half_14_07_φ2, half_14_07_φ3, half_14_07_φ4, half_14_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_10_07) (half_12_07)
    (by simpa only [half_14_07_φ4, show (2:ℝ)*8=16 by norm_num] using half_14_07_hx4)
  exact h.weaken (by norm_num [half_14_07_φ1, half_14_07_φ2, half_14_07_φ3, half_14_07_φ4, half_14_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_07_hx2 : SourcePowerBound (powerBoxCross 8 12 4 half_14_07_φ2) (141443003307/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 12) (u := 10) (t := 13)
    (D := 4) (ψ := (1070598211/10000000000 : ℝ)) half_14_07_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_07_φ1, half_14_07_φ2, half_14_07_φ3, half_14_07_φ4, half_14_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_07_φ1, half_14_07_φ2, half_14_07_φ3, half_14_07_φ4, half_14_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_07_φ1, half_14_07_φ2, half_14_07_φ3, half_14_07_φ4, half_14_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_11_07) (half_13_07)
    (by simpa only [half_14_07_φ3, show (2:ℝ)*4=8 by norm_num] using half_14_07_hx3)
  exact h.weaken (by norm_num [half_14_07_φ1, half_14_07_φ2, half_14_07_φ3, half_14_07_φ4, half_14_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_07_hx1 : SourcePowerBound (powerBoxCross 8 13 2 half_14_07_φ1) (6982518347/400000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 13) (u := 11) (t := 14)
    (D := 2) (ψ := (1123776927/10000000000 : ℝ)) half_14_07_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_07_φ1, half_14_07_φ2, half_14_07_φ3, half_14_07_φ4, half_14_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_07_φ1, half_14_07_φ2, half_14_07_φ3, half_14_07_φ4, half_14_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_07_φ1, half_14_07_φ2, half_14_07_φ3, half_14_07_φ4, half_14_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_12_07) (half_14_06)
    (by simpa only [half_14_07_φ2, show (2:ℝ)*2=4 by norm_num] using half_14_07_hx2)
  exact h.weaken (by norm_num [half_14_07_φ1, half_14_07_φ2, half_14_07_φ3, half_14_07_φ4, half_14_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_07 : AdmissibleExponent 8 28 (325856977/16000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 12) (ψ := (581953039/5000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_13_07)
    (by simpa only [half_14_07_φ1] using half_14_07_hx1)
  exact admissibleExponent_mono h (by norm_num [half_14_07_φ1, half_14_07_φ2, half_14_07_φ3, half_14_07_φ4, half_14_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_15_07_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1188241789/10000000000 : ℝ)

def half_15_07_φ2 : Fin 2 → ℝ := Fin.snoc half_15_07_φ1 (46283813/400000000 : ℝ)

def half_15_07_φ3 : Fin 3 → ℝ := Fin.snoc half_15_07_φ2 (1093523269/10000000000 : ℝ)

def half_15_07_φ4 : Fin 4 → ℝ := Fin.snoc half_15_07_φ3 (937305659/10000000000 : ℝ)

def half_15_07_φ5 : Fin 5 → ℝ := Fin.snoc half_15_07_φ4 (16068097/200000000 : ℝ)

theorem half_15_07_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_15_07_φ5) (15307252817/2500000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_15_07_φ5 (by norm_num [half_15_07_φ1, half_15_07_φ2, half_15_07_φ3, half_15_07_φ4, half_15_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_07_φ1, half_15_07_φ2, half_15_07_φ3, half_15_07_φ4, half_15_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_07_φ1, half_15_07_φ2, half_15_07_φ3, half_15_07_φ4, half_15_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_15_07_φ1, half_15_07_φ2, half_15_07_φ3, half_15_07_φ4, half_15_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_15_07_φ1, half_15_07_φ2, half_15_07_φ3, half_15_07_φ4, half_15_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_15_07_hx5 : SourcePowerBound (powerBoxCross 8 10 32 half_15_07_φ5) (84420775311/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 10) (r := 2) (v := 13) (w := 14) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_15_07_φ5 (by norm_num [half_15_07_φ1, half_15_07_φ2, half_15_07_φ3, half_15_07_φ4, half_15_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_07_φ1, half_15_07_φ2, half_15_07_φ3, half_15_07_φ4, half_15_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_15_07_hF2 (half_13_07) (half_14_07)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_15_07_φ1, half_15_07_φ2, half_15_07_φ3, half_15_07_φ4, half_15_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_07_hx4 : SourcePowerBound (powerBoxCross 8 11 16 half_15_07_φ4) (10136516693/1000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 11) (u := 9) (t := 12)
    (D := 16) (ψ := (16068097/200000000 : ℝ)) half_15_07_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_07_φ1, half_15_07_φ2, half_15_07_φ3, half_15_07_φ4, half_15_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_07_φ1, half_15_07_φ2, half_15_07_φ3, half_15_07_φ4, half_15_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_07_φ1, half_15_07_φ2, half_15_07_φ3, half_15_07_φ4, half_15_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_10_07) (half_12_07)
    (by simpa only [half_15_07_φ5, show (2:ℝ)*16=32 by norm_num] using half_15_07_hx5)
  exact h.weaken (by norm_num [half_15_07_φ1, half_15_07_φ2, half_15_07_φ3, half_15_07_φ4, half_15_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_07_hx3 : SourcePowerBound (powerBoxCross 8 12 8 half_15_07_φ3) (124153322387/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 12) (u := 10) (t := 13)
    (D := 8) (ψ := (937305659/10000000000 : ℝ)) half_15_07_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_07_φ1, half_15_07_φ2, half_15_07_φ3, half_15_07_φ4, half_15_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_07_φ1, half_15_07_φ2, half_15_07_φ3, half_15_07_φ4, half_15_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_07_φ1, half_15_07_φ2, half_15_07_φ3, half_15_07_φ4, half_15_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_11_07) (half_13_07)
    (by simpa only [half_15_07_φ4, show (2:ℝ)*8=16 by norm_num] using half_15_07_hx4)
  exact h.weaken (by norm_num [half_15_07_φ1, half_15_07_φ2, half_15_07_φ3, half_15_07_φ4, half_15_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_07_hx2 : SourcePowerBound (powerBoxCross 8 13 4 half_15_07_φ2) (154391164763/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 13) (u := 11) (t := 14)
    (D := 4) (ψ := (1093523269/10000000000 : ℝ)) half_15_07_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_07_φ1, half_15_07_φ2, half_15_07_φ3, half_15_07_φ4, half_15_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_07_φ1, half_15_07_φ2, half_15_07_φ3, half_15_07_φ4, half_15_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_07_φ1, half_15_07_φ2, half_15_07_φ3, half_15_07_φ4, half_15_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_12_07) (half_14_07)
    (by simpa only [half_15_07_φ3, show (2:ℝ)*4=8 by norm_num] using half_15_07_hx3)
  exact h.weaken (by norm_num [half_15_07_φ1, half_15_07_φ2, half_15_07_φ3, half_15_07_φ4, half_15_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_07_hx1 : SourcePowerBound (powerBoxCross 8 14 2 half_15_07_φ1) (190649047587/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 14) (u := 12) (t := 15)
    (D := 2) (ψ := (46283813/400000000 : ℝ)) half_15_07_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_07_φ1, half_15_07_φ2, half_15_07_φ3, half_15_07_φ4, half_15_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_07_φ1, half_15_07_φ2, half_15_07_φ3, half_15_07_φ4, half_15_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_07_φ1, half_15_07_φ2, half_15_07_φ3, half_15_07_φ4, half_15_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_13_07) (half_15_06)
    (by simpa only [half_15_07_φ2, show (2:ℝ)*2=4 by norm_num] using half_15_07_hx2)
  exact h.weaken (by norm_num [half_15_07_φ1, half_15_07_φ2, half_15_07_φ3, half_15_07_φ4, half_15_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_07 : AdmissibleExponent 8 30 (22273157589/1000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 13) (ψ := (1188241789/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_14_07)
    (by simpa only [half_15_07_φ1] using half_15_07_hx1)
  exact admissibleExponent_mono h (by norm_num [half_15_07_φ1, half_15_07_φ2, half_15_07_φ3, half_15_07_φ4, half_15_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_16_07_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (18848787/156250000 : ℝ)

def half_16_07_φ2 : Fin 2 → ℝ := Fin.snoc half_16_07_φ1 (1185135383/10000000000 : ℝ)

def half_16_07_φ3 : Fin 3 → ℝ := Fin.snoc half_16_07_φ2 (543467303/5000000000 : ℝ)

def half_16_07_φ4 : Fin 4 → ℝ := Fin.snoc half_16_07_φ3 (465829117/5000000000 : ℝ)

def half_16_07_φ5 : Fin 5 → ℝ := Fin.snoc half_16_07_φ4 (3992821/50000000 : ℝ)

theorem half_16_07_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_16_07_φ5) (60619089389/10000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_16_07_φ5 (by norm_num [half_16_07_φ1, half_16_07_φ2, half_16_07_φ3, half_16_07_φ4, half_16_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_07_φ1, half_16_07_φ2, half_16_07_φ3, half_16_07_φ4, half_16_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_07_φ1, half_16_07_φ2, half_16_07_φ3, half_16_07_φ4, half_16_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_16_07_φ1, half_16_07_φ2, half_16_07_φ3, half_16_07_φ4, half_16_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_16_07_φ1, half_16_07_φ2, half_16_07_φ3, half_16_07_φ4, half_16_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_16_07_hx5 : SourcePowerBound (powerBoxCross 8 11 32 half_16_07_φ5) (46454911099/5000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 11) (r := 2) (v := 14) (w := 15) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_16_07_φ5 (by norm_num [half_16_07_φ1, half_16_07_φ2, half_16_07_φ3, half_16_07_φ4, half_16_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_07_φ1, half_16_07_φ2, half_16_07_φ3, half_16_07_φ4, half_16_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_16_07_hF2 (half_14_07) (half_15_07)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_16_07_φ1, half_16_07_φ2, half_16_07_φ3, half_16_07_φ4, half_16_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_07_hx4 : SourcePowerBound (powerBoxCross 8 12 16 half_16_07_φ4) (111089964191/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 12) (u := 10) (t := 13)
    (D := 16) (ψ := (3992821/50000000 : ℝ)) half_16_07_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_07_φ1, half_16_07_φ2, half_16_07_φ3, half_16_07_φ4, half_16_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_07_φ1, half_16_07_φ2, half_16_07_φ3, half_16_07_φ4, half_16_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_07_φ1, half_16_07_φ2, half_16_07_φ3, half_16_07_φ4, half_16_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_11_07) (half_13_07)
    (by simpa only [half_16_07_φ5, show (2:ℝ)*16=32 by norm_num] using half_16_07_hx5)
  exact h.weaken (by norm_num [half_16_07_φ1, half_16_07_φ2, half_16_07_φ3, half_16_07_φ4, half_16_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_07_hx3 : SourcePowerBound (powerBoxCross 8 13 8 half_16_07_φ3) (135494408279/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 13) (u := 11) (t := 14)
    (D := 8) (ψ := (465829117/5000000000 : ℝ)) half_16_07_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_07_φ1, half_16_07_φ2, half_16_07_φ3, half_16_07_φ4, half_16_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_07_φ1, half_16_07_φ2, half_16_07_φ3, half_16_07_φ4, half_16_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_07_φ1, half_16_07_φ2, half_16_07_φ3, half_16_07_φ4, half_16_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_12_07) (half_14_07)
    (by simpa only [half_16_07_φ4, show (2:ℝ)*8=16 by norm_num] using half_16_07_hx4)
  exact h.weaken (by norm_num [half_16_07_φ1, half_16_07_φ2, half_16_07_φ3, half_16_07_φ4, half_16_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_07_hx2 : SourcePowerBound (powerBoxCross 8 14 4 half_16_07_φ2) (83848457427/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 14) (u := 12) (t := 15)
    (D := 4) (ψ := (543467303/5000000000 : ℝ)) half_16_07_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_07_φ1, half_16_07_φ2, half_16_07_φ3, half_16_07_φ4, half_16_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_07_φ1, half_16_07_φ2, half_16_07_φ3, half_16_07_φ4, half_16_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_07_φ1, half_16_07_φ2, half_16_07_φ3, half_16_07_φ4, half_16_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_13_07) (half_15_07)
    (by simpa only [half_16_07_φ3, show (2:ℝ)*4=8 by norm_num] using half_16_07_hx3)
  exact h.weaken (by norm_num [half_16_07_φ1, half_16_07_φ2, half_16_07_φ3, half_16_07_φ4, half_16_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_07_hx1 : SourcePowerBound (powerBoxCross 8 15 2 half_16_07_φ1) (25883661257/1250000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 15) (u := 13) (t := 16)
    (D := 2) (ψ := (1185135383/10000000000 : ℝ)) half_16_07_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_07_φ1, half_16_07_φ2, half_16_07_φ3, half_16_07_φ4, half_16_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_07_φ1, half_16_07_φ2, half_16_07_φ3, half_16_07_φ4, half_16_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_07_φ1, half_16_07_φ2, half_16_07_φ3, half_16_07_φ4, half_16_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_14_07) (half_16_06)
    (by simpa only [half_16_07_φ2, show (2:ℝ)*2=4 by norm_num] using half_16_07_hx2)
  exact h.weaken (by norm_num [half_16_07_φ1, half_16_07_φ2, half_16_07_φ3, half_16_07_φ4, half_16_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_07 : AdmissibleExponent 8 32 (30256579841/1250000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 14) (ψ := (18848787/156250000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_15_07)
    (by simpa only [half_16_07_φ1] using half_16_07_hx1)
  exact admissibleExponent_mono h (by norm_num [half_16_07_φ1, half_16_07_φ2, half_16_07_φ3, half_16_07_φ4, half_16_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_17_07_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (38118449/312500000 : ℝ)

def half_17_07_φ2 : Fin 2 → ℝ := Fin.snoc half_17_07_φ1 (1205902019/10000000000 : ℝ)

def half_17_07_φ3 : Fin 3 → ℝ := Fin.snoc half_17_07_φ2 (135255493/1250000000 : ℝ)

def half_17_07_φ4 : Fin 4 → ℝ := Fin.snoc half_17_07_φ3 (463733119/5000000000 : ℝ)

def half_17_07_φ5 : Fin 5 → ℝ := Fin.snoc half_17_07_φ4 (794971061/10000000000 : ℝ)

theorem half_17_07_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_17_07_φ5) (6016635377/1000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_17_07_φ5 (by norm_num [half_17_07_φ1, half_17_07_φ2, half_17_07_φ3, half_17_07_φ4, half_17_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_07_φ1, half_17_07_φ2, half_17_07_φ3, half_17_07_φ4, half_17_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_07_φ1, half_17_07_φ2, half_17_07_φ3, half_17_07_φ4, half_17_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_17_07_φ1, half_17_07_φ2, half_17_07_φ3, half_17_07_φ4, half_17_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_17_07_φ1, half_17_07_φ2, half_17_07_φ3, half_17_07_φ4, half_17_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_17_07_hx5 : SourcePowerBound (powerBoxCross 8 12 32 half_17_07_φ5) (50816383939/5000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 12) (r := 2) (v := 0) (w := 16) (D := 32)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_17_07_φ5 (by norm_num [half_17_07_φ1, half_17_07_φ2, half_17_07_φ3, half_17_07_φ4, half_17_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_07_φ1, half_17_07_φ2, half_17_07_φ3, half_17_07_φ4, half_17_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_17_07_hF2 (admissibleExponent_zero 8) (half_16_07)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_17_07_φ1, half_17_07_φ2, half_17_07_φ3, half_17_07_φ4, half_17_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_07_hx4 : SourcePowerBound (powerBoxCross 8 13 16 half_17_07_φ4) (12110184429/1000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 13) (u := 11) (t := 14)
    (D := 16) (ψ := (794971061/10000000000 : ℝ)) half_17_07_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_07_φ1, half_17_07_φ2, half_17_07_φ3, half_17_07_φ4, half_17_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_07_φ1, half_17_07_φ2, half_17_07_φ3, half_17_07_φ4, half_17_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_07_φ1, half_17_07_φ2, half_17_07_φ3, half_17_07_φ4, half_17_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_12_07) (half_14_07)
    (by simpa only [half_17_07_φ5, show (2:ℝ)*16=32 by norm_num] using half_17_07_hx5)
  exact h.weaken (by norm_num [half_17_07_φ1, half_17_07_φ2, half_17_07_φ3, half_17_07_φ4, half_17_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_07_hx3 : SourcePowerBound (powerBoxCross 8 14 8 half_17_07_φ3) (73584389433/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 14) (u := 12) (t := 15)
    (D := 8) (ψ := (463733119/5000000000 : ℝ)) half_17_07_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_07_φ1, half_17_07_φ2, half_17_07_φ3, half_17_07_φ4, half_17_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_07_φ1, half_17_07_φ2, half_17_07_φ3, half_17_07_φ4, half_17_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_07_φ1, half_17_07_φ2, half_17_07_φ3, half_17_07_φ4, half_17_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_13_07) (half_15_07)
    (by simpa only [half_17_07_φ4, show (2:ℝ)*8=16 by norm_num] using half_17_07_hx4)
  exact h.weaken (by norm_num [half_17_07_φ1, half_17_07_φ2, half_17_07_φ3, half_17_07_φ4, half_17_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_07_hx2 : SourcePowerBound (powerBoxCross 8 15 4 half_17_07_φ2) (22671389567/1250000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 15) (u := 13) (t := 16)
    (D := 4) (ψ := (135255493/1250000000 : ℝ)) half_17_07_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_07_φ1, half_17_07_φ2, half_17_07_φ3, half_17_07_φ4, half_17_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_07_φ1, half_17_07_φ2, half_17_07_φ3, half_17_07_φ4, half_17_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_07_φ1, half_17_07_φ2, half_17_07_φ3, half_17_07_φ4, half_17_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_14_07) (half_16_07)
    (by simpa only [half_17_07_φ3, show (2:ℝ)*4=8 by norm_num] using half_17_07_hx3)
  exact h.weaken (by norm_num [half_17_07_φ1, half_17_07_φ2, half_17_07_φ3, half_17_07_φ4, half_17_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_07_hx1 : SourcePowerBound (powerBoxCross 8 16 2 half_17_07_φ1) (55936770343/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 16) (u := 14) (t := 17)
    (D := 2) (ψ := (1205902019/10000000000 : ℝ)) half_17_07_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_07_φ1, half_17_07_φ2, half_17_07_φ3, half_17_07_φ4, half_17_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_07_φ1, half_17_07_φ2, half_17_07_φ3, half_17_07_φ4, half_17_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_07_φ1, half_17_07_φ2, half_17_07_φ3, half_17_07_φ4, half_17_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_15_07) (half_17_06)
    (by simpa only [half_17_07_φ2, show (2:ℝ)*2=4 by norm_num] using half_17_07_hx2)
  exact h.weaken (by norm_num [half_17_07_φ1, half_17_07_φ2, half_17_07_φ3, half_17_07_φ4, half_17_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_07 : AdmissibleExponent 8 34 (13078029139/500000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 15) (ψ := (38118449/312500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_16_07)
    (by simpa only [half_17_07_φ1] using half_17_07_hx1)
  exact admissibleExponent_mono h (by norm_num [half_17_07_φ1, half_17_07_φ2, half_17_07_φ3, half_17_07_φ4, half_17_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_18_07_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1230182297/10000000000 : ℝ)

def half_18_07_φ2 : Fin 2 → ℝ := Fin.snoc half_18_07_φ1 (122180627/1000000000 : ℝ)

def half_18_07_φ3 : Fin 3 → ℝ := Fin.snoc half_18_07_φ2 (1078287347/10000000000 : ℝ)

def half_18_07_φ4 : Fin 4 → ℝ := Fin.snoc half_18_07_φ3 (924246297/10000000000 : ℝ)

def half_18_07_φ5 : Fin 5 → ℝ := Fin.snoc half_18_07_φ4 (99026389/1250000000 : ℝ)

theorem half_18_07_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_18_07_φ5) (59818600217/10000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_18_07_φ5 (by norm_num [half_18_07_φ1, half_18_07_φ2, half_18_07_φ3, half_18_07_φ4, half_18_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_18_07_φ1, half_18_07_φ2, half_18_07_φ3, half_18_07_φ4, half_18_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_18_07_φ1, half_18_07_φ2, half_18_07_φ3, half_18_07_φ4, half_18_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_18_07_φ1, half_18_07_φ2, half_18_07_φ3, half_18_07_φ4, half_18_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_18_07_φ1, half_18_07_φ2, half_18_07_φ3, half_18_07_φ4, half_18_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_18_07_hx5 : SourcePowerBound (powerBoxCross 8 13 32 half_18_07_φ5) (55269715737/5000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 13) (r := 2) (v := 17) (w := 18) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_18_07_φ5 (by norm_num [half_18_07_φ1, half_18_07_φ2, half_18_07_φ3, half_18_07_φ4, half_18_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_18_07_φ1, half_18_07_φ2, half_18_07_φ3, half_18_07_φ4, half_18_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_18_07_hF2 (half_17_07) (half_18_06)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_18_07_φ1, half_18_07_φ2, half_18_07_φ3, half_18_07_φ4, half_18_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_18_07_hx4 : SourcePowerBound (powerBoxCross 8 14 16 half_18_07_φ4) (131339177249/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 14) (u := 12) (t := 15)
    (D := 16) (ψ := (99026389/1250000000 : ℝ)) half_18_07_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_18_07_φ1, half_18_07_φ2, half_18_07_φ3, half_18_07_φ4, half_18_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_18_07_φ1, half_18_07_φ2, half_18_07_φ3, half_18_07_φ4, half_18_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_18_07_φ1, half_18_07_φ2, half_18_07_φ3, half_18_07_φ4, half_18_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_13_07) (half_15_07)
    (by simpa only [half_18_07_φ5, show (2:ℝ)*16=32 by norm_num] using half_18_07_hx5)
  exact h.weaken (by norm_num [half_18_07_φ1, half_18_07_φ2, half_18_07_φ3, half_18_07_φ4, half_18_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_18_07_hx3 : SourcePowerBound (powerBoxCross 8 15 8 half_18_07_φ3) (79545818639/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 15) (u := 13) (t := 16)
    (D := 8) (ψ := (924246297/10000000000 : ℝ)) half_18_07_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_18_07_φ1, half_18_07_φ2, half_18_07_φ3, half_18_07_φ4, half_18_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_18_07_φ1, half_18_07_φ2, half_18_07_φ3, half_18_07_φ4, half_18_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_18_07_φ1, half_18_07_φ2, half_18_07_φ3, half_18_07_φ4, half_18_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_14_07) (half_16_07)
    (by simpa only [half_18_07_φ4, show (2:ℝ)*8=16 by norm_num] using half_18_07_hx4)
  exact h.weaken (by norm_num [half_18_07_φ1, half_18_07_φ2, half_18_07_φ3, half_18_07_φ4, half_18_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_18_07_hx2 : SourcePowerBound (powerBoxCross 8 16 4 half_18_07_φ2) (195312138649/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 16) (u := 14) (t := 17)
    (D := 4) (ψ := (1078287347/10000000000 : ℝ)) half_18_07_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_18_07_φ1, half_18_07_φ2, half_18_07_φ3, half_18_07_φ4, half_18_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_18_07_φ1, half_18_07_φ2, half_18_07_φ3, half_18_07_φ4, half_18_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_18_07_φ1, half_18_07_φ2, half_18_07_φ3, half_18_07_φ4, half_18_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_15_07) (half_17_07)
    (by simpa only [half_18_07_φ3, show (2:ℝ)*4=8 by norm_num] using half_18_07_hx3)
  exact h.weaken (by norm_num [half_18_07_φ1, half_18_07_φ2, half_18_07_φ3, half_18_07_φ4, half_18_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_18_07_hx1 : SourcePowerBound (powerBoxCross 8 17 2 half_18_07_φ1) (240614045231/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 17) (u := 15) (t := 18)
    (D := 2) (ψ := (122180627/1000000000 : ℝ)) half_18_07_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_18_07_φ1, half_18_07_φ2, half_18_07_φ3, half_18_07_φ4, half_18_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_18_07_φ1, half_18_07_φ2, half_18_07_φ3, half_18_07_φ4, half_18_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_18_07_φ1, half_18_07_φ2, half_18_07_φ3, half_18_07_φ4, half_18_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_16_07) (half_18_06)
    (by simpa only [half_18_07_φ2, show (2:ℝ)*2=4 by norm_num] using half_18_07_hx2)
  exact h.weaken (by norm_num [half_18_07_φ1, half_18_07_φ2, half_18_07_φ3, half_18_07_φ4, half_18_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_18_07 : AdmissibleExponent 8 36 (35151257629/1250000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 16) (ψ := (1230182297/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_17_07)
    (by simpa only [half_18_07_φ1] using half_18_07_hx1)
  exact admissibleExponent_mono h (by norm_num [half_18_07_φ1, half_18_07_φ2, half_18_07_φ3, half_18_07_φ4, half_18_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_19_07_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (123782043/1000000000 : ℝ)

def half_19_07_φ2 : Fin 2 → ℝ := Fin.snoc half_19_07_φ1 (308442421/2500000000 : ℝ)

def half_19_07_φ3 : Fin 3 → ℝ := Fin.snoc half_19_07_φ2 (537743563/5000000000 : ℝ)

def half_19_07_φ4 : Fin 4 → ℝ := Fin.snoc half_19_07_φ3 (230461527/2500000000 : ℝ)

def half_19_07_φ5 : Fin 5 → ℝ := Fin.snoc half_19_07_φ4 (790153807/10000000000 : ℝ)

theorem half_19_07_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_19_07_φ5) (11911875949/2000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_19_07_φ5 (by norm_num [half_19_07_φ1, half_19_07_φ2, half_19_07_φ3, half_19_07_φ4, half_19_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_19_07_φ1, half_19_07_φ2, half_19_07_φ3, half_19_07_φ4, half_19_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_19_07_φ1, half_19_07_φ2, half_19_07_φ3, half_19_07_φ4, half_19_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_19_07_φ1, half_19_07_φ2, half_19_07_φ3, half_19_07_φ4, half_19_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_19_07_φ1, half_19_07_φ2, half_19_07_φ3, half_19_07_φ4, half_19_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_19_07_hx5 : SourcePowerBound (powerBoxCross 8 14 32 half_19_07_φ5) (119571813681/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 14) (r := 2) (v := 18) (w := 19) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_19_07_φ5 (by norm_num [half_19_07_φ1, half_19_07_φ2, half_19_07_φ3, half_19_07_φ4, half_19_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_19_07_φ1, half_19_07_φ2, half_19_07_φ3, half_19_07_φ4, half_19_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_19_07_hF2 (half_18_07) (half_19_06)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_19_07_φ1, half_19_07_φ2, half_19_07_φ3, half_19_07_φ4, half_19_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_19_07_hx4 : SourcePowerBound (powerBoxCross 8 15 16 half_19_07_φ4) (141752336449/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 15) (u := 13) (t := 16)
    (D := 16) (ψ := (790153807/10000000000 : ℝ)) half_19_07_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_19_07_φ1, half_19_07_φ2, half_19_07_φ3, half_19_07_φ4, half_19_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_19_07_φ1, half_19_07_φ2, half_19_07_φ3, half_19_07_φ4, half_19_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_19_07_φ1, half_19_07_φ2, half_19_07_φ3, half_19_07_φ4, half_19_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_14_07) (half_16_07)
    (by simpa only [half_19_07_φ5, show (2:ℝ)*16=32 by norm_num] using half_19_07_hx5)
  exact h.weaken (by norm_num [half_19_07_φ1, half_19_07_φ2, half_19_07_φ3, half_19_07_φ4, half_19_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_19_07_hx3 : SourcePowerBound (powerBoxCross 8 16 8 half_19_07_φ3) (85609839169/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 16) (u := 14) (t := 17)
    (D := 8) (ψ := (230461527/2500000000 : ℝ)) half_19_07_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_19_07_φ1, half_19_07_φ2, half_19_07_φ3, half_19_07_φ4, half_19_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_19_07_φ1, half_19_07_φ2, half_19_07_φ3, half_19_07_φ4, half_19_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_19_07_φ1, half_19_07_φ2, half_19_07_φ3, half_19_07_φ4, half_19_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_15_07) (half_17_07)
    (by simpa only [half_19_07_φ4, show (2:ℝ)*8=16 by norm_num] using half_19_07_hx4)
  exact h.weaken (by norm_num [half_19_07_φ1, half_19_07_φ2, half_19_07_φ3, half_19_07_φ4, half_19_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_19_07_hx2 : SourcePowerBound (powerBoxCross 8 17 4 half_19_07_φ2) (209482554399/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 17) (u := 15) (t := 18)
    (D := 4) (ψ := (537743563/5000000000 : ℝ)) half_19_07_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_19_07_φ1, half_19_07_φ2, half_19_07_φ3, half_19_07_φ4, half_19_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_19_07_φ1, half_19_07_φ2, half_19_07_φ3, half_19_07_φ4, half_19_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_19_07_φ1, half_19_07_φ2, half_19_07_φ3, half_19_07_φ4, half_19_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_16_07) (half_18_07)
    (by simpa only [half_19_07_φ3, show (2:ℝ)*4=8 by norm_num] using half_19_07_hx3)
  exact h.weaken (by norm_num [half_19_07_φ1, half_19_07_φ2, half_19_07_φ3, half_19_07_φ4, half_19_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_19_07_hx1 : SourcePowerBound (powerBoxCross 8 18 2 half_19_07_φ1) (257639125597/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 18) (u := 16) (t := 19)
    (D := 2) (ψ := (308442421/2500000000 : ℝ)) half_19_07_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_19_07_φ1, half_19_07_φ2, half_19_07_φ3, half_19_07_φ4, half_19_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_19_07_φ1, half_19_07_φ2, half_19_07_φ3, half_19_07_φ4, half_19_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_19_07_φ1, half_19_07_φ2, half_19_07_φ3, half_19_07_φ4, half_19_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_17_07) (half_19_06)
    (by simpa only [half_19_07_φ2, show (2:ℝ)*2=4 by norm_num] using half_19_07_hx2)
  exact h.weaken (by norm_num [half_19_07_φ1, half_19_07_φ2, half_19_07_φ3, half_19_07_φ4, half_19_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_19_07 : AdmissibleExponent 8 38 (300962840647/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 17) (ψ := (123782043/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_18_07)
    (by simpa only [half_19_07_φ1] using half_19_07_hx1)
  exact admissibleExponent_mono h (by norm_num [half_19_07_φ1, half_19_07_φ2, half_19_07_φ3, half_19_07_φ4, half_19_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_20_07_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (310958137/2500000000 : ℝ)

def half_20_07_φ2 : Fin 2 → ℝ := Fin.snoc half_20_07_φ1 (310634009/2500000000 : ℝ)

def half_20_07_φ3 : Fin 3 → ℝ := Fin.snoc half_20_07_φ2 (268343979/2500000000 : ℝ)

def half_20_07_φ4 : Fin 4 → ℝ := Fin.snoc half_20_07_φ3 (920036499/10000000000 : ℝ)

def half_20_07_φ5 : Fin 5 → ℝ := Fin.snoc half_20_07_φ4 (394301357/5000000000 : ℝ)

theorem half_20_07_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_20_07_φ5) (59363942027/10000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_20_07_φ5 (by norm_num [half_20_07_φ1, half_20_07_φ2, half_20_07_φ3, half_20_07_φ4, half_20_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_20_07_φ1, half_20_07_φ2, half_20_07_φ3, half_20_07_φ4, half_20_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_20_07_φ1, half_20_07_φ2, half_20_07_φ3, half_20_07_φ4, half_20_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_20_07_φ1, half_20_07_φ2, half_20_07_φ3, half_20_07_φ4, half_20_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_20_07_φ1, half_20_07_φ2, half_20_07_φ3, half_20_07_φ4, half_20_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_20_07_hx5 : SourcePowerBound (powerBoxCross 8 15 32 half_20_07_φ5) (32174718123/2500000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 15) (r := 2) (v := 0) (w := 20) (D := 32)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_20_07_φ5 (by norm_num [half_20_07_φ1, half_20_07_φ2, half_20_07_φ3, half_20_07_φ4, half_20_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_20_07_φ1, half_20_07_φ2, half_20_07_φ3, half_20_07_φ4, half_20_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_20_07_hF2 (admissibleExponent_zero 8) (half_20_06)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_20_07_φ1, half_20_07_φ2, half_20_07_φ3, half_20_07_φ4, half_20_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_20_07_hx4 : SourcePowerBound (powerBoxCross 8 16 16 half_20_07_φ4) (38074631763/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 16) (u := 14) (t := 17)
    (D := 16) (ψ := (394301357/5000000000 : ℝ)) half_20_07_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_20_07_φ1, half_20_07_φ2, half_20_07_φ3, half_20_07_φ4, half_20_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_20_07_φ1, half_20_07_φ2, half_20_07_φ3, half_20_07_φ4, half_20_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_20_07_φ1, half_20_07_φ2, half_20_07_φ3, half_20_07_φ4, half_20_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_15_07) (half_17_07)
    (by simpa only [half_20_07_φ5, show (2:ℝ)*16=32 by norm_num] using half_20_07_hx5)
  exact h.weaken (by norm_num [half_20_07_φ1, half_20_07_φ2, half_20_07_φ3, half_20_07_φ4, half_20_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_20_07_hx3 : SourcePowerBound (powerBoxCross 8 17 8 half_20_07_φ3) (91751977811/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 17) (u := 15) (t := 18)
    (D := 8) (ψ := (920036499/10000000000 : ℝ)) half_20_07_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_20_07_φ1, half_20_07_φ2, half_20_07_φ3, half_20_07_φ4, half_20_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_20_07_φ1, half_20_07_φ2, half_20_07_φ3, half_20_07_φ4, half_20_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_20_07_φ1, half_20_07_φ2, half_20_07_φ3, half_20_07_φ4, half_20_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_16_07) (half_18_07)
    (by simpa only [half_20_07_φ4, show (2:ℝ)*8=16 by norm_num] using half_20_07_hx4)
  exact h.weaken (by norm_num [half_20_07_φ1, half_20_07_φ2, half_20_07_φ3, half_20_07_φ4, half_20_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_20_07_hx2 : SourcePowerBound (powerBoxCross 8 18 4 half_20_07_φ2) (55956645777/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 18) (u := 16) (t := 19)
    (D := 4) (ψ := (268343979/2500000000 : ℝ)) half_20_07_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_20_07_φ1, half_20_07_φ2, half_20_07_φ3, half_20_07_φ4, half_20_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_20_07_φ1, half_20_07_φ2, half_20_07_φ3, half_20_07_φ4, half_20_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_20_07_φ1, half_20_07_φ2, half_20_07_φ3, half_20_07_φ4, half_20_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_17_07) (half_19_07)
    (by simpa only [half_20_07_φ3, show (2:ℝ)*4=8 by norm_num] using half_20_07_hx3)
  exact h.weaken (by norm_num [half_20_07_φ1, half_20_07_φ2, half_20_07_φ3, half_20_07_φ4, half_20_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_20_07_hx1 : SourcePowerBound (powerBoxCross 8 19 2 half_20_07_φ1) (27477193551/1000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 19) (u := 17) (t := 20)
    (D := 2) (ψ := (310634009/2500000000 : ℝ)) half_20_07_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_20_07_φ1, half_20_07_φ2, half_20_07_φ3, half_20_07_φ4, half_20_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_20_07_φ1, half_20_07_φ2, half_20_07_φ3, half_20_07_φ4, half_20_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_20_07_φ1, half_20_07_φ2, half_20_07_φ3, half_20_07_φ4, half_20_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_18_07) (half_20_06)
    (by simpa only [half_20_07_φ2, show (2:ℝ)*2=4 by norm_num] using half_20_07_hx2)
  exact h.weaken (by norm_num [half_20_07_φ1, half_20_07_φ2, half_20_07_φ3, half_20_07_φ4, half_20_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_20_07 : AdmissibleExponent 8 40 (160396869893/5000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 18) (ψ := (310958137/2500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_19_07)
    (by simpa only [half_20_07_φ1] using half_20_07_hx1)
  exact admissibleExponent_mono h (by norm_num [half_20_07_φ1, half_20_07_φ2, half_20_07_φ3, half_20_07_φ4, half_20_07_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_10_08_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1031669863/10000000000 : ℝ)

def half_10_08_φ2 : Fin 2 → ℝ := Fin.snoc half_10_08_φ1 (15021961/156250000 : ℝ)

def half_10_08_φ3 : Fin 3 → ℝ := Fin.snoc half_10_08_φ2 (418292421/5000000000 : ℝ)

def half_10_08_φ4 : Fin 4 → ℝ := Fin.snoc half_10_08_φ3 (137253873/2500000000 : ℝ)

theorem half_10_08_hF2 : SourcePowerBound (paddedMoment 8 0 2 16 half_10_08_φ4) (69047810279/10000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 4) (r := 0) (n := 1) (D := 16)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_10_08_φ4 (by norm_num [half_10_08_φ1, half_10_08_φ2, half_10_08_φ3, half_10_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_08_φ1, half_10_08_φ2, half_10_08_φ3, half_10_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_08_φ1, half_10_08_φ2, half_10_08_φ3, half_10_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_10_08_φ1, half_10_08_φ2, half_10_08_φ3, half_10_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_10_08_φ1, half_10_08_φ2, half_10_08_φ3, half_10_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_10_08_hx4 : SourcePowerBound (powerBoxCross 8 6 16 half_10_08_φ4) (66141538913/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 6) (r := 2) (v := 0) (w := 8) (D := 16)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_10_08_φ4 (by norm_num [half_10_08_φ1, half_10_08_φ2, half_10_08_φ3, half_10_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_08_φ1, half_10_08_φ2, half_10_08_φ3, half_10_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_10_08_hF2 (admissibleExponent_zero 8) (SeedCompletionHigher8SimpleSeeds.degree8_half_8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_10_08_φ1, half_10_08_φ2, half_10_08_φ3, half_10_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_08_hx3 : SourcePowerBound (powerBoxCross 8 7 8 half_10_08_φ3) (19118719177/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 7) (u := 5) (t := 8)
    (D := 8) (ψ := (137253873/2500000000 : ℝ)) half_10_08_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_08_φ1, half_10_08_φ2, half_10_08_φ3, half_10_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_08_φ1, half_10_08_φ2, half_10_08_φ3, half_10_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_08_φ1, half_10_08_φ2, half_10_08_φ3, half_10_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionEven8SecondSeeds.degree8_half_6) (SeedCompletionHigher8SimpleSeeds.degree8_half_8)
    (by simpa only [half_10_08_φ4, show (2:ℝ)*8=16 by norm_num] using half_10_08_hx4)
  exact h.weaken (by norm_num [half_10_08_φ1, half_10_08_φ2, half_10_08_φ3, half_10_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_08_hx2 : SourcePowerBound (powerBoxCross 8 8 4 half_10_08_φ2) (92550771231/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 8) (u := 6) (t := 9)
    (D := 4) (ψ := (418292421/5000000000 : ℝ)) half_10_08_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_08_φ1, half_10_08_φ2, half_10_08_φ3, half_10_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_08_φ1, half_10_08_φ2, half_10_08_φ3, half_10_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_08_φ1, half_10_08_φ2, half_10_08_φ3, half_10_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_7) (SeedCompletionHigher8SimpleSeeds.degree8_half_9)
    (by simpa only [half_10_08_φ3, show (2:ℝ)*4=8 by norm_num] using half_10_08_hx3)
  exact h.weaken (by norm_num [half_10_08_φ1, half_10_08_φ2, half_10_08_φ3, half_10_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_08_hx1 : SourcePowerBound (powerBoxCross 8 9 2 half_10_08_φ1) (56872575667/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 9) (u := 7) (t := 10)
    (D := 2) (ψ := (15021961/156250000 : ℝ)) half_10_08_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_08_φ1, half_10_08_φ2, half_10_08_φ3, half_10_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_08_φ1, half_10_08_φ2, half_10_08_φ3, half_10_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_08_φ1, half_10_08_φ2, half_10_08_φ3, half_10_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_8) (half_10_07)
    (by simpa only [half_10_08_φ2, show (2:ℝ)*2=4 by norm_num] using half_10_08_hx2)
  exact h.weaken (by norm_num [half_10_08_φ1, half_10_08_φ2, half_10_08_φ3, half_10_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_08 : AdmissibleExponent 8 20 (26256707801/2000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 8) (ψ := (1031669863/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_9)
    (by simpa only [half_10_08_φ1] using half_10_08_hx1)
  exact admissibleExponent_mono h (by norm_num [half_10_08_φ1, half_10_08_φ2, half_10_08_φ3, half_10_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_11_08_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (268618749/2500000000 : ℝ)

def half_11_08_φ2 : Fin 2 → ℝ := Fin.snoc half_11_08_φ1 (50613351/500000000 : ℝ)

def half_11_08_φ3 : Fin 3 → ℝ := Fin.snoc half_11_08_φ2 (18446179/200000000 : ℝ)

def half_11_08_φ4 : Fin 4 → ℝ := Fin.snoc half_11_08_φ3 (740526073/10000000000 : ℝ)

theorem half_11_08_hF2 : SourcePowerBound (paddedMoment 8 0 2 16 half_11_08_φ4) (61258882181/10000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 4) (r := 0) (n := 1) (D := 16)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_11_08_φ4 (by norm_num [half_11_08_φ1, half_11_08_φ2, half_11_08_φ3, half_11_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_08_φ1, half_11_08_φ2, half_11_08_φ3, half_11_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_08_φ1, half_11_08_φ2, half_11_08_φ3, half_11_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_11_08_φ1, half_11_08_φ2, half_11_08_φ3, half_11_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_11_08_φ1, half_11_08_φ2, half_11_08_φ3, half_11_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_11_08_hx4 : SourcePowerBound (powerBoxCross 8 7 16 half_11_08_φ4) (1119092637/156250000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 7) (r := 2) (v := 9) (w := 10) (D := 16)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_11_08_φ4 (by norm_num [half_11_08_φ1, half_11_08_φ2, half_11_08_φ3, half_11_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_08_φ1, half_11_08_φ2, half_11_08_φ3, half_11_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_11_08_hF2 (SeedCompletionHigher8SimpleSeeds.degree8_half_9) (half_10_08)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_11_08_φ1, half_11_08_φ2, half_11_08_φ3, half_11_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_08_hx3 : SourcePowerBound (powerBoxCross 8 8 8 half_11_08_φ3) (17025212383/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 8) (u := 6) (t := 9)
    (D := 8) (ψ := (740526073/10000000000 : ℝ)) half_11_08_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_08_φ1, half_11_08_φ2, half_11_08_φ3, half_11_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_08_φ1, half_11_08_φ2, half_11_08_φ3, half_11_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_08_φ1, half_11_08_φ2, half_11_08_φ3, half_11_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_7) (SeedCompletionHigher8SimpleSeeds.degree8_half_9)
    (by simpa only [half_11_08_φ4, show (2:ℝ)*8=16 by norm_num] using half_11_08_hx4)
  exact h.weaken (by norm_num [half_11_08_φ1, half_11_08_φ2, half_11_08_φ3, half_11_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_08_hx2 : SourcePowerBound (powerBoxCross 8 9 4 half_11_08_φ2) (104120776687/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 9) (u := 7) (t := 10)
    (D := 4) (ψ := (18446179/200000000 : ℝ)) half_11_08_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_08_φ1, half_11_08_φ2, half_11_08_φ3, half_11_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_08_φ1, half_11_08_φ2, half_11_08_φ3, half_11_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_08_φ1, half_11_08_φ2, half_11_08_φ3, half_11_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_8) (half_10_08)
    (by simpa only [half_11_08_φ3, show (2:ℝ)*4=8 by norm_num] using half_11_08_hx3)
  exact h.weaken (by norm_num [half_11_08_φ1, half_11_08_φ2, half_11_08_φ3, half_11_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_08_hx1 : SourcePowerBound (powerBoxCross 8 10 2 half_11_08_φ1) (64125963001/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 10) (u := 8) (t := 11)
    (D := 2) (ψ := (50613351/500000000 : ℝ)) half_11_08_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_08_φ1, half_11_08_φ2, half_11_08_φ3, half_11_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_08_φ1, half_11_08_φ2, half_11_08_φ3, half_11_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_08_φ1, half_11_08_φ2, half_11_08_φ3, half_11_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_9) (half_11_07)
    (by simpa only [half_11_08_φ2, show (2:ℝ)*2=4 by norm_num] using half_11_08_hx2)
  exact h.weaken (by norm_num [half_11_08_φ1, half_11_08_φ2, half_11_08_φ3, half_11_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_08 : AdmissibleExponent 8 22 (74333475463/5000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 9) (ψ := (268618749/2500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_10_08)
    (by simpa only [half_11_08_φ1] using half_11_08_hx1)
  exact admissibleExponent_mono h (by norm_num [half_11_08_φ1, half_11_08_φ2, half_11_08_φ3, half_11_08_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_12_08_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (276856323/2500000000 : ℝ)

def half_12_08_φ2 : Fin 2 → ℝ := Fin.snoc half_12_08_φ1 (1055616851/10000000000 : ℝ)

def half_12_08_φ3 : Fin 3 → ℝ := Fin.snoc half_12_08_φ2 (977066677/10000000000 : ℝ)

def half_12_08_φ4 : Fin 4 → ℝ := Fin.snoc half_12_08_φ3 (421012417/5000000000 : ℝ)

def half_12_08_φ5 : Fin 5 → ℝ := Fin.snoc half_12_08_φ4 (264025641/5000000000 : ℝ)

theorem half_12_08_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_12_08_φ5) (9410764543/1250000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_12_08_φ5 (by norm_num [half_12_08_φ1, half_12_08_φ2, half_12_08_φ3, half_12_08_φ4, half_12_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_08_φ1, half_12_08_φ2, half_12_08_φ3, half_12_08_φ4, half_12_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_08_φ1, half_12_08_φ2, half_12_08_φ3, half_12_08_φ4, half_12_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_12_08_φ1, half_12_08_φ2, half_12_08_φ3, half_12_08_φ4, half_12_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_12_08_φ1, half_12_08_φ2, half_12_08_φ3, half_12_08_φ4, half_12_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_12_08_hx5 : SourcePowerBound (powerBoxCross 8 7 32 half_12_08_φ5) (1365535357/200000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 7) (r := 2) (v := 9) (w := 10) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_12_08_φ5 (by norm_num [half_12_08_φ1, half_12_08_φ2, half_12_08_φ3, half_12_08_φ4, half_12_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_08_φ1, half_12_08_φ2, half_12_08_φ3, half_12_08_φ4, half_12_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_12_08_hF2 (SeedCompletionHigher8SimpleSeeds.degree8_half_9) (half_10_08)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_12_08_φ1, half_12_08_φ2, half_12_08_φ3, half_12_08_φ4, half_12_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_08_hx4 : SourcePowerBound (powerBoxCross 8 8 16 half_12_08_φ4) (7809429149/1000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 8) (u := 6) (t := 9)
    (D := 16) (ψ := (264025641/5000000000 : ℝ)) half_12_08_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_08_φ1, half_12_08_φ2, half_12_08_φ3, half_12_08_φ4, half_12_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_08_φ1, half_12_08_φ2, half_12_08_φ3, half_12_08_φ4, half_12_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_08_φ1, half_12_08_φ2, half_12_08_φ3, half_12_08_φ4, half_12_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_7) (SeedCompletionHigher8SimpleSeeds.degree8_half_9)
    (by simpa only [half_12_08_φ5, show (2:ℝ)*16=32 by norm_num] using half_12_08_hx5)
  exact h.weaken (by norm_num [half_12_08_φ1, half_12_08_φ2, half_12_08_φ3, half_12_08_φ4, half_12_08_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

end Waring.SeedCompletionAlternate8Seeds
