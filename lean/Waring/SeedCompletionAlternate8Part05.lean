import Waring.SeedCompletionAlternate8Part04
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

theorem half_18_10_hx4 : SourcePowerBound (powerBoxCross 8 14 16 half_18_10_φ4) (13133484387/1000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 14) (u := 12) (t := 15)
    (D := 16) (ψ := (396148209/5000000000 : ℝ)) half_18_10_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_18_10_φ1, half_18_10_φ2, half_18_10_φ3, half_18_10_φ4, half_18_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_18_10_φ1, half_18_10_φ2, half_18_10_φ3, half_18_10_φ4, half_18_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_18_10_φ1, half_18_10_φ2, half_18_10_φ3, half_18_10_φ4, half_18_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_13_10) (half_15_10)
    (by simpa only [half_18_10_φ5, show (2:ℝ)*16=32 by norm_num] using half_18_10_hx5)
  exact h.weaken (by norm_num [half_18_10_φ1, half_18_10_φ2, half_18_10_φ3, half_18_10_φ4, half_18_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_18_10_hx3 : SourcePowerBound (powerBoxCross 8 15 8 half_18_10_φ3) (159087730823/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 15) (u := 13) (t := 16)
    (D := 8) (ψ := (924345821/10000000000 : ℝ)) half_18_10_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_18_10_φ1, half_18_10_φ2, half_18_10_φ3, half_18_10_φ4, half_18_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_18_10_φ1, half_18_10_φ2, half_18_10_φ3, half_18_10_φ4, half_18_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_18_10_φ1, half_18_10_φ2, half_18_10_φ3, half_18_10_φ4, half_18_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_14_10) (half_16_10)
    (by simpa only [half_18_10_φ4, show (2:ℝ)*8=16 by norm_num] using half_18_10_hx4)
  exact h.weaken (by norm_num [half_18_10_φ1, half_18_10_φ2, half_18_10_φ3, half_18_10_φ4, half_18_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_18_10_hx2 : SourcePowerBound (powerBoxCross 8 16 4 half_18_10_φ2) (24413435857/1250000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 16) (u := 14) (t := 17)
    (D := 4) (ψ := (539201729/5000000000 : ℝ)) half_18_10_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_18_10_φ1, half_18_10_φ2, half_18_10_φ3, half_18_10_φ4, half_18_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_18_10_φ1, half_18_10_φ2, half_18_10_φ3, half_18_10_φ4, half_18_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_18_10_φ1, half_18_10_φ2, half_18_10_φ3, half_18_10_φ4, half_18_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_15_10) (half_17_10)
    (by simpa only [half_18_10_φ3, show (2:ℝ)*4=8 by norm_num] using half_18_10_hx3)
  exact h.weaken (by norm_num [half_18_10_φ1, half_18_10_φ2, half_18_10_φ3, half_18_10_φ4, half_18_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_18_10_hx1 : SourcePowerBound (powerBoxCross 8 17 2 half_18_10_φ1) (4812019847/200000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 17) (u := 15) (t := 18)
    (D := 2) (ψ := (244424821/2000000000 : ℝ)) half_18_10_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_18_10_φ1, half_18_10_φ2, half_18_10_φ3, half_18_10_φ4, half_18_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_18_10_φ1, half_18_10_φ2, half_18_10_φ3, half_18_10_φ4, half_18_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_18_10_φ1, half_18_10_φ2, half_18_10_φ3, half_18_10_φ4, half_18_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_16_10) (half_18_09)
    (by simpa only [half_18_10_φ2, show (2:ℝ)*2=4 by norm_num] using half_18_10_hx2)
  exact h.weaken (by norm_num [half_18_10_φ1, half_18_10_φ2, half_18_10_φ3, half_18_10_φ4, half_18_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_18_10 : AdmissibleExponent 8 36 (281159697889/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 16) (ψ := (1229051683/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_17_10)
    (by simpa only [half_18_10_φ1] using half_18_10_hx1)
  exact admissibleExponent_mono h (by norm_num [half_18_10_φ1, half_18_10_φ2, half_18_10_φ3, half_18_10_φ4, half_18_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_19_10_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (30914599/250000000 : ℝ)

def half_19_10_φ2 : Fin 2 → ℝ := Fin.snoc half_19_10_φ1 (1234112529/10000000000 : ℝ)

def half_19_10_φ3 : Fin 3 → ℝ := Fin.snoc half_19_10_φ2 (1075614787/10000000000 : ℝ)

def half_19_10_φ4 : Fin 4 → ℝ := Fin.snoc half_19_10_φ3 (921955531/10000000000 : ℝ)

def half_19_10_φ5 : Fin 5 → ℝ := Fin.snoc half_19_10_φ4 (395123799/5000000000 : ℝ)

theorem half_19_10_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_19_10_φ5) (11914239499/2000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_19_10_φ5 (by norm_num [half_19_10_φ1, half_19_10_φ2, half_19_10_φ3, half_19_10_φ4, half_19_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_19_10_φ1, half_19_10_φ2, half_19_10_φ3, half_19_10_φ4, half_19_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_19_10_φ1, half_19_10_φ2, half_19_10_φ3, half_19_10_φ4, half_19_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_19_10_φ1, half_19_10_φ2, half_19_10_φ3, half_19_10_φ4, half_19_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_19_10_φ1, half_19_10_φ2, half_19_10_φ3, half_19_10_φ4, half_19_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_19_10_hx5 : SourcePowerBound (powerBoxCross 8 14 32 half_19_10_φ5) (59780448187/5000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 14) (r := 2) (v := 18) (w := 19) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_19_10_φ5 (by norm_num [half_19_10_φ1, half_19_10_φ2, half_19_10_φ3, half_19_10_φ4, half_19_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_19_10_φ1, half_19_10_φ2, half_19_10_φ3, half_19_10_φ4, half_19_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_19_10_hF2 (half_18_10) (half_19_09)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_19_10_φ1, half_19_10_φ2, half_19_10_φ3, half_19_10_φ4, half_19_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_19_10_hx4 : SourcePowerBound (powerBoxCross 8 15 16 half_19_10_φ4) (35436614697/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 15) (u := 13) (t := 16)
    (D := 16) (ψ := (395123799/5000000000 : ℝ)) half_19_10_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_19_10_φ1, half_19_10_φ2, half_19_10_φ3, half_19_10_φ4, half_19_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_19_10_φ1, half_19_10_φ2, half_19_10_φ3, half_19_10_φ4, half_19_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_19_10_φ1, half_19_10_φ2, half_19_10_φ3, half_19_10_φ4, half_19_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_14_10) (half_16_10)
    (by simpa only [half_19_10_φ5, show (2:ℝ)*16=32 by norm_num] using half_19_10_hx5)
  exact h.weaken (by norm_num [half_19_10_φ1, half_19_10_φ2, half_19_10_φ3, half_19_10_φ4, half_19_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_19_10_hx3 : SourcePowerBound (powerBoxCross 8 16 8 half_19_10_φ3) (85607879183/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 16) (u := 14) (t := 17)
    (D := 8) (ψ := (921955531/10000000000 : ℝ)) half_19_10_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_19_10_φ1, half_19_10_φ2, half_19_10_φ3, half_19_10_φ4, half_19_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_19_10_φ1, half_19_10_φ2, half_19_10_φ3, half_19_10_φ4, half_19_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_19_10_φ1, half_19_10_φ2, half_19_10_φ3, half_19_10_φ4, half_19_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_15_10) (half_17_10)
    (by simpa only [half_19_10_φ4, show (2:ℝ)*8=16 by norm_num] using half_19_10_hx4)
  exact h.weaken (by norm_num [half_19_10_φ1, half_19_10_φ2, half_19_10_φ3, half_19_10_φ4, half_19_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_19_10_hx2 : SourcePowerBound (powerBoxCross 8 17 4 half_19_10_φ2) (104739652847/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 17) (u := 15) (t := 18)
    (D := 4) (ψ := (1075614787/10000000000 : ℝ)) half_19_10_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_19_10_φ1, half_19_10_φ2, half_19_10_φ3, half_19_10_φ4, half_19_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_19_10_φ1, half_19_10_φ2, half_19_10_φ3, half_19_10_φ4, half_19_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_19_10_φ1, half_19_10_φ2, half_19_10_φ3, half_19_10_φ4, half_19_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_16_10) (half_18_10)
    (by simpa only [half_19_10_φ3, show (2:ℝ)*4=8 by norm_num] using half_19_10_hx3)
  exact h.weaken (by norm_num [half_19_10_φ1, half_19_10_φ2, half_19_10_φ3, half_19_10_φ4, half_19_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_19_10_hx1 : SourcePowerBound (powerBoxCross 8 18 2 half_19_10_φ1) (64407131149/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 18) (u := 16) (t := 19)
    (D := 2) (ψ := (1234112529/10000000000 : ℝ)) half_19_10_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_19_10_φ1, half_19_10_φ2, half_19_10_φ3, half_19_10_φ4, half_19_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_19_10_φ1, half_19_10_φ2, half_19_10_φ3, half_19_10_φ4, half_19_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_19_10_φ1, half_19_10_φ2, half_19_10_φ3, half_19_10_φ4, half_19_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_17_10) (half_19_09)
    (by simpa only [half_19_10_φ2, show (2:ℝ)*2=4 by norm_num] using half_19_10_hx2)
  exact h.weaken (by norm_num [half_19_10_φ1, half_19_10_φ2, half_19_10_φ3, half_19_10_φ4, half_19_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_19_10 : AdmissibleExponent 8 38 (75227240799/2500000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 17) (ψ := (30914599/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_18_10)
    (by simpa only [half_19_10_φ1] using half_19_10_hx1)
  exact admissibleExponent_mono h (by norm_num [half_19_10_φ1, half_19_10_φ2, half_19_10_φ3, half_19_10_φ4, half_19_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_20_10_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (38815549/312500000 : ℝ)

def half_20_10_φ2 : Fin 2 → ℝ := Fin.snoc half_20_10_φ1 (621383829/5000000000 : ℝ)

def half_20_10_φ3 : Fin 3 → ℝ := Fin.snoc half_20_10_φ2 (1073590681/10000000000 : ℝ)

def half_20_10_φ4 : Fin 4 → ℝ := Fin.snoc half_20_10_φ3 (115027573/1250000000 : ℝ)

def half_20_10_φ5 : Fin 5 → ℝ := Fin.snoc half_20_10_φ4 (1577521/20000000 : ℝ)

theorem half_20_10_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_20_10_φ5) (59383823189/10000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_20_10_φ5 (by norm_num [half_20_10_φ1, half_20_10_φ2, half_20_10_φ3, half_20_10_φ4, half_20_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_20_10_φ1, half_20_10_φ2, half_20_10_φ3, half_20_10_φ4, half_20_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_20_10_φ1, half_20_10_φ2, half_20_10_φ3, half_20_10_φ4, half_20_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_20_10_φ1, half_20_10_φ2, half_20_10_φ3, half_20_10_φ4, half_20_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_20_10_φ1, half_20_10_φ2, half_20_10_φ3, half_20_10_φ4, half_20_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_20_10_hx5 : SourcePowerBound (powerBoxCross 8 15 32 half_20_10_φ5) (5147668699/400000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 15) (r := 2) (v := 0) (w := 20) (D := 32)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_20_10_φ5 (by norm_num [half_20_10_φ1, half_20_10_φ2, half_20_10_φ3, half_20_10_φ4, half_20_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_20_10_φ1, half_20_10_φ2, half_20_10_φ3, half_20_10_φ4, half_20_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_20_10_hF2 (admissibleExponent_zero 8) (half_20_09)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_20_10_φ1, half_20_10_φ2, half_20_10_φ3, half_20_10_φ4, half_20_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_20_10_hx4 : SourcePowerBound (powerBoxCross 8 16 16 half_20_10_φ4) (152302487531/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 16) (u := 14) (t := 17)
    (D := 16) (ψ := (1577521/20000000 : ℝ)) half_20_10_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_20_10_φ1, half_20_10_φ2, half_20_10_φ3, half_20_10_φ4, half_20_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_20_10_φ1, half_20_10_φ2, half_20_10_φ3, half_20_10_φ4, half_20_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_20_10_φ1, half_20_10_φ2, half_20_10_φ3, half_20_10_φ4, half_20_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_15_10) (half_17_10)
    (by simpa only [half_20_10_φ5, show (2:ℝ)*16=32 by norm_num] using half_20_10_hx5)
  exact h.weaken (by norm_num [half_20_10_φ1, half_20_10_φ2, half_20_10_φ3, half_20_10_φ4, half_20_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_20_10_hx3 : SourcePowerBound (powerBoxCross 8 17 8 half_20_10_φ3) (1835151967/100000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 17) (u := 15) (t := 18)
    (D := 8) (ψ := (115027573/1250000000 : ℝ)) half_20_10_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_20_10_φ1, half_20_10_φ2, half_20_10_φ3, half_20_10_φ4, half_20_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_20_10_φ1, half_20_10_φ2, half_20_10_φ3, half_20_10_φ4, half_20_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_20_10_φ1, half_20_10_φ2, half_20_10_φ3, half_20_10_φ4, half_20_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_16_10) (half_18_10)
    (by simpa only [half_20_10_φ4, show (2:ℝ)*8=16 by norm_num] using half_20_10_hx4)
  exact h.weaken (by norm_num [half_20_10_φ1, half_20_10_φ2, half_20_10_φ3, half_20_10_φ4, half_20_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_20_10_hx2 : SourcePowerBound (powerBoxCross 8 18 4 half_20_10_φ2) (27980423369/1250000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 18) (u := 16) (t := 19)
    (D := 4) (ψ := (1073590681/10000000000 : ℝ)) half_20_10_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_20_10_φ1, half_20_10_φ2, half_20_10_φ3, half_20_10_φ4, half_20_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_20_10_φ1, half_20_10_φ2, half_20_10_φ3, half_20_10_φ4, half_20_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_20_10_φ1, half_20_10_φ2, half_20_10_φ3, half_20_10_φ4, half_20_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_17_10) (half_19_10)
    (by simpa only [half_20_10_φ3, show (2:ℝ)*4=8 by norm_num] using half_20_10_hx3)
  exact h.weaken (by norm_num [half_20_10_φ1, half_20_10_φ2, half_20_10_φ3, half_20_10_φ4, half_20_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_20_10_hx1 : SourcePowerBound (powerBoxCross 8 19 2 half_20_10_φ1) (274775231633/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 19) (u := 17) (t := 20)
    (D := 2) (ψ := (621383829/5000000000 : ℝ)) half_20_10_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_20_10_φ1, half_20_10_φ2, half_20_10_φ3, half_20_10_φ4, half_20_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_20_10_φ1, half_20_10_φ2, half_20_10_φ3, half_20_10_φ4, half_20_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_20_10_φ1, half_20_10_φ2, half_20_10_φ3, half_20_10_φ4, half_20_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_18_10) (half_20_09)
    (by simpa only [half_20_10_φ2, show (2:ℝ)*2=4 by norm_num] using half_20_10_hx2)
  exact h.weaken (by norm_num [half_20_10_φ1, half_20_10_φ2, half_20_10_φ3, half_20_10_φ4, half_20_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_20_10 : AdmissibleExponent 8 40 (320732841649/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 18) (ψ := (38815549/312500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_19_10)
    (by simpa only [half_20_10_φ1] using half_20_10_hx1)
  exact admissibleExponent_mono h (by norm_num [half_20_10_φ1, half_20_10_φ2, half_20_10_φ3, half_20_10_φ4, half_20_10_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_10_11_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (20632031/200000000 : ℝ)

def half_10_11_φ2 : Fin 2 → ℝ := Fin.snoc half_10_11_φ1 (192280891/2000000000 : ℝ)

def half_10_11_φ3 : Fin 3 → ℝ := Fin.snoc half_10_11_φ2 (52286309/625000000 : ℝ)

def half_10_11_φ4 : Fin 4 → ℝ := Fin.snoc half_10_11_φ3 (549002253/10000000000 : ℝ)

theorem half_10_11_hF2 : SourcePowerBound (paddedMoment 8 0 2 16 half_10_11_φ4) (34524813379/5000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 4) (r := 0) (n := 1) (D := 16)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_10_11_φ4 (by norm_num [half_10_11_φ1, half_10_11_φ2, half_10_11_φ3, half_10_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_11_φ1, half_10_11_φ2, half_10_11_φ3, half_10_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_11_φ1, half_10_11_φ2, half_10_11_φ3, half_10_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_10_11_φ1, half_10_11_φ2, half_10_11_φ3, half_10_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_10_11_φ1, half_10_11_φ2, half_10_11_φ3, half_10_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_10_11_hx4 : SourcePowerBound (powerBoxCross 8 6 16 half_10_11_φ4) (66142631581/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 6) (r := 2) (v := 0) (w := 8) (D := 16)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_10_11_φ4 (by norm_num [half_10_11_φ1, half_10_11_φ2, half_10_11_φ3, half_10_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_11_φ1, half_10_11_φ2, half_10_11_φ3, half_10_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_10_11_hF2 (admissibleExponent_zero 8) (SeedCompletionHigher8SimpleSeeds.degree8_half_8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_10_11_φ1, half_10_11_φ2, half_10_11_φ3, half_10_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_11_hx3 : SourcePowerBound (powerBoxCross 8 7 8 half_10_11_φ3) (38237983591/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 7) (u := 5) (t := 8)
    (D := 8) (ψ := (549002253/10000000000 : ℝ)) half_10_11_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_11_φ1, half_10_11_φ2, half_10_11_φ3, half_10_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_11_φ1, half_10_11_φ2, half_10_11_φ3, half_10_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_11_φ1, half_10_11_φ2, half_10_11_φ3, half_10_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionEven8SecondSeeds.degree8_half_6) (SeedCompletionHigher8SimpleSeeds.degree8_half_8)
    (by simpa only [half_10_11_φ4, show (2:ℝ)*8=16 by norm_num] using half_10_11_hx4)
  exact h.weaken (by norm_num [half_10_11_φ1, half_10_11_φ2, half_10_11_φ3, half_10_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_11_hx2 : SourcePowerBound (powerBoxCross 8 8 4 half_10_11_φ2) (11568991387/1250000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 8) (u := 6) (t := 9)
    (D := 4) (ψ := (52286309/625000000 : ℝ)) half_10_11_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_11_φ1, half_10_11_φ2, half_10_11_φ3, half_10_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_11_φ1, half_10_11_φ2, half_10_11_φ3, half_10_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_11_φ1, half_10_11_φ2, half_10_11_φ3, half_10_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_7) (SeedCompletionHigher8SimpleSeeds.degree8_half_9)
    (by simpa only [half_10_11_φ3, show (2:ℝ)*4=8 by norm_num] using half_10_11_hx3)
  exact h.weaken (by norm_num [half_10_11_φ1, half_10_11_φ2, half_10_11_φ3, half_10_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_11_hx1 : SourcePowerBound (powerBoxCross 8 9 2 half_10_11_φ1) (28436466351/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 9) (u := 7) (t := 10)
    (D := 2) (ψ := (192280891/2000000000 : ℝ)) half_10_11_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_11_φ1, half_10_11_φ2, half_10_11_φ3, half_10_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_11_φ1, half_10_11_φ2, half_10_11_φ3, half_10_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_11_φ1, half_10_11_φ2, half_10_11_φ3, half_10_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_8) (half_10_10)
    (by simpa only [half_10_11_φ2, show (2:ℝ)*2=4 by norm_num] using half_10_11_hx2)
  exact h.weaken (by norm_num [half_10_11_φ1, half_10_11_φ2, half_10_11_φ3, half_10_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_11 : AdmissibleExponent 8 20 (65641545877/5000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 8) (ψ := (20632031/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_9)
    (by simpa only [half_10_11_φ1] using half_10_11_hx1)
  exact admissibleExponent_mono h (by norm_num [half_10_11_φ1, half_10_11_φ2, half_10_11_φ3, half_10_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_11_11_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (134279771/1250000000 : ℝ)

def half_11_11_φ2 : Fin 2 → ℝ := Fin.snoc half_11_11_φ1 (1012239289/10000000000 : ℝ)

def half_11_11_φ3 : Fin 3 → ℝ := Fin.snoc half_11_11_φ2 (922291563/10000000000 : ℝ)

def half_11_11_φ4 : Fin 4 → ℝ := Fin.snoc half_11_11_φ3 (370236661/5000000000 : ℝ)

theorem half_11_11_hF2 : SourcePowerBound (paddedMoment 8 0 2 16 half_11_11_φ4) (30632955409/5000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 4) (r := 0) (n := 1) (D := 16)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_11_11_φ4 (by norm_num [half_11_11_φ1, half_11_11_φ2, half_11_11_φ3, half_11_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_11_φ1, half_11_11_φ2, half_11_11_φ3, half_11_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_11_φ1, half_11_11_φ2, half_11_11_φ3, half_11_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_11_11_φ1, half_11_11_φ2, half_11_11_φ3, half_11_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_11_11_φ1, half_11_11_φ2, half_11_11_φ3, half_11_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_11_11_hx4 : SourcePowerBound (powerBoxCross 8 7 16 half_11_11_φ4) (69947882/9765625 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 7) (r := 2) (v := 9) (w := 10) (D := 16)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_11_11_φ4 (by norm_num [half_11_11_φ1, half_11_11_φ2, half_11_11_φ3, half_11_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_11_φ1, half_11_11_φ2, half_11_11_φ3, half_11_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_11_11_hF2 (SeedCompletionHigher8SimpleSeeds.degree8_half_9) (half_10_11)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_11_11_φ1, half_11_11_φ2, half_11_11_φ3, half_11_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_11_hx3 : SourcePowerBound (powerBoxCross 8 8 8 half_11_11_φ3) (21282667899/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 8) (u := 6) (t := 9)
    (D := 8) (ψ := (370236661/5000000000 : ℝ)) half_11_11_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_11_φ1, half_11_11_φ2, half_11_11_φ3, half_11_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_11_φ1, half_11_11_φ2, half_11_11_φ3, half_11_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_11_φ1, half_11_11_φ2, half_11_11_φ3, half_11_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_7) (SeedCompletionHigher8SimpleSeeds.degree8_half_9)
    (by simpa only [half_11_11_φ4, show (2:ℝ)*8=16 by norm_num] using half_11_11_hx4)
  exact h.weaken (by norm_num [half_11_11_φ1, half_11_11_φ2, half_11_11_φ3, half_11_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_11_hx2 : SourcePowerBound (powerBoxCross 8 9 4 half_11_11_φ2) (104125436727/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 9) (u := 7) (t := 10)
    (D := 4) (ψ := (922291563/10000000000 : ℝ)) half_11_11_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_11_φ1, half_11_11_φ2, half_11_11_φ3, half_11_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_11_φ1, half_11_11_φ2, half_11_11_φ3, half_11_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_11_φ1, half_11_11_φ2, half_11_11_φ3, half_11_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_8) (half_10_11)
    (by simpa only [half_11_11_φ3, show (2:ℝ)*4=8 by norm_num] using half_11_11_hx3)
  exact h.weaken (by norm_num [half_11_11_φ1, half_11_11_φ2, half_11_11_φ3, half_11_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_11_hx1 : SourcePowerBound (powerBoxCross 8 10 2 half_11_11_φ1) (64127199563/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 10) (u := 8) (t := 11)
    (D := 2) (ψ := (1012239289/10000000000 : ℝ)) half_11_11_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_11_φ1, half_11_11_φ2, half_11_11_φ3, half_11_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_11_φ1, half_11_11_φ2, half_11_11_φ3, half_11_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_11_φ1, half_11_11_φ2, half_11_11_φ3, half_11_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_9) (half_11_10)
    (by simpa only [half_11_11_φ2, show (2:ℝ)*2=4 by norm_num] using half_11_11_hx2)
  exact h.weaken (by norm_num [half_11_11_φ1, half_11_11_φ2, half_11_11_φ3, half_11_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_11 : AdmissibleExponent 8 22 (74332462159/5000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 9) (ψ := (134279771/1250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_10_11)
    (by simpa only [half_11_11_φ1] using half_11_11_hx1)
  exact admissibleExponent_mono h (by norm_num [half_11_11_φ1, half_11_11_φ2, half_11_11_φ3, half_11_11_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_12_11_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (553494683/5000000000 : ℝ)

def half_12_11_φ2 : Fin 2 → ℝ := Fin.snoc half_12_11_φ1 (527775793/5000000000 : ℝ)

def half_12_11_φ3 : Fin 3 → ℝ := Fin.snoc half_12_11_φ2 (97703789/1000000000 : ℝ)

def half_12_11_φ4 : Fin 4 → ℝ := Fin.snoc half_12_11_φ3 (420997117/5000000000 : ℝ)

def half_12_11_φ5 : Fin 5 → ℝ := Fin.snoc half_12_11_φ4 (131989391/2500000000 : ℝ)

theorem half_12_11_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_12_11_φ5) (941248207/125000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_12_11_φ5 (by norm_num [half_12_11_φ1, half_12_11_φ2, half_12_11_φ3, half_12_11_φ4, half_12_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_11_φ1, half_12_11_φ2, half_12_11_φ3, half_12_11_φ4, half_12_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_11_φ1, half_12_11_φ2, half_12_11_φ3, half_12_11_φ4, half_12_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_12_11_φ1, half_12_11_φ2, half_12_11_φ3, half_12_11_φ4, half_12_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_12_11_φ1, half_12_11_φ2, half_12_11_φ3, half_12_11_φ4, half_12_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_12_11_hx5 : SourcePowerBound (powerBoxCross 8 7 32 half_12_11_φ5) (8535754471/1250000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 7) (r := 2) (v := 9) (w := 10) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_12_11_φ5 (by norm_num [half_12_11_φ1, half_12_11_φ2, half_12_11_φ3, half_12_11_φ4, half_12_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_11_φ1, half_12_11_φ2, half_12_11_φ3, half_12_11_φ4, half_12_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_12_11_hF2 (SeedCompletionHigher8SimpleSeeds.degree8_half_9) (half_10_11)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_12_11_φ1, half_12_11_φ2, half_12_11_φ3, half_12_11_φ4, half_12_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_11_hx4 : SourcePowerBound (powerBoxCross 8 8 16 half_12_11_φ4) (7810348843/1000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 8) (u := 6) (t := 9)
    (D := 16) (ψ := (131989391/2500000000 : ℝ)) half_12_11_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_11_φ1, half_12_11_φ2, half_12_11_φ3, half_12_11_φ4, half_12_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_11_φ1, half_12_11_φ2, half_12_11_φ3, half_12_11_φ4, half_12_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_11_φ1, half_12_11_φ2, half_12_11_φ3, half_12_11_φ4, half_12_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_7) (SeedCompletionHigher8SimpleSeeds.degree8_half_9)
    (by simpa only [half_12_11_φ5, show (2:ℝ)*16=32 by norm_num] using half_12_11_hx5)
  exact h.weaken (by norm_num [half_12_11_φ1, half_12_11_φ2, half_12_11_φ3, half_12_11_φ4, half_12_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_11_hx3 : SourcePowerBound (powerBoxCross 8 9 8 half_12_11_φ3) (94411040041/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 9) (u := 7) (t := 10)
    (D := 8) (ψ := (420997117/5000000000 : ℝ)) half_12_11_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_11_φ1, half_12_11_φ2, half_12_11_φ3, half_12_11_φ4, half_12_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_11_φ1, half_12_11_φ2, half_12_11_φ3, half_12_11_φ4, half_12_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_11_φ1, half_12_11_φ2, half_12_11_φ3, half_12_11_φ4, half_12_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_8) (half_10_11)
    (by simpa only [half_12_11_φ4, show (2:ℝ)*8=16 by norm_num] using half_12_11_hx4)
  exact h.weaken (by norm_num [half_12_11_φ1, half_12_11_φ2, half_12_11_φ3, half_12_11_φ4, half_12_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_11_hx2 : SourcePowerBound (powerBoxCross 8 10 4 half_12_11_φ2) (23239842313/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 10) (u := 8) (t := 11)
    (D := 4) (ψ := (97703789/1000000000 : ℝ)) half_12_11_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_11_φ1, half_12_11_φ2, half_12_11_φ3, half_12_11_φ4, half_12_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_11_φ1, half_12_11_φ2, half_12_11_φ3, half_12_11_φ4, half_12_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_11_φ1, half_12_11_φ2, half_12_11_φ3, half_12_11_φ4, half_12_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_9) (half_11_11)
    (by simpa only [half_12_11_φ3, show (2:ℝ)*4=8 by norm_num] using half_12_11_hx3)
  exact h.weaken (by norm_num [half_12_11_φ1, half_12_11_φ2, half_12_11_φ3, half_12_11_φ4, half_12_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_11_hx1 : SourcePowerBound (powerBoxCross 8 11 2 half_12_11_φ1) (71657432327/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 11) (u := 9) (t := 12)
    (D := 2) (ψ := (527775793/5000000000 : ℝ)) half_12_11_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_11_φ1, half_12_11_φ2, half_12_11_φ3, half_12_11_φ4, half_12_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_11_φ1, half_12_11_φ2, half_12_11_φ3, half_12_11_φ4, half_12_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_11_φ1, half_12_11_φ2, half_12_11_φ3, half_12_11_φ4, half_12_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_10_11) (half_12_10)
    (by simpa only [half_12_11_φ2, show (2:ℝ)*2=4 by norm_num] using half_12_11_hx2)
  exact h.weaken (by norm_num [half_12_11_φ1, half_12_11_φ2, half_12_11_φ3, half_12_11_φ4, half_12_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_11 : AdmissibleExponent 8 24 (8328082067/500000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 10) (ψ := (553494683/5000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_11_11)
    (by simpa only [half_12_11_φ1] using half_12_11_hx1)
  exact admissibleExponent_mono h (by norm_num [half_12_11_φ1, half_12_11_φ2, half_12_11_φ3, half_12_11_φ4, half_12_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_13_11_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (56784087/500000000 : ℝ)

def half_13_11_φ2 : Fin 2 → ℝ := Fin.snoc half_13_11_φ1 (545080461/5000000000 : ℝ)

def half_13_11_φ3 : Fin 3 → ℝ := Fin.snoc half_13_11_φ2 (1024827171/10000000000 : ℝ)

def half_13_11_φ4 : Fin 4 → ℝ := Fin.snoc half_13_11_φ3 (456193663/5000000000 : ℝ)

def half_13_11_φ5 : Fin 5 → ℝ := Fin.snoc half_13_11_φ4 (342427799/5000000000 : ℝ)

theorem half_13_11_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_13_11_φ5) (68193832103/10000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_13_11_φ5 (by norm_num [half_13_11_φ1, half_13_11_φ2, half_13_11_φ3, half_13_11_φ4, half_13_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_11_φ1, half_13_11_φ2, half_13_11_φ3, half_13_11_φ4, half_13_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_11_φ1, half_13_11_φ2, half_13_11_φ3, half_13_11_φ4, half_13_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_13_11_φ1, half_13_11_φ2, half_13_11_φ3, half_13_11_φ4, half_13_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_13_11_φ1, half_13_11_φ2, half_13_11_φ3, half_13_11_φ4, half_13_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_13_11_hx5 : SourcePowerBound (powerBoxCross 8 8 32 half_13_11_φ5) (14450947917/2000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 8) (r := 2) (v := 10) (w := 11) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_13_11_φ5 (by norm_num [half_13_11_φ1, half_13_11_φ2, half_13_11_φ3, half_13_11_φ4, half_13_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_11_φ1, half_13_11_φ2, half_13_11_φ3, half_13_11_φ4, half_13_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_13_11_hF2 (half_10_11) (half_11_11)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_13_11_φ1, half_13_11_φ2, half_13_11_φ3, half_13_11_φ4, half_13_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_11_hx4 : SourcePowerBound (powerBoxCross 8 9 16 half_13_11_φ4) (1700153637/200000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 9) (u := 7) (t := 10)
    (D := 16) (ψ := (342427799/5000000000 : ℝ)) half_13_11_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_11_φ1, half_13_11_φ2, half_13_11_φ3, half_13_11_φ4, half_13_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_11_φ1, half_13_11_φ2, half_13_11_φ3, half_13_11_φ4, half_13_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_11_φ1, half_13_11_φ2, half_13_11_φ3, half_13_11_φ4, half_13_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_8) (half_10_11)
    (by simpa only [half_13_11_φ5, show (2:ℝ)*16=32 by norm_num] using half_13_11_hx5)
  exact h.weaken (by norm_num [half_13_11_φ1, half_13_11_φ2, half_13_11_φ3, half_13_11_φ4, half_13_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_11_hx3 : SourcePowerBound (powerBoxCross 8 10 8 half_13_11_φ3) (20810244341/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 10) (u := 8) (t := 11)
    (D := 8) (ψ := (456193663/5000000000 : ℝ)) half_13_11_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_11_φ1, half_13_11_φ2, half_13_11_φ3, half_13_11_φ4, half_13_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_11_φ1, half_13_11_φ2, half_13_11_φ3, half_13_11_φ4, half_13_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_11_φ1, half_13_11_φ2, half_13_11_φ3, half_13_11_φ4, half_13_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_9) (half_11_11)
    (by simpa only [half_13_11_φ4, show (2:ℝ)*8=16 by norm_num] using half_13_11_hx4)
  exact h.weaken (by norm_num [half_13_11_φ1, half_13_11_φ2, half_13_11_φ3, half_13_11_φ4, half_13_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_11_hx2 : SourcePowerBound (powerBoxCross 8 11 4 half_13_11_φ2) (128714839973/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 11) (u := 9) (t := 12)
    (D := 4) (ψ := (1024827171/10000000000 : ℝ)) half_13_11_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_11_φ1, half_13_11_φ2, half_13_11_φ3, half_13_11_φ4, half_13_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_11_φ1, half_13_11_φ2, half_13_11_φ3, half_13_11_φ4, half_13_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_11_φ1, half_13_11_φ2, half_13_11_φ3, half_13_11_φ4, half_13_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_10_11) (half_12_11)
    (by simpa only [half_13_11_φ3, show (2:ℝ)*4=8 by norm_num] using half_13_11_hx3)
  exact h.weaken (by norm_num [half_13_11_φ1, half_13_11_φ2, half_13_11_φ3, half_13_11_φ4, half_13_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_11_hx1 : SourcePowerBound (powerBoxCross 8 12 2 half_13_11_φ1) (158781221617/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 12) (u := 10) (t := 13)
    (D := 2) (ψ := (545080461/5000000000 : ℝ)) half_13_11_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_11_φ1, half_13_11_φ2, half_13_11_φ3, half_13_11_φ4, half_13_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_11_φ1, half_13_11_φ2, half_13_11_φ3, half_13_11_φ4, half_13_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_11_φ1, half_13_11_φ2, half_13_11_φ3, half_13_11_φ4, half_13_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_11_11) (half_13_10)
    (by simpa only [half_13_11_φ2, show (2:ℝ)*2=4 by norm_num] using half_13_11_hx2)
  exact h.weaken (by norm_num [half_13_11_φ1, half_13_11_φ2, half_13_11_φ3, half_13_11_φ4, half_13_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_11 : AdmissibleExponent 8 26 (184901901637/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 11) (ψ := (56784087/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_12_11)
    (by simpa only [half_13_11_φ1] using half_13_11_hx1)
  exact admissibleExponent_mono h (by norm_num [half_13_11_φ1, half_13_11_φ2, half_13_11_φ3, half_13_11_φ4, half_13_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_14_11_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (46489763/400000000 : ℝ)

def half_14_11_φ2 : Fin 2 → ℝ := Fin.snoc half_14_11_φ1 (140444297/1250000000 : ℝ)

def half_14_11_φ3 : Fin 3 → ℝ := Fin.snoc half_14_11_φ2 (535130279/5000000000 : ℝ)

def half_14_11_φ4 : Fin 4 → ℝ := Fin.snoc half_14_11_φ3 (949134427/10000000000 : ℝ)

def half_14_11_φ5 : Fin 5 → ℝ := Fin.snoc half_14_11_φ4 (406771897/5000000000 : ℝ)

theorem half_14_11_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_14_11_φ5) (6250651817/1000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_14_11_φ5 (by norm_num [half_14_11_φ1, half_14_11_φ2, half_14_11_φ3, half_14_11_φ4, half_14_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_11_φ1, half_14_11_φ2, half_14_11_φ3, half_14_11_φ4, half_14_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_11_φ1, half_14_11_φ2, half_14_11_φ3, half_14_11_φ4, half_14_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_14_11_φ1, half_14_11_φ2, half_14_11_φ3, half_14_11_φ4, half_14_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_14_11_φ1, half_14_11_φ2, half_14_11_φ3, half_14_11_φ4, half_14_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_14_11_hx5 : SourcePowerBound (powerBoxCross 8 9 32 half_14_11_φ5) (9575495619/1250000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 9) (r := 2) (v := 0) (w := 12) (D := 32)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_14_11_φ5 (by norm_num [half_14_11_φ1, half_14_11_φ2, half_14_11_φ3, half_14_11_φ4, half_14_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_11_φ1, half_14_11_φ2, half_14_11_φ3, half_14_11_φ4, half_14_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_14_11_hF2 (admissibleExponent_zero 8) (half_12_11)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_14_11_φ1, half_14_11_φ2, half_14_11_φ3, half_14_11_φ4, half_14_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_11_hx4 : SourcePowerBound (powerBoxCross 8 10 16 half_14_11_φ4) (46239913521/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 10) (u := 8) (t := 11)
    (D := 16) (ψ := (406771897/5000000000 : ℝ)) half_14_11_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_11_φ1, half_14_11_φ2, half_14_11_φ3, half_14_11_φ4, half_14_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_11_φ1, half_14_11_φ2, half_14_11_φ3, half_14_11_φ4, half_14_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_11_φ1, half_14_11_φ2, half_14_11_φ3, half_14_11_φ4, half_14_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_9) (half_11_11)
    (by simpa only [half_14_11_φ5, show (2:ℝ)*16=32 by norm_num] using half_14_11_hx5)
  exact h.weaken (by norm_num [half_14_11_φ1, half_14_11_φ2, half_14_11_φ3, half_14_11_φ4, half_14_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_11_hx3 : SourcePowerBound (powerBoxCross 8 11 8 half_14_11_φ3) (28460442467/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 11) (u := 9) (t := 12)
    (D := 8) (ψ := (949134427/10000000000 : ℝ)) half_14_11_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_11_φ1, half_14_11_φ2, half_14_11_φ3, half_14_11_φ4, half_14_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_11_φ1, half_14_11_φ2, half_14_11_φ3, half_14_11_φ4, half_14_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_11_φ1, half_14_11_φ2, half_14_11_φ3, half_14_11_φ4, half_14_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_10_11) (half_12_11)
    (by simpa only [half_14_11_φ4, show (2:ℝ)*8=16 by norm_num] using half_14_11_hx4)
  exact h.weaken (by norm_num [half_14_11_φ1, half_14_11_φ2, half_14_11_φ3, half_14_11_φ4, half_14_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_11_hx2 : SourcePowerBound (powerBoxCross 8 12 4 half_14_11_φ2) (17684606627/1250000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 12) (u := 10) (t := 13)
    (D := 4) (ψ := (535130279/5000000000 : ℝ)) half_14_11_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_11_φ1, half_14_11_φ2, half_14_11_φ3, half_14_11_φ4, half_14_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_11_φ1, half_14_11_φ2, half_14_11_φ3, half_14_11_φ4, half_14_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_11_φ1, half_14_11_φ2, half_14_11_φ3, half_14_11_φ4, half_14_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_11_11) (half_13_11)
    (by simpa only [half_14_11_φ3, show (2:ℝ)*4=8 by norm_num] using half_14_11_hx3)
  exact h.weaken (by norm_num [half_14_11_φ1, half_14_11_φ2, half_14_11_φ3, half_14_11_φ4, half_14_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_11_hx1 : SourcePowerBound (powerBoxCross 8 13 2 half_14_11_φ1) (174574031757/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 13) (u := 11) (t := 14)
    (D := 2) (ψ := (140444297/1250000000 : ℝ)) half_14_11_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_11_φ1, half_14_11_φ2, half_14_11_φ3, half_14_11_φ4, half_14_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_11_φ1, half_14_11_φ2, half_14_11_φ3, half_14_11_φ4, half_14_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_11_φ1, half_14_11_φ2, half_14_11_φ3, half_14_11_φ4, half_14_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_12_11) (half_14_10)
    (by simpa only [half_14_11_φ2, show (2:ℝ)*2=4 by norm_num] using half_14_11_hx2)
  exact h.weaken (by norm_num [half_14_11_φ1, half_14_11_φ2, half_14_11_φ3, half_14_11_φ4, half_14_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_11 : AdmissibleExponent 8 28 (1590860419/78125000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 12) (ψ := (46489763/400000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_13_11)
    (by simpa only [half_14_11_φ1] using half_14_11_hx1)
  exact admissibleExponent_mono h (by norm_num [half_14_11_φ1, half_14_11_φ2, half_14_11_φ3, half_14_11_φ4, half_14_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_15_11_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1186543229/10000000000 : ℝ)

def half_15_11_φ2 : Fin 2 → ℝ := Fin.snoc half_15_11_φ1 (1156909387/10000000000 : ℝ)

def half_15_11_φ3 : Fin 3 → ℝ := Fin.snoc half_15_11_φ2 (1093792483/10000000000 : ℝ)

def half_15_11_φ4 : Fin 4 → ℝ := Fin.snoc half_15_11_φ3 (468768207/5000000000 : ℝ)

def half_15_11_φ5 : Fin 5 → ℝ := Fin.snoc half_15_11_φ4 (10045033/125000000 : ℝ)

theorem half_15_11_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_15_11_φ5) (61253932787/10000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_15_11_φ5 (by norm_num [half_15_11_φ1, half_15_11_φ2, half_15_11_φ3, half_15_11_φ4, half_15_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_11_φ1, half_15_11_φ2, half_15_11_φ3, half_15_11_φ4, half_15_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_11_φ1, half_15_11_φ2, half_15_11_φ3, half_15_11_φ4, half_15_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_15_11_φ1, half_15_11_φ2, half_15_11_φ3, half_15_11_φ4, half_15_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_15_11_φ1, half_15_11_φ2, half_15_11_φ3, half_15_11_φ4, half_15_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_15_11_hx5 : SourcePowerBound (powerBoxCross 8 10 32 half_15_11_φ5) (21108859283/2500000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 10) (r := 2) (v := 13) (w := 14) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_15_11_φ5 (by norm_num [half_15_11_φ1, half_15_11_φ2, half_15_11_φ3, half_15_11_φ4, half_15_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_11_φ1, half_15_11_φ2, half_15_11_φ3, half_15_11_φ4, half_15_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_15_11_hF2 (half_13_11) (half_14_11)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_15_11_φ1, half_15_11_φ2, half_15_11_φ3, half_15_11_φ4, half_15_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_11_hx4 : SourcePowerBound (powerBoxCross 8 11 16 half_15_11_φ4) (25346872389/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 11) (u := 9) (t := 12)
    (D := 16) (ψ := (10045033/125000000 : ℝ)) half_15_11_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_11_φ1, half_15_11_φ2, half_15_11_φ3, half_15_11_φ4, half_15_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_11_φ1, half_15_11_φ2, half_15_11_φ3, half_15_11_φ4, half_15_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_11_φ1, half_15_11_φ2, half_15_11_φ3, half_15_11_φ4, half_15_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_10_11) (half_12_11)
    (by simpa only [half_15_11_φ5, show (2:ℝ)*16=32 by norm_num] using half_15_11_hx5)
  exact h.weaken (by norm_num [half_15_11_φ1, half_15_11_φ2, half_15_11_φ3, half_15_11_φ4, half_15_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_11_hx3 : SourcePowerBound (powerBoxCross 8 12 8 half_15_11_φ3) (62090406169/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 12) (u := 10) (t := 13)
    (D := 8) (ψ := (468768207/5000000000 : ℝ)) half_15_11_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_11_φ1, half_15_11_φ2, half_15_11_φ3, half_15_11_φ4, half_15_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_11_φ1, half_15_11_φ2, half_15_11_φ3, half_15_11_φ4, half_15_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_11_φ1, half_15_11_φ2, half_15_11_φ3, half_15_11_φ4, half_15_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_11_11) (half_13_11)
    (by simpa only [half_15_11_φ4, show (2:ℝ)*8=16 by norm_num] using half_15_11_hx4)
  exact h.weaken (by norm_num [half_15_11_φ1, half_15_11_φ2, half_15_11_φ3, half_15_11_φ4, half_15_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_11_hx2 : SourcePowerBound (powerBoxCross 8 13 4 half_15_11_φ2) (38605530979/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 13) (u := 11) (t := 14)
    (D := 4) (ψ := (1093792483/10000000000 : ℝ)) half_15_11_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_11_φ1, half_15_11_φ2, half_15_11_φ3, half_15_11_φ4, half_15_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_11_φ1, half_15_11_φ2, half_15_11_φ3, half_15_11_φ4, half_15_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_11_φ1, half_15_11_φ2, half_15_11_φ3, half_15_11_φ4, half_15_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_12_11) (half_14_11)
    (by simpa only [half_15_11_φ3, show (2:ℝ)*4=8 by norm_num] using half_15_11_hx3)
  exact h.weaken (by norm_num [half_15_11_φ1, half_15_11_φ2, half_15_11_φ3, half_15_11_φ4, half_15_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_11_hx1 : SourcePowerBound (powerBoxCross 8 14 2 half_15_11_φ1) (190655081241/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 14) (u := 12) (t := 15)
    (D := 2) (ψ := (1156909387/10000000000 : ℝ)) half_15_11_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_11_φ1, half_15_11_φ2, half_15_11_φ3, half_15_11_φ4, half_15_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_11_φ1, half_15_11_φ2, half_15_11_φ3, half_15_11_φ4, half_15_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_11_φ1, half_15_11_φ2, half_15_11_φ3, half_15_11_φ4, half_15_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_13_11) (half_15_10)
    (by simpa only [half_15_11_φ2, show (2:ℝ)*2=4 by norm_num] using half_15_11_hx2)
  exact h.weaken (by norm_num [half_15_11_φ1, half_15_11_φ2, half_15_11_φ3, half_15_11_φ4, half_15_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_11 : AdmissibleExponent 8 30 (27836468553/1250000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 13) (ψ := (1186543229/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_14_11)
    (by simpa only [half_15_11_φ1] using half_15_11_hx1)
  exact admissibleExponent_mono h (by norm_num [half_15_11_φ1, half_15_11_φ2, half_15_11_φ3, half_15_11_φ4, half_15_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_16_11_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (602376351/5000000000 : ℝ)

def half_16_11_φ2 : Fin 2 → ℝ := Fin.snoc half_16_11_φ1 (296280347/2500000000 : ℝ)

def half_16_11_φ3 : Fin 3 → ℝ := Fin.snoc half_16_11_φ2 (271790211/2500000000 : ℝ)

def half_16_11_φ4 : Fin 4 → ℝ := Fin.snoc half_16_11_φ3 (116481519/1250000000 : ℝ)

def half_16_11_φ5 : Fin 5 → ℝ := Fin.snoc half_16_11_φ4 (49920651/625000000 : ℝ)

theorem half_16_11_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_16_11_φ5) (30320016229/5000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_16_11_φ5 (by norm_num [half_16_11_φ1, half_16_11_φ2, half_16_11_φ3, half_16_11_φ4, half_16_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_11_φ1, half_16_11_φ2, half_16_11_φ3, half_16_11_φ4, half_16_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_11_φ1, half_16_11_φ2, half_16_11_φ3, half_16_11_φ4, half_16_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_16_11_φ1, half_16_11_φ2, half_16_11_φ3, half_16_11_φ4, half_16_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_16_11_φ1, half_16_11_φ2, half_16_11_φ3, half_16_11_φ4, half_16_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_16_11_hx5 : SourcePowerBound (powerBoxCross 8 11 32 half_16_11_φ5) (92918047207/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 11) (r := 2) (v := 14) (w := 15) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_16_11_φ5 (by norm_num [half_16_11_φ1, half_16_11_φ2, half_16_11_φ3, half_16_11_φ4, half_16_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_11_φ1, half_16_11_φ2, half_16_11_φ3, half_16_11_φ4, half_16_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_16_11_hF2 (half_14_11) (half_15_11)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_16_11_φ1, half_16_11_φ2, half_16_11_φ3, half_16_11_φ4, half_16_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_11_hx4 : SourcePowerBound (powerBoxCross 8 12 16 half_16_11_φ4) (55552479337/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 12) (u := 10) (t := 13)
    (D := 16) (ψ := (49920651/625000000 : ℝ)) half_16_11_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_11_φ1, half_16_11_φ2, half_16_11_φ3, half_16_11_φ4, half_16_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_11_φ1, half_16_11_φ2, half_16_11_φ3, half_16_11_φ4, half_16_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_11_φ1, half_16_11_φ2, half_16_11_φ3, half_16_11_φ4, half_16_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_11_11) (half_13_11)
    (by simpa only [half_16_11_φ5, show (2:ℝ)*16=32 by norm_num] using half_16_11_hx5)
  exact h.weaken (by norm_num [half_16_11_φ1, half_16_11_φ2, half_16_11_φ3, half_16_11_φ4, half_16_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_11_hx3 : SourcePowerBound (powerBoxCross 8 13 8 half_16_11_φ3) (6775638461/500000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 13) (u := 11) (t := 14)
    (D := 8) (ψ := (116481519/1250000000 : ℝ)) half_16_11_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_11_φ1, half_16_11_φ2, half_16_11_φ3, half_16_11_φ4, half_16_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_11_φ1, half_16_11_φ2, half_16_11_φ3, half_16_11_φ4, half_16_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_11_φ1, half_16_11_φ2, half_16_11_φ3, half_16_11_φ4, half_16_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_12_11) (half_14_11)
    (by simpa only [half_16_11_φ4, show (2:ℝ)*8=16 by norm_num] using half_16_11_hx4)
  exact h.weaken (by norm_num [half_16_11_φ1, half_16_11_φ2, half_16_11_φ3, half_16_11_φ4, half_16_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_11_hx2 : SourcePowerBound (powerBoxCross 8 14 4 half_16_11_φ2) (167716948077/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 14) (u := 12) (t := 15)
    (D := 4) (ψ := (271790211/2500000000 : ℝ)) half_16_11_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_11_φ1, half_16_11_φ2, half_16_11_φ3, half_16_11_φ4, half_16_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_11_φ1, half_16_11_φ2, half_16_11_φ3, half_16_11_φ4, half_16_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_11_φ1, half_16_11_φ2, half_16_11_φ3, half_16_11_φ4, half_16_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_13_11) (half_15_11)
    (by simpa only [half_16_11_φ3, show (2:ℝ)*4=8 by norm_num] using half_16_11_hx3)
  exact h.weaken (by norm_num [half_16_11_φ1, half_16_11_φ2, half_16_11_φ3, half_16_11_φ4, half_16_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_11_hx1 : SourcePowerBound (powerBoxCross 8 15 2 half_16_11_φ1) (51766913143/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 15) (u := 13) (t := 16)
    (D := 2) (ψ := (296280347/2500000000 : ℝ)) half_16_11_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_11_φ1, half_16_11_φ2, half_16_11_φ3, half_16_11_φ4, half_16_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_11_φ1, half_16_11_φ2, half_16_11_φ3, half_16_11_φ4, half_16_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_11_φ1, half_16_11_φ2, half_16_11_φ3, half_16_11_φ4, half_16_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_14_11) (half_16_10)
    (by simpa only [half_16_11_φ2, show (2:ℝ)*2=4 by norm_num] using half_16_11_hx2)
  exact h.weaken (by norm_num [half_16_11_φ1, half_16_11_φ2, half_16_11_φ3, half_16_11_φ4, half_16_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_11 : AdmissibleExponent 8 32 (24200548093/1000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 14) (ψ := (602376351/5000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_15_11)
    (by simpa only [half_16_11_φ1] using half_16_11_hx1)
  exact admissibleExponent_mono h (by norm_num [half_16_11_φ1, half_16_11_φ2, half_16_11_φ3, half_16_11_φ4, half_16_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_17_11_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1218408751/10000000000 : ℝ)

def half_17_11_φ2 : Fin 2 → ℝ := Fin.snoc half_17_11_φ1 (75381057/625000000 : ℝ)

def half_17_11_φ3 : Fin 3 → ℝ := Fin.snoc half_17_11_φ2 (270553369/2500000000 : ℝ)

def half_17_11_φ4 : Fin 4 → ℝ := Fin.snoc half_17_11_φ3 (927611551/10000000000 : ℝ)

def half_17_11_φ5 : Fin 5 → ℝ := Fin.snoc half_17_11_φ4 (159019123/2000000000 : ℝ)

theorem half_17_11_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_17_11_φ5) (12036409519/2000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_17_11_φ5 (by norm_num [half_17_11_φ1, half_17_11_φ2, half_17_11_φ3, half_17_11_φ4, half_17_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_11_φ1, half_17_11_φ2, half_17_11_φ3, half_17_11_φ4, half_17_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_11_φ1, half_17_11_φ2, half_17_11_φ3, half_17_11_φ4, half_17_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_17_11_φ1, half_17_11_φ2, half_17_11_φ3, half_17_11_φ4, half_17_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_17_11_φ1, half_17_11_φ2, half_17_11_φ3, half_17_11_φ4, half_17_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_17_11_hx5 : SourcePowerBound (powerBoxCross 8 12 32 half_17_11_φ5) (50816692751/5000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 12) (r := 2) (v := 0) (w := 16) (D := 32)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_17_11_φ5 (by norm_num [half_17_11_φ1, half_17_11_φ2, half_17_11_φ3, half_17_11_φ4, half_17_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_11_φ1, half_17_11_φ2, half_17_11_φ3, half_17_11_φ4, half_17_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_17_11_hF2 (admissibleExponent_zero 8) (half_16_11)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_17_11_φ1, half_17_11_φ2, half_17_11_φ3, half_17_11_φ4, half_17_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_11_hx4 : SourcePowerBound (powerBoxCross 8 13 16 half_17_11_φ4) (1892297409/156250000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 13) (u := 11) (t := 14)
    (D := 16) (ψ := (159019123/2000000000 : ℝ)) half_17_11_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_11_φ1, half_17_11_φ2, half_17_11_φ3, half_17_11_φ4, half_17_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_11_φ1, half_17_11_φ2, half_17_11_φ3, half_17_11_φ4, half_17_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_11_φ1, half_17_11_φ2, half_17_11_φ3, half_17_11_φ4, half_17_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_12_11) (half_14_11)
    (by simpa only [half_17_11_φ5, show (2:ℝ)*16=32 by norm_num] using half_17_11_hx5)
  exact h.weaken (by norm_num [half_17_11_φ1, half_17_11_φ2, half_17_11_φ3, half_17_11_φ4, half_17_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_11_hx3 : SourcePowerBound (powerBoxCross 8 14 8 half_17_11_φ3) (147175147887/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 14) (u := 12) (t := 15)
    (D := 8) (ψ := (927611551/10000000000 : ℝ)) half_17_11_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_11_φ1, half_17_11_φ2, half_17_11_φ3, half_17_11_φ4, half_17_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_11_φ1, half_17_11_φ2, half_17_11_φ3, half_17_11_φ4, half_17_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_11_φ1, half_17_11_φ2, half_17_11_φ3, half_17_11_φ4, half_17_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_13_11) (half_15_11)
    (by simpa only [half_17_11_φ4, show (2:ℝ)*8=16 by norm_num] using half_17_11_hx4)
  exact h.weaken (by norm_num [half_17_11_φ1, half_17_11_φ2, half_17_11_φ3, half_17_11_φ4, half_17_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_11_hx2 : SourcePowerBound (powerBoxCross 8 15 4 half_17_11_φ2) (36275448713/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 15) (u := 13) (t := 16)
    (D := 4) (ψ := (270553369/2500000000 : ℝ)) half_17_11_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_11_φ1, half_17_11_φ2, half_17_11_φ3, half_17_11_φ4, half_17_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_11_φ1, half_17_11_φ2, half_17_11_φ3, half_17_11_φ4, half_17_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_11_φ1, half_17_11_φ2, half_17_11_φ3, half_17_11_φ4, half_17_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_14_11) (half_16_11)
    (by simpa only [half_17_11_φ3, show (2:ℝ)*4=8 by norm_num] using half_17_11_hx3)
  exact h.weaken (by norm_num [half_17_11_φ1, half_17_11_φ2, half_17_11_φ3, half_17_11_φ4, half_17_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_11_hx1 : SourcePowerBound (powerBoxCross 8 16 2 half_17_11_φ1) (223737730109/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 16) (u := 14) (t := 17)
    (D := 2) (ψ := (75381057/625000000 : ℝ)) half_17_11_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_11_φ1, half_17_11_φ2, half_17_11_φ3, half_17_11_φ4, half_17_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_11_φ1, half_17_11_φ2, half_17_11_φ3, half_17_11_φ4, half_17_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_11_φ1, half_17_11_φ2, half_17_11_φ3, half_17_11_φ4, half_17_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_15_11) (half_17_10)
    (by simpa only [half_17_11_φ2, show (2:ℝ)*2=4 by norm_num] using half_17_11_hx2)
  exact h.weaken (by norm_num [half_17_11_φ1, half_17_11_φ2, half_17_11_φ3, half_17_11_φ4, half_17_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_11 : AdmissibleExponent 8 34 (26150840139/1000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 15) (ψ := (1218408751/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_16_11)
    (by simpa only [half_17_11_φ1] using half_17_11_hx1)
  exact admissibleExponent_mono h (by norm_num [half_17_11_φ1, half_17_11_φ2, half_17_11_φ3, half_17_11_φ4, half_17_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_18_11_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1228880477/10000000000 : ℝ)

def half_18_11_φ2 : Fin 2 → ℝ := Fin.snoc half_18_11_φ1 (611065069/5000000000 : ℝ)

def half_18_11_φ3 : Fin 3 → ℝ := Fin.snoc half_18_11_φ2 (539213527/5000000000 : ℝ)

def half_18_11_φ4 : Fin 4 → ℝ := Fin.snoc half_18_11_φ3 (462183023/5000000000 : ℝ)

def half_18_11_φ5 : Fin 5 → ℝ := Fin.snoc half_18_11_φ4 (396156877/5000000000 : ℝ)

theorem half_18_11_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_18_11_φ5) (59831533151/10000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_18_11_φ5 (by norm_num [half_18_11_φ1, half_18_11_φ2, half_18_11_φ3, half_18_11_φ4, half_18_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_18_11_φ1, half_18_11_φ2, half_18_11_φ3, half_18_11_φ4, half_18_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_18_11_φ1, half_18_11_φ2, half_18_11_φ3, half_18_11_φ4, half_18_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_18_11_φ1, half_18_11_φ2, half_18_11_φ3, half_18_11_φ4, half_18_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_18_11_φ1, half_18_11_φ2, half_18_11_φ3, half_18_11_φ4, half_18_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_18_11_hx5 : SourcePowerBound (powerBoxCross 8 13 32 half_18_11_φ5) (27632974687/2500000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 13) (r := 2) (v := 17) (w := 18) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_18_11_φ5 (by norm_num [half_18_11_φ1, half_18_11_φ2, half_18_11_φ3, half_18_11_φ4, half_18_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_18_11_φ1, half_18_11_φ2, half_18_11_φ3, half_18_11_φ4, half_18_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_18_11_hF2 (half_17_11) (half_18_10)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_18_11_φ1, half_18_11_φ2, half_18_11_φ3, half_18_11_φ4, half_18_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_18_11_hx4 : SourcePowerBound (powerBoxCross 8 14 16 half_18_11_φ4) (131336165687/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 14) (u := 12) (t := 15)
    (D := 16) (ψ := (396156877/5000000000 : ℝ)) half_18_11_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_18_11_φ1, half_18_11_φ2, half_18_11_φ3, half_18_11_φ4, half_18_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_18_11_φ1, half_18_11_φ2, half_18_11_φ3, half_18_11_φ4, half_18_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_18_11_φ1, half_18_11_φ2, half_18_11_φ3, half_18_11_φ4, half_18_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_13_11) (half_15_11)
    (by simpa only [half_18_11_φ5, show (2:ℝ)*16=32 by norm_num] using half_18_11_hx5)
  exact h.weaken (by norm_num [half_18_11_φ1, half_18_11_φ2, half_18_11_φ3, half_18_11_φ4, half_18_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_18_11_hx3 : SourcePowerBound (powerBoxCross 8 15 8 half_18_11_φ3) (9943098129/625000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 15) (u := 13) (t := 16)
    (D := 8) (ψ := (462183023/5000000000 : ℝ)) half_18_11_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_18_11_φ1, half_18_11_φ2, half_18_11_φ3, half_18_11_φ4, half_18_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_18_11_φ1, half_18_11_φ2, half_18_11_φ3, half_18_11_φ4, half_18_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_18_11_φ1, half_18_11_φ2, half_18_11_φ3, half_18_11_φ4, half_18_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_14_11) (half_16_11)
    (by simpa only [half_18_11_φ4, show (2:ℝ)*8=16 by norm_num] using half_18_11_hx4)
  exact h.weaken (by norm_num [half_18_11_φ1, half_18_11_φ2, half_18_11_φ3, half_18_11_φ4, half_18_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_18_11_hx2 : SourcePowerBound (powerBoxCross 8 16 4 half_18_11_φ2) (12206852967/625000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 16) (u := 14) (t := 17)
    (D := 4) (ψ := (539213527/5000000000 : ℝ)) half_18_11_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_18_11_φ1, half_18_11_φ2, half_18_11_φ3, half_18_11_φ4, half_18_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_18_11_φ1, half_18_11_φ2, half_18_11_φ3, half_18_11_φ4, half_18_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_18_11_φ1, half_18_11_φ2, half_18_11_φ3, half_18_11_φ4, half_18_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_15_11) (half_17_11)
    (by simpa only [half_18_11_φ3, show (2:ℝ)*4=8 by norm_num] using half_18_11_hx3)
  exact h.weaken (by norm_num [half_18_11_φ1, half_18_11_φ2, half_18_11_φ3, half_18_11_φ4, half_18_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_18_11_hx1 : SourcePowerBound (powerBoxCross 8 17 2 half_18_11_φ1) (30075128121/1250000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 17) (u := 15) (t := 18)
    (D := 2) (ψ := (611065069/5000000000 : ℝ)) half_18_11_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_18_11_φ1, half_18_11_φ2, half_18_11_φ3, half_18_11_φ4, half_18_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_18_11_φ1, half_18_11_φ2, half_18_11_φ3, half_18_11_φ4, half_18_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_18_11_φ1, half_18_11_φ2, half_18_11_φ3, half_18_11_φ4, half_18_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_16_11) (half_18_10)
    (by simpa only [half_18_11_φ2, show (2:ℝ)*2=4 by norm_num] using half_18_11_hx2)
  exact h.weaken (by norm_num [half_18_11_φ1, half_18_11_φ2, half_18_11_φ3, half_18_11_φ4, half_18_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_18_11 : AdmissibleExponent 8 36 (281154080709/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 16) (ψ := (1228880477/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_17_11)
    (by simpa only [half_18_11_φ1] using half_18_11_hx1)
  exact admissibleExponent_mono h (by norm_num [half_18_11_φ1, half_18_11_φ2, half_18_11_φ3, half_18_11_φ4, half_18_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_19_11_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (309102221/2500000000 : ℝ)

def half_19_11_φ2 : Fin 2 → ℝ := Fin.snoc half_19_11_φ1 (1234124559/10000000000 : ℝ)

def half_19_11_φ3 : Fin 3 → ℝ := Fin.snoc half_19_11_φ2 (1075638079/10000000000 : ℝ)

def half_19_11_φ4 : Fin 4 → ℝ := Fin.snoc half_19_11_φ3 (115246937/1250000000 : ℝ)

def half_19_11_φ5 : Fin 5 → ℝ := Fin.snoc half_19_11_φ4 (790264711/10000000000 : ℝ)

theorem half_19_11_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_19_11_φ5) (59573353691/10000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_19_11_φ5 (by norm_num [half_19_11_φ1, half_19_11_φ2, half_19_11_φ3, half_19_11_φ4, half_19_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_19_11_φ1, half_19_11_φ2, half_19_11_φ3, half_19_11_φ4, half_19_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_19_11_φ1, half_19_11_φ2, half_19_11_φ3, half_19_11_φ4, half_19_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_19_11_φ1, half_19_11_φ2, half_19_11_φ3, half_19_11_φ4, half_19_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_19_11_φ1, half_19_11_φ2, half_19_11_φ3, half_19_11_φ4, half_19_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_19_11_hx5 : SourcePowerBound (powerBoxCross 8 14 32 half_19_11_φ5) (29890145309/2500000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 14) (r := 2) (v := 18) (w := 19) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_19_11_φ5 (by norm_num [half_19_11_φ1, half_19_11_φ2, half_19_11_φ3, half_19_11_φ4, half_19_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_19_11_φ1, half_19_11_φ2, half_19_11_φ3, half_19_11_φ4, half_19_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_19_11_hF2 (half_18_11) (half_19_10)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_19_11_φ1, half_19_11_φ2, half_19_11_φ3, half_19_11_φ4, half_19_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_19_11_hx4 : SourcePowerBound (powerBoxCross 8 15 16 half_19_11_φ4) (141747286721/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 15) (u := 13) (t := 16)
    (D := 16) (ψ := (790264711/10000000000 : ℝ)) half_19_11_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_19_11_φ1, half_19_11_φ2, half_19_11_φ3, half_19_11_φ4, half_19_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_19_11_φ1, half_19_11_φ2, half_19_11_φ3, half_19_11_φ4, half_19_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_19_11_φ1, half_19_11_φ2, half_19_11_φ3, half_19_11_φ4, half_19_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_14_11) (half_16_11)
    (by simpa only [half_19_11_φ5, show (2:ℝ)*16=32 by norm_num] using half_19_11_hx5)
  exact h.weaken (by norm_num [half_19_11_φ1, half_19_11_φ2, half_19_11_φ3, half_19_11_φ4, half_19_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_19_11_hx3 : SourcePowerBound (powerBoxCross 8 16 8 half_19_11_φ3) (42804301533/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 16) (u := 14) (t := 17)
    (D := 8) (ψ := (115246937/1250000000 : ℝ)) half_19_11_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_19_11_φ1, half_19_11_φ2, half_19_11_φ3, half_19_11_φ4, half_19_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_19_11_φ1, half_19_11_φ2, half_19_11_φ3, half_19_11_φ4, half_19_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_19_11_φ1, half_19_11_φ2, half_19_11_φ3, half_19_11_φ4, half_19_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_15_11) (half_17_11)
    (by simpa only [half_19_11_φ4, show (2:ℝ)*8=16 by norm_num] using half_19_11_hx4)
  exact h.weaken (by norm_num [half_19_11_φ1, half_19_11_φ2, half_19_11_φ3, half_19_11_φ4, half_19_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_19_11_hx2 : SourcePowerBound (powerBoxCross 8 17 4 half_19_11_φ2) (52370284661/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 17) (u := 15) (t := 18)
    (D := 4) (ψ := (1075638079/10000000000 : ℝ)) half_19_11_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_19_11_φ1, half_19_11_φ2, half_19_11_φ3, half_19_11_φ4, half_19_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_19_11_φ1, half_19_11_φ2, half_19_11_φ3, half_19_11_φ4, half_19_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_19_11_φ1, half_19_11_φ2, half_19_11_φ3, half_19_11_φ4, half_19_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_16_11) (half_18_11)
    (by simpa only [half_19_11_φ3, show (2:ℝ)*4=8 by norm_num] using half_19_11_hx3)
  exact h.weaken (by norm_num [half_19_11_φ1, half_19_11_φ2, half_19_11_φ3, half_19_11_φ4, half_19_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_19_11_hx1 : SourcePowerBound (powerBoxCross 8 18 2 half_19_11_φ1) (257628349281/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 18) (u := 16) (t := 19)
    (D := 2) (ψ := (1234124559/10000000000 : ℝ)) half_19_11_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_19_11_φ1, half_19_11_φ2, half_19_11_φ3, half_19_11_φ4, half_19_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_19_11_φ1, half_19_11_φ2, half_19_11_φ3, half_19_11_φ4, half_19_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_19_11_φ1, half_19_11_φ2, half_19_11_φ3, half_19_11_φ4, half_19_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_17_11) (half_19_10)
    (by simpa only [half_19_11_φ2, show (2:ℝ)*2=4 by norm_num] using half_19_11_hx2)
  exact h.weaken (by norm_num [half_19_11_φ1, half_19_11_φ2, half_19_11_φ3, half_19_11_φ4, half_19_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_19_11 : AdmissibleExponent 8 38 (300902660221/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 17) (ψ := (309102221/2500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_18_11)
    (by simpa only [half_19_11_φ1] using half_19_11_hx1)
  exact admissibleExponent_mono h (by norm_num [half_19_11_φ1, half_19_11_φ2, half_19_11_φ3, half_19_11_φ4, half_19_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_20_11_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1241892273/10000000000 : ℝ)

def half_20_11_φ2 : Fin 2 → ℝ := Fin.snoc half_20_11_φ1 (1242779413/10000000000 : ℝ)

def half_20_11_φ3 : Fin 3 → ℝ := Fin.snoc half_20_11_φ2 (107361833/1000000000 : ℝ)

def half_20_11_φ4 : Fin 4 → ℝ := Fin.snoc half_20_11_φ3 (920244283/10000000000 : ℝ)

def half_20_11_φ5 : Fin 5 → ℝ := Fin.snoc half_20_11_φ4 (394390407/5000000000 : ℝ)

theorem half_20_11_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_20_11_φ5) (59386382627/10000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_20_11_φ5 (by norm_num [half_20_11_φ1, half_20_11_φ2, half_20_11_φ3, half_20_11_φ4, half_20_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_20_11_φ1, half_20_11_φ2, half_20_11_φ3, half_20_11_φ4, half_20_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_20_11_φ1, half_20_11_φ2, half_20_11_φ3, half_20_11_φ4, half_20_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_20_11_φ1, half_20_11_φ2, half_20_11_φ3, half_20_11_φ4, half_20_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_20_11_φ1, half_20_11_φ2, half_20_11_φ3, half_20_11_φ4, half_20_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_20_11_hx5 : SourcePowerBound (powerBoxCross 8 15 32 half_20_11_φ5) (12869115609/1000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 15) (r := 2) (v := 0) (w := 20) (D := 32)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_20_11_φ5 (by norm_num [half_20_11_φ1, half_20_11_φ2, half_20_11_φ3, half_20_11_φ4, half_20_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_20_11_φ1, half_20_11_φ2, half_20_11_φ3, half_20_11_φ4, half_20_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_20_11_hF2 (admissibleExponent_zero 8) (half_20_10)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_20_11_φ1, half_20_11_φ2, half_20_11_φ3, half_20_11_φ4, half_20_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_20_11_hx4 : SourcePowerBound (powerBoxCross 8 16 16 half_20_11_φ4) (76151756621/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 16) (u := 14) (t := 17)
    (D := 16) (ψ := (394390407/5000000000 : ℝ)) half_20_11_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_20_11_φ1, half_20_11_φ2, half_20_11_φ3, half_20_11_φ4, half_20_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_20_11_φ1, half_20_11_φ2, half_20_11_φ3, half_20_11_φ4, half_20_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_20_11_φ1, half_20_11_φ2, half_20_11_φ3, half_20_11_φ4, half_20_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_15_11) (half_17_11)
    (by simpa only [half_20_11_φ5, show (2:ℝ)*16=32 by norm_num] using half_20_11_hx5)
  exact h.weaken (by norm_num [half_20_11_φ1, half_20_11_φ2, half_20_11_φ3, half_20_11_φ4, half_20_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_20_11_hx3 : SourcePowerBound (powerBoxCross 8 17 8 half_20_11_φ3) (183517180389/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 17) (u := 15) (t := 18)
    (D := 8) (ψ := (920244283/10000000000 : ℝ)) half_20_11_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_20_11_φ1, half_20_11_φ2, half_20_11_φ3, half_20_11_φ4, half_20_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_20_11_φ1, half_20_11_φ2, half_20_11_φ3, half_20_11_φ4, half_20_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_20_11_φ1, half_20_11_φ2, half_20_11_φ3, half_20_11_φ4, half_20_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_16_11) (half_18_11)
    (by simpa only [half_20_11_φ4, show (2:ℝ)*8=16 by norm_num] using half_20_11_hx4)
  exact h.weaken (by norm_num [half_20_11_φ1, half_20_11_φ2, half_20_11_φ3, half_20_11_φ4, half_20_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_20_11_hx2 : SourcePowerBound (powerBoxCross 8 18 4 half_20_11_φ2) (44769211169/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 18) (u := 16) (t := 19)
    (D := 4) (ψ := (107361833/1000000000 : ℝ)) half_20_11_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_20_11_φ1, half_20_11_φ2, half_20_11_φ3, half_20_11_φ4, half_20_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_20_11_φ1, half_20_11_φ2, half_20_11_φ3, half_20_11_φ4, half_20_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_20_11_φ1, half_20_11_φ2, half_20_11_φ3, half_20_11_φ4, half_20_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_17_11) (half_19_11)
    (by simpa only [half_20_11_φ3, show (2:ℝ)*4=8 by norm_num] using half_20_11_hx3)
  exact h.weaken (by norm_num [half_20_11_φ1, half_20_11_φ2, half_20_11_φ3, half_20_11_φ4, half_20_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_20_11_hx1 : SourcePowerBound (powerBoxCross 8 19 2 half_20_11_φ1) (17173480227/625000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 19) (u := 17) (t := 20)
    (D := 2) (ψ := (1242779413/10000000000 : ℝ)) half_20_11_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_20_11_φ1, half_20_11_φ2, half_20_11_φ3, half_20_11_φ4, half_20_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_20_11_φ1, half_20_11_φ2, half_20_11_φ3, half_20_11_φ4, half_20_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_20_11_φ1, half_20_11_φ2, half_20_11_φ3, half_20_11_φ4, half_20_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_18_11) (half_20_10)
    (by simpa only [half_20_11_φ2, show (2:ℝ)*2=4 by norm_num] using half_20_11_hx2)
  exact h.weaken (by norm_num [half_20_11_φ1, half_20_11_φ2, half_20_11_φ3, half_20_11_φ4, half_20_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_20_11 : AdmissibleExponent 8 40 (320725697733/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 18) (ψ := (1241892273/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_19_11)
    (by simpa only [half_20_11_φ1] using half_20_11_hx1)
  exact admissibleExponent_mono h (by norm_num [half_20_11_φ1, half_20_11_φ2, half_20_11_φ3, half_20_11_φ4, half_20_11_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_10_12_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1031599291/10000000000 : ℝ)

def half_10_12_φ2 : Fin 2 → ℝ := Fin.snoc half_10_12_φ1 (961404421/10000000000 : ℝ)

def half_10_12_φ3 : Fin 3 → ℝ := Fin.snoc half_10_12_φ2 (167316163/2000000000 : ℝ)

def half_10_12_φ4 : Fin 4 → ℝ := Fin.snoc half_10_12_φ3 (109800363/2000000000 : ℝ)

theorem half_10_12_hF2 : SourcePowerBound (paddedMoment 8 0 2 16 half_10_12_φ4) (34524843409/5000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 4) (r := 0) (n := 1) (D := 16)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_10_12_φ4 (by norm_num [half_10_12_φ1, half_10_12_φ2, half_10_12_φ3, half_10_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_12_φ1, half_10_12_φ2, half_10_12_φ3, half_10_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_12_φ1, half_10_12_φ2, half_10_12_φ3, half_10_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_10_12_φ1, half_10_12_φ2, half_10_12_φ3, half_10_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_10_12_φ1, half_10_12_φ2, half_10_12_φ3, half_10_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_10_12_hx4 : SourcePowerBound (powerBoxCross 8 6 16 half_10_12_φ4) (66142667709/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 6) (r := 2) (v := 0) (w := 8) (D := 16)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_10_12_φ4 (by norm_num [half_10_12_φ1, half_10_12_φ2, half_10_12_φ3, half_10_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_12_φ1, half_10_12_φ2, half_10_12_φ3, half_10_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_10_12_hF2 (admissibleExponent_zero 8) (SeedCompletionHigher8SimpleSeeds.degree8_half_8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_10_12_φ1, half_10_12_φ2, half_10_12_φ3, half_10_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_12_hx3 : SourcePowerBound (powerBoxCross 8 7 8 half_10_12_φ3) (76476003233/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 7) (u := 5) (t := 8)
    (D := 8) (ψ := (109800363/2000000000 : ℝ)) half_10_12_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_12_φ1, half_10_12_φ2, half_10_12_φ3, half_10_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_12_φ1, half_10_12_φ2, half_10_12_φ3, half_10_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_12_φ1, half_10_12_φ2, half_10_12_φ3, half_10_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionEven8SecondSeeds.degree8_half_6) (SeedCompletionHigher8SimpleSeeds.degree8_half_8)
    (by simpa only [half_10_12_φ4, show (2:ℝ)*8=16 by norm_num] using half_10_12_hx4)
  exact h.weaken (by norm_num [half_10_12_φ1, half_10_12_φ2, half_10_12_φ3, half_10_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_12_hx2 : SourcePowerBound (powerBoxCross 8 8 4 half_10_12_φ2) (92551969439/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 8) (u := 6) (t := 9)
    (D := 4) (ψ := (167316163/2000000000 : ℝ)) half_10_12_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_12_φ1, half_10_12_φ2, half_10_12_φ3, half_10_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_12_φ1, half_10_12_φ2, half_10_12_φ3, half_10_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_12_φ1, half_10_12_φ2, half_10_12_φ3, half_10_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_7) (SeedCompletionHigher8SimpleSeeds.degree8_half_9)
    (by simpa only [half_10_12_φ3, show (2:ℝ)*4=8 by norm_num] using half_10_12_hx3)
  exact h.weaken (by norm_num [half_10_12_φ1, half_10_12_φ2, half_10_12_φ3, half_10_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_12_hx1 : SourcePowerBound (powerBoxCross 8 9 2 half_10_12_φ1) (113745889017/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 9) (u := 7) (t := 10)
    (D := 2) (ψ := (961404421/10000000000 : ℝ)) half_10_12_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_12_φ1, half_10_12_φ2, half_10_12_φ3, half_10_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_12_φ1, half_10_12_φ2, half_10_12_φ3, half_10_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_12_φ1, half_10_12_φ2, half_10_12_φ3, half_10_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_8) (half_10_11)
    (by simpa only [half_10_12_φ2, show (2:ℝ)*2=4 by norm_num] using half_10_12_hx2)
  exact h.weaken (by norm_num [half_10_12_φ1, half_10_12_φ2, half_10_12_φ3, half_10_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_12 : AdmissibleExponent 8 20 (32820769241/2500000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 8) (ψ := (1031599291/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_9)
    (by simpa only [half_10_12_φ1] using half_10_12_hx1)
  exact admissibleExponent_mono h (by norm_num [half_10_12_φ1, half_10_12_φ2, half_10_12_φ3, half_10_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_11_12_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1074227587/10000000000 : ℝ)

def half_11_12_φ2 : Fin 2 → ℝ := Fin.snoc half_11_12_φ1 (126529791/1250000000 : ℝ)

def half_11_12_φ3 : Fin 3 → ℝ := Fin.snoc half_11_12_φ2 (230572711/2500000000 : ℝ)

def half_11_12_φ4 : Fin 4 → ℝ := Fin.snoc half_11_12_φ3 (740471133/10000000000 : ℝ)

theorem half_11_12_hF2 : SourcePowerBound (paddedMoment 8 0 2 16 half_11_12_φ4) (15316553567/2500000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 4) (r := 0) (n := 1) (D := 16)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_11_12_φ4 (by norm_num [half_11_12_φ1, half_11_12_φ2, half_11_12_φ3, half_11_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_12_φ1, half_11_12_φ2, half_11_12_φ3, half_11_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_12_φ1, half_11_12_φ2, half_11_12_φ3, half_11_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_11_12_φ1, half_11_12_φ2, half_11_12_φ3, half_11_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_11_12_φ1, half_11_12_φ2, half_11_12_φ3, half_11_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_11_12_hx4 : SourcePowerBound (powerBoxCross 8 7 16 half_11_12_φ4) (71626834893/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 7) (r := 2) (v := 9) (w := 10) (D := 16)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_11_12_φ4 (by norm_num [half_11_12_φ1, half_11_12_φ2, half_11_12_φ3, half_11_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_12_φ1, half_11_12_φ2, half_11_12_φ3, half_11_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_11_12_hF2 (SeedCompletionHigher8SimpleSeeds.degree8_half_9) (half_10_12)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_11_12_φ1, half_11_12_φ2, half_11_12_φ3, half_11_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_12_hx3 : SourcePowerBound (powerBoxCross 8 8 8 half_11_12_φ3) (17026174471/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 8) (u := 6) (t := 9)
    (D := 8) (ψ := (740471133/10000000000 : ℝ)) half_11_12_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_12_φ1, half_11_12_φ2, half_11_12_φ3, half_11_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_12_φ1, half_11_12_φ2, half_11_12_φ3, half_11_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_12_φ1, half_11_12_φ2, half_11_12_φ3, half_11_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_7) (SeedCompletionHigher8SimpleSeeds.degree8_half_9)
    (by simpa only [half_11_12_φ4, show (2:ℝ)*8=16 by norm_num] using half_11_12_hx4)
  exact h.weaken (by norm_num [half_11_12_φ1, half_11_12_φ2, half_11_12_φ3, half_11_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_12_hx2 : SourcePowerBound (powerBoxCross 8 9 4 half_11_12_φ2) (52062821011/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 9) (u := 7) (t := 10)
    (D := 4) (ψ := (230572711/2500000000 : ℝ)) half_11_12_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_12_φ1, half_11_12_φ2, half_11_12_φ3, half_11_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_12_φ1, half_11_12_φ2, half_11_12_φ3, half_11_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_12_φ1, half_11_12_φ2, half_11_12_φ3, half_11_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_8) (half_10_12)
    (by simpa only [half_11_12_φ3, show (2:ℝ)*4=8 by norm_num] using half_11_12_hx3)
  exact h.weaken (by norm_num [half_11_12_φ1, half_11_12_φ2, half_11_12_φ3, half_11_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_12_hx1 : SourcePowerBound (powerBoxCross 8 10 2 half_11_12_φ1) (64127257129/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 10) (u := 8) (t := 11)
    (D := 2) (ψ := (126529791/1250000000 : ℝ)) half_11_12_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_12_φ1, half_11_12_φ2, half_11_12_φ3, half_11_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_12_φ1, half_11_12_φ2, half_11_12_φ3, half_11_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_12_φ1, half_11_12_φ2, half_11_12_φ3, half_11_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_9) (half_11_11)
    (by simpa only [half_11_12_φ2, show (2:ℝ)*2=4 by norm_num] using half_11_12_hx2)
  exact h.weaken (by norm_num [half_11_12_φ1, half_11_12_φ2, half_11_12_φ3, half_11_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_12 : AdmissibleExponent 8 22 (148664838411/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 9) (ψ := (1074227587/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_10_12)
    (by simpa only [half_11_12_φ1] using half_11_12_hx1)
  exact admissibleExponent_mono h (by norm_num [half_11_12_φ1, half_11_12_φ2, half_11_12_φ3, half_11_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_12_12_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1106964533/10000000000 : ℝ)

def half_12_12_φ2 : Fin 2 → ℝ := Fin.snoc half_12_12_φ1 (1055548473/10000000000 : ℝ)

def half_12_12_φ3 : Fin 3 → ℝ := Fin.snoc half_12_12_φ2 (977036757/10000000000 : ℝ)

def half_12_12_φ4 : Fin 4 → ℝ := Fin.snoc half_12_12_φ3 (841992627/10000000000 : ℝ)

def half_12_12_φ5 : Fin 5 → ℝ := Fin.snoc half_12_12_φ4 (4223621/80000000 : ℝ)

theorem half_12_12_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_12_12_φ5) (15060120937/2000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_12_12_φ5 (by norm_num [half_12_12_φ1, half_12_12_φ2, half_12_12_φ3, half_12_12_φ4, half_12_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_12_φ1, half_12_12_φ2, half_12_12_φ3, half_12_12_φ4, half_12_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_12_φ1, half_12_12_φ2, half_12_12_φ3, half_12_12_φ4, half_12_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_12_12_φ1, half_12_12_φ2, half_12_12_φ3, half_12_12_φ4, half_12_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_12_12_φ1, half_12_12_φ2, half_12_12_φ3, half_12_12_φ4, half_12_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_12_12_hx5 : SourcePowerBound (powerBoxCross 8 7 32 half_12_12_φ5) (34143270849/5000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 7) (r := 2) (v := 9) (w := 10) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_12_12_φ5 (by norm_num [half_12_12_φ1, half_12_12_φ2, half_12_12_φ3, half_12_12_φ4, half_12_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_12_φ1, half_12_12_φ2, half_12_12_φ3, half_12_12_φ4, half_12_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_12_12_hF2 (SeedCompletionHigher8SimpleSeeds.degree8_half_9) (half_10_12)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_12_12_φ1, half_12_12_φ2, half_12_12_φ3, half_12_12_φ4, half_12_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_12_hx4 : SourcePowerBound (powerBoxCross 8 8 16 half_12_12_φ4) (39051996207/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 8) (u := 6) (t := 9)
    (D := 16) (ψ := (4223621/80000000 : ℝ)) half_12_12_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_12_φ1, half_12_12_φ2, half_12_12_φ3, half_12_12_φ4, half_12_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_12_φ1, half_12_12_φ2, half_12_12_φ3, half_12_12_φ4, half_12_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_12_φ1, half_12_12_φ2, half_12_12_φ3, half_12_12_φ4, half_12_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_7) (SeedCompletionHigher8SimpleSeeds.degree8_half_9)
    (by simpa only [half_12_12_φ5, show (2:ℝ)*16=32 by norm_num] using half_12_12_hx5)
  exact h.weaken (by norm_num [half_12_12_φ1, half_12_12_φ2, half_12_12_φ3, half_12_12_φ4, half_12_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_12_hx3 : SourcePowerBound (powerBoxCross 8 9 8 half_12_12_φ3) (94411567563/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 9) (u := 7) (t := 10)
    (D := 8) (ψ := (841992627/10000000000 : ℝ)) half_12_12_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_12_φ1, half_12_12_φ2, half_12_12_φ3, half_12_12_φ4, half_12_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_12_φ1, half_12_12_φ2, half_12_12_φ3, half_12_12_φ4, half_12_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_12_φ1, half_12_12_φ2, half_12_12_φ3, half_12_12_φ4, half_12_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_8) (half_10_12)
    (by simpa only [half_12_12_φ4, show (2:ℝ)*8=16 by norm_num] using half_12_12_hx4)
  exact h.weaken (by norm_num [half_12_12_φ1, half_12_12_φ2, half_12_12_φ3, half_12_12_φ4, half_12_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_12_hx2 : SourcePowerBound (powerBoxCross 8 10 4 half_12_12_φ2) (116199737571/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 10) (u := 8) (t := 11)
    (D := 4) (ψ := (977036757/10000000000 : ℝ)) half_12_12_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_12_φ1, half_12_12_φ2, half_12_12_φ3, half_12_12_φ4, half_12_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_12_φ1, half_12_12_φ2, half_12_12_φ3, half_12_12_φ4, half_12_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_12_φ1, half_12_12_φ2, half_12_12_φ3, half_12_12_φ4, half_12_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_9) (half_11_12)
    (by simpa only [half_12_12_φ3, show (2:ℝ)*4=8 by norm_num] using half_12_12_hx3)
  exact h.weaken (by norm_num [half_12_12_φ1, half_12_12_φ2, half_12_12_φ3, half_12_12_φ4, half_12_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_12_hx1 : SourcePowerBound (powerBoxCross 8 11 2 half_12_12_φ1) (2239298947/156250000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 11) (u := 9) (t := 12)
    (D := 2) (ψ := (1055548473/10000000000 : ℝ)) half_12_12_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_12_φ1, half_12_12_φ2, half_12_12_φ3, half_12_12_φ4, half_12_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_12_φ1, half_12_12_φ2, half_12_12_φ3, half_12_12_φ4, half_12_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_12_φ1, half_12_12_φ2, half_12_12_φ3, half_12_12_φ4, half_12_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_10_12) (half_12_11)
    (by simpa only [half_12_12_φ2, show (2:ℝ)*2=4 by norm_num] using half_12_12_hx2)
  exact h.weaken (by norm_num [half_12_12_φ1, half_12_12_φ2, half_12_12_φ3, half_12_12_φ4, half_12_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_12 : AdmissibleExponent 8 24 (166561387801/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 10) (ψ := (1106964533/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_11_12)
    (by simpa only [half_12_12_φ1] using half_12_12_hx1)
  exact admissibleExponent_mono h (by norm_num [half_12_12_φ1, half_12_12_φ2, half_12_12_φ3, half_12_12_φ4, half_12_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_13_12_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (567818219/5000000000 : ℝ)

def half_13_12_φ2 : Fin 2 → ℝ := Fin.snoc half_13_12_φ1 (545077393/5000000000 : ℝ)

def half_13_12_φ3 : Fin 3 → ℝ := Fin.snoc half_13_12_φ2 (1281029/12500000 : ℝ)

def half_13_12_φ4 : Fin 4 → ℝ := Fin.snoc half_13_12_φ3 (182476579/2000000000 : ℝ)

def half_13_12_φ5 : Fin 5 → ℝ := Fin.snoc half_13_12_φ4 (13696897/200000000 : ℝ)

theorem half_13_12_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_13_12_φ5) (68195314451/10000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_13_12_φ5 (by norm_num [half_13_12_φ1, half_13_12_φ2, half_13_12_φ3, half_13_12_φ4, half_13_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_12_φ1, half_13_12_φ2, half_13_12_φ3, half_13_12_φ4, half_13_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_12_φ1, half_13_12_φ2, half_13_12_φ3, half_13_12_φ4, half_13_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_13_12_φ1, half_13_12_φ2, half_13_12_φ3, half_13_12_φ4, half_13_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_13_12_φ1, half_13_12_φ2, half_13_12_φ3, half_13_12_φ4, half_13_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_13_12_hx5 : SourcePowerBound (powerBoxCross 8 8 32 half_13_12_φ5) (7225584251/1000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 8) (r := 2) (v := 10) (w := 11) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_13_12_φ5 (by norm_num [half_13_12_φ1, half_13_12_φ2, half_13_12_φ3, half_13_12_φ4, half_13_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_12_φ1, half_13_12_φ2, half_13_12_φ3, half_13_12_φ4, half_13_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_13_12_hF2 (half_10_12) (half_11_12)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_13_12_φ1, half_13_12_φ2, half_13_12_φ3, half_13_12_φ4, half_13_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_12_hx4 : SourcePowerBound (powerBoxCross 8 9 16 half_13_12_φ4) (2656523457/312500000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 9) (u := 7) (t := 10)
    (D := 16) (ψ := (13696897/200000000 : ℝ)) half_13_12_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_12_φ1, half_13_12_φ2, half_13_12_φ3, half_13_12_φ4, half_13_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_12_φ1, half_13_12_φ2, half_13_12_φ3, half_13_12_φ4, half_13_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_12_φ1, half_13_12_φ2, half_13_12_φ3, half_13_12_φ4, half_13_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_8) (half_10_12)
    (by simpa only [half_13_12_φ5, show (2:ℝ)*16=32 by norm_num] using half_13_12_hx5)
  exact h.weaken (by norm_num [half_13_12_φ1, half_13_12_φ2, half_13_12_φ3, half_13_12_φ4, half_13_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_12_hx3 : SourcePowerBound (powerBoxCross 8 10 8 half_13_12_φ3) (104052295237/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 10) (u := 8) (t := 11)
    (D := 8) (ψ := (182476579/2000000000 : ℝ)) half_13_12_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_12_φ1, half_13_12_φ2, half_13_12_φ3, half_13_12_φ4, half_13_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_12_φ1, half_13_12_φ2, half_13_12_φ3, half_13_12_φ4, half_13_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_12_φ1, half_13_12_φ2, half_13_12_φ3, half_13_12_φ4, half_13_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_9) (half_11_12)
    (by simpa only [half_13_12_φ4, show (2:ℝ)*8=16 by norm_num] using half_13_12_hx4)
  exact h.weaken (by norm_num [half_13_12_φ1, half_13_12_φ2, half_13_12_φ3, half_13_12_φ4, half_13_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_12_hx2 : SourcePowerBound (powerBoxCross 8 11 4 half_13_12_φ2) (64357924437/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 11) (u := 9) (t := 12)
    (D := 4) (ψ := (1281029/12500000 : ℝ)) half_13_12_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_12_φ1, half_13_12_φ2, half_13_12_φ3, half_13_12_φ4, half_13_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_12_φ1, half_13_12_φ2, half_13_12_φ3, half_13_12_φ4, half_13_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_12_φ1, half_13_12_φ2, half_13_12_φ3, half_13_12_φ4, half_13_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_10_12) (half_12_12)
    (by simpa only [half_13_12_φ3, show (2:ℝ)*4=8 by norm_num] using half_13_12_hx3)
  exact h.weaken (by norm_num [half_13_12_φ1, half_13_12_φ2, half_13_12_φ3, half_13_12_φ4, half_13_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_12_hx1 : SourcePowerBound (powerBoxCross 8 12 2 half_13_12_φ1) (9923856633/625000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 12) (u := 10) (t := 13)
    (D := 2) (ψ := (545077393/5000000000 : ℝ)) half_13_12_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_12_φ1, half_13_12_φ2, half_13_12_φ3, half_13_12_φ4, half_13_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_12_φ1, half_13_12_φ2, half_13_12_φ3, half_13_12_φ4, half_13_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_12_φ1, half_13_12_φ2, half_13_12_φ3, half_13_12_φ4, half_13_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_11_12) (half_13_11)
    (by simpa only [half_13_12_φ2, show (2:ℝ)*2=4 by norm_num] using half_13_12_hx2)
  exact h.weaken (by norm_num [half_13_12_φ1, half_13_12_φ2, half_13_12_φ3, half_13_12_φ4, half_13_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_12 : AdmissibleExponent 8 26 (92450672101/5000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 11) (ψ := (567818219/5000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_12_12)
    (by simpa only [half_13_12_φ1] using half_13_12_hx1)
  exact admissibleExponent_mono h (by norm_num [half_13_12_φ1, half_13_12_φ2, half_13_12_φ3, half_13_12_φ4, half_13_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_14_12_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1162174703/10000000000 : ℝ)

def half_14_12_φ2 : Fin 2 → ℝ := Fin.snoc half_14_12_φ1 (280886007/2500000000 : ℝ)

def half_14_12_φ3 : Fin 3 → ℝ := Fin.snoc half_14_12_φ2 (1070250301/10000000000 : ℝ)

def half_14_12_φ4 : Fin 4 → ℝ := Fin.snoc half_14_12_φ3 (11864341/125000000 : ℝ)

def half_14_12_φ5 : Fin 5 → ℝ := Fin.snoc half_14_12_φ4 (203388703/2500000000 : ℝ)

theorem half_14_12_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_14_12_φ5) (15626976599/2500000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_14_12_φ5 (by norm_num [half_14_12_φ1, half_14_12_φ2, half_14_12_φ3, half_14_12_φ4, half_14_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_12_φ1, half_14_12_φ2, half_14_12_φ3, half_14_12_φ4, half_14_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_12_φ1, half_14_12_φ2, half_14_12_φ3, half_14_12_φ4, half_14_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_14_12_φ1, half_14_12_φ2, half_14_12_φ3, half_14_12_φ4, half_14_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_14_12_φ1, half_14_12_φ2, half_14_12_φ3, half_14_12_φ4, half_14_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_14_12_hx5 : SourcePowerBound (powerBoxCross 8 9 32 half_14_12_φ5) (299238457/39062500 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 9) (r := 2) (v := 0) (w := 12) (D := 32)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_14_12_φ5 (by norm_num [half_14_12_φ1, half_14_12_φ2, half_14_12_φ3, half_14_12_φ4, half_14_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_12_φ1, half_14_12_φ2, half_14_12_φ3, half_14_12_φ4, half_14_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_14_12_hF2 (admissibleExponent_zero 8) (half_12_12)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_14_12_φ1, half_14_12_φ2, half_14_12_φ3, half_14_12_φ4, half_14_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_12_hx4 : SourcePowerBound (powerBoxCross 8 10 16 half_14_12_φ4) (92481279469/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 10) (u := 8) (t := 11)
    (D := 16) (ψ := (203388703/2500000000 : ℝ)) half_14_12_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_12_φ1, half_14_12_φ2, half_14_12_φ3, half_14_12_φ4, half_14_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_12_φ1, half_14_12_φ2, half_14_12_φ3, half_14_12_φ4, half_14_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_12_φ1, half_14_12_φ2, half_14_12_φ3, half_14_12_φ4, half_14_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_9) (half_11_12)
    (by simpa only [half_14_12_φ5, show (2:ℝ)*16=32 by norm_num] using half_14_12_hx5)
  exact h.weaken (by norm_num [half_14_12_φ1, half_14_12_φ2, half_14_12_φ3, half_14_12_φ4, half_14_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_12_hx3 : SourcePowerBound (powerBoxCross 8 11 8 half_14_12_φ3) (56921799107/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 11) (u := 9) (t := 12)
    (D := 8) (ψ := (11864341/125000000 : ℝ)) half_14_12_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_12_φ1, half_14_12_φ2, half_14_12_φ3, half_14_12_φ4, half_14_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_12_φ1, half_14_12_φ2, half_14_12_φ3, half_14_12_φ4, half_14_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_12_φ1, half_14_12_φ2, half_14_12_φ3, half_14_12_φ4, half_14_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_10_12) (half_12_12)
    (by simpa only [half_14_12_φ4, show (2:ℝ)*8=16 by norm_num] using half_14_12_hx4)
  exact h.weaken (by norm_num [half_14_12_φ1, half_14_12_φ2, half_14_12_φ3, half_14_12_φ4, half_14_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_12_hx2 : SourcePowerBound (powerBoxCross 8 12 4 half_14_12_φ2) (141478460519/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 12) (u := 10) (t := 13)
    (D := 4) (ψ := (1070250301/10000000000 : ℝ)) half_14_12_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_12_φ1, half_14_12_φ2, half_14_12_φ3, half_14_12_φ4, half_14_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_12_φ1, half_14_12_φ2, half_14_12_φ3, half_14_12_φ4, half_14_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_12_φ1, half_14_12_φ2, half_14_12_φ3, half_14_12_φ4, half_14_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_11_12) (half_13_12)
    (by simpa only [half_14_12_φ3, show (2:ℝ)*4=8 by norm_num] using half_14_12_hx3)
  exact h.weaken (by norm_num [half_14_12_φ1, half_14_12_φ2, half_14_12_φ3, half_14_12_φ4, half_14_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_12_hx1 : SourcePowerBound (powerBoxCross 8 13 2 half_14_12_φ1) (87287376217/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 13) (u := 11) (t := 14)
    (D := 2) (ψ := (280886007/2500000000 : ℝ)) half_14_12_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_12_φ1, half_14_12_φ2, half_14_12_φ3, half_14_12_φ4, half_14_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_12_φ1, half_14_12_φ2, half_14_12_φ3, half_14_12_φ4, half_14_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_12_φ1, half_14_12_φ2, half_14_12_φ3, half_14_12_φ4, half_14_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_12_12) (half_14_11)
    (by simpa only [half_14_12_φ2, show (2:ℝ)*2=4 by norm_num] using half_14_12_hx2)
  exact h.weaken (by norm_num [half_14_12_φ1, half_14_12_φ2, half_14_12_φ3, half_14_12_φ4, half_14_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_12 : AdmissibleExponent 8 28 (203629120009/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 12) (ψ := (1162174703/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_13_12)
    (by simpa only [half_14_12_φ1] using half_14_12_hx1)
  exact admissibleExponent_mono h (by norm_num [half_14_12_φ1, half_14_12_φ2, half_14_12_φ3, half_14_12_φ4, half_14_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_15_12_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (237290651/2000000000 : ℝ)

def half_15_12_φ2 : Fin 2 → ℝ := Fin.snoc half_15_12_φ1 (1156895297/10000000000 : ℝ)

def half_15_12_φ3 : Fin 3 → ℝ := Fin.snoc half_15_12_φ2 (1093807349/10000000000 : ℝ)

def half_15_12_φ4 : Fin 4 → ℝ := Fin.snoc half_15_12_φ3 (234387289/2500000000 : ℝ)

def half_15_12_φ5 : Fin 5 → ℝ := Fin.snoc half_15_12_φ4 (401806781/5000000000 : ℝ)

theorem half_15_12_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_15_12_φ5) (61255309001/10000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_15_12_φ5 (by norm_num [half_15_12_φ1, half_15_12_φ2, half_15_12_φ3, half_15_12_φ4, half_15_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_12_φ1, half_15_12_φ2, half_15_12_φ3, half_15_12_φ4, half_15_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_12_φ1, half_15_12_φ2, half_15_12_φ3, half_15_12_φ4, half_15_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_15_12_φ1, half_15_12_φ2, half_15_12_φ3, half_15_12_φ4, half_15_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_15_12_φ1, half_15_12_φ2, half_15_12_φ3, half_15_12_φ4, half_15_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_15_12_hx5 : SourcePowerBound (powerBoxCross 8 10 32 half_15_12_φ5) (42218232049/5000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 10) (r := 2) (v := 13) (w := 14) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_15_12_φ5 (by norm_num [half_15_12_φ1, half_15_12_φ2, half_15_12_φ3, half_15_12_φ4, half_15_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_12_φ1, half_15_12_φ2, half_15_12_φ3, half_15_12_φ4, half_15_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_15_12_hF2 (half_13_12) (half_14_12)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_15_12_φ1, half_15_12_φ2, half_15_12_φ3, half_15_12_φ4, half_15_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_12_hx4 : SourcePowerBound (powerBoxCross 8 11 16 half_15_12_φ4) (50694469907/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 11) (u := 9) (t := 12)
    (D := 16) (ψ := (401806781/5000000000 : ℝ)) half_15_12_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_12_φ1, half_15_12_φ2, half_15_12_φ3, half_15_12_φ4, half_15_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_12_φ1, half_15_12_φ2, half_15_12_φ3, half_15_12_φ4, half_15_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_12_φ1, half_15_12_φ2, half_15_12_φ3, half_15_12_φ4, half_15_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_10_12) (half_12_12)
    (by simpa only [half_15_12_φ5, show (2:ℝ)*16=32 by norm_num] using half_15_12_hx5)
  exact h.weaken (by norm_num [half_15_12_φ1, half_15_12_φ2, half_15_12_φ3, half_15_12_φ4, half_15_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_12_hx3 : SourcePowerBound (powerBoxCross 8 12 8 half_15_12_φ3) (124182625177/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 12) (u := 10) (t := 13)
    (D := 8) (ψ := (234387289/2500000000 : ℝ)) half_15_12_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_12_φ1, half_15_12_φ2, half_15_12_φ3, half_15_12_φ4, half_15_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_12_φ1, half_15_12_φ2, half_15_12_φ3, half_15_12_φ4, half_15_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_12_φ1, half_15_12_φ2, half_15_12_φ3, half_15_12_φ4, half_15_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_11_12) (half_13_12)
    (by simpa only [half_15_12_φ4, show (2:ℝ)*8=16 by norm_num] using half_15_12_hx4)
  exact h.weaken (by norm_num [half_15_12_φ1, half_15_12_φ2, half_15_12_φ3, half_15_12_φ4, half_15_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_12_hx2 : SourcePowerBound (powerBoxCross 8 13 4 half_15_12_φ2) (154424236999/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 13) (u := 11) (t := 14)
    (D := 4) (ψ := (1093807349/10000000000 : ℝ)) half_15_12_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_12_φ1, half_15_12_φ2, half_15_12_φ3, half_15_12_φ4, half_15_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_12_φ1, half_15_12_φ2, half_15_12_φ3, half_15_12_φ4, half_15_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_12_φ1, half_15_12_φ2, half_15_12_φ3, half_15_12_φ4, half_15_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_12_12) (half_14_12)
    (by simpa only [half_15_12_φ3, show (2:ℝ)*4=8 by norm_num] using half_15_12_hx3)
  exact h.weaken (by norm_num [half_15_12_φ1, half_15_12_φ2, half_15_12_φ3, half_15_12_φ4, half_15_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_12_hx1 : SourcePowerBound (powerBoxCross 8 14 2 half_15_12_φ1) (190655930043/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 14) (u := 12) (t := 15)
    (D := 2) (ψ := (1156895297/10000000000 : ℝ)) half_15_12_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_12_φ1, half_15_12_φ2, half_15_12_φ3, half_15_12_φ4, half_15_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_12_φ1, half_15_12_φ2, half_15_12_φ3, half_15_12_φ4, half_15_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_12_φ1, half_15_12_φ2, half_15_12_φ3, half_15_12_φ4, half_15_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_13_12) (half_15_11)
    (by simpa only [half_15_12_φ2, show (2:ℝ)*2=4 by norm_num] using half_15_12_hx2)
  exact h.weaken (by norm_num [half_15_12_φ1, half_15_12_φ2, half_15_12_φ3, half_15_12_φ4, half_15_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_12 : AdmissibleExponent 8 30 (27836270991/1250000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 13) (ψ := (237290651/2000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_14_12)
    (by simpa only [half_15_12_φ1] using half_15_12_hx1)
  exact admissibleExponent_mono h (by norm_num [half_15_12_φ1, half_15_12_φ2, half_15_12_φ3, half_15_12_φ4, half_15_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_16_12_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (301162679/2500000000 : ℝ)

def half_16_12_φ2 : Fin 2 → ℝ := Fin.snoc half_16_12_φ1 (1185108309/10000000000 : ℝ)

def half_16_12_φ3 : Fin 3 → ℝ := Fin.snoc half_16_12_φ2 (543588641/5000000000 : ℝ)

def half_16_12_φ4 : Fin 4 → ℝ := Fin.snoc half_16_12_φ3 (931866241/10000000000 : ℝ)

def half_16_12_φ5 : Fin 5 → ℝ := Fin.snoc half_16_12_φ4 (199685623/2500000000 : ℝ)

theorem half_16_12_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_16_12_φ5) (758019427/125000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_16_12_φ5 (by norm_num [half_16_12_φ1, half_16_12_φ2, half_16_12_φ3, half_16_12_φ4, half_16_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_12_φ1, half_16_12_φ2, half_16_12_φ3, half_16_12_φ4, half_16_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_12_φ1, half_16_12_φ2, half_16_12_φ3, half_16_12_φ4, half_16_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_16_12_φ1, half_16_12_φ2, half_16_12_φ3, half_16_12_φ4, half_16_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_16_12_φ1, half_16_12_φ2, half_16_12_φ3, half_16_12_φ4, half_16_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_16_12_hx5 : SourcePowerBound (powerBoxCross 8 11 32 half_16_12_φ5) (92919103187/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 11) (r := 2) (v := 14) (w := 15) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_16_12_φ5 (by norm_num [half_16_12_φ1, half_16_12_φ2, half_16_12_φ3, half_16_12_φ4, half_16_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_12_φ1, half_16_12_φ2, half_16_12_φ3, half_16_12_φ4, half_16_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_16_12_hF2 (half_14_12) (half_15_12)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_16_12_φ1, half_16_12_φ2, half_16_12_φ3, half_16_12_φ4, half_16_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_12_hx4 : SourcePowerBound (powerBoxCross 8 12 16 half_16_12_φ4) (111106535071/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 12) (u := 10) (t := 13)
    (D := 16) (ψ := (199685623/2500000000 : ℝ)) half_16_12_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_12_φ1, half_16_12_φ2, half_16_12_φ3, half_16_12_φ4, half_16_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_12_φ1, half_16_12_φ2, half_16_12_φ3, half_16_12_φ4, half_16_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_12_φ1, half_16_12_φ2, half_16_12_φ3, half_16_12_φ4, half_16_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_11_12) (half_13_12)
    (by simpa only [half_16_12_φ5, show (2:ℝ)*16=32 by norm_num] using half_16_12_hx5)
  exact h.weaken (by norm_num [half_16_12_φ1, half_16_12_φ2, half_16_12_φ3, half_16_12_φ4, half_16_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_12_hx3 : SourcePowerBound (powerBoxCross 8 13 8 half_16_12_φ3) (135514738211/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 13) (u := 11) (t := 14)
    (D := 8) (ψ := (931866241/10000000000 : ℝ)) half_16_12_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_12_φ1, half_16_12_φ2, half_16_12_φ3, half_16_12_φ4, half_16_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_12_φ1, half_16_12_φ2, half_16_12_φ3, half_16_12_φ4, half_16_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_12_φ1, half_16_12_φ2, half_16_12_φ3, half_16_12_φ4, half_16_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_12_12) (half_14_12)
    (by simpa only [half_16_12_φ4, show (2:ℝ)*8=16 by norm_num] using half_16_12_hx4)
  exact h.weaken (by norm_num [half_16_12_φ1, half_16_12_φ2, half_16_12_φ3, half_16_12_φ4, half_16_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_12_hx2 : SourcePowerBound (powerBoxCross 8 14 4 half_16_12_φ2) (83859610289/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 14) (u := 12) (t := 15)
    (D := 4) (ψ := (543588641/5000000000 : ℝ)) half_16_12_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_12_φ1, half_16_12_φ2, half_16_12_φ3, half_16_12_φ4, half_16_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_12_φ1, half_16_12_φ2, half_16_12_φ3, half_16_12_φ4, half_16_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_12_φ1, half_16_12_φ2, half_16_12_φ3, half_16_12_φ4, half_16_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_13_12) (half_15_12)
    (by simpa only [half_16_12_φ3, show (2:ℝ)*4=8 by norm_num] using half_16_12_hx3)
  exact h.weaken (by norm_num [half_16_12_φ1, half_16_12_φ2, half_16_12_φ3, half_16_12_φ4, half_16_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_12_hx1 : SourcePowerBound (powerBoxCross 8 15 2 half_16_12_φ1) (103534215813/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 15) (u := 13) (t := 16)
    (D := 2) (ψ := (1185108309/10000000000 : ℝ)) half_16_12_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_12_φ1, half_16_12_φ2, half_16_12_φ3, half_16_12_φ4, half_16_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_12_φ1, half_16_12_φ2, half_16_12_φ3, half_16_12_φ4, half_16_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_12_φ1, half_16_12_φ2, half_16_12_φ3, half_16_12_φ4, half_16_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_14_12) (half_16_11)
    (by simpa only [half_16_12_φ2, show (2:ℝ)*2=4 by norm_num] using half_16_12_hx2)
  exact h.weaken (by norm_num [half_16_12_φ1, half_16_12_φ2, half_16_12_φ3, half_16_12_φ4, half_16_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_12 : AdmissibleExponent 8 32 (24200330239/1000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 14) (ψ := (301162679/2500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_15_12)
    (by simpa only [half_16_12_φ1] using half_16_12_hx1)
  exact admissibleExponent_mono h (by norm_num [half_16_12_φ1, half_16_12_φ2, half_16_12_φ3, half_16_12_φ4, half_16_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_17_12_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (609151147/5000000000 : ℝ)

def half_17_12_φ2 : Fin 2 → ℝ := Fin.snoc half_17_12_φ1 (150761213/1250000000 : ℝ)

def half_17_12_φ3 : Fin 3 → ℝ := Fin.snoc half_17_12_φ2 (541114857/5000000000 : ℝ)

def half_17_12_φ4 : Fin 4 → ℝ := Fin.snoc half_17_12_φ3 (927625469/10000000000 : ℝ)

def half_17_12_φ5 : Fin 5 → ℝ := Fin.snoc half_17_12_φ4 (159021509/2000000000 : ℝ)

theorem half_17_12_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_17_12_φ5) (30091775377/5000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_17_12_φ5 (by norm_num [half_17_12_φ1, half_17_12_φ2, half_17_12_φ3, half_17_12_φ4, half_17_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_12_φ1, half_17_12_φ2, half_17_12_φ3, half_17_12_φ4, half_17_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_12_φ1, half_17_12_φ2, half_17_12_φ3, half_17_12_φ4, half_17_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_17_12_φ1, half_17_12_φ2, half_17_12_φ3, half_17_12_φ4, half_17_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_17_12_φ1, half_17_12_φ2, half_17_12_φ3, half_17_12_φ4, half_17_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_17_12_hx5 : SourcePowerBound (powerBoxCross 8 12 32 half_17_12_φ5) (50817140501/5000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 12) (r := 2) (v := 0) (w := 16) (D := 32)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_17_12_φ5 (by norm_num [half_17_12_φ1, half_17_12_φ2, half_17_12_φ3, half_17_12_φ4, half_17_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_12_φ1, half_17_12_φ2, half_17_12_φ3, half_17_12_φ4, half_17_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_17_12_hF2 (admissibleExponent_zero 8) (half_16_12)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_17_12_φ1, half_17_12_φ2, half_17_12_φ3, half_17_12_φ4, half_17_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_12_hx4 : SourcePowerBound (powerBoxCross 8 13 16 half_17_12_φ4) (30277119893/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 13) (u := 11) (t := 14)
    (D := 16) (ψ := (159021509/2000000000 : ℝ)) half_17_12_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_12_φ1, half_17_12_φ2, half_17_12_φ3, half_17_12_φ4, half_17_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_12_φ1, half_17_12_φ2, half_17_12_φ3, half_17_12_φ4, half_17_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_12_φ1, half_17_12_φ2, half_17_12_φ3, half_17_12_φ4, half_17_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_12_12) (half_14_12)
    (by simpa only [half_17_12_φ5, show (2:ℝ)*16=32 by norm_num] using half_17_12_hx5)
  exact h.weaken (by norm_num [half_17_12_φ1, half_17_12_φ2, half_17_12_φ3, half_17_12_φ4, half_17_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_12_hx3 : SourcePowerBound (powerBoxCross 8 14 8 half_17_12_φ3) (73588478613/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 14) (u := 12) (t := 15)
    (D := 8) (ψ := (927625469/10000000000 : ℝ)) half_17_12_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_12_φ1, half_17_12_φ2, half_17_12_φ3, half_17_12_φ4, half_17_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_12_φ1, half_17_12_φ2, half_17_12_φ3, half_17_12_φ4, half_17_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_12_φ1, half_17_12_φ2, half_17_12_φ3, half_17_12_φ4, half_17_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_13_12) (half_15_12)
    (by simpa only [half_17_12_φ4, show (2:ℝ)*8=16 by norm_num] using half_17_12_hx4)
  exact h.weaken (by norm_num [half_17_12_φ1, half_17_12_φ2, half_17_12_φ3, half_17_12_φ4, half_17_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_12_hx2 : SourcePowerBound (powerBoxCross 8 15 4 half_17_12_φ2) (22672414433/1250000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 15) (u := 13) (t := 16)
    (D := 4) (ψ := (541114857/5000000000 : ℝ)) half_17_12_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_12_φ1, half_17_12_φ2, half_17_12_φ3, half_17_12_φ4, half_17_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_12_φ1, half_17_12_φ2, half_17_12_φ3, half_17_12_φ4, half_17_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_12_φ1, half_17_12_φ2, half_17_12_φ3, half_17_12_φ4, half_17_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_14_12) (half_16_12)
    (by simpa only [half_17_12_φ3, show (2:ℝ)*4=8 by norm_num] using half_17_12_hx3)
  exact h.weaken (by norm_num [half_17_12_φ1, half_17_12_φ2, half_17_12_φ3, half_17_12_φ4, half_17_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_12_hx1 : SourcePowerBound (powerBoxCross 8 16 2 half_17_12_φ1) (223738286841/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 16) (u := 14) (t := 17)
    (D := 2) (ψ := (150761213/1250000000 : ℝ)) half_17_12_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_12_φ1, half_17_12_φ2, half_17_12_φ3, half_17_12_φ4, half_17_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_12_φ1, half_17_12_φ2, half_17_12_φ3, half_17_12_φ4, half_17_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_12_φ1, half_17_12_φ2, half_17_12_φ3, half_17_12_φ4, half_17_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_15_12) (half_17_11)
    (by simpa only [half_17_12_φ2, show (2:ℝ)*2=4 by norm_num] using half_17_12_hx2)
  exact h.weaken (by norm_num [half_17_12_φ1, half_17_12_φ2, half_17_12_φ3, half_17_12_φ4, half_17_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_12 : AdmissibleExponent 8 34 (52301131591/2000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 15) (ψ := (609151147/5000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_16_12)
    (by simpa only [half_17_12_φ1] using half_17_12_hx1)
  exact admissibleExponent_mono h (by norm_num [half_17_12_φ1, half_17_12_φ2, half_17_12_φ3, half_17_12_φ4, half_17_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_18_12_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (245753871/2000000000 : ℝ)

def half_18_12_φ2 : Fin 2 → ℝ := Fin.snoc half_18_12_φ1 (305531871/2500000000 : ℝ)

def half_18_12_φ3 : Fin 3 → ℝ := Fin.snoc half_18_12_φ2 (269610827/2500000000 : ℝ)

def half_18_12_φ4 : Fin 4 → ℝ := Fin.snoc half_18_12_φ3 (462189989/5000000000 : ℝ)

def half_18_12_φ5 : Fin 5 → ℝ := Fin.snoc half_18_12_φ4 (12380089/156250000 : ℝ)

theorem half_18_12_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_18_12_φ5) (59833037759/10000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_18_12_φ5 (by norm_num [half_18_12_φ1, half_18_12_φ2, half_18_12_φ3, half_18_12_φ4, half_18_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_18_12_φ1, half_18_12_φ2, half_18_12_φ3, half_18_12_φ4, half_18_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_18_12_φ1, half_18_12_φ2, half_18_12_φ3, half_18_12_φ4, half_18_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_18_12_φ1, half_18_12_φ2, half_18_12_φ3, half_18_12_φ4, half_18_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_18_12_φ1, half_18_12_φ2, half_18_12_φ3, half_18_12_φ4, half_18_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_18_12_hx5 : SourcePowerBound (powerBoxCross 8 13 32 half_18_12_φ5) (110532395637/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 13) (r := 2) (v := 17) (w := 18) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_18_12_φ5 (by norm_num [half_18_12_φ1, half_18_12_φ2, half_18_12_φ3, half_18_12_φ4, half_18_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_18_12_φ1, half_18_12_φ2, half_18_12_φ3, half_18_12_φ4, half_18_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_18_12_hF2 (half_17_12) (half_18_11)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_18_12_φ1, half_18_12_φ2, half_18_12_φ3, half_18_12_φ4, half_18_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_18_12_hx4 : SourcePowerBound (powerBoxCross 8 14 16 half_18_12_φ4) (65668674209/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 14) (u := 12) (t := 15)
    (D := 16) (ψ := (12380089/156250000 : ℝ)) half_18_12_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_18_12_φ1, half_18_12_φ2, half_18_12_φ3, half_18_12_φ4, half_18_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_18_12_φ1, half_18_12_φ2, half_18_12_φ3, half_18_12_φ4, half_18_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_18_12_φ1, half_18_12_φ2, half_18_12_φ3, half_18_12_φ4, half_18_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_13_12) (half_15_12)
    (by simpa only [half_18_12_φ5, show (2:ℝ)*16=32 by norm_num] using half_18_12_hx5)
  exact h.weaken (by norm_num [half_18_12_φ1, half_18_12_φ2, half_18_12_φ3, half_18_12_φ4, half_18_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_18_12_hx3 : SourcePowerBound (powerBoxCross 8 15 8 half_18_12_φ3) (159091166051/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 15) (u := 13) (t := 16)
    (D := 8) (ψ := (462189989/5000000000 : ℝ)) half_18_12_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_18_12_φ1, half_18_12_φ2, half_18_12_φ3, half_18_12_φ4, half_18_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_18_12_φ1, half_18_12_φ2, half_18_12_φ3, half_18_12_φ4, half_18_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_18_12_φ1, half_18_12_φ2, half_18_12_φ3, half_18_12_φ4, half_18_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_14_12) (half_16_12)
    (by simpa only [half_18_12_φ4, show (2:ℝ)*8=16 by norm_num] using half_18_12_hx4)
  exact h.weaken (by norm_num [half_18_12_φ1, half_18_12_φ2, half_18_12_φ3, half_18_12_φ4, half_18_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_18_12_hx2 : SourcePowerBound (powerBoxCross 8 16 4 half_18_12_φ2) (19531153151/1000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 16) (u := 14) (t := 17)
    (D := 4) (ψ := (269610827/2500000000 : ℝ)) half_18_12_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_18_12_φ1, half_18_12_φ2, half_18_12_φ3, half_18_12_φ4, half_18_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_18_12_φ1, half_18_12_φ2, half_18_12_φ3, half_18_12_φ4, half_18_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_18_12_φ1, half_18_12_φ2, half_18_12_φ3, half_18_12_φ4, half_18_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_15_12) (half_17_12)
    (by simpa only [half_18_12_φ3, show (2:ℝ)*4=8 by norm_num] using half_18_12_hx3)
  exact h.weaken (by norm_num [half_18_12_φ1, half_18_12_φ2, half_18_12_φ3, half_18_12_φ4, half_18_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_18_12_hx1 : SourcePowerBound (powerBoxCross 8 17 2 half_18_12_φ1) (240601413449/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 17) (u := 15) (t := 18)
    (D := 2) (ψ := (305531871/2500000000 : ℝ)) half_18_12_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_18_12_φ1, half_18_12_φ2, half_18_12_φ3, half_18_12_φ4, half_18_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_18_12_φ1, half_18_12_φ2, half_18_12_φ3, half_18_12_φ4, half_18_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_18_12_φ1, half_18_12_φ2, half_18_12_φ3, half_18_12_φ4, half_18_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_16_12) (half_18_11)
    (by simpa only [half_18_12_φ2, show (2:ℝ)*2=4 by norm_num] using half_18_12_hx2)
  exact h.weaken (by norm_num [half_18_12_φ1, half_18_12_φ2, half_18_12_φ3, half_18_12_φ4, half_18_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_18_12 : AdmissibleExponent 8 36 (70287700541/2500000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 16) (ψ := (245753871/2000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_17_12)
    (by simpa only [half_18_12_φ1] using half_18_12_hx1)
  exact admissibleExponent_mono h (by norm_num [half_18_12_φ1, half_18_12_φ2, half_18_12_φ3, half_18_12_φ4, half_18_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_19_12_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (19317091/156250000 : ℝ)

def half_19_12_φ2 : Fin 2 → ℝ := Fin.snoc half_19_12_φ1 (617062329/5000000000 : ℝ)

def half_19_12_φ3 : Fin 3 → ℝ := Fin.snoc half_19_12_φ2 (537827251/5000000000 : ℝ)

def half_19_12_φ4 : Fin 4 → ℝ := Fin.snoc half_19_12_φ3 (921989573/10000000000 : ℝ)

def half_19_12_φ5 : Fin 5 → ℝ := Fin.snoc half_19_12_φ4 (790276777/10000000000 : ℝ)

theorem half_19_12_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_19_12_φ5) (29787436993/5000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_19_12_φ5 (by norm_num [half_19_12_φ1, half_19_12_φ2, half_19_12_φ3, half_19_12_φ4, half_19_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_19_12_φ1, half_19_12_φ2, half_19_12_φ3, half_19_12_φ4, half_19_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_19_12_φ1, half_19_12_φ2, half_19_12_φ3, half_19_12_φ4, half_19_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_19_12_φ1, half_19_12_φ2, half_19_12_φ3, half_19_12_φ4, half_19_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_19_12_φ1, half_19_12_φ2, half_19_12_φ3, half_19_12_φ4, half_19_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_19_12_hx5 : SourcePowerBound (powerBoxCross 8 14 32 half_19_12_φ5) (59780338203/5000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 14) (r := 2) (v := 18) (w := 19) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_19_12_φ5 (by norm_num [half_19_12_φ1, half_19_12_φ2, half_19_12_φ3, half_19_12_φ4, half_19_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_19_12_φ1, half_19_12_φ2, half_19_12_φ3, half_19_12_φ4, half_19_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_19_12_hF2 (half_18_12) (half_19_11)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_19_12_φ1, half_19_12_φ2, half_19_12_φ3, half_19_12_φ4, half_19_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_19_12_hx4 : SourcePowerBound (powerBoxCross 8 15 16 half_19_12_φ4) (28349642447/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 15) (u := 13) (t := 16)
    (D := 16) (ψ := (790276777/10000000000 : ℝ)) half_19_12_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_19_12_φ1, half_19_12_φ2, half_19_12_φ3, half_19_12_φ4, half_19_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_19_12_φ1, half_19_12_φ2, half_19_12_φ3, half_19_12_φ4, half_19_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_19_12_φ1, half_19_12_φ2, half_19_12_φ3, half_19_12_φ4, half_19_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_14_12) (half_16_12)
    (by simpa only [half_19_12_φ5, show (2:ℝ)*16=32 by norm_num] using half_19_12_hx5)
  exact h.weaken (by norm_num [half_19_12_φ1, half_19_12_φ2, half_19_12_φ3, half_19_12_φ4, half_19_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_19_12_hx3 : SourcePowerBound (powerBoxCross 8 16 8 half_19_12_φ3) (85609310509/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 16) (u := 14) (t := 17)
    (D := 8) (ψ := (921989573/10000000000 : ℝ)) half_19_12_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_19_12_φ1, half_19_12_φ2, half_19_12_φ3, half_19_12_φ4, half_19_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_19_12_φ1, half_19_12_φ2, half_19_12_φ3, half_19_12_φ4, half_19_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_19_12_φ1, half_19_12_φ2, half_19_12_φ3, half_19_12_φ4, half_19_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_15_12) (half_17_12)
    (by simpa only [half_19_12_φ4, show (2:ℝ)*8=16 by norm_num] using half_19_12_hx4)
  exact h.weaken (by norm_num [half_19_12_φ1, half_19_12_φ2, half_19_12_φ3, half_19_12_φ4, half_19_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_19_12_hx2 : SourcePowerBound (powerBoxCross 8 17 4 half_19_12_φ2) (209482884791/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 17) (u := 15) (t := 18)
    (D := 4) (ψ := (537827251/5000000000 : ℝ)) half_19_12_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_19_12_φ1, half_19_12_φ2, half_19_12_φ3, half_19_12_φ4, half_19_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_19_12_φ1, half_19_12_φ2, half_19_12_φ3, half_19_12_φ4, half_19_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_19_12_φ1, half_19_12_φ2, half_19_12_φ3, half_19_12_φ4, half_19_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_16_12) (half_18_12)
    (by simpa only [half_19_12_φ3, show (2:ℝ)*4=8 by norm_num] using half_19_12_hx3)
  exact h.weaken (by norm_num [half_19_12_φ1, half_19_12_φ2, half_19_12_φ3, half_19_12_φ4, half_19_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_19_12_hx1 : SourcePowerBound (powerBoxCross 8 18 2 half_19_12_φ1) (257628595957/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 18) (u := 16) (t := 19)
    (D := 2) (ψ := (617062329/5000000000 : ℝ)) half_19_12_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_19_12_φ1, half_19_12_φ2, half_19_12_φ3, half_19_12_φ4, half_19_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_19_12_φ1, half_19_12_φ2, half_19_12_φ3, half_19_12_φ4, half_19_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_19_12_φ1, half_19_12_φ2, half_19_12_φ3, half_19_12_φ4, half_19_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_17_12) (half_19_11)
    (by simpa only [half_19_12_φ2, show (2:ℝ)*2=4 by norm_num] using half_19_12_hx2)
  exact h.weaken (by norm_num [half_19_12_φ1, half_19_12_φ2, half_19_12_φ3, half_19_12_φ4, half_19_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_19_12 : AdmissibleExponent 8 38 (300898879797/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 17) (ψ := (19317091/156250000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_18_12)
    (by simpa only [half_19_12_φ1] using half_19_12_hx1)
  exact admissibleExponent_mono h (by norm_num [half_19_12_φ1, half_19_12_φ2, half_19_12_φ3, half_19_12_φ4, half_19_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_20_12_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1241761661/10000000000 : ℝ)

def half_20_12_φ2 : Fin 2 → ℝ := Fin.snoc half_20_12_φ1 (1242780423/10000000000 : ℝ)

def half_20_12_φ3 : Fin 3 → ℝ := Fin.snoc half_20_12_φ2 (268409211/2500000000 : ℝ)

def half_20_12_φ4 : Fin 4 → ℝ := Fin.snoc half_20_12_φ3 (115032519/1250000000 : ℝ)

def half_20_12_φ5 : Fin 5 → ℝ := Fin.snoc half_20_12_φ4 (49299651/625000000 : ℝ)

theorem half_20_12_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_20_12_φ5) (7423512073/1250000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_20_12_φ5 (by norm_num [half_20_12_φ1, half_20_12_φ2, half_20_12_φ3, half_20_12_φ4, half_20_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_20_12_φ1, half_20_12_φ2, half_20_12_φ3, half_20_12_φ4, half_20_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_20_12_φ1, half_20_12_φ2, half_20_12_φ3, half_20_12_φ4, half_20_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_20_12_φ1, half_20_12_φ2, half_20_12_φ3, half_20_12_φ4, half_20_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_20_12_φ1, half_20_12_φ2, half_20_12_φ3, half_20_12_φ4, half_20_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_20_12_hx5 : SourcePowerBound (powerBoxCross 8 15 32 half_20_12_φ5) (128691012087/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 15) (r := 2) (v := 0) (w := 20) (D := 32)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_20_12_φ5 (by norm_num [half_20_12_φ1, half_20_12_φ2, half_20_12_φ3, half_20_12_φ4, half_20_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_20_12_φ1, half_20_12_φ2, half_20_12_φ3, half_20_12_φ4, half_20_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_20_12_hF2 (admissibleExponent_zero 8) (half_20_11)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_20_12_φ1, half_20_12_φ2, half_20_12_φ3, half_20_12_φ4, half_20_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_20_12_hx4 : SourcePowerBound (powerBoxCross 8 16 16 half_20_12_φ4) (76152229681/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 16) (u := 14) (t := 17)
    (D := 16) (ψ := (49299651/625000000 : ℝ)) half_20_12_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_20_12_φ1, half_20_12_φ2, half_20_12_φ3, half_20_12_φ4, half_20_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_20_12_φ1, half_20_12_φ2, half_20_12_φ3, half_20_12_φ4, half_20_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_20_12_φ1, half_20_12_φ2, half_20_12_φ3, half_20_12_φ4, half_20_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_15_12) (half_17_12)
    (by simpa only [half_20_12_φ5, show (2:ℝ)*16=32 by norm_num] using half_20_12_hx5)
  exact h.weaken (by norm_num [half_20_12_φ1, half_20_12_φ2, half_20_12_φ3, half_20_12_φ4, half_20_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_20_12_hx3 : SourcePowerBound (powerBoxCross 8 17 8 half_20_12_φ3) (183518793879/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 17) (u := 15) (t := 18)
    (D := 8) (ψ := (115032519/1250000000 : ℝ)) half_20_12_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_20_12_φ1, half_20_12_φ2, half_20_12_φ3, half_20_12_φ4, half_20_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_20_12_φ1, half_20_12_φ2, half_20_12_φ3, half_20_12_φ4, half_20_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_20_12_φ1, half_20_12_φ2, half_20_12_φ3, half_20_12_φ4, half_20_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_16_12) (half_18_12)
    (by simpa only [half_20_12_φ4, show (2:ℝ)*8=16 by norm_num] using half_20_12_hx4)
  exact h.weaken (by norm_num [half_20_12_φ1, half_20_12_φ2, half_20_12_φ3, half_20_12_φ4, half_20_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_20_12_hx2 : SourcePowerBound (powerBoxCross 8 18 4 half_20_12_φ2) (3497627359/156250000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 18) (u := 16) (t := 19)
    (D := 4) (ψ := (268409211/2500000000 : ℝ)) half_20_12_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_20_12_φ1, half_20_12_φ2, half_20_12_φ3, half_20_12_φ4, half_20_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_20_12_φ1, half_20_12_φ2, half_20_12_φ3, half_20_12_φ4, half_20_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_20_12_φ1, half_20_12_φ2, half_20_12_φ3, half_20_12_φ4, half_20_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_17_12) (half_19_12)
    (by simpa only [half_20_12_φ3, show (2:ℝ)*4=8 by norm_num] using half_20_12_hx3)
  exact h.weaken (by norm_num [half_20_12_φ1, half_20_12_φ2, half_20_12_φ3, half_20_12_φ4, half_20_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_20_12_hx1 : SourcePowerBound (powerBoxCross 8 19 2 half_20_12_φ1) (274776172187/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 19) (u := 17) (t := 20)
    (D := 2) (ψ := (1242780423/10000000000 : ℝ)) half_20_12_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_20_12_φ1, half_20_12_φ2, half_20_12_φ3, half_20_12_φ4, half_20_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_20_12_φ1, half_20_12_φ2, half_20_12_φ3, half_20_12_φ4, half_20_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_20_12_φ1, half_20_12_φ2, half_20_12_φ3, half_20_12_φ4, half_20_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_18_12) (half_20_11)
    (by simpa only [half_20_12_φ2, show (2:ℝ)*2=4 by norm_num] using half_20_12_hx2)
  exact h.weaken (by norm_num [half_20_12_φ1, half_20_12_φ2, half_20_12_φ3, half_20_12_φ4, half_20_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_20_12 : AdmissibleExponent 8 40 (80180338411/2500000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 18) (ψ := (1241761661/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_19_12)
    (by simpa only [half_20_12_φ1] using half_20_12_hx1)
  exact admissibleExponent_mono h (by norm_num [half_20_12_φ1, half_20_12_φ2, half_20_12_φ3, half_20_12_φ4, half_20_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem alternate_source8_admissible :
    Certificate.AdmissibleCurve 8 Certificate.alternateSource8 := by
  apply Certificate.admissibleCurve_of_highOrder (by norm_num)
    (by decide +kernel : Certificate.LowSeedShape Certificate.alternateSource8)
  intro i hi hsize
  have htop : i ≤ 20 := by norm_num [Certificate.alternateSource8] at hsize; omega
  interval_cases i
  · simpa [Certificate.alternateSource8, Certificate.Q] using SeedCompletionEven8SecondSeeds.degree8_half_3
  · simpa [Certificate.alternateSource8, Certificate.Q] using SeedCompletionEven8SecondSeeds.degree8_half_4
  · simpa [Certificate.alternateSource8, Certificate.Q] using SeedCompletionEven8SecondSeeds.degree8_half_5
  · simpa [Certificate.alternateSource8, Certificate.Q] using SeedCompletionEven8SecondSeeds.degree8_half_6
  · simpa [Certificate.alternateSource8, Certificate.Q] using SeedCompletionHigher8SimpleSeeds.degree8_half_7
  · simpa [Certificate.alternateSource8, Certificate.Q] using SeedCompletionHigher8SimpleSeeds.degree8_half_8
  · simpa [Certificate.alternateSource8, Certificate.Q] using SeedCompletionHigher8SimpleSeeds.degree8_half_9
  · simpa [Certificate.alternateSource8, Certificate.Q] using half_10_12
  · simpa [Certificate.alternateSource8, Certificate.Q] using half_11_12
  · simpa [Certificate.alternateSource8, Certificate.Q] using half_12_12
  · simpa [Certificate.alternateSource8, Certificate.Q] using half_13_12
  · simpa [Certificate.alternateSource8, Certificate.Q] using half_14_12
  · simpa [Certificate.alternateSource8, Certificate.Q] using half_15_12
  · simpa [Certificate.alternateSource8, Certificate.Q] using half_16_12
  · simpa [Certificate.alternateSource8, Certificate.Q] using half_17_12
  · simpa [Certificate.alternateSource8, Certificate.Q] using half_18_12
  · simpa [Certificate.alternateSource8, Certificate.Q] using half_19_12
  · simpa [Certificate.alternateSource8, Certificate.Q] using half_20_12

#print axioms alternate_source8_admissible
end Waring.SeedCompletionAlternate8Seeds
