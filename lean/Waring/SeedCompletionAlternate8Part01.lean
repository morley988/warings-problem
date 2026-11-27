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

theorem half_10_00 : AdmissibleExponent 8 20 (33178241493/2500000000 : ℝ) := by
  have h := endpoint_admissible (s := 8) (by norm_num : 0 < (8 : ℕ))
    (SeedCompletionHigher8SimpleSeeds.degree8_half_9) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

theorem half_11_00 : AdmissibleExponent 8 22 (75561922613/5000000000 : ℝ) := by
  have h := endpoint_admissible (s := 9) (by norm_num : 0 < (8 : ℕ))
    (half_10_00) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

theorem half_12_00 : AdmissibleExponent 8 24 (169733364573/10000000000 : ℝ) := by
  have h := endpoint_admissible (s := 10) (by norm_num : 0 < (8 : ℕ))
    (half_11_00) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

theorem half_13_00 : AdmissibleExponent 8 26 (94258347001/5000000000 : ℝ) := by
  have h := endpoint_admissible (s := 11) (by norm_num : 0 < (8 : ℕ))
    (half_12_00) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

theorem half_14_00 : AdmissibleExponent 8 28 (51863026813/2500000000 : ℝ) := by
  have h := endpoint_admissible (s := 12) (by norm_num : 0 < (8 : ℕ))
    (half_13_00) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

theorem half_15_00 : AdmissibleExponent 8 30 (113260296923/5000000000 : ℝ) := by
  have h := endpoint_admissible (s := 13) (by norm_num : 0 < (8 : ℕ))
    (half_14_00) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

theorem half_16_00 : AdmissibleExponent 8 32 (479893593/19531250 : ℝ) := by
  have h := endpoint_admissible (s := 14) (by norm_num : 0 < (8 : ℕ))
    (half_15_00) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

theorem half_17_00 : AdmissibleExponent 8 34 (4140505151/156250000 : ℝ) := by
  have h := endpoint_admissible (s := 15) (by norm_num : 0 < (8 : ℕ))
    (half_16_00) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

theorem half_18_00 : AdmissibleExponent 8 36 (35546036057/1250000000 : ℝ) := by
  have h := endpoint_admissible (s := 16) (by norm_num : 0 < (8 : ℕ))
    (half_17_00) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

theorem half_19_00 : AdmissibleExponent 8 38 (303822252399/10000000000 : ℝ) := by
  have h := endpoint_admissible (s := 17) (by norm_num : 0 < (8 : ℕ))
    (half_18_00) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

theorem half_20_00 : AdmissibleExponent 8 40 (6466889417/200000000 : ℝ) := by
  have h := endpoint_admissible (s := 18) (by norm_num : 0 < (8 : ℕ))
    (half_19_00) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

def half_10_01_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (555590601/5000000000 : ℝ)

def half_10_01_φ2 : Fin 2 → ℝ := Fin.snoc half_10_01_φ1 (192525219/2000000000 : ℝ)

def half_10_01_φ3 : Fin 3 → ℝ := Fin.snoc half_10_01_φ2 (841121209/10000000000 : ℝ)

def half_10_01_φ4 : Fin 4 → ℝ := Fin.snoc half_10_01_φ3 (282212861/5000000000 : ℝ)

theorem half_10_01_hF2 : SourcePowerBound (paddedMoment 8 0 2 16 half_10_01_φ4) (16733390303/2500000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 4) (r := 0) (n := 1) (D := 16)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_10_01_φ4 (by norm_num [half_10_01_φ1, half_10_01_φ2, half_10_01_φ3, half_10_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_01_φ1, half_10_01_φ2, half_10_01_φ3, half_10_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_01_φ1, half_10_01_φ2, half_10_01_φ3, half_10_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_10_01_φ1, half_10_01_φ2, half_10_01_φ3, half_10_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_10_01_φ1, half_10_01_φ2, half_10_01_φ3, half_10_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_10_01_hx4 : SourcePowerBound (powerBoxCross 8 6 16 half_10_01_φ4) (32434876503/5000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 6) (r := 2) (v := 0) (w := 8) (D := 16)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_10_01_φ4 (by norm_num [half_10_01_φ1, half_10_01_φ2, half_10_01_φ3, half_10_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_01_φ1, half_10_01_φ2, half_10_01_φ3, half_10_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_10_01_hF2 (admissibleExponent_zero 8) (SeedCompletionHigher8SimpleSeeds.degree8_half_8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_10_01_φ1, half_10_01_φ2, half_10_01_φ3, half_10_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_01_hx3 : SourcePowerBound (powerBoxCross 8 7 8 half_10_01_φ3) (75205658937/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 7) (u := 5) (t := 8)
    (D := 8) (ψ := (282212861/5000000000 : ℝ)) half_10_01_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_01_φ1, half_10_01_φ2, half_10_01_φ3, half_10_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_01_φ1, half_10_01_φ2, half_10_01_φ3, half_10_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_01_φ1, half_10_01_φ2, half_10_01_φ3, half_10_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionEven8SecondSeeds.degree8_half_6) (SeedCompletionHigher8SimpleSeeds.degree8_half_8)
    (by simpa only [half_10_01_φ4, show (2:ℝ)*8=16 by norm_num] using half_10_01_hx4)
  exact h.weaken (by norm_num [half_10_01_φ1, half_10_01_φ2, half_10_01_φ3, half_10_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_01_hx2 : SourcePowerBound (powerBoxCross 8 8 4 half_10_01_φ2) (18240155839/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 8) (u := 6) (t := 9)
    (D := 4) (ψ := (841121209/10000000000 : ℝ)) half_10_01_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_01_φ1, half_10_01_φ2, half_10_01_φ3, half_10_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_01_φ1, half_10_01_φ2, half_10_01_φ3, half_10_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_01_φ1, half_10_01_φ2, half_10_01_φ3, half_10_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_7) (SeedCompletionHigher8SimpleSeeds.degree8_half_9)
    (by simpa only [half_10_01_φ3, show (2:ℝ)*4=8 by norm_num] using half_10_01_hx3)
  exact h.weaken (by norm_num [half_10_01_φ1, half_10_01_φ2, half_10_01_φ3, half_10_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_01_hx1 : SourcePowerBound (powerBoxCross 8 9 2 half_10_01_φ1) (112914026437/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 9) (u := 7) (t := 10)
    (D := 2) (ψ := (192525219/2000000000 : ℝ)) half_10_01_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_01_φ1, half_10_01_φ2, half_10_01_φ3, half_10_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_01_φ1, half_10_01_φ2, half_10_01_φ3, half_10_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_01_φ1, half_10_01_φ2, half_10_01_φ3, half_10_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_8) (half_10_00)
    (by simpa only [half_10_01_φ2, show (2:ℝ)*2=4 by norm_num] using half_10_01_hx2)
  exact h.weaken (by norm_num [half_10_01_φ1, half_10_01_φ2, half_10_01_φ3, half_10_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_01 : AdmissibleExponent 8 20 (131804106871/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 8) (ψ := (555590601/5000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_9)
    (by simpa only [half_10_01_φ1] using half_10_01_hx1)
  exact admissibleExponent_mono h (by norm_num [half_10_01_φ1, half_10_01_φ2, half_10_01_φ3, half_10_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem chord_1 : AdmissibleExponent 8 22 (14128903367/937500000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 22) (t := (2/3 : ℝ))
    (half_10_01) (half_13_00) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1 <;> norm_num

theorem chord_2 : AdmissibleExponent 8 24 (4070699959/240000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 24) (t := (1/3 : ℝ))
    (half_10_01) (half_13_00) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1 <;> norm_num

def half_11_01_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (45644563/400000000 : ℝ)

def half_11_01_φ2 : Fin 2 → ℝ := Fin.snoc half_11_01_φ1 (1040850559/10000000000 : ℝ)

def half_11_01_φ3 : Fin 3 → ℝ := Fin.snoc half_11_01_φ2 (465749299/5000000000 : ℝ)

def half_11_01_φ4 : Fin 4 → ℝ := Fin.snoc half_11_01_φ3 (191949289/2500000000 : ℝ)

theorem half_11_01_hF2 : SourcePowerBound (paddedMoment 8 0 2 16 half_11_01_φ4) (14623382963/2500000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 4) (r := 0) (n := 1) (D := 16)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_11_01_φ4 (by norm_num [half_11_01_φ1, half_11_01_φ2, half_11_01_φ3, half_11_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_01_φ1, half_11_01_φ2, half_11_01_φ3, half_11_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_01_φ1, half_11_01_φ2, half_11_01_φ3, half_11_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_11_01_φ1, half_11_01_φ2, half_11_01_φ3, half_11_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_11_01_φ1, half_11_01_φ2, half_11_01_φ3, half_11_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_11_01_hx4 : SourcePowerBound (powerBoxCross 8 7 16 half_11_01_φ4) (13964789293/2000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 7) (r := 2) (v := 9) (w := 10) (D := 16)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_11_01_φ4 (by norm_num [half_11_01_φ1, half_11_01_φ2, half_11_01_φ3, half_11_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_01_φ1, half_11_01_φ2, half_11_01_φ3, half_11_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_11_01_hF2 (SeedCompletionHigher8SimpleSeeds.degree8_half_9) (half_10_01)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_11_01_φ1, half_11_01_φ2, half_11_01_φ3, half_11_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_01_hx3 : SourcePowerBound (powerBoxCross 8 8 8 half_11_01_φ3) (83440977709/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 8) (u := 6) (t := 9)
    (D := 8) (ψ := (191949289/2500000000 : ℝ)) half_11_01_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_01_φ1, half_11_01_φ2, half_11_01_φ3, half_11_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_01_φ1, half_11_01_φ2, half_11_01_φ3, half_11_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_01_φ1, half_11_01_φ2, half_11_01_φ3, half_11_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_7) (SeedCompletionHigher8SimpleSeeds.degree8_half_9)
    (by simpa only [half_11_01_φ4, show (2:ℝ)*8=16 by norm_num] using half_11_01_hx4)
  exact h.weaken (by norm_num [half_11_01_φ1, half_11_01_φ2, half_11_01_φ3, half_11_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_01_hx2 : SourcePowerBound (powerBoxCross 8 9 4 half_11_01_φ2) (51296155283/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 9) (u := 7) (t := 10)
    (D := 4) (ψ := (465749299/5000000000 : ℝ)) half_11_01_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_01_φ1, half_11_01_φ2, half_11_01_φ3, half_11_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_01_φ1, half_11_01_φ2, half_11_01_φ3, half_11_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_01_φ1, half_11_01_φ2, half_11_01_φ3, half_11_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_8) (half_10_01)
    (by simpa only [half_11_01_φ3, show (2:ℝ)*4=8 by norm_num] using half_11_01_hx3)
  exact h.weaken (by norm_num [half_11_01_φ1, half_11_01_φ2, half_11_01_φ3, half_11_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_01_hx1 : SourcePowerBound (powerBoxCross 8 10 2 half_11_01_φ1) (63952434399/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 10) (u := 8) (t := 11)
    (D := 2) (ψ := (1040850559/10000000000 : ℝ)) half_11_01_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_01_φ1, half_11_01_φ2, half_11_01_φ3, half_11_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_01_φ1, half_11_01_φ2, half_11_01_φ3, half_11_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_01_φ1, half_11_01_φ2, half_11_01_φ3, half_11_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_9) (chord_1)
    (by simpa only [half_11_01_φ2, show (2:ℝ)*2=4 by norm_num] using half_11_01_hx2)
  exact h.weaken (by norm_num [half_11_01_φ1, half_11_01_φ2, half_11_01_φ3, half_11_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_01 : AdmissibleExponent 8 22 (149586036223/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 9) (ψ := (45644563/400000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_10_01)
    (by simpa only [half_11_01_φ1] using half_11_01_hx1)
  exact admissibleExponent_mono h (by norm_num [half_11_01_φ1, half_11_01_φ2, half_11_01_φ3, half_11_01_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem chord_3 : AdmissibleExponent 8 24 (211012416127/12500000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 24) (t := (4/5 : ℝ))
    (half_11_01) (half_16_00) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1 <;> norm_num

theorem chord_4 : AdmissibleExponent 8 26 (940169147901/50000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 26) (t := (3/5 : ℝ))
    (half_11_01) (half_16_00) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1 <;> norm_num

theorem chord_5 : AdmissibleExponent 8 28 (518144315647/25000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 28) (t := (2/5 : ℝ))
    (half_11_01) (half_16_00) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1 <;> norm_num

theorem chord_6 : AdmissibleExponent 8 30 (1132408114687/50000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 30) (t := (1/5 : ℝ))
    (half_11_01) (half_16_00) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1 <;> norm_num

def half_12_01_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1156326443/10000000000 : ℝ)

def half_12_01_φ2 : Fin 2 → ℝ := Fin.snoc half_12_01_φ1 (1059593757/10000000000 : ℝ)

def half_12_01_φ3 : Fin 3 → ℝ := Fin.snoc half_12_01_φ2 (200360921/2000000000 : ℝ)

def half_12_01_φ4 : Fin 4 → ℝ := Fin.snoc half_12_01_φ3 (169958257/2000000000 : ℝ)

def half_12_01_φ5 : Fin 5 → ℝ := Fin.snoc half_12_01_φ4 (17220619/312500000 : ℝ)

theorem half_12_01_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_12_01_φ5) (36504953071/5000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_12_01_φ5 (by norm_num [half_12_01_φ1, half_12_01_φ2, half_12_01_φ3, half_12_01_φ4, half_12_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_01_φ1, half_12_01_φ2, half_12_01_φ3, half_12_01_φ4, half_12_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_01_φ1, half_12_01_φ2, half_12_01_φ3, half_12_01_φ4, half_12_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_12_01_φ1, half_12_01_φ2, half_12_01_φ3, half_12_01_φ4, half_12_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_12_01_φ1, half_12_01_φ2, half_12_01_φ3, half_12_01_φ4, half_12_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_12_01_hx5 : SourcePowerBound (powerBoxCross 8 7 32 half_12_01_φ5) (8350163187/1250000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 7) (r := 2) (v := 9) (w := 10) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_12_01_φ5 (by norm_num [half_12_01_φ1, half_12_01_φ2, half_12_01_φ3, half_12_01_φ4, half_12_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_01_φ1, half_12_01_φ2, half_12_01_φ3, half_12_01_φ4, half_12_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_12_01_hF2 (SeedCompletionHigher8SimpleSeeds.degree8_half_9) (half_10_01)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_12_01_φ1, half_12_01_φ2, half_12_01_φ3, half_12_01_φ4, half_12_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_01_hx4 : SourcePowerBound (powerBoxCross 8 8 16 half_12_01_φ4) (76718338511/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 8) (u := 6) (t := 9)
    (D := 16) (ψ := (17220619/312500000 : ℝ)) half_12_01_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_01_φ1, half_12_01_φ2, half_12_01_φ3, half_12_01_φ4, half_12_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_01_φ1, half_12_01_φ2, half_12_01_φ3, half_12_01_φ4, half_12_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_01_φ1, half_12_01_φ2, half_12_01_φ3, half_12_01_φ4, half_12_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_7) (SeedCompletionHigher8SimpleSeeds.degree8_half_9)
    (by simpa only [half_12_01_φ5, show (2:ℝ)*16=32 by norm_num] using half_12_01_hx5)
  exact h.weaken (by norm_num [half_12_01_φ1, half_12_01_φ2, half_12_01_φ3, half_12_01_φ4, half_12_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_01_hx3 : SourcePowerBound (powerBoxCross 8 9 8 half_12_01_φ3) (23291788327/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 9) (u := 7) (t := 10)
    (D := 8) (ψ := (169958257/2000000000 : ℝ)) half_12_01_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_01_φ1, half_12_01_φ2, half_12_01_φ3, half_12_01_φ4, half_12_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_01_φ1, half_12_01_φ2, half_12_01_φ3, half_12_01_φ4, half_12_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_01_φ1, half_12_01_φ2, half_12_01_φ3, half_12_01_φ4, half_12_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_8) (half_10_01)
    (by simpa only [half_12_01_φ4, show (2:ℝ)*8=16 by norm_num] using half_12_01_hx4)
  exact h.weaken (by norm_num [half_12_01_φ1, half_12_01_φ2, half_12_01_φ3, half_12_01_φ4, half_12_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_01_hx2 : SourcePowerBound (powerBoxCross 8 10 4 half_12_01_φ2) (115562677243/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 10) (u := 8) (t := 11)
    (D := 4) (ψ := (200360921/2000000000 : ℝ)) half_12_01_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_01_φ1, half_12_01_φ2, half_12_01_φ3, half_12_01_φ4, half_12_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_01_φ1, half_12_01_φ2, half_12_01_φ3, half_12_01_φ4, half_12_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_01_φ1, half_12_01_φ2, half_12_01_φ3, half_12_01_φ4, half_12_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_9) (half_11_01)
    (by simpa only [half_12_01_φ3, show (2:ℝ)*4=8 by norm_num] using half_12_01_hx3)
  exact h.weaken (by norm_num [half_12_01_φ1, half_12_01_φ2, half_12_01_φ3, half_12_01_φ4, half_12_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_01_hx1 : SourcePowerBound (powerBoxCross 8 11 2 half_12_01_φ1) (143445333751/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 11) (u := 9) (t := 12)
    (D := 2) (ψ := (1059593757/10000000000 : ℝ)) half_12_01_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_01_φ1, half_12_01_φ2, half_12_01_φ3, half_12_01_φ4, half_12_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_01_φ1, half_12_01_φ2, half_12_01_φ3, half_12_01_φ4, half_12_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_01_φ1, half_12_01_φ2, half_12_01_φ3, half_12_01_φ4, half_12_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_10_01) (chord_3)
    (by simpa only [half_12_01_φ2, show (2:ℝ)*2=4 by norm_num] using half_12_01_hx2)
  exact h.weaken (by norm_num [half_12_01_φ1, half_12_01_φ2, half_12_01_φ3, half_12_01_φ4, half_12_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_01 : AdmissibleExponent 8 24 (83864094527/5000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 10) (ψ := (1156326443/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_11_01)
    (by simpa only [half_12_01_φ1] using half_12_01_hx1)
  exact admissibleExponent_mono h (by norm_num [half_12_01_φ1, half_12_01_φ2, half_12_01_φ3, half_12_01_φ4, half_12_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem chord_7 : AdmissibleExponent 8 26 (187168205621/10000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 26) (t := (5/6 : ℝ))
    (half_12_01) (half_18_00) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1 <;> norm_num

theorem chord_8 : AdmissibleExponent 8 28 (51652055547/2500000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 28) (t := (2/3 : ℝ))
    (half_12_01) (half_18_00) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1 <;> norm_num

theorem chord_9 : AdmissibleExponent 8 30 (45209647751/2000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 30) (t := (1/2 : ℝ))
    (half_12_01) (half_18_00) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1 <;> norm_num

theorem chord_10 : AdmissibleExponent 8 32 (122744127661/5000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 32) (t := (1/3 : ℝ))
    (half_12_01) (half_18_00) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1 <;> norm_num

theorem chord_11 : AdmissibleExponent 8 34 (264928271889/10000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 34) (t := (1/6 : ℝ))
    (half_12_01) (half_18_00) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1 <;> norm_num

def half_13_01_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1173509909/10000000000 : ℝ)

def half_13_01_φ2 : Fin 2 → ℝ := Fin.snoc half_13_01_φ1 (270919289/2500000000 : ℝ)

def half_13_01_φ3 : Fin 3 → ℝ := Fin.snoc half_13_01_φ2 (207048251/2000000000 : ℝ)

def half_13_01_φ4 : Fin 4 → ℝ := Fin.snoc half_13_01_φ3 (118828287/1250000000 : ℝ)

def half_13_01_φ5 : Fin 5 → ℝ := Fin.snoc half_13_01_φ4 (147271549/2000000000 : ℝ)

theorem half_13_01_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_13_01_φ5) (65432340419/10000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_13_01_φ5 (by norm_num [half_13_01_φ1, half_13_01_φ2, half_13_01_φ3, half_13_01_φ4, half_13_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_01_φ1, half_13_01_φ2, half_13_01_φ3, half_13_01_φ4, half_13_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_01_φ1, half_13_01_φ2, half_13_01_φ3, half_13_01_φ4, half_13_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_13_01_φ1, half_13_01_φ2, half_13_01_φ3, half_13_01_φ4, half_13_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_13_01_φ1, half_13_01_φ2, half_13_01_φ3, half_13_01_φ4, half_13_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_13_01_hx5 : SourcePowerBound (powerBoxCross 8 8 32 half_13_01_φ5) (7045192707/1000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 8) (r := 2) (v := 10) (w := 11) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_13_01_φ5 (by norm_num [half_13_01_φ1, half_13_01_φ2, half_13_01_φ3, half_13_01_φ4, half_13_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_01_φ1, half_13_01_φ2, half_13_01_φ3, half_13_01_φ4, half_13_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_13_01_hF2 (half_10_01) (half_11_01)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_13_01_φ1, half_13_01_φ2, half_13_01_φ3, half_13_01_φ4, half_13_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_01_hx4 : SourcePowerBound (powerBoxCross 8 9 16 half_13_01_φ4) (83837407699/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 9) (u := 7) (t := 10)
    (D := 16) (ψ := (147271549/2000000000 : ℝ)) half_13_01_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_01_φ1, half_13_01_φ2, half_13_01_φ3, half_13_01_φ4, half_13_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_01_φ1, half_13_01_φ2, half_13_01_φ3, half_13_01_φ4, half_13_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_01_φ1, half_13_01_φ2, half_13_01_φ3, half_13_01_φ4, half_13_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_8) (half_10_01)
    (by simpa only [half_13_01_φ5, show (2:ℝ)*16=32 by norm_num] using half_13_01_hx5)
  exact h.weaken (by norm_num [half_13_01_φ1, half_13_01_φ2, half_13_01_φ3, half_13_01_φ4, half_13_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_01_hx3 : SourcePowerBound (powerBoxCross 8 10 8 half_13_01_φ3) (103643481261/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 10) (u := 8) (t := 11)
    (D := 8) (ψ := (118828287/1250000000 : ℝ)) half_13_01_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_01_φ1, half_13_01_φ2, half_13_01_φ3, half_13_01_φ4, half_13_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_01_φ1, half_13_01_φ2, half_13_01_φ3, half_13_01_φ4, half_13_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_01_φ1, half_13_01_φ2, half_13_01_φ3, half_13_01_φ4, half_13_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_9) (half_11_01)
    (by simpa only [half_13_01_φ4, show (2:ℝ)*8=16 by norm_num] using half_13_01_hx4)
  exact h.weaken (by norm_num [half_13_01_φ1, half_13_01_φ2, half_13_01_φ3, half_13_01_φ4, half_13_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_01_hx2 : SourcePowerBound (powerBoxCross 8 11 4 half_13_01_φ2) (25738155483/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 11) (u := 9) (t := 12)
    (D := 4) (ψ := (207048251/2000000000 : ℝ)) half_13_01_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_01_φ1, half_13_01_φ2, half_13_01_φ3, half_13_01_φ4, half_13_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_01_φ1, half_13_01_φ2, half_13_01_φ3, half_13_01_φ4, half_13_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_01_φ1, half_13_01_φ2, half_13_01_φ3, half_13_01_φ4, half_13_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_10_01) (half_12_01)
    (by simpa only [half_13_01_φ3, show (2:ℝ)*4=8 by norm_num] using half_13_01_hx3)
  exact h.weaken (by norm_num [half_13_01_φ1, half_13_01_φ2, half_13_01_φ3, half_13_01_φ4, half_13_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_01_hx1 : SourcePowerBound (powerBoxCross 8 12 2 half_13_01_φ1) (79609314889/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 12) (u := 10) (t := 13)
    (D := 2) (ψ := (270919289/2500000000 : ℝ)) half_13_01_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_01_φ1, half_13_01_φ2, half_13_01_φ3, half_13_01_φ4, half_13_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_01_φ1, half_13_01_φ2, half_13_01_φ3, half_13_01_φ4, half_13_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_01_φ1, half_13_01_φ2, half_13_01_φ3, half_13_01_φ4, half_13_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_11_01) (chord_7)
    (by simpa only [half_13_01_φ2, show (2:ℝ)*2=4 by norm_num] using half_13_01_hx2)
  exact h.weaken (by norm_num [half_13_01_φ1, half_13_01_φ2, half_13_01_φ3, half_13_01_φ4, half_13_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_01 : AdmissibleExponent 8 26 (37241871537/2000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 11) (ψ := (1173509909/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_12_01)
    (by simpa only [half_13_01_φ1] using half_13_01_hx1)
  exact admissibleExponent_mono h (by norm_num [half_13_01_φ1, half_13_01_φ2, half_13_01_φ3, half_13_01_φ4, half_13_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem chord_12 : AdmissibleExponent 8 28 (281367308/13671875 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 28) (t := (6/7 : ℝ))
    (half_13_01) (half_20_00) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1 <;> norm_num

theorem chord_13 : AdmissibleExponent 8 30 (12621885841/560000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 30) (t := (5/7 : ℝ))
    (half_13_01) (half_20_00) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1 <;> norm_num

theorem chord_14 : AdmissibleExponent 8 32 (171487084329/7000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 32) (t := (4/7 : ℝ))
    (half_13_01) (half_20_00) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1 <;> norm_num

theorem chord_15 : AdmissibleExponent 8 34 (370401191291/14000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 34) (t := (3/7 : ℝ))
    (half_13_01) (half_20_00) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1 <;> norm_num

theorem chord_16 : AdmissibleExponent 8 36 (99457053481/3500000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 36) (t := (2/7 : ℝ))
    (half_13_01) (half_20_00) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1 <;> norm_num

theorem chord_17 : AdmissibleExponent 8 38 (425255236557/14000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 38) (t := (1/7 : ℝ))
    (half_13_01) (half_20_00) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1 <;> norm_num

def half_14_01_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1188968721/10000000000 : ℝ)

def half_14_01_φ2 : Fin 2 → ℝ := Fin.snoc half_14_01_φ1 (1113277923/10000000000 : ℝ)

def half_14_01_φ3 : Fin 3 → ℝ := Fin.snoc half_14_01_φ2 (1072440801/10000000000 : ℝ)

def half_14_01_φ4 : Fin 4 → ℝ := Fin.snoc half_14_01_φ3 (946473221/10000000000 : ℝ)

def half_14_01_φ5 : Fin 5 → ℝ := Fin.snoc half_14_01_φ4 (811262761/10000000000 : ℝ)

theorem half_14_01_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_14_01_φ5) (62219108033/10000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_14_01_φ5 (by norm_num [half_14_01_φ1, half_14_01_φ2, half_14_01_φ3, half_14_01_φ4, half_14_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_01_φ1, half_14_01_φ2, half_14_01_φ3, half_14_01_φ4, half_14_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_01_φ1, half_14_01_φ2, half_14_01_φ3, half_14_01_φ4, half_14_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_14_01_φ1, half_14_01_φ2, half_14_01_φ3, half_14_01_φ4, half_14_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_14_01_φ1, half_14_01_φ2, half_14_01_φ3, half_14_01_φ4, half_14_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_14_01_hx5 : SourcePowerBound (powerBoxCross 8 9 32 half_14_01_φ5) (19196753071/2500000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 9) (r := 2) (v := 0) (w := 12) (D := 32)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_14_01_φ5 (by norm_num [half_14_01_φ1, half_14_01_φ2, half_14_01_φ3, half_14_01_φ4, half_14_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_01_φ1, half_14_01_φ2, half_14_01_φ3, half_14_01_φ4, half_14_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_14_01_hF2 (admissibleExponent_zero 8) (half_12_01)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_14_01_φ1, half_14_01_φ2, half_14_01_φ3, half_14_01_φ4, half_14_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_01_hx4 : SourcePowerBound (powerBoxCross 8 10 16 half_14_01_φ4) (23159732649/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 10) (u := 8) (t := 11)
    (D := 16) (ψ := (811262761/10000000000 : ℝ)) half_14_01_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_01_φ1, half_14_01_φ2, half_14_01_φ3, half_14_01_φ4, half_14_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_01_φ1, half_14_01_φ2, half_14_01_φ3, half_14_01_φ4, half_14_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_01_φ1, half_14_01_φ2, half_14_01_φ3, half_14_01_φ4, half_14_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_9) (half_11_01)
    (by simpa only [half_14_01_φ5, show (2:ℝ)*16=32 by norm_num] using half_14_01_hx5)
  exact h.weaken (by norm_num [half_14_01_φ1, half_14_01_φ2, half_14_01_φ3, half_14_01_φ4, half_14_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_01_hx3 : SourcePowerBound (powerBoxCross 8 11 8 half_14_01_φ3) (114062138679/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 11) (u := 9) (t := 12)
    (D := 8) (ψ := (946473221/10000000000 : ℝ)) half_14_01_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_01_φ1, half_14_01_φ2, half_14_01_φ3, half_14_01_φ4, half_14_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_01_φ1, half_14_01_φ2, half_14_01_φ3, half_14_01_φ4, half_14_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_01_φ1, half_14_01_φ2, half_14_01_φ3, half_14_01_φ4, half_14_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_10_01) (half_12_01)
    (by simpa only [half_14_01_φ4, show (2:ℝ)*8=16 by norm_num] using half_14_01_hx4)
  exact h.weaken (by norm_num [half_14_01_φ1, half_14_01_φ2, half_14_01_φ3, half_14_01_φ4, half_14_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_01_hx2 : SourcePowerBound (powerBoxCross 8 12 4 half_14_01_φ2) (70951759949/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 12) (u := 10) (t := 13)
    (D := 4) (ψ := (1072440801/10000000000 : ℝ)) half_14_01_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_01_φ1, half_14_01_φ2, half_14_01_φ3, half_14_01_φ4, half_14_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_01_φ1, half_14_01_φ2, half_14_01_φ3, half_14_01_φ4, half_14_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_01_φ1, half_14_01_φ2, half_14_01_φ3, half_14_01_φ4, half_14_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_11_01) (half_13_01)
    (by simpa only [half_14_01_φ3, show (2:ℝ)*4=8 by norm_num] using half_14_01_hx3)
  exact h.weaken (by norm_num [half_14_01_φ1, half_14_01_φ2, half_14_01_φ3, half_14_01_φ4, half_14_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_01_hx1 : SourcePowerBound (powerBoxCross 8 13 2 half_14_01_φ1) (17525861623/1000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 13) (u := 11) (t := 14)
    (D := 2) (ψ := (1113277923/10000000000 : ℝ)) half_14_01_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_01_φ1, half_14_01_φ2, half_14_01_φ3, half_14_01_φ4, half_14_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_01_φ1, half_14_01_φ2, half_14_01_φ3, half_14_01_φ4, half_14_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_01_φ1, half_14_01_φ2, half_14_01_φ3, half_14_01_φ4, half_14_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_12_01) (chord_12)
    (by simpa only [half_14_01_φ2, show (2:ℝ)*2=4 by norm_num] using half_14_01_hx2)
  exact h.weaken (by norm_num [half_14_01_φ1, half_14_01_φ2, half_14_01_φ3, half_14_01_φ4, half_14_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_01 : AdmissibleExponent 8 28 (40996566851/2000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 12) (ψ := (1188968721/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_13_01)
    (by simpa only [half_14_01_φ1] using half_14_01_hx1)
  exact admissibleExponent_mono h (by norm_num [half_14_01_φ1, half_14_01_φ2, half_14_01_φ3, half_14_01_φ4, half_14_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem chord_18 : AdmissibleExponent 8 30 (3595356379/160000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 30) (t := (5/6 : ℝ))
    (half_14_01) (half_20_00) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1 <;> norm_num

theorem chord_19 : AdmissibleExponent 8 32 (1527729457/62500000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 32) (t := (2/3 : ℝ))
    (half_14_01) (half_20_00) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1 <;> norm_num

theorem chord_20 : AdmissibleExponent 8 34 (105665461021/4000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 34) (t := (1/2 : ℝ))
    (half_14_01) (half_20_00) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1 <;> norm_num

theorem chord_21 : AdmissibleExponent 8 36 (56778118397/2000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 36) (t := (1/3 : ℝ))
    (half_14_01) (half_20_00) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1 <;> norm_num

theorem chord_22 : AdmissibleExponent 8 38 (121447012567/4000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 38) (t := (1/6 : ℝ))
    (half_14_01) (half_20_00) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1 <;> norm_num

def half_15_01_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (75229303/625000000 : ℝ)

def half_15_01_φ2 : Fin 2 → ℝ := Fin.snoc half_15_01_φ1 (285266661/2500000000 : ℝ)

def half_15_01_φ3 : Fin 3 → ℝ := Fin.snoc half_15_01_φ2 (218721843/2000000000 : ℝ)

def half_15_01_φ4 : Fin 4 → ℝ := Fin.snoc half_15_01_φ3 (937379327/10000000000 : ℝ)

def half_15_01_φ5 : Fin 5 → ℝ := Fin.snoc half_15_01_φ4 (401733997/5000000000 : ℝ)

theorem half_15_01_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_15_01_φ5) (15309241853/2500000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_15_01_φ5 (by norm_num [half_15_01_φ1, half_15_01_φ2, half_15_01_φ3, half_15_01_φ4, half_15_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_01_φ1, half_15_01_φ2, half_15_01_φ3, half_15_01_φ4, half_15_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_01_φ1, half_15_01_φ2, half_15_01_φ3, half_15_01_φ4, half_15_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_15_01_φ1, half_15_01_φ2, half_15_01_φ3, half_15_01_φ4, half_15_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_15_01_φ1, half_15_01_φ2, half_15_01_φ3, half_15_01_φ4, half_15_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_15_01_hx5 : SourcePowerBound (powerBoxCross 8 10 32 half_15_01_φ5) (8489779169/1000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 10) (r := 2) (v := 13) (w := 14) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_15_01_φ5 (by norm_num [half_15_01_φ1, half_15_01_φ2, half_15_01_φ3, half_15_01_φ4, half_15_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_01_φ1, half_15_01_φ2, half_15_01_φ3, half_15_01_φ4, half_15_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_15_01_hF2 (half_13_01) (half_14_01)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_15_01_φ1, half_15_01_φ2, half_15_01_φ3, half_15_01_φ4, half_15_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_01_hx4 : SourcePowerBound (powerBoxCross 8 11 16 half_15_01_φ4) (20386857759/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 11) (u := 9) (t := 12)
    (D := 16) (ψ := (401733997/5000000000 : ℝ)) half_15_01_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_01_φ1, half_15_01_φ2, half_15_01_φ3, half_15_01_φ4, half_15_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_01_φ1, half_15_01_φ2, half_15_01_φ3, half_15_01_φ4, half_15_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_01_φ1, half_15_01_φ2, half_15_01_φ3, half_15_01_φ4, half_15_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_10_01) (half_12_01)
    (by simpa only [half_15_01_φ5, show (2:ℝ)*16=32 by norm_num] using half_15_01_hx5)
  exact h.weaken (by norm_num [half_15_01_φ1, half_15_01_φ2, half_15_01_φ3, half_15_01_φ4, half_15_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_01_hx3 : SourcePowerBound (powerBoxCross 8 12 8 half_15_01_φ3) (12486750173/1000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 12) (u := 10) (t := 13)
    (D := 8) (ψ := (937379327/10000000000 : ℝ)) half_15_01_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_01_φ1, half_15_01_φ2, half_15_01_φ3, half_15_01_φ4, half_15_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_01_φ1, half_15_01_φ2, half_15_01_φ3, half_15_01_φ4, half_15_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_01_φ1, half_15_01_φ2, half_15_01_φ3, half_15_01_φ4, half_15_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_11_01) (half_13_01)
    (by simpa only [half_15_01_φ4, show (2:ℝ)*8=16 by norm_num] using half_15_01_hx4)
  exact h.weaken (by norm_num [half_15_01_φ1, half_15_01_φ2, half_15_01_φ3, half_15_01_φ4, half_15_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_01_hx2 : SourcePowerBound (powerBoxCross 8 13 4 half_15_01_φ2) (155263573407/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 13) (u := 11) (t := 14)
    (D := 4) (ψ := (218721843/2000000000 : ℝ)) half_15_01_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_01_φ1, half_15_01_φ2, half_15_01_φ3, half_15_01_φ4, half_15_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_01_φ1, half_15_01_φ2, half_15_01_φ3, half_15_01_φ4, half_15_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_01_φ1, half_15_01_φ2, half_15_01_φ3, half_15_01_φ4, half_15_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_12_01) (half_14_01)
    (by simpa only [half_15_01_φ3, show (2:ℝ)*4=8 by norm_num] using half_15_01_hx3)
  exact h.weaken (by norm_num [half_15_01_φ1, half_15_01_φ2, half_15_01_φ3, half_15_01_φ4, half_15_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_01_hx1 : SourcePowerBound (powerBoxCross 8 14 2 half_15_01_φ1) (47878339477/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 14) (u := 12) (t := 15)
    (D := 2) (ψ := (285266661/2500000000 : ℝ)) half_15_01_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_01_φ1, half_15_01_φ2, half_15_01_φ3, half_15_01_φ4, half_15_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_01_φ1, half_15_01_φ2, half_15_01_φ3, half_15_01_φ4, half_15_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_01_φ1, half_15_01_φ2, half_15_01_φ3, half_15_01_φ4, half_15_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_13_01) (chord_18)
    (by simpa only [half_15_01_φ2, show (2:ℝ)*2=4 by norm_num] using half_15_01_hx2)
  exact h.weaken (by norm_num [half_15_01_φ1, half_15_01_φ2, half_15_01_φ3, half_15_01_φ4, half_15_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_01 : AdmissibleExponent 8 30 (56003104201/2500000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 13) (ψ := (75229303/625000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_14_01)
    (by simpa only [half_15_01_φ1] using half_15_01_hx1)
  exact admissibleExponent_mono h (by norm_num [half_15_01_φ1, half_15_01_φ2, half_15_01_φ3, half_15_01_φ4, half_15_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem chord_23 : AdmissibleExponent 8 32 (609697069033/25000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 32) (t := (4/5 : ℝ))
    (half_15_01) (half_20_00) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1 <;> norm_num

theorem chord_24 : AdmissibleExponent 8 34 (82420387007/3125000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 34) (t := (3/5 : ℝ))
    (half_15_01) (half_20_00) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1 <;> norm_num

theorem chord_25 : AdmissibleExponent 8 36 (709029123079/25000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 36) (t := (2/5 : ℝ))
    (half_15_01) (half_20_00) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1 <;> norm_num

theorem chord_26 : AdmissibleExponent 8 38 (379347575051/12500000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 38) (t := (1/5 : ℝ))
    (half_15_01) (half_20_00) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1 <;> norm_num

def half_16_01_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (304365247/2500000000 : ℝ)

def half_16_01_φ2 : Fin 2 → ℝ := Fin.snoc half_16_01_φ1 (1165656959/10000000000 : ℝ)

def half_16_01_φ3 : Fin 3 → ℝ := Fin.snoc half_16_01_φ2 (1088126007/10000000000 : ℝ)

def half_16_01_φ4 : Fin 4 → ℝ := Fin.snoc half_16_01_φ3 (186535887/2000000000 : ℝ)

def half_16_01_φ5 : Fin 5 → ℝ := Fin.snoc half_16_01_φ4 (159887903/2000000000 : ℝ)

theorem half_16_01_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_16_01_φ5) (7591172377/1250000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_16_01_φ5 (by norm_num [half_16_01_φ1, half_16_01_φ2, half_16_01_φ3, half_16_01_φ4, half_16_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_01_φ1, half_16_01_φ2, half_16_01_φ3, half_16_01_φ4, half_16_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_01_φ1, half_16_01_φ2, half_16_01_φ3, half_16_01_φ4, half_16_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_16_01_φ1, half_16_01_φ2, half_16_01_φ3, half_16_01_φ4, half_16_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_16_01_φ1, half_16_01_φ2, half_16_01_φ3, half_16_01_φ4, half_16_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_16_01_hx5 : SourcePowerBound (powerBoxCross 8 11 32 half_16_01_φ5) (46744182423/5000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 11) (r := 2) (v := 14) (w := 15) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_16_01_φ5 (by norm_num [half_16_01_φ1, half_16_01_φ2, half_16_01_φ3, half_16_01_φ4, half_16_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_01_φ1, half_16_01_φ2, half_16_01_φ3, half_16_01_φ4, half_16_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_16_01_hF2 (half_14_01) (half_15_01)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_16_01_φ1, half_16_01_φ2, half_16_01_φ3, half_16_01_φ4, half_16_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_01_hx4 : SourcePowerBound (powerBoxCross 8 12 16 half_16_01_φ4) (55913328517/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 12) (u := 10) (t := 13)
    (D := 16) (ψ := (159887903/2000000000 : ℝ)) half_16_01_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_01_φ1, half_16_01_φ2, half_16_01_φ3, half_16_01_φ4, half_16_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_01_φ1, half_16_01_φ2, half_16_01_φ3, half_16_01_φ4, half_16_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_01_φ1, half_16_01_φ2, half_16_01_φ3, half_16_01_φ4, half_16_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_11_01) (half_13_01)
    (by simpa only [half_16_01_φ5, show (2:ℝ)*16=32 by norm_num] using half_16_01_hx5)
  exact h.weaken (by norm_num [half_16_01_φ1, half_16_01_φ2, half_16_01_φ3, half_16_01_φ4, half_16_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_01_hx3 : SourcePowerBound (powerBoxCross 8 13 8 half_16_01_φ3) (17050491763/1250000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 13) (u := 11) (t := 14)
    (D := 8) (ψ := (186535887/2000000000 : ℝ)) half_16_01_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_01_φ1, half_16_01_φ2, half_16_01_φ3, half_16_01_φ4, half_16_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_01_φ1, half_16_01_φ2, half_16_01_φ3, half_16_01_φ4, half_16_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_01_φ1, half_16_01_φ2, half_16_01_φ3, half_16_01_φ4, half_16_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_12_01) (half_14_01)
    (by simpa only [half_16_01_φ4, show (2:ℝ)*8=16 by norm_num] using half_16_01_hx4)
  exact h.weaken (by norm_num [half_16_01_φ1, half_16_01_φ2, half_16_01_φ3, half_16_01_φ4, half_16_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_01_hx2 : SourcePowerBound (powerBoxCross 8 14 4 half_16_01_φ2) (84388218593/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 14) (u := 12) (t := 15)
    (D := 4) (ψ := (1088126007/10000000000 : ℝ)) half_16_01_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_01_φ1, half_16_01_φ2, half_16_01_φ3, half_16_01_φ4, half_16_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_01_φ1, half_16_01_φ2, half_16_01_φ3, half_16_01_φ4, half_16_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_01_φ1, half_16_01_φ2, half_16_01_φ3, half_16_01_φ4, half_16_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_13_01) (half_15_01)
    (by simpa only [half_16_01_φ3, show (2:ℝ)*4=8 by norm_num] using half_16_01_hx3)
  exact h.weaken (by norm_num [half_16_01_φ1, half_16_01_φ2, half_16_01_φ3, half_16_01_φ4, half_16_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_01_hx1 : SourcePowerBound (powerBoxCross 8 15 2 half_16_01_φ1) (6498663749/312500000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 15) (u := 13) (t := 16)
    (D := 2) (ψ := (1165656959/10000000000 : ℝ)) half_16_01_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_01_φ1, half_16_01_φ2, half_16_01_φ3, half_16_01_φ4, half_16_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_01_φ1, half_16_01_φ2, half_16_01_φ3, half_16_01_φ4, half_16_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_01_φ1, half_16_01_φ2, half_16_01_φ3, half_16_01_φ4, half_16_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_14_01) (chord_23)
    (by simpa only [half_16_01_φ2, show (2:ℝ)*2=4 by norm_num] using half_16_01_hx2)
  exact h.weaken (by norm_num [half_16_01_φ1, half_16_01_φ2, half_16_01_φ3, half_16_01_φ4, half_16_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_01 : AdmissibleExponent 8 32 (12163180431/500000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 14) (ψ := (304365247/2500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_15_01)
    (by simpa only [half_16_01_φ1] using half_16_01_hx1)
  exact admissibleExponent_mono h (by norm_num [half_16_01_φ1, half_16_01_φ2, half_16_01_φ3, half_16_01_φ4, half_16_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem chord_27 : AdmissibleExponent 8 34 (105313529671/4000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 34) (t := (3/4 : ℝ))
    (half_16_01) (half_20_00) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1 <;> norm_num

theorem chord_28 : AdmissibleExponent 8 36 (56660807947/2000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 36) (t := (1/2 : ℝ))
    (half_16_01) (half_20_00) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1 <;> norm_num

theorem chord_29 : AdmissibleExponent 8 38 (121329702117/4000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 38) (t := (1/4 : ℝ))
    (half_16_01) (half_20_00) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1 <;> norm_num

def half_17_01_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1230472069/10000000000 : ℝ)

def half_17_01_φ2 : Fin 2 → ℝ := Fin.snoc half_17_01_φ1 (237227063/2000000000 : ℝ)

def half_17_01_φ3 : Fin 3 → ℝ := Fin.snoc half_17_01_φ2 (541670901/5000000000 : ℝ)

def half_17_01_φ4 : Fin 4 → ℝ := Fin.snoc half_17_01_φ3 (928578687/10000000000 : ℝ)

def half_17_01_φ5 : Fin 5 → ℝ := Fin.snoc half_17_01_φ4 (795924589/10000000000 : ℝ)

theorem half_17_01_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_17_01_φ5) (30143249149/5000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_17_01_φ5 (by norm_num [half_17_01_φ1, half_17_01_φ2, half_17_01_φ3, half_17_01_φ4, half_17_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_01_φ1, half_17_01_φ2, half_17_01_φ3, half_17_01_φ4, half_17_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_01_φ1, half_17_01_φ2, half_17_01_φ3, half_17_01_φ4, half_17_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_17_01_φ1, half_17_01_φ2, half_17_01_φ3, half_17_01_φ4, half_17_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_17_01_φ1, half_17_01_φ2, half_17_01_φ3, half_17_01_φ4, half_17_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_17_01_hx5 : SourcePowerBound (powerBoxCross 8 12 32 half_17_01_φ5) (102200394117/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 12) (r := 2) (v := 0) (w := 16) (D := 32)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_17_01_φ5 (by norm_num [half_17_01_φ1, half_17_01_φ2, half_17_01_φ3, half_17_01_φ4, half_17_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_01_φ1, half_17_01_φ2, half_17_01_φ3, half_17_01_φ4, half_17_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_17_01_hF2 (admissibleExponent_zero 8) (half_16_01)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_17_01_φ1, half_17_01_φ2, half_17_01_φ3, half_17_01_φ4, half_17_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_01_hx4 : SourcePowerBound (powerBoxCross 8 13 16 half_17_01_φ4) (24371257931/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 13) (u := 11) (t := 14)
    (D := 16) (ψ := (795924589/10000000000 : ℝ)) half_17_01_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_01_φ1, half_17_01_φ2, half_17_01_φ3, half_17_01_φ4, half_17_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_01_φ1, half_17_01_φ2, half_17_01_φ3, half_17_01_φ4, half_17_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_01_φ1, half_17_01_φ2, half_17_01_φ3, half_17_01_φ4, half_17_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_12_01) (half_14_01)
    (by simpa only [half_17_01_φ5, show (2:ℝ)*16=32 by norm_num] using half_17_01_hx5)
  exact h.weaken (by norm_num [half_17_01_φ1, half_17_01_φ2, half_17_01_φ3, half_17_01_φ4, half_17_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_01_hx3 : SourcePowerBound (powerBoxCross 8 14 8 half_17_01_φ3) (74045080437/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 14) (u := 12) (t := 15)
    (D := 8) (ψ := (928578687/10000000000 : ℝ)) half_17_01_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_01_φ1, half_17_01_φ2, half_17_01_φ3, half_17_01_φ4, half_17_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_01_φ1, half_17_01_φ2, half_17_01_φ3, half_17_01_φ4, half_17_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_01_φ1, half_17_01_φ2, half_17_01_φ3, half_17_01_φ4, half_17_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_13_01) (half_15_01)
    (by simpa only [half_17_01_φ4, show (2:ℝ)*8=16 by norm_num] using half_17_01_hx4)
  exact h.weaken (by norm_num [half_17_01_φ1, half_17_01_φ2, half_17_01_φ3, half_17_01_φ4, half_17_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_01_hx2 : SourcePowerBound (powerBoxCross 8 15 4 half_17_01_φ2) (45612560397/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 15) (u := 13) (t := 16)
    (D := 4) (ψ := (541670901/5000000000 : ℝ)) half_17_01_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_01_φ1, half_17_01_φ2, half_17_01_φ3, half_17_01_φ4, half_17_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_01_φ1, half_17_01_φ2, half_17_01_φ3, half_17_01_φ4, half_17_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_01_φ1, half_17_01_φ2, half_17_01_φ3, half_17_01_φ4, half_17_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_14_01) (half_16_01)
    (by simpa only [half_17_01_φ3, show (2:ℝ)*4=8 by norm_num] using half_17_01_hx3)
  exact h.weaken (by norm_num [half_17_01_φ1, half_17_01_φ2, half_17_01_φ3, half_17_01_φ4, half_17_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_01_hx1 : SourcePowerBound (powerBoxCross 8 16 2 half_17_01_φ1) (56140293279/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 16) (u := 14) (t := 17)
    (D := 2) (ψ := (237227063/2000000000 : ℝ)) half_17_01_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_01_φ1, half_17_01_φ2, half_17_01_φ3, half_17_01_φ4, half_17_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_01_φ1, half_17_01_φ2, half_17_01_φ3, half_17_01_φ4, half_17_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_01_φ1, half_17_01_φ2, half_17_01_φ3, half_17_01_φ4, half_17_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_15_01) (chord_27)
    (by simpa only [half_17_01_φ2, show (2:ℝ)*2=4 by norm_num] using half_17_01_hx2)
  exact h.weaken (by norm_num [half_17_01_φ1, half_17_01_φ2, half_17_01_φ3, half_17_01_φ4, half_17_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_01 : AdmissibleExponent 8 34 (52541161451/2000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 15) (ψ := (1230472069/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_16_01)
    (by simpa only [half_17_01_φ1] using half_17_01_hx1)
  exact admissibleExponent_mono h (by norm_num [half_17_01_φ1, half_17_01_φ2, half_17_01_φ3, half_17_01_φ4, half_17_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem chord_30 : AdmissibleExponent 8 36 (3536483689/125000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 36) (t := (2/3 : ℝ))
    (half_17_01) (half_20_00) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1 <;> norm_num

theorem chord_31 : AdmissibleExponent 8 38 (60626316597/2000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 38) (t := (1/3 : ℝ))
    (half_17_01) (half_20_00) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1 <;> norm_num

def half_18_01_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (622424969/5000000000 : ℝ)

def half_18_01_φ2 : Fin 2 → ℝ := Fin.snoc half_18_01_φ1 (602246787/5000000000 : ℝ)

def half_18_01_φ3 : Fin 3 → ℝ := Fin.snoc half_18_01_φ2 (269666303/2500000000 : ℝ)

def half_18_01_φ4 : Fin 4 → ℝ := Fin.snoc half_18_01_φ3 (924570181/10000000000 : ℝ)

def half_18_01_φ5 : Fin 5 → ℝ := Fin.snoc half_18_01_φ4 (792488727/10000000000 : ℝ)

theorem half_18_01_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_18_01_φ5) (3740848733/625000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_18_01_φ5 (by norm_num [half_18_01_φ1, half_18_01_φ2, half_18_01_φ3, half_18_01_φ4, half_18_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_18_01_φ1, half_18_01_φ2, half_18_01_φ3, half_18_01_φ4, half_18_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_18_01_φ1, half_18_01_φ2, half_18_01_φ3, half_18_01_φ4, half_18_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_18_01_φ1, half_18_01_φ2, half_18_01_φ3, half_18_01_φ4, half_18_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_18_01_φ1, half_18_01_φ2, half_18_01_φ3, half_18_01_φ4, half_18_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_18_01_hx5 : SourcePowerBound (powerBoxCross 8 13 32 half_18_01_φ5) (22210458753/2000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 13) (r := 2) (v := 17) (w := 18) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_18_01_φ5 (by norm_num [half_18_01_φ1, half_18_01_φ2, half_18_01_φ3, half_18_01_φ4, half_18_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_18_01_φ1, half_18_01_φ2, half_18_01_φ3, half_18_01_φ4, half_18_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_18_01_hF2 (half_17_01) (chord_30)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_18_01_φ1, half_18_01_φ2, half_18_01_φ3, half_18_01_φ4, half_18_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_18_01_hx4 : SourcePowerBound (powerBoxCross 8 14 16 half_18_01_φ4) (131982790129/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 14) (u := 12) (t := 15)
    (D := 16) (ψ := (792488727/10000000000 : ℝ)) half_18_01_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_18_01_φ1, half_18_01_φ2, half_18_01_φ3, half_18_01_φ4, half_18_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_18_01_φ1, half_18_01_φ2, half_18_01_φ3, half_18_01_φ4, half_18_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_18_01_φ1, half_18_01_φ2, half_18_01_φ3, half_18_01_φ4, half_18_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_13_01) (half_15_01)
    (by simpa only [half_18_01_φ5, show (2:ℝ)*16=32 by norm_num] using half_18_01_hx5)
  exact h.weaken (by norm_num [half_18_01_φ1, half_18_01_φ2, half_18_01_φ3, half_18_01_φ4, half_18_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_18_01_hx3 : SourcePowerBound (powerBoxCross 8 15 8 half_18_01_φ3) (39961264903/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 15) (u := 13) (t := 16)
    (D := 8) (ψ := (924570181/10000000000 : ℝ)) half_18_01_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_18_01_φ1, half_18_01_φ2, half_18_01_φ3, half_18_01_φ4, half_18_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_18_01_φ1, half_18_01_φ2, half_18_01_φ3, half_18_01_φ4, half_18_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_18_01_φ1, half_18_01_φ2, half_18_01_φ3, half_18_01_φ4, half_18_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_14_01) (half_16_01)
    (by simpa only [half_18_01_φ4, show (2:ℝ)*8=16 by norm_num] using half_18_01_hx4)
  exact h.weaken (by norm_num [half_18_01_φ1, half_18_01_φ2, half_18_01_φ3, half_18_01_φ4, half_18_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_18_01_hx2 : SourcePowerBound (powerBoxCross 8 16 4 half_18_01_φ2) (24521317311/1250000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 16) (u := 14) (t := 17)
    (D := 4) (ψ := (269666303/2500000000 : ℝ)) half_18_01_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_18_01_φ1, half_18_01_φ2, half_18_01_φ3, half_18_01_φ4, half_18_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_18_01_φ1, half_18_01_φ2, half_18_01_φ3, half_18_01_φ4, half_18_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_18_01_φ1, half_18_01_φ2, half_18_01_φ3, half_18_01_φ4, half_18_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_15_01) (half_17_01)
    (by simpa only [half_18_01_φ3, show (2:ℝ)*4=8 by norm_num] using half_18_01_hx3)
  exact h.weaken (by norm_num [half_18_01_φ1, half_18_01_φ2, half_18_01_φ3, half_18_01_φ4, half_18_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_18_01_hx1 : SourcePowerBound (powerBoxCross 8 17 2 half_18_01_φ1) (48249545283/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 17) (u := 15) (t := 18)
    (D := 2) (ψ := (602246787/5000000000 : ℝ)) half_18_01_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_18_01_φ1, half_18_01_φ2, half_18_01_φ3, half_18_01_φ4, half_18_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_18_01_φ1, half_18_01_φ2, half_18_01_φ3, half_18_01_φ4, half_18_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_18_01_φ1, half_18_01_φ2, half_18_01_φ3, half_18_01_φ4, half_18_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_16_01) (chord_30)
    (by simpa only [half_18_01_φ2, show (2:ℝ)*2=4 by norm_num] using half_18_01_hx2)
  exact h.weaken (by norm_num [half_18_01_φ1, half_18_01_φ2, half_18_01_φ3, half_18_01_φ4, half_18_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_18_01 : AdmissibleExponent 8 36 (282327774369/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 16) (ψ := (622424969/5000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_17_01)
    (by simpa only [half_18_01_φ1] using half_18_01_hx1)
  exact admissibleExponent_mono h (by norm_num [half_18_01_φ1, half_18_01_φ2, half_18_01_φ3, half_18_01_φ4, half_18_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem chord_32 : AdmissibleExponent 8 38 (605672245219/20000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 38) (t := (1/2 : ℝ))
    (half_18_01) (half_20_00) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1 <;> norm_num

def half_19_01_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1/8 : ℝ)

def half_19_01_φ2 : Fin 2 → ℝ := Fin.snoc half_19_01_φ1 (610499271/5000000000 : ℝ)

def half_19_01_φ3 : Fin 3 → ℝ := Fin.snoc half_19_01_φ2 (268892909/2500000000 : ℝ)

def half_19_01_φ4 : Fin 4 → ℝ := Fin.snoc half_19_01_φ3 (184383709/2000000000 : ℝ)

def half_19_01_φ5 : Fin 5 → ℝ := Fin.snoc half_19_01_φ4 (98776987/1250000000 : ℝ)

theorem half_19_01_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_19_01_φ5) (59567203001/10000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_19_01_φ5 (by norm_num [half_19_01_φ1, half_19_01_φ2, half_19_01_φ3, half_19_01_φ4, half_19_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_19_01_φ1, half_19_01_φ2, half_19_01_φ3, half_19_01_φ4, half_19_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_19_01_φ1, half_19_01_φ2, half_19_01_φ3, half_19_01_φ4, half_19_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_19_01_φ1, half_19_01_φ2, half_19_01_φ3, half_19_01_φ4, half_19_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_19_01_φ1, half_19_01_φ2, half_19_01_φ3, half_19_01_φ4, half_19_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_19_01_hx5 : SourcePowerBound (powerBoxCross 8 14 32 half_19_01_φ5) (120148560531/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 14) (r := 2) (v := 18) (w := 19) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_19_01_φ5 (by norm_num [half_19_01_φ1, half_19_01_φ2, half_19_01_φ3, half_19_01_φ4, half_19_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_19_01_φ1, half_19_01_φ2, half_19_01_φ3, half_19_01_φ4, half_19_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_19_01_hF2 (half_18_01) (chord_32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_19_01_φ1, half_19_01_φ2, half_19_01_φ3, half_19_01_φ4, half_19_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_19_01_hx4 : SourcePowerBound (powerBoxCross 8 15 16 half_19_01_φ4) (2847665081/200000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 15) (u := 13) (t := 16)
    (D := 16) (ψ := (98776987/1250000000 : ℝ)) half_19_01_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_19_01_φ1, half_19_01_φ2, half_19_01_φ3, half_19_01_φ4, half_19_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_19_01_φ1, half_19_01_φ2, half_19_01_φ3, half_19_01_φ4, half_19_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_19_01_φ1, half_19_01_φ2, half_19_01_φ3, half_19_01_φ4, half_19_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_14_01) (half_16_01)
    (by simpa only [half_19_01_φ5, show (2:ℝ)*16=32 by norm_num] using half_19_01_hx5)
  exact h.weaken (by norm_num [half_19_01_φ1, half_19_01_φ2, half_19_01_φ3, half_19_01_φ4, half_19_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_19_01_hx3 : SourcePowerBound (powerBoxCross 8 16 8 half_19_01_φ3) (171914124853/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 16) (u := 14) (t := 17)
    (D := 8) (ψ := (184383709/2000000000 : ℝ)) half_19_01_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_19_01_φ1, half_19_01_φ2, half_19_01_φ3, half_19_01_φ4, half_19_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_19_01_φ1, half_19_01_φ2, half_19_01_φ3, half_19_01_φ4, half_19_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_19_01_φ1, half_19_01_φ2, half_19_01_φ3, half_19_01_φ4, half_19_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_15_01) (half_17_01)
    (by simpa only [half_19_01_φ4, show (2:ℝ)*8=16 by norm_num] using half_19_01_hx4)
  exact h.weaken (by norm_num [half_19_01_φ1, half_19_01_φ2, half_19_01_φ3, half_19_01_φ4, half_19_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_19_01_hx2 : SourcePowerBound (powerBoxCross 8 17 4 half_19_01_φ2) (210262239131/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 17) (u := 15) (t := 18)
    (D := 4) (ψ := (268892909/2500000000 : ℝ)) half_19_01_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_19_01_φ1, half_19_01_φ2, half_19_01_φ3, half_19_01_φ4, half_19_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_19_01_φ1, half_19_01_φ2, half_19_01_φ3, half_19_01_φ4, half_19_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_19_01_φ1, half_19_01_φ2, half_19_01_φ3, half_19_01_φ4, half_19_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_16_01) (half_18_01)
    (by simpa only [half_19_01_φ3, show (2:ℝ)*4=8 by norm_num] using half_19_01_hx3)
  exact h.weaken (by norm_num [half_19_01_φ1, half_19_01_φ2, half_19_01_φ3, half_19_01_φ4, half_19_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_19_01_hx1 : SourcePowerBound (powerBoxCross 8 18 2 half_19_01_φ1) (258393399151/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 18) (u := 16) (t := 19)
    (D := 2) (ψ := (610499271/5000000000 : ℝ)) half_19_01_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_19_01_φ1, half_19_01_φ2, half_19_01_φ3, half_19_01_φ4, half_19_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_19_01_φ1, half_19_01_φ2, half_19_01_φ3, half_19_01_φ4, half_19_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_19_01_φ1, half_19_01_φ2, half_19_01_φ3, half_19_01_φ4, half_19_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_17_01) (chord_32)
    (by simpa only [half_19_01_φ2, show (2:ℝ)*2=4 by norm_num] using half_19_01_hx2)
  exact h.weaken (by norm_num [half_19_01_φ1, half_19_01_φ2, half_19_01_φ3, half_19_01_φ4, half_19_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_19_01 : AdmissibleExponent 8 38 (302143399151/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 17) (ψ := (1/8 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_18_01)
    (by simpa only [half_19_01_φ1] using half_19_01_hx1)
  exact admissibleExponent_mono h (by norm_num [half_19_01_φ1, half_19_01_φ2, half_19_01_φ3, half_19_01_φ4, half_19_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_20_01_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1/8 : ℝ)

def half_20_01_φ2 : Fin 2 → ℝ := Fin.snoc half_20_01_φ1 (1239247423/10000000000 : ℝ)

def half_20_01_φ3 : Fin 3 → ℝ := Fin.snoc half_20_01_φ2 (1072964653/10000000000 : ℝ)

def half_20_01_φ4 : Fin 4 → ℝ := Fin.snoc half_20_01_φ3 (919683989/10000000000 : ℝ)

def half_20_01_φ5 : Fin 5 → ℝ := Fin.snoc half_20_01_φ4 (394150281/5000000000 : ℝ)

theorem half_20_01_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_20_01_φ5) (59325870833/10000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_20_01_φ5 (by norm_num [half_20_01_φ1, half_20_01_φ2, half_20_01_φ3, half_20_01_φ4, half_20_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_20_01_φ1, half_20_01_φ2, half_20_01_φ3, half_20_01_φ4, half_20_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_20_01_φ1, half_20_01_φ2, half_20_01_φ3, half_20_01_φ4, half_20_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_20_01_φ1, half_20_01_φ2, half_20_01_φ3, half_20_01_φ4, half_20_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_20_01_φ1, half_20_01_φ2, half_20_01_φ3, half_20_01_φ4, half_20_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_20_01_hx5 : SourcePowerBound (powerBoxCross 8 15 32 half_20_01_φ5) (64766575187/5000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 15) (r := 2) (v := 0) (w := 20) (D := 32)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_20_01_φ5 (by norm_num [half_20_01_φ1, half_20_01_φ2, half_20_01_φ3, half_20_01_φ4, half_20_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_20_01_φ1, half_20_01_φ2, half_20_01_φ3, half_20_01_φ4, half_20_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_20_01_hF2 (admissibleExponent_zero 8) (half_20_00)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_20_01_φ1, half_20_01_φ2, half_20_01_φ3, half_20_01_φ4, half_20_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_20_01_hx4 : SourcePowerBound (powerBoxCross 8 16 16 half_20_01_φ4) (152992194547/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 16) (u := 14) (t := 17)
    (D := 16) (ψ := (394150281/5000000000 : ℝ)) half_20_01_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_20_01_φ1, half_20_01_φ2, half_20_01_φ3, half_20_01_φ4, half_20_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_20_01_φ1, half_20_01_φ2, half_20_01_φ3, half_20_01_φ4, half_20_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_20_01_φ1, half_20_01_φ2, half_20_01_φ3, half_20_01_φ4, half_20_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_15_01) (half_17_01)
    (by simpa only [half_20_01_φ5, show (2:ℝ)*16=32 by norm_num] using half_20_01_hx5)
  exact h.weaken (by norm_num [half_20_01_φ1, half_20_01_φ2, half_20_01_φ3, half_20_01_φ4, half_20_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_20_01_hx3 : SourcePowerBound (powerBoxCross 8 17 8 half_20_01_φ3) (9208088683/500000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 17) (u := 15) (t := 18)
    (D := 8) (ψ := (919683989/10000000000 : ℝ)) half_20_01_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_20_01_φ1, half_20_01_φ2, half_20_01_φ3, half_20_01_φ4, half_20_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_20_01_φ1, half_20_01_φ2, half_20_01_φ3, half_20_01_φ4, half_20_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_20_01_φ1, half_20_01_φ2, half_20_01_φ3, half_20_01_φ4, half_20_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_16_01) (half_18_01)
    (by simpa only [half_20_01_φ4, show (2:ℝ)*8=16 by norm_num] using half_20_01_hx4)
  exact h.weaken (by norm_num [half_20_01_φ1, half_20_01_φ2, half_20_01_φ3, half_20_01_φ4, half_20_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_20_01_hx2 : SourcePowerBound (powerBoxCross 8 18 4 half_20_01_φ2) (112269326657/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 18) (u := 16) (t := 19)
    (D := 4) (ψ := (1072964653/10000000000 : ℝ)) half_20_01_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_20_01_φ1, half_20_01_φ2, half_20_01_φ3, half_20_01_φ4, half_20_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_20_01_φ1, half_20_01_φ2, half_20_01_φ3, half_20_01_φ4, half_20_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_20_01_φ1, half_20_01_φ2, half_20_01_φ3, half_20_01_φ4, half_20_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_17_01) (half_19_01)
    (by simpa only [half_20_01_φ3, show (2:ℝ)*4=8 by norm_num] using half_20_01_hx3)
  exact h.weaken (by norm_num [half_20_01_φ1, half_20_01_φ2, half_20_01_φ3, half_20_01_φ4, half_20_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_20_01_hx1 : SourcePowerBound (powerBoxCross 8 19 2 half_20_01_φ1) (276044362557/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 19) (u := 17) (t := 20)
    (D := 2) (ψ := (1239247423/10000000000 : ℝ)) half_20_01_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_20_01_φ1, half_20_01_φ2, half_20_01_φ3, half_20_01_φ4, half_20_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_20_01_φ1, half_20_01_φ2, half_20_01_φ3, half_20_01_φ4, half_20_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_20_01_φ1, half_20_01_φ2, half_20_01_φ3, half_20_01_φ4, half_20_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_18_01) (half_20_00)
    (by simpa only [half_20_01_φ2, show (2:ℝ)*2=4 by norm_num] using half_20_01_hx2)
  exact h.weaken (by norm_num [half_20_01_φ1, half_20_01_φ2, half_20_01_φ3, half_20_01_φ4, half_20_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_20_01 : AdmissibleExponent 8 40 (322294362557/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 18) (ψ := (1/8 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_19_01)
    (by simpa only [half_20_01_φ1] using half_20_01_hx1)
  exact admissibleExponent_mono h (by norm_num [half_20_01_φ1, half_20_01_φ2, half_20_01_φ3, half_20_01_φ4, half_20_01_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_10_02_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (212152339/2000000000 : ℝ)

def half_10_02_φ2 : Fin 2 → ℝ := Fin.snoc half_10_02_φ1 (961852097/10000000000 : ℝ)

def half_10_02_φ3 : Fin 3 → ℝ := Fin.snoc half_10_02_φ2 (838244621/10000000000 : ℝ)

def half_10_02_φ4 : Fin 4 → ℝ := Fin.snoc half_10_02_φ3 (55465383/1000000000 : ℝ)

theorem half_10_02_hF2 : SourcePowerBound (paddedMoment 8 0 2 16 half_10_02_φ4) (68274242897/10000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 4) (r := 0) (n := 1) (D := 16)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_10_02_φ4 (by norm_num [half_10_02_φ1, half_10_02_φ2, half_10_02_φ3, half_10_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_02_φ1, half_10_02_φ2, half_10_02_φ3, half_10_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_02_φ1, half_10_02_φ2, half_10_02_φ3, half_10_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_10_02_φ1, half_10_02_φ2, half_10_02_φ3, half_10_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_10_02_φ1, half_10_02_φ2, half_10_02_φ3, half_10_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_10_02_hx4 : SourcePowerBound (powerBoxCross 8 6 16 half_10_02_φ4) (16419053579/2500000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 6) (r := 2) (v := 0) (w := 8) (D := 16)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_10_02_φ4 (by norm_num [half_10_02_φ1, half_10_02_φ2, half_10_02_φ3, half_10_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_02_φ1, half_10_02_φ2, half_10_02_φ3, half_10_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_10_02_hF2 (admissibleExponent_zero 8) (SeedCompletionHigher8SimpleSeeds.degree8_half_8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_10_02_φ1, half_10_02_φ2, half_10_02_φ3, half_10_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_02_hx3 : SourcePowerBound (powerBoxCross 8 7 8 half_10_02_φ3) (15202098349/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 7) (u := 5) (t := 8)
    (D := 8) (ψ := (55465383/1000000000 : ℝ)) half_10_02_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_02_φ1, half_10_02_φ2, half_10_02_φ3, half_10_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_02_φ1, half_10_02_φ2, half_10_02_φ3, half_10_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_02_φ1, half_10_02_φ2, half_10_02_φ3, half_10_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionEven8SecondSeeds.degree8_half_6) (SeedCompletionHigher8SimpleSeeds.degree8_half_8)
    (by simpa only [half_10_02_φ4, show (2:ℝ)*8=16 by norm_num] using half_10_02_hx4)
  exact h.weaken (by norm_num [half_10_02_φ1, half_10_02_φ2, half_10_02_φ3, half_10_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_02_hx2 : SourcePowerBound (powerBoxCross 8 8 4 half_10_02_φ2) (46028416179/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 8) (u := 6) (t := 9)
    (D := 4) (ψ := (838244621/10000000000 : ℝ)) half_10_02_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_02_φ1, half_10_02_φ2, half_10_02_φ3, half_10_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_02_φ1, half_10_02_φ2, half_10_02_φ3, half_10_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_02_φ1, half_10_02_φ2, half_10_02_φ3, half_10_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_7) (SeedCompletionHigher8SimpleSeeds.degree8_half_9)
    (by simpa only [half_10_02_φ3, show (2:ℝ)*4=8 by norm_num] using half_10_02_hx3)
  exact h.weaken (by norm_num [half_10_02_φ1, half_10_02_φ2, half_10_02_φ3, half_10_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_02_hx1 : SourcePowerBound (powerBoxCross 8 9 2 half_10_02_φ1) (113441057019/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 9) (u := 7) (t := 10)
    (D := 2) (ψ := (961852097/10000000000 : ℝ)) half_10_02_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_02_φ1, half_10_02_φ2, half_10_02_φ3, half_10_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_02_φ1, half_10_02_φ2, half_10_02_φ3, half_10_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_02_φ1, half_10_02_φ2, half_10_02_φ3, half_10_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_8) (half_10_01)
    (by simpa only [half_10_02_φ2, show (2:ℝ)*2=4 by norm_num] using half_10_02_hx2)
  exact h.weaken (by norm_num [half_10_02_φ1, half_10_02_φ2, half_10_02_φ3, half_10_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_02 : AdmissibleExponent 8 20 (65737002917/5000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 8) (ψ := (212152339/2000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_9)
    (by simpa only [half_10_02_φ1] using half_10_02_hx1)
  exact admissibleExponent_mono h (by norm_num [half_10_02_φ1, half_10_02_φ2, half_10_02_φ3, half_10_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_11_02_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (110844271/1000000000 : ℝ)

def half_11_02_φ2 : Fin 2 → ℝ := Fin.snoc half_11_02_φ1 (2557367/25000000 : ℝ)

def half_11_02_φ3 : Fin 3 → ℝ := Fin.snoc half_11_02_φ2 (926194731/10000000000 : ℝ)

def half_11_02_φ4 : Fin 4 → ℝ := Fin.snoc half_11_02_φ3 (150423479/2000000000 : ℝ)

theorem half_11_02_hF2 : SourcePowerBound (paddedMoment 8 0 2 16 half_11_02_φ4) (14999066411/2500000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 4) (r := 0) (n := 1) (D := 16)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_11_02_φ4 (by norm_num [half_11_02_φ1, half_11_02_φ2, half_11_02_φ3, half_11_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_02_φ1, half_11_02_φ2, half_11_02_φ3, half_11_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_02_φ1, half_11_02_φ2, half_11_02_φ3, half_11_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_11_02_φ1, half_11_02_φ2, half_11_02_φ3, half_11_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_11_02_φ1, half_11_02_φ2, half_11_02_φ3, half_11_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_11_02_hx4 : SourcePowerBound (powerBoxCross 8 7 16 half_11_02_φ4) (35397057869/5000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 7) (r := 2) (v := 9) (w := 10) (D := 16)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_11_02_φ4 (by norm_num [half_11_02_φ1, half_11_02_φ2, half_11_02_φ3, half_11_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_02_φ1, half_11_02_φ2, half_11_02_φ3, half_11_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_11_02_hF2 (SeedCompletionHigher8SimpleSeeds.degree8_half_9) (half_10_02)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_11_02_φ1, half_11_02_φ2, half_11_02_φ3, half_11_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_02_hx3 : SourcePowerBound (powerBoxCross 8 8 8 half_11_02_φ3) (42169854453/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 8) (u := 6) (t := 9)
    (D := 8) (ψ := (150423479/2000000000 : ℝ)) half_11_02_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_02_φ1, half_11_02_φ2, half_11_02_φ3, half_11_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_02_φ1, half_11_02_φ2, half_11_02_φ3, half_11_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_02_φ1, half_11_02_φ2, half_11_02_φ3, half_11_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_7) (SeedCompletionHigher8SimpleSeeds.degree8_half_9)
    (by simpa only [half_11_02_φ4, show (2:ℝ)*8=16 by norm_num] using half_11_02_hx4)
  exact h.weaken (by norm_num [half_11_02_φ1, half_11_02_φ2, half_11_02_φ3, half_11_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_02_hx2 : SourcePowerBound (powerBoxCross 8 9 4 half_11_02_φ2) (25845584681/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 9) (u := 7) (t := 10)
    (D := 4) (ψ := (926194731/10000000000 : ℝ)) half_11_02_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_02_φ1, half_11_02_φ2, half_11_02_φ3, half_11_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_02_φ1, half_11_02_φ2, half_11_02_φ3, half_11_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_02_φ1, half_11_02_φ2, half_11_02_φ3, half_11_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_8) (half_10_02)
    (by simpa only [half_11_02_φ3, show (2:ℝ)*4=8 by norm_num] using half_11_02_hx3)
  exact h.weaken (by norm_num [half_11_02_φ1, half_11_02_φ2, half_11_02_φ3, half_11_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_02_hx1 : SourcePowerBound (powerBoxCross 8 10 2 half_11_02_φ1) (128009308221/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 10) (u := 8) (t := 11)
    (D := 2) (ψ := (2557367/25000000 : ℝ)) half_11_02_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_02_φ1, half_11_02_φ2, half_11_02_φ3, half_11_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_02_φ1, half_11_02_φ2, half_11_02_φ3, half_11_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_02_φ1, half_11_02_φ2, half_11_02_φ3, half_11_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_9) (half_11_01)
    (by simpa only [half_11_02_φ2, show (2:ℝ)*2=4 by norm_num] using half_11_02_hx2)
  exact h.weaken (by norm_num [half_11_02_φ1, half_11_02_φ2, half_11_02_φ3, half_11_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_02 : AdmissibleExponent 8 22 (149069719711/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 9) (ψ := (110844271/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_10_02)
    (by simpa only [half_11_02_φ1] using half_11_02_hx1)
  exact admissibleExponent_mono h (by norm_num [half_11_02_φ1, half_11_02_φ2, half_11_02_φ3, half_11_02_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem chord_33 : AdmissibleExponent 8 24 (83819769349/5000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 24) (t := (1/2 : ℝ))
    (half_11_02) (half_13_01) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1 <;> norm_num

def half_12_02_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (283280437/2500000000 : ℝ)

def half_12_02_φ2 : Fin 2 → ℝ := Fin.snoc half_12_02_φ1 (530179891/5000000000 : ℝ)

def half_12_02_φ3 : Fin 3 → ℝ := Fin.snoc half_12_02_φ2 (1972693/20000000 : ℝ)

def half_12_02_φ4 : Fin 4 → ℝ := Fin.snoc half_12_02_φ3 (422731801/5000000000 : ℝ)

def half_12_02_φ5 : Fin 5 → ℝ := Fin.snoc half_12_02_φ4 (269156001/5000000000 : ℝ)

theorem half_12_02_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_12_02_φ5) (37082161843/5000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_12_02_φ5 (by norm_num [half_12_02_φ1, half_12_02_φ2, half_12_02_φ3, half_12_02_φ4, half_12_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_02_φ1, half_12_02_φ2, half_12_02_φ3, half_12_02_φ4, half_12_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_02_φ1, half_12_02_φ2, half_12_02_φ3, half_12_02_φ4, half_12_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_12_02_φ1, half_12_02_φ2, half_12_02_φ3, half_12_02_φ4, half_12_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_12_02_φ1, half_12_02_φ2, half_12_02_φ3, half_12_02_φ4, half_12_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_12_02_hx5 : SourcePowerBound (powerBoxCross 8 7 32 half_12_02_φ5) (67540981341/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 7) (r := 2) (v := 9) (w := 10) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_12_02_φ5 (by norm_num [half_12_02_φ1, half_12_02_φ2, half_12_02_φ3, half_12_02_φ4, half_12_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_02_φ1, half_12_02_φ2, half_12_02_φ3, half_12_02_φ4, half_12_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_12_02_hF2 (SeedCompletionHigher8SimpleSeeds.degree8_half_9) (half_10_02)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_12_02_φ1, half_12_02_φ2, half_12_02_φ3, half_12_02_φ4, half_12_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_02_hx4 : SourcePowerBound (powerBoxCross 8 8 16 half_12_02_φ4) (15478979553/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 8) (u := 6) (t := 9)
    (D := 16) (ψ := (269156001/5000000000 : ℝ)) half_12_02_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_02_φ1, half_12_02_φ2, half_12_02_φ3, half_12_02_φ4, half_12_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_02_φ1, half_12_02_φ2, half_12_02_φ3, half_12_02_φ4, half_12_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_02_φ1, half_12_02_φ2, half_12_02_φ3, half_12_02_φ4, half_12_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_7) (SeedCompletionHigher8SimpleSeeds.degree8_half_9)
    (by simpa only [half_12_02_φ5, show (2:ℝ)*16=32 by norm_num] using half_12_02_hx5)
  exact h.weaken (by norm_num [half_12_02_φ1, half_12_02_φ2, half_12_02_φ3, half_12_02_φ4, half_12_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_02_hx3 : SourcePowerBound (powerBoxCross 8 9 8 half_12_02_φ3) (46871397131/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 9) (u := 7) (t := 10)
    (D := 8) (ψ := (422731801/5000000000 : ℝ)) half_12_02_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_02_φ1, half_12_02_φ2, half_12_02_φ3, half_12_02_φ4, half_12_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_02_φ1, half_12_02_φ2, half_12_02_φ3, half_12_02_φ4, half_12_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_02_φ1, half_12_02_φ2, half_12_02_φ3, half_12_02_φ4, half_12_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_8) (half_10_02)
    (by simpa only [half_12_02_φ4, show (2:ℝ)*8=16 by norm_num] using half_12_02_hx4)
  exact h.weaken (by norm_num [half_12_02_φ1, half_12_02_φ2, half_12_02_φ3, half_12_02_φ4, half_12_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_02_hx2 : SourcePowerBound (powerBoxCross 8 10 4 half_12_02_φ2) (115763933039/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 10) (u := 8) (t := 11)
    (D := 4) (ψ := (1972693/20000000 : ℝ)) half_12_02_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_02_φ1, half_12_02_φ2, half_12_02_φ3, half_12_02_φ4, half_12_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_02_φ1, half_12_02_φ2, half_12_02_φ3, half_12_02_φ4, half_12_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_02_φ1, half_12_02_φ2, half_12_02_φ3, half_12_02_φ4, half_12_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_9) (half_11_02)
    (by simpa only [half_12_02_φ3, show (2:ℝ)*4=8 by norm_num] using half_12_02_hx3)
  exact h.weaken (by norm_num [half_12_02_φ1, half_12_02_φ2, half_12_02_φ3, half_12_02_φ4, half_12_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_02_hx1 : SourcePowerBound (powerBoxCross 8 11 2 half_12_02_φ1) (35827856831/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 11) (u := 9) (t := 12)
    (D := 2) (ψ := (530179891/5000000000 : ℝ)) half_12_02_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_02_φ1, half_12_02_φ2, half_12_02_φ3, half_12_02_φ4, half_12_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_02_φ1, half_12_02_φ2, half_12_02_φ3, half_12_02_φ4, half_12_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_02_φ1, half_12_02_φ2, half_12_02_φ3, half_12_02_φ4, half_12_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_10_02) (chord_33)
    (by simpa only [half_12_02_φ2, show (2:ℝ)*2=4 by norm_num] using half_12_02_hx2)
  exact h.weaken (by norm_num [half_12_02_φ1, half_12_02_φ2, half_12_02_φ3, half_12_02_φ4, half_12_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_02 : AdmissibleExponent 8 24 (5222093251/312500000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 10) (ψ := (283280437/2500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_11_02)
    (by simpa only [half_12_02_φ1] using half_12_02_hx1)
  exact admissibleExponent_mono h (by norm_num [half_12_02_φ1, half_12_02_φ2, half_12_02_φ3, half_12_02_φ4, half_12_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem chord_34 : AdmissibleExponent 8 26 (372089818287/20000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 26) (t := (1/2 : ℝ))
    (half_12_02) (half_14_01) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1 <;> norm_num

def half_13_02_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1157292733/10000000000 : ℝ)

def half_13_02_φ2 : Fin 2 → ℝ := Fin.snoc half_13_02_φ1 (34013399/312500000 : ℝ)

def half_13_02_φ3 : Fin 3 → ℝ := Fin.snoc half_13_02_φ2 (129010711/1250000000 : ℝ)

def half_13_02_φ4 : Fin 4 → ℝ := Fin.snoc half_13_02_φ3 (37121121/400000000 : ℝ)

def half_13_02_φ5 : Fin 5 → ℝ := Fin.snoc half_13_02_φ4 (707987771/10000000000 : ℝ)

theorem half_13_02_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_13_02_φ5) (13361943463/2000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_13_02_φ5 (by norm_num [half_13_02_φ1, half_13_02_φ2, half_13_02_φ3, half_13_02_φ4, half_13_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_02_φ1, half_13_02_φ2, half_13_02_φ3, half_13_02_φ4, half_13_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_02_φ1, half_13_02_φ2, half_13_02_φ3, half_13_02_φ4, half_13_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_13_02_φ1, half_13_02_φ2, half_13_02_φ3, half_13_02_φ4, half_13_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_13_02_φ1, half_13_02_φ2, half_13_02_φ3, half_13_02_φ4, half_13_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_13_02_hx5 : SourcePowerBound (powerBoxCross 8 8 32 half_13_02_φ5) (35664840047/5000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 8) (r := 2) (v := 10) (w := 11) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_13_02_φ5 (by norm_num [half_13_02_φ1, half_13_02_φ2, half_13_02_φ3, half_13_02_φ4, half_13_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_02_φ1, half_13_02_φ2, half_13_02_φ3, half_13_02_φ4, half_13_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_13_02_hF2 (half_10_02) (half_11_02)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_13_02_φ1, half_13_02_φ2, half_13_02_φ3, half_13_02_φ4, half_13_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_02_hx4 : SourcePowerBound (powerBoxCross 8 9 16 half_13_02_φ4) (3373737113/400000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 9) (u := 7) (t := 10)
    (D := 16) (ψ := (707987771/10000000000 : ℝ)) half_13_02_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_02_φ1, half_13_02_φ2, half_13_02_φ3, half_13_02_φ4, half_13_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_02_φ1, half_13_02_φ2, half_13_02_φ3, half_13_02_φ4, half_13_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_02_φ1, half_13_02_φ2, half_13_02_φ3, half_13_02_φ4, half_13_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_8) (half_10_02)
    (by simpa only [half_13_02_φ5, show (2:ℝ)*16=32 by norm_num] using half_13_02_hx5)
  exact h.weaken (by norm_num [half_13_02_φ1, half_13_02_φ2, half_13_02_φ3, half_13_02_φ4, half_13_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_02_hx3 : SourcePowerBound (powerBoxCross 8 10 8 half_13_02_φ3) (103691396873/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 10) (u := 8) (t := 11)
    (D := 8) (ψ := (37121121/400000000 : ℝ)) half_13_02_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_02_φ1, half_13_02_φ2, half_13_02_φ3, half_13_02_φ4, half_13_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_02_φ1, half_13_02_φ2, half_13_02_φ3, half_13_02_φ4, half_13_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_02_φ1, half_13_02_φ2, half_13_02_φ3, half_13_02_φ4, half_13_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_9) (half_11_02)
    (by simpa only [half_13_02_φ4, show (2:ℝ)*8=16 by norm_num] using half_13_02_hx4)
  exact h.weaken (by norm_num [half_13_02_φ1, half_13_02_φ2, half_13_02_φ3, half_13_02_φ4, half_13_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_02_hx2 : SourcePowerBound (powerBoxCross 8 11 4 half_13_02_φ2) (25716038377/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 11) (u := 9) (t := 12)
    (D := 4) (ψ := (129010711/1250000000 : ℝ)) half_13_02_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_02_φ1, half_13_02_φ2, half_13_02_φ3, half_13_02_φ4, half_13_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_02_φ1, half_13_02_φ2, half_13_02_φ3, half_13_02_φ4, half_13_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_02_φ1, half_13_02_φ2, half_13_02_φ3, half_13_02_φ4, half_13_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_10_02) (half_12_02)
    (by simpa only [half_13_02_φ3, show (2:ℝ)*4=8 by norm_num] using half_13_02_hx3)
  exact h.weaken (by norm_num [half_13_02_φ1, half_13_02_φ2, half_13_02_φ3, half_13_02_φ4, half_13_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_02_hx1 : SourcePowerBound (powerBoxCross 8 12 2 half_13_02_φ1) (31785021389/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 12) (u := 10) (t := 13)
    (D := 2) (ψ := (34013399/312500000 : ℝ)) half_13_02_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_02_φ1, half_13_02_φ2, half_13_02_φ3, half_13_02_φ4, half_13_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_02_φ1, half_13_02_φ2, half_13_02_φ3, half_13_02_φ4, half_13_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_02_φ1, half_13_02_φ2, half_13_02_φ3, half_13_02_φ4, half_13_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_11_02) (chord_34)
    (by simpa only [half_13_02_φ2, show (2:ℝ)*2=4 by norm_num] using half_13_02_hx2)
  exact h.weaken (by norm_num [half_13_02_φ1, half_13_02_φ2, half_13_02_φ3, half_13_02_φ4, half_13_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_02 : AdmissibleExponent 8 26 (46385709951/2500000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 11) (ψ := (1157292733/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_12_02)
    (by simpa only [half_13_02_φ1] using half_13_02_hx1)
  exact admissibleExponent_mono h (by norm_num [half_13_02_φ1, half_13_02_φ2, half_13_02_φ3, half_13_02_φ4, half_13_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem chord_35 : AdmissibleExponent 8 28 (12798601769/625000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 28) (t := (1/2 : ℝ))
    (half_13_02) (half_15_01) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1 <;> norm_num

def half_14_02_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (5896329/50000000 : ℝ)

def half_14_02_φ2 : Fin 2 → ℝ := Fin.snoc half_14_02_φ1 (1119933833/10000000000 : ℝ)

def half_14_02_φ3 : Fin 3 → ℝ := Fin.snoc half_14_02_φ2 (1073165647/10000000000 : ℝ)

def half_14_02_φ4 : Fin 4 → ℝ := Fin.snoc half_14_02_φ3 (946804959/10000000000 : ℝ)

def half_14_02_φ5 : Fin 5 → ℝ := Fin.snoc half_14_02_φ4 (202886777/2500000000 : ℝ)

theorem half_14_02_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_14_02_φ5) (62254935713/10000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_14_02_φ5 (by norm_num [half_14_02_φ1, half_14_02_φ2, half_14_02_φ3, half_14_02_φ4, half_14_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_02_φ1, half_14_02_φ2, half_14_02_φ3, half_14_02_φ4, half_14_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_02_φ1, half_14_02_φ2, half_14_02_φ3, half_14_02_φ4, half_14_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_14_02_φ1, half_14_02_φ2, half_14_02_φ3, half_14_02_φ4, half_14_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_14_02_φ1, half_14_02_φ2, half_14_02_φ3, half_14_02_φ4, half_14_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_14_02_hx5 : SourcePowerBound (powerBoxCross 8 9 32 half_14_02_φ5) (76590569319/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 9) (r := 2) (v := 0) (w := 12) (D := 32)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_14_02_φ5 (by norm_num [half_14_02_φ1, half_14_02_φ2, half_14_02_φ3, half_14_02_φ4, half_14_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_02_φ1, half_14_02_φ2, half_14_02_φ3, half_14_02_φ4, half_14_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_14_02_hF2 (admissibleExponent_zero 8) (half_12_02)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_14_02_φ1, half_14_02_φ2, half_14_02_φ3, half_14_02_φ4, half_14_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_02_hx4 : SourcePowerBound (powerBoxCross 8 10 16 half_14_02_φ4) (92418324251/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 10) (u := 8) (t := 11)
    (D := 16) (ψ := (202886777/2500000000 : ℝ)) half_14_02_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_02_φ1, half_14_02_φ2, half_14_02_φ3, half_14_02_φ4, half_14_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_02_φ1, half_14_02_φ2, half_14_02_φ3, half_14_02_φ4, half_14_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_02_φ1, half_14_02_φ2, half_14_02_φ3, half_14_02_φ4, half_14_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_9) (half_11_02)
    (by simpa only [half_14_02_φ5, show (2:ℝ)*16=32 by norm_num] using half_14_02_hx5)
  exact h.weaken (by norm_num [half_14_02_φ1, half_14_02_φ2, half_14_02_φ3, half_14_02_φ4, half_14_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_02_hx3 : SourcePowerBound (powerBoxCross 8 11 8 half_14_02_φ3) (113776733223/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 11) (u := 9) (t := 12)
    (D := 8) (ψ := (946804959/10000000000 : ℝ)) half_14_02_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_02_φ1, half_14_02_φ2, half_14_02_φ3, half_14_02_φ4, half_14_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_02_φ1, half_14_02_φ2, half_14_02_φ3, half_14_02_φ4, half_14_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_02_φ1, half_14_02_φ2, half_14_02_φ3, half_14_02_φ4, half_14_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_10_02) (half_12_02)
    (by simpa only [half_14_02_φ4, show (2:ℝ)*8=16 by norm_num] using half_14_02_hx4)
  exact h.weaken (by norm_num [half_14_02_φ1, half_14_02_φ2, half_14_02_φ3, half_14_02_φ4, half_14_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_02_hx2 : SourcePowerBound (powerBoxCross 8 12 4 half_14_02_φ2) (141550825633/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 12) (u := 10) (t := 13)
    (D := 4) (ψ := (1073165647/10000000000 : ℝ)) half_14_02_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_02_φ1, half_14_02_φ2, half_14_02_φ3, half_14_02_φ4, half_14_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_02_φ1, half_14_02_φ2, half_14_02_φ3, half_14_02_φ4, half_14_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_02_φ1, half_14_02_φ2, half_14_02_φ3, half_14_02_φ4, half_14_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_11_02) (half_13_02)
    (by simpa only [half_14_02_φ3, show (2:ℝ)*4=8 by norm_num] using half_14_02_hx3)
  exact h.weaken (by norm_num [half_14_02_φ1, half_14_02_φ2, half_14_02_φ3, half_14_02_φ4, half_14_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_02_hx1 : SourcePowerBound (powerBoxCross 8 13 2 half_14_02_φ1) (34968334613/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 13) (u := 11) (t := 14)
    (D := 2) (ψ := (1119933833/10000000000 : ℝ)) half_14_02_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_02_φ1, half_14_02_φ2, half_14_02_φ3, half_14_02_φ4, half_14_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_02_φ1, half_14_02_φ2, half_14_02_φ3, half_14_02_φ4, half_14_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_02_φ1, half_14_02_φ2, half_14_02_φ3, half_14_02_φ4, half_14_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_12_02) (chord_35)
    (by simpa only [half_14_02_φ2, show (2:ℝ)*2=4 by norm_num] using half_14_02_hx2)
  exact h.weaken (by norm_num [half_14_02_φ1, half_14_02_φ2, half_14_02_φ3, half_14_02_φ4, half_14_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_02 : AdmissibleExponent 8 28 (40864663613/2000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 12) (ψ := (5896329/50000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_13_02)
    (by simpa only [half_14_02_φ1] using half_14_02_hx1)
  exact admissibleExponent_mono h (by norm_num [half_14_02_φ1, half_14_02_φ2, half_14_02_φ3, half_14_02_φ4, half_14_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem chord_36 : AdmissibleExponent 8 30 (44756829559/2000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 30) (t := (2/3 : ℝ))
    (half_14_02) (half_17_01) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1 <;> norm_num

theorem chord_37 : AdmissibleExponent 8 32 (9729799101/400000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 32) (t := (1/3 : ℝ))
    (half_14_02) (half_17_01) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1 <;> norm_num

def half_15_02_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1197803079/10000000000 : ℝ)

def half_15_02_φ2 : Fin 2 → ℝ := Fin.snoc half_15_02_φ1 (575229467/5000000000 : ℝ)

def half_15_02_φ3 : Fin 3 → ℝ := Fin.snoc half_15_02_φ2 (546552713/5000000000 : ℝ)

def half_15_02_φ4 : Fin 4 → ℝ := Fin.snoc half_15_02_φ3 (234236877/2500000000 : ℝ)

def half_15_02_φ5 : Fin 5 → ℝ := Fin.snoc half_15_02_φ4 (100387233/1250000000 : ℝ)

theorem half_15_02_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_15_02_φ5) (61190330969/10000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_15_02_φ5 (by norm_num [half_15_02_φ1, half_15_02_φ2, half_15_02_φ3, half_15_02_φ4, half_15_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_02_φ1, half_15_02_φ2, half_15_02_φ3, half_15_02_φ4, half_15_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_02_φ1, half_15_02_φ2, half_15_02_φ3, half_15_02_φ4, half_15_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_15_02_φ1, half_15_02_φ2, half_15_02_φ3, half_15_02_φ4, half_15_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_15_02_φ1, half_15_02_φ2, half_15_02_φ3, half_15_02_φ4, half_15_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_15_02_hx5 : SourcePowerBound (powerBoxCross 8 10 32 half_15_02_φ5) (42307021679/5000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 10) (r := 2) (v := 13) (w := 14) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_15_02_φ5 (by norm_num [half_15_02_φ1, half_15_02_φ2, half_15_02_φ3, half_15_02_φ4, half_15_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_02_φ1, half_15_02_φ2, half_15_02_φ3, half_15_02_φ4, half_15_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_15_02_hF2 (half_13_02) (half_14_02)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_15_02_φ1, half_15_02_φ2, half_15_02_φ3, half_15_02_φ4, half_15_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_02_hx4 : SourcePowerBound (powerBoxCross 8 11 16 half_15_02_φ4) (12697936349/1250000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 11) (u := 9) (t := 12)
    (D := 16) (ψ := (100387233/1250000000 : ℝ)) half_15_02_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_02_φ1, half_15_02_φ2, half_15_02_φ3, half_15_02_φ4, half_15_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_02_φ1, half_15_02_φ2, half_15_02_φ3, half_15_02_φ4, half_15_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_02_φ1, half_15_02_φ2, half_15_02_φ3, half_15_02_φ4, half_15_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_10_02) (half_12_02)
    (by simpa only [half_15_02_φ5, show (2:ℝ)*16=32 by norm_num] using half_15_02_hx5)
  exact h.weaken (by norm_num [half_15_02_φ1, half_15_02_φ2, half_15_02_φ3, half_15_02_φ4, half_15_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_02_hx3 : SourcePowerBound (powerBoxCross 8 12 8 half_15_02_φ3) (31107568431/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 12) (u := 10) (t := 13)
    (D := 8) (ψ := (234236877/2500000000 : ℝ)) half_15_02_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_02_φ1, half_15_02_φ2, half_15_02_φ3, half_15_02_φ4, half_15_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_02_φ1, half_15_02_φ2, half_15_02_φ3, half_15_02_φ4, half_15_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_02_φ1, half_15_02_φ2, half_15_02_φ3, half_15_02_φ4, half_15_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_11_02) (half_13_02)
    (by simpa only [half_15_02_φ4, show (2:ℝ)*8=16 by norm_num] using half_15_02_hx4)
  exact h.weaken (by norm_num [half_15_02_φ1, half_15_02_φ2, half_15_02_φ3, half_15_02_φ4, half_15_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_02_hx2 : SourcePowerBound (powerBoxCross 8 13 4 half_15_02_φ2) (154738356939/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 13) (u := 11) (t := 14)
    (D := 4) (ψ := (546552713/5000000000 : ℝ)) half_15_02_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_02_φ1, half_15_02_φ2, half_15_02_φ3, half_15_02_φ4, half_15_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_02_φ1, half_15_02_φ2, half_15_02_φ3, half_15_02_φ4, half_15_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_02_φ1, half_15_02_φ2, half_15_02_φ3, half_15_02_φ4, half_15_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_12_02) (half_14_02)
    (by simpa only [half_15_02_φ3, show (2:ℝ)*4=8 by norm_num] using half_15_02_hx3)
  exact h.weaken (by norm_num [half_15_02_φ1, half_15_02_φ2, half_15_02_φ3, half_15_02_φ4, half_15_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_02_hx1 : SourcePowerBound (powerBoxCross 8 14 2 half_15_02_φ1) (191047211203/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 14) (u := 12) (t := 15)
    (D := 2) (ψ := (575229467/5000000000 : ℝ)) half_15_02_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_02_φ1, half_15_02_φ2, half_15_02_φ3, half_15_02_φ4, half_15_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_02_φ1, half_15_02_φ2, half_15_02_φ3, half_15_02_φ4, half_15_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_02_φ1, half_15_02_φ2, half_15_02_φ3, half_15_02_φ4, half_15_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_13_02) (chord_36)
    (by simpa only [half_15_02_φ2, show (2:ℝ)*2=4 by norm_num] using half_15_02_hx2)
  exact h.weaken (by norm_num [half_15_02_φ1, half_15_02_φ2, half_15_02_φ3, half_15_02_φ4, half_15_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_02 : AdmissibleExponent 8 30 (3490435849/156250000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 13) (ψ := (1197803079/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_14_02)
    (by simpa only [half_15_02_φ1] using half_15_02_hx1)
  exact admissibleExponent_mono h (by norm_num [half_15_02_φ1, half_15_02_φ2, half_15_02_φ3, half_15_02_φ4, half_15_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem chord_38 : AdmissibleExponent 8 32 (729103563041/30000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 32) (t := (2/3 : ℝ))
    (half_15_02) (half_18_01) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1 <;> norm_num

theorem chord_39 : AdmissibleExponent 8 34 (394021721537/15000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 34) (t := (1/3 : ℝ))
    (half_15_02) (half_18_01) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1 <;> norm_num

def half_16_02_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1213149617/10000000000 : ℝ)

def half_16_02_φ2 : Fin 2 → ℝ := Fin.snoc half_16_02_φ1 (1175917689/10000000000 : ℝ)

def half_16_02_φ3 : Fin 3 → ℝ := Fin.snoc half_16_02_φ2 (543638049/5000000000 : ℝ)

def half_16_02_φ4 : Fin 4 → ℝ := Fin.snoc half_16_02_φ3 (931950941/10000000000 : ℝ)

def half_16_02_φ5 : Fin 5 → ℝ := Fin.snoc half_16_02_φ4 (798815093/10000000000 : ℝ)

theorem half_16_02_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_16_02_φ5) (30325350901/5000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_16_02_φ5 (by norm_num [half_16_02_φ1, half_16_02_φ2, half_16_02_φ3, half_16_02_φ4, half_16_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_02_φ1, half_16_02_φ2, half_16_02_φ3, half_16_02_φ4, half_16_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_02_φ1, half_16_02_φ2, half_16_02_φ3, half_16_02_φ4, half_16_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_16_02_φ1, half_16_02_φ2, half_16_02_φ3, half_16_02_φ4, half_16_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_16_02_φ1, half_16_02_φ2, half_16_02_φ3, half_16_02_φ4, half_16_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_16_02_hx5 : SourcePowerBound (powerBoxCross 8 11 32 half_16_02_φ5) (93178844541/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 11) (r := 2) (v := 14) (w := 15) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_16_02_φ5 (by norm_num [half_16_02_φ1, half_16_02_φ2, half_16_02_φ3, half_16_02_φ4, half_16_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_02_φ1, half_16_02_φ2, half_16_02_φ3, half_16_02_φ4, half_16_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_16_02_hF2 (half_14_02) (half_15_02)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_16_02_φ1, half_16_02_φ2, half_16_02_φ3, half_16_02_φ4, half_16_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_02_hx4 : SourcePowerBound (powerBoxCross 8 12 16 half_16_02_φ4) (111422997869/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 12) (u := 10) (t := 13)
    (D := 16) (ψ := (798815093/10000000000 : ℝ)) half_16_02_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_02_φ1, half_16_02_φ2, half_16_02_φ3, half_16_02_φ4, half_16_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_02_φ1, half_16_02_φ2, half_16_02_φ3, half_16_02_φ4, half_16_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_02_φ1, half_16_02_φ2, half_16_02_φ3, half_16_02_φ4, half_16_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_11_02) (half_13_02)
    (by simpa only [half_16_02_φ5, show (2:ℝ)*16=32 by norm_num] using half_16_02_hx5)
  exact h.weaken (by norm_num [half_16_02_φ1, half_16_02_φ2, half_16_02_φ3, half_16_02_φ4, half_16_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_02_hx3 : SourcePowerBound (powerBoxCross 8 13 8 half_16_02_φ3) (135908490923/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 13) (u := 11) (t := 14)
    (D := 8) (ψ := (931950941/10000000000 : ℝ)) half_16_02_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_02_φ1, half_16_02_φ2, half_16_02_φ3, half_16_02_φ4, half_16_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_02_φ1, half_16_02_φ2, half_16_02_φ3, half_16_02_φ4, half_16_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_02_φ1, half_16_02_φ2, half_16_02_φ3, half_16_02_φ4, half_16_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_12_02) (half_14_02)
    (by simpa only [half_16_02_φ4, show (2:ℝ)*8=16 by norm_num] using half_16_02_hx4)
  exact h.weaken (by norm_num [half_16_02_φ1, half_16_02_φ2, half_16_02_φ3, half_16_02_φ4, half_16_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_02_hx2 : SourcePowerBound (powerBoxCross 8 14 4 half_16_02_φ2) (84096486269/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 14) (u := 12) (t := 15)
    (D := 4) (ψ := (543638049/5000000000 : ℝ)) half_16_02_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_02_φ1, half_16_02_φ2, half_16_02_φ3, half_16_02_φ4, half_16_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_02_φ1, half_16_02_φ2, half_16_02_φ3, half_16_02_φ4, half_16_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_02_φ1, half_16_02_φ2, half_16_02_φ3, half_16_02_φ4, half_16_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_13_02) (half_15_02)
    (by simpa only [half_16_02_φ3, show (2:ℝ)*4=8 by norm_num] using half_16_02_hx3)
  exact h.weaken (by norm_num [half_16_02_φ1, half_16_02_φ2, half_16_02_φ3, half_16_02_φ4, half_16_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_02_hx1 : SourcePowerBound (powerBoxCross 8 15 2 half_16_02_φ1) (103750375057/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 15) (u := 13) (t := 16)
    (D := 2) (ψ := (1175917689/10000000000 : ℝ)) half_16_02_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_02_φ1, half_16_02_φ2, half_16_02_φ3, half_16_02_φ4, half_16_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_02_φ1, half_16_02_φ2, half_16_02_φ3, half_16_02_φ4, half_16_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_02_φ1, half_16_02_φ2, half_16_02_φ3, half_16_02_φ4, half_16_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_14_02) (chord_38)
    (by simpa only [half_16_02_φ2, show (2:ℝ)*2=4 by norm_num] using half_16_02_hx2)
  exact h.weaken (by norm_num [half_16_02_φ1, half_16_02_φ2, half_16_02_φ3, half_16_02_φ4, half_16_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_02 : AdmissibleExponent 8 32 (242682089007/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 14) (ψ := (1213149617/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_15_02)
    (by simpa only [half_16_02_φ1] using half_16_02_hx1)
  exact admissibleExponent_mono h (by norm_num [half_16_02_φ1, half_16_02_φ2, half_16_02_φ3, half_16_02_φ4, half_16_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem chord_40 : AdmissibleExponent 8 34 (157501515433/6000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 34) (t := (2/3 : ℝ))
    (half_16_02) (half_19_01) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1 <;> norm_num

theorem chord_41 : AdmissibleExponent 8 36 (846968887309/30000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 36) (t := (1/3 : ℝ))
    (half_16_02) (half_19_01) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1 <;> norm_num

def half_17_02_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1226596233/10000000000 : ℝ)

def half_17_02_φ2 : Fin 2 → ℝ := Fin.snoc half_17_02_φ1 (1196135553/10000000000 : ℝ)

def half_17_02_φ3 : Fin 3 → ℝ := Fin.snoc half_17_02_φ2 (1082466887/10000000000 : ℝ)

def half_17_02_φ4 : Fin 4 → ℝ := Fin.snoc half_17_02_φ3 (23195719/250000000 : ℝ)

def half_17_02_φ5 : Fin 5 → ℝ := Fin.snoc half_17_02_φ4 (397640897/5000000000 : ℝ)

theorem half_17_02_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_17_02_φ5) (60205506233/10000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_17_02_φ5 (by norm_num [half_17_02_φ1, half_17_02_φ2, half_17_02_φ3, half_17_02_φ4, half_17_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_02_φ1, half_17_02_φ2, half_17_02_φ3, half_17_02_φ4, half_17_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_02_φ1, half_17_02_φ2, half_17_02_φ3, half_17_02_φ4, half_17_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_17_02_φ1, half_17_02_φ2, half_17_02_φ3, half_17_02_φ4, half_17_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_17_02_φ1, half_17_02_φ2, half_17_02_φ3, half_17_02_φ4, half_17_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_17_02_hx5 : SourcePowerBound (powerBoxCross 8 12 32 half_17_02_φ5) (4076066717/400000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 12) (r := 2) (v := 0) (w := 16) (D := 32)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_17_02_φ5 (by norm_num [half_17_02_φ1, half_17_02_φ2, half_17_02_φ3, half_17_02_φ4, half_17_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_02_φ1, half_17_02_φ2, half_17_02_φ3, half_17_02_φ4, half_17_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_17_02_hF2 (admissibleExponent_zero 8) (half_16_02)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_17_02_φ1, half_17_02_φ2, half_17_02_φ3, half_17_02_φ4, half_17_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_02_hx4 : SourcePowerBound (powerBoxCross 8 13 16 half_17_02_φ4) (60727046951/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 13) (u := 11) (t := 14)
    (D := 16) (ψ := (397640897/5000000000 : ℝ)) half_17_02_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_02_φ1, half_17_02_φ2, half_17_02_φ3, half_17_02_φ4, half_17_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_02_φ1, half_17_02_φ2, half_17_02_φ3, half_17_02_φ4, half_17_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_02_φ1, half_17_02_φ2, half_17_02_φ3, half_17_02_φ4, half_17_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_12_02) (half_14_02)
    (by simpa only [half_17_02_φ5, show (2:ℝ)*16=32 by norm_num] using half_17_02_hx5)
  exact h.weaken (by norm_num [half_17_02_φ1, half_17_02_φ2, half_17_02_φ3, half_17_02_φ4, half_17_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_02_hx3 : SourcePowerBound (powerBoxCross 8 14 8 half_17_02_φ3) (36899927681/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 14) (u := 12) (t := 15)
    (D := 8) (ψ := (23195719/250000000 : ℝ)) half_17_02_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_02_φ1, half_17_02_φ2, half_17_02_φ3, half_17_02_φ4, half_17_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_02_φ1, half_17_02_φ2, half_17_02_φ3, half_17_02_φ4, half_17_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_02_φ1, half_17_02_φ2, half_17_02_φ3, half_17_02_φ4, half_17_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_13_02) (half_15_02)
    (by simpa only [half_17_02_φ4, show (2:ℝ)*8=16 by norm_num] using half_17_02_hx4)
  exact h.weaken (by norm_num [half_17_02_φ1, half_17_02_φ2, half_17_02_φ3, half_17_02_φ4, half_17_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_02_hx2 : SourcePowerBound (powerBoxCross 8 15 4 half_17_02_φ2) (181876961043/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 15) (u := 13) (t := 16)
    (D := 4) (ψ := (1082466887/10000000000 : ℝ)) half_17_02_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_02_φ1, half_17_02_φ2, half_17_02_φ3, half_17_02_φ4, half_17_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_02_φ1, half_17_02_φ2, half_17_02_φ3, half_17_02_φ4, half_17_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_02_φ1, half_17_02_φ2, half_17_02_φ3, half_17_02_φ4, half_17_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_14_02) (half_16_02)
    (by simpa only [half_17_02_φ3, show (2:ℝ)*4=8 by norm_num] using half_17_02_hx3)
  exact h.weaken (by norm_num [half_17_02_φ1, half_17_02_φ2, half_17_02_φ3, half_17_02_φ4, half_17_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_02_hx1 : SourcePowerBound (powerBoxCross 8 16 2 half_17_02_φ1) (112070695813/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 16) (u := 14) (t := 17)
    (D := 2) (ψ := (1196135553/10000000000 : ℝ)) half_17_02_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_02_φ1, half_17_02_φ2, half_17_02_φ3, half_17_02_φ4, half_17_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_02_φ1, half_17_02_φ2, half_17_02_φ3, half_17_02_φ4, half_17_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_02_φ1, half_17_02_φ2, half_17_02_φ3, half_17_02_φ4, half_17_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_15_02) (chord_40)
    (by simpa only [half_17_02_φ2, show (2:ℝ)*2=4 by norm_num] using half_17_02_hx2)
  exact h.weaken (by norm_num [half_17_02_φ1, half_17_02_φ2, half_17_02_φ3, half_17_02_φ4, half_17_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_02 : AdmissibleExponent 8 34 (262165874849/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 15) (ψ := (1226596233/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_16_02)
    (by simpa only [half_17_02_φ1] using half_17_02_hx1)
  exact admissibleExponent_mono h (by norm_num [half_17_02_φ1, half_17_02_φ2, half_17_02_φ3, half_17_02_φ4, half_17_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem chord_42 : AdmissibleExponent 8 36 (282154637/10000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 36) (t := (1/2 : ℝ))
    (half_17_02) (half_19_01) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1 <;> norm_num

def half_18_02_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (247793761/2000000000 : ℝ)

def half_18_02_φ2 : Fin 2 → ℝ := Fin.snoc half_18_02_φ1 (1213313893/10000000000 : ℝ)

def half_18_02_φ3 : Fin 3 → ℝ := Fin.snoc half_18_02_φ2 (67390333/625000000 : ℝ)

def half_18_02_φ4 : Fin 4 → ℝ := Fin.snoc half_18_02_φ3 (924210281/10000000000 : ℝ)

def half_18_02_φ5 : Fin 5 → ℝ := Fin.snoc half_18_02_φ4 (792180241/10000000000 : ℝ)

theorem half_18_02_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_18_02_φ5) (14953677623/2500000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_18_02_φ5 (by norm_num [half_18_02_φ1, half_18_02_φ2, half_18_02_φ3, half_18_02_φ4, half_18_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_18_02_φ1, half_18_02_φ2, half_18_02_φ3, half_18_02_φ4, half_18_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_18_02_φ1, half_18_02_φ2, half_18_02_φ3, half_18_02_φ4, half_18_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_18_02_φ1, half_18_02_φ2, half_18_02_φ3, half_18_02_φ4, half_18_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_18_02_φ1, half_18_02_φ2, half_18_02_φ3, half_18_02_φ4, half_18_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_18_02_hx5 : SourcePowerBound (powerBoxCross 8 13 32 half_18_02_φ5) (110786064771/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 13) (r := 2) (v := 17) (w := 18) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_18_02_φ5 (by norm_num [half_18_02_φ1, half_18_02_φ2, half_18_02_φ3, half_18_02_φ4, half_18_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_18_02_φ1, half_18_02_φ2, half_18_02_φ3, half_18_02_φ4, half_18_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_18_02_hF2 (half_17_02) (chord_42)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_18_02_φ1, half_18_02_φ2, half_18_02_φ3, half_18_02_φ4, half_18_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_18_02_hx4 : SourcePowerBound (powerBoxCross 8 14 16 half_18_02_φ4) (131640917981/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 14) (u := 12) (t := 15)
    (D := 16) (ψ := (792180241/10000000000 : ℝ)) half_18_02_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_18_02_φ1, half_18_02_φ2, half_18_02_φ3, half_18_02_φ4, half_18_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_18_02_φ1, half_18_02_φ2, half_18_02_φ3, half_18_02_φ4, half_18_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_18_02_φ1, half_18_02_φ2, half_18_02_φ3, half_18_02_φ4, half_18_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_13_02) (half_15_02)
    (by simpa only [half_18_02_φ5, show (2:ℝ)*16=32 by norm_num] using half_18_02_hx5)
  exact h.weaken (by norm_num [half_18_02_φ1, half_18_02_φ2, half_18_02_φ3, half_18_02_φ4, half_18_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_18_02_hx3 : SourcePowerBound (powerBoxCross 8 15 8 half_18_02_φ3) (31888339673/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 15) (u := 13) (t := 16)
    (D := 8) (ψ := (924210281/10000000000 : ℝ)) half_18_02_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_18_02_φ1, half_18_02_φ2, half_18_02_φ3, half_18_02_φ4, half_18_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_18_02_φ1, half_18_02_φ2, half_18_02_φ3, half_18_02_φ4, half_18_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_18_02_φ1, half_18_02_φ2, half_18_02_φ3, half_18_02_φ4, half_18_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_14_02) (half_16_02)
    (by simpa only [half_18_02_φ4, show (2:ℝ)*8=16 by norm_num] using half_18_02_hx4)
  exact h.weaken (by norm_num [half_18_02_φ1, half_18_02_φ2, half_18_02_φ3, half_18_02_φ4, half_18_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_18_02_hx2 : SourcePowerBound (powerBoxCross 8 16 4 half_18_02_φ2) (48927528119/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 16) (u := 14) (t := 17)
    (D := 4) (ψ := (67390333/625000000 : ℝ)) half_18_02_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_18_02_φ1, half_18_02_φ2, half_18_02_φ3, half_18_02_φ4, half_18_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_18_02_φ1, half_18_02_φ2, half_18_02_φ3, half_18_02_φ4, half_18_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_18_02_φ1, half_18_02_φ2, half_18_02_φ3, half_18_02_φ4, half_18_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_15_02) (half_17_02)
    (by simpa only [half_18_02_φ3, show (2:ℝ)*4=8 by norm_num] using half_18_02_hx3)
  exact h.weaken (by norm_num [half_18_02_φ1, half_18_02_φ2, half_18_02_φ3, half_18_02_φ4, half_18_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_18_02_hx1 : SourcePowerBound (powerBoxCross 8 17 2 half_18_02_φ1) (240923309591/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 17) (u := 15) (t := 18)
    (D := 2) (ψ := (1213313893/10000000000 : ℝ)) half_18_02_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_18_02_φ1, half_18_02_φ2, half_18_02_φ3, half_18_02_φ4, half_18_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_18_02_φ1, half_18_02_φ2, half_18_02_φ3, half_18_02_φ4, half_18_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_18_02_φ1, half_18_02_φ2, half_18_02_φ3, half_18_02_φ4, half_18_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_16_02) (chord_42)
    (by simpa only [half_18_02_φ2, show (2:ℝ)*2=4 by norm_num] using half_18_02_hx2)
  exact h.weaken (by norm_num [half_18_02_φ1, half_18_02_φ2, half_18_02_φ3, half_18_02_φ4, half_18_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_18_02 : AdmissibleExponent 8 36 (70452320039/2500000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 16) (ψ := (247793761/2000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_17_02)
    (by simpa only [half_18_02_φ1] using half_18_02_hx1)
  exact admissibleExponent_mono h (by norm_num [half_18_02_φ1, half_18_02_φ2, half_18_02_φ3, half_18_02_φ4, half_18_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem chord_43 : AdmissibleExponent 8 38 (604103642713/20000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 38) (t := (1/2 : ℝ))
    (half_18_02) (half_20_01) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1 <;> norm_num

def half_19_02_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1/8 : ℝ)

def half_19_02_φ2 : Fin 2 → ℝ := Fin.snoc half_19_02_φ1 (1227654001/10000000000 : ℝ)

def half_19_02_φ3 : Fin 3 → ℝ := Fin.snoc half_19_02_φ2 (134327607/1250000000 : ℝ)

def half_19_02_φ4 : Fin 4 → ℝ := Fin.snoc half_19_02_φ3 (921103591/10000000000 : ℝ)

def half_19_02_φ5 : Fin 5 → ℝ := Fin.snoc half_19_02_φ4 (197379341/2500000000 : ℝ)

theorem half_19_02_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_19_02_φ5) (14869796987/2500000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_19_02_φ5 (by norm_num [half_19_02_φ1, half_19_02_φ2, half_19_02_φ3, half_19_02_φ4, half_19_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_19_02_φ1, half_19_02_φ2, half_19_02_φ3, half_19_02_φ4, half_19_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_19_02_φ1, half_19_02_φ2, half_19_02_φ3, half_19_02_φ4, half_19_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_19_02_φ1, half_19_02_φ2, half_19_02_φ3, half_19_02_φ4, half_19_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_19_02_φ1, half_19_02_φ2, half_19_02_φ3, half_19_02_φ4, half_19_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_19_02_hx5 : SourcePowerBound (powerBoxCross 8 14 32 half_19_02_φ5) (7486646401/625000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 14) (r := 2) (v := 18) (w := 19) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_19_02_φ5 (by norm_num [half_19_02_φ1, half_19_02_φ2, half_19_02_φ3, half_19_02_φ4, half_19_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_19_02_φ1, half_19_02_φ2, half_19_02_φ3, half_19_02_φ4, half_19_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_19_02_hF2 (half_18_02) (chord_43)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_19_02_φ1, half_19_02_φ2, half_19_02_φ3, half_19_02_φ4, half_19_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_19_02_hx4 : SourcePowerBound (powerBoxCross 8 15 16 half_19_02_φ4) (8872214639/625000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 15) (u := 13) (t := 16)
    (D := 16) (ψ := (197379341/2500000000 : ℝ)) half_19_02_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_19_02_φ1, half_19_02_φ2, half_19_02_φ3, half_19_02_φ4, half_19_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_19_02_φ1, half_19_02_φ2, half_19_02_φ3, half_19_02_φ4, half_19_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_19_02_φ1, half_19_02_φ2, half_19_02_φ3, half_19_02_φ4, half_19_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_14_02) (half_16_02)
    (by simpa only [half_19_02_φ5, show (2:ℝ)*16=32 by norm_num] using half_19_02_hx5)
  exact h.weaken (by norm_num [half_19_02_φ1, half_19_02_φ2, half_19_02_φ3, half_19_02_φ4, half_19_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_19_02_hx3 : SourcePowerBound (powerBoxCross 8 16 8 half_19_02_φ3) (21427429041/1250000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 16) (u := 14) (t := 17)
    (D := 8) (ψ := (921103591/10000000000 : ℝ)) half_19_02_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_19_02_φ1, half_19_02_φ2, half_19_02_φ3, half_19_02_φ4, half_19_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_19_02_φ1, half_19_02_φ2, half_19_02_φ3, half_19_02_φ4, half_19_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_19_02_φ1, half_19_02_φ2, half_19_02_φ3, half_19_02_φ4, half_19_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_15_02) (half_17_02)
    (by simpa only [half_19_02_φ4, show (2:ℝ)*8=16 by norm_num] using half_19_02_hx4)
  exact h.weaken (by norm_num [half_19_02_φ1, half_19_02_φ2, half_19_02_φ3, half_19_02_φ4, half_19_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_19_02_hx2 : SourcePowerBound (powerBoxCross 8 17 4 half_19_02_φ2) (104843947991/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 17) (u := 15) (t := 18)
    (D := 4) (ψ := (134327607/1250000000 : ℝ)) half_19_02_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_19_02_φ1, half_19_02_φ2, half_19_02_φ3, half_19_02_φ4, half_19_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_19_02_φ1, half_19_02_φ2, half_19_02_φ3, half_19_02_φ4, half_19_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_19_02_φ1, half_19_02_φ2, half_19_02_φ3, half_19_02_φ4, half_19_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_16_02) (half_18_02)
    (by simpa only [half_19_02_φ3, show (2:ℝ)*4=8 by norm_num] using half_19_02_hx3)
  exact h.weaken (by norm_num [half_19_02_φ1, half_19_02_φ2, half_19_02_φ3, half_19_02_φ4, half_19_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_19_02_hx1 : SourcePowerBound (powerBoxCross 8 18 2 half_19_02_φ1) (257872910851/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 18) (u := 16) (t := 19)
    (D := 2) (ψ := (1227654001/10000000000 : ℝ)) half_19_02_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_19_02_φ1, half_19_02_φ2, half_19_02_φ3, half_19_02_φ4, half_19_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_19_02_φ1, half_19_02_φ2, half_19_02_φ3, half_19_02_φ4, half_19_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_19_02_φ1, half_19_02_φ2, half_19_02_φ3, half_19_02_φ4, half_19_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_17_02) (chord_43)
    (by simpa only [half_19_02_φ2, show (2:ℝ)*2=4 by norm_num] using half_19_02_hx2)
  exact h.weaken (by norm_num [half_19_02_φ1, half_19_02_φ2, half_19_02_φ3, half_19_02_φ4, half_19_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_19_02 : AdmissibleExponent 8 38 (301622910851/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 17) (ψ := (1/8 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_18_02)
    (by simpa only [half_19_02_φ1] using half_19_02_hx1)
  exact admissibleExponent_mono h (by norm_num [half_19_02_φ1, half_19_02_φ2, half_19_02_φ3, half_19_02_φ4, half_19_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_20_02_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1/8 : ℝ)

def half_20_02_φ2 : Fin 2 → ℝ := Fin.snoc half_20_02_φ1 (1242589471/10000000000 : ℝ)

def half_20_02_φ3 : Fin 3 → ℝ := Fin.snoc half_20_02_φ2 (536243609/5000000000 : ℝ)

def half_20_02_φ4 : Fin 4 → ℝ := Fin.snoc half_20_02_φ3 (459637379/5000000000 : ℝ)

def half_20_02_φ5 : Fin 5 → ℝ := Fin.snoc half_20_02_φ4 (787949793/10000000000 : ℝ)

theorem half_20_02_hF2 : SourcePowerBound (paddedMoment 8 0 2 32 half_20_02_φ5) (1482041849/250000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_20_02_φ5 (by norm_num [half_20_02_φ1, half_20_02_φ2, half_20_02_φ3, half_20_02_φ4, half_20_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_20_02_φ1, half_20_02_φ2, half_20_02_φ3, half_20_02_φ4, half_20_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_20_02_φ1, half_20_02_φ2, half_20_02_φ3, half_20_02_φ4, half_20_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_20_02_φ1, half_20_02_φ2, half_20_02_φ3, half_20_02_φ4, half_20_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_20_02_φ1, half_20_02_φ2, half_20_02_φ3, half_20_02_φ4, half_20_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_20_02_hx5 : SourcePowerBound (powerBoxCross 8 15 32 half_20_02_φ5) (129098717857/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 15) (r := 2) (v := 0) (w := 20) (D := 32)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_20_02_φ5 (by norm_num [half_20_02_φ1, half_20_02_φ2, half_20_02_φ3, half_20_02_φ4, half_20_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_20_02_φ1, half_20_02_φ2, half_20_02_φ3, half_20_02_φ4, half_20_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_20_02_hF2 (admissibleExponent_zero 8) (half_20_01)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_20_02_φ1, half_20_02_φ2, half_20_02_φ3, half_20_02_φ4, half_20_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_20_02_hx4 : SourcePowerBound (powerBoxCross 8 16 16 half_20_02_φ4) (38145035569/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 4) (s := 16) (u := 14) (t := 17)
    (D := 16) (ψ := (787949793/10000000000 : ℝ)) half_20_02_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_20_02_φ1, half_20_02_φ2, half_20_02_φ3, half_20_02_φ4, half_20_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_20_02_φ1, half_20_02_φ2, half_20_02_φ3, half_20_02_φ4, half_20_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_20_02_φ1, half_20_02_φ2, half_20_02_φ3, half_20_02_φ4, half_20_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_15_02) (half_17_02)
    (by simpa only [half_20_02_φ5, show (2:ℝ)*16=32 by norm_num] using half_20_02_hx5)
  exact h.weaken (by norm_num [half_20_02_φ1, half_20_02_φ2, half_20_02_φ3, half_20_02_φ4, half_20_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_20_02_hx3 : SourcePowerBound (powerBoxCross 8 17 8 half_20_02_φ3) (183732116783/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 17) (u := 15) (t := 18)
    (D := 8) (ψ := (459637379/5000000000 : ℝ)) half_20_02_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_20_02_φ1, half_20_02_φ2, half_20_02_φ3, half_20_02_φ4, half_20_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_20_02_φ1, half_20_02_φ2, half_20_02_φ3, half_20_02_φ4, half_20_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_20_02_φ1, half_20_02_φ2, half_20_02_φ3, half_20_02_φ4, half_20_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_16_02) (half_18_02)
    (by simpa only [half_20_02_φ4, show (2:ℝ)*8=16 by norm_num] using half_20_02_hx4)
  exact h.weaken (by norm_num [half_20_02_φ1, half_20_02_φ2, half_20_02_φ3, half_20_02_φ4, half_20_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_20_02_hx2 : SourcePowerBound (powerBoxCross 8 18 4 half_20_02_φ2) (28007298147/1250000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 18) (u := 16) (t := 19)
    (D := 4) (ψ := (536243609/5000000000 : ℝ)) half_20_02_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_20_02_φ1, half_20_02_φ2, half_20_02_φ3, half_20_02_φ4, half_20_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_20_02_φ1, half_20_02_φ2, half_20_02_φ3, half_20_02_φ4, half_20_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_20_02_φ1, half_20_02_φ2, half_20_02_φ3, half_20_02_φ4, half_20_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_17_02) (half_19_02)
    (by simpa only [half_20_02_φ3, show (2:ℝ)*4=8 by norm_num] using half_20_02_hx3)
  exact h.weaken (by norm_num [half_20_02_φ1, half_20_02_φ2, half_20_02_φ3, half_20_02_φ4, half_20_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_20_02_hx1 : SourcePowerBound (powerBoxCross 8 19 2 half_20_02_φ1) (5508065839/200000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 19) (u := 17) (t := 20)
    (D := 2) (ψ := (1242589471/10000000000 : ℝ)) half_20_02_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_20_02_φ1, half_20_02_φ2, half_20_02_φ3, half_20_02_φ4, half_20_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_20_02_φ1, half_20_02_φ2, half_20_02_φ3, half_20_02_φ4, half_20_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_20_02_φ1, half_20_02_φ2, half_20_02_φ3, half_20_02_φ4, half_20_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (half_18_02) (half_20_01)
    (by simpa only [half_20_02_φ2, show (2:ℝ)*2=4 by norm_num] using half_20_02_hx2)
  exact h.weaken (by norm_num [half_20_02_φ1, half_20_02_φ2, half_20_02_φ3, half_20_02_φ4, half_20_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_20_02 : AdmissibleExponent 8 40 (6433065839/200000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 18) (ψ := (1/8 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_19_02)
    (by simpa only [half_20_02_φ1] using half_20_02_hx1)
  exact admissibleExponent_mono h (by norm_num [half_20_02_φ1, half_20_02_φ2, half_20_02_φ3, half_20_02_φ4, half_20_02_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_10_03_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1042307247/10000000000 : ℝ)

def half_10_03_φ2 : Fin 2 → ℝ := Fin.snoc half_10_03_φ1 (1201961/12500000 : ℝ)

def half_10_03_φ3 : Fin 3 → ℝ := Fin.snoc half_10_03_φ2 (837191737/10000000000 : ℝ)

def half_10_03_φ4 : Fin 4 → ℝ := Fin.snoc half_10_03_φ3 (275538571/5000000000 : ℝ)

theorem half_10_03_hF2 : SourcePowerBound (paddedMoment 8 0 2 16 half_10_03_φ4) (34382478277/5000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 4) (r := 0) (n := 1) (D := 16)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_10_03_φ4 (by norm_num [half_10_03_φ1, half_10_03_φ2, half_10_03_φ3, half_10_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_03_φ1, half_10_03_φ2, half_10_03_φ3, half_10_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_03_φ1, half_10_03_φ2, half_10_03_φ3, half_10_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_10_03_φ1, half_10_03_φ2, half_10_03_φ3, half_10_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_10_03_φ1, half_10_03_φ2, half_10_03_φ3, half_10_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_10_03_hx4 : SourcePowerBound (powerBoxCross 8 6 16 half_10_03_φ4) (65971393689/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 6) (r := 2) (v := 0) (w := 8) (D := 16)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_10_03_φ4 (by norm_num [half_10_03_φ1, half_10_03_φ2, half_10_03_φ3, half_10_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_03_φ1, half_10_03_φ2, half_10_03_φ3, half_10_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_10_03_hF2 (admissibleExponent_zero 8) (SeedCompletionHigher8SimpleSeeds.degree8_half_8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_10_03_φ1, half_10_03_φ2, half_10_03_φ3, half_10_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_03_hx3 : SourcePowerBound (powerBoxCross 8 7 8 half_10_03_φ3) (9538134383/1250000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 7) (u := 5) (t := 8)
    (D := 8) (ψ := (275538571/5000000000 : ℝ)) half_10_03_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_03_φ1, half_10_03_φ2, half_10_03_φ3, half_10_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_03_φ1, half_10_03_φ2, half_10_03_φ3, half_10_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_03_φ1, half_10_03_φ2, half_10_03_φ3, half_10_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionEven8SecondSeeds.degree8_half_6) (SeedCompletionHigher8SimpleSeeds.degree8_half_8)
    (by simpa only [half_10_03_φ4, show (2:ℝ)*8=16 by norm_num] using half_10_03_hx4)
  exact h.weaken (by norm_num [half_10_03_φ1, half_10_03_φ2, half_10_03_φ3, half_10_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_03_hx2 : SourcePowerBound (powerBoxCross 8 8 4 half_10_03_φ2) (23092540809/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 8) (u := 6) (t := 9)
    (D := 4) (ψ := (837191737/10000000000 : ℝ)) half_10_03_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_03_φ1, half_10_03_φ2, half_10_03_φ3, half_10_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_03_φ1, half_10_03_φ2, half_10_03_φ3, half_10_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_03_φ1, half_10_03_φ2, half_10_03_φ3, half_10_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_7) (SeedCompletionHigher8SimpleSeeds.degree8_half_9)
    (by simpa only [half_10_03_φ3, show (2:ℝ)*4=8 by norm_num] using half_10_03_hx3)
  exact h.weaken (by norm_num [half_10_03_φ1, half_10_03_φ2, half_10_03_φ3, half_10_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_03_hx1 : SourcePowerBound (powerBoxCross 8 9 2 half_10_03_φ1) (113633959717/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 9) (u := 7) (t := 10)
    (D := 2) (ψ := (1201961/12500000 : ℝ)) half_10_03_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_03_φ1, half_10_03_φ2, half_10_03_φ3, half_10_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_03_φ1, half_10_03_φ2, half_10_03_φ3, half_10_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_03_φ1, half_10_03_φ2, half_10_03_φ3, half_10_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_8) (half_10_02)
    (by simpa only [half_10_03_φ2, show (2:ℝ)*2=4 by norm_num] using half_10_03_hx2)
  exact h.weaken (by norm_num [half_10_03_φ1, half_10_03_φ2, half_10_03_φ3, half_10_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_03 : AdmissibleExponent 8 20 (32838295729/2500000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 8) (ψ := (1042307247/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_9)
    (by simpa only [half_10_03_φ1] using half_10_03_hx1)
  exact admissibleExponent_mono h (by norm_num [half_10_03_φ1, half_10_03_φ2, half_10_03_φ3, half_10_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_11_03_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (272633781/2500000000 : ℝ)

def half_11_03_φ2 : Fin 2 → ℝ := Fin.snoc half_11_03_φ1 (508121181/5000000000 : ℝ)

def half_11_03_φ3 : Fin 3 → ℝ := Fin.snoc half_11_03_φ2 (923924021/10000000000 : ℝ)

def half_11_03_φ4 : Fin 4 → ℝ := Fin.snoc half_11_03_φ3 (372682029/5000000000 : ℝ)

theorem half_11_03_hF2 : SourcePowerBound (paddedMoment 8 0 2 16 half_11_03_φ4) (12140524627/2000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 8) (j := 4) (r := 0) (n := 1) (D := 16)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_11_03_φ4 (by norm_num [half_11_03_φ1, half_11_03_φ2, half_11_03_φ3, half_11_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_03_φ1, half_11_03_φ2, half_11_03_φ3, half_11_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_03_φ1, half_11_03_φ2, half_11_03_φ3, half_11_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by
      unfold PrefixCondition
      intro i hi
      interval_cases i <;> norm_num [phiExtend, Finset.sum_range_succ, half_11_03_φ1, half_11_03_φ2, half_11_03_φ3, half_11_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [dyadicExponent, half_11_03_φ1, half_11_03_φ2, half_11_03_φ3, half_11_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_11_03_hx4 : SourcePowerBound (powerBoxCross 8 7 16 half_11_03_φ4) (71255077441/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 7) (r := 2) (v := 9) (w := 10) (D := 16)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_11_03_φ4 (by norm_num [half_11_03_φ1, half_11_03_φ2, half_11_03_φ3, half_11_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_03_φ1, half_11_03_φ2, half_11_03_φ3, half_11_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_11_03_hF2 (SeedCompletionHigher8SimpleSeeds.degree8_half_9) (half_10_03)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_11_03_φ1, half_11_03_φ2, half_11_03_φ3, half_11_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_03_hx3 : SourcePowerBound (powerBoxCross 8 8 8 half_11_03_φ3) (2649197669/312500000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 3) (s := 8) (u := 6) (t := 9)
    (D := 8) (ψ := (372682029/5000000000 : ℝ)) half_11_03_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_03_φ1, half_11_03_φ2, half_11_03_φ3, half_11_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_03_φ1, half_11_03_φ2, half_11_03_φ3, half_11_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_03_φ1, half_11_03_φ2, half_11_03_φ3, half_11_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_7) (SeedCompletionHigher8SimpleSeeds.degree8_half_9)
    (by simpa only [half_11_03_φ4, show (2:ℝ)*8=16 by norm_num] using half_11_03_hx4)
  exact h.weaken (by norm_num [half_11_03_φ1, half_11_03_φ2, half_11_03_φ3, half_11_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_03_hx2 : SourcePowerBound (powerBoxCross 8 9 4 half_11_03_φ2) (20756573339/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 9) (u := 7) (t := 10)
    (D := 4) (ψ := (923924021/10000000000 : ℝ)) half_11_03_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_03_φ1, half_11_03_φ2, half_11_03_φ3, half_11_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_03_φ1, half_11_03_φ2, half_11_03_φ3, half_11_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_03_φ1, half_11_03_φ2, half_11_03_φ3, half_11_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_8) (half_10_03)
    (by simpa only [half_11_03_φ3, show (2:ℝ)*4=8 by norm_num] using half_11_03_hx3)
  exact h.weaken (by norm_num [half_11_03_φ1, half_11_03_φ2, half_11_03_φ3, half_11_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_03_hx1 : SourcePowerBound (powerBoxCross 8 10 2 half_11_03_φ1) (128119192083/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 10) (u := 8) (t := 11)
    (D := 2) (ψ := (508121181/5000000000 : ℝ)) half_11_03_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_03_φ1, half_11_03_φ2, half_11_03_φ3, half_11_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_03_φ1, half_11_03_φ2, half_11_03_φ3, half_11_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_03_φ1, half_11_03_φ2, half_11_03_φ3, half_11_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) (SeedCompletionHigher8SimpleSeeds.degree8_half_9) (half_11_02)
    (by simpa only [half_11_03_φ2, show (2:ℝ)*2=4 by norm_num] using half_11_03_hx2)
  exact h.weaken (by norm_num [half_11_03_φ1, half_11_03_φ2, half_11_03_φ3, half_11_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_03 : AdmissibleExponent 8 22 (148839359439/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 9) (ψ := (272633781/2500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_10_03)
    (by simpa only [half_11_03_φ1] using half_11_03_hx1)
  exact admissibleExponent_mono h (by norm_num [half_11_03_φ1, half_11_03_φ2, half_11_03_φ3, half_11_03_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_12_03_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (561271641/5000000000 : ℝ)

def half_12_03_φ2 : Fin 2 → ℝ := Fin.snoc half_12_03_φ1 (1058601939/10000000000 : ℝ)

def half_12_03_φ3 : Fin 3 → ℝ := Fin.snoc half_12_03_φ2 (980580219/10000000000 : ℝ)

end Waring.SeedCompletionAlternate8Seeds
