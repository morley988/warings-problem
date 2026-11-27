import Waring.SeedCompletionAlternate9Steps05

noncomputable section
set_option maxHeartbeats 2000000
namespace Waring.SeedCompletionAlternate9Seeds
open SmoothMoments FirstStageTransport SeedCompletionNaturalBox
open SeedCompletionSourceBounds SeedCompletionPaddedSource SeedCompletionGeneralTerminal
open PolicyCompletionMajorPowerRanges SeedCompletionDivisorPowerScales
open PolicyCompletionSharpResidualSource

private def half_18_05_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (267979699/2500000000 : ℝ)

private theorem half_18_05_total1 : total half_18_05_φ1=(267979699/2500000000 : ℝ) := by
  norm_num [half_18_05_φ1,total,emptyPhi,Fin.snoc]

private theorem half_18_05_bounds1 : ∀ l,0≤half_18_05_φ1 l ∧ half_18_05_φ1 l≤1 ∧
    0≤shiftExponents 9 half_18_05_φ1 l :=
  alternate_bounds_snoc emptyPhi (267979699/2500000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_18_05_φ2 : Fin 2 → ℝ := Fin.snoc half_18_05_φ1 (526193977/5000000000 : ℝ)

private theorem half_18_05_total2 : total half_18_05_φ2=(8497227/40000000 : ℝ) := by
  change total (Fin.snoc half_18_05_φ1 (526193977/5000000000 : ℝ))=(8497227/40000000 : ℝ)
  rw [alternate_total_snoc,half_18_05_total1]
  norm_num

private theorem half_18_05_bounds2 : ∀ l,0≤half_18_05_φ2 l ∧ half_18_05_φ2 l≤1 ∧
    0≤shiftExponents 9 half_18_05_φ2 l :=
  alternate_bounds_snoc half_18_05_φ1 (526193977/5000000000 : ℝ) half_18_05_bounds1 (by norm_num)

private def half_18_05_φ3 : Fin 3 → ℝ := Fin.snoc half_18_05_φ2 (123057707/1250000000 : ℝ)

private theorem half_18_05_total3 : total half_18_05_φ3=(1554384203/5000000000 : ℝ) := by
  change total (Fin.snoc half_18_05_φ2 (123057707/1250000000 : ℝ))=(1554384203/5000000000 : ℝ)
  rw [alternate_total_snoc,half_18_05_total2]
  norm_num

private theorem half_18_05_bounds3 : ∀ l,0≤half_18_05_φ3 l ∧ half_18_05_φ3 l≤1 ∧
    0≤shiftExponents 9 half_18_05_φ3 l :=
  alternate_bounds_snoc half_18_05_φ2 (123057707/1250000000 : ℝ) half_18_05_bounds2 (by norm_num)

private def half_18_05_φ4 : Fin 4 → ℝ := Fin.snoc half_18_05_φ3 (861403949/10000000000 : ℝ)

private theorem half_18_05_total4 : total half_18_05_φ4=(794034471/2000000000 : ℝ) := by
  change total (Fin.snoc half_18_05_φ3 (861403949/10000000000 : ℝ))=(794034471/2000000000 : ℝ)
  rw [alternate_total_snoc,half_18_05_total3]
  norm_num

private theorem half_18_05_bounds4 : ∀ l,0≤half_18_05_φ4 l ∧ half_18_05_φ4 l≤1 ∧
    0≤shiftExponents 9 half_18_05_φ4 l :=
  alternate_bounds_snoc half_18_05_φ3 (861403949/10000000000 : ℝ) half_18_05_bounds3 (by norm_num)

private def half_18_05_φ5 : Fin 5 → ℝ := Fin.snoc half_18_05_φ4 (150745691/2000000000 : ℝ)

private theorem half_18_05_total5 : total half_18_05_φ5=(472390081/1000000000 : ℝ) := by
  change total (Fin.snoc half_18_05_φ4 (150745691/2000000000 : ℝ))=(472390081/1000000000 : ℝ)
  rw [alternate_total_snoc,half_18_05_total4]
  norm_num

private theorem half_18_05_bounds5 : ∀ l,0≤half_18_05_φ5 l ∧ half_18_05_φ5 l≤1 ∧
    0≤shiftExponents 9 half_18_05_φ5 l :=
  alternate_bounds_snoc half_18_05_φ4 (150745691/2000000000 : ℝ) half_18_05_bounds4 (by norm_num)

private def half_18_05_φ6 : Fin 6 → ℝ := Fin.snoc half_18_05_φ5 (329756199/5000000000 : ℝ)

private theorem half_18_05_total6 : total half_18_05_φ6=(672926651/1250000000 : ℝ) := by
  change total (Fin.snoc half_18_05_φ5 (329756199/5000000000 : ℝ))=(672926651/1250000000 : ℝ)
  rw [alternate_total_snoc,half_18_05_total5]
  norm_num

private theorem half_18_05_bounds6 : ∀ l,0≤half_18_05_φ6 l ∧ half_18_05_φ6 l≤1 ∧
    0≤shiftExponents 9 half_18_05_φ6 l :=
  alternate_bounds_snoc half_18_05_φ5 (329756199/5000000000 : ℝ) half_18_05_bounds5 (by norm_num)

private theorem half_18_05_prefix : PrefixCondition 9 half_18_05_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_18_05_φ1, half_18_05_φ2, half_18_05_φ3, half_18_05_φ4, half_18_05_φ5, half_18_05_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_18_05_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_18_05_φ6) (1106220047/156250000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_18_05_φ6
    (fun i => (half_18_05_bounds6 i).1) (fun i => (half_18_05_bounds6 i).2.1)
    (fun i => (half_18_05_bounds6 i).2.2) half_18_05_prefix
  convert h using 1 <;> norm_num [half_18_05_total1, half_18_05_total2, half_18_05_total3, half_18_05_total4, half_18_05_total5, half_18_05_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_18_05_hx6 : SourcePowerBound
    (powerBoxCross 9 12 64 half_18_05_φ6) (98890548277/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 12) (r := 2) (v := 0) (w := 16) (D := 64)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_18_05_φ6 (by norm_num [half_18_05_total1, half_18_05_total2, half_18_05_total3, half_18_05_total4, half_18_05_total5, half_18_05_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_18_05_total1, half_18_05_total2, half_18_05_total3, half_18_05_total4, half_18_05_total5, half_18_05_total6, parameterExponent, curveLoss, dyadicExponent]) half_18_05_hF2
    (admissibleExponent_zero 9) (half_16_05)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_18_05_total1, half_18_05_total2, half_18_05_total3, half_18_05_total4, half_18_05_total5, half_18_05_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_18_05_hx5 : SourcePowerBound
    (powerBoxCross 9 13 32 half_18_05_φ5) (115155201709/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 13) (u := 11) (t := 14)
    (D := 32) (ψ := (329756199/5000000000 : ℝ)) half_18_05_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_18_05_bounds5 l).1) (fun l => (half_18_05_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_18_05_total1, half_18_05_total2, half_18_05_total3, half_18_05_total4, half_18_05_total5, half_18_05_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_12_05) (half_14_05)
    (by simpa only [half_18_05_φ6, show (2:ℝ)*32=64 by norm_num] using half_18_05_hx6)
  exact h.weaken (by norm_num [half_18_05_total1, half_18_05_total2, half_18_05_total3, half_18_05_total4, half_18_05_total5, half_18_05_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_18_05_hx4 : SourcePowerBound
    (powerBoxCross 9 14 16 half_18_05_φ4) (17018248977/1250000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 14) (u := 12) (t := 15)
    (D := 16) (ψ := (150745691/2000000000 : ℝ)) half_18_05_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_18_05_bounds4 l).1) (fun l => (half_18_05_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_18_05_total1, half_18_05_total2, half_18_05_total3, half_18_05_total4, half_18_05_total5, half_18_05_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_13_05) (half_15_05)
    (by simpa only [half_18_05_φ5, show (2:ℝ)*16=32 by norm_num] using half_18_05_hx5)
  exact h.weaken (by norm_num [half_18_05_total1, half_18_05_total2, half_18_05_total3, half_18_05_total4, half_18_05_total5, half_18_05_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_18_05_hx3 : SourcePowerBound
    (powerBoxCross 9 15 8 half_18_05_φ3) (16306338887/1000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 15) (u := 13) (t := 16)
    (D := 8) (ψ := (861403949/10000000000 : ℝ)) half_18_05_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_18_05_bounds3 l).1) (fun l => (half_18_05_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_18_05_total1, half_18_05_total2, half_18_05_total3, half_18_05_total4, half_18_05_total5, half_18_05_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_14_05) (half_16_05)
    (by simpa only [half_18_05_φ4, show (2:ℝ)*8=16 by norm_num] using half_18_05_hx4)
  exact h.weaken (by norm_num [half_18_05_total1, half_18_05_total2, half_18_05_total3, half_18_05_total4, half_18_05_total5, half_18_05_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_18_05_hx2 : SourcePowerBound
    (powerBoxCross 9 16 4 half_18_05_φ2) (98577391107/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 16) (u := 14) (t := 17)
    (D := 4) (ψ := (123057707/1250000000 : ℝ)) half_18_05_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_18_05_bounds2 l).1) (fun l => (half_18_05_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_18_05_total1, half_18_05_total2, half_18_05_total3, half_18_05_total4, half_18_05_total5, half_18_05_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_15_05) (half_17_05)
    (by simpa only [half_18_05_φ3, show (2:ℝ)*4=8 by norm_num] using half_18_05_hx3)
  exact h.weaken (by norm_num [half_18_05_total1, half_18_05_total2, half_18_05_total3, half_18_05_total4, half_18_05_total5, half_18_05_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_18_05_hx1 : SourcePowerBound
    (powerBoxCross 9 17 2 half_18_05_φ1) (237446863021/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 17) (u := 15) (t := 18)
    (D := 2) (ψ := (526193977/5000000000 : ℝ)) half_18_05_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_18_05_bounds1 l).1) (fun l => (half_18_05_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_18_05_total1, half_18_05_total2, half_18_05_total3, half_18_05_total4, half_18_05_total5, half_18_05_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_16_05) (half_18_04)
    (by simpa only [half_18_05_φ2, show (2:ℝ)*2=4 by norm_num] using half_18_05_hx2)
  exact h.weaken (by norm_num [half_18_05_total1, half_18_05_total2, half_18_05_total3, half_18_05_total4, half_18_05_total5, half_18_05_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_18_05 : AdmissibleExponent 9 36 (272820183289/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 16) (ψ := (267979699/2500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_17_05)
    (by simpa only [half_18_05_φ1] using half_18_05_hx1)
  exact admissibleExponent_mono h (by norm_num [half_18_05_total1, half_18_05_total2, half_18_05_total3, half_18_05_total4, half_18_05_total5, half_18_05_total6, parameterExponent, curveLoss, dyadicExponent])

private def half_19_05_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (54086617/500000000 : ℝ)

private theorem half_19_05_total1 : total half_19_05_φ1=(54086617/500000000 : ℝ) := by
  norm_num [half_19_05_φ1,total,emptyPhi,Fin.snoc]

private theorem half_19_05_bounds1 : ∀ l,0≤half_19_05_φ1 l ∧ half_19_05_φ1 l≤1 ∧
    0≤shiftExponents 9 half_19_05_φ1 l :=
  alternate_bounds_snoc emptyPhi (54086617/500000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_19_05_φ2 : Fin 2 → ℝ := Fin.snoc half_19_05_φ1 (1066093413/10000000000 : ℝ)

private theorem half_19_05_total2 : total half_19_05_φ2=(2147825753/10000000000 : ℝ) := by
  change total (Fin.snoc half_19_05_φ1 (1066093413/10000000000 : ℝ))=(2147825753/10000000000 : ℝ)
  rw [alternate_total_snoc,half_19_05_total1]
  norm_num

private theorem half_19_05_bounds2 : ∀ l,0≤half_19_05_φ2 l ∧ half_19_05_φ2 l≤1 ∧
    0≤shiftExponents 9 half_19_05_φ2 l :=
  alternate_bounds_snoc half_19_05_φ1 (1066093413/10000000000 : ℝ) half_19_05_bounds1 (by norm_num)

private def half_19_05_φ3 : Fin 3 → ℝ := Fin.snoc half_19_05_φ2 (49076089/500000000 : ℝ)

private theorem half_19_05_total3 : total half_19_05_φ3=(3129347533/10000000000 : ℝ) := by
  change total (Fin.snoc half_19_05_φ2 (49076089/500000000 : ℝ))=(3129347533/10000000000 : ℝ)
  rw [alternate_total_snoc,half_19_05_total2]
  norm_num

private theorem half_19_05_bounds3 : ∀ l,0≤half_19_05_φ3 l ∧ half_19_05_φ3 l≤1 ∧
    0≤shiftExponents 9 half_19_05_φ3 l :=
  alternate_bounds_snoc half_19_05_φ2 (49076089/500000000 : ℝ) half_19_05_bounds2 (by norm_num)

private def half_19_05_φ4 : Fin 4 → ℝ := Fin.snoc half_19_05_φ3 (429415779/5000000000 : ℝ)

private theorem half_19_05_total4 : total half_19_05_φ4=(3988179091/10000000000 : ℝ) := by
  change total (Fin.snoc half_19_05_φ3 (429415779/5000000000 : ℝ))=(3988179091/10000000000 : ℝ)
  rw [alternate_total_snoc,half_19_05_total3]
  norm_num

private theorem half_19_05_bounds4 : ∀ l,0≤half_19_05_φ4 l ∧ half_19_05_φ4 l≤1 ∧
    0≤shiftExponents 9 half_19_05_φ4 l :=
  alternate_bounds_snoc half_19_05_φ3 (429415779/5000000000 : ℝ) half_19_05_bounds3 (by norm_num)

private def half_19_05_φ5 : Fin 5 → ℝ := Fin.snoc half_19_05_φ4 (751477613/10000000000 : ℝ)

private theorem half_19_05_total5 : total half_19_05_φ5=(4628571/9765625 : ℝ) := by
  change total (Fin.snoc half_19_05_φ4 (751477613/10000000000 : ℝ))=(4628571/9765625 : ℝ)
  rw [alternate_total_snoc,half_19_05_total4]
  norm_num

private theorem half_19_05_bounds5 : ∀ l,0≤half_19_05_φ5 l ∧ half_19_05_φ5 l≤1 ∧
    0≤shiftExponents 9 half_19_05_φ5 l :=
  alternate_bounds_snoc half_19_05_φ4 (751477613/10000000000 : ℝ) half_19_05_bounds4 (by norm_num)

private def half_19_05_φ6 : Fin 6 → ℝ := Fin.snoc half_19_05_φ5 (657542911/10000000000 : ℝ)

private theorem half_19_05_total6 : total half_19_05_φ6=(1079439923/2000000000 : ℝ) := by
  change total (Fin.snoc half_19_05_φ5 (657542911/10000000000 : ℝ))=(1079439923/2000000000 : ℝ)
  rw [alternate_total_snoc,half_19_05_total5]
  norm_num

private theorem half_19_05_bounds6 : ∀ l,0≤half_19_05_φ6 l ∧ half_19_05_φ6 l≤1 ∧
    0≤shiftExponents 9 half_19_05_φ6 l :=
  alternate_bounds_snoc half_19_05_φ5 (657542911/10000000000 : ℝ) half_19_05_bounds5 (by norm_num)

private theorem half_19_05_prefix : PrefixCondition 9 half_19_05_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_19_05_φ1, half_19_05_φ2, half_19_05_φ3, half_19_05_φ4, half_19_05_φ5, half_19_05_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_19_05_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_19_05_φ6) (1761680231/250000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_19_05_φ6
    (fun i => (half_19_05_bounds6 i).1) (fun i => (half_19_05_bounds6 i).2.1)
    (fun i => (half_19_05_bounds6 i).2.2) half_19_05_prefix
  convert h using 1 <;> norm_num [half_19_05_total1, half_19_05_total2, half_19_05_total3, half_19_05_total4, half_19_05_total5, half_19_05_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_19_05_hx6 : SourcePowerBound
    (powerBoxCross 9 13 64 half_19_05_φ6) (26840778351/2500000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 13) (r := 2) (v := 17) (w := 18) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_19_05_φ6 (by norm_num [half_19_05_total1, half_19_05_total2, half_19_05_total3, half_19_05_total4, half_19_05_total5, half_19_05_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_19_05_total1, half_19_05_total2, half_19_05_total3, half_19_05_total4, half_19_05_total5, half_19_05_total6, parameterExponent, curveLoss, dyadicExponent]) half_19_05_hF2
    (half_17_05) (half_18_05)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_19_05_total1, half_19_05_total2, half_19_05_total3, half_19_05_total4, half_19_05_total5, half_19_05_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_19_05_hx5 : SourcePowerBound
    (powerBoxCross 9 14 32 half_19_05_φ5) (62335670169/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 14) (u := 12) (t := 15)
    (D := 32) (ψ := (657542911/10000000000 : ℝ)) half_19_05_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_19_05_bounds5 l).1) (fun l => (half_19_05_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_19_05_total1, half_19_05_total2, half_19_05_total3, half_19_05_total4, half_19_05_total5, half_19_05_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_13_05) (half_15_05)
    (by simpa only [half_19_05_φ6, show (2:ℝ)*32=64 by norm_num] using half_19_05_hx6)
  exact h.weaken (by norm_num [half_19_05_total1, half_19_05_total2, half_19_05_total3, half_19_05_total4, half_19_05_total5, half_19_05_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_19_05_hx4 : SourcePowerBound
    (powerBoxCross 9 15 16 half_19_05_φ4) (147013730021/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 15) (u := 13) (t := 16)
    (D := 16) (ψ := (751477613/10000000000 : ℝ)) half_19_05_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_19_05_bounds4 l).1) (fun l => (half_19_05_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_19_05_total1, half_19_05_total2, half_19_05_total3, half_19_05_total4, half_19_05_total5, half_19_05_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_14_05) (half_16_05)
    (by simpa only [half_19_05_φ5, show (2:ℝ)*16=32 by norm_num] using half_19_05_hx5)
  exact h.weaken (by norm_num [half_19_05_total1, half_19_05_total2, half_19_05_total3, half_19_05_total4, half_19_05_total5, half_19_05_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_19_05_hx3 : SourcePowerBound
    (powerBoxCross 9 16 8 half_19_05_φ3) (175546554791/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 16) (u := 14) (t := 17)
    (D := 8) (ψ := (429415779/5000000000 : ℝ)) half_19_05_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_19_05_bounds3 l).1) (fun l => (half_19_05_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_19_05_total1, half_19_05_total2, half_19_05_total3, half_19_05_total4, half_19_05_total5, half_19_05_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_15_05) (half_17_05)
    (by simpa only [half_19_05_φ4, show (2:ℝ)*8=16 by norm_num] using half_19_05_hx4)
  exact h.weaken (by norm_num [half_19_05_total1, half_19_05_total2, half_19_05_total3, half_19_05_total4, half_19_05_total5, half_19_05_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_19_05_hx2 : SourcePowerBound
    (powerBoxCross 9 17 4 half_19_05_φ2) (105753571419/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 17) (u := 15) (t := 18)
    (D := 4) (ψ := (49076089/500000000 : ℝ)) half_19_05_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_19_05_bounds2 l).1) (fun l => (half_19_05_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_19_05_total1, half_19_05_total2, half_19_05_total3, half_19_05_total4, half_19_05_total5, half_19_05_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_16_05) (half_18_05)
    (by simpa only [half_19_05_φ3, show (2:ℝ)*4=8 by norm_num] using half_19_05_hx3)
  exact h.weaken (by norm_num [half_19_05_total1, half_19_05_total2, half_19_05_total3, half_19_05_total4, half_19_05_total5, half_19_05_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_19_05_hx1 : SourcePowerBound
    (powerBoxCross 9 18 2 half_19_05_φ1) (993711227/39062500 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 18) (u := 16) (t := 19)
    (D := 2) (ψ := (1066093413/10000000000 : ℝ)) half_19_05_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_19_05_bounds1 l).1) (fun l => (half_19_05_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_19_05_total1, half_19_05_total2, half_19_05_total3, half_19_05_total4, half_19_05_total5, half_19_05_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_17_05) (half_19_04)
    (by simpa only [half_19_05_φ2, show (2:ℝ)*2=4 by norm_num] using half_19_05_hx2)
  exact h.weaken (by norm_num [half_19_05_total1, half_19_05_total2, half_19_05_total3, half_19_05_total4, half_19_05_total5, half_19_05_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_19_05 : AdmissibleExponent 9 38 (73062676503/2500000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 17) (ψ := (54086617/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_18_05)
    (by simpa only [half_19_05_φ1] using half_19_05_hx1)
  exact admissibleExponent_mono h (by norm_num [half_19_05_total1, half_19_05_total2, half_19_05_total3, half_19_05_total4, half_19_05_total5, half_19_05_total6, parameterExponent, curveLoss, dyadicExponent])

private def half_20_05_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (217992399/2000000000 : ℝ)

private theorem half_20_05_total1 : total half_20_05_φ1=(217992399/2000000000 : ℝ) := by
  norm_num [half_20_05_φ1,total,emptyPhi,Fin.snoc]

private theorem half_20_05_bounds1 : ∀ l,0≤half_20_05_φ1 l ∧ half_20_05_φ1 l≤1 ∧
    0≤shiftExponents 9 half_20_05_φ1 l :=
  alternate_bounds_snoc emptyPhi (217992399/2000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_20_05_φ2 : Fin 2 → ℝ := Fin.snoc half_20_05_φ1 (269267687/2500000000 : ℝ)

private theorem half_20_05_total2 : total half_20_05_φ2=(2167032743/10000000000 : ℝ) := by
  change total (Fin.snoc half_20_05_φ1 (269267687/2500000000 : ℝ))=(2167032743/10000000000 : ℝ)
  rw [alternate_total_snoc,half_20_05_total1]
  norm_num

private theorem half_20_05_bounds2 : ∀ l,0≤half_20_05_φ2 l ∧ half_20_05_φ2 l≤1 ∧
    0≤shiftExponents 9 half_20_05_φ2 l :=
  alternate_bounds_snoc half_20_05_φ1 (269267687/2500000000 : ℝ) half_20_05_bounds1 (by norm_num)

private def half_20_05_φ3 : Fin 3 → ℝ := Fin.snoc half_20_05_φ2 (979120907/10000000000 : ℝ)

private theorem half_20_05_total3 : total half_20_05_φ3=(62923073/200000000 : ℝ) := by
  change total (Fin.snoc half_20_05_φ2 (979120907/10000000000 : ℝ))=(62923073/200000000 : ℝ)
  rw [alternate_total_snoc,half_20_05_total2]
  norm_num

private theorem half_20_05_bounds3 : ∀ l,0≤half_20_05_φ3 l ∧ half_20_05_φ3 l≤1 ∧
    0≤shiftExponents 9 half_20_05_φ3 l :=
  alternate_bounds_snoc half_20_05_φ2 (979120907/10000000000 : ℝ) half_20_05_bounds2 (by norm_num)

private def half_20_05_φ4 : Fin 4 → ℝ := Fin.snoc half_20_05_φ3 (856730793/10000000000 : ℝ)

private theorem half_20_05_total4 : total half_20_05_φ4=(4002884443/10000000000 : ℝ) := by
  change total (Fin.snoc half_20_05_φ3 (856730793/10000000000 : ℝ))=(4002884443/10000000000 : ℝ)
  rw [alternate_total_snoc,half_20_05_total3]
  norm_num

private theorem half_20_05_bounds4 : ∀ l,0≤half_20_05_φ4 l ∧ half_20_05_φ4 l≤1 ∧
    0≤shiftExponents 9 half_20_05_φ4 l :=
  alternate_bounds_snoc half_20_05_φ3 (856730793/10000000000 : ℝ) half_20_05_bounds3 (by norm_num)

private def half_20_05_φ5 : Fin 5 → ℝ := Fin.snoc half_20_05_φ4 (187409861/2500000000 : ℝ)

private theorem half_20_05_total5 : total half_20_05_φ5=(4752523887/10000000000 : ℝ) := by
  change total (Fin.snoc half_20_05_φ4 (187409861/2500000000 : ℝ))=(4752523887/10000000000 : ℝ)
  rw [alternate_total_snoc,half_20_05_total4]
  norm_num

private theorem half_20_05_bounds5 : ∀ l,0≤half_20_05_φ5 l ∧ half_20_05_φ5 l≤1 ∧
    0≤shiftExponents 9 half_20_05_φ5 l :=
  alternate_bounds_snoc half_20_05_φ4 (187409861/2500000000 : ℝ) half_20_05_bounds4 (by norm_num)

private def half_20_05_φ6 : Fin 6 → ℝ := Fin.snoc half_20_05_φ5 (655934513/10000000000 : ℝ)

private theorem half_20_05_total6 : total half_20_05_φ6=(6760573/12500000 : ℝ) := by
  change total (Fin.snoc half_20_05_φ5 (655934513/10000000000 : ℝ))=(6760573/12500000 : ℝ)
  rw [alternate_total_snoc,half_20_05_total5]
  norm_num

private theorem half_20_05_bounds6 : ∀ l,0≤half_20_05_φ6 l ∧ half_20_05_φ6 l≤1 ∧
    0≤shiftExponents 9 half_20_05_φ6 l :=
  alternate_bounds_snoc half_20_05_φ5 (655934513/10000000000 : ℝ) half_20_05_bounds5 (by norm_num)

private theorem half_20_05_prefix : PrefixCondition 9 half_20_05_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_20_05_φ1, half_20_05_φ2, half_20_05_φ3, half_20_05_φ4, half_20_05_φ5, half_20_05_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_20_05_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_20_05_φ6) (10968281/1562500 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_20_05_φ6
    (fun i => (half_20_05_bounds6 i).1) (fun i => (half_20_05_bounds6 i).2.1)
    (fun i => (half_20_05_bounds6 i).2.2) half_20_05_prefix
  convert h using 1 <;> norm_num [half_20_05_total1, half_20_05_total2, half_20_05_total3, half_20_05_total4, half_20_05_total5, half_20_05_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_20_05_hx6 : SourcePowerBound
    (powerBoxCross 9 14 64 half_20_05_φ6) (115959943837/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 14) (r := 2) (v := 18) (w := 19) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_20_05_φ6 (by norm_num [half_20_05_total1, half_20_05_total2, half_20_05_total3, half_20_05_total4, half_20_05_total5, half_20_05_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_20_05_total1, half_20_05_total2, half_20_05_total3, half_20_05_total4, half_20_05_total5, half_20_05_total6, parameterExponent, curveLoss, dyadicExponent]) half_20_05_hF2
    (half_18_05) (half_19_05)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_20_05_total1, half_20_05_total2, half_20_05_total3, half_20_05_total4, half_20_05_total5, half_20_05_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_05_hx5 : SourcePowerBound
    (powerBoxCross 9 15 32 half_20_05_φ5) (83968269/6250000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 15) (u := 13) (t := 16)
    (D := 32) (ψ := (655934513/10000000000 : ℝ)) half_20_05_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_05_bounds5 l).1) (fun l => (half_20_05_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_05_total1, half_20_05_total2, half_20_05_total3, half_20_05_total4, half_20_05_total5, half_20_05_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_14_05) (half_16_05)
    (by simpa only [half_20_05_φ6, show (2:ℝ)*32=64 by norm_num] using half_20_05_hx6)
  exact h.weaken (by norm_num [half_20_05_total1, half_20_05_total2, half_20_05_total3, half_20_05_total4, half_20_05_total5, half_20_05_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_05_hx4 : SourcePowerBound
    (powerBoxCross 9 16 16 half_20_05_φ4) (31612487793/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 16) (u := 14) (t := 17)
    (D := 16) (ψ := (187409861/2500000000 : ℝ)) half_20_05_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_05_bounds4 l).1) (fun l => (half_20_05_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_05_total1, half_20_05_total2, half_20_05_total3, half_20_05_total4, half_20_05_total5, half_20_05_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_15_05) (half_17_05)
    (by simpa only [half_20_05_φ5, show (2:ℝ)*16=32 by norm_num] using half_20_05_hx5)
  exact h.weaken (by norm_num [half_20_05_total1, half_20_05_total2, half_20_05_total3, half_20_05_total4, half_20_05_total5, half_20_05_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_05_hx3 : SourcePowerBound
    (powerBoxCross 9 17 8 half_20_05_φ3) (188219313047/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 17) (u := 15) (t := 18)
    (D := 8) (ψ := (856730793/10000000000 : ℝ)) half_20_05_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_05_bounds3 l).1) (fun l => (half_20_05_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_05_total1, half_20_05_total2, half_20_05_total3, half_20_05_total4, half_20_05_total5, half_20_05_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_16_05) (half_18_05)
    (by simpa only [half_20_05_φ4, show (2:ℝ)*8=16 by norm_num] using half_20_05_hx4)
  exact h.weaken (by norm_num [half_20_05_total1, half_20_05_total2, half_20_05_total3, half_20_05_total4, half_20_05_total5, half_20_05_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_05_hx2 : SourcePowerBound
    (powerBoxCross 9 18 4 half_20_05_φ2) (226056531069/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 18) (u := 16) (t := 19)
    (D := 4) (ψ := (979120907/10000000000 : ℝ)) half_20_05_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_05_bounds2 l).1) (fun l => (half_20_05_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_05_total1, half_20_05_total2, half_20_05_total3, half_20_05_total4, half_20_05_total5, half_20_05_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_17_05) (half_19_05)
    (by simpa only [half_20_05_φ3, show (2:ℝ)*4=8 by norm_num] using half_20_05_hx3)
  exact h.weaken (by norm_num [half_20_05_total1, half_20_05_total2, half_20_05_total3, half_20_05_total4, half_20_05_total5, half_20_05_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_05_hx1 : SourcePowerBound
    (powerBoxCross 9 19 2 half_20_05_φ1) (67871612939/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 19) (u := 17) (t := 20)
    (D := 2) (ψ := (269267687/2500000000 : ℝ)) half_20_05_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_05_bounds1 l).1) (fun l => (half_20_05_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_05_total1, half_20_05_total2, half_20_05_total3, half_20_05_total4, half_20_05_total5, half_20_05_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_18_05) (half_20_04)
    (by simpa only [half_20_05_φ2, show (2:ℝ)*2=4 by norm_num] using half_20_05_hx2)
  exact h.weaken (by norm_num [half_20_05_total1, half_20_05_total2, half_20_05_total3, half_20_05_total4, half_20_05_total5, half_20_05_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_20_05 : AdmissibleExponent 9 40 (311815045571/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 18) (ψ := (217992399/2000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_19_05)
    (by simpa only [half_20_05_φ1] using half_20_05_hx1)
  exact admissibleExponent_mono h (by norm_num [half_20_05_total1, half_20_05_total2, half_20_05_total3, half_20_05_total4, half_20_05_total5, half_20_05_total6, parameterExponent, curveLoss, dyadicExponent])

private def half_21_05_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1097556457/10000000000 : ℝ)

private theorem half_21_05_total1 : total half_21_05_φ1=(1097556457/10000000000 : ℝ) := by
  norm_num [half_21_05_φ1,total,emptyPhi,Fin.snoc]

private theorem half_21_05_bounds1 : ∀ l,0≤half_21_05_φ1 l ∧ half_21_05_φ1 l≤1 ∧
    0≤shiftExponents 9 half_21_05_φ1 l :=
  alternate_bounds_snoc emptyPhi (1097556457/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_21_05_φ2 : Fin 2 → ℝ := Fin.snoc half_21_05_φ1 (217173111/2000000000 : ℝ)

private theorem half_21_05_total2 : total half_21_05_φ2=(545855503/2500000000 : ℝ) := by
  change total (Fin.snoc half_21_05_φ1 (217173111/2000000000 : ℝ))=(545855503/2500000000 : ℝ)
  rw [alternate_total_snoc,half_21_05_total1]
  norm_num

private theorem half_21_05_bounds2 : ∀ l,0≤half_21_05_φ2 l ∧ half_21_05_φ2 l≤1 ∧
    0≤shiftExponents 9 half_21_05_φ2 l :=
  alternate_bounds_snoc half_21_05_φ1 (217173111/2000000000 : ℝ) half_21_05_bounds1 (by norm_num)

private def half_21_05_φ3 : Fin 3 → ℝ := Fin.snoc half_21_05_φ2 (122134031/1250000000 : ℝ)

private theorem half_21_05_total3 : total half_21_05_φ3=(158024713/500000000 : ℝ) := by
  change total (Fin.snoc half_21_05_φ2 (122134031/1250000000 : ℝ))=(158024713/500000000 : ℝ)
  rw [alternate_total_snoc,half_21_05_total2]
  norm_num

private theorem half_21_05_bounds3 : ∀ l,0≤half_21_05_φ3 l ∧ half_21_05_φ3 l≤1 ∧
    0≤shiftExponents 9 half_21_05_φ3 l :=
  alternate_bounds_snoc half_21_05_φ2 (122134031/1250000000 : ℝ) half_21_05_bounds2 (by norm_num)

private def half_21_05_φ4 : Fin 4 → ℝ := Fin.snoc half_21_05_φ3 (854938217/10000000000 : ℝ)

private theorem half_21_05_total4 : total half_21_05_φ4=(4015432477/10000000000 : ℝ) := by
  change total (Fin.snoc half_21_05_φ3 (854938217/10000000000 : ℝ))=(4015432477/10000000000 : ℝ)
  rw [alternate_total_snoc,half_21_05_total3]
  norm_num

private theorem half_21_05_bounds4 : ∀ l,0≤half_21_05_φ4 l ∧ half_21_05_φ4 l≤1 ∧
    0≤shiftExponents 9 half_21_05_φ4 l :=
  alternate_bounds_snoc half_21_05_φ3 (854938217/10000000000 : ℝ) half_21_05_bounds3 (by norm_num)

private def half_21_05_φ5 : Fin 5 → ℝ := Fin.snoc half_21_05_φ4 (37403547/500000000 : ℝ)

private theorem half_21_05_total5 : total half_21_05_φ5=(4763503417/10000000000 : ℝ) := by
  change total (Fin.snoc half_21_05_φ4 (37403547/500000000 : ℝ))=(4763503417/10000000000 : ℝ)
  rw [alternate_total_snoc,half_21_05_total4]
  norm_num

private theorem half_21_05_bounds5 : ∀ l,0≤half_21_05_φ5 l ∧ half_21_05_φ5 l≤1 ∧
    0≤shiftExponents 9 half_21_05_φ5 l :=
  alternate_bounds_snoc half_21_05_φ4 (37403547/500000000 : ℝ) half_21_05_bounds4 (by norm_num)

private def half_21_05_φ6 : Fin 6 → ℝ := Fin.snoc half_21_05_φ5 (81820259/1250000000 : ℝ)

private theorem half_21_05_total6 : total half_21_05_φ6=(5418065489/10000000000 : ℝ) := by
  change total (Fin.snoc half_21_05_φ5 (81820259/1250000000 : ℝ))=(5418065489/10000000000 : ℝ)
  rw [alternate_total_snoc,half_21_05_total5]
  norm_num

private theorem half_21_05_bounds6 : ∀ l,0≤half_21_05_φ6 l ∧ half_21_05_φ6 l≤1 ∧
    0≤shiftExponents 9 half_21_05_φ6 l :=
  alternate_bounds_snoc half_21_05_φ5 (81820259/1250000000 : ℝ) half_21_05_bounds5 (by norm_num)

private theorem half_21_05_prefix : PrefixCondition 9 half_21_05_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_21_05_φ1, half_21_05_φ2, half_21_05_φ3, half_21_05_φ4, half_21_05_φ5, half_21_05_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_21_05_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_21_05_φ6) (8745803533/1250000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_21_05_φ6
    (fun i => (half_21_05_bounds6 i).1) (fun i => (half_21_05_bounds6 i).2.1)
    (fun i => (half_21_05_bounds6 i).2.2) half_21_05_prefix
  convert h using 1 <;> norm_num [half_21_05_total1, half_21_05_total2, half_21_05_total3, half_21_05_total4, half_21_05_total5, half_21_05_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_21_05_hx6 : SourcePowerBound
    (powerBoxCross 9 15 64 half_21_05_φ6) (124645315943/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 15) (r := 2) (v := 0) (w := 20) (D := 64)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_21_05_φ6 (by norm_num [half_21_05_total1, half_21_05_total2, half_21_05_total3, half_21_05_total4, half_21_05_total5, half_21_05_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_21_05_total1, half_21_05_total2, half_21_05_total3, half_21_05_total4, half_21_05_total5, half_21_05_total6, parameterExponent, curveLoss, dyadicExponent]) half_21_05_hF2
    (admissibleExponent_zero 9) (half_20_05)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_21_05_total1, half_21_05_total2, half_21_05_total3, half_21_05_total4, half_21_05_total5, half_21_05_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_21_05_hx5 : SourcePowerBound
    (powerBoxCross 9 16 32 half_21_05_φ5) (4504577817/312500000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 16) (u := 14) (t := 17)
    (D := 32) (ψ := (81820259/1250000000 : ℝ)) half_21_05_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_21_05_bounds5 l).1) (fun l => (half_21_05_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_21_05_total1, half_21_05_total2, half_21_05_total3, half_21_05_total4, half_21_05_total5, half_21_05_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_15_05) (half_17_05)
    (by simpa only [half_21_05_φ6, show (2:ℝ)*32=64 by norm_num] using half_21_05_hx6)
  exact h.weaken (by norm_num [half_21_05_total1, half_21_05_total2, half_21_05_total3, half_21_05_total4, half_21_05_total5, half_21_05_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_21_05_hx4 : SourcePowerBound
    (powerBoxCross 9 17 16 half_21_05_φ4) (169242155161/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 17) (u := 15) (t := 18)
    (D := 16) (ψ := (37403547/500000000 : ℝ)) half_21_05_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_21_05_bounds4 l).1) (fun l => (half_21_05_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_21_05_total1, half_21_05_total2, half_21_05_total3, half_21_05_total4, half_21_05_total5, half_21_05_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_16_05) (half_18_05)
    (by simpa only [half_21_05_φ5, show (2:ℝ)*16=32 by norm_num] using half_21_05_hx5)
  exact h.weaken (by norm_num [half_21_05_total1, half_21_05_total2, half_21_05_total3, half_21_05_total4, half_21_05_total5, half_21_05_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_21_05_hx3 : SourcePowerBound
    (powerBoxCross 9 18 8 half_21_05_φ3) (100514050093/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 18) (u := 16) (t := 19)
    (D := 8) (ψ := (854938217/10000000000 : ℝ)) half_21_05_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_21_05_bounds3 l).1) (fun l => (half_21_05_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_21_05_total1, half_21_05_total2, half_21_05_total3, half_21_05_total4, half_21_05_total5, half_21_05_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_17_05) (half_19_05)
    (by simpa only [half_21_05_φ4, show (2:ℝ)*8=16 by norm_num] using half_21_05_hx4)
  exact h.weaken (by norm_num [half_21_05_total1, half_21_05_total2, half_21_05_total3, half_21_05_total4, half_21_05_total5, half_21_05_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_21_05_hx2 : SourcePowerBound
    (powerBoxCross 9 19 4 half_21_05_φ2) (120372728731/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 19) (u := 17) (t := 20)
    (D := 4) (ψ := (122134031/1250000000 : ℝ)) half_21_05_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_21_05_bounds2 l).1) (fun l => (half_21_05_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_21_05_total1, half_21_05_total2, half_21_05_total3, half_21_05_total4, half_21_05_total5, half_21_05_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_18_05) (half_20_05)
    (by simpa only [half_21_05_φ3, show (2:ℝ)*4=8 by norm_num] using half_21_05_hx3)
  exact h.weaken (by norm_num [half_21_05_total1, half_21_05_total2, half_21_05_total3, half_21_05_total4, half_21_05_total5, half_21_05_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_21_05_hx1 : SourcePowerBound
    (powerBoxCross 9 20 2 half_21_05_φ1) (57737828073/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 20) (u := 18) (t := 21)
    (D := 2) (ψ := (217173111/2000000000 : ℝ)) half_21_05_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_21_05_bounds1 l).1) (fun l => (half_21_05_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_21_05_total1, half_21_05_total2, half_21_05_total3, half_21_05_total4, half_21_05_total5, half_21_05_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_19_05) (half_21_04)
    (by simpa only [half_21_05_φ2, show (2:ℝ)*2=4 by norm_num] using half_21_05_hx2)
  exact h.weaken (by norm_num [half_21_05_total1, half_21_05_total2, half_21_05_total3, half_21_05_total4, half_21_05_total5, half_21_05_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_21_05 : AdmissibleExponent 9 42 (82873460547/2500000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 19) (ψ := (1097556457/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_20_05)
    (by simpa only [half_21_05_φ1] using half_21_05_hx1)
  exact admissibleExponent_mono h (by norm_num [half_21_05_total1, half_21_05_total2, half_21_05_total3, half_21_05_total4, half_21_05_total5, half_21_05_total6, parameterExponent, curveLoss, dyadicExponent])

private def half_22_05_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (221113111/2000000000 : ℝ)

private theorem half_22_05_total1 : total half_22_05_φ1=(221113111/2000000000 : ℝ) := by
  norm_num [half_22_05_φ1,total,emptyPhi,Fin.snoc]

private theorem half_22_05_bounds1 : ∀ l,0≤half_22_05_φ1 l ∧ half_22_05_φ1 l≤1 ∧
    0≤shiftExponents 9 half_22_05_φ1 l :=
  alternate_bounds_snoc emptyPhi (221113111/2000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_22_05_φ2 : Fin 2 → ℝ := Fin.snoc half_22_05_φ1 (1093320907/10000000000 : ℝ)

private theorem half_22_05_total2 : total half_22_05_φ2=(1099443231/5000000000 : ℝ) := by
  change total (Fin.snoc half_22_05_φ1 (1093320907/10000000000 : ℝ))=(1099443231/5000000000 : ℝ)
  rw [alternate_total_snoc,half_22_05_total1]
  norm_num

private theorem half_22_05_bounds2 : ∀ l,0≤half_22_05_φ2 l ∧ half_22_05_φ2 l≤1 ∧
    0≤shiftExponents 9 half_22_05_φ2 l :=
  alternate_bounds_snoc half_22_05_φ1 (1093320907/10000000000 : ℝ) half_22_05_bounds1 (by norm_num)

private def half_22_05_φ3 : Fin 3 → ℝ := Fin.snoc half_22_05_φ2 (121892399/1250000000 : ℝ)

private theorem half_22_05_total3 : total half_22_05_φ3=(1587012827/5000000000 : ℝ) := by
  change total (Fin.snoc half_22_05_φ2 (121892399/1250000000 : ℝ))=(1587012827/5000000000 : ℝ)
  rw [alternate_total_snoc,half_22_05_total2]
  norm_num

private theorem half_22_05_bounds3 : ∀ l,0≤half_22_05_φ3 l ∧ half_22_05_φ3 l≤1 ∧
    0≤shiftExponents 9 half_22_05_φ3 l :=
  alternate_bounds_snoc half_22_05_φ2 (121892399/1250000000 : ℝ) half_22_05_bounds2 (by norm_num)

private def half_22_05_φ4 : Fin 4 → ℝ := Fin.snoc half_22_05_φ3 (853246793/10000000000 : ℝ)

private theorem half_22_05_total4 : total half_22_05_φ4=(4027272447/10000000000 : ℝ) := by
  change total (Fin.snoc half_22_05_φ3 (853246793/10000000000 : ℝ))=(4027272447/10000000000 : ℝ)
  rw [alternate_total_snoc,half_22_05_total3]
  norm_num

private theorem half_22_05_bounds4 : ∀ l,0≤half_22_05_φ4 l ∧ half_22_05_φ4 l≤1 ∧
    0≤shiftExponents 9 half_22_05_φ4 l :=
  alternate_bounds_snoc half_22_05_φ3 (853246793/10000000000 : ℝ) half_22_05_bounds3 (by norm_num)

private def half_22_05_φ5 : Fin 5 → ℝ := Fin.snoc half_22_05_φ4 (746590943/10000000000 : ℝ)

private theorem half_22_05_total5 : total half_22_05_φ5=(477386339/1000000000 : ℝ) := by
  change total (Fin.snoc half_22_05_φ4 (746590943/10000000000 : ℝ))=(477386339/1000000000 : ℝ)
  rw [alternate_total_snoc,half_22_05_total4]
  norm_num

private theorem half_22_05_bounds5 : ∀ l,0≤half_22_05_φ5 l ∧ half_22_05_φ5 l≤1 ∧
    0≤shiftExponents 9 half_22_05_φ5 l :=
  alternate_bounds_snoc half_22_05_φ4 (746590943/10000000000 : ℝ) half_22_05_bounds4 (by norm_num)

private def half_22_05_φ6 : Fin 6 → ℝ := Fin.snoc half_22_05_φ5 (26130683/400000000 : ℝ)

private theorem half_22_05_total6 : total half_22_05_φ6=(1085426093/2000000000 : ℝ) := by
  change total (Fin.snoc half_22_05_φ5 (26130683/400000000 : ℝ))=(1085426093/2000000000 : ℝ)
  rw [alternate_total_snoc,half_22_05_total5]
  norm_num

private theorem half_22_05_bounds6 : ∀ l,0≤half_22_05_φ6 l ∧ half_22_05_φ6 l≤1 ∧
    0≤shiftExponents 9 half_22_05_φ6 l :=
  alternate_bounds_snoc half_22_05_φ5 (26130683/400000000 : ℝ) half_22_05_bounds5 (by norm_num)

private theorem half_22_05_prefix : PrefixCondition 9 half_22_05_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_22_05_φ1, half_22_05_φ2, half_22_05_φ3, half_22_05_φ4, half_22_05_φ5, half_22_05_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_22_05_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_22_05_φ6) (1743721721/250000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_22_05_φ6
    (fun i => (half_22_05_bounds6 i).1) (fun i => (half_22_05_bounds6 i).2.1)
    (fun i => (half_22_05_bounds6 i).2.2) half_22_05_prefix
  convert h using 1 <;> norm_num [half_22_05_total1, half_22_05_total2, half_22_05_total3, half_22_05_total4, half_22_05_total5, half_22_05_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_22_05_hx6 : SourcePowerBound
    (powerBoxCross 9 16 64 half_22_05_φ6) (133411043957/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 16) (r := 2) (v := 21) (w := 22) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_22_05_φ6 (by norm_num [half_22_05_total1, half_22_05_total2, half_22_05_total3, half_22_05_total4, half_22_05_total5, half_22_05_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_22_05_total1, half_22_05_total2, half_22_05_total3, half_22_05_total4, half_22_05_total5, half_22_05_total6, parameterExponent, curveLoss, dyadicExponent]) half_22_05_hF2
    (half_21_05) (half_22_04)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_22_05_total1, half_22_05_total2, half_22_05_total3, half_22_05_total4, half_22_05_total5, half_22_05_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_22_05_hx5 : SourcePowerBound
    (powerBoxCross 9 17 32 half_22_05_φ5) (154025485473/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 17) (u := 15) (t := 18)
    (D := 32) (ψ := (26130683/400000000 : ℝ)) half_22_05_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_22_05_bounds5 l).1) (fun l => (half_22_05_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_22_05_total1, half_22_05_total2, half_22_05_total3, half_22_05_total4, half_22_05_total5, half_22_05_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_16_05) (half_18_05)
    (by simpa only [half_22_05_φ6, show (2:ℝ)*32=64 by norm_num] using half_22_05_hx6)
  exact h.weaken (by norm_num [half_22_05_total1, half_22_05_total2, half_22_05_total3, half_22_05_total4, half_22_05_total5, half_22_05_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_22_05_hx4 : SourcePowerBound
    (powerBoxCross 9 18 16 half_22_05_φ4) (90249547859/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 18) (u := 16) (t := 19)
    (D := 16) (ψ := (746590943/10000000000 : ℝ)) half_22_05_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_22_05_bounds4 l).1) (fun l => (half_22_05_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_22_05_total1, half_22_05_total2, half_22_05_total3, half_22_05_total4, half_22_05_total5, half_22_05_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_17_05) (half_19_05)
    (by simpa only [half_22_05_φ5, show (2:ℝ)*16=32 by norm_num] using half_22_05_hx5)
  exact h.weaken (by norm_num [half_22_05_total1, half_22_05_total2, half_22_05_total3, half_22_05_total4, half_22_05_total5, half_22_05_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_22_05_hx3 : SourcePowerBound
    (powerBoxCross 9 19 8 half_22_05_φ3) (213907339209/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 19) (u := 17) (t := 20)
    (D := 8) (ψ := (853246793/10000000000 : ℝ)) half_22_05_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_22_05_bounds3 l).1) (fun l => (half_22_05_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_22_05_total1, half_22_05_total2, half_22_05_total3, half_22_05_total4, half_22_05_total5, half_22_05_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_18_05) (half_20_05)
    (by simpa only [half_22_05_φ4, show (2:ℝ)*8=16 by norm_num] using half_22_05_hx4)
  exact h.weaken (by norm_num [half_22_05_total1, half_22_05_total2, half_22_05_total3, half_22_05_total4, half_22_05_total5, half_22_05_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_22_05_hx2 : SourcePowerBound
    (powerBoxCross 9 20 4 half_22_05_φ2) (63874813453/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 20) (u := 18) (t := 21)
    (D := 4) (ψ := (121892399/1250000000 : ℝ)) half_22_05_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_22_05_bounds2 l).1) (fun l => (half_22_05_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_22_05_total1, half_22_05_total2, half_22_05_total3, half_22_05_total4, half_22_05_total5, half_22_05_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_19_05) (half_21_05)
    (by simpa only [half_22_05_φ3, show (2:ℝ)*4=8 by norm_num] using half_22_05_hx3)
  exact h.weaken (by norm_num [half_22_05_total1, half_22_05_total2, half_22_05_total3, half_22_05_total4, half_22_05_total5, half_22_05_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_22_05_hx1 : SourcePowerBound
    (powerBoxCross 9 21 2 half_22_05_φ1) (61190118077/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 21) (u := 19) (t := 22)
    (D := 2) (ψ := (1093320907/10000000000 : ℝ)) half_22_05_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_22_05_bounds1 l).1) (fun l => (half_22_05_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_22_05_total1, half_22_05_total2, half_22_05_total3, half_22_05_total4, half_22_05_total5, half_22_05_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_20_05) (half_22_04)
    (by simpa only [half_22_05_φ2, show (2:ℝ)*2=4 by norm_num] using half_22_05_hx2)
  exact h.weaken (by norm_num [half_22_05_total1, half_22_05_total2, half_22_05_total3, half_22_05_total4, half_22_05_total5, half_22_05_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_22_05 : AdmissibleExponent 9 44 (17563938907/500000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 20) (ψ := (221113111/2000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_21_05)
    (by simpa only [half_22_05_φ1] using half_22_05_hx1)
  exact admissibleExponent_mono h (by norm_num [half_22_05_total1, half_22_05_total2, half_22_05_total3, half_22_05_total4, half_22_05_total5, half_22_05_total6, parameterExponent, curveLoss, dyadicExponent])

private def half_10_06_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (880959859/10000000000 : ℝ)

private theorem half_10_06_total1 : total half_10_06_φ1=(880959859/10000000000 : ℝ) := by
  norm_num [half_10_06_φ1,total,emptyPhi,Fin.snoc]

private theorem half_10_06_bounds1 : ∀ l,0≤half_10_06_φ1 l ∧ half_10_06_φ1 l≤1 ∧
    0≤shiftExponents 9 half_10_06_φ1 l :=
  alternate_bounds_snoc emptyPhi (880959859/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_10_06_φ2 : Fin 2 → ℝ := Fin.snoc half_10_06_φ1 (164314967/2000000000 : ℝ)

private theorem half_10_06_total2 : total half_10_06_φ2=(851267347/5000000000 : ℝ) := by
  change total (Fin.snoc half_10_06_φ1 (164314967/2000000000 : ℝ))=(851267347/5000000000 : ℝ)
  rw [alternate_total_snoc,half_10_06_total1]
  norm_num

private theorem half_10_06_bounds2 : ∀ l,0≤half_10_06_φ2 l ∧ half_10_06_φ2 l≤1 ∧
    0≤shiftExponents 9 half_10_06_φ2 l :=
  alternate_bounds_snoc half_10_06_φ1 (164314967/2000000000 : ℝ) half_10_06_bounds1 (by norm_num)

private def half_10_06_φ3 : Fin 3 → ℝ := Fin.snoc half_10_06_φ2 (89634061/1250000000 : ℝ)

private theorem half_10_06_total3 : total half_10_06_φ3=(1209803591/5000000000 : ℝ) := by
  change total (Fin.snoc half_10_06_φ2 (89634061/1250000000 : ℝ))=(1209803591/5000000000 : ℝ)
  rw [alternate_total_snoc,half_10_06_total2]
  norm_num

private theorem half_10_06_bounds3 : ∀ l,0≤half_10_06_φ3 l ∧ half_10_06_φ3 l≤1 ∧
    0≤shiftExponents 9 half_10_06_φ3 l :=
  alternate_bounds_snoc half_10_06_φ2 (89634061/1250000000 : ℝ) half_10_06_bounds2 (by norm_num)

private def half_10_06_φ4 : Fin 4 → ℝ := Fin.snoc half_10_06_φ3 (112575613/2500000000 : ℝ)

private theorem half_10_06_total4 : total half_10_06_φ4=(1434954817/5000000000 : ℝ) := by
  change total (Fin.snoc half_10_06_φ3 (112575613/2500000000 : ℝ))=(1434954817/5000000000 : ℝ)
  rw [alternate_total_snoc,half_10_06_total3]
  norm_num

private theorem half_10_06_bounds4 : ∀ l,0≤half_10_06_φ4 l ∧ half_10_06_φ4 l≤1 ∧
    0≤shiftExponents 9 half_10_06_φ4 l :=
  alternate_bounds_snoc half_10_06_φ3 (112575613/2500000000 : ℝ) half_10_06_bounds3 (by norm_num)

private theorem half_10_06_prefix : PrefixCondition 9 half_10_06_φ4 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_10_06_φ1, half_10_06_φ2, half_10_06_φ3, half_10_06_φ4, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_10_06_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 16 half_10_06_φ4) (4445135549/625000000 : ℝ) := by
  have h := padded_dyadic_divisor_power (k := 9) (j := 4) (r := 0) (n := 1) (D := 16)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_10_06_φ4
    (fun i => (half_10_06_bounds4 i).1) (fun i => (half_10_06_bounds4 i).2.1)
    (fun i => (half_10_06_bounds4 i).2.2) half_10_06_prefix
  convert h using 1 <;> norm_num [half_10_06_total1, half_10_06_total2, half_10_06_total3, half_10_06_total4, parameterExponent, curveLoss, dyadicExponent]

private theorem half_10_06_hx4 : SourcePowerBound
    (powerBoxCross 9 6 16 half_10_06_φ4) (69138192733/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 6) (r := 2) (v := 0) (w := 8) (D := 16)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_10_06_φ4 (by norm_num [half_10_06_total1, half_10_06_total2, half_10_06_total3, half_10_06_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_10_06_total1, half_10_06_total2, half_10_06_total3, half_10_06_total4, parameterExponent, curveLoss, dyadicExponent]) half_10_06_hF2
    (admissibleExponent_zero 9) (SeedCompletionHigher9SimpleSeeds.degree9_half_8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_10_06_total1, half_10_06_total2, half_10_06_total3, half_10_06_total4, parameterExponent, curveLoss, dyadicExponent])

private theorem half_10_06_hx3 : SourcePowerBound
    (powerBoxCross 9 7 8 half_10_06_φ3) (19692025189/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 7) (u := 5) (t := 8)
    (D := 8) (ψ := (112575613/2500000000 : ℝ)) half_10_06_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_10_06_bounds3 l).1) (fun l => (half_10_06_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_10_06_total1, half_10_06_total2, half_10_06_total3, half_10_06_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionNinthSecondSeeds.ninth_half_6) (SeedCompletionHigher9SimpleSeeds.degree9_half_8)
    (by simpa only [half_10_06_φ4, show (2:ℝ)*8=16 by norm_num] using half_10_06_hx4)
  exact h.weaken (by norm_num [half_10_06_total1, half_10_06_total2, half_10_06_total3, half_10_06_total4, parameterExponent, curveLoss, dyadicExponent])

private theorem half_10_06_hx2 : SourcePowerBound
    (powerBoxCross 9 8 4 half_10_06_φ2) (46731073527/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 8) (u := 6) (t := 9)
    (D := 4) (ψ := (89634061/1250000000 : ℝ)) half_10_06_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_10_06_bounds2 l).1) (fun l => (half_10_06_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_10_06_total1, half_10_06_total2, half_10_06_total3, half_10_06_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionNinthSecondSeeds.ninth_half_7) (SeedCompletionHigher9SimpleSeeds.degree9_half_9)
    (by simpa only [half_10_06_φ3, show (2:ℝ)*4=8 by norm_num] using half_10_06_hx3)
  exact h.weaken (by norm_num [half_10_06_total1, half_10_06_total2, half_10_06_total3, half_10_06_total4, parameterExponent, curveLoss, dyadicExponent])

private theorem half_10_06_hx1 : SourcePowerBound
    (powerBoxCross 9 9 2 half_10_06_φ1) (5624494407/500000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 9) (u := 7) (t := 10)
    (D := 2) (ψ := (164314967/2000000000 : ℝ)) half_10_06_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_10_06_bounds1 l).1) (fun l => (half_10_06_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_10_06_total1, half_10_06_total2, half_10_06_total3, half_10_06_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_8) (half_10_05)
    (by simpa only [half_10_06_φ2, show (2:ℝ)*2=4 by norm_num] using half_10_06_hx2)
  exact h.weaken (by norm_num [half_10_06_total1, half_10_06_total2, half_10_06_total3, half_10_06_total4, parameterExponent, curveLoss, dyadicExponent])

theorem half_10_06 : AdmissibleExponent 9 20 (127466205743/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 8) (ψ := (880959859/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (SeedCompletionHigher9SimpleSeeds.degree9_half_9)
    (by simpa only [half_10_06_φ1] using half_10_06_hx1)
  exact admissibleExponent_mono h (by norm_num [half_10_06_total1, half_10_06_total2, half_10_06_total3, half_10_06_total4, parameterExponent, curveLoss, dyadicExponent])

private def half_11_06_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (183397009/2000000000 : ℝ)

private theorem half_11_06_total1 : total half_11_06_φ1=(183397009/2000000000 : ℝ) := by
  norm_num [half_11_06_φ1,total,emptyPhi,Fin.snoc]

private theorem half_11_06_bounds1 : ∀ l,0≤half_11_06_φ1 l ∧ half_11_06_φ1 l≤1 ∧
    0≤shiftExponents 9 half_11_06_φ1 l :=
  alternate_bounds_snoc emptyPhi (183397009/2000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_11_06_φ2 : Fin 2 → ℝ := Fin.snoc half_11_06_φ1 (432779533/5000000000 : ℝ)

private theorem half_11_06_total2 : total half_11_06_φ2=(1782544111/10000000000 : ℝ) := by
  change total (Fin.snoc half_11_06_φ1 (432779533/5000000000 : ℝ))=(1782544111/10000000000 : ℝ)
  rw [alternate_total_snoc,half_11_06_total1]
  norm_num

private theorem half_11_06_bounds2 : ∀ l,0≤half_11_06_φ2 l ∧ half_11_06_φ2 l≤1 ∧
    0≤shiftExponents 9 half_11_06_φ2 l :=
  alternate_bounds_snoc half_11_06_φ1 (432779533/5000000000 : ℝ) half_11_06_bounds1 (by norm_num)

private def half_11_06_φ3 : Fin 3 → ℝ := Fin.snoc half_11_06_φ2 (788213527/10000000000 : ℝ)

private theorem half_11_06_total3 : total half_11_06_φ3=(1285378819/5000000000 : ℝ) := by
  change total (Fin.snoc half_11_06_φ2 (788213527/10000000000 : ℝ))=(1285378819/5000000000 : ℝ)
  rw [alternate_total_snoc,half_11_06_total2]
  norm_num

private theorem half_11_06_bounds3 : ∀ l,0≤half_11_06_φ3 l ∧ half_11_06_φ3 l≤1 ∧
    0≤shiftExponents 9 half_11_06_φ3 l :=
  alternate_bounds_snoc half_11_06_φ2 (788213527/10000000000 : ℝ) half_11_06_bounds2 (by norm_num)

private def half_11_06_φ4 : Fin 4 → ℝ := Fin.snoc half_11_06_φ3 (625079227/10000000000 : ℝ)

private theorem half_11_06_total4 : total half_11_06_φ4=(639167373/2000000000 : ℝ) := by
  change total (Fin.snoc half_11_06_φ3 (625079227/10000000000 : ℝ))=(639167373/2000000000 : ℝ)
  rw [alternate_total_snoc,half_11_06_total3]
  norm_num

private theorem half_11_06_bounds4 : ∀ l,0≤half_11_06_φ4 l ∧ half_11_06_φ4 l≤1 ∧
    0≤shiftExponents 9 half_11_06_φ4 l :=
  alternate_bounds_snoc half_11_06_φ3 (625079227/10000000000 : ℝ) half_11_06_bounds3 (by norm_num)

private theorem half_11_06_prefix : PrefixCondition 9 half_11_06_φ4 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_11_06_φ1, half_11_06_φ2, half_11_06_φ3, half_11_06_φ4, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_11_06_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 16 half_11_06_φ4) (1582497881/250000000 : ℝ) := by
  have h := padded_dyadic_divisor_power (k := 9) (j := 4) (r := 0) (n := 1) (D := 16)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_11_06_φ4
    (fun i => (half_11_06_bounds4 i).1) (fun i => (half_11_06_bounds4 i).2.1)
    (fun i => (half_11_06_bounds4 i).2.2) half_11_06_prefix
  convert h using 1 <;> norm_num [half_11_06_total1, half_11_06_total2, half_11_06_total3, half_11_06_total4, parameterExponent, curveLoss, dyadicExponent]

private theorem half_11_06_hx4 : SourcePowerBound
    (powerBoxCross 9 7 16 half_11_06_φ4) (37707601449/5000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 7) (r := 2) (v := 9) (w := 10) (D := 16)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_11_06_φ4 (by norm_num [half_11_06_total1, half_11_06_total2, half_11_06_total3, half_11_06_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_11_06_total1, half_11_06_total2, half_11_06_total3, half_11_06_total4, parameterExponent, curveLoss, dyadicExponent]) half_11_06_hF2
    (SeedCompletionHigher9SimpleSeeds.degree9_half_9) (half_10_06)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_11_06_total1, half_11_06_total2, half_11_06_total3, half_11_06_total4, parameterExponent, curveLoss, dyadicExponent])

private theorem half_11_06_hx3 : SourcePowerBound
    (powerBoxCross 9 8 8 half_11_06_φ3) (87877761957/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 8) (u := 6) (t := 9)
    (D := 8) (ψ := (625079227/10000000000 : ℝ)) half_11_06_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_11_06_bounds3 l).1) (fun l => (half_11_06_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_11_06_total1, half_11_06_total2, half_11_06_total3, half_11_06_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionNinthSecondSeeds.ninth_half_7) (SeedCompletionHigher9SimpleSeeds.degree9_half_9)
    (by simpa only [half_11_06_φ4, show (2:ℝ)*8=16 by norm_num] using half_11_06_hx4)
  exact h.weaken (by norm_num [half_11_06_total1, half_11_06_total2, half_11_06_total3, half_11_06_total4, parameterExponent, curveLoss, dyadicExponent])

private theorem half_11_06_hx2 : SourcePowerBound
    (powerBoxCross 9 9 4 half_11_06_φ2) (105092702139/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 9) (u := 7) (t := 10)
    (D := 4) (ψ := (788213527/10000000000 : ℝ)) half_11_06_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_11_06_bounds2 l).1) (fun l => (half_11_06_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_11_06_total1, half_11_06_total2, half_11_06_total3, half_11_06_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_8) (half_10_06)
    (by simpa only [half_11_06_φ3, show (2:ℝ)*4=8 by norm_num] using half_11_06_hx3)
  exact h.weaken (by norm_num [half_11_06_total1, half_11_06_total2, half_11_06_total3, half_11_06_total4, parameterExponent, curveLoss, dyadicExponent])

private theorem half_11_06_hx1 : SourcePowerBound
    (powerBoxCross 9 10 2 half_11_06_φ1) (126694730349/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 10) (u := 8) (t := 11)
    (D := 2) (ψ := (432779533/5000000000 : ℝ)) half_11_06_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_11_06_bounds1 l).1) (fun l => (half_11_06_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_11_06_total1, half_11_06_total2, half_11_06_total3, half_11_06_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_9) (half_11_05)
    (by simpa only [half_11_06_φ2, show (2:ℝ)*2=4 by norm_num] using half_11_06_hx2)
  exact h.weaken (by norm_num [half_11_06_total1, half_11_06_total2, half_11_06_total3, half_11_06_total4, parameterExponent, curveLoss, dyadicExponent])

theorem half_11_06 : AdmissibleExponent 9 22 (36029361551/2500000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 9) (ψ := (183397009/2000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_10_06)
    (by simpa only [half_11_06_φ1] using half_11_06_hx1)
  exact admissibleExponent_mono h (by norm_num [half_11_06_total1, half_11_06_total2, half_11_06_total3, half_11_06_total4, parameterExponent, curveLoss, dyadicExponent])

private def half_12_06_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (94902509/1000000000 : ℝ)

private theorem half_12_06_total1 : total half_12_06_φ1=(94902509/1000000000 : ℝ) := by
  norm_num [half_12_06_φ1,total,emptyPhi,Fin.snoc]

private theorem half_12_06_bounds1 : ∀ l,0≤half_12_06_φ1 l ∧ half_12_06_φ1 l≤1 ∧
    0≤shiftExponents 9 half_12_06_φ1 l :=
  alternate_bounds_snoc emptyPhi (94902509/1000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_12_06_φ2 : Fin 2 → ℝ := Fin.snoc half_12_06_φ1 (451763313/5000000000 : ℝ)

private theorem half_12_06_total2 : total half_12_06_φ2=(463137929/2500000000 : ℝ) := by
  change total (Fin.snoc half_12_06_φ1 (451763313/5000000000 : ℝ))=(463137929/2500000000 : ℝ)
  rw [alternate_total_snoc,half_12_06_total1]
  norm_num

private theorem half_12_06_bounds2 : ∀ l,0≤half_12_06_φ2 l ∧ half_12_06_φ2 l≤1 ∧
    0≤shiftExponents 9 half_12_06_φ2 l :=
  alternate_bounds_snoc half_12_06_φ1 (451763313/5000000000 : ℝ) half_12_06_bounds1 (by norm_num)

private def half_12_06_φ3 : Fin 3 → ℝ := Fin.snoc half_12_06_φ2 (840895051/10000000000 : ℝ)

private theorem half_12_06_total3 : total half_12_06_φ3=(2693446767/10000000000 : ℝ) := by
  change total (Fin.snoc half_12_06_φ2 (840895051/10000000000 : ℝ))=(2693446767/10000000000 : ℝ)
  rw [alternate_total_snoc,half_12_06_total2]
  norm_num

private theorem half_12_06_bounds3 : ∀ l,0≤half_12_06_φ3 l ∧ half_12_06_φ3 l≤1 ∧
    0≤shiftExponents 9 half_12_06_φ3 l :=
  alternate_bounds_snoc half_12_06_φ2 (840895051/10000000000 : ℝ) half_12_06_bounds2 (by norm_num)

private def half_12_06_φ4 : Fin 4 → ℝ := Fin.snoc half_12_06_φ3 (9101721/125000000 : ℝ)

private theorem half_12_06_total4 : total half_12_06_φ4=(3421584447/10000000000 : ℝ) := by
  change total (Fin.snoc half_12_06_φ3 (9101721/125000000 : ℝ))=(3421584447/10000000000 : ℝ)
  rw [alternate_total_snoc,half_12_06_total3]
  norm_num

private theorem half_12_06_bounds4 : ∀ l,0≤half_12_06_φ4 l ∧ half_12_06_φ4 l≤1 ∧
    0≤shiftExponents 9 half_12_06_φ4 l :=
  alternate_bounds_snoc half_12_06_φ3 (9101721/125000000 : ℝ) half_12_06_bounds3 (by norm_num)

private def half_12_06_φ5 : Fin 5 → ℝ := Fin.snoc half_12_06_φ4 (450880249/10000000000 : ℝ)

private theorem half_12_06_total5 : total half_12_06_φ5=(484058087/1250000000 : ℝ) := by
  change total (Fin.snoc half_12_06_φ4 (450880249/10000000000 : ℝ))=(484058087/1250000000 : ℝ)
  rw [alternate_total_snoc,half_12_06_total4]
  norm_num

private theorem half_12_06_bounds5 : ∀ l,0≤half_12_06_φ5 l ∧ half_12_06_φ5 l≤1 ∧
    0≤shiftExponents 9 half_12_06_φ5 l :=
  alternate_bounds_snoc half_12_06_φ4 (450880249/10000000000 : ℝ) half_12_06_bounds4 (by norm_num)

private theorem half_12_06_prefix : PrefixCondition 9 half_12_06_φ5 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_12_06_φ1, half_12_06_φ2, half_12_06_φ3, half_12_06_φ4, half_12_06_φ5, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_12_06_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 32 half_12_06_φ5) (1204075739/156250000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_12_06_φ5
    (fun i => (half_12_06_bounds5 i).1) (fun i => (half_12_06_bounds5 i).2.1)
    (fun i => (half_12_06_bounds5 i).2.2) half_12_06_prefix
  convert h using 1 <;> norm_num [half_12_06_total1, half_12_06_total2, half_12_06_total3, half_12_06_total4, half_12_06_total5, parameterExponent, curveLoss, dyadicExponent]

private theorem half_12_06_hx5 : SourcePowerBound
    (powerBoxCross 9 7 32 half_12_06_φ5) (36464796339/5000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 7) (r := 2) (v := 9) (w := 10) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_12_06_φ5 (by norm_num [half_12_06_total1, half_12_06_total2, half_12_06_total3, half_12_06_total4, half_12_06_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_12_06_total1, half_12_06_total2, half_12_06_total3, half_12_06_total4, half_12_06_total5, parameterExponent, curveLoss, dyadicExponent]) half_12_06_hF2
    (SeedCompletionHigher9SimpleSeeds.degree9_half_9) (half_10_06)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_12_06_total1, half_12_06_total2, half_12_06_total3, half_12_06_total4, half_12_06_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_12_06_hx4 : SourcePowerBound
    (powerBoxCross 9 8 16 half_12_06_φ4) (41179593149/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 8) (u := 6) (t := 9)
    (D := 16) (ψ := (450880249/10000000000 : ℝ)) half_12_06_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_12_06_bounds4 l).1) (fun l => (half_12_06_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_12_06_total1, half_12_06_total2, half_12_06_total3, half_12_06_total4, half_12_06_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionNinthSecondSeeds.ninth_half_7) (SeedCompletionHigher9SimpleSeeds.degree9_half_9)
    (by simpa only [half_12_06_φ5, show (2:ℝ)*16=32 by norm_num] using half_12_06_hx5)
  exact h.weaken (by norm_num [half_12_06_total1, half_12_06_total2, half_12_06_total3, half_12_06_total4, half_12_06_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_12_06_hx3 : SourcePowerBound
    (powerBoxCross 9 9 8 half_12_06_φ3) (19486753913/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 9) (u := 7) (t := 10)
    (D := 8) (ψ := (9101721/125000000 : ℝ)) half_12_06_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_12_06_bounds3 l).1) (fun l => (half_12_06_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_12_06_total1, half_12_06_total2, half_12_06_total3, half_12_06_total4, half_12_06_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_8) (half_10_06)
    (by simpa only [half_12_06_φ4, show (2:ℝ)*8=16 by norm_num] using half_12_06_hx4)
  exact h.weaken (by norm_num [half_12_06_total1, half_12_06_total2, half_12_06_total3, half_12_06_total4, half_12_06_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_12_06_hx2 : SourcePowerBound
    (powerBoxCross 9 10 4 half_12_06_φ2) (117163757841/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 10) (u := 8) (t := 11)
    (D := 4) (ψ := (840895051/10000000000 : ℝ)) half_12_06_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_12_06_bounds2 l).1) (fun l => (half_12_06_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_12_06_total1, half_12_06_total2, half_12_06_total3, half_12_06_total4, half_12_06_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_9) (half_11_06)
    (by simpa only [half_12_06_φ3, show (2:ℝ)*4=8 by norm_num] using half_12_06_hx3)
  exact h.weaken (by norm_num [half_12_06_total1, half_12_06_total2, half_12_06_total3, half_12_06_total4, half_12_06_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_12_06_hx1 : SourcePowerBound
    (powerBoxCross 9 11 2 half_12_06_φ1) (70694682031/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 11) (u := 9) (t := 12)
    (D := 2) (ψ := (451763313/5000000000 : ℝ)) half_12_06_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_12_06_bounds1 l).1) (fun l => (half_12_06_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_12_06_total1, half_12_06_total2, half_12_06_total3, half_12_06_total4, half_12_06_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_10_06) (half_12_05)
    (by simpa only [half_12_06_φ2, show (2:ℝ)*2=4 by norm_num] using half_12_06_hx2)
  exact h.weaken (by norm_num [half_12_06_total1, half_12_06_total2, half_12_06_total3, half_12_06_total4, half_12_06_total5, parameterExponent, curveLoss, dyadicExponent])

theorem half_12_06 : AdmissibleExponent 9 24 (20164861369/1250000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 10) (ψ := (94902509/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_11_06)
    (by simpa only [half_12_06_φ1] using half_12_06_hx1)
  exact admissibleExponent_mono h (by norm_num [half_12_06_total1, half_12_06_total2, half_12_06_total3, half_12_06_total4, half_12_06_total5, parameterExponent, curveLoss, dyadicExponent])

private def half_13_06_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (977213753/10000000000 : ℝ)

private theorem half_13_06_total1 : total half_13_06_φ1=(977213753/10000000000 : ℝ) := by
  norm_num [half_13_06_φ1,total,emptyPhi,Fin.snoc]

private theorem half_13_06_bounds1 : ∀ l,0≤half_13_06_φ1 l ∧ half_13_06_φ1 l≤1 ∧
    0≤shiftExponents 9 half_13_06_φ1 l :=
  alternate_bounds_snoc emptyPhi (977213753/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_13_06_φ2 : Fin 2 → ℝ := Fin.snoc half_13_06_φ1 (936025441/10000000000 : ℝ)

private theorem half_13_06_total2 : total half_13_06_φ2=(956619597/5000000000 : ℝ) := by
  change total (Fin.snoc half_13_06_φ1 (936025441/10000000000 : ℝ))=(956619597/5000000000 : ℝ)
  rw [alternate_total_snoc,half_13_06_total1]
  norm_num

private theorem half_13_06_bounds2 : ∀ l,0≤half_13_06_φ2 l ∧ half_13_06_φ2 l≤1 ∧
    0≤shiftExponents 9 half_13_06_φ2 l :=
  alternate_bounds_snoc half_13_06_φ1 (936025441/10000000000 : ℝ) half_13_06_bounds1 (by norm_num)

private def half_13_06_φ3 : Fin 3 → ℝ := Fin.snoc half_13_06_φ2 (3531331/40000000 : ℝ)

private theorem half_13_06_total3 : total half_13_06_φ3=(349508993/1250000000 : ℝ) := by
  change total (Fin.snoc half_13_06_φ2 (3531331/40000000 : ℝ))=(349508993/1250000000 : ℝ)
  rw [alternate_total_snoc,half_13_06_total2]
  norm_num

private theorem half_13_06_bounds3 : ∀ l,0≤half_13_06_φ3 l ∧ half_13_06_φ3 l≤1 ∧
    0≤shiftExponents 9 half_13_06_φ3 l :=
  alternate_bounds_snoc half_13_06_φ2 (3531331/40000000 : ℝ) half_13_06_bounds2 (by norm_num)

private def half_13_06_φ4 : Fin 4 → ℝ := Fin.snoc half_13_06_φ3 (794970231/10000000000 : ℝ)

private theorem half_13_06_total4 : total half_13_06_φ4=(143641687/400000000 : ℝ) := by
  change total (Fin.snoc half_13_06_φ3 (794970231/10000000000 : ℝ))=(143641687/400000000 : ℝ)
  rw [alternate_total_snoc,half_13_06_total3]
  norm_num

private theorem half_13_06_bounds4 : ∀ l,0≤half_13_06_φ4 l ∧ half_13_06_φ4 l≤1 ∧
    0≤shiftExponents 9 half_13_06_φ4 l :=
  alternate_bounds_snoc half_13_06_φ3 (794970231/10000000000 : ℝ) half_13_06_bounds3 (by norm_num)

private def half_13_06_φ5 : Fin 5 → ℝ := Fin.snoc half_13_06_φ4 (30404637/500000000 : ℝ)

private theorem half_13_06_total5 : total half_13_06_φ5=(839826983/2000000000 : ℝ) := by
  change total (Fin.snoc half_13_06_φ4 (30404637/500000000 : ℝ))=(839826983/2000000000 : ℝ)
  rw [alternate_total_snoc,half_13_06_total4]
  norm_num

private theorem half_13_06_bounds5 : ∀ l,0≤half_13_06_φ5 l ∧ half_13_06_φ5 l≤1 ∧
    0≤shiftExponents 9 half_13_06_φ5 l :=
  alternate_bounds_snoc half_13_06_φ4 (30404637/500000000 : ℝ) half_13_06_bounds4 (by norm_num)

private theorem half_13_06_prefix : PrefixCondition 9 half_13_06_φ5 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_13_06_φ1, half_13_06_φ2, half_13_06_φ3, half_13_06_φ4, half_13_06_φ5, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_13_06_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 32 half_13_06_φ5) (1730519051/250000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_13_06_φ5
    (fun i => (half_13_06_bounds5 i).1) (fun i => (half_13_06_bounds5 i).2.1)
    (fun i => (half_13_06_bounds5 i).2.2) half_13_06_prefix
  convert h using 1 <;> norm_num [half_13_06_total1, half_13_06_total2, half_13_06_total3, half_13_06_total4, half_13_06_total5, parameterExponent, curveLoss, dyadicExponent]

private theorem half_13_06_hx5 : SourcePowerBound
    (powerBoxCross 9 8 32 half_13_06_φ5) (38795420081/5000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 8) (r := 2) (v := 10) (w := 11) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_13_06_φ5 (by norm_num [half_13_06_total1, half_13_06_total2, half_13_06_total3, half_13_06_total4, half_13_06_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_13_06_total1, half_13_06_total2, half_13_06_total3, half_13_06_total4, half_13_06_total5, parameterExponent, curveLoss, dyadicExponent]) half_13_06_hF2
    (half_10_06) (half_11_06)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_13_06_total1, half_13_06_total2, half_13_06_total3, half_13_06_total4, half_13_06_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_13_06_hx4 : SourcePowerBound
    (powerBoxCross 9 9 16 half_13_06_φ4) (89838223767/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 9) (u := 7) (t := 10)
    (D := 16) (ψ := (30404637/500000000 : ℝ)) half_13_06_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_13_06_bounds4 l).1) (fun l => (half_13_06_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_13_06_total1, half_13_06_total2, half_13_06_total3, half_13_06_total4, half_13_06_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_8) (half_10_06)
    (by simpa only [half_13_06_φ5, show (2:ℝ)*16=32 by norm_num] using half_13_06_hx5)
  exact h.weaken (by norm_num [half_13_06_total1, half_13_06_total2, half_13_06_total3, half_13_06_total4, half_13_06_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_13_06_hx3 : SourcePowerBound
    (powerBoxCross 9 10 8 half_13_06_φ3) (4296106271/400000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 10) (u := 8) (t := 11)
    (D := 8) (ψ := (794970231/10000000000 : ℝ)) half_13_06_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_13_06_bounds3 l).1) (fun l => (half_13_06_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_13_06_total1, half_13_06_total2, half_13_06_total3, half_13_06_total4, half_13_06_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_9) (half_11_06)
    (by simpa only [half_13_06_φ4, show (2:ℝ)*8=16 by norm_num] using half_13_06_hx4)
  exact h.weaken (by norm_num [half_13_06_total1, half_13_06_total2, half_13_06_total3, half_13_06_total4, half_13_06_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_13_06_hx2 : SourcePowerBound
    (powerBoxCross 9 11 4 half_13_06_φ2) (16207830871/1250000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 11) (u := 9) (t := 12)
    (D := 4) (ψ := (3531331/40000000 : ℝ)) half_13_06_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_13_06_bounds2 l).1) (fun l => (half_13_06_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_13_06_total1, half_13_06_total2, half_13_06_total3, half_13_06_total4, half_13_06_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_10_06) (half_12_06)
    (by simpa only [half_13_06_φ3, show (2:ℝ)*4=8 by norm_num] using half_13_06_hx3)
  exact h.weaken (by norm_num [half_13_06_total1, half_13_06_total2, half_13_06_total3, half_13_06_total4, half_13_06_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_13_06_hx1 : SourcePowerBound
    (powerBoxCross 9 12 2 half_13_06_φ1) (78265900413/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 12) (u := 10) (t := 13)
    (D := 2) (ψ := (936025441/10000000000 : ℝ)) half_13_06_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_13_06_bounds1 l).1) (fun l => (half_13_06_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_13_06_total1, half_13_06_total2, half_13_06_total3, half_13_06_total4, half_13_06_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_11_06) (half_13_05)
    (by simpa only [half_13_06_φ2, show (2:ℝ)*2=4 by norm_num] using half_13_06_hx2)
  exact h.weaken (by norm_num [half_13_06_total1, half_13_06_total2, half_13_06_total3, half_13_06_total4, half_13_06_total5, parameterExponent, curveLoss, dyadicExponent])

theorem half_13_06 : AdmissibleExponent 9 26 (35801543429/2000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 11) (ψ := (977213753/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_12_06)
    (by simpa only [half_13_06_φ1] using half_13_06_hx1)
  exact admissibleExponent_mono h (by norm_num [half_13_06_total1, half_13_06_total2, half_13_06_total3, half_13_06_total4, half_13_06_total5, parameterExponent, curveLoss, dyadicExponent])

private def half_14_06_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (501283783/5000000000 : ℝ)

private theorem half_14_06_total1 : total half_14_06_φ1=(501283783/5000000000 : ℝ) := by
  norm_num [half_14_06_φ1,total,emptyPhi,Fin.snoc]

private theorem half_14_06_bounds1 : ∀ l,0≤half_14_06_φ1 l ∧ half_14_06_φ1 l≤1 ∧
    0≤shiftExponents 9 half_14_06_φ1 l :=
  alternate_bounds_snoc emptyPhi (501283783/5000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_14_06_φ2 : Fin 2 → ℝ := Fin.snoc half_14_06_φ1 (96558457/1000000000 : ℝ)

private theorem half_14_06_total2 : total half_14_06_φ2=(246019017/1250000000 : ℝ) := by
  change total (Fin.snoc half_14_06_φ1 (96558457/1000000000 : ℝ))=(246019017/1250000000 : ℝ)
  rw [alternate_total_snoc,half_14_06_total1]
  norm_num

private theorem half_14_06_bounds2 : ∀ l,0≤half_14_06_φ2 l ∧ half_14_06_φ2 l≤1 ∧
    0≤shiftExponents 9 half_14_06_φ2 l :=
  alternate_bounds_snoc half_14_06_φ1 (96558457/1000000000 : ℝ) half_14_06_bounds1 (by norm_num)

private def half_14_06_φ3 : Fin 3 → ℝ := Fin.snoc half_14_06_φ2 (230259281/2500000000 : ℝ)

private theorem half_14_06_total3 : total half_14_06_φ3=(144459463/500000000 : ℝ) := by
  change total (Fin.snoc half_14_06_φ2 (230259281/2500000000 : ℝ))=(144459463/500000000 : ℝ)
  rw [alternate_total_snoc,half_14_06_total2]
  norm_num

private theorem half_14_06_bounds3 : ∀ l,0≤half_14_06_φ3 l ∧ half_14_06_φ3 l≤1 ∧
    0≤shiftExponents 9 half_14_06_φ3 l :=
  alternate_bounds_snoc half_14_06_φ2 (230259281/2500000000 : ℝ) half_14_06_bounds2 (by norm_num)

private def half_14_06_φ4 : Fin 4 → ℝ := Fin.snoc half_14_06_φ3 (85304077/1000000000 : ℝ)

private theorem half_14_06_total4 : total half_14_06_φ4=(374223003/1000000000 : ℝ) := by
  change total (Fin.snoc half_14_06_φ3 (85304077/1000000000 : ℝ))=(374223003/1000000000 : ℝ)
  rw [alternate_total_snoc,half_14_06_total3]
  norm_num

private theorem half_14_06_bounds4 : ∀ l,0≤half_14_06_φ4 l ∧ half_14_06_φ4 l≤1 ∧
    0≤shiftExponents 9 half_14_06_φ4 l :=
  alternate_bounds_snoc half_14_06_φ3 (85304077/1000000000 : ℝ) half_14_06_bounds3 (by norm_num)

private def half_14_06_φ5 : Fin 5 → ℝ := Fin.snoc half_14_06_φ4 (725187593/10000000000 : ℝ)

private theorem half_14_06_total5 : total half_14_06_φ5=(4467417623/10000000000 : ℝ) := by
  change total (Fin.snoc half_14_06_φ4 (725187593/10000000000 : ℝ))=(4467417623/10000000000 : ℝ)
  rw [alternate_total_snoc,half_14_06_total4]
  norm_num

private theorem half_14_06_bounds5 : ∀ l,0≤half_14_06_φ5 l ∧ half_14_06_φ5 l≤1 ∧
    0≤shiftExponents 9 half_14_06_φ5 l :=
  alternate_bounds_snoc half_14_06_φ4 (725187593/10000000000 : ℝ) half_14_06_bounds4 (by norm_num)

private def half_14_06_φ6 : Fin 6 → ℝ := Fin.snoc half_14_06_φ5 (210344523/5000000000 : ℝ)

private theorem half_14_06_total6 : total half_14_06_φ6=(4888106669/10000000000 : ℝ) := by
  change total (Fin.snoc half_14_06_φ5 (210344523/5000000000 : ℝ))=(4888106669/10000000000 : ℝ)
  rw [alternate_total_snoc,half_14_06_total5]
  norm_num

private theorem half_14_06_bounds6 : ∀ l,0≤half_14_06_φ6 l ∧ half_14_06_φ6 l≤1 ∧
    0≤shiftExponents 9 half_14_06_φ6 l :=
  alternate_bounds_snoc half_14_06_φ5 (210344523/5000000000 : ℝ) half_14_06_bounds5 (by norm_num)

private theorem half_14_06_prefix : PrefixCondition 9 half_14_06_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_14_06_φ1, half_14_06_φ2, half_14_06_φ3, half_14_06_φ4, half_14_06_φ5, half_14_06_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_14_06_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_14_06_φ6) (10335679993/1250000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_14_06_φ6
    (fun i => (half_14_06_bounds6 i).1) (fun i => (half_14_06_bounds6 i).2.1)
    (fun i => (half_14_06_bounds6 i).2.2) half_14_06_prefix
  convert h using 1 <;> norm_num [half_14_06_total1, half_14_06_total2, half_14_06_total3, half_14_06_total4, half_14_06_total5, half_14_06_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_14_06_hF1 : SourcePowerBound
    (paddedMoment 9 0 1 64 half_14_06_φ6) (3861893331/1250000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 0) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_14_06_φ6
    (fun i => (half_14_06_bounds6 i).1) (fun i => (half_14_06_bounds6 i).2.1)
    (fun i => (half_14_06_bounds6 i).2.2) half_14_06_prefix
  convert h using 1 <;> norm_num [half_14_06_total1, half_14_06_total2, half_14_06_total3, half_14_06_total4, half_14_06_total5, half_14_06_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_14_06_hx6 : SourcePowerBound
    (powerBoxCross 9 8 64 half_14_06_φ6) (14755119689/2000000000 : ℝ) := by
  have h := full_B_cross_power (k := 9) (s := 8) (r := 1) (v := 2) (t := 11) (D := 64)
    (a := (1/22 : ℝ)) (b := (5/22 : ℝ)) (c := (8/11 : ℝ))
    (by norm_num) half_14_06_φ6 (by norm_num [half_14_06_total1, half_14_06_total2, half_14_06_total3, half_14_06_total4, half_14_06_total5, half_14_06_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_14_06_total1, half_14_06_total2, half_14_06_total3, half_14_06_total4, half_14_06_total5, half_14_06_total6, parameterExponent, curveLoss, dyadicExponent]) half_14_06_hF1 half_14_06_hF2
    (half_11_06)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_14_06_total1, half_14_06_total2, half_14_06_total3, half_14_06_total4, half_14_06_total5, half_14_06_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_14_06_hx5 : SourcePowerBound
    (powerBoxCross 9 9 32 half_14_06_φ5) (16486832151/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 9) (u := 7) (t := 10)
    (D := 32) (ψ := (210344523/5000000000 : ℝ)) half_14_06_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_14_06_bounds5 l).1) (fun l => (half_14_06_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_14_06_total1, half_14_06_total2, half_14_06_total3, half_14_06_total4, half_14_06_total5, half_14_06_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_8) (half_10_06)
    (by simpa only [half_14_06_φ6, show (2:ℝ)*32=64 by norm_num] using half_14_06_hx6)
  exact h.weaken (by norm_num [half_14_06_total1, half_14_06_total2, half_14_06_total3, half_14_06_total4, half_14_06_total5, half_14_06_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_14_06_hx4 : SourcePowerBound
    (powerBoxCross 9 10 16 half_14_06_φ4) (97504946149/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 10) (u := 8) (t := 11)
    (D := 16) (ψ := (725187593/10000000000 : ℝ)) half_14_06_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_14_06_bounds4 l).1) (fun l => (half_14_06_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_14_06_total1, half_14_06_total2, half_14_06_total3, half_14_06_total4, half_14_06_total5, half_14_06_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_9) (half_11_06)
    (by simpa only [half_14_06_φ5, show (2:ℝ)*16=32 by norm_num] using half_14_06_hx5)
  exact h.weaken (by norm_num [half_14_06_total1, half_14_06_total2, half_14_06_total3, half_14_06_total4, half_14_06_total5, half_14_06_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_14_06_hx3 : SourcePowerBound
    (powerBoxCross 9 11 8 half_14_06_φ3) (117655008467/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 11) (u := 9) (t := 12)
    (D := 8) (ψ := (85304077/1000000000 : ℝ)) half_14_06_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_14_06_bounds3 l).1) (fun l => (half_14_06_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_14_06_total1, half_14_06_total2, half_14_06_total3, half_14_06_total4, half_14_06_total5, half_14_06_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_10_06) (half_12_06)
    (by simpa only [half_14_06_φ4, show (2:ℝ)*8=16 by norm_num] using half_14_06_hx4)
  exact h.weaken (by norm_num [half_14_06_total1, half_14_06_total2, half_14_06_total3, half_14_06_total4, half_14_06_total5, half_14_06_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_14_06_hx2 : SourcePowerBound
    (powerBoxCross 9 12 4 half_14_06_φ2) (71256961511/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 12) (u := 10) (t := 13)
    (D := 4) (ψ := (230259281/2500000000 : ℝ)) half_14_06_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_14_06_bounds2 l).1) (fun l => (half_14_06_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_14_06_total1, half_14_06_total2, half_14_06_total3, half_14_06_total4, half_14_06_total5, half_14_06_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_11_06) (half_13_06)
    (by simpa only [half_14_06_φ3, show (2:ℝ)*4=8 by norm_num] using half_14_06_hx3)
  exact h.weaken (by norm_num [half_14_06_total1, half_14_06_total2, half_14_06_total3, half_14_06_total4, half_14_06_total5, half_14_06_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_14_06_hx1 : SourcePowerBound
    (powerBoxCross 9 13 2 half_14_06_φ1) (172063551593/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 13) (u := 11) (t := 14)
    (D := 2) (ψ := (96558457/1000000000 : ℝ)) half_14_06_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_14_06_bounds1 l).1) (fun l => (half_14_06_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_14_06_total1, half_14_06_total2, half_14_06_total3, half_14_06_total4, half_14_06_total5, half_14_06_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_12_06) (half_14_05)
    (by simpa only [half_14_06_φ2, show (2:ℝ)*2=4 by norm_num] using half_14_06_hx2)
  exact h.weaken (by norm_num [half_14_06_total1, half_14_06_total2, half_14_06_total3, half_14_06_total4, half_14_06_total5, half_14_06_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_14_06 : AdmissibleExponent 9 28 (197127740743/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 12) (ψ := (501283783/5000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_13_06)
    (by simpa only [half_14_06_φ1] using half_14_06_hx1)
  exact admissibleExponent_mono h (by norm_num [half_14_06_total1, half_14_06_total2, half_14_06_total3, half_14_06_total4, half_14_06_total5, half_14_06_total6, parameterExponent, curveLoss, dyadicExponent])

private def half_15_06_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1023113989/10000000000 : ℝ)

private theorem half_15_06_total1 : total half_15_06_φ1=(1023113989/10000000000 : ℝ) := by
  norm_num [half_15_06_φ1,total,emptyPhi,Fin.snoc]

private theorem half_15_06_bounds1 : ∀ l,0≤half_15_06_φ1 l ∧ half_15_06_φ1 l≤1 ∧
    0≤shiftExponents 9 half_15_06_φ1 l :=
  alternate_bounds_snoc emptyPhi (1023113989/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_15_06_φ2 : Fin 2 → ℝ := Fin.snoc half_15_06_φ1 (247635923/2500000000 : ℝ)

private theorem half_15_06_total2 : total half_15_06_φ2=(2013657681/10000000000 : ℝ) := by
  change total (Fin.snoc half_15_06_φ1 (247635923/2500000000 : ℝ))=(2013657681/10000000000 : ℝ)
  rw [alternate_total_snoc,half_15_06_total1]
  norm_num

private theorem half_15_06_bounds2 : ∀ l,0≤half_15_06_φ2 l ∧ half_15_06_φ2 l≤1 ∧
    0≤shiftExponents 9 half_15_06_φ2 l :=
  alternate_bounds_snoc half_15_06_φ1 (247635923/2500000000 : ℝ) half_15_06_bounds1 (by norm_num)

private def half_15_06_φ3 : Fin 3 → ℝ := Fin.snoc half_15_06_φ2 (59460091/625000000 : ℝ)

private theorem half_15_06_total3 : total half_15_06_φ3=(2965019137/10000000000 : ℝ) := by
  change total (Fin.snoc half_15_06_φ2 (59460091/625000000 : ℝ))=(2965019137/10000000000 : ℝ)
  rw [alternate_total_snoc,half_15_06_total2]
  norm_num

private theorem half_15_06_bounds3 : ∀ l,0≤half_15_06_φ3 l ∧ half_15_06_φ3 l≤1 ∧
    0≤shiftExponents 9 half_15_06_φ3 l :=
  alternate_bounds_snoc half_15_06_φ2 (59460091/625000000 : ℝ) half_15_06_bounds2 (by norm_num)

private def half_15_06_φ4 : Fin 4 → ℝ := Fin.snoc half_15_06_φ3 (879372607/10000000000 : ℝ)

private theorem half_15_06_total4 : total half_15_06_φ4=(60068621/156250000 : ℝ) := by
  change total (Fin.snoc half_15_06_φ3 (879372607/10000000000 : ℝ))=(60068621/156250000 : ℝ)
  rw [alternate_total_snoc,half_15_06_total3]
  norm_num

private theorem half_15_06_bounds4 : ∀ l,0≤half_15_06_φ4 l ∧ half_15_06_φ4 l≤1 ∧
    0≤shiftExponents 9 half_15_06_φ4 l :=
  alternate_bounds_snoc half_15_06_φ3 (879372607/10000000000 : ℝ) half_15_06_bounds3 (by norm_num)

private def half_15_06_φ5 : Fin 5 → ℝ := Fin.snoc half_15_06_φ4 (769451031/10000000000 : ℝ)

private theorem half_15_06_total5 : total half_15_06_φ5=(184553711/400000000 : ℝ) := by
  change total (Fin.snoc half_15_06_φ4 (769451031/10000000000 : ℝ))=(184553711/400000000 : ℝ)
  rw [alternate_total_snoc,half_15_06_total4]
  norm_num

private theorem half_15_06_bounds5 : ∀ l,0≤half_15_06_φ5 l ∧ half_15_06_φ5 l≤1 ∧
    0≤shiftExponents 9 half_15_06_φ5 l :=
  alternate_bounds_snoc half_15_06_φ4 (769451031/10000000000 : ℝ) half_15_06_bounds4 (by norm_num)

private def half_15_06_φ6 : Fin 6 → ℝ := Fin.snoc half_15_06_φ5 (550383993/10000000000 : ℝ)

private theorem half_15_06_total6 : total half_15_06_φ6=(322764173/625000000 : ℝ) := by
  change total (Fin.snoc half_15_06_φ5 (550383993/10000000000 : ℝ))=(322764173/625000000 : ℝ)
  rw [alternate_total_snoc,half_15_06_total5]
  norm_num

private theorem half_15_06_bounds6 : ∀ l,0≤half_15_06_φ6 l ∧ half_15_06_φ6 l≤1 ∧
    0≤shiftExponents 9 half_15_06_φ6 l :=
  alternate_bounds_snoc half_15_06_φ5 (550383993/10000000000 : ℝ) half_15_06_bounds5 (by norm_num)

private theorem half_15_06_prefix : PrefixCondition 9 half_15_06_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_15_06_φ1, half_15_06_φ2, half_15_06_φ3, half_15_06_φ4, half_15_06_φ5, half_15_06_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_15_06_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_15_06_φ6) (594207481/78125000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_15_06_φ6
    (fun i => (half_15_06_bounds6 i).1) (fun i => (half_15_06_bounds6 i).2.1)
    (fun i => (half_15_06_bounds6 i).2.2) half_15_06_prefix
  convert h using 1 <;> norm_num [half_15_06_total1, half_15_06_total2, half_15_06_total3, half_15_06_total4, half_15_06_total5, half_15_06_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_15_06_hx6 : SourcePowerBound
    (powerBoxCross 9 9 64 half_15_06_φ6) (38761128747/5000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 9) (r := 2) (v := 0) (w := 12) (D := 64)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_15_06_φ6 (by norm_num [half_15_06_total1, half_15_06_total2, half_15_06_total3, half_15_06_total4, half_15_06_total5, half_15_06_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_15_06_total1, half_15_06_total2, half_15_06_total3, half_15_06_total4, half_15_06_total5, half_15_06_total6, parameterExponent, curveLoss, dyadicExponent]) half_15_06_hF2
    (admissibleExponent_zero 9) (half_12_06)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_15_06_total1, half_15_06_total2, half_15_06_total3, half_15_06_total4, half_15_06_total5, half_15_06_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_15_06_hx5 : SourcePowerBound
    (powerBoxCross 9 10 32 half_15_06_φ5) (17759196559/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 10) (u := 8) (t := 11)
    (D := 32) (ψ := (550383993/10000000000 : ℝ)) half_15_06_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_15_06_bounds5 l).1) (fun l => (half_15_06_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_15_06_total1, half_15_06_total2, half_15_06_total3, half_15_06_total4, half_15_06_total5, half_15_06_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_9) (half_11_06)
    (by simpa only [half_15_06_φ6, show (2:ℝ)*32=64 by norm_num] using half_15_06_hx6)
  exact h.weaken (by norm_num [half_15_06_total1, half_15_06_total2, half_15_06_total3, half_15_06_total4, half_15_06_total5, half_15_06_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_15_06_hx4 : SourcePowerBound
    (powerBoxCross 9 11 16 half_15_06_φ4) (52990502033/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 11) (u := 9) (t := 12)
    (D := 16) (ψ := (769451031/10000000000 : ℝ)) half_15_06_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_15_06_bounds4 l).1) (fun l => (half_15_06_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_15_06_total1, half_15_06_total2, half_15_06_total3, half_15_06_total4, half_15_06_total5, half_15_06_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_10_06) (half_12_06)
    (by simpa only [half_15_06_φ5, show (2:ℝ)*16=32 by norm_num] using half_15_06_hx5)
  exact h.weaken (by norm_num [half_15_06_total1, half_15_06_total2, half_15_06_total3, half_15_06_total4, half_15_06_total5, half_15_06_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_15_06_hx3 : SourcePowerBound
    (powerBoxCross 9 12 8 half_15_06_φ3) (128329631081/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 12) (u := 10) (t := 13)
    (D := 8) (ψ := (879372607/10000000000 : ℝ)) half_15_06_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_15_06_bounds3 l).1) (fun l => (half_15_06_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_15_06_total1, half_15_06_total2, half_15_06_total3, half_15_06_total4, half_15_06_total5, half_15_06_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_11_06) (half_13_06)
    (by simpa only [half_15_06_φ4, show (2:ℝ)*8=16 by norm_num] using half_15_06_hx4)
  exact h.weaken (by norm_num [half_15_06_total1, half_15_06_total2, half_15_06_total3, half_15_06_total4, half_15_06_total5, half_15_06_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_15_06_hx2 : SourcePowerBound
    (powerBoxCross 9 13 4 half_15_06_φ2) (38941830617/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 13) (u := 11) (t := 14)
    (D := 4) (ψ := (59460091/625000000 : ℝ)) half_15_06_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_15_06_bounds2 l).1) (fun l => (half_15_06_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_15_06_total1, half_15_06_total2, half_15_06_total3, half_15_06_total4, half_15_06_total5, half_15_06_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_12_06) (half_14_06)
    (by simpa only [half_15_06_φ3, show (2:ℝ)*4=8 by norm_num] using half_15_06_hx3)
  exact h.weaken (by norm_num [half_15_06_total1, half_15_06_total2, half_15_06_total3, half_15_06_total4, half_15_06_total5, half_15_06_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_15_06_hx1 : SourcePowerBound
    (powerBoxCross 9 14 2 half_15_06_φ1) (187982439819/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 14) (u := 12) (t := 15)
    (D := 2) (ψ := (247635923/2500000000 : ℝ)) half_15_06_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_15_06_bounds1 l).1) (fun l => (half_15_06_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_15_06_total1, half_15_06_total2, half_15_06_total3, half_15_06_total4, half_15_06_total5, half_15_06_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_13_06) (half_15_05)
    (by simpa only [half_15_06_φ2, show (2:ℝ)*2=4 by norm_num] using half_15_06_hx2)
  exact h.weaken (by norm_num [half_15_06_total1, half_15_06_total2, half_15_06_total3, half_15_06_total4, half_15_06_total5, half_15_06_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_15_06 : AdmissibleExponent 9 30 (107803258761/5000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 13) (ψ := (1023113989/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_14_06)
    (by simpa only [half_15_06_φ1] using half_15_06_hx1)
  exact admissibleExponent_mono h (by norm_num [half_15_06_total1, half_15_06_total2, half_15_06_total3, half_15_06_total4, half_15_06_total5, half_15_06_total6, parameterExponent, curveLoss, dyadicExponent])

private def half_16_06_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (521243733/5000000000 : ℝ)

private theorem half_16_06_total1 : total half_16_06_φ1=(521243733/5000000000 : ℝ) := by
  norm_num [half_16_06_φ1,total,emptyPhi,Fin.snoc]

private theorem half_16_06_bounds1 : ∀ l,0≤half_16_06_φ1 l ∧ half_16_06_φ1 l≤1 ∧
    0≤shiftExponents 9 half_16_06_φ1 l :=
  alternate_bounds_snoc emptyPhi (521243733/5000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_16_06_φ2 : Fin 2 → ℝ := Fin.snoc half_16_06_φ1 (1013796529/10000000000 : ℝ)

private theorem half_16_06_total2 : total half_16_06_φ2=(411256799/2000000000 : ℝ) := by
  change total (Fin.snoc half_16_06_φ1 (1013796529/10000000000 : ℝ))=(411256799/2000000000 : ℝ)
  rw [alternate_total_snoc,half_16_06_total1]
  norm_num

private theorem half_16_06_bounds2 : ∀ l,0≤half_16_06_φ2 l ∧ half_16_06_φ2 l≤1 ∧
    0≤shiftExponents 9 half_16_06_φ2 l :=
  alternate_bounds_snoc half_16_06_φ1 (1013796529/10000000000 : ℝ) half_16_06_bounds1 (by norm_num)

private def half_16_06_φ3 : Fin 3 → ℝ := Fin.snoc half_16_06_φ2 (491611911/5000000000 : ℝ)

private theorem half_16_06_total3 : total half_16_06_φ3=(3039507817/10000000000 : ℝ) := by
  change total (Fin.snoc half_16_06_φ2 (491611911/5000000000 : ℝ))=(3039507817/10000000000 : ℝ)
  rw [alternate_total_snoc,half_16_06_total2]
  norm_num

private theorem half_16_06_bounds3 : ∀ l,0≤half_16_06_φ3 l ∧ half_16_06_φ3 l≤1 ∧
    0≤shiftExponents 9 half_16_06_φ3 l :=
  alternate_bounds_snoc half_16_06_φ2 (491611911/5000000000 : ℝ) half_16_06_bounds2 (by norm_num)

private def half_16_06_φ4 : Fin 4 → ℝ := Fin.snoc half_16_06_φ3 (435030761/5000000000 : ℝ)

private theorem half_16_06_total4 : total half_16_06_φ4=(3909569339/10000000000 : ℝ) := by
  change total (Fin.snoc half_16_06_φ3 (435030761/5000000000 : ℝ))=(3909569339/10000000000 : ℝ)
  rw [alternate_total_snoc,half_16_06_total3]
  norm_num

private theorem half_16_06_bounds4 : ∀ l,0≤half_16_06_φ4 l ∧ half_16_06_φ4 l≤1 ∧
    0≤shiftExponents 9 half_16_06_φ4 l :=
  alternate_bounds_snoc half_16_06_φ3 (435030761/5000000000 : ℝ) half_16_06_bounds3 (by norm_num)

private def half_16_06_φ5 : Fin 5 → ℝ := Fin.snoc half_16_06_φ4 (95162979/1250000000 : ℝ)

private theorem half_16_06_total5 : total half_16_06_φ5=(4670873171/10000000000 : ℝ) := by
  change total (Fin.snoc half_16_06_φ4 (95162979/1250000000 : ℝ))=(4670873171/10000000000 : ℝ)
  rw [alternate_total_snoc,half_16_06_total4]
  norm_num

private theorem half_16_06_bounds5 : ∀ l,0≤half_16_06_φ5 l ∧ half_16_06_φ5 l≤1 ∧
    0≤shiftExponents 9 half_16_06_φ5 l :=
  alternate_bounds_snoc half_16_06_φ4 (95162979/1250000000 : ℝ) half_16_06_bounds4 (by norm_num)

private def half_16_06_φ6 : Fin 6 → ℝ := Fin.snoc half_16_06_φ5 (165215371/2500000000 : ℝ)

private theorem half_16_06_total6 : total half_16_06_φ6=(1066346931/2000000000 : ℝ) := by
  change total (Fin.snoc half_16_06_φ5 (165215371/2500000000 : ℝ))=(1066346931/2000000000 : ℝ)
  rw [alternate_total_snoc,half_16_06_total5]
  norm_num

private theorem half_16_06_bounds6 : ∀ l,0≤half_16_06_φ6 l ∧ half_16_06_φ6 l≤1 ∧
    0≤shiftExponents 9 half_16_06_φ6 l :=
  alternate_bounds_snoc half_16_06_φ5 (165215371/2500000000 : ℝ) half_16_06_bounds5 (by norm_num)

private theorem half_16_06_prefix : PrefixCondition 9 half_16_06_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_16_06_φ1, half_16_06_φ2, half_16_06_φ3, half_16_06_φ4, half_16_06_φ5, half_16_06_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_16_06_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_16_06_φ6) (1800959207/250000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_16_06_φ6
    (fun i => (half_16_06_bounds6 i).1) (fun i => (half_16_06_bounds6 i).2.1)
    (fun i => (half_16_06_bounds6 i).2.2) half_16_06_prefix
  convert h using 1 <;> norm_num [half_16_06_total1, half_16_06_total2, half_16_06_total3, half_16_06_total4, half_16_06_total5, half_16_06_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_16_06_hx6 : SourcePowerBound
    (powerBoxCross 9 10 64 half_16_06_φ6) (10349810401/1250000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 10) (r := 2) (v := 13) (w := 14) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_16_06_φ6 (by norm_num [half_16_06_total1, half_16_06_total2, half_16_06_total3, half_16_06_total4, half_16_06_total5, half_16_06_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_16_06_total1, half_16_06_total2, half_16_06_total3, half_16_06_total4, half_16_06_total5, half_16_06_total6, parameterExponent, curveLoss, dyadicExponent]) half_16_06_hF2
    (half_13_06) (half_14_06)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_16_06_total1, half_16_06_total2, half_16_06_total3, half_16_06_total4, half_16_06_total5, half_16_06_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_16_06_hx5 : SourcePowerBound
    (powerBoxCross 9 11 32 half_16_06_φ5) (96978374509/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 11) (u := 9) (t := 12)
    (D := 32) (ψ := (165215371/2500000000 : ℝ)) half_16_06_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_16_06_bounds5 l).1) (fun l => (half_16_06_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_16_06_total1, half_16_06_total2, half_16_06_total3, half_16_06_total4, half_16_06_total5, half_16_06_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_10_06) (half_12_06)
    (by simpa only [half_16_06_φ6, show (2:ℝ)*32=64 by norm_num] using half_16_06_hx6)
  exact h.weaken (by norm_num [half_16_06_total1, half_16_06_total2, half_16_06_total3, half_16_06_total4, half_16_06_total5, half_16_06_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_16_06_hx4 : SourcePowerBound
    (powerBoxCross 9 12 16 half_16_06_φ4) (28839076147/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 12) (u := 10) (t := 13)
    (D := 16) (ψ := (95162979/1250000000 : ℝ)) half_16_06_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_16_06_bounds4 l).1) (fun l => (half_16_06_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_16_06_total1, half_16_06_total2, half_16_06_total3, half_16_06_total4, half_16_06_total5, half_16_06_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_11_06) (half_13_06)
    (by simpa only [half_16_06_φ5, show (2:ℝ)*16=32 by norm_num] using half_16_06_hx5)
  exact h.weaken (by norm_num [half_16_06_total1, half_16_06_total2, half_16_06_total3, half_16_06_total4, half_16_06_total5, half_16_06_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_16_06_hx3 : SourcePowerBound
    (powerBoxCross 9 13 8 half_16_06_φ3) (69565566727/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 13) (u := 11) (t := 14)
    (D := 8) (ψ := (435030761/5000000000 : ℝ)) half_16_06_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_16_06_bounds3 l).1) (fun l => (half_16_06_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_16_06_total1, half_16_06_total2, half_16_06_total3, half_16_06_total4, half_16_06_total5, half_16_06_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_12_06) (half_14_06)
    (by simpa only [half_16_06_φ4, show (2:ℝ)*8=16 by norm_num] using half_16_06_hx4)
  exact h.weaken (by norm_num [half_16_06_total1, half_16_06_total2, half_16_06_total3, half_16_06_total4, half_16_06_total5, half_16_06_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_16_06_hx2 : SourcePowerBound
    (powerBoxCross 9 14 4 half_16_06_φ2) (42316643931/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 14) (u := 12) (t := 15)
    (D := 4) (ψ := (491611911/5000000000 : ℝ)) half_16_06_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_16_06_bounds2 l).1) (fun l => (half_16_06_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_16_06_total1, half_16_06_total2, half_16_06_total3, half_16_06_total4, half_16_06_total5, half_16_06_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_13_06) (half_15_06)
    (by simpa only [half_16_06_φ3, show (2:ℝ)*4=8 by norm_num] using half_16_06_hx3)
  exact h.weaken (by norm_num [half_16_06_total1, half_16_06_total2, half_16_06_total3, half_16_06_total4, half_16_06_total5, half_16_06_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_16_06_hx1 : SourcePowerBound
    (powerBoxCross 9 15 2 half_16_06_φ1) (204172295787/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 15) (u := 13) (t := 16)
    (D := 2) (ψ := (1013796529/10000000000 : ℝ)) half_16_06_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_16_06_bounds1 l).1) (fun l => (half_16_06_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_16_06_total1, half_16_06_total2, half_16_06_total3, half_16_06_total4, half_16_06_total5, half_16_06_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_14_06) (half_16_05)
    (by simpa only [half_16_06_φ2, show (2:ℝ)*2=4 by norm_num] using half_16_06_hx2)
  exact h.weaken (by norm_num [half_16_06_total1, half_16_06_total2, half_16_06_total3, half_16_06_total4, half_16_06_total5, half_16_06_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_16_06 : AdmissibleExponent 9 32 (234404432301/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 14) (ψ := (521243733/5000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_15_06)
    (by simpa only [half_16_06_φ1] using half_16_06_hx1)
  exact admissibleExponent_mono h (by norm_num [half_16_06_total1, half_16_06_total2, half_16_06_total3, half_16_06_total4, half_16_06_total5, half_16_06_total6, parameterExponent, curveLoss, dyadicExponent])

end Waring.SeedCompletionAlternate9Seeds
