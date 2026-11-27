import Waring.SeedCompletionAlternate9Steps07

noncomputable section
set_option maxHeartbeats 2000000
namespace Waring.SeedCompletionAlternate9Seeds
open SmoothMoments FirstStageTransport SeedCompletionNaturalBox
open SeedCompletionSourceBounds SeedCompletionPaddedSource SeedCompletionGeneralTerminal
open PolicyCompletionMajorPowerRanges SeedCompletionDivisorPowerScales
open PolicyCompletionSharpResidualSource

private def half_16_07_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (260285451/2500000000 : ℝ)

private theorem half_16_07_total1 : total half_16_07_φ1=(260285451/2500000000 : ℝ) := by
  norm_num [half_16_07_φ1,total,emptyPhi,Fin.snoc]

private theorem half_16_07_bounds1 : ∀ l,0≤half_16_07_φ1 l ∧ half_16_07_φ1 l≤1 ∧
    0≤shiftExponents 9 half_16_07_φ1 l :=
  alternate_bounds_snoc emptyPhi (260285451/2500000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_16_07_φ2 : Fin 2 → ℝ := Fin.snoc half_16_07_φ1 (1013940037/10000000000 : ℝ)

private theorem half_16_07_total2 : total half_16_07_φ2=(2055081841/10000000000 : ℝ) := by
  change total (Fin.snoc half_16_07_φ1 (1013940037/10000000000 : ℝ))=(2055081841/10000000000 : ℝ)
  rw [alternate_total_snoc,half_16_07_total1]
  norm_num

private theorem half_16_07_bounds2 : ∀ l,0≤half_16_07_φ2 l ∧ half_16_07_φ2 l≤1 ∧
    0≤shiftExponents 9 half_16_07_φ2 l :=
  alternate_bounds_snoc half_16_07_φ1 (1013940037/10000000000 : ℝ) half_16_07_bounds1 (by norm_num)

private def half_16_07_φ3 : Fin 3 → ℝ := Fin.snoc half_16_07_φ2 (491564289/5000000000 : ℝ)

private theorem half_16_07_total3 : total half_16_07_φ3=(3038210419/10000000000 : ℝ) := by
  change total (Fin.snoc half_16_07_φ2 (491564289/5000000000 : ℝ))=(3038210419/10000000000 : ℝ)
  rw [alternate_total_snoc,half_16_07_total2]
  norm_num

private theorem half_16_07_bounds3 : ∀ l,0≤half_16_07_φ3 l ∧ half_16_07_φ3 l≤1 ∧
    0≤shiftExponents 9 half_16_07_φ3 l :=
  alternate_bounds_snoc half_16_07_φ2 (491564289/5000000000 : ℝ) half_16_07_bounds2 (by norm_num)

private def half_16_07_φ4 : Fin 4 → ℝ := Fin.snoc half_16_07_φ3 (870223697/10000000000 : ℝ)

private theorem half_16_07_total4 : total half_16_07_φ4=(977108529/2500000000 : ℝ) := by
  change total (Fin.snoc half_16_07_φ3 (870223697/10000000000 : ℝ))=(977108529/2500000000 : ℝ)
  rw [alternate_total_snoc,half_16_07_total3]
  norm_num

private theorem half_16_07_bounds4 : ∀ l,0≤half_16_07_φ4 l ∧ half_16_07_φ4 l≤1 ∧
    0≤shiftExponents 9 half_16_07_φ4 l :=
  alternate_bounds_snoc half_16_07_φ3 (870223697/10000000000 : ℝ) half_16_07_bounds3 (by norm_num)

private def half_16_07_φ5 : Fin 5 → ℝ := Fin.snoc half_16_07_φ4 (152289147/2000000000 : ℝ)

private theorem half_16_07_total5 : total half_16_07_φ5=(4669879851/10000000000 : ℝ) := by
  change total (Fin.snoc half_16_07_φ4 (152289147/2000000000 : ℝ))=(4669879851/10000000000 : ℝ)
  rw [alternate_total_snoc,half_16_07_total4]
  norm_num

private theorem half_16_07_bounds5 : ∀ l,0≤half_16_07_φ5 l ∧ half_16_07_φ5 l≤1 ∧
    0≤shiftExponents 9 half_16_07_φ5 l :=
  alternate_bounds_snoc half_16_07_φ4 (152289147/2000000000 : ℝ) half_16_07_bounds4 (by norm_num)

private def half_16_07_φ6 : Fin 6 → ℝ := Fin.snoc half_16_07_φ5 (329806611/5000000000 : ℝ)

private theorem half_16_07_total6 : total half_16_07_φ6=(5329493073/10000000000 : ℝ) := by
  change total (Fin.snoc half_16_07_φ5 (329806611/5000000000 : ℝ))=(5329493073/10000000000 : ℝ)
  rw [alternate_total_snoc,half_16_07_total5]
  norm_num

private theorem half_16_07_bounds6 : ∀ l,0≤half_16_07_φ6 l ∧ half_16_07_φ6 l≤1 ∧
    0≤shiftExponents 9 half_16_07_φ6 l :=
  alternate_bounds_snoc half_16_07_φ5 (329806611/5000000000 : ℝ) half_16_07_bounds5 (by norm_num)

private theorem half_16_07_prefix : PrefixCondition 9 half_16_07_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_16_07_φ1, half_16_07_φ2, half_16_07_φ3, half_16_07_φ4, half_16_07_φ5, half_16_07_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_16_07_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_16_07_φ6) (9011520781/1250000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_16_07_φ6
    (fun i => (half_16_07_bounds6 i).1) (fun i => (half_16_07_bounds6 i).2.1)
    (fun i => (half_16_07_bounds6 i).2.2) half_16_07_prefix
  convert h using 1 <;> norm_num [half_16_07_total1, half_16_07_total2, half_16_07_total3, half_16_07_total4, half_16_07_total5, half_16_07_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_16_07_hx6 : SourcePowerBound
    (powerBoxCross 9 10 64 half_16_07_φ6) (82832908899/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 10) (r := 2) (v := 13) (w := 14) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_16_07_φ6 (by norm_num [half_16_07_total1, half_16_07_total2, half_16_07_total3, half_16_07_total4, half_16_07_total5, half_16_07_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_16_07_total1, half_16_07_total2, half_16_07_total3, half_16_07_total4, half_16_07_total5, half_16_07_total6, parameterExponent, curveLoss, dyadicExponent]) half_16_07_hF2
    (half_13_07) (half_14_07)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_16_07_total1, half_16_07_total2, half_16_07_total3, half_16_07_total4, half_16_07_total5, half_16_07_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_16_07_hx5 : SourcePowerBound
    (powerBoxCross 9 11 32 half_16_07_φ5) (24247917329/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 11) (u := 9) (t := 12)
    (D := 32) (ψ := (329806611/5000000000 : ℝ)) half_16_07_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_16_07_bounds5 l).1) (fun l => (half_16_07_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_16_07_total1, half_16_07_total2, half_16_07_total3, half_16_07_total4, half_16_07_total5, half_16_07_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_10_07) (half_12_07)
    (by simpa only [half_16_07_φ6, show (2:ℝ)*32=64 by norm_num] using half_16_07_hx6)
  exact h.weaken (by norm_num [half_16_07_total1, half_16_07_total2, half_16_07_total3, half_16_07_total4, half_16_07_total5, half_16_07_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_16_07_hx4 : SourcePowerBound
    (powerBoxCross 9 12 16 half_16_07_φ4) (57685679383/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 12) (u := 10) (t := 13)
    (D := 16) (ψ := (152289147/2000000000 : ℝ)) half_16_07_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_16_07_bounds4 l).1) (fun l => (half_16_07_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_16_07_total1, half_16_07_total2, half_16_07_total3, half_16_07_total4, half_16_07_total5, half_16_07_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_11_07) (half_13_07)
    (by simpa only [half_16_07_φ5, show (2:ℝ)*16=32 by norm_num] using half_16_07_hx5)
  exact h.weaken (by norm_num [half_16_07_total1, half_16_07_total2, half_16_07_total3, half_16_07_total4, half_16_07_total5, half_16_07_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_16_07_hx3 : SourcePowerBound
    (powerBoxCross 9 13 8 half_16_07_φ3) (69573043039/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 13) (u := 11) (t := 14)
    (D := 8) (ψ := (870223697/10000000000 : ℝ)) half_16_07_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_16_07_bounds3 l).1) (fun l => (half_16_07_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_16_07_total1, half_16_07_total2, half_16_07_total3, half_16_07_total4, half_16_07_total5, half_16_07_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_12_07) (half_14_07)
    (by simpa only [half_16_07_φ4, show (2:ℝ)*8=16 by norm_num] using half_16_07_hx4)
  exact h.weaken (by norm_num [half_16_07_total1, half_16_07_total2, half_16_07_total3, half_16_07_total4, half_16_07_total5, half_16_07_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_16_07_hx2 : SourcePowerBound
    (powerBoxCross 9 14 4 half_16_07_φ2) (169272841941/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 14) (u := 12) (t := 15)
    (D := 4) (ψ := (491564289/5000000000 : ℝ)) half_16_07_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_16_07_bounds2 l).1) (fun l => (half_16_07_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_16_07_total1, half_16_07_total2, half_16_07_total3, half_16_07_total4, half_16_07_total5, half_16_07_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_13_07) (half_15_07)
    (by simpa only [half_16_07_φ3, show (2:ℝ)*4=8 by norm_num] using half_16_07_hx3)
  exact h.weaken (by norm_num [half_16_07_total1, half_16_07_total2, half_16_07_total3, half_16_07_total4, half_16_07_total5, half_16_07_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_16_07_hx1 : SourcePowerBound
    (powerBoxCross 9 15 2 half_16_07_φ1) (204159847729/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 15) (u := 13) (t := 16)
    (D := 2) (ψ := (1013940037/10000000000 : ℝ)) half_16_07_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_16_07_bounds1 l).1) (fun l => (half_16_07_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_16_07_total1, half_16_07_total2, half_16_07_total3, half_16_07_total4, half_16_07_total5, half_16_07_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_14_07) (half_16_06)
    (by simpa only [half_16_07_φ2, show (2:ℝ)*2=4 by norm_num] using half_16_07_hx2)
  exact h.weaken (by norm_num [half_16_07_total1, half_16_07_total2, half_16_07_total3, half_16_07_total4, half_16_07_total5, half_16_07_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_16_07 : AdmissibleExponent 9 32 (46870592009/2000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 14) (ψ := (260285451/2500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_15_07)
    (by simpa only [half_16_07_φ1] using half_16_07_hx1)
  exact admissibleExponent_mono h (by norm_num [half_16_07_total1, half_16_07_total2, half_16_07_total3, half_16_07_total4, half_16_07_total5, half_16_07_total6, parameterExponent, curveLoss, dyadicExponent])

private def half_17_07_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1057489877/10000000000 : ℝ)

private theorem half_17_07_total1 : total half_17_07_φ1=(1057489877/10000000000 : ℝ) := by
  norm_num [half_17_07_φ1,total,emptyPhi,Fin.snoc]

private theorem half_17_07_bounds1 : ∀ l,0≤half_17_07_φ1 l ∧ half_17_07_φ1 l≤1 ∧
    0≤shiftExponents 9 half_17_07_φ1 l :=
  alternate_bounds_snoc emptyPhi (1057489877/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_17_07_φ2 : Fin 2 → ℝ := Fin.snoc half_17_07_φ1 (517982633/5000000000 : ℝ)

private theorem half_17_07_total2 : total half_17_07_φ2=(2093455143/10000000000 : ℝ) := by
  change total (Fin.snoc half_17_07_φ1 (517982633/5000000000 : ℝ))=(2093455143/10000000000 : ℝ)
  rw [alternate_total_snoc,half_17_07_total1]
  norm_num

private theorem half_17_07_bounds2 : ∀ l,0≤half_17_07_φ2 l ∧ half_17_07_φ2 l≤1 ∧
    0≤shiftExponents 9 half_17_07_φ2 l :=
  alternate_bounds_snoc half_17_07_φ1 (517982633/5000000000 : ℝ) half_17_07_bounds1 (by norm_num)

private def half_17_07_φ3 : Fin 3 → ℝ := Fin.snoc half_17_07_φ2 (494159053/5000000000 : ℝ)

private theorem half_17_07_total3 : total half_17_07_φ3=(3081773249/10000000000 : ℝ) := by
  change total (Fin.snoc half_17_07_φ2 (494159053/5000000000 : ℝ))=(3081773249/10000000000 : ℝ)
  rw [alternate_total_snoc,half_17_07_total2]
  norm_num

private theorem half_17_07_bounds3 : ∀ l,0≤half_17_07_φ3 l ∧ half_17_07_φ3 l≤1 ∧
    0≤shiftExponents 9 half_17_07_φ3 l :=
  alternate_bounds_snoc half_17_07_φ2 (494159053/5000000000 : ℝ) half_17_07_bounds2 (by norm_num)

private def half_17_07_φ4 : Fin 4 → ℝ := Fin.snoc half_17_07_φ3 (864778343/10000000000 : ℝ)

private theorem half_17_07_total4 : total half_17_07_φ4=(493318949/1250000000 : ℝ) := by
  change total (Fin.snoc half_17_07_φ3 (864778343/10000000000 : ℝ))=(493318949/1250000000 : ℝ)
  rw [alternate_total_snoc,half_17_07_total3]
  norm_num

private theorem half_17_07_bounds4 : ∀ l,0≤half_17_07_φ4 l ∧ half_17_07_φ4 l≤1 ∧
    0≤shiftExponents 9 half_17_07_φ4 l :=
  alternate_bounds_snoc half_17_07_φ3 (864778343/10000000000 : ℝ) half_17_07_bounds3 (by norm_num)

private def half_17_07_φ5 : Fin 5 → ℝ := Fin.snoc half_17_07_φ4 (15133621/200000000 : ℝ)

private theorem half_17_07_total5 : total half_17_07_φ5=(2351616321/5000000000 : ℝ) := by
  change total (Fin.snoc half_17_07_φ4 (15133621/200000000 : ℝ))=(2351616321/5000000000 : ℝ)
  rw [alternate_total_snoc,half_17_07_total4]
  norm_num

private theorem half_17_07_bounds5 : ∀ l,0≤half_17_07_φ5 l ∧ half_17_07_φ5 l≤1 ∧
    0≤shiftExponents 9 half_17_07_φ5 l :=
  alternate_bounds_snoc half_17_07_φ4 (15133621/200000000 : ℝ) half_17_07_bounds4 (by norm_num)

private def half_17_07_φ6 : Fin 6 → ℝ := Fin.snoc half_17_07_φ5 (662095919/10000000000 : ℝ)

private theorem half_17_07_total6 : total half_17_07_φ6=(5365328561/10000000000 : ℝ) := by
  change total (Fin.snoc half_17_07_φ5 (662095919/10000000000 : ℝ))=(5365328561/10000000000 : ℝ)
  rw [alternate_total_snoc,half_17_07_total5]
  norm_num

private theorem half_17_07_bounds6 : ∀ l,0≤half_17_07_φ6 l ∧ half_17_07_φ6 l≤1 ∧
    0≤shiftExponents 9 half_17_07_φ6 l :=
  alternate_bounds_snoc half_17_07_φ5 (662095919/10000000000 : ℝ) half_17_07_bounds5 (by norm_num)

private theorem half_17_07_prefix : PrefixCondition 9 half_17_07_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_17_07_φ1, half_17_07_φ2, half_17_07_φ3, half_17_07_φ4, half_17_07_φ5, half_17_07_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_17_07_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_17_07_φ6) (8904014317/1250000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_17_07_φ6
    (fun i => (half_17_07_bounds6 i).1) (fun i => (half_17_07_bounds6 i).2.1)
    (fun i => (half_17_07_bounds6 i).2.2) half_17_07_prefix
  convert h using 1 <;> norm_num [half_17_07_total1, half_17_07_total2, half_17_07_total3, half_17_07_total4, half_17_07_total5, half_17_07_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_17_07_hx6 : SourcePowerBound
    (powerBoxCross 9 11 64 half_17_07_φ6) (11324668153/1250000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 11) (r := 2) (v := 14) (w := 15) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_17_07_φ6 (by norm_num [half_17_07_total1, half_17_07_total2, half_17_07_total3, half_17_07_total4, half_17_07_total5, half_17_07_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_17_07_total1, half_17_07_total2, half_17_07_total3, half_17_07_total4, half_17_07_total5, half_17_07_total6, parameterExponent, curveLoss, dyadicExponent]) half_17_07_hF2
    (half_14_07) (half_15_07)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_17_07_total1, half_17_07_total2, half_17_07_total3, half_17_07_total4, half_17_07_total5, half_17_07_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_17_07_hx5 : SourcePowerBound
    (powerBoxCross 9 12 32 half_17_07_φ5) (105839091783/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 12) (u := 10) (t := 13)
    (D := 32) (ψ := (662095919/10000000000 : ℝ)) half_17_07_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_17_07_bounds5 l).1) (fun l => (half_17_07_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_17_07_total1, half_17_07_total2, half_17_07_total3, half_17_07_total4, half_17_07_total5, half_17_07_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_11_07) (half_13_07)
    (by simpa only [half_17_07_φ6, show (2:ℝ)*32=64 by norm_num] using half_17_07_hx6)
  exact h.weaken (by norm_num [half_17_07_total1, half_17_07_total2, half_17_07_total3, half_17_07_total4, half_17_07_total5, half_17_07_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_17_07_hx4 : SourcePowerBound
    (powerBoxCross 9 13 16 half_17_07_φ4) (62744752683/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 13) (u := 11) (t := 14)
    (D := 16) (ψ := (15133621/200000000 : ℝ)) half_17_07_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_17_07_bounds4 l).1) (fun l => (half_17_07_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_17_07_total1, half_17_07_total2, half_17_07_total3, half_17_07_total4, half_17_07_total5, half_17_07_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_12_07) (half_14_07)
    (by simpa only [half_17_07_φ5, show (2:ℝ)*16=32 by norm_num] using half_17_07_hx5)
  exact h.weaken (by norm_num [half_17_07_total1, half_17_07_total2, half_17_07_total3, half_17_07_total4, half_17_07_total5, half_17_07_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_17_07_hx3 : SourcePowerBound
    (powerBoxCross 9 14 8 half_17_07_φ3) (150792638709/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 14) (u := 12) (t := 15)
    (D := 8) (ψ := (864778343/10000000000 : ℝ)) half_17_07_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_17_07_bounds3 l).1) (fun l => (half_17_07_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_17_07_total1, half_17_07_total2, half_17_07_total3, half_17_07_total4, half_17_07_total5, half_17_07_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_13_07) (half_15_07)
    (by simpa only [half_17_07_φ4, show (2:ℝ)*8=16 by norm_num] using half_17_07_hx4)
  exact h.weaken (by norm_num [half_17_07_total1, half_17_07_total2, half_17_07_total3, half_17_07_total4, half_17_07_total5, half_17_07_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_17_07_hx2 : SourcePowerBound
    (powerBoxCross 9 15 4 half_17_07_φ2) (91505451381/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 15) (u := 13) (t := 16)
    (D := 4) (ψ := (494159053/5000000000 : ℝ)) half_17_07_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_17_07_bounds2 l).1) (fun l => (half_17_07_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_17_07_total1, half_17_07_total2, half_17_07_total3, half_17_07_total4, half_17_07_total5, half_17_07_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_14_07) (half_16_07)
    (by simpa only [half_17_07_φ3, show (2:ℝ)*4=8 by norm_num] using half_17_07_hx3)
  exact h.weaken (by norm_num [half_17_07_total1, half_17_07_total2, half_17_07_total3, half_17_07_total4, half_17_07_total5, half_17_07_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_17_07_hx1 : SourcePowerBound
    (powerBoxCross 9 16 2 half_17_07_φ1) (110313930821/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 16) (u := 14) (t := 17)
    (D := 2) (ψ := (517982633/5000000000 : ℝ)) half_17_07_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_17_07_bounds1 l).1) (fun l => (half_17_07_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_17_07_total1, half_17_07_total2, half_17_07_total3, half_17_07_total4, half_17_07_total5, half_17_07_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_15_07) (half_17_06)
    (by simpa only [half_17_07_φ2, show (2:ℝ)*2=4 by norm_num] using half_17_07_hx2)
  exact h.weaken (by norm_num [half_17_07_total1, half_17_07_total2, half_17_07_total3, half_17_07_total4, half_17_07_total5, half_17_07_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_17_07 : AdmissibleExponent 9 34 (253410047829/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 15) (ψ := (1057489877/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_16_07)
    (by simpa only [half_17_07_φ1] using half_17_07_hx1)
  exact admissibleExponent_mono h (by norm_num [half_17_07_total1, half_17_07_total2, half_17_07_total3, half_17_07_total4, half_17_07_total5, half_17_07_total6, parameterExponent, curveLoss, dyadicExponent])

private def half_18_07_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (107016011/1000000000 : ℝ)

private theorem half_18_07_total1 : total half_18_07_φ1=(107016011/1000000000 : ℝ) := by
  norm_num [half_18_07_φ1,total,emptyPhi,Fin.snoc]

private theorem half_18_07_bounds1 : ∀ l,0≤half_18_07_φ1 l ∧ half_18_07_φ1 l≤1 ∧
    0≤shiftExponents 9 half_18_07_φ1 l :=
  alternate_bounds_snoc emptyPhi (107016011/1000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_18_07_φ2 : Fin 2 → ℝ := Fin.snoc half_18_07_φ1 (105376399/1000000000 : ℝ)

private theorem half_18_07_total2 : total half_18_07_φ2=(21239241/100000000 : ℝ) := by
  change total (Fin.snoc half_18_07_φ1 (105376399/1000000000 : ℝ))=(21239241/100000000 : ℝ)
  rw [alternate_total_snoc,half_18_07_total1]
  norm_num

private theorem half_18_07_bounds2 : ∀ l,0≤half_18_07_φ2 l ∧ half_18_07_φ2 l≤1 ∧
    0≤shiftExponents 9 half_18_07_φ2 l :=
  alternate_bounds_snoc half_18_07_φ1 (105376399/1000000000 : ℝ) half_18_07_bounds1 (by norm_num)

private def half_18_07_φ3 : Fin 3 → ℝ := Fin.snoc half_18_07_φ2 (984509487/10000000000 : ℝ)

private theorem half_18_07_total3 : total half_18_07_φ3=(3108433587/10000000000 : ℝ) := by
  change total (Fin.snoc half_18_07_φ2 (984509487/10000000000 : ℝ))=(3108433587/10000000000 : ℝ)
  rw [alternate_total_snoc,half_18_07_total2]
  norm_num

private theorem half_18_07_bounds3 : ∀ l,0≤half_18_07_φ3 l ∧ half_18_07_φ3 l≤1 ∧
    0≤shiftExponents 9 half_18_07_φ3 l :=
  alternate_bounds_snoc half_18_07_φ2 (984509487/10000000000 : ℝ) half_18_07_bounds2 (by norm_num)

private def half_18_07_φ4 : Fin 4 → ℝ := Fin.snoc half_18_07_φ3 (861445801/10000000000 : ℝ)

private theorem half_18_07_total4 : total half_18_07_φ4=(992469847/2500000000 : ℝ) := by
  change total (Fin.snoc half_18_07_φ3 (861445801/10000000000 : ℝ))=(992469847/2500000000 : ℝ)
  rw [alternate_total_snoc,half_18_07_total3]
  norm_num

private theorem half_18_07_bounds4 : ∀ l,0≤half_18_07_φ4 l ∧ half_18_07_φ4 l≤1 ∧
    0≤shiftExponents 9 half_18_07_φ4 l :=
  alternate_bounds_snoc half_18_07_φ3 (861445801/10000000000 : ℝ) half_18_07_bounds3 (by norm_num)

private def half_18_07_φ5 : Fin 5 → ℝ := Fin.snoc half_18_07_φ4 (188441269/2500000000 : ℝ)

private theorem half_18_07_total5 : total half_18_07_φ5=(295227779/625000000 : ℝ) := by
  change total (Fin.snoc half_18_07_φ4 (188441269/2500000000 : ℝ))=(295227779/625000000 : ℝ)
  rw [alternate_total_snoc,half_18_07_total4]
  norm_num

private theorem half_18_07_bounds5 : ∀ l,0≤half_18_07_φ5 l ∧ half_18_07_φ5 l≤1 ∧
    0≤shiftExponents 9 half_18_07_φ5 l :=
  alternate_bounds_snoc half_18_07_φ4 (188441269/2500000000 : ℝ) half_18_07_bounds4 (by norm_num)

private def half_18_07_φ6 : Fin 6 → ℝ := Fin.snoc half_18_07_φ5 (659544441/10000000000 : ℝ)

private theorem half_18_07_total6 : total half_18_07_φ6=(1076637781/2000000000 : ℝ) := by
  change total (Fin.snoc half_18_07_φ5 (659544441/10000000000 : ℝ))=(1076637781/2000000000 : ℝ)
  rw [alternate_total_snoc,half_18_07_total5]
  norm_num

private theorem half_18_07_bounds6 : ∀ l,0≤half_18_07_φ6 l ∧ half_18_07_φ6 l≤1 ∧
    0≤shiftExponents 9 half_18_07_φ6 l :=
  alternate_bounds_snoc half_18_07_φ5 (659544441/10000000000 : ℝ) half_18_07_bounds5 (by norm_num)

private theorem half_18_07_prefix : PrefixCondition 9 half_18_07_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_18_07_φ1, half_18_07_φ2, half_18_07_φ3, half_18_07_φ4, half_18_07_φ5, half_18_07_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_18_07_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_18_07_φ6) (1770086657/250000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_18_07_φ6
    (fun i => (half_18_07_bounds6 i).1) (fun i => (half_18_07_bounds6 i).2.1)
    (fun i => (half_18_07_bounds6 i).2.2) half_18_07_prefix
  convert h using 1 <;> norm_num [half_18_07_total1, half_18_07_total2, half_18_07_total3, half_18_07_total4, half_18_07_total5, half_18_07_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_18_07_hx6 : SourcePowerBound
    (powerBoxCross 9 12 64 half_18_07_φ6) (98848117527/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 12) (r := 2) (v := 0) (w := 16) (D := 64)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_18_07_φ6 (by norm_num [half_18_07_total1, half_18_07_total2, half_18_07_total3, half_18_07_total4, half_18_07_total5, half_18_07_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_18_07_total1, half_18_07_total2, half_18_07_total3, half_18_07_total4, half_18_07_total5, half_18_07_total6, parameterExponent, curveLoss, dyadicExponent]) half_18_07_hF2
    (admissibleExponent_zero 9) (half_16_07)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_18_07_total1, half_18_07_total2, half_18_07_total3, half_18_07_total4, half_18_07_total5, half_18_07_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_18_07_hx5 : SourcePowerBound
    (powerBoxCross 9 13 32 half_18_07_φ5) (14388829203/1250000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 13) (u := 11) (t := 14)
    (D := 32) (ψ := (659544441/10000000000 : ℝ)) half_18_07_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_18_07_bounds5 l).1) (fun l => (half_18_07_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_18_07_total1, half_18_07_total2, half_18_07_total3, half_18_07_total4, half_18_07_total5, half_18_07_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_12_07) (half_14_07)
    (by simpa only [half_18_07_φ6, show (2:ℝ)*32=64 by norm_num] using half_18_07_hx6)
  exact h.weaken (by norm_num [half_18_07_total1, half_18_07_total2, half_18_07_total3, half_18_07_total4, half_18_07_total5, half_18_07_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_18_07_hx4 : SourcePowerBound
    (powerBoxCross 9 14 16 half_18_07_φ4) (136091027223/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 14) (u := 12) (t := 15)
    (D := 16) (ψ := (188441269/2500000000 : ℝ)) half_18_07_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_18_07_bounds4 l).1) (fun l => (half_18_07_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_18_07_total1, half_18_07_total2, half_18_07_total3, half_18_07_total4, half_18_07_total5, half_18_07_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_13_07) (half_15_07)
    (by simpa only [half_18_07_φ5, show (2:ℝ)*16=32 by norm_num] using half_18_07_hx5)
  exact h.weaken (by norm_num [half_18_07_total1, half_18_07_total2, half_18_07_total3, half_18_07_total4, half_18_07_total5, half_18_07_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_18_07_hx3 : SourcePowerBound
    (powerBoxCross 9 15 8 half_18_07_φ3) (162994246989/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 15) (u := 13) (t := 16)
    (D := 8) (ψ := (861445801/10000000000 : ℝ)) half_18_07_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_18_07_bounds3 l).1) (fun l => (half_18_07_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_18_07_total1, half_18_07_total2, half_18_07_total3, half_18_07_total4, half_18_07_total5, half_18_07_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_14_07) (half_16_07)
    (by simpa only [half_18_07_φ4, show (2:ℝ)*8=16 by norm_num] using half_18_07_hx4)
  exact h.weaken (by norm_num [half_18_07_total1, half_18_07_total2, half_18_07_total3, half_18_07_total4, half_18_07_total5, half_18_07_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_18_07_hx2 : SourcePowerBound
    (powerBoxCross 9 16 4 half_18_07_φ2) (197070653183/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 16) (u := 14) (t := 17)
    (D := 4) (ψ := (984509487/10000000000 : ℝ)) half_18_07_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_18_07_bounds2 l).1) (fun l => (half_18_07_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_18_07_total1, half_18_07_total2, half_18_07_total3, half_18_07_total4, half_18_07_total5, half_18_07_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_15_07) (half_17_07)
    (by simpa only [half_18_07_φ3, show (2:ℝ)*4=8 by norm_num] using half_18_07_hx3)
  exact h.weaken (by norm_num [half_18_07_total1, half_18_07_total2, half_18_07_total3, half_18_07_total4, half_18_07_total5, half_18_07_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_18_07_hx1 : SourcePowerBound
    (powerBoxCross 9 17 2 half_18_07_φ1) (118680637739/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 17) (u := 15) (t := 18)
    (D := 2) (ψ := (105376399/1000000000 : ℝ)) half_18_07_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_18_07_bounds1 l).1) (fun l => (half_18_07_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_18_07_total1, half_18_07_total2, half_18_07_total3, half_18_07_total4, half_18_07_total5, half_18_07_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_16_07) (half_18_06)
    (by simpa only [half_18_07_φ2, show (2:ℝ)*2=4 by norm_num] using half_18_07_hx2)
  exact h.weaken (by norm_num [half_18_07_total1, half_18_07_total2, half_18_07_total3, half_18_07_total4, half_18_07_total5, half_18_07_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_18_07 : AdmissibleExponent 9 36 (68169139777/2500000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 16) (ψ := (107016011/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_17_07)
    (by simpa only [half_18_07_φ1] using half_18_07_hx1)
  exact admissibleExponent_mono h (by norm_num [half_18_07_total1, half_18_07_total2, half_18_07_total3, half_18_07_total4, half_18_07_total5, half_18_07_total6, parameterExponent, curveLoss, dyadicExponent])

private def half_19_07_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (108022813/1000000000 : ℝ)

private theorem half_19_07_total1 : total half_19_07_φ1=(108022813/1000000000 : ℝ) := by
  norm_num [half_19_07_φ1,total,emptyPhi,Fin.snoc]

private theorem half_19_07_bounds1 : ∀ l,0≤half_19_07_φ1 l ∧ half_19_07_φ1 l≤1 ∧
    0≤shiftExponents 9 half_19_07_φ1 l :=
  alternate_bounds_snoc emptyPhi (108022813/1000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_19_07_φ2 : Fin 2 → ℝ := Fin.snoc half_19_07_φ1 (533840767/5000000000 : ℝ)

private theorem half_19_07_total2 : total half_19_07_φ2=(67122177/312500000 : ℝ) := by
  change total (Fin.snoc half_19_07_φ1 (533840767/5000000000 : ℝ))=(67122177/312500000 : ℝ)
  rw [alternate_total_snoc,half_19_07_total1]
  norm_num

private theorem half_19_07_bounds2 : ∀ l,0≤half_19_07_φ2 l ∧ half_19_07_φ2 l≤1 ∧
    0≤shiftExponents 9 half_19_07_φ2 l :=
  alternate_bounds_snoc half_19_07_φ1 (533840767/5000000000 : ℝ) half_19_07_bounds1 (by norm_num)

private def half_19_07_φ3 : Fin 3 → ℝ := Fin.snoc half_19_07_φ2 (981511291/10000000000 : ℝ)

private theorem half_19_07_total3 : total half_19_07_φ3=(625884191/2000000000 : ℝ) := by
  change total (Fin.snoc half_19_07_φ2 (981511291/10000000000 : ℝ))=(625884191/2000000000 : ℝ)
  rw [alternate_total_snoc,half_19_07_total2]
  norm_num

private theorem half_19_07_bounds3 : ∀ l,0≤half_19_07_φ3 l ∧ half_19_07_φ3 l≤1 ∧
    0≤shiftExponents 9 half_19_07_φ3 l :=
  alternate_bounds_snoc half_19_07_φ2 (981511291/10000000000 : ℝ) half_19_07_bounds2 (by norm_num)

private def half_19_07_φ4 : Fin 4 → ℝ := Fin.snoc half_19_07_φ3 (42941119/500000000 : ℝ)

private theorem half_19_07_total4 : total half_19_07_φ4=(797648667/2000000000 : ℝ) := by
  change total (Fin.snoc half_19_07_φ3 (42941119/500000000 : ℝ))=(797648667/2000000000 : ℝ)
  rw [alternate_total_snoc,half_19_07_total3]
  norm_num

private theorem half_19_07_bounds4 : ∀ l,0≤half_19_07_φ4 l ∧ half_19_07_φ4 l≤1 ∧
    0≤shiftExponents 9 half_19_07_φ4 l :=
  alternate_bounds_snoc half_19_07_φ3 (42941119/500000000 : ℝ) half_19_07_bounds3 (by norm_num)

private def half_19_07_φ5 : Fin 5 → ℝ := Fin.snoc half_19_07_φ4 (375734791/5000000000 : ℝ)

private theorem half_19_07_total5 : total half_19_07_φ5=(4739712917/10000000000 : ℝ) := by
  change total (Fin.snoc half_19_07_φ4 (375734791/5000000000 : ℝ))=(4739712917/10000000000 : ℝ)
  rw [alternate_total_snoc,half_19_07_total4]
  norm_num

private theorem half_19_07_bounds5 : ∀ l,0≤half_19_07_φ5 l ∧ half_19_07_φ5 l≤1 ∧
    0≤shiftExponents 9 half_19_07_φ5 l :=
  alternate_bounds_snoc half_19_07_φ4 (375734791/5000000000 : ℝ) half_19_07_bounds4 (by norm_num)

private def half_19_07_φ6 : Fin 6 → ℝ := Fin.snoc half_19_07_φ5 (164383971/2500000000 : ℝ)

private theorem half_19_07_total6 : total half_19_07_φ6=(5397248801/10000000000 : ℝ) := by
  change total (Fin.snoc half_19_07_φ5 (164383971/2500000000 : ℝ))=(5397248801/10000000000 : ℝ)
  rw [alternate_total_snoc,half_19_07_total5]
  norm_num

private theorem half_19_07_bounds6 : ∀ l,0≤half_19_07_φ6 l ∧ half_19_07_φ6 l≤1 ∧
    0≤shiftExponents 9 half_19_07_φ6 l :=
  alternate_bounds_snoc half_19_07_φ5 (164383971/2500000000 : ℝ) half_19_07_bounds5 (by norm_num)

private theorem half_19_07_prefix : PrefixCondition 9 half_19_07_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_19_07_φ1, half_19_07_φ2, half_19_07_φ3, half_19_07_φ4, half_19_07_φ5, half_19_07_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_19_07_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_19_07_φ6) (8808253597/1250000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_19_07_φ6
    (fun i => (half_19_07_bounds6 i).1) (fun i => (half_19_07_bounds6 i).2.1)
    (fun i => (half_19_07_bounds6 i).2.2) half_19_07_prefix
  convert h using 1 <;> norm_num [half_19_07_total1, half_19_07_total2, half_19_07_total3, half_19_07_total4, half_19_07_total5, half_19_07_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_19_07_hx6 : SourcePowerBound
    (powerBoxCross 9 13 64 half_19_07_φ6) (107312236253/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 13) (r := 2) (v := 17) (w := 18) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_19_07_φ6 (by norm_num [half_19_07_total1, half_19_07_total2, half_19_07_total3, half_19_07_total4, half_19_07_total5, half_19_07_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_19_07_total1, half_19_07_total2, half_19_07_total3, half_19_07_total4, half_19_07_total5, half_19_07_total6, parameterExponent, curveLoss, dyadicExponent]) half_19_07_hF2
    (half_17_07) (half_18_07)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_19_07_total1, half_19_07_total2, half_19_07_total3, half_19_07_total4, half_19_07_total5, half_19_07_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_19_07_hx5 : SourcePowerBound
    (powerBoxCross 9 14 32 half_19_07_φ5) (124612296779/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 14) (u := 12) (t := 15)
    (D := 32) (ψ := (164383971/2500000000 : ℝ)) half_19_07_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_19_07_bounds5 l).1) (fun l => (half_19_07_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_19_07_total1, half_19_07_total2, half_19_07_total3, half_19_07_total4, half_19_07_total5, half_19_07_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_13_07) (half_15_07)
    (by simpa only [half_19_07_φ6, show (2:ℝ)*32=64 by norm_num] using half_19_07_hx6)
  exact h.weaken (by norm_num [half_19_07_total1, half_19_07_total2, half_19_07_total3, half_19_07_total4, half_19_07_total5, half_19_07_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_19_07_hx4 : SourcePowerBound
    (powerBoxCross 9 15 16 half_19_07_φ4) (146941662883/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 15) (u := 13) (t := 16)
    (D := 16) (ψ := (375734791/5000000000 : ℝ)) half_19_07_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_19_07_bounds4 l).1) (fun l => (half_19_07_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_19_07_total1, half_19_07_total2, half_19_07_total3, half_19_07_total4, half_19_07_total5, half_19_07_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_14_07) (half_16_07)
    (by simpa only [half_19_07_φ5, show (2:ℝ)*16=32 by norm_num] using half_19_07_hx5)
  exact h.weaken (by norm_num [half_19_07_total1, half_19_07_total2, half_19_07_total3, half_19_07_total4, half_19_07_total5, half_19_07_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_19_07_hx3 : SourcePowerBound
    (powerBoxCross 9 16 8 half_19_07_φ3) (5483117511/312500000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 16) (u := 14) (t := 17)
    (D := 8) (ψ := (42941119/500000000 : ℝ)) half_19_07_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_19_07_bounds3 l).1) (fun l => (half_19_07_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_19_07_total1, half_19_07_total2, half_19_07_total3, half_19_07_total4, half_19_07_total5, half_19_07_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_15_07) (half_17_07)
    (by simpa only [half_19_07_φ4, show (2:ℝ)*8=16 by norm_num] using half_19_07_hx4)
  exact h.weaken (by norm_num [half_19_07_total1, half_19_07_total2, half_19_07_total3, half_19_07_total4, half_19_07_total5, half_19_07_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_19_07_hx2 : SourcePowerBound
    (powerBoxCross 9 17 4 half_19_07_φ2) (105702857631/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 17) (u := 15) (t := 18)
    (D := 4) (ψ := (981511291/10000000000 : ℝ)) half_19_07_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_19_07_bounds2 l).1) (fun l => (half_19_07_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_19_07_total1, half_19_07_total2, half_19_07_total3, half_19_07_total4, half_19_07_total5, half_19_07_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_16_07) (half_18_07)
    (by simpa only [half_19_07_φ3, show (2:ℝ)*4=8 by norm_num] using half_19_07_hx3)
  exact h.weaken (by norm_num [half_19_07_total1, half_19_07_total2, half_19_07_total3, half_19_07_total4, half_19_07_total5, half_19_07_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_19_07_hx1 : SourcePowerBound
    (powerBoxCross 9 18 2 half_19_07_φ1) (254301498287/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 18) (u := 16) (t := 19)
    (D := 2) (ψ := (533840767/5000000000 : ℝ)) half_19_07_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_19_07_bounds1 l).1) (fun l => (half_19_07_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_19_07_total1, half_19_07_total2, half_19_07_total3, half_19_07_total4, half_19_07_total5, half_19_07_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_17_07) (half_19_06)
    (by simpa only [half_19_07_φ2, show (2:ℝ)*2=4 by norm_num] using half_19_07_hx2)
  exact h.weaken (by norm_num [half_19_07_total1, half_19_07_total2, half_19_07_total3, half_19_07_total4, half_19_07_total5, half_19_07_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_19_07 : AdmissibleExponent 9 38 (292109482837/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 17) (ψ := (108022813/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_18_07)
    (by simpa only [half_19_07_φ1] using half_19_07_hx1)
  exact admissibleExponent_mono h (by norm_num [half_19_07_total1, half_19_07_total2, half_19_07_total3, half_19_07_total4, half_19_07_total5, half_19_07_total6, parameterExponent, curveLoss, dyadicExponent])

private def half_20_07_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1088150093/10000000000 : ℝ)

private theorem half_20_07_total1 : total half_20_07_φ1=(1088150093/10000000000 : ℝ) := by
  norm_num [half_20_07_φ1,total,emptyPhi,Fin.snoc]

private theorem half_20_07_bounds1 : ∀ l,0≤half_20_07_φ1 l ∧ half_20_07_φ1 l≤1 ∧
    0≤shiftExponents 9 half_20_07_φ1 l :=
  alternate_bounds_snoc emptyPhi (1088150093/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_20_07_φ2 : Fin 2 → ℝ := Fin.snoc half_20_07_φ1 (1078650191/10000000000 : ℝ)

private theorem half_20_07_total2 : total half_20_07_φ2=(541700071/2500000000 : ℝ) := by
  change total (Fin.snoc half_20_07_φ1 (1078650191/10000000000 : ℝ))=(541700071/2500000000 : ℝ)
  rw [alternate_total_snoc,half_20_07_total1]
  norm_num

private theorem half_20_07_bounds2 : ∀ l,0≤half_20_07_φ2 l ∧ half_20_07_φ2 l≤1 ∧
    0≤shiftExponents 9 half_20_07_φ2 l :=
  alternate_bounds_snoc half_20_07_φ1 (1078650191/10000000000 : ℝ) half_20_07_bounds1 (by norm_num)

private def half_20_07_φ3 : Fin 3 → ℝ := Fin.snoc half_20_07_φ2 (244787491/2500000000 : ℝ)

private theorem half_20_07_total3 : total half_20_07_φ3=(393243781/1250000000 : ℝ) := by
  change total (Fin.snoc half_20_07_φ2 (244787491/2500000000 : ℝ))=(393243781/1250000000 : ℝ)
  rw [alternate_total_snoc,half_20_07_total2]
  norm_num

private theorem half_20_07_bounds3 : ∀ l,0≤half_20_07_φ3 l ∧ half_20_07_φ3 l≤1 ∧
    0≤shiftExponents 9 half_20_07_φ3 l :=
  alternate_bounds_snoc half_20_07_φ2 (244787491/2500000000 : ℝ) half_20_07_bounds2 (by norm_num)

private def half_20_07_φ4 : Fin 4 → ℝ := Fin.snoc half_20_07_φ3 (428378109/5000000000 : ℝ)

private theorem half_20_07_total4 : total half_20_07_φ4=(2001353233/5000000000 : ℝ) := by
  change total (Fin.snoc half_20_07_φ3 (428378109/5000000000 : ℝ))=(2001353233/5000000000 : ℝ)
  rw [alternate_total_snoc,half_20_07_total3]
  norm_num

private theorem half_20_07_bounds4 : ∀ l,0≤half_20_07_φ4 l ∧ half_20_07_φ4 l≤1 ∧
    0≤shiftExponents 9 half_20_07_φ4 l :=
  alternate_bounds_snoc half_20_07_φ3 (428378109/5000000000 : ℝ) half_20_07_bounds3 (by norm_num)

private def half_20_07_φ5 : Fin 5 → ℝ := Fin.snoc half_20_07_φ4 (749661691/10000000000 : ℝ)

private theorem half_20_07_total5 : total half_20_07_φ5=(4752368157/10000000000 : ℝ) := by
  change total (Fin.snoc half_20_07_φ4 (749661691/10000000000 : ℝ))=(4752368157/10000000000 : ℝ)
  rw [alternate_total_snoc,half_20_07_total4]
  norm_num

private theorem half_20_07_bounds5 : ∀ l,0≤half_20_07_φ5 l ∧ half_20_07_φ5 l≤1 ∧
    0≤shiftExponents 9 half_20_07_φ5 l :=
  alternate_bounds_snoc half_20_07_φ4 (749661691/10000000000 : ℝ) half_20_07_bounds4 (by norm_num)

private def half_20_07_φ6 : Fin 6 → ℝ := Fin.snoc half_20_07_φ5 (32797699/500000000 : ℝ)

private theorem half_20_07_total6 : total half_20_07_φ6=(5408322137/10000000000 : ℝ) := by
  change total (Fin.snoc half_20_07_φ5 (32797699/500000000 : ℝ))=(5408322137/10000000000 : ℝ)
  rw [alternate_total_snoc,half_20_07_total5]
  norm_num

private theorem half_20_07_bounds6 : ∀ l,0≤half_20_07_φ6 l ∧ half_20_07_φ6 l≤1 ∧
    0≤shiftExponents 9 half_20_07_φ6 l :=
  alternate_bounds_snoc half_20_07_φ5 (32797699/500000000 : ℝ) half_20_07_bounds5 (by norm_num)

private theorem half_20_07_prefix : PrefixCondition 9 half_20_07_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_20_07_φ1, half_20_07_φ2, half_20_07_φ3, half_20_07_φ4, half_20_07_φ5, half_20_07_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_20_07_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_20_07_φ6) (8775033589/1250000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_20_07_φ6
    (fun i => (half_20_07_bounds6 i).1) (fun i => (half_20_07_bounds6 i).2.1)
    (fun i => (half_20_07_bounds6 i).2.2) half_20_07_prefix
  convert h using 1 <;> norm_num [half_20_07_total1, half_20_07_total2, half_20_07_total3, half_20_07_total4, half_20_07_total5, half_20_07_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_20_07_hx6 : SourcePowerBound
    (powerBoxCross 9 14 64 half_20_07_φ6) (22639604/1953125 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 14) (r := 2) (v := 18) (w := 19) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_20_07_φ6 (by norm_num [half_20_07_total1, half_20_07_total2, half_20_07_total3, half_20_07_total4, half_20_07_total5, half_20_07_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_20_07_total1, half_20_07_total2, half_20_07_total3, half_20_07_total4, half_20_07_total5, half_20_07_total6, parameterExponent, curveLoss, dyadicExponent]) half_20_07_hF2
    (half_18_07) (half_19_07)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_20_07_total1, half_20_07_total2, half_20_07_total3, half_20_07_total4, half_20_07_total5, half_20_07_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_07_hx5 : SourcePowerBound
    (powerBoxCross 9 15 32 half_20_07_φ5) (33573298781/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 15) (u := 13) (t := 16)
    (D := 32) (ψ := (32797699/500000000 : ℝ)) half_20_07_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_07_bounds5 l).1) (fun l => (half_20_07_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_07_total1, half_20_07_total2, half_20_07_total3, half_20_07_total4, half_20_07_total5, half_20_07_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_14_07) (half_16_07)
    (by simpa only [half_20_07_φ6, show (2:ℝ)*32=64 by norm_num] using half_20_07_hx6)
  exact h.weaken (by norm_num [half_20_07_total1, half_20_07_total2, half_20_07_total3, half_20_07_total4, half_20_07_total5, half_20_07_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_07_hx4 : SourcePowerBound
    (powerBoxCross 9 16 16 half_20_07_φ4) (157994588283/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 16) (u := 14) (t := 17)
    (D := 16) (ψ := (749661691/10000000000 : ℝ)) half_20_07_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_07_bounds4 l).1) (fun l => (half_20_07_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_07_total1, half_20_07_total2, half_20_07_total3, half_20_07_total4, half_20_07_total5, half_20_07_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_15_07) (half_17_07)
    (by simpa only [half_20_07_φ5, show (2:ℝ)*16=32 by norm_num] using half_20_07_hx5)
  exact h.weaken (by norm_num [half_20_07_total1, half_20_07_total2, half_20_07_total3, half_20_07_total4, half_20_07_total5, half_20_07_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_07_hx3 : SourcePowerBound
    (powerBoxCross 9 17 8 half_20_07_φ3) (94070074823/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 17) (u := 15) (t := 18)
    (D := 8) (ψ := (428378109/5000000000 : ℝ)) half_20_07_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_07_bounds3 l).1) (fun l => (half_20_07_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_07_total1, half_20_07_total2, half_20_07_total3, half_20_07_total4, half_20_07_total5, half_20_07_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_16_07) (half_18_07)
    (by simpa only [half_20_07_φ4, show (2:ℝ)*8=16 by norm_num] using half_20_07_hx4)
  exact h.weaken (by norm_num [half_20_07_total1, half_20_07_total2, half_20_07_total3, half_20_07_total4, half_20_07_total5, half_20_07_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_07_hx2 : SourcePowerBound
    (powerBoxCross 9 18 4 half_20_07_φ2) (225966443993/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 18) (u := 16) (t := 19)
    (D := 4) (ψ := (244787491/2500000000 : ℝ)) half_20_07_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_07_bounds2 l).1) (fun l => (half_20_07_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_07_total1, half_20_07_total2, half_20_07_total3, half_20_07_total4, half_20_07_total5, half_20_07_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_17_07) (half_19_07)
    (by simpa only [half_20_07_φ3, show (2:ℝ)*4=8 by norm_num] using half_20_07_hx3)
  exact h.weaken (by norm_num [half_20_07_total1, half_20_07_total2, half_20_07_total3, half_20_07_total4, half_20_07_total5, half_20_07_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_07_hx1 : SourcePowerBound
    (powerBoxCross 9 19 2 half_20_07_φ1) (67852934211/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 19) (u := 17) (t := 20)
    (D := 2) (ψ := (1078650191/10000000000 : ℝ)) half_20_07_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_07_bounds1 l).1) (fun l => (half_20_07_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_07_total1, half_20_07_total2, half_20_07_total3, half_20_07_total4, half_20_07_total5, half_20_07_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_18_07) (half_20_06)
    (by simpa only [half_20_07_φ2, show (2:ℝ)*2=4 by norm_num] using half_20_07_hx2)
  exact h.weaken (by norm_num [half_20_07_total1, half_20_07_total2, half_20_07_total3, half_20_07_total4, half_20_07_total5, half_20_07_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_20_07 : AdmissibleExponent 9 40 (62334658057/2000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 18) (ψ := (1088150093/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_19_07)
    (by simpa only [half_20_07_φ1] using half_20_07_hx1)
  exact admissibleExponent_mono h (by norm_num [half_20_07_total1, half_20_07_total2, half_20_07_total3, half_20_07_total4, half_20_07_total5, half_20_07_total6, parameterExponent, curveLoss, dyadicExponent])

private def half_21_07_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1094581423/10000000000 : ℝ)

private theorem half_21_07_total1 : total half_21_07_φ1=(1094581423/10000000000 : ℝ) := by
  norm_num [half_21_07_φ1,total,emptyPhi,Fin.snoc]

private theorem half_21_07_bounds1 : ∀ l,0≤half_21_07_φ1 l ∧ half_21_07_φ1 l≤1 ∧
    0≤shiftExponents 9 half_21_07_φ1 l :=
  alternate_bounds_snoc emptyPhi (1094581423/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_21_07_φ2 : Fin 2 → ℝ := Fin.snoc half_21_07_φ1 (8697857/80000000 : ℝ)

private theorem half_21_07_total2 : total half_21_07_φ2=(545453387/2500000000 : ℝ) := by
  change total (Fin.snoc half_21_07_φ1 (8697857/80000000 : ℝ))=(545453387/2500000000 : ℝ)
  rw [alternate_total_snoc,half_21_07_total1]
  norm_num

private theorem half_21_07_bounds2 : ∀ l,0≤half_21_07_φ2 l ∧ half_21_07_φ2 l≤1 ∧
    0≤shiftExponents 9 half_21_07_φ2 l :=
  alternate_bounds_snoc half_21_07_φ1 (8697857/80000000 : ℝ) half_21_07_bounds1 (by norm_num)

private def half_21_07_φ3 : Fin 3 → ℝ := Fin.snoc half_21_07_φ2 (488636653/5000000000 : ℝ)

private theorem half_21_07_total3 : total half_21_07_φ3=(1579543427/5000000000 : ℝ) := by
  change total (Fin.snoc half_21_07_φ2 (488636653/5000000000 : ℝ))=(1579543427/5000000000 : ℝ)
  rw [alternate_total_snoc,half_21_07_total2]
  norm_num

private theorem half_21_07_bounds3 : ∀ l,0≤half_21_07_φ3 l ∧ half_21_07_φ3 l≤1 ∧
    0≤shiftExponents 9 half_21_07_φ3 l :=
  alternate_bounds_snoc half_21_07_φ2 (488636653/5000000000 : ℝ) half_21_07_bounds2 (by norm_num)

private def half_21_07_φ4 : Fin 4 → ℝ := Fin.snoc half_21_07_φ3 (855114143/10000000000 : ℝ)

private theorem half_21_07_total4 : total half_21_07_φ4=(4014200997/10000000000 : ℝ) := by
  change total (Fin.snoc half_21_07_φ3 (855114143/10000000000 : ℝ))=(4014200997/10000000000 : ℝ)
  rw [alternate_total_snoc,half_21_07_total3]
  norm_num

private theorem half_21_07_bounds4 : ∀ l,0≤half_21_07_φ4 l ∧ half_21_07_φ4 l≤1 ∧
    0≤shiftExponents 9 half_21_07_φ4 l :=
  alternate_bounds_snoc half_21_07_φ3 (855114143/10000000000 : ℝ) half_21_07_bounds3 (by norm_num)

private def half_21_07_φ5 : Fin 5 → ℝ := Fin.snoc half_21_07_φ4 (5985799/80000000 : ℝ)

private theorem half_21_07_total5 : total half_21_07_φ5=(297651617/625000000 : ℝ) := by
  change total (Fin.snoc half_21_07_φ4 (5985799/80000000 : ℝ))=(297651617/625000000 : ℝ)
  rw [alternate_total_snoc,half_21_07_total4]
  norm_num

private theorem half_21_07_bounds5 : ∀ l,0≤half_21_07_φ5 l ∧ half_21_07_φ5 l≤1 ∧
    0≤shiftExponents 9 half_21_07_φ5 l :=
  alternate_bounds_snoc half_21_07_φ4 (5985799/80000000 : ℝ) half_21_07_bounds4 (by norm_num)

private def half_21_07_φ6 : Fin 6 → ℝ := Fin.snoc half_21_07_φ5 (130939353/2000000000 : ℝ)

private theorem half_21_07_total6 : total half_21_07_φ6=(5417122637/10000000000 : ℝ) := by
  change total (Fin.snoc half_21_07_φ5 (130939353/2000000000 : ℝ))=(5417122637/10000000000 : ℝ)
  rw [alternate_total_snoc,half_21_07_total5]
  norm_num

private theorem half_21_07_bounds6 : ∀ l,0≤half_21_07_φ6 l ∧ half_21_07_φ6 l≤1 ∧
    0≤shiftExponents 9 half_21_07_φ6 l :=
  alternate_bounds_snoc half_21_07_φ5 (130939353/2000000000 : ℝ) half_21_07_bounds5 (by norm_num)

private theorem half_21_07_prefix : PrefixCondition 9 half_21_07_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_21_07_φ1, half_21_07_φ2, half_21_07_φ3, half_21_07_φ4, half_21_07_φ5, half_21_07_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_21_07_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_21_07_φ6) (8748632089/1250000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_21_07_φ6
    (fun i => (half_21_07_bounds6 i).1) (fun i => (half_21_07_bounds6 i).2.1)
    (fun i => (half_21_07_bounds6 i).2.2) half_21_07_prefix
  convert h using 1 <;> norm_num [half_21_07_total1, half_21_07_total2, half_21_07_total3, half_21_07_total4, half_21_07_total5, half_21_07_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_21_07_hx6 : SourcePowerBound
    (powerBoxCross 9 15 64 half_21_07_φ6) (124624299181/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 15) (r := 2) (v := 0) (w := 20) (D := 64)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_21_07_φ6 (by norm_num [half_21_07_total1, half_21_07_total2, half_21_07_total3, half_21_07_total4, half_21_07_total5, half_21_07_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_21_07_total1, half_21_07_total2, half_21_07_total3, half_21_07_total4, half_21_07_total5, half_21_07_total6, parameterExponent, curveLoss, dyadicExponent]) half_21_07_hF2
    (admissibleExponent_zero 9) (half_20_07)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_21_07_total1, half_21_07_total2, half_21_07_total3, half_21_07_total4, half_21_07_total5, half_21_07_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_21_07_hx5 : SourcePowerBound
    (powerBoxCross 9 16 32 half_21_07_φ5) (14411824471/1000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 16) (u := 14) (t := 17)
    (D := 32) (ψ := (130939353/2000000000 : ℝ)) half_21_07_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_21_07_bounds5 l).1) (fun l => (half_21_07_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_21_07_total1, half_21_07_total2, half_21_07_total3, half_21_07_total4, half_21_07_total5, half_21_07_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_15_07) (half_17_07)
    (by simpa only [half_21_07_φ6, show (2:ℝ)*32=64 by norm_num] using half_21_07_hx6)
  exact h.weaken (by norm_num [half_21_07_total1, half_21_07_total2, half_21_07_total3, half_21_07_total4, half_21_07_total5, half_21_07_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_21_07_hx4 : SourcePowerBound
    (powerBoxCross 9 17 16 half_21_07_φ4) (169209157713/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 17) (u := 15) (t := 18)
    (D := 16) (ψ := (5985799/80000000 : ℝ)) half_21_07_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_21_07_bounds4 l).1) (fun l => (half_21_07_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_21_07_total1, half_21_07_total2, half_21_07_total3, half_21_07_total4, half_21_07_total5, half_21_07_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_16_07) (half_18_07)
    (by simpa only [half_21_07_φ5, show (2:ℝ)*16=32 by norm_num] using half_21_07_hx5)
  exact h.weaken (by norm_num [half_21_07_total1, half_21_07_total2, half_21_07_total3, half_21_07_total4, half_21_07_total5, half_21_07_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_21_07_hx3 : SourcePowerBound
    (powerBoxCross 9 18 8 half_21_07_φ3) (200992394861/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 18) (u := 16) (t := 19)
    (D := 8) (ψ := (855114143/10000000000 : ℝ)) half_21_07_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_21_07_bounds3 l).1) (fun l => (half_21_07_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_21_07_total1, half_21_07_total2, half_21_07_total3, half_21_07_total4, half_21_07_total5, half_21_07_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_17_07) (half_19_07)
    (by simpa only [half_21_07_φ4, show (2:ℝ)*8=16 by norm_num] using half_21_07_hx4)
  exact h.weaken (by norm_num [half_21_07_total1, half_21_07_total2, half_21_07_total3, half_21_07_total4, half_21_07_total5, half_21_07_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_21_07_hx2 : SourcePowerBound
    (powerBoxCross 9 19 4 half_21_07_φ2) (30088402609/1250000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 19) (u := 17) (t := 20)
    (D := 4) (ψ := (488636653/5000000000 : ℝ)) half_21_07_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_21_07_bounds2 l).1) (fun l => (half_21_07_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_21_07_total1, half_21_07_total2, half_21_07_total3, half_21_07_total4, half_21_07_total5, half_21_07_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_18_07) (half_20_07)
    (by simpa only [half_21_07_φ3, show (2:ℝ)*4=8 by norm_num] using half_21_07_hx3)
  exact h.weaken (by norm_num [half_21_07_total1, half_21_07_total2, half_21_07_total3, half_21_07_total4, half_21_07_total5, half_21_07_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_21_07_hx1 : SourcePowerBound
    (powerBoxCross 9 20 2 half_21_07_φ1) (144326346177/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 20) (u := 18) (t := 21)
    (D := 2) (ψ := (8697857/80000000 : ℝ)) half_21_07_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_21_07_bounds1 l).1) (fun l => (half_21_07_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_21_07_total1, half_21_07_total2, half_21_07_total3, half_21_07_total4, half_21_07_total5, half_21_07_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_19_07) (half_21_06)
    (by simpa only [half_21_07_φ2, show (2:ℝ)*2=4 by norm_num] using half_21_07_hx2)
  exact h.weaken (by norm_num [half_21_07_total1, half_21_07_total2, half_21_07_total3, half_21_07_total4, half_21_07_total5, half_21_07_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_21_07 : AdmissibleExponent 9 42 (331341367851/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 19) (ψ := (1094581423/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_20_07)
    (by simpa only [half_21_07_φ1] using half_21_07_hx1)
  exact admissibleExponent_mono h (by norm_num [half_21_07_total1, half_21_07_total2, half_21_07_total3, half_21_07_total4, half_21_07_total5, half_21_07_total6, parameterExponent, curveLoss, dyadicExponent])

private def half_22_07_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (220038341/2000000000 : ℝ)

private theorem half_22_07_total1 : total half_22_07_φ1=(220038341/2000000000 : ℝ) := by
  norm_num [half_22_07_φ1,total,emptyPhi,Fin.snoc]

private theorem half_22_07_bounds1 : ∀ l,0≤half_22_07_φ1 l ∧ half_22_07_φ1 l≤1 ∧
    0≤shiftExponents 9 half_22_07_φ1 l :=
  alternate_bounds_snoc emptyPhi (220038341/2000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_22_07_φ2 : Fin 2 → ℝ := Fin.snoc half_22_07_φ1 (547065573/5000000000 : ℝ)

private theorem half_22_07_total2 : total half_22_07_φ2=(2194322851/10000000000 : ℝ) := by
  change total (Fin.snoc half_22_07_φ1 (547065573/5000000000 : ℝ))=(2194322851/10000000000 : ℝ)
  rw [alternate_total_snoc,half_22_07_total1]
  norm_num

private theorem half_22_07_bounds2 : ∀ l,0≤half_22_07_φ2 l ∧ half_22_07_φ2 l≤1 ∧
    0≤shiftExponents 9 half_22_07_φ2 l :=
  alternate_bounds_snoc half_22_07_φ1 (547065573/5000000000 : ℝ) half_22_07_bounds1 (by norm_num)

private def half_22_07_φ3 : Fin 3 → ℝ := Fin.snoc half_22_07_φ2 (975709643/10000000000 : ℝ)

private theorem half_22_07_total3 : total half_22_07_φ3=(1585016247/5000000000 : ℝ) := by
  change total (Fin.snoc half_22_07_φ2 (975709643/10000000000 : ℝ))=(1585016247/5000000000 : ℝ)
  rw [alternate_total_snoc,half_22_07_total2]
  norm_num

private theorem half_22_07_bounds3 : ∀ l,0≤half_22_07_φ3 l ∧ half_22_07_φ3 l≤1 ∧
    0≤shiftExponents 9 half_22_07_φ3 l :=
  alternate_bounds_snoc half_22_07_φ2 (975709643/10000000000 : ℝ) half_22_07_bounds2 (by norm_num)

private def half_22_07_φ4 : Fin 4 → ℝ := Fin.snoc half_22_07_φ3 (426872969/5000000000 : ℝ)

private theorem half_22_07_total4 : total half_22_07_φ4=(31435769/78125000 : ℝ) := by
  change total (Fin.snoc half_22_07_φ3 (426872969/5000000000 : ℝ))=(31435769/78125000 : ℝ)
  rw [alternate_total_snoc,half_22_07_total3]
  norm_num

private theorem half_22_07_bounds4 : ∀ l,0≤half_22_07_φ4 l ∧ half_22_07_φ4 l≤1 ∧
    0≤shiftExponents 9 half_22_07_φ4 l :=
  alternate_bounds_snoc half_22_07_φ3 (426872969/5000000000 : ℝ) half_22_07_bounds3 (by norm_num)

private def half_22_07_φ5 : Fin 5 → ℝ := Fin.snoc half_22_07_φ4 (149405539/2000000000 : ℝ)

private theorem half_22_07_total5 : total half_22_07_φ5=(4770806127/10000000000 : ℝ) := by
  change total (Fin.snoc half_22_07_φ4 (149405539/2000000000 : ℝ))=(4770806127/10000000000 : ℝ)
  rw [alternate_total_snoc,half_22_07_total4]
  norm_num

private theorem half_22_07_bounds5 : ∀ l,0≤half_22_07_φ5 l ∧ half_22_07_φ5 l≤1 ∧
    0≤shiftExponents 9 half_22_07_φ5 l :=
  alternate_bounds_snoc half_22_07_φ4 (149405539/2000000000 : ℝ) half_22_07_bounds4 (by norm_num)

private def half_22_07_φ6 : Fin 6 → ℝ := Fin.snoc half_22_07_φ5 (653649233/10000000000 : ℝ)

private theorem half_22_07_total6 : total half_22_07_φ6=(16951423/31250000 : ℝ) := by
  change total (Fin.snoc half_22_07_φ5 (653649233/10000000000 : ℝ))=(16951423/31250000 : ℝ)
  rw [alternate_total_snoc,half_22_07_total5]
  norm_num

private theorem half_22_07_bounds6 : ∀ l,0≤half_22_07_φ6 l ∧ half_22_07_φ6 l≤1 ∧
    0≤shiftExponents 9 half_22_07_φ6 l :=
  alternate_bounds_snoc half_22_07_φ5 (653649233/10000000000 : ℝ) half_22_07_bounds5 (by norm_num)

private theorem half_22_07_prefix : PrefixCondition 9 half_22_07_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_22_07_φ1, half_22_07_φ2, half_22_07_φ3, half_22_07_φ4, half_22_07_φ5, half_22_07_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_22_07_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_22_07_φ6) (27270731/3906250 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_22_07_φ6
    (fun i => (half_22_07_bounds6 i).1) (fun i => (half_22_07_bounds6 i).2.1)
    (fun i => (half_22_07_bounds6 i).2.2) half_22_07_prefix
  convert h using 1 <;> norm_num [half_22_07_total1, half_22_07_total2, half_22_07_total3, half_22_07_total4, half_22_07_total5, half_22_07_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_22_07_hx6 : SourcePowerBound
    (powerBoxCross 9 16 64 half_22_07_φ6) (133426024083/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 16) (r := 2) (v := 21) (w := 22) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_22_07_φ6 (by norm_num [half_22_07_total1, half_22_07_total2, half_22_07_total3, half_22_07_total4, half_22_07_total5, half_22_07_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_22_07_total1, half_22_07_total2, half_22_07_total3, half_22_07_total4, half_22_07_total5, half_22_07_total6, parameterExponent, curveLoss, dyadicExponent]) half_22_07_hF2
    (half_21_07) (half_22_06)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_22_07_total1, half_22_07_total2, half_22_07_total3, half_22_07_total4, half_22_07_total5, half_22_07_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_22_07_hx5 : SourcePowerBound
    (powerBoxCross 9 17 32 half_22_07_φ5) (30811056051/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 17) (u := 15) (t := 18)
    (D := 32) (ψ := (653649233/10000000000 : ℝ)) half_22_07_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_22_07_bounds5 l).1) (fun l => (half_22_07_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_22_07_total1, half_22_07_total2, half_22_07_total3, half_22_07_total4, half_22_07_total5, half_22_07_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_16_07) (half_18_07)
    (by simpa only [half_22_07_φ6, show (2:ℝ)*32=64 by norm_num] using half_22_07_hx6)
  exact h.weaken (by norm_num [half_22_07_total1, half_22_07_total2, half_22_07_total3, half_22_07_total4, half_22_07_total5, half_22_07_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_22_07_hx4 : SourcePowerBound
    (powerBoxCross 9 18 16 half_22_07_φ4) (36108806589/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 18) (u := 16) (t := 19)
    (D := 16) (ψ := (149405539/2000000000 : ℝ)) half_22_07_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_22_07_bounds4 l).1) (fun l => (half_22_07_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_22_07_total1, half_22_07_total2, half_22_07_total3, half_22_07_total4, half_22_07_total5, half_22_07_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_17_07) (half_19_07)
    (by simpa only [half_22_07_φ5, show (2:ℝ)*16=32 by norm_num] using half_22_07_hx5)
  exact h.weaken (by norm_num [half_22_07_total1, half_22_07_total2, half_22_07_total3, half_22_07_total4, half_22_07_total5, half_22_07_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_22_07_hx3 : SourcePowerBound
    (powerBoxCross 9 19 8 half_22_07_φ3) (213968362669/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 19) (u := 17) (t := 20)
    (D := 8) (ψ := (426872969/5000000000 : ℝ)) half_22_07_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_22_07_bounds3 l).1) (fun l => (half_22_07_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_22_07_total1, half_22_07_total2, half_22_07_total3, half_22_07_total4, half_22_07_total5, half_22_07_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_18_07) (half_20_07)
    (by simpa only [half_22_07_φ4, show (2:ℝ)*8=16 by norm_num] using half_22_07_hx4)
  exact h.weaken (by norm_num [half_22_07_total1, half_22_07_total2, half_22_07_total3, half_22_07_total4, half_22_07_total5, half_22_07_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_22_07_hx2 : SourcePowerBound
    (powerBoxCross 9 20 4 half_22_07_φ2) (7986709547/312500000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 20) (u := 18) (t := 21)
    (D := 4) (ψ := (975709643/10000000000 : ℝ)) half_22_07_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_22_07_bounds2 l).1) (fun l => (half_22_07_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_22_07_total1, half_22_07_total2, half_22_07_total3, half_22_07_total4, half_22_07_total5, half_22_07_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_19_07) (half_21_07)
    (by simpa only [half_22_07_φ3, show (2:ℝ)*4=8 by norm_num] using half_22_07_hx3)
  exact h.weaken (by norm_num [half_22_07_total1, half_22_07_total2, half_22_07_total3, half_22_07_total4, half_22_07_total5, half_22_07_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_22_07_hx1 : SourcePowerBound
    (powerBoxCross 9 21 2 half_22_07_φ1) (305987657117/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 21) (u := 19) (t := 22)
    (D := 2) (ψ := (547065573/5000000000 : ℝ)) half_22_07_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_22_07_bounds1 l).1) (fun l => (half_22_07_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_22_07_total1, half_22_07_total2, half_22_07_total3, half_22_07_total4, half_22_07_total5, half_22_07_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_20_07) (half_22_06)
    (by simpa only [half_22_07_φ2, show (2:ℝ)*2=4 by norm_num] using half_22_07_hx2)
  exact h.weaken (by norm_num [half_22_07_total1, half_22_07_total2, half_22_07_total3, half_22_07_total4, half_22_07_total5, half_22_07_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_22_07 : AdmissibleExponent 9 44 (175547758511/5000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 20) (ψ := (220038341/2000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_21_07)
    (by simpa only [half_22_07_φ1] using half_22_07_hx1)
  exact admissibleExponent_mono h (by norm_num [half_22_07_total1, half_22_07_total2, half_22_07_total3, half_22_07_total4, half_22_07_total5, half_22_07_total6, parameterExponent, curveLoss, dyadicExponent])

private def half_10_08_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (440302049/5000000000 : ℝ)

private theorem half_10_08_total1 : total half_10_08_φ1=(440302049/5000000000 : ℝ) := by
  norm_num [half_10_08_φ1,total,emptyPhi,Fin.snoc]

private theorem half_10_08_bounds1 : ∀ l,0≤half_10_08_φ1 l ∧ half_10_08_φ1 l≤1 ∧
    0≤shiftExponents 9 half_10_08_φ1 l :=
  alternate_bounds_snoc emptyPhi (440302049/5000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_10_08_φ2 : Fin 2 → ℝ := Fin.snoc half_10_08_φ1 (821569237/10000000000 : ℝ)

private theorem half_10_08_total2 : total half_10_08_φ2=(340434667/2000000000 : ℝ) := by
  change total (Fin.snoc half_10_08_φ1 (821569237/10000000000 : ℝ))=(340434667/2000000000 : ℝ)
  rw [alternate_total_snoc,half_10_08_total1]
  norm_num

private theorem half_10_08_bounds2 : ∀ l,0≤half_10_08_φ2 l ∧ half_10_08_φ2 l≤1 ∧
    0≤shiftExponents 9 half_10_08_φ2 l :=
  alternate_bounds_snoc half_10_08_φ1 (821569237/10000000000 : ℝ) half_10_08_bounds1 (by norm_num)

private def half_10_08_φ3 : Fin 3 → ℝ := Fin.snoc half_10_08_φ2 (358525489/5000000000 : ℝ)

private theorem half_10_08_total3 : total half_10_08_φ3=(2419224313/10000000000 : ℝ) := by
  change total (Fin.snoc half_10_08_φ2 (358525489/5000000000 : ℝ))=(2419224313/10000000000 : ℝ)
  rw [alternate_total_snoc,half_10_08_total2]
  norm_num

private theorem half_10_08_bounds3 : ∀ l,0≤half_10_08_φ3 l ∧ half_10_08_φ3 l≤1 ∧
    0≤shiftExponents 9 half_10_08_φ3 l :=
  alternate_bounds_snoc half_10_08_φ2 (358525489/5000000000 : ℝ) half_10_08_bounds2 (by norm_num)

private def half_10_08_φ4 : Fin 4 → ℝ := Fin.snoc half_10_08_φ3 (450223701/10000000000 : ℝ)

private theorem half_10_08_total4 : total half_10_08_φ4=(1434724007/5000000000 : ℝ) := by
  change total (Fin.snoc half_10_08_φ3 (450223701/10000000000 : ℝ))=(1434724007/5000000000 : ℝ)
  rw [alternate_total_snoc,half_10_08_total3]
  norm_num

private theorem half_10_08_bounds4 : ∀ l,0≤half_10_08_φ4 l ∧ half_10_08_φ4 l≤1 ∧
    0≤shiftExponents 9 half_10_08_φ4 l :=
  alternate_bounds_snoc half_10_08_φ3 (450223701/10000000000 : ℝ) half_10_08_bounds3 (by norm_num)

private theorem half_10_08_prefix : PrefixCondition 9 half_10_08_φ4 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_10_08_φ1, half_10_08_φ2, half_10_08_φ3, half_10_08_φ4, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_10_08_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 16 half_10_08_φ4) (4445827979/625000000 : ℝ) := by
  have h := padded_dyadic_divisor_power (k := 9) (j := 4) (r := 0) (n := 1) (D := 16)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_10_08_φ4
    (fun i => (half_10_08_bounds4 i).1) (fun i => (half_10_08_bounds4 i).2.1)
    (fun i => (half_10_08_bounds4 i).2.2) half_10_08_prefix
  convert h using 1 <;> norm_num [half_10_08_total1, half_10_08_total2, half_10_08_total3, half_10_08_total4, parameterExponent, curveLoss, dyadicExponent]

private theorem half_10_08_hx4 : SourcePowerBound
    (powerBoxCross 9 6 16 half_10_08_φ4) (69144287477/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 6) (r := 2) (v := 0) (w := 8) (D := 16)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_10_08_φ4 (by norm_num [half_10_08_total1, half_10_08_total2, half_10_08_total3, half_10_08_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_10_08_total1, half_10_08_total2, half_10_08_total3, half_10_08_total4, parameterExponent, curveLoss, dyadicExponent]) half_10_08_hF2
    (admissibleExponent_zero 9) (SeedCompletionHigher9SimpleSeeds.degree9_half_8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_10_08_total1, half_10_08_total2, half_10_08_total3, half_10_08_total4, parameterExponent, curveLoss, dyadicExponent])

private theorem half_10_08_hx3 : SourcePowerBound
    (powerBoxCross 9 7 8 half_10_08_φ3) (15754816999/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 7) (u := 5) (t := 8)
    (D := 8) (ψ := (450223701/10000000000 : ℝ)) half_10_08_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_10_08_bounds3 l).1) (fun l => (half_10_08_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_10_08_total1, half_10_08_total2, half_10_08_total3, half_10_08_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionNinthSecondSeeds.ninth_half_6) (SeedCompletionHigher9SimpleSeeds.degree9_half_8)
    (by simpa only [half_10_08_φ4, show (2:ℝ)*8=16 by norm_num] using half_10_08_hx4)
  exact h.weaken (by norm_num [half_10_08_total1, half_10_08_total2, half_10_08_total3, half_10_08_total4, parameterExponent, curveLoss, dyadicExponent])

private theorem half_10_08_hx2 : SourcePowerBound
    (powerBoxCross 9 8 4 half_10_08_φ2) (93468458017/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 8) (u := 6) (t := 9)
    (D := 4) (ψ := (358525489/5000000000 : ℝ)) half_10_08_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_10_08_bounds2 l).1) (fun l => (half_10_08_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_10_08_total1, half_10_08_total2, half_10_08_total3, half_10_08_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionNinthSecondSeeds.ninth_half_7) (SeedCompletionHigher9SimpleSeeds.degree9_half_9)
    (by simpa only [half_10_08_φ3, show (2:ℝ)*4=8 by norm_num] using half_10_08_hx3)
  exact h.weaken (by norm_num [half_10_08_total1, half_10_08_total2, half_10_08_total3, half_10_08_total4, parameterExponent, curveLoss, dyadicExponent])

private theorem half_10_08_hx1 : SourcePowerBound
    (powerBoxCross 9 9 2 half_10_08_φ1) (112493496453/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 9) (u := 7) (t := 10)
    (D := 2) (ψ := (821569237/10000000000 : ℝ)) half_10_08_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_10_08_bounds1 l).1) (fun l => (half_10_08_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_10_08_total1, half_10_08_total2, half_10_08_total3, half_10_08_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_8) (half_10_07)
    (by simpa only [half_10_08_φ2, show (2:ℝ)*2=4 by norm_num] using half_10_08_hx2)
  exact h.weaken (by norm_num [half_10_08_total1, half_10_08_total2, half_10_08_total3, half_10_08_total4, parameterExponent, curveLoss, dyadicExponent])

theorem half_10_08 : AdmissibleExponent 9 20 (127463766119/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 8) (ψ := (440302049/5000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (SeedCompletionHigher9SimpleSeeds.degree9_half_9)
    (by simpa only [half_10_08_φ1] using half_10_08_hx1)
  exact admissibleExponent_mono h (by norm_num [half_10_08_total1, half_10_08_total2, half_10_08_total3, half_10_08_total4, parameterExponent, curveLoss, dyadicExponent])

private def half_11_08_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (228983807/2500000000 : ℝ)

private theorem half_11_08_total1 : total half_11_08_φ1=(228983807/2500000000 : ℝ) := by
  norm_num [half_11_08_φ1,total,emptyPhi,Fin.snoc]

private theorem half_11_08_bounds1 : ∀ l,0≤half_11_08_φ1 l ∧ half_11_08_φ1 l≤1 ∧
    0≤shiftExponents 9 half_11_08_φ1 l :=
  alternate_bounds_snoc emptyPhi (228983807/2500000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_11_08_φ2 : Fin 2 → ℝ := Fin.snoc half_11_08_φ1 (865420767/10000000000 : ℝ)

private theorem half_11_08_total2 : total half_11_08_φ2=(356271199/2000000000 : ℝ) := by
  change total (Fin.snoc half_11_08_φ1 (865420767/10000000000 : ℝ))=(356271199/2000000000 : ℝ)
  rw [alternate_total_snoc,half_11_08_total1]
  norm_num

private theorem half_11_08_bounds2 : ∀ l,0≤half_11_08_φ2 l ∧ half_11_08_φ2 l≤1 ∧
    0≤shiftExponents 9 half_11_08_φ2 l :=
  alternate_bounds_snoc half_11_08_φ1 (865420767/10000000000 : ℝ) half_11_08_bounds1 (by norm_num)

private def half_11_08_φ3 : Fin 3 → ℝ := Fin.snoc half_11_08_φ2 (1261001/16000000 : ℝ)

private theorem half_11_08_total3 : total half_11_08_φ3=(128474081/500000000 : ℝ) := by
  change total (Fin.snoc half_11_08_φ2 (1261001/16000000 : ℝ))=(128474081/500000000 : ℝ)
  rw [alternate_total_snoc,half_11_08_total2]
  norm_num

private theorem half_11_08_bounds3 : ∀ l,0≤half_11_08_φ3 l ∧ half_11_08_φ3 l≤1 ∧
    0≤shiftExponents 9 half_11_08_φ3 l :=
  alternate_bounds_snoc half_11_08_φ2 (1261001/16000000 : ℝ) half_11_08_bounds2 (by norm_num)

private def half_11_08_φ4 : Fin 4 → ℝ := Fin.snoc half_11_08_φ3 (624794129/10000000000 : ℝ)

private theorem half_11_08_total4 : total half_11_08_φ4=(3194275749/10000000000 : ℝ) := by
  change total (Fin.snoc half_11_08_φ3 (624794129/10000000000 : ℝ))=(3194275749/10000000000 : ℝ)
  rw [alternate_total_snoc,half_11_08_total3]
  norm_num

private theorem half_11_08_bounds4 : ∀ l,0≤half_11_08_φ4 l ∧ half_11_08_φ4 l≤1 ∧
    0≤shiftExponents 9 half_11_08_φ4 l :=
  alternate_bounds_snoc half_11_08_φ3 (624794129/10000000000 : ℝ) half_11_08_bounds3 (by norm_num)

private theorem half_11_08_prefix : PrefixCondition 9 half_11_08_φ4 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_11_08_φ1, half_11_08_φ2, half_11_08_φ3, half_11_08_φ4, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_11_08_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 16 half_11_08_φ4) (7917172753/1250000000 : ℝ) := by
  have h := padded_dyadic_divisor_power (k := 9) (j := 4) (r := 0) (n := 1) (D := 16)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_11_08_φ4
    (fun i => (half_11_08_bounds4 i).1) (fun i => (half_11_08_bounds4 i).2.1)
    (fun i => (half_11_08_bounds4 i).2.2) half_11_08_prefix
  convert h using 1 <;> norm_num [half_11_08_total1, half_11_08_total2, half_11_08_total3, half_11_08_total4, parameterExponent, curveLoss, dyadicExponent]

private theorem half_11_08_hx4 : SourcePowerBound
    (powerBoxCross 9 7 16 half_11_08_φ4) (9429728327/1250000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 7) (r := 2) (v := 9) (w := 10) (D := 16)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_11_08_φ4 (by norm_num [half_11_08_total1, half_11_08_total2, half_11_08_total3, half_11_08_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_11_08_total1, half_11_08_total2, half_11_08_total3, half_11_08_total4, parameterExponent, curveLoss, dyadicExponent]) half_11_08_hF2
    (SeedCompletionHigher9SimpleSeeds.degree9_half_9) (half_10_08)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_11_08_total1, half_11_08_total2, half_11_08_total3, half_11_08_total4, parameterExponent, curveLoss, dyadicExponent])

private theorem half_11_08_hx3 : SourcePowerBound
    (powerBoxCross 9 8 8 half_11_08_φ3) (10987429221/1250000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 8) (u := 6) (t := 9)
    (D := 8) (ψ := (624794129/10000000000 : ℝ)) half_11_08_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_11_08_bounds3 l).1) (fun l => (half_11_08_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_11_08_total1, half_11_08_total2, half_11_08_total3, half_11_08_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionNinthSecondSeeds.ninth_half_7) (SeedCompletionHigher9SimpleSeeds.degree9_half_9)
    (by simpa only [half_11_08_φ4, show (2:ℝ)*8=16 by norm_num] using half_11_08_hx4)
  exact h.weaken (by norm_num [half_11_08_total1, half_11_08_total2, half_11_08_total3, half_11_08_total4, parameterExponent, curveLoss, dyadicExponent])

private theorem half_11_08_hx2 : SourcePowerBound
    (powerBoxCross 9 9 4 half_11_08_φ2) (21022840191/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 9) (u := 7) (t := 10)
    (D := 4) (ψ := (1261001/16000000 : ℝ)) half_11_08_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_11_08_bounds2 l).1) (fun l => (half_11_08_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_11_08_total1, half_11_08_total2, half_11_08_total3, half_11_08_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_8) (half_10_08)
    (by simpa only [half_11_08_φ3, show (2:ℝ)*4=8 by norm_num] using half_11_08_hx3)
  exact h.weaken (by norm_num [half_11_08_total1, half_11_08_total2, half_11_08_total3, half_11_08_total4, parameterExponent, curveLoss, dyadicExponent])

private theorem half_11_08_hx1 : SourcePowerBound
    (powerBoxCross 9 10 2 half_11_08_φ1) (63352422993/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 10) (u := 8) (t := 11)
    (D := 2) (ψ := (865420767/10000000000 : ℝ)) half_11_08_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_11_08_bounds1 l).1) (fun l => (half_11_08_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_11_08_total1, half_11_08_total2, half_11_08_total3, half_11_08_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_9) (half_11_07)
    (by simpa only [half_11_08_φ2, show (2:ℝ)*2=4 by norm_num] using half_11_08_hx2)
  exact h.weaken (by norm_num [half_11_08_total1, half_11_08_total2, half_11_08_total3, half_11_08_total4, parameterExponent, curveLoss, dyadicExponent])

theorem half_11_08 : AdmissibleExponent 9 22 (72053807659/5000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 9) (ψ := (228983807/2500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_10_08)
    (by simpa only [half_11_08_φ1] using half_11_08_hx1)
  exact admissibleExponent_mono h (by norm_num [half_11_08_total1, half_11_08_total2, half_11_08_total3, half_11_08_total4, parameterExponent, curveLoss, dyadicExponent])

private def half_12_08_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (947322639/10000000000 : ℝ)

private theorem half_12_08_total1 : total half_12_08_φ1=(947322639/10000000000 : ℝ) := by
  norm_num [half_12_08_φ1,total,emptyPhi,Fin.snoc]

private theorem half_12_08_bounds1 : ∀ l,0≤half_12_08_φ1 l ∧ half_12_08_φ1 l≤1 ∧
    0≤shiftExponents 9 half_12_08_φ1 l :=
  alternate_bounds_snoc emptyPhi (947322639/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_12_08_φ2 : Fin 2 → ℝ := Fin.snoc half_12_08_φ1 (451627691/5000000000 : ℝ)

private theorem half_12_08_total2 : total half_12_08_φ2=(1850578021/10000000000 : ℝ) := by
  change total (Fin.snoc half_12_08_φ1 (451627691/5000000000 : ℝ))=(1850578021/10000000000 : ℝ)
  rw [alternate_total_snoc,half_12_08_total1]
  norm_num

private theorem half_12_08_bounds2 : ∀ l,0≤half_12_08_φ2 l ∧ half_12_08_φ2 l≤1 ∧
    0≤shiftExponents 9 half_12_08_φ2 l :=
  alternate_bounds_snoc half_12_08_φ1 (451627691/5000000000 : ℝ) half_12_08_bounds1 (by norm_num)

private def half_12_08_φ3 : Fin 3 → ℝ := Fin.snoc half_12_08_φ2 (840753963/10000000000 : ℝ)

private theorem half_12_08_total3 : total half_12_08_φ3=(168208249/625000000 : ℝ) := by
  change total (Fin.snoc half_12_08_φ2 (840753963/10000000000 : ℝ))=(168208249/625000000 : ℝ)
  rw [alternate_total_snoc,half_12_08_total2]
  norm_num

private theorem half_12_08_bounds3 : ∀ l,0≤half_12_08_φ3 l ∧ half_12_08_φ3 l≤1 ∧
    0≤shiftExponents 9 half_12_08_φ3 l :=
  alternate_bounds_snoc half_12_08_φ2 (840753963/10000000000 : ℝ) half_12_08_bounds2 (by norm_num)

private def half_12_08_φ4 : Fin 4 → ℝ := Fin.snoc half_12_08_φ3 (363998863/5000000000 : ℝ)

private theorem half_12_08_total4 : total half_12_08_φ4=(341932971/1000000000 : ℝ) := by
  change total (Fin.snoc half_12_08_φ3 (363998863/5000000000 : ℝ))=(341932971/1000000000 : ℝ)
  rw [alternate_total_snoc,half_12_08_total3]
  norm_num

private theorem half_12_08_bounds4 : ∀ l,0≤half_12_08_φ4 l ∧ half_12_08_φ4 l≤1 ∧
    0≤shiftExponents 9 half_12_08_φ4 l :=
  alternate_bounds_snoc half_12_08_φ3 (363998863/5000000000 : ℝ) half_12_08_bounds3 (by norm_num)

private def half_12_08_φ5 : Fin 5 → ℝ := Fin.snoc half_12_08_φ4 (112605913/2500000000 : ℝ)

private theorem half_12_08_total5 : total half_12_08_φ5=(1934876681/5000000000 : ℝ) := by
  change total (Fin.snoc half_12_08_φ4 (112605913/2500000000 : ℝ))=(1934876681/5000000000 : ℝ)
  rw [alternate_total_snoc,half_12_08_total4]
  norm_num

private theorem half_12_08_bounds5 : ∀ l,0≤half_12_08_φ5 l ∧ half_12_08_φ5 l≤1 ∧
    0≤shiftExponents 9 half_12_08_φ5 l :=
  alternate_bounds_snoc half_12_08_φ4 (112605913/2500000000 : ℝ) half_12_08_bounds4 (by norm_num)

private theorem half_12_08_prefix : PrefixCondition 9 half_12_08_φ5 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_12_08_φ1, half_12_08_φ2, half_12_08_φ3, half_12_08_φ4, half_12_08_φ5, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_12_08_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 32 half_12_08_φ5) (4820369957/625000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_12_08_φ5
    (fun i => (half_12_08_bounds5 i).1) (fun i => (half_12_08_bounds5 i).2.1)
    (fun i => (half_12_08_bounds5 i).2.2) half_12_08_prefix
  convert h using 1 <;> norm_num [half_12_08_total1, half_12_08_total2, half_12_08_total3, half_12_08_total4, half_12_08_total5, parameterExponent, curveLoss, dyadicExponent]

private theorem half_12_08_hx5 : SourcePowerBound
    (powerBoxCross 9 7 32 half_12_08_φ5) (18242308101/2500000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 7) (r := 2) (v := 9) (w := 10) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_12_08_φ5 (by norm_num [half_12_08_total1, half_12_08_total2, half_12_08_total3, half_12_08_total4, half_12_08_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_12_08_total1, half_12_08_total2, half_12_08_total3, half_12_08_total4, half_12_08_total5, parameterExponent, curveLoss, dyadicExponent]) half_12_08_hF2
    (SeedCompletionHigher9SimpleSeeds.degree9_half_9) (half_10_08)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_12_08_total1, half_12_08_total2, half_12_08_total3, half_12_08_total4, half_12_08_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_12_08_hx4 : SourcePowerBound
    (powerBoxCross 9 8 16 half_12_08_φ4) (16479523787/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 8) (u := 6) (t := 9)
    (D := 16) (ψ := (112605913/2500000000 : ℝ)) half_12_08_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_12_08_bounds4 l).1) (fun l => (half_12_08_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_12_08_total1, half_12_08_total2, half_12_08_total3, half_12_08_total4, half_12_08_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionNinthSecondSeeds.ninth_half_7) (SeedCompletionHigher9SimpleSeeds.degree9_half_9)
    (by simpa only [half_12_08_φ5, show (2:ℝ)*16=32 by norm_num] using half_12_08_hx5)
  exact h.weaken (by norm_num [half_12_08_total1, half_12_08_total2, half_12_08_total3, half_12_08_total4, half_12_08_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_12_08_hx3 : SourcePowerBound
    (powerBoxCross 9 9 8 half_12_08_φ3) (97472982009/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 9) (u := 7) (t := 10)
    (D := 8) (ψ := (363998863/5000000000 : ℝ)) half_12_08_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_12_08_bounds3 l).1) (fun l => (half_12_08_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_12_08_total1, half_12_08_total2, half_12_08_total3, half_12_08_total4, half_12_08_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_8) (half_10_08)
    (by simpa only [half_12_08_φ4, show (2:ℝ)*8=16 by norm_num] using half_12_08_hx4)
  exact h.weaken (by norm_num [half_12_08_total1, half_12_08_total2, half_12_08_total3, half_12_08_total4, half_12_08_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_12_08_hx2 : SourcePowerBound
    (powerBoxCross 9 10 4 half_12_08_φ2) (117200275987/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 10) (u := 8) (t := 11)
    (D := 4) (ψ := (840753963/10000000000 : ℝ)) half_12_08_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_12_08_bounds2 l).1) (fun l => (half_12_08_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_12_08_total1, half_12_08_total2, half_12_08_total3, half_12_08_total4, half_12_08_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_9) (half_11_08)
    (by simpa only [half_12_08_φ3, show (2:ℝ)*4=8 by norm_num] using half_12_08_hx3)
  exact h.weaken (by norm_num [half_12_08_total1, half_12_08_total2, half_12_08_total3, half_12_08_total4, half_12_08_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_12_08_hx1 : SourcePowerBound
    (powerBoxCross 9 11 2 half_12_08_φ1) (141403297321/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 11) (u := 9) (t := 12)
    (D := 2) (ψ := (451627691/5000000000 : ℝ)) half_12_08_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_12_08_bounds1 l).1) (fun l => (half_12_08_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_12_08_total1, half_12_08_total2, half_12_08_total3, half_12_08_total4, half_12_08_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_10_08) (half_12_07)
    (by simpa only [half_12_08_φ2, show (2:ℝ)*2=4 by norm_num] using half_12_08_hx2)
  exact h.weaken (by norm_num [half_12_08_total1, half_12_08_total2, half_12_08_total3, half_12_08_total4, half_12_08_total5, parameterExponent, curveLoss, dyadicExponent])

theorem half_12_08 : AdmissibleExponent 9 24 (8064853637/500000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 10) (ψ := (947322639/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_11_08)
    (by simpa only [half_12_08_φ1] using half_12_08_hx1)
  exact admissibleExponent_mono h (by norm_num [half_12_08_total1, half_12_08_total2, half_12_08_total3, half_12_08_total4, half_12_08_total5, parameterExponent, curveLoss, dyadicExponent])

private def half_13_08_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (7799361/80000000 : ℝ)

private theorem half_13_08_total1 : total half_13_08_φ1=(7799361/80000000 : ℝ) := by
  norm_num [half_13_08_φ1,total,emptyPhi,Fin.snoc]

private theorem half_13_08_bounds1 : ∀ l,0≤half_13_08_φ1 l ∧ half_13_08_φ1 l≤1 ∧
    0≤shiftExponents 9 half_13_08_φ1 l :=
  alternate_bounds_snoc emptyPhi (7799361/80000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_13_08_φ2 : Fin 2 → ℝ := Fin.snoc half_13_08_φ1 (1871401/20000000 : ℝ)

private theorem half_13_08_total2 : total half_13_08_φ2=(3056993/16000000 : ℝ) := by
  change total (Fin.snoc half_13_08_φ1 (1871401/20000000 : ℝ))=(3056993/16000000 : ℝ)
  rw [alternate_total_snoc,half_13_08_total1]
  norm_num

private theorem half_13_08_bounds2 : ∀ l,0≤half_13_08_φ2 l ∧ half_13_08_φ2 l≤1 ∧
    0≤shiftExponents 9 half_13_08_φ2 l :=
  alternate_bounds_snoc half_13_08_φ1 (1871401/20000000 : ℝ) half_13_08_bounds1 (by norm_num)

private def half_13_08_φ3 : Fin 3 → ℝ := Fin.snoc half_13_08_φ2 (882489409/10000000000 : ℝ)

private theorem half_13_08_total3 : total half_13_08_φ3=(1396555017/5000000000 : ℝ) := by
  change total (Fin.snoc half_13_08_φ2 (882489409/10000000000 : ℝ))=(1396555017/5000000000 : ℝ)
  rw [alternate_total_snoc,half_13_08_total2]
  norm_num

private theorem half_13_08_bounds3 : ∀ l,0≤half_13_08_φ3 l ∧ half_13_08_φ3 l≤1 ∧
    0≤shiftExponents 9 half_13_08_φ3 l :=
  alternate_bounds_snoc half_13_08_φ2 (882489409/10000000000 : ℝ) half_13_08_bounds2 (by norm_num)

private def half_13_08_φ4 : Fin 4 → ℝ := Fin.snoc half_13_08_φ3 (794563051/10000000000 : ℝ)

private theorem half_13_08_total4 : total half_13_08_φ4=(717534617/2000000000 : ℝ) := by
  change total (Fin.snoc half_13_08_φ3 (794563051/10000000000 : ℝ))=(717534617/2000000000 : ℝ)
  rw [alternate_total_snoc,half_13_08_total3]
  norm_num

private theorem half_13_08_bounds4 : ∀ l,0≤half_13_08_φ4 l ∧ half_13_08_φ4 l≤1 ∧
    0≤shiftExponents 9 half_13_08_φ4 l :=
  alternate_bounds_snoc half_13_08_φ3 (794563051/10000000000 : ℝ) half_13_08_bounds3 (by norm_num)

private def half_13_08_φ5 : Fin 5 → ℝ := Fin.snoc half_13_08_φ4 (303578451/5000000000 : ℝ)

private theorem half_13_08_total5 : total half_13_08_φ5=(4194829987/10000000000 : ℝ) := by
  change total (Fin.snoc half_13_08_φ4 (303578451/5000000000 : ℝ))=(4194829987/10000000000 : ℝ)
  rw [alternate_total_snoc,half_13_08_total4]
  norm_num

private theorem half_13_08_bounds5 : ∀ l,0≤half_13_08_φ5 l ∧ half_13_08_φ5 l≤1 ∧
    0≤shiftExponents 9 half_13_08_φ5 l :=
  alternate_bounds_snoc half_13_08_φ4 (303578451/5000000000 : ℝ) half_13_08_bounds4 (by norm_num)

private theorem half_13_08_prefix : PrefixCondition 9 half_13_08_φ5 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_13_08_φ1, half_13_08_φ2, half_13_08_φ3, half_13_08_φ4, half_13_08_φ5, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_13_08_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 32 half_13_08_φ5) (8665510039/1250000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_13_08_φ5
    (fun i => (half_13_08_bounds5 i).1) (fun i => (half_13_08_bounds5 i).2.1)
    (fun i => (half_13_08_bounds5 i).2.2) half_13_08_prefix
  convert h using 1 <;> norm_num [half_13_08_total1, half_13_08_total2, half_13_08_total3, half_13_08_total4, half_13_08_total5, parameterExponent, curveLoss, dyadicExponent]

private theorem half_13_08_hx5 : SourcePowerBound
    (powerBoxCross 9 8 32 half_13_08_φ5) (77658201253/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 8) (r := 2) (v := 10) (w := 11) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_13_08_φ5 (by norm_num [half_13_08_total1, half_13_08_total2, half_13_08_total3, half_13_08_total4, half_13_08_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_13_08_total1, half_13_08_total2, half_13_08_total3, half_13_08_total4, half_13_08_total5, parameterExponent, curveLoss, dyadicExponent]) half_13_08_hF2
    (half_10_08) (half_11_08)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_13_08_total1, half_13_08_total2, half_13_08_total3, half_13_08_total4, half_13_08_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_13_08_hx4 : SourcePowerBound
    (powerBoxCross 9 9 16 half_13_08_φ4) (89899051961/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 9) (u := 7) (t := 10)
    (D := 16) (ψ := (303578451/5000000000 : ℝ)) half_13_08_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_13_08_bounds4 l).1) (fun l => (half_13_08_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_13_08_total1, half_13_08_total2, half_13_08_total3, half_13_08_total4, half_13_08_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_8) (half_10_08)
    (by simpa only [half_13_08_φ5, show (2:ℝ)*16=32 by norm_num] using half_13_08_hx5)
  exact h.weaken (by norm_num [half_13_08_total1, half_13_08_total2, half_13_08_total3, half_13_08_total4, half_13_08_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_13_08_hx3 : SourcePowerBound
    (powerBoxCross 9 10 8 half_13_08_φ3) (107459258121/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 10) (u := 8) (t := 11)
    (D := 8) (ψ := (794563051/10000000000 : ℝ)) half_13_08_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_13_08_bounds3 l).1) (fun l => (half_13_08_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_13_08_total1, half_13_08_total2, half_13_08_total3, half_13_08_total4, half_13_08_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_9) (half_11_08)
    (by simpa only [half_13_08_φ4, show (2:ℝ)*8=16 by norm_num] using half_13_08_hx4)
  exact h.weaken (by norm_num [half_13_08_total1, half_13_08_total2, half_13_08_total3, half_13_08_total4, half_13_08_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_13_08_hx2 : SourcePowerBound
    (powerBoxCross 9 11 4 half_13_08_φ2) (6485522831/500000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 11) (u := 9) (t := 12)
    (D := 4) (ψ := (882489409/10000000000 : ℝ)) half_13_08_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_13_08_bounds2 l).1) (fun l => (half_13_08_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_13_08_total1, half_13_08_total2, half_13_08_total3, half_13_08_total4, half_13_08_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_10_08) (half_12_08)
    (by simpa only [half_13_08_φ3, show (2:ℝ)*4=8 by norm_num] using half_13_08_hx3)
  exact h.weaken (by norm_num [half_13_08_total1, half_13_08_total2, half_13_08_total3, half_13_08_total4, half_13_08_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_13_08_hx1 : SourcePowerBound
    (powerBoxCross 9 12 2 half_13_08_φ1) (39136704159/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 12) (u := 10) (t := 13)
    (D := 2) (ψ := (1871401/20000000 : ℝ)) half_13_08_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_13_08_bounds1 l).1) (fun l => (half_13_08_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_13_08_total1, half_13_08_total2, half_13_08_total3, half_13_08_total4, half_13_08_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_11_08) (half_13_07)
    (by simpa only [half_13_08_φ2, show (2:ℝ)*2=4 by norm_num] using half_13_08_hx2)
  exact h.weaken (by norm_num [half_13_08_total1, half_13_08_total2, half_13_08_total3, half_13_08_total4, half_13_08_total5, parameterExponent, curveLoss, dyadicExponent])

theorem half_13_08 : AdmissibleExponent 9 26 (178969979511/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 11) (ψ := (7799361/80000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_12_08)
    (by simpa only [half_13_08_φ1] using half_13_08_hx1)
  exact admissibleExponent_mono h (by norm_num [half_13_08_total1, half_13_08_total2, half_13_08_total3, half_13_08_total4, half_13_08_total5, parameterExponent, curveLoss, dyadicExponent])

private def half_14_08_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (500049533/5000000000 : ℝ)

private theorem half_14_08_total1 : total half_14_08_φ1=(500049533/5000000000 : ℝ) := by
  norm_num [half_14_08_φ1,total,emptyPhi,Fin.snoc]

private theorem half_14_08_bounds1 : ∀ l,0≤half_14_08_φ1 l ∧ half_14_08_φ1 l≤1 ∧
    0≤shiftExponents 9 half_14_08_φ1 l :=
  alternate_bounds_snoc emptyPhi (500049533/5000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_14_08_φ2 : Fin 2 → ℝ := Fin.snoc half_14_08_φ1 (482670903/5000000000 : ℝ)

private theorem half_14_08_total2 : total half_14_08_φ2=(245680109/1250000000 : ℝ) := by
  change total (Fin.snoc half_14_08_φ1 (482670903/5000000000 : ℝ))=(245680109/1250000000 : ℝ)
  rw [alternate_total_snoc,half_14_08_total1]
  norm_num

private theorem half_14_08_bounds2 : ∀ l,0≤half_14_08_φ2 l ∧ half_14_08_φ2 l≤1 ∧
    0≤shiftExponents 9 half_14_08_φ2 l :=
  alternate_bounds_snoc half_14_08_φ1 (482670903/5000000000 : ℝ) half_14_08_bounds1 (by norm_num)

private def half_14_08_φ3 : Fin 3 → ℝ := Fin.snoc half_14_08_φ2 (920740903/10000000000 : ℝ)

private theorem half_14_08_total3 : total half_14_08_φ3=(115447271/400000000 : ℝ) := by
  change total (Fin.snoc half_14_08_φ2 (920740903/10000000000 : ℝ))=(115447271/400000000 : ℝ)
  rw [alternate_total_snoc,half_14_08_total2]
  norm_num

private theorem half_14_08_bounds3 : ∀ l,0≤half_14_08_φ3 l ∧ half_14_08_φ3 l≤1 ∧
    0≤shiftExponents 9 half_14_08_φ3 l :=
  alternate_bounds_snoc half_14_08_φ2 (920740903/10000000000 : ℝ) half_14_08_bounds2 (by norm_num)

private def half_14_08_φ4 : Fin 4 → ℝ := Fin.snoc half_14_08_φ3 (42635247/500000000 : ℝ)

private theorem half_14_08_total4 : total half_14_08_φ4=(747777343/2000000000 : ℝ) := by
  change total (Fin.snoc half_14_08_φ3 (42635247/500000000 : ℝ))=(747777343/2000000000 : ℝ)
  rw [alternate_total_snoc,half_14_08_total3]
  norm_num

private theorem half_14_08_bounds4 : ∀ l,0≤half_14_08_φ4 l ∧ half_14_08_φ4 l≤1 ∧
    0≤shiftExponents 9 half_14_08_φ4 l :=
  alternate_bounds_snoc half_14_08_φ3 (42635247/500000000 : ℝ) half_14_08_bounds3 (by norm_num)

private def half_14_08_φ5 : Fin 5 → ℝ := Fin.snoc half_14_08_φ4 (724728441/10000000000 : ℝ)

private theorem half_14_08_total5 : total half_14_08_φ5=(1115903789/2500000000 : ℝ) := by
  change total (Fin.snoc half_14_08_φ4 (724728441/10000000000 : ℝ))=(1115903789/2500000000 : ℝ)
  rw [alternate_total_snoc,half_14_08_total4]
  norm_num

private theorem half_14_08_bounds5 : ∀ l,0≤half_14_08_φ5 l ∧ half_14_08_φ5 l≤1 ∧
    0≤shiftExponents 9 half_14_08_φ5 l :=
  alternate_bounds_snoc half_14_08_φ4 (724728441/10000000000 : ℝ) half_14_08_bounds4 (by norm_num)

private def half_14_08_φ6 : Fin 6 → ℝ := Fin.snoc half_14_08_φ5 (209784547/5000000000 : ℝ)

private theorem half_14_08_total6 : total half_14_08_φ6=(19532737/40000000 : ℝ) := by
  change total (Fin.snoc half_14_08_φ5 (209784547/5000000000 : ℝ))=(19532737/40000000 : ℝ)
  rw [alternate_total_snoc,half_14_08_total5]
  norm_num

private theorem half_14_08_bounds6 : ∀ l,0≤half_14_08_φ6 l ∧ half_14_08_φ6 l≤1 ∧
    0≤shiftExponents 9 half_14_08_φ6 l :=
  alternate_bounds_snoc half_14_08_φ5 (209784547/5000000000 : ℝ) half_14_08_bounds5 (by norm_num)

private theorem half_14_08_prefix : PrefixCondition 9 half_14_08_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_14_08_φ1, half_14_08_φ2, half_14_08_φ3, half_14_08_φ4, half_14_08_φ5, half_14_08_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_14_08_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_14_08_φ6) (41401789/5000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_14_08_φ6
    (fun i => (half_14_08_bounds6 i).1) (fun i => (half_14_08_bounds6 i).2.1)
    (fun i => (half_14_08_bounds6 i).2.2) half_14_08_prefix
  convert h using 1 <;> norm_num [half_14_08_total1, half_14_08_total2, half_14_08_total3, half_14_08_total4, half_14_08_total5, half_14_08_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_14_08_hF1 : SourcePowerBound
    (paddedMoment 9 0 1 64 half_14_08_φ6) (15467263/5000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 0) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_14_08_φ6
    (fun i => (half_14_08_bounds6 i).1) (fun i => (half_14_08_bounds6 i).2.1)
    (fun i => (half_14_08_bounds6 i).2.2) half_14_08_prefix
  convert h using 1 <;> norm_num [half_14_08_total1, half_14_08_total2, half_14_08_total3, half_14_08_total4, half_14_08_total5, half_14_08_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_14_08_hx6 : SourcePowerBound
    (powerBoxCross 9 8 64 half_14_08_φ6) (73852172783/10000000000 : ℝ) := by
  have h := full_B_cross_power (k := 9) (s := 8) (r := 1) (v := 2) (t := 11) (D := 64)
    (a := (1/22 : ℝ)) (b := (5/22 : ℝ)) (c := (8/11 : ℝ))
    (by norm_num) half_14_08_φ6 (by norm_num [half_14_08_total1, half_14_08_total2, half_14_08_total3, half_14_08_total4, half_14_08_total5, half_14_08_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_14_08_total1, half_14_08_total2, half_14_08_total3, half_14_08_total4, half_14_08_total5, half_14_08_total6, parameterExponent, curveLoss, dyadicExponent]) half_14_08_hF1 half_14_08_hF2
    (half_11_08)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_14_08_total1, half_14_08_total2, half_14_08_total3, half_14_08_total4, half_14_08_total5, half_14_08_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_14_08_hx5 : SourcePowerBound
    (powerBoxCross 9 9 32 half_14_08_φ5) (82502817119/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 9) (u := 7) (t := 10)
    (D := 32) (ψ := (209784547/5000000000 : ℝ)) half_14_08_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_14_08_bounds5 l).1) (fun l => (half_14_08_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_14_08_total1, half_14_08_total2, half_14_08_total3, half_14_08_total4, half_14_08_total5, half_14_08_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_8) (half_10_08)
    (by simpa only [half_14_08_φ6, show (2:ℝ)*32=64 by norm_num] using half_14_08_hx6)
  exact h.weaken (by norm_num [half_14_08_total1, half_14_08_total2, half_14_08_total3, half_14_08_total4, half_14_08_total5, half_14_08_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_14_08_hx4 : SourcePowerBound
    (powerBoxCross 9 10 16 half_14_08_φ4) (19513951737/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 10) (u := 8) (t := 11)
    (D := 16) (ψ := (724728441/10000000000 : ℝ)) half_14_08_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_14_08_bounds4 l).1) (fun l => (half_14_08_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_14_08_total1, half_14_08_total2, half_14_08_total3, half_14_08_total4, half_14_08_total5, half_14_08_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_9) (half_11_08)
    (by simpa only [half_14_08_φ5, show (2:ℝ)*16=32 by norm_num] using half_14_08_hx5)
  exact h.weaken (by norm_num [half_14_08_total1, half_14_08_total2, half_14_08_total3, half_14_08_total4, half_14_08_total5, half_14_08_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_14_08_hx3 : SourcePowerBound
    (powerBoxCross 9 11 8 half_14_08_φ3) (58856375979/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 11) (u := 9) (t := 12)
    (D := 8) (ψ := (42635247/500000000 : ℝ)) half_14_08_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_14_08_bounds3 l).1) (fun l => (half_14_08_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_14_08_total1, half_14_08_total2, half_14_08_total3, half_14_08_total4, half_14_08_total5, half_14_08_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_10_08) (half_12_08)
    (by simpa only [half_14_08_φ4, show (2:ℝ)*8=16 by norm_num] using half_14_08_hx4)
  exact h.weaken (by norm_num [half_14_08_total1, half_14_08_total2, half_14_08_total3, half_14_08_total4, half_14_08_total5, half_14_08_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_14_08_hx2 : SourcePowerBound
    (powerBoxCross 9 12 4 half_14_08_φ2) (142559636099/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 12) (u := 10) (t := 13)
    (D := 4) (ψ := (920740903/10000000000 : ℝ)) half_14_08_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_14_08_bounds2 l).1) (fun l => (half_14_08_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_14_08_total1, half_14_08_total2, half_14_08_total3, half_14_08_total4, half_14_08_total5, half_14_08_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_11_08) (half_13_08)
    (by simpa only [half_14_08_φ3, show (2:ℝ)*4=8 by norm_num] using half_14_08_hx3)
  exact h.weaken (by norm_num [half_14_08_total1, half_14_08_total2, half_14_08_total3, half_14_08_total4, half_14_08_total5, half_14_08_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_14_08_hx1 : SourcePowerBound
    (powerBoxCross 9 13 2 half_14_08_φ1) (172071307649/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 13) (u := 11) (t := 14)
    (D := 2) (ψ := (482670903/5000000000 : ℝ)) half_14_08_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_14_08_bounds1 l).1) (fun l => (half_14_08_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_14_08_total1, half_14_08_total2, half_14_08_total3, half_14_08_total4, half_14_08_total5, half_14_08_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_12_08) (half_14_07)
    (by simpa only [half_14_08_φ2, show (2:ℝ)*2=4 by norm_num] using half_14_08_hx2)
  exact h.weaken (by norm_num [half_14_08_total1, half_14_08_total2, half_14_08_total3, half_14_08_total4, half_14_08_total5, half_14_08_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_14_08 : AdmissibleExponent 9 28 (197073784299/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 12) (ψ := (500049533/5000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_13_08)
    (by simpa only [half_14_08_φ1] using half_14_08_hx1)
  exact admissibleExponent_mono h (by norm_num [half_14_08_total1, half_14_08_total2, half_14_08_total3, half_14_08_total4, half_14_08_total5, half_14_08_total6, parameterExponent, curveLoss, dyadicExponent])

end Waring.SeedCompletionAlternate9Seeds
