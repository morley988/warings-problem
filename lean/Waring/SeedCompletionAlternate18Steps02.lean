import Waring.SeedCompletionAlternate18Steps01

noncomputable section
set_option maxHeartbeats 2000000
namespace Waring.SeedCompletionAlternate18Seeds
open SmoothMoments FirstStageTransport SeedCompletionNaturalBox
open SeedCompletionSourceBounds SeedCompletionPaddedSource SeedCompletionGeneralTerminal
open PolicyCompletionMajorPowerRanges SeedCompletionDivisorPowerScales
open PolicyCompletionSharpResidualSource

private def half_26_01_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (519417501/10000000000 : ℝ)

private theorem half_26_01_total1 : total half_26_01_φ1=(519417501/10000000000 : ℝ) := by
  norm_num [half_26_01_φ1,total,emptyPhi,Fin.snoc]

private theorem half_26_01_bounds1 : ∀ l,0≤half_26_01_φ1 l ∧ half_26_01_φ1 l≤1 ∧
    0≤shiftExponents 18 half_26_01_φ1 l :=
  alternate_bounds_snoc emptyPhi (519417501/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_26_01_φ2 : Fin 2 → ℝ := Fin.snoc half_26_01_φ1 (95290357/2000000000 : ℝ)

private theorem half_26_01_total2 : total half_26_01_φ2=(497934643/5000000000 : ℝ) := by
  change total (Fin.snoc half_26_01_φ1 (95290357/2000000000 : ℝ))=(497934643/5000000000 : ℝ)
  rw [alternate_total_snoc,half_26_01_total1]
  norm_num

private theorem half_26_01_bounds2 : ∀ l,0≤half_26_01_φ2 l ∧ half_26_01_φ2 l≤1 ∧
    0≤shiftExponents 18 half_26_01_φ2 l :=
  alternate_bounds_snoc half_26_01_φ1 (95290357/2000000000 : ℝ) half_26_01_bounds1 (by norm_num)

private def half_26_01_φ3 : Fin 3 → ℝ := Fin.snoc half_26_01_φ2 (470351969/10000000000 : ℝ)

private theorem half_26_01_total3 : total half_26_01_φ3=(293244251/2000000000 : ℝ) := by
  change total (Fin.snoc half_26_01_φ2 (470351969/10000000000 : ℝ))=(293244251/2000000000 : ℝ)
  rw [alternate_total_snoc,half_26_01_total2]
  norm_num

private theorem half_26_01_bounds3 : ∀ l,0≤half_26_01_φ3 l ∧ half_26_01_φ3 l≤1 ∧
    0≤shiftExponents 18 half_26_01_φ3 l :=
  alternate_bounds_snoc half_26_01_φ2 (470351969/10000000000 : ℝ) half_26_01_bounds2 (by norm_num)

private def half_26_01_φ4 : Fin 4 → ℝ := Fin.snoc half_26_01_φ3 (9292571/200000000 : ℝ)

private theorem half_26_01_total4 : total half_26_01_φ4=(386169961/2000000000 : ℝ) := by
  change total (Fin.snoc half_26_01_φ3 (9292571/200000000 : ℝ))=(386169961/2000000000 : ℝ)
  rw [alternate_total_snoc,half_26_01_total3]
  norm_num

private theorem half_26_01_bounds4 : ∀ l,0≤half_26_01_φ4 l ∧ half_26_01_φ4 l≤1 ∧
    0≤shiftExponents 18 half_26_01_φ4 l :=
  alternate_bounds_snoc half_26_01_φ3 (9292571/200000000 : ℝ) half_26_01_bounds3 (by norm_num)

private def half_26_01_φ5 : Fin 5 → ℝ := Fin.snoc half_26_01_φ4 (230099877/5000000000 : ℝ)

private theorem half_26_01_total5 : total half_26_01_φ5=(2391049559/10000000000 : ℝ) := by
  change total (Fin.snoc half_26_01_φ4 (230099877/5000000000 : ℝ))=(2391049559/10000000000 : ℝ)
  rw [alternate_total_snoc,half_26_01_total4]
  norm_num

private theorem half_26_01_bounds5 : ∀ l,0≤half_26_01_φ5 l ∧ half_26_01_φ5 l≤1 ∧
    0≤shiftExponents 18 half_26_01_φ5 l :=
  alternate_bounds_snoc half_26_01_φ4 (230099877/5000000000 : ℝ) half_26_01_bounds4 (by norm_num)

private def half_26_01_φ6 : Fin 6 → ℝ := Fin.snoc half_26_01_φ5 (447585319/10000000000 : ℝ)

private theorem half_26_01_total6 : total half_26_01_φ6=(1419317439/5000000000 : ℝ) := by
  change total (Fin.snoc half_26_01_φ5 (447585319/10000000000 : ℝ))=(1419317439/5000000000 : ℝ)
  rw [alternate_total_snoc,half_26_01_total5]
  norm_num

private theorem half_26_01_bounds6 : ∀ l,0≤half_26_01_φ6 l ∧ half_26_01_φ6 l≤1 ∧
    0≤shiftExponents 18 half_26_01_φ6 l :=
  alternate_bounds_snoc half_26_01_φ5 (447585319/10000000000 : ℝ) half_26_01_bounds5 (by norm_num)

private def half_26_01_φ7 : Fin 7 → ℝ := Fin.snoc half_26_01_φ6 (421256771/10000000000 : ℝ)

private theorem half_26_01_total7 : total half_26_01_φ7=(3259891649/10000000000 : ℝ) := by
  change total (Fin.snoc half_26_01_φ6 (421256771/10000000000 : ℝ))=(3259891649/10000000000 : ℝ)
  rw [alternate_total_snoc,half_26_01_total6]
  norm_num

private theorem half_26_01_bounds7 : ∀ l,0≤half_26_01_φ7 l ∧ half_26_01_φ7 l≤1 ∧
    0≤shiftExponents 18 half_26_01_φ7 l :=
  alternate_bounds_snoc half_26_01_φ6 (421256771/10000000000 : ℝ) half_26_01_bounds6 (by norm_num)

private def half_26_01_φ8 : Fin 8 → ℝ := Fin.snoc half_26_01_φ7 (396476961/10000000000 : ℝ)

private theorem half_26_01_total8 : total half_26_01_φ8=(365636861/1000000000 : ℝ) := by
  change total (Fin.snoc half_26_01_φ7 (396476961/10000000000 : ℝ))=(365636861/1000000000 : ℝ)
  rw [alternate_total_snoc,half_26_01_total7]
  norm_num

private theorem half_26_01_bounds8 : ∀ l,0≤half_26_01_φ8 l ∧ half_26_01_φ8 l≤1 ∧
    0≤shiftExponents 18 half_26_01_φ8 l :=
  alternate_bounds_snoc half_26_01_φ7 (396476961/10000000000 : ℝ) half_26_01_bounds7 (by norm_num)

private def half_26_01_φ9 : Fin 9 → ℝ := Fin.snoc half_26_01_φ8 (373154787/10000000000 : ℝ)

private theorem half_26_01_total9 : total half_26_01_φ9=(4029523397/10000000000 : ℝ) := by
  change total (Fin.snoc half_26_01_φ8 (373154787/10000000000 : ℝ))=(4029523397/10000000000 : ℝ)
  rw [alternate_total_snoc,half_26_01_total8]
  norm_num

private theorem half_26_01_bounds9 : ∀ l,0≤half_26_01_φ9 l ∧ half_26_01_φ9 l≤1 ∧
    0≤shiftExponents 18 half_26_01_φ9 l :=
  alternate_bounds_snoc half_26_01_φ8 (373154787/10000000000 : ℝ) half_26_01_bounds8 (by norm_num)

private def half_26_01_φ10 : Fin 10 → ℝ := Fin.snoc half_26_01_φ9 (70240901/2000000000 : ℝ)

private theorem half_26_01_total10 : total half_26_01_φ10=(2190363951/5000000000 : ℝ) := by
  change total (Fin.snoc half_26_01_φ9 (70240901/2000000000 : ℝ))=(2190363951/5000000000 : ℝ)
  rw [alternate_total_snoc,half_26_01_total9]
  norm_num

private theorem half_26_01_bounds10 : ∀ l,0≤half_26_01_φ10 l ∧ half_26_01_φ10 l≤1 ∧
    0≤shiftExponents 18 half_26_01_φ10 l :=
  alternate_bounds_snoc half_26_01_φ9 (70240901/2000000000 : ℝ) half_26_01_bounds9 (by norm_num)

private def half_26_01_φ11 : Fin 11 → ℝ := Fin.snoc half_26_01_φ10 (141562433/5000000000 : ℝ)

private theorem half_26_01_total11 : total half_26_01_φ11=(145745399/312500000 : ℝ) := by
  change total (Fin.snoc half_26_01_φ10 (141562433/5000000000 : ℝ))=(145745399/312500000 : ℝ)
  rw [alternate_total_snoc,half_26_01_total10]
  norm_num

private theorem half_26_01_bounds11 : ∀ l,0≤half_26_01_φ11 l ∧ half_26_01_φ11 l≤1 ∧
    0≤shiftExponents 18 half_26_01_φ11 l :=
  alternate_bounds_snoc half_26_01_φ10 (141562433/5000000000 : ℝ) half_26_01_bounds10 (by norm_num)

private theorem half_26_01_prefix : PrefixCondition 18 half_26_01_φ11 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_26_01_φ1, half_26_01_φ2, half_26_01_φ3, half_26_01_φ4, half_26_01_φ5, half_26_01_φ6, half_26_01_φ7, half_26_01_φ8, half_26_01_φ9, half_26_01_φ10, half_26_01_φ11, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_26_01_hF2 : SourcePowerBound
    (paddedMoment 18 0 2 2048 half_26_01_φ11) (212763803/18750000 : ℝ) := by
  have h := padded_dyadic_divisor_power (k := 18) (j := 11) (r := 0) (n := 1) (D := 2048)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_26_01_φ11
    (fun i => (half_26_01_bounds11 i).1) (fun i => (half_26_01_bounds11 i).2.1)
    (fun i => (half_26_01_bounds11 i).2.2) half_26_01_prefix
  convert h using 1 <;> norm_num [half_26_01_total1, half_26_01_total2, half_26_01_total3, half_26_01_total4, half_26_01_total5, half_26_01_total6, half_26_01_total7, half_26_01_total8, half_26_01_total9, half_26_01_total10, half_26_01_total11, parameterExponent, curveLoss, dyadicExponent]

private theorem half_26_01_hx11 : SourcePowerBound
    (powerBoxCross 18 15 2048 half_26_01_φ11) (33179999481/2500000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 15) (r := 2) (v := 0) (w := 20) (D := 2048)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_26_01_φ11 (by norm_num [half_26_01_total1, half_26_01_total2, half_26_01_total3, half_26_01_total4, half_26_01_total5, half_26_01_total6, half_26_01_total7, half_26_01_total8, half_26_01_total9, half_26_01_total10, half_26_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_26_01_total1, half_26_01_total2, half_26_01_total3, half_26_01_total4, half_26_01_total5, half_26_01_total6, half_26_01_total7, half_26_01_total8, half_26_01_total9, half_26_01_total10, half_26_01_total11, parameterExponent, curveLoss, dyadicExponent]) half_26_01_hF2
    (admissibleExponent_zero 18) (half_20_01)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_26_01_total1, half_26_01_total2, half_26_01_total3, half_26_01_total4, half_26_01_total5, half_26_01_total6, half_26_01_total7, half_26_01_total8, half_26_01_total9, half_26_01_total10, half_26_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_26_01_hx10 : SourcePowerBound
    (powerBoxCross 18 16 1024 half_26_01_φ10) (28542211543/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 10) (s := 16) (u := 14) (t := 17)
    (D := 1024) (ψ := (141562433/5000000000 : ℝ)) half_26_01_φ10
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_26_01_bounds10 l).1) (fun l => (half_26_01_bounds10 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_26_01_total1, half_26_01_total2, half_26_01_total3, half_26_01_total4, half_26_01_total5, half_26_01_total6, half_26_01_total7, half_26_01_total8, half_26_01_total9, half_26_01_total10, half_26_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher18SimpleSeeds.degree18_half_15) (SeedCompletionHigher18SimpleSeeds.degree18_half_17)
    (by simpa only [half_26_01_φ11, show (2:ℝ)*1024=2048 by norm_num] using half_26_01_hx11)
  exact h.weaken (by norm_num [half_26_01_total1, half_26_01_total2, half_26_01_total3, half_26_01_total4, half_26_01_total5, half_26_01_total6, half_26_01_total7, half_26_01_total8, half_26_01_total9, half_26_01_total10, half_26_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_26_01_hx9 : SourcePowerBound
    (powerBoxCross 18 17 512 half_26_01_φ9) (31108895803/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 9) (s := 17) (u := 15) (t := 18)
    (D := 512) (ψ := (70240901/2000000000 : ℝ)) half_26_01_φ9
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_26_01_bounds9 l).1) (fun l => (half_26_01_bounds9 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_26_01_total1, half_26_01_total2, half_26_01_total3, half_26_01_total4, half_26_01_total5, half_26_01_total6, half_26_01_total7, half_26_01_total8, half_26_01_total9, half_26_01_total10, half_26_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher18SimpleSeeds.degree18_half_16) (half_18_01)
    (by simpa only [half_26_01_φ10, show (2:ℝ)*512=1024 by norm_num] using half_26_01_hx10)
  exact h.weaken (by norm_num [half_26_01_total1, half_26_01_total2, half_26_01_total3, half_26_01_total4, half_26_01_total5, half_26_01_total6, half_26_01_total7, half_26_01_total8, half_26_01_total9, half_26_01_total10, half_26_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_26_01_hx8 : SourcePowerBound
    (powerBoxCross 18 18 256 half_26_01_φ8) (170284606293/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 8) (s := 18) (u := 16) (t := 19)
    (D := 256) (ψ := (373154787/10000000000 : ℝ)) half_26_01_φ8
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_26_01_bounds8 l).1) (fun l => (half_26_01_bounds8 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_26_01_total1, half_26_01_total2, half_26_01_total3, half_26_01_total4, half_26_01_total5, half_26_01_total6, half_26_01_total7, half_26_01_total8, half_26_01_total9, half_26_01_total10, half_26_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher18SimpleSeeds.degree18_half_17) (half_19_01)
    (by simpa only [half_26_01_φ9, show (2:ℝ)*256=512 by norm_num] using half_26_01_hx9)
  exact h.weaken (by norm_num [half_26_01_total1, half_26_01_total2, half_26_01_total3, half_26_01_total4, half_26_01_total5, half_26_01_total6, half_26_01_total7, half_26_01_total8, half_26_01_total9, half_26_01_total10, half_26_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_26_01_hx7 : SourcePowerBound
    (powerBoxCross 18 19 128 half_26_01_φ7) (37448550791/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 7) (s := 19) (u := 17) (t := 20)
    (D := 128) (ψ := (396476961/10000000000 : ℝ)) half_26_01_φ7
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_26_01_bounds7 l).1) (fun l => (half_26_01_bounds7 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_26_01_total1, half_26_01_total2, half_26_01_total3, half_26_01_total4, half_26_01_total5, half_26_01_total6, half_26_01_total7, half_26_01_total8, half_26_01_total9, half_26_01_total10, half_26_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_18_01) (half_20_01)
    (by simpa only [half_26_01_φ8, show (2:ℝ)*128=256 by norm_num] using half_26_01_hx8)
  exact h.weaken (by norm_num [half_26_01_total1, half_26_01_total2, half_26_01_total3, half_26_01_total4, half_26_01_total5, half_26_01_total6, half_26_01_total7, half_26_01_total8, half_26_01_total9, half_26_01_total10, half_26_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_26_01_hx6 : SourcePowerBound
    (powerBoxCross 18 20 64 half_26_01_φ6) (25835565337/1250000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 6) (s := 20) (u := 18) (t := 21)
    (D := 64) (ψ := (421256771/10000000000 : ℝ)) half_26_01_φ6
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_26_01_bounds6 l).1) (fun l => (half_26_01_bounds6 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_26_01_total1, half_26_01_total2, half_26_01_total3, half_26_01_total4, half_26_01_total5, half_26_01_total6, half_26_01_total7, half_26_01_total8, half_26_01_total9, half_26_01_total10, half_26_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_19_01) (half_21_01)
    (by simpa only [half_26_01_φ7, show (2:ℝ)*64=128 by norm_num] using half_26_01_hx7)
  exact h.weaken (by norm_num [half_26_01_total1, half_26_01_total2, half_26_01_total3, half_26_01_total4, half_26_01_total5, half_26_01_total6, half_26_01_total7, half_26_01_total8, half_26_01_total9, half_26_01_total10, half_26_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_26_01_hx5 : SourcePowerBound
    (powerBoxCross 18 21 32 half_26_01_φ5) (11442856169/500000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 5) (s := 21) (u := 19) (t := 22)
    (D := 32) (ψ := (447585319/10000000000 : ℝ)) half_26_01_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_26_01_bounds5 l).1) (fun l => (half_26_01_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_26_01_total1, half_26_01_total2, half_26_01_total3, half_26_01_total4, half_26_01_total5, half_26_01_total6, half_26_01_total7, half_26_01_total8, half_26_01_total9, half_26_01_total10, half_26_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_20_01) (half_22_01)
    (by simpa only [half_26_01_φ6, show (2:ℝ)*32=64 by norm_num] using half_26_01_hx6)
  exact h.weaken (by norm_num [half_26_01_total1, half_26_01_total2, half_26_01_total3, half_26_01_total4, half_26_01_total5, half_26_01_total6, half_26_01_total7, half_26_01_total8, half_26_01_total9, half_26_01_total10, half_26_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_26_01_hx4 : SourcePowerBound
    (powerBoxCross 18 22 16 half_26_01_φ4) (10132873781/400000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 22) (u := 20) (t := 23)
    (D := 16) (ψ := (230099877/5000000000 : ℝ)) half_26_01_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_26_01_bounds4 l).1) (fun l => (half_26_01_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_26_01_total1, half_26_01_total2, half_26_01_total3, half_26_01_total4, half_26_01_total5, half_26_01_total6, half_26_01_total7, half_26_01_total8, half_26_01_total9, half_26_01_total10, half_26_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_21_01) (half_23_01)
    (by simpa only [half_26_01_φ5, show (2:ℝ)*16=32 by norm_num] using half_26_01_hx5)
  exact h.weaken (by norm_num [half_26_01_total1, half_26_01_total2, half_26_01_total3, half_26_01_total4, half_26_01_total5, half_26_01_total6, half_26_01_total7, half_26_01_total8, half_26_01_total9, half_26_01_total10, half_26_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_26_01_hx3 : SourcePowerBound
    (powerBoxCross 18 23 8 half_26_01_φ3) (34972370371/1250000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 23) (u := 21) (t := 24)
    (D := 8) (ψ := (9292571/200000000 : ℝ)) half_26_01_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_26_01_bounds3 l).1) (fun l => (half_26_01_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_26_01_total1, half_26_01_total2, half_26_01_total3, half_26_01_total4, half_26_01_total5, half_26_01_total6, half_26_01_total7, half_26_01_total8, half_26_01_total9, half_26_01_total10, half_26_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_22_01) (half_24_01)
    (by simpa only [half_26_01_φ4, show (2:ℝ)*8=16 by norm_num] using half_26_01_hx4)
  exact h.weaken (by norm_num [half_26_01_total1, half_26_01_total2, half_26_01_total3, half_26_01_total4, half_26_01_total5, half_26_01_total6, half_26_01_total7, half_26_01_total8, half_26_01_total9, half_26_01_total10, half_26_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_26_01_hx2 : SourcePowerBound
    (powerBoxCross 18 24 4 half_26_01_φ2) (61665396091/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 24) (u := 22) (t := 25)
    (D := 4) (ψ := (470351969/10000000000 : ℝ)) half_26_01_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_26_01_bounds2 l).1) (fun l => (half_26_01_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_26_01_total1, half_26_01_total2, half_26_01_total3, half_26_01_total4, half_26_01_total5, half_26_01_total6, half_26_01_total7, half_26_01_total8, half_26_01_total9, half_26_01_total10, half_26_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_23_01) (half_25_01)
    (by simpa only [half_26_01_φ3, show (2:ℝ)*4=8 by norm_num] using half_26_01_hx3)
  exact h.weaken (by norm_num [half_26_01_total1, half_26_01_total2, half_26_01_total3, half_26_01_total4, half_26_01_total5, half_26_01_total6, half_26_01_total7, half_26_01_total8, half_26_01_total9, half_26_01_total10, half_26_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_26_01_hx1 : SourcePowerBound
    (powerBoxCross 18 25 2 half_26_01_φ1) (67940316371/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 25) (u := 23) (t := 26)
    (D := 2) (ψ := (95290357/2000000000 : ℝ)) half_26_01_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_26_01_bounds1 l).1) (fun l => (half_26_01_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_26_01_total1, half_26_01_total2, half_26_01_total3, half_26_01_total4, half_26_01_total5, half_26_01_total6, half_26_01_total7, half_26_01_total8, half_26_01_total9, half_26_01_total10, half_26_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_24_01) (chord_44)
    (by simpa only [half_26_01_φ2, show (2:ℝ)*2=4 by norm_num] using half_26_01_hx2)
  exact h.weaken (by norm_num [half_26_01_total1, half_26_01_total2, half_26_01_total3, half_26_01_total4, half_26_01_total5, half_26_01_total6, half_26_01_total7, half_26_01_total8, half_26_01_total9, half_26_01_total10, half_26_01_total11, parameterExponent, curveLoss, dyadicExponent])

theorem half_26_01 : AdmissibleExponent 18 52 (91288259851/2500000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 24) (ψ := (519417501/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_25_01)
    (by simpa only [half_26_01_φ1] using half_26_01_hx1)
  exact admissibleExponent_mono h (by norm_num [half_26_01_total1, half_26_01_total2, half_26_01_total3, half_26_01_total4, half_26_01_total5, half_26_01_total6, half_26_01_total7, half_26_01_total8, half_26_01_total9, half_26_01_total10, half_26_01_total11, parameterExponent, curveLoss, dyadicExponent])

theorem chord_49 : AdmissibleExponent 18 54 (961920254187/25000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 54) (t := (4/5 : ℝ))
    (half_26_01) (half_31_00)
    (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private def half_27_01_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (526941563/10000000000 : ℝ)

private theorem half_27_01_total1 : total half_27_01_φ1=(526941563/10000000000 : ℝ) := by
  norm_num [half_27_01_φ1,total,emptyPhi,Fin.snoc]

private theorem half_27_01_bounds1 : ∀ l,0≤half_27_01_φ1 l ∧ half_27_01_φ1 l≤1 ∧
    0≤shiftExponents 18 half_27_01_φ1 l :=
  alternate_bounds_snoc emptyPhi (526941563/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_27_01_φ2 : Fin 2 → ℝ := Fin.snoc half_27_01_φ1 (241490763/5000000000 : ℝ)

private theorem half_27_01_total2 : total half_27_01_φ2=(1009923089/10000000000 : ℝ) := by
  change total (Fin.snoc half_27_01_φ1 (241490763/5000000000 : ℝ))=(1009923089/10000000000 : ℝ)
  rw [alternate_total_snoc,half_27_01_total1]
  norm_num

private theorem half_27_01_bounds2 : ∀ l,0≤half_27_01_φ2 l ∧ half_27_01_φ2 l≤1 ∧
    0≤shiftExponents 18 half_27_01_φ2 l :=
  alternate_bounds_snoc half_27_01_φ1 (241490763/5000000000 : ℝ) half_27_01_bounds1 (by norm_num)

private def half_27_01_φ3 : Fin 3 → ℝ := Fin.snoc half_27_01_φ2 (478140931/10000000000 : ℝ)

private theorem half_27_01_total3 : total half_27_01_φ3=(74403201/500000000 : ℝ) := by
  change total (Fin.snoc half_27_01_φ2 (478140931/10000000000 : ℝ))=(74403201/500000000 : ℝ)
  rw [alternate_total_snoc,half_27_01_total2]
  norm_num

private theorem half_27_01_bounds3 : ∀ l,0≤half_27_01_φ3 l ∧ half_27_01_φ3 l≤1 ∧
    0≤shiftExponents 18 half_27_01_φ3 l :=
  alternate_bounds_snoc half_27_01_φ2 (478140931/10000000000 : ℝ) half_27_01_bounds2 (by norm_num)

private def half_27_01_φ4 : Fin 4 → ℝ := Fin.snoc half_27_01_φ3 (29697663/625000000 : ℝ)

private theorem half_27_01_total4 : total half_27_01_φ4=(490806657/2500000000 : ℝ) := by
  change total (Fin.snoc half_27_01_φ3 (29697663/625000000 : ℝ))=(490806657/2500000000 : ℝ)
  rw [alternate_total_snoc,half_27_01_total3]
  norm_num

private theorem half_27_01_bounds4 : ∀ l,0≤half_27_01_φ4 l ∧ half_27_01_φ4 l≤1 ∧
    0≤shiftExponents 18 half_27_01_φ4 l :=
  alternate_bounds_snoc half_27_01_φ3 (29697663/625000000 : ℝ) half_27_01_bounds3 (by norm_num)

private def half_27_01_φ5 : Fin 5 → ℝ := Fin.snoc half_27_01_φ4 (236375687/5000000000 : ℝ)

private theorem half_27_01_total5 : total half_27_01_φ5=(1217989001/5000000000 : ℝ) := by
  change total (Fin.snoc half_27_01_φ4 (236375687/5000000000 : ℝ))=(1217989001/5000000000 : ℝ)
  rw [alternate_total_snoc,half_27_01_total4]
  norm_num

private theorem half_27_01_bounds5 : ∀ l,0≤half_27_01_φ5 l ∧ half_27_01_φ5 l≤1 ∧
    0≤shiftExponents 18 half_27_01_φ5 l :=
  alternate_bounds_snoc half_27_01_φ4 (236375687/5000000000 : ℝ) half_27_01_bounds4 (by norm_num)

private def half_27_01_φ6 : Fin 6 → ℝ := Fin.snoc half_27_01_φ5 (44494247/1000000000 : ℝ)

private theorem half_27_01_total6 : total half_27_01_φ6=(360115059/1250000000 : ℝ) := by
  change total (Fin.snoc half_27_01_φ5 (44494247/1000000000 : ℝ))=(360115059/1250000000 : ℝ)
  rw [alternate_total_snoc,half_27_01_total5]
  norm_num

private theorem half_27_01_bounds6 : ∀ l,0≤half_27_01_φ6 l ∧ half_27_01_φ6 l≤1 ∧
    0≤shiftExponents 18 half_27_01_φ6 l :=
  alternate_bounds_snoc half_27_01_φ5 (44494247/1000000000 : ℝ) half_27_01_bounds5 (by norm_num)

private def half_27_01_φ7 : Fin 7 → ℝ := Fin.snoc half_27_01_φ6 (418769383/10000000000 : ℝ)

private theorem half_27_01_total7 : total half_27_01_φ7=(659937971/2000000000 : ℝ) := by
  change total (Fin.snoc half_27_01_φ6 (418769383/10000000000 : ℝ))=(659937971/2000000000 : ℝ)
  rw [alternate_total_snoc,half_27_01_total6]
  norm_num

private theorem half_27_01_bounds7 : ∀ l,0≤half_27_01_φ7 l ∧ half_27_01_φ7 l≤1 ∧
    0≤shiftExponents 18 half_27_01_φ7 l :=
  alternate_bounds_snoc half_27_01_φ6 (418769383/10000000000 : ℝ) half_27_01_bounds6 (by norm_num)

private def half_27_01_φ8 : Fin 8 → ℝ := Fin.snoc half_27_01_φ7 (39413589/1000000000 : ℝ)

private theorem half_27_01_total8 : total half_27_01_φ8=(738765149/2000000000 : ℝ) := by
  change total (Fin.snoc half_27_01_φ7 (39413589/1000000000 : ℝ))=(738765149/2000000000 : ℝ)
  rw [alternate_total_snoc,half_27_01_total7]
  norm_num

private theorem half_27_01_bounds8 : ∀ l,0≤half_27_01_φ8 l ∧ half_27_01_φ8 l≤1 ∧
    0≤shiftExponents 18 half_27_01_φ8 l :=
  alternate_bounds_snoc half_27_01_φ7 (39413589/1000000000 : ℝ) half_27_01_bounds7 (by norm_num)

private theorem half_27_01_prefix : PrefixCondition 18 half_27_01_φ8 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_27_01_φ1, half_27_01_φ2, half_27_01_φ3, half_27_01_φ4, half_27_01_φ5, half_27_01_φ6, half_27_01_φ7, half_27_01_φ8, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_27_01_hF8 : SourcePowerBound
    (paddedMoment 18 0 8 256 half_27_01_φ8) (113530478231/3000000000 : ℝ) := by
  have h := padded_dyadic_divisor_power (k := 18) (j := 8) (r := 0) (n := 3) (D := 256)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_27_01_φ8
    (fun i => (half_27_01_bounds8 i).1) (fun i => (half_27_01_bounds8 i).2.1)
    (fun i => (half_27_01_bounds8 i).2.2) half_27_01_prefix
  convert h using 1 <;> norm_num [half_27_01_total1, half_27_01_total2, half_27_01_total3, half_27_01_total4, half_27_01_total5, half_27_01_total6, half_27_01_total7, half_27_01_total8, parameterExponent, curveLoss, dyadicExponent]

private theorem half_27_01_hx8 : SourcePowerBound
    (powerBoxCross 18 19 256 half_27_01_φ8) (3609211699/200000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 19) (r := 8) (v := 20) (w := 21) (D := 256)
    (a := (1/16 : ℝ)) (b := (11/16 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_27_01_φ8 (by norm_num [half_27_01_total1, half_27_01_total2, half_27_01_total3, half_27_01_total4, half_27_01_total5, half_27_01_total6, half_27_01_total7, half_27_01_total8, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_27_01_total1, half_27_01_total2, half_27_01_total3, half_27_01_total4, half_27_01_total5, half_27_01_total6, half_27_01_total7, half_27_01_total8, parameterExponent, curveLoss, dyadicExponent]) half_27_01_hF8
    (half_20_01) (half_21_01)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_27_01_total1, half_27_01_total2, half_27_01_total3, half_27_01_total4, half_27_01_total5, half_27_01_total6, half_27_01_total7, half_27_01_total8, parameterExponent, curveLoss, dyadicExponent])

private theorem half_27_01_hx7 : SourcePowerBound
    (powerBoxCross 18 20 128 half_27_01_φ7) (197473385247/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 7) (s := 20) (u := 18) (t := 21)
    (D := 128) (ψ := (39413589/1000000000 : ℝ)) half_27_01_φ7
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_27_01_bounds7 l).1) (fun l => (half_27_01_bounds7 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_27_01_total1, half_27_01_total2, half_27_01_total3, half_27_01_total4, half_27_01_total5, half_27_01_total6, half_27_01_total7, half_27_01_total8, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_19_01) (half_21_01)
    (by simpa only [half_27_01_φ8, show (2:ℝ)*128=256 by norm_num] using half_27_01_hx8)
  exact h.weaken (by norm_num [half_27_01_total1, half_27_01_total2, half_27_01_total3, half_27_01_total4, half_27_01_total5, half_27_01_total6, half_27_01_total7, half_27_01_total8, parameterExponent, curveLoss, dyadicExponent])

private theorem half_27_01_hx6 : SourcePowerBound
    (powerBoxCross 18 21 64 half_27_01_φ6) (54326986221/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 6) (s := 21) (u := 19) (t := 22)
    (D := 64) (ψ := (418769383/10000000000 : ℝ)) half_27_01_φ6
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_27_01_bounds6 l).1) (fun l => (half_27_01_bounds6 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_27_01_total1, half_27_01_total2, half_27_01_total3, half_27_01_total4, half_27_01_total5, half_27_01_total6, half_27_01_total7, half_27_01_total8, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_20_01) (half_22_01)
    (by simpa only [half_27_01_φ7, show (2:ℝ)*64=128 by norm_num] using half_27_01_hx7)
  exact h.weaken (by norm_num [half_27_01_total1, half_27_01_total2, half_27_01_total3, half_27_01_total4, half_27_01_total5, half_27_01_total6, half_27_01_total7, half_27_01_total8, parameterExponent, curveLoss, dyadicExponent])

private theorem half_27_01_hx5 : SourcePowerBound
    (powerBoxCross 18 22 32 half_27_01_φ5) (240061350379/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 5) (s := 22) (u := 20) (t := 23)
    (D := 32) (ψ := (44494247/1000000000 : ℝ)) half_27_01_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_27_01_bounds5 l).1) (fun l => (half_27_01_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_27_01_total1, half_27_01_total2, half_27_01_total3, half_27_01_total4, half_27_01_total5, half_27_01_total6, half_27_01_total7, half_27_01_total8, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_21_01) (half_23_01)
    (by simpa only [half_27_01_φ6, show (2:ℝ)*32=64 by norm_num] using half_27_01_hx6)
  exact h.weaken (by norm_num [half_27_01_total1, half_27_01_total2, half_27_01_total3, half_27_01_total4, half_27_01_total5, half_27_01_total6, half_27_01_total7, half_27_01_total8, parameterExponent, curveLoss, dyadicExponent])

private theorem half_27_01_hx4 : SourcePowerBound
    (powerBoxCross 18 23 16 half_27_01_φ4) (53182159737/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 23) (u := 21) (t := 24)
    (D := 16) (ψ := (236375687/5000000000 : ℝ)) half_27_01_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_27_01_bounds4 l).1) (fun l => (half_27_01_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_27_01_total1, half_27_01_total2, half_27_01_total3, half_27_01_total4, half_27_01_total5, half_27_01_total6, half_27_01_total7, half_27_01_total8, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_22_01) (half_24_01)
    (by simpa only [half_27_01_φ5, show (2:ℝ)*16=32 by norm_num] using half_27_01_hx5)
  exact h.weaken (by norm_num [half_27_01_total1, half_27_01_total2, half_27_01_total3, half_27_01_total4, half_27_01_total5, half_27_01_total6, half_27_01_total7, half_27_01_total8, parameterExponent, curveLoss, dyadicExponent])

private theorem half_27_01_hx3 : SourcePowerBound
    (powerBoxCross 18 24 8 half_27_01_φ3) (73443139429/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 24) (u := 22) (t := 25)
    (D := 8) (ψ := (29697663/625000000 : ℝ)) half_27_01_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_27_01_bounds3 l).1) (fun l => (half_27_01_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_27_01_total1, half_27_01_total2, half_27_01_total3, half_27_01_total4, half_27_01_total5, half_27_01_total6, half_27_01_total7, half_27_01_total8, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_23_01) (half_25_01)
    (by simpa only [half_27_01_φ4, show (2:ℝ)*8=16 by norm_num] using half_27_01_hx4)
  exact h.weaken (by norm_num [half_27_01_total1, half_27_01_total2, half_27_01_total3, half_27_01_total4, half_27_01_total5, half_27_01_total6, half_27_01_total7, half_27_01_total8, parameterExponent, curveLoss, dyadicExponent])

private theorem half_27_01_hx2 : SourcePowerBound
    (powerBoxCross 18 25 4 half_27_01_φ2) (323675939907/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 25) (u := 23) (t := 26)
    (D := 4) (ψ := (478140931/10000000000 : ℝ)) half_27_01_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_27_01_bounds2 l).1) (fun l => (half_27_01_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_27_01_total1, half_27_01_total2, half_27_01_total3, half_27_01_total4, half_27_01_total5, half_27_01_total6, half_27_01_total7, half_27_01_total8, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_24_01) (half_26_01)
    (by simpa only [half_27_01_φ3, show (2:ℝ)*4=8 by norm_num] using half_27_01_hx3)
  exact h.weaken (by norm_num [half_27_01_total1, half_27_01_total2, half_27_01_total3, half_27_01_total4, half_27_01_total5, half_27_01_total6, half_27_01_total7, half_27_01_total8, parameterExponent, curveLoss, dyadicExponent])

private theorem half_27_01_hx1 : SourcePowerBound
    (powerBoxCross 18 26 2 half_27_01_φ1) (22277409353/625000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 26) (u := 24) (t := 27)
    (D := 2) (ψ := (241490763/5000000000 : ℝ)) half_27_01_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_27_01_bounds1 l).1) (fun l => (half_27_01_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_27_01_total1, half_27_01_total2, half_27_01_total3, half_27_01_total4, half_27_01_total5, half_27_01_total6, half_27_01_total7, half_27_01_total8, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_25_01) (chord_49)
    (by simpa only [half_27_01_φ2, show (2:ℝ)*2=4 by norm_num] using half_27_01_hx2)
  exact h.weaken (by norm_num [half_27_01_total1, half_27_01_total2, half_27_01_total3, half_27_01_total4, half_27_01_total5, half_27_01_total6, half_27_01_total7, half_27_01_total8, parameterExponent, curveLoss, dyadicExponent])

theorem half_27_01 : AdmissibleExponent 18 54 (383312569361/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 25) (ψ := (526941563/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_26_01)
    (by simpa only [half_27_01_φ1] using half_27_01_hx1)
  exact admissibleExponent_mono h (by norm_num [half_27_01_total1, half_27_01_total2, half_27_01_total3, half_27_01_total4, half_27_01_total5, half_27_01_total6, half_27_01_total7, half_27_01_total8, parameterExponent, curveLoss, dyadicExponent])

theorem chord_53 : AdmissibleExponent 18 56 (1613166058841/40000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 56) (t := (3/4 : ℝ))
    (half_27_01) (half_31_00)
    (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private def half_28_01_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (267966517/5000000000 : ℝ)

private theorem half_28_01_total1 : total half_28_01_φ1=(267966517/5000000000 : ℝ) := by
  norm_num [half_28_01_φ1,total,emptyPhi,Fin.snoc]

private theorem half_28_01_bounds1 : ∀ l,0≤half_28_01_φ1 l ∧ half_28_01_φ1 l≤1 ∧
    0≤shiftExponents 18 half_28_01_φ1 l :=
  alternate_bounds_snoc emptyPhi (267966517/5000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_28_01_φ2 : Fin 2 → ℝ := Fin.snoc half_28_01_φ1 (122244607/2500000000 : ℝ)

private theorem half_28_01_total2 : total half_28_01_φ2=(512455731/5000000000 : ℝ) := by
  change total (Fin.snoc half_28_01_φ1 (122244607/2500000000 : ℝ))=(512455731/5000000000 : ℝ)
  rw [alternate_total_snoc,half_28_01_total1]
  norm_num

private theorem half_28_01_bounds2 : ∀ l,0≤half_28_01_φ2 l ∧ half_28_01_φ2 l≤1 ∧
    0≤shiftExponents 18 half_28_01_φ2 l :=
  alternate_bounds_snoc half_28_01_φ1 (122244607/2500000000 : ℝ) half_28_01_bounds1 (by norm_num)

private def half_28_01_φ3 : Fin 3 → ℝ := Fin.snoc half_28_01_φ2 (121126679/2500000000 : ℝ)

private theorem half_28_01_total3 : total half_28_01_φ3=(754709089/5000000000 : ℝ) := by
  change total (Fin.snoc half_28_01_φ2 (121126679/2500000000 : ℝ))=(754709089/5000000000 : ℝ)
  rw [alternate_total_snoc,half_28_01_total2]
  norm_num

private theorem half_28_01_bounds3 : ∀ l,0≤half_28_01_φ3 l ∧ half_28_01_φ3 l≤1 ∧
    0≤shiftExponents 18 half_28_01_φ3 l :=
  alternate_bounds_snoc half_28_01_φ2 (121126679/2500000000 : ℝ) half_28_01_bounds2 (by norm_num)

private def half_28_01_φ4 : Fin 4 → ℝ := Fin.snoc half_28_01_φ3 (30155891/625000000 : ℝ)

private theorem half_28_01_total4 : total half_28_01_φ4=(995956217/5000000000 : ℝ) := by
  change total (Fin.snoc half_28_01_φ3 (30155891/625000000 : ℝ))=(995956217/5000000000 : ℝ)
  rw [alternate_total_snoc,half_28_01_total3]
  norm_num

private theorem half_28_01_bounds4 : ∀ l,0≤half_28_01_φ4 l ∧ half_28_01_φ4 l≤1 ∧
    0≤shiftExponents 18 half_28_01_φ4 l :=
  alternate_bounds_snoc half_28_01_φ3 (30155891/625000000 : ℝ) half_28_01_bounds3 (by norm_num)

private def half_28_01_φ5 : Fin 5 → ℝ := Fin.snoc half_28_01_φ4 (235531987/5000000000 : ℝ)

private theorem half_28_01_total5 : total half_28_01_φ5=(307872051/1250000000 : ℝ) := by
  change total (Fin.snoc half_28_01_φ4 (235531987/5000000000 : ℝ))=(307872051/1250000000 : ℝ)
  rw [alternate_total_snoc,half_28_01_total4]
  norm_num

private theorem half_28_01_bounds5 : ∀ l,0≤half_28_01_φ5 l ∧ half_28_01_φ5 l≤1 ∧
    0≤shiftExponents 18 half_28_01_φ5 l :=
  alternate_bounds_snoc half_28_01_φ4 (235531987/5000000000 : ℝ) half_28_01_bounds4 (by norm_num)

private def half_28_01_φ6 : Fin 6 → ℝ := Fin.snoc half_28_01_φ5 (55419291/1250000000 : ℝ)

private theorem half_28_01_total6 : total half_28_01_φ6=(181645671/625000000 : ℝ) := by
  change total (Fin.snoc half_28_01_φ5 (55419291/1250000000 : ℝ))=(181645671/625000000 : ℝ)
  rw [alternate_total_snoc,half_28_01_total5]
  norm_num

private theorem half_28_01_bounds6 : ∀ l,0≤half_28_01_φ6 l ∧ half_28_01_φ6 l≤1 ∧
    0≤shiftExponents 18 half_28_01_φ6 l :=
  alternate_bounds_snoc half_28_01_φ5 (55419291/1250000000 : ℝ) half_28_01_bounds5 (by norm_num)

private def half_28_01_φ7 : Fin 7 → ℝ := Fin.snoc half_28_01_φ6 (208637331/5000000000 : ℝ)

private theorem half_28_01_total7 : total half_28_01_φ7=(1661802699/5000000000 : ℝ) := by
  change total (Fin.snoc half_28_01_φ6 (208637331/5000000000 : ℝ))=(1661802699/5000000000 : ℝ)
  rw [alternate_total_snoc,half_28_01_total6]
  norm_num

private theorem half_28_01_bounds7 : ∀ l,0≤half_28_01_φ7 l ∧ half_28_01_φ7 l≤1 ∧
    0≤shiftExponents 18 half_28_01_φ7 l :=
  alternate_bounds_snoc half_28_01_φ6 (208637331/5000000000 : ℝ) half_28_01_bounds6 (by norm_num)

private def half_28_01_φ8 : Fin 8 → ℝ := Fin.snoc half_28_01_φ7 (196364547/5000000000 : ℝ)

private theorem half_28_01_total8 : total half_28_01_φ8=(929083623/2500000000 : ℝ) := by
  change total (Fin.snoc half_28_01_φ7 (196364547/5000000000 : ℝ))=(929083623/2500000000 : ℝ)
  rw [alternate_total_snoc,half_28_01_total7]
  norm_num

private theorem half_28_01_bounds8 : ∀ l,0≤half_28_01_φ8 l ∧ half_28_01_φ8 l≤1 ∧
    0≤shiftExponents 18 half_28_01_φ8 l :=
  alternate_bounds_snoc half_28_01_φ7 (196364547/5000000000 : ℝ) half_28_01_bounds7 (by norm_num)

private theorem half_28_01_prefix : PrefixCondition 18 half_28_01_φ8 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_28_01_φ1, half_28_01_φ2, half_28_01_φ3, half_28_01_φ4, half_28_01_φ5, half_28_01_φ6, half_28_01_φ7, half_28_01_φ8, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_28_01_hF16 : SourcePowerBound
    (paddedMoment 18 0 16 256 half_28_01_φ8) (296953021453/3750000000 : ℝ) := by
  have h := padded_dyadic_divisor_power (k := 18) (j := 8) (r := 0) (n := 4) (D := 256)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_28_01_φ8
    (fun i => (half_28_01_bounds8 i).1) (fun i => (half_28_01_bounds8 i).2.1)
    (fun i => (half_28_01_bounds8 i).2.2) half_28_01_prefix
  convert h using 1 <;> norm_num [half_28_01_total1, half_28_01_total2, half_28_01_total3, half_28_01_total4, half_28_01_total5, half_28_01_total6, half_28_01_total7, half_28_01_total8, parameterExponent, curveLoss, dyadicExponent]

private theorem half_28_01_hF8 : SourcePowerBound
    (paddedMoment 18 0 8 256 half_28_01_φ8) (139769139637/3750000000 : ℝ) := by
  have h := padded_dyadic_divisor_power (k := 18) (j := 8) (r := 0) (n := 3) (D := 256)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_28_01_φ8
    (fun i => (half_28_01_bounds8 i).1) (fun i => (half_28_01_bounds8 i).2.1)
    (fun i => (half_28_01_bounds8 i).2.2) half_28_01_prefix
  convert h using 1 <;> norm_num [half_28_01_total1, half_28_01_total2, half_28_01_total3, half_28_01_total4, half_28_01_total5, half_28_01_total6, half_28_01_total7, half_28_01_total8, parameterExponent, curveLoss, dyadicExponent]

private theorem half_28_01_hx8 : SourcePowerBound
    (powerBoxCross 18 20 256 half_28_01_φ8) (190111631557/10000000000 : ℝ) := by
  have h := full_B_cross_power (k := 18) (s := 20) (r := 8) (v := 16) (t := 21) (D := 256)
    (a := (11/336 : ℝ)) (b := (5/336 : ℝ)) (c := (20/21 : ℝ))
    (by norm_num) half_28_01_φ8 (by norm_num [half_28_01_total1, half_28_01_total2, half_28_01_total3, half_28_01_total4, half_28_01_total5, half_28_01_total6, half_28_01_total7, half_28_01_total8, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_28_01_total1, half_28_01_total2, half_28_01_total3, half_28_01_total4, half_28_01_total5, half_28_01_total6, half_28_01_total7, half_28_01_total8, parameterExponent, curveLoss, dyadicExponent]) half_28_01_hF8 half_28_01_hF16
    (half_21_01)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_28_01_total1, half_28_01_total2, half_28_01_total3, half_28_01_total4, half_28_01_total5, half_28_01_total6, half_28_01_total7, half_28_01_total8, parameterExponent, curveLoss, dyadicExponent])

private theorem half_28_01_hx7 : SourcePowerBound
    (powerBoxCross 18 21 128 half_28_01_φ7) (12989619143/625000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 7) (s := 21) (u := 19) (t := 22)
    (D := 128) (ψ := (196364547/5000000000 : ℝ)) half_28_01_φ7
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_28_01_bounds7 l).1) (fun l => (half_28_01_bounds7 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_28_01_total1, half_28_01_total2, half_28_01_total3, half_28_01_total4, half_28_01_total5, half_28_01_total6, half_28_01_total7, half_28_01_total8, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_20_01) (half_22_01)
    (by simpa only [half_28_01_φ8, show (2:ℝ)*128=256 by norm_num] using half_28_01_hx8)
  exact h.weaken (by norm_num [half_28_01_total1, half_28_01_total2, half_28_01_total3, half_28_01_total4, half_28_01_total5, half_28_01_total6, half_28_01_total7, half_28_01_total8, parameterExponent, curveLoss, dyadicExponent])

private theorem half_28_01_hx6 : SourcePowerBound
    (powerBoxCross 18 22 64 half_28_01_φ6) (228422067501/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 6) (s := 22) (u := 20) (t := 23)
    (D := 64) (ψ := (208637331/5000000000 : ℝ)) half_28_01_φ6
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_28_01_bounds6 l).1) (fun l => (half_28_01_bounds6 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_28_01_total1, half_28_01_total2, half_28_01_total3, half_28_01_total4, half_28_01_total5, half_28_01_total6, half_28_01_total7, half_28_01_total8, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_21_01) (half_23_01)
    (by simpa only [half_28_01_φ7, show (2:ℝ)*64=128 by norm_num] using half_28_01_hx7)
  exact h.weaken (by norm_num [half_28_01_total1, half_28_01_total2, half_28_01_total3, half_28_01_total4, half_28_01_total5, half_28_01_total6, half_28_01_total7, half_28_01_total8, parameterExponent, curveLoss, dyadicExponent])

private theorem half_28_01_hx5 : SourcePowerBound
    (powerBoxCross 18 23 32 half_28_01_φ5) (125989011051/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 5) (s := 23) (u := 21) (t := 24)
    (D := 32) (ψ := (55419291/1250000000 : ℝ)) half_28_01_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_28_01_bounds5 l).1) (fun l => (half_28_01_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_28_01_total1, half_28_01_total2, half_28_01_total3, half_28_01_total4, half_28_01_total5, half_28_01_total6, half_28_01_total7, half_28_01_total8, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_22_01) (half_24_01)
    (by simpa only [half_28_01_φ6, show (2:ℝ)*32=64 by norm_num] using half_28_01_hx6)
  exact h.weaken (by norm_num [half_28_01_total1, half_28_01_total2, half_28_01_total3, half_28_01_total4, half_28_01_total5, half_28_01_total6, half_28_01_total7, half_28_01_total8, parameterExponent, curveLoss, dyadicExponent])

private theorem half_28_01_hx4 : SourcePowerBound
    (powerBoxCross 18 24 16 half_28_01_φ4) (34835499497/1250000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 24) (u := 22) (t := 25)
    (D := 16) (ψ := (235531987/5000000000 : ℝ)) half_28_01_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_28_01_bounds4 l).1) (fun l => (half_28_01_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_28_01_total1, half_28_01_total2, half_28_01_total3, half_28_01_total4, half_28_01_total5, half_28_01_total6, half_28_01_total7, half_28_01_total8, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_23_01) (half_25_01)
    (by simpa only [half_28_01_φ5, show (2:ℝ)*16=32 by norm_num] using half_28_01_hx5)
  exact h.weaken (by norm_num [half_28_01_total1, half_28_01_total2, half_28_01_total3, half_28_01_total4, half_28_01_total5, half_28_01_total6, half_28_01_total7, half_28_01_total8, parameterExponent, curveLoss, dyadicExponent])

private theorem half_28_01_hx3 : SourcePowerBound
    (powerBoxCross 18 25 8 half_28_01_φ3) (153934323211/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 25) (u := 23) (t := 26)
    (D := 8) (ψ := (30155891/625000000 : ℝ)) half_28_01_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_28_01_bounds3 l).1) (fun l => (half_28_01_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_28_01_total1, half_28_01_total2, half_28_01_total3, half_28_01_total4, half_28_01_total5, half_28_01_total6, half_28_01_total7, half_28_01_total8, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_24_01) (half_26_01)
    (by simpa only [half_28_01_φ4, show (2:ℝ)*8=16 by norm_num] using half_28_01_hx4)
  exact h.weaken (by norm_num [half_28_01_total1, half_28_01_total2, half_28_01_total3, half_28_01_total4, half_28_01_total5, half_28_01_total6, half_28_01_total7, half_28_01_total8, parameterExponent, curveLoss, dyadicExponent])

private theorem half_28_01_hx2 : SourcePowerBound
    (powerBoxCross 18 26 4 half_28_01_φ2) (169553101357/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 26) (u := 24) (t := 27)
    (D := 4) (ψ := (121126679/2500000000 : ℝ)) half_28_01_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_28_01_bounds2 l).1) (fun l => (half_28_01_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_28_01_total1, half_28_01_total2, half_28_01_total3, half_28_01_total4, half_28_01_total5, half_28_01_total6, half_28_01_total7, half_28_01_total8, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_25_01) (half_27_01)
    (by simpa only [half_28_01_φ3, show (2:ℝ)*4=8 by norm_num] using half_28_01_hx3)
  exact h.weaken (by norm_num [half_28_01_total1, half_28_01_total2, half_28_01_total3, half_28_01_total4, half_28_01_total5, half_28_01_total6, half_28_01_total7, half_28_01_total8, parameterExponent, curveLoss, dyadicExponent])

private theorem half_28_01_hx1 : SourcePowerBound
    (powerBoxCross 18 27 2 half_28_01_φ1) (5832898681/156250000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 27) (u := 25) (t := 28)
    (D := 2) (ψ := (122244607/2500000000 : ℝ)) half_28_01_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_28_01_bounds1 l).1) (fun l => (half_28_01_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_28_01_total1, half_28_01_total2, half_28_01_total3, half_28_01_total4, half_28_01_total5, half_28_01_total6, half_28_01_total7, half_28_01_total8, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_26_01) (chord_53)
    (by simpa only [half_28_01_φ2, show (2:ℝ)*2=4 by norm_num] using half_28_01_hx2)
  exact h.weaken (by norm_num [half_28_01_total1, half_28_01_total2, half_28_01_total3, half_28_01_total4, half_28_01_total5, half_28_01_total6, half_28_01_total7, half_28_01_total8, parameterExponent, curveLoss, dyadicExponent])

theorem half_28_01 : AdmissibleExponent 18 56 (200854983193/5000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 26) (ψ := (267966517/5000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_27_01)
    (by simpa only [half_28_01_φ1] using half_28_01_hx1)
  exact admissibleExponent_mono h (by norm_num [half_28_01_total1, half_28_01_total2, half_28_01_total3, half_28_01_total4, half_28_01_total5, half_28_01_total6, half_28_01_total7, half_28_01_total8, parameterExponent, curveLoss, dyadicExponent])

theorem chord_56 : AdmissibleExponent 18 58 (42221609451/1000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 58) (t := (2/3 : ℝ))
    (half_28_01) (half_31_00)
    (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private def half_29_01_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (548471663/10000000000 : ℝ)

private theorem half_29_01_total1 : total half_29_01_φ1=(548471663/10000000000 : ℝ) := by
  norm_num [half_29_01_φ1,total,emptyPhi,Fin.snoc]

private theorem half_29_01_bounds1 : ∀ l,0≤half_29_01_φ1 l ∧ half_29_01_φ1 l≤1 ∧
    0≤shiftExponents 18 half_29_01_φ1 l :=
  alternate_bounds_snoc emptyPhi (548471663/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_29_01_φ2 : Fin 2 → ℝ := Fin.snoc half_29_01_φ1 (247368493/5000000000 : ℝ)

private theorem half_29_01_total2 : total half_29_01_φ2=(1043208649/10000000000 : ℝ) := by
  change total (Fin.snoc half_29_01_φ1 (247368493/5000000000 : ℝ))=(1043208649/10000000000 : ℝ)
  rw [alternate_total_snoc,half_29_01_total1]
  norm_num

private theorem half_29_01_bounds2 : ∀ l,0≤half_29_01_φ2 l ∧ half_29_01_φ2 l≤1 ∧
    0≤shiftExponents 18 half_29_01_φ2 l :=
  alternate_bounds_snoc half_29_01_φ1 (247368493/5000000000 : ℝ) half_29_01_bounds1 (by norm_num)

private def half_29_01_φ3 : Fin 3 → ℝ := Fin.snoc half_29_01_φ2 (49064437/1000000000 : ℝ)

private theorem half_29_01_total3 : total half_29_01_φ3=(1533853019/10000000000 : ℝ) := by
  change total (Fin.snoc half_29_01_φ2 (49064437/1000000000 : ℝ))=(1533853019/10000000000 : ℝ)
  rw [alternate_total_snoc,half_29_01_total2]
  norm_num

private theorem half_29_01_bounds3 : ∀ l,0≤half_29_01_φ3 l ∧ half_29_01_φ3 l≤1 ∧
    0≤shiftExponents 18 half_29_01_φ3 l :=
  alternate_bounds_snoc half_29_01_φ2 (49064437/1000000000 : ℝ) half_29_01_bounds2 (by norm_num)

private def half_29_01_φ4 : Fin 4 → ℝ := Fin.snoc half_29_01_φ3 (97835483/2000000000 : ℝ)

private theorem half_29_01_total4 : total half_29_01_φ4=(1011515217/5000000000 : ℝ) := by
  change total (Fin.snoc half_29_01_φ3 (97835483/2000000000 : ℝ))=(1011515217/5000000000 : ℝ)
  rw [alternate_total_snoc,half_29_01_total3]
  norm_num

private theorem half_29_01_bounds4 : ∀ l,0≤half_29_01_φ4 l ∧ half_29_01_φ4 l≤1 ∧
    0≤shiftExponents 18 half_29_01_φ4 l :=
  alternate_bounds_snoc half_29_01_φ3 (97835483/2000000000 : ℝ) half_29_01_bounds3 (by norm_num)

private def half_29_01_φ5 : Fin 5 → ℝ := Fin.snoc half_29_01_φ4 (469233503/10000000000 : ℝ)

private theorem half_29_01_total5 : total half_29_01_φ5=(2492263937/10000000000 : ℝ) := by
  change total (Fin.snoc half_29_01_φ4 (469233503/10000000000 : ℝ))=(2492263937/10000000000 : ℝ)
  rw [alternate_total_snoc,half_29_01_total4]
  norm_num

private theorem half_29_01_bounds5 : ∀ l,0≤half_29_01_φ5 l ∧ half_29_01_φ5 l≤1 ∧
    0≤shiftExponents 18 half_29_01_φ5 l :=
  alternate_bounds_snoc half_29_01_φ4 (469233503/10000000000 : ℝ) half_29_01_bounds4 (by norm_num)

private def half_29_01_φ6 : Fin 6 → ℝ := Fin.snoc half_29_01_φ5 (110407883/2500000000 : ℝ)

private theorem half_29_01_total6 : total half_29_01_φ6=(2933895469/10000000000 : ℝ) := by
  change total (Fin.snoc half_29_01_φ5 (110407883/2500000000 : ℝ))=(2933895469/10000000000 : ℝ)
  rw [alternate_total_snoc,half_29_01_total5]
  norm_num

private theorem half_29_01_bounds6 : ∀ l,0≤half_29_01_φ6 l ∧ half_29_01_φ6 l≤1 ∧
    0≤shiftExponents 18 half_29_01_φ6 l :=
  alternate_bounds_snoc half_29_01_φ5 (110407883/2500000000 : ℝ) half_29_01_bounds5 (by norm_num)

private def half_29_01_φ7 : Fin 7 → ℝ := Fin.snoc half_29_01_φ6 (415653207/10000000000 : ℝ)

private theorem half_29_01_total7 : total half_29_01_φ7=(837387169/2500000000 : ℝ) := by
  change total (Fin.snoc half_29_01_φ6 (415653207/10000000000 : ℝ))=(837387169/2500000000 : ℝ)
  rw [alternate_total_snoc,half_29_01_total6]
  norm_num

private theorem half_29_01_bounds7 : ∀ l,0≤half_29_01_φ7 l ∧ half_29_01_φ7 l≤1 ∧
    0≤shiftExponents 18 half_29_01_φ7 l :=
  alternate_bounds_snoc half_29_01_φ6 (415653207/10000000000 : ℝ) half_29_01_bounds6 (by norm_num)

private def half_29_01_φ8 : Fin 8 → ℝ := Fin.snoc half_29_01_φ7 (195601509/5000000000 : ℝ)

private theorem half_29_01_total8 : total half_29_01_φ8=(1870375847/5000000000 : ℝ) := by
  change total (Fin.snoc half_29_01_φ7 (195601509/5000000000 : ℝ))=(1870375847/5000000000 : ℝ)
  rw [alternate_total_snoc,half_29_01_total7]
  norm_num

private theorem half_29_01_bounds8 : ∀ l,0≤half_29_01_φ8 l ∧ half_29_01_φ8 l≤1 ∧
    0≤shiftExponents 18 half_29_01_φ8 l :=
  alternate_bounds_snoc half_29_01_φ7 (195601509/5000000000 : ℝ) half_29_01_bounds7 (by norm_num)

private theorem half_29_01_prefix : PrefixCondition 18 half_29_01_φ8 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_29_01_φ1, half_29_01_φ2, half_29_01_φ3, half_29_01_φ4, half_29_01_φ5, half_29_01_φ6, half_29_01_φ7, half_29_01_φ8, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_29_01_hF16 : SourcePowerBound
    (paddedMoment 18 0 16 256 half_29_01_φ8) (584273456717/7500000000 : ℝ) := by
  have h := padded_dyadic_divisor_power (k := 18) (j := 8) (r := 0) (n := 4) (D := 256)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_29_01_φ8
    (fun i => (half_29_01_bounds8 i).1) (fun i => (half_29_01_bounds8 i).2.1)
    (fun i => (half_29_01_bounds8 i).2.2) half_29_01_prefix
  convert h using 1 <;> norm_num [half_29_01_total1, half_29_01_total2, half_29_01_total3, half_29_01_total4, half_29_01_total5, half_29_01_total6, half_29_01_total7, half_29_01_total8, parameterExponent, curveLoss, dyadicExponent]

private theorem half_29_01_hx8 : SourcePowerBound
    (powerBoxCross 18 21 256 half_29_01_φ8) (99843621551/5000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 21) (r := 16) (v := 21) (w := 22) (D := 256)
    (a := (1/32 : ℝ)) (b := (5/16 : ℝ)) (c := (21/32 : ℝ))
    (by norm_num) half_29_01_φ8 (by norm_num [half_29_01_total1, half_29_01_total2, half_29_01_total3, half_29_01_total4, half_29_01_total5, half_29_01_total6, half_29_01_total7, half_29_01_total8, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_29_01_total1, half_29_01_total2, half_29_01_total3, half_29_01_total4, half_29_01_total5, half_29_01_total6, half_29_01_total7, half_29_01_total8, parameterExponent, curveLoss, dyadicExponent]) half_29_01_hF16
    (half_21_01) (half_22_01)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_29_01_total1, half_29_01_total2, half_29_01_total3, half_29_01_total4, half_29_01_total5, half_29_01_total6, half_29_01_total7, half_29_01_total8, parameterExponent, curveLoss, dyadicExponent])

private theorem half_29_01_hx7 : SourcePowerBound
    (powerBoxCross 18 22 128 half_29_01_φ7) (21813311757/1000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 7) (s := 22) (u := 20) (t := 23)
    (D := 128) (ψ := (195601509/5000000000 : ℝ)) half_29_01_φ7
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_29_01_bounds7 l).1) (fun l => (half_29_01_bounds7 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_29_01_total1, half_29_01_total2, half_29_01_total3, half_29_01_total4, half_29_01_total5, half_29_01_total6, half_29_01_total7, half_29_01_total8, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_21_01) (half_23_01)
    (by simpa only [half_29_01_φ8, show (2:ℝ)*128=256 by norm_num] using half_29_01_hx8)
  exact h.weaken (by norm_num [half_29_01_total1, half_29_01_total2, half_29_01_total3, half_29_01_total4, half_29_01_total5, half_29_01_total6, half_29_01_total7, half_29_01_total8, parameterExponent, curveLoss, dyadicExponent])

private theorem half_29_01_hx6 : SourcePowerBound
    (powerBoxCross 18 23 64 half_29_01_φ6) (239476912811/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 6) (s := 23) (u := 21) (t := 24)
    (D := 64) (ψ := (415653207/10000000000 : ℝ)) half_29_01_φ6
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_29_01_bounds6 l).1) (fun l => (half_29_01_bounds6 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_29_01_total1, half_29_01_total2, half_29_01_total3, half_29_01_total4, half_29_01_total5, half_29_01_total6, half_29_01_total7, half_29_01_total8, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_22_01) (half_24_01)
    (by simpa only [half_29_01_φ7, show (2:ℝ)*64=128 by norm_num] using half_29_01_hx7)
  exact h.weaken (by norm_num [half_29_01_total1, half_29_01_total2, half_29_01_total3, half_29_01_total4, half_29_01_total5, half_29_01_total6, half_29_01_total7, half_29_01_total8, parameterExponent, curveLoss, dyadicExponent])

private theorem half_29_01_hx5 : SourcePowerBound
    (powerBoxCross 18 24 32 half_29_01_φ5) (52766338067/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 5) (s := 24) (u := 22) (t := 25)
    (D := 32) (ψ := (110407883/2500000000 : ℝ)) half_29_01_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_29_01_bounds5 l).1) (fun l => (half_29_01_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_29_01_total1, half_29_01_total2, half_29_01_total3, half_29_01_total4, half_29_01_total5, half_29_01_total6, half_29_01_total7, half_29_01_total8, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_23_01) (half_25_01)
    (by simpa only [half_29_01_φ6, show (2:ℝ)*32=64 by norm_num] using half_29_01_hx6)
  exact h.weaken (by norm_num [half_29_01_total1, half_29_01_total2, half_29_01_total3, half_29_01_total4, half_29_01_total5, half_29_01_total6, half_29_01_total7, half_29_01_total8, parameterExponent, curveLoss, dyadicExponent])

private theorem half_29_01_hx4 : SourcePowerBound
    (powerBoxCross 18 25 16 half_29_01_φ4) (36423475989/1250000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 25) (u := 23) (t := 26)
    (D := 16) (ψ := (469233503/10000000000 : ℝ)) half_29_01_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_29_01_bounds4 l).1) (fun l => (half_29_01_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_29_01_total1, half_29_01_total2, half_29_01_total3, half_29_01_total4, half_29_01_total5, half_29_01_total6, half_29_01_total7, half_29_01_total8, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_24_01) (half_26_01)
    (by simpa only [half_29_01_φ5, show (2:ℝ)*16=32 by norm_num] using half_29_01_hx5)
  exact h.weaken (by norm_num [half_29_01_total1, half_29_01_total2, half_29_01_total3, half_29_01_total4, half_29_01_total5, half_29_01_total6, half_29_01_total7, half_29_01_total8, parameterExponent, curveLoss, dyadicExponent])

private theorem half_29_01_hx3 : SourcePowerBound
    (powerBoxCross 18 26 8 half_29_01_φ3) (80475006889/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 26) (u := 24) (t := 27)
    (D := 8) (ψ := (97835483/2000000000 : ℝ)) half_29_01_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_29_01_bounds3 l).1) (fun l => (half_29_01_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_29_01_total1, half_29_01_total2, half_29_01_total3, half_29_01_total4, half_29_01_total5, half_29_01_total6, half_29_01_total7, half_29_01_total8, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_25_01) (half_27_01)
    (by simpa only [half_29_01_φ4, show (2:ℝ)*8=16 by norm_num] using half_29_01_hx4)
  exact h.weaken (by norm_num [half_29_01_total1, half_29_01_total2, half_29_01_total3, half_29_01_total4, half_29_01_total5, half_29_01_total6, half_29_01_total7, half_29_01_total8, parameterExponent, curveLoss, dyadicExponent])

private theorem half_29_01_hx2 : SourcePowerBound
    (powerBoxCross 18 27 4 half_29_01_φ2) (88623947331/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 27) (u := 25) (t := 28)
    (D := 4) (ψ := (49064437/1000000000 : ℝ)) half_29_01_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_29_01_bounds2 l).1) (fun l => (half_29_01_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_29_01_total1, half_29_01_total2, half_29_01_total3, half_29_01_total4, half_29_01_total5, half_29_01_total6, half_29_01_total7, half_29_01_total8, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_26_01) (half_28_01)
    (by simpa only [half_29_01_φ3, show (2:ℝ)*4=8 by norm_num] using half_29_01_hx3)
  exact h.weaken (by norm_num [half_29_01_total1, half_29_01_total2, half_29_01_total3, half_29_01_total4, half_29_01_total5, half_29_01_total6, half_29_01_total7, half_29_01_total8, parameterExponent, curveLoss, dyadicExponent])

private theorem half_29_01_hx1 : SourcePowerBound
    (powerBoxCross 18 28 2 half_29_01_φ1) (12194555773/312500000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 28) (u := 26) (t := 29)
    (D := 2) (ψ := (247368493/5000000000 : ℝ)) half_29_01_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_29_01_bounds1 l).1) (fun l => (half_29_01_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_29_01_total1, half_29_01_total2, half_29_01_total3, half_29_01_total4, half_29_01_total5, half_29_01_total6, half_29_01_total7, half_29_01_total8, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_27_01) (chord_56)
    (by simpa only [half_29_01_φ2, show (2:ℝ)*2=4 by norm_num] using half_29_01_hx2)
  exact h.weaken (by norm_num [half_29_01_total1, half_29_01_total2, half_29_01_total3, half_29_01_total4, half_29_01_total5, half_29_01_total6, half_29_01_total7, half_29_01_total8, parameterExponent, curveLoss, dyadicExponent])

theorem half_29_01 : AdmissibleExponent 18 58 (420391726201/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 27) (ψ := (548471663/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_28_01)
    (by simpa only [half_29_01_φ1] using half_29_01_hx1)
  exact admissibleExponent_mono h (by norm_num [half_29_01_total1, half_29_01_total2, half_29_01_total3, half_29_01_total4, half_29_01_total5, half_29_01_total6, half_29_01_total7, half_29_01_total8, parameterExponent, curveLoss, dyadicExponent])

theorem chord_58 : AdmissibleExponent 18 60 (883620076959/20000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 60) (t := (1/2 : ℝ))
    (half_29_01) (half_31_00)
    (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private def half_30_01_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (111111111/2000000000 : ℝ)

private theorem half_30_01_total1 : total half_30_01_φ1=(111111111/2000000000 : ℝ) := by
  norm_num [half_30_01_φ1,total,emptyPhi,Fin.snoc]

private theorem half_30_01_bounds1 : ∀ l,0≤half_30_01_φ1 l ∧ half_30_01_φ1 l≤1 ∧
    0≤shiftExponents 18 half_30_01_φ1 l :=
  alternate_bounds_snoc emptyPhi (111111111/2000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_30_01_φ2 : Fin 2 → ℝ := Fin.snoc half_30_01_φ1 (10019191/200000000 : ℝ)

private theorem half_30_01_total2 : total half_30_01_φ2=(211303021/2000000000 : ℝ) := by
  change total (Fin.snoc half_30_01_φ1 (10019191/200000000 : ℝ))=(211303021/2000000000 : ℝ)
  rw [alternate_total_snoc,half_30_01_total1]
  norm_num

private theorem half_30_01_bounds2 : ∀ l,0≤half_30_01_φ2 l ∧ half_30_01_φ2 l≤1 ∧
    0≤shiftExponents 18 half_30_01_φ2 l :=
  alternate_bounds_snoc half_30_01_φ1 (10019191/200000000 : ℝ) half_30_01_bounds1 (by norm_num)

private def half_30_01_φ3 : Fin 3 → ℝ := Fin.snoc half_30_01_φ2 (248272129/5000000000 : ℝ)

private theorem half_30_01_total3 : total half_30_01_φ3=(1553059363/10000000000 : ℝ) := by
  change total (Fin.snoc half_30_01_φ2 (248272129/5000000000 : ℝ))=(1553059363/10000000000 : ℝ)
  rw [alternate_total_snoc,half_30_01_total2]
  norm_num

private theorem half_30_01_bounds3 : ∀ l,0≤half_30_01_φ3 l ∧ half_30_01_φ3 l≤1 ∧
    0≤shiftExponents 18 half_30_01_φ3 l :=
  alternate_bounds_snoc half_30_01_φ2 (248272129/5000000000 : ℝ) half_30_01_bounds2 (by norm_num)

private def half_30_01_φ4 : Fin 4 → ℝ := Fin.snoc half_30_01_φ3 (61953657/1250000000 : ℝ)

private theorem half_30_01_total4 : total half_30_01_φ4=(2048688619/10000000000 : ℝ) := by
  change total (Fin.snoc half_30_01_φ3 (61953657/1250000000 : ℝ))=(2048688619/10000000000 : ℝ)
  rw [alternate_total_snoc,half_30_01_total3]
  norm_num

private theorem half_30_01_bounds4 : ∀ l,0≤half_30_01_φ4 l ∧ half_30_01_φ4 l≤1 ∧
    0≤shiftExponents 18 half_30_01_φ4 l :=
  alternate_bounds_snoc half_30_01_φ3 (61953657/1250000000 : ℝ) half_30_01_bounds3 (by norm_num)

private def half_30_01_φ5 : Fin 5 → ℝ := Fin.snoc half_30_01_φ4 (233862099/5000000000 : ℝ)

private theorem half_30_01_total5 : total half_30_01_φ5=(2516412817/10000000000 : ℝ) := by
  change total (Fin.snoc half_30_01_φ4 (233862099/5000000000 : ℝ))=(2516412817/10000000000 : ℝ)
  rw [alternate_total_snoc,half_30_01_total4]
  norm_num

private theorem half_30_01_bounds5 : ∀ l,0≤half_30_01_φ5 l ∧ half_30_01_φ5 l≤1 ∧
    0≤shiftExponents 18 half_30_01_φ5 l :=
  alternate_bounds_snoc half_30_01_φ4 (233862099/5000000000 : ℝ) half_30_01_bounds4 (by norm_num)

private def half_30_01_φ6 : Fin 6 → ℝ := Fin.snoc half_30_01_φ5 (44021101/1000000000 : ℝ)

private theorem half_30_01_total6 : total half_30_01_φ6=(2956623827/10000000000 : ℝ) := by
  change total (Fin.snoc half_30_01_φ5 (44021101/1000000000 : ℝ))=(2956623827/10000000000 : ℝ)
  rw [alternate_total_snoc,half_30_01_total5]
  norm_num

private theorem half_30_01_bounds6 : ∀ l,0≤half_30_01_φ6 l ∧ half_30_01_φ6 l≤1 ∧
    0≤shiftExponents 18 half_30_01_φ6 l :=
  alternate_bounds_snoc half_30_01_φ5 (44021101/1000000000 : ℝ) half_30_01_bounds5 (by norm_num)

private def half_30_01_φ7 : Fin 7 → ℝ := Fin.snoc half_30_01_φ6 (82863249/2000000000 : ℝ)

private theorem half_30_01_total7 : total half_30_01_φ7=(421367509/1250000000 : ℝ) := by
  change total (Fin.snoc half_30_01_φ6 (82863249/2000000000 : ℝ))=(421367509/1250000000 : ℝ)
  rw [alternate_total_snoc,half_30_01_total6]
  norm_num

private theorem half_30_01_bounds7 : ∀ l,0≤half_30_01_φ7 l ∧ half_30_01_φ7 l≤1 ∧
    0≤shiftExponents 18 half_30_01_φ7 l :=
  alternate_bounds_snoc half_30_01_φ6 (82863249/2000000000 : ℝ) half_30_01_bounds6 (by norm_num)

private def half_30_01_φ8 : Fin 8 → ℝ := Fin.snoc half_30_01_φ7 (389944701/10000000000 : ℝ)

private theorem half_30_01_total8 : total half_30_01_φ8=(3760884773/10000000000 : ℝ) := by
  change total (Fin.snoc half_30_01_φ7 (389944701/10000000000 : ℝ))=(3760884773/10000000000 : ℝ)
  rw [alternate_total_snoc,half_30_01_total7]
  norm_num

private theorem half_30_01_bounds8 : ∀ l,0≤half_30_01_φ8 l ∧ half_30_01_φ8 l≤1 ∧
    0≤shiftExponents 18 half_30_01_φ8 l :=
  alternate_bounds_snoc half_30_01_φ7 (389944701/10000000000 : ℝ) half_30_01_bounds7 (by norm_num)

private theorem half_30_01_prefix : PrefixCondition 18 half_30_01_φ8 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_30_01_φ1, half_30_01_φ2, half_30_01_φ3, half_30_01_φ4, half_30_01_φ5, half_30_01_φ6, half_30_01_φ7, half_30_01_φ8, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_30_01_hF16 : SourcePowerBound
    (paddedMoment 18 0 16 256 half_30_01_φ8) (1152661914103/15000000000 : ℝ) := by
  have h := padded_dyadic_divisor_power (k := 18) (j := 8) (r := 0) (n := 4) (D := 256)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_30_01_φ8
    (fun i => (half_30_01_bounds8 i).1) (fun i => (half_30_01_bounds8 i).2.1)
    (fun i => (half_30_01_bounds8 i).2.2) half_30_01_prefix
  convert h using 1 <;> norm_num [half_30_01_total1, half_30_01_total2, half_30_01_total3, half_30_01_total4, half_30_01_total5, half_30_01_total6, half_30_01_total7, half_30_01_total8, parameterExponent, curveLoss, dyadicExponent]

private theorem half_30_01_hx8 : SourcePowerBound
    (powerBoxCross 18 22 256 half_30_01_φ8) (104772148793/5000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 22) (r := 16) (v := 22) (w := 23) (D := 256)
    (a := (1/32 : ℝ)) (b := (9/32 : ℝ)) (c := (11/16 : ℝ))
    (by norm_num) half_30_01_φ8 (by norm_num [half_30_01_total1, half_30_01_total2, half_30_01_total3, half_30_01_total4, half_30_01_total5, half_30_01_total6, half_30_01_total7, half_30_01_total8, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_30_01_total1, half_30_01_total2, half_30_01_total3, half_30_01_total4, half_30_01_total5, half_30_01_total6, half_30_01_total7, half_30_01_total8, parameterExponent, curveLoss, dyadicExponent]) half_30_01_hF16
    (half_22_01) (half_23_01)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_30_01_total1, half_30_01_total2, half_30_01_total3, half_30_01_total4, half_30_01_total5, half_30_01_total6, half_30_01_total7, half_30_01_total8, parameterExponent, curveLoss, dyadicExponent])

private theorem half_30_01_hx7 : SourcePowerBound
    (powerBoxCross 18 23 128 half_30_01_φ7) (57178678499/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 7) (s := 23) (u := 21) (t := 24)
    (D := 128) (ψ := (389944701/10000000000 : ℝ)) half_30_01_φ7
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_30_01_bounds7 l).1) (fun l => (half_30_01_bounds7 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_30_01_total1, half_30_01_total2, half_30_01_total3, half_30_01_total4, half_30_01_total5, half_30_01_total6, half_30_01_total7, half_30_01_total8, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_22_01) (half_24_01)
    (by simpa only [half_30_01_φ8, show (2:ℝ)*128=256 by norm_num] using half_30_01_hx8)
  exact h.weaken (by norm_num [half_30_01_total1, half_30_01_total2, half_30_01_total3, half_30_01_total4, half_30_01_total5, half_30_01_total6, half_30_01_total7, half_30_01_total8, parameterExponent, curveLoss, dyadicExponent])

private theorem half_30_01_hx6 : SourcePowerBound
    (powerBoxCross 18 24 64 half_30_01_φ6) (1959587891/78125000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 6) (s := 24) (u := 22) (t := 25)
    (D := 64) (ψ := (82863249/2000000000 : ℝ)) half_30_01_φ6
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_30_01_bounds6 l).1) (fun l => (half_30_01_bounds6 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_30_01_total1, half_30_01_total2, half_30_01_total3, half_30_01_total4, half_30_01_total5, half_30_01_total6, half_30_01_total7, half_30_01_total8, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_23_01) (half_25_01)
    (by simpa only [half_30_01_φ7, show (2:ℝ)*64=128 by norm_num] using half_30_01_hx7)
  exact h.weaken (by norm_num [half_30_01_total1, half_30_01_total2, half_30_01_total3, half_30_01_total4, half_30_01_total5, half_30_01_total6, half_30_01_total7, half_30_01_total8, parameterExponent, curveLoss, dyadicExponent])

private theorem half_30_01_hx5 : SourcePowerBound
    (powerBoxCross 18 25 32 half_30_01_φ5) (276001805091/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 5) (s := 25) (u := 23) (t := 26)
    (D := 32) (ψ := (44021101/1000000000 : ℝ)) half_30_01_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_30_01_bounds5 l).1) (fun l => (half_30_01_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_30_01_total1, half_30_01_total2, half_30_01_total3, half_30_01_total4, half_30_01_total5, half_30_01_total6, half_30_01_total7, half_30_01_total8, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_24_01) (half_26_01)
    (by simpa only [half_30_01_φ6, show (2:ℝ)*32=64 by norm_num] using half_30_01_hx6)
  exact h.weaken (by norm_num [half_30_01_total1, half_30_01_total2, half_30_01_total3, half_30_01_total4, half_30_01_total5, half_30_01_total6, half_30_01_total7, half_30_01_total8, parameterExponent, curveLoss, dyadicExponent])

private theorem half_30_01_hx4 : SourcePowerBound
    (powerBoxCross 18 26 16 half_30_01_φ4) (152219085949/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 26) (u := 24) (t := 27)
    (D := 16) (ψ := (233862099/5000000000 : ℝ)) half_30_01_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_30_01_bounds4 l).1) (fun l => (half_30_01_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_30_01_total1, half_30_01_total2, half_30_01_total3, half_30_01_total4, half_30_01_total5, half_30_01_total6, half_30_01_total7, half_30_01_total8, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_25_01) (half_27_01)
    (by simpa only [half_30_01_φ5, show (2:ℝ)*16=32 by norm_num] using half_30_01_hx5)
  exact h.weaken (by norm_num [half_30_01_total1, half_30_01_total2, half_30_01_total3, half_30_01_total4, half_30_01_total5, half_30_01_total6, half_30_01_total7, half_30_01_total8, parameterExponent, curveLoss, dyadicExponent])

private theorem half_30_01_hx3 : SourcePowerBound
    (powerBoxCross 18 27 8 half_30_01_φ3) (1050992623/31250000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 27) (u := 25) (t := 28)
    (D := 8) (ψ := (61953657/1250000000 : ℝ)) half_30_01_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_30_01_bounds3 l).1) (fun l => (half_30_01_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_30_01_total1, half_30_01_total2, half_30_01_total3, half_30_01_total4, half_30_01_total5, half_30_01_total6, half_30_01_total7, half_30_01_total8, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_26_01) (half_28_01)
    (by simpa only [half_30_01_φ4, show (2:ℝ)*8=16 by norm_num] using half_30_01_hx4)
  exact h.weaken (by norm_num [half_30_01_total1, half_30_01_total2, half_30_01_total3, half_30_01_total4, half_30_01_total5, half_30_01_total6, half_30_01_total7, half_30_01_total8, parameterExponent, curveLoss, dyadicExponent])

private theorem half_30_01_hx2 : SourcePowerBound
    (powerBoxCross 18 28 4 half_30_01_φ2) (92581304197/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 28) (u := 26) (t := 29)
    (D := 4) (ψ := (248272129/5000000000 : ℝ)) half_30_01_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_30_01_bounds2 l).1) (fun l => (half_30_01_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_30_01_total1, half_30_01_total2, half_30_01_total3, half_30_01_total4, half_30_01_total5, half_30_01_total6, half_30_01_total7, half_30_01_total8, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_27_01) (half_29_01)
    (by simpa only [half_30_01_φ3, show (2:ℝ)*4=8 by norm_num] using half_30_01_hx3)
  exact h.weaken (by norm_num [half_30_01_total1, half_30_01_total2, half_30_01_total3, half_30_01_total4, half_30_01_total5, half_30_01_total6, half_30_01_total7, half_30_01_total8, parameterExponent, curveLoss, dyadicExponent])

private theorem half_30_01_hx1 : SourcePowerBound
    (powerBoxCross 18 29 2 half_30_01_φ1) (81569858397/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 29) (u := 27) (t := 30)
    (D := 2) (ψ := (10019191/200000000 : ℝ)) half_30_01_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_30_01_bounds1 l).1) (fun l => (half_30_01_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_30_01_total1, half_30_01_total2, half_30_01_total3, half_30_01_total4, half_30_01_total5, half_30_01_total6, half_30_01_total7, half_30_01_total8, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_28_01) (chord_58)
    (by simpa only [half_30_01_φ2, show (2:ℝ)*2=4 by norm_num] using half_30_01_hx2)
  exact h.weaken (by norm_num [half_30_01_total1, half_30_01_total2, half_30_01_total3, half_30_01_total4, half_30_01_total5, half_30_01_total6, half_30_01_total7, half_30_01_total8, parameterExponent, curveLoss, dyadicExponent])

theorem half_30_01 : AdmissibleExponent 18 60 (21975797931/500000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 28) (ψ := (111111111/2000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_29_01)
    (by simpa only [half_30_01_φ1] using half_30_01_hx1)
  exact admissibleExponent_mono h (by norm_num [half_30_01_total1, half_30_01_total2, half_30_01_total3, half_30_01_total4, half_30_01_total5, half_30_01_total6, half_30_01_total7, half_30_01_total8, parameterExponent, curveLoss, dyadicExponent])

private def half_31_01_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (111111111/2000000000 : ℝ)

private theorem half_31_01_total1 : total half_31_01_φ1=(111111111/2000000000 : ℝ) := by
  norm_num [half_31_01_φ1,total,emptyPhi,Fin.snoc]

private theorem half_31_01_bounds1 : ∀ l,0≤half_31_01_φ1 l ∧ half_31_01_φ1 l≤1 ∧
    0≤shiftExponents 18 half_31_01_φ1 l :=
  alternate_bounds_snoc emptyPhi (111111111/2000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_31_01_φ2 : Fin 2 → ℝ := Fin.snoc half_31_01_φ1 (127498297/2500000000 : ℝ)

private theorem half_31_01_total2 : total half_31_01_φ2=(1065548743/10000000000 : ℝ) := by
  change total (Fin.snoc half_31_01_φ1 (127498297/2500000000 : ℝ))=(1065548743/10000000000 : ℝ)
  rw [alternate_total_snoc,half_31_01_total1]
  norm_num

private theorem half_31_01_bounds2 : ∀ l,0≤half_31_01_φ2 l ∧ half_31_01_φ2 l≤1 ∧
    0≤shiftExponents 18 half_31_01_φ2 l :=
  alternate_bounds_snoc half_31_01_φ1 (127498297/2500000000 : ℝ) half_31_01_bounds1 (by norm_num)

private def half_31_01_φ3 : Fin 3 → ℝ := Fin.snoc half_31_01_φ2 (62894277/1250000000 : ℝ)

private theorem half_31_01_total3 : total half_31_01_φ3=(1568702959/10000000000 : ℝ) := by
  change total (Fin.snoc half_31_01_φ2 (62894277/1250000000 : ℝ))=(1568702959/10000000000 : ℝ)
  rw [alternate_total_snoc,half_31_01_total2]
  norm_num

private theorem half_31_01_bounds3 : ∀ l,0≤half_31_01_φ3 l ∧ half_31_01_φ3 l≤1 ∧
    0≤shiftExponents 18 half_31_01_φ3 l :=
  alternate_bounds_snoc half_31_01_φ2 (62894277/1250000000 : ℝ) half_31_01_bounds2 (by norm_num)

private def half_31_01_φ4 : Fin 4 → ℝ := Fin.snoc half_31_01_φ3 (495958649/10000000000 : ℝ)

private theorem half_31_01_total4 : total half_31_01_φ4=(258082701/1250000000 : ℝ) := by
  change total (Fin.snoc half_31_01_φ3 (495958649/10000000000 : ℝ))=(258082701/1250000000 : ℝ)
  rw [alternate_total_snoc,half_31_01_total3]
  norm_num

private theorem half_31_01_bounds4 : ∀ l,0≤half_31_01_φ4 l ∧ half_31_01_φ4 l≤1 ∧
    0≤shiftExponents 18 half_31_01_φ4 l :=
  alternate_bounds_snoc half_31_01_φ3 (495958649/10000000000 : ℝ) half_31_01_bounds3 (by norm_num)

private def half_31_01_φ5 : Fin 5 → ℝ := Fin.snoc half_31_01_φ4 (466784611/10000000000 : ℝ)

private theorem half_31_01_total5 : total half_31_01_φ5=(2531446219/10000000000 : ℝ) := by
  change total (Fin.snoc half_31_01_φ4 (466784611/10000000000 : ℝ))=(2531446219/10000000000 : ℝ)
  rw [alternate_total_snoc,half_31_01_total4]
  norm_num

private theorem half_31_01_bounds5 : ∀ l,0≤half_31_01_φ5 l ∧ half_31_01_φ5 l≤1 ∧
    0≤shiftExponents 18 half_31_01_φ5 l :=
  alternate_bounds_snoc half_31_01_φ4 (466784611/10000000000 : ℝ) half_31_01_bounds4 (by norm_num)

private def half_31_01_φ6 : Fin 6 → ℝ := Fin.snoc half_31_01_φ5 (109831673/2500000000 : ℝ)

private theorem half_31_01_total6 : total half_31_01_φ6=(2970772911/10000000000 : ℝ) := by
  change total (Fin.snoc half_31_01_φ5 (109831673/2500000000 : ℝ))=(2970772911/10000000000 : ℝ)
  rw [alternate_total_snoc,half_31_01_total5]
  norm_num

private theorem half_31_01_bounds6 : ∀ l,0≤half_31_01_φ6 l ∧ half_31_01_φ6 l≤1 ∧
    0≤shiftExponents 18 half_31_01_φ6 l :=
  alternate_bounds_snoc half_31_01_φ5 (109831673/2500000000 : ℝ) half_31_01_bounds5 (by norm_num)

private def half_31_01_φ7 : Fin 7 → ℝ := Fin.snoc half_31_01_φ6 (206741973/5000000000 : ℝ)

private theorem half_31_01_total7 : total half_31_01_φ7=(3384256857/10000000000 : ℝ) := by
  change total (Fin.snoc half_31_01_φ6 (206741973/5000000000 : ℝ))=(3384256857/10000000000 : ℝ)
  rw [alternate_total_snoc,half_31_01_total6]
  norm_num

private theorem half_31_01_bounds7 : ∀ l,0≤half_31_01_φ7 l ∧ half_31_01_φ7 l≤1 ∧
    0≤shiftExponents 18 half_31_01_φ7 l :=
  alternate_bounds_snoc half_31_01_φ6 (206741973/5000000000 : ℝ) half_31_01_bounds6 (by norm_num)

private def half_31_01_φ8 : Fin 8 → ℝ := Fin.snoc half_31_01_φ7 (389161361/10000000000 : ℝ)

private theorem half_31_01_total8 : total half_31_01_φ8=(1886709109/5000000000 : ℝ) := by
  change total (Fin.snoc half_31_01_φ7 (389161361/10000000000 : ℝ))=(1886709109/5000000000 : ℝ)
  rw [alternate_total_snoc,half_31_01_total7]
  norm_num

private theorem half_31_01_bounds8 : ∀ l,0≤half_31_01_φ8 l ∧ half_31_01_φ8 l≤1 ∧
    0≤shiftExponents 18 half_31_01_φ8 l :=
  alternate_bounds_snoc half_31_01_φ7 (389161361/10000000000 : ℝ) half_31_01_bounds7 (by norm_num)

private theorem half_31_01_prefix : PrefixCondition 18 half_31_01_φ8 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_31_01_φ1, half_31_01_φ2, half_31_01_φ3, half_31_01_φ4, half_31_01_φ5, half_31_01_φ6, half_31_01_φ7, half_31_01_φ8, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_31_01_hF16 : SourcePowerBound
    (paddedMoment 18 0 16 256 half_31_01_φ8) (571386512999/7500000000 : ℝ) := by
  have h := padded_dyadic_divisor_power (k := 18) (j := 8) (r := 0) (n := 4) (D := 256)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_31_01_φ8
    (fun i => (half_31_01_bounds8 i).1) (fun i => (half_31_01_bounds8 i).2.1)
    (fun i => (half_31_01_bounds8 i).2.2) half_31_01_prefix
  convert h using 1 <;> norm_num [half_31_01_total1, half_31_01_total2, half_31_01_total3, half_31_01_total4, half_31_01_total5, half_31_01_total6, half_31_01_total7, half_31_01_total8, parameterExponent, curveLoss, dyadicExponent]

private theorem half_31_01_hx8 : SourcePowerBound
    (powerBoxCross 18 23 256 half_31_01_φ8) (219832525153/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 23) (r := 16) (v := 23) (w := 24) (D := 256)
    (a := (1/32 : ℝ)) (b := (1/4 : ℝ)) (c := (23/32 : ℝ))
    (by norm_num) half_31_01_φ8 (by norm_num [half_31_01_total1, half_31_01_total2, half_31_01_total3, half_31_01_total4, half_31_01_total5, half_31_01_total6, half_31_01_total7, half_31_01_total8, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_31_01_total1, half_31_01_total2, half_31_01_total3, half_31_01_total4, half_31_01_total5, half_31_01_total6, half_31_01_total7, half_31_01_total8, parameterExponent, curveLoss, dyadicExponent]) half_31_01_hF16
    (half_23_01) (half_24_01)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_31_01_total1, half_31_01_total2, half_31_01_total3, half_31_01_total4, half_31_01_total5, half_31_01_total6, half_31_01_total7, half_31_01_total8, parameterExponent, curveLoss, dyadicExponent])

private theorem half_31_01_hx7 : SourcePowerBound
    (powerBoxCross 18 24 128 half_31_01_φ7) (239761212063/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 7) (s := 24) (u := 22) (t := 25)
    (D := 128) (ψ := (389161361/10000000000 : ℝ)) half_31_01_φ7
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_31_01_bounds7 l).1) (fun l => (half_31_01_bounds7 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_31_01_total1, half_31_01_total2, half_31_01_total3, half_31_01_total4, half_31_01_total5, half_31_01_total6, half_31_01_total7, half_31_01_total8, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_23_01) (half_25_01)
    (by simpa only [half_31_01_φ8, show (2:ℝ)*128=256 by norm_num] using half_31_01_hx8)
  exact h.weaken (by norm_num [half_31_01_total1, half_31_01_total2, half_31_01_total3, half_31_01_total4, half_31_01_total5, half_31_01_total6, half_31_01_total7, half_31_01_total8, parameterExponent, curveLoss, dyadicExponent])

private theorem half_31_01_hx6 : SourcePowerBound
    (powerBoxCross 18 25 64 half_31_01_φ6) (26268309083/1000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 6) (s := 25) (u := 23) (t := 26)
    (D := 64) (ψ := (206741973/5000000000 : ℝ)) half_31_01_φ6
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_31_01_bounds6 l).1) (fun l => (half_31_01_bounds6 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_31_01_total1, half_31_01_total2, half_31_01_total3, half_31_01_total4, half_31_01_total5, half_31_01_total6, half_31_01_total7, half_31_01_total8, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_24_01) (half_26_01)
    (by simpa only [half_31_01_φ7, show (2:ℝ)*64=128 by norm_num] using half_31_01_hx7)
  exact h.weaken (by norm_num [half_31_01_total1, half_31_01_total2, half_31_01_total3, half_31_01_total4, half_31_01_total5, half_31_01_total6, half_31_01_total7, half_31_01_total8, parameterExponent, curveLoss, dyadicExponent])

private theorem half_31_01_hx5 : SourcePowerBound
    (powerBoxCross 18 26 32 half_31_01_φ5) (72181820867/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 5) (s := 26) (u := 24) (t := 27)
    (D := 32) (ψ := (109831673/2500000000 : ℝ)) half_31_01_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_31_01_bounds5 l).1) (fun l => (half_31_01_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_31_01_total1, half_31_01_total2, half_31_01_total3, half_31_01_total4, half_31_01_total5, half_31_01_total6, half_31_01_total7, half_31_01_total8, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_25_01) (half_27_01)
    (by simpa only [half_31_01_φ6, show (2:ℝ)*32=64 by norm_num] using half_31_01_hx6)
  exact h.weaken (by norm_num [half_31_01_total1, half_31_01_total2, half_31_01_total3, half_31_01_total4, half_31_01_total5, half_31_01_total6, half_31_01_total7, half_31_01_total8, parameterExponent, curveLoss, dyadicExponent])

private theorem half_31_01_hx4 : SourcePowerBound
    (powerBoxCross 18 27 16 half_31_01_φ4) (318102251583/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 27) (u := 25) (t := 28)
    (D := 16) (ψ := (466784611/10000000000 : ℝ)) half_31_01_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_31_01_bounds4 l).1) (fun l => (half_31_01_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_31_01_total1, half_31_01_total2, half_31_01_total3, half_31_01_total4, half_31_01_total5, half_31_01_total6, half_31_01_total7, half_31_01_total8, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_26_01) (half_28_01)
    (by simpa only [half_31_01_φ5, show (2:ℝ)*16=32 by norm_num] using half_31_01_hx5)
  exact h.weaken (by norm_num [half_31_01_total1, half_31_01_total2, half_31_01_total3, half_31_01_total4, half_31_01_total5, half_31_01_total6, half_31_01_total7, half_31_01_total8, parameterExponent, curveLoss, dyadicExponent])

private theorem half_31_01_hx3 : SourcePowerBound
    (powerBoxCross 18 28 8 half_31_01_φ3) (175541215349/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 28) (u := 26) (t := 29)
    (D := 8) (ψ := (495958649/10000000000 : ℝ)) half_31_01_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_31_01_bounds3 l).1) (fun l => (half_31_01_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_31_01_total1, half_31_01_total2, half_31_01_total3, half_31_01_total4, half_31_01_total5, half_31_01_total6, half_31_01_total7, half_31_01_total8, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_27_01) (half_29_01)
    (by simpa only [half_31_01_φ4, show (2:ℝ)*8=16 by norm_num] using half_31_01_hx4)
  exact h.weaken (by norm_num [half_31_01_total1, half_31_01_total2, half_31_01_total3, half_31_01_total4, half_31_01_total5, half_31_01_total6, half_31_01_total7, half_31_01_total8, parameterExponent, curveLoss, dyadicExponent])

private theorem half_31_01_hx2 : SourcePowerBound
    (powerBoxCross 18 29 4 half_31_01_φ2) (193331243711/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 29) (u := 27) (t := 30)
    (D := 4) (ψ := (62894277/1250000000 : ℝ)) half_31_01_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_31_01_bounds2 l).1) (fun l => (half_31_01_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_31_01_total1, half_31_01_total2, half_31_01_total3, half_31_01_total4, half_31_01_total5, half_31_01_total6, half_31_01_total7, half_31_01_total8, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_28_01) (half_30_01)
    (by simpa only [half_31_01_φ3, show (2:ℝ)*4=8 by norm_num] using half_31_01_hx3)
  exact h.weaken (by norm_num [half_31_01_total1, half_31_01_total2, half_31_01_total3, half_31_01_total4, half_31_01_total5, half_31_01_total6, half_31_01_total7, half_31_01_total8, parameterExponent, curveLoss, dyadicExponent])

private theorem half_31_01_hx1 : SourcePowerBound
    (powerBoxCross 18 30 2 half_31_01_φ1) (106722637139/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 30) (u := 28) (t := 31)
    (D := 2) (ψ := (127498297/2500000000 : ℝ)) half_31_01_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_31_01_bounds1 l).1) (fun l => (half_31_01_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_31_01_total1, half_31_01_total2, half_31_01_total3, half_31_01_total4, half_31_01_total5, half_31_01_total6, half_31_01_total7, half_31_01_total8, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_29_01) (half_31_00)
    (by simpa only [half_31_01_φ2, show (2:ℝ)*2=4 by norm_num] using half_31_01_hx2)
  exact h.weaken (by norm_num [half_31_01_total1, half_31_01_total2, half_31_01_total3, half_31_01_total4, half_31_01_total5, half_31_01_total6, half_31_01_total7, half_31_01_total8, parameterExponent, curveLoss, dyadicExponent])

theorem half_31_01 : AdmissibleExponent 18 62 (459668326301/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 29) (ψ := (111111111/2000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_30_01)
    (by simpa only [half_31_01_φ1] using half_31_01_hx1)
  exact admissibleExponent_mono h (by norm_num [half_31_01_total1, half_31_01_total2, half_31_01_total3, half_31_01_total4, half_31_01_total5, half_31_01_total6, half_31_01_total7, half_31_01_total8, parameterExponent, curveLoss, dyadicExponent])

private def half_18_02_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (11125363/250000000 : ℝ)

private theorem half_18_02_total1 : total half_18_02_φ1=(11125363/250000000 : ℝ) := by
  norm_num [half_18_02_φ1,total,emptyPhi,Fin.snoc]

private theorem half_18_02_bounds1 : ∀ l,0≤half_18_02_φ1 l ∧ half_18_02_φ1 l≤1 ∧
    0≤shiftExponents 18 half_18_02_φ1 l :=
  alternate_bounds_snoc emptyPhi (11125363/250000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_18_02_φ2 : Fin 2 → ℝ := Fin.snoc half_18_02_φ1 (421075943/10000000000 : ℝ)

private theorem half_18_02_total2 : total half_18_02_φ2=(866090463/10000000000 : ℝ) := by
  change total (Fin.snoc half_18_02_φ1 (421075943/10000000000 : ℝ))=(866090463/10000000000 : ℝ)
  rw [alternate_total_snoc,half_18_02_total1]
  norm_num

private theorem half_18_02_bounds2 : ∀ l,0≤half_18_02_φ2 l ∧ half_18_02_φ2 l≤1 ∧
    0≤shiftExponents 18 half_18_02_φ2 l :=
  alternate_bounds_snoc half_18_02_φ1 (421075943/10000000000 : ℝ) half_18_02_bounds1 (by norm_num)

private def half_18_02_φ3 : Fin 3 → ℝ := Fin.snoc half_18_02_φ2 (410938533/10000000000 : ℝ)

private theorem half_18_02_total3 : total half_18_02_φ3=(319257249/2500000000 : ℝ) := by
  change total (Fin.snoc half_18_02_φ2 (410938533/10000000000 : ℝ))=(319257249/2500000000 : ℝ)
  rw [alternate_total_snoc,half_18_02_total2]
  norm_num

private theorem half_18_02_bounds3 : ∀ l,0≤half_18_02_φ3 l ∧ half_18_02_φ3 l≤1 ∧
    0≤shiftExponents 18 half_18_02_φ3 l :=
  alternate_bounds_snoc half_18_02_φ2 (410938533/10000000000 : ℝ) half_18_02_bounds2 (by norm_num)

private def half_18_02_φ4 : Fin 4 → ℝ := Fin.snoc half_18_02_φ3 (398997693/10000000000 : ℝ)

private theorem half_18_02_total4 : total half_18_02_φ4=(1676026689/10000000000 : ℝ) := by
  change total (Fin.snoc half_18_02_φ3 (398997693/10000000000 : ℝ))=(1676026689/10000000000 : ℝ)
  rw [alternate_total_snoc,half_18_02_total3]
  norm_num

private theorem half_18_02_bounds4 : ∀ l,0≤half_18_02_φ4 l ∧ half_18_02_φ4 l≤1 ∧
    0≤shiftExponents 18 half_18_02_φ4 l :=
  alternate_bounds_snoc half_18_02_φ3 (398997693/10000000000 : ℝ) half_18_02_bounds3 (by norm_num)

private def half_18_02_φ5 : Fin 5 → ℝ := Fin.snoc half_18_02_φ4 (76269873/2000000000 : ℝ)

private theorem half_18_02_total5 : total half_18_02_φ5=(1028688027/5000000000 : ℝ) := by
  change total (Fin.snoc half_18_02_φ4 (76269873/2000000000 : ℝ))=(1028688027/5000000000 : ℝ)
  rw [alternate_total_snoc,half_18_02_total4]
  norm_num

private theorem half_18_02_bounds5 : ∀ l,0≤half_18_02_φ5 l ∧ half_18_02_φ5 l≤1 ∧
    0≤shiftExponents 18 half_18_02_φ5 l :=
  alternate_bounds_snoc half_18_02_φ4 (76269873/2000000000 : ℝ) half_18_02_bounds4 (by norm_num)

private def half_18_02_φ6 : Fin 6 → ℝ := Fin.snoc half_18_02_φ5 (171119201/5000000000 : ℝ)

private theorem half_18_02_total6 : total half_18_02_φ6=(299951807/1250000000 : ℝ) := by
  change total (Fin.snoc half_18_02_φ5 (171119201/5000000000 : ℝ))=(299951807/1250000000 : ℝ)
  rw [alternate_total_snoc,half_18_02_total5]
  norm_num

private theorem half_18_02_bounds6 : ∀ l,0≤half_18_02_φ6 l ∧ half_18_02_φ6 l≤1 ∧
    0≤shiftExponents 18 half_18_02_φ6 l :=
  alternate_bounds_snoc half_18_02_φ5 (171119201/5000000000 : ℝ) half_18_02_bounds5 (by norm_num)

private def half_18_02_φ7 : Fin 7 → ℝ := Fin.snoc half_18_02_φ6 (8719839/400000000 : ℝ)

private theorem half_18_02_total7 : total half_18_02_φ7=(2617610431/10000000000 : ℝ) := by
  change total (Fin.snoc half_18_02_φ6 (8719839/400000000 : ℝ))=(2617610431/10000000000 : ℝ)
  rw [alternate_total_snoc,half_18_02_total6]
  norm_num

private theorem half_18_02_bounds7 : ∀ l,0≤half_18_02_φ7 l ∧ half_18_02_φ7 l≤1 ∧
    0≤shiftExponents 18 half_18_02_φ7 l :=
  alternate_bounds_snoc half_18_02_φ6 (8719839/400000000 : ℝ) half_18_02_bounds6 (by norm_num)

private theorem half_18_02_prefix : PrefixCondition 18 half_18_02_φ7 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_18_02_φ1, half_18_02_φ2, half_18_02_φ3, half_18_02_φ4, half_18_02_φ5, half_18_02_φ6, half_18_02_φ7, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_18_02_hF2 : SourcePowerBound
    (paddedMoment 18 0 2 128 half_18_02_φ7) (96501868019/10000000000 : ℝ) := by
  have h := padded_dyadic_divisor_power (k := 18) (j := 7) (r := 0) (n := 1) (D := 128)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_18_02_φ7
    (fun i => (half_18_02_bounds7 i).1) (fun i => (half_18_02_bounds7 i).2.1)
    (fun i => (half_18_02_bounds7 i).2.2) half_18_02_prefix
  convert h using 1 <;> norm_num [half_18_02_total1, half_18_02_total2, half_18_02_total3, half_18_02_total4, half_18_02_total5, half_18_02_total6, half_18_02_total7, parameterExponent, curveLoss, dyadicExponent]

private theorem half_18_02_hx7 : SourcePowerBound
    (powerBoxCross 18 11 128 half_18_02_φ7) (12199158587/1000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 11) (r := 2) (v := 14) (w := 15) (D := 128)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_18_02_φ7 (by norm_num [half_18_02_total1, half_18_02_total2, half_18_02_total3, half_18_02_total4, half_18_02_total5, half_18_02_total6, half_18_02_total7, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_18_02_total1, half_18_02_total2, half_18_02_total3, half_18_02_total4, half_18_02_total5, half_18_02_total6, half_18_02_total7, parameterExponent, curveLoss, dyadicExponent]) half_18_02_hF2
    (SeedCompletionHigher18SimpleSeeds.degree18_half_14) (SeedCompletionHigher18SimpleSeeds.degree18_half_15)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_18_02_total1, half_18_02_total2, half_18_02_total3, half_18_02_total4, half_18_02_total5, half_18_02_total6, half_18_02_total7, parameterExponent, curveLoss, dyadicExponent])

private theorem half_18_02_hx6 : SourcePowerBound
    (powerBoxCross 18 12 64 half_18_02_φ6) (130963829383/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 6) (s := 12) (u := 10) (t := 13)
    (D := 64) (ψ := (8719839/400000000 : ℝ)) half_18_02_φ6
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_18_02_bounds6 l).1) (fun l => (half_18_02_bounds6 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_18_02_total1, half_18_02_total2, half_18_02_total3, half_18_02_total4, half_18_02_total5, half_18_02_total6, half_18_02_total7, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher18SimpleSeeds.degree18_half_11) (SeedCompletionHigher18SimpleSeeds.degree18_half_13)
    (by simpa only [half_18_02_φ7, show (2:ℝ)*64=128 by norm_num] using half_18_02_hx7)
  exact h.weaken (by norm_num [half_18_02_total1, half_18_02_total2, half_18_02_total3, half_18_02_total4, half_18_02_total5, half_18_02_total6, half_18_02_total7, parameterExponent, curveLoss, dyadicExponent])

private theorem half_18_02_hx5 : SourcePowerBound
    (powerBoxCross 18 13 32 half_18_02_φ5) (4477209349/312500000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 5) (s := 13) (u := 11) (t := 14)
    (D := 32) (ψ := (171119201/5000000000 : ℝ)) half_18_02_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_18_02_bounds5 l).1) (fun l => (half_18_02_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_18_02_total1, half_18_02_total2, half_18_02_total3, half_18_02_total4, half_18_02_total5, half_18_02_total6, half_18_02_total7, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher18SimpleSeeds.degree18_half_12) (SeedCompletionHigher18SimpleSeeds.degree18_half_14)
    (by simpa only [half_18_02_φ6, show (2:ℝ)*32=64 by norm_num] using half_18_02_hx6)
  exact h.weaken (by norm_num [half_18_02_total1, half_18_02_total2, half_18_02_total3, half_18_02_total4, half_18_02_total5, half_18_02_total6, half_18_02_total7, parameterExponent, curveLoss, dyadicExponent])

private theorem half_18_02_hx4 : SourcePowerBound
    (powerBoxCross 18 14 16 half_18_02_φ4) (15774142193/1000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 14) (u := 12) (t := 15)
    (D := 16) (ψ := (76269873/2000000000 : ℝ)) half_18_02_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_18_02_bounds4 l).1) (fun l => (half_18_02_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_18_02_total1, half_18_02_total2, half_18_02_total3, half_18_02_total4, half_18_02_total5, half_18_02_total6, half_18_02_total7, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher18SimpleSeeds.degree18_half_13) (SeedCompletionHigher18SimpleSeeds.degree18_half_15)
    (by simpa only [half_18_02_φ5, show (2:ℝ)*16=32 by norm_num] using half_18_02_hx5)
  exact h.weaken (by norm_num [half_18_02_total1, half_18_02_total2, half_18_02_total3, half_18_02_total4, half_18_02_total5, half_18_02_total6, half_18_02_total7, parameterExponent, curveLoss, dyadicExponent])

private theorem half_18_02_hx3 : SourcePowerBound
    (powerBoxCross 18 15 8 half_18_02_φ3) (34820884599/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 15) (u := 13) (t := 16)
    (D := 8) (ψ := (398997693/10000000000 : ℝ)) half_18_02_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_18_02_bounds3 l).1) (fun l => (half_18_02_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_18_02_total1, half_18_02_total2, half_18_02_total3, half_18_02_total4, half_18_02_total5, half_18_02_total6, half_18_02_total7, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher18SimpleSeeds.degree18_half_14) (SeedCompletionHigher18SimpleSeeds.degree18_half_16)
    (by simpa only [half_18_02_φ4, show (2:ℝ)*8=16 by norm_num] using half_18_02_hx4)
  exact h.weaken (by norm_num [half_18_02_total1, half_18_02_total2, half_18_02_total3, half_18_02_total4, half_18_02_total5, half_18_02_total6, half_18_02_total7, parameterExponent, curveLoss, dyadicExponent])

private theorem half_18_02_hx2 : SourcePowerBound
    (powerBoxCross 18 16 4 half_18_02_φ2) (9616731873/500000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 16) (u := 14) (t := 17)
    (D := 4) (ψ := (410938533/10000000000 : ℝ)) half_18_02_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_18_02_bounds2 l).1) (fun l => (half_18_02_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_18_02_total1, half_18_02_total2, half_18_02_total3, half_18_02_total4, half_18_02_total5, half_18_02_total6, half_18_02_total7, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher18SimpleSeeds.degree18_half_15) (SeedCompletionHigher18SimpleSeeds.degree18_half_17)
    (by simpa only [half_18_02_φ3, show (2:ℝ)*4=8 by norm_num] using half_18_02_hx3)
  exact h.weaken (by norm_num [half_18_02_total1, half_18_02_total2, half_18_02_total3, half_18_02_total4, half_18_02_total5, half_18_02_total6, half_18_02_total7, parameterExponent, curveLoss, dyadicExponent])

private theorem half_18_02_hx1 : SourcePowerBound
    (powerBoxCross 18 17 2 half_18_02_φ1) (42546131073/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 17) (u := 15) (t := 18)
    (D := 2) (ψ := (421075943/10000000000 : ℝ)) half_18_02_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_18_02_bounds1 l).1) (fun l => (half_18_02_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_18_02_total1, half_18_02_total2, half_18_02_total3, half_18_02_total4, half_18_02_total5, half_18_02_total6, half_18_02_total7, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher18SimpleSeeds.degree18_half_16) (half_18_01)
    (by simpa only [half_18_02_φ2, show (2:ℝ)*2=4 by norm_num] using half_18_02_hx2)
  exact h.weaken (by norm_num [half_18_02_total1, half_18_02_total2, half_18_02_total3, half_18_02_total4, half_18_02_total5, half_18_02_total6, half_18_02_total7, parameterExponent, curveLoss, dyadicExponent])

theorem half_18_02 : AdmissibleExponent 18 36 (9096645381/400000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 16) (ψ := (11125363/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (SeedCompletionHigher18SimpleSeeds.degree18_half_17)
    (by simpa only [half_18_02_φ1] using half_18_02_hx1)
  exact admissibleExponent_mono h (by norm_num [half_18_02_total1, half_18_02_total2, half_18_02_total3, half_18_02_total4, half_18_02_total5, half_18_02_total6, half_18_02_total7, parameterExponent, curveLoss, dyadicExponent])

theorem chord_59 : AdmissibleExponent 18 38 (488157293067/20000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 38) (t := (1/2 : ℝ))
    (half_18_02) (half_20_01)
    (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private def half_19_02_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (457906313/10000000000 : ℝ)

private theorem half_19_02_total1 : total half_19_02_φ1=(457906313/10000000000 : ℝ) := by
  norm_num [half_19_02_φ1,total,emptyPhi,Fin.snoc]

private theorem half_19_02_bounds1 : ∀ l,0≤half_19_02_φ1 l ∧ half_19_02_φ1 l≤1 ∧
    0≤shiftExponents 18 half_19_02_φ1 l :=
  alternate_bounds_snoc emptyPhi (457906313/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_19_02_φ2 : Fin 2 → ℝ := Fin.snoc half_19_02_φ1 (27159469/625000000 : ℝ)

private theorem half_19_02_total2 : total half_19_02_φ2=(892457817/10000000000 : ℝ) := by
  change total (Fin.snoc half_19_02_φ1 (27159469/625000000 : ℝ))=(892457817/10000000000 : ℝ)
  rw [alternate_total_snoc,half_19_02_total1]
  norm_num

private theorem half_19_02_bounds2 : ∀ l,0≤half_19_02_φ2 l ∧ half_19_02_φ2 l≤1 ∧
    0≤shiftExponents 18 half_19_02_φ2 l :=
  alternate_bounds_snoc half_19_02_φ1 (27159469/625000000 : ℝ) half_19_02_bounds1 (by norm_num)

private def half_19_02_φ3 : Fin 3 → ℝ := Fin.snoc half_19_02_φ2 (420141869/10000000000 : ℝ)

private theorem half_19_02_total3 : total half_19_02_φ3=(656299843/5000000000 : ℝ) := by
  change total (Fin.snoc half_19_02_φ2 (420141869/10000000000 : ℝ))=(656299843/5000000000 : ℝ)
  rw [alternate_total_snoc,half_19_02_total2]
  norm_num

private theorem half_19_02_bounds3 : ∀ l,0≤half_19_02_φ3 l ∧ half_19_02_φ3 l≤1 ∧
    0≤shiftExponents 18 half_19_02_φ3 l :=
  alternate_bounds_snoc half_19_02_φ2 (420141869/10000000000 : ℝ) half_19_02_bounds2 (by norm_num)

private def half_19_02_φ4 : Fin 4 → ℝ := Fin.snoc half_19_02_φ3 (204655249/5000000000 : ℝ)

private theorem half_19_02_total4 : total half_19_02_φ4=(215238773/1250000000 : ℝ) := by
  change total (Fin.snoc half_19_02_φ3 (204655249/5000000000 : ℝ))=(215238773/1250000000 : ℝ)
  rw [alternate_total_snoc,half_19_02_total3]
  norm_num

private theorem half_19_02_bounds4 : ∀ l,0≤half_19_02_φ4 l ∧ half_19_02_φ4 l≤1 ∧
    0≤shiftExponents 18 half_19_02_φ4 l :=
  alternate_bounds_snoc half_19_02_φ3 (204655249/5000000000 : ℝ) half_19_02_bounds3 (by norm_num)

private def half_19_02_φ5 : Fin 5 → ℝ := Fin.snoc half_19_02_φ4 (49388141/1250000000 : ℝ)

private theorem half_19_02_total5 : total half_19_02_φ5=(132313457/625000000 : ℝ) := by
  change total (Fin.snoc half_19_02_φ4 (49388141/1250000000 : ℝ))=(132313457/625000000 : ℝ)
  rw [alternate_total_snoc,half_19_02_total4]
  norm_num

private theorem half_19_02_bounds5 : ∀ l,0≤half_19_02_φ5 l ∧ half_19_02_φ5 l≤1 ∧
    0≤shiftExponents 18 half_19_02_φ5 l :=
  alternate_bounds_snoc half_19_02_φ4 (49388141/1250000000 : ℝ) half_19_02_bounds4 (by norm_num)

private def half_19_02_φ6 : Fin 6 → ℝ := Fin.snoc half_19_02_φ5 (18482121/500000000 : ℝ)

private theorem half_19_02_total6 : total half_19_02_φ6=(621664433/2500000000 : ℝ) := by
  change total (Fin.snoc half_19_02_φ5 (18482121/500000000 : ℝ))=(621664433/2500000000 : ℝ)
  rw [alternate_total_snoc,half_19_02_total5]
  norm_num

private theorem half_19_02_bounds6 : ∀ l,0≤half_19_02_φ6 l ∧ half_19_02_φ6 l≤1 ∧
    0≤shiftExponents 18 half_19_02_φ6 l :=
  alternate_bounds_snoc half_19_02_φ5 (18482121/500000000 : ℝ) half_19_02_bounds5 (by norm_num)

private def half_19_02_φ7 : Fin 7 → ℝ := Fin.snoc half_19_02_φ6 (150989887/5000000000 : ℝ)

private theorem half_19_02_total7 : total half_19_02_φ7=(1394318753/5000000000 : ℝ) := by
  change total (Fin.snoc half_19_02_φ6 (150989887/5000000000 : ℝ))=(1394318753/5000000000 : ℝ)
  rw [alternate_total_snoc,half_19_02_total6]
  norm_num

private theorem half_19_02_bounds7 : ∀ l,0≤half_19_02_φ7 l ∧ half_19_02_φ7 l≤1 ∧
    0≤shiftExponents 18 half_19_02_φ7 l :=
  alternate_bounds_snoc half_19_02_φ6 (150989887/5000000000 : ℝ) half_19_02_bounds6 (by norm_num)

private theorem half_19_02_prefix : PrefixCondition 18 half_19_02_φ7 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_19_02_φ1, half_19_02_φ2, half_19_02_φ3, half_19_02_φ4, half_19_02_φ5, half_19_02_φ6, half_19_02_φ7, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_19_02_hF2 : SourcePowerBound
    (paddedMoment 18 0 2 128 half_19_02_φ7) (43889743597/5000000000 : ℝ) := by
  have h := padded_dyadic_divisor_power (k := 18) (j := 7) (r := 0) (n := 1) (D := 128)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_19_02_φ7
    (fun i => (half_19_02_bounds7 i).1) (fun i => (half_19_02_bounds7 i).2.1)
    (fun i => (half_19_02_bounds7 i).2.2) half_19_02_prefix
  convert h using 1 <;> norm_num [half_19_02_total1, half_19_02_total2, half_19_02_total3, half_19_02_total4, half_19_02_total5, half_19_02_total6, half_19_02_total7, parameterExponent, curveLoss, dyadicExponent]

private theorem half_19_02_hx7 : SourcePowerBound
    (powerBoxCross 18 12 128 half_19_02_φ7) (12822083789/1000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 12) (r := 2) (v := 0) (w := 16) (D := 128)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_19_02_φ7 (by norm_num [half_19_02_total1, half_19_02_total2, half_19_02_total3, half_19_02_total4, half_19_02_total5, half_19_02_total6, half_19_02_total7, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_19_02_total1, half_19_02_total2, half_19_02_total3, half_19_02_total4, half_19_02_total5, half_19_02_total6, half_19_02_total7, parameterExponent, curveLoss, dyadicExponent]) half_19_02_hF2
    (admissibleExponent_zero 18) (SeedCompletionHigher18SimpleSeeds.degree18_half_16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_19_02_total1, half_19_02_total2, half_19_02_total3, half_19_02_total4, half_19_02_total5, half_19_02_total6, half_19_02_total7, parameterExponent, curveLoss, dyadicExponent])

private theorem half_19_02_hx6 : SourcePowerBound
    (powerBoxCross 18 13 64 half_19_02_φ6) (69600880597/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 6) (s := 13) (u := 11) (t := 14)
    (D := 64) (ψ := (150989887/5000000000 : ℝ)) half_19_02_φ6
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_19_02_bounds6 l).1) (fun l => (half_19_02_bounds6 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_19_02_total1, half_19_02_total2, half_19_02_total3, half_19_02_total4, half_19_02_total5, half_19_02_total6, half_19_02_total7, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher18SimpleSeeds.degree18_half_12) (SeedCompletionHigher18SimpleSeeds.degree18_half_14)
    (by simpa only [half_19_02_φ7, show (2:ℝ)*64=128 by norm_num] using half_19_02_hx7)
  exact h.weaken (by norm_num [half_19_02_total1, half_19_02_total2, half_19_02_total3, half_19_02_total4, half_19_02_total5, half_19_02_total6, half_19_02_total7, parameterExponent, curveLoss, dyadicExponent])

private theorem half_19_02_hx5 : SourcePowerBound
    (powerBoxCross 18 14 32 half_19_02_φ5) (152807837233/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 5) (s := 14) (u := 12) (t := 15)
    (D := 32) (ψ := (18482121/500000000 : ℝ)) half_19_02_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_19_02_bounds5 l).1) (fun l => (half_19_02_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_19_02_total1, half_19_02_total2, half_19_02_total3, half_19_02_total4, half_19_02_total5, half_19_02_total6, half_19_02_total7, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher18SimpleSeeds.degree18_half_13) (SeedCompletionHigher18SimpleSeeds.degree18_half_15)
    (by simpa only [half_19_02_φ6, show (2:ℝ)*32=64 by norm_num] using half_19_02_hx6)
  exact h.weaken (by norm_num [half_19_02_total1, half_19_02_total2, half_19_02_total3, half_19_02_total4, half_19_02_total5, half_19_02_total6, half_19_02_total7, parameterExponent, curveLoss, dyadicExponent])

private theorem half_19_02_hx4 : SourcePowerBound
    (powerBoxCross 18 15 16 half_19_02_φ4) (6737307779/400000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 15) (u := 13) (t := 16)
    (D := 16) (ψ := (49388141/1250000000 : ℝ)) half_19_02_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_19_02_bounds4 l).1) (fun l => (half_19_02_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_19_02_total1, half_19_02_total2, half_19_02_total3, half_19_02_total4, half_19_02_total5, half_19_02_total6, half_19_02_total7, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher18SimpleSeeds.degree18_half_14) (SeedCompletionHigher18SimpleSeeds.degree18_half_16)
    (by simpa only [half_19_02_φ5, show (2:ℝ)*16=32 by norm_num] using half_19_02_hx5)
  exact h.weaken (by norm_num [half_19_02_total1, half_19_02_total2, half_19_02_total3, half_19_02_total4, half_19_02_total5, half_19_02_total6, half_19_02_total7, parameterExponent, curveLoss, dyadicExponent])

private theorem half_19_02_hx3 : SourcePowerBound
    (powerBoxCross 18 16 8 half_19_02_φ3) (92976692001/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 16) (u := 14) (t := 17)
    (D := 8) (ψ := (204655249/5000000000 : ℝ)) half_19_02_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_19_02_bounds3 l).1) (fun l => (half_19_02_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_19_02_total1, half_19_02_total2, half_19_02_total3, half_19_02_total4, half_19_02_total5, half_19_02_total6, half_19_02_total7, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher18SimpleSeeds.degree18_half_15) (SeedCompletionHigher18SimpleSeeds.degree18_half_17)
    (by simpa only [half_19_02_φ4, show (2:ℝ)*8=16 by norm_num] using half_19_02_hx4)
  exact h.weaken (by norm_num [half_19_02_total1, half_19_02_total2, half_19_02_total3, half_19_02_total4, half_19_02_total5, half_19_02_total6, half_19_02_total7, parameterExponent, curveLoss, dyadicExponent])

private theorem half_19_02_hx2 : SourcePowerBound
    (powerBoxCross 18 17 4 half_19_02_φ2) (205463101441/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 17) (u := 15) (t := 18)
    (D := 4) (ψ := (420141869/10000000000 : ℝ)) half_19_02_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_19_02_bounds2 l).1) (fun l => (half_19_02_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_19_02_total1, half_19_02_total2, half_19_02_total3, half_19_02_total4, half_19_02_total5, half_19_02_total6, half_19_02_total7, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher18SimpleSeeds.degree18_half_16) (half_18_02)
    (by simpa only [half_19_02_φ3, show (2:ℝ)*4=8 by norm_num] using half_19_02_hx3)
  exact h.weaken (by norm_num [half_19_02_total1, half_19_02_total2, half_19_02_total3, half_19_02_total4, half_19_02_total5, half_19_02_total6, half_19_02_total7, parameterExponent, curveLoss, dyadicExponent])

private theorem half_19_02_hx1 : SourcePowerBound
    (powerBoxCross 18 18 2 half_19_02_φ1) (227460512487/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 18) (u := 16) (t := 19)
    (D := 2) (ψ := (27159469/625000000 : ℝ)) half_19_02_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_19_02_bounds1 l).1) (fun l => (half_19_02_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_19_02_total1, half_19_02_total2, half_19_02_total3, half_19_02_total4, half_19_02_total5, half_19_02_total6, half_19_02_total7, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher18SimpleSeeds.degree18_half_17) (chord_59)
    (by simpa only [half_19_02_φ2, show (2:ℝ)*2=4 by norm_num] using half_19_02_hx2)
  exact h.weaken (by norm_num [half_19_02_total1, half_19_02_total2, half_19_02_total3, half_19_02_total4, half_19_02_total5, half_19_02_total6, half_19_02_total7, parameterExponent, curveLoss, dyadicExponent])

theorem half_19_02 : AdmissibleExponent 18 38 (121743616721/5000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 17) (ψ := (457906313/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_18_02)
    (by simpa only [half_19_02_φ1] using half_19_02_hx1)
  exact admissibleExponent_mono h (by norm_num [half_19_02_total1, half_19_02_total2, half_19_02_total3, half_19_02_total4, half_19_02_total5, half_19_02_total6, half_19_02_total7, parameterExponent, curveLoss, dyadicExponent])

theorem chord_60 : AdmissibleExponent 18 40 (260541583623/10000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 40) (t := (1/2 : ℝ))
    (half_19_02) (half_21_01)
    (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private def half_20_02_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (233190727/5000000000 : ℝ)

private theorem half_20_02_total1 : total half_20_02_φ1=(233190727/5000000000 : ℝ) := by
  norm_num [half_20_02_φ1,total,emptyPhi,Fin.snoc]

private theorem half_20_02_bounds1 : ∀ l,0≤half_20_02_φ1 l ∧ half_20_02_φ1 l≤1 ∧
    0≤shiftExponents 18 half_20_02_φ1 l :=
  alternate_bounds_snoc emptyPhi (233190727/5000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_20_02_φ2 : Fin 2 → ℝ := Fin.snoc half_20_02_φ1 (441406507/10000000000 : ℝ)

private theorem half_20_02_total2 : total half_20_02_φ2=(907787961/10000000000 : ℝ) := by
  change total (Fin.snoc half_20_02_φ1 (441406507/10000000000 : ℝ))=(907787961/10000000000 : ℝ)
  rw [alternate_total_snoc,half_20_02_total1]
  norm_num

private theorem half_20_02_bounds2 : ∀ l,0≤half_20_02_φ2 l ∧ half_20_02_φ2 l≤1 ∧
    0≤shiftExponents 18 half_20_02_φ2 l :=
  alternate_bounds_snoc half_20_02_φ1 (441406507/10000000000 : ℝ) half_20_02_bounds1 (by norm_num)

private def half_20_02_φ3 : Fin 3 → ℝ := Fin.snoc half_20_02_φ2 (433508483/10000000000 : ℝ)

private theorem half_20_02_total3 : total half_20_02_φ3=(335324111/2500000000 : ℝ) := by
  change total (Fin.snoc half_20_02_φ2 (433508483/10000000000 : ℝ))=(335324111/2500000000 : ℝ)
  rw [alternate_total_snoc,half_20_02_total2]
  norm_num

private theorem half_20_02_bounds3 : ∀ l,0≤half_20_02_φ3 l ∧ half_20_02_φ3 l≤1 ∧
    0≤shiftExponents 18 half_20_02_φ3 l :=
  alternate_bounds_snoc half_20_02_φ2 (433508483/10000000000 : ℝ) half_20_02_bounds2 (by norm_num)

private def half_20_02_φ4 : Fin 4 → ℝ := Fin.snoc half_20_02_φ3 (418917111/10000000000 : ℝ)

private theorem half_20_02_total4 : total half_20_02_φ4=(352042711/2000000000 : ℝ) := by
  change total (Fin.snoc half_20_02_φ3 (418917111/10000000000 : ℝ))=(352042711/2000000000 : ℝ)
  rw [alternate_total_snoc,half_20_02_total3]
  norm_num

private theorem half_20_02_bounds4 : ∀ l,0≤half_20_02_φ4 l ∧ half_20_02_φ4 l≤1 ∧
    0≤shiftExponents 18 half_20_02_φ4 l :=
  alternate_bounds_snoc half_20_02_φ3 (418917111/10000000000 : ℝ) half_20_02_bounds3 (by norm_num)

private def half_20_02_φ5 : Fin 5 → ℝ := Fin.snoc half_20_02_φ4 (10170039/250000000 : ℝ)

private theorem half_20_02_total5 : total half_20_02_φ5=(433403023/2000000000 : ℝ) := by
  change total (Fin.snoc half_20_02_φ4 (10170039/250000000 : ℝ))=(433403023/2000000000 : ℝ)
  rw [alternate_total_snoc,half_20_02_total4]
  norm_num

private theorem half_20_02_bounds5 : ∀ l,0≤half_20_02_φ5 l ∧ half_20_02_φ5 l≤1 ∧
    0≤shiftExponents 18 half_20_02_φ5 l :=
  alternate_bounds_snoc half_20_02_φ4 (10170039/250000000 : ℝ) half_20_02_bounds4 (by norm_num)

private def half_20_02_φ6 : Fin 6 → ℝ := Fin.snoc half_20_02_φ5 (77681111/2000000000 : ℝ)

private theorem half_20_02_total6 : total half_20_02_φ6=(255542067/1000000000 : ℝ) := by
  change total (Fin.snoc half_20_02_φ5 (77681111/2000000000 : ℝ))=(255542067/1000000000 : ℝ)
  rw [alternate_total_snoc,half_20_02_total5]
  norm_num

private theorem half_20_02_bounds6 : ∀ l,0≤half_20_02_φ6 l ∧ half_20_02_φ6 l≤1 ∧
    0≤shiftExponents 18 half_20_02_φ6 l :=
  alternate_bounds_snoc half_20_02_φ5 (77681111/2000000000 : ℝ) half_20_02_bounds5 (by norm_num)

private def half_20_02_φ7 : Fin 7 → ℝ := Fin.snoc half_20_02_φ6 (21781181/625000000 : ℝ)

private theorem half_20_02_total7 : total half_20_02_φ7=(1451959783/5000000000 : ℝ) := by
  change total (Fin.snoc half_20_02_φ6 (21781181/625000000 : ℝ))=(1451959783/5000000000 : ℝ)
  rw [alternate_total_snoc,half_20_02_total6]
  norm_num

private theorem half_20_02_bounds7 : ∀ l,0≤half_20_02_φ7 l ∧ half_20_02_φ7 l≤1 ∧
    0≤shiftExponents 18 half_20_02_φ7 l :=
  alternate_bounds_snoc half_20_02_φ6 (21781181/625000000 : ℝ) half_20_02_bounds6 (by norm_num)

private def half_20_02_φ8 : Fin 8 → ℝ := Fin.snoc half_20_02_φ7 (228066597/10000000000 : ℝ)

private theorem half_20_02_total8 : total half_20_02_φ8=(3131986163/10000000000 : ℝ) := by
  change total (Fin.snoc half_20_02_φ7 (228066597/10000000000 : ℝ))=(3131986163/10000000000 : ℝ)
  rw [alternate_total_snoc,half_20_02_total7]
  norm_num

private theorem half_20_02_bounds8 : ∀ l,0≤half_20_02_φ8 l ∧ half_20_02_φ8 l≤1 ∧
    0≤shiftExponents 18 half_20_02_φ8 l :=
  alternate_bounds_snoc half_20_02_φ7 (228066597/10000000000 : ℝ) half_20_02_bounds7 (by norm_num)

private theorem half_20_02_prefix : PrefixCondition 18 half_20_02_φ8 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_20_02_φ1, half_20_02_φ2, half_20_02_φ3, half_20_02_φ4, half_20_02_φ5, half_20_02_φ6, half_20_02_φ7, half_20_02_φ8, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_20_02_hF2 : SourcePowerBound
    (paddedMoment 18 0 2 256 half_20_02_φ8) (100268705687/10000000000 : ℝ) := by
  have h := padded_dyadic_divisor_power (k := 18) (j := 8) (r := 0) (n := 1) (D := 256)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_20_02_φ8
    (fun i => (half_20_02_bounds8 i).1) (fun i => (half_20_02_bounds8 i).2.1)
    (fun i => (half_20_02_bounds8 i).2.2) half_20_02_prefix
  convert h using 1 <;> norm_num [half_20_02_total1, half_20_02_total2, half_20_02_total3, half_20_02_total4, half_20_02_total5, half_20_02_total6, half_20_02_total7, half_20_02_total8, parameterExponent, curveLoss, dyadicExponent]

private theorem half_20_02_hx8 : SourcePowerBound
    (powerBoxCross 18 12 256 half_20_02_φ8) (126283112559/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 12) (r := 2) (v := 0) (w := 16) (D := 256)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_20_02_φ8 (by norm_num [half_20_02_total1, half_20_02_total2, half_20_02_total3, half_20_02_total4, half_20_02_total5, half_20_02_total6, half_20_02_total7, half_20_02_total8, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_20_02_total1, half_20_02_total2, half_20_02_total3, half_20_02_total4, half_20_02_total5, half_20_02_total6, half_20_02_total7, half_20_02_total8, parameterExponent, curveLoss, dyadicExponent]) half_20_02_hF2
    (admissibleExponent_zero 18) (SeedCompletionHigher18SimpleSeeds.degree18_half_16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_20_02_total1, half_20_02_total2, half_20_02_total3, half_20_02_total4, half_20_02_total5, half_20_02_total6, half_20_02_total7, half_20_02_total8, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_02_hx7 : SourcePowerBound
    (powerBoxCross 18 13 128 half_20_02_φ7) (33837748341/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 7) (s := 13) (u := 11) (t := 14)
    (D := 128) (ψ := (228066597/10000000000 : ℝ)) half_20_02_φ7
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_02_bounds7 l).1) (fun l => (half_20_02_bounds7 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_02_total1, half_20_02_total2, half_20_02_total3, half_20_02_total4, half_20_02_total5, half_20_02_total6, half_20_02_total7, half_20_02_total8, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher18SimpleSeeds.degree18_half_12) (SeedCompletionHigher18SimpleSeeds.degree18_half_14)
    (by simpa only [half_20_02_φ8, show (2:ℝ)*128=256 by norm_num] using half_20_02_hx8)
  exact h.weaken (by norm_num [half_20_02_total1, half_20_02_total2, half_20_02_total3, half_20_02_total4, half_20_02_total5, half_20_02_total6, half_20_02_total7, half_20_02_total8, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_02_hx6 : SourcePowerBound
    (powerBoxCross 18 14 64 half_20_02_φ6) (73955397667/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 6) (s := 14) (u := 12) (t := 15)
    (D := 64) (ψ := (21781181/625000000 : ℝ)) half_20_02_φ6
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_02_bounds6 l).1) (fun l => (half_20_02_bounds6 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_02_total1, half_20_02_total2, half_20_02_total3, half_20_02_total4, half_20_02_total5, half_20_02_total6, half_20_02_total7, half_20_02_total8, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher18SimpleSeeds.degree18_half_13) (SeedCompletionHigher18SimpleSeeds.degree18_half_15)
    (by simpa only [half_20_02_φ7, show (2:ℝ)*64=128 by norm_num] using half_20_02_hx7)
  exact h.weaken (by norm_num [half_20_02_total1, half_20_02_total2, half_20_02_total3, half_20_02_total4, half_20_02_total5, half_20_02_total6, half_20_02_total7, half_20_02_total8, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_02_hx5 : SourcePowerBound
    (powerBoxCross 18 15 32 half_20_02_φ5) (81368621343/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 5) (s := 15) (u := 13) (t := 16)
    (D := 32) (ψ := (77681111/2000000000 : ℝ)) half_20_02_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_02_bounds5 l).1) (fun l => (half_20_02_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_02_total1, half_20_02_total2, half_20_02_total3, half_20_02_total4, half_20_02_total5, half_20_02_total6, half_20_02_total7, half_20_02_total8, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher18SimpleSeeds.degree18_half_14) (SeedCompletionHigher18SimpleSeeds.degree18_half_16)
    (by simpa only [half_20_02_φ6, show (2:ℝ)*32=64 by norm_num] using half_20_02_hx6)
  exact h.weaken (by norm_num [half_20_02_total1, half_20_02_total2, half_20_02_total3, half_20_02_total4, half_20_02_total5, half_20_02_total6, half_20_02_total7, half_20_02_total8, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_02_hx4 : SourcePowerBound
    (powerBoxCross 18 16 16 half_20_02_φ4) (179526413267/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 16) (u := 14) (t := 17)
    (D := 16) (ψ := (10170039/250000000 : ℝ)) half_20_02_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_02_bounds4 l).1) (fun l => (half_20_02_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_02_total1, half_20_02_total2, half_20_02_total3, half_20_02_total4, half_20_02_total5, half_20_02_total6, half_20_02_total7, half_20_02_total8, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher18SimpleSeeds.degree18_half_15) (SeedCompletionHigher18SimpleSeeds.degree18_half_17)
    (by simpa only [half_20_02_φ5, show (2:ℝ)*16=32 by norm_num] using half_20_02_hx5)
  exact h.weaken (by norm_num [half_20_02_total1, half_20_02_total2, half_20_02_total3, half_20_02_total4, half_20_02_total5, half_20_02_total6, half_20_02_total7, half_20_02_total8, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_02_hx3 : SourcePowerBound
    (powerBoxCross 18 17 8 half_20_02_φ3) (49577961679/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 17) (u := 15) (t := 18)
    (D := 8) (ψ := (418917111/10000000000 : ℝ)) half_20_02_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_02_bounds3 l).1) (fun l => (half_20_02_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_02_total1, half_20_02_total2, half_20_02_total3, half_20_02_total4, half_20_02_total5, half_20_02_total6, half_20_02_total7, half_20_02_total8, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher18SimpleSeeds.degree18_half_16) (half_18_02)
    (by simpa only [half_20_02_φ4, show (2:ℝ)*8=16 by norm_num] using half_20_02_hx4)
  exact h.weaken (by norm_num [half_20_02_total1, half_20_02_total2, half_20_02_total3, half_20_02_total4, half_20_02_total5, half_20_02_total6, half_20_02_total7, half_20_02_total8, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_02_hx2 : SourcePowerBound
    (powerBoxCross 18 18 4 half_20_02_φ2) (109642246711/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 18) (u := 16) (t := 19)
    (D := 4) (ψ := (433508483/10000000000 : ℝ)) half_20_02_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_02_bounds2 l).1) (fun l => (half_20_02_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_02_total1, half_20_02_total2, half_20_02_total3, half_20_02_total4, half_20_02_total5, half_20_02_total6, half_20_02_total7, half_20_02_total8, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher18SimpleSeeds.degree18_half_17) (half_19_02)
    (by simpa only [half_20_02_φ3, show (2:ℝ)*4=8 by norm_num] using half_20_02_hx3)
  exact h.weaken (by norm_num [half_20_02_total1, half_20_02_total2, half_20_02_total3, half_20_02_total4, half_20_02_total5, half_20_02_total6, half_20_02_total7, half_20_02_total8, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_02_hx1 : SourcePowerBound
    (powerBoxCross 18 19 2 half_20_02_φ1) (242597821907/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 19) (u := 17) (t := 20)
    (D := 2) (ψ := (441406507/10000000000 : ℝ)) half_20_02_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_02_bounds1 l).1) (fun l => (half_20_02_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_02_total1, half_20_02_total2, half_20_02_total3, half_20_02_total4, half_20_02_total5, half_20_02_total6, half_20_02_total7, half_20_02_total8, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_18_02) (chord_60)
    (by simpa only [half_20_02_φ2, show (2:ℝ)*2=4 by norm_num] using half_20_02_hx2)
  exact h.weaken (by norm_num [half_20_02_total1, half_20_02_total2, half_20_02_total3, half_20_02_total4, half_20_02_total5, half_20_02_total6, half_20_02_total7, half_20_02_total8, parameterExponent, curveLoss, dyadicExponent])

theorem half_20_02 : AdmissibleExponent 18 40 (51970787141/2000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 18) (ψ := (233190727/5000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_19_02)
    (by simpa only [half_20_02_φ1] using half_20_02_hx1)
  exact admissibleExponent_mono h (by norm_num [half_20_02_total1, half_20_02_total2, half_20_02_total3, half_20_02_total4, half_20_02_total5, half_20_02_total6, half_20_02_total7, half_20_02_total8, parameterExponent, curveLoss, dyadicExponent])

#print axioms half_20_02
end Waring.SeedCompletionAlternate18Seeds
