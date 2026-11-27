import Waring.SeedCompletionAlternate16Steps01

noncomputable section
set_option maxHeartbeats 2000000
namespace Waring.SeedCompletionAlternate16Seeds
open SmoothMoments FirstStageTransport SeedCompletionNaturalBox
open SeedCompletionSourceBounds SeedCompletionPaddedSource SeedCompletionGeneralTerminal
open PolicyCompletionMajorPowerRanges SeedCompletionDivisorPowerScales
open PolicyCompletionSharpResidualSource

private def half_23_01_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (5792683/100000000 : ℝ)

private theorem half_23_01_total1 : total half_23_01_φ1=(5792683/100000000 : ℝ) := by
  norm_num [half_23_01_φ1,total,emptyPhi,Fin.snoc]

private theorem half_23_01_bounds1 : ∀ l,0≤half_23_01_φ1 l ∧ half_23_01_φ1 l≤1 ∧
    0≤shiftExponents 16 half_23_01_φ1 l :=
  alternate_bounds_snoc emptyPhi (5792683/100000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_23_01_φ2 : Fin 2 → ℝ := Fin.snoc half_23_01_φ1 (266118657/5000000000 : ℝ)

private theorem half_23_01_total2 : total half_23_01_φ2=(555752807/5000000000 : ℝ) := by
  change total (Fin.snoc half_23_01_φ1 (266118657/5000000000 : ℝ))=(555752807/5000000000 : ℝ)
  rw [alternate_total_snoc,half_23_01_total1]
  norm_num

private theorem half_23_01_bounds2 : ∀ l,0≤half_23_01_φ2 l ∧ half_23_01_φ2 l≤1 ∧
    0≤shiftExponents 16 half_23_01_φ2 l :=
  alternate_bounds_snoc half_23_01_φ1 (266118657/5000000000 : ℝ) half_23_01_bounds1 (by norm_num)

private def half_23_01_φ3 : Fin 3 → ℝ := Fin.snoc half_23_01_φ2 (8197741/156250000 : ℝ)

private theorem half_23_01_total3 : total half_23_01_φ3=(818080519/5000000000 : ℝ) := by
  change total (Fin.snoc half_23_01_φ2 (8197741/156250000 : ℝ))=(818080519/5000000000 : ℝ)
  rw [alternate_total_snoc,half_23_01_total2]
  norm_num

private theorem half_23_01_bounds3 : ∀ l,0≤half_23_01_φ3 l ∧ half_23_01_φ3 l≤1 ∧
    0≤shiftExponents 16 half_23_01_φ3 l :=
  alternate_bounds_snoc half_23_01_φ2 (8197741/156250000 : ℝ) half_23_01_bounds2 (by norm_num)

private def half_23_01_φ4 : Fin 4 → ℝ := Fin.snoc half_23_01_φ3 (64698391/1250000000 : ℝ)

private theorem half_23_01_total4 : total half_23_01_φ4=(1076874083/5000000000 : ℝ) := by
  change total (Fin.snoc half_23_01_φ3 (64698391/1250000000 : ℝ))=(1076874083/5000000000 : ℝ)
  rw [alternate_total_snoc,half_23_01_total3]
  norm_num

private theorem half_23_01_bounds4 : ∀ l,0≤half_23_01_φ4 l ∧ half_23_01_φ4 l≤1 ∧
    0≤shiftExponents 16 half_23_01_φ4 l :=
  alternate_bounds_snoc half_23_01_φ3 (64698391/1250000000 : ℝ) half_23_01_bounds3 (by norm_num)

private def half_23_01_φ5 : Fin 5 → ℝ := Fin.snoc half_23_01_φ4 (51197221/1000000000 : ℝ)

private theorem half_23_01_total5 : total half_23_01_φ5=(333215047/1250000000 : ℝ) := by
  change total (Fin.snoc half_23_01_φ4 (51197221/1000000000 : ℝ))=(333215047/1250000000 : ℝ)
  rw [alternate_total_snoc,half_23_01_total4]
  norm_num

private theorem half_23_01_bounds5 : ∀ l,0≤half_23_01_φ5 l ∧ half_23_01_φ5 l≤1 ∧
    0≤shiftExponents 16 half_23_01_φ5 l :=
  alternate_bounds_snoc half_23_01_φ4 (51197221/1000000000 : ℝ) half_23_01_bounds4 (by norm_num)

private def half_23_01_φ6 : Fin 6 → ℝ := Fin.snoc half_23_01_φ5 (244475987/5000000000 : ℝ)

private theorem half_23_01_total6 : total half_23_01_φ6=(63093447/200000000 : ℝ) := by
  change total (Fin.snoc half_23_01_φ5 (244475987/5000000000 : ℝ))=(63093447/200000000 : ℝ)
  rw [alternate_total_snoc,half_23_01_total5]
  norm_num

private theorem half_23_01_bounds6 : ∀ l,0≤half_23_01_φ6 l ∧ half_23_01_φ6 l≤1 ∧
    0≤shiftExponents 16 half_23_01_φ6 l :=
  alternate_bounds_snoc half_23_01_φ5 (244475987/5000000000 : ℝ) half_23_01_bounds5 (by norm_num)

private def half_23_01_φ7 : Fin 7 → ℝ := Fin.snoc half_23_01_φ6 (57044397/1250000000 : ℝ)

private theorem half_23_01_total7 : total half_23_01_φ7=(1805513763/5000000000 : ℝ) := by
  change total (Fin.snoc half_23_01_φ6 (57044397/1250000000 : ℝ))=(1805513763/5000000000 : ℝ)
  rw [alternate_total_snoc,half_23_01_total6]
  norm_num

private theorem half_23_01_bounds7 : ∀ l,0≤half_23_01_φ7 l ∧ half_23_01_φ7 l≤1 ∧
    0≤shiftExponents 16 half_23_01_φ7 l :=
  alternate_bounds_snoc half_23_01_φ6 (57044397/1250000000 : ℝ) half_23_01_bounds6 (by norm_num)

private def half_23_01_φ8 : Fin 8 → ℝ := Fin.snoc half_23_01_φ7 (425931497/10000000000 : ℝ)

private theorem half_23_01_total8 : total half_23_01_φ8=(4036959023/10000000000 : ℝ) := by
  change total (Fin.snoc half_23_01_φ7 (425931497/10000000000 : ℝ))=(4036959023/10000000000 : ℝ)
  rw [alternate_total_snoc,half_23_01_total7]
  norm_num

private theorem half_23_01_bounds8 : ∀ l,0≤half_23_01_φ8 l ∧ half_23_01_φ8 l≤1 ∧
    0≤shiftExponents 16 half_23_01_φ8 l :=
  alternate_bounds_snoc half_23_01_φ7 (425931497/10000000000 : ℝ) half_23_01_bounds7 (by norm_num)

private def half_23_01_φ9 : Fin 9 → ℝ := Fin.snoc half_23_01_φ8 (6211501/156250000 : ℝ)

private theorem half_23_01_total9 : total half_23_01_φ9=(4434495087/10000000000 : ℝ) := by
  change total (Fin.snoc half_23_01_φ8 (6211501/156250000 : ℝ))=(4434495087/10000000000 : ℝ)
  rw [alternate_total_snoc,half_23_01_total8]
  norm_num

private theorem half_23_01_bounds9 : ∀ l,0≤half_23_01_φ9 l ∧ half_23_01_φ9 l≤1 ∧
    0≤shiftExponents 16 half_23_01_φ9 l :=
  alternate_bounds_snoc half_23_01_φ8 (6211501/156250000 : ℝ) half_23_01_bounds8 (by norm_num)

private def half_23_01_φ10 : Fin 10 → ℝ := Fin.snoc half_23_01_φ9 (358253537/10000000000 : ℝ)

private theorem half_23_01_total10 : total half_23_01_φ10=(299546789/625000000 : ℝ) := by
  change total (Fin.snoc half_23_01_φ9 (358253537/10000000000 : ℝ))=(299546789/625000000 : ℝ)
  rw [alternate_total_snoc,half_23_01_total9]
  norm_num

private theorem half_23_01_bounds10 : ∀ l,0≤half_23_01_φ10 l ∧ half_23_01_φ10 l≤1 ∧
    0≤shiftExponents 16 half_23_01_φ10 l :=
  alternate_bounds_snoc half_23_01_φ9 (358253537/10000000000 : ℝ) half_23_01_bounds9 (by norm_num)

private def half_23_01_φ11 : Fin 11 → ℝ := Fin.snoc half_23_01_φ10 (129354873/10000000000 : ℝ)

private theorem half_23_01_total11 : total half_23_01_φ11=(4922103497/10000000000 : ℝ) := by
  change total (Fin.snoc half_23_01_φ10 (129354873/10000000000 : ℝ))=(4922103497/10000000000 : ℝ)
  rw [alternate_total_snoc,half_23_01_total10]
  norm_num

private theorem half_23_01_bounds11 : ∀ l,0≤half_23_01_φ11 l ∧ half_23_01_φ11 l≤1 ∧
    0≤shiftExponents 16 half_23_01_φ11 l :=
  alternate_bounds_snoc half_23_01_φ10 (129354873/10000000000 : ℝ) half_23_01_bounds10 (by norm_num)

private theorem half_23_01_prefix : PrefixCondition 16 half_23_01_φ11 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_23_01_φ1, half_23_01_φ2, half_23_01_φ3, half_23_01_φ4, half_23_01_φ5, half_23_01_φ6, half_23_01_φ7, half_23_01_φ8, half_23_01_φ9, half_23_01_φ10, half_23_01_φ11, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_23_01_hF1 : SourcePowerBound
    (paddedMoment 16 0 1 2048 half_23_01_φ11) (9233689509/2000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 16) (j := 11) (r := 0) (n := 0) (D := 2048)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_23_01_φ11
    (fun i => (half_23_01_bounds11 i).1) (fun i => (half_23_01_bounds11 i).2.1)
    (fun i => (half_23_01_bounds11 i).2.2) half_23_01_prefix
  convert h using 1 <;> norm_num [half_23_01_total1, half_23_01_total2, half_23_01_total3, half_23_01_total4, half_23_01_total5, half_23_01_total6, half_23_01_total7, half_23_01_total8, half_23_01_total9, half_23_01_total10, half_23_01_total11, parameterExponent, curveLoss, dyadicExponent]

private theorem half_23_01_hx11 : SourcePowerBound
    (powerBoxCross 16 12 2048 half_23_01_φ11) (55096508191/5000000000 : ℝ) := by
  have h := full_A_cross_power (k := 16) (s := 12) (r := 1) (v := 0) (w := 24) (D := 2048)
    (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_23_01_φ11 (by norm_num [half_23_01_total1, half_23_01_total2, half_23_01_total3, half_23_01_total4, half_23_01_total5, half_23_01_total6, half_23_01_total7, half_23_01_total8, half_23_01_total9, half_23_01_total10, half_23_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_23_01_total1, half_23_01_total2, half_23_01_total3, half_23_01_total4, half_23_01_total5, half_23_01_total6, half_23_01_total7, half_23_01_total8, half_23_01_total9, half_23_01_total10, half_23_01_total11, parameterExponent, curveLoss, dyadicExponent]) half_23_01_hF1
    (admissibleExponent_zero 16) (chord_47)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_23_01_total1, half_23_01_total2, half_23_01_total3, half_23_01_total4, half_23_01_total5, half_23_01_total6, half_23_01_total7, half_23_01_total8, half_23_01_total9, half_23_01_total10, half_23_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_23_01_hx10 : SourcePowerBound
    (powerBoxCross 16 13 1024 half_23_01_φ10) (115136072579/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 10) (s := 13) (u := 11) (t := 14)
    (D := 1024) (ψ := (129354873/10000000000 : ℝ)) half_23_01_φ10
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_23_01_bounds10 l).1) (fun l => (half_23_01_bounds10 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_23_01_total1, half_23_01_total2, half_23_01_total3, half_23_01_total4, half_23_01_total5, half_23_01_total6, half_23_01_total7, half_23_01_total8, half_23_01_total9, half_23_01_total10, half_23_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher16SimpleSeeds.degree16_half_12) (SeedCompletionHigher16SimpleSeeds.degree16_half_14)
    (by simpa only [half_23_01_φ11, show (2:ℝ)*1024=2048 by norm_num] using half_23_01_hx11)
  exact h.weaken (by norm_num [half_23_01_total1, half_23_01_total2, half_23_01_total3, half_23_01_total4, half_23_01_total5, half_23_01_total6, half_23_01_total7, half_23_01_total8, half_23_01_total9, half_23_01_total10, half_23_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_23_01_hx9 : SourcePowerBound
    (powerBoxCross 16 14 512 half_23_01_φ9) (125713451817/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 9) (s := 14) (u := 12) (t := 15)
    (D := 512) (ψ := (358253537/10000000000 : ℝ)) half_23_01_φ9
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_23_01_bounds9 l).1) (fun l => (half_23_01_bounds9 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_23_01_total1, half_23_01_total2, half_23_01_total3, half_23_01_total4, half_23_01_total5, half_23_01_total6, half_23_01_total7, half_23_01_total8, half_23_01_total9, half_23_01_total10, half_23_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher16SimpleSeeds.degree16_half_13) (half_15_01)
    (by simpa only [half_23_01_φ10, show (2:ℝ)*512=1024 by norm_num] using half_23_01_hx10)
  exact h.weaken (by norm_num [half_23_01_total1, half_23_01_total2, half_23_01_total3, half_23_01_total4, half_23_01_total5, half_23_01_total6, half_23_01_total7, half_23_01_total8, half_23_01_total9, half_23_01_total10, half_23_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_23_01_hx8 : SourcePowerBound
    (powerBoxCross 16 15 256 half_23_01_φ8) (69183630763/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 8) (s := 15) (u := 13) (t := 16)
    (D := 256) (ψ := (6211501/156250000 : ℝ)) half_23_01_φ8
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_23_01_bounds8 l).1) (fun l => (half_23_01_bounds8 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_23_01_total1, half_23_01_total2, half_23_01_total3, half_23_01_total4, half_23_01_total5, half_23_01_total6, half_23_01_total7, half_23_01_total8, half_23_01_total9, half_23_01_total10, half_23_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher16SimpleSeeds.degree16_half_14) (half_16_01)
    (by simpa only [half_23_01_φ9, show (2:ℝ)*256=512 by norm_num] using half_23_01_hx9)
  exact h.weaken (by norm_num [half_23_01_total1, half_23_01_total2, half_23_01_total3, half_23_01_total4, half_23_01_total5, half_23_01_total6, half_23_01_total7, half_23_01_total8, half_23_01_total9, half_23_01_total10, half_23_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_23_01_hx7 : SourcePowerBound
    (powerBoxCross 16 16 128 half_23_01_φ7) (153237646631/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 7) (s := 16) (u := 14) (t := 17)
    (D := 128) (ψ := (425931497/10000000000 : ℝ)) half_23_01_φ7
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_23_01_bounds7 l).1) (fun l => (half_23_01_bounds7 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_23_01_total1, half_23_01_total2, half_23_01_total3, half_23_01_total4, half_23_01_total5, half_23_01_total6, half_23_01_total7, half_23_01_total8, half_23_01_total9, half_23_01_total10, half_23_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_15_01) (half_17_01)
    (by simpa only [half_23_01_φ8, show (2:ℝ)*128=256 by norm_num] using half_23_01_hx8)
  exact h.weaken (by norm_num [half_23_01_total1, half_23_01_total2, half_23_01_total3, half_23_01_total4, half_23_01_total5, half_23_01_total6, half_23_01_total7, half_23_01_total8, half_23_01_total9, half_23_01_total10, half_23_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_23_01_hx6 : SourcePowerBound
    (powerBoxCross 16 17 64 half_23_01_φ6) (6827476127/400000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 6) (s := 17) (u := 15) (t := 18)
    (D := 64) (ψ := (57044397/1250000000 : ℝ)) half_23_01_φ6
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_23_01_bounds6 l).1) (fun l => (half_23_01_bounds6 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_23_01_total1, half_23_01_total2, half_23_01_total3, half_23_01_total4, half_23_01_total5, half_23_01_total6, half_23_01_total7, half_23_01_total8, half_23_01_total9, half_23_01_total10, half_23_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_16_01) (half_18_01)
    (by simpa only [half_23_01_φ7, show (2:ℝ)*64=128 by norm_num] using half_23_01_hx7)
  exact h.weaken (by norm_num [half_23_01_total1, half_23_01_total2, half_23_01_total3, half_23_01_total4, half_23_01_total5, half_23_01_total6, half_23_01_total7, half_23_01_total8, half_23_01_total9, half_23_01_total10, half_23_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_23_01_hx5 : SourcePowerBound
    (powerBoxCross 16 18 32 half_23_01_φ5) (191037072393/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 5) (s := 18) (u := 16) (t := 19)
    (D := 32) (ψ := (244475987/5000000000 : ℝ)) half_23_01_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_23_01_bounds5 l).1) (fun l => (half_23_01_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_23_01_total1, half_23_01_total2, half_23_01_total3, half_23_01_total4, half_23_01_total5, half_23_01_total6, half_23_01_total7, half_23_01_total8, half_23_01_total9, half_23_01_total10, half_23_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_17_01) (half_19_01)
    (by simpa only [half_23_01_φ6, show (2:ℝ)*32=64 by norm_num] using half_23_01_hx6)
  exact h.weaken (by norm_num [half_23_01_total1, half_23_01_total2, half_23_01_total3, half_23_01_total4, half_23_01_total5, half_23_01_total6, half_23_01_total7, half_23_01_total8, half_23_01_total9, half_23_01_total10, half_23_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_23_01_hx4 : SourcePowerBound
    (powerBoxCross 16 19 16 half_23_01_φ4) (26767923479/1250000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 4) (s := 19) (u := 17) (t := 20)
    (D := 16) (ψ := (51197221/1000000000 : ℝ)) half_23_01_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_23_01_bounds4 l).1) (fun l => (half_23_01_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_23_01_total1, half_23_01_total2, half_23_01_total3, half_23_01_total4, half_23_01_total5, half_23_01_total6, half_23_01_total7, half_23_01_total8, half_23_01_total9, half_23_01_total10, half_23_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_18_01) (half_20_01)
    (by simpa only [half_23_01_φ5, show (2:ℝ)*16=32 by norm_num] using half_23_01_hx5)
  exact h.weaken (by norm_num [half_23_01_total1, half_23_01_total2, half_23_01_total3, half_23_01_total4, half_23_01_total5, half_23_01_total6, half_23_01_total7, half_23_01_total8, half_23_01_total9, half_23_01_total10, half_23_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_23_01_hx3 : SourcePowerBound
    (powerBoxCross 16 20 8 half_23_01_φ3) (59862460949/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 20) (u := 18) (t := 21)
    (D := 8) (ψ := (64698391/1250000000 : ℝ)) half_23_01_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_23_01_bounds3 l).1) (fun l => (half_23_01_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_23_01_total1, half_23_01_total2, half_23_01_total3, half_23_01_total4, half_23_01_total5, half_23_01_total6, half_23_01_total7, half_23_01_total8, half_23_01_total9, half_23_01_total10, half_23_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_19_01) (half_21_01)
    (by simpa only [half_23_01_φ4, show (2:ℝ)*8=16 by norm_num] using half_23_01_hx4)
  exact h.weaken (by norm_num [half_23_01_total1, half_23_01_total2, half_23_01_total3, half_23_01_total4, half_23_01_total5, half_23_01_total6, half_23_01_total7, half_23_01_total8, half_23_01_total9, half_23_01_total10, half_23_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_23_01_hx2 : SourcePowerBound
    (powerBoxCross 16 21 4 half_23_01_φ2) (267055452659/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 21) (u := 19) (t := 22)
    (D := 4) (ψ := (8197741/156250000 : ℝ)) half_23_01_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_23_01_bounds2 l).1) (fun l => (half_23_01_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_23_01_total1, half_23_01_total2, half_23_01_total3, half_23_01_total4, half_23_01_total5, half_23_01_total6, half_23_01_total7, half_23_01_total8, half_23_01_total9, half_23_01_total10, half_23_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_20_01) (half_22_01)
    (by simpa only [half_23_01_φ3, show (2:ℝ)*4=8 by norm_num] using half_23_01_hx3)
  exact h.weaken (by norm_num [half_23_01_total1, half_23_01_total2, half_23_01_total3, half_23_01_total4, half_23_01_total5, half_23_01_total6, half_23_01_total7, half_23_01_total8, half_23_01_total9, half_23_01_total10, half_23_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_23_01_hx1 : SourcePowerBound
    (powerBoxCross 16 22 2 half_23_01_φ1) (297670998301/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 22) (u := 20) (t := 23)
    (D := 2) (ψ := (266118657/5000000000 : ℝ)) half_23_01_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_23_01_bounds1 l).1) (fun l => (half_23_01_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_23_01_total1, half_23_01_total2, half_23_01_total3, half_23_01_total4, half_23_01_total5, half_23_01_total6, half_23_01_total7, half_23_01_total8, half_23_01_total9, half_23_01_total10, half_23_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_21_01) (chord_46)
    (by simpa only [half_23_01_φ2, show (2:ℝ)*2=4 by norm_num] using half_23_01_hx2)
  exact h.weaken (by norm_num [half_23_01_total1, half_23_01_total2, half_23_01_total3, half_23_01_total4, half_23_01_total5, half_23_01_total6, half_23_01_total7, half_23_01_total8, half_23_01_total9, half_23_01_total10, half_23_01_total11, parameterExponent, curveLoss, dyadicExponent])

theorem half_23_01 : AdmissibleExponent 16 46 (322579535201/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 21) (ψ := (5792683/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_22_01)
    (by simpa only [half_23_01_φ1] using half_23_01_hx1)
  exact admissibleExponent_mono h (by norm_num [half_23_01_total1, half_23_01_total2, half_23_01_total3, half_23_01_total4, half_23_01_total5, half_23_01_total6, half_23_01_total7, half_23_01_total8, half_23_01_total9, half_23_01_total10, half_23_01_total11, parameterExponent, curveLoss, dyadicExponent])

theorem chord_53 : AdmissibleExponent 16 48 (341943374357/10000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 48) (t := (6/7 : ℝ))
    (half_23_01) (half_30_00)
    (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private def half_24_01_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (292767913/5000000000 : ℝ)

private theorem half_24_01_total1 : total half_24_01_φ1=(292767913/5000000000 : ℝ) := by
  norm_num [half_24_01_φ1,total,emptyPhi,Fin.snoc]

private theorem half_24_01_bounds1 : ∀ l,0≤half_24_01_φ1 l ∧ half_24_01_φ1 l≤1 ∧
    0≤shiftExponents 16 half_24_01_φ1 l :=
  alternate_bounds_snoc emptyPhi (292767913/5000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_24_01_φ2 : Fin 2 → ℝ := Fin.snoc half_24_01_φ1 (4215259/78125000 : ℝ)

private theorem half_24_01_total2 : total half_24_01_φ2=(562544489/5000000000 : ℝ) := by
  change total (Fin.snoc half_24_01_φ1 (4215259/78125000 : ℝ))=(562544489/5000000000 : ℝ)
  rw [alternate_total_snoc,half_24_01_total1]
  norm_num

private theorem half_24_01_bounds2 : ∀ l,0≤half_24_01_φ2 l ∧ half_24_01_φ2 l≤1 ∧
    0≤shiftExponents 16 half_24_01_φ2 l :=
  alternate_bounds_snoc half_24_01_φ1 (4215259/78125000 : ℝ) half_24_01_bounds1 (by norm_num)

private def half_24_01_φ3 : Fin 3 → ℝ := Fin.snoc half_24_01_φ2 (532332319/10000000000 : ℝ)

private theorem half_24_01_total3 : total half_24_01_φ3=(1657421297/10000000000 : ℝ) := by
  change total (Fin.snoc half_24_01_φ2 (532332319/10000000000 : ℝ))=(1657421297/10000000000 : ℝ)
  rw [alternate_total_snoc,half_24_01_total2]
  norm_num

private theorem half_24_01_bounds3 : ∀ l,0≤half_24_01_φ3 l ∧ half_24_01_φ3 l≤1 ∧
    0≤shiftExponents 16 half_24_01_φ3 l :=
  alternate_bounds_snoc half_24_01_φ2 (532332319/10000000000 : ℝ) half_24_01_bounds2 (by norm_num)

private def half_24_01_φ4 : Fin 4 → ℝ := Fin.snoc half_24_01_φ3 (525817141/10000000000 : ℝ)

private theorem half_24_01_total4 : total half_24_01_φ4=(1091619219/5000000000 : ℝ) := by
  change total (Fin.snoc half_24_01_φ3 (525817141/10000000000 : ℝ))=(1091619219/5000000000 : ℝ)
  rw [alternate_total_snoc,half_24_01_total3]
  norm_num

private theorem half_24_01_bounds4 : ∀ l,0≤half_24_01_φ4 l ∧ half_24_01_φ4 l≤1 ∧
    0≤shiftExponents 16 half_24_01_φ4 l :=
  alternate_bounds_snoc half_24_01_φ3 (525817141/10000000000 : ℝ) half_24_01_bounds3 (by norm_num)

private def half_24_01_φ5 : Fin 5 → ℝ := Fin.snoc half_24_01_φ4 (521117437/10000000000 : ℝ)

private theorem half_24_01_total5 : total half_24_01_φ5=(21634847/80000000 : ℝ) := by
  change total (Fin.snoc half_24_01_φ4 (521117437/10000000000 : ℝ))=(21634847/80000000 : ℝ)
  rw [alternate_total_snoc,half_24_01_total4]
  norm_num

private theorem half_24_01_bounds5 : ∀ l,0≤half_24_01_φ5 l ∧ half_24_01_φ5 l≤1 ∧
    0≤shiftExponents 16 half_24_01_φ5 l :=
  alternate_bounds_snoc half_24_01_φ4 (521117437/10000000000 : ℝ) half_24_01_bounds4 (by norm_num)

private def half_24_01_φ6 : Fin 6 → ℝ := Fin.snoc half_24_01_φ5 (243188137/5000000000 : ℝ)

private theorem half_24_01_total6 : total half_24_01_φ6=(3190732149/10000000000 : ℝ) := by
  change total (Fin.snoc half_24_01_φ5 (243188137/5000000000 : ℝ))=(3190732149/10000000000 : ℝ)
  rw [alternate_total_snoc,half_24_01_total5]
  norm_num

private theorem half_24_01_bounds6 : ∀ l,0≤half_24_01_φ6 l ∧ half_24_01_φ6 l≤1 ∧
    0≤shiftExponents 16 half_24_01_φ6 l :=
  alternate_bounds_snoc half_24_01_φ5 (243188137/5000000000 : ℝ) half_24_01_bounds5 (by norm_num)

private def half_24_01_φ7 : Fin 7 → ℝ := Fin.snoc half_24_01_φ6 (453951189/10000000000 : ℝ)

private theorem half_24_01_total7 : total half_24_01_φ7=(1822341669/5000000000 : ℝ) := by
  change total (Fin.snoc half_24_01_φ6 (453951189/10000000000 : ℝ))=(1822341669/5000000000 : ℝ)
  rw [alternate_total_snoc,half_24_01_total6]
  norm_num

private theorem half_24_01_bounds7 : ∀ l,0≤half_24_01_φ7 l ∧ half_24_01_φ7 l≤1 ∧
    0≤shiftExponents 16 half_24_01_φ7 l :=
  alternate_bounds_snoc half_24_01_φ6 (453951189/10000000000 : ℝ) half_24_01_bounds6 (by norm_num)

private def half_24_01_φ8 : Fin 8 → ℝ := Fin.snoc half_24_01_φ7 (423687777/10000000000 : ℝ)

private theorem half_24_01_total8 : total half_24_01_φ8=(813674223/2000000000 : ℝ) := by
  change total (Fin.snoc half_24_01_φ7 (423687777/10000000000 : ℝ))=(813674223/2000000000 : ℝ)
  rw [alternate_total_snoc,half_24_01_total7]
  norm_num

private theorem half_24_01_bounds8 : ∀ l,0≤half_24_01_φ8 l ∧ half_24_01_φ8 l≤1 ∧
    0≤shiftExponents 16 half_24_01_φ8 l :=
  alternate_bounds_snoc half_24_01_φ7 (423687777/10000000000 : ℝ) half_24_01_bounds7 (by norm_num)

private def half_24_01_φ9 : Fin 9 → ℝ := Fin.snoc half_24_01_φ8 (15817677/400000000 : ℝ)

private theorem half_24_01_total9 : total half_24_01_φ9=(55797663/125000000 : ℝ) := by
  change total (Fin.snoc half_24_01_φ8 (15817677/400000000 : ℝ))=(55797663/125000000 : ℝ)
  rw [alternate_total_snoc,half_24_01_total8]
  norm_num

private theorem half_24_01_bounds9 : ∀ l,0≤half_24_01_φ9 l ∧ half_24_01_φ9 l≤1 ∧
    0≤shiftExponents 16 half_24_01_φ9 l :=
  alternate_bounds_snoc half_24_01_φ8 (15817677/400000000 : ℝ) half_24_01_bounds8 (by norm_num)

private def half_24_01_φ10 : Fin 10 → ℝ := Fin.snoc half_24_01_φ9 (36907913/1000000000 : ℝ)

private theorem half_24_01_total10 : total half_24_01_φ10=(483289217/1000000000 : ℝ) := by
  change total (Fin.snoc half_24_01_φ9 (36907913/1000000000 : ℝ))=(483289217/1000000000 : ℝ)
  rw [alternate_total_snoc,half_24_01_total9]
  norm_num

private theorem half_24_01_bounds10 : ∀ l,0≤half_24_01_φ10 l ∧ half_24_01_φ10 l≤1 ∧
    0≤shiftExponents 16 half_24_01_φ10 l :=
  alternate_bounds_snoc half_24_01_φ9 (36907913/1000000000 : ℝ) half_24_01_bounds9 (by norm_num)

private def half_24_01_φ11 : Fin 11 → ℝ := Fin.snoc half_24_01_φ10 (141761723/10000000000 : ℝ)

private theorem half_24_01_total11 : total half_24_01_φ11=(4974653893/10000000000 : ℝ) := by
  change total (Fin.snoc half_24_01_φ10 (141761723/10000000000 : ℝ))=(4974653893/10000000000 : ℝ)
  rw [alternate_total_snoc,half_24_01_total10]
  norm_num

private theorem half_24_01_bounds11 : ∀ l,0≤half_24_01_φ11 l ∧ half_24_01_φ11 l≤1 ∧
    0≤shiftExponents 16 half_24_01_φ11 l :=
  alternate_bounds_snoc half_24_01_φ10 (141761723/10000000000 : ℝ) half_24_01_bounds10 (by norm_num)

private theorem half_24_01_prefix : PrefixCondition 16 half_24_01_φ11 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_24_01_φ1, half_24_01_φ2, half_24_01_φ3, half_24_01_φ4, half_24_01_φ5, half_24_01_φ6, half_24_01_φ7, half_24_01_φ8, half_24_01_φ9, half_24_01_φ10, half_24_01_φ11, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_24_01_hF2 : SourcePowerBound
    (paddedMoment 16 0 2 2048 half_24_01_φ11) (25228114963/2000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 16) (j := 11) (r := 0) (n := 1) (D := 2048)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_24_01_φ11
    (fun i => (half_24_01_bounds11 i).1) (fun i => (half_24_01_bounds11 i).2.1)
    (fun i => (half_24_01_bounds11 i).2.2) half_24_01_prefix
  convert h using 1 <;> norm_num [half_24_01_total1, half_24_01_total2, half_24_01_total3, half_24_01_total4, half_24_01_total5, half_24_01_total6, half_24_01_total7, half_24_01_total8, half_24_01_total9, half_24_01_total10, half_24_01_total11, parameterExponent, curveLoss, dyadicExponent]

private theorem half_24_01_hF1 : SourcePowerBound
    (paddedMoment 16 0 1 2048 half_24_01_φ11) (9076038321/2000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 16) (j := 11) (r := 0) (n := 0) (D := 2048)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_24_01_φ11
    (fun i => (half_24_01_bounds11 i).1) (fun i => (half_24_01_bounds11 i).2.1)
    (fun i => (half_24_01_bounds11 i).2.2) half_24_01_prefix
  convert h using 1 <;> norm_num [half_24_01_total1, half_24_01_total2, half_24_01_total3, half_24_01_total4, half_24_01_total5, half_24_01_total6, half_24_01_total7, half_24_01_total8, half_24_01_total9, half_24_01_total10, half_24_01_total11, parameterExponent, curveLoss, dyadicExponent]

private theorem half_24_01_hx11 : SourcePowerBound
    (powerBoxCross 16 13 2048 half_24_01_φ11) (116103732121/10000000000 : ℝ) := by
  have h := full_B_cross_power (k := 16) (s := 13) (r := 1) (v := 2) (t := 20) (D := 2048)
    (a := (1/5 : ℝ)) (b := (3/20 : ℝ)) (c := (13/20 : ℝ))
    (by norm_num) half_24_01_φ11 (by norm_num [half_24_01_total1, half_24_01_total2, half_24_01_total3, half_24_01_total4, half_24_01_total5, half_24_01_total6, half_24_01_total7, half_24_01_total8, half_24_01_total9, half_24_01_total10, half_24_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_24_01_total1, half_24_01_total2, half_24_01_total3, half_24_01_total4, half_24_01_total5, half_24_01_total6, half_24_01_total7, half_24_01_total8, half_24_01_total9, half_24_01_total10, half_24_01_total11, parameterExponent, curveLoss, dyadicExponent]) half_24_01_hF1 half_24_01_hF2
    (half_20_01)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_24_01_total1, half_24_01_total2, half_24_01_total3, half_24_01_total4, half_24_01_total5, half_24_01_total6, half_24_01_total7, half_24_01_total8, half_24_01_total9, half_24_01_total10, half_24_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_24_01_hx10 : SourcePowerBound
    (powerBoxCross 16 14 1024 half_24_01_φ10) (30446531357/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 10) (s := 14) (u := 12) (t := 15)
    (D := 1024) (ψ := (141761723/10000000000 : ℝ)) half_24_01_φ10
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_24_01_bounds10 l).1) (fun l => (half_24_01_bounds10 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_24_01_total1, half_24_01_total2, half_24_01_total3, half_24_01_total4, half_24_01_total5, half_24_01_total6, half_24_01_total7, half_24_01_total8, half_24_01_total9, half_24_01_total10, half_24_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher16SimpleSeeds.degree16_half_13) (half_15_01)
    (by simpa only [half_24_01_φ11, show (2:ℝ)*1024=2048 by norm_num] using half_24_01_hx11)
  exact h.weaken (by norm_num [half_24_01_total1, half_24_01_total2, half_24_01_total3, half_24_01_total4, half_24_01_total5, half_24_01_total6, half_24_01_total7, half_24_01_total8, half_24_01_total9, half_24_01_total10, half_24_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_24_01_hx9 : SourcePowerBound
    (powerBoxCross 16 15 512 half_24_01_φ9) (133492891999/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 9) (s := 15) (u := 13) (t := 16)
    (D := 512) (ψ := (36907913/1000000000 : ℝ)) half_24_01_φ9
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_24_01_bounds9 l).1) (fun l => (half_24_01_bounds9 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_24_01_total1, half_24_01_total2, half_24_01_total3, half_24_01_total4, half_24_01_total5, half_24_01_total6, half_24_01_total7, half_24_01_total8, half_24_01_total9, half_24_01_total10, half_24_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher16SimpleSeeds.degree16_half_14) (half_16_01)
    (by simpa only [half_24_01_φ10, show (2:ℝ)*512=1024 by norm_num] using half_24_01_hx10)
  exact h.weaken (by norm_num [half_24_01_total1, half_24_01_total2, half_24_01_total3, half_24_01_total4, half_24_01_total5, half_24_01_total6, half_24_01_total7, half_24_01_total8, half_24_01_total9, half_24_01_total10, half_24_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_24_01_hx8 : SourcePowerBound
    (powerBoxCross 16 16 256 half_24_01_φ8) (146920268843/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 8) (s := 16) (u := 14) (t := 17)
    (D := 256) (ψ := (15817677/400000000 : ℝ)) half_24_01_φ8
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_24_01_bounds8 l).1) (fun l => (half_24_01_bounds8 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_24_01_total1, half_24_01_total2, half_24_01_total3, half_24_01_total4, half_24_01_total5, half_24_01_total6, half_24_01_total7, half_24_01_total8, half_24_01_total9, half_24_01_total10, half_24_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_15_01) (half_17_01)
    (by simpa only [half_24_01_φ9, show (2:ℝ)*256=512 by norm_num] using half_24_01_hx9)
  exact h.weaken (by norm_num [half_24_01_total1, half_24_01_total2, half_24_01_total3, half_24_01_total4, half_24_01_total5, half_24_01_total6, half_24_01_total7, half_24_01_total8, half_24_01_total9, half_24_01_total10, half_24_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_24_01_hx7 : SourcePowerBound
    (powerBoxCross 16 17 128 half_24_01_φ7) (162573265347/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 7) (s := 17) (u := 15) (t := 18)
    (D := 128) (ψ := (423687777/10000000000 : ℝ)) half_24_01_φ7
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_24_01_bounds7 l).1) (fun l => (half_24_01_bounds7 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_24_01_total1, half_24_01_total2, half_24_01_total3, half_24_01_total4, half_24_01_total5, half_24_01_total6, half_24_01_total7, half_24_01_total8, half_24_01_total9, half_24_01_total10, half_24_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_16_01) (half_18_01)
    (by simpa only [half_24_01_φ8, show (2:ℝ)*128=256 by norm_num] using half_24_01_hx8)
  exact h.weaken (by norm_num [half_24_01_total1, half_24_01_total2, half_24_01_total3, half_24_01_total4, half_24_01_total5, half_24_01_total6, half_24_01_total7, half_24_01_total8, half_24_01_total9, half_24_01_total10, half_24_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_24_01_hx6 : SourcePowerBound
    (powerBoxCross 16 18 64 half_24_01_φ6) (7233407753/400000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 6) (s := 18) (u := 16) (t := 19)
    (D := 64) (ψ := (453951189/10000000000 : ℝ)) half_24_01_φ6
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_24_01_bounds6 l).1) (fun l => (half_24_01_bounds6 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_24_01_total1, half_24_01_total2, half_24_01_total3, half_24_01_total4, half_24_01_total5, half_24_01_total6, half_24_01_total7, half_24_01_total8, half_24_01_total9, half_24_01_total10, half_24_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_17_01) (half_19_01)
    (by simpa only [half_24_01_φ7, show (2:ℝ)*64=128 by norm_num] using half_24_01_hx7)
  exact h.weaken (by norm_num [half_24_01_total1, half_24_01_total2, half_24_01_total3, half_24_01_total4, half_24_01_total5, half_24_01_total6, half_24_01_total7, half_24_01_total8, half_24_01_total9, half_24_01_total10, half_24_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_24_01_hx5 : SourcePowerBound
    (powerBoxCross 16 19 32 half_24_01_φ5) (202039192819/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 5) (s := 19) (u := 17) (t := 20)
    (D := 32) (ψ := (243188137/5000000000 : ℝ)) half_24_01_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_24_01_bounds5 l).1) (fun l => (half_24_01_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_24_01_total1, half_24_01_total2, half_24_01_total3, half_24_01_total4, half_24_01_total5, half_24_01_total6, half_24_01_total7, half_24_01_total8, half_24_01_total9, half_24_01_total10, half_24_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_18_01) (half_20_01)
    (by simpa only [half_24_01_φ6, show (2:ℝ)*32=64 by norm_num] using half_24_01_hx6)
  exact h.weaken (by norm_num [half_24_01_total1, half_24_01_total2, half_24_01_total3, half_24_01_total4, half_24_01_total5, half_24_01_total6, half_24_01_total7, half_24_01_total8, half_24_01_total9, half_24_01_total10, half_24_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_24_01_hx4 : SourcePowerBound
    (powerBoxCross 16 20 16 half_24_01_φ4) (113252977599/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 4) (s := 20) (u := 18) (t := 21)
    (D := 16) (ψ := (521117437/10000000000 : ℝ)) half_24_01_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_24_01_bounds4 l).1) (fun l => (half_24_01_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_24_01_total1, half_24_01_total2, half_24_01_total3, half_24_01_total4, half_24_01_total5, half_24_01_total6, half_24_01_total7, half_24_01_total8, half_24_01_total9, half_24_01_total10, half_24_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_19_01) (half_21_01)
    (by simpa only [half_24_01_φ5, show (2:ℝ)*16=32 by norm_num] using half_24_01_hx5)
  exact h.weaken (by norm_num [half_24_01_total1, half_24_01_total2, half_24_01_total3, half_24_01_total4, half_24_01_total5, half_24_01_total6, half_24_01_total7, half_24_01_total8, half_24_01_total9, half_24_01_total10, half_24_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_24_01_hx3 : SourcePowerBound
    (powerBoxCross 16 21 8 half_24_01_φ3) (253193550857/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 21) (u := 19) (t := 22)
    (D := 8) (ψ := (525817141/10000000000 : ℝ)) half_24_01_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_24_01_bounds3 l).1) (fun l => (half_24_01_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_24_01_total1, half_24_01_total2, half_24_01_total3, half_24_01_total4, half_24_01_total5, half_24_01_total6, half_24_01_total7, half_24_01_total8, half_24_01_total9, half_24_01_total10, half_24_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_20_01) (half_22_01)
    (by simpa only [half_24_01_φ4, show (2:ℝ)*8=16 by norm_num] using half_24_01_hx4)
  exact h.weaken (by norm_num [half_24_01_total1, half_24_01_total2, half_24_01_total3, half_24_01_total4, half_24_01_total5, half_24_01_total6, half_24_01_total7, half_24_01_total8, half_24_01_total9, half_24_01_total10, half_24_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_24_01_hx2 : SourcePowerBound
    (powerBoxCross 16 22 4 half_24_01_φ2) (56442930851/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 22) (u := 20) (t := 23)
    (D := 4) (ψ := (532332319/10000000000 : ℝ)) half_24_01_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_24_01_bounds2 l).1) (fun l => (half_24_01_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_24_01_total1, half_24_01_total2, half_24_01_total3, half_24_01_total4, half_24_01_total5, half_24_01_total6, half_24_01_total7, half_24_01_total8, half_24_01_total9, half_24_01_total10, half_24_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_21_01) (half_23_01)
    (by simpa only [half_24_01_φ3, show (2:ℝ)*4=8 by norm_num] using half_24_01_hx3)
  exact h.weaken (by norm_num [half_24_01_total1, half_24_01_total2, half_24_01_total3, half_24_01_total4, half_24_01_total5, half_24_01_total6, half_24_01_total7, half_24_01_total8, half_24_01_total9, half_24_01_total10, half_24_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_24_01_hx1 : SourcePowerBound
    (powerBoxCross 16 23 2 half_24_01_φ1) (78569220893/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 23) (u := 21) (t := 24)
    (D := 2) (ψ := (4215259/78125000 : ℝ)) half_24_01_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_24_01_bounds1 l).1) (fun l => (half_24_01_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_24_01_total1, half_24_01_total2, half_24_01_total3, half_24_01_total4, half_24_01_total5, half_24_01_total6, half_24_01_total7, half_24_01_total8, half_24_01_total9, half_24_01_total10, half_24_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_22_01) (chord_53)
    (by simpa only [half_24_01_φ2, show (2:ℝ)*2=4 by norm_num] using half_24_01_hx2)
  exact h.weaken (by norm_num [half_24_01_total1, half_24_01_total2, half_24_01_total3, half_24_01_total4, half_24_01_total5, half_24_01_total6, half_24_01_total7, half_24_01_total8, half_24_01_total9, half_24_01_total10, half_24_01_total11, parameterExponent, curveLoss, dyadicExponent])

theorem half_24_01 : AdmissibleExponent 16 48 (170312997871/5000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 22) (ψ := (292767913/5000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_23_01)
    (by simpa only [half_24_01_φ1] using half_24_01_hx1)
  exact admissibleExponent_mono h (by norm_num [half_24_01_total1, half_24_01_total2, half_24_01_total3, half_24_01_total4, half_24_01_total5, half_24_01_total6, half_24_01_total7, half_24_01_total8, half_24_01_total9, half_24_01_total10, half_24_01_total11, parameterExponent, curveLoss, dyadicExponent])

theorem chord_59 : AdmissibleExponent 16 50 (720418796001/20000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 50) (t := (5/6 : ℝ))
    (half_24_01) (half_30_00)
    (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private def half_25_01_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (592474431/10000000000 : ℝ)

private theorem half_25_01_total1 : total half_25_01_φ1=(592474431/10000000000 : ℝ) := by
  norm_num [half_25_01_φ1,total,emptyPhi,Fin.snoc]

private theorem half_25_01_bounds1 : ∀ l,0≤half_25_01_φ1 l ∧ half_25_01_φ1 l≤1 ∧
    0≤shiftExponents 16 half_25_01_φ1 l :=
  alternate_bounds_snoc emptyPhi (592474431/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_25_01_φ2 : Fin 2 → ℝ := Fin.snoc half_25_01_φ1 (136684517/2500000000 : ℝ)

private theorem half_25_01_total2 : total half_25_01_φ2=(1139212499/10000000000 : ℝ) := by
  change total (Fin.snoc half_25_01_φ1 (136684517/2500000000 : ℝ))=(1139212499/10000000000 : ℝ)
  rw [alternate_total_snoc,half_25_01_total1]
  norm_num

private theorem half_25_01_bounds2 : ∀ l,0≤half_25_01_φ2 l ∧ half_25_01_φ2 l≤1 ∧
    0≤shiftExponents 16 half_25_01_φ2 l :=
  alternate_bounds_snoc half_25_01_φ1 (136684517/2500000000 : ℝ) half_25_01_bounds1 (by norm_num)

private def half_25_01_φ3 : Fin 3 → ℝ := Fin.snoc half_25_01_φ2 (540323983/10000000000 : ℝ)

private theorem half_25_01_total3 : total half_25_01_φ3=(839768241/5000000000 : ℝ) := by
  change total (Fin.snoc half_25_01_φ2 (540323983/10000000000 : ℝ))=(839768241/5000000000 : ℝ)
  rw [alternate_total_snoc,half_25_01_total2]
  norm_num

private theorem half_25_01_bounds3 : ∀ l,0≤half_25_01_φ3 l ∧ half_25_01_φ3 l≤1 ∧
    0≤shiftExponents 16 half_25_01_φ3 l :=
  alternate_bounds_snoc half_25_01_φ2 (540323983/10000000000 : ℝ) half_25_01_bounds2 (by norm_num)

private def half_25_01_φ4 : Fin 4 → ℝ := Fin.snoc half_25_01_φ3 (535093403/10000000000 : ℝ)

private theorem half_25_01_total4 : total half_25_01_φ4=(442925977/2000000000 : ℝ) := by
  change total (Fin.snoc half_25_01_φ3 (535093403/10000000000 : ℝ))=(442925977/2000000000 : ℝ)
  rw [alternate_total_snoc,half_25_01_total3]
  norm_num

private theorem half_25_01_bounds4 : ∀ l,0≤half_25_01_φ4 l ∧ half_25_01_φ4 l≤1 ∧
    0≤shiftExponents 16 half_25_01_φ4 l :=
  alternate_bounds_snoc half_25_01_φ3 (535093403/10000000000 : ℝ) half_25_01_bounds3 (by norm_num)

private def half_25_01_φ5 : Fin 5 → ℝ := Fin.snoc half_25_01_φ4 (259512337/5000000000 : ℝ)

private theorem half_25_01_total5 : total half_25_01_φ5=(2733654559/10000000000 : ℝ) := by
  change total (Fin.snoc half_25_01_φ4 (259512337/5000000000 : ℝ))=(2733654559/10000000000 : ℝ)
  rw [alternate_total_snoc,half_25_01_total4]
  norm_num

private theorem half_25_01_bounds5 : ∀ l,0≤half_25_01_φ5 l ∧ half_25_01_φ5 l≤1 ∧
    0≤shiftExponents 16 half_25_01_φ5 l :=
  alternate_bounds_snoc half_25_01_φ4 (259512337/5000000000 : ℝ) half_25_01_bounds4 (by norm_num)

private def half_25_01_φ6 : Fin 6 → ℝ := Fin.snoc half_25_01_φ5 (484423029/10000000000 : ℝ)

private theorem half_25_01_total6 : total half_25_01_φ6=(804519397/2500000000 : ℝ) := by
  change total (Fin.snoc half_25_01_φ5 (484423029/10000000000 : ℝ))=(804519397/2500000000 : ℝ)
  rw [alternate_total_snoc,half_25_01_total5]
  norm_num

private theorem half_25_01_bounds6 : ∀ l,0≤half_25_01_φ6 l ∧ half_25_01_φ6 l≤1 ∧
    0≤shiftExponents 16 half_25_01_φ6 l :=
  alternate_bounds_snoc half_25_01_φ5 (484423029/10000000000 : ℝ) half_25_01_bounds5 (by norm_num)

private def half_25_01_φ7 : Fin 7 → ℝ := Fin.snoc half_25_01_φ6 (2825801/62500000 : ℝ)

private theorem half_25_01_total7 : total half_25_01_φ7=(917551437/2500000000 : ℝ) := by
  change total (Fin.snoc half_25_01_φ6 (2825801/62500000 : ℝ))=(917551437/2500000000 : ℝ)
  rw [alternate_total_snoc,half_25_01_total6]
  norm_num

private theorem half_25_01_bounds7 : ∀ l,0≤half_25_01_φ7 l ∧ half_25_01_φ7 l≤1 ∧
    0≤shiftExponents 16 half_25_01_φ7 l :=
  alternate_bounds_snoc half_25_01_φ6 (2825801/62500000 : ℝ) half_25_01_bounds6 (by norm_num)

private def half_25_01_φ8 : Fin 8 → ℝ := Fin.snoc half_25_01_φ7 (421986283/10000000000 : ℝ)

private theorem half_25_01_total8 : total half_25_01_φ8=(4092192031/10000000000 : ℝ) := by
  change total (Fin.snoc half_25_01_φ7 (421986283/10000000000 : ℝ))=(4092192031/10000000000 : ℝ)
  rw [alternate_total_snoc,half_25_01_total7]
  norm_num

private theorem half_25_01_bounds8 : ∀ l,0≤half_25_01_φ8 l ∧ half_25_01_φ8 l≤1 ∧
    0≤shiftExponents 16 half_25_01_φ8 l :=
  alternate_bounds_snoc half_25_01_φ7 (421986283/10000000000 : ℝ) half_25_01_bounds7 (by norm_num)

private def half_25_01_φ9 : Fin 9 → ℝ := Fin.snoc half_25_01_φ8 (49231733/1250000000 : ℝ)

private theorem half_25_01_total9 : total half_25_01_φ9=(897209179/2000000000 : ℝ) := by
  change total (Fin.snoc half_25_01_φ8 (49231733/1250000000 : ℝ))=(897209179/2000000000 : ℝ)
  rw [alternate_total_snoc,half_25_01_total8]
  norm_num

private theorem half_25_01_bounds9 : ∀ l,0≤half_25_01_φ9 l ∧ half_25_01_φ9 l≤1 ∧
    0≤shiftExponents 16 half_25_01_φ9 l :=
  alternate_bounds_snoc half_25_01_φ8 (49231733/1250000000 : ℝ) half_25_01_bounds8 (by norm_num)

private def half_25_01_φ10 : Fin 10 → ℝ := Fin.snoc half_25_01_φ9 (18379847/500000000 : ℝ)

private theorem half_25_01_total10 : total half_25_01_φ10=(970728567/2000000000 : ℝ) := by
  change total (Fin.snoc half_25_01_φ9 (18379847/500000000 : ℝ))=(970728567/2000000000 : ℝ)
  rw [alternate_total_snoc,half_25_01_total9]
  norm_num

private theorem half_25_01_bounds10 : ∀ l,0≤half_25_01_φ10 l ∧ half_25_01_φ10 l≤1 ∧
    0≤shiftExponents 16 half_25_01_φ10 l :=
  alternate_bounds_snoc half_25_01_φ9 (18379847/500000000 : ℝ) half_25_01_bounds9 (by norm_num)

private def half_25_01_φ11 : Fin 11 → ℝ := Fin.snoc half_25_01_φ10 (114961243/5000000000 : ℝ)

private theorem half_25_01_total11 : total half_25_01_φ11=(5083565321/10000000000 : ℝ) := by
  change total (Fin.snoc half_25_01_φ10 (114961243/5000000000 : ℝ))=(5083565321/10000000000 : ℝ)
  rw [alternate_total_snoc,half_25_01_total10]
  norm_num

private theorem half_25_01_bounds11 : ∀ l,0≤half_25_01_φ11 l ∧ half_25_01_φ11 l≤1 ∧
    0≤shiftExponents 16 half_25_01_φ11 l :=
  alternate_bounds_snoc half_25_01_φ10 (114961243/5000000000 : ℝ) half_25_01_bounds10 (by norm_num)

private theorem half_25_01_prefix : PrefixCondition 16 half_25_01_φ11 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_25_01_φ1, half_25_01_φ2, half_25_01_φ3, half_25_01_φ4, half_25_01_φ5, half_25_01_φ6, half_25_01_φ7, half_25_01_φ8, half_25_01_φ9, half_25_01_φ10, half_25_01_φ11, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_25_01_hF2 : SourcePowerBound
    (paddedMoment 16 0 2 2048 half_25_01_φ11) (24247912111/2000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 16) (j := 11) (r := 0) (n := 1) (D := 2048)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_25_01_φ11
    (fun i => (half_25_01_bounds11 i).1) (fun i => (half_25_01_bounds11 i).2.1)
    (fun i => (half_25_01_bounds11 i).2.2) half_25_01_prefix
  convert h using 1 <;> norm_num [half_25_01_total1, half_25_01_total2, half_25_01_total3, half_25_01_total4, half_25_01_total5, half_25_01_total6, half_25_01_total7, half_25_01_total8, half_25_01_total9, half_25_01_total10, half_25_01_total11, parameterExponent, curveLoss, dyadicExponent]

private theorem half_25_01_hF1 : SourcePowerBound
    (paddedMoment 16 0 1 2048 half_25_01_φ11) (8749304037/2000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 16) (j := 11) (r := 0) (n := 0) (D := 2048)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_25_01_φ11
    (fun i => (half_25_01_bounds11 i).1) (fun i => (half_25_01_bounds11 i).2.1)
    (fun i => (half_25_01_bounds11 i).2.2) half_25_01_prefix
  convert h using 1 <;> norm_num [half_25_01_total1, half_25_01_total2, half_25_01_total3, half_25_01_total4, half_25_01_total5, half_25_01_total6, half_25_01_total7, half_25_01_total8, half_25_01_total9, half_25_01_total10, half_25_01_total11, parameterExponent, curveLoss, dyadicExponent]

private theorem half_25_01_hx11 : SourcePowerBound
    (powerBoxCross 16 14 2048 half_25_01_φ11) (24290047201/2000000000 : ℝ) := by
  have h := full_B_cross_power (k := 16) (s := 14) (r := 1) (v := 2) (t := 20) (D := 2048)
    (a := (1/10 : ℝ)) (b := (1/5 : ℝ)) (c := (7/10 : ℝ))
    (by norm_num) half_25_01_φ11 (by norm_num [half_25_01_total1, half_25_01_total2, half_25_01_total3, half_25_01_total4, half_25_01_total5, half_25_01_total6, half_25_01_total7, half_25_01_total8, half_25_01_total9, half_25_01_total10, half_25_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_25_01_total1, half_25_01_total2, half_25_01_total3, half_25_01_total4, half_25_01_total5, half_25_01_total6, half_25_01_total7, half_25_01_total8, half_25_01_total9, half_25_01_total10, half_25_01_total11, parameterExponent, curveLoss, dyadicExponent]) half_25_01_hF1 half_25_01_hF2
    (half_20_01)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_25_01_total1, half_25_01_total2, half_25_01_total3, half_25_01_total4, half_25_01_total5, half_25_01_total6, half_25_01_total7, half_25_01_total8, half_25_01_total9, half_25_01_total10, half_25_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_25_01_hx10 : SourcePowerBound
    (powerBoxCross 16 15 1024 half_25_01_φ10) (1619657843/125000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 10) (s := 15) (u := 13) (t := 16)
    (D := 1024) (ψ := (114961243/5000000000 : ℝ)) half_25_01_φ10
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_25_01_bounds10 l).1) (fun l => (half_25_01_bounds10 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_25_01_total1, half_25_01_total2, half_25_01_total3, half_25_01_total4, half_25_01_total5, half_25_01_total6, half_25_01_total7, half_25_01_total8, half_25_01_total9, half_25_01_total10, half_25_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher16SimpleSeeds.degree16_half_14) (half_16_01)
    (by simpa only [half_25_01_φ11, show (2:ℝ)*1024=2048 by norm_num] using half_25_01_hx11)
  exact h.weaken (by norm_num [half_25_01_total1, half_25_01_total2, half_25_01_total3, half_25_01_total4, half_25_01_total5, half_25_01_total6, half_25_01_total7, half_25_01_total8, half_25_01_total9, half_25_01_total10, half_25_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_25_01_hx9 : SourcePowerBound
    (powerBoxCross 16 16 512 half_25_01_φ9) (28370037737/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 9) (s := 16) (u := 14) (t := 17)
    (D := 512) (ψ := (18379847/500000000 : ℝ)) half_25_01_φ9
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_25_01_bounds9 l).1) (fun l => (half_25_01_bounds9 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_25_01_total1, half_25_01_total2, half_25_01_total3, half_25_01_total4, half_25_01_total5, half_25_01_total6, half_25_01_total7, half_25_01_total8, half_25_01_total9, half_25_01_total10, half_25_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_15_01) (half_17_01)
    (by simpa only [half_25_01_φ10, show (2:ℝ)*512=1024 by norm_num] using half_25_01_hx10)
  exact h.weaken (by norm_num [half_25_01_total1, half_25_01_total2, half_25_01_total3, half_25_01_total4, half_25_01_total5, half_25_01_total6, half_25_01_total7, half_25_01_total8, half_25_01_total9, half_25_01_total10, half_25_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_25_01_hx8 : SourcePowerBound
    (powerBoxCross 16 17 256 half_25_01_φ8) (121833393/7812500 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 8) (s := 17) (u := 15) (t := 18)
    (D := 256) (ψ := (49231733/1250000000 : ℝ)) half_25_01_φ8
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_25_01_bounds8 l).1) (fun l => (half_25_01_bounds8 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_25_01_total1, half_25_01_total2, half_25_01_total3, half_25_01_total4, half_25_01_total5, half_25_01_total6, half_25_01_total7, half_25_01_total8, half_25_01_total9, half_25_01_total10, half_25_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_16_01) (half_18_01)
    (by simpa only [half_25_01_φ9, show (2:ℝ)*256=512 by norm_num] using half_25_01_hx9)
  exact h.weaken (by norm_num [half_25_01_total1, half_25_01_total2, half_25_01_total3, half_25_01_total4, half_25_01_total5, half_25_01_total6, half_25_01_total7, half_25_01_total8, half_25_01_total9, half_25_01_total10, half_25_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_25_01_hx7 : SourcePowerBound
    (powerBoxCross 16 18 128 half_25_01_φ7) (86171783453/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 7) (s := 18) (u := 16) (t := 19)
    (D := 128) (ψ := (421986283/10000000000 : ℝ)) half_25_01_φ7
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_25_01_bounds7 l).1) (fun l => (half_25_01_bounds7 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_25_01_total1, half_25_01_total2, half_25_01_total3, half_25_01_total4, half_25_01_total5, half_25_01_total6, half_25_01_total7, half_25_01_total8, half_25_01_total9, half_25_01_total10, half_25_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_17_01) (half_19_01)
    (by simpa only [half_25_01_φ8, show (2:ℝ)*128=256 by norm_num] using half_25_01_hx8)
  exact h.weaken (by norm_num [half_25_01_total1, half_25_01_total2, half_25_01_total3, half_25_01_total4, half_25_01_total5, half_25_01_total6, half_25_01_total7, half_25_01_total8, half_25_01_total9, half_25_01_total10, half_25_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_25_01_hx6 : SourcePowerBound
    (powerBoxCross 16 19 64 half_25_01_φ6) (191412818347/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 6) (s := 19) (u := 17) (t := 20)
    (D := 64) (ψ := (2825801/62500000 : ℝ)) half_25_01_φ6
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_25_01_bounds6 l).1) (fun l => (half_25_01_bounds6 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_25_01_total1, half_25_01_total2, half_25_01_total3, half_25_01_total4, half_25_01_total5, half_25_01_total6, half_25_01_total7, half_25_01_total8, half_25_01_total9, half_25_01_total10, half_25_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_18_01) (half_20_01)
    (by simpa only [half_25_01_φ7, show (2:ℝ)*64=128 by norm_num] using half_25_01_hx7)
  exact h.weaken (by norm_num [half_25_01_total1, half_25_01_total2, half_25_01_total3, half_25_01_total4, half_25_01_total5, half_25_01_total6, half_25_01_total7, half_25_01_total8, half_25_01_total9, half_25_01_total10, half_25_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_25_01_hx5 : SourcePowerBound
    (powerBoxCross 16 20 32 half_25_01_φ5) (26685480929/1250000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 5) (s := 20) (u := 18) (t := 21)
    (D := 32) (ψ := (484423029/10000000000 : ℝ)) half_25_01_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_25_01_bounds5 l).1) (fun l => (half_25_01_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_25_01_total1, half_25_01_total2, half_25_01_total3, half_25_01_total4, half_25_01_total5, half_25_01_total6, half_25_01_total7, half_25_01_total8, half_25_01_total9, half_25_01_total10, half_25_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_19_01) (half_21_01)
    (by simpa only [half_25_01_φ6, show (2:ℝ)*32=64 by norm_num] using half_25_01_hx6)
  exact h.weaken (by norm_num [half_25_01_total1, half_25_01_total2, half_25_01_total3, half_25_01_total4, half_25_01_total5, half_25_01_total6, half_25_01_total7, half_25_01_total8, half_25_01_total9, half_25_01_total10, half_25_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_25_01_hx4 : SourcePowerBound
    (powerBoxCross 16 21 16 half_25_01_φ4) (119440331747/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 4) (s := 21) (u := 19) (t := 22)
    (D := 16) (ψ := (259512337/5000000000 : ℝ)) half_25_01_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_25_01_bounds4 l).1) (fun l => (half_25_01_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_25_01_total1, half_25_01_total2, half_25_01_total3, half_25_01_total4, half_25_01_total5, half_25_01_total6, half_25_01_total7, half_25_01_total8, half_25_01_total9, half_25_01_total10, half_25_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_20_01) (half_22_01)
    (by simpa only [half_25_01_φ5, show (2:ℝ)*16=32 by norm_num] using half_25_01_hx5)
  exact h.weaken (by norm_num [half_25_01_total1, half_25_01_total2, half_25_01_total3, half_25_01_total4, half_25_01_total5, half_25_01_total6, half_25_01_total7, half_25_01_total8, half_25_01_total9, half_25_01_total10, half_25_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_25_01_hx3 : SourcePowerBound
    (powerBoxCross 16 22 8 half_25_01_φ3) (267013785609/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 22) (u := 20) (t := 23)
    (D := 8) (ψ := (535093403/10000000000 : ℝ)) half_25_01_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_25_01_bounds3 l).1) (fun l => (half_25_01_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_25_01_total1, half_25_01_total2, half_25_01_total3, half_25_01_total4, half_25_01_total5, half_25_01_total6, half_25_01_total7, half_25_01_total8, half_25_01_total9, half_25_01_total10, half_25_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_21_01) (half_23_01)
    (by simpa only [half_25_01_φ4, show (2:ℝ)*8=16 by norm_num] using half_25_01_hx4)
  exact h.weaken (by norm_num [half_25_01_total1, half_25_01_total2, half_25_01_total3, half_25_01_total4, half_25_01_total5, half_25_01_total6, half_25_01_total7, half_25_01_total8, half_25_01_total9, half_25_01_total10, half_25_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_25_01_hx2 : SourcePowerBound
    (powerBoxCross 16 23 4 half_25_01_φ2) (18593155811/625000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 23) (u := 21) (t := 24)
    (D := 4) (ψ := (540323983/10000000000 : ℝ)) half_25_01_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_25_01_bounds2 l).1) (fun l => (half_25_01_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_25_01_total1, half_25_01_total2, half_25_01_total3, half_25_01_total4, half_25_01_total5, half_25_01_total6, half_25_01_total7, half_25_01_total8, half_25_01_total9, half_25_01_total10, half_25_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_22_01) (half_24_01)
    (by simpa only [half_25_01_φ3, show (2:ℝ)*4=8 by norm_num] using half_25_01_hx3)
  exact h.weaken (by norm_num [half_25_01_total1, half_25_01_total2, half_25_01_total3, half_25_01_total4, half_25_01_total5, half_25_01_total6, half_25_01_total7, half_25_01_total8, half_25_01_total9, half_25_01_total10, half_25_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_25_01_hx1 : SourcePowerBound
    (powerBoxCross 16 24 2 half_25_01_φ1) (1034491409/31250000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 24) (u := 22) (t := 25)
    (D := 2) (ψ := (136684517/2500000000 : ℝ)) half_25_01_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_25_01_bounds1 l).1) (fun l => (half_25_01_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_25_01_total1, half_25_01_total2, half_25_01_total3, half_25_01_total4, half_25_01_total5, half_25_01_total6, half_25_01_total7, half_25_01_total8, half_25_01_total9, half_25_01_total10, half_25_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_23_01) (chord_59)
    (by simpa only [half_25_01_φ2, show (2:ℝ)*2=4 by norm_num] using half_25_01_hx2)
  exact h.weaken (by norm_num [half_25_01_total1, half_25_01_total2, half_25_01_total3, half_25_01_total4, half_25_01_total5, half_25_01_total6, half_25_01_total7, half_25_01_total8, half_25_01_total9, half_25_01_total10, half_25_01_total11, parameterExponent, curveLoss, dyadicExponent])

theorem half_25_01 : AdmissibleExponent 16 50 (358883549137/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 23) (ψ := (592474431/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_24_01)
    (by simpa only [half_25_01_φ1] using half_25_01_hx1)
  exact admissibleExponent_mono h (by norm_num [half_25_01_total1, half_25_01_total2, half_25_01_total3, half_25_01_total4, half_25_01_total5, half_25_01_total6, half_25_01_total7, half_25_01_total8, half_25_01_total9, half_25_01_total10, half_25_01_total11, parameterExponent, curveLoss, dyadicExponent])

theorem chord_64 : AdmissibleExponent 16 52 (1893660605841/50000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 52) (t := (4/5 : ℝ))
    (half_25_01) (half_30_00)
    (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private def half_26_01_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (600344417/10000000000 : ℝ)

private theorem half_26_01_total1 : total half_26_01_φ1=(600344417/10000000000 : ℝ) := by
  norm_num [half_26_01_φ1,total,emptyPhi,Fin.snoc]

private theorem half_26_01_bounds1 : ∀ l,0≤half_26_01_φ1 l ∧ half_26_01_φ1 l≤1 ∧
    0≤shiftExponents 16 half_26_01_φ1 l :=
  alternate_bounds_snoc emptyPhi (600344417/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_26_01_φ2 : Fin 2 → ℝ := Fin.snoc half_26_01_φ1 (69197971/1250000000 : ℝ)

private theorem half_26_01_total2 : total half_26_01_φ2=(230785637/2000000000 : ℝ) := by
  change total (Fin.snoc half_26_01_φ1 (69197971/1250000000 : ℝ))=(230785637/2000000000 : ℝ)
  rw [alternate_total_snoc,half_26_01_total1]
  norm_num

private theorem half_26_01_bounds2 : ∀ l,0≤half_26_01_φ2 l ∧ half_26_01_φ2 l≤1 ∧
    0≤shiftExponents 16 half_26_01_φ2 l :=
  alternate_bounds_snoc half_26_01_φ1 (69197971/1250000000 : ℝ) half_26_01_bounds1 (by norm_num)

private def half_26_01_φ3 : Fin 3 → ℝ := Fin.snoc half_26_01_φ2 (547803877/10000000000 : ℝ)

private theorem half_26_01_total3 : total half_26_01_φ3=(850866031/5000000000 : ℝ) := by
  change total (Fin.snoc half_26_01_φ2 (547803877/10000000000 : ℝ))=(850866031/5000000000 : ℝ)
  rw [alternate_total_snoc,half_26_01_total2]
  norm_num

private theorem half_26_01_bounds3 : ∀ l,0≤half_26_01_φ3 l ∧ half_26_01_φ3 l≤1 ∧
    0≤shiftExponents 16 half_26_01_φ3 l :=
  alternate_bounds_snoc half_26_01_φ2 (547803877/10000000000 : ℝ) half_26_01_bounds2 (by norm_num)

private def half_26_01_φ4 : Fin 4 → ℝ := Fin.snoc half_26_01_φ3 (543725377/10000000000 : ℝ)

private theorem half_26_01_total4 : total half_26_01_φ4=(2245457439/10000000000 : ℝ) := by
  change total (Fin.snoc half_26_01_φ3 (543725377/10000000000 : ℝ))=(2245457439/10000000000 : ℝ)
  rw [alternate_total_snoc,half_26_01_total3]
  norm_num

private theorem half_26_01_bounds4 : ∀ l,0≤half_26_01_φ4 l ∧ half_26_01_φ4 l≤1 ∧
    0≤shiftExponents 16 half_26_01_φ4 l :=
  alternate_bounds_snoc half_26_01_φ3 (543725377/10000000000 : ℝ) half_26_01_bounds3 (by norm_num)

private def half_26_01_φ5 : Fin 5 → ℝ := Fin.snoc half_26_01_φ4 (516969503/10000000000 : ℝ)

private theorem half_26_01_total5 : total half_26_01_φ5=(1381213471/5000000000 : ℝ) := by
  change total (Fin.snoc half_26_01_φ4 (516969503/10000000000 : ℝ))=(1381213471/5000000000 : ℝ)
  rw [alternate_total_snoc,half_26_01_total4]
  norm_num

private theorem half_26_01_bounds5 : ∀ l,0≤half_26_01_φ5 l ∧ half_26_01_φ5 l≤1 ∧
    0≤shiftExponents 16 half_26_01_φ5 l :=
  alternate_bounds_snoc half_26_01_φ4 (516969503/10000000000 : ℝ) half_26_01_bounds4 (by norm_num)

private def half_26_01_φ6 : Fin 6 → ℝ := Fin.snoc half_26_01_φ5 (48250487/1000000000 : ℝ)

private theorem half_26_01_total6 : total half_26_01_φ6=(811232953/2500000000 : ℝ) := by
  change total (Fin.snoc half_26_01_φ5 (48250487/1000000000 : ℝ))=(811232953/2500000000 : ℝ)
  rw [alternate_total_snoc,half_26_01_total5]
  norm_num

private theorem half_26_01_bounds6 : ∀ l,0≤half_26_01_φ6 l ∧ half_26_01_φ6 l≤1 ∧
    0≤shiftExponents 16 half_26_01_φ6 l :=
  alternate_bounds_snoc half_26_01_φ5 (48250487/1000000000 : ℝ) half_26_01_bounds5 (by norm_num)

private def half_26_01_φ7 : Fin 7 → ℝ := Fin.snoc half_26_01_φ6 (225168939/5000000000 : ℝ)

private theorem half_26_01_total7 : total half_26_01_φ7=(369526969/1000000000 : ℝ) := by
  change total (Fin.snoc half_26_01_φ6 (225168939/5000000000 : ℝ))=(369526969/1000000000 : ℝ)
  rw [alternate_total_snoc,half_26_01_total6]
  norm_num

private theorem half_26_01_bounds7 : ∀ l,0≤half_26_01_φ7 l ∧ half_26_01_φ7 l≤1 ∧
    0≤shiftExponents 16 half_26_01_φ7 l :=
  alternate_bounds_snoc half_26_01_φ6 (225168939/5000000000 : ℝ) half_26_01_bounds6 (by norm_num)

private def half_26_01_φ8 : Fin 8 → ℝ := Fin.snoc half_26_01_φ7 (420315353/10000000000 : ℝ)

private theorem half_26_01_total8 : total half_26_01_φ8=(4115585043/10000000000 : ℝ) := by
  change total (Fin.snoc half_26_01_φ7 (420315353/10000000000 : ℝ))=(4115585043/10000000000 : ℝ)
  rw [alternate_total_snoc,half_26_01_total7]
  norm_num

private theorem half_26_01_bounds8 : ∀ l,0≤half_26_01_φ8 l ∧ half_26_01_φ8 l≤1 ∧
    0≤shiftExponents 16 half_26_01_φ8 l :=
  alternate_bounds_snoc half_26_01_φ7 (420315353/10000000000 : ℝ) half_26_01_bounds7 (by norm_num)

private def half_26_01_φ9 : Fin 9 → ℝ := Fin.snoc half_26_01_φ8 (39229433/1000000000 : ℝ)

private theorem half_26_01_total9 : total half_26_01_φ9=(4507879373/10000000000 : ℝ) := by
  change total (Fin.snoc half_26_01_φ8 (39229433/1000000000 : ℝ))=(4507879373/10000000000 : ℝ)
  rw [alternate_total_snoc,half_26_01_total8]
  norm_num

private theorem half_26_01_bounds9 : ∀ l,0≤half_26_01_φ9 l ∧ half_26_01_φ9 l≤1 ∧
    0≤shiftExponents 16 half_26_01_φ9 l :=
  alternate_bounds_snoc half_26_01_φ8 (39229433/1000000000 : ℝ) half_26_01_bounds8 (by norm_num)

private def half_26_01_φ10 : Fin 10 → ℝ := Fin.snoc half_26_01_φ9 (183070687/5000000000 : ℝ)

private theorem half_26_01_total10 : total half_26_01_φ10=(4874020747/10000000000 : ℝ) := by
  change total (Fin.snoc half_26_01_φ9 (183070687/5000000000 : ℝ))=(4874020747/10000000000 : ℝ)
  rw [alternate_total_snoc,half_26_01_total9]
  norm_num

private theorem half_26_01_bounds10 : ∀ l,0≤half_26_01_φ10 l ∧ half_26_01_φ10 l≤1 ∧
    0≤shiftExponents 16 half_26_01_φ10 l :=
  alternate_bounds_snoc half_26_01_φ9 (183070687/5000000000 : ℝ) half_26_01_bounds9 (by norm_num)

private def half_26_01_φ11 : Fin 11 → ℝ := Fin.snoc half_26_01_φ10 (276735137/10000000000 : ℝ)

private theorem half_26_01_total11 : total half_26_01_φ11=(1287688971/2500000000 : ℝ) := by
  change total (Fin.snoc half_26_01_φ10 (276735137/10000000000 : ℝ))=(1287688971/2500000000 : ℝ)
  rw [alternate_total_snoc,half_26_01_total10]
  norm_num

private theorem half_26_01_bounds11 : ∀ l,0≤half_26_01_φ11 l ∧ half_26_01_φ11 l≤1 ∧
    0≤shiftExponents 16 half_26_01_φ11 l :=
  alternate_bounds_snoc half_26_01_φ10 (276735137/10000000000 : ℝ) half_26_01_bounds10 (by norm_num)

private theorem half_26_01_prefix : PrefixCondition 16 half_26_01_φ11 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_26_01_φ1, half_26_01_φ2, half_26_01_φ3, half_26_01_φ4, half_26_01_φ5, half_26_01_φ6, half_26_01_φ7, half_26_01_φ8, half_26_01_φ9, half_26_01_φ10, half_26_01_φ11, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_26_01_hF2 : SourcePowerBound
    (paddedMoment 16 0 2 2048 half_26_01_φ11) (5910799261/500000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 16) (j := 11) (r := 0) (n := 1) (D := 2048)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_26_01_φ11
    (fun i => (half_26_01_bounds11 i).1) (fun i => (half_26_01_bounds11 i).2.1)
    (fun i => (half_26_01_bounds11 i).2.2) half_26_01_prefix
  convert h using 1 <;> norm_num [half_26_01_total1, half_26_01_total2, half_26_01_total3, half_26_01_total4, half_26_01_total5, half_26_01_total6, half_26_01_total7, half_26_01_total8, half_26_01_total9, half_26_01_total10, half_26_01_total11, parameterExponent, curveLoss, dyadicExponent]

private theorem half_26_01_hx11 : SourcePowerBound
    (powerBoxCross 16 15 2048 half_26_01_φ11) (25530593643/2000000000 : ℝ) := by
  have h := full_A_cross_power (k := 16) (s := 15) (r := 2) (v := 0) (w := 20) (D := 2048)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_26_01_φ11 (by norm_num [half_26_01_total1, half_26_01_total2, half_26_01_total3, half_26_01_total4, half_26_01_total5, half_26_01_total6, half_26_01_total7, half_26_01_total8, half_26_01_total9, half_26_01_total10, half_26_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_26_01_total1, half_26_01_total2, half_26_01_total3, half_26_01_total4, half_26_01_total5, half_26_01_total6, half_26_01_total7, half_26_01_total8, half_26_01_total9, half_26_01_total10, half_26_01_total11, parameterExponent, curveLoss, dyadicExponent]) half_26_01_hF2
    (admissibleExponent_zero 16) (half_20_01)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_26_01_total1, half_26_01_total2, half_26_01_total3, half_26_01_total4, half_26_01_total5, half_26_01_total6, half_26_01_total7, half_26_01_total8, half_26_01_total9, half_26_01_total10, half_26_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_26_01_hx10 : SourcePowerBound
    (powerBoxCross 16 16 1024 half_26_01_φ10) (137414637829/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 10) (s := 16) (u := 14) (t := 17)
    (D := 1024) (ψ := (276735137/10000000000 : ℝ)) half_26_01_φ10
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_26_01_bounds10 l).1) (fun l => (half_26_01_bounds10 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_26_01_total1, half_26_01_total2, half_26_01_total3, half_26_01_total4, half_26_01_total5, half_26_01_total6, half_26_01_total7, half_26_01_total8, half_26_01_total9, half_26_01_total10, half_26_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_15_01) (half_17_01)
    (by simpa only [half_26_01_φ11, show (2:ℝ)*1024=2048 by norm_num] using half_26_01_hx11)
  exact h.weaken (by norm_num [half_26_01_total1, half_26_01_total2, half_26_01_total3, half_26_01_total4, half_26_01_total5, half_26_01_total6, half_26_01_total7, half_26_01_total8, half_26_01_total9, half_26_01_total10, half_26_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_26_01_hx9 : SourcePowerBound
    (powerBoxCross 16 17 512 half_26_01_φ9) (75141980261/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 9) (s := 17) (u := 15) (t := 18)
    (D := 512) (ψ := (183070687/5000000000 : ℝ)) half_26_01_φ9
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_26_01_bounds9 l).1) (fun l => (half_26_01_bounds9 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_26_01_total1, half_26_01_total2, half_26_01_total3, half_26_01_total4, half_26_01_total5, half_26_01_total6, half_26_01_total7, half_26_01_total8, half_26_01_total9, half_26_01_total10, half_26_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_16_01) (half_18_01)
    (by simpa only [half_26_01_φ10, show (2:ℝ)*512=1024 by norm_num] using half_26_01_hx10)
  exact h.weaken (by norm_num [half_26_01_total1, half_26_01_total2, half_26_01_total3, half_26_01_total4, half_26_01_total5, half_26_01_total6, half_26_01_total7, half_26_01_total8, half_26_01_total9, half_26_01_total10, half_26_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_26_01_hx8 : SourcePowerBound
    (powerBoxCross 16 18 256 half_26_01_φ8) (82528785441/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 8) (s := 18) (u := 16) (t := 19)
    (D := 256) (ψ := (39229433/1000000000 : ℝ)) half_26_01_φ8
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_26_01_bounds8 l).1) (fun l => (half_26_01_bounds8 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_26_01_total1, half_26_01_total2, half_26_01_total3, half_26_01_total4, half_26_01_total5, half_26_01_total6, half_26_01_total7, half_26_01_total8, half_26_01_total9, half_26_01_total10, half_26_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_17_01) (half_19_01)
    (by simpa only [half_26_01_φ9, show (2:ℝ)*256=512 by norm_num] using half_26_01_hx9)
  exact h.weaken (by norm_num [half_26_01_total1, half_26_01_total2, half_26_01_total3, half_26_01_total4, half_26_01_total5, half_26_01_total6, half_26_01_total7, half_26_01_total8, half_26_01_total9, half_26_01_total10, half_26_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_26_01_hx7 : SourcePowerBound
    (powerBoxCross 16 19 128 half_26_01_φ7) (91099252877/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 7) (s := 19) (u := 17) (t := 20)
    (D := 128) (ψ := (420315353/10000000000 : ℝ)) half_26_01_φ7
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_26_01_bounds7 l).1) (fun l => (half_26_01_bounds7 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_26_01_total1, half_26_01_total2, half_26_01_total3, half_26_01_total4, half_26_01_total5, half_26_01_total6, half_26_01_total7, half_26_01_total8, half_26_01_total9, half_26_01_total10, half_26_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_18_01) (half_20_01)
    (by simpa only [half_26_01_φ8, show (2:ℝ)*128=256 by norm_num] using half_26_01_hx8)
  exact h.weaken (by norm_num [half_26_01_total1, half_26_01_total2, half_26_01_total3, half_26_01_total4, half_26_01_total5, half_26_01_total6, half_26_01_total7, half_26_01_total8, half_26_01_total9, half_26_01_total10, half_26_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_26_01_hx6 : SourcePowerBound
    (powerBoxCross 16 20 64 half_26_01_φ6) (25258934213/1250000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 6) (s := 20) (u := 18) (t := 21)
    (D := 64) (ψ := (225168939/5000000000 : ℝ)) half_26_01_φ6
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_26_01_bounds6 l).1) (fun l => (half_26_01_bounds6 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_26_01_total1, half_26_01_total2, half_26_01_total3, half_26_01_total4, half_26_01_total5, half_26_01_total6, half_26_01_total7, half_26_01_total8, half_26_01_total9, half_26_01_total10, half_26_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_19_01) (half_21_01)
    (by simpa only [half_26_01_φ7, show (2:ℝ)*64=128 by norm_num] using half_26_01_hx7)
  exact h.weaken (by norm_num [half_26_01_total1, half_26_01_total2, half_26_01_total3, half_26_01_total4, half_26_01_total5, half_26_01_total6, half_26_01_total7, half_26_01_total8, half_26_01_total9, half_26_01_total10, half_26_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_26_01_hx5 : SourcePowerBound
    (powerBoxCross 16 21 32 half_26_01_φ5) (28125869029/1250000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 5) (s := 21) (u := 19) (t := 22)
    (D := 32) (ψ := (48250487/1000000000 : ℝ)) half_26_01_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_26_01_bounds5 l).1) (fun l => (half_26_01_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_26_01_total1, half_26_01_total2, half_26_01_total3, half_26_01_total4, half_26_01_total5, half_26_01_total6, half_26_01_total7, half_26_01_total8, half_26_01_total9, half_26_01_total10, half_26_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_20_01) (half_22_01)
    (by simpa only [half_26_01_φ6, show (2:ℝ)*32=64 by norm_num] using half_26_01_hx6)
  exact h.weaken (by norm_num [half_26_01_total1, half_26_01_total2, half_26_01_total3, half_26_01_total4, half_26_01_total5, half_26_01_total6, half_26_01_total7, half_26_01_total8, half_26_01_total9, half_26_01_total10, half_26_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_26_01_hx4 : SourcePowerBound
    (powerBoxCross 16 22 16 half_26_01_φ4) (251333256887/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 4) (s := 22) (u := 20) (t := 23)
    (D := 16) (ψ := (516969503/10000000000 : ℝ)) half_26_01_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_26_01_bounds4 l).1) (fun l => (half_26_01_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_26_01_total1, half_26_01_total2, half_26_01_total3, half_26_01_total4, half_26_01_total5, half_26_01_total6, half_26_01_total7, half_26_01_total8, half_26_01_total9, half_26_01_total10, half_26_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_21_01) (half_23_01)
    (by simpa only [half_26_01_φ5, show (2:ℝ)*16=32 by norm_num] using half_26_01_hx5)
  exact h.weaken (by norm_num [half_26_01_total1, half_26_01_total2, half_26_01_total3, half_26_01_total4, half_26_01_total5, half_26_01_total6, half_26_01_total7, half_26_01_total8, half_26_01_total9, half_26_01_total10, half_26_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_26_01_hx3 : SourcePowerBound
    (powerBoxCross 16 23 8 half_26_01_φ3) (5618480451/200000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 23) (u := 21) (t := 24)
    (D := 8) (ψ := (543725377/10000000000 : ℝ)) half_26_01_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_26_01_bounds3 l).1) (fun l => (half_26_01_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_26_01_total1, half_26_01_total2, half_26_01_total3, half_26_01_total4, half_26_01_total5, half_26_01_total6, half_26_01_total7, half_26_01_total8, half_26_01_total9, half_26_01_total10, half_26_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_22_01) (half_24_01)
    (by simpa only [half_26_01_φ4, show (2:ℝ)*8=16 by norm_num] using half_26_01_hx4)
  exact h.weaken (by norm_num [half_26_01_total1, half_26_01_total2, half_26_01_total3, half_26_01_total4, half_26_01_total5, half_26_01_total6, half_26_01_total7, half_26_01_total8, half_26_01_total9, half_26_01_total10, half_26_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_26_01_hx2 : SourcePowerBound
    (powerBoxCross 16 24 4 half_26_01_φ2) (62573723913/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 24) (u := 22) (t := 25)
    (D := 4) (ψ := (547803877/10000000000 : ℝ)) half_26_01_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_26_01_bounds2 l).1) (fun l => (half_26_01_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_26_01_total1, half_26_01_total2, half_26_01_total3, half_26_01_total4, half_26_01_total5, half_26_01_total6, half_26_01_total7, half_26_01_total8, half_26_01_total9, half_26_01_total10, half_26_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_23_01) (half_25_01)
    (by simpa only [half_26_01_φ3, show (2:ℝ)*4=8 by norm_num] using half_26_01_hx3)
  exact h.weaken (by norm_num [half_26_01_total1, half_26_01_total2, half_26_01_total3, half_26_01_total4, half_26_01_total5, half_26_01_total6, half_26_01_total7, half_26_01_total8, half_26_01_total9, half_26_01_total10, half_26_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_26_01_hx1 : SourcePowerBound
    (powerBoxCross 16 25 2 half_26_01_φ1) (339783711/9765625 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 25) (u := 23) (t := 26)
    (D := 2) (ψ := (69197971/1250000000 : ℝ)) half_26_01_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_26_01_bounds1 l).1) (fun l => (half_26_01_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_26_01_total1, half_26_01_total2, half_26_01_total3, half_26_01_total4, half_26_01_total5, half_26_01_total6, half_26_01_total7, half_26_01_total8, half_26_01_total9, half_26_01_total10, half_26_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_24_01) (chord_64)
    (by simpa only [half_26_01_φ2, show (2:ℝ)*2=4 by norm_num] using half_26_01_hx2)
  exact h.weaken (by norm_num [half_26_01_total1, half_26_01_total2, half_26_01_total3, half_26_01_total4, half_26_01_total5, half_26_01_total6, half_26_01_total7, half_26_01_total8, half_26_01_total9, half_26_01_total10, half_26_01_total11, parameterExponent, curveLoss, dyadicExponent])

theorem half_26_01 : AdmissibleExponent 16 52 (377355396497/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 24) (ψ := (600344417/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_25_01)
    (by simpa only [half_26_01_φ1] using half_26_01_hx1)
  exact admissibleExponent_mono h (by norm_num [half_26_01_total1, half_26_01_total2, half_26_01_total3, half_26_01_total4, half_26_01_total5, half_26_01_total6, half_26_01_total7, half_26_01_total8, half_26_01_total9, half_26_01_total10, half_26_01_total11, parameterExponent, curveLoss, dyadicExponent])

theorem chord_68 : AdmissibleExponent 16 54 (6211689839/156250000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 54) (t := (3/4 : ℝ))
    (half_26_01) (half_30_00)
    (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private def half_27_01_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (609995127/10000000000 : ℝ)

private theorem half_27_01_total1 : total half_27_01_φ1=(609995127/10000000000 : ℝ) := by
  norm_num [half_27_01_φ1,total,emptyPhi,Fin.snoc]

private theorem half_27_01_bounds1 : ∀ l,0≤half_27_01_φ1 l ∧ half_27_01_φ1 l≤1 ∧
    0≤shiftExponents 16 half_27_01_φ1 l :=
  alternate_bounds_snoc emptyPhi (609995127/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_27_01_φ2 : Fin 2 → ℝ := Fin.snoc half_27_01_φ1 (2800493/50000000 : ℝ)

private theorem half_27_01_total2 : total half_27_01_φ2=(1170093727/10000000000 : ℝ) := by
  change total (Fin.snoc half_27_01_φ1 (2800493/50000000 : ℝ))=(1170093727/10000000000 : ℝ)
  rw [alternate_total_snoc,half_27_01_total1]
  norm_num

private theorem half_27_01_bounds2 : ∀ l,0≤half_27_01_φ2 l ∧ half_27_01_φ2 l≤1 ∧
    0≤shiftExponents 16 half_27_01_φ2 l :=
  alternate_bounds_snoc half_27_01_φ1 (2800493/50000000 : ℝ) half_27_01_bounds1 (by norm_num)

private def half_27_01_φ3 : Fin 3 → ℝ := Fin.snoc half_27_01_φ2 (554905177/10000000000 : ℝ)

private theorem half_27_01_total3 : total half_27_01_φ3=(215624863/1250000000 : ℝ) := by
  change total (Fin.snoc half_27_01_φ2 (554905177/10000000000 : ℝ))=(215624863/1250000000 : ℝ)
  rw [alternate_total_snoc,half_27_01_total2]
  norm_num

private theorem half_27_01_bounds3 : ∀ l,0≤half_27_01_φ3 l ∧ half_27_01_φ3 l≤1 ∧
    0≤shiftExponents 16 half_27_01_φ3 l :=
  alternate_bounds_snoc half_27_01_φ2 (554905177/10000000000 : ℝ) half_27_01_bounds2 (by norm_num)

private def half_27_01_φ4 : Fin 4 → ℝ := Fin.snoc half_27_01_φ3 (551666739/10000000000 : ℝ)

private theorem half_27_01_total4 : total half_27_01_φ4=(2276665643/10000000000 : ℝ) := by
  change total (Fin.snoc half_27_01_φ3 (551666739/10000000000 : ℝ))=(2276665643/10000000000 : ℝ)
  rw [alternate_total_snoc,half_27_01_total3]
  norm_num

private theorem half_27_01_bounds4 : ∀ l,0≤half_27_01_φ4 l ∧ half_27_01_φ4 l≤1 ∧
    0≤shiftExponents 16 half_27_01_φ4 l :=
  alternate_bounds_snoc half_27_01_φ3 (551666739/10000000000 : ℝ) half_27_01_bounds3 (by norm_num)

private def half_27_01_φ5 : Fin 5 → ℝ := Fin.snoc half_27_01_φ4 (128722239/2500000000 : ℝ)

private theorem half_27_01_total5 : total half_27_01_φ5=(2791554599/10000000000 : ℝ) := by
  change total (Fin.snoc half_27_01_φ4 (128722239/2500000000 : ℝ))=(2791554599/10000000000 : ℝ)
  rw [alternate_total_snoc,half_27_01_total4]
  norm_num

private theorem half_27_01_bounds5 : ∀ l,0≤half_27_01_φ5 l ∧ half_27_01_φ5 l≤1 ∧
    0≤shiftExponents 16 half_27_01_φ5 l :=
  alternate_bounds_snoc half_27_01_φ4 (128722239/2500000000 : ℝ) half_27_01_bounds4 (by norm_num)

private def half_27_01_φ6 : Fin 6 → ℝ := Fin.snoc half_27_01_φ5 (240281513/5000000000 : ℝ)

private theorem half_27_01_total6 : total half_27_01_φ6=(26176941/80000000 : ℝ) := by
  change total (Fin.snoc half_27_01_φ5 (240281513/5000000000 : ℝ))=(26176941/80000000 : ℝ)
  rw [alternate_total_snoc,half_27_01_total5]
  norm_num

private theorem half_27_01_bounds6 : ∀ l,0≤half_27_01_φ6 l ∧ half_27_01_φ6 l≤1 ∧
    0≤shiftExponents 16 half_27_01_φ6 l :=
  alternate_bounds_snoc half_27_01_φ5 (240281513/5000000000 : ℝ) half_27_01_bounds5 (by norm_num)

private def half_27_01_φ7 : Fin 7 → ℝ := Fin.snoc half_27_01_φ6 (448525491/10000000000 : ℝ)

private theorem half_27_01_total7 : total half_27_01_φ7=(930160779/2500000000 : ℝ) := by
  change total (Fin.snoc half_27_01_φ6 (448525491/10000000000 : ℝ))=(930160779/2500000000 : ℝ)
  rw [alternate_total_snoc,half_27_01_total6]
  norm_num

private theorem half_27_01_bounds7 : ∀ l,0≤half_27_01_φ7 l ∧ half_27_01_φ7 l≤1 ∧
    0≤shiftExponents 16 half_27_01_φ7 l :=
  alternate_bounds_snoc half_27_01_φ6 (448525491/10000000000 : ℝ) half_27_01_bounds6 (by norm_num)

private def half_27_01_φ8 : Fin 8 → ℝ := Fin.snoc half_27_01_φ7 (418623791/10000000000 : ℝ)

private theorem half_27_01_total8 : total half_27_01_φ8=(4139266907/10000000000 : ℝ) := by
  change total (Fin.snoc half_27_01_φ7 (418623791/10000000000 : ℝ))=(4139266907/10000000000 : ℝ)
  rw [alternate_total_snoc,half_27_01_total7]
  norm_num

private theorem half_27_01_bounds8 : ∀ l,0≤half_27_01_φ8 l ∧ half_27_01_φ8 l≤1 ∧
    0≤shiftExponents 16 half_27_01_φ8 l :=
  alternate_bounds_snoc half_27_01_φ7 (418623791/10000000000 : ℝ) half_27_01_bounds7 (by norm_num)

private def half_27_01_φ9 : Fin 9 → ℝ := Fin.snoc half_27_01_φ8 (390715539/10000000000 : ℝ)

private theorem half_27_01_total9 : total half_27_01_φ9=(2264991223/5000000000 : ℝ) := by
  change total (Fin.snoc half_27_01_φ8 (390715539/10000000000 : ℝ))=(2264991223/5000000000 : ℝ)
  rw [alternate_total_snoc,half_27_01_total8]
  norm_num

private theorem half_27_01_bounds9 : ∀ l,0≤half_27_01_φ9 l ∧ half_27_01_φ9 l≤1 ∧
    0≤shiftExponents 16 half_27_01_φ9 l :=
  alternate_bounds_snoc half_27_01_φ8 (390715539/10000000000 : ℝ) half_27_01_bounds8 (by norm_num)

private def half_27_01_φ10 : Fin 10 → ℝ := Fin.snoc half_27_01_φ9 (91166959/2500000000 : ℝ)

private theorem half_27_01_total10 : total half_27_01_φ10=(2447325141/5000000000 : ℝ) := by
  change total (Fin.snoc half_27_01_φ9 (91166959/2500000000 : ℝ))=(2447325141/5000000000 : ℝ)
  rw [alternate_total_snoc,half_27_01_total9]
  norm_num

private theorem half_27_01_bounds10 : ∀ l,0≤half_27_01_φ10 l ∧ half_27_01_φ10 l≤1 ∧
    0≤shiftExponents 16 half_27_01_φ10 l :=
  alternate_bounds_snoc half_27_01_φ9 (91166959/2500000000 : ℝ) half_27_01_bounds9 (by norm_num)

private def half_27_01_φ11 : Fin 11 → ℝ := Fin.snoc half_27_01_φ10 (328369513/10000000000 : ℝ)

private theorem half_27_01_total11 : total half_27_01_φ11=(1044603959/2000000000 : ℝ) := by
  change total (Fin.snoc half_27_01_φ10 (328369513/10000000000 : ℝ))=(1044603959/2000000000 : ℝ)
  rw [alternate_total_snoc,half_27_01_total10]
  norm_num

private theorem half_27_01_bounds11 : ∀ l,0≤half_27_01_φ11 l ∧ half_27_01_φ11 l≤1 ∧
    0≤shiftExponents 16 half_27_01_φ11 l :=
  alternate_bounds_snoc half_27_01_φ10 (328369513/10000000000 : ℝ) half_27_01_bounds10 (by norm_num)

private theorem half_27_01_prefix : PrefixCondition 16 half_27_01_φ11 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_27_01_φ1, half_27_01_φ2, half_27_01_φ3, half_27_01_φ4, half_27_01_φ5, half_27_01_φ6, half_27_01_φ7, half_27_01_φ8, half_27_01_φ9, half_27_01_φ10, half_27_01_φ11, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_27_01_hF2 : SourcePowerBound
    (paddedMoment 16 0 2 2048 half_27_01_φ11) (4598564369/400000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 16) (j := 11) (r := 0) (n := 1) (D := 2048)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_27_01_φ11
    (fun i => (half_27_01_bounds11 i).1) (fun i => (half_27_01_bounds11 i).2.1)
    (fun i => (half_27_01_bounds11 i).2.2) half_27_01_prefix
  convert h using 1 <;> norm_num [half_27_01_total1, half_27_01_total2, half_27_01_total3, half_27_01_total4, half_27_01_total5, half_27_01_total6, half_27_01_total7, half_27_01_total8, half_27_01_total9, half_27_01_total10, half_27_01_total11, parameterExponent, curveLoss, dyadicExponent]

private theorem half_27_01_hx11 : SourcePowerBound
    (powerBoxCross 16 16 2048 half_27_01_φ11) (261161887/19531250 : ℝ) := by
  have h := full_A_cross_power (k := 16) (s := 16) (r := 2) (v := 21) (w := 22) (D := 2048)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_27_01_φ11 (by norm_num [half_27_01_total1, half_27_01_total2, half_27_01_total3, half_27_01_total4, half_27_01_total5, half_27_01_total6, half_27_01_total7, half_27_01_total8, half_27_01_total9, half_27_01_total10, half_27_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_27_01_total1, half_27_01_total2, half_27_01_total3, half_27_01_total4, half_27_01_total5, half_27_01_total6, half_27_01_total7, half_27_01_total8, half_27_01_total9, half_27_01_total10, half_27_01_total11, parameterExponent, curveLoss, dyadicExponent]) half_27_01_hF2
    (half_21_01) (half_22_01)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_27_01_total1, half_27_01_total2, half_27_01_total3, half_27_01_total4, half_27_01_total5, half_27_01_total6, half_27_01_total7, half_27_01_total8, half_27_01_total9, half_27_01_total10, half_27_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_27_01_hx10 : SourcePowerBound
    (powerBoxCross 16 17 1024 half_27_01_φ10) (145390736537/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 10) (s := 17) (u := 15) (t := 18)
    (D := 1024) (ψ := (328369513/10000000000 : ℝ)) half_27_01_φ10
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_27_01_bounds10 l).1) (fun l => (half_27_01_bounds10 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_27_01_total1, half_27_01_total2, half_27_01_total3, half_27_01_total4, half_27_01_total5, half_27_01_total6, half_27_01_total7, half_27_01_total8, half_27_01_total9, half_27_01_total10, half_27_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_16_01) (half_18_01)
    (by simpa only [half_27_01_φ11, show (2:ℝ)*1024=2048 by norm_num] using half_27_01_hx11)
  exact h.weaken (by norm_num [half_27_01_total1, half_27_01_total2, half_27_01_total3, half_27_01_total4, half_27_01_total5, half_27_01_total6, half_27_01_total7, half_27_01_total8, half_27_01_total9, half_27_01_total10, half_27_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_27_01_hx9 : SourcePowerBound
    (powerBoxCross 16 18 512 half_27_01_φ9) (158814044197/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 9) (s := 18) (u := 16) (t := 19)
    (D := 512) (ψ := (91166959/2500000000 : ℝ)) half_27_01_φ9
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_27_01_bounds9 l).1) (fun l => (half_27_01_bounds9 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_27_01_total1, half_27_01_total2, half_27_01_total3, half_27_01_total4, half_27_01_total5, half_27_01_total6, half_27_01_total7, half_27_01_total8, half_27_01_total9, half_27_01_total10, half_27_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_17_01) (half_19_01)
    (by simpa only [half_27_01_φ10, show (2:ℝ)*512=1024 by norm_num] using half_27_01_hx10)
  exact h.weaken (by norm_num [half_27_01_total1, half_27_01_total2, half_27_01_total3, half_27_01_total4, half_27_01_total5, half_27_01_total6, half_27_01_total7, half_27_01_total8, half_27_01_total9, half_27_01_total10, half_27_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_27_01_hx8 : SourcePowerBound
    (powerBoxCross 16 19 256 half_27_01_φ8) (2722512493/156250000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 8) (s := 19) (u := 17) (t := 20)
    (D := 256) (ψ := (390715539/10000000000 : ℝ)) half_27_01_φ8
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_27_01_bounds8 l).1) (fun l => (half_27_01_bounds8 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_27_01_total1, half_27_01_total2, half_27_01_total3, half_27_01_total4, half_27_01_total5, half_27_01_total6, half_27_01_total7, half_27_01_total8, half_27_01_total9, half_27_01_total10, half_27_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_18_01) (half_20_01)
    (by simpa only [half_27_01_φ9, show (2:ℝ)*256=512 by norm_num] using half_27_01_hx9)
  exact h.weaken (by norm_num [half_27_01_total1, half_27_01_total2, half_27_01_total3, half_27_01_total4, half_27_01_total5, half_27_01_total6, half_27_01_total7, half_27_01_total8, half_27_01_total9, half_27_01_total10, half_27_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_27_01_hx7 : SourcePowerBound
    (powerBoxCross 16 20 128 half_27_01_φ7) (9605430441/500000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 7) (s := 20) (u := 18) (t := 21)
    (D := 128) (ψ := (418623791/10000000000 : ℝ)) half_27_01_φ7
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_27_01_bounds7 l).1) (fun l => (half_27_01_bounds7 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_27_01_total1, half_27_01_total2, half_27_01_total3, half_27_01_total4, half_27_01_total5, half_27_01_total6, half_27_01_total7, half_27_01_total8, half_27_01_total9, half_27_01_total10, half_27_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_19_01) (half_21_01)
    (by simpa only [half_27_01_φ8, show (2:ℝ)*128=256 by norm_num] using half_27_01_hx8)
  exact h.weaken (by norm_num [half_27_01_total1, half_27_01_total2, half_27_01_total3, half_27_01_total4, half_27_01_total5, half_27_01_total6, half_27_01_total7, half_27_01_total8, half_27_01_total9, half_27_01_total10, half_27_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_27_01_hx6 : SourcePowerBound
    (powerBoxCross 16 21 64 half_27_01_φ6) (212773967107/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 6) (s := 21) (u := 19) (t := 22)
    (D := 64) (ψ := (448525491/10000000000 : ℝ)) half_27_01_φ6
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_27_01_bounds6 l).1) (fun l => (half_27_01_bounds6 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_27_01_total1, half_27_01_total2, half_27_01_total3, half_27_01_total4, half_27_01_total5, half_27_01_total6, half_27_01_total7, half_27_01_total8, half_27_01_total9, half_27_01_total10, half_27_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_20_01) (half_22_01)
    (by simpa only [half_27_01_φ7, show (2:ℝ)*64=128 by norm_num] using half_27_01_hx7)
  exact h.weaken (by norm_num [half_27_01_total1, half_27_01_total2, half_27_01_total3, half_27_01_total4, half_27_01_total5, half_27_01_total6, half_27_01_total7, half_27_01_total8, half_27_01_total9, half_27_01_total10, half_27_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_27_01_hx5 : SourcePowerBound
    (powerBoxCross 16 22 32 half_27_01_φ5) (236566714443/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 5) (s := 22) (u := 20) (t := 23)
    (D := 32) (ψ := (240281513/5000000000 : ℝ)) half_27_01_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_27_01_bounds5 l).1) (fun l => (half_27_01_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_27_01_total1, half_27_01_total2, half_27_01_total3, half_27_01_total4, half_27_01_total5, half_27_01_total6, half_27_01_total7, half_27_01_total8, half_27_01_total9, half_27_01_total10, half_27_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_21_01) (half_23_01)
    (by simpa only [half_27_01_φ6, show (2:ℝ)*32=64 by norm_num] using half_27_01_hx6)
  exact h.weaken (by norm_num [half_27_01_total1, half_27_01_total2, half_27_01_total3, half_27_01_total4, half_27_01_total5, half_27_01_total6, half_27_01_total7, half_27_01_total8, half_27_01_total9, half_27_01_total10, half_27_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_27_01_hx4 : SourcePowerBound
    (powerBoxCross 16 23 16 half_27_01_φ4) (65954225061/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 4) (s := 23) (u := 21) (t := 24)
    (D := 16) (ψ := (128722239/2500000000 : ℝ)) half_27_01_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_27_01_bounds4 l).1) (fun l => (half_27_01_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_27_01_total1, half_27_01_total2, half_27_01_total3, half_27_01_total4, half_27_01_total5, half_27_01_total6, half_27_01_total7, half_27_01_total8, half_27_01_total9, half_27_01_total10, half_27_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_22_01) (half_24_01)
    (by simpa only [half_27_01_φ5, show (2:ℝ)*16=32 by norm_num] using half_27_01_hx5)
  exact h.weaken (by norm_num [half_27_01_total1, half_27_01_total2, half_27_01_total3, half_27_01_total4, half_27_01_total5, half_27_01_total6, half_27_01_total7, half_27_01_total8, half_27_01_total9, half_27_01_total10, half_27_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_27_01_hx3 : SourcePowerBound
    (powerBoxCross 16 24 8 half_27_01_φ3) (73717887023/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 24) (u := 22) (t := 25)
    (D := 8) (ψ := (551666739/10000000000 : ℝ)) half_27_01_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_27_01_bounds3 l).1) (fun l => (half_27_01_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_27_01_total1, half_27_01_total2, half_27_01_total3, half_27_01_total4, half_27_01_total5, half_27_01_total6, half_27_01_total7, half_27_01_total8, half_27_01_total9, half_27_01_total10, half_27_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_23_01) (half_25_01)
    (by simpa only [half_27_01_φ4, show (2:ℝ)*8=16 by norm_num] using half_27_01_hx4)
  exact h.weaken (by norm_num [half_27_01_total1, half_27_01_total2, half_27_01_total3, half_27_01_total4, half_27_01_total5, half_27_01_total6, half_27_01_total7, half_27_01_total8, half_27_01_total9, half_27_01_total10, half_27_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_27_01_hx2 : SourcePowerBound
    (powerBoxCross 16 25 4 half_27_01_φ2) (328300981887/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 25) (u := 23) (t := 26)
    (D := 4) (ψ := (554905177/10000000000 : ℝ)) half_27_01_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_27_01_bounds2 l).1) (fun l => (half_27_01_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_27_01_total1, half_27_01_total2, half_27_01_total3, half_27_01_total4, half_27_01_total5, half_27_01_total6, half_27_01_total7, half_27_01_total8, half_27_01_total9, half_27_01_total10, half_27_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_24_01) (half_26_01)
    (by simpa only [half_27_01_φ3, show (2:ℝ)*4=8 by norm_num] using half_27_01_hx3)
  exact h.weaken (by norm_num [half_27_01_total1, half_27_01_total2, half_27_01_total3, half_27_01_total4, half_27_01_total5, half_27_01_total6, half_27_01_total7, half_27_01_total8, half_27_01_total9, half_27_01_total10, half_27_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_27_01_hx1 : SourcePowerBound
    (powerBoxCross 16 26 2 half_27_01_φ1) (22809181021/625000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 26) (u := 24) (t := 27)
    (D := 2) (ψ := (2800493/50000000 : ℝ)) half_27_01_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_27_01_bounds1 l).1) (fun l => (half_27_01_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_27_01_total1, half_27_01_total2, half_27_01_total3, half_27_01_total4, half_27_01_total5, half_27_01_total6, half_27_01_total7, half_27_01_total8, half_27_01_total9, half_27_01_total10, half_27_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_25_01) (chord_68)
    (by simpa only [half_27_01_φ2, show (2:ℝ)*2=4 by norm_num] using half_27_01_hx2)
  exact h.weaken (by norm_num [half_27_01_total1, half_27_01_total2, half_27_01_total3, half_27_01_total4, half_27_01_total5, half_27_01_total6, half_27_01_total7, half_27_01_total8, half_27_01_total9, half_27_01_total10, half_27_01_total11, parameterExponent, curveLoss, dyadicExponent])

theorem half_27_01 : AdmissibleExponent 16 54 (396056647813/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 25) (ψ := (609995127/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_26_01)
    (by simpa only [half_27_01_φ1] using half_27_01_hx1)
  exact admissibleExponent_mono h (by norm_num [half_27_01_total1, half_27_01_total2, half_27_01_total3, half_27_01_total4, half_27_01_total5, half_27_01_total6, half_27_01_total7, half_27_01_total8, half_27_01_total9, half_27_01_total10, half_27_01_total11, parameterExponent, curveLoss, dyadicExponent])

theorem chord_71 : AdmissibleExponent 16 56 (1250239704919/30000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 56) (t := (2/3 : ℝ))
    (half_27_01) (half_30_00)
    (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private def half_28_01_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (77924889/1250000000 : ℝ)

private theorem half_28_01_total1 : total half_28_01_φ1=(77924889/1250000000 : ℝ) := by
  norm_num [half_28_01_φ1,total,emptyPhi,Fin.snoc]

private theorem half_28_01_bounds1 : ∀ l,0≤half_28_01_φ1 l ∧ half_28_01_φ1 l≤1 ∧
    0≤shiftExponents 16 half_28_01_φ1 l :=
  alternate_bounds_snoc emptyPhi (77924889/1250000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_28_01_φ2 : Fin 2 → ℝ := Fin.snoc half_28_01_φ1 (141682119/2500000000 : ℝ)

private theorem half_28_01_total2 : total half_28_01_φ2=(297531897/2500000000 : ℝ) := by
  change total (Fin.snoc half_28_01_φ1 (141682119/2500000000 : ℝ))=(297531897/2500000000 : ℝ)
  rw [alternate_total_snoc,half_28_01_total1]
  norm_num

private theorem half_28_01_bounds2 : ∀ l,0≤half_28_01_φ2 l ∧ half_28_01_φ2 l≤1 ∧
    0≤shiftExponents 16 half_28_01_φ2 l :=
  alternate_bounds_snoc half_28_01_φ1 (141682119/2500000000 : ℝ) half_28_01_bounds1 (by norm_num)

private def half_28_01_φ3 : Fin 3 → ℝ := Fin.snoc half_28_01_φ2 (562174661/10000000000 : ℝ)

private theorem half_28_01_total3 : total half_28_01_φ3=(1752302249/10000000000 : ℝ) := by
  change total (Fin.snoc half_28_01_φ2 (562174661/10000000000 : ℝ))=(1752302249/10000000000 : ℝ)
  rw [alternate_total_snoc,half_28_01_total2]
  norm_num

private theorem half_28_01_bounds3 : ∀ l,0≤half_28_01_φ3 l ∧ half_28_01_φ3 l≤1 ∧
    0≤shiftExponents 16 half_28_01_φ3 l :=
  alternate_bounds_snoc half_28_01_φ2 (562174661/10000000000 : ℝ) half_28_01_bounds2 (by norm_num)

private def half_28_01_φ4 : Fin 4 → ℝ := Fin.snoc half_28_01_φ3 (137461629/2500000000 : ℝ)

private theorem half_28_01_total4 : total half_28_01_φ4=(460429753/2000000000 : ℝ) := by
  change total (Fin.snoc half_28_01_φ3 (137461629/2500000000 : ℝ))=(460429753/2000000000 : ℝ)
  rw [alternate_total_snoc,half_28_01_total3]
  norm_num

private theorem half_28_01_bounds4 : ∀ l,0≤half_28_01_φ4 l ∧ half_28_01_φ4 l≤1 ∧
    0≤shiftExponents 16 half_28_01_φ4 l :=
  alternate_bounds_snoc half_28_01_φ3 (137461629/2500000000 : ℝ) half_28_01_bounds3 (by norm_num)

private def half_28_01_φ5 : Fin 5 → ℝ := Fin.snoc half_28_01_φ4 (256595041/5000000000 : ℝ)

private theorem half_28_01_total5 : total half_28_01_φ5=(2815338847/10000000000 : ℝ) := by
  change total (Fin.snoc half_28_01_φ4 (256595041/5000000000 : ℝ))=(2815338847/10000000000 : ℝ)
  rw [alternate_total_snoc,half_28_01_total4]
  norm_num

private theorem half_28_01_bounds5 : ∀ l,0≤half_28_01_φ5 l ∧ half_28_01_φ5 l≤1 ∧
    0≤shiftExponents 16 half_28_01_φ5 l :=
  alternate_bounds_snoc half_28_01_φ4 (256595041/5000000000 : ℝ) half_28_01_bounds4 (by norm_num)

private def half_28_01_φ6 : Fin 6 → ℝ := Fin.snoc half_28_01_φ5 (47897741/1000000000 : ℝ)

private theorem half_28_01_total6 : total half_28_01_φ6=(3294316257/10000000000 : ℝ) := by
  change total (Fin.snoc half_28_01_φ5 (47897741/1000000000 : ℝ))=(3294316257/10000000000 : ℝ)
  rw [alternate_total_snoc,half_28_01_total5]
  norm_num

private theorem half_28_01_bounds6 : ∀ l,0≤half_28_01_φ6 l ∧ half_28_01_φ6 l≤1 ∧
    0≤shiftExponents 16 half_28_01_φ6 l :=
  alternate_bounds_snoc half_28_01_φ5 (47897741/1000000000 : ℝ) half_28_01_bounds5 (by norm_num)

private def half_28_01_φ7 : Fin 7 → ℝ := Fin.snoc half_28_01_φ6 (223522791/5000000000 : ℝ)

private theorem half_28_01_total7 : total half_28_01_φ7=(3741361839/10000000000 : ℝ) := by
  change total (Fin.snoc half_28_01_φ6 (223522791/5000000000 : ℝ))=(3741361839/10000000000 : ℝ)
  rw [alternate_total_snoc,half_28_01_total6]
  norm_num

private theorem half_28_01_bounds7 : ∀ l,0≤half_28_01_φ7 l ∧ half_28_01_φ7 l≤1 ∧
    0≤shiftExponents 16 half_28_01_φ7 l :=
  alternate_bounds_snoc half_28_01_φ6 (223522791/5000000000 : ℝ) half_28_01_bounds6 (by norm_num)

private def half_28_01_φ8 : Fin 8 → ℝ := Fin.snoc half_28_01_φ7 (417242543/10000000000 : ℝ)

private theorem half_28_01_total8 : total half_28_01_φ8=(2079302191/5000000000 : ℝ) := by
  change total (Fin.snoc half_28_01_φ7 (417242543/10000000000 : ℝ))=(2079302191/5000000000 : ℝ)
  rw [alternate_total_snoc,half_28_01_total7]
  norm_num

private theorem half_28_01_bounds8 : ∀ l,0≤half_28_01_φ8 l ∧ half_28_01_φ8 l≤1 ∧
    0≤shiftExponents 16 half_28_01_φ8 l :=
  alternate_bounds_snoc half_28_01_φ7 (417242543/10000000000 : ℝ) half_28_01_bounds7 (by norm_num)

private def half_28_01_φ9 : Fin 9 → ℝ := Fin.snoc half_28_01_φ8 (194713187/5000000000 : ℝ)

private theorem half_28_01_total9 : total half_28_01_φ9=(1137007689/2500000000 : ℝ) := by
  change total (Fin.snoc half_28_01_φ8 (194713187/5000000000 : ℝ))=(1137007689/2500000000 : ℝ)
  rw [alternate_total_snoc,half_28_01_total8]
  norm_num

private theorem half_28_01_bounds9 : ∀ l,0≤half_28_01_φ9 l ∧ half_28_01_φ9 l≤1 ∧
    0≤shiftExponents 16 half_28_01_φ9 l :=
  alternate_bounds_snoc half_28_01_φ8 (194713187/5000000000 : ℝ) half_28_01_bounds8 (by norm_num)

private def half_28_01_φ10 : Fin 10 → ℝ := Fin.snoc half_28_01_φ9 (72692923/2000000000 : ℝ)

private theorem half_28_01_total10 : total half_28_01_φ10=(4911495371/10000000000 : ℝ) := by
  change total (Fin.snoc half_28_01_φ9 (72692923/2000000000 : ℝ))=(4911495371/10000000000 : ℝ)
  rw [alternate_total_snoc,half_28_01_total9]
  norm_num

private theorem half_28_01_bounds10 : ∀ l,0≤half_28_01_φ10 l ∧ half_28_01_φ10 l≤1 ∧
    0≤shiftExponents 16 half_28_01_φ10 l :=
  alternate_bounds_snoc half_28_01_φ9 (72692923/2000000000 : ℝ) half_28_01_bounds9 (by norm_num)

private def half_28_01_φ11 : Fin 11 → ℝ := Fin.snoc half_28_01_φ10 (339233641/10000000000 : ℝ)

private theorem half_28_01_total11 : total half_28_01_φ11=(1312682253/2500000000 : ℝ) := by
  change total (Fin.snoc half_28_01_φ10 (339233641/10000000000 : ℝ))=(1312682253/2500000000 : ℝ)
  rw [alternate_total_snoc,half_28_01_total10]
  norm_num

private theorem half_28_01_bounds11 : ∀ l,0≤half_28_01_φ11 l ∧ half_28_01_φ11 l≤1 ∧
    0≤shiftExponents 16 half_28_01_φ11 l :=
  alternate_bounds_snoc half_28_01_φ10 (339233641/10000000000 : ℝ) half_28_01_bounds10 (by norm_num)

private theorem half_28_01_prefix : PrefixCondition 16 half_28_01_φ11 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_28_01_φ1, half_28_01_φ2, half_28_01_φ3, half_28_01_φ4, half_28_01_φ5, half_28_01_φ6, half_28_01_φ7, half_28_01_φ8, half_28_01_φ9, half_28_01_φ10, half_28_01_φ11, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_28_01_hF2 : SourcePowerBound
    (paddedMoment 16 0 2 2048 half_28_01_φ11) (5685859723/500000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 16) (j := 11) (r := 0) (n := 1) (D := 2048)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_28_01_φ11
    (fun i => (half_28_01_bounds11 i).1) (fun i => (half_28_01_bounds11 i).2.1)
    (fun i => (half_28_01_bounds11 i).2.2) half_28_01_prefix
  convert h using 1 <;> norm_num [half_28_01_total1, half_28_01_total2, half_28_01_total3, half_28_01_total4, half_28_01_total5, half_28_01_total6, half_28_01_total7, half_28_01_total8, half_28_01_total9, half_28_01_total10, half_28_01_total11, parameterExponent, curveLoss, dyadicExponent]

private theorem half_28_01_hx11 : SourcePowerBound
    (powerBoxCross 16 17 2048 half_28_01_φ11) (141213049543/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 16) (s := 17) (r := 2) (v := 22) (w := 23) (D := 2048)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_28_01_φ11 (by norm_num [half_28_01_total1, half_28_01_total2, half_28_01_total3, half_28_01_total4, half_28_01_total5, half_28_01_total6, half_28_01_total7, half_28_01_total8, half_28_01_total9, half_28_01_total10, half_28_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_28_01_total1, half_28_01_total2, half_28_01_total3, half_28_01_total4, half_28_01_total5, half_28_01_total6, half_28_01_total7, half_28_01_total8, half_28_01_total9, half_28_01_total10, half_28_01_total11, parameterExponent, curveLoss, dyadicExponent]) half_28_01_hF2
    (half_22_01) (half_23_01)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_28_01_total1, half_28_01_total2, half_28_01_total3, half_28_01_total4, half_28_01_total5, half_28_01_total6, half_28_01_total7, half_28_01_total8, half_28_01_total9, half_28_01_total10, half_28_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_28_01_hx10 : SourcePowerBound
    (powerBoxCross 16 18 1024 half_28_01_φ10) (76813182293/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 10) (s := 18) (u := 16) (t := 19)
    (D := 1024) (ψ := (339233641/10000000000 : ℝ)) half_28_01_φ10
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_28_01_bounds10 l).1) (fun l => (half_28_01_bounds10 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_28_01_total1, half_28_01_total2, half_28_01_total3, half_28_01_total4, half_28_01_total5, half_28_01_total6, half_28_01_total7, half_28_01_total8, half_28_01_total9, half_28_01_total10, half_28_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_17_01) (half_19_01)
    (by simpa only [half_28_01_φ11, show (2:ℝ)*1024=2048 by norm_num] using half_28_01_hx11)
  exact h.weaken (by norm_num [half_28_01_total1, half_28_01_total2, half_28_01_total3, half_28_01_total4, half_28_01_total5, half_28_01_total6, half_28_01_total7, half_28_01_total8, half_28_01_total9, half_28_01_total10, half_28_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_28_01_hx9 : SourcePowerBound
    (powerBoxCross 16 19 512 half_28_01_φ9) (83795773711/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 9) (s := 19) (u := 17) (t := 20)
    (D := 512) (ψ := (72692923/2000000000 : ℝ)) half_28_01_φ9
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_28_01_bounds9 l).1) (fun l => (half_28_01_bounds9 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_28_01_total1, half_28_01_total2, half_28_01_total3, half_28_01_total4, half_28_01_total5, half_28_01_total6, half_28_01_total7, half_28_01_total8, half_28_01_total9, half_28_01_total10, half_28_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_18_01) (half_20_01)
    (by simpa only [half_28_01_φ10, show (2:ℝ)*512=1024 by norm_num] using half_28_01_hx10)
  exact h.weaken (by norm_num [half_28_01_total1, half_28_01_total2, half_28_01_total3, half_28_01_total4, half_28_01_total5, half_28_01_total6, half_28_01_total7, half_28_01_total8, half_28_01_total9, half_28_01_total10, half_28_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_28_01_hx8 : SourcePowerBound
    (powerBoxCross 16 20 256 half_28_01_φ8) (18367160649/1000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 8) (s := 20) (u := 18) (t := 21)
    (D := 256) (ψ := (194713187/5000000000 : ℝ)) half_28_01_φ8
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_28_01_bounds8 l).1) (fun l => (half_28_01_bounds8 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_28_01_total1, half_28_01_total2, half_28_01_total3, half_28_01_total4, half_28_01_total5, half_28_01_total6, half_28_01_total7, half_28_01_total8, half_28_01_total9, half_28_01_total10, half_28_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_19_01) (half_21_01)
    (by simpa only [half_28_01_φ9, show (2:ℝ)*256=512 by norm_num] using half_28_01_hx9)
  exact h.weaken (by norm_num [half_28_01_total1, half_28_01_total2, half_28_01_total3, half_28_01_total4, half_28_01_total5, half_28_01_total6, half_28_01_total7, half_28_01_total8, half_28_01_total9, half_28_01_total10, half_28_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_28_01_hx7 : SourcePowerBound
    (powerBoxCross 16 21 128 half_28_01_φ7) (202276134373/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 7) (s := 21) (u := 19) (t := 22)
    (D := 128) (ψ := (417242543/10000000000 : ℝ)) half_28_01_φ7
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_28_01_bounds7 l).1) (fun l => (half_28_01_bounds7 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_28_01_total1, half_28_01_total2, half_28_01_total3, half_28_01_total4, half_28_01_total5, half_28_01_total6, half_28_01_total7, half_28_01_total8, half_28_01_total9, half_28_01_total10, half_28_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_20_01) (half_22_01)
    (by simpa only [half_28_01_φ8, show (2:ℝ)*128=256 by norm_num] using half_28_01_hx8)
  exact h.weaken (by norm_num [half_28_01_total1, half_28_01_total2, half_28_01_total3, half_28_01_total4, half_28_01_total5, half_28_01_total6, half_28_01_total7, half_28_01_total8, half_28_01_total9, half_28_01_total10, half_28_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_28_01_hx6 : SourcePowerBound
    (powerBoxCross 16 22 64 half_28_01_φ6) (111875473471/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 6) (s := 22) (u := 20) (t := 23)
    (D := 64) (ψ := (223522791/5000000000 : ℝ)) half_28_01_φ6
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_28_01_bounds6 l).1) (fun l => (half_28_01_bounds6 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_28_01_total1, half_28_01_total2, half_28_01_total3, half_28_01_total4, half_28_01_total5, half_28_01_total6, half_28_01_total7, half_28_01_total8, half_28_01_total9, half_28_01_total10, half_28_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_21_01) (half_23_01)
    (by simpa only [half_28_01_φ7, show (2:ℝ)*64=128 by norm_num] using half_28_01_hx7)
  exact h.weaken (by norm_num [half_28_01_total1, half_28_01_total2, half_28_01_total3, half_28_01_total4, half_28_01_total5, half_28_01_total6, half_28_01_total7, half_28_01_total8, half_28_01_total9, half_28_01_total10, half_28_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_28_01_hx5 : SourcePowerBound
    (powerBoxCross 16 23 32 half_28_01_φ5) (248422564399/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 5) (s := 23) (u := 21) (t := 24)
    (D := 32) (ψ := (47897741/1000000000 : ℝ)) half_28_01_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_28_01_bounds5 l).1) (fun l => (half_28_01_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_28_01_total1, half_28_01_total2, half_28_01_total3, half_28_01_total4, half_28_01_total5, half_28_01_total6, half_28_01_total7, half_28_01_total8, half_28_01_total9, half_28_01_total10, half_28_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_22_01) (half_24_01)
    (by simpa only [half_28_01_φ6, show (2:ℝ)*32=64 by norm_num] using half_28_01_hx6)
  exact h.weaken (by norm_num [half_28_01_total1, half_28_01_total2, half_28_01_total3, half_28_01_total4, half_28_01_total5, half_28_01_total6, half_28_01_total7, half_28_01_total8, half_28_01_total9, half_28_01_total10, half_28_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_28_01_hx4 : SourcePowerBound
    (powerBoxCross 16 24 16 half_28_01_φ4) (55324710381/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 4) (s := 24) (u := 22) (t := 25)
    (D := 16) (ψ := (256595041/5000000000 : ℝ)) half_28_01_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_28_01_bounds4 l).1) (fun l => (half_28_01_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_28_01_total1, half_28_01_total2, half_28_01_total3, half_28_01_total4, half_28_01_total5, half_28_01_total6, half_28_01_total7, half_28_01_total8, half_28_01_total9, half_28_01_total10, half_28_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_23_01) (half_25_01)
    (by simpa only [half_28_01_φ5, show (2:ℝ)*16=32 by norm_num] using half_28_01_hx5)
  exact h.weaken (by norm_num [half_28_01_total1, half_28_01_total2, half_28_01_total3, half_28_01_total4, half_28_01_total5, half_28_01_total6, half_28_01_total7, half_28_01_total8, half_28_01_total9, half_28_01_total10, half_28_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_28_01_hx3 : SourcePowerBound
    (powerBoxCross 16 25 8 half_28_01_φ3) (154353282481/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 25) (u := 23) (t := 26)
    (D := 8) (ψ := (137461629/2500000000 : ℝ)) half_28_01_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_28_01_bounds3 l).1) (fun l => (half_28_01_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_28_01_total1, half_28_01_total2, half_28_01_total3, half_28_01_total4, half_28_01_total5, half_28_01_total6, half_28_01_total7, half_28_01_total8, half_28_01_total9, half_28_01_total10, half_28_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_24_01) (half_26_01)
    (by simpa only [half_28_01_φ4, show (2:ℝ)*8=16 by norm_num] using half_28_01_hx4)
  exact h.weaken (by norm_num [half_28_01_total1, half_28_01_total2, half_28_01_total3, half_28_01_total4, half_28_01_total5, half_28_01_total6, half_28_01_total7, half_28_01_total8, half_28_01_total9, half_28_01_total10, half_28_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_28_01_hx2 : SourcePowerBound
    (powerBoxCross 16 26 4 half_28_01_φ2) (85915257881/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 26) (u := 24) (t := 27)
    (D := 4) (ψ := (562174661/10000000000 : ℝ)) half_28_01_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_28_01_bounds2 l).1) (fun l => (half_28_01_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_28_01_total1, half_28_01_total2, half_28_01_total3, half_28_01_total4, half_28_01_total5, half_28_01_total6, half_28_01_total7, half_28_01_total8, half_28_01_total9, half_28_01_total10, half_28_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_25_01) (half_27_01)
    (by simpa only [half_28_01_φ3, show (2:ℝ)*4=8 by norm_num] using half_28_01_hx3)
  exact h.weaken (by norm_num [half_28_01_total1, half_28_01_total2, half_28_01_total3, half_28_01_total4, half_28_01_total5, half_28_01_total6, half_28_01_total7, half_28_01_total8, half_28_01_total9, half_28_01_total10, half_28_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_28_01_hx1 : SourcePowerBound
    (powerBoxCross 16 27 2 half_28_01_φ1) (381989910683/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 27) (u := 25) (t := 28)
    (D := 2) (ψ := (141682119/2500000000 : ℝ)) half_28_01_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_28_01_bounds1 l).1) (fun l => (half_28_01_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_28_01_total1, half_28_01_total2, half_28_01_total3, half_28_01_total4, half_28_01_total5, half_28_01_total6, half_28_01_total7, half_28_01_total8, half_28_01_total9, half_28_01_total10, half_28_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_26_01) (chord_71)
    (by simpa only [half_28_01_φ2, show (2:ℝ)*2=4 by norm_num] using half_28_01_hx2)
  exact h.weaken (by norm_num [half_28_01_total1, half_28_01_total2, half_28_01_total3, half_28_01_total4, half_28_01_total5, half_28_01_total6, half_28_01_total7, half_28_01_total8, half_28_01_total9, half_28_01_total10, half_28_01_total11, parameterExponent, curveLoss, dyadicExponent])

theorem half_28_01 : AdmissibleExponent 16 56 (415030063619/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 26) (ψ := (77924889/1250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_27_01)
    (by simpa only [half_28_01_φ1] using half_28_01_hx1)
  exact admissibleExponent_mono h (by norm_num [half_28_01_total1, half_28_01_total2, half_28_01_total3, half_28_01_total4, half_28_01_total5, half_28_01_total6, half_28_01_total7, half_28_01_total8, half_28_01_total9, half_28_01_total10, half_28_01_total11, parameterExponent, curveLoss, dyadicExponent])

theorem chord_73 : AdmissibleExponent 16 58 (54572279557/1250000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 58) (t := (1/2 : ℝ))
    (half_28_01) (half_30_00)
    (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

#print axioms chord_73
end Waring.SeedCompletionAlternate16Seeds
