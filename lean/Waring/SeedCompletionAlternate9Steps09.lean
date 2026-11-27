import Waring.SeedCompletionAlternate9Steps08

noncomputable section
set_option maxHeartbeats 2000000
namespace Waring.SeedCompletionAlternate9Seeds
open SmoothMoments FirstStageTransport SeedCompletionNaturalBox
open SeedCompletionSourceBounds SeedCompletionPaddedSource SeedCompletionGeneralTerminal
open PolicyCompletionMajorPowerRanges SeedCompletionDivisorPowerScales
open PolicyCompletionSharpResidualSource

private def half_15_08_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (510302469/5000000000 : ℝ)

private theorem half_15_08_total1 : total half_15_08_φ1=(510302469/5000000000 : ℝ) := by
  norm_num [half_15_08_φ1,total,emptyPhi,Fin.snoc]

private theorem half_15_08_bounds1 : ∀ l,0≤half_15_08_φ1 l ∧ half_15_08_φ1 l≤1 ∧
    0≤shiftExponents 9 half_15_08_φ1 l :=
  alternate_bounds_snoc emptyPhi (510302469/5000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_15_08_φ2 : Fin 2 → ℝ := Fin.snoc half_15_08_φ1 (247622571/2500000000 : ℝ)

private theorem half_15_08_total2 : total half_15_08_φ2=(1005547611/5000000000 : ℝ) := by
  change total (Fin.snoc half_15_08_φ1 (247622571/2500000000 : ℝ))=(1005547611/5000000000 : ℝ)
  rw [alternate_total_snoc,half_15_08_total1]
  norm_num

private theorem half_15_08_bounds2 : ∀ l,0≤half_15_08_φ2 l ∧ half_15_08_φ2 l≤1 ∧
    0≤shiftExponents 9 half_15_08_φ2 l :=
  alternate_bounds_snoc half_15_08_φ1 (247622571/2500000000 : ℝ) half_15_08_bounds1 (by norm_num)

private def half_15_08_φ3 : Fin 3 → ℝ := Fin.snoc half_15_08_φ2 (950991921/10000000000 : ℝ)

private theorem half_15_08_total3 : total half_15_08_φ3=(2962087143/10000000000 : ℝ) := by
  change total (Fin.snoc half_15_08_φ2 (950991921/10000000000 : ℝ))=(2962087143/10000000000 : ℝ)
  rw [alternate_total_snoc,half_15_08_total2]
  norm_num

private theorem half_15_08_bounds3 : ∀ l,0≤half_15_08_φ3 l ∧ half_15_08_φ3 l≤1 ∧
    0≤shiftExponents 9 half_15_08_φ3 l :=
  alternate_bounds_snoc half_15_08_φ2 (950991921/10000000000 : ℝ) half_15_08_bounds2 (by norm_num)

private def half_15_08_φ4 : Fin 4 → ℝ := Fin.snoc half_15_08_φ3 (439869553/5000000000 : ℝ)

private theorem half_15_08_total4 : total half_15_08_φ4=(3841826249/10000000000 : ℝ) := by
  change total (Fin.snoc half_15_08_φ3 (439869553/5000000000 : ℝ))=(3841826249/10000000000 : ℝ)
  rw [alternate_total_snoc,half_15_08_total3]
  norm_num

private theorem half_15_08_bounds4 : ∀ l,0≤half_15_08_φ4 l ∧ half_15_08_φ4 l≤1 ∧
    0≤shiftExponents 9 half_15_08_φ4 l :=
  alternate_bounds_snoc half_15_08_φ3 (439869553/5000000000 : ℝ) half_15_08_bounds3 (by norm_num)

private def half_15_08_φ5 : Fin 5 → ℝ := Fin.snoc half_15_08_φ4 (384885859/5000000000 : ℝ)

private theorem half_15_08_total5 : total half_15_08_φ5=(4611597967/10000000000 : ℝ) := by
  change total (Fin.snoc half_15_08_φ4 (384885859/5000000000 : ℝ))=(4611597967/10000000000 : ℝ)
  rw [alternate_total_snoc,half_15_08_total4]
  norm_num

private theorem half_15_08_bounds5 : ∀ l,0≤half_15_08_φ5 l ∧ half_15_08_φ5 l≤1 ∧
    0≤shiftExponents 9 half_15_08_φ5 l :=
  alternate_bounds_snoc half_15_08_φ4 (384885859/5000000000 : ℝ) half_15_08_bounds4 (by norm_num)

private def half_15_08_φ6 : Fin 6 → ℝ := Fin.snoc half_15_08_φ5 (21963771/400000000 : ℝ)

private theorem half_15_08_total6 : total half_15_08_φ6=(2580346121/5000000000 : ℝ) := by
  change total (Fin.snoc half_15_08_φ5 (21963771/400000000 : ℝ))=(2580346121/5000000000 : ℝ)
  rw [alternate_total_snoc,half_15_08_total5]
  norm_num

private theorem half_15_08_bounds6 : ∀ l,0≤half_15_08_φ6 l ∧ half_15_08_φ6 l≤1 ∧
    0≤shiftExponents 9 half_15_08_φ6 l :=
  alternate_bounds_snoc half_15_08_φ5 (21963771/400000000 : ℝ) half_15_08_bounds5 (by norm_num)

private theorem half_15_08_prefix : PrefixCondition 9 half_15_08_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_15_08_φ1, half_15_08_φ2, half_15_08_φ3, half_15_08_φ4, half_15_08_φ5, half_15_08_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_15_08_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_15_08_φ6) (4758961637/625000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_15_08_φ6
    (fun i => (half_15_08_bounds6 i).1) (fun i => (half_15_08_bounds6 i).2.1)
    (fun i => (half_15_08_bounds6 i).2.2) half_15_08_prefix
  convert h using 1 <;> norm_num [half_15_08_total1, half_15_08_total2, half_15_08_total3, half_15_08_total4, half_15_08_total5, half_15_08_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_15_08_hx6 : SourcePowerBound
    (powerBoxCross 9 9 64 half_15_08_φ6) (19394577427/2500000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 9) (r := 2) (v := 0) (w := 12) (D := 64)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_15_08_φ6 (by norm_num [half_15_08_total1, half_15_08_total2, half_15_08_total3, half_15_08_total4, half_15_08_total5, half_15_08_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_15_08_total1, half_15_08_total2, half_15_08_total3, half_15_08_total4, half_15_08_total5, half_15_08_total6, parameterExponent, curveLoss, dyadicExponent]) half_15_08_hF2
    (admissibleExponent_zero 9) (half_12_08)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_15_08_total1, half_15_08_total2, half_15_08_total3, half_15_08_total4, half_15_08_total5, half_15_08_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_15_08_hx5 : SourcePowerBound
    (powerBoxCross 9 10 32 half_15_08_φ5) (22208888173/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 10) (u := 8) (t := 11)
    (D := 32) (ψ := (21963771/400000000 : ℝ)) half_15_08_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_15_08_bounds5 l).1) (fun l => (half_15_08_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_15_08_total1, half_15_08_total2, half_15_08_total3, half_15_08_total4, half_15_08_total5, half_15_08_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_9) (half_11_08)
    (by simpa only [half_15_08_φ6, show (2:ℝ)*32=64 by norm_num] using half_15_08_hx6)
  exact h.weaken (by norm_num [half_15_08_total1, half_15_08_total2, half_15_08_total3, half_15_08_total4, half_15_08_total5, half_15_08_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_15_08_hx4 : SourcePowerBound
    (powerBoxCross 9 11 16 half_15_08_φ4) (21205614529/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 11) (u := 9) (t := 12)
    (D := 16) (ψ := (384885859/5000000000 : ℝ)) half_15_08_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_15_08_bounds4 l).1) (fun l => (half_15_08_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_15_08_total1, half_15_08_total2, half_15_08_total3, half_15_08_total4, half_15_08_total5, half_15_08_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_10_08) (half_12_08)
    (by simpa only [half_15_08_φ5, show (2:ℝ)*16=32 by norm_num] using half_15_08_hx5)
  exact h.weaken (by norm_num [half_15_08_total1, half_15_08_total2, half_15_08_total3, half_15_08_total4, half_15_08_total5, half_15_08_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_15_08_hx3 : SourcePowerBound
    (powerBoxCross 9 12 8 half_15_08_φ3) (25676340871/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 12) (u := 10) (t := 13)
    (D := 8) (ψ := (439869553/5000000000 : ℝ)) half_15_08_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_15_08_bounds3 l).1) (fun l => (half_15_08_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_15_08_total1, half_15_08_total2, half_15_08_total3, half_15_08_total4, half_15_08_total5, half_15_08_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_11_08) (half_13_08)
    (by simpa only [half_15_08_φ4, show (2:ℝ)*8=16 by norm_num] using half_15_08_hx4)
  exact h.weaken (by norm_num [half_15_08_total1, half_15_08_total2, half_15_08_total3, half_15_08_total4, half_15_08_total5, half_15_08_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_15_08_hx2 : SourcePowerBound
    (powerBoxCross 9 13 4 half_15_08_φ2) (2434422863/156250000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 13) (u := 11) (t := 14)
    (D := 4) (ψ := (950991921/10000000000 : ℝ)) half_15_08_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_15_08_bounds2 l).1) (fun l => (half_15_08_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_15_08_total1, half_15_08_total2, half_15_08_total3, half_15_08_total4, half_15_08_total5, half_15_08_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_12_08) (half_14_08)
    (by simpa only [half_15_08_φ3, show (2:ℝ)*4=8 by norm_num] using half_15_08_hx3)
  exact h.weaken (by norm_num [half_15_08_total1, half_15_08_total2, half_15_08_total3, half_15_08_total4, half_15_08_total5, half_15_08_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_15_08_hx1 : SourcePowerBound
    (powerBoxCross 9 14 2 half_15_08_φ1) (2937202211/156250000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 14) (u := 12) (t := 15)
    (D := 2) (ψ := (247622571/2500000000 : ℝ)) half_15_08_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_15_08_bounds1 l).1) (fun l => (half_15_08_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_15_08_total1, half_15_08_total2, half_15_08_total3, half_15_08_total4, half_15_08_total5, half_15_08_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_13_08) (half_15_07)
    (by simpa only [half_15_08_φ2, show (2:ℝ)*2=4 by norm_num] using half_15_08_hx2)
  exact h.weaken (by norm_num [half_15_08_total1, half_15_08_total2, half_15_08_total3, half_15_08_total4, half_15_08_total5, half_15_08_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_15_08 : AdmissibleExponent 9 30 (21553727483/1000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 13) (ψ := (510302469/5000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_14_08)
    (by simpa only [half_15_08_φ1] using half_15_08_hx1)
  exact admissibleExponent_mono h (by norm_num [half_15_08_total1, half_15_08_total2, half_15_08_total3, half_15_08_total4, half_15_08_total5, half_15_08_total6, parameterExponent, curveLoss, dyadicExponent])

private def half_16_08_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1040219489/10000000000 : ℝ)

private theorem half_16_08_total1 : total half_16_08_φ1=(1040219489/10000000000 : ℝ) := by
  norm_num [half_16_08_φ1,total,emptyPhi,Fin.snoc]

private theorem half_16_08_bounds1 : ∀ l,0≤half_16_08_φ1 l ∧ half_16_08_φ1 l≤1 ∧
    0≤shiftExponents 9 half_16_08_φ1 l :=
  alternate_bounds_snoc emptyPhi (1040219489/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_16_08_φ2 : Fin 2 → ℝ := Fin.snoc half_16_08_φ1 (253490167/2500000000 : ℝ)

private theorem half_16_08_total2 : total half_16_08_φ2=(2054180157/10000000000 : ℝ) := by
  change total (Fin.snoc half_16_08_φ1 (253490167/2500000000 : ℝ))=(2054180157/10000000000 : ℝ)
  rw [alternate_total_snoc,half_16_08_total1]
  norm_num

private theorem half_16_08_bounds2 : ∀ l,0≤half_16_08_φ2 l ∧ half_16_08_φ2 l≤1 ∧
    0≤shiftExponents 9 half_16_08_φ2 l :=
  alternate_bounds_snoc half_16_08_φ1 (253490167/2500000000 : ℝ) half_16_08_bounds1 (by norm_num)

private def half_16_08_φ3 : Fin 3 → ℝ := Fin.snoc half_16_08_φ2 (122878721/1250000000 : ℝ)

private theorem half_16_08_total3 : total half_16_08_φ3=(121488397/400000000 : ℝ) := by
  change total (Fin.snoc half_16_08_φ2 (122878721/1250000000 : ℝ))=(121488397/400000000 : ℝ)
  rw [alternate_total_snoc,half_16_08_total2]
  norm_num

private theorem half_16_08_bounds3 : ∀ l,0≤half_16_08_φ3 l ∧ half_16_08_φ3 l≤1 ∧
    0≤shiftExponents 9 half_16_08_φ3 l :=
  alternate_bounds_snoc half_16_08_φ2 (122878721/1250000000 : ℝ) half_16_08_bounds2 (by norm_num)

private def half_16_08_φ4 : Fin 4 → ℝ := Fin.snoc half_16_08_φ3 (870348759/10000000000 : ℝ)

private theorem half_16_08_total4 : total half_16_08_φ4=(976889671/2500000000 : ℝ) := by
  change total (Fin.snoc half_16_08_φ3 (870348759/10000000000 : ℝ))=(976889671/2500000000 : ℝ)
  rw [alternate_total_snoc,half_16_08_total3]
  norm_num

private theorem half_16_08_bounds4 : ∀ l,0≤half_16_08_φ4 l ∧ half_16_08_φ4 l≤1 ∧
    0≤shiftExponents 9 half_16_08_φ4 l :=
  alternate_bounds_snoc half_16_08_φ3 (870348759/10000000000 : ℝ) half_16_08_bounds3 (by norm_num)

private def half_16_08_φ5 : Fin 5 → ℝ := Fin.snoc half_16_08_φ4 (190388791/2500000000 : ℝ)

private theorem half_16_08_total5 : total half_16_08_φ5=(583639231/1250000000 : ℝ) := by
  change total (Fin.snoc half_16_08_φ4 (190388791/2500000000 : ℝ))=(583639231/1250000000 : ℝ)
  rw [alternate_total_snoc,half_16_08_total4]
  norm_num

private theorem half_16_08_bounds5 : ∀ l,0≤half_16_08_φ5 l ∧ half_16_08_φ5 l≤1 ∧
    0≤shiftExponents 9 half_16_08_φ5 l :=
  alternate_bounds_snoc half_16_08_φ4 (190388791/2500000000 : ℝ) half_16_08_bounds4 (by norm_num)

private def half_16_08_φ6 : Fin 6 → ℝ := Fin.snoc half_16_08_φ5 (131790967/2000000000 : ℝ)

private theorem half_16_08_total6 : total half_16_08_φ6=(5328068683/10000000000 : ℝ) := by
  change total (Fin.snoc half_16_08_φ5 (131790967/2000000000 : ℝ))=(5328068683/10000000000 : ℝ)
  rw [alternate_total_snoc,half_16_08_total5]
  norm_num

private theorem half_16_08_bounds6 : ∀ l,0≤half_16_08_φ6 l ∧ half_16_08_φ6 l≤1 ∧
    0≤shiftExponents 9 half_16_08_φ6 l :=
  alternate_bounds_snoc half_16_08_φ5 (131790967/2000000000 : ℝ) half_16_08_bounds5 (by norm_num)

private theorem half_16_08_prefix : PrefixCondition 9 half_16_08_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_16_08_φ1, half_16_08_φ2, half_16_08_φ3, half_16_08_φ4, half_16_08_φ5, half_16_08_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_16_08_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_16_08_φ6) (9015793951/1250000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_16_08_φ6
    (fun i => (half_16_08_bounds6 i).1) (fun i => (half_16_08_bounds6 i).2.1)
    (fun i => (half_16_08_bounds6 i).2.2) half_16_08_prefix
  convert h using 1 <;> norm_num [half_16_08_total1, half_16_08_total2, half_16_08_total3, half_16_08_total4, half_16_08_total5, half_16_08_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_16_08_hx6 : SourcePowerBound
    (powerBoxCross 9 10 64 half_16_08_φ6) (41428120061/5000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 10) (r := 2) (v := 13) (w := 14) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_16_08_φ6 (by norm_num [half_16_08_total1, half_16_08_total2, half_16_08_total3, half_16_08_total4, half_16_08_total5, half_16_08_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_16_08_total1, half_16_08_total2, half_16_08_total3, half_16_08_total4, half_16_08_total5, half_16_08_total6, parameterExponent, curveLoss, dyadicExponent]) half_16_08_hF2
    (half_13_08) (half_14_08)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_16_08_total1, half_16_08_total2, half_16_08_total3, half_16_08_total4, half_16_08_total5, half_16_08_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_16_08_hx5 : SourcePowerBound
    (powerBoxCross 9 11 32 half_16_08_φ5) (48502276087/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 11) (u := 9) (t := 12)
    (D := 32) (ψ := (131790967/2000000000 : ℝ)) half_16_08_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_16_08_bounds5 l).1) (fun l => (half_16_08_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_16_08_total1, half_16_08_total2, half_16_08_total3, half_16_08_total4, half_16_08_total5, half_16_08_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_10_08) (half_12_08)
    (by simpa only [half_16_08_φ6, show (2:ℝ)*32=64 by norm_num] using half_16_08_hx6)
  exact h.weaken (by norm_num [half_16_08_total1, half_16_08_total2, half_16_08_total3, half_16_08_total4, half_16_08_total5, half_16_08_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_16_08_hx4 : SourcePowerBound
    (powerBoxCross 9 12 16 half_16_08_φ4) (14423321931/1250000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 12) (u := 10) (t := 13)
    (D := 16) (ψ := (190388791/2500000000 : ℝ)) half_16_08_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_16_08_bounds4 l).1) (fun l => (half_16_08_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_16_08_total1, half_16_08_total2, half_16_08_total3, half_16_08_total4, half_16_08_total5, half_16_08_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_11_08) (half_13_08)
    (by simpa only [half_16_08_φ5, show (2:ℝ)*16=32 by norm_num] using half_16_08_hx5)
  exact h.weaken (by norm_num [half_16_08_total1, half_16_08_total2, half_16_08_total3, half_16_08_total4, half_16_08_total5, half_16_08_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_16_08_hx3 : SourcePowerBound
    (powerBoxCross 9 13 8 half_16_08_φ3) (139162628221/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 13) (u := 11) (t := 14)
    (D := 8) (ψ := (870348759/10000000000 : ℝ)) half_16_08_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_16_08_bounds3 l).1) (fun l => (half_16_08_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_16_08_total1, half_16_08_total2, half_16_08_total3, half_16_08_total4, half_16_08_total5, half_16_08_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_12_08) (half_14_08)
    (by simpa only [half_16_08_φ4, show (2:ℝ)*8=16 by norm_num] using half_16_08_hx4)
  exact h.weaken (by norm_num [half_16_08_total1, half_16_08_total2, half_16_08_total3, half_16_08_total4, half_16_08_total5, half_16_08_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_16_08_hx2 : SourcePowerBound
    (powerBoxCross 9 14 4 half_16_08_φ2) (84641741673/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 14) (u := 12) (t := 15)
    (D := 4) (ψ := (122878721/1250000000 : ℝ)) half_16_08_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_16_08_bounds2 l).1) (fun l => (half_16_08_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_16_08_total1, half_16_08_total2, half_16_08_total3, half_16_08_total4, half_16_08_total5, half_16_08_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_13_08) (half_15_08)
    (by simpa only [half_16_08_φ3, show (2:ℝ)*4=8 by norm_num] using half_16_08_hx3)
  exact h.weaken (by norm_num [half_16_08_total1, half_16_08_total2, half_16_08_total3, half_16_08_total4, half_16_08_total5, half_16_08_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_16_08_hx1 : SourcePowerBound
    (powerBoxCross 9 15 2 half_16_08_φ1) (204156886941/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 15) (u := 13) (t := 16)
    (D := 2) (ψ := (253490167/2500000000 : ℝ)) half_16_08_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_16_08_bounds1 l).1) (fun l => (half_16_08_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_16_08_total1, half_16_08_total2, half_16_08_total3, half_16_08_total4, half_16_08_total5, half_16_08_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_14_08) (half_16_07)
    (by simpa only [half_16_08_φ2, show (2:ℝ)*2=4 by norm_num] using half_16_08_hx2)
  exact h.weaken (by norm_num [half_16_08_total1, half_16_08_total2, half_16_08_total3, half_16_08_total4, half_16_08_total5, half_16_08_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_16_08 : AdmissibleExponent 9 32 (117161626061/5000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 14) (ψ := (1040219489/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_15_08)
    (by simpa only [half_16_08_φ1] using half_16_08_hx1)
  exact admissibleExponent_mono h (by norm_num [half_16_08_total1, half_16_08_total2, half_16_08_total3, half_16_08_total4, half_16_08_total5, half_16_08_total6, parameterExponent, curveLoss, dyadicExponent])

private def half_17_08_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1056669279/10000000000 : ℝ)

private theorem half_17_08_total1 : total half_17_08_φ1=(1056669279/10000000000 : ℝ) := by
  norm_num [half_17_08_φ1,total,emptyPhi,Fin.snoc]

private theorem half_17_08_bounds1 : ∀ l,0≤half_17_08_φ1 l ∧ half_17_08_φ1 l≤1 ∧
    0≤shiftExponents 9 half_17_08_φ1 l :=
  alternate_bounds_snoc emptyPhi (1056669279/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_17_08_φ2 : Fin 2 → ℝ := Fin.snoc half_17_08_φ1 (207216027/2000000000 : ℝ)

private theorem half_17_08_total2 : total half_17_08_φ2=(1046374707/5000000000 : ℝ) := by
  change total (Fin.snoc half_17_08_φ1 (207216027/2000000000 : ℝ))=(1046374707/5000000000 : ℝ)
  rw [alternate_total_snoc,half_17_08_total1]
  norm_num

private theorem half_17_08_bounds2 : ∀ l,0≤half_17_08_φ2 l ∧ half_17_08_φ2 l≤1 ∧
    0≤shiftExponents 9 half_17_08_φ2 l :=
  alternate_bounds_snoc half_17_08_φ1 (207216027/2000000000 : ℝ) half_17_08_bounds1 (by norm_num)

private def half_17_08_φ3 : Fin 3 → ℝ := Fin.snoc half_17_08_φ2 (988406323/10000000000 : ℝ)

private theorem half_17_08_total3 : total half_17_08_φ3=(3081155737/10000000000 : ℝ) := by
  change total (Fin.snoc half_17_08_φ2 (988406323/10000000000 : ℝ))=(3081155737/10000000000 : ℝ)
  rw [alternate_total_snoc,half_17_08_total2]
  norm_num

private theorem half_17_08_bounds3 : ∀ l,0≤half_17_08_φ3 l ∧ half_17_08_φ3 l≤1 ∧
    0≤shiftExponents 9 half_17_08_φ3 l :=
  alternate_bounds_snoc half_17_08_φ2 (988406323/10000000000 : ℝ) half_17_08_bounds2 (by norm_num)

private def half_17_08_φ4 : Fin 4 → ℝ := Fin.snoc half_17_08_φ3 (216213883/2500000000 : ℝ)

private theorem half_17_08_total4 : total half_17_08_φ4=(3946011269/10000000000 : ℝ) := by
  change total (Fin.snoc half_17_08_φ3 (216213883/2500000000 : ℝ))=(3946011269/10000000000 : ℝ)
  rw [alternate_total_snoc,half_17_08_total3]
  norm_num

private theorem half_17_08_bounds4 : ∀ l,0≤half_17_08_φ4 l ∧ half_17_08_φ4 l≤1 ∧
    0≤shiftExponents 9 half_17_08_φ4 l :=
  alternate_bounds_snoc half_17_08_φ3 (216213883/2500000000 : ℝ) half_17_08_bounds3 (by norm_num)

private def half_17_08_φ5 : Fin 5 → ℝ := Fin.snoc half_17_08_φ4 (756748591/10000000000 : ℝ)

private theorem half_17_08_total5 : total half_17_08_φ5=(235137993/500000000 : ℝ) := by
  change total (Fin.snoc half_17_08_φ4 (756748591/10000000000 : ℝ))=(235137993/500000000 : ℝ)
  rw [alternate_total_snoc,half_17_08_total4]
  norm_num

private theorem half_17_08_bounds5 : ∀ l,0≤half_17_08_φ5 l ∧ half_17_08_φ5 l≤1 ∧
    0≤shiftExponents 9 half_17_08_φ5 l :=
  alternate_bounds_snoc half_17_08_φ4 (756748591/10000000000 : ℝ) half_17_08_bounds4 (by norm_num)

private def half_17_08_φ6 : Fin 6 → ℝ := Fin.snoc half_17_08_φ5 (662155017/10000000000 : ℝ)

private theorem half_17_08_total6 : total half_17_08_φ6=(5364914877/10000000000 : ℝ) := by
  change total (Fin.snoc half_17_08_φ5 (662155017/10000000000 : ℝ))=(5364914877/10000000000 : ℝ)
  rw [alternate_total_snoc,half_17_08_total5]
  norm_num

private theorem half_17_08_bounds6 : ∀ l,0≤half_17_08_φ6 l ∧ half_17_08_φ6 l≤1 ∧
    0≤shiftExponents 9 half_17_08_φ6 l :=
  alternate_bounds_snoc half_17_08_φ5 (662155017/10000000000 : ℝ) half_17_08_bounds5 (by norm_num)

private theorem half_17_08_prefix : PrefixCondition 9 half_17_08_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_17_08_φ1, half_17_08_φ2, half_17_08_φ3, half_17_08_φ4, half_17_08_φ5, half_17_08_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_17_08_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_17_08_φ6) (8905255369/1250000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_17_08_φ6
    (fun i => (half_17_08_bounds6 i).1) (fun i => (half_17_08_bounds6 i).2.1)
    (fun i => (half_17_08_bounds6 i).2.2) half_17_08_prefix
  convert h using 1 <;> norm_num [half_17_08_total1, half_17_08_total2, half_17_08_total3, half_17_08_total4, half_17_08_total5, half_17_08_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_17_08_hx6 : SourcePowerBound
    (powerBoxCross 9 11 64 half_17_08_φ6) (90598535683/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 11) (r := 2) (v := 14) (w := 15) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_17_08_φ6 (by norm_num [half_17_08_total1, half_17_08_total2, half_17_08_total3, half_17_08_total4, half_17_08_total5, half_17_08_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_17_08_total1, half_17_08_total2, half_17_08_total3, half_17_08_total4, half_17_08_total5, half_17_08_total6, parameterExponent, curveLoss, dyadicExponent]) half_17_08_hF2
    (half_14_08) (half_15_08)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_17_08_total1, half_17_08_total2, half_17_08_total3, half_17_08_total4, half_17_08_total5, half_17_08_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_17_08_hx5 : SourcePowerBound
    (powerBoxCross 9 12 32 half_17_08_φ5) (105843204047/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 12) (u := 10) (t := 13)
    (D := 32) (ψ := (662155017/10000000000 : ℝ)) half_17_08_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_17_08_bounds5 l).1) (fun l => (half_17_08_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_17_08_total1, half_17_08_total2, half_17_08_total3, half_17_08_total4, half_17_08_total5, half_17_08_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_11_08) (half_13_08)
    (by simpa only [half_17_08_φ6, show (2:ℝ)*32=64 by norm_num] using half_17_08_hx6)
  exact h.weaken (by norm_num [half_17_08_total1, half_17_08_total2, half_17_08_total3, half_17_08_total4, half_17_08_total5, half_17_08_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_17_08_hx4 : SourcePowerBound
    (powerBoxCross 9 13 16 half_17_08_φ4) (125494289211/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 13) (u := 11) (t := 14)
    (D := 16) (ψ := (756748591/10000000000 : ℝ)) half_17_08_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_17_08_bounds4 l).1) (fun l => (half_17_08_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_17_08_total1, half_17_08_total2, half_17_08_total3, half_17_08_total4, half_17_08_total5, half_17_08_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_12_08) (half_14_08)
    (by simpa only [half_17_08_φ5, show (2:ℝ)*16=32 by norm_num] using half_17_08_hx5)
  exact h.weaken (by norm_num [half_17_08_total1, half_17_08_total2, half_17_08_total3, half_17_08_total4, half_17_08_total5, half_17_08_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_17_08_hx3 : SourcePowerBound
    (powerBoxCross 9 14 8 half_17_08_φ3) (150796657679/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 14) (u := 12) (t := 15)
    (D := 8) (ψ := (216213883/2500000000 : ℝ)) half_17_08_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_17_08_bounds3 l).1) (fun l => (half_17_08_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_17_08_total1, half_17_08_total2, half_17_08_total3, half_17_08_total4, half_17_08_total5, half_17_08_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_13_08) (half_15_08)
    (by simpa only [half_17_08_φ4, show (2:ℝ)*8=16 by norm_num] using half_17_08_hx4)
  exact h.weaken (by norm_num [half_17_08_total1, half_17_08_total2, half_17_08_total3, half_17_08_total4, half_17_08_total5, half_17_08_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_17_08_hx2 : SourcePowerBound
    (powerBoxCross 9 15 4 half_17_08_φ2) (183013450177/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 15) (u := 13) (t := 16)
    (D := 4) (ψ := (988406323/10000000000 : ℝ)) half_17_08_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_17_08_bounds2 l).1) (fun l => (half_17_08_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_17_08_total1, half_17_08_total2, half_17_08_total3, half_17_08_total4, half_17_08_total5, half_17_08_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_14_08) (half_16_08)
    (by simpa only [half_17_08_φ3, show (2:ℝ)*4=8 by norm_num] using half_17_08_hx3)
  exact h.weaken (by norm_num [half_17_08_total1, half_17_08_total2, half_17_08_total3, half_17_08_total4, half_17_08_total5, half_17_08_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_17_08_hx1 : SourcePowerBound
    (powerBoxCross 9 16 2 half_17_08_φ1) (110309851609/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 16) (u := 14) (t := 17)
    (D := 2) (ψ := (207216027/2000000000 : ℝ)) half_17_08_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_17_08_bounds1 l).1) (fun l => (half_17_08_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_17_08_total1, half_17_08_total2, half_17_08_total3, half_17_08_total4, half_17_08_total5, half_17_08_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_15_08) (half_17_07)
    (by simpa only [half_17_08_φ2, show (2:ℝ)*2=4 by norm_num] using half_17_08_hx2)
  exact h.weaken (by norm_num [half_17_08_total1, half_17_08_total2, half_17_08_total3, half_17_08_total4, half_17_08_total5, half_17_08_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_17_08 : AdmissibleExponent 9 34 (253376450867/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 15) (ψ := (1056669279/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_16_08)
    (by simpa only [half_17_08_φ1] using half_17_08_hx1)
  exact admissibleExponent_mono h (by norm_num [half_17_08_total1, half_17_08_total2, half_17_08_total3, half_17_08_total4, half_17_08_total5, half_17_08_total6, parameterExponent, curveLoss, dyadicExponent])

private def half_18_08_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1069480353/10000000000 : ℝ)

private theorem half_18_08_total1 : total half_18_08_φ1=(1069480353/10000000000 : ℝ) := by
  norm_num [half_18_08_φ1,total,emptyPhi,Fin.snoc]

private theorem half_18_08_bounds1 : ∀ l,0≤half_18_08_φ1 l ∧ half_18_08_φ1 l≤1 ∧
    0≤shiftExponents 9 half_18_08_φ1 l :=
  alternate_bounds_snoc emptyPhi (1069480353/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_18_08_φ2 : Fin 2 → ℝ := Fin.snoc half_18_08_φ1 (210795661/2000000000 : ℝ)

private theorem half_18_08_total2 : total half_18_08_φ2=(1061729329/5000000000 : ℝ) := by
  change total (Fin.snoc half_18_08_φ1 (210795661/2000000000 : ℝ))=(1061729329/5000000000 : ℝ)
  rw [alternate_total_snoc,half_18_08_total1]
  norm_num

private theorem half_18_08_bounds2 : ∀ l,0≤half_18_08_φ2 l ∧ half_18_08_φ2 l≤1 ∧
    0≤shiftExponents 9 half_18_08_φ2 l :=
  alternate_bounds_snoc half_18_08_φ1 (210795661/2000000000 : ℝ) half_18_08_bounds1 (by norm_num)

private def half_18_08_φ3 : Fin 3 → ℝ := Fin.snoc half_18_08_φ2 (984567667/10000000000 : ℝ)

private theorem half_18_08_total3 : total half_18_08_φ3=(124321053/400000000 : ℝ) := by
  change total (Fin.snoc half_18_08_φ2 (984567667/10000000000 : ℝ))=(124321053/400000000 : ℝ)
  rw [alternate_total_snoc,half_18_08_total2]
  norm_num

private theorem half_18_08_bounds3 : ∀ l,0≤half_18_08_φ3 l ∧ half_18_08_φ3 l≤1 ∧
    0≤shiftExponents 9 half_18_08_φ3 l :=
  alternate_bounds_snoc half_18_08_φ2 (984567667/10000000000 : ℝ) half_18_08_bounds2 (by norm_num)

private def half_18_08_φ4 : Fin 4 → ℝ := Fin.snoc half_18_08_φ3 (861496709/10000000000 : ℝ)

private theorem half_18_08_total4 : total half_18_08_φ4=(1984761517/5000000000 : ℝ) := by
  change total (Fin.snoc half_18_08_φ3 (861496709/10000000000 : ℝ))=(1984761517/5000000000 : ℝ)
  rw [alternate_total_snoc,half_18_08_total3]
  norm_num

private theorem half_18_08_bounds4 : ∀ l,0≤half_18_08_φ4 l ∧ half_18_08_φ4 l≤1 ∧
    0≤shiftExponents 9 half_18_08_φ4 l :=
  alternate_bounds_snoc half_18_08_φ3 (861496709/10000000000 : ℝ) half_18_08_bounds3 (by norm_num)

private def half_18_08_φ5 : Fin 5 → ℝ := Fin.snoc half_18_08_φ4 (37690481/500000000 : ℝ)

private theorem half_18_08_total5 : total half_18_08_φ5=(2361666327/5000000000 : ℝ) := by
  change total (Fin.snoc half_18_08_φ4 (37690481/500000000 : ℝ))=(2361666327/5000000000 : ℝ)
  rw [alternate_total_snoc,half_18_08_total4]
  norm_num

private theorem half_18_08_bounds5 : ∀ l,0≤half_18_08_φ5 l ∧ half_18_08_φ5 l≤1 ∧
    0≤shiftExponents 9 half_18_08_φ5 l :=
  alternate_bounds_snoc half_18_08_φ4 (37690481/500000000 : ℝ) half_18_08_bounds4 (by norm_num)

private def half_18_08_φ6 : Fin 6 → ℝ := Fin.snoc half_18_08_φ5 (659583417/10000000000 : ℝ)

private theorem half_18_08_total6 : total half_18_08_φ6=(5382916071/10000000000 : ℝ) := by
  change total (Fin.snoc half_18_08_φ5 (659583417/10000000000 : ℝ))=(5382916071/10000000000 : ℝ)
  rw [alternate_total_snoc,half_18_08_total5]
  norm_num

private theorem half_18_08_bounds6 : ∀ l,0≤half_18_08_φ6 l ∧ half_18_08_φ6 l≤1 ∧
    0≤shiftExponents 9 half_18_08_φ6 l :=
  alternate_bounds_snoc half_18_08_φ5 (659583417/10000000000 : ℝ) half_18_08_bounds5 (by norm_num)

private theorem half_18_08_prefix : PrefixCondition 9 half_18_08_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_18_08_φ1, half_18_08_φ2, half_18_08_φ3, half_18_08_φ4, half_18_08_φ5, half_18_08_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_18_08_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_18_08_φ6) (8851251787/1250000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_18_08_φ6
    (fun i => (half_18_08_bounds6 i).1) (fun i => (half_18_08_bounds6 i).2.1)
    (fun i => (half_18_08_bounds6 i).2.2) half_18_08_prefix
  convert h using 1 <;> norm_num [half_18_08_total1, half_18_08_total2, half_18_08_total3, half_18_08_total4, half_18_08_total5, half_18_08_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_18_08_hx6 : SourcePowerBound
    (powerBoxCross 9 12 64 half_18_08_φ6) (24711065673/2500000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 12) (r := 2) (v := 0) (w := 16) (D := 64)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_18_08_φ6 (by norm_num [half_18_08_total1, half_18_08_total2, half_18_08_total3, half_18_08_total4, half_18_08_total5, half_18_08_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_18_08_total1, half_18_08_total2, half_18_08_total3, half_18_08_total4, half_18_08_total5, half_18_08_total6, parameterExponent, curveLoss, dyadicExponent]) half_18_08_hF2
    (admissibleExponent_zero 9) (half_16_08)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_18_08_total1, half_18_08_total2, half_18_08_total3, half_18_08_total4, half_18_08_total5, half_18_08_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_18_08_hx5 : SourcePowerBound
    (powerBoxCross 9 13 32 half_18_08_φ5) (3597145317/312500000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 13) (u := 11) (t := 14)
    (D := 32) (ψ := (659583417/10000000000 : ℝ)) half_18_08_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_18_08_bounds5 l).1) (fun l => (half_18_08_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_18_08_total1, half_18_08_total2, half_18_08_total3, half_18_08_total4, half_18_08_total5, half_18_08_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_12_08) (half_14_08)
    (by simpa only [half_18_08_φ6, show (2:ℝ)*32=64 by norm_num] using half_18_08_hx6)
  exact h.weaken (by norm_num [half_18_08_total1, half_18_08_total2, half_18_08_total3, half_18_08_total4, half_18_08_total5, half_18_08_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_18_08_hx4 : SourcePowerBound
    (powerBoxCross 9 14 16 half_18_08_φ4) (27217696349/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 14) (u := 12) (t := 15)
    (D := 16) (ψ := (37690481/500000000 : ℝ)) half_18_08_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_18_08_bounds4 l).1) (fun l => (half_18_08_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_18_08_total1, half_18_08_total2, half_18_08_total3, half_18_08_total4, half_18_08_total5, half_18_08_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_13_08) (half_15_08)
    (by simpa only [half_18_08_φ5, show (2:ℝ)*16=32 by norm_num] using half_18_08_hx5)
  exact h.weaken (by norm_num [half_18_08_total1, half_18_08_total2, half_18_08_total3, half_18_08_total4, half_18_08_total5, half_18_08_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_18_08_hx3 : SourcePowerBound
    (powerBoxCross 9 15 8 half_18_08_φ3) (81494912699/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 15) (u := 13) (t := 16)
    (D := 8) (ψ := (861496709/10000000000 : ℝ)) half_18_08_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_18_08_bounds3 l).1) (fun l => (half_18_08_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_18_08_total1, half_18_08_total2, half_18_08_total3, half_18_08_total4, half_18_08_total5, half_18_08_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_14_08) (half_16_08)
    (by simpa only [half_18_08_φ4, show (2:ℝ)*8=16 by norm_num] using half_18_08_hx4)
  exact h.weaken (by norm_num [half_18_08_total1, half_18_08_total2, half_18_08_total3, half_18_08_total4, half_18_08_total5, half_18_08_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_18_08_hx2 : SourcePowerBound
    (powerBoxCross 9 16 4 half_18_08_φ2) (49265953439/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 16) (u := 14) (t := 17)
    (D := 4) (ψ := (984567667/10000000000 : ℝ)) half_18_08_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_18_08_bounds2 l).1) (fun l => (half_18_08_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_18_08_total1, half_18_08_total2, half_18_08_total3, half_18_08_total4, half_18_08_total5, half_18_08_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_15_08) (half_17_08)
    (by simpa only [half_18_08_φ3, show (2:ℝ)*4=8 by norm_num] using half_18_08_hx3)
  exact h.weaken (by norm_num [half_18_08_total1, half_18_08_total2, half_18_08_total3, half_18_08_total4, half_18_08_total5, half_18_08_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_18_08_hx1 : SourcePowerBound
    (powerBoxCross 9 17 2 half_18_08_φ1) (118673908807/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 17) (u := 15) (t := 18)
    (D := 2) (ψ := (210795661/2000000000 : ℝ)) half_18_08_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_18_08_bounds1 l).1) (fun l => (half_18_08_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_18_08_total1, half_18_08_total2, half_18_08_total3, half_18_08_total4, half_18_08_total5, half_18_08_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_16_08) (half_18_07)
    (by simpa only [half_18_08_φ2, show (2:ℝ)*2=4 by norm_num] using half_18_08_hx2)
  exact h.weaken (by norm_num [half_18_08_total1, half_18_08_total2, half_18_08_total3, half_18_08_total4, half_18_08_total5, half_18_08_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_18_08 : AdmissibleExponent 9 36 (272640669263/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 16) (ψ := (1069480353/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_17_08)
    (by simpa only [half_18_08_φ1] using half_18_08_hx1)
  exact admissibleExponent_mono h (by norm_num [half_18_08_total1, half_18_08_total2, half_18_08_total3, half_18_08_total4, half_18_08_total5, half_18_08_total6, parameterExponent, curveLoss, dyadicExponent])

private def half_19_08_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (134956721/1250000000 : ℝ)

private theorem half_19_08_total1 : total half_19_08_φ1=(134956721/1250000000 : ℝ) := by
  norm_num [half_19_08_φ1,total,emptyPhi,Fin.snoc]

private theorem half_19_08_bounds1 : ∀ l,0≤half_19_08_φ1 l ∧ half_19_08_φ1 l≤1 ∧
    0≤shiftExponents 9 half_19_08_φ1 l :=
  alternate_bounds_snoc emptyPhi (134956721/1250000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_19_08_φ2 : Fin 2 → ℝ := Fin.snoc half_19_08_φ1 (1067984623/10000000000 : ℝ)

private theorem half_19_08_total2 : total half_19_08_φ2=(2147638391/10000000000 : ℝ) := by
  change total (Fin.snoc half_19_08_φ1 (1067984623/10000000000 : ℝ))=(2147638391/10000000000 : ℝ)
  rw [alternate_total_snoc,half_19_08_total1]
  norm_num

private theorem half_19_08_bounds2 : ∀ l,0≤half_19_08_φ2 l ∧ half_19_08_φ2 l≤1 ∧
    0≤shiftExponents 9 half_19_08_φ2 l :=
  alternate_bounds_snoc half_19_08_φ1 (1067984623/10000000000 : ℝ) half_19_08_bounds1 (by norm_num)

private def half_19_08_φ3 : Fin 3 → ℝ := Fin.snoc half_19_08_φ2 (2453863/25000000 : ℝ)

private theorem half_19_08_total3 : total half_19_08_φ3=(3129183591/10000000000 : ℝ) := by
  change total (Fin.snoc half_19_08_φ2 (2453863/25000000 : ℝ))=(3129183591/10000000000 : ℝ)
  rw [alternate_total_snoc,half_19_08_total2]
  norm_num

private theorem half_19_08_bounds3 : ∀ l,0≤half_19_08_φ3 l ∧ half_19_08_φ3 l≤1 ∧
    0≤shiftExponents 9 half_19_08_φ3 l :=
  alternate_bounds_snoc half_19_08_φ2 (2453863/25000000 : ℝ) half_19_08_bounds2 (by norm_num)

private def half_19_08_φ4 : Fin 4 → ℝ := Fin.snoc half_19_08_φ3 (17177041/200000000 : ℝ)

private theorem half_19_08_total4 : total half_19_08_φ4=(3988035641/10000000000 : ℝ) := by
  change total (Fin.snoc half_19_08_φ3 (17177041/200000000 : ℝ))=(3988035641/10000000000 : ℝ)
  rw [alternate_total_snoc,half_19_08_total3]
  norm_num

private theorem half_19_08_bounds4 : ∀ l,0≤half_19_08_φ4 l ∧ half_19_08_φ4 l≤1 ∧
    0≤shiftExponents 9 half_19_08_φ4 l :=
  alternate_bounds_snoc half_19_08_φ3 (17177041/200000000 : ℝ) half_19_08_bounds3 (by norm_num)

private def half_19_08_φ5 : Fin 5 → ℝ := Fin.snoc half_19_08_φ4 (93936943/1250000000 : ℝ)

private theorem half_19_08_total5 : total half_19_08_φ5=(947906237/2000000000 : ℝ) := by
  change total (Fin.snoc half_19_08_φ4 (93936943/1250000000 : ℝ))=(947906237/2000000000 : ℝ)
  rw [alternate_total_snoc,half_19_08_total4]
  norm_num

private theorem half_19_08_bounds5 : ∀ l,0≤half_19_08_φ5 l ∧ half_19_08_φ5 l≤1 ∧
    0≤shiftExponents 9 half_19_08_φ5 l :=
  alternate_bounds_snoc half_19_08_φ4 (93936943/1250000000 : ℝ) half_19_08_bounds4 (by norm_num)

private def half_19_08_φ6 : Fin 6 → ℝ := Fin.snoc half_19_08_φ5 (657558601/10000000000 : ℝ)

private theorem half_19_08_total6 : total half_19_08_φ6=(2698544893/5000000000 : ℝ) := by
  change total (Fin.snoc half_19_08_φ5 (657558601/10000000000 : ℝ))=(2698544893/5000000000 : ℝ)
  rw [alternate_total_snoc,half_19_08_total5]
  norm_num

private theorem half_19_08_bounds6 : ∀ l,0≤half_19_08_φ6 l ∧ half_19_08_φ6 l≤1 ∧
    0≤shiftExponents 9 half_19_08_φ6 l :=
  alternate_bounds_snoc half_19_08_φ5 (657558601/10000000000 : ℝ) half_19_08_bounds5 (by norm_num)

private theorem half_19_08_prefix : PrefixCondition 9 half_19_08_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_19_08_φ1, half_19_08_φ2, half_19_08_φ3, half_19_08_φ4, half_19_08_φ5, half_19_08_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_19_08_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_19_08_φ6) (4404365321/625000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_19_08_φ6
    (fun i => (half_19_08_bounds6 i).1) (fun i => (half_19_08_bounds6 i).2.1)
    (fun i => (half_19_08_bounds6 i).2.2) half_19_08_prefix
  convert h using 1 <;> norm_num [half_19_08_total1, half_19_08_total2, half_19_08_total3, half_19_08_total4, half_19_08_total5, half_19_08_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_19_08_hx6 : SourcePowerBound
    (powerBoxCross 9 13 64 half_19_08_φ6) (107304427001/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 13) (r := 2) (v := 17) (w := 18) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_19_08_φ6 (by norm_num [half_19_08_total1, half_19_08_total2, half_19_08_total3, half_19_08_total4, half_19_08_total5, half_19_08_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_19_08_total1, half_19_08_total2, half_19_08_total3, half_19_08_total4, half_19_08_total5, half_19_08_total6, parameterExponent, curveLoss, dyadicExponent]) half_19_08_hF2
    (half_17_08) (half_18_08)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_19_08_total1, half_19_08_total2, half_19_08_total3, half_19_08_total4, half_19_08_total5, half_19_08_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_19_08_hx5 : SourcePowerBound
    (powerBoxCross 9 14 32 half_19_08_φ5) (124604926909/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 14) (u := 12) (t := 15)
    (D := 32) (ψ := (657558601/10000000000 : ℝ)) half_19_08_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_19_08_bounds5 l).1) (fun l => (half_19_08_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_19_08_total1, half_19_08_total2, half_19_08_total3, half_19_08_total4, half_19_08_total5, half_19_08_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_13_08) (half_15_08)
    (by simpa only [half_19_08_φ6, show (2:ℝ)*32=64 by norm_num] using half_19_08_hx6)
  exact h.weaken (by norm_num [half_19_08_total1, half_19_08_total2, half_19_08_total3, half_19_08_total4, half_19_08_total5, half_19_08_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_19_08_hx4 : SourcePowerBound
    (powerBoxCross 9 15 16 half_19_08_φ4) (146932662747/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 15) (u := 13) (t := 16)
    (D := 16) (ψ := (93936943/1250000000 : ℝ)) half_19_08_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_19_08_bounds4 l).1) (fun l => (half_19_08_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_19_08_total1, half_19_08_total2, half_19_08_total3, half_19_08_total4, half_19_08_total5, half_19_08_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_14_08) (half_16_08)
    (by simpa only [half_19_08_φ5, show (2:ℝ)*16=32 by norm_num] using half_19_08_hx5)
  exact h.weaken (by norm_num [half_19_08_total1, half_19_08_total2, half_19_08_total3, half_19_08_total4, half_19_08_total5, half_19_08_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_19_08_hx3 : SourcePowerBound
    (powerBoxCross 9 16 8 half_19_08_φ3) (175448105549/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 16) (u := 14) (t := 17)
    (D := 8) (ψ := (17177041/200000000 : ℝ)) half_19_08_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_19_08_bounds3 l).1) (fun l => (half_19_08_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_19_08_total1, half_19_08_total2, half_19_08_total3, half_19_08_total4, half_19_08_total5, half_19_08_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_15_08) (half_17_08)
    (by simpa only [half_19_08_φ4, show (2:ℝ)*8=16 by norm_num] using half_19_08_hx4)
  exact h.weaken (by norm_num [half_19_08_total1, half_19_08_total2, half_19_08_total3, half_19_08_total4, half_19_08_total5, half_19_08_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_19_08_hx2 : SourcePowerBound
    (powerBoxCross 9 17 4 half_19_08_φ2) (21139110603/1000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 17) (u := 15) (t := 18)
    (D := 4) (ψ := (2453863/25000000 : ℝ)) half_19_08_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_19_08_bounds2 l).1) (fun l => (half_19_08_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_19_08_total1, half_19_08_total2, half_19_08_total3, half_19_08_total4, half_19_08_total5, half_19_08_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_16_08) (half_18_08)
    (by simpa only [half_19_08_φ3, show (2:ℝ)*4=8 by norm_num] using half_19_08_hx3)
  exact h.weaken (by norm_num [half_19_08_total1, half_19_08_total2, half_19_08_total3, half_19_08_total4, half_19_08_total5, half_19_08_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_19_08_hx1 : SourcePowerBound
    (powerBoxCross 9 18 2 half_19_08_φ1) (254284570451/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 18) (u := 16) (t := 19)
    (D := 2) (ψ := (1067984623/10000000000 : ℝ)) half_19_08_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_19_08_bounds1 l).1) (fun l => (half_19_08_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_19_08_total1, half_19_08_total2, half_19_08_total3, half_19_08_total4, half_19_08_total5, half_19_08_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_17_08) (half_19_07)
    (by simpa only [half_19_08_φ2, show (2:ℝ)*2=4 by norm_num] using half_19_08_hx2)
  exact h.weaken (by norm_num [half_19_08_total1, half_19_08_total2, half_19_08_total3, half_19_08_total4, half_19_08_total5, half_19_08_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_19_08 : AdmissibleExponent 9 38 (292072452331/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 17) (ψ := (134956721/1250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_18_08)
    (by simpa only [half_19_08_φ1] using half_19_08_hx1)
  exact admissibleExponent_mono h (by norm_num [half_19_08_total1, half_19_08_total2, half_19_08_total3, half_19_08_total4, half_19_08_total5, half_19_08_total6, parameterExponent, curveLoss, dyadicExponent])

private def half_20_08_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1087597903/10000000000 : ℝ)

private theorem half_20_08_total1 : total half_20_08_φ1=(1087597903/10000000000 : ℝ) := by
  norm_num [half_20_08_φ1,total,emptyPhi,Fin.snoc]

private theorem half_20_08_bounds1 : ∀ l,0≤half_20_08_φ1 l ∧ half_20_08_φ1 l≤1 ∧
    0≤shiftExponents 9 half_20_08_φ1 l :=
  alternate_bounds_snoc emptyPhi (1087597903/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_20_08_φ2 : Fin 2 → ℝ := Fin.snoc half_20_08_φ1 (1079002513/10000000000 : ℝ)

private theorem half_20_08_total2 : total half_20_08_φ2=(67706263/312500000 : ℝ) := by
  change total (Fin.snoc half_20_08_φ1 (1079002513/10000000000 : ℝ))=(67706263/312500000 : ℝ)
  rw [alternate_total_snoc,half_20_08_total1]
  norm_num

private theorem half_20_08_bounds2 : ∀ l,0≤half_20_08_φ2 l ∧ half_20_08_φ2 l≤1 ∧
    0≤shiftExponents 9 half_20_08_φ2 l :=
  alternate_bounds_snoc half_20_08_φ1 (1079002513/10000000000 : ℝ) half_20_08_bounds1 (by norm_num)

private def half_20_08_φ3 : Fin 3 → ℝ := Fin.snoc half_20_08_φ2 (979174947/10000000000 : ℝ)

private theorem half_20_08_total3 : total half_20_08_φ3=(3145775363/10000000000 : ℝ) := by
  change total (Fin.snoc half_20_08_φ2 (979174947/10000000000 : ℝ))=(3145775363/10000000000 : ℝ)
  rw [alternate_total_snoc,half_20_08_total2]
  norm_num

private theorem half_20_08_bounds3 : ∀ l,0≤half_20_08_φ3 l ∧ half_20_08_φ3 l≤1 ∧
    0≤shiftExponents 9 half_20_08_φ3 l :=
  alternate_bounds_snoc half_20_08_φ2 (979174947/10000000000 : ℝ) half_20_08_bounds2 (by norm_num)

private def half_20_08_φ4 : Fin 4 → ℝ := Fin.snoc half_20_08_φ3 (856778079/10000000000 : ℝ)

private theorem half_20_08_total4 : total half_20_08_φ4=(2001276721/5000000000 : ℝ) := by
  change total (Fin.snoc half_20_08_φ3 (856778079/10000000000 : ℝ))=(2001276721/5000000000 : ℝ)
  rw [alternate_total_snoc,half_20_08_total3]
  norm_num

private theorem half_20_08_bounds4 : ∀ l,0≤half_20_08_φ4 l ∧ half_20_08_φ4 l≤1 ∧
    0≤shiftExponents 9 half_20_08_φ4 l :=
  alternate_bounds_snoc half_20_08_φ3 (856778079/10000000000 : ℝ) half_20_08_bounds3 (by norm_num)

private def half_20_08_φ5 : Fin 5 → ℝ := Fin.snoc half_20_08_φ4 (749680819/10000000000 : ℝ)

private theorem half_20_08_total5 : total half_20_08_φ5=(4752234261/10000000000 : ℝ) := by
  change total (Fin.snoc half_20_08_φ4 (749680819/10000000000 : ℝ))=(4752234261/10000000000 : ℝ)
  rw [alternate_total_snoc,half_20_08_total4]
  norm_num

private theorem half_20_08_bounds5 : ∀ l,0≤half_20_08_φ5 l ∧ half_20_08_φ5 l≤1 ∧
    0≤shiftExponents 9 half_20_08_φ5 l :=
  alternate_bounds_snoc half_20_08_φ4 (749680819/10000000000 : ℝ) half_20_08_bounds4 (by norm_num)

private def half_20_08_φ6 : Fin 6 → ℝ := Fin.snoc half_20_08_φ5 (655970717/10000000000 : ℝ)

private theorem half_20_08_total6 : total half_20_08_φ6=(2704102489/5000000000 : ℝ) := by
  change total (Fin.snoc half_20_08_φ5 (655970717/10000000000 : ℝ))=(2704102489/5000000000 : ℝ)
  rw [alternate_total_snoc,half_20_08_total5]
  norm_num

private theorem half_20_08_bounds6 : ∀ l,0≤half_20_08_φ6 l ∧ half_20_08_φ6 l≤1 ∧
    0≤shiftExponents 9 half_20_08_φ6 l :=
  alternate_bounds_snoc half_20_08_φ5 (655970717/10000000000 : ℝ) half_20_08_bounds5 (by norm_num)

private theorem half_20_08_prefix : PrefixCondition 9 half_20_08_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_20_08_φ1, half_20_08_φ2, half_20_08_φ3, half_20_08_φ4, half_20_08_φ5, half_20_08_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_20_08_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_20_08_φ6) (4387692533/625000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_20_08_φ6
    (fun i => (half_20_08_bounds6 i).1) (fun i => (half_20_08_bounds6 i).2.1)
    (fun i => (half_20_08_bounds6 i).2.2) half_20_08_prefix
  convert h using 1 <;> norm_num [half_20_08_total1, half_20_08_total2, half_20_08_total3, half_20_08_total4, half_20_08_total5, half_20_08_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_20_08_hx6 : SourcePowerBound
    (powerBoxCross 9 14 64 half_20_08_φ6) (14488170433/1250000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 14) (r := 2) (v := 18) (w := 19) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_20_08_φ6 (by norm_num [half_20_08_total1, half_20_08_total2, half_20_08_total3, half_20_08_total4, half_20_08_total5, half_20_08_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_20_08_total1, half_20_08_total2, half_20_08_total3, half_20_08_total4, half_20_08_total5, half_20_08_total6, parameterExponent, curveLoss, dyadicExponent]) half_20_08_hF2
    (half_18_08) (half_19_08)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_20_08_total1, half_20_08_total2, half_20_08_total3, half_20_08_total4, half_20_08_total5, half_20_08_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_08_hx5 : SourcePowerBound
    (powerBoxCross 9 15 32 half_20_08_φ5) (26856605217/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 15) (u := 13) (t := 16)
    (D := 32) (ψ := (655970717/10000000000 : ℝ)) half_20_08_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_08_bounds5 l).1) (fun l => (half_20_08_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_08_total1, half_20_08_total2, half_20_08_total3, half_20_08_total4, half_20_08_total5, half_20_08_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_14_08) (half_16_08)
    (by simpa only [half_20_08_φ6, show (2:ℝ)*32=64 by norm_num] using half_20_08_hx6)
  exact h.weaken (by norm_num [half_20_08_total1, half_20_08_total2, half_20_08_total3, half_20_08_total4, half_20_08_total5, half_20_08_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_08_hx4 : SourcePowerBound
    (powerBoxCross 9 16 16 half_20_08_φ4) (157982257307/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 16) (u := 14) (t := 17)
    (D := 16) (ψ := (749680819/10000000000 : ℝ)) half_20_08_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_08_bounds4 l).1) (fun l => (half_20_08_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_08_total1, half_20_08_total2, half_20_08_total3, half_20_08_total4, half_20_08_total5, half_20_08_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_15_08) (half_17_08)
    (by simpa only [half_20_08_φ5, show (2:ℝ)*16=32 by norm_num] using half_20_08_hx5)
  exact h.weaken (by norm_num [half_20_08_total1, half_20_08_total2, half_20_08_total3, half_20_08_total4, half_20_08_total5, half_20_08_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_08_hx3 : SourcePowerBound
    (powerBoxCross 9 17 8 half_20_08_φ3) (94062553521/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 17) (u := 15) (t := 18)
    (D := 8) (ψ := (856778079/10000000000 : ℝ)) half_20_08_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_08_bounds3 l).1) (fun l => (half_20_08_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_08_total1, half_20_08_total2, half_20_08_total3, half_20_08_total4, half_20_08_total5, half_20_08_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_16_08) (half_18_08)
    (by simpa only [half_20_08_φ4, show (2:ℝ)*8=16 by norm_num] using half_20_08_hx4)
  exact h.weaken (by norm_num [half_20_08_total1, half_20_08_total2, half_20_08_total3, half_20_08_total4, half_20_08_total5, half_20_08_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_08_hx2 : SourcePowerBound
    (powerBoxCross 9 18 4 half_20_08_φ2) (56487137453/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 18) (u := 16) (t := 19)
    (D := 4) (ψ := (979174947/10000000000 : ℝ)) half_20_08_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_08_bounds2 l).1) (fun l => (half_20_08_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_08_total1, half_20_08_total2, half_20_08_total3, half_20_08_total4, half_20_08_total5, half_20_08_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_17_08) (half_19_08)
    (by simpa only [half_20_08_φ3, show (2:ℝ)*4=8 by norm_num] using half_20_08_hx3)
  exact h.weaken (by norm_num [half_20_08_total1, half_20_08_total2, half_20_08_total3, half_20_08_total4, half_20_08_total5, half_20_08_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_08_hx1 : SourcePowerBound
    (powerBoxCross 9 19 2 half_20_08_φ1) (16962144473/625000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 19) (u := 17) (t := 20)
    (D := 2) (ψ := (1079002513/10000000000 : ℝ)) half_20_08_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_08_bounds1 l).1) (fun l => (half_20_08_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_08_total1, half_20_08_total2, half_20_08_total3, half_20_08_total4, half_20_08_total5, half_20_08_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_18_08) (half_20_07)
    (by simpa only [half_20_08_φ2, show (2:ℝ)*2=4 by norm_num] using half_20_08_hx2)
  exact h.weaken (by norm_num [half_20_08_total1, half_20_08_total2, half_20_08_total3, half_20_08_total4, half_20_08_total5, half_20_08_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_20_08 : AdmissibleExponent 9 40 (311635433979/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 18) (ψ := (1087597903/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_19_08)
    (by simpa only [half_20_08_φ1] using half_20_08_hx1)
  exact admissibleExponent_mono h (by norm_num [half_20_08_total1, half_20_08_total2, half_20_08_total3, half_20_08_total4, half_20_08_total5, half_20_08_total6, parameterExponent, curveLoss, dyadicExponent])

private def half_21_08_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (546950519/5000000000 : ℝ)

private theorem half_21_08_total1 : total half_21_08_φ1=(546950519/5000000000 : ℝ) := by
  norm_num [half_21_08_φ1,total,emptyPhi,Fin.snoc]

private theorem half_21_08_bounds1 : ∀ l,0≤half_21_08_φ1 l ∧ half_21_08_φ1 l≤1 ∧
    0≤shiftExponents 9 half_21_08_φ1 l :=
  alternate_bounds_snoc emptyPhi (546950519/5000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_21_08_φ2 : Fin 2 → ℝ := Fin.snoc half_21_08_φ1 (543794537/5000000000 : ℝ)

private theorem half_21_08_total2 : total half_21_08_φ2=(34085783/156250000 : ℝ) := by
  change total (Fin.snoc half_21_08_φ1 (543794537/5000000000 : ℝ))=(34085783/156250000 : ℝ)
  rw [alternate_total_snoc,half_21_08_total1]
  norm_num

private theorem half_21_08_bounds2 : ∀ l,0≤half_21_08_φ2 l ∧ half_21_08_φ2 l≤1 ∧
    0≤shiftExponents 9 half_21_08_φ2 l :=
  alternate_bounds_snoc half_21_08_φ1 (543794537/5000000000 : ℝ) half_21_08_bounds1 (by norm_num)

private def half_21_08_φ3 : Fin 3 → ℝ := Fin.snoc half_21_08_φ2 (195462747/2000000000 : ℝ)

private theorem half_21_08_total3 : total half_21_08_φ3=(3158803847/10000000000 : ℝ) := by
  change total (Fin.snoc half_21_08_φ2 (195462747/2000000000 : ℝ))=(3158803847/10000000000 : ℝ)
  rw [alternate_total_snoc,half_21_08_total2]
  norm_num

private theorem half_21_08_bounds3 : ∀ l,0≤half_21_08_φ3 l ∧ half_21_08_φ3 l≤1 ∧
    0≤shiftExponents 9 half_21_08_φ3 l :=
  alternate_bounds_snoc half_21_08_φ2 (195462747/2000000000 : ℝ) half_21_08_bounds2 (by norm_num)

private def half_21_08_φ4 : Fin 4 → ℝ := Fin.snoc half_21_08_φ3 (427574759/5000000000 : ℝ)

private theorem half_21_08_total4 : total half_21_08_φ4=(802790673/2000000000 : ℝ) := by
  change total (Fin.snoc half_21_08_φ3 (427574759/5000000000 : ℝ))=(802790673/2000000000 : ℝ)
  rw [alternate_total_snoc,half_21_08_total3]
  norm_num

private theorem half_21_08_bounds4 : ∀ l,0≤half_21_08_φ4 l ∧ half_21_08_φ4 l≤1 ∧
    0≤shiftExponents 9 half_21_08_φ4 l :=
  alternate_bounds_snoc half_21_08_φ3 (427574759/5000000000 : ℝ) half_21_08_bounds3 (by norm_num)

private def half_21_08_φ5 : Fin 5 → ℝ := Fin.snoc half_21_08_φ4 (748255829/10000000000 : ℝ)

private theorem half_21_08_total5 : total half_21_08_φ5=(2381104597/5000000000 : ℝ) := by
  change total (Fin.snoc half_21_08_φ4 (748255829/10000000000 : ℝ))=(2381104597/5000000000 : ℝ)
  rw [alternate_total_snoc,half_21_08_total4]
  norm_num

private theorem half_21_08_bounds5 : ∀ l,0≤half_21_08_φ5 l ∧ half_21_08_φ5 l≤1 ∧
    0≤shiftExponents 9 half_21_08_φ5 l :=
  alternate_bounds_snoc half_21_08_φ4 (748255829/10000000000 : ℝ) half_21_08_bounds4 (by norm_num)

private def half_21_08_φ6 : Fin 6 → ℝ := Fin.snoc half_21_08_φ5 (13094477/200000000 : ℝ)

private theorem half_21_08_total6 : total half_21_08_φ6=(1354233261/2500000000 : ℝ) := by
  change total (Fin.snoc half_21_08_φ5 (13094477/200000000 : ℝ))=(1354233261/2500000000 : ℝ)
  rw [alternate_total_snoc,half_21_08_total5]
  norm_num

private theorem half_21_08_bounds6 : ∀ l,0≤half_21_08_φ6 l ∧ half_21_08_φ6 l≤1 ∧
    0≤shiftExponents 9 half_21_08_φ6 l :=
  alternate_bounds_snoc half_21_08_φ5 (13094477/200000000 : ℝ) half_21_08_bounds5 (by norm_num)

private theorem half_21_08_prefix : PrefixCondition 9 half_21_08_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_21_08_φ1, half_21_08_φ2, half_21_08_φ3, half_21_08_φ4, half_21_08_φ5, half_21_08_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_21_08_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_21_08_φ6) (2187300217/312500000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_21_08_φ6
    (fun i => (half_21_08_bounds6 i).1) (fun i => (half_21_08_bounds6 i).2.1)
    (fun i => (half_21_08_bounds6 i).2.2) half_21_08_prefix
  convert h using 1 <;> norm_num [half_21_08_total1, half_21_08_total2, half_21_08_total3, half_21_08_total4, half_21_08_total5, half_21_08_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_21_08_hx6 : SourcePowerBound
    (powerBoxCross 9 15 64 half_21_08_φ6) (124616856221/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 15) (r := 2) (v := 0) (w := 20) (D := 64)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_21_08_φ6 (by norm_num [half_21_08_total1, half_21_08_total2, half_21_08_total3, half_21_08_total4, half_21_08_total5, half_21_08_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_21_08_total1, half_21_08_total2, half_21_08_total3, half_21_08_total4, half_21_08_total5, half_21_08_total6, parameterExponent, curveLoss, dyadicExponent]) half_21_08_hF2
    (admissibleExponent_zero 9) (half_20_08)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_21_08_total1, half_21_08_total2, half_21_08_total3, half_21_08_total4, half_21_08_total5, half_21_08_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_21_08_hx5 : SourcePowerBound
    (powerBoxCross 9 16 32 half_21_08_φ5) (720548647/50000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 16) (u := 14) (t := 17)
    (D := 32) (ψ := (13094477/200000000 : ℝ)) half_21_08_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_21_08_bounds5 l).1) (fun l => (half_21_08_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_21_08_total1, half_21_08_total2, half_21_08_total3, half_21_08_total4, half_21_08_total5, half_21_08_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_15_08) (half_17_08)
    (by simpa only [half_21_08_φ6, show (2:ℝ)*32=64 by norm_num] using half_21_08_hx6)
  exact h.weaken (by norm_num [half_21_08_total1, half_21_08_total2, half_21_08_total3, half_21_08_total4, half_21_08_total5, half_21_08_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_21_08_hx4 : SourcePowerBound
    (powerBoxCross 9 17 16 half_21_08_φ4) (16919900463/1000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 17) (u := 15) (t := 18)
    (D := 16) (ψ := (748255829/10000000000 : ℝ)) half_21_08_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_21_08_bounds4 l).1) (fun l => (half_21_08_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_21_08_total1, half_21_08_total2, half_21_08_total3, half_21_08_total4, half_21_08_total5, half_21_08_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_16_08) (half_18_08)
    (by simpa only [half_21_08_φ5, show (2:ℝ)*16=32 by norm_num] using half_21_08_hx5)
  exact h.weaken (by norm_num [half_21_08_total1, half_21_08_total2, half_21_08_total3, half_21_08_total4, half_21_08_total5, half_21_08_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_21_08_hx3 : SourcePowerBound
    (powerBoxCross 9 18 8 half_21_08_φ3) (200980500839/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 18) (u := 16) (t := 19)
    (D := 8) (ψ := (427574759/5000000000 : ℝ)) half_21_08_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_21_08_bounds3 l).1) (fun l => (half_21_08_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_21_08_total1, half_21_08_total2, half_21_08_total3, half_21_08_total4, half_21_08_total5, half_21_08_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_17_08) (half_19_08)
    (by simpa only [half_21_08_φ4, show (2:ℝ)*8=16 by norm_num] using half_21_08_hx4)
  exact h.weaken (by norm_num [half_21_08_total1, half_21_08_total2, half_21_08_total3, half_21_08_total4, half_21_08_total5, half_21_08_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_21_08_hx2 : SourcePowerBound
    (powerBoxCross 9 19 4 half_21_08_φ2) (48138703287/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 19) (u := 17) (t := 20)
    (D := 4) (ψ := (195462747/2000000000 : ℝ)) half_21_08_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_21_08_bounds2 l).1) (fun l => (half_21_08_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_21_08_total1, half_21_08_total2, half_21_08_total3, half_21_08_total4, half_21_08_total5, half_21_08_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_18_08) (half_20_08)
    (by simpa only [half_21_08_φ3, show (2:ℝ)*4=8 by norm_num] using half_21_08_hx3)
  exact h.weaken (by norm_num [half_21_08_total1, half_21_08_total2, half_21_08_total3, half_21_08_total4, half_21_08_total5, half_21_08_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_21_08_hx1 : SourcePowerBound
    (powerBoxCross 9 20 2 half_21_08_φ1) (288639502549/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 20) (u := 18) (t := 21)
    (D := 2) (ψ := (543794537/5000000000 : ℝ)) half_21_08_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_21_08_bounds1 l).1) (fun l => (half_21_08_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_21_08_total1, half_21_08_total2, half_21_08_total3, half_21_08_total4, half_21_08_total5, half_21_08_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_19_08) (half_21_07)
    (by simpa only [half_21_08_φ2, show (2:ℝ)*2=4 by norm_num] using half_21_08_hx2)
  exact h.weaken (by norm_num [half_21_08_total1, half_21_08_total2, half_21_08_total3, half_21_08_total4, half_21_08_total5, half_21_08_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_21_08 : AdmissibleExponent 9 42 (331301643031/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 19) (ψ := (546950519/5000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_20_08)
    (by simpa only [half_21_08_φ1] using half_21_08_hx1)
  exact admissibleExponent_mono h (by norm_num [half_21_08_total1, half_21_08_total2, half_21_08_total3, half_21_08_total4, half_21_08_total5, half_21_08_total6, parameterExponent, curveLoss, dyadicExponent])

private def half_22_08_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (21982649/200000000 : ℝ)

private theorem half_22_08_total1 : total half_22_08_φ1=(21982649/200000000 : ℝ) := by
  norm_num [half_22_08_φ1,total,emptyPhi,Fin.snoc]

private theorem half_22_08_bounds1 : ∀ l,0≤half_22_08_φ1 l ∧ half_22_08_φ1 l≤1 ∧
    0≤shiftExponents 9 half_22_08_φ1 l :=
  alternate_bounds_snoc emptyPhi (21982649/200000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_22_08_φ2 : Fin 2 → ℝ := Fin.snoc half_22_08_φ1 (547207533/5000000000 : ℝ)

private theorem half_22_08_total2 : total half_22_08_φ2=(548386879/2500000000 : ℝ) := by
  change total (Fin.snoc half_22_08_φ1 (547207533/5000000000 : ℝ))=(548386879/2500000000 : ℝ)
  rw [alternate_total_snoc,half_22_08_total1]
  norm_num

private theorem half_22_08_bounds2 : ∀ l,0≤half_22_08_φ2 l ∧ half_22_08_φ2 l≤1 ∧
    0≤shiftExponents 9 half_22_08_φ2 l :=
  alternate_bounds_snoc half_22_08_φ1 (547207533/5000000000 : ℝ) half_22_08_bounds1 (by norm_num)

private def half_22_08_φ3 : Fin 3 → ℝ := Fin.snoc half_22_08_φ2 (6098791/62500000 : ℝ)

private theorem half_22_08_total3 : total half_22_08_φ3=(792338519/2500000000 : ℝ) := by
  change total (Fin.snoc half_22_08_φ2 (6098791/62500000 : ℝ))=(792338519/2500000000 : ℝ)
  rw [alternate_total_snoc,half_22_08_total2]
  norm_num

private theorem half_22_08_bounds3 : ∀ l,0≤half_22_08_φ3 l ∧ half_22_08_φ3 l≤1 ∧
    0≤shiftExponents 9 half_22_08_φ3 l :=
  alternate_bounds_snoc half_22_08_φ2 (6098791/62500000 : ℝ) half_22_08_bounds2 (by norm_num)

private def half_22_08_φ4 : Fin 4 → ℝ := Fin.snoc half_22_08_φ3 (42691537/500000000 : ℝ)

private theorem half_22_08_total4 : total half_22_08_φ4=(251449051/625000000 : ℝ) := by
  change total (Fin.snoc half_22_08_φ3 (42691537/500000000 : ℝ))=(251449051/625000000 : ℝ)
  rw [alternate_total_snoc,half_22_08_total3]
  norm_num

private theorem half_22_08_bounds4 : ∀ l,0≤half_22_08_φ4 l ∧ half_22_08_φ4 l≤1 ∧
    0≤shiftExponents 9 half_22_08_φ4 l :=
  alternate_bounds_snoc half_22_08_φ3 (42691537/500000000 : ℝ) half_22_08_bounds3 (by norm_num)

private def half_22_08_φ5 : Fin 5 → ℝ := Fin.snoc half_22_08_φ4 (747101897/10000000000 : ℝ)

private theorem half_22_08_total5 : total half_22_08_φ5=(4770286713/10000000000 : ℝ) := by
  change total (Fin.snoc half_22_08_φ4 (747101897/10000000000 : ℝ))=(4770286713/10000000000 : ℝ)
  rw [alternate_total_snoc,half_22_08_total4]
  norm_num

private theorem half_22_08_bounds5 : ∀ l,0≤half_22_08_φ5 l ∧ half_22_08_φ5 l≤1 ∧
    0≤shiftExponents 9 half_22_08_φ5 l :=
  alternate_bounds_snoc half_22_08_φ4 (747101897/10000000000 : ℝ) half_22_08_bounds4 (by norm_num)

private def half_22_08_φ6 : Fin 6 → ℝ := Fin.snoc half_22_08_φ5 (8171427/125000000 : ℝ)

private theorem half_22_08_total6 : total half_22_08_φ6=(5424000873/10000000000 : ℝ) := by
  change total (Fin.snoc half_22_08_φ5 (8171427/125000000 : ℝ))=(5424000873/10000000000 : ℝ)
  rw [alternate_total_snoc,half_22_08_total5]
  norm_num

private theorem half_22_08_bounds6 : ∀ l,0≤half_22_08_φ6 l ∧ half_22_08_φ6 l≤1 ∧
    0≤shiftExponents 9 half_22_08_φ6 l :=
  alternate_bounds_snoc half_22_08_φ5 (8171427/125000000 : ℝ) half_22_08_bounds5 (by norm_num)

private theorem half_22_08_prefix : PrefixCondition 9 half_22_08_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_22_08_φ1, half_22_08_φ2, half_22_08_φ3, half_22_08_φ4, half_22_08_φ5, half_22_08_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_22_08_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_22_08_φ6) (8727997381/1250000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_22_08_φ6
    (fun i => (half_22_08_bounds6 i).1) (fun i => (half_22_08_bounds6 i).2.1)
    (fun i => (half_22_08_bounds6 i).2.2) half_22_08_prefix
  convert h using 1 <;> norm_num [half_22_08_total1, half_22_08_total2, half_22_08_total3, half_22_08_total4, half_22_08_total5, half_22_08_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_22_08_hx6 : SourcePowerBound
    (powerBoxCross 9 16 64 half_22_08_φ6) (133423115711/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 16) (r := 2) (v := 21) (w := 22) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_22_08_φ6 (by norm_num [half_22_08_total1, half_22_08_total2, half_22_08_total3, half_22_08_total4, half_22_08_total5, half_22_08_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_22_08_total1, half_22_08_total2, half_22_08_total3, half_22_08_total4, half_22_08_total5, half_22_08_total6, parameterExponent, curveLoss, dyadicExponent]) half_22_08_hF2
    (half_21_08) (half_22_07)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_22_08_total1, half_22_08_total2, half_22_08_total3, half_22_08_total4, half_22_08_total5, half_22_08_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_22_08_hx5 : SourcePowerBound
    (powerBoxCross 9 17 32 half_22_08_φ5) (30810921403/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 17) (u := 15) (t := 18)
    (D := 32) (ψ := (8171427/125000000 : ℝ)) half_22_08_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_22_08_bounds5 l).1) (fun l => (half_22_08_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_22_08_total1, half_22_08_total2, half_22_08_total3, half_22_08_total4, half_22_08_total5, half_22_08_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_16_08) (half_18_08)
    (by simpa only [half_22_08_φ6, show (2:ℝ)*32=64 by norm_num] using half_22_08_hx6)
  exact h.weaken (by norm_num [half_22_08_total1, half_22_08_total2, half_22_08_total3, half_22_08_total4, half_22_08_total5, half_22_08_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_22_08_hx4 : SourcePowerBound
    (powerBoxCross 9 18 16 half_22_08_φ4) (180544898941/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 18) (u := 16) (t := 19)
    (D := 16) (ψ := (747101897/10000000000 : ℝ)) half_22_08_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_22_08_bounds4 l).1) (fun l => (half_22_08_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_22_08_total1, half_22_08_total2, half_22_08_total3, half_22_08_total4, half_22_08_total5, half_22_08_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_17_08) (half_19_08)
    (by simpa only [half_22_08_φ5, show (2:ℝ)*16=32 by norm_num] using half_22_08_hx5)
  exact h.weaken (by norm_num [half_22_08_total1, half_22_08_total2, half_22_08_total3, half_22_08_total4, half_22_08_total5, half_22_08_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_22_08_hx3 : SourcePowerBound
    (powerBoxCross 9 19 8 half_22_08_φ3) (213970636461/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 19) (u := 17) (t := 20)
    (D := 8) (ψ := (42691537/500000000 : ℝ)) half_22_08_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_22_08_bounds3 l).1) (fun l => (half_22_08_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_22_08_total1, half_22_08_total2, half_22_08_total3, half_22_08_total4, half_22_08_total5, half_22_08_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_18_08) (half_20_08)
    (by simpa only [half_22_08_φ4, show (2:ℝ)*8=16 by norm_num] using half_22_08_hx4)
  exact h.weaken (by norm_num [half_22_08_total1, half_22_08_total2, half_22_08_total3, half_22_08_total4, half_22_08_total5, half_22_08_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_22_08_hx2 : SourcePowerBound
    (powerBoxCross 9 20 4 half_22_08_φ2) (255578076237/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 20) (u := 18) (t := 21)
    (D := 4) (ψ := (6098791/62500000 : ℝ)) half_22_08_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_22_08_bounds2 l).1) (fun l => (half_22_08_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_22_08_total1, half_22_08_total2, half_22_08_total3, half_22_08_total4, half_22_08_total5, half_22_08_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_19_08) (half_21_08)
    (by simpa only [half_22_08_φ3, show (2:ℝ)*4=8 by norm_num] using half_22_08_hx3)
  exact h.weaken (by norm_num [half_22_08_total1, half_22_08_total2, half_22_08_total3, half_22_08_total4, half_22_08_total5, half_22_08_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_22_08_hx1 : SourcePowerBound
    (powerBoxCross 9 21 2 half_22_08_φ1) (305986336827/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 21) (u := 19) (t := 22)
    (D := 2) (ψ := (547207533/5000000000 : ℝ)) half_22_08_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_22_08_bounds1 l).1) (fun l => (half_22_08_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_22_08_total1, half_22_08_total2, half_22_08_total3, half_22_08_total4, half_22_08_total5, half_22_08_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_20_08) (half_22_07)
    (by simpa only [half_22_08_φ2, show (2:ℝ)*2=4 by norm_num] using half_22_08_hx2)
  exact h.weaken (by norm_num [half_22_08_total1, half_22_08_total2, half_22_08_total3, half_22_08_total4, half_22_08_total5, half_22_08_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_22_08 : AdmissibleExponent 9 44 (351050767277/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 20) (ψ := (21982649/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_21_08)
    (by simpa only [half_22_08_φ1] using half_22_08_hx1)
  exact admissibleExponent_mono h (by norm_num [half_22_08_total1, half_22_08_total2, half_22_08_total3, half_22_08_total4, half_22_08_total5, half_22_08_total6, parameterExponent, curveLoss, dyadicExponent])

private def half_10_09_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (22014303/250000000 : ℝ)

private theorem half_10_09_total1 : total half_10_09_φ1=(22014303/250000000 : ℝ) := by
  norm_num [half_10_09_φ1,total,emptyPhi,Fin.snoc]

private theorem half_10_09_bounds1 : ∀ l,0≤half_10_09_φ1 l ∧ half_10_09_φ1 l≤1 ∧
    0≤shiftExponents 9 half_10_09_φ1 l :=
  alternate_bounds_snoc emptyPhi (22014303/250000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_10_09_φ2 : Fin 2 → ℝ := Fin.snoc half_10_09_φ1 (410784367/5000000000 : ℝ)

private theorem half_10_09_total2 : total half_10_09_φ2=(851070427/5000000000 : ℝ) := by
  change total (Fin.snoc half_10_09_φ1 (410784367/5000000000 : ℝ))=(851070427/5000000000 : ℝ)
  rw [alternate_total_snoc,half_10_09_total1]
  norm_num

private theorem half_10_09_bounds2 : ∀ l,0≤half_10_09_φ2 l ∧ half_10_09_φ2 l≤1 ∧
    0≤shiftExponents 9 half_10_09_φ2 l :=
  alternate_bounds_snoc half_10_09_φ1 (410784367/5000000000 : ℝ) half_10_09_bounds1 (by norm_num)

private def half_10_09_φ3 : Fin 3 → ℝ := Fin.snoc half_10_09_φ2 (179262261/2500000000 : ℝ)

private theorem half_10_09_total3 : total half_10_09_φ3=(1209594949/5000000000 : ℝ) := by
  change total (Fin.snoc half_10_09_φ2 (179262261/2500000000 : ℝ))=(1209594949/5000000000 : ℝ)
  rw [alternate_total_snoc,half_10_09_total2]
  norm_num

private theorem half_10_09_bounds3 : ∀ l,0≤half_10_09_φ3 l ∧ half_10_09_φ3 l≤1 ∧
    0≤shiftExponents 9 half_10_09_φ3 l :=
  alternate_bounds_snoc half_10_09_φ2 (179262261/2500000000 : ℝ) half_10_09_bounds2 (by norm_num)

private def half_10_09_φ4 : Fin 4 → ℝ := Fin.snoc half_10_09_φ3 (450216623/10000000000 : ℝ)

private theorem half_10_09_total4 : total half_10_09_φ4=(2869406521/10000000000 : ℝ) := by
  change total (Fin.snoc half_10_09_φ3 (450216623/10000000000 : ℝ))=(2869406521/10000000000 : ℝ)
  rw [alternate_total_snoc,half_10_09_total3]
  norm_num

private theorem half_10_09_bounds4 : ∀ l,0≤half_10_09_φ4 l ∧ half_10_09_φ4 l≤1 ∧
    0≤shiftExponents 9 half_10_09_φ4 l :=
  alternate_bounds_snoc half_10_09_φ3 (450216623/10000000000 : ℝ) half_10_09_bounds3 (by norm_num)

private theorem half_10_09_prefix : PrefixCondition 9 half_10_09_φ4 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_10_09_φ1, half_10_09_φ2, half_10_09_φ3, half_10_09_φ4, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_10_09_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 16 half_10_09_φ4) (8891780437/1250000000 : ℝ) := by
  have h := padded_dyadic_divisor_power (k := 9) (j := 4) (r := 0) (n := 1) (D := 16)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_10_09_φ4
    (fun i => (half_10_09_bounds4 i).1) (fun i => (half_10_09_bounds4 i).2.1)
    (fun i => (half_10_09_bounds4 i).2.2) half_10_09_prefix
  convert h using 1 <;> norm_num [half_10_09_total1, half_10_09_total2, half_10_09_total3, half_10_09_total4, parameterExponent, curveLoss, dyadicExponent]

private theorem half_10_09_hx4 : SourcePowerBound
    (powerBoxCross 9 6 16 half_10_09_φ4) (69144835307/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 6) (r := 2) (v := 0) (w := 8) (D := 16)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_10_09_φ4 (by norm_num [half_10_09_total1, half_10_09_total2, half_10_09_total3, half_10_09_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_10_09_total1, half_10_09_total2, half_10_09_total3, half_10_09_total4, parameterExponent, curveLoss, dyadicExponent]) half_10_09_hF2
    (admissibleExponent_zero 9) (SeedCompletionHigher9SimpleSeeds.degree9_half_8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_10_09_total1, half_10_09_total2, half_10_09_total3, half_10_09_total4, parameterExponent, curveLoss, dyadicExponent])

private theorem half_10_09_hx3 : SourcePowerBound
    (powerBoxCross 9 7 8 half_10_09_φ3) (78774622901/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 7) (u := 5) (t := 8)
    (D := 8) (ψ := (450216623/10000000000 : ℝ)) half_10_09_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_10_09_bounds3 l).1) (fun l => (half_10_09_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_10_09_total1, half_10_09_total2, half_10_09_total3, half_10_09_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionNinthSecondSeeds.ninth_half_6) (SeedCompletionHigher9SimpleSeeds.degree9_half_8)
    (by simpa only [half_10_09_φ4, show (2:ℝ)*8=16 by norm_num] using half_10_09_hx4)
  exact h.weaken (by norm_num [half_10_09_total1, half_10_09_total2, half_10_09_total3, half_10_09_total4, parameterExponent, curveLoss, dyadicExponent])

private theorem half_10_09_hx2 : SourcePowerBound
    (powerBoxCross 9 8 4 half_10_09_φ2) (93469025283/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 8) (u := 6) (t := 9)
    (D := 4) (ψ := (179262261/2500000000 : ℝ)) half_10_09_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_10_09_bounds2 l).1) (fun l => (half_10_09_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_10_09_total1, half_10_09_total2, half_10_09_total3, half_10_09_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionNinthSecondSeeds.ninth_half_7) (SeedCompletionHigher9SimpleSeeds.degree9_half_9)
    (by simpa only [half_10_09_φ3, show (2:ℝ)*4=8 by norm_num] using half_10_09_hx3)
  exact h.weaken (by norm_num [half_10_09_total1, half_10_09_total2, half_10_09_total3, half_10_09_total4, parameterExponent, curveLoss, dyadicExponent])

private theorem half_10_09_hx1 : SourcePowerBound
    (powerBoxCross 9 9 2 half_10_09_φ1) (112493820789/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 9) (u := 7) (t := 10)
    (D := 2) (ψ := (410784367/5000000000 : ℝ)) half_10_09_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_10_09_bounds1 l).1) (fun l => (half_10_09_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_10_09_total1, half_10_09_total2, half_10_09_total3, half_10_09_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_8) (half_10_08)
    (by simpa only [half_10_09_φ2, show (2:ℝ)*2=4 by norm_num] using half_10_09_hx2)
  exact h.weaken (by norm_num [half_10_09_total1, half_10_09_total2, half_10_09_total3, half_10_09_total4, parameterExponent, curveLoss, dyadicExponent])

theorem half_10_09 : AdmissibleExponent 9 20 (127463546829/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 8) (ψ := (22014303/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (SeedCompletionHigher9SimpleSeeds.degree9_half_9)
    (by simpa only [half_10_09_φ1] using half_10_09_hx1)
  exact admissibleExponent_mono h (by norm_num [half_10_09_total1, half_10_09_total2, half_10_09_total3, half_10_09_total4, parameterExponent, curveLoss, dyadicExponent])

private def half_11_09_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (915812371/10000000000 : ℝ)

private theorem half_11_09_total1 : total half_11_09_φ1=(915812371/10000000000 : ℝ) := by
  norm_num [half_11_09_φ1,total,emptyPhi,Fin.snoc]

private theorem half_11_09_bounds1 : ∀ l,0≤half_11_09_φ1 l ∧ half_11_09_φ1 l≤1 ∧
    0≤shiftExponents 9 half_11_09_φ1 l :=
  alternate_bounds_snoc emptyPhi (915812371/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_11_09_φ2 : Fin 2 → ℝ := Fin.snoc half_11_09_φ1 (865407839/10000000000 : ℝ)

private theorem half_11_09_total2 : total half_11_09_φ2=(178122021/1000000000 : ℝ) := by
  change total (Fin.snoc half_11_09_φ1 (865407839/10000000000 : ℝ))=(178122021/1000000000 : ℝ)
  rw [alternate_total_snoc,half_11_09_total1]
  norm_num

private theorem half_11_09_bounds2 : ∀ l,0≤half_11_09_φ2 l ∧ half_11_09_φ2 l≤1 ∧
    0≤shiftExponents 9 half_11_09_φ2 l :=
  alternate_bounds_snoc half_11_09_φ1 (865407839/10000000000 : ℝ) half_11_09_bounds1 (by norm_num)

private def half_11_09_φ3 : Fin 3 → ℝ := Fin.snoc half_11_09_φ2 (788116037/10000000000 : ℝ)

private theorem half_11_09_total3 : total half_11_09_φ3=(2569336247/10000000000 : ℝ) := by
  change total (Fin.snoc half_11_09_φ2 (788116037/10000000000 : ℝ))=(2569336247/10000000000 : ℝ)
  rw [alternate_total_snoc,half_11_09_total2]
  norm_num

private theorem half_11_09_bounds3 : ∀ l,0≤half_11_09_φ3 l ∧ half_11_09_φ3 l≤1 ∧
    0≤shiftExponents 9 half_11_09_φ3 l :=
  alternate_bounds_snoc half_11_09_φ2 (788116037/10000000000 : ℝ) half_11_09_bounds2 (by norm_num)

private def half_11_09_φ4 : Fin 4 → ℝ := Fin.snoc half_11_09_φ3 (156190739/2500000000 : ℝ)

private theorem half_11_09_total4 : total half_11_09_φ4=(3194099203/10000000000 : ℝ) := by
  change total (Fin.snoc half_11_09_φ3 (156190739/2500000000 : ℝ))=(3194099203/10000000000 : ℝ)
  rw [alternate_total_snoc,half_11_09_total3]
  norm_num

private theorem half_11_09_bounds4 : ∀ l,0≤half_11_09_φ4 l ∧ half_11_09_φ4 l≤1 ∧
    0≤shiftExponents 9 half_11_09_φ4 l :=
  alternate_bounds_snoc half_11_09_φ3 (156190739/2500000000 : ℝ) half_11_09_bounds3 (by norm_num)

private theorem half_11_09_prefix : PrefixCondition 9 half_11_09_φ4 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_11_09_φ1, half_11_09_φ2, half_11_09_φ3, half_11_09_φ4, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_11_09_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 16 half_11_09_φ4) (7917702391/1250000000 : ℝ) := by
  have h := padded_dyadic_divisor_power (k := 9) (j := 4) (r := 0) (n := 1) (D := 16)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_11_09_φ4
    (fun i => (half_11_09_bounds4 i).1) (fun i => (half_11_09_bounds4 i).2.1)
    (fun i => (half_11_09_bounds4 i).2.2) half_11_09_prefix
  convert h using 1 <;> norm_num [half_11_09_total1, half_11_09_total2, half_11_09_total3, half_11_09_total4, parameterExponent, curveLoss, dyadicExponent]

private theorem half_11_09_hx4 : SourcePowerBound
    (powerBoxCross 9 7 16 half_11_09_φ4) (75440394743/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 7) (r := 2) (v := 9) (w := 10) (D := 16)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_11_09_φ4 (by norm_num [half_11_09_total1, half_11_09_total2, half_11_09_total3, half_11_09_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_11_09_total1, half_11_09_total2, half_11_09_total3, half_11_09_total4, parameterExponent, curveLoss, dyadicExponent]) half_11_09_hF2
    (SeedCompletionHigher9SimpleSeeds.degree9_half_9) (half_10_09)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_11_09_total1, half_11_09_total2, half_11_09_total3, half_11_09_total4, parameterExponent, curveLoss, dyadicExponent])

private theorem half_11_09_hx3 : SourcePowerBound
    (powerBoxCross 9 8 8 half_11_09_φ3) (87901906609/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 8) (u := 6) (t := 9)
    (D := 8) (ψ := (156190739/2500000000 : ℝ)) half_11_09_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_11_09_bounds3 l).1) (fun l => (half_11_09_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_11_09_total1, half_11_09_total2, half_11_09_total3, half_11_09_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionNinthSecondSeeds.ninth_half_7) (SeedCompletionHigher9SimpleSeeds.degree9_half_9)
    (by simpa only [half_11_09_φ4, show (2:ℝ)*8=16 by norm_num] using half_11_09_hx4)
  exact h.weaken (by norm_num [half_11_09_total1, half_11_09_total2, half_11_09_total3, half_11_09_total4, parameterExponent, curveLoss, dyadicExponent])

private theorem half_11_09_hx2 : SourcePowerBound
    (powerBoxCross 9 9 4 half_11_09_φ2) (52558341937/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 9) (u := 7) (t := 10)
    (D := 4) (ψ := (788116037/10000000000 : ℝ)) half_11_09_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_11_09_bounds2 l).1) (fun l => (half_11_09_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_11_09_total1, half_11_09_total2, half_11_09_total3, half_11_09_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_8) (half_10_09)
    (by simpa only [half_11_09_φ3, show (2:ℝ)*4=8 by norm_num] using half_11_09_hx3)
  exact h.weaken (by norm_num [half_11_09_total1, half_11_09_total2, half_11_09_total3, half_11_09_total4, parameterExponent, curveLoss, dyadicExponent])

private theorem half_11_09_hx1 : SourcePowerBound
    (powerBoxCross 9 10 2 half_11_09_φ1) (126706089901/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 10) (u := 8) (t := 11)
    (D := 2) (ψ := (865407839/10000000000 : ℝ)) half_11_09_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_11_09_bounds1 l).1) (fun l => (half_11_09_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_11_09_total1, half_11_09_total2, half_11_09_total3, half_11_09_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_9) (half_11_08)
    (by simpa only [half_11_09_φ2, show (2:ℝ)*2=4 by norm_num] using half_11_09_hx2)
  exact h.weaken (by norm_num [half_11_09_total1, half_11_09_total2, half_11_09_total3, half_11_09_total4, parameterExponent, curveLoss, dyadicExponent])

theorem half_11_09 : AdmissibleExponent 9 22 (2882130499/200000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 9) (ψ := (915812371/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_10_09)
    (by simpa only [half_11_09_φ1] using half_11_09_hx1)
  exact admissibleExponent_mono h (by norm_num [half_11_09_total1, half_11_09_total2, half_11_09_total3, half_11_09_total4, parameterExponent, curveLoss, dyadicExponent])

private def half_12_09_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (947075423/10000000000 : ℝ)

private theorem half_12_09_total1 : total half_12_09_φ1=(947075423/10000000000 : ℝ) := by
  norm_num [half_12_09_φ1,total,emptyPhi,Fin.snoc]

private theorem half_12_09_bounds1 : ∀ l,0≤half_12_09_φ1 l ∧ half_12_09_φ1 l≤1 ∧
    0≤shiftExponents 9 half_12_09_φ1 l :=
  alternate_bounds_snoc emptyPhi (947075423/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_12_09_φ2 : Fin 2 → ℝ := Fin.snoc half_12_09_φ1 (451610649/5000000000 : ℝ)

private theorem half_12_09_total2 : total half_12_09_φ2=(1850296721/10000000000 : ℝ) := by
  change total (Fin.snoc half_12_09_φ1 (451610649/5000000000 : ℝ))=(1850296721/10000000000 : ℝ)
  rw [alternate_total_snoc,half_12_09_total1]
  norm_num

private theorem half_12_09_bounds2 : ∀ l,0≤half_12_09_φ2 l ∧ half_12_09_φ2 l≤1 ∧
    0≤shiftExponents 9 half_12_09_φ2 l :=
  alternate_bounds_snoc half_12_09_φ1 (451610649/5000000000 : ℝ) half_12_09_bounds1 (by norm_num)

private def half_12_09_φ3 : Fin 3 → ℝ := Fin.snoc half_12_09_φ2 (210184869/2500000000 : ℝ)

private theorem half_12_09_total3 : total half_12_09_φ3=(2691036197/10000000000 : ℝ) := by
  change total (Fin.snoc half_12_09_φ2 (210184869/2500000000 : ℝ))=(2691036197/10000000000 : ℝ)
  rw [alternate_total_snoc,half_12_09_total2]
  norm_num

private theorem half_12_09_bounds3 : ∀ l,0≤half_12_09_φ3 l ∧ half_12_09_φ3 l≤1 ∧
    0≤shiftExponents 9 half_12_09_φ3 l :=
  alternate_bounds_snoc half_12_09_φ2 (210184869/2500000000 : ℝ) half_12_09_bounds2 (by norm_num)

private def half_12_09_φ4 : Fin 4 → ℝ := Fin.snoc half_12_09_φ3 (145595799/2000000000 : ℝ)

private theorem half_12_09_total4 : total half_12_09_φ4=(427376899/1250000000 : ℝ) := by
  change total (Fin.snoc half_12_09_φ3 (145595799/2000000000 : ℝ))=(427376899/1250000000 : ℝ)
  rw [alternate_total_snoc,half_12_09_total3]
  norm_num

private theorem half_12_09_bounds4 : ∀ l,0≤half_12_09_φ4 l ∧ half_12_09_φ4 l≤1 ∧
    0≤shiftExponents 9 half_12_09_φ4 l :=
  alternate_bounds_snoc half_12_09_φ3 (145595799/2000000000 : ℝ) half_12_09_bounds3 (by norm_num)

private def half_12_09_φ5 : Fin 5 → ℝ := Fin.snoc half_12_09_φ4 (450362391/10000000000 : ℝ)

private theorem half_12_09_total5 : total half_12_09_φ5=(3869377583/10000000000 : ℝ) := by
  change total (Fin.snoc half_12_09_φ4 (450362391/10000000000 : ℝ))=(3869377583/10000000000 : ℝ)
  rw [alternate_total_snoc,half_12_09_total4]
  norm_num

private theorem half_12_09_bounds5 : ∀ l,0≤half_12_09_φ5 l ∧ half_12_09_φ5 l≤1 ∧
    0≤shiftExponents 9 half_12_09_φ5 l :=
  alternate_bounds_snoc half_12_09_φ4 (450362391/10000000000 : ℝ) half_12_09_bounds4 (by norm_num)

private theorem half_12_09_prefix : PrefixCondition 9 half_12_09_φ5 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_12_09_φ1, half_12_09_φ2, half_12_09_φ3, half_12_09_φ4, half_12_09_φ5, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_12_09_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 32 half_12_09_φ5) (9641867251/1250000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_12_09_φ5
    (fun i => (half_12_09_bounds5 i).1) (fun i => (half_12_09_bounds5 i).2.1)
    (fun i => (half_12_09_bounds5 i).2.2) half_12_09_prefix
  convert h using 1 <;> norm_num [half_12_09_total1, half_12_09_total2, half_12_09_total3, half_12_09_total4, half_12_09_total5, parameterExponent, curveLoss, dyadicExponent]

private theorem half_12_09_hx5 : SourcePowerBound
    (powerBoxCross 9 7 32 half_12_09_φ5) (72974744483/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 7) (r := 2) (v := 9) (w := 10) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_12_09_φ5 (by norm_num [half_12_09_total1, half_12_09_total2, half_12_09_total3, half_12_09_total4, half_12_09_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_12_09_total1, half_12_09_total2, half_12_09_total3, half_12_09_total4, half_12_09_total5, parameterExponent, curveLoss, dyadicExponent]) half_12_09_hF2
    (SeedCompletionHigher9SimpleSeeds.degree9_half_9) (half_10_09)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_12_09_total1, half_12_09_total2, half_12_09_total3, half_12_09_total4, half_12_09_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_12_09_hx4 : SourcePowerBound
    (powerBoxCross 9 8 16 half_12_09_φ4) (82402987109/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 8) (u := 6) (t := 9)
    (D := 16) (ψ := (450362391/10000000000 : ℝ)) half_12_09_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_12_09_bounds4 l).1) (fun l => (half_12_09_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_12_09_total1, half_12_09_total2, half_12_09_total3, half_12_09_total4, half_12_09_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionNinthSecondSeeds.ninth_half_7) (SeedCompletionHigher9SimpleSeeds.degree9_half_9)
    (by simpa only [half_12_09_φ5, show (2:ℝ)*16=32 by norm_num] using half_12_09_hx5)
  exact h.weaken (by norm_num [half_12_09_total1, half_12_09_total2, half_12_09_total3, half_12_09_total4, half_12_09_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_12_09_hx3 : SourcePowerBound
    (powerBoxCross 9 9 8 half_12_09_φ3) (1523101777/156250000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 9) (u := 7) (t := 10)
    (D := 8) (ψ := (145595799/2000000000 : ℝ)) half_12_09_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_12_09_bounds3 l).1) (fun l => (half_12_09_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_12_09_total1, half_12_09_total2, half_12_09_total3, half_12_09_total4, half_12_09_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_8) (half_10_09)
    (by simpa only [half_12_09_φ4, show (2:ℝ)*8=16 by norm_num] using half_12_09_hx4)
  exact h.weaken (by norm_num [half_12_09_total1, half_12_09_total2, half_12_09_total3, half_12_09_total4, half_12_09_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_12_09_hx2 : SourcePowerBound
    (powerBoxCross 9 10 4 half_12_09_φ2) (14650703309/1250000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 10) (u := 8) (t := 11)
    (D := 4) (ψ := (210184869/2500000000 : ℝ)) half_12_09_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_12_09_bounds2 l).1) (fun l => (half_12_09_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_12_09_total1, half_12_09_total2, half_12_09_total3, half_12_09_total4, half_12_09_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_9) (half_11_09)
    (by simpa only [half_12_09_φ3, show (2:ℝ)*4=8 by norm_num] using half_12_09_hx3)
  exact h.weaken (by norm_num [half_12_09_total1, half_12_09_total2, half_12_09_total3, half_12_09_total4, half_12_09_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_12_09_hx1 : SourcePowerBound
    (powerBoxCross 9 11 2 half_12_09_φ1) (17675703197/1250000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 11) (u := 9) (t := 12)
    (D := 2) (ψ := (451610649/5000000000 : ℝ)) half_12_09_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_12_09_bounds1 l).1) (fun l => (half_12_09_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_12_09_total1, half_12_09_total2, half_12_09_total3, half_12_09_total4, half_12_09_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_10_09) (half_12_08)
    (by simpa only [half_12_09_φ2, show (2:ℝ)*2=4 by norm_num] using half_12_09_hx2)
  exact h.weaken (by norm_num [half_12_09_total1, half_12_09_total2, half_12_09_total3, half_12_09_total4, half_12_09_total5, parameterExponent, curveLoss, dyadicExponent])

theorem half_12_09 : AdmissibleExponent 9 24 (161294209459/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 10) (ψ := (947075423/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_11_09)
    (by simpa only [half_12_09_φ1] using half_12_09_hx1)
  exact admissibleExponent_mono h (by norm_num [half_12_09_total1, half_12_09_total2, half_12_09_total3, half_12_09_total4, half_12_09_total5, parameterExponent, curveLoss, dyadicExponent])

private def half_13_09_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (487262563/5000000000 : ℝ)

private theorem half_13_09_total1 : total half_13_09_φ1=(487262563/5000000000 : ℝ) := by
  norm_num [half_13_09_φ1,total,emptyPhi,Fin.snoc]

private theorem half_13_09_bounds1 : ∀ l,0≤half_13_09_φ1 l ∧ half_13_09_φ1 l≤1 ∧
    0≤shiftExponents 9 half_13_09_φ1 l :=
  alternate_bounds_snoc emptyPhi (487262563/5000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_13_09_φ2 : Fin 2 → ℝ := Fin.snoc half_13_09_φ1 (187128917/2000000000 : ℝ)

private theorem half_13_09_total2 : total half_13_09_φ2=(1910169711/10000000000 : ℝ) := by
  change total (Fin.snoc half_13_09_φ1 (187128917/2000000000 : ℝ))=(1910169711/10000000000 : ℝ)
  rw [alternate_total_snoc,half_13_09_total1]
  norm_num

private theorem half_13_09_bounds2 : ∀ l,0≤half_13_09_φ2 l ∧ half_13_09_φ2 l≤1 ∧
    0≤shiftExponents 9 half_13_09_φ2 l :=
  alternate_bounds_snoc half_13_09_φ1 (187128917/2000000000 : ℝ) half_13_09_bounds1 (by norm_num)

private def half_13_09_φ3 : Fin 3 → ℝ := Fin.snoc half_13_09_φ2 (441222587/5000000000 : ℝ)

private theorem half_13_09_total3 : total half_13_09_φ3=(558522977/2000000000 : ℝ) := by
  change total (Fin.snoc half_13_09_φ2 (441222587/5000000000 : ℝ))=(558522977/2000000000 : ℝ)
  rw [alternate_total_snoc,half_13_09_total2]
  norm_num

private theorem half_13_09_bounds3 : ∀ l,0≤half_13_09_φ3 l ∧ half_13_09_φ3 l≤1 ∧
    0≤shiftExponents 9 half_13_09_φ3 l :=
  alternate_bounds_snoc half_13_09_φ2 (441222587/5000000000 : ℝ) half_13_09_bounds2 (by norm_num)

private def half_13_09_φ4 : Fin 4 → ℝ := Fin.snoc half_13_09_φ3 (31780443/400000000 : ℝ)

private theorem half_13_09_total4 : total half_13_09_φ4=(89678149/250000000 : ℝ) := by
  change total (Fin.snoc half_13_09_φ3 (31780443/400000000 : ℝ))=(89678149/250000000 : ℝ)
  rw [alternate_total_snoc,half_13_09_total3]
  norm_num

private theorem half_13_09_bounds4 : ∀ l,0≤half_13_09_φ4 l ∧ half_13_09_φ4 l≤1 ∧
    0≤shiftExponents 9 half_13_09_φ4 l :=
  alternate_bounds_snoc half_13_09_φ3 (31780443/400000000 : ℝ) half_13_09_bounds3 (by norm_num)

private def half_13_09_φ5 : Fin 5 → ℝ := Fin.snoc half_13_09_φ4 (60702703/1000000000 : ℝ)

private theorem half_13_09_total5 : total half_13_09_φ5=(419415299/1000000000 : ℝ) := by
  change total (Fin.snoc half_13_09_φ4 (60702703/1000000000 : ℝ))=(419415299/1000000000 : ℝ)
  rw [alternate_total_snoc,half_13_09_total4]
  norm_num

private theorem half_13_09_bounds5 : ∀ l,0≤half_13_09_φ5 l ∧ half_13_09_φ5 l≤1 ∧
    0≤shiftExponents 9 half_13_09_φ5 l :=
  alternate_bounds_snoc half_13_09_φ4 (60702703/1000000000 : ℝ) half_13_09_bounds4 (by norm_num)

private theorem half_13_09_prefix : PrefixCondition 9 half_13_09_φ5 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_13_09_φ1, half_13_09_φ2, half_13_09_φ3, half_13_09_φ4, half_13_09_φ5, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_13_09_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 32 half_13_09_φ5) (866754103/125000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_13_09_φ5
    (fun i => (half_13_09_bounds5 i).1) (fun i => (half_13_09_bounds5 i).2.1)
    (fun i => (half_13_09_bounds5 i).2.2) half_13_09_prefix
  convert h using 1 <;> norm_num [half_13_09_total1, half_13_09_total2, half_13_09_total3, half_13_09_total4, half_13_09_total5, parameterExponent, curveLoss, dyadicExponent]

private theorem half_13_09_hx5 : SourcePowerBound
    (powerBoxCross 9 8 32 half_13_09_φ5) (77668950217/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 8) (r := 2) (v := 10) (w := 11) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_13_09_φ5 (by norm_num [half_13_09_total1, half_13_09_total2, half_13_09_total3, half_13_09_total4, half_13_09_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_13_09_total1, half_13_09_total2, half_13_09_total3, half_13_09_total4, half_13_09_total5, parameterExponent, curveLoss, dyadicExponent]) half_13_09_hF2
    (half_10_09) (half_11_09)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_13_09_total1, half_13_09_total2, half_13_09_total3, half_13_09_total4, half_13_09_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_13_09_hx4 : SourcePowerBound
    (powerBoxCross 9 9 16 half_13_09_φ4) (89909057519/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 9) (u := 7) (t := 10)
    (D := 16) (ψ := (60702703/1000000000 : ℝ)) half_13_09_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_13_09_bounds4 l).1) (fun l => (half_13_09_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_13_09_total1, half_13_09_total2, half_13_09_total3, half_13_09_total4, half_13_09_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_8) (half_10_09)
    (by simpa only [half_13_09_φ5, show (2:ℝ)*16=32 by norm_num] using half_13_09_hx5)
  exact h.weaken (by norm_num [half_13_09_total1, half_13_09_total2, half_13_09_total3, half_13_09_total4, half_13_09_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_13_09_hx3 : SourcePowerBound
    (powerBoxCross 9 10 8 half_13_09_φ3) (53734487251/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 10) (u := 8) (t := 11)
    (D := 8) (ψ := (31780443/400000000 : ℝ)) half_13_09_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_13_09_bounds3 l).1) (fun l => (half_13_09_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_13_09_total1, half_13_09_total2, half_13_09_total3, half_13_09_total4, half_13_09_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_9) (half_11_09)
    (by simpa only [half_13_09_φ4, show (2:ℝ)*8=16 by norm_num] using half_13_09_hx4)
  exact h.weaken (by norm_num [half_13_09_total1, half_13_09_total2, half_13_09_total3, half_13_09_total4, half_13_09_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_13_09_hx2 : SourcePowerBound
    (powerBoxCross 9 11 4 half_13_09_φ2) (129719176617/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 11) (u := 9) (t := 12)
    (D := 4) (ψ := (441222587/5000000000 : ℝ)) half_13_09_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_13_09_bounds2 l).1) (fun l => (half_13_09_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_13_09_total1, half_13_09_total2, half_13_09_total3, half_13_09_total4, half_13_09_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_10_09) (half_12_09)
    (by simpa only [half_13_09_φ3, show (2:ℝ)*4=8 by norm_num] using half_13_09_hx3)
  exact h.weaken (by norm_num [half_13_09_total1, half_13_09_total2, half_13_09_total3, half_13_09_total4, half_13_09_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_13_09_hx1 : SourcePowerBound
    (powerBoxCross 9 12 2 half_13_09_φ1) (156550208611/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 12) (u := 10) (t := 13)
    (D := 2) (ψ := (187128917/2000000000 : ℝ)) half_13_09_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_13_09_bounds1 l).1) (fun l => (half_13_09_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_13_09_total1, half_13_09_total2, half_13_09_total3, half_13_09_total4, half_13_09_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_11_09) (half_13_08)
    (by simpa only [half_13_09_φ2, show (2:ℝ)*2=4 by norm_num] using half_13_09_hx2)
  exact h.weaken (by norm_num [half_13_09_total1, half_13_09_total2, half_13_09_total3, half_13_09_total4, half_13_09_total5, parameterExponent, curveLoss, dyadicExponent])

theorem half_13_09 : AdmissibleExponent 9 26 (178964286509/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 11) (ψ := (487262563/5000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_12_09)
    (by simpa only [half_13_09_φ1] using half_13_09_hx1)
  exact admissibleExponent_mono h (by norm_num [half_13_09_total1, half_13_09_total2, half_13_09_total3, half_13_09_total4, half_13_09_total5, parameterExponent, curveLoss, dyadicExponent])

end Waring.SeedCompletionAlternate9Seeds
