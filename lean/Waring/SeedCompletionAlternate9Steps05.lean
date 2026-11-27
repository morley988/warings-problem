import Waring.SeedCompletionAlternate9Steps04

noncomputable section
set_option maxHeartbeats 2000000
namespace Waring.SeedCompletionAlternate9Seeds
open SmoothMoments FirstStageTransport SeedCompletionNaturalBox
open SeedCompletionSourceBounds SeedCompletionPaddedSource SeedCompletionGeneralTerminal
open PolicyCompletionMajorPowerRanges SeedCompletionDivisorPowerScales
open PolicyCompletionSharpResidualSource

private def half_19_04_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (135330077/1250000000 : ℝ)

private theorem half_19_04_total1 : total half_19_04_φ1=(135330077/1250000000 : ℝ) := by
  norm_num [half_19_04_φ1,total,emptyPhi,Fin.snoc]

private theorem half_19_04_bounds1 : ∀ l,0≤half_19_04_φ1 l ∧ half_19_04_φ1 l≤1 ∧
    0≤shiftExponents 9 half_19_04_φ1 l :=
  alternate_bounds_snoc emptyPhi (135330077/1250000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_19_04_φ2 : Fin 2 → ℝ := Fin.snoc half_19_04_φ1 (1064409143/10000000000 : ℝ)

private theorem half_19_04_total2 : total half_19_04_φ2=(2147049759/10000000000 : ℝ) := by
  change total (Fin.snoc half_19_04_φ1 (1064409143/10000000000 : ℝ))=(2147049759/10000000000 : ℝ)
  rw [alternate_total_snoc,half_19_04_total1]
  norm_num

private theorem half_19_04_bounds2 : ∀ l,0≤half_19_04_φ2 l ∧ half_19_04_φ2 l≤1 ∧
    0≤shiftExponents 9 half_19_04_φ2 l :=
  alternate_bounds_snoc half_19_04_φ1 (1064409143/10000000000 : ℝ) half_19_04_bounds1 (by norm_num)

private def half_19_04_φ3 : Fin 3 → ℝ := Fin.snoc half_19_04_φ2 (981618779/10000000000 : ℝ)

private theorem half_19_04_total3 : total half_19_04_φ3=(1564334269/5000000000 : ℝ) := by
  change total (Fin.snoc half_19_04_φ2 (981618779/10000000000 : ℝ))=(1564334269/5000000000 : ℝ)
  rw [alternate_total_snoc,half_19_04_total2]
  norm_num

private theorem half_19_04_bounds3 : ∀ l,0≤half_19_04_φ3 l ∧ half_19_04_φ3 l≤1 ∧
    0≤shiftExponents 9 half_19_04_φ3 l :=
  alternate_bounds_snoc half_19_04_φ2 (981618779/10000000000 : ℝ) half_19_04_bounds2 (by norm_num)

private def half_19_04_φ4 : Fin 4 → ℝ := Fin.snoc half_19_04_φ3 (53682277/625000000 : ℝ)

private theorem half_19_04_total4 : total half_19_04_φ4=(398758497/1000000000 : ℝ) := by
  change total (Fin.snoc half_19_04_φ3 (53682277/625000000 : ℝ))=(398758497/1000000000 : ℝ)
  rw [alternate_total_snoc,half_19_04_total3]
  norm_num

private theorem half_19_04_bounds4 : ∀ l,0≤half_19_04_φ4 l ∧ half_19_04_φ4 l≤1 ∧
    0≤shiftExponents 9 half_19_04_φ4 l :=
  alternate_bounds_snoc half_19_04_φ3 (53682277/625000000 : ℝ) half_19_04_bounds3 (by norm_num)

private def half_19_04_φ5 : Fin 5 → ℝ := Fin.snoc half_19_04_φ4 (375775939/5000000000 : ℝ)

private theorem half_19_04_total5 : total half_19_04_φ5=(296196053/625000000 : ℝ) := by
  change total (Fin.snoc half_19_04_φ4 (375775939/5000000000 : ℝ))=(296196053/625000000 : ℝ)
  rw [alternate_total_snoc,half_19_04_total4]
  norm_num

private theorem half_19_04_bounds5 : ∀ l,0≤half_19_04_φ5 l ∧ half_19_04_φ5 l≤1 ∧
    0≤shiftExponents 9 half_19_04_φ5 l :=
  alternate_bounds_snoc half_19_04_φ4 (375775939/5000000000 : ℝ) half_19_04_bounds4 (by norm_num)

private def half_19_04_φ6 : Fin 6 → ℝ := Fin.snoc half_19_04_φ5 (657607893/10000000000 : ℝ)

private theorem half_19_04_total6 : total half_19_04_φ6=(5396744741/10000000000 : ℝ) := by
  change total (Fin.snoc half_19_04_φ5 (657607893/10000000000 : ℝ))=(5396744741/10000000000 : ℝ)
  rw [alternate_total_snoc,half_19_04_total5]
  norm_num

private theorem half_19_04_bounds6 : ∀ l,0≤half_19_04_φ6 l ∧ half_19_04_φ6 l≤1 ∧
    0≤shiftExponents 9 half_19_04_φ6 l :=
  alternate_bounds_snoc half_19_04_φ5 (657607893/10000000000 : ℝ) half_19_04_bounds5 (by norm_num)

private theorem half_19_04_prefix : PrefixCondition 9 half_19_04_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_19_04_φ1, half_19_04_φ2, half_19_04_φ3, half_19_04_φ4, half_19_04_φ5, half_19_04_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_19_04_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_19_04_φ6) (8809765777/1250000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_19_04_φ6
    (fun i => (half_19_04_bounds6 i).1) (fun i => (half_19_04_bounds6 i).2.1)
    (fun i => (half_19_04_bounds6 i).2.2) half_19_04_prefix
  convert h using 1 <;> norm_num [half_19_04_total1, half_19_04_total2, half_19_04_total3, half_19_04_total4, half_19_04_total5, half_19_04_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_19_04_hx6 : SourcePowerBound
    (powerBoxCross 9 13 64 half_19_04_φ6) (107420624831/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 13) (r := 2) (v := 17) (w := 18) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_19_04_φ6 (by norm_num [half_19_04_total1, half_19_04_total2, half_19_04_total3, half_19_04_total4, half_19_04_total5, half_19_04_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_19_04_total1, half_19_04_total2, half_19_04_total3, half_19_04_total4, half_19_04_total5, half_19_04_total6, parameterExponent, curveLoss, dyadicExponent]) half_19_04_hF2
    (half_17_04) (half_18_04)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_19_04_total1, half_19_04_total2, half_19_04_total3, half_19_04_total4, half_19_04_total5, half_19_04_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_19_04_hx5 : SourcePowerBound
    (powerBoxCross 9 14 32 half_19_04_φ5) (974565281/78125000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 14) (u := 12) (t := 15)
    (D := 32) (ψ := (657607893/10000000000 : ℝ)) half_19_04_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_19_04_bounds5 l).1) (fun l => (half_19_04_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_19_04_total1, half_19_04_total2, half_19_04_total3, half_19_04_total4, half_19_04_total5, half_19_04_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_13_04) (half_15_04)
    (by simpa only [half_19_04_φ6, show (2:ℝ)*32=64 by norm_num] using half_19_04_hx6)
  exact h.weaken (by norm_num [half_19_04_total1, half_19_04_total2, half_19_04_total3, half_19_04_total4, half_19_04_total5, half_19_04_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_19_04_hx4 : SourcePowerBound
    (powerBoxCross 9 15 16 half_19_04_φ4) (73551230929/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 15) (u := 13) (t := 16)
    (D := 16) (ψ := (375775939/5000000000 : ℝ)) half_19_04_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_19_04_bounds4 l).1) (fun l => (half_19_04_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_19_04_total1, half_19_04_total2, half_19_04_total3, half_19_04_total4, half_19_04_total5, half_19_04_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_14_04) (half_16_04)
    (by simpa only [half_19_04_φ5, show (2:ℝ)*16=32 by norm_num] using half_19_04_hx5)
  exact h.weaken (by norm_num [half_19_04_total1, half_19_04_total2, half_19_04_total3, half_19_04_total4, half_19_04_total5, half_19_04_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_19_04_hx3 : SourcePowerBound
    (powerBoxCross 9 16 8 half_19_04_φ3) (175650038703/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 16) (u := 14) (t := 17)
    (D := 8) (ψ := (53682277/625000000 : ℝ)) half_19_04_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_19_04_bounds3 l).1) (fun l => (half_19_04_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_19_04_total1, half_19_04_total2, half_19_04_total3, half_19_04_total4, half_19_04_total5, half_19_04_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_15_04) (half_17_04)
    (by simpa only [half_19_04_φ4, show (2:ℝ)*8=16 by norm_num] using half_19_04_hx4)
  exact h.weaken (by norm_num [half_19_04_total1, half_19_04_total2, half_19_04_total3, half_19_04_total4, half_19_04_total5, half_19_04_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_19_04_hx2 : SourcePowerBound
    (powerBoxCross 9 17 4 half_19_04_φ2) (105812149137/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 17) (u := 15) (t := 18)
    (D := 4) (ψ := (981618779/10000000000 : ℝ)) half_19_04_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_19_04_bounds2 l).1) (fun l => (half_19_04_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_19_04_total1, half_19_04_total2, half_19_04_total3, half_19_04_total4, half_19_04_total5, half_19_04_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_16_04) (half_18_04)
    (by simpa only [half_19_04_φ3, show (2:ℝ)*4=8 by norm_num] using half_19_04_hx3)
  exact h.weaken (by norm_num [half_19_04_total1, half_19_04_total2, half_19_04_total3, half_19_04_total4, half_19_04_total5, half_19_04_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_19_04_hx1 : SourcePowerBound
    (powerBoxCross 9 18 2 half_19_04_φ1) (254480258221/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 18) (u := 16) (t := 19)
    (D := 2) (ψ := (1064409143/10000000000 : ℝ)) half_19_04_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_19_04_bounds1 l).1) (fun l => (half_19_04_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_19_04_total1, half_19_04_total2, half_19_04_total3, half_19_04_total4, half_19_04_total5, half_19_04_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_17_04) (chord_72)
    (by simpa only [half_19_04_φ2, show (2:ℝ)*2=4 by norm_num] using half_19_04_hx2)
  exact h.weaken (by norm_num [half_19_04_total1, half_19_04_total2, half_19_04_total3, half_19_04_total4, half_19_04_total5, half_19_04_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_19_04 : AdmissibleExponent 9 38 (292372679781/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 17) (ψ := (135330077/1250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_18_04)
    (by simpa only [half_19_04_φ1] using half_19_04_hx1)
  exact admissibleExponent_mono h (by norm_num [half_19_04_total1, half_19_04_total2, half_19_04_total3, half_19_04_total4, half_19_04_total5, half_19_04_total6, parameterExponent, curveLoss, dyadicExponent])

theorem chord_73 : AdmissibleExponent 9 40 (124847639203/4000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 40) (t := (1/2 : ℝ))
    (half_19_04) (half_21_03)
    (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private def half_20_04_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1091674177/10000000000 : ℝ)

private theorem half_20_04_total1 : total half_20_04_φ1=(1091674177/10000000000 : ℝ) := by
  norm_num [half_20_04_φ1,total,emptyPhi,Fin.snoc]

private theorem half_20_04_bounds1 : ∀ l,0≤half_20_04_φ1 l ∧ half_20_04_φ1 l≤1 ∧
    0≤shiftExponents 9 half_20_04_φ1 l :=
  alternate_bounds_snoc emptyPhi (1091674177/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_20_04_φ2 : Fin 2 → ℝ := Fin.snoc half_20_04_φ1 (26890401/250000000 : ℝ)

private theorem half_20_04_total2 : total half_20_04_φ2=(2167290217/10000000000 : ℝ) := by
  change total (Fin.snoc half_20_04_φ1 (26890401/250000000 : ℝ))=(2167290217/10000000000 : ℝ)
  rw [alternate_total_snoc,half_20_04_total1]
  norm_num

private theorem half_20_04_bounds2 : ∀ l,0≤half_20_04_φ2 l ∧ half_20_04_φ2 l≤1 ∧
    0≤shiftExponents 9 half_20_04_φ2 l :=
  alternate_bounds_snoc half_20_04_φ1 (26890401/250000000 : ℝ) half_20_04_bounds1 (by norm_num)

private def half_20_04_φ3 : Fin 3 → ℝ := Fin.snoc half_20_04_φ2 (489544361/5000000000 : ℝ)

private theorem half_20_04_total3 : total half_20_04_φ3=(3146378939/10000000000 : ℝ) := by
  change total (Fin.snoc half_20_04_φ2 (489544361/5000000000 : ℝ))=(3146378939/10000000000 : ℝ)
  rw [alternate_total_snoc,half_20_04_total2]
  norm_num

private theorem half_20_04_bounds3 : ∀ l,0≤half_20_04_φ3 l ∧ half_20_04_φ3 l≤1 ∧
    0≤shiftExponents 9 half_20_04_φ3 l :=
  alternate_bounds_snoc half_20_04_φ2 (489544361/5000000000 : ℝ) half_20_04_bounds2 (by norm_num)

private def half_20_04_φ4 : Fin 4 → ℝ := Fin.snoc half_20_04_φ3 (107087829/1250000000 : ℝ)

private theorem half_20_04_total4 : total half_20_04_φ4=(4003081571/10000000000 : ℝ) := by
  change total (Fin.snoc half_20_04_φ3 (107087829/1250000000 : ℝ))=(4003081571/10000000000 : ℝ)
  rw [alternate_total_snoc,half_20_04_total3]
  norm_num

private theorem half_20_04_bounds4 : ∀ l,0≤half_20_04_φ4 l ∧ half_20_04_φ4 l≤1 ∧
    0≤shiftExponents 9 half_20_04_φ4 l :=
  alternate_bounds_snoc half_20_04_φ3 (107087829/1250000000 : ℝ) half_20_04_bounds3 (by norm_num)

private def half_20_04_φ5 : Fin 5 → ℝ := Fin.snoc half_20_04_φ4 (749614803/10000000000 : ℝ)

private theorem half_20_04_total5 : total half_20_04_φ5=(2376348187/5000000000 : ℝ) := by
  change total (Fin.snoc half_20_04_φ4 (749614803/10000000000 : ℝ))=(2376348187/5000000000 : ℝ)
  rw [alternate_total_snoc,half_20_04_total4]
  norm_num

private theorem half_20_04_bounds5 : ∀ l,0≤half_20_04_φ5 l ∧ half_20_04_φ5 l≤1 ∧
    0≤shiftExponents 9 half_20_04_φ5 l :=
  alternate_bounds_snoc half_20_04_φ4 (749614803/10000000000 : ℝ) half_20_04_bounds4 (by norm_num)

private def half_20_04_φ6 : Fin 6 → ℝ := Fin.snoc half_20_04_φ5 (81989119/1250000000 : ℝ)

private theorem half_20_04_total6 : total half_20_04_φ6=(2704304663/5000000000 : ℝ) := by
  change total (Fin.snoc half_20_04_φ5 (81989119/1250000000 : ℝ))=(2704304663/5000000000 : ℝ)
  rw [alternate_total_snoc,half_20_04_total5]
  norm_num

private theorem half_20_04_bounds6 : ∀ l,0≤half_20_04_φ6 l ∧ half_20_04_φ6 l≤1 ∧
    0≤shiftExponents 9 half_20_04_φ6 l :=
  alternate_bounds_snoc half_20_04_φ5 (81989119/1250000000 : ℝ) half_20_04_bounds5 (by norm_num)

private theorem half_20_04_prefix : PrefixCondition 9 half_20_04_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_20_04_φ1, half_20_04_φ2, half_20_04_φ3, half_20_04_φ4, half_20_04_φ5, half_20_04_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_20_04_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_20_04_φ6) (4387086011/625000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_20_04_φ6
    (fun i => (half_20_04_bounds6 i).1) (fun i => (half_20_04_bounds6 i).2.1)
    (fun i => (half_20_04_bounds6 i).2.2) half_20_04_prefix
  convert h using 1 <;> norm_num [half_20_04_total1, half_20_04_total2, half_20_04_total3, half_20_04_total4, half_20_04_total5, half_20_04_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_20_04_hx6 : SourcePowerBound
    (powerBoxCross 9 14 64 half_20_04_φ6) (115998486221/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 14) (r := 2) (v := 18) (w := 19) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_20_04_φ6 (by norm_num [half_20_04_total1, half_20_04_total2, half_20_04_total3, half_20_04_total4, half_20_04_total5, half_20_04_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_20_04_total1, half_20_04_total2, half_20_04_total3, half_20_04_total4, half_20_04_total5, half_20_04_total6, parameterExponent, curveLoss, dyadicExponent]) half_20_04_hF2
    (half_18_04) (half_19_04)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_20_04_total1, half_20_04_total2, half_20_04_total3, half_20_04_total4, half_20_04_total5, half_20_04_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_04_hx5 : SourcePowerBound
    (powerBoxCross 9 15 32 half_20_04_φ5) (67201024031/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 15) (u := 13) (t := 16)
    (D := 32) (ψ := (81989119/1250000000 : ℝ)) half_20_04_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_04_bounds5 l).1) (fun l => (half_20_04_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_04_total1, half_20_04_total2, half_20_04_total3, half_20_04_total4, half_20_04_total5, half_20_04_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_14_04) (half_16_04)
    (by simpa only [half_20_04_φ6, show (2:ℝ)*32=64 by norm_num] using half_20_04_hx6)
  exact h.weaken (by norm_num [half_20_04_total1, half_20_04_total2, half_20_04_total3, half_20_04_total4, half_20_04_total5, half_20_04_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_04_hx4 : SourcePowerBound
    (powerBoxCross 9 16 16 half_20_04_φ4) (158125840693/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 16) (u := 14) (t := 17)
    (D := 16) (ψ := (749614803/10000000000 : ℝ)) half_20_04_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_04_bounds4 l).1) (fun l => (half_20_04_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_04_total1, half_20_04_total2, half_20_04_total3, half_20_04_total4, half_20_04_total5, half_20_04_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_15_04) (half_17_04)
    (by simpa only [half_20_04_φ5, show (2:ℝ)*16=32 by norm_num] using half_20_04_hx5)
  exact h.weaken (by norm_num [half_20_04_total1, half_20_04_total2, half_20_04_total3, half_20_04_total4, half_20_04_total5, half_20_04_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_04_hx3 : SourcePowerBound
    (powerBoxCross 9 17 8 half_20_04_φ3) (94145216461/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 17) (u := 15) (t := 18)
    (D := 8) (ψ := (107087829/1250000000 : ℝ)) half_20_04_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_04_bounds3 l).1) (fun l => (half_20_04_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_04_total1, half_20_04_total2, half_20_04_total3, half_20_04_total4, half_20_04_total5, half_20_04_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_16_04) (half_18_04)
    (by simpa only [half_20_04_φ4, show (2:ℝ)*8=16 by norm_num] using half_20_04_hx4)
  exact h.weaken (by norm_num [half_20_04_total1, half_20_04_total2, half_20_04_total3, half_20_04_total4, half_20_04_total5, half_20_04_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_04_hx2 : SourcePowerBound
    (powerBoxCross 9 18 4 half_20_04_φ2) (226134536967/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 18) (u := 16) (t := 19)
    (D := 4) (ψ := (489544361/5000000000 : ℝ)) half_20_04_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_04_bounds2 l).1) (fun l => (half_20_04_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_04_total1, half_20_04_total2, half_20_04_total3, half_20_04_total4, half_20_04_total5, half_20_04_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_17_04) (half_19_04)
    (by simpa only [half_20_04_φ3, show (2:ℝ)*4=8 by norm_num] using half_20_04_hx3)
  exact h.weaken (by norm_num [half_20_04_total1, half_20_04_total2, half_20_04_total3, half_20_04_total4, half_20_04_total5, half_20_04_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_04_hx1 : SourcePowerBound
    (powerBoxCross 9 19 2 half_20_04_φ1) (67886695877/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 19) (u := 17) (t := 20)
    (D := 2) (ψ := (26890401/250000000 : ℝ)) half_20_04_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_04_bounds1 l).1) (fun l => (half_20_04_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_04_total1, half_20_04_total2, half_20_04_total3, half_20_04_total4, half_20_04_total5, half_20_04_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_18_04) (chord_73)
    (by simpa only [half_20_04_φ2, show (2:ℝ)*2=4 by norm_num] using half_20_04_hx2)
  exact h.weaken (by norm_num [half_20_04_total1, half_20_04_total2, half_20_04_total3, half_20_04_total4, half_20_04_total5, half_20_04_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_20_04 : AdmissibleExponent 9 40 (311938728057/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 18) (ψ := (1091674177/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_19_04)
    (by simpa only [half_20_04_φ1] using half_20_04_hx1)
  exact admissibleExponent_mono h (by norm_num [half_20_04_total1, half_20_04_total2, half_20_04_total3, half_20_04_total4, half_20_04_total5, half_20_04_total6, parameterExponent, curveLoss, dyadicExponent])

theorem chord_74 : AdmissibleExponent 9 42 (66371445463/2000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 42) (t := (1/2 : ℝ))
    (half_20_04) (half_22_03)
    (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private def half_21_04_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1101090461/10000000000 : ℝ)

private theorem half_21_04_total1 : total half_21_04_φ1=(1101090461/10000000000 : ℝ) := by
  norm_num [half_21_04_φ1,total,emptyPhi,Fin.snoc]

private theorem half_21_04_bounds1 : ∀ l,0≤half_21_04_φ1 l ∧ half_21_04_φ1 l≤1 ∧
    0≤shiftExponents 9 half_21_04_φ1 l :=
  alternate_bounds_snoc emptyPhi (1101090461/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_21_04_φ2 : Fin 2 → ℝ := Fin.snoc half_21_04_φ1 (542409909/5000000000 : ℝ)

private theorem half_21_04_total2 : total half_21_04_φ2=(2185910279/10000000000 : ℝ) := by
  change total (Fin.snoc half_21_04_φ1 (542409909/5000000000 : ℝ))=(2185910279/10000000000 : ℝ)
  rw [alternate_total_snoc,half_21_04_total1]
  norm_num

private theorem half_21_04_bounds2 : ∀ l,0≤half_21_04_φ2 l ∧ half_21_04_φ2 l≤1 ∧
    0≤shiftExponents 9 half_21_04_φ2 l :=
  alternate_bounds_snoc half_21_04_φ1 (542409909/5000000000 : ℝ) half_21_04_bounds1 (by norm_num)

private def half_21_04_φ3 : Fin 3 → ℝ := Fin.snoc half_21_04_φ2 (195352243/2000000000 : ℝ)

private theorem half_21_04_total3 : total half_21_04_φ3=(1581335747/5000000000 : ℝ) := by
  change total (Fin.snoc half_21_04_φ2 (195352243/2000000000 : ℝ))=(1581335747/5000000000 : ℝ)
  rw [alternate_total_snoc,half_21_04_total2]
  norm_num

private theorem half_21_04_bounds3 : ∀ l,0≤half_21_04_φ3 l ∧ half_21_04_φ3 l≤1 ∧
    0≤shiftExponents 9 half_21_04_φ3 l :=
  alternate_bounds_snoc half_21_04_φ2 (195352243/2000000000 : ℝ) half_21_04_bounds2 (by norm_num)

private def half_21_04_φ4 : Fin 4 → ℝ := Fin.snoc half_21_04_φ3 (854666063/10000000000 : ℝ)

private theorem half_21_04_total4 : total half_21_04_φ4=(4017337557/10000000000 : ℝ) := by
  change total (Fin.snoc half_21_04_φ3 (854666063/10000000000 : ℝ))=(4017337557/10000000000 : ℝ)
  rw [alternate_total_snoc,half_21_04_total3]
  norm_num

private theorem half_21_04_bounds4 : ∀ l,0≤half_21_04_φ4 l ∧ half_21_04_φ4 l≤1 ∧
    0≤shiftExponents 9 half_21_04_φ4 l :=
  alternate_bounds_snoc half_21_04_φ3 (854666063/10000000000 : ℝ) half_21_04_bounds3 (by norm_num)

private def half_21_04_φ5 : Fin 5 → ℝ := Fin.snoc half_21_04_φ4 (149566561/2000000000 : ℝ)

private theorem half_21_04_total5 : total half_21_04_φ5=(2382585181/5000000000 : ℝ) := by
  change total (Fin.snoc half_21_04_φ4 (149566561/2000000000 : ℝ))=(2382585181/5000000000 : ℝ)
  rw [alternate_total_snoc,half_21_04_total4]
  norm_num

private theorem half_21_04_bounds5 : ∀ l,0≤half_21_04_φ5 l ∧ half_21_04_φ5 l≤1 ∧
    0≤shiftExponents 9 half_21_04_φ5 l :=
  alternate_bounds_snoc half_21_04_φ4 (149566561/2000000000 : ℝ) half_21_04_bounds4 (by norm_num)

private def half_21_04_φ6 : Fin 6 → ℝ := Fin.snoc half_21_04_φ5 (81794213/1250000000 : ℝ)

private theorem half_21_04_total6 : total half_21_04_φ6=(2709762033/5000000000 : ℝ) := by
  change total (Fin.snoc half_21_04_φ5 (81794213/1250000000 : ℝ))=(2709762033/5000000000 : ℝ)
  rw [alternate_total_snoc,half_21_04_total5]
  norm_num

private theorem half_21_04_bounds6 : ∀ l,0≤half_21_04_φ6 l ∧ half_21_04_φ6 l≤1 ∧
    0≤shiftExponents 9 half_21_04_φ6 l :=
  alternate_bounds_snoc half_21_04_φ5 (81794213/1250000000 : ℝ) half_21_04_bounds5 (by norm_num)

private theorem half_21_04_prefix : PrefixCondition 9 half_21_04_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_21_04_φ1, half_21_04_φ2, half_21_04_φ3, half_21_04_φ4, half_21_04_φ5, half_21_04_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_21_04_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_21_04_φ6) (4370713901/625000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_21_04_φ6
    (fun i => (half_21_04_bounds6 i).1) (fun i => (half_21_04_bounds6 i).2.1)
    (fun i => (half_21_04_bounds6 i).2.2) half_21_04_prefix
  convert h using 1 <;> norm_num [half_21_04_total1, half_21_04_total2, half_21_04_total3, half_21_04_total4, half_21_04_total5, half_21_04_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_21_04_hx6 : SourcePowerBound
    (powerBoxCross 9 15 64 half_21_04_φ6) (124644943361/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 15) (r := 2) (v := 0) (w := 20) (D := 64)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_21_04_φ6 (by norm_num [half_21_04_total1, half_21_04_total2, half_21_04_total3, half_21_04_total4, half_21_04_total5, half_21_04_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_21_04_total1, half_21_04_total2, half_21_04_total3, half_21_04_total4, half_21_04_total5, half_21_04_total6, parameterExponent, curveLoss, dyadicExponent]) half_21_04_hF2
    (admissibleExponent_zero 9) (half_20_04)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_21_04_total1, half_21_04_total2, half_21_04_total3, half_21_04_total4, half_21_04_total5, half_21_04_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_21_04_hx5 : SourcePowerBound
    (powerBoxCross 9 16 32 half_21_04_φ5) (72075477647/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 16) (u := 14) (t := 17)
    (D := 32) (ψ := (81794213/1250000000 : ℝ)) half_21_04_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_21_04_bounds5 l).1) (fun l => (half_21_04_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_21_04_total1, half_21_04_total2, half_21_04_total3, half_21_04_total4, half_21_04_total5, half_21_04_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_15_04) (half_17_04)
    (by simpa only [half_21_04_φ6, show (2:ℝ)*32=64 by norm_num] using half_21_04_hx6)
  exact h.weaken (by norm_num [half_21_04_total1, half_21_04_total2, half_21_04_total3, half_21_04_total4, half_21_04_total5, half_21_04_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_21_04_hx4 : SourcePowerBound
    (powerBoxCross 9 17 16 half_21_04_φ4) (42311337261/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 17) (u := 15) (t := 18)
    (D := 16) (ψ := (149566561/2000000000 : ℝ)) half_21_04_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_21_04_bounds4 l).1) (fun l => (half_21_04_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_21_04_total1, half_21_04_total2, half_21_04_total3, half_21_04_total4, half_21_04_total5, half_21_04_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_16_04) (half_18_04)
    (by simpa only [half_21_04_φ5, show (2:ℝ)*16=32 by norm_num] using half_21_04_hx5)
  exact h.weaken (by norm_num [half_21_04_total1, half_21_04_total2, half_21_04_total3, half_21_04_total4, half_21_04_total5, half_21_04_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_21_04_hx3 : SourcePowerBound
    (powerBoxCross 9 18 8 half_21_04_φ3) (100513190739/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 18) (u := 16) (t := 19)
    (D := 8) (ψ := (854666063/10000000000 : ℝ)) half_21_04_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_21_04_bounds3 l).1) (fun l => (half_21_04_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_21_04_total1, half_21_04_total2, half_21_04_total3, half_21_04_total4, half_21_04_total5, half_21_04_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_17_04) (half_19_04)
    (by simpa only [half_21_04_φ4, show (2:ℝ)*8=16 by norm_num] using half_21_04_hx4)
  exact h.weaken (by norm_num [half_21_04_total1, half_21_04_total2, half_21_04_total3, half_21_04_total4, half_21_04_total5, half_21_04_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_21_04_hx2 : SourcePowerBound
    (powerBoxCross 9 19 4 half_21_04_φ2) (240738731311/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 19) (u := 17) (t := 20)
    (D := 4) (ψ := (195352243/2000000000 : ℝ)) half_21_04_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_21_04_bounds2 l).1) (fun l => (half_21_04_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_21_04_total1, half_21_04_total2, half_21_04_total3, half_21_04_total4, half_21_04_total5, half_21_04_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_18_04) (half_20_04)
    (by simpa only [half_21_04_φ3, show (2:ℝ)*4=8 by norm_num] using half_21_04_hx3)
  exact h.weaken (by norm_num [half_21_04_total1, half_21_04_total2, half_21_04_total3, half_21_04_total4, half_21_04_total5, half_21_04_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_21_04_hx1 : SourcePowerBound
    (powerBoxCross 9 20 2 half_21_04_φ1) (72173135683/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 20) (u := 18) (t := 21)
    (D := 2) (ψ := (542409909/5000000000 : ℝ)) half_21_04_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_21_04_bounds1 l).1) (fun l => (half_21_04_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_21_04_total1, half_21_04_total2, half_21_04_total3, half_21_04_total4, half_21_04_total5, half_21_04_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_19_04) (chord_74)
    (by simpa only [half_21_04_φ2, show (2:ℝ)*2=4 by norm_num] using half_21_04_hx2)
  exact h.weaken (by norm_num [half_21_04_total1, half_21_04_total2, half_21_04_total3, half_21_04_total4, half_21_04_total5, half_21_04_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_21_04 : AdmissibleExponent 9 42 (331635070711/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 19) (ψ := (1101090461/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_20_04)
    (by simpa only [half_21_04_φ1] using half_21_04_hx1)
  exact admissibleExponent_mono h (by norm_num [half_21_04_total1, half_21_04_total2, half_21_04_total3, half_21_04_total4, half_21_04_total5, half_21_04_total6, parameterExponent, curveLoss, dyadicExponent])

private def half_22_04_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1111111111/10000000000 : ℝ)

private theorem half_22_04_total1 : total half_22_04_φ1=(1111111111/10000000000 : ℝ) := by
  norm_num [half_22_04_φ1,total,emptyPhi,Fin.snoc]

private theorem half_22_04_bounds1 : ∀ l,0≤half_22_04_φ1 l ∧ half_22_04_φ1 l≤1 ∧
    0≤shiftExponents 9 half_22_04_φ1 l :=
  alternate_bounds_snoc emptyPhi (1111111111/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_22_04_φ2 : Fin 2 → ℝ := Fin.snoc half_22_04_φ1 (68314153/625000000 : ℝ)

private theorem half_22_04_total2 : total half_22_04_φ2=(2204137559/10000000000 : ℝ) := by
  change total (Fin.snoc half_22_04_φ1 (68314153/625000000 : ℝ))=(2204137559/10000000000 : ℝ)
  rw [alternate_total_snoc,half_22_04_total1]
  norm_num

private theorem half_22_04_bounds2 : ∀ l,0≤half_22_04_φ2 l ∧ half_22_04_φ2 l≤1 ∧
    0≤shiftExponents 9 half_22_04_φ2 l :=
  alternate_bounds_snoc half_22_04_φ1 (68314153/625000000 : ℝ) half_22_04_bounds1 (by norm_num)

private def half_22_04_φ3 : Fin 3 → ℝ := Fin.snoc half_22_04_φ2 (194896561/2000000000 : ℝ)

private theorem half_22_04_total3 : total half_22_04_φ3=(794655091/2500000000 : ℝ) := by
  change total (Fin.snoc half_22_04_φ2 (194896561/2000000000 : ℝ))=(794655091/2500000000 : ℝ)
  rw [alternate_total_snoc,half_22_04_total2]
  norm_num

private theorem half_22_04_bounds3 : ∀ l,0≤half_22_04_φ3 l ∧ half_22_04_φ3 l≤1 ∧
    0≤shiftExponents 9 half_22_04_φ3 l :=
  alternate_bounds_snoc half_22_04_φ2 (194896561/2000000000 : ℝ) half_22_04_bounds2 (by norm_num)

private def half_22_04_φ4 : Fin 4 → ℝ := Fin.snoc half_22_04_φ3 (426336227/5000000000 : ℝ)

private theorem half_22_04_total4 : total half_22_04_φ4=(2015646409/5000000000 : ℝ) := by
  change total (Fin.snoc half_22_04_φ3 (426336227/5000000000 : ℝ))=(2015646409/5000000000 : ℝ)
  rw [alternate_total_snoc,half_22_04_total3]
  norm_num

private theorem half_22_04_bounds4 : ∀ l,0≤half_22_04_φ4 l ∧ half_22_04_φ4 l≤1 ∧
    0≤shiftExponents 9 half_22_04_φ4 l :=
  alternate_bounds_snoc half_22_04_φ3 (426336227/5000000000 : ℝ) half_22_04_bounds3 (by norm_num)

private def half_22_04_φ5 : Fin 5 → ℝ := Fin.snoc half_22_04_φ4 (746088397/10000000000 : ℝ)

private theorem half_22_04_total5 : total half_22_04_φ5=(955476243/2000000000 : ℝ) := by
  change total (Fin.snoc half_22_04_φ4 (746088397/10000000000 : ℝ))=(955476243/2000000000 : ℝ)
  rw [alternate_total_snoc,half_22_04_total4]
  norm_num

private theorem half_22_04_bounds5 : ∀ l,0≤half_22_04_φ5 l ∧ half_22_04_φ5 l≤1 ∧
    0≤shiftExponents 9 half_22_04_φ5 l :=
  alternate_bounds_snoc half_22_04_φ4 (746088397/10000000000 : ℝ) half_22_04_bounds4 (by norm_num)

private def half_22_04_φ6 : Fin 6 → ℝ := Fin.snoc half_22_04_φ5 (652827347/10000000000 : ℝ)

private theorem half_22_04_total6 : total half_22_04_φ6=(2715104281/5000000000 : ℝ) := by
  change total (Fin.snoc half_22_04_φ5 (652827347/10000000000 : ℝ))=(2715104281/5000000000 : ℝ)
  rw [alternate_total_snoc,half_22_04_total5]
  norm_num

private theorem half_22_04_bounds6 : ∀ l,0≤half_22_04_φ6 l ∧ half_22_04_φ6 l≤1 ∧
    0≤shiftExponents 9 half_22_04_φ6 l :=
  alternate_bounds_snoc half_22_04_φ5 (652827347/10000000000 : ℝ) half_22_04_bounds5 (by norm_num)

private theorem half_22_04_prefix : PrefixCondition 9 half_22_04_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_22_04_φ1, half_22_04_φ2, half_22_04_φ3, half_22_04_φ4, half_22_04_φ5, half_22_04_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_22_04_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_22_04_φ6) (4354687157/625000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_22_04_φ6
    (fun i => (half_22_04_bounds6 i).1) (fun i => (half_22_04_bounds6 i).2.1)
    (fun i => (half_22_04_bounds6 i).2.2) half_22_04_prefix
  convert h using 1 <;> norm_num [half_22_04_total1, half_22_04_total2, half_22_04_total3, half_22_04_total4, half_22_04_total5, half_22_04_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_22_04_hx6 : SourcePowerBound
    (powerBoxCross 9 16 64 half_22_04_φ6) (133382446547/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 16) (r := 2) (v := 21) (w := 22) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_22_04_φ6 (by norm_num [half_22_04_total1, half_22_04_total2, half_22_04_total3, half_22_04_total4, half_22_04_total5, half_22_04_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_22_04_total1, half_22_04_total2, half_22_04_total3, half_22_04_total4, half_22_04_total5, half_22_04_total6, parameterExponent, curveLoss, dyadicExponent]) half_22_04_hF2
    (half_21_04) (half_22_03)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_22_04_total1, half_22_04_total2, half_22_04_total3, half_22_04_total4, half_22_04_total5, half_22_04_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_22_04_hx5 : SourcePowerBound
    (powerBoxCross 9 17 32 half_22_04_φ5) (76987856177/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 17) (u := 15) (t := 18)
    (D := 32) (ψ := (652827347/10000000000 : ℝ)) half_22_04_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_22_04_bounds5 l).1) (fun l => (half_22_04_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_22_04_total1, half_22_04_total2, half_22_04_total3, half_22_04_total4, half_22_04_total5, half_22_04_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_16_04) (half_18_04)
    (by simpa only [half_22_04_φ6, show (2:ℝ)*32=64 by norm_num] using half_22_04_hx6)
  exact h.weaken (by norm_num [half_22_04_total1, half_22_04_total2, half_22_04_total3, half_22_04_total4, half_22_04_total5, half_22_04_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_22_04_hx4 : SourcePowerBound
    (powerBoxCross 9 18 16 half_22_04_φ4) (180427489137/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 18) (u := 16) (t := 19)
    (D := 16) (ψ := (746088397/10000000000 : ℝ)) half_22_04_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_22_04_bounds4 l).1) (fun l => (half_22_04_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_22_04_total1, half_22_04_total2, half_22_04_total3, half_22_04_total4, half_22_04_total5, half_22_04_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_17_04) (half_19_04)
    (by simpa only [half_22_04_φ5, show (2:ℝ)*16=32 by norm_num] using half_22_04_hx5)
  exact h.weaken (by norm_num [half_22_04_total1, half_22_04_total2, half_22_04_total3, half_22_04_total4, half_22_04_total5, half_22_04_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_22_04_hx3 : SourcePowerBound
    (powerBoxCross 9 19 8 half_22_04_φ3) (10690682771/500000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 19) (u := 17) (t := 20)
    (D := 8) (ψ := (426336227/5000000000 : ℝ)) half_22_04_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_22_04_bounds3 l).1) (fun l => (half_22_04_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_22_04_total1, half_22_04_total2, half_22_04_total3, half_22_04_total4, half_22_04_total5, half_22_04_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_18_04) (half_20_04)
    (by simpa only [half_22_04_φ4, show (2:ℝ)*8=16 by norm_num] using half_22_04_hx4)
  exact h.weaken (by norm_num [half_22_04_total1, half_22_04_total2, half_22_04_total3, half_22_04_total4, half_22_04_total5, half_22_04_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_22_04_hx2 : SourcePowerBound
    (powerBoxCross 9 20 4 half_22_04_φ2) (255387278961/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 20) (u := 18) (t := 21)
    (D := 4) (ψ := (194896561/2000000000 : ℝ)) half_22_04_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_22_04_bounds2 l).1) (fun l => (half_22_04_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_22_04_total1, half_22_04_total2, half_22_04_total3, half_22_04_total4, half_22_04_total5, half_22_04_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_19_04) (half_21_04)
    (by simpa only [half_22_04_φ3, show (2:ℝ)*4=8 by norm_num] using half_22_04_hx3)
  exact h.weaken (by norm_num [half_22_04_total1, half_22_04_total2, half_22_04_total3, half_22_04_total4, half_22_04_total5, half_22_04_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_22_04_hx1 : SourcePowerBound
    (powerBoxCross 9 21 2 half_22_04_φ1) (305907978141/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 21) (u := 19) (t := 22)
    (D := 2) (ψ := (68314153/625000000 : ℝ)) half_22_04_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_22_04_bounds1 l).1) (fun l => (half_22_04_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_22_04_total1, half_22_04_total2, half_22_04_total3, half_22_04_total4, half_22_04_total5, half_22_04_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_20_04) (half_22_03)
    (by simpa only [half_22_04_φ2, show (2:ℝ)*2=4 by norm_num] using half_22_04_hx2)
  exact h.weaken (by norm_num [half_22_04_total1, half_22_04_total2, half_22_04_total3, half_22_04_total4, half_22_04_total5, half_22_04_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_22_04 : AdmissibleExponent 9 44 (87865883423/2500000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 20) (ψ := (1111111111/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_21_04)
    (by simpa only [half_22_04_φ1] using half_22_04_hx1)
  exact admissibleExponent_mono h (by norm_num [half_22_04_total1, half_22_04_total2, half_22_04_total3, half_22_04_total4, half_22_04_total5, half_22_04_total6, parameterExponent, curveLoss, dyadicExponent])

private def half_10_05_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (110214749/1250000000 : ℝ)

private theorem half_10_05_total1 : total half_10_05_φ1=(110214749/1250000000 : ℝ) := by
  norm_num [half_10_05_φ1,total,emptyPhi,Fin.snoc]

private theorem half_10_05_bounds1 : ∀ l,0≤half_10_05_φ1 l ∧ half_10_05_φ1 l≤1 ∧
    0≤shiftExponents 9 half_10_05_φ1 l :=
  alternate_bounds_snoc emptyPhi (110214749/1250000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_10_05_φ2 : Fin 2 → ℝ := Fin.snoc half_10_05_φ1 (410793381/5000000000 : ℝ)

private theorem half_10_05_total2 : total half_10_05_φ2=(851652377/5000000000 : ℝ) := by
  change total (Fin.snoc half_10_05_φ1 (410793381/5000000000 : ℝ))=(851652377/5000000000 : ℝ)
  rw [alternate_total_snoc,half_10_05_total1]
  norm_num

private theorem half_10_05_bounds2 : ∀ l,0≤half_10_05_φ2 l ∧ half_10_05_φ2 l≤1 ∧
    0≤shiftExponents 9 half_10_05_φ2 l :=
  alternate_bounds_snoc half_10_05_φ1 (410793381/5000000000 : ℝ) half_10_05_bounds1 (by norm_num)

private def half_10_05_φ3 : Fin 3 → ℝ := Fin.snoc half_10_05_φ2 (89639791/1250000000 : ℝ)

private theorem half_10_05_total3 : total half_10_05_φ3=(1210211541/5000000000 : ℝ) := by
  change total (Fin.snoc half_10_05_φ2 (89639791/1250000000 : ℝ))=(1210211541/5000000000 : ℝ)
  rw [alternate_total_snoc,half_10_05_total2]
  norm_num

private theorem half_10_05_bounds3 : ∀ l,0≤half_10_05_φ3 l ∧ half_10_05_φ3 l≤1 ∧
    0≤shiftExponents 9 half_10_05_φ3 l :=
  alternate_bounds_snoc half_10_05_φ2 (89639791/1250000000 : ℝ) half_10_05_bounds2 (by norm_num)

private def half_10_05_φ4 : Fin 4 → ℝ := Fin.snoc half_10_05_φ3 (45047027/1000000000 : ℝ)

private theorem half_10_05_total4 : total half_10_05_φ4=(358861669/1250000000 : ℝ) := by
  change total (Fin.snoc half_10_05_φ3 (45047027/1000000000 : ℝ))=(358861669/1250000000 : ℝ)
  rw [alternate_total_snoc,half_10_05_total3]
  norm_num

private theorem half_10_05_bounds4 : ∀ l,0≤half_10_05_φ4 l ∧ half_10_05_φ4 l≤1 ∧
    0≤shiftExponents 9 half_10_05_φ4 l :=
  alternate_bounds_snoc half_10_05_φ3 (45047027/1000000000 : ℝ) half_10_05_bounds3 (by norm_num)

private theorem half_10_05_prefix : PrefixCondition 9 half_10_05_φ4 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_10_05_φ1, half_10_05_φ2, half_10_05_φ3, half_10_05_φ4, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_10_05_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 16 half_10_05_φ4) (1110914993/156250000 : ℝ) := by
  have h := padded_dyadic_divisor_power (k := 9) (j := 4) (r := 0) (n := 1) (D := 16)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_10_05_φ4
    (fun i => (half_10_05_bounds4 i).1) (fun i => (half_10_05_bounds4 i).2.1)
    (fun i => (half_10_05_bounds4 i).2.2) half_10_05_prefix
  convert h using 1 <;> norm_num [half_10_05_total1, half_10_05_total2, half_10_05_total3, half_10_05_total4, parameterExponent, curveLoss, dyadicExponent]

private theorem half_10_05_hx4 : SourcePowerBound
    (powerBoxCross 9 6 16 half_10_05_φ4) (34562602379/5000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 6) (r := 2) (v := 0) (w := 8) (D := 16)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_10_05_φ4 (by norm_num [half_10_05_total1, half_10_05_total2, half_10_05_total3, half_10_05_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_10_05_total1, half_10_05_total2, half_10_05_total3, half_10_05_total4, parameterExponent, curveLoss, dyadicExponent]) half_10_05_hF2
    (admissibleExponent_zero 9) (SeedCompletionHigher9SimpleSeeds.degree9_half_8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_10_05_total1, half_10_05_total2, half_10_05_total3, half_10_05_total4, parameterExponent, curveLoss, dyadicExponent])

private theorem half_10_05_hx3 : SourcePowerBound
    (powerBoxCross 9 7 8 half_10_05_φ3) (19688837061/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 7) (u := 5) (t := 8)
    (D := 8) (ψ := (45047027/1000000000 : ℝ)) half_10_05_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_10_05_bounds3 l).1) (fun l => (half_10_05_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_10_05_total1, half_10_05_total2, half_10_05_total3, half_10_05_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionNinthSecondSeeds.ninth_half_6) (SeedCompletionHigher9SimpleSeeds.degree9_half_8)
    (by simpa only [half_10_05_φ4, show (2:ℝ)*8=16 by norm_num] using half_10_05_hx4)
  exact h.weaken (by norm_num [half_10_05_total1, half_10_05_total2, half_10_05_total3, half_10_05_total4, parameterExponent, curveLoss, dyadicExponent])

private theorem half_10_05_hx2 : SourcePowerBound
    (powerBoxCross 9 8 4 half_10_05_φ2) (93448698321/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 8) (u := 6) (t := 9)
    (D := 4) (ψ := (89639791/1250000000 : ℝ)) half_10_05_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_10_05_bounds2 l).1) (fun l => (half_10_05_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_10_05_total1, half_10_05_total2, half_10_05_total3, half_10_05_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionNinthSecondSeeds.ninth_half_7) (SeedCompletionHigher9SimpleSeeds.degree9_half_9)
    (by simpa only [half_10_05_φ3, show (2:ℝ)*4=8 by norm_num] using half_10_05_hx3)
  exact h.weaken (by norm_num [half_10_05_total1, half_10_05_total2, half_10_05_total3, half_10_05_total4, parameterExponent, curveLoss, dyadicExponent])

private theorem half_10_05_hx1 : SourcePowerBound
    (powerBoxCross 9 9 2 half_10_05_φ1) (56241099387/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 9) (u := 7) (t := 10)
    (D := 2) (ψ := (410793381/5000000000 : ℝ)) half_10_05_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_10_05_bounds1 l).1) (fun l => (half_10_05_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_10_05_total1, half_10_05_total2, half_10_05_total3, half_10_05_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_8) (half_10_04)
    (by simpa only [half_10_05_φ2, show (2:ℝ)*2=4 by norm_num] using half_10_05_hx2)
  exact h.weaken (by norm_num [half_10_05_total1, half_10_05_total2, half_10_05_total3, half_10_05_total4, parameterExponent, curveLoss, dyadicExponent])

theorem half_10_05 : AdmissibleExponent 9 20 (63735702319/5000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 8) (ψ := (110214749/1250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (SeedCompletionHigher9SimpleSeeds.degree9_half_9)
    (by simpa only [half_10_05_φ1] using half_10_05_hx1)
  exact admissibleExponent_mono h (by norm_num [half_10_05_total1, half_10_05_total2, half_10_05_total3, half_10_05_total4, parameterExponent, curveLoss, dyadicExponent])

private def half_11_05_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (183753843/2000000000 : ℝ)

private theorem half_11_05_total1 : total half_11_05_φ1=(183753843/2000000000 : ℝ) := by
  norm_num [half_11_05_φ1,total,emptyPhi,Fin.snoc]

private theorem half_11_05_bounds1 : ∀ l,0≤half_11_05_φ1 l ∧ half_11_05_φ1 l≤1 ∧
    0≤shiftExponents 9 half_11_05_φ1 l :=
  alternate_bounds_snoc emptyPhi (183753843/2000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_11_05_φ2 : Fin 2 → ℝ := Fin.snoc half_11_05_φ1 (865845831/10000000000 : ℝ)

private theorem half_11_05_total2 : total half_11_05_φ2=(892307523/5000000000 : ℝ) := by
  change total (Fin.snoc half_11_05_φ1 (865845831/10000000000 : ℝ))=(892307523/5000000000 : ℝ)
  rw [alternate_total_snoc,half_11_05_total1]
  norm_num

private theorem half_11_05_bounds2 : ∀ l,0≤half_11_05_φ2 l ∧ half_11_05_φ2 l≤1 ∧
    0≤shiftExponents 9 half_11_05_φ2 l :=
  alternate_bounds_snoc half_11_05_φ1 (865845831/10000000000 : ℝ) half_11_05_bounds1 (by norm_num)

private def half_11_05_φ3 : Fin 3 → ℝ := Fin.snoc half_11_05_φ2 (394187001/5000000000 : ℝ)

private theorem half_11_05_total3 : total half_11_05_φ3=(321623631/1250000000 : ℝ) := by
  change total (Fin.snoc half_11_05_φ2 (394187001/5000000000 : ℝ))=(321623631/1250000000 : ℝ)
  rw [alternate_total_snoc,half_11_05_total2]
  norm_num

private theorem half_11_05_bounds3 : ∀ l,0≤half_11_05_φ3 l ∧ half_11_05_φ3 l≤1 ∧
    0≤shiftExponents 9 half_11_05_φ3 l :=
  alternate_bounds_snoc half_11_05_φ2 (394187001/5000000000 : ℝ) half_11_05_bounds2 (by norm_num)

private def half_11_05_φ4 : Fin 4 → ℝ := Fin.snoc half_11_05_φ3 (62559853/1000000000 : ℝ)

private theorem half_11_05_total4 : total half_11_05_φ4=(1599293789/5000000000 : ℝ) := by
  change total (Fin.snoc half_11_05_φ3 (62559853/1000000000 : ℝ))=(1599293789/5000000000 : ℝ)
  rw [alternate_total_snoc,half_11_05_total3]
  norm_num

private theorem half_11_05_bounds4 : ∀ l,0≤half_11_05_φ4 l ∧ half_11_05_φ4 l≤1 ∧
    0≤shiftExponents 9 half_11_05_φ4 l :=
  alternate_bounds_snoc half_11_05_φ3 (62559853/1000000000 : ℝ) half_11_05_bounds3 (by norm_num)

private theorem half_11_05_prefix : PrefixCondition 9 half_11_05_φ4 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_11_05_φ1, half_11_05_φ2, half_11_05_φ3, half_11_05_φ4, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_11_05_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 16 half_11_05_φ4) (3952118633/625000000 : ℝ) := by
  have h := padded_dyadic_divisor_power (k := 9) (j := 4) (r := 0) (n := 1) (D := 16)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_11_05_φ4
    (fun i => (half_11_05_bounds4 i).1) (fun i => (half_11_05_bounds4 i).2.1)
    (fun i => (half_11_05_bounds4 i).2.2) half_11_05_prefix
  convert h using 1 <;> norm_num [half_11_05_total1, half_11_05_total2, half_11_05_total3, half_11_05_total4, parameterExponent, curveLoss, dyadicExponent]

private theorem half_11_05_hx4 : SourcePowerBound
    (powerBoxCross 9 7 16 half_11_05_φ4) (2355484129/312500000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 7) (r := 2) (v := 9) (w := 10) (D := 16)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_11_05_φ4 (by norm_num [half_11_05_total1, half_11_05_total2, half_11_05_total3, half_11_05_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_11_05_total1, half_11_05_total2, half_11_05_total3, half_11_05_total4, parameterExponent, curveLoss, dyadicExponent]) half_11_05_hF2
    (SeedCompletionHigher9SimpleSeeds.degree9_half_9) (half_10_05)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_11_05_total1, half_11_05_total2, half_11_05_total3, half_11_05_total4, parameterExponent, curveLoss, dyadicExponent])

private theorem half_11_05_hx3 : SourcePowerBound
    (powerBoxCross 9 8 8 half_11_05_φ3) (5489995291/625000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 8) (u := 6) (t := 9)
    (D := 8) (ψ := (62559853/1000000000 : ℝ)) half_11_05_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_11_05_bounds3 l).1) (fun l => (half_11_05_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_11_05_total1, half_11_05_total2, half_11_05_total3, half_11_05_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionNinthSecondSeeds.ninth_half_7) (SeedCompletionHigher9SimpleSeeds.degree9_half_9)
    (by simpa only [half_11_05_φ4, show (2:ℝ)*8=16 by norm_num] using half_11_05_hx4)
  exact h.weaken (by norm_num [half_11_05_total1, half_11_05_total2, half_11_05_total3, half_11_05_total4, parameterExponent, curveLoss, dyadicExponent])

private theorem half_11_05_hx2 : SourcePowerBound
    (powerBoxCross 9 9 4 half_11_05_φ2) (52527820073/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 9) (u := 7) (t := 10)
    (D := 4) (ψ := (394187001/5000000000 : ℝ)) half_11_05_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_11_05_bounds2 l).1) (fun l => (half_11_05_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_11_05_total1, half_11_05_total2, half_11_05_total3, half_11_05_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_8) (half_10_05)
    (by simpa only [half_11_05_φ3, show (2:ℝ)*4=8 by norm_num] using half_11_05_hx3)
  exact h.weaken (by norm_num [half_11_05_total1, half_11_05_total2, half_11_05_total3, half_11_05_total4, parameterExponent, curveLoss, dyadicExponent])

private theorem half_11_05_hx1 : SourcePowerBound
    (powerBoxCross 9 10 2 half_11_05_φ1) (63339246813/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 10) (u := 8) (t := 11)
    (D := 2) (ψ := (865845831/10000000000 : ℝ)) half_11_05_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_11_05_bounds1 l).1) (fun l => (half_11_05_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_11_05_total1, half_11_05_total2, half_11_05_total3, half_11_05_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_9) (half_11_04)
    (by simpa only [half_11_05_φ2, show (2:ℝ)*2=4 by norm_num] using half_11_05_hx2)
  exact h.weaken (by norm_num [half_11_05_total1, half_11_05_total2, half_11_05_total3, half_11_05_total4, parameterExponent, curveLoss, dyadicExponent])

theorem half_11_05 : AdmissibleExponent 9 22 (144135108711/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 9) (ψ := (183753843/2000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_10_05)
    (by simpa only [half_11_05_φ1] using half_11_05_hx1)
  exact admissibleExponent_mono h (by norm_num [half_11_05_total1, half_11_05_total2, half_11_05_total3, half_11_05_total4, parameterExponent, curveLoss, dyadicExponent])

private def half_12_05_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (951409489/10000000000 : ℝ)

private theorem half_12_05_total1 : total half_12_05_φ1=(951409489/10000000000 : ℝ) := by
  norm_num [half_12_05_φ1,total,emptyPhi,Fin.snoc]

private theorem half_12_05_bounds1 : ∀ l,0≤half_12_05_φ1 l ∧ half_12_05_φ1 l≤1 ∧
    0≤shiftExponents 9 half_12_05_φ1 l :=
  alternate_bounds_snoc emptyPhi (951409489/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_12_05_φ2 : Fin 2 → ℝ := Fin.snoc half_12_05_φ1 (903951077/10000000000 : ℝ)

private theorem half_12_05_total2 : total half_12_05_φ2=(927680283/5000000000 : ℝ) := by
  change total (Fin.snoc half_12_05_φ1 (903951077/10000000000 : ℝ))=(927680283/5000000000 : ℝ)
  rw [alternate_total_snoc,half_12_05_total1]
  norm_num

private theorem half_12_05_bounds2 : ∀ l,0≤half_12_05_φ2 l ∧ half_12_05_φ2 l≤1 ∧
    0≤shiftExponents 9 half_12_05_φ2 l :=
  alternate_bounds_snoc half_12_05_φ1 (903951077/10000000000 : ℝ) half_12_05_bounds1 (by norm_num)

private def half_12_05_φ3 : Fin 3 → ℝ := Fin.snoc half_12_05_φ2 (841171337/10000000000 : ℝ)

private theorem half_12_05_total3 : total half_12_05_φ3=(2696531903/10000000000 : ℝ) := by
  change total (Fin.snoc half_12_05_φ2 (841171337/10000000000 : ℝ))=(2696531903/10000000000 : ℝ)
  rw [alternate_total_snoc,half_12_05_total2]
  norm_num

private theorem half_12_05_bounds3 : ∀ l,0≤half_12_05_φ3 l ∧ half_12_05_φ3 l≤1 ∧
    0≤shiftExponents 9 half_12_05_φ3 l :=
  alternate_bounds_snoc half_12_05_φ2 (841171337/10000000000 : ℝ) half_12_05_bounds2 (by norm_num)

private def half_12_05_φ4 : Fin 4 → ℝ := Fin.snoc half_12_05_φ3 (728353179/10000000000 : ℝ)

private theorem half_12_05_total4 : total half_12_05_φ4=(1712442541/5000000000 : ℝ) := by
  change total (Fin.snoc half_12_05_φ3 (728353179/10000000000 : ℝ))=(1712442541/5000000000 : ℝ)
  rw [alternate_total_snoc,half_12_05_total3]
  norm_num

private theorem half_12_05_bounds4 : ∀ l,0≤half_12_05_φ4 l ∧ half_12_05_φ4 l≤1 ∧
    0≤shiftExponents 9 half_12_05_φ4 l :=
  alternate_bounds_snoc half_12_05_φ3 (728353179/10000000000 : ℝ) half_12_05_bounds3 (by norm_num)

private def half_12_05_φ5 : Fin 5 → ℝ := Fin.snoc half_12_05_φ4 (56447657/1250000000 : ℝ)

private theorem half_12_05_total5 : total half_12_05_φ5=(1938233169/5000000000 : ℝ) := by
  change total (Fin.snoc half_12_05_φ4 (56447657/1250000000 : ℝ))=(1938233169/5000000000 : ℝ)
  rw [alternate_total_snoc,half_12_05_total4]
  norm_num

private theorem half_12_05_bounds5 : ∀ l,0≤half_12_05_φ5 l ∧ half_12_05_φ5 l≤1 ∧
    0≤shiftExponents 9 half_12_05_φ5 l :=
  alternate_bounds_snoc half_12_05_φ4 (56447657/1250000000 : ℝ) half_12_05_bounds4 (by norm_num)

private theorem half_12_05_prefix : PrefixCondition 9 half_12_05_φ5 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_12_05_φ1, half_12_05_φ2, half_12_05_φ3, half_12_05_φ4, half_12_05_φ5, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_12_05_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 32 half_12_05_φ5) (4810300493/625000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_12_05_φ5
    (fun i => (half_12_05_bounds5 i).1) (fun i => (half_12_05_bounds5 i).2.1)
    (fun i => (half_12_05_bounds5 i).2.2) half_12_05_prefix
  convert h using 1 <;> norm_num [half_12_05_total1, half_12_05_total2, half_12_05_total3, half_12_05_total4, half_12_05_total5, parameterExponent, curveLoss, dyadicExponent]

private theorem half_12_05_hx5 : SourcePowerBound
    (powerBoxCross 9 7 32 half_12_05_φ5) (7287133271/1000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 7) (r := 2) (v := 9) (w := 10) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_12_05_φ5 (by norm_num [half_12_05_total1, half_12_05_total2, half_12_05_total3, half_12_05_total4, half_12_05_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_12_05_total1, half_12_05_total2, half_12_05_total3, half_12_05_total4, half_12_05_total5, parameterExponent, curveLoss, dyadicExponent]) half_12_05_hF2
    (SeedCompletionHigher9SimpleSeeds.degree9_half_9) (half_10_05)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_12_05_total1, half_12_05_total2, half_12_05_total3, half_12_05_total4, half_12_05_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_12_05_hx4 : SourcePowerBound
    (powerBoxCross 9 8 16 half_12_05_φ4) (82303021653/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 8) (u := 6) (t := 9)
    (D := 16) (ψ := (56447657/1250000000 : ℝ)) half_12_05_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_12_05_bounds4 l).1) (fun l => (half_12_05_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_12_05_total1, half_12_05_total2, half_12_05_total3, half_12_05_total4, half_12_05_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionNinthSecondSeeds.ninth_half_7) (SeedCompletionHigher9SimpleSeeds.degree9_half_9)
    (by simpa only [half_12_05_φ5, show (2:ℝ)*16=32 by norm_num] using half_12_05_hx5)
  exact h.weaken (by norm_num [half_12_05_total1, half_12_05_total2, half_12_05_total3, half_12_05_total4, half_12_05_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_12_05_hx3 : SourcePowerBound
    (powerBoxCross 9 9 8 half_12_05_φ3) (9737719891/1000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 9) (u := 7) (t := 10)
    (D := 8) (ψ := (728353179/10000000000 : ℝ)) half_12_05_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_12_05_bounds3 l).1) (fun l => (half_12_05_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_12_05_total1, half_12_05_total2, half_12_05_total3, half_12_05_total4, half_12_05_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_8) (half_10_05)
    (by simpa only [half_12_05_φ4, show (2:ℝ)*8=16 by norm_num] using half_12_05_hx4)
  exact h.weaken (by norm_num [half_12_05_total1, half_12_05_total2, half_12_05_total3, half_12_05_total4, half_12_05_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_12_05_hx2 : SourcePowerBound
    (powerBoxCross 9 10 4 half_12_05_φ2) (29278384517/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 10) (u := 8) (t := 11)
    (D := 4) (ψ := (841171337/10000000000 : ℝ)) half_12_05_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_12_05_bounds2 l).1) (fun l => (half_12_05_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_12_05_total1, half_12_05_total2, half_12_05_total3, half_12_05_total4, half_12_05_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_9) (half_11_05)
    (by simpa only [half_12_05_φ3, show (2:ℝ)*4=8 by norm_num] using half_12_05_hx3)
  exact h.weaken (by norm_num [half_12_05_total1, half_12_05_total2, half_12_05_total3, half_12_05_total4, half_12_05_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_12_05_hx1 : SourcePowerBound
    (powerBoxCross 9 11 2 half_12_05_φ1) (141373367191/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 11) (u := 9) (t := 12)
    (D := 2) (ψ := (903951077/10000000000 : ℝ)) half_12_05_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_12_05_bounds1 l).1) (fun l => (half_12_05_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_12_05_total1, half_12_05_total2, half_12_05_total3, half_12_05_total4, half_12_05_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_10_05) (half_12_04)
    (by simpa only [half_12_05_φ2, show (2:ℝ)*2=4 by norm_num] using half_12_05_hx2)
  exact h.weaken (by norm_num [half_12_05_total1, half_12_05_total2, half_12_05_total3, half_12_05_total4, half_12_05_total5, parameterExponent, curveLoss, dyadicExponent])

theorem half_12_05 : AdmissibleExponent 9 24 (8067648323/500000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 10) (ψ := (951409489/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_11_05)
    (by simpa only [half_12_05_φ1] using half_12_05_hx1)
  exact admissibleExponent_mono h (by norm_num [half_12_05_total1, half_12_05_total2, half_12_05_total3, half_12_05_total4, half_12_05_total5, parameterExponent, curveLoss, dyadicExponent])

private def half_13_05_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (979969121/10000000000 : ℝ)

private theorem half_13_05_total1 : total half_13_05_φ1=(979969121/10000000000 : ℝ) := by
  norm_num [half_13_05_φ1,total,emptyPhi,Fin.snoc]

private theorem half_13_05_bounds1 : ∀ l,0≤half_13_05_φ1 l ∧ half_13_05_φ1 l≤1 ∧
    0≤shiftExponents 9 half_13_05_φ1 l :=
  alternate_bounds_snoc emptyPhi (979969121/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_13_05_φ2 : Fin 2 → ℝ := Fin.snoc half_13_05_φ1 (936383693/10000000000 : ℝ)

private theorem half_13_05_total2 : total half_13_05_φ2=(958176407/5000000000 : ℝ) := by
  change total (Fin.snoc half_13_05_φ1 (936383693/10000000000 : ℝ))=(958176407/5000000000 : ℝ)
  rw [alternate_total_snoc,half_13_05_total1]
  norm_num

private theorem half_13_05_bounds2 : ∀ l,0≤half_13_05_φ2 l ∧ half_13_05_φ2 l≤1 ∧
    0≤shiftExponents 9 half_13_05_φ2 l :=
  alternate_bounds_snoc half_13_05_φ1 (936383693/10000000000 : ℝ) half_13_05_bounds1 (by norm_num)

private def half_13_05_φ3 : Fin 3 → ℝ := Fin.snoc half_13_05_φ2 (35334743/400000000 : ℝ)

private theorem half_13_05_total3 : total half_13_05_φ3=(2799721389/10000000000 : ℝ) := by
  change total (Fin.snoc half_13_05_φ2 (35334743/400000000 : ℝ))=(2799721389/10000000000 : ℝ)
  rw [alternate_total_snoc,half_13_05_total2]
  norm_num

private theorem half_13_05_bounds3 : ∀ l,0≤half_13_05_φ3 l ∧ half_13_05_φ3 l≤1 ∧
    0≤shiftExponents 9 half_13_05_φ3 l :=
  alternate_bounds_snoc half_13_05_φ2 (35334743/400000000 : ℝ) half_13_05_bounds2 (by norm_num)

private def half_13_05_φ4 : Fin 4 → ℝ := Fin.snoc half_13_05_φ3 (39782319/500000000 : ℝ)

private theorem half_13_05_total4 : total half_13_05_φ4=(3595367769/10000000000 : ℝ) := by
  change total (Fin.snoc half_13_05_φ3 (39782319/500000000 : ℝ))=(3595367769/10000000000 : ℝ)
  rw [alternate_total_snoc,half_13_05_total3]
  norm_num

private theorem half_13_05_bounds4 : ∀ l,0≤half_13_05_φ4 l ∧ half_13_05_φ4 l≤1 ∧
    0≤shiftExponents 9 half_13_05_φ4 l :=
  alternate_bounds_snoc half_13_05_φ3 (39782319/500000000 : ℝ) half_13_05_bounds3 (by norm_num)

private def half_13_05_φ5 : Fin 5 → ℝ := Fin.snoc half_13_05_φ4 (609519317/10000000000 : ℝ)

private theorem half_13_05_total5 : total half_13_05_φ5=(2102443543/5000000000 : ℝ) := by
  change total (Fin.snoc half_13_05_φ4 (609519317/10000000000 : ℝ))=(2102443543/5000000000 : ℝ)
  rw [alternate_total_snoc,half_13_05_total4]
  norm_num

private theorem half_13_05_bounds5 : ∀ l,0≤half_13_05_φ5 l ∧ half_13_05_φ5 l≤1 ∧
    0≤shiftExponents 9 half_13_05_φ5 l :=
  alternate_bounds_snoc half_13_05_φ4 (609519317/10000000000 : ℝ) half_13_05_bounds4 (by norm_num)

private theorem half_13_05_prefix : PrefixCondition 9 half_13_05_φ5 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_13_05_φ1, half_13_05_φ2, half_13_05_φ3, half_13_05_φ4, half_13_05_φ5, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_13_05_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 32 half_13_05_φ5) (4317669371/625000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_13_05_φ5
    (fun i => (half_13_05_bounds5 i).1) (fun i => (half_13_05_bounds5 i).2.1)
    (fun i => (half_13_05_bounds5 i).2.2) half_13_05_prefix
  convert h using 1 <;> norm_num [half_13_05_total1, half_13_05_total2, half_13_05_total3, half_13_05_total4, half_13_05_total5, parameterExponent, curveLoss, dyadicExponent]

private theorem half_13_05_hx5 : SourcePowerBound
    (powerBoxCross 9 8 32 half_13_05_φ5) (77502418557/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 8) (r := 2) (v := 10) (w := 11) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_13_05_φ5 (by norm_num [half_13_05_total1, half_13_05_total2, half_13_05_total3, half_13_05_total4, half_13_05_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_13_05_total1, half_13_05_total2, half_13_05_total3, half_13_05_total4, half_13_05_total5, parameterExponent, curveLoss, dyadicExponent]) half_13_05_hF2
    (half_10_05) (half_11_05)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_13_05_total1, half_13_05_total2, half_13_05_total3, half_13_05_total4, half_13_05_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_13_05_hx4 : SourcePowerBound
    (powerBoxCross 9 9 16 half_13_05_φ4) (44880753207/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 9) (u := 7) (t := 10)
    (D := 16) (ψ := (609519317/10000000000 : ℝ)) half_13_05_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_13_05_bounds4 l).1) (fun l => (half_13_05_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_13_05_total1, half_13_05_total2, half_13_05_total3, half_13_05_total4, half_13_05_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_8) (half_10_05)
    (by simpa only [half_13_05_φ5, show (2:ℝ)*16=32 by norm_num] using half_13_05_hx5)
  exact h.weaken (by norm_num [half_13_05_total1, half_13_05_total2, half_13_05_total3, half_13_05_total4, half_13_05_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_13_05_hx3 : SourcePowerBound
    (powerBoxCross 9 10 8 half_13_05_φ3) (107335508899/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 10) (u := 8) (t := 11)
    (D := 8) (ψ := (39782319/500000000 : ℝ)) half_13_05_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_13_05_bounds3 l).1) (fun l => (half_13_05_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_13_05_total1, half_13_05_total2, half_13_05_total3, half_13_05_total4, half_13_05_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_9) (half_11_05)
    (by simpa only [half_13_05_φ4, show (2:ℝ)*8=16 by norm_num] using half_13_05_hx4)
  exact h.weaken (by norm_num [half_13_05_total1, half_13_05_total2, half_13_05_total3, half_13_05_total4, half_13_05_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_13_05_hx2 : SourcePowerBound
    (powerBoxCross 9 11 4 half_13_05_φ2) (3240259183/250000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 11) (u := 9) (t := 12)
    (D := 4) (ψ := (35334743/400000000 : ℝ)) half_13_05_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_13_05_bounds2 l).1) (fun l => (half_13_05_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_13_05_total1, half_13_05_total2, half_13_05_total3, half_13_05_total4, half_13_05_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_10_05) (half_12_05)
    (by simpa only [half_13_05_φ3, show (2:ℝ)*4=8 by norm_num] using half_13_05_hx3)
  exact h.weaken (by norm_num [half_13_05_total1, half_13_05_total2, half_13_05_total3, half_13_05_total4, half_13_05_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_13_05_hx1 : SourcePowerBound
    (powerBoxCross 9 12 2 half_13_05_φ1) (156520843111/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 12) (u := 10) (t := 13)
    (D := 2) (ψ := (936383693/10000000000 : ℝ)) half_13_05_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_13_05_bounds1 l).1) (fun l => (half_13_05_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_13_05_total1, half_13_05_total2, half_13_05_total3, half_13_05_total4, half_13_05_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_11_05) (half_13_04)
    (by simpa only [half_13_05_φ2, show (2:ℝ)*2=4 by norm_num] using half_13_05_hx2)
  exact h.weaken (by norm_num [half_13_05_total1, half_13_05_total2, half_13_05_total3, half_13_05_total4, half_13_05_total5, parameterExponent, curveLoss, dyadicExponent])

theorem half_13_05 : AdmissibleExponent 9 26 (89530066447/5000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 11) (ψ := (979969121/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_12_05)
    (by simpa only [half_13_05_φ1] using half_13_05_hx1)
  exact admissibleExponent_mono h (by norm_num [half_13_05_total1, half_13_05_total2, half_13_05_total3, half_13_05_total4, half_13_05_total5, parameterExponent, curveLoss, dyadicExponent])

private def half_14_05_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1005106557/10000000000 : ℝ)

private theorem half_14_05_total1 : total half_14_05_φ1=(1005106557/10000000000 : ℝ) := by
  norm_num [half_14_05_φ1,total,emptyPhi,Fin.snoc]

private theorem half_14_05_bounds1 : ∀ l,0≤half_14_05_φ1 l ∧ half_14_05_φ1 l≤1 ∧
    0≤shiftExponents 9 half_14_05_φ1 l :=
  alternate_bounds_snoc emptyPhi (1005106557/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_14_05_φ2 : Fin 2 → ℝ := Fin.snoc half_14_05_φ1 (96571059/1000000000 : ℝ)

private theorem half_14_05_total2 : total half_14_05_φ2=(1970817147/10000000000 : ℝ) := by
  change total (Fin.snoc half_14_05_φ1 (96571059/1000000000 : ℝ))=(1970817147/10000000000 : ℝ)
  rw [alternate_total_snoc,half_14_05_total1]
  norm_num

private theorem half_14_05_bounds2 : ∀ l,0≤half_14_05_φ2 l ∧ half_14_05_φ2 l≤1 ∧
    0≤shiftExponents 9 half_14_05_φ2 l :=
  alternate_bounds_snoc half_14_05_φ1 (96571059/1000000000 : ℝ) half_14_05_bounds1 (by norm_num)

private def half_14_05_φ3 : Fin 3 → ℝ := Fin.snoc half_14_05_φ2 (921363707/10000000000 : ℝ)

private theorem half_14_05_total3 : total half_14_05_φ3=(1446090427/5000000000 : ℝ) := by
  change total (Fin.snoc half_14_05_φ2 (921363707/10000000000 : ℝ))=(1446090427/5000000000 : ℝ)
  rw [alternate_total_snoc,half_14_05_total2]
  norm_num

private theorem half_14_05_bounds3 : ∀ l,0≤half_14_05_φ3 l ∧ half_14_05_φ3 l≤1 ∧
    0≤shiftExponents 9 half_14_05_φ3 l :=
  alternate_bounds_snoc half_14_05_φ2 (921363707/10000000000 : ℝ) half_14_05_bounds2 (by norm_num)

private def half_14_05_φ4 : Fin 4 → ℝ := Fin.snoc half_14_05_φ3 (853548077/10000000000 : ℝ)

private theorem half_14_05_total4 : total half_14_05_φ4=(3745728931/10000000000 : ℝ) := by
  change total (Fin.snoc half_14_05_φ3 (853548077/10000000000 : ℝ))=(3745728931/10000000000 : ℝ)
  rw [alternate_total_snoc,half_14_05_total3]
  norm_num

private theorem half_14_05_bounds4 : ∀ l,0≤half_14_05_φ4 l ∧ half_14_05_φ4 l≤1 ∧
    0≤shiftExponents 9 half_14_05_φ4 l :=
  alternate_bounds_snoc half_14_05_φ3 (853548077/10000000000 : ℝ) half_14_05_bounds3 (by norm_num)

private def half_14_05_φ5 : Fin 5 → ℝ := Fin.snoc half_14_05_φ4 (145177553/2000000000 : ℝ)

private theorem half_14_05_total5 : total half_14_05_φ5=(558952087/1250000000 : ℝ) := by
  change total (Fin.snoc half_14_05_φ4 (145177553/2000000000 : ℝ))=(558952087/1250000000 : ℝ)
  rw [alternate_total_snoc,half_14_05_total4]
  norm_num

private theorem half_14_05_bounds5 : ∀ l,0≤half_14_05_φ5 l ∧ half_14_05_φ5 l≤1 ∧
    0≤shiftExponents 9 half_14_05_φ5 l :=
  alternate_bounds_snoc half_14_05_φ4 (145177553/2000000000 : ℝ) half_14_05_bounds4 (by norm_num)

private def half_14_05_φ6 : Fin 6 → ℝ := Fin.snoc half_14_05_φ5 (105563289/2500000000 : ℝ)

private theorem half_14_05_total6 : total half_14_05_φ6=(1223467463/2500000000 : ℝ) := by
  change total (Fin.snoc half_14_05_φ5 (105563289/2500000000 : ℝ))=(1223467463/2500000000 : ℝ)
  rw [alternate_total_snoc,half_14_05_total5]
  norm_num

private theorem half_14_05_bounds6 : ∀ l,0≤half_14_05_φ6 l ∧ half_14_05_φ6 l≤1 ∧
    0≤shiftExponents 9 half_14_05_φ6 l :=
  alternate_bounds_snoc half_14_05_φ5 (105563289/2500000000 : ℝ) half_14_05_bounds5 (by norm_num)

private theorem half_14_05_prefix : PrefixCondition 9 half_14_05_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_14_05_φ1, half_14_05_φ2, half_14_05_φ3, half_14_05_φ4, half_14_05_φ5, half_14_05_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_14_05_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_14_05_φ6) (2579597611/312500000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_14_05_φ6
    (fun i => (half_14_05_bounds6 i).1) (fun i => (half_14_05_bounds6 i).2.1)
    (fun i => (half_14_05_bounds6 i).2.2) half_14_05_prefix
  convert h using 1 <;> norm_num [half_14_05_total1, half_14_05_total2, half_14_05_total3, half_14_05_total4, half_14_05_total5, half_14_05_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_14_05_hF1 : SourcePowerBound
    (paddedMoment 9 0 1 64 half_14_05_φ6) (964032537/312500000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 0) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_14_05_φ6
    (fun i => (half_14_05_bounds6 i).1) (fun i => (half_14_05_bounds6 i).2.1)
    (fun i => (half_14_05_bounds6 i).2.2) half_14_05_prefix
  convert h using 1 <;> norm_num [half_14_05_total1, half_14_05_total2, half_14_05_total3, half_14_05_total4, half_14_05_total5, half_14_05_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_14_05_hx6 : SourcePowerBound
    (powerBoxCross 9 8 64 half_14_05_φ6) (73688220787/10000000000 : ℝ) := by
  have h := full_B_cross_power (k := 9) (s := 8) (r := 1) (v := 2) (t := 11) (D := 64)
    (a := (1/22 : ℝ)) (b := (5/22 : ℝ)) (c := (8/11 : ℝ))
    (by norm_num) half_14_05_φ6 (by norm_num [half_14_05_total1, half_14_05_total2, half_14_05_total3, half_14_05_total4, half_14_05_total5, half_14_05_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_14_05_total1, half_14_05_total2, half_14_05_total3, half_14_05_total4, half_14_05_total5, half_14_05_total6, parameterExponent, curveLoss, dyadicExponent]) half_14_05_hF1 half_14_05_hF2
    (half_11_05)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_14_05_total1, half_14_05_total2, half_14_05_total3, half_14_05_total4, half_14_05_total5, half_14_05_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_14_05_hx5 : SourcePowerBound
    (powerBoxCross 9 9 32 half_14_05_φ5) (82360081537/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 9) (u := 7) (t := 10)
    (D := 32) (ψ := (105563289/2500000000 : ℝ)) half_14_05_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_14_05_bounds5 l).1) (fun l => (half_14_05_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_14_05_total1, half_14_05_total2, half_14_05_total3, half_14_05_total4, half_14_05_total5, half_14_05_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_8) (half_10_05)
    (by simpa only [half_14_05_φ6, show (2:ℝ)*32=64 by norm_num] using half_14_05_hx6)
  exact h.weaken (by norm_num [half_14_05_total1, half_14_05_total2, half_14_05_total3, half_14_05_total4, half_14_05_total5, half_14_05_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_14_05_hx4 : SourcePowerBound
    (powerBoxCross 9 10 16 half_14_05_φ4) (97440173069/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 10) (u := 8) (t := 11)
    (D := 16) (ψ := (145177553/2000000000 : ℝ)) half_14_05_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_14_05_bounds4 l).1) (fun l => (half_14_05_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_14_05_total1, half_14_05_total2, half_14_05_total3, half_14_05_total4, half_14_05_total5, half_14_05_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_9) (half_11_05)
    (by simpa only [half_14_05_φ5, show (2:ℝ)*16=32 by norm_num] using half_14_05_hx5)
  exact h.weaken (by norm_num [half_14_05_total1, half_14_05_total2, half_14_05_total3, half_14_05_total4, half_14_05_total5, half_14_05_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_14_05_hx3 : SourcePowerBound
    (powerBoxCross 9 11 8 half_14_05_φ3) (14700431883/1250000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 11) (u := 9) (t := 12)
    (D := 8) (ψ := (853548077/10000000000 : ℝ)) half_14_05_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_14_05_bounds3 l).1) (fun l => (half_14_05_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_14_05_total1, half_14_05_total2, half_14_05_total3, half_14_05_total4, half_14_05_total5, half_14_05_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_10_05) (half_12_05)
    (by simpa only [half_14_05_φ4, show (2:ℝ)*8=16 by norm_num] using half_14_05_hx4)
  exact h.weaken (by norm_num [half_14_05_total1, half_14_05_total2, half_14_05_total3, half_14_05_total4, half_14_05_total5, half_14_05_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_14_05_hx2 : SourcePowerBound
    (powerBoxCross 9 12 4 half_14_05_φ2) (71239052651/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 12) (u := 10) (t := 13)
    (D := 4) (ψ := (921363707/10000000000 : ℝ)) half_14_05_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_14_05_bounds2 l).1) (fun l => (half_14_05_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_14_05_total1, half_14_05_total2, half_14_05_total3, half_14_05_total4, half_14_05_total5, half_14_05_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_11_05) (half_13_05)
    (by simpa only [half_14_05_φ3, show (2:ℝ)*4=8 by norm_num] using half_14_05_hx3)
  exact h.weaken (by norm_num [half_14_05_total1, half_14_05_total2, half_14_05_total3, half_14_05_total4, half_14_05_total5, half_14_05_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_14_05_hx1 : SourcePowerBound
    (powerBoxCross 9 13 2 half_14_05_φ1) (172067788091/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 13) (u := 11) (t := 14)
    (D := 2) (ψ := (96571059/1000000000 : ℝ)) half_14_05_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_14_05_bounds1 l).1) (fun l => (half_14_05_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_14_05_total1, half_14_05_total2, half_14_05_total3, half_14_05_total4, half_14_05_total5, half_14_05_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_12_05) (half_14_04)
    (by simpa only [half_14_05_φ2, show (2:ℝ)*2=4 by norm_num] using half_14_05_hx2)
  exact h.weaken (by norm_num [half_14_05_total1, half_14_05_total2, half_14_05_total3, half_14_05_total4, half_14_05_total5, half_14_05_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_14_05 : AdmissibleExponent 9 28 (12324715751/625000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 12) (ψ := (1005106557/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_13_05)
    (by simpa only [half_14_05_φ1] using half_14_05_hx1)
  exact admissibleExponent_mono h (by norm_num [half_14_05_total1, half_14_05_total2, half_14_05_total3, half_14_05_total4, half_14_05_total5, half_14_05_total6, parameterExponent, curveLoss, dyadicExponent])

private def half_15_05_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (20507479/200000000 : ℝ)

private theorem half_15_05_total1 : total half_15_05_φ1=(20507479/200000000 : ℝ) := by
  norm_num [half_15_05_φ1,total,emptyPhi,Fin.snoc]

private theorem half_15_05_bounds1 : ∀ l,0≤half_15_05_φ1 l ∧ half_15_05_φ1 l≤1 ∧
    0≤shiftExponents 9 half_15_05_φ1 l :=
  alternate_bounds_snoc emptyPhi (20507479/200000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_15_05_φ2 : Fin 2 → ℝ := Fin.snoc half_15_05_φ1 (198070479/2000000000 : ℝ)

private theorem half_15_05_total2 : total half_15_05_φ2=(403145269/2000000000 : ℝ) := by
  change total (Fin.snoc half_15_05_φ1 (198070479/2000000000 : ℝ))=(403145269/2000000000 : ℝ)
  rw [alternate_total_snoc,half_15_05_total1]
  norm_num

private theorem half_15_05_bounds2 : ∀ l,0≤half_15_05_φ2 l ∧ half_15_05_φ2 l≤1 ∧
    0≤shiftExponents 9 half_15_05_φ2 l :=
  alternate_bounds_snoc half_15_05_φ1 (198070479/2000000000 : ℝ) half_15_05_bounds1 (by norm_num)

private def half_15_05_φ3 : Fin 3 → ℝ := Fin.snoc half_15_05_φ2 (38066251/400000000 : ℝ)

private theorem half_15_05_total3 : total half_15_05_φ3=(148369131/500000000 : ℝ) := by
  change total (Fin.snoc half_15_05_φ2 (38066251/400000000 : ℝ))=(148369131/500000000 : ℝ)
  rw [alternate_total_snoc,half_15_05_total2]
  norm_num

private theorem half_15_05_bounds3 : ∀ l,0≤half_15_05_φ3 l ∧ half_15_05_φ3 l≤1 ∧
    0≤shiftExponents 9 half_15_05_φ3 l :=
  alternate_bounds_snoc half_15_05_φ2 (38066251/400000000 : ℝ) half_15_05_bounds2 (by norm_num)

private def half_15_05_φ4 : Fin 4 → ℝ := Fin.snoc half_15_05_φ3 (219769293/2500000000 : ℝ)

private theorem half_15_05_total4 : total half_15_05_φ4=(240403737/625000000 : ℝ) := by
  change total (Fin.snoc half_15_05_φ3 (219769293/2500000000 : ℝ))=(240403737/625000000 : ℝ)
  rw [alternate_total_snoc,half_15_05_total3]
  norm_num

private theorem half_15_05_bounds4 : ∀ l,0≤half_15_05_φ4 l ∧ half_15_05_φ4 l≤1 ∧
    0≤shiftExponents 9 half_15_05_φ4 l :=
  alternate_bounds_snoc half_15_05_φ3 (219769293/2500000000 : ℝ) half_15_05_bounds3 (by norm_num)

private def half_15_05_φ5 : Fin 5 → ℝ := Fin.snoc half_15_05_φ4 (30767701/400000000 : ℝ)

private theorem half_15_05_total5 : total half_15_05_φ5=(4615652317/10000000000 : ℝ) := by
  change total (Fin.snoc half_15_05_φ4 (30767701/400000000 : ℝ))=(4615652317/10000000000 : ℝ)
  rw [alternate_total_snoc,half_15_05_total4]
  norm_num

private theorem half_15_05_bounds5 : ∀ l,0≤half_15_05_φ5 l ∧ half_15_05_φ5 l≤1 ∧
    0≤shiftExponents 9 half_15_05_φ5 l :=
  alternate_bounds_snoc half_15_05_φ4 (30767701/400000000 : ℝ) half_15_05_bounds4 (by norm_num)

private def half_15_05_φ6 : Fin 6 → ℝ := Fin.snoc half_15_05_φ5 (55217347/1000000000 : ℝ)

private theorem half_15_05_total6 : total half_15_05_φ6=(5167825787/10000000000 : ℝ) := by
  change total (Fin.snoc half_15_05_φ5 (55217347/1000000000 : ℝ))=(5167825787/10000000000 : ℝ)
  rw [alternate_total_snoc,half_15_05_total5]
  norm_num

private theorem half_15_05_bounds6 : ∀ l,0≤half_15_05_φ6 l ∧ half_15_05_φ6 l≤1 ∧
    0≤shiftExponents 9 half_15_05_φ6 l :=
  alternate_bounds_snoc half_15_05_φ5 (55217347/1000000000 : ℝ) half_15_05_bounds5 (by norm_num)

private theorem half_15_05_prefix : PrefixCondition 9 half_15_05_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_15_05_φ1, half_15_05_φ2, half_15_05_φ3, half_15_05_φ4, half_15_05_φ5, half_15_05_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_15_05_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_15_05_φ6) (9496522639/1250000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_15_05_φ6
    (fun i => (half_15_05_bounds6 i).1) (fun i => (half_15_05_bounds6 i).2.1)
    (fun i => (half_15_05_bounds6 i).2.2) half_15_05_prefix
  convert h using 1 <;> norm_num [half_15_05_total1, half_15_05_total2, half_15_05_total3, half_15_05_total4, half_15_05_total5, half_15_05_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_15_05_hx6 : SourcePowerBound
    (powerBoxCross 9 9 64 half_15_05_φ6) (77469468557/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 9) (r := 2) (v := 0) (w := 12) (D := 64)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_15_05_φ6 (by norm_num [half_15_05_total1, half_15_05_total2, half_15_05_total3, half_15_05_total4, half_15_05_total5, half_15_05_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_15_05_total1, half_15_05_total2, half_15_05_total3, half_15_05_total4, half_15_05_total5, half_15_05_total6, parameterExponent, curveLoss, dyadicExponent]) half_15_05_hF2
    (admissibleExponent_zero 9) (half_12_05)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_15_05_total1, half_15_05_total2, half_15_05_total3, half_15_05_total4, half_15_05_total5, half_15_05_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_15_05_hx5 : SourcePowerBound
    (powerBoxCross 9 10 32 half_15_05_φ5) (44384638219/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 10) (u := 8) (t := 11)
    (D := 32) (ψ := (55217347/1000000000 : ℝ)) half_15_05_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_15_05_bounds5 l).1) (fun l => (half_15_05_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_15_05_total1, half_15_05_total2, half_15_05_total3, half_15_05_total4, half_15_05_total5, half_15_05_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_9) (half_11_05)
    (by simpa only [half_15_05_φ6, show (2:ℝ)*32=64 by norm_num] using half_15_05_hx6)
  exact h.weaken (by norm_num [half_15_05_total1, half_15_05_total2, half_15_05_total3, half_15_05_total4, half_15_05_total5, half_15_05_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_15_05_hx4 : SourcePowerBound
    (powerBoxCross 9 11 16 half_15_05_φ4) (105950726379/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 11) (u := 9) (t := 12)
    (D := 16) (ψ := (30767701/400000000 : ℝ)) half_15_05_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_15_05_bounds4 l).1) (fun l => (half_15_05_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_15_05_total1, half_15_05_total2, half_15_05_total3, half_15_05_total4, half_15_05_total5, half_15_05_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_10_05) (half_12_05)
    (by simpa only [half_15_05_φ5, show (2:ℝ)*16=32 by norm_num] using half_15_05_hx5)
  exact h.weaken (by norm_num [half_15_05_total1, half_15_05_total2, half_15_05_total3, half_15_05_total4, half_15_05_total5, half_15_05_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_15_05_hx3 : SourcePowerBound
    (powerBoxCross 9 12 8 half_15_05_φ3) (128299213149/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 12) (u := 10) (t := 13)
    (D := 8) (ψ := (219769293/2500000000 : ℝ)) half_15_05_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_15_05_bounds3 l).1) (fun l => (half_15_05_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_15_05_total1, half_15_05_total2, half_15_05_total3, half_15_05_total4, half_15_05_total5, half_15_05_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_11_05) (half_13_05)
    (by simpa only [half_15_05_φ4, show (2:ℝ)*8=16 by norm_num] using half_15_05_hx4)
  exact h.weaken (by norm_num [half_15_05_total1, half_15_05_total2, half_15_05_total3, half_15_05_total4, half_15_05_total5, half_15_05_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_15_05_hx2 : SourcePowerBound
    (powerBoxCross 9 13 4 half_15_05_φ2) (77876935489/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 13) (u := 11) (t := 14)
    (D := 4) (ψ := (38066251/400000000 : ℝ)) half_15_05_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_15_05_bounds2 l).1) (fun l => (half_15_05_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_15_05_total1, half_15_05_total2, half_15_05_total3, half_15_05_total4, half_15_05_total5, half_15_05_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_12_05) (half_14_05)
    (by simpa only [half_15_05_φ3, show (2:ℝ)*4=8 by norm_num] using half_15_05_hx3)
  exact h.weaken (by norm_num [half_15_05_total1, half_15_05_total2, half_15_05_total3, half_15_05_total4, half_15_05_total5, half_15_05_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_15_05_hx1 : SourcePowerBound
    (powerBoxCross 9 14 2 half_15_05_φ1) (94000459007/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 14) (u := 12) (t := 15)
    (D := 2) (ψ := (198070479/2000000000 : ℝ)) half_15_05_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_15_05_bounds1 l).1) (fun l => (half_15_05_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_15_05_total1, half_15_05_total2, half_15_05_total3, half_15_05_total4, half_15_05_total5, half_15_05_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_13_05) (half_15_04)
    (by simpa only [half_15_05_φ2, show (2:ℝ)*2=4 by norm_num] using half_15_05_hx2)
  exact h.weaken (by norm_num [half_15_05_total1, half_15_05_total2, half_15_05_total3, half_15_05_total4, half_15_05_total5, half_15_05_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_15_05 : AdmissibleExponent 9 30 (26960751833/1250000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 13) (ψ := (20507479/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_14_05)
    (by simpa only [half_15_05_φ1] using half_15_05_hx1)
  exact admissibleExponent_mono h (by norm_num [half_15_05_total1, half_15_05_total2, half_15_05_total3, half_15_05_total4, half_15_05_total5, half_15_05_total6, parameterExponent, curveLoss, dyadicExponent])

private def half_16_05_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (261070699/2500000000 : ℝ)

private theorem half_16_05_total1 : total half_16_05_φ1=(261070699/2500000000 : ℝ) := by
  norm_num [half_16_05_φ1,total,emptyPhi,Fin.snoc]

private theorem half_16_05_bounds1 : ∀ l,0≤half_16_05_φ1 l ∧ half_16_05_φ1 l≤1 ∧
    0≤shiftExponents 9 half_16_05_φ1 l :=
  alternate_bounds_snoc emptyPhi (261070699/2500000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_16_05_φ2 : Fin 2 → ℝ := Fin.snoc half_16_05_φ1 (25333569/250000000 : ℝ)

private theorem half_16_05_total2 : total half_16_05_φ2=(514406389/2500000000 : ℝ) := by
  change total (Fin.snoc half_16_05_φ1 (25333569/250000000 : ℝ))=(514406389/2500000000 : ℝ)
  rw [alternate_total_snoc,half_16_05_total1]
  norm_num

private theorem half_16_05_bounds2 : ∀ l,0≤half_16_05_φ2 l ∧ half_16_05_φ2 l≤1 ∧
    0≤shiftExponents 9 half_16_05_φ2 l :=
  alternate_bounds_snoc half_16_05_φ1 (25333569/250000000 : ℝ) half_16_05_bounds1 (by norm_num)

private def half_16_05_φ3 : Fin 3 → ℝ := Fin.snoc half_16_05_φ2 (6145011/62500000 : ℝ)

private theorem half_16_05_total3 : total half_16_05_φ3=(760206829/2500000000 : ℝ) := by
  change total (Fin.snoc half_16_05_φ2 (6145011/62500000 : ℝ))=(760206829/2500000000 : ℝ)
  rw [alternate_total_snoc,half_16_05_total2]
  norm_num

private theorem half_16_05_bounds3 : ∀ l,0≤half_16_05_φ3 l ∧ half_16_05_φ3 l≤1 ∧
    0≤shiftExponents 9 half_16_05_φ3 l :=
  alternate_bounds_snoc half_16_05_φ2 (6145011/62500000 : ℝ) half_16_05_bounds2 (by norm_num)

private def half_16_05_φ4 : Fin 4 → ℝ := Fin.snoc half_16_05_φ3 (173979317/2000000000 : ℝ)

private theorem half_16_05_total4 : total half_16_05_φ4=(3910723901/10000000000 : ℝ) := by
  change total (Fin.snoc half_16_05_φ3 (173979317/2000000000 : ℝ))=(3910723901/10000000000 : ℝ)
  rw [alternate_total_snoc,half_16_05_total3]
  norm_num

private theorem half_16_05_bounds4 : ∀ l,0≤half_16_05_φ4 l ∧ half_16_05_φ4 l≤1 ∧
    0≤shiftExponents 9 half_16_05_φ4 l :=
  alternate_bounds_snoc half_16_05_φ3 (173979317/2000000000 : ℝ) half_16_05_bounds3 (by norm_num)

private def half_16_05_φ5 : Fin 5 → ℝ := Fin.snoc half_16_05_φ4 (95144939/1250000000 : ℝ)

private theorem half_16_05_total5 : total half_16_05_φ5=(4671883413/10000000000 : ℝ) := by
  change total (Fin.snoc half_16_05_φ4 (95144939/1250000000 : ℝ))=(4671883413/10000000000 : ℝ)
  rw [alternate_total_snoc,half_16_05_total4]
  norm_num

private theorem half_16_05_bounds5 : ∀ l,0≤half_16_05_φ5 l ∧ half_16_05_φ5 l≤1 ∧
    0≤shiftExponents 9 half_16_05_φ5 l :=
  alternate_bounds_snoc half_16_05_φ4 (95144939/1250000000 : ℝ) half_16_05_bounds4 (by norm_num)

private def half_16_05_φ6 : Fin 6 → ℝ := Fin.snoc half_16_05_φ5 (207233/3125000 : ℝ)

private theorem half_16_05_total6 : total half_16_05_φ6=(5335029013/10000000000 : ℝ) := by
  change total (Fin.snoc half_16_05_φ5 (207233/3125000 : ℝ))=(5335029013/10000000000 : ℝ)
  rw [alternate_total_snoc,half_16_05_total5]
  norm_num

private theorem half_16_05_bounds6 : ∀ l,0≤half_16_05_φ6 l ∧ half_16_05_φ6 l≤1 ∧
    0≤shiftExponents 9 half_16_05_φ6 l :=
  alternate_bounds_snoc half_16_05_φ5 (207233/3125000 : ℝ) half_16_05_bounds5 (by norm_num)

private theorem half_16_05_prefix : PrefixCondition 9 half_16_05_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_16_05_φ1, half_16_05_φ2, half_16_05_φ3, half_16_05_φ4, half_16_05_φ5, half_16_05_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_16_05_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_16_05_φ6) (8994912961/1250000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_16_05_φ6
    (fun i => (half_16_05_bounds6 i).1) (fun i => (half_16_05_bounds6 i).2.1)
    (fun i => (half_16_05_bounds6 i).2.2) half_16_05_prefix
  convert h using 1 <;> norm_num [half_16_05_total1, half_16_05_total2, half_16_05_total3, half_16_05_total4, half_16_05_total5, half_16_05_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_16_05_hx6 : SourcePowerBound
    (powerBoxCross 9 10 64 half_16_05_φ6) (82753118727/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 10) (r := 2) (v := 13) (w := 14) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_16_05_φ6 (by norm_num [half_16_05_total1, half_16_05_total2, half_16_05_total3, half_16_05_total4, half_16_05_total5, half_16_05_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_16_05_total1, half_16_05_total2, half_16_05_total3, half_16_05_total4, half_16_05_total5, half_16_05_total6, parameterExponent, curveLoss, dyadicExponent]) half_16_05_hF2
    (half_13_05) (half_14_05)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_16_05_total1, half_16_05_total2, half_16_05_total3, half_16_05_total4, half_16_05_total5, half_16_05_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_16_05_hx5 : SourcePowerBound
    (powerBoxCross 9 11 32 half_16_05_φ5) (1212178497/125000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 11) (u := 9) (t := 12)
    (D := 32) (ψ := (207233/3125000 : ℝ)) half_16_05_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_16_05_bounds5 l).1) (fun l => (half_16_05_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_16_05_total1, half_16_05_total2, half_16_05_total3, half_16_05_total4, half_16_05_total5, half_16_05_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_10_05) (half_12_05)
    (by simpa only [half_16_05_φ6, show (2:ℝ)*32=64 by norm_num] using half_16_05_hx6)
  exact h.weaken (by norm_num [half_16_05_total1, half_16_05_total2, half_16_05_total3, half_16_05_total4, half_16_05_total5, half_16_05_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_16_05_hx4 : SourcePowerBound
    (powerBoxCross 9 12 16 half_16_05_φ4) (7209609283/625000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 12) (u := 10) (t := 13)
    (D := 16) (ψ := (95144939/1250000000 : ℝ)) half_16_05_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_16_05_bounds4 l).1) (fun l => (half_16_05_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_16_05_total1, half_16_05_total2, half_16_05_total3, half_16_05_total4, half_16_05_total5, half_16_05_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_11_05) (half_13_05)
    (by simpa only [half_16_05_φ5, show (2:ℝ)*16=32 by norm_num] using half_16_05_hx5)
  exact h.weaken (by norm_num [half_16_05_total1, half_16_05_total2, half_16_05_total3, half_16_05_total4, half_16_05_total5, half_16_05_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_16_05_hx3 : SourcePowerBound
    (powerBoxCross 9 13 8 half_16_05_φ3) (69566617941/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 13) (u := 11) (t := 14)
    (D := 8) (ψ := (173979317/2000000000 : ℝ)) half_16_05_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_16_05_bounds3 l).1) (fun l => (half_16_05_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_16_05_total1, half_16_05_total2, half_16_05_total3, half_16_05_total4, half_16_05_total5, half_16_05_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_12_05) (half_14_05)
    (by simpa only [half_16_05_φ4, show (2:ℝ)*8=16 by norm_num] using half_16_05_hx4)
  exact h.weaken (by norm_num [half_16_05_total1, half_16_05_total2, half_16_05_total3, half_16_05_total4, half_16_05_total5, half_16_05_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_16_05_hx2 : SourcePowerBound
    (powerBoxCross 9 14 4 half_16_05_φ2) (169279092257/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 14) (u := 12) (t := 15)
    (D := 4) (ψ := (6145011/62500000 : ℝ)) half_16_05_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_16_05_bounds2 l).1) (fun l => (half_16_05_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_16_05_total1, half_16_05_total2, half_16_05_total3, half_16_05_total4, half_16_05_total5, half_16_05_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_13_05) (half_15_05)
    (by simpa only [half_16_05_φ3, show (2:ℝ)*4=8 by norm_num] using half_16_05_hx3)
  exact h.weaken (by norm_num [half_16_05_total1, half_16_05_total2, half_16_05_total3, half_16_05_total4, half_16_05_total5, half_16_05_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_16_05_hx1 : SourcePowerBound
    (powerBoxCross 9 15 2 half_16_05_φ1) (204206578021/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 15) (u := 13) (t := 16)
    (D := 2) (ψ := (25333569/250000000 : ℝ)) half_16_05_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_16_05_bounds1 l).1) (fun l => (half_16_05_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_16_05_total1, half_16_05_total2, half_16_05_total3, half_16_05_total4, half_16_05_total5, half_16_05_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_14_05) (half_16_04)
    (by simpa only [half_16_05_φ2, show (2:ℝ)*2=4 by norm_num] using half_16_05_hx2)
  exact h.weaken (by norm_num [half_16_05_total1, half_16_05_total2, half_16_05_total3, half_16_05_total4, half_16_05_total5, half_16_05_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_16_05 : AdmissibleExponent 9 32 (46898155821/2000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 14) (ψ := (261070699/2500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_15_05)
    (by simpa only [half_16_05_φ1] using half_16_05_hx1)
  exact admissibleExponent_mono h (by norm_num [half_16_05_total1, half_16_05_total2, half_16_05_total3, half_16_05_total4, half_16_05_total5, half_16_05_total6, parameterExponent, curveLoss, dyadicExponent])

private def half_17_05_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (105989503/1000000000 : ℝ)

private theorem half_17_05_total1 : total half_17_05_φ1=(105989503/1000000000 : ℝ) := by
  norm_num [half_17_05_φ1,total,emptyPhi,Fin.snoc]

private theorem half_17_05_bounds1 : ∀ l,0≤half_17_05_φ1 l ∧ half_17_05_φ1 l≤1 ∧
    0≤shiftExponents 9 half_17_05_φ1 l :=
  alternate_bounds_snoc emptyPhi (105989503/1000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_17_05_φ2 : Fin 2 → ℝ := Fin.snoc half_17_05_φ1 (1034942121/10000000000 : ℝ)

private theorem half_17_05_total2 : total half_17_05_φ2=(2094837151/10000000000 : ℝ) := by
  change total (Fin.snoc half_17_05_φ1 (1034942121/10000000000 : ℝ))=(2094837151/10000000000 : ℝ)
  rw [alternate_total_snoc,half_17_05_total1]
  norm_num

private theorem half_17_05_bounds2 : ∀ l,0≤half_17_05_φ2 l ∧ half_17_05_φ2 l≤1 ∧
    0≤shiftExponents 9 half_17_05_φ2 l :=
  alternate_bounds_snoc half_17_05_φ1 (1034942121/10000000000 : ℝ) half_17_05_bounds1 (by norm_num)

private def half_17_05_φ3 : Fin 3 → ℝ := Fin.snoc half_17_05_φ2 (197629071/2000000000 : ℝ)

private theorem half_17_05_total3 : total half_17_05_φ3=(1541491253/5000000000 : ℝ) := by
  change total (Fin.snoc half_17_05_φ2 (197629071/2000000000 : ℝ))=(1541491253/5000000000 : ℝ)
  rw [alternate_total_snoc,half_17_05_total2]
  norm_num

private theorem half_17_05_bounds3 : ∀ l,0≤half_17_05_φ3 l ∧ half_17_05_φ3 l≤1 ∧
    0≤shiftExponents 9 half_17_05_φ3 l :=
  alternate_bounds_snoc half_17_05_φ2 (197629071/2000000000 : ℝ) half_17_05_bounds2 (by norm_num)

private def half_17_05_φ4 : Fin 4 → ℝ := Fin.snoc half_17_05_φ3 (432313593/5000000000 : ℝ)

private theorem half_17_05_total4 : total half_17_05_φ4=(986902423/2500000000 : ℝ) := by
  change total (Fin.snoc half_17_05_φ3 (432313593/5000000000 : ℝ))=(986902423/2500000000 : ℝ)
  rw [alternate_total_snoc,half_17_05_total3]
  norm_num

private theorem half_17_05_bounds4 : ∀ l,0≤half_17_05_φ4 l ∧ half_17_05_φ4 l≤1 ∧
    0≤shiftExponents 9 half_17_05_φ4 l :=
  alternate_bounds_snoc half_17_05_φ3 (432313593/5000000000 : ℝ) half_17_05_bounds3 (by norm_num)

private def half_17_05_φ5 : Fin 5 → ℝ := Fin.snoc half_17_05_φ4 (189137197/2500000000 : ℝ)

private theorem half_17_05_total5 : total half_17_05_φ5=(58801981/125000000 : ℝ) := by
  change total (Fin.snoc half_17_05_φ4 (189137197/2500000000 : ℝ))=(58801981/125000000 : ℝ)
  rw [alternate_total_snoc,half_17_05_total4]
  norm_num

private theorem half_17_05_bounds5 : ∀ l,0≤half_17_05_φ5 l ∧ half_17_05_φ5 l≤1 ∧
    0≤shiftExponents 9 half_17_05_φ5 l :=
  alternate_bounds_snoc half_17_05_φ4 (189137197/2500000000 : ℝ) half_17_05_bounds4 (by norm_num)

private def half_17_05_φ6 : Fin 6 → ℝ := Fin.snoc half_17_05_φ5 (661980189/10000000000 : ℝ)

private theorem half_17_05_total6 : total half_17_05_φ6=(5366138669/10000000000 : ℝ) := by
  change total (Fin.snoc half_17_05_φ5 (661980189/10000000000 : ℝ))=(5366138669/10000000000 : ℝ)
  rw [alternate_total_snoc,half_17_05_total5]
  norm_num

private theorem half_17_05_bounds6 : ∀ l,0≤half_17_05_φ6 l ∧ half_17_05_φ6 l≤1 ∧
    0≤shiftExponents 9 half_17_05_φ6 l :=
  alternate_bounds_snoc half_17_05_φ5 (661980189/10000000000 : ℝ) half_17_05_bounds5 (by norm_num)

private theorem half_17_05_prefix : PrefixCondition 9 half_17_05_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_17_05_φ1, half_17_05_φ2, half_17_05_φ3, half_17_05_φ4, half_17_05_φ5, half_17_05_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_17_05_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_17_05_φ6) (8901583993/1250000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_17_05_φ6
    (fun i => (half_17_05_bounds6 i).1) (fun i => (half_17_05_bounds6 i).2.1)
    (fun i => (half_17_05_bounds6 i).2.2) half_17_05_prefix
  convert h using 1 <;> norm_num [half_17_05_total1, half_17_05_total2, half_17_05_total3, half_17_05_total4, half_17_05_total5, half_17_05_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_17_05_hx6 : SourcePowerBound
    (powerBoxCross 9 11 64 half_17_05_φ6) (9062053163/1000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 11) (r := 2) (v := 14) (w := 15) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_17_05_φ6 (by norm_num [half_17_05_total1, half_17_05_total2, half_17_05_total3, half_17_05_total4, half_17_05_total5, half_17_05_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_17_05_total1, half_17_05_total2, half_17_05_total3, half_17_05_total4, half_17_05_total5, half_17_05_total6, parameterExponent, curveLoss, dyadicExponent]) half_17_05_hF2
    (half_14_05) (half_15_05)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_17_05_total1, half_17_05_total2, half_17_05_total3, half_17_05_total4, half_17_05_total5, half_17_05_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_17_05_hx5 : SourcePowerBound
    (powerBoxCross 9 12 32 half_17_05_φ5) (52929064099/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 12) (u := 10) (t := 13)
    (D := 32) (ψ := (661980189/10000000000 : ℝ)) half_17_05_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_17_05_bounds5 l).1) (fun l => (half_17_05_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_17_05_total1, half_17_05_total2, half_17_05_total3, half_17_05_total4, half_17_05_total5, half_17_05_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_11_05) (half_13_05)
    (by simpa only [half_17_05_φ6, show (2:ℝ)*32=64 by norm_num] using half_17_05_hx6)
  exact h.weaken (by norm_num [half_17_05_total1, half_17_05_total2, half_17_05_total3, half_17_05_total4, half_17_05_total5, half_17_05_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_17_05_hx4 : SourcePowerBound
    (powerBoxCross 9 13 16 half_17_05_φ4) (62757064261/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 13) (u := 11) (t := 14)
    (D := 16) (ψ := (189137197/2500000000 : ℝ)) half_17_05_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_17_05_bounds4 l).1) (fun l => (half_17_05_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_17_05_total1, half_17_05_total2, half_17_05_total3, half_17_05_total4, half_17_05_total5, half_17_05_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_12_05) (half_14_05)
    (by simpa only [half_17_05_φ5, show (2:ℝ)*16=32 by norm_num] using half_17_05_hx5)
  exact h.weaken (by norm_num [half_17_05_total1, half_17_05_total2, half_17_05_total3, half_17_05_total4, half_17_05_total5, half_17_05_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_17_05_hx3 : SourcePowerBound
    (powerBoxCross 9 14 8 half_17_05_φ3) (30165634179/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 14) (u := 12) (t := 15)
    (D := 8) (ψ := (432313593/5000000000 : ℝ)) half_17_05_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_17_05_bounds3 l).1) (fun l => (half_17_05_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_17_05_total1, half_17_05_total2, half_17_05_total3, half_17_05_total4, half_17_05_total5, half_17_05_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_13_05) (half_15_05)
    (by simpa only [half_17_05_φ4, show (2:ℝ)*8=16 by norm_num] using half_17_05_hx4)
  exact h.weaken (by norm_num [half_17_05_total1, half_17_05_total2, half_17_05_total3, half_17_05_total4, half_17_05_total5, half_17_05_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_17_05_hx2 : SourcePowerBound
    (powerBoxCross 9 15 4 half_17_05_φ2) (183059088907/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 15) (u := 13) (t := 16)
    (D := 4) (ψ := (197629071/2000000000 : ℝ)) half_17_05_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_17_05_bounds2 l).1) (fun l => (half_17_05_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_17_05_total1, half_17_05_total2, half_17_05_total3, half_17_05_total4, half_17_05_total5, half_17_05_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_14_05) (half_16_05)
    (by simpa only [half_17_05_φ3, show (2:ℝ)*4=8 by norm_num] using half_17_05_hx3)
  exact h.weaken (by norm_num [half_17_05_total1, half_17_05_total2, half_17_05_total3, half_17_05_total4, half_17_05_total5, half_17_05_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_17_05_hx1 : SourcePowerBound
    (powerBoxCross 9 16 2 half_17_05_φ1) (110348556503/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 16) (u := 14) (t := 17)
    (D := 2) (ψ := (1034942121/10000000000 : ℝ)) half_17_05_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_17_05_bounds1 l).1) (fun l => (half_17_05_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_17_05_total1, half_17_05_total2, half_17_05_total3, half_17_05_total4, half_17_05_total5, half_17_05_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_15_05) (half_17_04)
    (by simpa only [half_17_05_φ2, show (2:ℝ)*2=4 by norm_num] using half_17_05_hx2)
  exact h.weaken (by norm_num [half_17_05_total1, half_17_05_total2, half_17_05_total3, half_17_05_total4, half_17_05_total5, half_17_05_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_17_05 : AdmissibleExponent 9 34 (31694232367/1250000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 15) (ψ := (105989503/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_16_05)
    (by simpa only [half_17_05_φ1] using half_17_05_hx1)
  exact admissibleExponent_mono h (by norm_num [half_17_05_total1, half_17_05_total2, half_17_05_total3, half_17_05_total4, half_17_05_total5, half_17_05_total6, parameterExponent, curveLoss, dyadicExponent])

end Waring.SeedCompletionAlternate9Seeds
