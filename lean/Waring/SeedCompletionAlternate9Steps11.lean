import Waring.SeedCompletionAlternate9Steps10

noncomputable section
set_option maxHeartbeats 2000000
namespace Waring.SeedCompletionAlternate9Seeds
open SmoothMoments FirstStageTransport SeedCompletionNaturalBox
open SeedCompletionSourceBounds SeedCompletionPaddedSource SeedCompletionGeneralTerminal
open PolicyCompletionMajorPowerRanges SeedCompletionDivisorPowerScales
open PolicyCompletionSharpResidualSource

private def half_13_10_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (487166113/5000000000 : ℝ)

private theorem half_13_10_total1 : total half_13_10_φ1=(487166113/5000000000 : ℝ) := by
  norm_num [half_13_10_φ1,total,emptyPhi,Fin.snoc]

private theorem half_13_10_bounds1 : ∀ l,0≤half_13_10_φ1 l ∧ half_13_10_φ1 l≤1 ∧
    0≤shiftExponents 9 half_13_10_φ1 l :=
  alternate_bounds_snoc emptyPhi (487166113/5000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_13_10_φ2 : Fin 2 → ℝ := Fin.snoc half_13_10_φ1 (467809013/5000000000 : ℝ)

private theorem half_13_10_total2 : total half_13_10_φ2=(477487563/2500000000 : ℝ) := by
  change total (Fin.snoc half_13_10_φ1 (467809013/5000000000 : ℝ))=(477487563/2500000000 : ℝ)
  rw [alternate_total_snoc,half_13_10_total1]
  norm_num

private theorem half_13_10_bounds2 : ∀ l,0≤half_13_10_φ2 l ∧ half_13_10_φ2 l≤1 ∧
    0≤shiftExponents 9 half_13_10_φ2 l :=
  alternate_bounds_snoc half_13_10_φ1 (467809013/5000000000 : ℝ) half_13_10_bounds1 (by norm_num)

private def half_13_10_φ3 : Fin 3 → ℝ := Fin.snoc half_13_10_φ2 (882426609/10000000000 : ℝ)

private theorem half_13_10_total3 : total half_13_10_φ3=(2792376861/10000000000 : ℝ) := by
  change total (Fin.snoc half_13_10_φ2 (882426609/10000000000 : ℝ))=(2792376861/10000000000 : ℝ)
  rw [alternate_total_snoc,half_13_10_total2]
  norm_num

private theorem half_13_10_bounds3 : ∀ l,0≤half_13_10_φ3 l ∧ half_13_10_φ3 l≤1 ∧
    0≤shiftExponents 9 half_13_10_φ3 l :=
  alternate_bounds_snoc half_13_10_φ2 (882426609/10000000000 : ℝ) half_13_10_bounds2 (by norm_num)

private def half_13_10_φ4 : Fin 4 → ℝ := Fin.snoc half_13_10_φ3 (39724439/500000000 : ℝ)

private theorem half_13_10_total4 : total half_13_10_φ4=(3586865641/10000000000 : ℝ) := by
  change total (Fin.snoc half_13_10_φ3 (39724439/500000000 : ℝ))=(3586865641/10000000000 : ℝ)
  rw [alternate_total_snoc,half_13_10_total3]
  norm_num

private theorem half_13_10_bounds4 : ∀ l,0≤half_13_10_φ4 l ∧ half_13_10_φ4 l≤1 ∧
    0≤shiftExponents 9 half_13_10_φ4 l :=
  alternate_bounds_snoc half_13_10_φ3 (39724439/500000000 : ℝ) half_13_10_bounds3 (by norm_num)

private def half_13_10_φ5 : Fin 5 → ℝ := Fin.snoc half_13_10_φ4 (121393857/2000000000 : ℝ)

private theorem half_13_10_total5 : total half_13_10_φ5=(2096917463/5000000000 : ℝ) := by
  change total (Fin.snoc half_13_10_φ4 (121393857/2000000000 : ℝ))=(2096917463/5000000000 : ℝ)
  rw [alternate_total_snoc,half_13_10_total4]
  norm_num

private theorem half_13_10_bounds5 : ∀ l,0≤half_13_10_φ5 l ∧ half_13_10_φ5 l≤1 ∧
    0≤shiftExponents 9 half_13_10_φ5 l :=
  alternate_bounds_snoc half_13_10_φ4 (121393857/2000000000 : ℝ) half_13_10_bounds4 (by norm_num)

private theorem half_13_10_prefix : PrefixCondition 9 half_13_10_φ5 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_13_10_φ1, half_13_10_φ2, half_13_10_φ3, half_13_10_φ4, half_13_10_φ5, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_13_10_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 32 half_13_10_φ5) (4334247611/625000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_13_10_φ5
    (fun i => (half_13_10_bounds5 i).1) (fun i => (half_13_10_bounds5 i).2.1)
    (fun i => (half_13_10_bounds5 i).2.2) half_13_10_prefix
  convert h using 1 <;> norm_num [half_13_10_total1, half_13_10_total2, half_13_10_total3, half_13_10_total4, half_13_10_total5, parameterExponent, curveLoss, dyadicExponent]

private theorem half_13_10_hx5 : SourcePowerBound
    (powerBoxCross 9 8 32 half_13_10_φ5) (970925371/125000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 8) (r := 2) (v := 10) (w := 11) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_13_10_φ5 (by norm_num [half_13_10_total1, half_13_10_total2, half_13_10_total3, half_13_10_total4, half_13_10_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_13_10_total1, half_13_10_total2, half_13_10_total3, half_13_10_total4, half_13_10_total5, parameterExponent, curveLoss, dyadicExponent]) half_13_10_hF2
    (half_10_10) (half_11_10)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_13_10_total1, half_13_10_total2, half_13_10_total3, half_13_10_total4, half_13_10_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_13_10_hx4 : SourcePowerBound
    (powerBoxCross 9 9 16 half_13_10_φ4) (89913840021/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 9) (u := 7) (t := 10)
    (D := 16) (ψ := (121393857/2000000000 : ℝ)) half_13_10_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_13_10_bounds4 l).1) (fun l => (half_13_10_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_13_10_total1, half_13_10_total2, half_13_10_total3, half_13_10_total4, half_13_10_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_8) (half_10_10)
    (by simpa only [half_13_10_φ5, show (2:ℝ)*16=32 by norm_num] using half_13_10_hx5)
  exact h.weaken (by norm_num [half_13_10_total1, half_13_10_total2, half_13_10_total3, half_13_10_total4, half_13_10_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_13_10_hx3 : SourcePowerBound
    (powerBoxCross 9 10 8 half_13_10_φ3) (53736845263/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 10) (u := 8) (t := 11)
    (D := 8) (ψ := (39724439/500000000 : ℝ)) half_13_10_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_13_10_bounds3 l).1) (fun l => (half_13_10_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_13_10_total1, half_13_10_total2, half_13_10_total3, half_13_10_total4, half_13_10_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_9) (half_11_10)
    (by simpa only [half_13_10_φ4, show (2:ℝ)*8=16 by norm_num] using half_13_10_hx4)
  exact h.weaken (by norm_num [half_13_10_total1, half_13_10_total2, half_13_10_total3, half_13_10_total4, half_13_10_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_13_10_hx2 : SourcePowerBound
    (powerBoxCross 9 11 4 half_13_10_φ2) (129723512671/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 11) (u := 9) (t := 12)
    (D := 4) (ψ := (882426609/10000000000 : ℝ)) half_13_10_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_13_10_bounds2 l).1) (fun l => (half_13_10_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_13_10_total1, half_13_10_total2, half_13_10_total3, half_13_10_total4, half_13_10_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_10_10) (half_12_10)
    (by simpa only [half_13_10_φ3, show (2:ℝ)*4=8 by norm_num] using half_13_10_hx3)
  exact h.weaken (by norm_num [half_13_10_total1, half_13_10_total2, half_13_10_total3, half_13_10_total4, half_13_10_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_13_10_hx1 : SourcePowerBound
    (powerBoxCross 9 12 2 half_13_10_φ1) (156552026377/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 12) (u := 10) (t := 13)
    (D := 2) (ψ := (467809013/5000000000 : ℝ)) half_13_10_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_13_10_bounds1 l).1) (fun l => (half_13_10_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_13_10_total1, half_13_10_total2, half_13_10_total3, half_13_10_total4, half_13_10_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_11_10) (half_13_09)
    (by simpa only [half_13_10_φ2, show (2:ℝ)*2=4 by norm_num] using half_13_10_hx2)
  exact h.weaken (by norm_num [half_13_10_total1, half_13_10_total2, half_13_10_total3, half_13_10_total4, half_13_10_total5, parameterExponent, curveLoss, dyadicExponent])

theorem half_13_10 : AdmissibleExponent 9 26 (7158466703/400000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 11) (ψ := (487166113/5000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_12_10)
    (by simpa only [half_13_10_φ1] using half_13_10_hx1)
  exact admissibleExponent_mono h (by norm_num [half_13_10_total1, half_13_10_total2, half_13_10_total3, half_13_10_total4, half_13_10_total5, parameterExponent, curveLoss, dyadicExponent])

private def half_14_10_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (999335457/10000000000 : ℝ)

private theorem half_14_10_total1 : total half_14_10_φ1=(999335457/10000000000 : ℝ) := by
  norm_num [half_14_10_φ1,total,emptyPhi,Fin.snoc]

private theorem half_14_10_bounds1 : ∀ l,0≤half_14_10_φ1 l ∧ half_14_10_φ1 l≤1 ∧
    0≤shiftExponents 9 half_14_10_φ1 l :=
  alternate_bounds_snoc emptyPhi (999335457/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_14_10_φ2 : Fin 2 → ℝ := Fin.snoc half_14_10_φ1 (96524583/1000000000 : ℝ)

private theorem half_14_10_total2 : total half_14_10_φ2=(1964581287/10000000000 : ℝ) := by
  change total (Fin.snoc half_14_10_φ1 (96524583/1000000000 : ℝ))=(1964581287/10000000000 : ℝ)
  rw [alternate_total_snoc,half_14_10_total1]
  norm_num

private theorem half_14_10_bounds2 : ∀ l,0≤half_14_10_φ2 l ∧ half_14_10_φ2 l≤1 ∧
    0≤shiftExponents 9 half_14_10_φ2 l :=
  alternate_bounds_snoc half_14_10_φ1 (96524583/1000000000 : ℝ) half_14_10_bounds1 (by norm_num)

private def half_14_10_φ3 : Fin 3 → ℝ := Fin.snoc half_14_10_φ2 (920665269/10000000000 : ℝ)

private theorem half_14_10_total3 : total half_14_10_φ3=(721311639/2500000000 : ℝ) := by
  change total (Fin.snoc half_14_10_φ2 (920665269/10000000000 : ℝ))=(721311639/2500000000 : ℝ)
  rw [alternate_total_snoc,half_14_10_total2]
  norm_num

private theorem half_14_10_bounds3 : ∀ l,0≤half_14_10_φ3 l ∧ half_14_10_φ3 l≤1 ∧
    0≤shiftExponents 9 half_14_10_φ3 l :=
  alternate_bounds_snoc half_14_10_φ2 (920665269/10000000000 : ℝ) half_14_10_bounds2 (by norm_num)

private def half_14_10_φ4 : Fin 4 → ℝ := Fin.snoc half_14_10_φ3 (852639099/10000000000 : ℝ)

private theorem half_14_10_total4 : total half_14_10_φ4=(747577131/2000000000 : ℝ) := by
  change total (Fin.snoc half_14_10_φ3 (852639099/10000000000 : ℝ))=(747577131/2000000000 : ℝ)
  rw [alternate_total_snoc,half_14_10_total3]
  norm_num

private theorem half_14_10_bounds4 : ∀ l,0≤half_14_10_φ4 l ∧ half_14_10_φ4 l≤1 ∧
    0≤shiftExponents 9 half_14_10_φ4 l :=
  alternate_bounds_snoc half_14_10_φ3 (852639099/10000000000 : ℝ) half_14_10_bounds3 (by norm_num)

private def half_14_10_φ5 : Fin 5 → ℝ := Fin.snoc half_14_10_φ4 (362315547/5000000000 : ℝ)

private theorem half_14_10_total5 : total half_14_10_φ5=(4462516749/10000000000 : ℝ) := by
  change total (Fin.snoc half_14_10_φ4 (362315547/5000000000 : ℝ))=(4462516749/10000000000 : ℝ)
  rw [alternate_total_snoc,half_14_10_total4]
  norm_num

private theorem half_14_10_bounds5 : ∀ l,0≤half_14_10_φ5 l ∧ half_14_10_φ5 l≤1 ∧
    0≤shiftExponents 9 half_14_10_φ5 l :=
  alternate_bounds_snoc half_14_10_φ4 (362315547/5000000000 : ℝ) half_14_10_bounds4 (by norm_num)

private def half_14_10_φ6 : Fin 6 → ℝ := Fin.snoc half_14_10_φ5 (209654759/5000000000 : ℝ)

private theorem half_14_10_total6 : total half_14_10_φ6=(4881826267/10000000000 : ℝ) := by
  change total (Fin.snoc half_14_10_φ5 (209654759/5000000000 : ℝ))=(4881826267/10000000000 : ℝ)
  rw [alternate_total_snoc,half_14_10_total5]
  norm_num

private theorem half_14_10_bounds6 : ∀ l,0≤half_14_10_φ6 l ∧ half_14_10_φ6 l≤1 ∧
    0≤shiftExponents 9 half_14_10_φ6 l :=
  alternate_bounds_snoc half_14_10_φ5 (209654759/5000000000 : ℝ) half_14_10_bounds5 (by norm_num)

private theorem half_14_10_prefix : PrefixCondition 9 half_14_10_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_14_10_φ1, half_14_10_φ2, half_14_10_φ3, half_14_10_φ4, half_14_10_φ5, half_14_10_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_14_10_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_14_10_φ6) (10354521199/1250000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_14_10_φ6
    (fun i => (half_14_10_bounds6 i).1) (fun i => (half_14_10_bounds6 i).2.1)
    (fun i => (half_14_10_bounds6 i).2.2) half_14_10_prefix
  convert h using 1 <;> norm_num [half_14_10_total1, half_14_10_total2, half_14_10_total3, half_14_10_total4, half_14_10_total5, half_14_10_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_14_10_hF1 : SourcePowerBound
    (paddedMoment 9 0 1 64 half_14_10_φ6) (3868173733/1250000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 0) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_14_10_φ6
    (fun i => (half_14_10_bounds6 i).1) (fun i => (half_14_10_bounds6 i).2.1)
    (fun i => (half_14_10_bounds6 i).2.2) half_14_10_prefix
  convert h using 1 <;> norm_num [half_14_10_total1, half_14_10_total2, half_14_10_total3, half_14_10_total4, half_14_10_total5, half_14_10_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_14_10_hx6 : SourcePowerBound
    (powerBoxCross 9 8 64 half_14_10_φ6) (36936871219/5000000000 : ℝ) := by
  have h := full_B_cross_power (k := 9) (s := 8) (r := 1) (v := 2) (t := 11) (D := 64)
    (a := (1/22 : ℝ)) (b := (5/22 : ℝ)) (c := (8/11 : ℝ))
    (by norm_num) half_14_10_φ6 (by norm_num [half_14_10_total1, half_14_10_total2, half_14_10_total3, half_14_10_total4, half_14_10_total5, half_14_10_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_14_10_total1, half_14_10_total2, half_14_10_total3, half_14_10_total4, half_14_10_total5, half_14_10_total6, parameterExponent, curveLoss, dyadicExponent]) half_14_10_hF1 half_14_10_hF2
    (half_11_10)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_14_10_total1, half_14_10_total2, half_14_10_total3, half_14_10_total4, half_14_10_total5, half_14_10_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_14_10_hx5 : SourcePowerBound
    (powerBoxCross 9 9 32 half_14_10_φ5) (82522967257/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 9) (u := 7) (t := 10)
    (D := 32) (ψ := (209654759/5000000000 : ℝ)) half_14_10_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_14_10_bounds5 l).1) (fun l => (half_14_10_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_14_10_total1, half_14_10_total2, half_14_10_total3, half_14_10_total4, half_14_10_total5, half_14_10_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_8) (half_10_10)
    (by simpa only [half_14_10_φ6, show (2:ℝ)*32=64 by norm_num] using half_14_10_hx6)
  exact h.weaken (by norm_num [half_14_10_total1, half_14_10_total2, half_14_10_total3, half_14_10_total4, half_14_10_total5, half_14_10_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_14_10_hx4 : SourcePowerBound
    (powerBoxCross 9 10 16 half_14_10_φ4) (97589749359/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 10) (u := 8) (t := 11)
    (D := 16) (ψ := (362315547/5000000000 : ℝ)) half_14_10_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_14_10_bounds4 l).1) (fun l => (half_14_10_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_14_10_total1, half_14_10_total2, half_14_10_total3, half_14_10_total4, half_14_10_total5, half_14_10_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_9) (half_11_10)
    (by simpa only [half_14_10_φ5, show (2:ℝ)*16=32 by norm_num] using half_14_10_hx5)
  exact h.weaken (by norm_num [half_14_10_total1, half_14_10_total2, half_14_10_total3, half_14_10_total4, half_14_10_total5, half_14_10_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_14_10_hx3 : SourcePowerBound
    (powerBoxCross 9 11 8 half_14_10_φ3) (117731952679/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 11) (u := 9) (t := 12)
    (D := 8) (ψ := (852639099/10000000000 : ℝ)) half_14_10_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_14_10_bounds3 l).1) (fun l => (half_14_10_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_14_10_total1, half_14_10_total2, half_14_10_total3, half_14_10_total4, half_14_10_total5, half_14_10_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_10_10) (half_12_10)
    (by simpa only [half_14_10_φ4, show (2:ℝ)*8=16 by norm_num] using half_14_10_hx4)
  exact h.weaken (by norm_num [half_14_10_total1, half_14_10_total2, half_14_10_total3, half_14_10_total4, half_14_10_total5, half_14_10_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_14_10_hx2 : SourcePowerBound
    (powerBoxCross 9 12 4 half_14_10_φ2) (17822029143/1250000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 12) (u := 10) (t := 13)
    (D := 4) (ψ := (920665269/10000000000 : ℝ)) half_14_10_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_14_10_bounds2 l).1) (fun l => (half_14_10_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_14_10_total1, half_14_10_total2, half_14_10_total3, half_14_10_total4, half_14_10_total5, half_14_10_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_11_10) (half_13_10)
    (by simpa only [half_14_10_φ3, show (2:ℝ)*4=8 by norm_num] using half_14_10_hx3)
  exact h.weaken (by norm_num [half_14_10_total1, half_14_10_total2, half_14_10_total3, half_14_10_total4, half_14_10_total5, half_14_10_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_14_10_hx1 : SourcePowerBound
    (powerBoxCross 9 13 2 half_14_10_φ1) (172076729053/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 13) (u := 11) (t := 14)
    (D := 2) (ψ := (96524583/1000000000 : ℝ)) half_14_10_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_14_10_bounds1 l).1) (fun l => (half_14_10_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_14_10_total1, half_14_10_total2, half_14_10_total3, half_14_10_total4, half_14_10_total5, half_14_10_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_12_10) (half_14_09)
    (by simpa only [half_14_10_φ2, show (2:ℝ)*2=4 by norm_num] using half_14_10_hx2)
  exact h.weaken (by norm_num [half_14_10_total1, half_14_10_total2, half_14_10_total3, half_14_10_total4, half_14_10_total5, half_14_10_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_14_10 : AdmissibleExponent 9 28 (98530057739/5000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 12) (ψ := (999335457/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_13_10)
    (by simpa only [half_14_10_φ1] using half_14_10_hx1)
  exact admissibleExponent_mono h (by norm_num [half_14_10_total1, half_14_10_total2, half_14_10_total3, half_14_10_total4, half_14_10_total5, half_14_10_total6, parameterExponent, curveLoss, dyadicExponent])

private def half_15_10_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1019694301/10000000000 : ℝ)

private theorem half_15_10_total1 : total half_15_10_φ1=(1019694301/10000000000 : ℝ) := by
  norm_num [half_15_10_φ1,total,emptyPhi,Fin.snoc]

private theorem half_15_10_bounds1 : ∀ l,0≤half_15_10_φ1 l ∧ half_15_10_φ1 l≤1 ∧
    0≤shiftExponents 9 half_15_10_φ1 l :=
  alternate_bounds_snoc emptyPhi (1019694301/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_15_10_φ2 : Fin 2 → ℝ := Fin.snoc half_15_10_φ1 (495204303/5000000000 : ℝ)

private theorem half_15_10_total2 : total half_15_10_φ2=(2010102907/10000000000 : ℝ) := by
  change total (Fin.snoc half_15_10_φ1 (495204303/5000000000 : ℝ))=(2010102907/10000000000 : ℝ)
  rw [alternate_total_snoc,half_15_10_total1]
  norm_num

private theorem half_15_10_bounds2 : ∀ l,0≤half_15_10_φ2 l ∧ half_15_10_φ2 l≤1 ∧
    0≤shiftExponents 9 half_15_10_φ2 l :=
  alternate_bounds_snoc half_15_10_φ1 (495204303/5000000000 : ℝ) half_15_10_bounds1 (by norm_num)

private def half_15_10_φ3 : Fin 3 → ℝ := Fin.snoc half_15_10_φ2 (237716211/2500000000 : ℝ)

private theorem half_15_10_total3 : total half_15_10_φ3=(2960967751/10000000000 : ℝ) := by
  change total (Fin.snoc half_15_10_φ2 (237716211/2500000000 : ℝ))=(2960967751/10000000000 : ℝ)
  rw [alternate_total_snoc,half_15_10_total2]
  norm_num

private theorem half_15_10_bounds3 : ∀ l,0≤half_15_10_φ3 l ∧ half_15_10_φ3 l≤1 ∧
    0≤shiftExponents 9 half_15_10_φ3 l :=
  alternate_bounds_snoc half_15_10_φ2 (237716211/2500000000 : ℝ) half_15_10_bounds2 (by norm_num)

private def half_15_10_φ4 : Fin 4 → ℝ := Fin.snoc half_15_10_φ3 (87987903/1000000000 : ℝ)

private theorem half_15_10_total4 : total half_15_10_φ4=(3840846781/10000000000 : ℝ) := by
  change total (Fin.snoc half_15_10_φ3 (87987903/1000000000 : ℝ))=(3840846781/10000000000 : ℝ)
  rw [alternate_total_snoc,half_15_10_total3]
  norm_num

private theorem half_15_10_bounds4 : ∀ l,0≤half_15_10_φ4 l ∧ half_15_10_φ4 l≤1 ∧
    0≤shiftExponents 9 half_15_10_φ4 l :=
  alternate_bounds_snoc half_15_10_φ3 (87987903/1000000000 : ℝ) half_15_10_bounds3 (by norm_num)

private def half_15_10_φ5 : Fin 5 → ℝ := Fin.snoc half_15_10_φ4 (96236769/1250000000 : ℝ)

private theorem half_15_10_total5 : total half_15_10_φ5=(4610740933/10000000000 : ℝ) := by
  change total (Fin.snoc half_15_10_φ4 (96236769/1250000000 : ℝ))=(4610740933/10000000000 : ℝ)
  rw [alternate_total_snoc,half_15_10_total4]
  norm_num

private theorem half_15_10_bounds5 : ∀ l,0≤half_15_10_φ5 l ∧ half_15_10_φ5 l≤1 ∧
    0≤shiftExponents 9 half_15_10_φ5 l :=
  alternate_bounds_snoc half_15_10_φ4 (96236769/1250000000 : ℝ) half_15_10_bounds4 (by norm_num)

private def half_15_10_φ6 : Fin 6 → ℝ := Fin.snoc half_15_10_φ5 (68599417/1250000000 : ℝ)

private theorem half_15_10_total6 : total half_15_10_φ6=(5159536269/10000000000 : ℝ) := by
  change total (Fin.snoc half_15_10_φ5 (68599417/1250000000 : ℝ))=(5159536269/10000000000 : ℝ)
  rw [alternate_total_snoc,half_15_10_total5]
  norm_num

private theorem half_15_10_bounds6 : ∀ l,0≤half_15_10_φ6 l ∧ half_15_10_φ6 l≤1 ∧
    0≤shiftExponents 9 half_15_10_φ6 l :=
  alternate_bounds_snoc half_15_10_φ5 (68599417/1250000000 : ℝ) half_15_10_bounds5 (by norm_num)

private theorem half_15_10_prefix : PrefixCondition 9 half_15_10_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_15_10_φ1, half_15_10_φ2, half_15_10_φ3, half_15_10_φ4, half_15_10_φ5, half_15_10_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_15_10_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_15_10_φ6) (9521391193/1250000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_15_10_φ6
    (fun i => (half_15_10_bounds6 i).1) (fun i => (half_15_10_bounds6 i).2.1)
    (fun i => (half_15_10_bounds6 i).2.2) half_15_10_prefix
  convert h using 1 <;> norm_num [half_15_10_total1, half_15_10_total2, half_15_10_total3, half_15_10_total4, half_15_10_total5, half_15_10_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_15_10_hx6 : SourcePowerBound
    (powerBoxCross 9 9 64 half_15_10_φ6) (19399436869/2500000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 9) (r := 2) (v := 0) (w := 12) (D := 64)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_15_10_φ6 (by norm_num [half_15_10_total1, half_15_10_total2, half_15_10_total3, half_15_10_total4, half_15_10_total5, half_15_10_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_15_10_total1, half_15_10_total2, half_15_10_total3, half_15_10_total4, half_15_10_total5, half_15_10_total6, parameterExponent, curveLoss, dyadicExponent]) half_15_10_hF2
    (admissibleExponent_zero 9) (half_12_10)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_15_10_total1, half_15_10_total2, half_15_10_total3, half_15_10_total4, half_15_10_total5, half_15_10_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_15_10_hx5 : SourcePowerBound
    (powerBoxCross 9 10 32 half_15_10_φ5) (2221298147/250000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 10) (u := 8) (t := 11)
    (D := 32) (ψ := (68599417/1250000000 : ℝ)) half_15_10_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_15_10_bounds5 l).1) (fun l => (half_15_10_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_15_10_total1, half_15_10_total2, half_15_10_total3, half_15_10_total4, half_15_10_total5, half_15_10_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_9) (half_11_10)
    (by simpa only [half_15_10_φ6, show (2:ℝ)*32=64 by norm_num] using half_15_10_hx6)
  exact h.weaken (by norm_num [half_15_10_total1, half_15_10_total2, half_15_10_total3, half_15_10_total4, half_15_10_total5, half_15_10_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_15_10_hx4 : SourcePowerBound
    (powerBoxCross 9 11 16 half_15_10_φ4) (106047982169/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 11) (u := 9) (t := 12)
    (D := 16) (ψ := (96236769/1250000000 : ℝ)) half_15_10_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_15_10_bounds4 l).1) (fun l => (half_15_10_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_15_10_total1, half_15_10_total2, half_15_10_total3, half_15_10_total4, half_15_10_total5, half_15_10_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_10_10) (half_12_10)
    (by simpa only [half_15_10_φ5, show (2:ℝ)*16=32 by norm_num] using half_15_10_hx5)
  exact h.weaken (by norm_num [half_15_10_total1, half_15_10_total2, half_15_10_total3, half_15_10_total4, half_15_10_total5, half_15_10_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_15_10_hx3 : SourcePowerBound
    (powerBoxCross 9 12 8 half_15_10_φ3) (64202348683/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 12) (u := 10) (t := 13)
    (D := 8) (ψ := (87987903/1000000000 : ℝ)) half_15_10_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_15_10_bounds3 l).1) (fun l => (half_15_10_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_15_10_total1, half_15_10_total2, half_15_10_total3, half_15_10_total4, half_15_10_total5, half_15_10_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_11_10) (half_13_10)
    (by simpa only [half_15_10_φ4, show (2:ℝ)*8=16 by norm_num] using half_15_10_hx4)
  exact h.weaken (by norm_num [half_15_10_total1, half_15_10_total2, half_15_10_total3, half_15_10_total4, half_15_10_total5, half_15_10_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_15_10_hx2 : SourcePowerBound
    (powerBoxCross 9 13 4 half_15_10_φ2) (19477673119/1250000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 13) (u := 11) (t := 14)
    (D := 4) (ψ := (237716211/2500000000 : ℝ)) half_15_10_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_15_10_bounds2 l).1) (fun l => (half_15_10_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_15_10_total1, half_15_10_total2, half_15_10_total3, half_15_10_total4, half_15_10_total5, half_15_10_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_12_10) (half_14_10)
    (by simpa only [half_15_10_φ3, show (2:ℝ)*4=8 by norm_num] using half_15_10_hx3)
  exact h.weaken (by norm_num [half_15_10_total1, half_15_10_total2, half_15_10_total3, half_15_10_total4, half_15_10_total5, half_15_10_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_15_10_hx1 : SourcePowerBound
    (powerBoxCross 9 14 2 half_15_10_φ1) (37597140423/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 14) (u := 12) (t := 15)
    (D := 2) (ψ := (495204303/5000000000 : ℝ)) half_15_10_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_15_10_bounds1 l).1) (fun l => (half_15_10_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_15_10_total1, half_15_10_total2, half_15_10_total3, half_15_10_total4, half_15_10_total5, half_15_10_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_13_10) (half_15_09)
    (by simpa only [half_15_10_φ2, show (2:ℝ)*2=4 by norm_num] using half_15_10_hx2)
  exact h.weaken (by norm_num [half_15_10_total1, half_15_10_total2, half_15_10_total3, half_15_10_total4, half_15_10_total5, half_15_10_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_15_10 : AdmissibleExponent 9 30 (107758724121/5000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 13) (ψ := (1019694301/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_14_10)
    (by simpa only [half_15_10_φ1] using half_15_10_hx1)
  exact admissibleExponent_mono h (by norm_num [half_15_10_total1, half_15_10_total2, half_15_10_total3, half_15_10_total4, half_15_10_total5, half_15_10_total6, parameterExponent, curveLoss, dyadicExponent])

private def half_16_10_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1039263223/10000000000 : ℝ)

private theorem half_16_10_total1 : total half_16_10_φ1=(1039263223/10000000000 : ℝ) := by
  norm_num [half_16_10_φ1,total,emptyPhi,Fin.snoc]

private theorem half_16_10_bounds1 : ∀ l,0≤half_16_10_φ1 l ∧ half_16_10_φ1 l≤1 ∧
    0≤shiftExponents 9 half_16_10_φ1 l :=
  alternate_bounds_snoc emptyPhi (1039263223/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_16_10_φ2 : Fin 2 → ℝ := Fin.snoc half_16_10_φ1 (101391921/1000000000 : ℝ)

private theorem half_16_10_total2 : total half_16_10_φ2=(2053182433/10000000000 : ℝ) := by
  change total (Fin.snoc half_16_10_φ1 (101391921/1000000000 : ℝ))=(2053182433/10000000000 : ℝ)
  rw [alternate_total_snoc,half_16_10_total1]
  norm_num

private theorem half_16_10_bounds2 : ∀ l,0≤half_16_10_φ2 l ∧ half_16_10_φ2 l≤1 ∧
    0≤shiftExponents 9 half_16_10_φ2 l :=
  alternate_bounds_snoc half_16_10_φ1 (101391921/1000000000 : ℝ) half_16_10_bounds1 (by norm_num)

private def half_16_10_φ3 : Fin 3 → ℝ := Fin.snoc half_16_10_φ2 (491455481/5000000000 : ℝ)

private theorem half_16_10_total3 : total half_16_10_φ3=(607218679/2000000000 : ℝ) := by
  change total (Fin.snoc half_16_10_φ2 (491455481/5000000000 : ℝ))=(607218679/2000000000 : ℝ)
  rw [alternate_total_snoc,half_16_10_total2]
  norm_num

private theorem half_16_10_bounds3 : ∀ l,0≤half_16_10_φ3 l ∧ half_16_10_φ3 l≤1 ∧
    0≤shiftExponents 9 half_16_10_φ3 l :=
  alternate_bounds_snoc half_16_10_φ2 (491455481/5000000000 : ℝ) half_16_10_bounds2 (by norm_num)

private def half_16_10_φ4 : Fin 4 → ℝ := Fin.snoc half_16_10_φ3 (34819533/400000000 : ℝ)

private theorem half_16_10_total4 : total half_16_10_φ4=(97664543/250000000 : ℝ) := by
  change total (Fin.snoc half_16_10_φ3 (34819533/400000000 : ℝ))=(97664543/250000000 : ℝ)
  rw [alternate_total_snoc,half_16_10_total3]
  norm_num

private theorem half_16_10_bounds4 : ∀ l,0≤half_16_10_φ4 l ∧ half_16_10_φ4 l≤1 ∧
    0≤shiftExponents 9 half_16_10_φ4 l :=
  alternate_bounds_snoc half_16_10_φ3 (34819533/400000000 : ℝ) half_16_10_bounds3 (by norm_num)

private def half_16_10_φ5 : Fin 5 → ℝ := Fin.snoc half_16_10_φ4 (190419321/2500000000 : ℝ)

private theorem half_16_10_total5 : total half_16_10_φ5=(1167064751/2500000000 : ℝ) := by
  change total (Fin.snoc half_16_10_φ4 (190419321/2500000000 : ℝ))=(1167064751/2500000000 : ℝ)
  rw [alternate_total_snoc,half_16_10_total4]
  norm_num

private theorem half_16_10_bounds5 : ∀ l,0≤half_16_10_φ5 l ∧ half_16_10_φ5 l≤1 ∧
    0≤shiftExponents 9 half_16_10_φ5 l :=
  alternate_bounds_snoc half_16_10_φ4 (190419321/2500000000 : ℝ) half_16_10_bounds4 (by norm_num)

private def half_16_10_φ6 : Fin 6 → ℝ := Fin.snoc half_16_10_φ5 (131688971/2000000000 : ℝ)

private theorem half_16_10_total6 : total half_16_10_φ6=(5326703859/10000000000 : ℝ) := by
  change total (Fin.snoc half_16_10_φ5 (131688971/2000000000 : ℝ))=(5326703859/10000000000 : ℝ)
  rw [alternate_total_snoc,half_16_10_total5]
  norm_num

private theorem half_16_10_bounds6 : ∀ l,0≤half_16_10_φ6 l ∧ half_16_10_φ6 l≤1 ∧
    0≤shiftExponents 9 half_16_10_φ6 l :=
  alternate_bounds_snoc half_16_10_φ5 (131688971/2000000000 : ℝ) half_16_10_bounds5 (by norm_num)

private theorem half_16_10_prefix : PrefixCondition 9 half_16_10_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_16_10_φ1, half_16_10_φ2, half_16_10_φ3, half_16_10_φ4, half_16_10_φ5, half_16_10_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_16_10_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_16_10_φ6) (9019888423/1250000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_16_10_φ6
    (fun i => (half_16_10_bounds6 i).1) (fun i => (half_16_10_bounds6 i).2.1)
    (fun i => (half_16_10_bounds6 i).2.2) half_16_10_prefix
  convert h using 1 <;> norm_num [half_16_10_total1, half_16_10_total2, half_16_10_total3, half_16_10_total4, half_16_10_total5, half_16_10_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_16_10_hx6 : SourcePowerBound
    (powerBoxCross 9 10 64 half_16_10_φ6) (828798273/100000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 10) (r := 2) (v := 13) (w := 14) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_16_10_φ6 (by norm_num [half_16_10_total1, half_16_10_total2, half_16_10_total3, half_16_10_total4, half_16_10_total5, half_16_10_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_16_10_total1, half_16_10_total2, half_16_10_total3, half_16_10_total4, half_16_10_total5, half_16_10_total6, parameterExponent, curveLoss, dyadicExponent]) half_16_10_hF2
    (half_13_10) (half_14_10)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_16_10_total1, half_16_10_total2, half_16_10_total3, half_16_10_total4, half_16_10_total5, half_16_10_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_16_10_hx5 : SourcePowerBound
    (powerBoxCross 9 11 32 half_16_10_φ5) (48510363049/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 11) (u := 9) (t := 12)
    (D := 32) (ψ := (131688971/2000000000 : ℝ)) half_16_10_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_16_10_bounds5 l).1) (fun l => (half_16_10_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_16_10_total1, half_16_10_total2, half_16_10_total3, half_16_10_total4, half_16_10_total5, half_16_10_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_10_10) (half_12_10)
    (by simpa only [half_16_10_φ6, show (2:ℝ)*32=64 by norm_num] using half_16_10_hx6)
  exact h.weaken (by norm_num [half_16_10_total1, half_16_10_total2, half_16_10_total3, half_16_10_total4, half_16_10_total5, half_16_10_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_16_10_hx4 : SourcePowerBound
    (powerBoxCross 9 12 16 half_16_10_φ4) (115406062483/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 12) (u := 10) (t := 13)
    (D := 16) (ψ := (190419321/2500000000 : ℝ)) half_16_10_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_16_10_bounds4 l).1) (fun l => (half_16_10_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_16_10_total1, half_16_10_total2, half_16_10_total3, half_16_10_total4, half_16_10_total5, half_16_10_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_11_10) (half_13_10)
    (by simpa only [half_16_10_φ5, show (2:ℝ)*16=32 by norm_num] using half_16_10_hx5)
  exact h.weaken (by norm_num [half_16_10_total1, half_16_10_total2, half_16_10_total3, half_16_10_total4, half_16_10_total5, half_16_10_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_16_10_hx3 : SourcePowerBound
    (powerBoxCross 9 13 8 half_16_10_φ3) (139184685387/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 13) (u := 11) (t := 14)
    (D := 8) (ψ := (34819533/400000000 : ℝ)) half_16_10_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_16_10_bounds3 l).1) (fun l => (half_16_10_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_16_10_total1, half_16_10_total2, half_16_10_total3, half_16_10_total4, half_16_10_total5, half_16_10_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_12_10) (half_14_10)
    (by simpa only [half_16_10_φ4, show (2:ℝ)*8=16 by norm_num] using half_16_10_hx4)
  exact h.weaken (by norm_num [half_16_10_total1, half_16_10_total2, half_16_10_total3, half_16_10_total4, half_16_10_total5, half_16_10_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_16_10_hx2 : SourcePowerBound
    (powerBoxCross 9 14 4 half_16_10_φ2) (169299892171/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 14) (u := 12) (t := 15)
    (D := 4) (ψ := (491455481/5000000000 : ℝ)) half_16_10_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_16_10_bounds2 l).1) (fun l => (half_16_10_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_16_10_total1, half_16_10_total2, half_16_10_total3, half_16_10_total4, half_16_10_total5, half_16_10_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_13_10) (half_15_10)
    (by simpa only [half_16_10_φ3, show (2:ℝ)*4=8 by norm_num] using half_16_10_hx3)
  exact h.weaken (by norm_num [half_16_10_total1, half_16_10_total2, half_16_10_total3, half_16_10_total4, half_16_10_total5, half_16_10_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_16_10_hx1 : SourcePowerBound
    (powerBoxCross 9 15 2 half_16_10_φ1) (204158775679/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 15) (u := 13) (t := 16)
    (D := 2) (ψ := (101391921/1000000000 : ℝ)) half_16_10_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_16_10_bounds1 l).1) (fun l => (half_16_10_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_16_10_total1, half_16_10_total2, half_16_10_total3, half_16_10_total4, half_16_10_total5, half_16_10_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_14_10) (half_16_09)
    (by simpa only [half_16_10_φ2, show (2:ℝ)*2=4 by norm_num] using half_16_10_hx2)
  exact h.weaken (by norm_num [half_16_10_total1, half_16_10_total2, half_16_10_total3, half_16_10_total4, half_16_10_total5, half_16_10_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_16_10 : AdmissibleExponent 9 32 (117148704573/5000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 14) (ψ := (1039263223/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_15_10)
    (by simpa only [half_16_10_φ1] using half_16_10_hx1)
  exact admissibleExponent_mono h (by norm_num [half_16_10_total1, half_16_10_total2, half_16_10_total3, half_16_10_total4, half_16_10_total5, half_16_10_total6, parameterExponent, curveLoss, dyadicExponent])

private def half_17_10_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1055728371/10000000000 : ℝ)

private theorem half_17_10_total1 : total half_17_10_φ1=(1055728371/10000000000 : ℝ) := by
  norm_num [half_17_10_φ1,total,emptyPhi,Fin.snoc]

private theorem half_17_10_bounds1 : ∀ l,0≤half_17_10_φ1 l ∧ half_17_10_φ1 l≤1 ∧
    0≤shiftExponents 9 half_17_10_φ1 l :=
  alternate_bounds_snoc emptyPhi (1055728371/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_17_10_φ2 : Fin 2 → ℝ := Fin.snoc half_17_10_φ1 (64756793/625000000 : ℝ)

private theorem half_17_10_total2 : total half_17_10_φ2=(2091837059/10000000000 : ℝ) := by
  change total (Fin.snoc half_17_10_φ1 (64756793/625000000 : ℝ))=(2091837059/10000000000 : ℝ)
  rw [alternate_total_snoc,half_17_10_total1]
  norm_num

private theorem half_17_10_bounds2 : ∀ l,0≤half_17_10_φ2 l ∧ half_17_10_φ2 l≤1 ∧
    0≤shiftExponents 9 half_17_10_φ2 l :=
  alternate_bounds_snoc half_17_10_φ1 (64756793/625000000 : ℝ) half_17_10_bounds1 (by norm_num)

private def half_17_10_φ3 : Fin 3 → ℝ := Fin.snoc half_17_10_φ2 (988520367/10000000000 : ℝ)

private theorem half_17_10_total3 : total half_17_10_φ3=(1540178713/5000000000 : ℝ) := by
  change total (Fin.snoc half_17_10_φ2 (988520367/10000000000 : ℝ))=(1540178713/5000000000 : ℝ)
  rw [alternate_total_snoc,half_17_10_total2]
  norm_num

private theorem half_17_10_bounds3 : ∀ l,0≤half_17_10_φ3 l ∧ half_17_10_φ3 l≤1 ∧
    0≤shiftExponents 9 half_17_10_φ3 l :=
  alternate_bounds_snoc half_17_10_φ2 (988520367/10000000000 : ℝ) half_17_10_bounds2 (by norm_num)

private def half_17_10_φ4 : Fin 4 → ℝ := Fin.snoc half_17_10_φ3 (864955321/10000000000 : ℝ)

private theorem half_17_10_total4 : total half_17_10_φ4=(3945312747/10000000000 : ℝ) := by
  change total (Fin.snoc half_17_10_φ3 (864955321/10000000000 : ℝ))=(3945312747/10000000000 : ℝ)
  rw [alternate_total_snoc,half_17_10_total3]
  norm_num

private theorem half_17_10_bounds4 : ∀ l,0≤half_17_10_φ4 l ∧ half_17_10_φ4 l≤1 ∧
    0≤shiftExponents 9 half_17_10_φ4 l :=
  alternate_bounds_snoc half_17_10_φ3 (864955321/10000000000 : ℝ) half_17_10_bounds3 (by norm_num)

private def half_17_10_φ5 : Fin 5 → ℝ := Fin.snoc half_17_10_φ4 (378417953/5000000000 : ℝ)

private theorem half_17_10_total5 : total half_17_10_φ5=(4702148653/10000000000 : ℝ) := by
  change total (Fin.snoc half_17_10_φ4 (378417953/5000000000 : ℝ))=(4702148653/10000000000 : ℝ)
  rw [alternate_total_snoc,half_17_10_total4]
  norm_num

private theorem half_17_10_bounds5 : ∀ l,0≤half_17_10_φ5 l ∧ half_17_10_φ5 l≤1 ∧
    0≤shiftExponents 9 half_17_10_φ5 l :=
  alternate_bounds_snoc half_17_10_φ4 (378417953/5000000000 : ℝ) half_17_10_bounds4 (by norm_num)

private def half_17_10_φ6 : Fin 6 → ℝ := Fin.snoc half_17_10_φ5 (331115709/5000000000 : ℝ)

private theorem half_17_10_total6 : total half_17_10_φ6=(5364380071/10000000000 : ℝ) := by
  change total (Fin.snoc half_17_10_φ5 (331115709/5000000000 : ℝ))=(5364380071/10000000000 : ℝ)
  rw [alternate_total_snoc,half_17_10_total5]
  norm_num

private theorem half_17_10_bounds6 : ∀ l,0≤half_17_10_φ6 l ∧ half_17_10_φ6 l≤1 ∧
    0≤shiftExponents 9 half_17_10_φ6 l :=
  alternate_bounds_snoc half_17_10_φ5 (331115709/5000000000 : ℝ) half_17_10_bounds5 (by norm_num)

private theorem half_17_10_prefix : PrefixCondition 9 half_17_10_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_17_10_φ1, half_17_10_φ2, half_17_10_φ3, half_17_10_φ4, half_17_10_φ5, half_17_10_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_17_10_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_17_10_φ6) (8906859787/1250000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_17_10_φ6
    (fun i => (half_17_10_bounds6 i).1) (fun i => (half_17_10_bounds6 i).2.1)
    (fun i => (half_17_10_bounds6 i).2.2) half_17_10_prefix
  convert h using 1 <;> norm_num [half_17_10_total1, half_17_10_total2, half_17_10_total3, half_17_10_total4, half_17_10_total5, half_17_10_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_17_10_hx6 : SourcePowerBound
    (powerBoxCross 9 11 64 half_17_10_φ6) (90603963443/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 11) (r := 2) (v := 14) (w := 15) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_17_10_φ6 (by norm_num [half_17_10_total1, half_17_10_total2, half_17_10_total3, half_17_10_total4, half_17_10_total5, half_17_10_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_17_10_total1, half_17_10_total2, half_17_10_total3, half_17_10_total4, half_17_10_total5, half_17_10_total6, parameterExponent, curveLoss, dyadicExponent]) half_17_10_hF2
    (half_14_10) (half_15_10)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_17_10_total1, half_17_10_total2, half_17_10_total3, half_17_10_total4, half_17_10_total5, half_17_10_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_17_10_hx5 : SourcePowerBound
    (powerBoxCross 9 12 32 half_17_10_φ5) (5292621629/500000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 12) (u := 10) (t := 13)
    (D := 32) (ψ := (331115709/5000000000 : ℝ)) half_17_10_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_17_10_bounds5 l).1) (fun l => (half_17_10_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_17_10_total1, half_17_10_total2, half_17_10_total3, half_17_10_total4, half_17_10_total5, half_17_10_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_11_10) (half_13_10)
    (by simpa only [half_17_10_φ6, show (2:ℝ)*32=64 by norm_num] using half_17_10_hx6)
  exact h.weaken (by norm_num [half_17_10_total1, half_17_10_total2, half_17_10_total3, half_17_10_total4, half_17_10_total5, half_17_10_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_17_10_hx4 : SourcePowerBound
    (powerBoxCross 9 13 16 half_17_10_φ4) (31376361671/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 13) (u := 11) (t := 14)
    (D := 16) (ψ := (378417953/5000000000 : ℝ)) half_17_10_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_17_10_bounds4 l).1) (fun l => (half_17_10_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_17_10_total1, half_17_10_total2, half_17_10_total3, half_17_10_total4, half_17_10_total5, half_17_10_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_12_10) (half_14_10)
    (by simpa only [half_17_10_φ5, show (2:ℝ)*16=32 by norm_num] using half_17_10_hx5)
  exact h.weaken (by norm_num [half_17_10_total1, half_17_10_total2, half_17_10_total3, half_17_10_total4, half_17_10_total5, half_17_10_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_17_10_hx3 : SourcePowerBound
    (powerBoxCross 9 14 8 half_17_10_φ3) (75404210333/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 14) (u := 12) (t := 15)
    (D := 8) (ψ := (864955321/10000000000 : ℝ)) half_17_10_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_17_10_bounds3 l).1) (fun l => (half_17_10_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_17_10_total1, half_17_10_total2, half_17_10_total3, half_17_10_total4, half_17_10_total5, half_17_10_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_13_10) (half_15_10)
    (by simpa only [half_17_10_φ4, show (2:ℝ)*8=16 by norm_num] using half_17_10_hx4)
  exact h.weaken (by norm_num [half_17_10_total1, half_17_10_total2, half_17_10_total3, half_17_10_total4, half_17_10_total5, half_17_10_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_17_10_hx2 : SourcePowerBound
    (powerBoxCross 9 15 4 half_17_10_φ2) (183024991461/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 15) (u := 13) (t := 16)
    (D := 4) (ψ := (988520367/10000000000 : ℝ)) half_17_10_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_17_10_bounds2 l).1) (fun l => (half_17_10_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_17_10_total1, half_17_10_total2, half_17_10_total3, half_17_10_total4, half_17_10_total5, half_17_10_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_14_10) (half_16_10)
    (by simpa only [half_17_10_φ3, show (2:ℝ)*4=8 by norm_num] using half_17_10_hx3)
  exact h.weaken (by norm_num [half_17_10_total1, half_17_10_total2, half_17_10_total3, half_17_10_total4, half_17_10_total5, half_17_10_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_17_10_hx1 : SourcePowerBound
    (powerBoxCross 9 16 2 half_17_10_φ1) (110308847657/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 16) (u := 14) (t := 17)
    (D := 2) (ψ := (64756793/625000000 : ℝ)) half_17_10_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_17_10_bounds1 l).1) (fun l => (half_17_10_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_17_10_total1, half_17_10_total2, half_17_10_total3, half_17_10_total4, half_17_10_total5, half_17_10_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_15_10) (half_17_09)
    (by simpa only [half_17_10_φ2, show (2:ℝ)*2=4 by norm_num] using half_17_10_hx2)
  exact h.weaken (by norm_num [half_17_10_total1, half_17_10_total2, half_17_10_total3, half_17_10_total4, half_17_10_total5, half_17_10_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_17_10 : AdmissibleExponent 9 34 (50669054963/2000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 15) (ψ := (1055728371/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_16_10)
    (by simpa only [half_17_10_φ1] using half_17_10_hx1)
  exact admissibleExponent_mono h (by norm_num [half_17_10_total1, half_17_10_total2, half_17_10_total3, half_17_10_total4, half_17_10_total5, half_17_10_total6, parameterExponent, curveLoss, dyadicExponent])

private def half_18_10_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (534313301/5000000000 : ℝ)

private theorem half_18_10_total1 : total half_18_10_φ1=(534313301/5000000000 : ℝ) := by
  norm_num [half_18_10_φ1,total,emptyPhi,Fin.snoc]

private theorem half_18_10_bounds1 : ∀ l,0≤half_18_10_φ1 l ∧ half_18_10_φ1 l≤1 ∧
    0≤shiftExponents 9 half_18_10_φ1 l :=
  alternate_bounds_snoc emptyPhi (534313301/5000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_18_10_φ2 : Fin 2 → ℝ := Fin.snoc half_18_10_φ1 (105409743/1000000000 : ℝ)

private theorem half_18_10_total2 : total half_18_10_φ2=(33167563/156250000 : ℝ) := by
  change total (Fin.snoc half_18_10_φ1 (105409743/1000000000 : ℝ))=(33167563/156250000 : ℝ)
  rw [alternate_total_snoc,half_18_10_total1]
  norm_num

private theorem half_18_10_bounds2 : ∀ l,0≤half_18_10_φ2 l ∧ half_18_10_φ2 l≤1 ∧
    0≤shiftExponents 9 half_18_10_φ2 l :=
  alternate_bounds_snoc half_18_10_φ1 (105409743/1000000000 : ℝ) half_18_10_bounds1 (by norm_num)

private def half_18_10_φ3 : Fin 3 → ℝ := Fin.snoc half_18_10_φ2 (196931899/2000000000 : ℝ)

private theorem half_18_10_total3 : total half_18_10_φ3=(3107383527/10000000000 : ℝ) := by
  change total (Fin.snoc half_18_10_φ2 (196931899/2000000000 : ℝ))=(3107383527/10000000000 : ℝ)
  rw [alternate_total_snoc,half_18_10_total2]
  norm_num

private theorem half_18_10_bounds3 : ∀ l,0≤half_18_10_φ3 l ∧ half_18_10_φ3 l≤1 ∧
    0≤shiftExponents 9 half_18_10_φ3 l :=
  alternate_bounds_snoc half_18_10_φ2 (196931899/2000000000 : ℝ) half_18_10_bounds2 (by norm_num)

private def half_18_10_φ4 : Fin 4 → ℝ := Fin.snoc half_18_10_φ3 (430788529/5000000000 : ℝ)

private theorem half_18_10_total4 : total half_18_10_φ4=(793792117/2000000000 : ℝ) := by
  change total (Fin.snoc half_18_10_φ3 (430788529/5000000000 : ℝ))=(793792117/2000000000 : ℝ)
  rw [alternate_total_snoc,half_18_10_total3]
  norm_num

private theorem half_18_10_bounds4 : ∀ l,0≤half_18_10_φ4 l ∧ half_18_10_φ4 l≤1 ∧
    0≤shiftExponents 9 half_18_10_φ4 l :=
  alternate_bounds_snoc half_18_10_φ3 (430788529/5000000000 : ℝ) half_18_10_bounds3 (by norm_num)

private def half_18_10_φ5 : Fin 5 → ℝ := Fin.snoc half_18_10_φ4 (376939963/5000000000 : ℝ)

private theorem half_18_10_total5 : total half_18_10_φ5=(4722840511/10000000000 : ℝ) := by
  change total (Fin.snoc half_18_10_φ4 (376939963/5000000000 : ℝ))=(4722840511/10000000000 : ℝ)
  rw [alternate_total_snoc,half_18_10_total4]
  norm_num

private theorem half_18_10_bounds5 : ∀ l,0≤half_18_10_φ5 l ∧ half_18_10_φ5 l≤1 ∧
    0≤shiftExponents 9 half_18_10_φ5 l :=
  alternate_bounds_snoc half_18_10_φ4 (376939963/5000000000 : ℝ) half_18_10_bounds4 (by norm_num)

private def half_18_10_φ6 : Fin 6 → ℝ := Fin.snoc half_18_10_φ5 (131928987/2000000000 : ℝ)

private theorem half_18_10_total6 : total half_18_10_φ6=(2691242723/5000000000 : ℝ) := by
  change total (Fin.snoc half_18_10_φ5 (131928987/2000000000 : ℝ))=(2691242723/5000000000 : ℝ)
  rw [alternate_total_snoc,half_18_10_total5]
  norm_num

private theorem half_18_10_bounds6 : ∀ l,0≤half_18_10_φ6 l ∧ half_18_10_φ6 l≤1 ∧
    0≤shiftExponents 9 half_18_10_φ6 l :=
  alternate_bounds_snoc half_18_10_φ5 (131928987/2000000000 : ℝ) half_18_10_bounds5 (by norm_num)

private theorem half_18_10_prefix : PrefixCondition 9 half_18_10_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_18_10_φ1, half_18_10_φ2, half_18_10_φ3, half_18_10_φ4, half_18_10_φ5, half_18_10_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_18_10_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_18_10_φ6) (4426271831/625000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_18_10_φ6
    (fun i => (half_18_10_bounds6 i).1) (fun i => (half_18_10_bounds6 i).2.1)
    (fun i => (half_18_10_bounds6 i).2.2) half_18_10_prefix
  convert h using 1 <;> norm_num [half_18_10_total1, half_18_10_total2, half_18_10_total3, half_18_10_total4, half_18_10_total5, half_18_10_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_18_10_hx6 : SourcePowerBound
    (powerBoxCross 9 12 64 half_18_10_φ6) (98845464577/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 12) (r := 2) (v := 0) (w := 16) (D := 64)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_18_10_φ6 (by norm_num [half_18_10_total1, half_18_10_total2, half_18_10_total3, half_18_10_total4, half_18_10_total5, half_18_10_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_18_10_total1, half_18_10_total2, half_18_10_total3, half_18_10_total4, half_18_10_total5, half_18_10_total6, parameterExponent, curveLoss, dyadicExponent]) half_18_10_hF2
    (admissibleExponent_zero 9) (half_16_10)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_18_10_total1, half_18_10_total2, half_18_10_total3, half_18_10_total4, half_18_10_total5, half_18_10_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_18_10_hx5 : SourcePowerBound
    (powerBoxCross 9 13 32 half_18_10_φ5) (14389146239/1250000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 13) (u := 11) (t := 14)
    (D := 32) (ψ := (131928987/2000000000 : ℝ)) half_18_10_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_18_10_bounds5 l).1) (fun l => (half_18_10_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_18_10_total1, half_18_10_total2, half_18_10_total3, half_18_10_total4, half_18_10_total5, half_18_10_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_12_10) (half_14_10)
    (by simpa only [half_18_10_φ6, show (2:ℝ)*32=64 by norm_num] using half_18_10_hx6)
  exact h.weaken (by norm_num [half_18_10_total1, half_18_10_total2, half_18_10_total3, half_18_10_total4, half_18_10_total5, half_18_10_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_18_10_hx4 : SourcePowerBound
    (powerBoxCross 9 14 16 half_18_10_φ4) (6804697647/500000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 14) (u := 12) (t := 15)
    (D := 16) (ψ := (376939963/5000000000 : ℝ)) half_18_10_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_18_10_bounds4 l).1) (fun l => (half_18_10_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_18_10_total1, half_18_10_total2, half_18_10_total3, half_18_10_total4, half_18_10_total5, half_18_10_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_13_10) (half_15_10)
    (by simpa only [half_18_10_φ5, show (2:ℝ)*16=32 by norm_num] using half_18_10_hx5)
  exact h.weaken (by norm_num [half_18_10_total1, half_18_10_total2, half_18_10_total3, half_18_10_total4, half_18_10_total5, half_18_10_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_18_10_hx3 : SourcePowerBound
    (powerBoxCross 9 15 8 half_18_10_φ3) (162994841739/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 15) (u := 13) (t := 16)
    (D := 8) (ψ := (430788529/5000000000 : ℝ)) half_18_10_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_18_10_bounds3 l).1) (fun l => (half_18_10_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_18_10_total1, half_18_10_total2, half_18_10_total3, half_18_10_total4, half_18_10_total5, half_18_10_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_14_10) (half_16_10)
    (by simpa only [half_18_10_φ4, show (2:ℝ)*8=16 by norm_num] using half_18_10_hx4)
  exact h.weaken (by norm_num [half_18_10_total1, half_18_10_total2, half_18_10_total3, half_18_10_total4, half_18_10_total5, half_18_10_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_18_10_hx2 : SourcePowerBound
    (powerBoxCross 9 16 4 half_18_10_φ2) (39413523933/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 16) (u := 14) (t := 17)
    (D := 4) (ψ := (196931899/2000000000 : ℝ)) half_18_10_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_18_10_bounds2 l).1) (fun l => (half_18_10_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_18_10_total1, half_18_10_total2, half_18_10_total3, half_18_10_total4, half_18_10_total5, half_18_10_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_15_10) (half_17_10)
    (by simpa only [half_18_10_φ3, show (2:ℝ)*4=8 by norm_num] using half_18_10_hx3)
  exact h.weaken (by norm_num [half_18_10_total1, half_18_10_total2, half_18_10_total3, half_18_10_total4, half_18_10_total5, half_18_10_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_18_10_hx1 : SourcePowerBound
    (powerBoxCross 9 17 2 half_18_10_φ1) (23734075141/1000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 17) (u := 15) (t := 18)
    (D := 2) (ψ := (105409743/1000000000 : ℝ)) half_18_10_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_18_10_bounds1 l).1) (fun l => (half_18_10_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_18_10_total1, half_18_10_total2, half_18_10_total3, half_18_10_total4, half_18_10_total5, half_18_10_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_16_10) (half_18_09)
    (by simpa only [half_18_10_φ2, show (2:ℝ)*2=4 by norm_num] using half_18_10_hx2)
  exact h.weaken (by norm_num [half_18_10_total1, half_18_10_total2, half_18_10_total3, half_18_10_total4, half_18_10_total5, half_18_10_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_18_10 : AdmissibleExponent 9 36 (68151357319/2500000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 16) (ψ := (534313301/5000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_17_10)
    (by simpa only [half_18_10_φ1] using half_18_10_hx1)
  exact admissibleExponent_mono h (by norm_num [half_18_10_total1, half_18_10_total2, half_18_10_total3, half_18_10_total4, half_18_10_total5, half_18_10_total6, parameterExponent, curveLoss, dyadicExponent])

private def half_19_10_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (269722967/2500000000 : ℝ)

private theorem half_19_10_total1 : total half_19_10_φ1=(269722967/2500000000 : ℝ) := by
  norm_num [half_19_10_φ1,total,emptyPhi,Fin.snoc]

private theorem half_19_10_bounds1 : ∀ l,0≤half_19_10_φ1 l ∧ half_19_10_φ1 l≤1 ∧
    0≤shiftExponents 9 half_19_10_φ1 l :=
  alternate_bounds_snoc emptyPhi (269722967/2500000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_19_10_φ2 : Fin 2 → ℝ := Fin.snoc half_19_10_φ1 (1068203183/10000000000 : ℝ)

private theorem half_19_10_total2 : total half_19_10_φ2=(2147095051/10000000000 : ℝ) := by
  change total (Fin.snoc half_19_10_φ1 (1068203183/10000000000 : ℝ))=(2147095051/10000000000 : ℝ)
  rw [alternate_total_snoc,half_19_10_total1]
  norm_num

private theorem half_19_10_bounds2 : ∀ l,0≤half_19_10_φ2 l ∧ half_19_10_φ2 l≤1 ∧
    0≤shiftExponents 9 half_19_10_φ2 l :=
  alternate_bounds_snoc half_19_10_φ1 (1068203183/10000000000 : ℝ) half_19_10_bounds1 (by norm_num)

private def half_19_10_φ3 : Fin 3 → ℝ := Fin.snoc half_19_10_φ2 (490806559/5000000000 : ℝ)

private theorem half_19_10_total3 : total half_19_10_φ3=(3128708169/10000000000 : ℝ) := by
  change total (Fin.snoc half_19_10_φ2 (490806559/5000000000 : ℝ))=(3128708169/10000000000 : ℝ)
  rw [alternate_total_snoc,half_19_10_total2]
  norm_num

private theorem half_19_10_bounds3 : ∀ l,0≤half_19_10_φ3 l ∧ half_19_10_φ3 l≤1 ∧
    0≤shiftExponents 9 half_19_10_φ3 l :=
  alternate_bounds_snoc half_19_10_φ2 (490806559/5000000000 : ℝ) half_19_10_bounds2 (by norm_num)

private def half_19_10_φ4 : Fin 4 → ℝ := Fin.snoc half_19_10_φ3 (429455739/5000000000 : ℝ)

private theorem half_19_10_total4 : total half_19_10_φ4=(3987619647/10000000000 : ℝ) := by
  change total (Fin.snoc half_19_10_φ3 (429455739/5000000000 : ℝ))=(3987619647/10000000000 : ℝ)
  rw [alternate_total_snoc,half_19_10_total3]
  norm_num

private theorem half_19_10_bounds4 : ∀ l,0≤half_19_10_φ4 l ∧ half_19_10_φ4 l≤1 ∧
    0≤shiftExponents 9 half_19_10_φ4 l :=
  alternate_bounds_snoc half_19_10_φ3 (429455739/5000000000 : ℝ) half_19_10_bounds3 (by norm_num)

private def half_19_10_φ5 : Fin 5 → ℝ := Fin.snoc half_19_10_φ4 (751547543/10000000000 : ℝ)

private theorem half_19_10_total5 : total half_19_10_φ5=(473916719/1000000000 : ℝ) := by
  change total (Fin.snoc half_19_10_φ4 (751547543/10000000000 : ℝ))=(473916719/1000000000 : ℝ)
  rw [alternate_total_snoc,half_19_10_total4]
  norm_num

private theorem half_19_10_bounds5 : ∀ l,0≤half_19_10_φ5 l ∧ half_19_10_φ5 l≤1 ∧
    0≤shiftExponents 9 half_19_10_φ5 l :=
  alternate_bounds_snoc half_19_10_φ4 (751547543/10000000000 : ℝ) half_19_10_bounds4 (by norm_num)

private def half_19_10_φ6 : Fin 6 → ℝ := Fin.snoc half_19_10_φ5 (6576041/100000000 : ℝ)

private theorem half_19_10_total6 : total half_19_10_φ6=(539677129/1000000000 : ℝ) := by
  change total (Fin.snoc half_19_10_φ5 (6576041/100000000 : ℝ))=(539677129/1000000000 : ℝ)
  rw [alternate_total_snoc,half_19_10_total5]
  norm_num

private theorem half_19_10_bounds6 : ∀ l,0≤half_19_10_φ6 l ∧ half_19_10_φ6 l≤1 ∧
    0≤shiftExponents 9 half_19_10_φ6 l :=
  alternate_bounds_snoc half_19_10_φ5 (6576041/100000000 : ℝ) half_19_10_bounds5 (by norm_num)

private theorem half_19_10_prefix : PrefixCondition 9 half_19_10_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_19_10_φ1, half_19_10_φ2, half_19_10_φ3, half_19_10_φ4, half_19_10_φ5, half_19_10_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_19_10_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_19_10_φ6) (880968613/125000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_19_10_φ6
    (fun i => (half_19_10_bounds6 i).1) (fun i => (half_19_10_bounds6 i).2.1)
    (fun i => (half_19_10_bounds6 i).2.2) half_19_10_prefix
  convert h using 1 <;> norm_num [half_19_10_total1, half_19_10_total2, half_19_10_total3, half_19_10_total4, half_19_10_total5, half_19_10_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_19_10_hx6 : SourcePowerBound
    (powerBoxCross 9 13 64 half_19_10_φ6) (107301312853/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 13) (r := 2) (v := 17) (w := 18) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_19_10_φ6 (by norm_num [half_19_10_total1, half_19_10_total2, half_19_10_total3, half_19_10_total4, half_19_10_total5, half_19_10_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_19_10_total1, half_19_10_total2, half_19_10_total3, half_19_10_total4, half_19_10_total5, half_19_10_total6, parameterExponent, curveLoss, dyadicExponent]) half_19_10_hF2
    (half_17_10) (half_18_10)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_19_10_total1, half_19_10_total2, half_19_10_total3, half_19_10_total4, half_19_10_total5, half_19_10_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_19_10_hx5 : SourcePowerBound
    (powerBoxCross 9 14 32 half_19_10_φ5) (124604102059/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 14) (u := 12) (t := 15)
    (D := 32) (ψ := (6576041/100000000 : ℝ)) half_19_10_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_19_10_bounds5 l).1) (fun l => (half_19_10_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_19_10_total1, half_19_10_total2, half_19_10_total3, half_19_10_total4, half_19_10_total5, half_19_10_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_13_10) (half_15_10)
    (by simpa only [half_19_10_φ6, show (2:ℝ)*32=64 by norm_num] using half_19_10_hx6)
  exact h.weaken (by norm_num [half_19_10_total1, half_19_10_total2, half_19_10_total3, half_19_10_total4, half_19_10_total5, half_19_10_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_19_10_hx4 : SourcePowerBound
    (powerBoxCross 9 15 16 half_19_10_φ4) (4591616289/312500000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 15) (u := 13) (t := 16)
    (D := 16) (ψ := (751547543/10000000000 : ℝ)) half_19_10_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_19_10_bounds4 l).1) (fun l => (half_19_10_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_19_10_total1, half_19_10_total2, half_19_10_total3, half_19_10_total4, half_19_10_total5, half_19_10_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_14_10) (half_16_10)
    (by simpa only [half_19_10_φ5, show (2:ℝ)*16=32 by norm_num] using half_19_10_hx5)
  exact h.weaken (by norm_num [half_19_10_total1, half_19_10_total2, half_19_10_total3, half_19_10_total4, half_19_10_total5, half_19_10_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_19_10_hx3 : SourcePowerBound
    (powerBoxCross 9 16 8 half_19_10_φ3) (87722855121/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 16) (u := 14) (t := 17)
    (D := 8) (ψ := (429455739/5000000000 : ℝ)) half_19_10_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_19_10_bounds3 l).1) (fun l => (half_19_10_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_19_10_total1, half_19_10_total2, half_19_10_total3, half_19_10_total4, half_19_10_total5, half_19_10_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_15_10) (half_17_10)
    (by simpa only [half_19_10_φ4, show (2:ℝ)*8=16 by norm_num] using half_19_10_hx4)
  exact h.weaken (by norm_num [half_19_10_total1, half_19_10_total2, half_19_10_total3, half_19_10_total4, half_19_10_total5, half_19_10_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_19_10_hx2 : SourcePowerBound
    (powerBoxCross 9 17 4 half_19_10_φ2) (211386704481/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 17) (u := 15) (t := 18)
    (D := 4) (ψ := (490806559/5000000000 : ℝ)) half_19_10_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_19_10_bounds2 l).1) (fun l => (half_19_10_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_19_10_total1, half_19_10_total2, half_19_10_total3, half_19_10_total4, half_19_10_total5, half_19_10_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_16_10) (half_18_10)
    (by simpa only [half_19_10_φ3, show (2:ℝ)*4=8 by norm_num] using half_19_10_hx3)
  exact h.weaken (by norm_num [half_19_10_total1, half_19_10_total2, half_19_10_total3, half_19_10_total4, half_19_10_total5, half_19_10_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_19_10_hx1 : SourcePowerBound
    (powerBoxCross 9 18 2 half_19_10_φ1) (7946035721/312500000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 18) (u := 16) (t := 19)
    (D := 2) (ψ := (1068203183/10000000000 : ℝ)) half_19_10_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_19_10_bounds1 l).1) (fun l => (half_19_10_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_19_10_total1, half_19_10_total2, half_19_10_total3, half_19_10_total4, half_19_10_total5, half_19_10_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_17_10) (half_19_09)
    (by simpa only [half_19_10_φ2, show (2:ℝ)*2=4 by norm_num] using half_19_10_hx2)
  exact h.weaken (by norm_num [half_19_10_total1, half_19_10_total2, half_19_10_total3, half_19_10_total4, half_19_10_total5, half_19_10_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_19_10 : AdmissibleExponent 9 38 (73008589613/2500000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 17) (ψ := (269722967/2500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_18_10)
    (by simpa only [half_19_10_φ1] using half_19_10_hx1)
  exact admissibleExponent_mono h (by norm_num [half_19_10_total1, half_19_10_total2, half_19_10_total3, half_19_10_total4, half_19_10_total5, half_19_10_total6, parameterExponent, curveLoss, dyadicExponent])

private def half_20_10_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (217377813/2000000000 : ℝ)

private theorem half_20_10_total1 : total half_20_10_φ1=(217377813/2000000000 : ℝ) := by
  norm_num [half_20_10_φ1,total,emptyPhi,Fin.snoc]

private theorem half_20_10_bounds1 : ∀ l,0≤half_20_10_φ1 l ∧ half_20_10_φ1 l≤1 ∧
    0≤shiftExponents 9 half_20_10_φ1 l :=
  alternate_bounds_snoc emptyPhi (217377813/2000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_20_10_φ2 : Fin 2 → ℝ := Fin.snoc half_20_10_φ1 (215859317/2000000000 : ℝ)

private theorem half_20_10_total2 : total half_20_10_φ2=(43323713/200000000 : ℝ) := by
  change total (Fin.snoc half_20_10_φ1 (215859317/2000000000 : ℝ))=(43323713/200000000 : ℝ)
  rw [alternate_total_snoc,half_20_10_total1]
  norm_num

private theorem half_20_10_bounds2 : ∀ l,0≤half_20_10_φ2 l ∧ half_20_10_φ2 l≤1 ∧
    0≤shiftExponents 9 half_20_10_φ2 l :=
  alternate_bounds_snoc half_20_10_φ1 (215859317/2000000000 : ℝ) half_20_10_bounds1 (by norm_num)

private def half_20_10_φ3 : Fin 3 → ℝ := Fin.snoc half_20_10_φ2 (979226793/10000000000 : ℝ)

private theorem half_20_10_total3 : total half_20_10_φ3=(3145412443/10000000000 : ℝ) := by
  change total (Fin.snoc half_20_10_φ2 (979226793/10000000000 : ℝ))=(3145412443/10000000000 : ℝ)
  rw [alternate_total_snoc,half_20_10_total2]
  norm_num

private theorem half_20_10_bounds3 : ∀ l,0≤half_20_10_φ3 l ∧ half_20_10_φ3 l≤1 ∧
    0≤shiftExponents 9 half_20_10_φ3 l :=
  alternate_bounds_snoc half_20_10_φ2 (979226793/10000000000 : ℝ) half_20_10_bounds2 (by norm_num)

private def half_20_10_φ4 : Fin 4 → ℝ := Fin.snoc half_20_10_φ3 (214205861/2500000000 : ℝ)

private theorem half_20_10_total4 : total half_20_10_φ4=(4002235887/10000000000 : ℝ) := by
  change total (Fin.snoc half_20_10_φ3 (214205861/2500000000 : ℝ))=(4002235887/10000000000 : ℝ)
  rw [alternate_total_snoc,half_20_10_total3]
  norm_num

private theorem half_20_10_bounds4 : ∀ l,0≤half_20_10_φ4 l ∧ half_20_10_φ4 l≤1 ∧
    0≤shiftExponents 9 half_20_10_φ4 l :=
  alternate_bounds_snoc half_20_10_φ3 (214205861/2500000000 : ℝ) half_20_10_bounds3 (by norm_num)

private def half_20_10_φ5 : Fin 5 → ℝ := Fin.snoc half_20_10_φ4 (749720513/10000000000 : ℝ)

private theorem half_20_10_total5 : total half_20_10_φ5=(11879891/25000000 : ℝ) := by
  change total (Fin.snoc half_20_10_φ4 (749720513/10000000000 : ℝ))=(11879891/25000000 : ℝ)
  rw [alternate_total_snoc,half_20_10_total4]
  norm_num

private theorem half_20_10_bounds5 : ∀ l,0≤half_20_10_φ5 l ∧ half_20_10_φ5 l≤1 ∧
    0≤shiftExponents 9 half_20_10_φ5 l :=
  alternate_bounds_snoc half_20_10_φ4 (749720513/10000000000 : ℝ) half_20_10_bounds4 (by norm_num)

private def half_20_10_φ6 : Fin 6 → ℝ := Fin.snoc half_20_10_φ5 (656005449/10000000000 : ℝ)

private theorem half_20_10_total6 : total half_20_10_φ6=(5407961849/10000000000 : ℝ) := by
  change total (Fin.snoc half_20_10_φ5 (656005449/10000000000 : ℝ))=(5407961849/10000000000 : ℝ)
  rw [alternate_total_snoc,half_20_10_total5]
  norm_num

private theorem half_20_10_bounds6 : ∀ l,0≤half_20_10_φ6 l ∧ half_20_10_φ6 l≤1 ∧
    0≤shiftExponents 9 half_20_10_φ6 l :=
  alternate_bounds_snoc half_20_10_φ5 (656005449/10000000000 : ℝ) half_20_10_bounds5 (by norm_num)

private theorem half_20_10_prefix : PrefixCondition 9 half_20_10_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_20_10_φ1, half_20_10_φ2, half_20_10_φ3, half_20_10_φ4, half_20_10_φ5, half_20_10_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_20_10_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_20_10_φ6) (8776114453/1250000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_20_10_φ6
    (fun i => (half_20_10_bounds6 i).1) (fun i => (half_20_10_bounds6 i).2.1)
    (fun i => (half_20_10_bounds6 i).2.2) half_20_10_prefix
  convert h using 1 <;> norm_num [half_20_10_total1, half_20_10_total2, half_20_10_total3, half_20_10_total4, half_20_10_total5, half_20_10_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_20_10_hx6 : SourcePowerBound
    (powerBoxCross 9 14 64 half_20_10_φ6) (57949618981/5000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 14) (r := 2) (v := 18) (w := 19) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_20_10_φ6 (by norm_num [half_20_10_total1, half_20_10_total2, half_20_10_total3, half_20_10_total4, half_20_10_total5, half_20_10_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_20_10_total1, half_20_10_total2, half_20_10_total3, half_20_10_total4, half_20_10_total5, half_20_10_total6, parameterExponent, curveLoss, dyadicExponent]) half_20_10_hF2
    (half_18_10) (half_19_10)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_20_10_total1, half_20_10_total2, half_20_10_total3, half_20_10_total4, half_20_10_total5, half_20_10_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_10_hx5 : SourcePowerBound
    (powerBoxCross 9 15 32 half_20_10_φ5) (134278017871/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 15) (u := 13) (t := 16)
    (D := 32) (ψ := (656005449/10000000000 : ℝ)) half_20_10_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_10_bounds5 l).1) (fun l => (half_20_10_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_10_total1, half_20_10_total2, half_20_10_total3, half_20_10_total4, half_20_10_total5, half_20_10_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_14_10) (half_16_10)
    (by simpa only [half_20_10_φ6, show (2:ℝ)*32=64 by norm_num] using half_20_10_hx6)
  exact h.weaken (by norm_num [half_20_10_total1, half_20_10_total2, half_20_10_total3, half_20_10_total4, half_20_10_total5, half_20_10_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_10_hx4 : SourcePowerBound
    (powerBoxCross 9 16 16 half_20_10_φ4) (157976272701/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 16) (u := 14) (t := 17)
    (D := 16) (ψ := (749720513/10000000000 : ℝ)) half_20_10_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_10_bounds4 l).1) (fun l => (half_20_10_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_10_total1, half_20_10_total2, half_20_10_total3, half_20_10_total4, half_20_10_total5, half_20_10_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_15_10) (half_17_10)
    (by simpa only [half_20_10_φ5, show (2:ℝ)*16=32 by norm_num] using half_20_10_hx5)
  exact h.weaken (by norm_num [half_20_10_total1, half_20_10_total2, half_20_10_total3, half_20_10_total4, half_20_10_total5, half_20_10_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_10_hx3 : SourcePowerBound
    (powerBoxCross 9 17 8 half_20_10_φ3) (37623427827/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 17) (u := 15) (t := 18)
    (D := 8) (ψ := (214205861/2500000000 : ℝ)) half_20_10_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_10_bounds3 l).1) (fun l => (half_20_10_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_10_total1, half_20_10_total2, half_20_10_total3, half_20_10_total4, half_20_10_total5, half_20_10_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_16_10) (half_18_10)
    (by simpa only [half_20_10_φ4, show (2:ℝ)*8=16 by norm_num] using half_20_10_hx4)
  exact h.weaken (by norm_num [half_20_10_total1, half_20_10_total2, half_20_10_total3, half_20_10_total4, half_20_10_total5, half_20_10_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_10_hx2 : SourcePowerBound
    (powerBoxCross 9 18 4 half_20_10_φ2) (225938216449/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 18) (u := 16) (t := 19)
    (D := 4) (ψ := (979226793/10000000000 : ℝ)) half_20_10_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_10_bounds2 l).1) (fun l => (half_20_10_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_10_total1, half_20_10_total2, half_20_10_total3, half_20_10_total4, half_20_10_total5, half_20_10_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_17_10) (half_19_10)
    (by simpa only [half_20_10_φ3, show (2:ℝ)*4=8 by norm_num] using half_20_10_hx3)
  exact h.weaken (by norm_num [half_20_10_total1, half_20_10_total2, half_20_10_total3, half_20_10_total4, half_20_10_total5, half_20_10_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_10_hx1 : SourcePowerBound
    (powerBoxCross 9 19 2 half_20_10_φ1) (6784508811/250000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 19) (u := 17) (t := 20)
    (D := 2) (ψ := (215859317/2000000000 : ℝ)) half_20_10_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_10_bounds1 l).1) (fun l => (half_20_10_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_10_total1, half_20_10_total2, half_20_10_total3, half_20_10_total4, half_20_10_total5, half_20_10_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_18_10) (half_20_09)
    (by simpa only [half_20_10_φ2, show (2:ℝ)*2=4 by norm_num] using half_20_10_hx2)
  exact h.weaken (by norm_num [half_20_10_total1, half_20_10_total2, half_20_10_total3, half_20_10_total4, half_20_10_total5, half_20_10_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_20_10 : AdmissibleExponent 9 40 (62319049569/2000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 18) (ψ := (217377813/2000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_19_10)
    (by simpa only [half_20_10_φ1] using half_20_10_hx1)
  exact admissibleExponent_mono h (by norm_num [half_20_10_total1, half_20_10_total2, half_20_10_total3, half_20_10_total4, half_20_10_total5, half_20_10_total6, parameterExponent, curveLoss, dyadicExponent])

private def half_21_10_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (273285657/2500000000 : ℝ)

private theorem half_21_10_total1 : total half_21_10_φ1=(273285657/2500000000 : ℝ) := by
  norm_num [half_21_10_φ1,total,emptyPhi,Fin.snoc]

private theorem half_21_10_bounds1 : ∀ l,0≤half_21_10_φ1 l ∧ half_21_10_φ1 l≤1 ∧
    0≤shiftExponents 9 half_21_10_φ1 l :=
  alternate_bounds_snoc emptyPhi (273285657/2500000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_21_10_φ2 : Fin 2 → ℝ := Fin.snoc half_21_10_φ1 (543962689/5000000000 : ℝ)

private theorem half_21_10_total2 : total half_21_10_φ2=(1090534003/5000000000 : ℝ) := by
  change total (Fin.snoc half_21_10_φ1 (543962689/5000000000 : ℝ))=(1090534003/5000000000 : ℝ)
  rw [alternate_total_snoc,half_21_10_total1]
  norm_num

private theorem half_21_10_bounds2 : ∀ l,0≤half_21_10_φ2 l ∧ half_21_10_φ2 l≤1 ∧
    0≤shiftExponents 9 half_21_10_φ2 l :=
  alternate_bounds_snoc half_21_10_φ1 (543962689/5000000000 : ℝ) half_21_10_bounds1 (by norm_num)

private def half_21_10_φ3 : Fin 3 → ℝ := Fin.snoc half_21_10_φ2 (977366499/10000000000 : ℝ)

private theorem half_21_10_total3 : total half_21_10_φ3=(631686901/2000000000 : ℝ) := by
  change total (Fin.snoc half_21_10_φ2 (977366499/10000000000 : ℝ))=(631686901/2000000000 : ℝ)
  rw [alternate_total_snoc,half_21_10_total2]
  norm_num

private theorem half_21_10_bounds3 : ∀ l,0≤half_21_10_φ3 l ∧ half_21_10_φ3 l≤1 ∧
    0≤shiftExponents 9 half_21_10_φ3 l :=
  alternate_bounds_snoc half_21_10_φ2 (977366499/10000000000 : ℝ) half_21_10_bounds2 (by norm_num)

private def half_21_10_φ4 : Fin 4 → ℝ := Fin.snoc half_21_10_φ3 (427597843/5000000000 : ℝ)

private theorem half_21_10_total4 : total half_21_10_φ4=(4013630191/10000000000 : ℝ) := by
  change total (Fin.snoc half_21_10_φ3 (427597843/5000000000 : ℝ))=(4013630191/10000000000 : ℝ)
  rw [alternate_total_snoc,half_21_10_total3]
  norm_num

private theorem half_21_10_bounds4 : ∀ l,0≤half_21_10_φ4 l ∧ half_21_10_φ4 l≤1 ∧
    0≤shiftExponents 9 half_21_10_φ4 l :=
  alternate_bounds_snoc half_21_10_φ3 (427597843/5000000000 : ℝ) half_21_10_bounds3 (by norm_num)

private def half_21_10_φ5 : Fin 5 → ℝ := Fin.snoc half_21_10_φ4 (29931849/400000000 : ℝ)

private theorem half_21_10_total5 : total half_21_10_φ5=(297620401/625000000 : ℝ) := by
  change total (Fin.snoc half_21_10_φ4 (29931849/400000000 : ℝ))=(297620401/625000000 : ℝ)
  rw [alternate_total_snoc,half_21_10_total4]
  norm_num

private theorem half_21_10_bounds5 : ∀ l,0≤half_21_10_φ5 l ∧ half_21_10_φ5 l≤1 ∧
    0≤shiftExponents 9 half_21_10_φ5 l :=
  alternate_bounds_snoc half_21_10_φ4 (29931849/400000000 : ℝ) half_21_10_bounds4 (by norm_num)

private def half_21_10_φ6 : Fin 6 → ℝ := Fin.snoc half_21_10_φ5 (654759197/10000000000 : ℝ)

private theorem half_21_10_total6 : total half_21_10_φ6=(5416685613/10000000000 : ℝ) := by
  change total (Fin.snoc half_21_10_φ5 (654759197/10000000000 : ℝ))=(5416685613/10000000000 : ℝ)
  rw [alternate_total_snoc,half_21_10_total5]
  norm_num

private theorem half_21_10_bounds6 : ∀ l,0≤half_21_10_φ6 l ∧ half_21_10_φ6 l≤1 ∧
    0≤shiftExponents 9 half_21_10_φ6 l :=
  alternate_bounds_snoc half_21_10_φ5 (654759197/10000000000 : ℝ) half_21_10_bounds5 (by norm_num)

private theorem half_21_10_prefix : PrefixCondition 9 half_21_10_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_21_10_φ1, half_21_10_φ2, half_21_10_φ3, half_21_10_φ4, half_21_10_φ5, half_21_10_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_21_10_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_21_10_φ6) (8749943161/1250000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_21_10_φ6
    (fun i => (half_21_10_bounds6 i).1) (fun i => (half_21_10_bounds6 i).2.1)
    (fun i => (half_21_10_bounds6 i).2.2) half_21_10_prefix
  convert h using 1 <;> norm_num [half_21_10_total1, half_21_10_total2, half_21_10_total3, half_21_10_total4, half_21_10_total5, half_21_10_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_21_10_hx6 : SourcePowerBound
    (powerBoxCross 9 15 64 half_21_10_φ6) (12461031/1000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 15) (r := 2) (v := 0) (w := 20) (D := 64)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_21_10_φ6 (by norm_num [half_21_10_total1, half_21_10_total2, half_21_10_total3, half_21_10_total4, half_21_10_total5, half_21_10_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_21_10_total1, half_21_10_total2, half_21_10_total3, half_21_10_total4, half_21_10_total5, half_21_10_total6, parameterExponent, curveLoss, dyadicExponent]) half_21_10_hF2
    (admissibleExponent_zero 9) (half_20_10)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_21_10_total1, half_21_10_total2, half_21_10_total3, half_21_10_total4, half_21_10_total5, half_21_10_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_21_10_hx5 : SourcePowerBound
    (powerBoxCross 9 16 32 half_21_10_φ5) (5764140691/400000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 16) (u := 14) (t := 17)
    (D := 32) (ψ := (654759197/10000000000 : ℝ)) half_21_10_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_21_10_bounds5 l).1) (fun l => (half_21_10_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_21_10_total1, half_21_10_total2, half_21_10_total3, half_21_10_total4, half_21_10_total5, half_21_10_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_15_10) (half_17_10)
    (by simpa only [half_21_10_φ6, show (2:ℝ)*32=64 by norm_num] using half_21_10_hx6)
  exact h.weaken (by norm_num [half_21_10_total1, half_21_10_total2, half_21_10_total3, half_21_10_total4, half_21_10_total5, half_21_10_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_21_10_hx4 : SourcePowerBound
    (powerBoxCross 9 17 16 half_21_10_φ4) (169191674941/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 17) (u := 15) (t := 18)
    (D := 16) (ψ := (29931849/400000000 : ℝ)) half_21_10_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_21_10_bounds4 l).1) (fun l => (half_21_10_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_21_10_total1, half_21_10_total2, half_21_10_total3, half_21_10_total4, half_21_10_total5, half_21_10_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_16_10) (half_18_10)
    (by simpa only [half_21_10_φ5, show (2:ℝ)*16=32 by norm_num] using half_21_10_hx5)
  exact h.weaken (by norm_num [half_21_10_total1, half_21_10_total2, half_21_10_total3, half_21_10_total4, half_21_10_total5, half_21_10_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_21_10_hx3 : SourcePowerBound
    (powerBoxCross 9 18 8 half_21_10_φ3) (200971437777/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 18) (u := 16) (t := 19)
    (D := 8) (ψ := (427597843/5000000000 : ℝ)) half_21_10_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_21_10_bounds3 l).1) (fun l => (half_21_10_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_21_10_total1, half_21_10_total2, half_21_10_total3, half_21_10_total4, half_21_10_total5, half_21_10_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_17_10) (half_19_10)
    (by simpa only [half_21_10_φ4, show (2:ℝ)*8=16 by norm_num] using half_21_10_hx4)
  exact h.weaken (by norm_num [half_21_10_total1, half_21_10_total2, half_21_10_total3, half_21_10_total4, half_21_10_total5, half_21_10_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_21_10_hx2 : SourcePowerBound
    (powerBoxCross 9 19 4 half_21_10_φ2) (9627298529/400000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 19) (u := 17) (t := 20)
    (D := 4) (ψ := (977366499/10000000000 : ℝ)) half_21_10_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_21_10_bounds2 l).1) (fun l => (half_21_10_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_21_10_total1, half_21_10_total2, half_21_10_total3, half_21_10_total4, half_21_10_total5, half_21_10_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_18_10) (half_20_10)
    (by simpa only [half_21_10_φ3, show (2:ℝ)*4=8 by norm_num] using half_21_10_hx3)
  exact h.weaken (by norm_num [half_21_10_total1, half_21_10_total2, half_21_10_total3, half_21_10_total4, half_21_10_total5, half_21_10_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_21_10_hx1 : SourcePowerBound
    (powerBoxCross 9 20 2 half_21_10_φ1) (72156646417/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 20) (u := 18) (t := 21)
    (D := 2) (ψ := (543962689/5000000000 : ℝ)) half_21_10_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_21_10_bounds1 l).1) (fun l => (half_21_10_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_21_10_total1, half_21_10_total2, half_21_10_total3, half_21_10_total4, half_21_10_total5, half_21_10_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_19_10) (half_21_09)
    (by simpa only [half_21_10_φ2, show (2:ℝ)*2=4 by norm_num] using half_21_10_hx2)
  exact h.weaken (by norm_num [half_21_10_total1, half_21_10_total2, half_21_10_total3, half_21_10_total4, half_21_10_total5, half_21_10_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_21_10 : AdmissibleExponent 9 42 (517592419/15625000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 19) (ψ := (273285657/2500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_20_10)
    (by simpa only [half_21_10_φ1] using half_21_10_hx1)
  exact admissibleExponent_mono h (by norm_num [half_21_10_total1, half_21_10_total2, half_21_10_total3, half_21_10_total4, half_21_10_total5, half_21_10_total6, parameterExponent, curveLoss, dyadicExponent])

private def half_22_10_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (549059167/5000000000 : ℝ)

private theorem half_22_10_total1 : total half_22_10_φ1=(549059167/5000000000 : ℝ) := by
  norm_num [half_22_10_φ1,total,emptyPhi,Fin.snoc]

private theorem half_22_10_bounds1 : ∀ l,0≤half_22_10_φ1 l ∧ half_22_10_φ1 l≤1 ∧
    0≤shiftExponents 9 half_22_10_φ1 l :=
  alternate_bounds_snoc emptyPhi (549059167/5000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_22_10_φ2 : Fin 2 → ℝ := Fin.snoc half_22_10_φ1 (547361911/5000000000 : ℝ)

private theorem half_22_10_total2 : total half_22_10_φ2=(548210539/2500000000 : ℝ) := by
  change total (Fin.snoc half_22_10_φ1 (547361911/5000000000 : ℝ))=(548210539/2500000000 : ℝ)
  rw [alternate_total_snoc,half_22_10_total1]
  norm_num

private theorem half_22_10_bounds2 : ∀ l,0≤half_22_10_φ2 l ∧ half_22_10_φ2 l≤1 ∧
    0≤shiftExponents 9 half_22_10_φ2 l :=
  alternate_bounds_snoc half_22_10_φ1 (547361911/5000000000 : ℝ) half_22_10_bounds1 (by norm_num)

private def half_22_10_φ3 : Fin 3 → ℝ := Fin.snoc half_22_10_φ2 (97589473/1000000000 : ℝ)

private theorem half_22_10_total3 : total half_22_10_φ3=(1584368443/5000000000 : ℝ) := by
  change total (Fin.snoc half_22_10_φ2 (97589473/1000000000 : ℝ))=(1584368443/5000000000 : ℝ)
  rw [alternate_total_snoc,half_22_10_total2]
  norm_num

private theorem half_22_10_bounds3 : ∀ l,0≤half_22_10_φ3 l ∧ half_22_10_φ3 l≤1 ∧
    0≤shiftExponents 9 half_22_10_φ3 l :=
  alternate_bounds_snoc half_22_10_φ2 (97589473/1000000000 : ℝ) half_22_10_bounds2 (by norm_num)

private def half_22_10_φ4 : Fin 4 → ℝ := Fin.snoc half_22_10_φ3 (853907889/10000000000 : ℝ)

private theorem half_22_10_total4 : total half_22_10_φ4=(160905791/400000000 : ℝ) := by
  change total (Fin.snoc half_22_10_φ3 (853907889/10000000000 : ℝ))=(160905791/400000000 : ℝ)
  rw [alternate_total_snoc,half_22_10_total3]
  norm_num

private theorem half_22_10_bounds4 : ∀ l,0≤half_22_10_φ4 l ∧ half_22_10_φ4 l≤1 ∧
    0≤shiftExponents 9 half_22_10_φ4 l :=
  alternate_bounds_snoc half_22_10_φ3 (853907889/10000000000 : ℝ) half_22_10_bounds3 (by norm_num)

private def half_22_10_φ5 : Fin 5 → ℝ := Fin.snoc half_22_10_φ4 (373584701/5000000000 : ℝ)

private theorem half_22_10_total5 : total half_22_10_φ5=(4769814177/10000000000 : ℝ) := by
  change total (Fin.snoc half_22_10_φ4 (373584701/5000000000 : ℝ))=(4769814177/10000000000 : ℝ)
  rw [alternate_total_snoc,half_22_10_total4]
  norm_num

private theorem half_22_10_bounds5 : ∀ l,0≤half_22_10_φ5 l ∧ half_22_10_φ5 l≤1 ∧
    0≤shiftExponents 9 half_22_10_φ5 l :=
  alternate_bounds_snoc half_22_10_φ4 (373584701/5000000000 : ℝ) half_22_10_bounds4 (by norm_num)

private def half_22_10_φ6 : Fin 6 → ℝ := Fin.snoc half_22_10_φ5 (653773227/10000000000 : ℝ)

private theorem half_22_10_total6 : total half_22_10_φ6=(1355896851/2500000000 : ℝ) := by
  change total (Fin.snoc half_22_10_φ5 (653773227/10000000000 : ℝ))=(1355896851/2500000000 : ℝ)
  rw [alternate_total_snoc,half_22_10_total5]
  norm_num

private theorem half_22_10_bounds6 : ∀ l,0≤half_22_10_φ6 l ∧ half_22_10_φ6 l≤1 ∧
    0≤shiftExponents 9 half_22_10_φ6 l :=
  alternate_bounds_snoc half_22_10_φ5 (653773227/10000000000 : ℝ) half_22_10_bounds5 (by norm_num)

private theorem half_22_10_prefix : PrefixCondition 9 half_22_10_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_22_10_φ1, half_22_10_φ2, half_22_10_φ3, half_22_10_φ4, half_22_10_φ5, half_22_10_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_22_10_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_22_10_φ6) (2182309447/312500000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_22_10_φ6
    (fun i => (half_22_10_bounds6 i).1) (fun i => (half_22_10_bounds6 i).2.1)
    (fun i => (half_22_10_bounds6 i).2.2) half_22_10_prefix
  convert h using 1 <;> norm_num [half_22_10_total1, half_22_10_total2, half_22_10_total3, half_22_10_total4, half_22_10_total5, half_22_10_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_22_10_hx6 : SourcePowerBound
    (powerBoxCross 9 16 64 half_22_10_φ6) (6670898067/500000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 16) (r := 2) (v := 21) (w := 22) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_22_10_φ6 (by norm_num [half_22_10_total1, half_22_10_total2, half_22_10_total3, half_22_10_total4, half_22_10_total5, half_22_10_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_22_10_total1, half_22_10_total2, half_22_10_total3, half_22_10_total4, half_22_10_total5, half_22_10_total6, parameterExponent, curveLoss, dyadicExponent]) half_22_10_hF2
    (half_21_10) (half_22_09)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_22_10_total1, half_22_10_total2, half_22_10_total3, half_22_10_total4, half_22_10_total5, half_22_10_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_22_10_hx5 : SourcePowerBound
    (powerBoxCross 9 17 32 half_22_10_φ5) (30810412311/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 17) (u := 15) (t := 18)
    (D := 32) (ψ := (653773227/10000000000 : ℝ)) half_22_10_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_22_10_bounds5 l).1) (fun l => (half_22_10_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_22_10_total1, half_22_10_total2, half_22_10_total3, half_22_10_total4, half_22_10_total5, half_22_10_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_16_10) (half_18_10)
    (by simpa only [half_22_10_φ6, show (2:ℝ)*32=64 by norm_num] using half_22_10_hx6)
  exact h.weaken (by norm_num [half_22_10_total1, half_22_10_total2, half_22_10_total3, half_22_10_total4, half_22_10_total5, half_22_10_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_22_10_hx4 : SourcePowerBound
    (powerBoxCross 9 18 16 half_22_10_φ4) (18054340173/1000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 18) (u := 16) (t := 19)
    (D := 16) (ψ := (373584701/5000000000 : ℝ)) half_22_10_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_22_10_bounds4 l).1) (fun l => (half_22_10_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_22_10_total1, half_22_10_total2, half_22_10_total3, half_22_10_total4, half_22_10_total5, half_22_10_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_17_10) (half_19_10)
    (by simpa only [half_22_10_φ5, show (2:ℝ)*16=32 by norm_num] using half_22_10_hx5)
  exact h.weaken (by norm_num [half_22_10_total1, half_22_10_total2, half_22_10_total3, half_22_10_total4, half_22_10_total5, half_22_10_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_22_10_hx3 : SourcePowerBound
    (powerBoxCross 9 19 8 half_22_10_φ3) (106984798767/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 19) (u := 17) (t := 20)
    (D := 8) (ψ := (853907889/10000000000 : ℝ)) half_22_10_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_22_10_bounds3 l).1) (fun l => (half_22_10_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_22_10_total1, half_22_10_total2, half_22_10_total3, half_22_10_total4, half_22_10_total5, half_22_10_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_18_10) (half_20_10)
    (by simpa only [half_22_10_φ4, show (2:ℝ)*8=16 by norm_num] using half_22_10_hx4)
  exact h.weaken (by norm_num [half_22_10_total1, half_22_10_total2, half_22_10_total3, half_22_10_total4, half_22_10_total5, half_22_10_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_22_10_hx2 : SourcePowerBound
    (powerBoxCross 9 20 4 half_22_10_φ2) (31947138187/1250000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 20) (u := 18) (t := 21)
    (D := 4) (ψ := (97589473/1000000000 : ℝ)) half_22_10_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_22_10_bounds2 l).1) (fun l => (half_22_10_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_22_10_total1, half_22_10_total2, half_22_10_total3, half_22_10_total4, half_22_10_total5, half_22_10_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_19_10) (half_21_10)
    (by simpa only [half_22_10_φ3, show (2:ℝ)*4=8 by norm_num] using half_22_10_hx3)
  exact h.weaken (by norm_num [half_22_10_total1, half_22_10_total2, half_22_10_total3, half_22_10_total4, half_22_10_total5, half_22_10_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_22_10_hx1 : SourcePowerBound
    (powerBoxCross 9 21 2 half_22_10_φ1) (152990546053/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 21) (u := 19) (t := 22)
    (D := 2) (ψ := (547361911/5000000000 : ℝ)) half_22_10_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_22_10_bounds1 l).1) (fun l => (half_22_10_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_22_10_total1, half_22_10_total2, half_22_10_total3, half_22_10_total4, half_22_10_total5, half_22_10_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_20_10) (half_22_09)
    (by simpa only [half_22_10_φ2, show (2:ℝ)*2=4 by norm_num] using half_22_10_hx2)
  exact h.weaken (by norm_num [half_22_10_total1, half_22_10_total2, half_22_10_total3, half_22_10_total4, half_22_10_total5, half_22_10_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_22_10 : AdmissibleExponent 9 44 (1755019719/50000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 20) (ψ := (549059167/5000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_21_10)
    (by simpa only [half_22_10_φ1] using half_22_10_hx1)
  exact admissibleExponent_mono h (by norm_num [half_22_10_total1, half_22_10_total2, half_22_10_total3, half_22_10_total4, half_22_10_total5, half_22_10_total6, parameterExponent, curveLoss, dyadicExponent])

private def half_10_11_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (880557113/10000000000 : ℝ)

private theorem half_10_11_total1 : total half_10_11_φ1=(880557113/10000000000 : ℝ) := by
  norm_num [half_10_11_φ1,total,emptyPhi,Fin.snoc]

private theorem half_10_11_bounds1 : ∀ l,0≤half_10_11_φ1 l ∧ half_10_11_φ1 l≤1 ∧
    0≤shiftExponents 9 half_10_11_φ1 l :=
  alternate_bounds_snoc emptyPhi (880557113/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_10_11_φ2 : Fin 2 → ℝ := Fin.snoc half_10_11_φ1 (410784249/5000000000 : ℝ)

private theorem half_10_11_total2 : total half_10_11_φ2=(1702125611/10000000000 : ℝ) := by
  change total (Fin.snoc half_10_11_φ1 (410784249/5000000000 : ℝ))=(1702125611/10000000000 : ℝ)
  rw [alternate_total_snoc,half_10_11_total1]
  norm_num

private theorem half_10_11_bounds2 : ∀ l,0≤half_10_11_φ2 l ∧ half_10_11_φ2 l≤1 ∧
    0≤shiftExponents 9 half_10_11_φ2 l :=
  alternate_bounds_snoc half_10_11_φ1 (410784249/5000000000 : ℝ) half_10_11_bounds1 (by norm_num)

private def half_10_11_φ3 : Fin 3 → ℝ := Fin.snoc half_10_11_φ2 (717048137/10000000000 : ℝ)

private theorem half_10_11_total3 : total half_10_11_φ3=(604793437/2500000000 : ℝ) := by
  change total (Fin.snoc half_10_11_φ2 (717048137/10000000000 : ℝ))=(604793437/2500000000 : ℝ)
  rw [alternate_total_snoc,half_10_11_total2]
  norm_num

private theorem half_10_11_bounds3 : ∀ l,0≤half_10_11_φ3 l ∧ half_10_11_φ3 l≤1 ∧
    0≤shiftExponents 9 half_10_11_φ3 l :=
  alternate_bounds_snoc half_10_11_φ2 (717048137/10000000000 : ℝ) half_10_11_bounds2 (by norm_num)

private def half_10_11_φ4 : Fin 4 → ℝ := Fin.snoc half_10_11_φ3 (450213301/10000000000 : ℝ)

private theorem half_10_11_total4 : total half_10_11_φ4=(2869387049/10000000000 : ℝ) := by
  change total (Fin.snoc half_10_11_φ3 (450213301/10000000000 : ℝ))=(2869387049/10000000000 : ℝ)
  rw [alternate_total_snoc,half_10_11_total3]
  norm_num

private theorem half_10_11_bounds4 : ∀ l,0≤half_10_11_φ4 l ∧ half_10_11_φ4 l≤1 ∧
    0≤shiftExponents 9 half_10_11_φ4 l :=
  alternate_bounds_snoc half_10_11_φ3 (450213301/10000000000 : ℝ) half_10_11_bounds3 (by norm_num)

private theorem half_10_11_prefix : PrefixCondition 9 half_10_11_φ4 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_10_11_φ1, half_10_11_φ2, half_10_11_φ3, half_10_11_φ4, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_10_11_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 16 half_10_11_φ4) (8891838853/1250000000 : ℝ) := by
  have h := padded_dyadic_divisor_power (k := 9) (j := 4) (r := 0) (n := 1) (D := 16)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_10_11_φ4
    (fun i => (half_10_11_bounds4 i).1) (fun i => (half_10_11_bounds4 i).2.1)
    (fun i => (half_10_11_bounds4 i).2.2) half_10_11_prefix
  convert h using 1 <;> norm_num [half_10_11_total1, half_10_11_total2, half_10_11_total3, half_10_11_total4, parameterExponent, curveLoss, dyadicExponent]

private theorem half_10_11_hx4 : SourcePowerBound
    (powerBoxCross 9 6 16 half_10_11_φ4) (13829018479/2000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 6) (r := 2) (v := 0) (w := 8) (D := 16)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_10_11_φ4 (by norm_num [half_10_11_total1, half_10_11_total2, half_10_11_total3, half_10_11_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_10_11_total1, half_10_11_total2, half_10_11_total3, half_10_11_total4, parameterExponent, curveLoss, dyadicExponent]) half_10_11_hF2
    (admissibleExponent_zero 9) (SeedCompletionHigher9SimpleSeeds.degree9_half_8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_10_11_total1, half_10_11_total2, half_10_11_total3, half_10_11_total4, parameterExponent, curveLoss, dyadicExponent])

private theorem half_10_11_hx3 : SourcePowerBound
    (powerBoxCross 9 7 8 half_10_11_φ3) (39387437663/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 7) (u := 5) (t := 8)
    (D := 8) (ψ := (450213301/10000000000 : ℝ)) half_10_11_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_10_11_bounds3 l).1) (fun l => (half_10_11_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_10_11_total1, half_10_11_total2, half_10_11_total3, half_10_11_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionNinthSecondSeeds.ninth_half_6) (SeedCompletionHigher9SimpleSeeds.degree9_half_8)
    (by simpa only [half_10_11_φ4, show (2:ℝ)*8=16 by norm_num] using half_10_11_hx4)
  exact h.weaken (by norm_num [half_10_11_total1, half_10_11_total2, half_10_11_total3, half_10_11_total4, parameterExponent, curveLoss, dyadicExponent])

private theorem half_10_11_hx2 : SourcePowerBound
    (powerBoxCross 9 8 4 half_10_11_φ2) (46734645747/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 8) (u := 6) (t := 9)
    (D := 4) (ψ := (717048137/10000000000 : ℝ)) half_10_11_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_10_11_bounds2 l).1) (fun l => (half_10_11_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_10_11_total1, half_10_11_total2, half_10_11_total3, half_10_11_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionNinthSecondSeeds.ninth_half_7) (SeedCompletionHigher9SimpleSeeds.degree9_half_9)
    (by simpa only [half_10_11_φ3, show (2:ℝ)*4=8 by norm_num] using half_10_11_hx3)
  exact h.weaken (by norm_num [half_10_11_total1, half_10_11_total2, half_10_11_total3, half_10_11_total4, parameterExponent, curveLoss, dyadicExponent])

private theorem half_10_11_hx1 : SourcePowerBound
    (powerBoxCross 9 9 2 half_10_11_φ1) (112493972997/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 9) (u := 7) (t := 10)
    (D := 2) (ψ := (410784249/5000000000 : ℝ)) half_10_11_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_10_11_bounds1 l).1) (fun l => (half_10_11_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_10_11_total1, half_10_11_total2, half_10_11_total3, half_10_11_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_8) (half_10_10)
    (by simpa only [half_10_11_φ2, show (2:ℝ)*2=4 by norm_num] using half_10_11_hx2)
  exact h.weaken (by norm_num [half_10_11_total1, half_10_11_total2, half_10_11_total3, half_10_11_total4, parameterExponent, curveLoss, dyadicExponent])

theorem half_10_11 : AdmissibleExponent 9 20 (63731721959/5000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 8) (ψ := (880557113/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (SeedCompletionHigher9SimpleSeeds.degree9_half_9)
    (by simpa only [half_10_11_φ1] using half_10_11_hx1)
  exact admissibleExponent_mono h (by norm_num [half_10_11_total1, half_10_11_total2, half_10_11_total3, half_10_11_total4, parameterExponent, curveLoss, dyadicExponent])

private def half_11_11_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (228936043/2500000000 : ℝ)

private theorem half_11_11_total1 : total half_11_11_φ1=(228936043/2500000000 : ℝ) := by
  norm_num [half_11_11_φ1,total,emptyPhi,Fin.snoc]

private theorem half_11_11_bounds1 : ∀ l,0≤half_11_11_φ1 l ∧ half_11_11_φ1 l≤1 ∧
    0≤shiftExponents 9 half_11_11_φ1 l :=
  alternate_bounds_snoc emptyPhi (228936043/2500000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_11_11_φ2 : Fin 2 → ℝ := Fin.snoc half_11_11_φ1 (86540159/1000000000 : ℝ)

private theorem half_11_11_total2 : total half_11_11_φ2=(890572881/5000000000 : ℝ) := by
  change total (Fin.snoc half_11_11_φ1 (86540159/1000000000 : ℝ))=(890572881/5000000000 : ℝ)
  rw [alternate_total_snoc,half_11_11_total1]
  norm_num

private theorem half_11_11_bounds2 : ∀ l,0≤half_11_11_φ2 l ∧ half_11_11_φ2 l≤1 ∧
    0≤shiftExponents 9 half_11_11_φ2 l :=
  alternate_bounds_snoc half_11_11_φ1 (86540159/1000000000 : ℝ) half_11_11_bounds1 (by norm_num)

private def half_11_11_φ3 : Fin 3 → ℝ := Fin.snoc half_11_11_φ2 (788110913/10000000000 : ℝ)

private theorem half_11_11_total3 : total half_11_11_φ3=(102770267/400000000 : ℝ) := by
  change total (Fin.snoc half_11_11_φ2 (788110913/10000000000 : ℝ))=(102770267/400000000 : ℝ)
  rw [alternate_total_snoc,half_11_11_total2]
  norm_num

private theorem half_11_11_bounds3 : ∀ l,0≤half_11_11_φ3 l ∧ half_11_11_φ3 l≤1 ∧
    0≤shiftExponents 9 half_11_11_φ3 l :=
  alternate_bounds_snoc half_11_11_φ2 (788110913/10000000000 : ℝ) half_11_11_bounds2 (by norm_num)

private def half_11_11_φ4 : Fin 4 → ℝ := Fin.snoc half_11_11_φ3 (156186569/2500000000 : ℝ)

private theorem half_11_11_total4 : total half_11_11_φ4=(3194002951/10000000000 : ℝ) := by
  change total (Fin.snoc half_11_11_φ3 (156186569/2500000000 : ℝ))=(3194002951/10000000000 : ℝ)
  rw [alternate_total_snoc,half_11_11_total3]
  norm_num

private theorem half_11_11_bounds4 : ∀ l,0≤half_11_11_φ4 l ∧ half_11_11_φ4 l≤1 ∧
    0≤shiftExponents 9 half_11_11_φ4 l :=
  alternate_bounds_snoc half_11_11_φ3 (156186569/2500000000 : ℝ) half_11_11_bounds3 (by norm_num)

private theorem half_11_11_prefix : PrefixCondition 9 half_11_11_φ4 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_11_11_φ1, half_11_11_φ2, half_11_11_φ3, half_11_11_φ4, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_11_11_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 16 half_11_11_φ4) (7917991147/1250000000 : ℝ) := by
  have h := padded_dyadic_divisor_power (k := 9) (j := 4) (r := 0) (n := 1) (D := 16)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_11_11_φ4
    (fun i => (half_11_11_bounds4 i).1) (fun i => (half_11_11_bounds4 i).2.1)
    (fun i => (half_11_11_bounds4 i).2.2) half_11_11_prefix
  convert h using 1 <;> norm_num [half_11_11_total1, half_11_11_total2, half_11_11_total3, half_11_11_total4, parameterExponent, curveLoss, dyadicExponent]

private theorem half_11_11_hx4 : SourcePowerBound
    (powerBoxCross 9 7 16 half_11_11_φ4) (9430224713/1250000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 7) (r := 2) (v := 9) (w := 10) (D := 16)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_11_11_φ4 (by norm_num [half_11_11_total1, half_11_11_total2, half_11_11_total3, half_11_11_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_11_11_total1, half_11_11_total2, half_11_11_total3, half_11_11_total4, parameterExponent, curveLoss, dyadicExponent]) half_11_11_hF2
    (SeedCompletionHigher9SimpleSeeds.degree9_half_9) (half_10_11)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_11_11_total1, half_11_11_total2, half_11_11_total3, half_11_11_total4, parameterExponent, curveLoss, dyadicExponent])

private theorem half_11_11_hx3 : SourcePowerBound
    (powerBoxCross 9 8 8 half_11_11_φ3) (87903261273/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 8) (u := 6) (t := 9)
    (D := 8) (ψ := (156186569/2500000000 : ℝ)) half_11_11_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_11_11_bounds3 l).1) (fun l => (half_11_11_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_11_11_total1, half_11_11_total2, half_11_11_total3, half_11_11_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionNinthSecondSeeds.ninth_half_7) (SeedCompletionHigher9SimpleSeeds.degree9_half_9)
    (by simpa only [half_11_11_φ4, show (2:ℝ)*8=16 by norm_num] using half_11_11_hx4)
  exact h.weaken (by norm_num [half_11_11_total1, half_11_11_total2, half_11_11_total3, half_11_11_total4, parameterExponent, curveLoss, dyadicExponent])

private theorem half_11_11_hx2 : SourcePowerBound
    (powerBoxCross 9 9 4 half_11_11_φ2) (26279513187/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 9) (u := 7) (t := 10)
    (D := 4) (ψ := (788110913/10000000000 : ℝ)) half_11_11_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_11_11_bounds2 l).1) (fun l => (half_11_11_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_11_11_total1, half_11_11_total2, half_11_11_total3, half_11_11_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_8) (half_10_11)
    (by simpa only [half_11_11_φ3, show (2:ℝ)*4=8 by norm_num] using half_11_11_hx3)
  exact h.weaken (by norm_num [half_11_11_total1, half_11_11_total2, half_11_11_total3, half_11_11_total4, parameterExponent, curveLoss, dyadicExponent])

private theorem half_11_11_hx1 : SourcePowerBound
    (powerBoxCross 9 10 2 half_11_11_φ1) (126706797503/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 10) (u := 8) (t := 11)
    (D := 2) (ψ := (86540159/1000000000 : ℝ)) half_11_11_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_11_11_bounds1 l).1) (fun l => (half_11_11_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_11_11_total1, half_11_11_total2, half_11_11_total3, half_11_11_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_9) (half_11_10)
    (by simpa only [half_11_11_φ2, show (2:ℝ)*2=4 by norm_num] using half_11_11_hx2)
  exact h.weaken (by norm_num [half_11_11_total1, half_11_11_total2, half_11_11_total3, half_11_11_total4, parameterExponent, curveLoss, dyadicExponent])

theorem half_11_11 : AdmissibleExponent 9 22 (144105936771/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 9) (ψ := (228936043/2500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_10_11)
    (by simpa only [half_11_11_φ1] using half_11_11_hx1)
  exact admissibleExponent_mono h (by norm_num [half_11_11_total1, half_11_11_total2, half_11_11_total3, half_11_11_total4, parameterExponent, curveLoss, dyadicExponent])

end Waring.SeedCompletionAlternate9Seeds
